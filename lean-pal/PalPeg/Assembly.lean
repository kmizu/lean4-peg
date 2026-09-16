import PalPeg.Stages
import PalPeg.Chain
import Mathlib.Data.List.Perm.Subperm

/-!
# 上位オンライン制御器（assembly）

二進段（dyadic stage）方式の実時間回文認識器の **最上位のオンライン制御器** を定義し、
段ごとの二つのオラクル・インタフェースに対して相対的に正当性を証明する。
（各オラクルの実時間実現は他ファイルで扱う。）

* `MatchOracle` / `MiddleOracle` — 段ごとのインタフェース（`pal_prefix_iff_stage` の二つの連言肢）。
* `stageAnswer` / `dyadicAnswer` — 段の答えと大域の答え。
* `dyadicAnswer_correct` / `dyadicAnswer_length_iff_mem_PAL` — 正当性。
* `liveStages` / `liveStages_length_le` / `stageOf_mem_live` /
  `stage_created_at` / `stage_retired` — 段のライフサイクル
  （`delayed_pal.py:43-52,110-114` に対応）。
* `dyadicAnswer_take` / `dyadicAnswer_prefix` — 局所性：時刻 `n` の答えは `w.take n` にしか依存しない。
-/

namespace PalPeg

universe u
variable {α : Type u}

/-! ## 段ごとのオラクル・インタフェース -/

/-- **照合オラクル**：幅 `W` の段が持つパターン照合器。
時刻 `n`（`2 * W ≤ n ≤ |w|`）において、反転パターン `(w.take W).reverse` が
接頭辞 `w.take n` の末尾に出現するか否かを返す。 -/
structure MatchOracle (w : List α) (W : ℕ) (ans : ℕ → Bool) : Prop where
  spec : ∀ n, 2 * W ≤ n → n ≤ w.length →
    (ans n = true ↔ occursAt (w.take W).reverse (w.take n))

/-- **中央オラクル**：幅 `W` の段が持つ「中央が回文か」のフラグ列。
時刻 `n`（`2 * W ≤ n ≤ |w|`）において、中央部 `(w.drop W).take (n - 2 * W)` が
回文か否かを返す。 -/
structure MiddleOracle (w : List α) (W : ℕ) (flag : ℕ → Bool) : Prop where
  spec : ∀ n, 2 * W ≤ n → n ≤ w.length →
    (flag n = true ↔ IsPal ((w.drop W).take (n - 2 * W)))

/-! ## 段の答えと大域の答え -/

/-- 段の答え：照合と中央フラグの論理積（`delayed_pal.py:80` の `matched and middle`）。 -/
def stageAnswer (ans flag : ℕ → Bool) (n : ℕ) : Bool := ans n && flag n

/-- 段の答えの正当性：`pal_prefix_iff_stage` をオラクルで置き換えたもの。 -/
theorem stageAnswer_correct {w : List α} {W : ℕ} {ans flag : ℕ → Bool}
    (hm : MatchOracle w W ans) (hf : MiddleOracle w W flag)
    {n : ℕ} (hW : 2 * W ≤ n) (hn : n ≤ w.length) :
    stageAnswer ans flag n = true ↔ IsPal (w.take n) := by
  rw [pal_prefix_iff_stage hW hn, stageAnswer, Bool.and_eq_true,
    hm.spec n hW hn, hf.spec n hW hn]

/-- **上位オンライン制御器**（`delayed_pal.py:106-118`）：
`n < 2` は常に真、`2 ≤ n < 4` は両端 1 文字の比較、
`4 ≤ n` は担当段 `stageOf n` の答えをそのまま使う。 -/
def dyadicAnswer [DecidableEq α] (w : List α) (oracles : ℕ → (ℕ → Bool) × (ℕ → Bool))
    (n : ℕ) : Bool :=
  if n < 2 then true
  else if n < 4 then decide (w[0]? = w[n - 1]?)
  else
    let W := stageOf n
    stageAnswer (oracles W).1 (oracles W).2 n

/-! ## 正当性 -/

/-- **主定理**：二つのオラクル・インタフェースを満たす段の集まりが与えられれば、
制御器 `dyadicAnswer` は全ての時刻 `n ≤ |w|` で接頭辞 `w.take n` の回文性を正しく答える。 -/
theorem dyadicAnswer_correct [DecidableEq α] {w : List α}
    {oracles : ℕ → (ℕ → Bool) × (ℕ → Bool)}
    (hO : ∀ W, MatchOracle w W (oracles W).1 ∧ MiddleOracle w W (oracles W).2)
    (n : ℕ) (hn : n ≤ w.length) :
    dyadicAnswer w oracles n = true ↔ IsPal (w.take n) := by
  unfold dyadicAnswer
  split_ifs with h2 h4
  · exact iff_of_true rfl (pal_take_lt_two w h2)
  · rw [decide_eq_true_iff]
    exact (pal_take_two_three (by omega) (by omega) hn).symm
  · have hs := stageOf_spec (n := n) (by omega)
    exact stageAnswer_correct (hO (stageOf n)).1 (hO (stageOf n)).2 hs.1 hn

/-- 系（`α = Fin 2`）：全体を読み終えた時刻の答えは `w ∈ PAL` と一致する。 -/
theorem dyadicAnswer_length_iff_mem_PAL {w : List (Fin 2)}
    {oracles : ℕ → (ℕ → Bool) × (ℕ → Bool)}
    (hO : ∀ W, MatchOracle w W (oracles W).1 ∧ MiddleOracle w W (oracles W).2) :
    dyadicAnswer w oracles w.length = true ↔ w ∈ PAL := by
  rw [dyadicAnswer_correct hO w.length le_rfl, List.take_length]
  exact (mem_PAL_iff_isPal w).symm

/-! ## 段のライフサイクル -/

/-- 時刻 `n` に「生きている」段の幅の一覧：`W ≤ n < 4 * W` を満たす 2 冪
（`delayed_pal.py:96-105` の生成・退役規則）。 -/
def liveStages (n : ℕ) : List ℕ :=
  ((List.range (Nat.log 2 n + 1)).map (2 ^ ·)).filter
    (fun W => decide (W ≤ n ∧ n < 4 * W))

theorem mem_liveStages {W n : ℕ} :
    W ∈ liveStages n ↔
      (∃ k, k < Nat.log 2 n + 1 ∧ 2 ^ k = W) ∧ W ≤ n ∧ n < 4 * W := by
  simp only [liveStages, List.mem_filter, List.mem_map, List.mem_range, decide_eq_true_eq]

theorem liveStages_spec {W n : ℕ} (h : W ∈ liveStages n) : W ≤ n ∧ n < 4 * W :=
  (mem_liveStages.mp h).2

theorem liveStages_pow {W n : ℕ} (h : W ∈ liveStages n) : ∃ k, W = 2 ^ k := by
  obtain ⟨⟨k, _, hk⟩, _⟩ := mem_liveStages.mp h
  exact ⟨k, hk.symm⟩

/-- 生きている二つの段の指数は高々 1 しか離れない（`live_stages` の言い換え）。 -/
theorem liveStages_exponents_close {n j k : ℕ}
    (hj : 2 ^ j ∈ liveStages n) (hk : 2 ^ k ∈ liveStages n) : j ≤ k + 1 ∧ k ≤ j + 1 := by
  obtain ⟨hj1, hj2⟩ := liveStages_spec hj
  obtain ⟨hk1, hk2⟩ := liveStages_spec hk
  exact live_stages hk1 hk2 hj1 hj2

/-- 生きている段は `2 ^ (log₂ n - 1)` と `2 ^ (log₂ n)` の二つしかありえない。 -/
theorem liveStages_subset (n : ℕ) :
    liveStages n ⊆ [2 ^ (Nat.log 2 n - 1), 2 ^ Nat.log 2 n] := by
  intro W hW
  obtain ⟨⟨k, hklt, rfl⟩, hle, hlt⟩ := mem_liveStages.mp hW
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hn0 : n ≠ 0 := by omega
  have h4 : (4 : ℕ) * 2 ^ k = 2 ^ (k + 2) := by
    rw [Nat.pow_succ, Nat.pow_succ]; omega
  have hlog : Nat.log 2 n < k + 2 := Nat.log_lt_of_lt_pow hn0 (by omega)
  have hcase : k = Nat.log 2 n - 1 ∨ k = Nat.log 2 n := by omega
  rcases hcase with h | h <;> simp [h]

theorem liveStages_nodup (n : ℕ) : (liveStages n).Nodup := by
  have hinj : Function.Injective (fun k : ℕ => 2 ^ k) :=
    Nat.pow_right_injective (le_refl 2)
  exact (List.nodup_range.map hinj).filter _

/-- **生きている段は高々 2 つ**（`delayed_pal.py:113-114` の表明）。 -/
theorem liveStages_length_le (n : ℕ) : (liveStages n).length ≤ 2 := by
  have h := (List.subperm_of_subset (liveStages_nodup n) (liveStages_subset n)).length_le
  simpa using h

/-- 時刻 `n ≥ 4` の担当段は実際に生きている（被覆性）。 -/
theorem stageOf_mem_live {n : ℕ} (hn : 4 ≤ n) : stageOf n ∈ liveStages n := by
  obtain ⟨h1, h2⟩ := stageOf_spec (n := n) (by omega)
  exact mem_liveStages.mpr ⟨⟨Nat.log 2 n - 1, by omega, rfl⟩, by omega, h2⟩

/-- **生成**：幅 `W = 2 ^ k` の段は時刻 `W` に生まれる。 -/
theorem stage_created_at {W k : ℕ} (hW : W = 2 ^ k) : W ∈ liveStages W := by
  subst hW
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  refine mem_liveStages.mpr ⟨⟨k, ?_, rfl⟩, le_rfl, by omega⟩
  rw [Nat.log_pow (by omega)]
  omega

/-- **退役**：幅 `W` の段は時刻 `4 * W` にはもう生きていない。 -/
theorem stage_retired (W : ℕ) : W ∉ liveStages (4 * W) := by
  intro h
  have := (liveStages_spec h).2
  omega

/-! ## 局所性（オンライン性） -/

/-- オラクルの値が時刻 `n` で一致すれば、`dyadicAnswer` も一致する。 -/
theorem dyadicAnswer_congr_oracles [DecidableEq α] (w : List α)
    (o o' : ℕ → (ℕ → Bool) × (ℕ → Bool)) (n : ℕ)
    (h1 : ∀ W, (o' W).1 n = (o W).1 n) (h2 : ∀ W, (o' W).2 n = (o W).2 n) :
    dyadicAnswer w o' n = dyadicAnswer w o n := by
  unfold dyadicAnswer
  split_ifs with ha hb
  · rfl
  · rfl
  · simp only [stageAnswer, h1, h2]

/-- **局所性**：時刻 `n` の答えは接頭辞 `w.take m`（`n ≤ m`）だけに依存する。 -/
theorem dyadicAnswer_take_of_le [DecidableEq α] (w : List α)
    (o : ℕ → (ℕ → Bool) × (ℕ → Bool)) {n m : ℕ} (hnm : n ≤ m) :
    dyadicAnswer (w.take m) o n = dyadicAnswer w o n := by
  unfold dyadicAnswer
  split_ifs with ha hb
  · rfl
  · rw [List.getElem?_take_of_lt (show 0 < m by omega),
      List.getElem?_take_of_lt (show n - 1 < m by omega)]
  · rfl

/-- 特に、時刻 `n` の答えは `w.take n` だけで決まる。 -/
theorem dyadicAnswer_take [DecidableEq α] (w : List α)
    (o : ℕ → (ℕ → Bool) × (ℕ → Bool)) (n : ℕ) :
    dyadicAnswer (w.take n) o n = dyadicAnswer w o n :=
  dyadicAnswer_take_of_le w o le_rfl

/-- 接頭辞整合なオラクルのもとでの完全な局所性：
`w.take m` 上の制御器と `w` 上の制御器は時刻 `n ≤ m` で同じ答えを返す。 -/
theorem dyadicAnswer_prefix [DecidableEq α] (w : List α)
    (o o' : ℕ → (ℕ → Bool) × (ℕ → Bool)) {n m : ℕ} (hnm : n ≤ m)
    (h1 : ∀ W, (o' W).1 n = (o W).1 n) (h2 : ∀ W, (o' W).2 n = (o W).2 n) :
    dyadicAnswer (w.take m) o' n = dyadicAnswer w o n := by
  rw [dyadicAnswer_congr_oracles (w.take m) o o' n h1 h2, dyadicAnswer_take_of_le w o hnm]

/-- オンライン版の正当性：時刻 `n` までしか読んでいなくても答えは正しい。 -/
theorem dyadicAnswer_online [DecidableEq α] {w : List α}
    {oracles : ℕ → (ℕ → Bool) × (ℕ → Bool)}
    (hO : ∀ W, MatchOracle w W (oracles W).1 ∧ MiddleOracle w W (oracles W).2)
    {n m : ℕ} (hnm : n ≤ m) (hn : n ≤ w.length) :
    dyadicAnswer (w.take m) oracles n = true ↔ IsPal (w.take n) := by
  rw [dyadicAnswer_take_of_le w oracles hnm]
  exact dyadicAnswer_correct hO n hn

/-! ## 半分割版（`half split`）の制御器

幅 `S` の段が分割点 `h = S / 2` を使う版。段は依然として `n ∈ [2S, 4S)` で答えるが、
分割は `h` で行うので、パターン `(w.take h).reverse` は時刻 `h` に確定し、
前処理をラウンド `(h, S]` に回してから、テキスト `w.drop S` を時刻 `S` から
実時間で走査できる（`PalPeg.StageMatcher` の `stageMatchH` を参照）。

段の分割そのものは `pal_prefix_iff_stage` を `W := S / 2` で使うだけなので、
必要なのは「オラクル対が満たすべき条件を各時刻で述べた版」である。 -/

/-- 各時刻ごとの段の正当性（`stageAnswer_correct` の点ごと版）。 -/
theorem stageAnswer_correct_at {w : List α} {W : ℕ} {ans flag : ℕ → Bool} {n : ℕ}
    (hm : ans n = true ↔ occursAt (w.take W).reverse (w.take n))
    (hf : flag n = true ↔ IsPal ((w.drop W).take (n - 2 * W)))
    (hW : 2 * W ≤ n) (hn : n ≤ w.length) :
    stageAnswer ans flag n = true ↔ IsPal (w.take n) := by
  rw [pal_prefix_iff_stage hW hn, stageAnswer, Bool.and_eq_true, hm, hf]

/-- **半分割版の主定理**：幅 `S` の段のオラクル対が、答える時刻 `n ∈ [2S, 4S)` において
分割点 `S / 2` の照合・中央条件を満たせば、制御器 `dyadicAnswer` は正しい。 -/
theorem dyadicAnswer_correctH [DecidableEq α] {w : List α}
    {oracles : ℕ → (ℕ → Bool) × (ℕ → Bool)}
    (hO : ∀ S n, 2 ≤ S → 2 * S ≤ n → n < 4 * S → n ≤ w.length →
      ((oracles S).1 n = true ↔ occursAt (w.take (S / 2)).reverse (w.take n)) ∧
        ((oracles S).2 n = true ↔ IsPal ((w.drop (S / 2)).take (n - 2 * (S / 2)))))
    (n : ℕ) (hn : n ≤ w.length) :
    dyadicAnswer w oracles n = true ↔ IsPal (w.take n) := by
  unfold dyadicAnswer
  split_ifs with h2 h4
  · exact iff_of_true rfl (pal_take_lt_two w h2)
  · rw [decide_eq_true_iff]
    exact (pal_take_two_three (by omega) (by omega) hn).symm
  · obtain ⟨hs1, hs2⟩ := stageOf_spec (n := n) (by omega)
    have hS2 : 2 ≤ stageOf n := by omega
    obtain ⟨hm, hf⟩ := hO (stageOf n) n hS2 hs1 hs2 hn
    exact stageAnswer_correct_at hm hf (by omega) hn

/-- 系（`α = Fin 2`）：半分割版でも読み終えた時刻の答えは `w ∈ PAL` と一致する。 -/
theorem dyadicAnswer_length_iff_mem_PALH {w : List (Fin 2)}
    {oracles : ℕ → (ℕ → Bool) × (ℕ → Bool)}
    (hO : ∀ S n, 2 ≤ S → 2 * S ≤ n → n < 4 * S → n ≤ w.length →
      ((oracles S).1 n = true ↔ occursAt (w.take (S / 2)).reverse (w.take n)) ∧
        ((oracles S).2 n = true ↔ IsPal ((w.drop (S / 2)).take (n - 2 * (S / 2))))) :
    dyadicAnswer w oracles w.length = true ↔ w ∈ PAL := by
  rw [dyadicAnswer_correctH hO w.length le_rfl, List.take_length]
  exact (mem_PAL_iff_isPal w).symm

/-! ## 小例による健全性チェック -/

example : liveStages 1 = [1] := by decide
example : liveStages 4 = [2, 4] := by decide
example : liveStages 7 = [2, 4] := by decide
example : liveStages 8 = [4, 8] := by decide
example : stageOf 7 ∈ liveStages 7 := by decide


end PalPeg
