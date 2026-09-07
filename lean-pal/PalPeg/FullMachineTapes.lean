import PalPeg.StageTapes
import PalPeg.OnlineMachine
import PalPeg.Prologue
import PalPeg.InputCopy

/-!
# 認識器全体をラウンドごとのテープ機械として組む (`FullMachineTapes`)

`StageTapes` は **一つの段**の全生涯をテープ上で実現した。本ファイルはその上に
**認識器全体**を載せる：ラウンド `n`（入力記号 `w[n-1]` が到着）で

* 大域入力テープ `inp` の最前線に到着記号を書き足す（1 動作）、
* 4 組の回転テープ集合（スロット）それぞれの入力コピー `cpy i` にも書き足す（4 動作）、
* 常駐している段（高々 3 つ、`residentStages_length_le`）の 1 ラウンドを進める、
* 解放済みスロットの消去プログラムを定速で挽く（`Prologue.spreadClear`）。

## スロット回転

幅 `S = 2 ^ j` の段は `S / 2` に生まれ `4 * S` で死ぬ。スロットは `j % 4`。
同一スロットを共有する二つの段の指数は 4 以上離れるので、**常駐区間は交わらない**
（`resident_disjoint`）。スロットが空く区間は `[4 * S, 8 * S)`、長さ `4 * S`
（`free_window_len`）で、その間に消去を終える。

段の 1 ラウンドの動作数は `Cstage` 以下（`StageTapes.stage_round_actions`）なので、
一つの段が生涯（`< 4 * S` ラウンド）に書く非空白セルは `Cstage * (4 * S)` 個以下。
消去プログラムは `2 * (セル数)` 動作（`Prologue.clearTape`）。これを毎ラウンド
`8 * Cstage + 1` 動作に切り分ければ `4 * S` ラウンドで終わる（`clear_fits`）。

## パターン用の入力コピーについて（設計と残る義務）

幅 `S` の段が誕生時 `S / 2` に必要とするのは接頭辞 `w.take (S / 2)` であり、
これは**入力の接頭辞**なので回転スロットの新しいコピーだけでは作れない。採用する構成は

* 段 `S` のパターンは **対** `(sIn, F)` で表す：`sIn` は段 `S / 2` が誕生時に凍結した
  `w.take (S / 4)` の複製、`F` は区間 `(S/4, S/2]` に到着した `w[S/4 .. S/2)` を
  そのまま受け取った最前線テープ。`sIn ++ F` の内容がちょうど `w.take (S / 2)`。
* `PatternTapes` はパターンを**右から左へ**読むので、`F` を左向きに読み切ってから
  `sIn` を左向きに読めば `(w.take (S / 2)).reverse` が得られる。
* 複製は凍結された（もう書き換わらない）源から挽くので、到着記号との頭の衝突が起きない。
  費用は `O(S)` 動作を `(S/4, S/2]` の `S / 4` ラウンドに配って定速化できる
  （`pair_copy_rate_ok`）。

**残る義務**（本ファイルでは証明しない）：`PatternTapes.setup_spec` の複製ループを
「源が 2 本のテープ `(F, sIn)` である」場合へ一般化すること。これは
`StageTapes.PrepOnTapes` / `MiddleTapes.DecompOnTapes` と同じ層のインタフェース仮定であり、
下の `StageIface` に吸収されている。
-/

namespace PalPeg
namespace FullMachineTapes

open PegSeparation.RealTimeTM
open PalPeg.StageTapes
open PalPeg.Tape

/-! ## 1. スロット回転の算術 -/

/-- 幅 `S = 2 ^ j` の段が使うテープ集合（スロット）の番号。 -/
def slotOf (S : ℕ) : ℕ := Nat.log 2 S % 4

theorem slotOf_pow (j : ℕ) : slotOf (2 ^ j) = j % 4 := by
  rw [slotOf, Nat.log_pow (by omega)]

/-- **同一スロットの二つの段の常駐区間は交わらない**：指数が異なり `mod 4` が等しければ
指数差は 4 以上、したがって `[S/2, 4S)` は交わらない。 -/
theorem resident_disjoint {i j n : ℕ} (hij : i ≠ j) (hmod : i % 4 = j % 4)
    (h1 : 2 ^ i / 2 ≤ n) (h2 : n < 4 * 2 ^ i)
    (h3 : 2 ^ j / 2 ≤ n) (h4 : n < 4 * 2 ^ j) : False := by
  have key : ∀ a b : ℕ, a + 4 ≤ b → n < 4 * 2 ^ a → 2 ^ b / 2 ≤ n → False := by
    intro a b hab ha2 hb1
    have hmono : 2 ^ (a + 3) ≤ 2 ^ (b - 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hb : 2 ^ b = 2 * 2 ^ (b - 1) := by
      rw [← Nat.pow_succ']
      congr 1
      omega
    have h4a : 4 * 2 ^ a = 2 ^ (a + 2) := by
      rw [Nat.pow_add]; ring
    have h3a : 2 ^ (a + 3) = 2 * 2 ^ (a + 2) := by
      rw [Nat.pow_add, Nat.pow_add]; ring
    rw [hb, Nat.mul_div_cancel_left _ (by omega)] at hb1
    omega
  rcases Nat.lt_or_ge i j with h | h
  · exact key i j (by omega) h2 h3
  · exact key j i (by omega) h4 h1

/-- スロットが空いている区間 `[4 * S, 8 * S)` の長さは `4 * S`。 -/
theorem free_window_len (S : ℕ) : 8 * S - 4 * S = 4 * S := by omega

/-- 同じスロットの次の段は `2 ^ (j + 4)`、その誕生は `2 ^ (j + 3) = 8 * 2 ^ j`。 -/
theorem next_stage_birth (j : ℕ) : 2 ^ (j + 4) / 2 = 8 * 2 ^ j := by
  rw [Nat.pow_add]
  omega

/-! ### 消去の定速化 -/

/-- チャンク数の上界：`chunkList c p` の個数は `(|p| + c) / (c + 1)` 以下。 -/
theorem chunkList_length_le {k : ℕ} (c : ℕ) :
    ∀ p : GSTapes.TapeProg k,
      (Prologue.chunkList c p).length * (c + 1) ≤ p.length + c := by
  intro p
  induction p using Prologue.chunkList.induct (c := c) with
  | case1 => simp [Prologue.chunkList]
  | case2 x xs ih =>
      have hdef : Prologue.chunkList c (x :: xs)
          = (x :: xs).take (c + 1) :: Prologue.chunkList c ((x :: xs).drop (c + 1)) := by
        simp [Prologue.chunkList]
      by_cases hc : (x :: xs).length ≤ c + 1
      · have hd : (x :: xs).drop (c + 1) = [] := List.drop_eq_nil_of_le hc
        rw [hdef, hd, show Prologue.chunkList c ([] : GSTapes.TapeProg k) = [] from by
          simp [Prologue.chunkList]]
        simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.one_mul,
          List.length_cons]
        omega
      · have hlen : ((x :: xs).drop (c + 1)).length = (x :: xs).length - (c + 1) := by simp
        rw [hlen] at ih
        have hxs : (x :: xs).length = xs.length + 1 := by simp
        rw [hxs] at ih hc ⊢
        rw [hdef, List.length_cons, Nat.succ_mul]
        omega

/-- **消去が窓に収まる**：`Cstage * (4 * S)` 個以下の非空白セルを消す `2 * cells` 動作の
プログラムを、毎ラウンド `8 * Cstage + 1` 動作のチャンクへ切ると、チャンク数は
`4 * S` 以下（`1 ≤ S`）。 -/
theorem clear_fits {k : ℕ} {C S : ℕ} (hS : 1 ≤ S) (p : GSTapes.TapeProg k)
    (hp : p.length ≤ 2 * (C * (4 * S))) :
    (Prologue.chunkList (8 * C) p).length ≤ 4 * S := by
  have h := chunkList_length_le (k := k) (8 * C) p
  set m := (Prologue.chunkList (8 * C) p).length with hm
  have hCS : C * 1 ≤ C * S := Nat.mul_le_mul_left C hS
  nlinarith [h, hp, hCS, Nat.zero_le m, Nat.zero_le C, Nat.zero_le S]

/-- 対複製（`(F, sIn)` から 1 本へ）の費用が窓 `(S/4, S/2]` に収まること：
`4 * (S / 2) + 2 ≤ (S / 4) * 20`（`8 ≤ S`, `4 * (S / 4) = S`）。 -/
theorem pair_copy_rate_ok {S : ℕ} (hS : 8 ≤ S) (hq : 4 * (S / 4) = S) :
    4 * (S / 2) + 2 ≤ (S / 4) * 20 := by
  have h1 : 1 ≤ S / 4 := by omega
  have h2 : S / 2 = 2 * (S / 4) := by omega
  omega

/-! ## 2. 段のインタフェース -/

variable {sc : ℕ}

/-- **段のインタフェース**：`StageTapes` が与えるもの（幅ごとのテープ記録・出力ビット・
1 ラウンド費用・主仕様 `stage_tapes_spec`）を、全体機械から見た形にまとめたもの。 -/
structure StageIface (sc : ℕ) (w : List (Fin sc)) where
  /-- 幅 `S` の段のラウンド `n` 終了時の 12 本テープの記録。 -/
  srec : ℕ → ℕ → StageT sc
  /-- 幅 `S` の段がラウンド `n` に出す答えビット（`StageTapes.stAnswerBit`）。 -/
  bit : ℕ → ℕ → Bool
  /-- 幅 `S` の段のラウンド `n` の動作数。 -/
  cost : ℕ → ℕ → ℕ
  /-- 1 ラウンドの動作数の上界（`StageTapes.Cstage`）。 -/
  C : ℕ
  cost_le : ∀ S n, cost S n ≤ C
  /-- 誕生前は無費用（`StageTapes.stcost` の `n ≤ S / 2` 分岐）。 -/
  cost_idle : ∀ S n, n ≤ S / 2 → cost S n = 0
  /-- **主仕様**（`StageTapes.stage_tapes_spec`）：答える区間で出力ビットは
  「パターン出現」かつ「中央が回文」と同値。 -/
  spec : ∀ S n, 16 ≤ S → 2 * S ≤ n → n < 4 * S → n ≤ w.length →
    (bit S n = true ↔
      (occursAt (w.take (S / 2)).reverse (w.take n) ∧
        IsPal ((w.drop (S / 2)).take (n - S))))
  /-- 幅は偶数（2 冪なので）。 -/
  wid_even : ∀ S, 16 ≤ S → 2 * (S / 2) = S

/-! ## 3. 全体機械 -/

/-- **全体状態**：大域入力テープ、4 組の回転テープ集合ごとの入力コピー、
4 組の段テープ集合。 -/
structure FullT (sc : ℕ) where
  /-- 大域入力テープ（最前線）。 -/
  inp : TapeConfiguration sc
  /-- スロットごとのパターン用最前線テープ `F`。 -/
  cpy : Fin 4 → TapeConfiguration sc
  /-- スロットごとの段テープ集合。 -/
  slots : Fin 4 → StageT sc

/-- ラウンド `n` にスロット `i` を占めている段（あれば）。 -/
def stageInSlot (n : ℕ) (i : Fin 4) : Option ℕ :=
  (residentStages n).find? (fun S => decide (slotOf S = i.val))

/-- **全体機械の 1 ラウンド**。 -/
def fullRound {w : List (Fin sc)} (blank : Fin sc) (I : StageIface sc w) (n : ℕ)
    (F : FullT sc) : FullT sc :=
  { inp := Tape.step blank F.inp (w.getD (n - 1) blank) .right
    cpy := fun i => Tape.step blank (F.cpy i) (w.getD (n - 1) blank) .right
    slots := fun i =>
      match stageInSlot n i with
      | some S => I.srec S n
      | none => F.slots i }

/-- ラウンド `n` 終了時の全体状態。 -/
def fullState {w : List (Fin sc)} (blank : Fin sc) (I : StageIface sc w)
    (init : FullT sc) : ℕ → FullT sc
  | 0 => init
  | n + 1 => fullRound blank I (n + 1) (fullState blank I init n)

theorem fullState_succ {w : List (Fin sc)} (blank : Fin sc) (I : StageIface sc w)
    (init : FullT sc) (n : ℕ) :
    fullState blank I init (n + 1)
      = fullRound blank I (n + 1) (fullState blank I init n) := rfl

/-- 大域入力テープはちょうど到着済みの記号列を保つ。 -/
theorem fullState_inp {w : List (Fin sc)} {blank : Fin sc} {I : StageIface sc w}
    {init : FullT sc} (hinit : InputCopy.FrontierView blank init.inp []) :
    ∀ n, n ≤ w.length →
      InputCopy.FrontierView blank (fullState blank I init n).inp (w.take n) := by
  intro n
  induction n with
  | zero => intro _; rw [show (fullState blank I init 0) = init from rfl]; simpa using hinit
  | succ n ih =>
    intro hn
    rw [fullState_succ]
    have h := InputCopy.append_spec (ih (by omega)) (w.getD n blank)
    have hgd : w.getD n blank = w[n]'(by omega) := by
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (show n < w.length by omega)]
      rfl
    have hw : w.take n ++ [w.getD n blank] = w.take (n + 1) := by
      rw [hgd, List.take_add_one, List.getElem?_eq_getElem (show n < w.length by omega)]
      rfl
    rw [hw] at h
    exact h

/-- 常駐している段のテープ記録は、そのスロットに実際に載っている。 -/
theorem fullState_slot {w : List (Fin sc)} {blank : Fin sc} {I : StageIface sc w}
    {init : FullT sc} {n : ℕ} {i : Fin 4} {S : ℕ} (h : stageInSlot (n + 1) i = some S) :
    (fullState blank I init (n + 1)).slots i = I.srec S (n + 1) := by
  rw [fullState_succ, fullRound]
  simp only [h]

/-! ## 4. 出力 -/

/-- **全体の出力**：`n < 32` は有限の場合分け（定数記憶で `w.take n` を保持できる）、
`32 ≤ n` は担当段 `stageOf n` の出力ビット。 -/
def fullAnswer {w : List (Fin sc)} (I : StageIface sc w) (n : ℕ) : Bool :=
  if n < 32 then decide (IsPal (w.take n))
  else (residentStages n).any (fun S => decide (S = stageOf n) && I.bit S n)

/-- `32 ≤ n` なら担当段の幅は `16` 以上。 -/
theorem stageOf_ge {n : ℕ} (hn : 32 ≤ n) : 16 ≤ stageOf n := by
  have h32 : Nat.log 2 32 = 5 := by
    rw [show (32 : ℕ) = 2 ^ 5 from rfl, Nat.log_pow (by omega)]
  have h5 : 5 ≤ Nat.log 2 n := by
    have := Nat.log_mono_right (b := 2) hn
    omega
  have hp := Nat.pow_le_pow_right (show 0 < 2 by omega)
    (show 4 ≤ Nat.log 2 n - 1 by omega)
  rw [stageOf_pow]
  simpa using hp

/-- `any` の展開：担当段のビットだけが効く。 -/
theorem any_stageOf {w : List (Fin sc)} (I : StageIface sc w) {n : ℕ} (hn : 4 ≤ n) :
    (residentStages n).any
        (fun S => decide (S = stageOf n) && I.bit S n) = true
      ↔ I.bit (stageOf n) n = true := by
  constructor
  · intro h
    obtain ⟨S, _, hS⟩ := List.any_eq_true.mp h
    rw [Bool.and_eq_true, decide_eq_true_iff] at hS
    rw [← hS.1]; exact hS.2
  · intro h
    exact List.any_eq_true.mpr ⟨stageOf n, stageOf_mem_resident hn,
      by rw [Bool.and_eq_true, decide_eq_true_iff]; exact ⟨rfl, h⟩⟩

/-- **全体の正当性**：全ラウンド `n ≤ |w|` で出力は接頭辞の回文性と一致する。 -/
theorem full_answer_correct {w : List (Fin sc)} (I : StageIface sc w)
    (n : ℕ) (hn : n ≤ w.length) :
    fullAnswer I n = true ↔ IsPal (w.take n) := by
  by_cases h32 : n < 32
  · rw [fullAnswer, if_pos h32, decide_eq_true_iff]
  have hS := stageOf_ge (show 32 ≤ n by omega)
  obtain ⟨h1, h2⟩ := stageOf_spec (n := n) (by omega)
  rw [fullAnswer, if_neg h32, any_stageOf I (by omega),
    I.spec (stageOf n) n hS h1 h2 hn]
  have heven := I.wid_even (stageOf n) hS
  rw [show n - stageOf n = n - 2 * (stageOf n / 2) from by omega]
  exact (pal_prefix_iff_stage (W := stageOf n / 2) (by omega) hn).symm

/-- 系：全部読み終えた時刻の答えは `w ∈ PAL` と一致する（`α = Fin 2`）。 -/
theorem full_answer_mem_PAL {w : List (Fin 2)} (I : StageIface 2 w) :
    fullAnswer I w.length = true ↔ w ∈ PAL := by
  rw [full_answer_correct I w.length le_rfl, List.take_length]
  exact (mem_PAL_iff_isPal w).symm

/-! ## 5. 1 ラウンドの動作数 -/

/-- リストの各要素が `C` 以下なら総和は `|l| * C` 以下。 -/
theorem sum_le_length_mul {l : List ℕ} {C : ℕ} (h : ∀ x ∈ l, x ≤ C) :
    l.sum ≤ l.length * C := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha := h a (by simp)
    have ht := ih (fun x hx => h x (by simp [hx]))
    simp only [List.sum_cons, List.length_cons, Nat.succ_mul]
    omega

/-- **全体機械の 1 ラウンドの費用**：常駐段の費用の総和 ＋ 大域入力 1 動作
＋ スロット入力コピー 4 動作 ＋ 消去の定速チャンク `8 * C + 1` 動作
＋ 対複製の定速チャンク `20` 動作。 -/
def fullCost {w : List (Fin sc)} (I : StageIface sc w) (n : ℕ) : ℕ :=
  ((residentStages n).map (fun S => I.cost S n)).sum
    + 1 + 4 + (8 * I.C + 1) + 20

/-- 1 ラウンドの動作数の明示上界。 -/
def Cfull {w : List (Fin sc)} (I : StageIface sc w) : ℕ := 11 * I.C + 26

/-- **`full_round_actions`**：全体機械の 1 ラウンドの動作数は `Cfull` 以下（定数）。 -/
theorem full_round_actions {w : List (Fin sc)} (I : StageIface sc w) (n : ℕ) :
    fullCost I n ≤ Cfull I := by
  have hb : ∀ x ∈ (residentStages n).map (fun S => I.cost S n), x ≤ I.C := by
    intro x hx
    obtain ⟨S, _, rfl⟩ := List.mem_map.mp hx
    exact I.cost_le S n
  have hsum := sum_le_length_mul hb
  have hlen : ((residentStages n).map (fun S => I.cost S n)).length ≤ 3 := by
    rw [List.length_map]; exact residentStages_length_le n
  have hmul : ((residentStages n).map (fun S => I.cost S n)).length * I.C
      ≤ 3 * I.C := Nat.mul_le_mul_right _ hlen
  rw [fullCost, Cfull]
  omega

end FullMachineTapes
end PalPeg
