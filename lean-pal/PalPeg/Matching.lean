import PalPeg.Words

/-!
# オンライン文字列照合の抽象状態と Galil の予測可能性

`List α`（`DecidableEq α`）上で、KMP 的なオンライン照合の**添字レベル**（実時間ではない）
の状態を定義し、以下を証明する。

* `matchState P T` — パターン `P` の接頭辞であって同時にテキスト `T` の接尾辞である最長のもの。
* `matchState_snoc_*` — 1 文字追加時の KMP ステップ（一致 / 失敗リンクを辿る / 0 に落ちる）。
* `predictability` — 失敗ステップ直後は、しばらく出現が起こり得ない（Galil 1975/1981）。
* `work_le` — 失敗リンクを辿る回数は、その「保証されたゼロ出力」の個数で押さえられる。
* `border_snapshot` — 現在の照合の境界は、`j - b` 文字前のテキスト接頭辞の照合に等しい。
-/

namespace PalPeg

universe u
variable {α : Type u} [DecidableEq α]

/-! ## 境界（border） -/

/-- `b` が `P` の境界（長さ `b` の接頭辞と接尾辞が一致）であること。 -/
def IsBorder (P : List α) (b : ℕ) : Prop :=
  b ≤ P.length ∧ P.take b = P.drop (P.length - b)

instance (P : List α) (b : ℕ) : Decidable (IsBorder P b) :=
  inferInstanceAs (Decidable (b ≤ P.length ∧ P.take b = P.drop (P.length - b)))

/-! ## 照合状態 -/

/-- `j` がテキスト `T` に対するパターン `P` の照合位置であること：
`P` の長さ `j` の接頭辞が `T` の接尾辞に一致する。 -/
def MatchAt (P T : List α) (j : ℕ) : Prop :=
  j ≤ P.length ∧ j ≤ T.length ∧ P.take j = T.drop (T.length - j)

instance (P T : List α) (j : ℕ) : Decidable (MatchAt P T j) :=
  inferInstanceAs (Decidable (j ≤ P.length ∧ j ≤ T.length ∧ P.take j = T.drop (T.length - j)))

omit [DecidableEq α] in
theorem matchAt_zero (P T : List α) : MatchAt P T 0 := by
  refine ⟨Nat.zero_le _, Nat.zero_le _, ?_⟩
  simp

omit [DecidableEq α] in
theorem matchAt_le_min {P T : List α} {j : ℕ} (h : MatchAt P T j) :
    j ≤ min P.length T.length :=
  le_min h.1 h.2.1

/-- オンライン照合の状態：`P` の接頭辞かつ `T` の接尾辞である最長のものの長さ。 -/
def matchState (P T : List α) : ℕ :=
  Nat.findGreatest (MatchAt P T) (min P.length T.length)

theorem matchState_spec (P T : List α) : MatchAt P T (matchState P T) :=
  Nat.findGreatest_spec (Nat.zero_le _) (matchAt_zero P T)

theorem matchState_le (P T : List α) : matchState P T ≤ min P.length T.length :=
  Nat.findGreatest_le _

theorem matchState_le_pattern (P T : List α) : matchState P T ≤ P.length :=
  (matchState_spec P T).1

theorem matchState_le_text (P T : List α) : matchState P T ≤ T.length :=
  (matchState_spec P T).2.1

/-- 最大性：任意の照合位置は `matchState` 以下。 -/
theorem MatchAt.le_matchState {P T : List α} {j : ℕ} (h : MatchAt P T j) :
    j ≤ matchState P T :=
  Nat.le_findGreatest (matchAt_le_min h) h

/-! ## 出現 -/

/-- `P` が `T` の末尾に出現すること。 -/
def occursAt (P T : List α) : Prop :=
  P.length ≤ T.length ∧ P = T.drop (T.length - P.length)

instance (P T : List α) : Decidable (occursAt P T) :=
  inferInstanceAs (Decidable (P.length ≤ T.length ∧ P = T.drop (T.length - P.length)))

theorem occursAt_iff_matchState (P T : List α) :
    occursAt P T ↔ matchState P T = P.length := by
  constructor
  · rintro ⟨hlen, heq⟩
    have hm : MatchAt P T P.length := ⟨le_rfl, hlen, by rw [List.take_length]; exact heq⟩
    exact le_antisymm (matchState_le_pattern P T) hm.le_matchState
  · intro h
    obtain ⟨_, hT, heq⟩ := matchState_spec P T
    rw [h] at hT heq
    rw [List.take_length] at heq
    exact ⟨hT, heq⟩

/-! ## 境界鎖（border chain） -/

/-- `P.take j` の境界すべて（`0` を含み `j` 自身は除く）を狭義単調減少に並べたもの。 -/
def borderChain (P : List α) (j : ℕ) : List ℕ :=
  ((List.range j).filter (fun b => decide (IsBorder (P.take j) b))).reverse

/-- 現在状態 `j` に対する最長の真の境界（存在しなければ `0`）。 -/
def longestBorder (P : List α) (j : ℕ) : ℕ := (borderChain P j).headD 0

theorem mem_borderChain {P : List α} {j b : ℕ} :
    b ∈ borderChain P j ↔ b < j ∧ IsBorder (P.take j) b := by
  simp [borderChain, List.mem_filter, List.mem_range]

/-- 境界鎖は狭義単調減少。 -/
theorem borderChain_sorted (P : List α) (j : ℕ) :
    (borderChain P j).Pairwise (· > ·) :=
  List.pairwise_reverse.mpr (List.Pairwise.filter _ List.pairwise_lt_range)

theorem borderChain_nodup (P : List α) (j : ℕ) : (borderChain P j).Nodup :=
  List.nodup_reverse.mpr (List.Nodup.filter _ List.nodup_range)

/-! ## 照合位置と境界の対応 -/

omit [DecidableEq α] in
/-- 現在の状態 `j` 以下の照合位置は、ちょうど `P.take j` の境界（および `j` 自身）。 -/
theorem matchAt_iff_isBorder {P T : List α} {j m : ℕ} (hj : MatchAt P T j) (hm : m ≤ j) :
    MatchAt P T m ↔ IsBorder (P.take j) m := by
  obtain ⟨hjP, hjT, hjE⟩ := hj
  have hlen : (P.take j).length = j := by simp only [List.length_take]; omega
  have hkey : (P.take j).take m = P.take m := by
    rw [List.take_take]; congr 1; omega
  have hkey2 : (P.take j).drop ((P.take j).length - m) = T.drop (T.length - m) := by
    rw [hlen, hjE, List.drop_drop]
    congr 1
    omega
  constructor
  · rintro ⟨_, _, h⟩
    exact ⟨by omega, by rw [hkey, hkey2]; exact h⟩
  · rintro ⟨_, h⟩
    rw [hkey, hkey2] at h
    exact ⟨by omega, by omega, h⟩

/-- 照合位置の完全な分類：現在状態そのものか、その境界鎖の要素。 -/
theorem matchAt_iff_eq_or_mem {P T : List α} {m : ℕ} :
    MatchAt P T m ↔ m = matchState P T ∨ m ∈ borderChain P (matchState P T) := by
  set j := matchState P T with hjdef
  have hj : MatchAt P T j := matchState_spec P T
  constructor
  · intro h
    have hmj : m ≤ j := h.le_matchState
    rcases Nat.eq_or_lt_of_le hmj with heq | hlt
    · exact Or.inl heq
    · exact Or.inr (mem_borderChain.mpr ⟨hlt, (matchAt_iff_isBorder hj hmj).mp h⟩)
  · rintro (rfl | hmem)
    · exact hj
    · obtain ⟨hlt, hb⟩ := mem_borderChain.mp hmem
      exact (matchAt_iff_isBorder hj (Nat.le_of_lt hlt)).mpr hb

/-! ## 1 文字追加（KMP ステップ） -/

omit [DecidableEq α] in
/-- **鍵となる補題**：`T ++ [a]` に対する長さ `m+1` の照合は、
`T` に対する長さ `m` の照合と `P[m] = a` に分解される。 -/
theorem matchAt_snoc_succ (P T : List α) (a : α) (m : ℕ) :
    MatchAt P (T ++ [a]) (m + 1) ↔ MatchAt P T m ∧ P[m]? = some a := by
  have hTl : (T ++ [a]).length = T.length + 1 := by simp
  constructor
  · rintro ⟨h1, h2, h3⟩
    rw [hTl] at h2 h3
    have hmP : m ≤ P.length := by omega
    have hmT : m ≤ T.length := by omega
    rw [show T.length + 1 - (m + 1) = T.length - m by omega,
      List.drop_append_of_le_length (by omega), List.take_add_one] at h3
    have hlen : (P.take m).length = (T.drop (T.length - m)).length := by
      simp only [List.length_take, List.length_drop]; omega
    obtain ⟨hA, hB⟩ := List.append_inj h3 hlen
    refine ⟨⟨hmP, hmT, hA⟩, ?_⟩
    cases hx : P[m]? with
    | none => rw [hx] at hB; simp at hB
    | some x => rw [hx] at hB; simp at hB; rw [hB]
  · rintro ⟨⟨hmP, hmT, hA⟩, ha⟩
    have hmlt : m < P.length := by
      have := List.getElem?_eq_some_iff.mp ha
      obtain ⟨h, _⟩ := this
      exact h
    refine ⟨by omega, by rw [hTl]; omega, ?_⟩
    rw [hTl, show T.length + 1 - (m + 1) = T.length - m by omega,
      List.drop_append_of_le_length (by omega), List.take_add_one, hA, ha]
    simp

/-- 上界：新状態は「旧状態 + 1」を超えない。 -/
theorem matchState_snoc_le (P T : List α) (a : α) :
    matchState P (T ++ [a]) ≤ matchState P T + 1 := by
  set s := matchState P (T ++ [a]) with hs
  cases hsz : s with
  | zero => omega
  | succ m =>
    have h : MatchAt P (T ++ [a]) (m + 1) := hsz ▸ matchState_spec P (T ++ [a])
    have := ((matchAt_snoc_succ P T a m).mp h).1.le_matchState
    omega

/-- **KMP ステップ（一致）**：`P[j] = a` なら状態は `j + 1`。 -/
theorem matchState_snoc_hit (P T : List α) (a : α)
    (ha : P[matchState P T]? = some a) :
    matchState P (T ++ [a]) = matchState P T + 1 := by
  refine le_antisymm (matchState_snoc_le P T a) ?_
  exact MatchAt.le_matchState ((matchAt_snoc_succ P T a _).mpr ⟨matchState_spec P T, ha⟩)

/-- **KMP ステップ（失敗して境界へ）**：`P[j] ≠ a` で、`P[b] = a` となる境界 `b` の中で
`b` が最大なら、新状態は `b + 1`。 -/
theorem matchState_snoc_miss (P T : List α) (a : α)
    (ha : P[matchState P T]? ≠ some a)
    {b : ℕ} (hb : b ∈ borderChain P (matchState P T)) (hba : P[b]? = some a)
    (hmax : ∀ c ∈ borderChain P (matchState P T), P[c]? = some a → c ≤ b) :
    matchState P (T ++ [a]) = b + 1 := by
  have hbM : MatchAt P T b := matchAt_iff_eq_or_mem.mpr (Or.inr hb)
  have hlow : b + 1 ≤ matchState P (T ++ [a]) :=
    MatchAt.le_matchState ((matchAt_snoc_succ P T a b).mpr ⟨hbM, hba⟩)
  refine le_antisymm ?_ hlow
  set s := matchState P (T ++ [a]) with hs
  cases hsz : s with
  | zero => omega
  | succ m =>
    have h : MatchAt P (T ++ [a]) (m + 1) := hsz ▸ matchState_spec P (T ++ [a])
    obtain ⟨hmM, hma⟩ := (matchAt_snoc_succ P T a m).mp h
    rcases matchAt_iff_eq_or_mem.mp hmM with heq | hmem
    · exact absurd (heq ▸ hma) ha
    · have := hmax m hmem hma
      omega

/-- **KMP ステップ（全滅）**：`P[j] ≠ a` かつどの境界 `b` でも `P[b] ≠ a` なら、新状態は `0`。 -/
theorem matchState_snoc_zero (P T : List α) (a : α)
    (ha : P[matchState P T]? ≠ some a)
    (hnone : ∀ b ∈ borderChain P (matchState P T), P[b]? ≠ some a) :
    matchState P (T ++ [a]) = 0 := by
  by_contra hne
  obtain ⟨m, hm⟩ : ∃ m, matchState P (T ++ [a]) = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos
    (Nat.pos_of_ne_zero hne)).symm⟩
  have h : MatchAt P (T ++ [a]) (m + 1) := hm ▸ matchState_spec P (T ++ [a])
  obtain ⟨hmM, hma⟩ := (matchAt_snoc_succ P T a m).mp h
  rcases matchAt_iff_eq_or_mem.mp hmM with heq | hmem
  · exact ha (heq ▸ hma)
  · exact hnone m hmem hma

/-! ## Galil の予測可能性 -/

omit [DecidableEq α] in
/-- 出現が起きたなら、テキストの接頭辞側にも対応する照合が存在する。 -/
theorem matchAt_of_occursAt_append {P T T' : List α} (h : occursAt P (T ++ T'))
    (hd : T'.length ≤ P.length) : MatchAt P T (P.length - T'.length) := by
  obtain ⟨hlen, heq⟩ := h
  simp only [List.length_append] at hlen heq
  set n := T.length
  set d := T'.length
  set L := P.length with hL
  have hstart : n + d - L ≤ n := by omega
  rw [List.drop_append_of_le_length hstart] at heq
  have hdl : (T.drop (n + d - L)).length = L - d := by
    simp only [List.length_drop]; omega
  refine ⟨by omega, by omega, ?_⟩
  have : P.take (L - d) = (T.drop (n + d - L) ++ T').take (L - d) := by rw [← heq]
  rw [this, List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  congr 1
  omega

/-- **予測可能性（Galil）**：現在状態が `j` のとき、残り `P.length - j` 文字未満では
`P` の出現は起こり得ない。 -/
theorem predictability (P T T' : List α)
    (h : T'.length + matchState P T < P.length) : ¬ occursAt P (T ++ T') := by
  intro hocc
  have hd : T'.length ≤ P.length := by omega
  have := (matchAt_of_occursAt_append hocc hd).le_matchState
  omega

/-- ステップ形：1 文字読んだ直後の状態を `s` とすると、そこから `P.length - s - 1` 文字の間
出現は起こらない。 -/
theorem predictability_step (P T : List α) (a : α) (T' : List α)
    (h : T'.length < P.length - matchState P (T ++ [a])) :
    ¬ occursAt P (T ++ [a] ++ T') :=
  predictability P (T ++ [a]) T' (by omega)

/-! ## 仕事量の上界 -/

/-- 失敗ステップの仕事量：生き残った境界 `b` より真に大きい境界の個数
（＝失敗リンクを辿って失敗した回数）。 -/
def stepWork (P : List α) (j b : ℕ) : ℕ :=
  ((borderChain P j).filter (fun c => decide (b < c))).length

theorem stepWork_le_sub (P : List α) (j b : ℕ) : stepWork P j b ≤ j - b - 1 := by
  set L := (borderChain P j).filter (fun c => decide (b < c)) with hL
  have hnd : L.Nodup := List.Nodup.filter _ (borderChain_nodup P j)
  have hsub : L.toFinset ⊆ Finset.Ioo b j := by
    intro c hc
    rw [List.mem_toFinset, hL, List.mem_filter] at hc
    obtain ⟨hc1, hc2⟩ := hc
    exact Finset.mem_Ioo.mpr ⟨by simpa using hc2, (mem_borderChain.mp hc1).1⟩
  calc L.length = L.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
    _ ≤ (Finset.Ioo b j).card := Finset.card_le_card hsub
    _ = j - b - 1 := Nat.card_Ioo b j

/-- **仕事量 ≤ 保証されたゼロ出力数**：新状態を `s = b + 1` とすると、
失敗リンクを辿った回数は `P.length - s` 以下。 -/
theorem work_le {P : List α} {j b : ℕ} (hj : j ≤ P.length) :
    stepWork P j b ≤ P.length - (b + 1) :=
  le_trans (stepWork_le_sub P j b) (by omega)

/-! ## スナップショット補題 -/

/-- **境界スナップショット**：現在の照合 `j` の境界 `b` は、`j - b` 文字前の
テキスト接頭辞に対する照合そのもの。 -/
theorem border_snapshot {P T : List α} {j b : ℕ} (hj : matchState P T = j)
    (hb : IsBorder (P.take j) b) :
    P.take b = (T.take (T.length - (j - b))).drop (T.length - j) := by
  have hjm : MatchAt P T j := hj ▸ matchState_spec P T
  obtain ⟨hjP, hjT, hjE⟩ := hjm
  have hlen : (P.take j).length = j := by simp only [List.length_take]; omega
  have hbj : b ≤ j := by have h1 := hb.1; omega
  rw [List.drop_take, ← hjE, List.take_take]
  congr 1
  omega

/-! ## 小例による健全性チェック -/

example : matchState [0, 0, 1] [0, 0, 0] = 2 := by decide
example : matchState ([0, 0, 1] : List ℕ) [] = 0 := by decide
example : matchState [0, 0, 1] [0, 0, 0, 1] = 3 := by decide
example : occursAt [0, 0, 1] [0, 0, 0, 1] := by decide
example : ¬ occursAt ([0, 0, 1] : List ℕ) [0, 0, 0] := by decide
example : borderChain ([0, 0, 1] : List ℕ) 2 = [1, 0] := by decide
example : borderChain ([0, 0, 1] : List ℕ) 3 = [0] := by decide
example : longestBorder ([0, 0, 1] : List ℕ) 2 = 1 := by decide
example : stepWork ([0, 0, 1] : List ℕ) 2 0 = 1 := by decide

end PalPeg
