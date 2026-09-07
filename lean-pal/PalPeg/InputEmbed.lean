import PalPeg.FullMachineTapes
import PalPeg.StageIfaceInstance
import PalPeg.Words
import PalPeg.PassSumRelabel
import PalPeg.PassSumGen

/-!
# 入力アルファベットの埋め込み (`InputEmbed`)

`ASSEMBLY_PLAN.md` のギャップ：`StageIfaceInstance.full_answer_mem_PAL_of` は
`sc = 2`（機械アルファベット＝入力アルファベット）で述べられているが、機械は
`blank, mark, leftSym, endSym, startSym, one, zero` という 7 個の特殊記号を
**入力記号と別に**必要とする。`Fin 2` の上ではその仮定
（`mark ≠ blank`, `leftSym ∉ w`, `endSym ∉ w`, `one ≠ zero`, …）は同時には
充たせない（`w` が両方の記号を含めば `leftSym ∉ w` は偽）ので、あの定理は**空虚**である
（`sc_two_hypotheses_unsatisfiable` を参照）。

修正：入力語は `input : List (Fin 2)`、テープ上の語は `w := input.map ι`
（`ι : Fin 2 ↪ Fin sc` は像が特殊記号を避ける埋め込み）とする。本ファイルは

1. `IsPal`・`occursAt`・`take/drop/reverse` が単射な `map` と可換であること、
2. `PAL` との橋渡し `(input.take n) ∈ PAL ↔ IsPal ((input.map ι).take n)`、
3. 特殊記号の仮定 `leftSym ∉ input.map ι` 等が `leftSym ∉ Set.range ι` から従うこと、
4. 上の 3 つを使って `FullMachineTapes.full_answer_correct` /
   `StageIfaceInstance.stageIface` を **入力アルファベット `Fin 2`** の言葉で
   述べ直した `full_answer_mem_PAL_embed` / `full_answer_mem_PAL_of_embed`、
5. 具体的な記号割り当て `symbols9`（`sc = 9`＝入力 2 記号＋特殊 7 記号）

を与える。
-/

set_option autoImplicit false

namespace PalPeg
namespace InputEmbed

open PegSeparation.RealTimeTM

/-! ## 0. `sc = 2` が空虚であること -/

/-- **ギャップの明示**：`Fin 2` の上では、特殊記号の仮定は同時には充たせない。
`w` が両方の入力記号を含む（`0 ∈ w` かつ `1 ∈ w`）なら、どんな `leftSym` でも
`leftSym ∈ w`。 -/
theorem sc_two_hypotheses_unsatisfiable {w : List (Fin 2)} (h0 : (0 : Fin 2) ∈ w)
    (h1 : (1 : Fin 2) ∈ w) (leftSym : Fin 2) : leftSym ∈ w := by
  fin_cases leftSym
  · exact h0
  · exact h1

/-! ## 1. `map` と可換な操作 -/

section Map

variable {α β : Type} {f : α → β}

theorem map_take (l : List α) (n : ℕ) : (l.map f).take n = (l.take n).map f :=
  (List.map_take).symm

theorem map_drop (l : List α) (n : ℕ) : (l.map f).drop n = (l.drop n).map f :=
  (List.map_drop).symm

theorem map_reverse (l : List α) : (l.map f).reverse = l.reverse.map f :=
  (List.map_reverse).symm

/-- 単射な `map` の下で回文性は不変。 -/
theorem isPal_map (hf : Function.Injective f) (l : List α) :
    IsPal (l.map f) ↔ IsPal l := by
  unfold IsPal
  rw [map_reverse]
  exact ⟨fun h => List.map_injective_iff.mpr hf h, fun h => congrArg (List.map f) h⟩

/-- 単射な `map` の下で「末尾に出現する」も不変。 -/
theorem occursAt_map (hf : Function.Injective f) (P T : List α) :
    occursAt (P.map f) (T.map f) ↔ occursAt P T := by
  unfold occursAt
  rw [List.length_map, List.length_map, map_drop]
  exact and_congr_right fun _ =>
    ⟨fun h => List.map_injective_iff.mpr hf h, fun h => congrArg (List.map f) h⟩

end Map

/-! ## 2. `PAL` との橋渡し -/

variable {sc : ℕ}

/-- **橋渡し**：`Fin 2` 上の入力接頭辞の `PAL` 所属は、埋め込んだ語の回文性と同値。 -/
theorem mem_PAL_iff_isPal_map (ι : Fin 2 ↪ Fin sc) (input : List (Fin 2)) (n : ℕ) :
    (input.take n) ∈ PAL ↔ IsPal ((input.map ι).take n) := by
  rw [map_take, isPal_map ι.injective]
  exact mem_PAL_iff_isPal _

/-! ## 3. 特殊記号が像に入らないこと -/

/-- `c` が `ι` の像に入らないなら、`c` は `input.map ι` に現れない。 -/
theorem notMem_map_of_notMem_range {c : Fin sc} {ι : Fin 2 ↪ Fin sc}
    (h : c ∉ Set.range ι) (input : List (Fin 2)) : c ∉ input.map ι := by
  intro hc
  obtain ⟨a, -, ha⟩ := List.mem_map.mp hc
  exact h ⟨a, ha⟩

/-- `hι`（像が特殊記号をすべて避ける）からの取り出し。 -/
theorem notMem_range_of_hi {ι : Fin 2 ↪ Fin sc} {c : Fin sc}
    {Sp : Set (Fin sc)} (hι : ∀ i, ι i ∉ Sp) (hc : c ∈ Sp) : c ∉ Set.range ι := by
  rintro ⟨i, rfl⟩
  exact hι i hc

/-! ## 4. 語が像に収まることと `PassPeriodSum` -/

/-- `input.map ι` の記号は `ι 0` と `ι 1` のいずれか。 -/
theorem mem_map_cases (ι : Fin 2 ↪ Fin sc) (input : List (Fin 2)) :
    ∀ c ∈ input.map ι, c = ι 0 ∨ c = ι 1 := by
  intro c hc
  obtain ⟨a, -, rfl⟩ := List.mem_map.mp hc
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- **像に収まる語に対する周期和の上界**：`EndToEnd2.PassPeriodSum 8 C₁` から
`PassSumRelabel.passPeriodSum_of_subset` で得られる。
（注意：`StageIfaceInstance.stageIface` の `hsum` は `∀ y : List (Fin sc)` という
全称の形なので、`sc ≥ 3` ではこの補題だけからは埋まらない。そちらは
`PassSumGen.hsum_of_consumption`（消費量補題の任意アルファベット版）で埋める：
`full_answer_mem_PAL_of_embed'` を見よ。） -/
theorem passPeriodSum_map {C₁ : ℕ} (hsum₂ : EndToEnd2.PassPeriodSum 8 C₁)
    (ι : Fin 2 ↪ Fin sc) (input : List (Fin 2)) (b s : ℕ) :
    stripLoop2Periods (input.map ι) 8 b ((input.map ι).length + 1) s ≤ C₁ * b :=
  passPeriodSum_of_subset hsum₂ ι (input.map ι) (mem_map_cases ι input) b s

/-- **像に収まる語なら記号は `ι 0` か `ι 1`**（`Set.range` 版）。 -/
theorem mem_range_cases {ι : Fin 2 ↪ Fin sc} {c : Fin sc} (hc : c ∈ Set.range ι) :
    c = ι 0 ∨ c = ι 1 := by
  obtain ⟨i, rfl⟩ := hc
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- **弱められた `hsum` の充足（`Set.range ι` 版）**：`EndToEnd2.PassPeriodSum 8 C₁` から、
記号が `ι` の像に収まる**すべての** `y` について周期和の上界が従う。
`StageTapes.PrepOnTapes.len_le`（したがって `PrepInstance.prepInstance` /
`StageIfaceInstance.stageIface`）の `hsum` を
`∀ y, (∀ c ∈ y, c ∈ A) → …` の形に弱めれば、`A := (· ∈ Set.range ι)` で
これがそのまま埋める。 -/
theorem hsum_of_mem_range {C₁ : ℕ} (hsum₂ : EndToEnd2.PassPeriodSum 8 C₁)
    (ι : Fin 2 ↪ Fin sc) (y : List (Fin sc)) (hy : ∀ c ∈ y, c ∈ Set.range ι) (b s : ℕ) :
    stripLoop2Periods y 8 b (y.length + 1) s ≤ C₁ * b :=
  passPeriodSum_of_subset hsum₂ ι y (fun c hc => mem_range_cases (hy c hc)) b s

/-- **弱められた `hsum` の充足（`w = input.map ι` 版）**：記号が実際の入力語
`input.map ι` に現れるものだけからなる `y` について。 -/
theorem hsum_of_mem_word {C₁ : ℕ} (hsum₂ : EndToEnd2.PassPeriodSum 8 C₁)
    (ι : Fin 2 ↪ Fin sc) (input : List (Fin 2)) (y : List (Fin sc))
    (hy : ∀ c ∈ y, c ∈ input.map ι) (b s : ℕ) :
    stripLoop2Periods y 8 b (y.length + 1) s ≤ C₁ * b :=
  passPeriodSum_of_subset hsum₂ ι y
    (fun c hc => mem_map_cases ι input c (hy c hc)) b s

/-! ## 5. 主定理 -/

/-- **全体の出力の正当性（埋め込み版・インタフェース一般）**：
`FullMachineTapes.full_answer_correct` を `w = input.map ι` に適用し、
結論を入力語 `input` の言葉（`PAL` 所属）へ翻訳したもの。
添字の付け方（`n ≤ |input|`、`n < 32` は素朴表、`32 ≤ n` は担当段）は
`full_answer_correct` のものそのままである。 -/
theorem full_answer_mem_PAL_embed (ι : Fin 2 ↪ Fin sc) (input : List (Fin 2))
    (I : FullMachineTapes.StageIface sc (input.map ι)) (n : ℕ) (hn : n ≤ input.length) :
    FullMachineTapes.fullAnswer I n = true ↔ (input.take n) ∈ PAL := by
  rw [FullMachineTapes.full_answer_correct I n (by simpa using hn),
    ← mem_PAL_iff_isPal_map ι input n]

/-- 系：全部読み終えた時刻。 -/
theorem full_answer_mem_PAL_embed_length (ι : Fin 2 ↪ Fin sc) (input : List (Fin 2))
    (I : FullMachineTapes.StageIface sc (input.map ι)) :
    FullMachineTapes.fullAnswer I input.length = true ↔ input ∈ PAL := by
  rw [full_answer_mem_PAL_embed ι input I input.length le_rfl, List.take_length]

/-- 段の出力ビットの仕様も、入力語の言葉で書ける（`occursAt` / `IsPal` を
`Fin 2` 上に引き戻したもの）。 -/
theorem stage_bit_embed (ι : Fin 2 ↪ Fin sc) (input : List (Fin 2))
    (I : FullMachineTapes.StageIface sc (input.map ι)) (S n : ℕ)
    (hS : 16 ≤ S) (h1 : 2 * S ≤ n) (h2 : n < 4 * S) (hn : n ≤ input.length) :
    I.bit S n = true
      ↔ (occursAt (input.take (S / 2)).reverse (input.take n)
          ∧ IsPal ((input.drop (S / 2)).take (n - S))) := by
  rw [I.spec S n hS h1 h2 (by simpa using hn)]
  rw [map_take, map_take, map_reverse, occursAt_map ι.injective,
    map_drop, map_take, isPal_map ι.injective]

open PalPeg.StageTapes PalPeg.StageIfaceInstance in
/-- **`stageIface` 版**：`StageIfaceInstance.stageIface` を `w := input.map ι` で
具体化したときの全体出力の正当性。特殊記号の仮定 `leftSym ∉ w` / `endSym ∉ w` は
`hι : ∀ i, ι i ∉ ({blank, mark, leftSym, endSym, startSym, one, zero} : Set (Fin sc))`
から従う（`sc = 2` では `hι` 自身が充たせないので、この定理は本当に `sc ≥ 3` 用）。 -/
theorem full_answer_mem_PAL_of_embed
    {blank startSym endSym mark leftSym one zero : Fin sc}
    (ι : Fin 2 ↪ Fin sc)
    (hι : ∀ i, ι i ∉ ({blank, mark, leftSym, endSym, startSym, one, zero} : Set (Fin sc)))
    (C₁ : ℕ)
    (hsum : ∀ (y : List (Fin sc)) (b s : ℕ),
      stripLoop2Periods y 8 b (y.length + 1) s ≤ C₁ * b)
    (hmb : mark ≠ blank)
    (D : MiddleTapes.DecompOnTapes sc blank startSym endSym mark)
    (input : List (Fin 2))
    (cstOf : ℕ → ScanState → ℕ) (A B' U : ℕ)
    (initOf : ℕ → StageT sc)
    (hC : 0 < A + B')
    (hcost : ∀ (S : ℕ) (st : ScanState), cstOf S st ≤ (A + B')
      * (Phi 8 (scanStep (vOf (input.map ι) S) 8 (peOf (input.map ι) S)
          (reOf (input.map ι) S) ((input.map ι).drop S) st) - Phi 8 st))
    (hadvance : ∀ (S : ℕ) (st : ScanState), st.q ≠ (vOf (input.map ι) S).length →
      ((input.map ι).drop S)[st.pos + st.q]? = (vOf (input.map ι) S)[st.q]? →
        cstOf S st ≤ 1)
    (hne : one ≠ zero)
    (hpow : ∀ S, 16 ≤ S → 4 * (S / 4) = S ∧ 2 * (S / 2) = S)
    (hinit : ∀ S, 16 ≤ S → S / 2 ≤ (input.map ι).length →
      PrepPre blank mark leftSym (S / 2) (input.map ι) ((input.map ι).drop S)
          (initOf S).pg.ts
        ∧ ∀ m, m ≤ S / 2 →
          MiddleTapes.MEncodes blank startSym endSym mark leftSym one zero D
            (input.map ι) S m (initOf S).md)
    (n : ℕ) (hn : n ≤ input.length) :
    FullMachineTapes.fullAnswer
        (stageIface C₁ hsum hmb D (input.map ι) cstOf A B' U initOf hC hcost hadvance hne
          (notMem_map_of_notMem_range (notMem_range_of_hi hι (by simp)) input)
          (notMem_map_of_notMem_range (notMem_range_of_hi hι (by simp)) input)
          hpow hinit) n = true
      ↔ (input.take n) ∈ PAL :=
  full_answer_mem_PAL_embed ι input _ n hn

open PalPeg.StageTapes PalPeg.StageIfaceInstance in
/-- **`stageIface` 版・数学的仮定は消費量補題だけ**：`hsum` を
`PassSumGen.hsum_of_consumption` で消し、残る「数学的」仮定を
`hcons : ∀ (x : List (Fin sc)) (b : ℕ), PassSum10.Consumption x 8 b`
（`PassSum10` の消費量補題の任意アルファベット版）ひとつにしたもの。
ほかの仮定はすべて機械側の構造的なもの（記号の相異・段幅の 2 冪性・誕生時テープ・
費用関数の性質）である。 -/
theorem full_answer_mem_PAL_of_embed'
    {blank startSym endSym mark leftSym one zero : Fin sc}
    (ι : Fin 2 ↪ Fin sc)
    (hι : ∀ i, ι i ∉ ({blank, mark, leftSym, endSym, startSym, one, zero} : Set (Fin sc)))
    (hcons : ∀ (x : List (Fin sc)) (b : ℕ), PassSum10.Consumption x 8 b)
    (hmb : mark ≠ blank)
    (D : MiddleTapes.DecompOnTapes sc blank startSym endSym mark)
    (input : List (Fin 2))
    (cstOf : ℕ → ScanState → ℕ) (A B' U : ℕ)
    (initOf : ℕ → StageT sc)
    (hC : 0 < A + B')
    (hcost : ∀ (S : ℕ) (st : ScanState), cstOf S st ≤ (A + B')
      * (Phi 8 (scanStep (vOf (input.map ι) S) 8 (peOf (input.map ι) S)
          (reOf (input.map ι) S) ((input.map ι).drop S) st) - Phi 8 st))
    (hadvance : ∀ (S : ℕ) (st : ScanState), st.q ≠ (vOf (input.map ι) S).length →
      ((input.map ι).drop S)[st.pos + st.q]? = (vOf (input.map ι) S)[st.q]? →
        cstOf S st ≤ 1)
    (hne : one ≠ zero)
    (hpow : ∀ S, 16 ≤ S → 4 * (S / 4) = S ∧ 2 * (S / 2) = S)
    (hinit : ∀ S, 16 ≤ S → S / 2 ≤ (input.map ι).length →
      PrepPre blank mark leftSym (S / 2) (input.map ι) ((input.map ι).drop S)
          (initOf S).pg.ts
        ∧ ∀ m, m ≤ S / 2 →
          MiddleTapes.MEncodes blank startSym endSym mark leftSym one zero D
            (input.map ι) S m (initOf S).md)
    (n : ℕ) (hn : n ≤ input.length) :
    FullMachineTapes.fullAnswer
        (stageIface 2 (PassSumGen.hsum_of_consumption hcons) hmb D (input.map ι) cstOf
          A B' U initOf hC hcost hadvance hne
          (notMem_map_of_notMem_range (notMem_range_of_hi hι (by simp)) input)
          (notMem_map_of_notMem_range (notMem_range_of_hi hι (by simp)) input)
          hpow hinit) n = true
      ↔ (input.take n) ∈ PAL :=
  full_answer_mem_PAL_embed ι input _ n hn

/-! ## 6. 具体的な記号割り当て（`sc = 9`）

入力 2 記号＋特殊 7 記号で `sc = 9` が足りる。 -/

section Symbols9

/-- 入力 2 記号を `Fin 9` の `7, 8` へ送る埋め込み。特殊記号は `0..6` を使う。 -/
def emb9 : Fin 2 ↪ Fin 9 :=
  ⟨fun i => if i = 0 then 7 else 8, by decide⟩

/-- 特殊記号の割り当て：`blank, mark, leftSym, endSym, startSym, one, zero = 0..6`。 -/
def symbols9 : Fin 7 → Fin 9 := fun j => j.castLE (by omega)

/-- 7 個の特殊記号は互いに相異なる。 -/
theorem symbols9_injective : Function.Injective symbols9 := by decide

/-- `mark ≠ blank`。 -/
theorem symbols9_mark_ne_blank : symbols9 1 ≠ symbols9 0 := by decide

/-- `one ≠ zero`。 -/
theorem symbols9_one_ne_zero : symbols9 5 ≠ symbols9 6 := by decide

/-- **`emb9` の像は特殊記号を避ける**。 -/
theorem emb9_avoids : ∀ i, emb9 i ∉
    ({symbols9 0, symbols9 1, symbols9 2, symbols9 3, symbols9 4, symbols9 5,
      symbols9 6} : Set (Fin 9)) := by
  intro i
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  fin_cases i <;>
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- `leftSym = 2` は入力語に現れない。 -/
theorem emb9_leftSym_notMem (input : List (Fin 2)) :
    symbols9 2 ∉ input.map emb9 :=
  notMem_map_of_notMem_range (notMem_range_of_hi emb9_avoids (by simp)) input

/-- `endSym = 3` は入力語に現れない。 -/
theorem emb9_endSym_notMem (input : List (Fin 2)) :
    symbols9 3 ∉ input.map emb9 :=
  notMem_map_of_notMem_range (notMem_range_of_hi emb9_avoids (by simp)) input

/-- `sc = 9` での橋渡し。 -/
theorem mem_PAL_iff_isPal_map9 (input : List (Fin 2)) (n : ℕ) :
    (input.take n) ∈ PAL ↔ IsPal ((input.map emb9).take n) :=
  mem_PAL_iff_isPal_map emb9 input n

/-- `sc = 9` での主定理。 -/
theorem full_answer_mem_PAL_embed9 (input : List (Fin 2))
    (I : FullMachineTapes.StageIface 9 (input.map emb9)) (n : ℕ) (hn : n ≤ input.length) :
    FullMachineTapes.fullAnswer I n = true ↔ (input.take n) ∈ PAL :=
  full_answer_mem_PAL_embed emb9 input I n hn

/-- `sc = 9` での周期和（像に収まる語に対して）。 -/
theorem passPeriodSum_map9 {C₁ : ℕ} (hsum₂ : EndToEnd2.PassPeriodSum 8 C₁)
    (input : List (Fin 2)) (b s : ℕ) :
    stripLoop2Periods (input.map emb9) 8 b ((input.map emb9).length + 1) s ≤ C₁ * b :=
  passPeriodSum_map hsum₂ emb9 input b s

/-- `sc = 9` での弱められた `hsum` の充足。 -/
theorem hsum_of_mem_range9 {C₁ : ℕ} (hsum₂ : EndToEnd2.PassPeriodSum 8 C₁)
    (y : List (Fin 9)) (hy : ∀ c ∈ y, c ∈ Set.range emb9) (b s : ℕ) :
    stripLoop2Periods y 8 b (y.length + 1) s ≤ C₁ * b :=
  hsum_of_mem_range hsum₂ emb9 y hy b s

/-- `sc = 9`：入力語の記号は `emb9` の像に入る（`hsum_of_mem_range9` の適用条件）。 -/
theorem mem_range_emb9 (input : List (Fin 2)) :
    ∀ c ∈ input.map emb9, c ∈ Set.range emb9 := by
  intro c hc
  obtain ⟨a, -, rfl⟩ := List.mem_map.mp hc
  exact ⟨a, rfl⟩

open PalPeg.StageTapes PalPeg.StageIfaceInstance in
/-- **`sc = 9` の具体化**：記号は `symbols9`（`blank, mark, leftSym, endSym, startSym,
one, zero = 0,1,2,3,4,5,6`）、入力は `emb9`（`7, 8`）。記号の相異と像の分離は
`decide` で片づき、数学的仮定は消費量補題 `hcons` だけが残る。 -/
theorem full_answer_mem_PAL_of_embed9
    (hcons : ∀ (x : List (Fin 9)) (b : ℕ), PassSum10.Consumption x 8 b)
    (D : MiddleTapes.DecompOnTapes 9 (symbols9 0) (symbols9 4) (symbols9 3) (symbols9 1))
    (input : List (Fin 2))
    (cstOf : ℕ → ScanState → ℕ) (A B' U : ℕ)
    (initOf : ℕ → StageT 9)
    (hC : 0 < A + B')
    (hcost : ∀ (S : ℕ) (st : ScanState), cstOf S st ≤ (A + B')
      * (Phi 8 (scanStep (vOf (input.map emb9) S) 8 (peOf (input.map emb9) S)
          (reOf (input.map emb9) S) ((input.map emb9).drop S) st) - Phi 8 st))
    (hadvance : ∀ (S : ℕ) (st : ScanState), st.q ≠ (vOf (input.map emb9) S).length →
      ((input.map emb9).drop S)[st.pos + st.q]? = (vOf (input.map emb9) S)[st.q]? →
        cstOf S st ≤ 1)
    (hpow : ∀ S, 16 ≤ S → 4 * (S / 4) = S ∧ 2 * (S / 2) = S)
    (hinit : ∀ S, 16 ≤ S → S / 2 ≤ (input.map emb9).length →
      PrepPre (symbols9 0) (symbols9 1) (symbols9 2) (S / 2) (input.map emb9)
          ((input.map emb9).drop S) (initOf S).pg.ts
        ∧ ∀ m, m ≤ S / 2 →
          MiddleTapes.MEncodes (symbols9 0) (symbols9 4) (symbols9 3) (symbols9 1)
            (symbols9 2) (symbols9 5) (symbols9 6) D (input.map emb9) S m (initOf S).md)
    (n : ℕ) (hn : n ≤ input.length) :
    FullMachineTapes.fullAnswer
        (stageIface 2 (PassSumGen.hsum_of_consumption hcons) symbols9_mark_ne_blank D
          (input.map emb9) cstOf A B' U initOf hC hcost hadvance symbols9_one_ne_zero
          (notMem_map_of_notMem_range (notMem_range_of_hi emb9_avoids (by simp)) input)
          (notMem_map_of_notMem_range (notMem_range_of_hi emb9_avoids (by simp)) input)
          hpow hinit) n = true
      ↔ (input.take n) ∈ PAL :=
  full_answer_mem_PAL_embed emb9 input _ n hn

end Symbols9

section Audit

#print axioms sc_two_hypotheses_unsatisfiable
#print axioms isPal_map
#print axioms occursAt_map
#print axioms mem_PAL_iff_isPal_map
#print axioms passPeriodSum_map
#print axioms full_answer_mem_PAL_embed
#print axioms full_answer_mem_PAL_embed_length
#print axioms stage_bit_embed
#print axioms full_answer_mem_PAL_of_embed
#print axioms emb9_avoids
#print axioms full_answer_mem_PAL_embed9
#print axioms passPeriodSum_map9
#print axioms hsum_of_mem_range
#print axioms hsum_of_mem_word
#print axioms hsum_of_mem_range9
#print axioms mem_range_emb9
#print axioms full_answer_mem_PAL_of_embed'
#print axioms full_answer_mem_PAL_of_embed9

end Audit

end InputEmbed
end PalPeg
