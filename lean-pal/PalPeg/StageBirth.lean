import PalPeg.StageIfaceInstance
import PalPeg.FullMachineTapes
import PalPeg.InputCopySentinel
import PalPeg.Prologue
import PalPeg.ClearAny
import PalPeg.MiddleTapes

/-!
# 段の誕生時のテープ配置 (`StageBirth`)

`StageIfaceInstance.stageIface` の最後のパラメータ `initOf` を具体的に構成し、
仮定 `hinit` を（可能な範囲で）落とす。

## 監査結果（重要）

本ファイルの構成の過程で、`hinit` の**述べ方**に 2 つの不備が見つかり、**両方とも修正した**。

1. **`hinit` は護りなしでは充足不能**（`hinit_unsatisfiable`）。
   `StageTapes.PrepPre` は `hle : L ≤ w.length` を含み、護りのない `hinit` は
   `∀ S, 16 ≤ S → PrepPre … (S / 2) w …` を要求する。`w` は有限なので
   `S := 2 * w.length + 16` を取れば `S / 2 = w.length + 8 > w.length` となり矛盾する。
   すなわち **どんな `initOf` を取っても護りなしの `hinit` は証明できない**。
   `stageIface.spec` は `hinit S hS` を `hw : n ≤ w.length`（したがって
   `S / 2 ≤ w.length`）を持つ文脈でしか使わないので、
   **`StageIfaceInstance.stageIface` の `hinit` を
   `∀ S, 16 ≤ S → S / 2 ≤ w.length → …` と護った**。
   本ファイルの `initOf_hinit` はこの護られた形をそのまま証明し、
   `stageIface_full` からは残余仮定 `hlen` が消えた。

2. **旧 `PrepPre.inb` は未来の入力を要求していた**（`prepPre_inb_needs_future_input`）。
   旧 `inb : SeqView blank (ts sIn) w (L - 1)` は `SeqView.right_eq` により
   テープの右文脈が `w.drop L ++ (空白)` であることを要求する。段が生まれる
   ラウンド `S / 2` に実際に届いている記号は `w.take (S / 2)` だけで、入力コピーの
   右側は**空白**である。さらに全体機械が渡すのは左端番兵つきの
   `SeqView blank tp (leftSym :: w') b`（`PatternProg.PrepPreL.inb` の形、
   `FullMachineTapes.stage_birth_pair_prepView`、`InputCopySentinel.prepView_at`）
   であり、旧 `inb` の `tp.left = (w.take (L-1)).reverse` とも合わない（番兵セルが余分）。
   **`StageTapes.PrepPre` を番兵つきの
   `inb : SeqView blank (ts sIn) (leftSym :: w.take L) L`（＋ `hfresh : leftSym ∉ w`）
   に変えた**。下流（`PatternTapes.SetupPre` / `setupProgram` / `setup_spec`、
   `PatternProg.setupProg_exec`、`PrepInstance.prologueProg` / `prologue_spec` /
   `prepPre_to_setupPre`）も同じ形へ揃えてある。

その結果、本ファイルの誕生時テープ `birthTapes` は

* 入力コピー `sIn` は **空白テープに番兵を置いて `w.take L` を流し込み 1 歩戻したもの**
  （`InputCopySentinel.prepView_at`、すなわち実機で起きることそのもの）、
* 残り 11 本は空白テープ・カウンタ `0`

だけから作られ、**未来の入力を一切必要としない**。
-/

namespace PalPeg
namespace StageBirth

open PegSeparation.RealTimeTM
open PalPeg.Tape
open PalPeg.PatternTapes

variable {sc : ℕ}

/-! ## 1. 基本のテープ -/

/-- 空白テープ（右文脈に `n` セル分の空白を実体化したもの）。 -/
def blankTape (blank : Fin sc) (n : ℕ) : TapeConfiguration sc :=
  ⟨[], blank, List.replicate n blank⟩

theorem blankTape_stackView (blank : Fin sc) (n : ℕ) :
    StackView blank (blankTape blank n) [] :=
  ⟨rfl, rfl, blanks_replicate _ _⟩

/-- 値 `0` の（マーカつき）カウンタテープ。 -/
def zeroCounter (blank mark : Fin sc) (n : ℕ) : TapeConfiguration sc :=
  ⟨[mark], blank, List.replicate n blank⟩

theorem zeroCounter_view (blank mark : Fin sc) (n : ℕ) :
    CounterView' blank mark (zeroCounter blank mark n) 0 :=
  counterView'_initial blank mark _ (blanks_replicate _ _)

/-- 空白テープは、長さ `m + 1 ≤ n + 1` の全空白語の添字 `0` の `SeqView` でもある。 -/
theorem blankTape_seqView_replicate {blank : Fin sc} {n m : ℕ} (hm : m ≤ n) :
    SeqView blank (blankTape blank n) (List.replicate (m + 1) blank) 0 := by
  refine ⟨rfl, ?_, ⟨List.replicate (n - m) blank, ?_, blanks_replicate _ _⟩⟩
  · rw [List.getElem?_replicate]
    simp [blankTape]
  · show List.replicate n blank
      = (List.replicate (m + 1) blank).drop (0 + 1) ++ List.replicate (n - m) blank
    rw [show (0 + 1) = 1 from rfl, List.drop_replicate,
      ← List.replicate_add]
    congr 1
    omega

/-- テキストテープ：誕生時は**空白のまま**でよい。`TextFeed.padW blank Text 0` は
全空白語なので、空白テープがその添字 `0` の `SeqView` になる。 -/
theorem blankTape_padW {blank : Fin sc} {Text : List (Fin sc)} {n : ℕ}
    (hn : Text.length ≤ n) :
    SeqView blank (blankTape blank n) (TextFeed.padW blank Text 0) 0 := by
  have hpad : TextFeed.padW blank Text 0 = List.replicate (Text.length + 1) blank := by
    simp [TextFeed.padW]
  rw [hpad]
  exact blankTape_seqView_replicate hn

/-- **誕生時の入力コピーテープ**：空白テープに左端番兵 `leftSym` を置き、
到着済みのパターン `w.take L` を 1 記号 1 行動で流し込み、最後に 1 歩左へ戻したもの。
`FullMachineTapes.stage_birth_pair_prepView` が全体機械側で作るものと同じ形であり、
未来の入力（`w.drop L`）を一切必要としない。 -/
def copyTape (blank leftSym : Fin sc) (w : List (Fin sc)) (L n : ℕ) :
    TapeConfiguration sc :=
  Tape.step blank
    (InputCopySentinel.feed blank
      (GSTapes.runProg blank (blankTape blank n) (InputCopySentinel.sentinelInit leftSym))
      (w.take L))
    blank .left

/-- 誕生時の入力コピーは `PrepPre.inb` の形（番兵つき、ヘッドは添字 `L`）。 -/
theorem copyTape_seqView {blank leftSym : Fin sc} {w : List (Fin sc)} {L n : ℕ}
    (hle : L ≤ w.length) :
    SeqView blank (copyTape blank leftSym w L n) (leftSym :: w.take L) L := by
  have hlen : (w.take L).length = L := by
    simp only [List.length_take]; omega
  have h := InputCopySentinel.prepView (blank := blank)
    (blankTape_stackView blank n) leftSym (w.take L)
  rw [hlen] at h
  exact h

/-! ## 2. 誕生時の 12 本テープ -/

/-- 誕生時の 12 本テープ：`sIn` は `copyTape`（番兵つき入力コピー）、
7 本の単進カウンタは `0`、残り（`sU` / `sP` / `sT` / `sX2`）は空白。 -/
def birthTapes (blank mark leftSym : Fin sc) (w : List (Fin sc)) (L n : ℕ) :
    Tapes sc := fun j =>
  if j = sIn then copyTape blank leftSym w L n
  else if j = sU ∨ j = sP ∨ j = sT ∨ j = sX2 then blankTape blank n
  else zeroCounter blank mark n

@[simp] theorem birthTapes_sIn (blank mark leftSym : Fin sc) (w : List (Fin sc)) (L n : ℕ) :
    birthTapes blank mark leftSym w L n sIn = copyTape blank leftSym w L n := by
  rw [birthTapes, if_pos rfl]

theorem birthTapes_blank {blank mark leftSym : Fin sc} {w : List (Fin sc)} {L n : ℕ}
    {j : Fin 12}
    (hj : j ≠ sIn) (hj2 : j = sU ∨ j = sP ∨ j = sT ∨ j = sX2) :
    birthTapes blank mark leftSym w L n j = blankTape blank n := by
  rw [birthTapes, if_neg hj, if_pos hj2]

theorem birthTapes_counter {blank mark leftSym : Fin sc} {w : List (Fin sc)} {L n : ℕ}
    {j : Fin 12}
    (hj : j ≠ sIn) (hj2 : ¬ (j = sU ∨ j = sP ∨ j = sT ∨ j = sX2)) :
    birthTapes blank mark leftSym w L n j = zeroCounter blank mark n := by
  rw [birthTapes, if_neg hj, if_neg hj2]

/-- **誕生時のテープは `PrepPre` を満たす**（実際に存在するものだけから）。 -/
theorem birthTapes_prepPre {blank mark leftSym : Fin sc} {w Text : List (Fin sc)} {L n : ℕ}
    (hpos : 0 < L) (hle : L ≤ w.length) (hfresh : leftSym ∉ w) (hn : Text.length ≤ n) :
    StageTapes.PrepPre blank mark leftSym L w Text
      (birthTapes blank mark leftSym w L n) := by
  refine
    { hpos := hpos
      hle := hle
      hfresh := hfresh
      inb := ?_
      emptyU := ?_
      emptyP := ?_
      txt := ?_
      txt2 := ?_
      cs := ?_
      c1 := ?_
      c2 := ?_
      ap := ?_
      an := ?_
      rp := ?_
      rn := ?_ }
  · rw [birthTapes_sIn]
    exact copyTape_seqView hle
  · rw [birthTapes_blank (by decide) (by decide)]; exact blankTape_stackView _ _
  · rw [birthTapes_blank (by decide) (by decide)]; exact blankTape_stackView _ _
  · rw [birthTapes_blank (by decide) (by decide)]; exact blankTape_padW hn
  · rw [birthTapes_blank (by decide) (by decide)]; exact blankTape_padW hn
  · rw [birthTapes_counter (by decide) (by decide)]; exact zeroCounter_view _ _ _
  · rw [birthTapes_counter (by decide) (by decide)]; exact zeroCounter_view _ _ _
  · rw [birthTapes_counter (by decide) (by decide)]; exact zeroCounter_view _ _ _
  · rw [birthTapes_counter (by decide) (by decide)]; exact zeroCounter_view _ _ _
  · rw [birthTapes_counter (by decide) (by decide)]; exact zeroCounter_view _ _ _
  · rw [birthTapes_counter (by decide) (by decide)]; exact zeroCounter_view _ _ _
  · rw [birthTapes_counter (by decide) (by decide)]; exact zeroCounter_view _ _ _

/-! ## 3. 中央ジョブの誕生時の状態 -/

/-- 6 + 9 本の作業テープをすべて空白にしたもの。 -/
def blankOv (blank : Fin sc) (n : ℕ) : BorderTapes.OvTapes sc :=
  { P := blankTape blank n, X := blankTape blank n, Cnt := blankTape blank n
    U := blankTape blank n, X2 := blankTape blank n, F := blankTape blank n
    S1 := blankTape blank n, S2 := blankTape blank n, S3 := blankTape blank n
    S4 := blankTape blank n, S5 := blankTape blank n, S6 := blankTape blank n
    S7 := blankTape blank n, S8 := blankTape blank n, S9 := blankTape blank n }

theorem blankOv_scratchBlank (blank : Fin sc) (n : ℕ) :
    BorderTapes.ScratchBlank blank (blankOv blank n) :=
  ⟨blankTape_stackView _ _, blankTape_stackView _ _, blankTape_stackView _ _,
   blankTape_stackView _ _, blankTape_stackView _ _, blankTape_stackView _ _,
   blankTape_stackView _ _, blankTape_stackView _ _, blankTape_stackView _ _⟩

/-- 空白の作業テープ束は段テープ `P` / `U` / `Cnt` も空なので `EntryBlank` を満たす。 -/
theorem blankOv_entryBlank (blank : Fin sc) (n : ℕ) :
    MiddleTapes.EntryBlank blank (blankOv blank n) :=
  ⟨blankOv_scratchBlank blank n, blankTape_stackView _ _, blankTape_stackView _ _,
   blankTape_stackView _ _⟩

/-- フラグテープの初期条件（`MEncodes.gwf` / `foutWF` が要求する形）。 -/
theorem blankTape_flagWF {blank : Fin sc} {S n : ℕ} (hn : MiddleTapes.Lmax S ≤ n) :
    ∃ ω : List (Fin sc), MiddleTapes.Lmax S + 1 ≤ ω.length
      ∧ SeqView blank (blankTape blank n) ω 0 :=
  ⟨List.replicate (MiddleTapes.Lmax S + 1) blank, by simp,
    blankTape_seqView_replicate hn⟩

/-- 誕生時の入力コピー：空白テープに左端番兵を置いたもの。 -/
def sentinelTape (blank leftSym : Fin sc) (n : ℕ) : TapeConfiguration sc :=
  GSTapes.runProg blank (blankTape blank n)
    (InputCopySentinel.sentinelInit leftSym)

theorem sentinelTape_frontier (blank leftSym : Fin sc) (n : ℕ) :
    InputCopy.FrontierView blank (sentinelTape blank leftSym n) [leftSym] :=
  InputCopySentinel.sentinelInit_spec (blankTape_stackView blank n) leftSym

/-- 中央ジョブの誕生時の状態。 -/
def midInit (blank leftSym : Fin sc) (S n : ℕ) : MiddleTapes.MState sc :=
  MiddleTapes.minit S ⟨[], blankOv blank n⟩ (blankTape blank n)
    (fun _ => sentinelTape blank leftSym n) (fun _ => sentinelTape blank leftSym n)

/-- **誕生時の中央ジョブは `MEncodes` を満たす**（`MiddleTapes.minit_encodes`）。 -/
theorem midInit_encodes {blank startSym endSym mark leftSym one zero : Fin sc}
    (D : MiddleTapes.DecompOnTapes sc blank startSym endSym mark)
    (w : List (Fin sc)) {S n : ℕ} (hn : MiddleTapes.Lmax S ≤ n) :
    ∀ m, m ≤ S / 2 →
      MiddleTapes.MEncodes blank startSym endSym mark leftSym one zero D w S m
        (midInit blank leftSym S n) :=
  MiddleTapes.minit_encodes D
    (fun _ => sentinelTape_frontier blank leftSym n)
    (fun _ => sentinelTape_frontier blank leftSym n)
    rfl (blankTape_flagWF hn) (blankOv_entryBlank blank n) (blankTape_flagWF hn)

/-! ## 4. 段の誕生時の状態 `initOf` -/

/-- テープの右側に実体化しておく空白セルの本数（テキストとフラグ語の両方を賄う）。 -/
def bufSize (w : List (Fin sc)) (S : ℕ) : ℕ := w.length + MiddleTapes.Lmax S

theorem bufSize_text (w : List (Fin sc)) (S : ℕ) : (w.drop S).length ≤ bufSize w S := by
  simp only [bufSize, List.length_drop]
  omega

theorem bufSize_lmax (w : List (Fin sc)) (S : ℕ) : MiddleTapes.Lmax S ≤ bufSize w S := by
  simp only [bufSize]; omega

/-- **段の誕生時の状態**：12 本の準備テープは `birthTapes`（動作列は空、
つまり誕生ラウンドではまだ何も挽いていない）、中央ジョブは `midInit`、
照合器は `StageTapes.startVM` を誕生時のテープに載せたもの。 -/
def initOf (blank startSym endSym mark leftSym : Fin sc) (w : List (Fin sc)) (S : ℕ) :
    StageTapes.StageT sc :=
  { sm := ⟨StageTapes.startVM blank startSym endSym mark
      (birthTapes blank mark leftSym w (S / 2) (bufSize w S)), 0⟩
    md := midInit blank leftSym S (bufSize w S)
    pg := ⟨[], birthTapes blank mark leftSym w (S / 2) (bufSize w S)⟩ }

@[simp] theorem initOf_pg_ts (blank startSym endSym mark leftSym : Fin sc)
    (w : List (Fin sc)) (S : ℕ) :
    (initOf blank startSym endSym mark leftSym w S).pg.ts
      = birthTapes blank mark leftSym w (S / 2) (bufSize w S) := rfl

@[simp] theorem initOf_md (blank startSym endSym mark leftSym : Fin sc)
    (w : List (Fin sc)) (S : ℕ) :
    (initOf blank startSym endSym mark leftSym w S).md
      = midInit blank leftSym S (bufSize w S) := rfl

/-- **主定理（護られた `hinit`）**：`S / 2 ≤ w.length` のもとで、
`StageIfaceInstance.stageIface` の `hinit` の中身が成り立つ。 -/
theorem initOf_hinit {blank startSym endSym mark leftSym one zero : Fin sc}
    (D : MiddleTapes.DecompOnTapes sc blank startSym endSym mark)
    (w : List (Fin sc)) (hfresh : leftSym ∉ w) :
    ∀ S, 16 ≤ S → S / 2 ≤ w.length →
      StageTapes.PrepPre blank mark leftSym (S / 2) w (w.drop S)
          (initOf blank startSym endSym mark leftSym w S).pg.ts
        ∧ ∀ m, m ≤ S / 2 →
          MiddleTapes.MEncodes blank startSym endSym mark leftSym one zero D w S m
            (initOf blank startSym endSym mark leftSym w S).md := by
  intro S hS hle
  refine ⟨?_, ?_⟩
  · rw [initOf_pg_ts]
    exact birthTapes_prepPre (by omega) hle hfresh (bufSize_text w S)
  · rw [initOf_md]
    exact midInit_encodes D w (bufSize_lmax w S)

/-! ## 5. 監査：`hinit` の 2 つのギャップ -/

/-- **ギャップ 1**：`hinit` は護りなしでは**どんな `initOf` でも偽**。
`PrepPre.hle` が `S / 2 ≤ w.length` を要求するのに、`S` は上限なく走るため。 -/
theorem hinit_unsatisfiable {blank startSym endSym mark leftSym one zero : Fin sc}
    (D : MiddleTapes.DecompOnTapes sc blank startSym endSym mark)
    (w : List (Fin sc)) (I : ℕ → StageTapes.StageT sc) :
    ¬ (∀ S, 16 ≤ S →
        StageTapes.PrepPre blank mark leftSym (S / 2) w (w.drop S) (I S).pg.ts
          ∧ ∀ m, m ≤ S / 2 →
            MiddleTapes.MEncodes blank startSym endSym mark leftSym one zero D w S m
              (I S).md) := by
  intro h
  obtain ⟨hp, -⟩ := h (2 * w.length + 16) (by omega)
  have := hp.hle
  omega

/-- **ギャップ 2**：`PrepPre.inb` は未来の入力を要求する。
入力コピーの右文脈が（誕生時の実物のように）空白なら、`w` の添字 `L` 以降は
すべて空白でなければならない。 -/
theorem prepPre_inb_needs_future_input {blank : Fin sc} {tp : TapeConfiguration sc}
    {w : List (Fin sc)} {L : ℕ} (hpos : 0 < L)
    (hview : SeqView blank tp w (L - 1)) (hblank : Blanks blank tp.right)
    {i : ℕ} (hi₁ : L ≤ i) (hi₂ : i < w.length) : w[i]'hi₂ = blank := by
  obtain ⟨t, ht, -⟩ := hview.right_eq
  have hmem : w[i]'hi₂ ∈ w.drop (L - 1 + 1) := by
    have hL : L - 1 + 1 = L := by omega
    rw [hL]
    have : w[i]'hi₂ = (w.drop L)[i - L]'(by simp only [List.length_drop]; omega) := by
      rw [List.getElem_drop]
      congr 1
      omega
    rw [this]
    exact List.getElem_mem _
  refine hblank _ ?_
  rw [ht]
  exact List.mem_append_left _ hmem

/-- **ギャップ 2 の系（旧形の反例）**：`w` に非空白記号が添字 `L` 以降にあるなら、
右文脈が空白のテープ（＝誕生時に実際に存在するもの）は**旧** `inb` の形
`SeqView blank (ts sIn) w (L - 1)` を満たせない。現在の `PrepPre.inb`
（番兵つき `SeqView blank (ts sIn) (leftSym :: w.take L) L`）にはこの障害はなく、
`copyTape_seqView` が実物のテープからそれを与える。 -/
theorem not_old_inb_of_blank_right {blank : Fin sc} {w : List (Fin sc)} {L : ℕ}
    {ts : Tapes sc} (hpos : 0 < L) (hblank : Blanks blank (ts sIn).right)
    {i : ℕ} (hi₁ : L ≤ i) (hi₂ : i < w.length) (hne : w[i]'hi₂ ≠ blank) :
    ¬ SeqView blank (ts sIn) w (L - 1) := fun h =>
  hne (prepPre_inb_needs_future_input hpos h hblank hi₁ hi₂)

/-! ## 6. `hinit` を落としたインタフェース -/

section Full

variable {blank startSym endSym mark leftSym one zero : Fin sc}

/-- **`hinit` を落としたインタフェース**。`hinit` は `initOf_hinit` が与える
（`stageIface` 側の `hinit` は `S / 2 ≤ w.length` で護られているので、
残余仮定は一切残らない）。他の仮定は `stageIface` のものをそのまま引き継ぐ。 -/
noncomputable def stageIface_full
    (C₁ : ℕ)
    (hsum : ∀ (y : List (Fin sc)) (b s : ℕ),
      stripLoop2Periods y 8 b (y.length + 1) s ≤ C₁ * b)
    (hmb : mark ≠ blank)
    (D : MiddleTapes.DecompOnTapes sc blank startSym endSym mark)
    (w : List (Fin sc))
    (cstOf : ℕ → ScanState → ℕ) (A B' U : ℕ)
    (hC : 0 < A + B')
    (hcost : ∀ (S : ℕ) (st : ScanState), cstOf S st ≤ (A + B')
      * (Phi 8 (scanStep (StageIfaceInstance.vOf w S) 8
          (StageIfaceInstance.peOf w S) (StageIfaceInstance.reOf w S) (w.drop S) st)
        - Phi 8 st))
    (hadvance : ∀ (S : ℕ) (st : ScanState), st.q ≠ (StageIfaceInstance.vOf w S).length →
      (w.drop S)[st.pos + st.q]? = (StageIfaceInstance.vOf w S)[st.q]? → cstOf S st ≤ 1)
    (hne : one ≠ zero) (hleft : leftSym ∉ w) (hend : endSym ∉ w)
    (hpow : ∀ S, 16 ≤ S → 4 * (S / 4) = S ∧ 2 * (S / 2) = S) :
    FullMachineTapes.StageIface sc w :=
  StageIfaceInstance.stageIface (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (leftSym := leftSym) (one := one) (zero := zero)
    C₁ hsum hmb D w cstOf A B' U (initOf blank startSym endSym mark leftSym w)
    hC hcost hadvance hne hleft hend hpow (initOf_hinit D w hleft)

end Full

section Audit

#print axioms initOf_hinit
#print axioms hinit_unsatisfiable
#print axioms prepPre_inb_needs_future_input
#print axioms stageIface_full

end Audit

end StageBirth
end PalPeg
