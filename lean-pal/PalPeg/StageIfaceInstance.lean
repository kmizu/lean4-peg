import PalPeg.FullMachineTapes
import PalPeg.StageTapes
import PalPeg.PrepInstance
import PalPeg.PrepInstances
import PalPeg.EndToEnd2
import PalPeg.MiddleTapes

/-!
# 段のインタフェース `FullMachineTapes.StageIface` の具体化 (`StageIfaceInstance`)

`StageTapes.stage_tapes_spec'` を `FullMachineTapes.StageIface` の形へ束ねる。

* 前処理インタフェース `Pre` は `PrepInstance.prepInstance C₁ hsum hmb` を使う。
  段幅 `S` に対する分解 `(s, p₁, r)` は `PrepInstances.rawRes w (S / 2)` の成分で、
  `hres` は `rfl`、`H` / `hs` / `hkp` は `PrepInstances.prep_core` /
  `prep_cut_lt` / `prep_kp_5S` が与える（`prep_res_eq5` と同じ内容）。
* 分解器 `D : MiddleTapes.DecompOnTapes` は**パラメータ**（具体化は別ファイル）。
* 照合フェーズの費用関数 `cstOf S` と定数 `A` `B'` もパラメータで、
  `hcost` / `hadvance` は仮定として受け取る。
* 誕生時のテープ配置 `initOf S` もパラメータで、`hinit` が
  `PrepPre` と `MEncodes` を与える（全体機械側では
  `FullMachineTapes.stage_birth_pair_prepView` と中央ジョブの前口上から来る）。
-/

namespace PalPeg
namespace StageIfaceInstance

open PegSeparation.RealTimeTM
open PalPeg.StageTapes
open PalPeg.PrepInstances

variable {sc : ℕ}

section Defs

variable (w : List (Fin sc))

/-- 幅 `S` の段の切断位置（`decompose2` の生の出力）。 -/
def sCut (S : ℕ) : ℕ := (rawRes w (S / 2)).1

/-- 生の周期。 -/
def p1Raw (S : ℕ) : ℕ := (rawRes w (S / 2)).2.1

/-- 生の到達長。 -/
def rRaw (S : ℕ) : ℕ := (rawRes w (S / 2)).2.2

/-- パターンの前半（`u`）。 -/
def uOf (S : ℕ) : List (Fin sc) := (w.take (S / 2)).reverse.take (sCut w S)

/-- パターンの後半（`v`）。 -/
def vOf (S : ℕ) : List (Fin sc) := (w.take (S / 2)).reverse.drop (sCut w S)

/-- 正規化済み周期。 -/
def peOf (S : ℕ) : ℕ := effPeriod (vOf w S) (p1Raw w S)

/-- 正規化済み到達長。 -/
def reOf (S : ℕ) : ℕ := effReach (p1Raw w S) (rRaw w S)

end Defs

section Iface

variable {blank startSym endSym mark leftSym one zero : Fin sc}

/-- **段のインタフェース**。`StageTapes.stage_tapes_spec'` の仮定のうち、
段幅 `S` ごとに変わるものは `∀ S, 16 ≤ S → …` の形で受け取る。 -/
noncomputable def stageIface
    (C₁ : ℕ)
    (hsum : ∀ (y : List (Fin sc)) (b s : ℕ),
      stripLoop2Periods y 8 b (y.length + 1) s ≤ C₁ * b)
    (hmb : mark ≠ blank)
    (D : MiddleTapes.DecompOnTapes sc blank startSym endSym mark)
    (w : List (Fin sc))
    (cstOf : ℕ → ScanState → ℕ) (A B' U : ℕ)
    (initOf : ℕ → StageT sc)
    (hC : 0 < A + B')
    (hcost : ∀ (S : ℕ) (st : ScanState), cstOf S st ≤ (A + B')
      * (Phi 8 (scanStep (vOf w S) 8 (peOf w S) (reOf w S) (w.drop S) st) - Phi 8 st))
    (hadvance : ∀ (S : ℕ) (st : ScanState), st.q ≠ (vOf w S).length →
      (w.drop S)[st.pos + st.q]? = (vOf w S)[st.q]? → cstOf S st ≤ 1)
    (hne : one ≠ zero) (hleft : leftSym ∉ w) (hend : endSym ∉ w)
    (hpow : ∀ S, 16 ≤ S → 4 * (S / 4) = S ∧ 2 * (S / 2) = S)
    (hinit : ∀ S, 16 ≤ S → S / 2 ≤ w.length →
      PrepPre blank mark leftSym (S / 2) w (w.drop S) (initOf S).pg.ts
        ∧ ∀ m, m ≤ S / 2 →
          MiddleTapes.MEncodes blank startSym endSym mark leftSym one zero D w S m
            (initOf S).md) :
    FullMachineTapes.StageIface sc w where
  srec := fun S n =>
    ststate D (PrepInstance.prepInstance (blank := blank) (startSym := startSym)
        (endSym := endSym) (mark := mark) C₁ hsum hmb)
      leftSym one zero (uOf w S) (vOf w S) (w.drop S) 8 (peOf w S) (reOf w S)
      (cstOf S) A B' S w (initOf S) n
  bit := fun S n =>
    stAnswerBit (uOf w S) (vOf w S) (w.drop S) 8 (peOf w S) (reOf w S)
      (cstOf S) A B' S one n
      (ststate D (PrepInstance.prepInstance (blank := blank) (startSym := startSym)
          (endSym := endSym) (mark := mark) C₁ hsum hmb)
        leftSym one zero (uOf w S) (vOf w S) (w.drop S) 8 (peOf w S) (reOf w S)
        (cstOf S) A B' S w (initOf S) (n - 1))
      (ststate D (PrepInstance.prepInstance (blank := blank) (startSym := startSym)
          (endSym := endSym) (mark := mark) C₁ hsum hmb)
        leftSym one zero (uOf w S) (vOf w S) (w.drop S) 8 (peOf w S) (reOf w S)
        (cstOf S) A B' S w (initOf S) n)
  cost := fun S n =>
    stcost D (PrepInstance.prepInstance (blank := blank) (startSym := startSym)
        (endSym := endSym) (mark := mark) C₁ hsum hmb)
      (uOf w S) U A B' 8 S n
      (ststate D (PrepInstance.prepInstance (blank := blank) (startSym := startSym)
          (endSym := endSym) (mark := mark) C₁ hsum hmb)
        leftSym one zero (uOf w S) (vOf w S) (w.drop S) 8 (peOf w S) (reOf w S)
        (cstOf S) A B' S w (initOf S) (n - 1))
  C := Cstage D (PrepInstance.prepInstance (blank := blank) (startSym := startSym)
      (endSym := endSym) (mark := mark) C₁ hsum hmb) U A B' 8
  cost_le := fun S n => stage_round_actions _ _ _ _ _ _ _ _ _ _
  cost_idle := by
    intro S n hn
    show stcost _ _ _ _ _ _ _ _ _ _ = 0
    rw [stcost, if_pos hn]
  spec := by
    intro S n hS h1 h2 hw
    have hSle : S / 2 ≤ w.length := by omega
    obtain ⟨hq, hev⟩ := hpow S hS
    obtain ⟨hpinit, hminit⟩ := hinit S hS hSle
    exact stage_tapes_spec' (D := D)
      (Pre := PrepInstance.prepInstance (blank := blank) (startSym := startSym)
        (endSym := endSym) (mark := mark) C₁ hsum hmb)
      (leftSym := leftSym) (one := one) (zero := zero)
      (w := w) (S := S) (k := 8) (s := sCut w S) (p₁ := p1Raw w S) (r := rRaw w S)
      (A := A) (B' := B') (cst := cstOf S) (init := initOf S)
      hmb (by omega) hq rfl
      (prep_kp_5S (by omega) hSle)
      hpinit (by omega) (prep_cut_lt (by omega) hSle)
      (prep_core w (S / 2)) hC (hcost S) (hadvance S)
      hne hleft hend hev hminit h1 h2 hw
  wid_even := fun S hS => (hpow S hS).2

/-- **`stageIface_spec`**：上のインタフェースの主仕様の再掲。 -/
theorem stageIface_spec
    (C₁ : ℕ)
    (hsum : ∀ (y : List (Fin sc)) (b s : ℕ),
      stripLoop2Periods y 8 b (y.length + 1) s ≤ C₁ * b)
    (hmb : mark ≠ blank)
    (D : MiddleTapes.DecompOnTapes sc blank startSym endSym mark)
    (w : List (Fin sc))
    (cstOf : ℕ → ScanState → ℕ) (A B' U : ℕ)
    (initOf : ℕ → StageT sc)
    (hC : 0 < A + B')
    (hcost : ∀ (S : ℕ) (st : ScanState), cstOf S st ≤ (A + B')
      * (Phi 8 (scanStep (vOf w S) 8 (peOf w S) (reOf w S) (w.drop S) st) - Phi 8 st))
    (hadvance : ∀ (S : ℕ) (st : ScanState), st.q ≠ (vOf w S).length →
      (w.drop S)[st.pos + st.q]? = (vOf w S)[st.q]? → cstOf S st ≤ 1)
    (hne : one ≠ zero) (hleft : leftSym ∉ w) (hend : endSym ∉ w)
    (hpow : ∀ S, 16 ≤ S → 4 * (S / 4) = S ∧ 2 * (S / 2) = S)
    (hinit : ∀ S, 16 ≤ S → S / 2 ≤ w.length →
      PrepPre blank mark leftSym (S / 2) w (w.drop S) (initOf S).pg.ts
        ∧ ∀ m, m ≤ S / 2 →
          MiddleTapes.MEncodes blank startSym endSym mark leftSym one zero D w S m
            (initOf S).md)
    (S n : ℕ) (hS : 16 ≤ S) (h1 : 2 * S ≤ n) (h2 : n < 4 * S) (hw : n ≤ w.length) :
    (stageIface C₁ hsum hmb D w cstOf A B' U initOf hC hcost hadvance hne hleft hend
        hpow hinit).bit S n = true
      ↔ (occursAt (w.take (S / 2)).reverse (w.take n)
          ∧ IsPal ((w.drop (S / 2)).take (n - S))) :=
  (stageIface C₁ hsum hmb D w cstOf A B' U initOf hC hcost hadvance hne hleft hend
    hpow hinit).spec S n hS h1 h2 hw

/-- **全体の出力の正当性**：`FullMachineTapes.full_answer_mem_PAL` を上の
インタフェースに適用したもの（2 記号アルファベット）。 -/
theorem full_answer_mem_PAL_of
    {blank startSym endSym mark leftSym one zero : Fin 2}
    (C₁ : ℕ)
    (hsum : ∀ (y : List (Fin 2)) (b s : ℕ),
      stripLoop2Periods y 8 b (y.length + 1) s ≤ C₁ * b)
    (hmb : mark ≠ blank)
    (D : MiddleTapes.DecompOnTapes 2 blank startSym endSym mark)
    (w : List (Fin 2))
    (cstOf : ℕ → ScanState → ℕ) (A B' U : ℕ)
    (initOf : ℕ → StageT 2)
    (hC : 0 < A + B')
    (hcost : ∀ (S : ℕ) (st : ScanState), cstOf S st ≤ (A + B')
      * (Phi 8 (scanStep (vOf w S) 8 (peOf w S) (reOf w S) (w.drop S) st) - Phi 8 st))
    (hadvance : ∀ (S : ℕ) (st : ScanState), st.q ≠ (vOf w S).length →
      (w.drop S)[st.pos + st.q]? = (vOf w S)[st.q]? → cstOf S st ≤ 1)
    (hne : one ≠ zero) (hleft : leftSym ∉ w) (hend : endSym ∉ w)
    (hpow : ∀ S, 16 ≤ S → 4 * (S / 4) = S ∧ 2 * (S / 2) = S)
    (hinit : ∀ S, 16 ≤ S → S / 2 ≤ w.length →
      PrepPre blank mark leftSym (S / 2) w (w.drop S) (initOf S).pg.ts
        ∧ ∀ m, m ≤ S / 2 →
          MiddleTapes.MEncodes blank startSym endSym mark leftSym one zero D w S m
            (initOf S).md) :
    FullMachineTapes.fullAnswer
        (stageIface C₁ hsum hmb D w cstOf A B' U initOf hC hcost hadvance hne hleft hend
          hpow hinit) w.length = true
      ↔ w ∈ PAL :=
  FullMachineTapes.full_answer_mem_PAL _

end Iface

section Audit

#print axioms stageIface_spec
#print axioms full_answer_mem_PAL_of

end Audit

end StageIfaceInstance
end PalPeg
