import PalPeg.GSPreprocessProg65
import PalPeg.Consumption

/-! # Unconditional linear-time finite preprocessing at exponent eight -/
set_option autoImplicit false
namespace PalPeg.GSPreProg
open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang
variable {sc : ℕ} {Terminal : Type} {blank startSym endSym mark : Fin sc}
  {x : List (Fin sc)}

def preprocessSlope : ℕ := 255 * decompRate 8
def preprocessOffset : ℕ := 22 * decompRate 8 + 8

theorem DECOMPOSE_eight_linear (hend : endSym ∉ x) (hmark : mark ≠ blank)
    {ts : Tapes sc}
    (he : EncS blank startSym endSym mark x 0 0
      ⟨0, 0, 0, 0, 0, 0, 0⟩ ⟨0, 0, 0⟩ ts) :
    ∃ L, ExecA Terminal blank endSym mark (DECOMPOSE 8) ts L ∧
      EncS blank startSym endSym mark x (decompose2 x 8).1 (decompose2 x 8).1
        ⟨0, 0, 0, (decompose2 x 8).2.1, 0, (decompose2 x 8).1, (decompose2 x 8).2.2⟩
        ⟨0, 0, 0⟩ (applyActs blank L ts) ∧
      L.length ≤ preprocessSlope * x.length + preprocessOffset := by
  obtain ⟨L, hx, hfin, hl⟩ := DECOMPOSE_initial (Terminal := Terminal) hend hmark 8 (by omega) he
  refine ⟨L, hx, hfin, ?_⟩
  have hw := decompose2Work_le x 8 2 (by omega)
    (fun b s => PalPeg.PassSum10.passPeriodSumGen_eight x b s)
  have hw' : decompose2Work x 8 ≤ 254 * x.length + 21 := by simpa using hw
  have hm := Nat.mul_le_mul_left (decompRate 8) (Nat.add_le_add_right hw' (x.length + 1))
  unfold preprocessSlope preprocessOffset
  nlinarith only [hl, hm]

/-- info: 'PalPeg.GSPreProg.DECOMPOSE_eight_linear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DECOMPOSE_eight_linear
end PalPeg.GSPreProg
