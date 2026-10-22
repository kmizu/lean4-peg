import Shallot.Peg.Separation.Upper
import Cfg.OpenProblems

/-!
# PEG languages are strictly inside P over the binary alphabet

`IsBitPEL` is the existing full-input PEG semantics on the fixed alphabet
`{'0', '1'}`. Its equivalence to restricting a `Cfg.IsPEL` language is
explicit. `KEXP 0` is the existing multitape polynomial-time class.

The witness is the concrete `PolyDiag 15`. Its lifted character language
also witnesses nonmembership in the repository's original `Cfg.IsPEL`.
-/

namespace Shallot.PegSeparation

open Complexity Shallot.MacroPeg.KExp Shallot.MacroPeg.HO Shallot.Packrat.Machine

/-- The fixed binary alphabet used to compare language classes. -/
def binaryChar (b : Bool) : Char := if b then '1' else '0'

theorem binaryChar_injective (a b : Bool) (h : binaryChar a = binaryChar b) : a = b := by
  cases a <;> cases b <;> simp_all [binaryChar]

/-- PEG languages on the fixed binary alphabet, allowing divergent grammars. -/
def IsBitPEL (L : Lang) : Prop := ∃ g : Grammar, ∀ w, L w ↔ bitLanguage g binaryChar w

/-- This fixed-alphabet class is exactly restriction of the original PEG language class. -/
theorem isBitPEL_iff_restriction (L : Lang) :
    IsBitPEL L ↔ ∃ A : Shallot.Cfg.Language, Shallot.Cfg.IsPEL A ∧ ∀ w, L w ↔ A (w.map binaryChar) := by
  constructor
  · rintro ⟨g, hg⟩
    let A : Shallot.Cfg.Language := fun x => ∃ t, Derives g (.nt g.start) x (.ok t [])
    exact ⟨A, ⟨g, fun _ => Iff.rfl⟩, hg⟩
  · rintro ⟨A, ⟨g, hg⟩, hA⟩
    exact ⟨g, fun w => (hA w).trans (hg (w.map binaryChar))⟩

/-- Every binary PEG language is in the existing polynomial-time TM class. -/
theorem bitPEL_in_P {L : Lang} (h : IsBitPEL L) : KEXP 0 L := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨M, c, hdec, ht⟩ := bitLanguage_time15 g binaryChar
  refine ⟨_, M, (fun N => c * (N + 1) ^ 15), c, 15, ?_, ?_, ht⟩
  · intro N; simp only [tower_zero]; exact Nat.le_refl _
  · intro w
    obtain ⟨t, hh, hL⟩ := hdec w
    exact ⟨t, hh, hL.trans (hg w).symm⟩

/-- A concrete language in P that is not a PEG language. -/
theorem polynomial_non_PEL : KEXP 0 (PolyDiag 15) ∧ ¬ IsBitPEL (PolyDiag 15) :=
  ⟨polyDiag_in_P 15, polyDiag_not_peg binaryChar⟩

/-- **Strict inclusion PEL ⊊ P**, on the standard fixed binary alphabet. -/
theorem pel_strict_in_p :
    (∀ L, IsBitPEL L → KEXP 0 L) ∧ ∃ L, KEXP 0 L ∧ ¬ IsBitPEL L :=
  ⟨fun _ h => bitPEL_in_P h, PolyDiag 15, polynomial_non_PEL⟩

/-- Lift a binary language to character strings, rejecting all nonbinary strings. -/
def liftBinary (L : Lang) : Shallot.Cfg.Language := fun x => ∃ w : List Bool, x = w.map binaryChar ∧ L w

theorem liftBinary_on_bits (L : Lang) (w : List Bool) : liftBinary L (w.map binaryChar) ↔ L w := by
  constructor
  · rintro ⟨u, hu, hL⟩
    have he : w = u := (List.map_inj_right binaryChar_injective).mp hu
    exact he.symm ▸ hL
  · intro h; exact ⟨w, rfl, h⟩

/-- The same witness is outside the original character-string PEG class. -/
theorem lifted_polyDiag_not_PEL : ¬ Shallot.Cfg.IsPEL (liftBinary (PolyDiag 15)) := by
  rintro ⟨g, hg⟩
  apply polyDiag_not_peg binaryChar
  exact ⟨g, fun w => (liftBinary_on_bits (PolyDiag 15) w).symm.trans (hg (w.map binaryChar))⟩

private theorem P_congr {L L' : Lang} (h : ∀ w, L w ↔ L' w) (hL : KEXP 0 L) : KEXP 0 L' := by
  obtain ⟨k, M, T, c, d, hT, hdec, ht⟩ := hL
  refine ⟨k, M, T, c, d, hT, ?_, ht⟩
  intro w
  obtain ⟨t, hh, hLw⟩ := hdec w
  exact ⟨t, hh, hLw.trans (h w)⟩

/-- A supported binary character language, polynomial-time under its binary encoding, outside `Cfg.IsPEL`. -/
theorem character_counterexample :
    ∃ A : Shallot.Cfg.Language,
      (∀ x, A x → ∃ w : List Bool, x = w.map binaryChar) ∧
      KEXP 0 (fun w => A (w.map binaryChar)) ∧ ¬ Shallot.Cfg.IsPEL A := by
  refine ⟨liftBinary (PolyDiag 15), ?_, ?_, lifted_polyDiag_not_PEL⟩
  · intro x h; obtain ⟨w, hw, _⟩ := h; exact ⟨w, hw⟩
  · exact P_congr (fun w => (liftBinary_on_bits (PolyDiag 15) w).symm) (polyDiag_in_P 15)

end Shallot.PegSeparation
