import MacroPeg.ExpandSemantics
import MacroPeg.Soundness
import MacroPeg.Completeness
import Shallot.Peg.Soundness
import Shallot.Peg.Completeness

/-!
# Observations of Macro PEG and plain PEG (instructions.md §3)

Parse trees are erased: an observation is `Option (List Char)` — `none` for failure, `some rest` for success with the
remaining input. On the Macro PEG side this is the existing `MOutcome.restOf`; here the same projection is added for plain
PEG. An observation holds when a *finite derivation* projects to it, so the absence of every observation means that no
finite derivation exists; nothing here reads a fuel-bounded `none` as non-termination.

Observational equivalence `e ≈ f` (fixed grammar, call-by-name) compares the existence of derivations with each
observation, in both directions, on every input.
-/

namespace Shallot.MacroPeg

open Shallot (PExp Outcome Grammar Derives pegRun)

/-- The plain-PEG counterpart of `MOutcome.restOf`. -/
def pegRestOf : Outcome → Option (List Char)
  | .fail => none
  | .ok _ r => some r

/-- `e` has a finite call-by-name derivation on `x` projecting to `r`. -/
def MacroObs (g : MGrammar) (e : MExp) (x : List Char) (r : Option (List Char)) : Prop :=
  ∃ o, MDerives g .callByName e x o ∧ o.restOf = r

/-- `e` has a finite plain-PEG derivation on `x` projecting to `r`. -/
def PegObs (g : Grammar) (e : PExp) (x : List Char) (r : Option (List Char)) : Prop :=
  ∃ o, Derives g e x o ∧ pegRestOf o = r

/-- Observational equivalence of two Macro PEG expressions under a fixed grammar and call-by-name. -/
def ObsEquiv (g : MGrammar) (e f : MExp) : Prop :=
  ∀ x r, MacroObs g e x r ↔ MacroObs g f x r

/-- Success language (any remaining input). -/
def MAccepts (g : MGrammar) (e : MExp) (x : List Char) : Prop := ∃ rest, MacroObs g e x (some rest)
/-- Whole-consumption language. -/
def MRecognizesAll (g : MGrammar) (e : MExp) (x : List Char) : Prop := MacroObs g e x (some [])
def PAccepts (g : Grammar) (e : PExp) (x : List Char) : Prop := ∃ rest, PegObs g e x (some rest)
def PRecognizesAll (g : Grammar) (e : PExp) (x : List Char) : Prop := PegObs g e x (some [])

theorem obsEquiv_refl (g : MGrammar) (e : MExp) : ObsEquiv g e e := fun _ _ => Iff.rfl

theorem obsEquiv_symm {g : MGrammar} {e f : MExp} (h : ObsEquiv g e f) : ObsEquiv g f e :=
  fun x r => (h x r).symm

theorem obsEquiv_trans {g : MGrammar} {e f k : MExp} (h₁ : ObsEquiv g e f) (h₂ : ObsEquiv g f k) :
    ObsEquiv g e k := fun x r => (h₁ x r).trans (h₂ x r)

/-- An observation is the projection of a fuel-bounded run on some fuel (each side picks its own). -/
theorem macroObs_iff_run (g : MGrammar) (e : MExp) (x : List Char) (r : Option (List Char)) :
    MacroObs g e x r ↔ ∃ f o, mpegRun g .callByName f e x = some o ∧ o.restOf = r := by
  constructor
  · rintro ⟨o, hd, hr⟩
    obtain ⟨f, hf⟩ := mpegRun_complete hd
    exact ⟨f, o, hf, hr⟩
  · rintro ⟨f, o, hf, hr⟩
    exact ⟨o, mpegRun_sound hf, hr⟩

theorem pegObs_iff_run (g : Grammar) (e : PExp) (x : List Char) (r : Option (List Char)) :
    PegObs g e x r ↔ ∃ f o, pegRun g f e x = some o ∧ pegRestOf o = r := by
  constructor
  · rintro ⟨o, hd, hr⟩
    obtain ⟨f, hf⟩ := Shallot.pegRun_complete hd
    exact ⟨f, o, hf, hr⟩
  · rintro ⟨f, o, hf, hr⟩
    exact ⟨o, Shallot.pegRun_sound hf, hr⟩

end Shallot.MacroPeg
