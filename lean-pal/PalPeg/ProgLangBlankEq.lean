import PalPeg.ProgramBlankEq
import PalPeg.ProgLangLib

/-! Transfer finite-program execution certificates across right-blank padding. -/
set_option autoImplicit false

namespace PalPeg.ProgLang
open PalPeg.Program
variable {A C Γ Terminal : Type} {t : ℕ}

def RunBlankEq (blank : Γ) (x y : Stack A C × (Fin t → STape Γ)) : Prop :=
  x.1 = y.1 ∧ ∀ j, STape.BlankEq blank (x.2 j) (y.2 j)

theorem microStep_blankEq (I : Interp Terminal A C Γ t) {blank : Γ}
    {x y : Stack A C × (Fin t → STape Γ)} (h : RunBlankEq blank x y) (a : Option Terminal) :
    RunBlankEq blank (microStep I blank a x) (microStep I blank a y) := by
  obtain ⟨s, T⟩ := x
  obtain ⟨s', U⟩ := y
  obtain ⟨hs, hT⟩ := h
  change s = s' at hs
  subst s'
  have hf : (fun j => (T j).focus) = (fun j => (U j).focus) := funext fun j => (hT j).focus
  unfold RunBlankEq microStep
  dsimp only
  rw [hf]
  refine ⟨rfl, ?_⟩
  cases ha : (stepStack (evalConds I (fun j => (U j).focus)) s).2 with
  | none => exact hT
  | some a => exact fun j => (hT j).applyAction _

theorem runInputs_blankEq (I : Interp Terminal A C Γ t) {blank : Γ}
    (l : List (Option Terminal)) {x y : Stack A C × (Fin t → STape Γ)}
    (h : RunBlankEq blank x y) :
    RunBlankEq blank (runInputs I blank l x) (runInputs I blank l y) := by
  induction l generalizing x y with
  | nil => exact h
  | cons a l ih => exact ih (microStep_blankEq I h a)

theorem trace_blankEq (I : Interp Terminal A C Γ t) {blank : Γ}
    (l : List (Option Terminal)) {x y : Stack A C × (Fin t → STape Γ)}
    (h : RunBlankEq blank x y) : trace I blank l x = trace I blank l y := by
  induction l generalizing x y with
  | nil => rfl
  | cons a l ih =>
    obtain ⟨s, T⟩ := x
    obtain ⟨s', U⟩ := y
    have ht := ih (microStep_blankEq I h a)
    obtain ⟨hs, hT⟩ := h
    change s = s' at hs
    subst s'
    have hf : (fun j => (T j).focus) = (fun j => (U j).focus) := funext fun j => (hT j).focus
    simp only [trace_cons, hf, ht]

theorem applyTrace_blankEq {blank : Γ} {T U : Fin t → STape Γ}
    (h : ∀ j, STape.BlankEq blank (T j) (U j)) (tr : List (Fin t → Γ × PegSeparation.RealTimeTM.Move)) :
    ∀ j, STape.BlankEq blank (applyTrace blank T tr j) (applyTrace blank U tr j) := by
  induction tr generalizing T U with
  | nil => exact h
  | cons a tr ih => exact ih (fun j => (h j).applyAction (a j))

/-- A certificate derived using an explicitly padded representative is a
certificate for the unpadded tapes too, with identical instructions and cost. -/
theorem exec_blankEq {I : Interp Terminal A C Γ t} {blank : Γ} {p : Prog A C}
    {T U : Fin t → STape Γ} {tr : List (Fin t → Γ × PegSeparation.RealTimeTM.Move)}
    (h : ∀ j, STape.BlankEq blank (T j) (U j)) (he : Exec I blank p U tr) :
    Exec I blank p T tr := by
  intro r l hl
  obtain ⟨htr, s', hrun, hseq⟩ := he r l hl
  have hbase : RunBlankEq blank ([p] ++ r, T) ([p] ++ r, U) := ⟨rfl, h⟩
  have htrace : trace I blank l ([p] ++ r, T) = tr := (trace_blankEq I l hbase).trans htr
  have hs := (runInputs_blankEq I l hbase).1
  rw [hrun] at hs
  have ht := runInputs_snd_eq_applyTrace I blank l ([p] ++ r, T)
  rw [htrace] at ht
  refine ⟨htrace, s', Prod.ext hs ht, ?_⟩
  have hf : (fun j => (applyTrace blank T tr j).focus) =
      (fun j => (applyTrace blank U tr j).focus) :=
    funext fun j => (applyTrace_blankEq h tr j).focus
  unfold SEqAt
  rw [hf]
  exact hseq

/-- info: 'PalPeg.ProgLang.exec_blankEq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exec_blankEq

end PalPeg.ProgLang
