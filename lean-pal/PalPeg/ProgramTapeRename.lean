import PalPeg.ProgramMachine

set_option autoImplicit false
namespace PalPeg.Program.TapeRename
open PegSeparation.RealTimeTM
variable {Terminal Q Γ : Type} [Fintype Q] [DecidableEq Q]
  [Fintype Γ] [DecidableEq Γ] {t B : ℕ}

/-- e maps a logical tape name to its physical tape. Renaming changes only
head selection; it performs no data movement and allocates no extra tape. -/
def machine (M : StructuredMachine Terminal Q Γ t B) (e : Fin t ≃ Fin t) :
    StructuredMachine Terminal Q Γ t B where
  tapeCount_pos := M.tapeCount_pos
  blank := M.blank
  initial := M.initial
  accepting := M.accepting
  micro := fun q a σ =>
    let d := M.micro q a (fun j => σ (e j))
    (d.1, fun j => d.2 (e.symm j))

def view (e : Fin t ≃ Fin t) (x : SConfig Q Γ t) : SConfig Q Γ t :=
  ⟨x.state, fun j => x.tape (e j)⟩

theorem micro_view (M : StructuredMachine Terminal Q Γ t B) (e : Fin t ≃ Fin t)
    (x : SConfig Q Γ t) (a : Option Terminal) :
    view e ((machine M e).sMicroStep x a) = M.sMicroStep (view e x) a := by
  simp only [StructuredMachine.sMicroStep, machine, view, Equiv.symm_apply_apply]

theorem steps_view (M : StructuredMachine Terminal Q Γ t B) (e : Fin t ≃ Fin t)
    (ops : List (Option Terminal)) (x : SConfig Q Γ t) :
    view e (ops.foldl (machine M e).sMicroStep x) = ops.foldl M.sMicroStep (view e x) := by
  induction ops generalizing x with
  | nil => rfl
  | cons a ops ih => rw [List.foldl_cons, ih, micro_view, List.foldl_cons]

theorem round_view (M : StructuredMachine Terminal Q Γ t B) (e : Fin t ≃ Fin t)
    (x : SConfig Q Γ t) (a : Terminal) :
    view e ((machine M e).sRound x a) = M.sRound (view e x) a :=
  steps_view M e _ x

theorem run_view (M : StructuredMachine Terminal Q Γ t B) (e : Fin t ≃ Fin t)
    (w : List Terminal) (x : SConfig Q Γ t) :
    view e (w.foldl (machine M e).sRound x) = w.foldl M.sRound (view e x) := by
  induction w generalizing x with
  | nil => rfl
  | cons a w ih => rw [List.foldl_cons, ih, round_view, List.foldl_cons]

end PalPeg.Program.TapeRename
