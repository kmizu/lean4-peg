import PalPeg.ProgramMachine

/-! Four disjoint finite-control machines receive each real arrival once,
in parallel. This is wiring, not a stage scheduler or PAL acceptance rule. -/
set_option autoImplicit false
namespace PalPeg.ProgramBroadcast
open PegSeparation.RealTimeTM PalPeg.Program
variable {Terminal Q Γ : Type} [Fintype Q] [DecidableEq Q] [Fintype Γ] [DecidableEq Γ]
variable {t B : ℕ}

def slice (i : Fin 4) (x : SConfig (Fin 4 → Q) Γ (4 * t)) : SConfig Q Γ t :=
  ⟨x.state i, fun j => x.tape (finProdFinEquiv (i, j))⟩

def machine (M : StructuredMachine Terminal Q Γ t B) :
    StructuredMachine Terminal (Fin 4 → Q) Γ (4 * t) B where
  tapeCount_pos := Nat.mul_pos (by decide) M.tapeCount_pos
  blank := M.blank
  initial := fun _ => M.initial
  accepting := fun _ => false
  micro q a σ :=
    let r := fun i => M.micro (q i) a (fun j => σ (finProdFinEquiv (i, j)))
    (fun i => (r i).1, fun j => (r (finProdFinEquiv.symm j).1).2 (finProdFinEquiv.symm j).2)

theorem micro_slice (M : StructuredMachine Terminal Q Γ t B) (i : Fin 4)
    (x : SConfig (Fin 4 → Q) Γ (4 * t)) (a : Option Terminal) :
    slice i ((machine M).sMicroStep x a) = M.sMicroStep (slice i x) a := by
  simp only [StructuredMachine.sMicroStep, machine, slice, Equiv.symm_apply_apply]

theorem micro_run_slice (M : StructuredMachine Terminal Q Γ t B) (i : Fin 4)
    (ops : List (Option Terminal)) (x : SConfig (Fin 4 → Q) Γ (4 * t)) :
    slice i (ops.foldl (machine M).sMicroStep x) = ops.foldl M.sMicroStep (slice i x) := by
  induction ops generalizing x with
  | nil => rfl
  | cons a ops ih => rw [List.foldl_cons, ih, micro_slice, List.foldl_cons]

theorem round_slice (M : StructuredMachine Terminal Q Γ t B) (i : Fin 4)
    (x : SConfig (Fin 4 → Q) Γ (4 * t)) (a : Terminal) :
    slice i ((machine M).sRound x a) = M.sRound (slice i x) a :=
  micro_run_slice M i _ x

/-- Valid also for different local stages and clocks in the four slots. -/
theorem run_slice (M : StructuredMachine Terminal Q Γ t B) (i : Fin 4)
    (word : List Terminal) (x : SConfig (Fin 4 → Q) Γ (4 * t)) :
    slice i (word.foldl (machine M).sRound x) = word.foldl M.sRound (slice i x) := by
  induction word generalizing x with
  | nil => rfl
  | cons a word ih => rw [List.foldl_cons, ih, round_slice, List.foldl_cons]

theorem initialized_slice (M : StructuredMachine Terminal Q Γ t B) (i : Fin 4)
    (word : List Terminal) : slice i ((machine M).srun word) = M.srun word :=
  run_slice M i word (machine M).sInit

/-- info: 'PalPeg.ProgramBroadcast.run_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_slice
end PalPeg.ProgramBroadcast
