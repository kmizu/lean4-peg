import PalPeg.SlotClockGeneration
import PalPeg.SlotSchedule

set_option autoImplicit false
namespace PalPeg.SlotClockStartup
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.SlotClock

def initialWidth (i : Fin 4) : ℕ := ![4, 8, 16, 2] i
def initialPhase (i : Fin 4) : Fin 30 := ![6, 2, 0, 14] i
def addr (i : Fin 4) (j : Fin 2) : Fin 8 := finProdFinEquiv (i, j)

abbrev Control := Fin 33 × (Fin 4 → Ctrl)

def bootAction (c : Fin 33) (σ : Fin 8 → Symbol) (j : Fin 8) : Symbol × Move :=
  let ij : Fin 4 × Fin 2 := finProdFinEquiv.symm j
  if ij.2 = 0 ∧ c.val ≤ initialWidth ij.1 then
    (if c = 0 ∨ c.val = initialWidth ij.1 then .edge else .tick,
      if c.val < initialWidth ij.1 then .right else .stay)
  else (σ j, .stay)

/-- After 32 actual arrivals, the same finite controller automatically switches
from bounded initialization to four independent two-microstep clocks. -/
def body : PhaseBody Unit Control Symbol 8 2 := fun q a ph σ =>
  if h : q.1.val < 32 then
    if ph = 0 then (q, bootAction q.1 σ)
    else ((⟨q.1.val + 1, by omega⟩, q.2), fun j => (σ j, .stay))
  else
    let r := fun i => SlotClock.body (q.2 i) a ph (fun j => σ (addr i j))
    ((q.1, fun i => (r i).1), fun j =>
      let ij : Fin 4 × Fin 2 := finProdFinEquiv.symm j
      (r ij.1).2 ij.2)

def machine : StructuredMachine Unit (Control × Fin 2) Symbol 8 2 :=
  ofPhases (by decide) (by decide) .blank (0, fun i => (false, initialPhase i))
    (fun _ => false) body

def ready : SConfig (Control × Fin 2) Symbol 8 :=
  ⟨((32, fun i => (false, initialPhase i)), 0), fun j =>
    let ij : Fin 4 × Fin 2 := finProdFinEquiv.symm j
    if ij.2 = 0 then SlotClock.seed (initialWidth ij.1) 0 else STape.blankTape .blank⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem startup : machine.srun (List.replicate 32 ()) = ready := by
  let x := machine.srun (List.replicate 32 ())
  have hc : x.state.1.1 = 32 ∧ x.state.2 = 0 := by decide
  have hs : ∀ i, x.state.1.2 i = (false, initialPhase i) := by
    intro i
    fin_cases i <;> decide
  have ht : ∀ j, ((x.tape j).left, (x.tape j).focus, (x.tape j).right) =
      ((ready.tape j).left, (ready.tape j).focus, (ready.tape j).right) := by
    intro j
    fin_cases j <;> decide
  have hstate : x.state = ready.state := by
    apply Prod.ext
    · exact Prod.ext hc.1 (funext hs)
    · exact hc.2
  have htape : x.tape = ready.tape := by
    funext j
    have he : ∀ A B : STape Symbol,
        (A.left, A.focus, A.right) = (B.left, B.focus, B.right) → A = B := by
      intro A B
      cases A; cases B
      simp only [Prod.mk.injEq, STape.mk.injEq]
      exact id
    exact he _ _ (ht j)
  have he : ∀ A B : SConfig (Control × Fin 2) Symbol 8,
      A.state = B.state → A.tape = B.tape → A = B := by
    intro A B
    cases A; cases B
    intro hs ht
    cases hs; cases ht
    rfl
  exact he x ready hstate htape

def slice (i : Fin 4) (x : SConfig (Control × Fin 2) Symbol 8) :
    SConfig (Ctrl × Fin 2) Symbol 2 :=
  ⟨(x.state.1.2 i, x.state.2), fun j => x.tape (addr i j)⟩

theorem live_micro (i : Fin 4) (x : SConfig (Control × Fin 2) Symbol 8)
    (hc : x.state.1.1 = 32) (a : Option Unit) :
    slice i (machine.sMicroStep x a) = SlotClock.machine.sMicroStep (slice i x) a := by
  rcases x with ⟨⟨⟨c, q⟩, ph⟩, T⟩
  change c = 32 at hc
  subst c
  simp [slice, StructuredMachine.sMicroStep, machine, SlotClock.machine, ofPhases, body, addr]

theorem live_count (x : SConfig (Control × Fin 2) Symbol 8)
    (hc : x.state.1.1 = 32) (a : Option Unit) :
    (machine.sMicroStep x a).state.1.1 = 32 := by
  rcases x with ⟨⟨⟨c, q⟩, ph⟩, T⟩
  change c = 32 at hc
  subst c
  simp [StructuredMachine.sMicroStep, machine, ofPhases, body]

theorem live_steps (ops : List (Option Unit)) (x : SConfig (Control × Fin 2) Symbol 8)
    (hc : x.state.1.1 = 32) (i : Fin 4) :
    (ops.foldl machine.sMicroStep x).state.1.1 = 32 ∧
    slice i (ops.foldl machine.sMicroStep x) =
      ops.foldl SlotClock.machine.sMicroStep (slice i x) := by
  induction ops generalizing x with
  | nil => exact ⟨hc, rfl⟩
  | cons a ops ih =>
    have hh := ih (machine.sMicroStep x a) (live_count x hc a)
    simpa only [List.foldl_cons, live_micro i x hc a] using hh

theorem live_rounds (input : List Unit) (x : SConfig (Control × Fin 2) Symbol 8)
    (hc : x.state.1.1 = 32) (i : Fin 4) :
    (input.foldl machine.sRound x).state.1.1 = 32 ∧
    slice i (input.foldl machine.sRound x) =
      input.foldl SlotClock.machine.sRound (slice i x) := by
  induction input generalizing x with
  | nil => exact ⟨hc, rfl⟩
  | cons a input ih =>
    have hr := live_steps (PalPeg.Speedup.MultiStepMachine.roundInputs 2 a) x hc i
    have hh := ih (machine.sRound x a) hr.1
    have he : slice i (machine.sRound x a) = SlotClock.machine.sRound (slice i x) a := hr.2
    simpa only [List.foldl_cons, he] using hh

theorem startup_continuation (input : List Unit) (i : Fin 4) :
    slice i (machine.srun (List.replicate 32 () ++ input)) =
      input.foldl SlotClock.machine.sRound (slice i ready) := by
  change slice i ((List.replicate 32 () ++ input).foldl machine.sRound machine.sInit) = _
  rw [List.foldl_append]
  change slice i (input.foldl machine.sRound (machine.srun (List.replicate 32 ()))) = _
  rw [startup]
  exact (live_rounds input ready rfl i).2

theorem ready_slice (i : Fin 4) :
    slice i ready = ⟨((false, initialPhase i), 0), SlotClock.seed (initialWidth i)⟩ := by
  simp [slice, ready, addr, SlotClock.seed]
  rfl

theorem from_blank (input : List Unit) (i : Fin 4) :
    slice i (machine.srun (List.replicate 32 () ++ input)) =
      input.foldl SlotClock.machine.sRound
        ⟨((false, initialPhase i), 0), SlotClock.seed (initialWidth i)⟩ := by
  rw [startup_continuation, ready_slice]

theorem schedule_at_32 (i : Fin 4) :
    (SlotSchedule.canonSlot 32 i).q = initialWidth i ∧
    (SlotSchedule.canonSlot 32 i).p = (initialPhase i).val ∧
    (SlotSchedule.canonSlot 32 i).r = 0 ∧ (SlotSchedule.canonSlot 32 i).nx = 0 := by
  fin_cases i <;> decide

/-- info: 'PalPeg.SlotClockStartup.startup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms startup
/-- info: 'PalPeg.SlotClockStartup.startup_continuation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms startup_continuation
/-- info: 'PalPeg.SlotClockStartup.from_blank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms from_blank
/-- info: 'PalPeg.SlotClockStartup.schedule_at_32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms schedule_at_32

end PalPeg.SlotClockStartup
