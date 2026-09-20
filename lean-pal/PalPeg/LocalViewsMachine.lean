import PalPeg.LocalViewInit

/-!
# The machine of several views

`viewCount` views on `viewCount * 12` tapes, one slot counter for all of them.  An input letter
reaches the machine on one step only, and the very first step is the initialization, so the
control latches letters: `current` is the letter the views enqueue during this slot, `pending` a
letter that arrived while the slot was running.  The command of a slot is a function of
`current`, hence constant through the slot.
-/

set_option autoImplicit false

namespace PalPeg.ConcreteLocalMachine

open PalPeg
open PalPeg.LocalInputView
open PalPeg.LocalViewCells
open PalPeg.CloseoutCoreStep (Γc blankc)
open PalPeg.CloseoutCoreEnc12 (Act ActRule compStep)
open PalPeg.Local (Window readWin)
open PalPeg.Program (STape)

/-- The control: started, the letter of this slot, a latched letter, the slot counter, the
controls of the views. -/
abbrev MachineControl (viewCount : ℕ) : Type :=
  Bool × Option (Fin 2) × Option (Fin 2) × Fin 11 × (Fin viewCount → ViewControl)

abbrev MachineState (viewCount : ℕ) : Type :=
  MachineControl viewCount × (Fin (viewCount * 12) → STape Γc)

/-- The command of a slot: distribute the letter of the slot, if any. -/
def commandOfLetter : Option (Fin 2) → ViewCommand
  | some a => .arrive a
  | none => .stay

def nextSlot (slot : Fin 11) : Fin 11 :=
  if h : slot.val + 1 < 11 then ⟨slot.val + 1, h⟩ else 0

/-- Tape `tape` of view `view`. -/
def viewTape {viewCount : ℕ} (view : Fin viewCount) (tape : Fin 12) : Fin (viewCount * 12) :=
  finProdFinEquiv (view, tape)

/-- The registers after a step: the first step starts the machine on the first letter; the last
step of a slot hands the latched letter to the next slot. -/
def registersAfter (started : Bool) (current pending : Option (Fin 2)) (slot : Fin 11)
    (input : Option (Fin 2)) : Option (Fin 2) × Option (Fin 2) × Fin 11 :=
  if started then
    if slot.val = 10 then (input <|> pending, none, 0)
    else (current, input <|> pending, nextSlot slot)
  else (input, none, 0)

section Machine

variable {K : ℕ}

/-- **The machine of several views.** -/
def machineRule (viewCount : ℕ) (hK : 2 ≤ K) :
    ActRule (Fin 2) (MachineControl viewCount) Γc (viewCount * 12) K where
  nq := fun control input windows =>
    (true,
      (registersAfter control.1 control.2.1 control.2.2.1 control.2.2.2.1 input).1,
      (registersAfter control.1 control.2.1 control.2.2.1 control.2.2.2.1 input).2.1,
      (registersAfter control.1 control.2.1 control.2.2.1 control.2.2.2.1 input).2.2,
      fun view => viewNext (Fin 2) hK control.2.2.2.1 (commandOfLetter control.2.1)
        (control.2.2.2.2 view) (fun tape => windows (viewTape view tape)))
  acts := fun control _ windows tape =>
    viewActs (Fin 2) hK control.2.2.2.1 (commandOfLetter control.2.1)
      (control.2.2.2.2 (finProdFinEquiv.symm tape).1)
      (fun viewTapeIndex => windows (viewTape (finProdFinEquiv.symm tape).1 viewTapeIndex))
      (finProdFinEquiv.symm tape).2
  len_le := fun _ _ _ _ => viewActs_length _ hK _ _ _ _ _

/-- One real step. -/
def machineStep (viewCount : ℕ) (hK : 2 ≤ K) (x : MachineState viewCount)
    (input : Option (Fin 2)) : MachineState viewCount :=
  (compStep (machineRule viewCount hK)).apply blankc x input

/-- The state after `count` real steps on the inputs `inputs 0`, `inputs 1`, …. -/
def machineIter (viewCount : ℕ) (hK : 2 ≤ K) (inputs : ℕ → Option (Fin 2))
    (x : MachineState viewCount) : ℕ → MachineState viewCount
  | 0 => x
  | count + 1 => machineStep viewCount hK (machineIter viewCount hK inputs x count) (inputs count)

/-- The part of a state that belongs to a view. -/
def viewStateOf {viewCount : ℕ} (x : MachineState viewCount) (view : Fin viewCount) :
    ViewState :=
  (x.1.2.2.2.2 view, fun tape => x.2 (viewTape view tape))

/-- **A real step is a `ViewStep` of every view.** -/
theorem machine_viewStep (viewCount : ℕ) (hK : 2 ≤ K) (x : MachineState viewCount)
    (input : Option (Fin 2)) (view : Fin viewCount) :
    ViewStep (Fin 2) hK x.1.2.2.2.1 (commandOfLetter x.1.2.1) (viewStateOf x view)
      (viewStateOf (machineStep viewCount hK x input) view) := by
  refine viewStep_of_apply (Fin 2) hK (machineRule viewCount hK) (viewTape view)
    (fun control => control.2.2.2.2 view) x.1.2.2.2.1 (commandOfLetter x.1.2.1) x input rfl ?_
  intro tape
  show viewActs (Fin 2) hK _ _ (x.1.2.2.2.2 (finProdFinEquiv.symm (viewTape view tape)).1) _
    (finProdFinEquiv.symm (viewTape view tape)).2 = _
  unfold viewTape
  rw [Equiv.symm_apply_apply]

theorem machineStep_registers (viewCount : ℕ) (hK : 2 ≤ K) (x : MachineState viewCount)
    (input : Option (Fin 2)) :
    (machineStep viewCount hK x input).1.1 = true ∧
      ((machineStep viewCount hK x input).1.2.1, (machineStep viewCount hK x input).1.2.2.1,
        (machineStep viewCount hK x input).1.2.2.2.1)
        = registersAfter x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2.1 input :=
  ⟨rfl, rfl⟩

/-! ## The first step -/

/-- The state a machine starts in: not started, no letter, slot `0`, blank tapes. -/
def machineInitState (viewCount : ℕ) : MachineState viewCount :=
  ((false, none, none, 0, fun _ => viewInitControl), fun _ => STape.blankTape blankc)

/-- **The first step**: the machine is started on the first letter, at step `0` of a slot, and
every view represents the empty view with nothing owed. -/
theorem machineInit (viewCount : ℕ) (hK : 2 ≤ K) (input : Option (Fin 2)) (micro : MicroOp) :
    (machineStep viewCount hK (machineInitState viewCount) input).1.1 = true ∧
      (machineStep viewCount hK (machineInitState viewCount) input).1.2.1 = input ∧
      (machineStep viewCount hK (machineInitState viewCount) input).1.2.2.1 = none ∧
      (machineStep viewCount hK (machineInitState viewCount) input).1.2.2.2.1 = 0 ∧
      ∀ view : Fin viewCount,
        (viewStateOf (machineStep viewCount hK (machineInitState viewCount) input) view).1
          = viewInitControl ∧
        ViewRep K emptyView viewInitControl.1 (micro, viewInitControl.2.2)
          (viewStateOf (machineStep viewCount hK (machineInitState viewCount) input) view).2 := by
  refine ⟨rfl, rfl, rfl, rfl, fun view => ?_⟩
  refine viewInit_of_apply (Fin 2) hK (machineRule viewCount hK) (viewTape view)
    (fun control => control.2.2.2.2 view) (slot := 0) rfl (machineInitState viewCount) input
    (fun _ => rfl) rfl rfl ?_ micro
  intro tape
  show viewActs (Fin 2) hK _ _
    ((machineInitState viewCount).1.2.2.2.2 (finProdFinEquiv.symm (viewTape view tape)).1) _
    (finProdFinEquiv.symm (viewTape view tape)).2 = _
  unfold viewTape
  rw [Equiv.symm_apply_apply]
  rfl

/-! ## One slot -/

/-- Through a slot the machine stays started, the counter counts, the letter stays. -/
theorem machineIter_registers (viewCount : ℕ) (hK : 2 ≤ K) (inputs : ℕ → Option (Fin 2))
    (x : MachineState viewCount) (hstarted : x.1.1 = true) (hslot : x.1.2.2.2.1 = 0) :
    ∀ count ≤ 10,
      (machineIter viewCount hK inputs x count).1.1 = true ∧
        (machineIter viewCount hK inputs x count).1.2.2.2.1.val = count ∧
        (machineIter viewCount hK inputs x count).1.2.1 = x.1.2.1
  | 0, _ => ⟨hstarted, by rw [show machineIter viewCount hK inputs x 0 = x from rfl, hslot]; rfl,
      rfl⟩
  | count + 1, hcount => by
    obtain ⟨hstartedAt, hslotAt, hcurrentAt⟩ :=
      machineIter_registers viewCount hK inputs x hstarted hslot count (by omega)
    obtain ⟨hstartedNext, hregisters⟩ := machineStep_registers viewCount hK
      (machineIter viewCount hK inputs x count) (inputs count)
    have hnotLast : ¬ (machineIter viewCount hK inputs x count).1.2.2.2.1.val = 10 := by omega
    unfold registersAfter at hregisters
    rw [hstartedAt, if_pos rfl, if_neg hnotLast] at hregisters
    have hcurrentNext := congrArg Prod.fst hregisters
    have hslotNext := congrArg (fun registers => registers.2.2) hregisters
    refine ⟨hstartedNext, ?_, ?_⟩
    · show (machineStep viewCount hK _ _).1.2.2.2.1.val = count + 1
      rw [show (machineStep viewCount hK (machineIter viewCount hK inputs x count)
        (inputs count)).1.2.2.2.1 = nextSlot (machineIter viewCount hK inputs x count).1.2.2.2.1
        from hslotNext]
      unfold nextSlot
      rw [dif_pos (by omega)]
      show (machineIter viewCount hK inputs x count).1.2.2.2.1.val + 1 = count + 1
      omega
    · show (machineStep viewCount hK _ _).1.2.1 = x.1.2.1
      rw [show (machineStep viewCount hK (machineIter viewCount hK inputs x count)
        (inputs count)).1.2.1 = (machineIter viewCount hK inputs x count).1.2.1
        from hcurrentNext]
      exact hcurrentAt

/-- **One slot of the machine.**  Eleven real steps from step `0` of a slot take every view to
the view commanded by the letter of the slot, with nothing owed. -/
theorem machineSlot (viewCount : ℕ) (hK : 2 ≤ K) (inputs : ℕ → Option (Fin 2))
    (x : MachineState viewCount) (hstarted : x.1.1 = true) (hslot : x.1.2.2.2.1 = 0)
    (views : Fin viewCount → InputView) (hwf : ∀ view, WF (views view))
    (hcells : ∀ view, ViewCells (views view)) {first : MicroOp}
    (hrep : ∀ view, ViewRep K (views view) (viewStateOf x view).1.1
      (first, (viewStateOf x view).1.2.2) (viewStateOf x view).2)
    (howed : ∀ view, (viewStateOf x view).1.2.2.2.2 = 0) (last : MicroOp) (view : Fin viewCount) :
    ViewRep K (viewApply (commandOfLetter x.1.2.1) (views view))
        (viewStateOf (machineIter viewCount hK inputs x 11) view).1.1
        (last, (viewStateOf (machineIter viewCount hK inputs x 11) view).1.2.2)
        (viewStateOf (machineIter viewCount hK inputs x 11) view).2 ∧
      (viewStateOf (machineIter viewCount hK inputs x 11) view).1.2.2.2.2.val = 0 := by
  refine viewSlot_sound (Fin 2) hK (hwf view) (hcells view) (commandOfLetter x.1.2.1)
    (fun count => viewStateOf (machineIter viewCount hK inputs x count) view) ?_ (hrep view)
    (howed view) last
  intro step hstep
  obtain ⟨-, hslotAt, hcurrentAt⟩ :=
    machineIter_registers viewCount hK inputs x hstarted hslot step (by omega)
  have hview := machine_viewStep viewCount hK (machineIter viewCount hK inputs x step)
    (inputs step) view
  have hslotEq : (machineIter viewCount hK inputs x step).1.2.2.2.1 = ⟨step, hstep⟩ :=
    Fin.ext hslotAt
  rw [hslotEq, hcurrentAt] at hview
  exact hview

#print axioms machineInit
#print axioms machineSlot

end Machine

end PalPeg.ConcreteLocalMachine
