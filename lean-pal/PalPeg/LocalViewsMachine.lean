import PalPeg.LocalViewInit
import PalPeg.LocalStepFusion

/-!
# The machine of several views

`viewCount` views on `viewCount * 12` tapes, one slot counter for all of them.  A slot is eleven
micro-steps; the machine that is run is their fusion `compStep (iterRule … 11)`, so one real step
is one slot, and an input letter reaches the first micro-step of its slot.  The command of a slot
is read there; the later micro-steps do not use it (`viewSlot_sound`).
-/

set_option autoImplicit false

namespace PalPeg.ConcreteLocalMachine

open PalPeg
open PalPeg.LocalInputView
open PalPeg.LocalViewCells
open PalPeg.CloseoutCoreStep (Γc blankc)
open PalPeg.CloseoutCoreEnc12 (Act ActRule compStep TEqG)
open PalPeg.Local (Window readWin pos)
open PalPeg.Program (STape)
open PalPeg.LocalStepFusion (iterRule iterRadius iterRadius_eq idealStep idealIter idealRun
  idealRun_step idealIter_eq_idealRun compStep_iterRule)

/-- The control: the slot counter and the controls of the views. -/
abbrev MachineControl (viewCount : ℕ) : Type := Fin 11 × (Fin viewCount → ViewControl)

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

section Machine

variable {K : ℕ}

/-- **One micro-step of the machine of several views.** -/
def machineRule (viewCount : ℕ) (hK : 2 ≤ K) :
    ActRule (Fin 2) (MachineControl viewCount) Γc (viewCount * 12) K where
  nq := fun control input windows =>
    (nextSlot control.1,
      fun view => viewNext (Fin 2) hK control.1 (commandOfLetter input) (control.2 view)
        (fun tape => windows (viewTape view tape)))
  acts := fun control input windows tape =>
    viewActs (Fin 2) hK control.1 (commandOfLetter input)
      (control.2 (finProdFinEquiv.symm tape).1)
      (fun viewTapeIndex => windows (viewTape (finProdFinEquiv.symm tape).1 viewTapeIndex))
      (finProdFinEquiv.symm tape).2
  len_le := fun _ _ _ _ => viewActs_length _ hK _ _ _ _ _

/-- The part of a state that belongs to a view. -/
def viewStateOf {viewCount : ℕ} (x : MachineState viewCount) (view : Fin viewCount) :
    ViewState :=
  (x.1.2 view, fun tape => x.2 (viewTape view tape))

/-- **An ideal micro-step is a `ViewStep` of every view**, to any tapes `TEqG`-equal to the
ideal ones. -/
theorem machine_viewStep (viewCount : ℕ) (hK : 2 ≤ K) (x : MachineState viewCount)
    (input : Option (Fin 2)) (view : Fin viewCount) (tapes' : Fin (viewCount * 12) → STape Γc)
    (htapes : ∀ tape, TEqG blankc
      ((idealStep (machineRule viewCount hK) blankc x input).2 tape) (tapes' tape)) :
    ViewStep (Fin 2) hK x.1.1 (commandOfLetter input) (viewStateOf x view)
      (viewStateOf ((idealStep (machineRule viewCount hK) blankc x input).1, tapes') view) := by
  refine ⟨rfl, fun tape _ => ?_⟩
  have hideal := htapes (viewTape view tape)
  have hacts : (machineRule viewCount hK).acts x.1 input
      (fun tape => readWin blankc K (x.2 tape)) (viewTape view tape)
      = viewActs (Fin 2) hK x.1.1 (commandOfLetter input) (x.1.2 view)
          (fun viewTapeIndex => readWin blankc K (x.2 (viewTape view viewTapeIndex))) tape := by
    show viewActs (Fin 2) hK _ _ (x.1.2 (finProdFinEquiv.symm (viewTape view tape)).1) _
      (finProdFinEquiv.symm (viewTape view tape)).2 = _
    unfold viewTape
    rw [Equiv.symm_apply_apply]
  rw [show (idealStep (machineRule viewCount hK) blankc x input).2 (viewTape view tape)
      = PalPeg.CloseoutCoreEnc12.actList blankc (x.2 (viewTape view tape))
          ((machineRule viewCount hK).acts x.1 input (fun tape => readWin blankc K (x.2 tape))
            (viewTape view tape)) from rfl, hacts] at hideal
  exact hideal

theorem idealStep_slot (viewCount : ℕ) (hK : 2 ≤ K) (x : MachineState viewCount)
    (input : Option (Fin 2)) :
    (idealStep (machineRule viewCount hK) blankc x input).1.1 = nextSlot x.1.1 :=
  rfl

/-- The slot counter along the ideal run of a slot. -/
theorem idealRun_slot (viewCount : ℕ) (hK : 2 ≤ K) (x : MachineState viewCount)
    (input : Option (Fin 2)) (hslot : x.1.1 = 0) :
    ∀ count, count < 11 →
      (idealRun (machineRule viewCount hK) blankc x input count).1.1.val = count
  | 0, _ => by
    rw [show idealRun (machineRule viewCount hK) blankc x input 0 = x from rfl, hslot]
    rfl
  | count + 1, hcount => by
    have hprevious := idealRun_slot viewCount hK x input hslot count (by omega)
    rw [idealRun_step, idealStep_slot]
    unfold nextSlot
    rw [dif_pos (by omega)]
    show (idealRun (machineRule viewCount hK) blankc x input count).1.1.val + 1 = _
    rw [hprevious]

/-- **A state that agrees with the ideal run of a slot is one slot of every view later.**  From
step `0` of a slot, every view goes to the view commanded by the input of the step, with nothing
owed, and the machine is at step `0` again. -/
theorem machineSlot_of_ideal (viewCount : ℕ) (hK : 2 ≤ K) {margin : ℕ} (hmarginLe : K ≤ margin)
    (x : MachineState viewCount) (hslot : x.1.1 = 0) (input : Option (Fin 2))
    (views : Fin viewCount → InputView) (hwf : ∀ view, WF (views view))
    (hcells : ∀ view, ViewCells (views view)) {first : MicroOp}
    (hrep : ∀ view, ViewRep margin (views view) (viewStateOf x view).1.1
      (first, (viewStateOf x view).1.2.2) (viewStateOf x view).2)
    (howed : ∀ view, (viewStateOf x view).1.2.2.2.2 = 0) (last : MicroOp)
    (real : MachineState viewCount)
    (hcontrol : real.1 = (idealIter (machineRule viewCount hK) blankc 11 x input).1)
    (htapes : ∀ tape, TEqG blankc
      ((idealIter (machineRule viewCount hK) blankc 11 x input).2 tape) (real.2 tape)) :
    real.1.1 = 0 ∧
      ∀ view : Fin viewCount,
        ViewRep margin (viewApply (commandOfLetter input) (views view))
          (viewStateOf real view).1.1 (last, (viewStateOf real view).1.2.2)
          (viewStateOf real view).2 ∧
        (viewStateOf real view).1.2.2.2.2.val = 0 := by
  rw [idealIter_eq_idealRun] at hcontrol htapes
  have hlastSlot := idealRun_slot viewCount hK x input hslot 10 (by omega)
  have hlastStep : idealRun (machineRule viewCount hK) blankc x input 11
      = idealStep (machineRule viewCount hK) blankc
          (idealRun (machineRule viewCount hK) blankc x input 10) none :=
    idealRun_step (machineRule viewCount hK) blankc x input 10
  rw [hlastStep] at hcontrol htapes
  refine ⟨?_, fun view => ?_⟩
  · rw [hcontrol, idealStep_slot]
    unfold nextSlot
    rw [dif_neg (by omega)]
  · let states : ℕ → ViewState := fun count =>
      if count < 11 then viewStateOf (idealRun (machineRule viewCount hK) blankc x input count) view
      else viewStateOf real view
    have hstates0 : states 0 = viewStateOf x view := rfl
    have hstates11 : states 11 = viewStateOf real view := rfl
    have hsound := viewSlot_sound (Fin 2) hK hmarginLe (hwf view) (hcells view)
      (fun count => commandOfLetter (if count = 0 then input else none)) states ?_
      (first := first) (by rw [hstates0]; exact hrep view) (by rw [hstates0]; exact howed view)
      last
    · rw [hstates11] at hsound
      exact hsound
    · intro step hstep
      have hslotAt := idealRun_slot viewCount hK x input hslot step hstep
      have hslotEq : (idealRun (machineRule viewCount hK) blankc x input step).1.1
          = ⟨step, hstep⟩ := Fin.ext hslotAt
      have hfrom : states step
          = viewStateOf (idealRun (machineRule viewCount hK) blankc x input step) view :=
        if_pos hstep
      rw [hfrom, ← hslotEq]
      by_cases hlast : step + 1 < 11
      · have hto : states (step + 1)
            = viewStateOf (idealRun (machineRule viewCount hK) blankc x input (step + 1)) view :=
          if_pos hlast
        rw [hto]
        exact machine_viewStep viewCount hK _ _ view _ (fun _ => ⟨rfl, fun _ => rfl⟩)
      · have hstepEq : step = 10 := by omega
        subst hstepEq
        have hto : states (10 + 1) = viewStateOf real view := rfl
        rw [hto]
        have hrealEq : real
            = ((idealStep (machineRule viewCount hK) blankc
                (idealRun (machineRule viewCount hK) blankc x input 10) none).1, real.2) :=
          Prod.ext hcontrol rfl
        rw [hrealEq]
        exact machine_viewStep viewCount hK _ _ view _ htapes

/-- **One real step of the fused machine is one slot of every view**, from a state whose views
are represented with the margin of the fused rule. -/
theorem machineSlot (viewCount : ℕ) (hK : 2 ≤ K) {margin : ℕ} (hmarginLe : K ≤ margin)
    (hfused : iterRadius K 11 ≤ margin) (x : MachineState viewCount) (hslot : x.1.1 = 0)
    (input : Option (Fin 2))
    (views : Fin viewCount → InputView) (hwf : ∀ view, WF (views view))
    (hcells : ∀ view, ViewCells (views view)) {first : MicroOp}
    (hrep : ∀ view, ViewRep margin (views view) (viewStateOf x view).1.1
      (first, (viewStateOf x view).1.2.2) (viewStateOf x view).2)
    (howed : ∀ view, (viewStateOf x view).1.2.2.2.2 = 0) (last : MicroOp) :
    ((compStep (iterRule (machineRule viewCount hK) 11)).apply blankc x input).1.1 = 0 ∧
      ∀ view : Fin viewCount,
        ViewRep margin (viewApply (commandOfLetter input) (views view))
          (viewStateOf ((compStep (iterRule (machineRule viewCount hK) 11)).apply blankc x input)
            view).1.1
          (last, (viewStateOf
            ((compStep (iterRule (machineRule viewCount hK) 11)).apply blankc x input)
            view).1.2.2)
          (viewStateOf ((compStep (iterRule (machineRule viewCount hK) 11)).apply blankc x input)
            view).2 ∧
        (viewStateOf ((compStep (iterRule (machineRule viewCount hK) 11)).apply blankc x input)
          view).1.2.2.2.2.val = 0 := by
  have hmargin : ∀ tape, iterRadius K 11 ≤ pos (x.2 tape) := by
    intro tape
    have hview := (hrep (finProdFinEquiv.symm tape).1).margin_le_pos hK hmarginLe
      (finProdFinEquiv.symm tape).2
    have htape : viewTape (finProdFinEquiv.symm tape).1 (finProdFinEquiv.symm tape).2 = tape :=
      finProdFinEquiv.apply_symm_apply tape
    have hpos : margin ≤ pos (x.2 tape) := by
      rw [← htape]
      exact hview
    omega
  obtain ⟨hcontrol, htapes⟩ := compStep_iterRule blankc (machineRule viewCount hK) 11 x input
    hmargin
  exact machineSlot_of_ideal viewCount hK hmarginLe x hslot input views hwf hcells hrep howed
    last _ hcontrol htapes

/-- The state a machine starts in: step `0` of a slot, the initial control of every view, blank
tapes with the heads on the left edge. -/
def machineInitState (viewCount : ℕ) : MachineState viewCount :=
  ((0, fun _ => viewInitControl), fun _ => STape.blankTape blankc)

/-- **The first real step needs no initialization**: from blank tapes the fused machine does
what it does from stacks of seals as high as its radius (`compStep_apply_blankEdge`), and those
represent the empty view.  So after the first step every view is the view commanded by the first
input, applied to the empty view, with the margin of the fused rule. -/
theorem machineFirstSlot (viewCount : ℕ) (hK : 2 ≤ K) (input : Option (Fin 2))
    (last : MicroOp) :
    ((compStep (iterRule (machineRule viewCount hK) 11)).apply blankc
        (machineInitState viewCount) input).1.1 = 0 ∧
      ∀ view : Fin viewCount,
        ViewRep (iterRadius K 11) (viewApply (commandOfLetter input) emptyView)
          (viewStateOf ((compStep (iterRule (machineRule viewCount hK) 11)).apply blankc
            (machineInitState viewCount) input) view).1.1
          (last, (viewStateOf ((compStep (iterRule (machineRule viewCount hK) 11)).apply blankc
            (machineInitState viewCount) input) view).1.2.2)
          (viewStateOf ((compStep (iterRule (machineRule viewCount hK) 11)).apply blankc
            (machineInitState viewCount) input) view).2 ∧
        (viewStateOf ((compStep (iterRule (machineRule viewCount hK) 11)).apply blankc
          (machineInitState viewCount) input) view).1.2.2.2.2.val = 0 := by
  have hradius : iterRadius K 11 = 11 * K := iterRadius_eq K 11
  let seals : Fin (viewCount * 12) → STape Γc := fun _ =>
    PalPeg.CloseoutCoreEnc18.dTape (List.replicate (iterRadius K 11) none) []
  have hsealsPos : ∀ tape, pos (seals tape) = iterRadius K 11 := fun _ => by
    show pos (PalPeg.CloseoutCoreEnc18.dTape _ _) = _
    rw [pos_dTape, List.length_replicate]
  have hsealsBlank : ∀ tape, AllBlank (seals tape) := fun _ => allBlank_dTape_seals _
  obtain ⟨hcontrol, htapes⟩ := compStep_apply_blankEdge (iterRule (machineRule viewCount hK) 11)
    (machineInitState viewCount).1 input (machineInitState viewCount).2 seals (fun _ => rfl)
    (fun _ => allBlank_blankTape) hsealsPos hsealsBlank
  have hideal := PalPeg.LocalStepFusion.iterRule_ideal blankc (machineRule viewCount hK) 11
    ((machineInitState viewCount).1, seals) input (fun tape => (hsealsPos tape).ge)
  generalize iterRule (machineRule viewCount hK) 11 = fused at hcontrol htapes hideal ⊢
  refine machineSlot_of_ideal viewCount hK (margin := iterRadius K 11) (by omega)
    ((machineInitState viewCount).1, seals) rfl input (fun _ => emptyView)
    (fun _ => WF_emptyView) (fun _ => viewCells_emptyView) (first := MicroOp.incLength)
    (fun view => viewRep_empty_of_seals (by omega)
      (fun tape => stackTape_of_blank (hsealsPos (viewTape view tape))
        (hsealsBlank (viewTape view tape))) MicroOp.incLength)
    (fun _ => rfl) last _ ?_ ?_
  · rw [← hideal]
    exact hcontrol
  · intro tape
    rw [← hideal]
    exact htapes tape

#print axioms machineSlot
#print axioms machineFirstSlot

end Machine

end PalPeg.ConcreteLocalMachine
