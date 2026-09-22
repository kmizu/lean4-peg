import PalPeg.LocalViewsMachine
import PalPeg.LocalSysConcrete

/-!
# An abstract input head on twelve tapes

The head component of the relation between an abstract state and a configuration of the physical
machine: an abstract `PlaceHead` is the abstraction (`absHead' · []`) of some well-formed view
that the twelve tapes of a view of the machine represent, with nothing owed.  The letters that
have not arrived are in nobody's `incoming`, so the pending list is empty.

One real step of the fused machine on an input letter is the abstract arrival `arrivePH` at
every head; on no input every head stays.  The first real step, from blank tapes, is the arrival
at the head of the empty view.
-/

set_option autoImplicit false

namespace PalPeg.ConcreteLocalMachine

open PalPeg
open PalPeg.LocalInputView
open PalPeg.LocalViewCells
open PalPeg.LocalArrival (absHead' absHead'_arrive)
open PalPeg.GalilTickArrive (arrivePH)
open PalPeg.GalilScaffoldInputHead (PlaceHead)
open PalPeg.CloseoutCoreStep (Γc blankc)
open PalPeg.CloseoutCoreEnc12 (compStep)
open PalPeg.LocalStepFusion (iterRule iterRadius)

/-- The twelve tapes and the control of a view represent the abstract head `head`. -/
def HeadRep (margin : ℕ) (head : PlaceHead) (state : ViewState) : Prop :=
  ∃ (v : InputView) (first : MicroOp), WF v ∧ ViewCells v ∧ absHead' v [] = head ∧
    ViewRep margin v state.1.1 (first, state.1.2.2) state.2 ∧ state.1.2.2.2.2 = 0

/-- The abstract head after the command of a slot. -/
def headAfter : Option (Fin 2) → PlaceHead → PlaceHead
  | some a, head => arrivePH a head
  | none, head => head

theorem absHead'_viewApply_commandOfLetter {v : InputView} (hwf : WF v)
    (input : Option (Fin 2)) :
    absHead' (viewApply (commandOfLetter input) v) [] = headAfter input (absHead' v []) := by
  cases input with
  | none => rfl
  | some a =>
    show absHead' (arrive a v) [] = arrivePH a (absHead' v [])
    rw [absHead'_arrive hwf a [], ← PalPeg.LocalSysConcrete.absHead'_append v [] a]
    rfl

theorem wf_viewApply_commandOfLetter {v : InputView} (hwf : WF v) (hcells : ViewCells v)
    (input : Option (Fin 2)) :
    WF (viewApply (commandOfLetter input) v) ∧ ViewCells (viewApply (commandOfLetter input) v) := by
  cases input with
  | none => exact ⟨hwf, hcells⟩
  | some a => exact ⟨WF_arrive hwf a, viewCells_arrive hwf hcells a⟩

section Machine

variable {K : ℕ}

/-- **One real step of the fused machine is the abstract arrival at every head** (and nothing on
a step without input). -/
theorem headRep_machineSlot (viewCount : ℕ) (hK : 2 ≤ K) {margin : ℕ} (hmarginLe : K ≤ margin)
    (hfused : iterRadius K 11 ≤ margin) (x : MachineState viewCount) (hslot : x.1.1 = 0)
    (input : Option (Fin 2)) (heads : Fin viewCount → PlaceHead)
    (hrep : ∀ view, HeadRep margin (heads view) (viewStateOf x view)) :
    ((compStep (iterRule (machineRule viewCount hK) 11)).apply blankc x input).1.1 = 0 ∧
      ∀ view, HeadRep margin (headAfter input (heads view))
        (viewStateOf ((compStep (iterRule (machineRule viewCount hK) 11)).apply blankc x input)
          view) := by
  choose views firsts hwf hcells habs hviewRep howed using hrep
  -- the micro-operation named in the representation is free: fix one for all views
  have hviewRep' : ∀ view, ViewRep margin (views view) (viewStateOf x view).1.1
      (MicroOp.incLength, (viewStateOf x view).1.2.2) (viewStateOf x view).2 := fun view =>
    ⟨(hviewRep view).gap, (hviewRep view).queue, (hviewRep view).back, (hviewRep view).near⟩
  obtain ⟨hslotNext, hviews⟩ := machineSlot viewCount hK hmarginLe hfused x hslot input views
    hwf hcells hviewRep' howed MicroOp.incLength
  refine ⟨hslotNext, fun view => ?_⟩
  obtain ⟨hwfNext, hcellsNext⟩ := wf_viewApply_commandOfLetter (hwf view) (hcells view) input
  refine ⟨viewApply (commandOfLetter input) (views view), MicroOp.incLength, hwfNext,
    hcellsNext, ?_, (hviews view).1, Fin.ext (hviews view).2⟩
  rw [absHead'_viewApply_commandOfLetter (hwf view), habs view]

/-- **The first real step, from blank tapes**, is the arrival at the head of the empty view. -/
theorem headRep_machineFirstSlot (viewCount : ℕ) (hK : 2 ≤ K) (input : Option (Fin 2)) :
    ((compStep (iterRule (machineRule viewCount hK) 11)).apply blankc
        (machineInitState viewCount) input).1.1 = 0 ∧
      ∀ view : Fin viewCount,
        HeadRep (iterRadius K 11) (headAfter input (absHead' emptyView []))
          (viewStateOf ((compStep (iterRule (machineRule viewCount hK) 11)).apply blankc
            (machineInitState viewCount) input) view) := by
  obtain ⟨hslotNext, hviews⟩ := machineFirstSlot viewCount hK input MicroOp.incLength
  refine ⟨hslotNext, fun view => ?_⟩
  obtain ⟨hwfNext, hcellsNext⟩ :=
    wf_viewApply_commandOfLetter WF_emptyView viewCells_emptyView input
  exact ⟨viewApply (commandOfLetter input) emptyView, MicroOp.incLength, hwfNext, hcellsNext,
    absHead'_viewApply_commandOfLetter WF_emptyView input, (hviews view).1,
    Fin.ext (hviews view).2⟩

#print axioms headRep_machineSlot
#print axioms headRep_machineFirstSlot

end Machine

end PalPeg.ConcreteLocalMachine
