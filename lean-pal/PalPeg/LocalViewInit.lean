import PalPeg.LocalViewSlot

/-!
# The empty view on stacks of seals

A machine starts on blank tapes with its heads at the left edge.  Its first step does what it
does from blank tapes whose heads stand at the radius of its rule
(`compStep_apply_blankEdge`), and such a tape is a stack of seals.  Twelve of them represent the
empty view: the blank cell under the head of the tape `focus :: back` is the sentinel.
-/

set_option autoImplicit false

namespace PalPeg.ConcreteLocalMachine

open PalPeg
open PalPeg.LocalInputView
open PalPeg.CloseoutCoreStep (Γc blankc)
open PalPeg.CloseoutCoreEnc12 (Act ActRule compStep winAfter dAfter)
open PalPeg.Local (Window readWin pos sweep idx)
open PalPeg.Program (STape)

/-- The control a view starts in: no gap, no job, the initial control of the queue. -/
def viewInitControl : ViewControl := (false, none, initControl.2.2)

section ViewInit

/-- **Twelve stacks of `margin` seals represent the empty view.** -/
theorem viewRep_empty_of_seals {margin : ℕ} (hmarginPos : 1 ≤ margin)
    {tapes : Fin 12 → STape Γc}
    (htape : ∀ tape, StackTape (tapes tape) (List.replicate margin none)) (micro : MicroOp) :
    ViewRep margin emptyView viewInitControl.1 (micro, viewInitControl.2.2) tapes := by
  obtain ⟨height, rfl⟩ : ∃ height, margin = height + 1 := ⟨margin - 1, by omega⟩
  refine ⟨rfl, microRep_empty_of_seals (fun tape => htape _) micro,
    ⟨List.replicate height none, by rw [List.length_replicate], ?_⟩,
    ⟨List.replicate (height + 1) none, sealed_replicate _, by rw [List.length_replicate], ?_⟩⟩
  · exact htape backTape
  · exact htape nearTape

end ViewInit

end PalPeg.ConcreteLocalMachine
