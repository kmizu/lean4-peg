import PalPeg.LocalViewSlot

/-!
# The first step of a view: from blank tapes to the empty view

A machine starts on blank tapes with its heads at the left edge, where `compStep_apply` has no
margin.  The first step of a view is a decision step on the command `stay` from the initial
control: on blank windows it makes no action on any of the twelve tapes, so the sweep from the
edge leaves every tape blank with its head at `K` (`sweep_blank_edge`).  Twelve such tapes
represent the empty view: the blank cell under the head of the tape `focus :: back` is the
sentinel.
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

variable {K : ℕ}

/-- From the initial control the command `stay` makes no action at step `0`. -/
theorem viewActs_init (Terminal : Type) (hK : 2 ≤ K) {slot : Fin 11} (hslot : slot.val = 0)
    (windows : Fin 12 → Window Γc K) (tape : Fin 12) :
    viewActs Terminal hK slot .stay viewInitControl windows tape = [] := by
  by_cases hqueue : tape.val < 10
  · have htape : tape = queueTapeOfView ⟨tape.val, hqueue⟩ := Fin.ext rfl
    rw [htape, viewActs_queue, slotMicroOp_zero hslot]
    exact programRule_acts_idle (Terminal := Terminal) hK currentOp_initControl rfl none
      (queueWindowsOfView windows) _
  · unfold viewActs
    rw [dif_neg hqueue, if_pos hslot]
    split <;> rfl

/-- From the initial control the command `stay` keeps the control at step `0`. -/
theorem viewNext_init (Terminal : Type) (hK : 2 ≤ K) {slot : Fin 11} (hslot : slot.val = 0)
    (windows : Fin 12 → Window Γc K) :
    viewNext Terminal hK slot .stay viewInitControl windows = viewInitControl := by
  unfold viewNext
  rw [if_pos hslot, slotMicroOp_zero hslot, microRule_nq_none hK _ none _ rfl]
  rfl

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

/-- **The first step of a view inside a larger machine.**  On blank tapes, from the initial
control, a step of the machine that agrees with `viewNext` / `viewActs` on the command `stay` at
step `0` keeps the control and leaves the twelve tapes representing the empty view. -/
theorem viewInit_of_apply {Terminal Q : Type} {tapeCount : ℕ} (ViewTerminal : Type)
    (hK : 2 ≤ K) (R : ActRule Terminal Q Γc tapeCount K) (embed : Fin 12 → Fin tapeCount)
    (project : Q → ViewControl) {slot : Fin 11} (hslot : slot.val = 0)
    (x : Q × (Fin tapeCount → STape Γc)) (input : Option Terminal)
    (hblank : ∀ tape, x.2 (embed tape) = STape.blankTape blankc)
    (hcontrol : project x.1 = viewInitControl)
    (hnq : project (R.nq x.1 input (fun tape => readWin blankc K (x.2 tape)))
      = viewNext ViewTerminal hK slot .stay (project x.1)
          (fun tape => readWin blankc K (x.2 (embed tape))))
    (hacts : ∀ tape, R.acts x.1 input (fun tape => readWin blankc K (x.2 tape)) (embed tape)
      = viewActs ViewTerminal hK slot .stay (project x.1)
          (fun tape => readWin blankc K (x.2 (embed tape))) tape)
    (micro : MicroOp) :
    project ((compStep R).apply blankc x input).1 = viewInitControl ∧
      ViewRep K emptyView viewInitControl.1 (micro, viewInitControl.2.2)
        (fun tape => ((compStep R).apply blankc x input).2 (embed tape)) := by
  refine ⟨?_, viewRep_empty_of_seals (by omega) (fun tape => ?_) micro⟩
  · show project (R.nq x.1 input _) = _
    rw [hnq, hcontrol, viewNext_init ViewTerminal hK hslot]
  · have hnone : R.acts x.1 input (fun tape => readWin blankc K (x.2 tape)) (embed tape) = [] := by
      rw [hacts tape, hcontrol, viewActs_init ViewTerminal hK hslot]
    show StackTape (sweep blankc K (x.2 (embed tape))
      (winAfter K (readWin blankc K (x.2 (embed tape)))
        (R.acts x.1 input (fun tape => readWin blankc K (x.2 tape)) (embed tape)))
      (dAfter K (readWin blankc K (x.2 (embed tape)))
        (R.acts x.1 input (fun tape => readWin blankc K (x.2 tape)) (embed tape)))) _
    rw [hnone, hblank tape]
    have hdisplacement :
        dAfter K (readWin blankc K (STape.blankTape blankc)) ([] : List (Act Γc)) = 0 := by
      unfold dAfter
      simp
    rw [hdisplacement]
    obtain ⟨hpos, hallBlank⟩ := sweep_blank_edge K (tape := STape.blankTape blankc) rfl
      allBlank_blankTape (window := winAfter K (readWin blankc K (STape.blankTape blankc)) [])
      (fun i => by
        show (readWin blankc K (STape.blankTape blankc)) (idx K (i : ℕ)) = blankc
        exact readWin_allBlank allBlank_blankTape _)
    exact stackTape_of_blank hpos hallBlank

#print axioms viewInit_of_apply

end ViewInit

end PalPeg.ConcreteLocalMachine
