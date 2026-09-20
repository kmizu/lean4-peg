import PalPeg.LocalViewLayout

/-!
# The decision step of a view

On the first step of a slot a view reads its three symbols and the gap bit, and performs the two
stack operations of `LocalViewDecision` on the tapes `focus :: back` and `near`.  The tape
actions are functions of the windows; on a represented view they take the two stack tapes to the
stacks of `viewApply command v`.
-/

set_option autoImplicit false

namespace PalPeg.ConcreteLocalMachine

open PalPeg
open PalPeg.LocalInputView
open PalPeg.LocalViewCells
open PalPeg.CloseoutCoreStep (Γc blankc)
open PalPeg.CloseoutCoreEnc12 (Act actList TEqG)
open PalPeg.CloseoutCoreEnc20 (Delta)
open PalPeg.CloseoutCoreEnc25 (RTag)
open PalPeg.Local (Window readWin)
open PalPeg.Program (STape)

/-- A cell operation that does not seal acts on the top part of a stack, as long as a pop finds a
cell there. -/
theorem cellApply_append (u : Delta) {stack : List (Option (Fin 2))}
    (bottom : List (Option (Fin 2))) (hpop : u = .pop → stack ≠ []) :
    cellApply u false (stack ++ bottom) = cellApply u false stack ++ bottom := by
  cases u with
  | keep => rfl
  | push a => rfl
  | pop =>
    cases stack with
    | nil => exact absurd rfl (hpop rfl)
    | cons cell rest => rfl

theorem near_ne_nil_of_pop {move : HeadMove} {v : InputView}
    (hpop : nearDeltaOf move (viewTops v) = .pop) : v.near ≠ [] := by
  intro hnil
  cases move with
  | stay => simp [nearDeltaOf] at hpop
  | right => simp [nearDeltaOf, viewTops, hnil] at hpop
  | left => cases hfocus : v.focus <;> simp [nearDeltaOf, viewTops, hfocus] at hpop

section DecisionStep

variable {K : ℕ}

/-- The actions on the tape `focus :: back`, from the windows. -/
def backActsOfWindows (command : ViewCommand) (gap : Bool) (tag : RTag)
    (windows : Fin 12 → Window Γc K) : List (Act Γc) :=
  cellActsOfTop (backDeltaOf (headMoveOf command gap).1 (viewTopsOfWindows tag windows)) false
    (centreSym (windows backTape))

/-- The actions on the tape `near`, from the windows. -/
def nearActsOfWindows (command : ViewCommand) (gap : Bool) (tag : RTag)
    (windows : Fin 12 → Window Γc K) : List (Act Γc) :=
  cellActsOfTop (nearDeltaOf (headMoveOf command gap).1 (viewTopsOfWindows tag windows)) false
    (centreSym (windows nearTape))

/-- The job of the queue, from the windows. -/
def queueJobOfWindows (command : ViewCommand) (gap : Bool) (tag : RTag)
    (windows : Fin 12 → Window Γc K) : Option QueueJob :=
  queueJobOf command (headMoveOf command gap).1 (viewTopsOfWindows tag windows)

/-- **The decision step on the two stack tapes.**  Tapes `TEqG`-equal to the results of the
chosen actions carry the stacks of `viewApply command v`, over bottoms still `K` high; the chosen
job of the queue and the next gap bit are those of `viewApply command v`. -/
theorem viewDecision_sound {v : InputView} {gap : Bool} {micro : MicroControl}
    {tapes : Fin 12 → STape Γc} (hcells : ViewCells v) (hrep : ViewRep K v gap micro tapes)
    (command : ViewCommand) {backTape' nearTape' : STape Γc}
    (hbackTape : TEqG blankc
      (actList blankc (tapes backTape)
        (backActsOfWindows command gap micro.2.1 (fun tape => readWin blankc K (tapes tape))))
      backTape')
    (hnearTape : TEqG blankc
      (actList blankc (tapes nearTape)
        (nearActsOfWindows command gap micro.2.1 (fun tape => readWin blankc K (tapes tape))))
      nearTape') :
    (∃ bottom : List (Option (Fin 2)), K ≤ bottom.length ∧
        StackTape backTape' (backStack (viewApply command v) ++ bottom)) ∧
      (∃ bottom : List (Option (Fin 2)), Sealed bottom ∧ K ≤ bottom.length ∧
        StackTape nearTape' ((viewApply command v).near ++ bottom)) ∧
      (viewApply command v).far
        = jobApply (queueJobOfWindows command gap micro.2.1
            (fun tape => readWin blankc K (tapes tape))) v.far ∧
      (viewApply command v).gap = (headMoveOf command gap).2 := by
  obtain ⟨hback, hnear, hfar, hgap⟩ := viewApply_observed hcells command
  have htops := viewTopsOfWindows_eq hcells hrep
  obtain ⟨backBottom, hbackHeight, hbackStack⟩ := hrep.back
  obtain ⟨nearBottom, hnearSealed, hnearHeight, hnearStack⟩ := hrep.near
  have hgapEq : gap = v.gap := hrep.gap
  have hbackLength : K ≤ (backStack v ++ backBottom).length := by
    simp only [backStack, List.length_append, List.length_cons]
    omega
  have hnearLength : K ≤ (v.near ++ nearBottom).length := by
    simp only [List.length_append]
    omega
  refine ⟨⟨backBottom, hbackHeight, ?_⟩, ⟨nearBottom, hnearSealed, hnearHeight, ?_⟩, ?_, ?_⟩
  · have hstep := hbackStack.cellApply
      (backDeltaOf (headMoveOf command v.gap).1 (viewTops v)) false
    rw [cellApply_append _ backBottom (fun _ => by simp [backStack]), ← hback,
      ← hbackStack.centreSym_eq hbackLength] at hstep
    refine hstep.of_teqG ?_
    unfold backActsOfWindows at hbackTape
    rwa [htops, hgapEq] at hbackTape
  · have hstep := hnearStack.cellApply
      (nearDeltaOf (headMoveOf command v.gap).1 (viewTops v)) false
    rw [cellApply_append _ nearBottom near_ne_nil_of_pop, ← hnear,
      ← hnearStack.centreSym_eq hnearLength] at hstep
    refine hstep.of_teqG ?_
    unfold nearActsOfWindows at hnearTape
    rwa [htops, hgapEq] at hnearTape
  · unfold queueJobOfWindows
    rw [htops, hgapEq]
    exact hfar
  · rw [hgapEq]
    exact hgap

#print axioms viewDecision_sound

end DecisionStep

end PalPeg.ConcreteLocalMachine
