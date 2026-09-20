import PalPeg.LocalViewDecision

/-!
# A view on twelve tapes

Tapes `0`–`9` are the queue machine of `far`, tape `10` is the stack `focus :: back`, tape `11`
is the stack `near`.  The three symbols of `ViewTops` are the centre symbols of tape `10`, of
tape `11`, and of the tape the role tag assigns to the front of the queue.
-/

set_option autoImplicit false

namespace PalPeg.ConcreteLocalMachine

open PalPeg
open PalPeg.LocalInputView
open PalPeg.LocalViewCells
open PalPeg.CloseoutCoreStep (Γc blankc)
open PalPeg.CloseoutCoreEnc21 (SRole)
open PalPeg.CloseoutCoreEnc25 (RTag roleOf sbound_roleOf)
open PalPeg.Local (Window readWin)
open PalPeg.Program (STape)

def backTape : Fin 12 := 10

def nearTape : Fin 12 := 11

/-- The ten tapes of the queue among the twelve. -/
def queueTapeOfView (tape : Fin 10) : Fin 12 := Fin.castLE (by omega) tape

/-- The tape of the front of the queue among the twelve. -/
def frontTape (tag : RTag) : Fin 12 :=
  queueTapeOfView (Fin.castLE (by omega) (roleTape tag .front))

/-- **A view on twelve tapes.**  The gap bit is in the control; the stack tapes are at least
`K` high, which is the margin of `compStep_apply` (on the tape `focus :: back` the sentinel is
one of the `K` cells: a blank tape gives no more, and the sentinel is never popped). -/
structure ViewRep (K : ℕ) (v : InputView) (gap : Bool) (micro : MicroControl)
    (tapes : Fin 12 → STape Γc) : Prop where
  gap : gap = v.gap
  queue : MicroRep K v.far micro (fun tape => tapes (queueTapeOfView tape))
  back : ∃ bottom : List (Option (Fin 2)), K ≤ bottom.length + 1 ∧
    StackTape (tapes backTape) (backStack v ++ bottom)
  near : ∃ bottom : List (Option (Fin 2)), Sealed bottom ∧ K ≤ bottom.length ∧
    StackTape (tapes nearTape) (v.near ++ bottom)

section Observation

variable {K : ℕ}

/-- The three symbols, read from the windows. -/
def viewTopsOfWindows (tag : RTag) (windows : Fin 12 → Window Γc K) : ViewTops :=
  ⟨symLetter (centreSym (windows backTape)), symLetter (centreSym (windows nearTape)),
    symLetter (centreSym (windows (frontTape tag)))⟩

/-- **The windows of a represented view show its three symbols.** -/
theorem viewTopsOfWindows_eq {v : InputView} {gap : Bool} {micro : MicroControl}
    {tapes : Fin 12 → STape Γc} (hcells : ViewCells v) (hrep : ViewRep K v gap micro tapes) :
    viewTopsOfWindows micro.2.1 (fun tape => readWin blankc K (tapes tape)) = viewTops v := by
  obtain ⟨backBottom, hbackHeight, hbackTape⟩ := hrep.back
  obtain ⟨nearBottom, hnearSealed, hnearHeight, hnearTape⟩ := hrep.near
  obtain ⟨⟨stack, junk, bottom, -, hlays, hheight, htapes, -, -, -⟩, -⟩ := hrep.queue
  have hfocus : symLetter (centreSym (readWin blankc K (tapes backTape))) = v.focus := by
    have hbackLength : K ≤ (backStack v ++ backBottom).length := by
      simp only [backStack, List.length_append, List.length_cons]
      omega
    rw [hbackTape.centreSym_eq hbackLength, ← topLetter_eq_sym]
    rfl
  have hnear : symLetter (centreSym (readWin blankc K (tapes nearTape)))
      = v.near.head?.bind id := by
    obtain ⟨nearLetters, hletters⟩ := near_letters hcells
    have hnearLength : K ≤ (v.near ++ nearBottom).length := by
      simp only [List.length_append]
      omega
    rw [hnearTape.centreSym_eq hnearLength, ← topLetter_eq_sym, hletters,
      topLetter_sealed hnearSealed]
    cases nearLetters <;> rfl
  have hfront : symLetter (centreSym (readWin blankc K (tapes (frontTape micro.2.1))))
      = RTQueue.head? v.far := by
    have htape : StackTape (tapes (frontTape micro.2.1)) (stack (roleOf micro.2.1 .front)) := by
      have h := htapes (roleTape micro.2.1 .front) (by
        rw [roleTape_val]; exact sbound_roleOf micro.2.1 .front)
      rwa [roleTape_val] at h
    have hstack := hlays.1 .front
    have hfrontLength : K ≤ (stack (roleOf micro.2.1 .front)).length := by
      rw [hstack]
      have hjunk := hheight (roleOf micro.2.1 .front)
      simp only [List.length_append]
      omega
    rw [htape.centreSym_eq hfrontLength, ← topLetter_eq_sym, hstack,
      topLetter_sealed (hlays.2 _)]
    rfl
  show ViewTops.mk _ _ _ = ViewTops.mk _ _ _
  rw [hfocus, hnear, hfront]

#print axioms viewTopsOfWindows_eq

end Observation

end PalPeg.ConcreteLocalMachine
