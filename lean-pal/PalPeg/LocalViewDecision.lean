import PalPeg.LocalQueueInit
import PalPeg.LocalViewCells

/-!
# What a view does, chosen from three symbols

A view is laid on twelve tapes: the ten tapes of its queue, the stack `focus :: back`, and the
stack `near`.  One command to a view (`ViewCommand`) is decided from the gap bit of the control
and three symbols: the focus, the top of `near`, the head of the queue (`ViewTops`).  The decision
is one cell operation on each of the two stacks and at most one job of the queue.

Only letters are pushed: the sentinel is the bottom of `focus :: back` (`LocalViewCells`), so on a
tape it is one more seal.
-/

set_option autoImplicit false

namespace PalPeg.ConcreteLocalMachine

open PalPeg
open PalPeg.LocalInputView
open PalPeg.LocalViewCells
open PalPeg.CloseoutCoreEnc20 (Delta)
open PalPeg.RTQueue (Queue)

/-- The commands of a view.  `stepRight` / `stepLeft` are the two directions of
`repositionStep`; the direction is the sender's business. -/
inductive ViewCommand where
  | stay
  | arrive (a : Fin 2)
  | moveRight
  | moveLeft
  | stepRight
  | stepLeft
  deriving DecidableEq

def viewApply : ViewCommand → InputView → InputView
  | .stay, v => v
  | .arrive a, v => arrive a v
  | .moveRight, v => moveRight v
  | .moveLeft, v => moveLeftV v
  | .stepRight, v => stepRight v
  | .stepLeft, v => stepLeft v

inductive HeadMove where
  | stay
  | right
  | left
  deriving DecidableEq

/-- The move of the head and the next gap bit, from the command and the gap bit. -/
def headMoveOf : ViewCommand → Bool → HeadMove × Bool
  | .moveRight, true => (.right, false)
  | .moveRight, false => (.stay, true)
  | .moveLeft, true => (.stay, false)
  | .moveLeft, false => (.left, true)
  | .stepRight, gap => (.right, gap)
  | .stepLeft, gap => (.left, gap)
  | .stay, gap => (.stay, gap)
  | .arrive _, gap => (.stay, gap)

/-- The three symbols a view reads. -/
structure ViewTops where
  focus : Option (Fin 2)
  near : Option (Fin 2)
  front : Option (Fin 2)

def viewTops (v : InputView) : ViewTops :=
  ⟨v.focus, v.near.head?.bind id, RTQueue.head? v.far⟩

def backDeltaOf : HeadMove → ViewTops → Delta
  | .right, tops =>
    match tops.near with
    | some c => .push c
    | none =>
      match tops.front with
      | some a => .push a
      | none => .keep
  | .left, tops =>
    match tops.focus with
    | some _ => .pop
    | none => .keep
  | .stay, _ => .keep

def nearDeltaOf : HeadMove → ViewTops → Delta
  | .right, tops =>
    match tops.near with
    | some _ => .pop
    | none => .keep
  | .left, tops =>
    match tops.focus with
    | some a => .push a
    | none => .keep
  | .stay, _ => .keep

/-- The job of the queue: an arrival enqueues, a step to the right past `near` dequeues. -/
def queueJobOf : ViewCommand → HeadMove → ViewTops → Option QueueJob
  | .arrive a, _, _ => some (.snoc a)
  | _, .right, tops =>
    match tops.near, tops.front with
    | none, some _ => some .tail
    | _, _ => none
  | _, _, _ => none

def jobApply : Option QueueJob → Queue (Fin 2) → Queue (Fin 2)
  | none, q => q
  | some (.snoc a), q => RTQueue.snoc q a
  | some .tail, q => RTQueue.tail q

/-- The stack of the focus tape. -/
def backStack (v : InputView) : List (Option (Fin 2)) := v.focus :: v.back

/-- What a head move does to a view, as the three chosen operations. -/
structure MovedBy (move : HeadMove) (v v' : InputView) : Prop where
  back : backStack v' = cellApply (backDeltaOf move (viewTops v)) false (backStack v)
  near : v'.near = cellApply (nearDeltaOf move (viewTops v)) false v.near
  far : v'.far = jobApply (queueJobOf .stay move (viewTops v)) v.far
  gap : v'.gap = v.gap

theorem movedBy_stay (v : InputView) : MovedBy .stay v v := ⟨rfl, rfl, rfl, rfl⟩

theorem movedBy_stepRight {v : InputView} (hcells : ViewCells v) :
    MovedBy .right v (stepRight v) := by
  obtain ⟨nearLetters, hnear⟩ := near_letters hcells
  cases nearLetters with
  | cons c rest =>
    have hnear' : v.near = some c :: rest.map some := hnear
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [backStack, stepRight, viewTops, backDeltaOf, cellApply, hnear']
    · simp [stepRight, viewTops, nearDeltaOf, cellApply, hnear']
    · simp [stepRight, viewTops, queueJobOf, jobApply, hnear']
    · simp [stepRight, hnear']
  | nil =>
    have hnear' : v.near = [] := hnear
    cases hhead : RTQueue.head? v.far with
    | some a =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [backStack, stepRight, viewTops, backDeltaOf, cellApply, hnear', hhead]
      · simp [stepRight, viewTops, nearDeltaOf, cellApply, hnear', hhead]
      · simp [stepRight, viewTops, queueJobOf, jobApply, hnear', hhead]
      · simp [stepRight, hnear', hhead]
    | none =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [backStack, stepRight, viewTops, backDeltaOf, cellApply, hnear', hhead]
      · simp [stepRight, viewTops, nearDeltaOf, cellApply, hnear', hhead]
      · simp [stepRight, viewTops, queueJobOf, jobApply, hnear', hhead]
      · simp [stepRight, hnear', hhead]

theorem movedBy_stepLeft {v : InputView} (hcells : ViewCells v) :
    MovedBy .left v (stepLeft v) := by
  cases hback : v.back with
  | nil =>
    have hfocus : v.focus = none := (back_nil_iff_focus_none hcells).1 hback
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [backStack, stepLeft, viewTops, backDeltaOf, cellApply, hback, hfocus]
    · simp [stepLeft, viewTops, nearDeltaOf, cellApply, hback, hfocus]
    · simp [stepLeft, queueJobOf, jobApply, hback]
    · simp [stepLeft, hback]
  | cons c rest =>
    have hfocus : v.focus ≠ none := fun h => by
      have := (back_nil_iff_focus_none hcells).2 h
      rw [hback] at this
      cases this
    obtain ⟨a, ha⟩ : ∃ a, v.focus = some a := Option.ne_none_iff_exists'.1 hfocus
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [backStack, stepLeft, viewTops, backDeltaOf, cellApply, hback, ha]
    · simp [stepLeft, viewTops, nearDeltaOf, cellApply, hback, ha]
    · simp [stepLeft, queueJobOf, jobApply, hback]
    · simp [stepLeft, hback]

/-- **A command is the three operations chosen from the gap bit and the three symbols.** -/
theorem viewApply_observed {v : InputView} (hcells : ViewCells v) (command : ViewCommand) :
    backStack (viewApply command v)
        = cellApply (backDeltaOf (headMoveOf command v.gap).1 (viewTops v)) false (backStack v) ∧
      (viewApply command v).near
        = cellApply (nearDeltaOf (headMoveOf command v.gap).1 (viewTops v)) false v.near ∧
      (viewApply command v).far
        = jobApply (queueJobOf command (headMoveOf command v.gap).1 (viewTops v)) v.far ∧
      (viewApply command v).gap = (headMoveOf command v.gap).2 := by
  have hright := movedBy_stepRight hcells
  have hleft := movedBy_stepLeft hcells
  cases command with
  | stay => exact ⟨rfl, rfl, rfl, rfl⟩
  | arrive a => exact ⟨rfl, rfl, rfl, rfl⟩
  | stepRight =>
    refine ⟨hright.back, hright.near, hright.far, ?_⟩
    show (stepRight v).gap = _
    rw [hright.gap]
    generalize v.gap = gap
    cases gap <;> rfl
  | stepLeft =>
    refine ⟨hleft.back, hleft.near, hleft.far, ?_⟩
    show (stepLeft v).gap = _
    rw [hleft.gap]
    generalize v.gap = gap
    cases gap <;> rfl
  | moveRight =>
    cases hgap : v.gap with
    | true =>
      have happly : viewApply .moveRight v = { stepRight v with gap := false } := by
        simp [viewApply, moveRight, hgap]
      rw [happly]
      exact ⟨hright.back, hright.near, hright.far, rfl⟩
    | false =>
      have happly : viewApply .moveRight v = { v with gap := true } := by
        simp [viewApply, moveRight, hgap]
      rw [happly]
      exact ⟨rfl, rfl, rfl, rfl⟩
  | moveLeft =>
    cases hgap : v.gap with
    | true =>
      have happly : viewApply .moveLeft v = { v with gap := false } := by
        simp [viewApply, moveLeftV, hgap]
      rw [happly]
      exact ⟨rfl, rfl, rfl, rfl⟩
    | false =>
      have happly : viewApply .moveLeft v = { stepLeft v with gap := true } := by
        simp [viewApply, moveLeftV, hgap]
      rw [happly]
      exact ⟨hleft.back, hleft.near, hleft.far, rfl⟩

#print axioms viewApply_observed

end PalPeg.ConcreteLocalMachine
