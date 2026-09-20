import PalPeg.LocalQueueMicro

/-!
# The micro-programs of the queue

`RTQueue.snoc` and `RTQueue.tail` — the two operations an input view makes on its queue
(`LocalInputView.arrive`, `stepRight`) — are fixed lists of micro-operations of the machine of
`PalPeg.LocalQueueMicro`.  The two increments after each rotation step pay what a reversing step
owes to the lazy length counter; on the abstract queue they do nothing.
-/

set_option autoImplicit false

namespace PalPeg.ConcreteLocalMachine

open PalPeg
open PalPeg.CloseoutCoreEnc22 (tail_hrot)
open PalPeg.CloseoutCoreEnc25 (SOp sApply)
open PalPeg.RTQueue (Queue)

/-- The abstract effect of a list of micro-operations. -/
def runMicro (program : List MicroOp) (q : Queue (Fin 2)) : Queue (Fin 2) :=
  program.foldl (fun queue micro => microApply micro queue) q

/-- `RTQueue.check`: the rotation test, then two rotation steps each followed by the two
increments it may owe, then the install. -/
def checkProgram : List MicroOp :=
  [.checkStart, .sub .exec, .incLength, .incLength, .sub .exec, .incLength, .incLength,
    .sub .install]

def snocProgram (a : Fin 2) : List MicroOp := .sub (.snocPush a) :: checkProgram

/-- The program of a dequeue from a non-empty front. -/
def tailProgram : List MicroOp := .sub .tailPop :: .sub .inval :: checkProgram

theorem runMicro_check (q : Queue (Fin 2)) (hrot : q.lenf < q.lenr → q.state = .idle) :
    runMicro checkProgram q = RTQueue.check q := by
  rw [check_eq_sApply q hrot]
  by_cases hle : q.lenr ≤ q.lenf
  · simp [runMicro, checkProgram, microApply, abstractOp, hle]
  · simp [runMicro, checkProgram, microApply, abstractOp, hle]

/-- **An enqueue is the program `snocProgram`.** -/
theorem runMicro_snoc {q : Queue (Fin 2)} (hq : RTQueue.Inv q) (a : Fin 2) :
    runMicro (snocProgram a) q = RTQueue.snoc q a := by
  have hrot : (sApply (.snocPush a) q).lenf < (sApply (.snocPush a) q).lenr →
      (sApply (.snocPush a) q).state = .idle := (RTQueue.snoc_pinv hq a).rot
  show runMicro checkProgram (sApply (.snocPush a) q) = _
  rw [runMicro_check _ hrot]
  rfl

/-- **A dequeue from a non-empty front is the program `tailProgram`.** -/
theorem runMicro_tail {q : Queue (Fin 2)} (hq : RTQueue.Inv q) (hfront : q.front ≠ []) :
    runMicro tailProgram q = RTQueue.tail q := by
  have hpop : sApply .tailPop q = { q with lenf := q.lenf - 1, front := q.front.tail } := by
    show (if q.front = [] then q else _) = _
    rw [if_neg hfront]
  rw [tail_eq_sApply q hfront]
  show runMicro checkProgram (sApply .inval (sApply .tailPop q)) = _
  rw [runMicro_check]
  rw [hpop]
  exact tail_hrot q hq

#print axioms runMicro_snoc
#print axioms runMicro_tail

end PalPeg.ConcreteLocalMachine
