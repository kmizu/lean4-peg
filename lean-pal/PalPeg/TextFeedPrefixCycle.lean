import PalPeg.TextFeedPrefixMachine

/-! Exact source-continuation transitions of the atomic prefix worker.
These are not additional controller states: they name reachable stacks
already stored in CtrlS source by the finite machine. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPrefixCycle
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.TextFeedControl PalPeg.TextFeedPrefixAtomic

variable {k : ℕ}

def gate : Prog Act Cond := .ite .blankText .skip (.seq (.act (.uMove .right)) (.act .textRight))
def body : Prog Act Cond := .seq (.act .supply) gate
def loop : Prog Act Cond := .loop .notEndU .idle body
def rewindLoop : Prog Act Cond := .loop .notStartU (.uMove .left) .skip
def tail : Prog Act Cond := .seq rewindLoop (.act (.uMove .right))

def loopS : Stack Act Cond := [loop, tail]
def fillS : Stack Act Cond := [body, loop, tail]
def gateS : Stack Act Cond := [gate, loop, tail]
def rightS : Stack Act Cond := [.act .textRight, loop, tail]
def rewindS : Stack Act Cond := [.skip, rewindLoop, .act (.uMove .right)]

def tick (e : Env k) (z : Stack Act Cond × Model k) : Stack Act Cond × Model k :=
  let r := stepStack (modelEval e z.2) z.1
  (r.1, effect e (r.2.getD .idle) z.2)

theorem start_step (e : Env k) (D : Model k) :
    stepStack (modelEval e D) [source] = stepStack (modelEval e D) loopS := by
  rw [source, stepStack_seq]
  rfl

theorem loop_step (e : Env k) (D : Model k) (hu : D.U.focus ≠ e.endSym) :
    stepStack (modelEval e D) loopS = (fillS, some .idle) := by
  simp only [loopS, loop, stepStack_loop, modelEval, decide_eq_true hu, ↓reduceIte]
  rfl

theorem fill_step (e : Env k) (D : Model k) :
    stepStack (modelEval e D) fillS = (gateS, some .supply) := by
  rw [fillS, body, stepStack_seq, stepStack_act]
  rfl

theorem gate_ready_step (e : Env k) (D : Model k) (ht : (D.S GSTapes.tT).focus ≠ e.blank) :
    stepStack (modelEval e D) gateS = (rightS, some (.uMove .right)) := by
  simp only [gateS, gate, stepStack_ite, modelEval, decide_eq_false ht,
    Bool.false_eq_true, ↓reduceIte, stepStack_seq, stepStack_act]
  rfl

theorem gate_wait_step (e : Env k) (D : Model k)
    (ht : (D.S GSTapes.tT).focus = e.blank) (hu : D.U.focus ≠ e.endSym) :
    stepStack (modelEval e D) gateS = (fillS, some .idle) := by
  simp only [gateS, gate, stepStack_ite, modelEval, ht, decide_true, ↓reduceIte, stepStack_skip]
  exact loop_step e D hu

theorem right_step (e : Env k) (D : Model k) :
    stepStack (modelEval e D) rightS = (loopS, some .textRight) := by
  rw [rightS, stepStack_act]
  rfl

theorem end_step (e : Env k) (D : Model k) (hu : D.U.focus = e.endSym)
    (hse : e.startSym ≠ e.endSym) :
    stepStack (modelEval e D) loopS = (rewindS, some (.uMove .left)) := by
  have hs : D.U.focus ≠ e.startSym := by rw [hu]; exact hse.symm
  simp only [loopS, loop, stepStack_loop, modelEval, hu, ne_eq, not_true_eq_false,
    decide_false, Bool.false_eq_true, ↓reduceIte]
  rw [tail, stepStack_seq, rewindLoop, stepStack_loop]
  simp only [modelEval, decide_eq_true hs, ↓reduceIte]
  rfl

theorem rewind_more_step (e : Env k) (D : Model k) (hu : D.U.focus ≠ e.startSym) :
    stepStack (modelEval e D) rewindS = (rewindS, some (.uMove .left)) := by
  simp only [rewindS, stepStack_skip, rewindLoop, stepStack_loop, modelEval,
    decide_eq_true hu, ↓reduceIte]

theorem rewind_end_step (e : Env k) (D : Model k) (hu : D.U.focus = e.startSym) :
    stepStack (modelEval e D) rewindS = ([], some (.uMove .right)) := by
  simp only [rewindS, stepStack_skip, rewindLoop, stepStack_loop, modelEval, hu,
    ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte, stepStack_act]

theorem tick_of_step {e : Env k} {D : Model k} {s s' : Stack Act Cond} {a : Act}
    (h : stepStack (modelEval e D) s = (s', some a)) :
    tick e (s, D) = (s', effect e a D) := by
  simp only [tick, h, Option.getD_some]

theorem tick_four (e : Env k) (D : Model k) (hu : D.U.focus ≠ e.endSym)
    (ht : ((effect e .supply D).S GSTapes.tT).focus ≠ e.blank) :
    (tick e)^[4] (loopS, D) =
      (loopS, effect e .textRight (effect e (.uMove .right) (effect e .supply D))) := by
  change tick e (tick e (tick e (tick e (loopS, D)))) = _
  rw [tick_of_step (loop_step e D hu)]
  change tick e (tick e (tick e (fillS, D))) = _
  rw [tick_of_step (fill_step e D), tick_of_step (gate_ready_step e _ ht),
    tick_of_step (right_step e _)]

theorem tick_wait (e : Env k) (D : Model k) (hu : D.U.focus ≠ e.endSym)
    (ht : (D.S GSTapes.tT).focus = e.blank) (he : effect e .supply D = D) :
    (tick e)^[2] (fillS, D) = (fillS, D) := by
  change tick e (tick e (fillS, D)) = _
  rw [tick_of_step (fill_step e D), he, tick_of_step (gate_wait_step e D ht hu)]
  rfl

theorem tick_nil (e : Env k) (D : Model k) : tick e ([], D) = ([], D) := by
  simp only [tick, stepStack_nil, Option.getD_none, effect]

theorem tick_start (e : Env k) (D : Model k) : tick e ([source], D) = tick e (loopS, D) := by
  simp only [tick, start_step]

theorem tick_start_iterate (e : Env k) (D : Model k) (N : ℕ) (hN : 0 < N) :
    (tick e)^[N] ([source], D) = (tick e)^[N] (loopS, D) := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  rw [Function.iterate_succ_apply, Function.iterate_succ_apply, tick_start]

/-- The worker part of the actual arrival-bearing machine has exactly
this transition, including after a supply call that changes its next guard. -/
theorem machine_work_tick (e : Env k) (R : ℕ)
    (z : TextFeedPrefixMachine.Outer R × TextFeedPrefixMachine.Data k) (hz : z.1.1 ≠ 0) :
    let y := TextFeedPrefixMachine.modelStep e R z
    (y.1.2.2.val, y.2.worker) = tick e (z.1.2.2.val, z.2.worker) := by
  simp only [TextFeedPrefixMachine.modelStep, if_neg hz, TextFeedPrefixMachine.work, tick,
    stepCtrlS]

/-- info: 'PalPeg.TextFeedPrefixCycle.machine_work_tick' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms machine_work_tick

end PalPeg.TextFeedPrefixCycle
