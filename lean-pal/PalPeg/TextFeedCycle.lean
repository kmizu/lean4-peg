import PalPeg.TextFeedScan

/-! Control phases around a suspended GS scan: loop, optional supply, and
scan entry. These are transitions of the actual feeder worker, not an
external oracle deciding when a scan is ready. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.TextFeedCycle
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangBank PalPeg.GSProg
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueProg PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.TextFeedControl PalPeg.TextFeedInput PalPeg.TextFeedAtomic
open PalPeg.TextFeedSchedule PalPeg.TextFeedScan

variable {k : ℕ} {Terminal : Type}

def fillGate : Prog WorkerAct WorkerCond :=
  .ite (.inr (.inl .blankText)) (.act .supply) .skip

def scanGate (rate : ℕ) : Prog WorkerAct WorkerCond :=
  .ite (.inr (.inl .enabled)) (scanLift (scanProg rate)) .skip

def beforeFill (rate : ℕ) : Stack WorkerAct WorkerCond :=
  [.seq fillGate (scanGate rate), worker rate]

def afterFill (rate : ℕ) : Stack WorkerAct WorkerCond := [scanGate rate, worker rate]

def eval (e : Env k) (S : Stage k) : WorkerCond → Bool
  | .inl _ => true
  | .inr (.inl .blankText) => decide ((S GSTapes.tT).focus = e.blank)
  | .inr (.inl .enabled) => decide ((S GSTapes.tP).focus = e.endSym ∨ (S GSTapes.tT).focus ≠ e.blank)
  | .inr (.inr c) => evalConds (scanInterp e) (fun j => (S j).focus) c

theorem eval_rtapes (e : Env k) (qt : QT k) (m : Mode) (S : Stage k) (old : Fin k) :
    (fun c => workerCond e c (fun j => (rtapes e qt m S old j).focus)) = eval e S := by
  funext c
  rcases c with u | t | c
  · rfl
  · cases t <;> simp only [workerCond, stageSymbols_rtapes, eval]
  · exact workerCond_scan e qt m S old c

theorem loop_step (e : Env k) (S : Stage k) (rate : ℕ) :
    stepStack (eval e S) [worker rate] = (beforeFill rate, some .idle) := by
  rw [worker, stepStack_loop]
  rfl

theorem fill_step_blank (e : Env k) (S : Stage k) (rate : ℕ)
    (h : (S GSTapes.tT).focus = e.blank) :
    stepStack (eval e S) (beforeFill rate) = (afterFill rate, some .supply) := by
  simp only [beforeFill, fillGate, stepStack_seq, stepStack_ite, eval, h, decide_true,
    ite_true, stepStack_act, afterFill]

theorem fill_step_nonblank (e : Env k) (S : Stage k) (rate : ℕ)
    (h : (S GSTapes.tT).focus ≠ e.blank) :
    stepStack (eval e S) (beforeFill rate) = stepStack (eval e S) (afterFill rate) := by
  simp only [beforeFill, fillGate, stepStack_seq, stepStack_ite, eval, h, decide_false,
    Bool.false_eq_true, ite_false, stepStack_skip, afterFill]

theorem gate_enabled (e : Env k) (S : Stage k) (rate : ℕ)
    (h : (S GSTapes.tP).focus = e.endSym ∨ (S GSTapes.tT).focus ≠ e.blank) :
    stepStack (eval e S) (afterFill rate) =
      stepStack (eval e S) ([scanLift (scanProg rate)] ++ [worker rate]) := by
  simp only [afterFill, scanGate, stepStack_ite, eval, h, decide_true, ite_true,
    List.singleton_append]

theorem gate_disabled (e : Env k) (S : Stage k) (rate : ℕ)
    (h : ¬ ((S GSTapes.tP).focus = e.endSym ∨ (S GSTapes.tT).focus ≠ e.blank)) :
    stepStack (eval e S) (afterFill rate) = (beforeFill rate, some .idle) := by
  simp only [afterFill, scanGate, stepStack_ite, eval, h, decide_false, Bool.false_eq_true, ite_false,
    stepStack_skip]
  exact loop_step e S rate

attribute [local irreducible] ProgLangBank.runChunk

/-- A known worker control transition has exactly its specified atomic
effect. Queue/register tape details do not participate in this decision. -/
theorem run_worker_action {e : Env k} (hc : Function.Injective e.code)
    (hmb : e.mark ≠ e.blank) (R rate : ℕ)
    (x : CallCtrl (programs e.blank e.mark) (Outer R rate) × (Fin 20 → STape (Fin k)))
    (hb : AtBoundary (programs e.blank e.mark) x.1.2.2.1)
    (hc0 : x.1.1.1 ≠ ⟨0, Nat.zero_lt_succ R⟩)
    {qt : QT k} {m : Mode} {q : Queue (Fin k)} (S : Stage k) (old : Fin k)
    (hx : x.2 = rtapes e qt m S old) (h : Ready e.blank e.mark qt m q)
    (s' : Stack WorkerAct WorkerCond) (a : WorkerAct)
    (hs : stepStack (eval e S) x.1.1.2.val = (s', some a)) :
    ∃ qt' m', (TextFeedSchedule.run (Terminal := Terminal) e R rate x).2 =
        rtapes e qt' m' (effect e (workerLabel a) q S).2 old ∧
      AtBoundary (programs e.blank e.mark)
        (TextFeedSchedule.run (Terminal := Terminal) e R rate x).1.2.2.1 ∧
      Ready e.blank e.mark qt' m' (effect e (workerLabel a) q S).1 ∧
      (TextFeedSchedule.run (Terminal := Terminal) e R rate x).1.1.2.val = s' := by
  have hm : stepStack (fun c => workerCond e c (fun j => (x.2 j).focus)) x.1.1.2.val =
      (s', some a) := by rw [hx, eval_rtapes]; exact hs
  have hsel : decode (TextFeedSchedule.choose e R rate x.1.1 (fun j => (x.2 j).focus)).2 =
      workerLabel a := by
    simp only [TextFeedSchedule.choose, if_neg hc0, hm, Option.getD_some, decode_encode]
  have ha : TextFeedAtomic.allowed e.mark
      (decode (TextFeedSchedule.choose e R rate x.1.1 (fun j => (x.2 j).focus)).2) := by
    rw [hsel]; exact worker_allowed e.mark a
  obtain ⟨qt', m', ht, hb', hr⟩ := TextFeedAtomic.call_ready (Terminal := Terminal)
    hc hmb (TextFeedSchedule.choose e R rate) x hb S old hx h ha
  rw [hsel] at ht hr
  refine ⟨qt', m', ht, hb', hr, ?_⟩
  simp only [TextFeedSchedule.run, callRun, TextFeedSchedule.choose, if_neg hc0,
    stepCtrlS_val, hm]

/-- info: 'PalPeg.TextFeedCycle.run_worker_action' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_worker_action

def CallResult (e : Env k) (R rate : ℕ)
    (x : CallCtrl (programs e.blank e.mark) (Outer R rate) × (Fin 20 → STape (Fin k)))
    (q : Queue (Fin k)) (S : Stage k) (old : Fin k) (s : Stack WorkerAct WorkerCond) : Prop :=
  ∃ qt' m', (TextFeedSchedule.run (Terminal := Terminal) e R rate x).2 = rtapes e qt' m' S old ∧
    AtBoundary (programs e.blank e.mark) (TextFeedSchedule.run (Terminal := Terminal) e R rate x).1.2.2.1 ∧
    Ready e.blank e.mark qt' m' q ∧
    (TextFeedSchedule.run (Terminal := Terminal) e R rate x).1.1.2.val = s

/-- This accepts the return equivalence proved for a completed GS scan,
not just a syntactically singleton loop stack. -/
theorem run_loop {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (R rate : ℕ)
    (x : CallCtrl (programs e.blank e.mark) (Outer R rate) × (Fin 20 → STape (Fin k)))
    (hb : AtBoundary (programs e.blank e.mark) x.1.2.2.1)
    (hc0 : x.1.1.1 ≠ ⟨0, Nat.zero_lt_succ R⟩)
    {qt : QT k} {m : Mode} {q : Queue (Fin k)} (S : Stage k) (old : Fin k)
    (hx : x.2 = rtapes e qt m S old) (h : Ready e.blank e.mark qt m q)
    (hs : stepStack (eval e S) x.1.1.2.val = stepStack (eval e S) [worker rate]) :
    CallResult (Terminal := Terminal) e R rate x q S old (beforeFill rate) :=
  run_worker_action hc hmb R rate x hb hc0 S old hx h _ .idle (hs.trans (loop_step e S rate))

theorem run_supply {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (R rate : ℕ)
    (x : CallCtrl (programs e.blank e.mark) (Outer R rate) × (Fin 20 → STape (Fin k)))
    (hb : AtBoundary (programs e.blank e.mark) x.1.2.2.1)
    (hc0 : x.1.1.1 ≠ ⟨0, Nat.zero_lt_succ R⟩)
    {qt : QT k} {m : Mode} {q : Queue (Fin k)} (S : Stage k) (old : Fin k)
    (hx : x.2 = rtapes e qt m S old) (h : Ready e.blank e.mark qt m q)
    (hs : x.1.1.2.val = beforeFill rate) (hblank : (S GSTapes.tT).focus = e.blank) :
    CallResult (Terminal := Terminal) e R rate x
      (supplyEffect e q S).1 (supplyEffect e q S).2 old (afterFill rate) := by
  apply run_worker_action hc hmb R rate x hb hc0 S old hx h _ .supply
  rw [hs]; exact fill_step_blank e S rate hblank

theorem run_wait {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (R rate : ℕ)
    (x : CallCtrl (programs e.blank e.mark) (Outer R rate) × (Fin 20 → STape (Fin k)))
    (hb : AtBoundary (programs e.blank e.mark) x.1.2.2.1)
    (hc0 : x.1.1.1 ≠ ⟨0, Nat.zero_lt_succ R⟩)
    {qt : QT k} {m : Mode} {q : Queue (Fin k)} (S : Stage k) (old : Fin k)
    (hx : x.2 = rtapes e qt m S old) (h : Ready e.blank e.mark qt m q)
    (hs : x.1.1.2.val = afterFill rate)
    (hdisabled : ¬ ((S GSTapes.tP).focus = e.endSym ∨ (S GSTapes.tT).focus ≠ e.blank)) :
    CallResult (Terminal := Terminal) e R rate x q S old (beforeFill rate) := by
  apply run_worker_action hc hmb R rate x hb hc0 S old hx h _ .idle
  rw [hs]; exact gate_disabled e S rate hdisabled

theorem scan_has_action (ev : Cond8 → Bool) (rate : ℕ) :
    ∃ a, (stepStack ev [scanProg rate]).2 = some a := by
  cases hv : ev .matchOk with
  | false =>
    refine ⟨(GSTapes.tAn, false, .left), ?_⟩
    simp [scanProg, hv, PUT]
  | true =>
    refine ⟨(GSTapes.tP, true, .right), ?_⟩
    simp [scanProg, hv, advProg, KEEP]

theorem gate_scan_step (e : Env k) (S : Stage k) (rate : ℕ)
    (hen : (S GSTapes.tP).focus = e.endSym ∨ (S GSTapes.tT).focus ≠ e.blank)
    (a : Act8) (ha : (stepStack (evalConds (scanInterp e) (fun j => (S j).focus))
      [scanProg rate]).2 = some a) :
    stepStack (eval e S) (afterFill rate) =
      ((TextFeedScan.scanStep e [scanProg rate] S).1.map scanLift ++ [worker rate], some (.scan a)) := by
  rw [gate_enabled e S rate hen]
  exact (step_sim_map WorkerAct.scan (fun c => .inr (.inr c))
    (evalConds (scanInterp e) (fun j => (S j).focus)) (eval e S)
    (fun _ => rfl) [scanProg rate] [worker rate]).1 a ha

/-- Both entry routes (after supply or directly from a nonblank text cell)
perform exactly the first GS source instruction and retain its continuation. -/
theorem run_enter {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (R rate : ℕ)
    (x : CallCtrl (programs e.blank e.mark) (Outer R rate) × (Fin 20 → STape (Fin k)))
    (hb : AtBoundary (programs e.blank e.mark) x.1.2.2.1)
    (hc0 : x.1.1.1 ≠ ⟨0, Nat.zero_lt_succ R⟩)
    {qt : QT k} {m : Mode} {q : Queue (Fin k)} (S : Stage k) (old : Fin k)
    (hx : x.2 = rtapes e qt m S old) (h : Ready e.blank e.mark qt m q)
    (hs : x.1.1.2.val = afterFill rate ∨
      (x.1.1.2.val = beforeFill rate ∧ (S GSTapes.tT).focus ≠ e.blank))
    (hen : (S GSTapes.tP).focus = e.endSym ∨ (S GSTapes.tT).focus ≠ e.blank) :
    CallResult (Terminal := Terminal) e R rate x q
      (TextFeedScan.scanStep e [scanProg rate] S).2 old
      ((TextFeedScan.scanStep e [scanProg rate] S).1.map scanLift ++ [worker rate]) := by
  obtain ⟨a, ha⟩ := scan_has_action (evalConds (scanInterp e) (fun j => (S j).focus)) rate
  have hstep : stepStack (eval e S) x.1.1.2.val =
      ((TextFeedScan.scanStep e [scanProg rate] S).1.map scanLift ++ [worker rate], some (.scan a)) := by
    rcases hs with hs | ⟨hs, hnb⟩
    · rw [hs]; exact gate_scan_step e S rate hen a ha
    · rw [hs, fill_step_nonblank e S rate hnb]; exact gate_scan_step e S rate hen a ha
  have hh := run_worker_action (Terminal := Terminal) hc hmb R rate x hb hc0 S old hx h _ (.scan a) hstep
  simp only [workerLabel] at hh
  rw [scan_step_effect e q S [scanProg rate] a ha] at hh
  exact hh

/-- info: 'PalPeg.TextFeedCycle.run_enter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_enter

end PalPeg.TextFeedCycle
