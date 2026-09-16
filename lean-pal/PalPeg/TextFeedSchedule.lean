import PalPeg.TextFeedAtomic

/-! A concrete feeder scheduler: capture one terminal, enqueue it once,
then resume a fixed number of worker calls. A worker is suspended only at
the boundaries of the bounded atomic calls, never inside a queue update. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.TextFeedSchedule
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangPersist2 PalPeg.ProgLangBank
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueProg
open PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.TextFeedControl PalPeg.TextFeedTiming PalPeg.TextFeedInput
open PalPeg.TextFeedAtomic

variable {k : ℕ} {Terminal : Type}

noncomputable local instance : DecidableEq (AP k ⊕ Empty) := Classical.decEq _
noncomputable local instance : DecidableEq (CT k ⊕ Fin k) := Classical.decEq _

inductive WorkerAct where
  | idle
  | supply
  | scan (a : GSProg.Act8)
  deriving DecidableEq, Fintype

def workerLabel : WorkerAct → Label k
  | .idle => .idle
  | .supply => .supply
  | .scan a => .scan a

theorem worker_allowed (mark : Fin k) (a : WorkerAct) :
    TextFeedAtomic.allowed mark (workerLabel a) := by cases a <;> trivial

abbrev WorkerCond := Unit ⊕ Test ⊕ GSProg.Cond8

def stageSymbols (σ : Fin 20 → Fin k) (j : Fin 8) : Fin k :=
  σ (Fin.castAddEmb 1 (Fin.natAddEmb 11 j))

def workerCond (e : Env k) : WorkerCond → (Fin 20 → Fin k) → Bool
  | .inl _, _ => true
  | .inr (.inl .blankText), σ => decide (stageSymbols σ GSTapes.tT = e.blank)
  | .inr (.inl .enabled), σ => decide (stageSymbols σ GSTapes.tP = e.endSym ∨
      stageSymbols σ GSTapes.tT ≠ e.blank)
  | .inr (.inr c), σ => GSProg.condOf8 e.endSym e.mark e.startSym c (stageSymbols σ)

/-- The GS loop remains in the outer finite continuation. Only a single GS
primitive is dispatched in any one worker call. -/
def worker (rate : ℕ) : Prog WorkerAct WorkerCond :=
  .loop (.inl ()) .idle
    (.seq (.ite (.inr (.inl .blankText)) (.act .supply) .skip)
      (.ite (.inr (.inl .enabled))
        (Prog.map WorkerAct.scan (fun c => .inr (.inr c)) (GSProg.scanProg rate)) .skip))

abbrev Outer (R rate : ℕ) := Fin (R + 1) × CtrlS (worker rate)

noncomputable local instance (R rate : ℕ) : DecidableEq (Outer R rate) := Classical.decEq _

noncomputable def encode (a : Label k) : Index k := Fintype.equivFin (Label k) a

@[simp] theorem decode_encode (a : Label k) : decode (encode a) = a := by
  exact Equiv.symm_apply_apply _ _

/-- Counter zero is reserved for enqueue. The worker continuation is not
advanced there. Other counters cannot dispatch an enqueue instruction. -/
noncomputable def choose (e : Env k) (R rate : ℕ)
    (c : Outer R rate) (σ : Fin 20 → Fin k) : Outer R rate × Index k :=
  let w := if c.1 = ⟨0, Nat.zero_lt_succ R⟩ then
      (c.2, encode (.enqueue (σ inputIdx)))
    else
      (stepCtrlS (worker rate) (fun b => workerCond e b σ) c.2,
        encode (workerLabel ((stepStack (fun b => workerCond e b σ) c.2.val).2.getD .idle)))
  ((nextPhase c.1, w.1), w.2)

theorem choose_zero (e : Env k) (R rate : ℕ) (c : CtrlS (worker rate))
    (σ : Fin 20 → Fin k) :
    choose e R rate (⟨0, Nat.zero_lt_succ R⟩, c) σ =
      ((nextPhase ⟨0, Nat.zero_lt_succ R⟩, c), encode (.enqueue (σ inputIdx))) := by
  simp only [choose, ↓reduceIte]

theorem input_focus (e : Env k) (qt : QT k) (m : Mode) (S : Stage k) (a : Fin k) :
    (rtapes e qt m S a inputIdx).focus = a := by
  simp only [rtapes, inputIdx, Fin.natAddEmb_apply, Fin.append_right, TextFeedInput.cell]

theorem choose_allowed (e : Env k) (R rate : ℕ) (c : Outer R rate)
    (σ : Fin 20 → Fin k) (h : σ inputIdx ≠ e.mark) :
    TextFeedAtomic.allowed e.mark (decode (choose e R rate c σ).2) := by
  unfold choose
  split_ifs with hc
  · simpa only [decode_encode, TextFeedAtomic.allowed] using h
  · simpa only [decode_encode] using worker_allowed e.mark
      ((stepStack (fun b => workerCond e b σ) c.2.val).2.getD .idle)

noncomputable def run (e : Env k) (R rate : ℕ) :=
  callRun (programs e.blank e.mark) (fun _ => interp (Terminal := Terminal) e)
    (choose e R rate) 48 e.blank

theorem run_counter (e : Env k) (R rate : ℕ)
    (x : CallCtrl (programs e.blank e.mark) (Outer R rate) × (Fin 20 → STape (Fin k))) :
    (run (Terminal := Terminal) e R rate x).1.1.1 = nextPhase x.1.1.1 := rfl

theorem run_counter_iterate (e : Env k) (R rate N : ℕ)
    (x : CallCtrl (programs e.blank e.mark) (Outer R rate) × (Fin 20 → STape (Fin k))) :
    ((run (Terminal := Terminal) e R rate)^[N] x).1.1.1 = nextPhase^[N] x.1.1.1 := by
  induction N with
  | zero => rfl
  | succ N ih => rw [Function.iterate_succ_apply', run_counter, ih,
      Function.iterate_succ_apply']

/-- The macro scheduler is synchronized again after one enqueue and R
worker calls, so the next external arrival cannot arrive mid-queue-call. -/
theorem run_counter_frame (e : Env k) (R rate : ℕ)
    (x : CallCtrl (programs e.blank e.mark) (Outer R rate) × (Fin 20 → STape (Fin k)))
    (h : x.1.1.1 = ⟨0, Nat.zero_lt_succ R⟩) :
    ((run (Terminal := Terminal) e R rate)^[R + 1] x).1.1.1 = ⟨0, Nat.zero_lt_succ R⟩ := by
  rw [run_counter_iterate, h, nextPhase_iterate_round]

def isEnqueue : Label k → Bool
  | .enqueue _ => true
  | _ => false

theorem choose_enqueues (e : Env k) (R rate : ℕ) (c : Outer R rate)
    (σ : Fin 20 → Fin k) :
    isEnqueue (decode (choose e R rate c σ).2) =
      decide (c.1 = ⟨0, Nat.zero_lt_succ R⟩) := by
  unfold choose
  split_ifs with h
  · simp only [decode_encode, isEnqueue, h, decide_true]
  · simp only [decode_encode, h, decide_false]
    cases (stepStack (fun b => workerCond e b σ) c.2.val).2.getD .idle <;> rfl

/-- Exactly call zero, and no later worker call in the same input frame,
dispatches an enqueue. This holds independently of tape contents. -/
theorem run_enqueues_once (e : Env k) (R rate N : ℕ) (hN : N < R + 1)
    (x : CallCtrl (programs e.blank e.mark) (Outer R rate) × (Fin 20 → STape (Fin k)))
    (hc0 : x.1.1.1 = ⟨0, Nat.zero_lt_succ R⟩) :
    let y := (run (Terminal := Terminal) e R rate)^[N] x
    isEnqueue (decode (choose e R rate y.1.1 (fun j => (y.2 j).focus)).2) = decide (N = 0) := by
  dsimp only
  rw [choose_enqueues, run_counter_iterate, hc0,
    nextPhase_iterate (Nat.zero_lt_succ R) N hN]
  simp only [Fin.mk.injEq]

attribute [local irreducible] ProgLangBank.runChunk

theorem run_ready {e : Env k} (hc : Function.Injective e.code)
    (hmb : e.mark ≠ e.blank) (R rate : ℕ)
    (x : CallCtrl (programs e.blank e.mark) (Outer R rate) × (Fin 20 → STape (Fin k)))
    (hb : AtBoundary (programs e.blank e.mark) x.1.2.2.1)
    {qt : QT k} {m : Mode} {q : Queue (Fin k)} (S : Stage k) (old : Fin k)
    (hx : x.2 = rtapes e qt m S old) (h : Ready e.blank e.mark qt m q)
    (ha : old ≠ e.mark) :
    ∃ qt' m' q' S', (run (Terminal := Terminal) e R rate x).2 = rtapes e qt' m' S' old ∧
      AtBoundary (programs e.blank e.mark) (run (Terminal := Terminal) e R rate x).1.2.2.1 ∧
      Ready e.blank e.mark qt' m' q' := by
  have hi : (x.2 inputIdx).focus ≠ e.mark := by rw [hx, input_focus]; exact ha
  obtain ⟨qt', m', ht, hb', hr⟩ := TextFeedAtomic.call_ready (Terminal := Terminal)
    hc hmb (choose e R rate) x hb S old hx h (choose_allowed e R rate x.1.1 _ hi)
  exact ⟨qt', m', _, _, ht, hb', hr⟩

theorem run_ready_iterate {e : Env k} (hc : Function.Injective e.code)
    (hmb : e.mark ≠ e.blank) (R rate N : ℕ)
    (x : CallCtrl (programs e.blank e.mark) (Outer R rate) × (Fin 20 → STape (Fin k)))
    (hb : AtBoundary (programs e.blank e.mark) x.1.2.2.1)
    {qt : QT k} {m : Mode} {q : Queue (Fin k)} (S : Stage k) (old : Fin k)
    (hx : x.2 = rtapes e qt m S old) (h : Ready e.blank e.mark qt m q)
    (ha : old ≠ e.mark) :
    ∃ qt' m' q' S', ((run (Terminal := Terminal) e R rate)^[N] x).2 = rtapes e qt' m' S' old ∧
      AtBoundary (programs e.blank e.mark)
        ((run (Terminal := Terminal) e R rate)^[N] x).1.2.2.1 ∧
      Ready e.blank e.mark qt' m' q' := by
  induction N with
  | zero => exact ⟨qt, m, q, S, hx, hb, h⟩
  | succ N ih =>
    obtain ⟨qt', m', q', S', ht, hb', hr⟩ := ih
    rw [Function.iterate_succ_apply']
    exact run_ready hc hmb R rate _ hb' S' old ht hr ha

/-- The first call enqueues the captured symbol and does not advance the
worker. Thus the register is used before any worker continuation resumes. -/
theorem run_first_enqueue {e : Env k} (hc : Function.Injective e.code)
    (hmb : e.mark ≠ e.blank) (R rate : ℕ)
    (x : CallCtrl (programs e.blank e.mark) (Outer R rate) × (Fin 20 → STape (Fin k)))
    (hb : AtBoundary (programs e.blank e.mark) x.1.2.2.1)
    (hc0 : x.1.1.1 = ⟨0, Nat.zero_lt_succ R⟩)
    {qt : QT k} {m : Mode} {q : Queue (Fin k)} (S : Stage k) (old : Fin k)
    (hx : x.2 = rtapes e qt m S old) (h : Ready e.blank e.mark qt m q)
    (ha : old ≠ e.mark) :
    ∃ qt' m', (run (Terminal := Terminal) e R rate x).2 = rtapes e qt' m' S old ∧
      AtBoundary (programs e.blank e.mark) (run (Terminal := Terminal) e R rate x).1.2.2.1 ∧
      Ready e.blank e.mark qt' m' (snoc q old) ∧
      (run (Terminal := Terminal) e R rate x).1.1.2 = x.1.1.2 := by
  have hsel : decode (choose e R rate x.1.1 (fun j => (x.2 j).focus)).2 = .enqueue old := by
    simp only [choose, hc0, ↓reduceIte, decode_encode, hx, input_focus]
  have hi : (x.2 inputIdx).focus ≠ e.mark := by rw [hx, input_focus]; exact ha
  obtain ⟨qt', m', ht, hb', hr⟩ := TextFeedAtomic.call_ready (Terminal := Terminal)
    hc hmb (choose e R rate) x hb S old hx h (choose_allowed e R rate x.1.1 _ hi)
  rw [hsel] at ht hr
  refine ⟨qt', m', ht, hb', hr, ?_⟩
  simp only [run, callRun, choose, hc0, ↓reduceIte]

/-- The actual arrival-bearing machine. Its fixed bound is 1+49*(R+1).
R is a machine parameter, not a bound depending on the pattern length. -/
noncomputable def machine (e : Env k) (enc : Terminal → Fin k) (R rate : ℕ) := by
  classical
  exact callFrameMachine (programs e.blank e.mark) (fun _ => interp e)
    (choose e R rate) 48 (R + 1) e.blank (by omega : 0 < 20)
    (⟨0, Nat.zero_lt_succ R⟩, startCtrlS (worker rate)) (encode .idle) (capture enc)

theorem machine_round (e : Env k) (enc : Terminal → Fin k) (R rate : ℕ)
    (c : CallCtrl (programs e.blank e.mark) (Outer R rate)) (T : Fin 20 → STape (Fin k))
    (a : Terminal) :
    (machine e enc R rate).sRound
      { state := ((c, ⟨0, by omega⟩), ⟨0, by omega⟩), tape := T } a =
      let y := (run (Terminal := Terminal) e R rate)^[R + 1]
        (c, arriveA e.blank (capture enc) (some a) T)
      { state := ((y.1, ⟨0, by omega⟩), ⟨0, by omega⟩), tape := y.2 } := by
  classical
  exact callFrameMachine_round (programs e.blank e.mark) (fun _ => interp e)
    (choose e R rate) 48 (R + 1) e.blank (by omega)
    (⟨0, Nat.zero_lt_succ R⟩, startCtrlS (worker rate)) (encode .idle) (capture enc) a c T

/-- Across an actual arrival-bearing frame the incoming register is kept
until the next frame, all queue calls finish, and the scheduler counter is
ready for the next enqueue. This is not yet a GS completion/deadline theorem. -/
theorem machine_round_ready {e : Env k} (hc : Function.Injective e.code)
    (hmb : e.mark ≠ e.blank) (enc : Terminal → Fin k) (R rate : ℕ)
    (c : CallCtrl (programs e.blank e.mark) (Outer R rate))
    (hb : AtBoundary (programs e.blank e.mark) c.2.2.1)
    (hc0 : c.1.1 = ⟨0, Nat.zero_lt_succ R⟩)
    {qt : QT k} {m : Mode} {q : Queue (Fin k)} (S : Stage k) (old : Fin k)
    (h : Ready e.blank e.mark qt m q) (a : Terminal) (ha : enc a ≠ e.mark) :
    let z := (machine e enc R rate).sRound
      { state := ((c, ⟨0, by omega⟩), ⟨0, by omega⟩), tape := rtapes e qt m S old } a
    ∃ qt' m' q' S', z.tape = rtapes e qt' m' S' (enc a) ∧
      z.state.1.1.1.1 = ⟨0, Nat.zero_lt_succ R⟩ ∧
      AtBoundary (programs e.blank e.mark) z.state.1.1.2.2.1 ∧
      Ready e.blank e.mark qt' m' q' := by
  classical
  dsimp only
  rw [machine_round, capture_some]
  obtain ⟨qt', m', q', S', ht, hb', hr⟩ := run_ready_iterate (Terminal := Terminal)
    hc hmb R rate (R + 1) (c, rtapes e qt m S (enc a)) hb S (enc a) rfl h ha
  exact ⟨qt', m', q', S', ht, run_counter_frame e R rate _ hc0, hb', hr⟩

/-- info: 'PalPeg.TextFeedSchedule.run_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_ready

/-- info: 'PalPeg.TextFeedSchedule.run_first_enqueue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_first_enqueue

/-- info: 'PalPeg.TextFeedSchedule.run_enqueues_once' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_enqueues_once

/-- info: 'PalPeg.TextFeedSchedule.machine_round_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms machine_round_ready

end PalPeg.TextFeedSchedule
