import PalPeg.TextFeedSchedule

/-! Refinement of a suspended GS subprogram inside the feeder worker.
During a scanner call, queue representation changes cannot affect GS
conditions, and the physical call matches one original GS microstep. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.TextFeedScan
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangBank PalPeg.GSProg
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueProg
open PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.TextFeedControl PalPeg.TextFeedInput PalPeg.TextFeedAtomic PalPeg.TextFeedSchedule

variable {k : ℕ} {Terminal : Type}

def scanInterp (e : Env k) : Interp Unit Act8 Cond8 (Fin k) 8 :=
  I8 e.blank e.endSym e.mark e.startSym

def scanLift : Prog Act8 Cond8 → Prog WorkerAct WorkerCond :=
  Prog.map WorkerAct.scan (fun c => .inr (.inr c))

def scanStep (e : Env k) (s : Stack Act8 Cond8) (S : Stage k) :=
  microStep (scanInterp e) e.blank none (s, S)

theorem stageSymbols_rtapes (e : Env k) (qt : QT k) (m : Mode) (S : Stage k) (old : Fin k) :
    stageSymbols (fun j => (rtapes e qt m S old j).focus) = fun j => (S j).focus := by
  funext j
  simp only [stageSymbols, rtapes, TextFeedControl.tapes, Fin.castAddEmb_apply,
    Fin.natAddEmb_apply, Fin.append_left, Fin.append_right]

/-- GS conditions inspect only the eight scanner tapes. In particular, a
queue enqueue or a replacement of the arrival register cannot change them. -/
theorem workerCond_scan (e : Env k) (qt : QT k) (m : Mode) (S : Stage k) (old : Fin k)
    (c : Cond8) :
    workerCond e (.inr (.inr c)) (fun j => (rtapes e qt m S old j).focus) =
      evalConds (scanInterp e) (fun j => (S j).focus) c := by
  simp only [workerCond, stageSymbols_rtapes]
  rfl

theorem scan_step_control (e : Env k) (qt : QT k) (m : Mode) (S : Stage k) (old : Fin k)
    (s : Stack Act8 Cond8) (r : Stack WorkerAct WorkerCond) (a : Act8)
    (ha : (stepStack (evalConds (scanInterp e) (fun j => (S j).focus)) s).2 = some a) :
    stepStack (fun c => workerCond e c (fun j => (rtapes e qt m S old j).focus))
      (s.map scanLift ++ r) =
        ((scanStep e s S).1.map scanLift ++ r, some (.scan a)) := by
  exact (step_sim_map WorkerAct.scan (fun c => .inr (.inr c))
    (evalConds (scanInterp e) (fun j => (S j).focus))
    (fun c => workerCond e c (fun j => (rtapes e qt m S old j).focus))
    (workerCond_scan e qt m S old) s r).1 a ha

theorem scan_step_effect (e : Env k) (q : Queue (Fin k)) (S : Stage k)
    (s : Stack Act8 Cond8) (a : Act8)
    (ha : (stepStack (evalConds (scanInterp e) (fun j => (S j).focus)) s).2 = some a) :
    (effect e (.scan a) q S).2 = (scanStep e s S).2 := by
  simp only [effect, scanStep, microStep, ha, applyTrace, actVec]
  rfl

attribute [local irreducible] ProgLangBank.runChunk

/-- A non-arrival worker call refines one source GS step even when the
source program has a nonempty suspended continuation and an outer suffix. -/
theorem run_scan_step {e : Env k} (hc : Function.Injective e.code)
    (hmb : e.mark ≠ e.blank) (R rate : ℕ)
    (x : CallCtrl (programs e.blank e.mark) (Outer R rate) × (Fin 20 → STape (Fin k)))
    (hb : AtBoundary (programs e.blank e.mark) x.1.2.2.1)
    (hc0 : x.1.1.1 ≠ ⟨0, Nat.zero_lt_succ R⟩)
    {qt : QT k} {m : Mode} {q : Queue (Fin k)} (S : Stage k) (old : Fin k)
    (hx : x.2 = rtapes e qt m S old) (h : Ready e.blank e.mark qt m q)
    (s : Stack Act8 Cond8) (r : Stack WorkerAct WorkerCond)
    (hs : x.1.1.2.val = s.map scanLift ++ r) (a : Act8)
    (ha : (stepStack (evalConds (scanInterp e) (fun j => (S j).focus)) s).2 = some a) :
    ∃ qt' m', (TextFeedSchedule.run (Terminal := Terminal) e R rate x).2 =
        rtapes e qt' m' (scanStep e s S).2 old ∧
      AtBoundary (programs e.blank e.mark)
        (TextFeedSchedule.run (Terminal := Terminal) e R rate x).1.2.2.1 ∧
      Ready e.blank e.mark qt' m' q ∧
      (TextFeedSchedule.run (Terminal := Terminal) e R rate x).1.1.2.val =
        (scanStep e s S).1.map scanLift ++ r := by
  have hm : stepStack (fun c => workerCond e c (fun j => (x.2 j).focus)) x.1.1.2.val =
      ((scanStep e s S).1.map scanLift ++ r, some (.scan a)) := by
    rw [hx, hs]
    exact scan_step_control e qt m S old s r a ha
  have hsel : decode (choose e R rate x.1.1 (fun j => (x.2 j).focus)).2 = .scan a := by
    simp only [TextFeedSchedule.choose, if_neg hc0, hm, Option.getD_some, workerLabel, decode_encode]
  have hallowed : TextFeedAtomic.allowed e.mark
      (decode (choose e R rate x.1.1 (fun j => (x.2 j).focus)).2) := by
    rw [hsel]; trivial
  obtain ⟨qt', m', ht, hb', hr⟩ := TextFeedAtomic.call_ready (Terminal := Terminal)
    hc hmb (choose e R rate) x hb S old hx h hallowed
  rw [hsel, scan_step_effect e q S s a ha] at ht
  rw [hsel] at hr
  refine ⟨qt', m', ht, hb', hr, ?_⟩
  simp only [TextFeedSchedule.run, callRun, TextFeedSchedule.choose, if_neg hc0, stepCtrlS_val, hm]

/-- info: 'PalPeg.TextFeedScan.run_scan_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_scan_step

/-- Any live prefix of the original GS program can be resumed in a worker
window. The statement keeps the remaining source continuation, not merely
the final tape values, so the next input frame can resume the same scan. -/
theorem run_scan_prefix {e : Env k} (hc : Function.Injective e.code)
    (hmb : e.mark ≠ e.blank) (R rate N : ℕ)
    (x : CallCtrl (programs e.blank e.mark) (Outer R rate) × (Fin 20 → STape (Fin k)))
    (hb : AtBoundary (programs e.blank e.mark) x.1.2.2.1)
    {qt : QT k} {m : Mode} {q : Queue (Fin k)} (S : Stage k) (old : Fin k)
    (hx : x.2 = rtapes e qt m S old) (h : Ready e.blank e.mark qt m q)
    (s : Stack Act8 Cond8) (r : Stack WorkerAct WorkerCond)
    (hs : x.1.1.2.val = s.map scanLift ++ r)
    (htrace : (trace (scanInterp e) e.blank (List.replicate N none) (s, S)).length = N)
    (hpos : N ≠ 0 → 0 < x.1.1.1.val) (hlen : x.1.1.1.val + N ≤ R + 1) :
    let y := (TextFeedSchedule.run (Terminal := Terminal) e R rate)^[N] x
    let u := runInputs (scanInterp e) e.blank (List.replicate N none) (s, S)
    ∃ qt' m', y.2 = rtapes e qt' m' u.2 old ∧
      AtBoundary (programs e.blank e.mark) y.1.2.2.1 ∧ Ready e.blank e.mark qt' m' q ∧
      y.1.1.2.val = u.1.map scanLift ++ r := by
  induction N generalizing x qt m S s with
  | zero => exact ⟨qt, m, hx, hb, h, hs⟩
  | succ N ih =>
    have hsome : ∃ a, (stepStack (evalConds (scanInterp e) (fun j => (S j).focus)) s).2 =
        some a := by
      cases hw : (stepStack (evalConds (scanInterp e) (fun j => (S j).focus)) s).2 with
      | some a => exact ⟨a, rfl⟩
      | none =>
        have hle := trace_length_le (scanInterp e) e.blank (List.replicate N none)
          (scanStep e s S)
        rw [List.replicate_succ, trace_cons, hw] at htrace
        simp only [List.nil_append, List.length_replicate] at htrace hle
        change (trace (scanInterp e) e.blank (List.replicate N none)
          (scanStep e s S)).length = N + 1 at htrace
        omega
    obtain ⟨a, ha⟩ := hsome
    have hc0 : x.1.1.1 ≠ ⟨0, Nat.zero_lt_succ R⟩ := by
      have hh := hpos (Nat.succ_ne_zero N)
      intro hz
      rw [hz] at hh
      simp at hh
    obtain ⟨qt', m', ht, hb', hr, hs'⟩ := run_scan_step (Terminal := Terminal)
      hc hmb R rate x hb hc0 S old hx h s r hs a ha
    have htrace' : (trace (scanInterp e) e.blank (List.replicate N none)
        (scanStep e s S)).length = N := by
      rw [List.replicate_succ, trace_cons, ha] at htrace
      simpa only [List.singleton_append, List.length_cons, Nat.succ.injEq, scanStep] using htrace
    have hnext (hn : N ≠ 0) : x.1.1.1.val + 1 < R + 1 := by omega
    have hp' : N ≠ 0 → 0 < (TextFeedSchedule.run (Terminal := Terminal) e R rate x).1.1.1.val := by
      intro hn
      rw [run_counter]
      simp only [nextPhase, dif_pos (hnext hn)]
      omega
    have hl' : (TextFeedSchedule.run (Terminal := Terminal) e R rate x).1.1.1.val + N ≤ R + 1 := by
      by_cases hn : N = 0
      · have hlt := (TextFeedSchedule.run (Terminal := Terminal) e R rate x).1.1.1.isLt
        omega
      · rw [run_counter]
        simp only [nextPhase, dif_pos (hnext hn)]
        omega
    have hz := ih (x := TextFeedSchedule.run (Terminal := Terminal) e R rate x)
      (qt := qt') (m := m') (S := (scanStep e s S).2) (s := (scanStep e s S).1)
      hb' ht hr hs' htrace' hp' hl'
    simpa only [Function.iterate_succ_apply, List.replicate_succ, runInputs_cons,
      scanStep, Prod.mk.eta] using hz

/-- info: 'PalPeg.TextFeedScan.run_scan_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_scan_prefix

noncomputable local instance : DecidableEq (AP k ⊕ Empty) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedInput.CT k ⊕ Fin k) := Classical.decEq _
noncomputable local instance (R rate : ℕ) : DecidableEq (Outer R rate) := Classical.decEq _

/-- While a long GS scan is still live, one real input frame enqueues the
new symbol and executes exactly R source GS instructions. Both the source
continuation and FIFO effect are retained for the next frame. -/
theorem busy_frame {e : Env k} (hc : Function.Injective e.code)
    (hmb : e.mark ≠ e.blank) (enc : Terminal → Fin k) (R rate : ℕ)
    (c : CallCtrl (programs e.blank e.mark) (Outer R rate))
    (hb : AtBoundary (programs e.blank e.mark) c.2.2.1)
    (hc0 : c.1.1 = ⟨0, Nat.zero_lt_succ R⟩)
    {qt : QT k} {m : Mode} {q : Queue (Fin k)} (S : Stage k) (old : Fin k)
    (h : Ready e.blank e.mark qt m q) (a : Terminal) (ha : enc a ≠ e.mark)
    (s : Stack Act8 Cond8) (r : Stack WorkerAct WorkerCond)
    (hs : c.1.2.val = s.map scanLift ++ r)
    (htrace : (trace (scanInterp e) e.blank (List.replicate R none) (s, S)).length = R) :
    let z := (TextFeedSchedule.machine e enc R rate).sRound
      { state := ((c, ⟨0, by omega⟩), ⟨0, by omega⟩), tape := rtapes e qt m S old } a
    let u := runInputs (scanInterp e) e.blank (List.replicate R none) (s, S)
    ∃ qt' m' c', z =
        { state := ((c', ⟨0, by omega⟩), ⟨0, by omega⟩), tape := rtapes e qt' m' u.2 (enc a) } ∧
      AtBoundary (programs e.blank e.mark) c'.2.2.1 ∧
      Ready e.blank e.mark qt' m' (snoc q (enc a)) ∧
      c'.1.2.val = u.1.map scanLift ++ r ∧
      c'.1.1 = ⟨0, Nat.zero_lt_succ R⟩ := by
  classical
  dsimp only
  rw [machine_round, capture_some]
  let x := (c, rtapes e qt m S (enc a))
  let x1 := TextFeedSchedule.run (Terminal := Terminal) e R rate x
  obtain ⟨qt1, m1, ht1, hb1, hr1, hw1⟩ := run_first_enqueue (Terminal := Terminal)
    hc hmb R rate x hb hc0 S (enc a) rfl h ha
  have hs1 : x1.1.1.2.val = s.map scanLift ++ r := by rw [hw1]; exact hs
  have hcount : x1.1.1.1 = nextPhase ⟨0, Nat.zero_lt_succ R⟩ := by
    rw [run_counter, hc0]
  have hpos : R ≠ 0 → 0 < x1.1.1.1.val := by
    intro hR
    have ht : (0 : ℕ) + 1 < R + 1 := by omega
    rw [hcount]
    simp only [nextPhase, dif_pos ht]
    omega
  have hlen : x1.1.1.1.val + R ≤ R + 1 := by
    by_cases hR : R = 0
    · have hh := x1.1.1.1.isLt; omega
    · have ht : (0 : ℕ) + 1 < R + 1 := by omega
      rw [hcount]
      simp only [nextPhase, dif_pos ht]
      omega
  obtain ⟨qt', m', ht, hb', hr, hs'⟩ := run_scan_prefix (Terminal := Terminal)
    hc hmb R rate R x1 hb1 S (enc a) ht1 hr1 s r hs1 htrace hpos hlen
  have hcnt := run_counter_frame (Terminal := Terminal) e R rate x hc0
  rw [Function.iterate_succ_apply] at hcnt ⊢
  refine ⟨qt', m', ((TextFeedSchedule.run (Terminal := Terminal) e R rate)^[R] x1).1,
    ?_, hb', hr, hs', hcnt⟩
  dsimp only [x1, x] at ht ⊢
  rw [ht]

/-- info: 'PalPeg.TextFeedScan.busy_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms busy_frame

/-- An action-producing run has action-producing prefixes and suffixes.
This supplies the live-prefix premise without assuming a bound on the
length of a whole GS operation. -/
theorem live_split (e : Env k) (s : Stack Act8 Cond8) (S : Stage k) (N M : ℕ)
    (h : (trace (scanInterp e) e.blank (List.replicate (N + M) none) (s, S)).length = N + M) :
    (trace (scanInterp e) e.blank (List.replicate N none) (s, S)).length = N ∧
      (trace (scanInterp e) e.blank (List.replicate M none)
        (runInputs (scanInterp e) e.blank (List.replicate N none) (s, S))).length = M := by
  rw [List.replicate_add, trace_append, List.length_append] at h
  have h₁ := trace_length_le (scanInterp e) e.blank (List.replicate N none) (s, S)
  have h₂ := trace_length_le (scanInterp e) e.blank (List.replicate M none)
    (runInputs (scanInterp e) e.blank (List.replicate N none) (s, S))
  simp only [List.length_replicate] at h₁ h₂
  omega

/-- A long scan may span arbitrarily many actual input frames. All those
arrivals are enqueued in order, while the source GS program advances by
exactly word.length*R primitive instructions. No whole-scan constant-time
premise or repeated input is used. -/
theorem busy_frames {e : Env k} (hc : Function.Injective e.code)
    (hmb : e.mark ≠ e.blank) (enc : Terminal → Fin k) (R rate : ℕ) (word : List Terminal)
    (c : CallCtrl (programs e.blank e.mark) (Outer R rate))
    (hb : AtBoundary (programs e.blank e.mark) c.2.2.1)
    (hc0 : c.1.1 = ⟨0, Nat.zero_lt_succ R⟩)
    {qt : QT k} {m : Mode} {q : Queue (Fin k)} (S : Stage k) (old : Fin k)
    (h : Ready e.blank e.mark qt m q)
    (s : Stack Act8 Cond8) (r : Stack WorkerAct WorkerCond)
    (hs : c.1.2.val = s.map scanLift ++ r)
    (htrace : (trace (scanInterp e) e.blank (List.replicate (word.length * R) none) (s, S)).length =
      word.length * R)
    (hall : ∀ a ∈ word, enc a ≠ e.mark) :
    let z := word.foldl (TextFeedSchedule.machine e enc R rate).sRound
      { state := ((c, ⟨0, by omega⟩), ⟨0, by omega⟩), tape := rtapes e qt m S old }
    let u := runInputs (scanInterp e) e.blank (List.replicate (word.length * R) none) (s, S)
    ∃ qt' m' c', z =
        { state := ((c', ⟨0, by omega⟩), ⟨0, by omega⟩),
          tape := rtapes e qt' m' u.2 (word.foldl (fun _ a => enc a) old) } ∧
      AtBoundary (programs e.blank e.mark) c'.2.2.1 ∧
      Ready e.blank e.mark qt' m' (word.foldl (fun q a => snoc q (enc a)) q) ∧
      c'.1.2.val = u.1.map scanLift ++ r ∧
      c'.1.1 = ⟨0, Nat.zero_lt_succ R⟩ := by
  classical
  induction word generalizing c qt m q S old s with
  | nil =>
    simp only [List.length_nil, Nat.zero_mul, List.replicate_zero, runInputs_nil,
      List.foldl_nil]
    exact ⟨qt, m, c, rfl, hb, h, hs, hc0⟩
  | cons a word ih =>
    have hsize : (a :: word).length * R = R + word.length * R := by
      simp only [List.length_cons, Nat.succ_mul]; omega
    rw [hsize] at htrace
    obtain ⟨hpre, htail⟩ := live_split e s S R (word.length * R) htrace
    obtain ⟨qt1, m1, c1, hz1, hb1, hr1, hs1, hc1⟩ := busy_frame
      hc hmb enc R rate c hb hc0 S old h a (hall a (List.mem_cons_self)) s r hs hpre
    have hz := ih (c := c1) (qt := qt1) (m := m1) (q := snoc q (enc a))
      (S := (runInputs (scanInterp e) e.blank (List.replicate R none) (s, S)).2)
      (old := enc a) (s := (runInputs (scanInterp e) e.blank (List.replicate R none) (s, S)).1)
      hb1 hc1 hr1 hs1 htail (fun b hb => hall b (List.mem_cons_of_mem a hb))
    simpa only [List.foldl_cons, hz1, hsize, List.replicate_add, runInputs_append,
      Prod.mk.eta] using hz

/-- info: 'PalPeg.TextFeedScan.busy_frames' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms busy_frames

theorem arrivals_fifo (enc : Terminal → Fin k) (word : List Terminal)
    (q : Queue (Fin k)) (h : RTQueue.Inv q) :
    toList (word.foldl (fun q a => snoc q (enc a)) q) = toList q ++ word.map enc := by
  simpa only [List.foldl_map] using toList_foldl_snoc (word.map enc) q h

/-- The live-prefix condition follows from the source program's existing
ExecK proof. No new bound on the GS step length is assumed. -/
theorem execK_live_prefix (e : Env k) (s : Stack Act8 Cond8) (S : Stage k)
    (tr : List (Fin 8 → Fin k × Move)) (he : ExecK (scanInterp e) e.blank s S tr)
    (N : ℕ) (hN : N ≤ tr.length) :
    (trace (scanInterp e) e.blank (List.replicate N none) (s, S)).length = N := by
  have ht := congrArg List.length (he [] (List.replicate tr.length none) (by simp)).1
  simp only [List.append_nil] at ht
  have hlen : N + (tr.length - N) = tr.length := by omega
  exact (live_split e s S N (tr.length - N) (by simpa only [hlen] using ht)).1

/-- At the exact source endpoint the GS prefix has no pending action. Its
normalization may be folded into the next outer worker instruction. -/
theorem execK_return (e : Env k) (s : Stack Act8 Cond8) (S : Stage k)
    (tr : List (Fin 8 → Fin k × Move)) (he : ExecK (scanInterp e) e.blank s S tr) :
    let u := runInputs (scanInterp e) e.blank (List.replicate tr.length none) (s, S)
    (stepStack (evalConds (scanInterp e) (fun j => (u.2 j).focus)) u.1).2 = none := by
  obtain ⟨s', hrun, heq⟩ := (he [] (List.replicate tr.length none) (by simp)).2
  simp only [List.append_nil] at hrun
  dsimp only
  rw [hrun]
  have hh := congrArg Prod.snd heq
  simpa only [stepStack_nil] using hh

/-- Completion of a GS prefix returns to the surrounding worker control.
The equality is for the next control step, so residual pure-control nodes
are not mistaken for an extra GS instruction. -/
theorem run_scan_return {e : Env k} (hc : Function.Injective e.code)
    (hmb : e.mark ≠ e.blank) (R rate N : ℕ)
    (x : CallCtrl (programs e.blank e.mark) (Outer R rate) × (Fin 20 → STape (Fin k)))
    (hb : AtBoundary (programs e.blank e.mark) x.1.2.2.1)
    {qt : QT k} {m : Mode} {q : Queue (Fin k)} (S : Stage k) (old : Fin k)
    (hx : x.2 = rtapes e qt m S old) (h : Ready e.blank e.mark qt m q)
    (s : Stack Act8 Cond8) (r : Stack WorkerAct WorkerCond)
    (hs : x.1.1.2.val = s.map scanLift ++ r)
    (htrace : (trace (scanInterp e) e.blank (List.replicate N none) (s, S)).length = N)
    (hpos : N ≠ 0 → 0 < x.1.1.1.val) (hlen : x.1.1.1.val + N ≤ R + 1)
    (hhalt : let u := runInputs (scanInterp e) e.blank (List.replicate N none) (s, S)
      (stepStack (evalConds (scanInterp e) (fun j => (u.2 j).focus)) u.1).2 = none) :
    let y := (TextFeedSchedule.run (Terminal := Terminal) e R rate)^[N] x
    let u := runInputs (scanInterp e) e.blank (List.replicate N none) (s, S)
    ∃ qt' m', y.2 = rtapes e qt' m' u.2 old ∧
      AtBoundary (programs e.blank e.mark) y.1.2.2.1 ∧ Ready e.blank e.mark qt' m' q ∧
      stepStack (fun c => workerCond e c (fun j => (y.2 j).focus)) y.1.1.2.val =
        stepStack (fun c => workerCond e c (fun j => (y.2 j).focus)) r := by
  obtain ⟨qt', m', ht, hb', hr, hs'⟩ := run_scan_prefix (Terminal := Terminal)
    hc hmb R rate N x hb S old hx h s r hs htrace hpos hlen
  refine ⟨qt', m', ht, hb', hr, ?_⟩
  rw [hs']
  apply (step_sim_map WorkerAct.scan (fun c => .inr (.inr c))
    (evalConds (scanInterp e) (fun j =>
      ((runInputs (scanInterp e) e.blank (List.replicate N none) (s, S)).2 j).focus))
    (fun c => workerCond e c (fun j =>
      (((TextFeedSchedule.run (Terminal := Terminal) e R rate)^[N] x).2 j).focus))
    ?_ _ r).2 hhalt
  intro c
  rw [ht]
  exact workerCond_scan e qt' m' _ old c

/-- info: 'PalPeg.TextFeedScan.run_scan_return' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_scan_return

/-- The existing GS correctness proof supplies the prefix/return premises
used above, as well as the exact final tape state. The cost is the actual
source trace length, not an assumed uniform bound on a whole GS scan. -/
theorem source_certificate {e : Env k} {v Text : List (Fin k)} {rate p₁ rem : ℕ}
    {ts : GSTapes.TapesState' k} {st : ScanState}
    (hk : 0 < rate) (hmb : e.mark ≠ e.blank) (hstart : e.startSym ∉ v)
    (hE : GSTapes.Encodes' e.blank e.startSym e.endSym e.mark v Text rate p₁ rem ts st)
    (hq : st.q ≤ v.length) :
    let cost := (GSTapes.program' e.blank e.endSym e.mark rate ts).length
    let u := runInputs (scanInterp e) e.blank (List.replicate cost none) ([scanProg rate], TS ts)
    (∀ N, N ≤ cost →
      (trace (scanInterp e) e.blank (List.replicate N none) ([scanProg rate], TS ts)).length = N) ∧
      u.2 = TS (GSTapes.applyActs' e.blank (GSTapes.program' e.blank e.endSym e.mark rate ts) ts) ∧
      (stepStack (evalConds (scanInterp e) (fun j => (u.2 j).focus)) u.1).2 = none := by
  have he : ExecK (scanInterp e) e.blank [scanProg rate] (TS ts)
      (avecs e.blank (GSTapes.program' e.blank e.endSym e.mark rate ts) ts) :=
    scanProg_exec (Terminal := Unit) hk hmb hstart hE hq
  refine ⟨?_, ?_, ?_⟩
  · intro N hN
    apply execK_live_prefix e [scanProg rate] (TS ts) _ he N
    simpa only [avecs_length] using hN
  · exact scanProg_tapes (Terminal := Unit) hk hmb hstart hE hq _ (by simp)
  · simpa only [avecs_length] using execK_return e [scanProg rate] (TS ts) _ he

/-- info: 'PalPeg.TextFeedScan.source_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_certificate

end PalPeg.TextFeedScan
