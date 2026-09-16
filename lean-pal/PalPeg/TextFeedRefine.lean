import PalPeg.TextFeedCycleModel

/-! A reference invariant spanning every phase of the feeder worker.
The unbounded progress count and Machine' below are proof-only ghosts;
the implemented controller remains TextFeedSchedule.machine. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace PalPeg.TextFeedRefine
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangBank PalPeg.GSProg
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueProg PalPeg.RTQueueClosed
open PalPeg.TextFeedControl PalPeg.TextFeedInput PalPeg.TextFeedAtomic
open PalPeg.TextFeedSchedule PalPeg.TextFeedScan PalPeg.TextFeedCycle PalPeg.TextFeedCycleModel

variable {k : ℕ} {Terminal : Type}

inductive Phase where
  | loop
  | fill
  | gate
  | scan (progress : ℕ)

abbrev Phys (e : Env k) (R rate : ℕ) :=
  CallCtrl (programs e.blank e.mark) (Outer R rate) × (Fin 20 → STape (Fin k))

def cost (e : Env k) (rate : ℕ) (M : TextFeed.Machine' k) : ℕ :=
  (GSTapes.program' e.blank e.endSym e.mark rate M.ts).length

def source (e : Env k) (rate : ℕ) (M : TextFeed.Machine' k) (N : ℕ) :=
  runInputs (scanInterp e) e.blank (List.replicate N none) ([scanProg rate], TS M.ts)

theorem source_succ (e : Env k) (rate : ℕ) (M : TextFeed.Machine' k) (N : ℕ) :
    source e rate M (N + 1) =
      TextFeedScan.scanStep e (source e rate M N).1 (source e rate M N).2 := by
  simp only [source, List.replicate_add, runInputs_append]
  rfl

theorem source_one (e : Env k) (rate : ℕ) (M : TextFeed.Machine' k) :
    source e rate M 1 = TextFeedScan.scanStep e [scanProg rate] (TS M.ts) := rfl

def stage (e : Env k) (rate : ℕ) (M : TextFeed.Machine' k) : Phase → Stage k
  | .scan N => (source e rate M N).2
  | _ => TS M.ts

def control (e : Env k) (rate : ℕ) (M : TextFeed.Machine' k)
    (ph : Phase) (s : Stack WorkerAct WorkerCond) : Prop :=
  match ph with
  | .loop => stepStack (TextFeedCycle.eval e (TS M.ts)) s =
      stepStack (TextFeedCycle.eval e (TS M.ts)) [worker rate]
  | .fill => s = beforeFill rate
  | .gate => s = afterFill rate
  | .scan N => s = (source e rate M N).1.map scanLift ++ [worker rate]

def pending (e : Env k) (v : List (Fin k)) (rate : ℕ) (M : TextFeed.Machine' k) : Phase → Prop
  | .scan N => N ≤ cost e rate M ∧ (M.st.q ≠ v.length → M.st.pos + M.st.q < M.m)
  | _ => True

structure Sim (e : Env k) (v Text : List (Fin k)) (R rate p₁ rem n : ℕ)
    (M : TextFeed.Machine' k) (ph : Phase) (x : Phys e R rate) (old : Fin k) : Prop where
  reference : TextFeed.FeedInv' e.blank e.startSym e.endSym e.mark v Text rate p₁ rem n M
  bank : AtBoundary (programs e.blank e.mark) x.1.2.2.1
  ctrl : control e rate M ph x.1.1.2.val
  work : pending e v rate M ph
  tapes : ∃ qt m, x.2 = rtapes e qt m (stage e rate M ph) old ∧ Ready e.blank e.mark qt m M.Q

noncomputable def advance (e : Env k) (v Text : List (Fin k)) (rate p₁ rem n : ℕ)
    (M : TextFeed.Machine' k) (ph : Phase) : TextFeed.Machine' k × Phase := by
  classical
  exact match ph with
  | .loop => (M, .fill)
  | .fill => if (TS M.ts GSTapes.tT).focus = e.blank
      then (TextFeed.fillIf' e.blank e.mark n M, .gate) else (M, .scan 1)
  | .gate => if GateEnabled e (TS M.ts) then (M, .scan 1) else (M, .fill)
  | .scan N => if N < cost e rate M then (M, .scan (N + 1))
      else (TextFeed.scanOne' e.blank e.endSym e.mark v rate p₁ rem Text M, .fill)

theorem certificate {e : Env k} {v Text : List (Fin k)} {rate p₁ rem n : ℕ}
    {M : TextFeed.Machine' k} (hk : 0 < rate) (hmb : e.mark ≠ e.blank) (hstart : e.startSym ∉ v)
    (hf : TextFeed.FeedInv' e.blank e.startSym e.endSym e.mark v Text rate p₁ rem n M) :
    (∀ N, N ≤ cost e rate M →
      (trace (scanInterp e) e.blank (List.replicate N none) ([scanProg rate], TS M.ts)).length = N) ∧
    (source e rate M (cost e rate M)).2 =
      TS (TextFeed.scanOne' e.blank e.endSym e.mark v rate p₁ rem Text M).ts ∧
    (stepStack (evalConds (scanInterp e) (fun j =>
      ((source e rate M (cost e rate M)).2 j).focus)) (source e rate M (cost e rate M)).1).2 = none :=
  source_certificate hk hmb hstart hf.scan hf.qle

theorem cost_pos {e : Env k} {v Text : List (Fin k)} {rate p₁ rem n : ℕ}
    {M : TextFeed.Machine' k} (hk : 0 < rate) (hmb : e.mark ≠ e.blank) (hstart : e.startSym ∉ v)
    (hf : TextFeed.FeedInv' e.blank e.startSym e.endSym e.mark v Text rate p₁ rem n M) :
    0 < cost e rate M := by
  have hh := (certificate hk hmb hstart hf).2.2
  by_contra hz
  have hz : cost e rate M = 0 := by omega
  rw [hz] at hh
  simp only [source, List.replicate_zero, runInputs_nil] at hh
  obtain ⟨a, ha⟩ := scan_has_action (evalConds (scanInterp e) (fun j => (TS M.ts j).focus)) rate
  rw [ha] at hh
  cases hh

theorem source_next_action {e : Env k} {v Text : List (Fin k)} {rate p₁ rem n N : ℕ}
    {M : TextFeed.Machine' k} (hk : 0 < rate) (hmb : e.mark ≠ e.blank) (hstart : e.startSym ∉ v)
    (hf : TextFeed.FeedInv' e.blank e.startSym e.endSym e.mark v Text rate p₁ rem n M)
    (hN : N < cost e rate M) :
    ∃ a, (stepStack (evalConds (scanInterp e) (fun j => ((source e rate M N).2 j).focus))
      (source e rate M N).1).2 = some a := by
  have hfull := (certificate hk hmb hstart hf).1 (N + 1) (by omega)
  have ht := (live_split e [scanProg rate] (TS M.ts) N 1 hfull).2
  change (trace (scanInterp e) e.blank [none] (source e rate M N)).length = 1 at ht
  cases ha : (stepStack (evalConds (scanInterp e) (fun j => ((source e rate M N).2 j).focus))
      (source e rate M N).1).2 with
  | some a => exact ⟨a, rfl⟩
  | none =>
    simp only [trace_cons, ha, trace_nil, List.append_nil, List.length_nil] at ht
    omega

theorem of_result {e : Env k} {v Text : List (Fin k)} {R rate p₁ rem n : ℕ}
    {M : TextFeed.Machine' k} {ph : Phase} {x : Phys e R rate} {old : Fin k}
    {s : Stack WorkerAct WorkerCond}
    (hf : TextFeed.FeedInv' e.blank e.startSym e.endSym e.mark v Text rate p₁ rem n M)
    (hw : pending e v rate M ph) (hc : control e rate M ph s)
    (hr : CallResult (Terminal := Terminal) e R rate x M.Q (stage e rate M ph) old s) :
    Sim e v Text R rate p₁ rem n M ph (TextFeedSchedule.run (Terminal := Terminal) e R rate x) old := by
  obtain ⟨qt, m, ht, hb, hq, hs⟩ := hr
  refine ⟨hf, hb, ?_, hw, qt, m, ht, hq⟩
  rw [hs]; exact hc

attribute [local irreducible] ProgLangBank.runChunk

/-- Every non-arrival macrocall refines one phase of the reference worker,
including start, optional supply, waiting, partial GS execution, and return.
The reference progress counter never appears in the implemented controller. -/
theorem worker_step {e : Env k} (hc : Function.Injective e.code)
    (hmb : e.mark ≠ e.blank) {v Text : List (Fin k)} {R rate p₁ rem n : ℕ}
    (hk : 0 < rate) (hv : 0 < v.length) (hend : e.endSym ∉ v) (hstart : e.startSym ∉ v)
    (hblank : e.blank ∉ Text) (hmark : e.mark ∉ Text) (hn : n ≤ Text.length)
    {M : TextFeed.Machine' k} {ph : Phase} {x : Phys e R rate} {old : Fin k}
    (h : Sim e v Text R rate p₁ rem n M ph x old)
    (hc0 : x.1.1.1 ≠ ⟨0, Nat.zero_lt_succ R⟩) :
    let z := advance e v Text rate p₁ rem n M ph
    Sim e v Text R rate p₁ rem n z.1 z.2
      (TextFeedSchedule.run (Terminal := Terminal) e R rate x) old := by
  classical
  obtain ⟨hf, hb, hctrl, hw, qt, m, ht, hq⟩ := h
  have hEnter (hT : x.2 = rtapes e qt m (TS M.ts) old)
      (hroute : x.1.1.2.val = afterFill rate ∨
        (x.1.1.2.val = beforeFill rate ∧ (TS M.ts GSTapes.tT).focus ≠ e.blank))
      (hg : GateEnabled e (TS M.ts)) :
      Sim e v Text R rate p₁ rem n M (.scan 1)
        (TextFeedSchedule.run (Terminal := Terminal) e R rate x) old := by
    have hr := run_enter (Terminal := Terminal) hc hmb R rate x hb hc0 (TS M.ts) old hT hq hroute hg
    apply of_result hf
      (show pending e v rate M (.scan 1) from
        ⟨cost_pos hk hmb hstart hf, scan_ready hend hblank hn hf hg⟩)
      (s := (TextFeedScan.scanStep e [scanProg rate] (TS M.ts)).1.map scanLift ++ [worker rate])
    · change _ = (source e rate M 1).1.map scanLift ++ [worker rate]
      rw [source_one]
    · simpa only [stage, source_one] using hr
  cases ph with
  | loop =>
    change Sim e v Text R rate p₁ rem n M .fill _ old
    exact of_result hf trivial rfl
      (run_loop (Terminal := Terminal) hc hmb R rate x hb hc0 (TS M.ts) old ht hq hctrl)
  | fill =>
    by_cases hblankT : (TS M.ts GSTapes.tT).focus = e.blank
    · simp only [advance, if_pos hblankT]
      have hr := run_supply (Terminal := Terminal) hc hmb R rate x hb hc0 (TS M.ts) old ht hq hctrl hblankT
      have heff := fill_effect_matches hblank hmark hn hf
      rw [fillEffect, if_pos hblankT] at heff
      rw [heff] at hr
      exact of_result (TextFeed.fillIf'_feedInv hmb hn hf) trivial rfl hr
    · simp only [advance, if_neg hblankT]
      exact hEnter ht (Or.inr ⟨hctrl, hblankT⟩) (Or.inr hblankT)
  | gate =>
    by_cases hg : GateEnabled e (TS M.ts)
    · simp only [advance, if_pos hg]
      exact hEnter ht (Or.inl hctrl) hg
    · simp only [advance, if_neg hg]
      exact of_result hf trivial rfl
        (run_wait (Terminal := Terminal) hc hmb R rate x hb hc0 (TS M.ts) old ht hq hctrl hg)
  | scan N =>
    change N ≤ cost e rate M ∧ (M.st.q ≠ v.length → M.st.pos + M.st.q < M.m) at hw
    by_cases hN : N < cost e rate M
    · simp only [advance, if_pos hN]
      obtain ⟨a, ha⟩ := source_next_action hk hmb hstart hf hN
      have hr := run_scan_step (Terminal := Terminal) hc hmb R rate x hb hc0
        (source e rate M N).2 old ht hq (source e rate M N).1 [worker rate] hctrl a ha
      apply of_result hf (show pending e v rate M (.scan (N + 1)) from ⟨by omega, hw.2⟩)
        (s := (TextFeedScan.scanStep e (source e rate M N).1 (source e rate M N).2).1.map scanLift ++
          [worker rate])
      · change _ = (source e rate M (N + 1)).1.map scanLift ++ [worker rate]
        rw [source_succ]
      · simpa only [CallResult, stage, source_succ] using hr
    · simp only [advance, if_neg hN]
      have hNc : N = cost e rate M := by omega
      subst N
      let M1 := TextFeed.scanOne' e.blank e.endSym e.mark v rate p₁ rem Text M
      have hf1 := TextFeed.scanOne'_feedInv hk hmb hv hend hn hw.2 hf
      obtain ⟨_, hfinal, hhalt⟩ := certificate hk hmb hstart hf
      have ht1 : x.2 = rtapes e qt m (TS M1.ts) old := by
        change x.2 = rtapes e qt m (source e rate M (cost e rate M)).2 old at ht
        rw [hfinal] at ht
        exact ht
      have hret : stepStack (TextFeedCycle.eval e (TS M1.ts)) x.1.1.2.val =
          stepStack (TextFeedCycle.eval e (TS M1.ts)) [worker rate] := by
        change x.1.1.2.val = (source e rate M (cost e rate M)).1.map scanLift ++ [worker rate] at hctrl
        rw [hctrl]
        apply (step_sim_map WorkerAct.scan (fun c => .inr (.inr c))
          (evalConds (scanInterp e) (fun j => ((source e rate M (cost e rate M)).2 j).focus))
          (TextFeedCycle.eval e (TS M1.ts)) ?_ _ [worker rate]).2 hhalt
        intro c
        simp only [TextFeedCycle.eval, hfinal]
        rfl
      exact of_result hf1 trivial rfl
        (run_loop (Terminal := Terminal) hc hmb R rate x hb hc0 (TS M1.ts) old ht1 hq hret)

/-- info: 'PalPeg.TextFeedRefine.worker_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms worker_step

@[simp] theorem stage_arrive (e : Env k) (rate : ℕ) (M : TextFeed.Machine' k) (ph : Phase) (a : Fin k) :
    stage e rate (TextFeed.arrive' e.blank e.mark a M) ph = stage e rate M ph := by
  cases ph <;> rfl

@[simp] theorem control_arrive (e : Env k) (rate : ℕ) (M : TextFeed.Machine' k)
    (ph : Phase) (a : Fin k) (s : Stack WorkerAct WorkerCond) :
    control e rate (TextFeed.arrive' e.blank e.mark a M) ph s = control e rate M ph s := by
  cases ph <;> rfl

@[simp] theorem pending_arrive (e : Env k) (v : List (Fin k)) (rate : ℕ)
    (M : TextFeed.Machine' k) (ph : Phase) (a : Fin k) :
    pending e v rate (TextFeed.arrive' e.blank e.mark a M) ph = pending e v rate M ph := by
  cases ph <;> rfl

/-- Enqueue preserves even an in-flight scan's reference snapshot and
progress; only the ghost FIFO and arrival count are advanced. -/
theorem arrival_step {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    {v Text : List (Fin k)} {R rate p₁ rem n : ℕ} (hmark : e.mark ∉ Text) (hn : n < Text.length)
    {M : TextFeed.Machine' k} {ph : Phase} {x : Phys e R rate} {a : Fin k}
    (ha : Text[n]? = some a) (h : Sim e v Text R rate p₁ rem n M ph x a)
    (hc0 : x.1.1.1 = ⟨0, Nat.zero_lt_succ R⟩) :
    Sim e v Text R rate p₁ rem (n + 1) (TextFeed.arrive' e.blank e.mark a M) ph
      (TextFeedSchedule.run (Terminal := Terminal) e R rate x) a := by
  obtain ⟨hf, hb, hctrl, hw, qt, m, ht, hq⟩ := h
  have ham : a ≠ e.mark := fun he => hmark (he ▸ List.mem_of_getElem? ha)
  obtain ⟨qt', m', ht', hb', hq', hc'⟩ := run_first_enqueue (Terminal := Terminal)
    hc hmb R rate x hb hc0 (stage e rate M ph) a ht hq ham
  refine ⟨TextFeed.arrive'_feedInv hmb hn ha hf, hb', ?_, ?_, qt', m', ?_, hq'⟩
  · rw [control_arrive, hc']; exact hctrl
  · rw [pending_arrive]; exact hw
  · simpa only [stage_arrive] using ht'

/-- The arrival hook changes just the register. It cannot disturb an
unfinished source scan or any logical worker phase. -/
theorem capture_sim {e : Env k} {v Text : List (Fin k)} {R rate p₁ rem n : ℕ}
    {M : TextFeed.Machine' k} {ph : Phase} {x : Phys e R rate} {old : Fin k}
    (h : Sim e v Text R rate p₁ rem n M ph x old) (enc : Terminal → Fin k) (a : Terminal) :
    Sim e v Text R rate p₁ rem n M ph
      (x.1, ProgLangPersist2.arriveA e.blank (capture enc) (some a) x.2) (enc a) := by
  obtain ⟨hf, hb, hctrl, hw, qt, m, ht, hq⟩ := h
  refine ⟨hf, hb, hctrl, hw, qt, m, ?_, hq⟩
  rw [ht, capture_some]

noncomputable def modelRun (e : Env k) (v Text : List (Fin k)) (rate p₁ rem n N : ℕ)
    (M : TextFeed.Machine' k) (ph : Phase) :=
  (fun z : TextFeed.Machine' k × Phase => advance e v Text rate p₁ rem n z.1 z.2)^[N] (M, ph)

/-- A complete worker window may cross any number of logical iteration
boundaries. The reference invariant survives all of them. -/
theorem worker_steps {e : Env k} (hc : Function.Injective e.code)
    (hmb : e.mark ≠ e.blank) {v Text : List (Fin k)} {R rate p₁ rem n : ℕ}
    (hk : 0 < rate) (hv : 0 < v.length) (hend : e.endSym ∉ v) (hstart : e.startSym ∉ v)
    (hblank : e.blank ∉ Text) (hmark : e.mark ∉ Text) (hn : n ≤ Text.length)
    (N : ℕ) {M : TextFeed.Machine' k} {ph : Phase} {x : Phys e R rate} {old : Fin k}
    (h : Sim e v Text R rate p₁ rem n M ph x old)
    (hpos : N ≠ 0 → 0 < x.1.1.1.val) (hlen : x.1.1.1.val + N ≤ R + 1) :
    let z := modelRun e v Text rate p₁ rem n N M ph
    Sim e v Text R rate p₁ rem n z.1 z.2
      ((TextFeedSchedule.run (Terminal := Terminal) e R rate)^[N] x) old := by
  induction N generalizing M ph x with
  | zero => exact h
  | succ N ih =>
    have hc0 : x.1.1.1 ≠ ⟨0, Nat.zero_lt_succ R⟩ := by
      have hh := hpos (Nat.succ_ne_zero N)
      intro hz; rw [hz] at hh; simp at hh
    have h1 := worker_step (Terminal := Terminal) hc hmb hk hv hend hstart hblank hmark hn h hc0
    have hnext (hN : N ≠ 0) : x.1.1.1.val + 1 < R + 1 := by omega
    have hp' : N ≠ 0 → 0 < (TextFeedSchedule.run (Terminal := Terminal) e R rate x).1.1.1.val := by
      intro hN
      rw [run_counter]
      simp only [nextPhase, dif_pos (hnext hN)]
      omega
    have hl' : (TextFeedSchedule.run (Terminal := Terminal) e R rate x).1.1.1.val + N ≤ R + 1 := by
      by_cases hN : N = 0
      · have hh := (TextFeedSchedule.run (Terminal := Terminal) e R rate x).1.1.1.isLt; omega
      · rw [run_counter]
        simp only [nextPhase, dif_pos (hnext hN)]
        omega
    have hz := ih h1 hp' hl'
    simpa only [modelRun, Function.iterate_succ_apply] using hz

/-- info: 'PalPeg.TextFeedRefine.worker_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms worker_steps

noncomputable local instance : DecidableEq (AP k ⊕ Empty) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedInput.CT k ⊕ Fin k) := Classical.decEq _
noncomputable local instance (R rate : ℕ) : DecidableEq (Outer R rate) := Classical.decEq _

/-- One actual input round preserves the full reference invariant, whether
the worker waits, supplies text, starts a scan, resumes it, or finishes it.
This is functional refinement; a separate service bound is still required
to establish that the requested output is ready at its deadline. -/
theorem frame_step {e : Env k} (hc : Function.Injective e.code)
    (hmb : e.mark ≠ e.blank) {v Text : List (Fin k)} {R rate p₁ rem n : ℕ}
    (hk : 0 < rate) (hv : 0 < v.length) (hend : e.endSym ∉ v) (hstart : e.startSym ∉ v)
    (hblank : e.blank ∉ Text) (hmark : e.mark ∉ Text) (hn : n < Text.length)
    (enc : Terminal → Fin k) (a : Terminal) (ha : Text[n]? = some (enc a))
    {M : TextFeed.Machine' k} {ph : Phase}
    (c : CallCtrl (programs e.blank e.mark) (Outer R rate)) (T : Fin 20 → STape (Fin k))
    (old : Fin k) (h : Sim e v Text R rate p₁ rem n M ph (c, T) old)
    (hc0 : c.1.1 = ⟨0, Nat.zero_lt_succ R⟩) :
    let z := (TextFeedSchedule.machine e enc R rate).sRound
      { state := ((c, ⟨0, by omega⟩), ⟨0, by omega⟩), tape := T } a
    let u := modelRun e v Text rate p₁ rem (n + 1) R (TextFeed.arrive' e.blank e.mark (enc a) M) ph
    Sim e v Text R rate p₁ rem (n + 1) u.1 u.2 (z.state.1.1, z.tape) (enc a) ∧
      z.state.1.1.1.1 = ⟨0, Nat.zero_lt_succ R⟩ ∧
      z.state.1.2 = ⟨0, by omega⟩ ∧ z.state.2 = ⟨0, by omega⟩ := by
  classical
  dsimp only
  rw [machine_round]
  let x0 : Phys e R rate := (c, ProgLangPersist2.arriveA e.blank (capture enc) (some a) T)
  let x1 := TextFeedSchedule.run (Terminal := Terminal) e R rate x0
  have hcap := capture_sim h enc a
  have harr := arrival_step (Terminal := Terminal) hc hmb hmark hn ha hcap hc0
  have hcount : x1.1.1.1 = nextPhase ⟨0, Nat.zero_lt_succ R⟩ := by rw [run_counter, hc0]
  have hpos : R ≠ 0 → 0 < x1.1.1.1.val := by
    intro hR
    have hlt : (0 : ℕ) + 1 < R + 1 := by omega
    rw [hcount]
    simp only [nextPhase, dif_pos hlt]
    omega
  have hlen : x1.1.1.1.val + R ≤ R + 1 := by
    by_cases hR : R = 0
    · have hh := x1.1.1.1.isLt; omega
    · have hlt : (0 : ℕ) + 1 < R + 1 := by omega
      rw [hcount]
      simp only [nextPhase, dif_pos hlt]
      omega
  have hwork := worker_steps (Terminal := Terminal) hc hmb hk hv hend hstart hblank hmark
    (by omega : n + 1 ≤ Text.length) R harr hpos hlen
  refine ⟨?_, run_counter_frame (Terminal := Terminal) e R rate x0 hc0, rfl, rfl⟩
  simpa only [Function.iterate_succ_apply, Prod.mk.eta] using hwork

/-- info: 'PalPeg.TextFeedRefine.frame_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms frame_step

end PalPeg.TextFeedRefine
