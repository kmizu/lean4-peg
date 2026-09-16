import PalPeg.TextFeedPrepStartupFrames

/-! The last preparation window may be shorter than a full real-input
frame. Its final source instruction and the worker handoff both fit before
the next arrival; no full-frame padding of the source program is assumed. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPrepFinish
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangBank PalPeg.ProgLangPersist2 PalPeg.PrepInstance
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.TextFeedControl PalPeg.TextFeedInput PalPeg.TextFeedPrepare
open PalPeg.TextFeedStartupBank PalPeg.TextFeedStartupSchedule PalPeg.TextFeedStartupSafety
open PalPeg.TextFeedPrepResume PalPeg.TextFeedPrepInterrupt PalPeg.TextFeedPrepBootstrap

variable {k : ℕ} {Terminal : Type}

noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedStartupBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedStartupBank.Cond k) := Classical.decEq _

theorem worker_first (e : Env k) (rate : ℕ) (σ : Fin 20 → Fin k) :
    (stepStack (fun c => TextFeedSchedule.workerCond e c σ) [TextFeedSchedule.worker rate]).1 =
      TextFeedCycle.beforeFill rate := by
  rw [TextFeedSchedule.worker, stepStack_loop]
  rfl

theorem counter_after_prefix {R J : ℕ} (hJ : J < R) :
    nextPhase^[J + 1] (⟨0, Nat.zero_lt_succ R⟩ : Fin (R + 1)) ≠ ⟨0, Nat.zero_lt_succ R⟩ := by
  rw [nextPhase_iterate (Nat.zero_lt_succ R) (J + 1) (by omega)]
  intro h
  have hh := congrArg Fin.val h
  change J + 1 = 0 at hh
  omega

attribute [local irreducible] ProgLangBank.runChunk

theorem handoff_ready (e : Env k) (leftSym : Fin k) (R rate : ℕ)
    (x : CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 27 → STape (Fin k)))
    (hb : AtBoundary (programs e) x.1.2.2.1) (hf : x.1.1.2.1 = false)
    (hc0 : x.1.1.1 ≠ ⟨0, Nat.zero_lt_succ R⟩)
    {q : Queue (Fin k)} {old : Fin k} (hq : ReadyAt e x.2 q old)
    (s : Stack (PrepAct k) (PrepCond k))
    (hs : x.1.1.2.2.val = s.map TextFeedPrepResume.lift ++
      [(TextFeedSchedule.worker rate).map Sum.inr Sum.inr])
    (hreturn : (stepStack (evalConds (source e) (fun j => (prepView x.2 j).focus)) s).2 = none) :
    let y := run (Terminal := Terminal) e leftSym R rate x
    y.2 = x.2 ∧ AtBoundary (programs e) y.1.2.2.1 ∧ ReadyAt e y.2 q old ∧
      y.1.1.2.1 = false ∧
      y.1.1.2.2.val = (TextFeedCycle.beforeFill rate).map (Prog.map Sum.inr Sum.inr) := by
  obtain ⟨ht, hb', hs'⟩ := TextFeedPrepHandoff.run_handoff (Terminal := Terminal)
    e leftSym R rate x hb hc0 s hs hreturn
  rw [worker_first] at hs'
  exact ⟨ht, hb', ht ▸ hq, TextFeedStartupRun.choose_false e leftSym R rate _ _ hf, hs'⟩

/-- Complete a final J-step preparation suffix and hand off inside the
same real-input frame. The queued arrival count includes this last input. -/
theorem finish_calls {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (enc : Terminal → Fin k) (R rate J : ℕ) (hJR : J < R)
    (c : CallCtrl (programs e) (Outer e leftSym R rate)) (T : Fin 27 → STape (Fin k))
    (hb : AtBoundary (programs e) c.2.2.1) (hf : c.1.2.1 = false)
    (hc0 : c.1.1 = ⟨0, Nat.zero_lt_succ R⟩)
    {q : Queue (Fin k)} {old : Fin k} (h : ReadyAt e T q old) (a : Terminal) (ha : enc a ≠ e.mark)
    (s : Stack (PrepAct k) (PrepCond k)) (P : Fin 15 → STape (Fin k)) (hv : prepView T = P)
    (hs : c.1.2.2.val = s.map TextFeedPrepResume.lift ++
      [(TextFeedSchedule.worker rate).map Sum.inr Sum.inr])
    (htrace : (trace (source e) e.blank (List.replicate J none) (s, P)).length = J)
    (hreturn : let u := runInputs (source e) e.blank (List.replicate J none) (s, P)
      (stepStack (evalConds (source e) (fun j => (u.2 j).focus)) u.1).2 = none) :
    let y := (run (Terminal := Terminal) e leftSym R rate)^[J + 2]
      (c, arriveA e.blank (TextFeedStartupSchedule.capture enc) (some a) T)
    let u := runInputs (source e) e.blank (List.replicate J none) (s, P)
    prepView y.2 = u.2 ∧ AtBoundary (programs e) y.1.2.2.1 ∧
      ReadyAt e y.2 (snoc q (enc a)) (enc a) ∧
      y.1.1.2.2.val = (TextFeedCycle.beforeFill rate).map (Prog.map Sum.inr Sum.inr) ∧
      y.1.1.2.1 = false := by
  obtain ⟨c1, T1, he, hv1, hb1, hr1, hs1, hc1, hf1⟩ := TextFeedPrepFrames.busy_calls
    hc hmb leftSym enc R rate J (Nat.le_of_lt hJR) c T hb hf hc0 h a ha s
    [(TextFeedSchedule.worker rate).map Sum.inr Sum.inr] P hv hs htrace
  have hne : c1.1.1 ≠ ⟨0, Nat.zero_lt_succ R⟩ := by
    rw [hc1, hc0]
    exact counter_after_prefix hJR
  have hret : (stepStack (evalConds (source e) (fun j => (prepView T1 j).focus))
      (runInputs (source e) e.blank (List.replicate J none) (s, P)).1).2 = none := by
    rw [hv1]
    exact hreturn
  obtain ⟨ht, hb', hr', hf', hs'⟩ := handoff_ready (Terminal := Terminal) e leftSym R rate
    (c1, T1) hb1 hf1 hne hr1 _ hs1 hret
  dsimp only
  rw [Function.iterate_succ_apply', he]
  exact ⟨(congrArg prepView ht).trans hv1, hb', hr', hs', hf'⟩

/-- The same partial-window finish works when all preprocessing fits in
the very first frame, whose FIFO starts blank rather than Ready. -/
theorem finish_initial {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (enc : Terminal → Fin k) (R rate J : ℕ) (hJ : 0 < J) (hJR : J < R)
    (c : CallCtrl (programs e) (Outer e leftSym R rate)) (T : Fin 27 → STape (Fin k))
    (hb : AtBoundary (programs e) c.2.2.1) (hf : c.1.2.1 = true)
    (hc0 : c.1.1 = ⟨0, Nat.zero_lt_succ R⟩) (S : Stage k) (old : Fin k)
    (hx : feedView T = TextFeedInit.unprepared e S old)
    (hs : c.1.2.2.val = [task e leftSym rate]) (a : Terminal) (ha : enc a ≠ e.mark)
    (htrace : (trace (source e) e.blank (List.replicate J none)
      ([finitePrepSetup e.blank e.startSym e.endSym leftSym e.mark rate], prepView T)).length = J)
    (hreturn :
      let u := runInputs (source e) e.blank (List.replicate J none)
        ([finitePrepSetup e.blank e.startSym e.endSym leftSym e.mark rate], prepView T)
      (stepStack (evalConds (source e) (fun j => (u.2 j).focus)) u.1).2 = none) :
    let y := (run (Terminal := Terminal) e leftSym R rate)^[J + 2]
      (c, arriveA e.blank (TextFeedStartupSchedule.capture enc) (some a) T)
    let u := runInputs (source e) e.blank (List.replicate J none)
      ([finitePrepSetup e.blank e.startSym e.endSym leftSym e.mark rate], prepView T)
    prepView y.2 = u.2 ∧ AtBoundary (programs e) y.1.2.2.1 ∧
      ReadyAt e y.2 (snoc empty (enc a)) (enc a) ∧
      y.1.1.2.2.val = (TextFeedCycle.beforeFill rate).map (Prog.map Sum.inr Sum.inr) ∧
      y.1.1.2.1 = false := by
  obtain ⟨c1, T1, he, hv1, hb1, hr1, hs1, hc1, hf1⟩ := initial_calls hc hmb leftSym enc R rate
    J hJ (Nat.le_of_lt hJR) c T hb hf hc0 S old hx hs a ha htrace
  have hne : c1.1.1 ≠ ⟨0, Nat.zero_lt_succ R⟩ := by
    rw [hc1, hc0]
    exact counter_after_prefix hJR
  have hret : (stepStack (evalConds (source e) (fun j => (prepView T1 j).focus))
      (runInputs (source e) e.blank (List.replicate J none)
        ([finitePrepSetup e.blank e.startSym e.endSym leftSym e.mark rate], prepView T)).1).2 = none := by
    rw [hv1]
    exact hreturn
  obtain ⟨ht, hb', hr', hf', hs'⟩ := handoff_ready (Terminal := Terminal) e leftSym R rate
    (c1, T1) hb1 hf1 hne hr1 _ hs1 hret
  dsimp only
  rw [Function.iterate_succ_apply', he]
  exact ⟨(congrArg prepView ht).trans hv1, hb', hr', hs', hf'⟩

/-- info: 'PalPeg.TextFeedPrepFinish.finish_initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms finish_initial

/-- info: 'PalPeg.TextFeedPrepFinish.finish_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms finish_calls

end PalPeg.TextFeedPrepFinish
