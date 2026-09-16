import PalPeg.TextFeedPrepFinish

/-! Execute a finite preparation job from initial task control across all
of its real arrivals, including the last partial frame and actual handoff. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPrepEndpoint
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangBank PalPeg.ProgLangPersist2 PalPeg.PrepInstance
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.TextFeedControl PalPeg.TextFeedInput PalPeg.TextFeedPrepare
open PalPeg.TextFeedStartupBank PalPeg.TextFeedStartupSchedule PalPeg.TextFeedStartupSafety
open PalPeg.TextFeedPrepResume PalPeg.TextFeedPrepInterrupt PalPeg.TextFeedPrepFinish

variable {k : ℕ} {Terminal : Type}

noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedStartupBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedStartupBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (Outer e leftSym R rate) := Classical.decEq _

noncomputable def stateBefore (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k) (R rate : ℕ)
    (c : CallCtrl (programs e) (Outer e leftSym R rate)) (T : Fin 27 → STape (Fin k))
    (word : List Terminal) :=
  word.foldl (machine e leftSym enc R rate).sRound
    { state := ((c, ⟨0, by omega⟩), ⟨0, by omega⟩), tape := T }

noncomputable def prefixRun (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k) (R rate : ℕ)
    (c : CallCtrl (programs e) (Outer e leftSym R rate)) (T : Fin 27 → STape (Fin k))
    (word : List Terminal) (a : Terminal) (calls : ℕ) :=
  let z := stateBefore e leftSym enc R rate c T word
  (run (Terminal := Terminal) e leftSym R rate)^[calls]
    (z.state.1.1, arriveA e.blank (TextFeedStartupSchedule.capture enc) (some a) z.tape)

/-- The actual finite machine reaches its prepared tapes and worker
continuation after floor(cost/R) complete frames and J+2 calls of the last
frame. All prior inputs, including the last arrival, remain in the FIFO. -/
theorem end_at_cost {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (enc : Terminal → Fin k) (R rate J : ℕ) (hR : 0 < R) (hJR : J < R)
    (c : CallCtrl (programs e) (Outer e leftSym R rate)) (T : Fin 27 → STape (Fin k))
    (hb : AtBoundary (programs e) c.2.2.1) (hf : c.1.2.1 = true)
    (hc0 : c.1.1 = ⟨0, Nat.zero_lt_succ R⟩) (S : Stage k) (old : Fin k)
    (hx : feedView T = TextFeedInit.unprepared e S old)
    (hs : c.1.2.2.val = [task e leftSym rate]) (word : List Terminal) (a : Terminal)
    (hall : ∀ b ∈ word ++ [a], enc b ≠ e.mark)
    (tr : List (Fin 15 → Fin k × Move))
    (he : Exec (source e) e.blank
      (finitePrepSetup e.blank e.startSym e.endSym leftSym e.mark rate) (prepView T) tr)
    (hsplit : word.length * R + J = tr.length) :
    let z := stateBefore e leftSym enc R rate c T word
    let y := prefixRun e leftSym enc R rate c T word a (J + 2)
    z.state.1.2 = ⟨0, by omega⟩ ∧ z.state.2 = ⟨0, by omega⟩ ∧
      prepView y.2 = applyTrace e.blank (prepView T) tr ∧ AtBoundary (programs e) y.1.2.2.1 ∧
      ReadyAt e y.2 (snoc (word.foldl (fun q b => snoc q (enc b)) empty) (enc a)) (enc a) ∧
      y.1.1.2.2.val = (TextFeedCycle.beforeFill rate).map (Prog.map Sum.inr Sum.inr) ∧
      y.1.1.2.1 = false := by
  let p := finitePrepSetup e.blank e.startSym e.endSym leftSym e.mark rate
  let P := prepView T
  have hend := TextFeedPrepHandoff.exec_endpoint e p P tr he
  have hpos := TextFeedPrepHandoff.prep_cost_pos e leftSym rate P tr he
  have halla : enc a ≠ e.mark := hall a (List.mem_append.mpr (Or.inr (List.mem_singleton_self a)))
  cases word with
  | nil =>
    simp only [List.length_nil, Nat.zero_mul, Nat.zero_add] at hsplit
    have hj : 0 < J := by omega
    have hlive := TextFeedPrepHandoff.exec_live_prefix e p P tr he J (by omega)
    have hret : (stepStack (evalConds (source e) (fun j =>
        ((runInputs (source e) e.blank (List.replicate J none) ([p], P)).2 j).focus))
        (runInputs (source e) e.blank (List.replicate J none) ([p], P)).1).2 = none := by
      simpa only [hsplit] using hend.2
    obtain ⟨hv, hb', hr, hs', hf'⟩ := finish_initial hc hmb leftSym enc R rate J hj hJR
      c T hb hf hc0 S old hx hs a halla hlive hret
    dsimp only [prefixRun, stateBefore, List.foldl_nil]
    exact ⟨rfl, rfl, hv.trans (by simpa only [hsplit] using hend.1), hb', hr, hs', hf'⟩
  | cons b word =>
    have hlive := TextFeedPrepHandoff.exec_live_prefix e p P tr he ((b :: word).length * R) (by omega)
    obtain ⟨c1, T1, hz1, hv1, hb1, hr1, hs1, hc1, hf1⟩ := TextFeedPrepStartupFrames.started_frames
      hc hmb leftSym enc R rate hR c T hb hf hc0 S old hx hs b word
      (fun d hd => hall d (List.mem_append.mpr (Or.inl hd))) hlive
    let u1 := runInputs (source e) e.blank (List.replicate ((b :: word).length * R) none) ([p], P)
    have hliveAll := TextFeedPrepHandoff.exec_live_prefix e p P tr he tr.length (Nat.le_refl _)
    have hliveSum : (trace (source e) e.blank
        (List.replicate ((b :: word).length * R + J) none) ([p], P)).length =
          (b :: word).length * R + J := by simpa only [hsplit] using hliveAll
    have hliveTail := (TextFeedPrepFrames.live_split e [p] P ((b :: word).length * R) J hliveSum).2
    have hsum : runInputs (source e) e.blank (List.replicate J none) u1 =
        runInputs (source e) e.blank (List.replicate tr.length none) ([p], P) := by
      dsimp only [u1]
      rw [← runInputs_append, ← List.replicate_add, hsplit]
    have hret : (stepStack (evalConds (source e) (fun j =>
        ((runInputs (source e) e.blank (List.replicate J none) u1).2 j).focus))
        (runInputs (source e) e.blank (List.replicate J none) u1).1).2 = none := by
      rw [hsum]
      exact hend.2
    obtain ⟨hv, hb', hr, hs', hf'⟩ := finish_calls hc hmb leftSym enc R rate J hJR
      c1 T1 hb1 hf1 hc1 hr1 a halla u1.1 u1.2 hv1 hs1 hliveTail hret
    have hout : (runInputs (source e) e.blank (List.replicate J none) (u1.1, u1.2)).2 =
        applyTrace e.blank P tr := by
      rw [Prod.mk.eta, hsum]
      exact hend.1
    have hz : stateBefore e leftSym enc R rate c T (b :: word) =
        { state := ((c1, ⟨0, by omega⟩), ⟨0, by omega⟩), tape := T1 } := hz1
    dsimp only [prefixRun]
    rw [hz]
    exact ⟨rfl, rfl, hv.trans hout, hb', hr, hs', hf'⟩

/-- info: 'PalPeg.TextFeedPrepEndpoint.end_at_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms end_at_cost

end PalPeg.TextFeedPrepEndpoint
