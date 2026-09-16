import PalPeg.TextFeedStartupBudget

/-! Entry into the interrupted preparation run from the actual finite
task's initial control and blank private FIFO, on the first real arrival. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPrepBootstrap
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangBank PalPeg.ProgLangPersist2 PalPeg.PrepInstance
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.TextFeedControl PalPeg.TextFeedInput PalPeg.TextFeedPrepare
open PalPeg.TextFeedStartupBank PalPeg.TextFeedStartupSchedule PalPeg.TextFeedStartupSafety
open PalPeg.TextFeedPrepResume PalPeg.TextFeedPrepInterrupt

variable {k : ℕ} {Terminal : Type}

noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedStartupBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedStartupBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (Outer e leftSym R rate) := Classical.decEq _

attribute [local irreducible] ProgLangBank.runChunk

theorem bootstrap_view {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate : ℕ)
    (x : CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 27 → STape (Fin k)))
    (hb : AtBoundary (programs e) x.1.2.2.1) (hf : x.1.1.2.1 = true)
    (hc0 : x.1.1.1 = ⟨0, Nat.zero_lt_succ R⟩) (S : Stage k) (old : Fin k)
    (hx : feedView x.2 = TextFeedInit.unprepared e S old) (ha : old ≠ e.mark) :
    prepView (run (Terminal := Terminal) e leftSym R rate x).2 = prepView x.2 := by
  have hi : (x.2 inputSlot).focus = old := congrArg STape.focus (congrFun hx inputIdx)
  have hsel : decode (choose e leftSym R rate x.1.1 (fun j => (x.2 j).focus)).2 = .first old := by
    rw [TextFeedStartupSchedule.choose, if_pos hc0]
    simp only [hf, ↓reduceIte, decode_encode, hi]
  obtain ⟨tr, qt', m', he, hn, ht, _⟩ := first_exec (Terminal := Terminal) hc hmb S old old ha x.2
  have hs : extend feedSlot (TextFeedInit.unprepared e S old) x.2 = x.2 := by
    rw [← hx]
    exact extend_restrict feedSlot x.2
  rw [hs] at he ht
  have hex : Exec (TextFeedStartupSchedule.interp (Terminal := Terminal) e).toInterp e.blank
      (programs e (choose e leftSym R rate x.1.1 (fun j => (x.2 j).focus)).2) x.2 tr := by
    change Exec (shared e) e.blank (low e (decode _)) x.2 tr
    rw [hsel]
    exact he
  obtain ⟨hyt, _, _, _⟩ := callRun_exec (programs e)
    (fun _ => TextFeedStartupSchedule.interp (Terminal := Terminal) e)
    (choose e leftSym R rate) 48 e.blank x hb tr hex (by omega)
  change prepView (callRun _ _ _ _ _ x).2 = _
  rw [hyt, ht]
  apply prepView_feed
  intro i
  simpa only [scanSlot, feedView, TextFeedInit.unprepared, rtapes, TextFeedControl.tapes,
    Fin.castAddEmb_apply, Fin.natAddEmb_apply, Fin.append_left, Fin.append_right] using
    (congrFun hx (scanSlot i)).symm

theorem capture_unprepared (e : Env k) (enc : Terminal → Fin k) (a : Terminal)
    (S : Stage k) (old : Fin k) :
    arriveA e.blank (TextFeedInput.capture enc) (some a) (TextFeedInit.unprepared e S old) =
      TextFeedInit.unprepared e S (enc a) := by
  funext j
  fin_cases j <;> rfl

/-- Even the first productive window starts from the real `seq prep worker`
control. Bootstrap preserves the prep snapshot before its first instruction. -/
theorem initial_calls {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (enc : Terminal → Fin k) (R rate J : ℕ) (hJ : 0 < J) (hJR : J ≤ R)
    (c : CallCtrl (programs e) (Outer e leftSym R rate)) (T : Fin 27 → STape (Fin k))
    (hb : AtBoundary (programs e) c.2.2.1) (hf : c.1.2.1 = true)
    (hc0 : c.1.1 = ⟨0, Nat.zero_lt_succ R⟩) (S : Stage k) (old : Fin k)
    (hx : feedView T = TextFeedInit.unprepared e S old)
    (hs : c.1.2.2.val = [task e leftSym rate]) (a : Terminal) (ha : enc a ≠ e.mark)
    (htrace : (trace (TextFeedPrepResume.source e) e.blank (List.replicate J none)
      ([finitePrepSetup e.blank e.startSym e.endSym leftSym e.mark rate], prepView T)).length = J) :
    let z := (run (Terminal := Terminal) e leftSym R rate)^[J + 1]
      (c, arriveA e.blank (TextFeedStartupSchedule.capture enc) (some a) T)
    let u := runInputs (TextFeedPrepResume.source e) e.blank (List.replicate J none)
      ([finitePrepSetup e.blank e.startSym e.endSym leftSym e.mark rate], prepView T)
    ∃ c' T', z = (c', T') ∧
      prepView T' = u.2 ∧ AtBoundary (programs e) c'.2.2.1 ∧
      ReadyAt e T' (snoc empty (enc a)) (enc a) ∧
      c'.1.2.2.val = u.1.map TextFeedPrepResume.lift ++
        [(TextFeedSchedule.worker rate).map Sum.inr Sum.inr] ∧
      c'.1.1 = nextPhase^[J + 1] c.1.1 ∧ c'.1.2.1 = false := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hJ)
  let p := finitePrepSetup e.blank e.startSym e.endSym leftSym e.mark rate
  let P := prepView T
  let x := (c, arriveA e.blank (TextFeedStartupSchedule.capture enc) (some a) T)
  let x1 := run (Terminal := Terminal) e leftSym R rate x
  let x2 := run (Terminal := Terminal) e leftSym R rate x1
  have hcap : feedView x.2 = TextFeedInit.unprepared e S (enc a) := by
    rw [TextFeedStartupRun.capture_view, hx, capture_unprepared]
  have hv0 : prepView x.2 = P := capture_prepView e.blank enc (some a) T
  obtain ⟨hr1, hb1, hf1, hw1⟩ := TextFeedStartupRun.run_first (Terminal := Terminal)
    hc hmb leftSym R rate x hb hf hc0 S (enc a) hcap ha
  have hv1 : prepView x1.2 = P := (bootstrap_view (Terminal := Terminal)
    hc hmb leftSym R rate x hb hf hc0 S (enc a) hcap ha).trans hv0
  have hs1 : x1.1.1.2.2.val = [task e leftSym rate] := by rw [hw1]; exact hs
  have hcount1 : x1.1.1.1 = ⟨1, by omega⟩ := by
    rw [run_counter, hc0]
    simp only [nextPhase, dif_pos (show (0 : ℕ) + 1 < R + 1 by omega)]
  have hsome : ∃ b, (stepStack (evalConds (TextFeedPrepResume.source e) (fun j => (P j).focus)) [p]).2 = some b := by
    cases hh : (stepStack (evalConds (TextFeedPrepResume.source e) (fun j => (P j).focus)) [p]).2 with
    | some b => exact ⟨b, rfl⟩
    | none =>
      have hl := trace_length_le (TextFeedPrepResume.source e) e.blank (List.replicate N none) (sourceStep e [p] P)
      change (trace (TextFeedPrepResume.source e) e.blank (List.replicate (N + 1) none) ([p], P)).length = N + 1 at htrace
      rw [List.replicate_succ, trace_cons, hh] at htrace
      simp only [List.nil_append, List.length_replicate] at hl htrace
      change (trace (TextFeedPrepResume.source e) e.blank (List.replicate N none) (sourceStep e [p] P)).length = N + 1 at htrace
      omega
  obtain ⟨b, hbact⟩ := hsome
  have hbact' : (stepStack (evalConds (TextFeedPrepResume.source e) (fun j => (prepView x1.2 j).focus)) [p]).2 = some b := by
    rw [hv1]; exact hbact
  obtain ⟨ht2, hb2, hs2⟩ := run_start (Terminal := Terminal) e leftSym R rate x1 hb1
    (by rw [hcount1]; intro hh; have hv : (1 : ℕ) = 0 := congrArg Fin.val hh; omega) hs1 b hbact'
  rw [hv1] at ht2 hs2
  have hv2 : prepView x2.2 = (sourceStep e [p] P).2 := by rw [ht2, prepView_extend]
  have hr2 : ReadyAt e x2.2 (snoc empty (enc a)) (enc a) := by rw [ht2]; exact ready_prep hr1 _
  have htail : (trace (TextFeedPrepResume.source e) e.blank (List.replicate N none) (sourceStep e [p] P)).length = N := by
    change (trace (TextFeedPrepResume.source e) e.blank (List.replicate (N + 1) none) ([p], P)).length = N + 1 at htrace
    rw [List.replicate_succ, trace_cons, hbact] at htrace
    simpa only [List.singleton_append, List.length_cons, Nat.succ.injEq, sourceStep] using htrace
  have hcount2 : x2.1.1.1 = nextPhase ⟨1, by omega⟩ := by rw [run_counter, hcount1]
  have hpos : N ≠ 0 → 0 < x2.1.1.1.val := by
    intro hn
    rw [hcount2]
    simp only [nextPhase, dif_pos (show (1 : ℕ) + 1 < R + 1 by omega)]
    omega
  have hlen : x2.1.1.1.val + N ≤ R + 1 := by
    by_cases hn : N = 0
    · have hh := x2.1.1.1.isLt; omega
    · rw [hcount2]
      simp only [nextPhase, dif_pos (show (1 : ℕ) + 1 < R + 1 by omega)]
      omega
  obtain ⟨ht, hb', hs'⟩ := run_prefix (Terminal := Terminal) e leftSym R rate N x2 hb2
    (sourceStep e [p] P).1 [(TextFeedSchedule.worker rate).map Sum.inr Sum.inr]
    (sourceStep e [p] P).2 hv2 hs2 htail hpos hlen
  have hcnt := run_counter_iterate (Terminal := Terminal) e leftSym R rate ((N + 1) + 1) x
  dsimp only
  rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
  rw [Function.iterate_succ_apply, Function.iterate_succ_apply] at hcnt
  refine ⟨((run (Terminal := Terminal) e leftSym R rate)^[N] x2).1,
    ((run (Terminal := Terminal) e leftSym R rate)^[N] x2).2, rfl, ?_, hb', ?_, ?_, hcnt, ?_⟩
  · rw [ht, prepView_extend]
    rfl
  · rw [ht]; exact ready_prep hr2 _
  · exact hs'
  · exact TextFeedPrepFrames.run_false_iterate e leftSym R rate (N + 1) x1 hf1

theorem initial_frame {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (enc : Terminal → Fin k) (R rate : ℕ) (hR : 0 < R)
    (c : CallCtrl (programs e) (Outer e leftSym R rate)) (T : Fin 27 → STape (Fin k))
    (hb : AtBoundary (programs e) c.2.2.1) (hf : c.1.2.1 = true)
    (hc0 : c.1.1 = ⟨0, Nat.zero_lt_succ R⟩) (S : Stage k) (old : Fin k)
    (hx : feedView T = TextFeedInit.unprepared e S old)
    (hs : c.1.2.2.val = [task e leftSym rate]) (a : Terminal) (ha : enc a ≠ e.mark)
    (htrace : (trace (TextFeedPrepResume.source e) e.blank (List.replicate R none)
      ([finitePrepSetup e.blank e.startSym e.endSym leftSym e.mark rate], prepView T)).length = R) :
    let z := (machine e leftSym enc R rate).sRound
      { state := ((c, ⟨0, by omega⟩), ⟨0, by omega⟩), tape := T } a
    let u := runInputs (TextFeedPrepResume.source e) e.blank (List.replicate R none)
      ([finitePrepSetup e.blank e.startSym e.endSym leftSym e.mark rate], prepView T)
    ∃ c' T', z = { state := ((c', ⟨0, by omega⟩), ⟨0, by omega⟩), tape := T' } ∧
      prepView T' = u.2 ∧ AtBoundary (programs e) c'.2.2.1 ∧
      ReadyAt e T' (snoc empty (enc a)) (enc a) ∧
      c'.1.2.2.val = u.1.map TextFeedPrepResume.lift ++
        [(TextFeedSchedule.worker rate).map Sum.inr Sum.inr] ∧
      c'.1.1 = ⟨0, Nat.zero_lt_succ R⟩ ∧ c'.1.2.1 = false := by
  dsimp only
  rw [machine_round]
  obtain ⟨c', T', he, hv, hb', hr, hs', hcnt, hf'⟩ := initial_calls (Terminal := Terminal)
    hc hmb leftSym enc R rate R hR (Nat.le_refl R) c T hb hf hc0 S old hx hs a ha htrace
  refine ⟨c', T', ?_, hv, hb', hr, hs', ?_, hf'⟩
  · rw [he]
  · rw [hc0, nextPhase_iterate_round] at hcnt
    exact hcnt

/-- info: 'PalPeg.TextFeedPrepBootstrap.initial_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms initial_frame

end PalPeg.TextFeedPrepBootstrap
