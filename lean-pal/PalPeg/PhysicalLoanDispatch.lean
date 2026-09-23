import PalPeg.PhysicalGrowMatchCase

/-! # Common physical dispatcher with the borrowed radius mirror

Arrival and starvation use the same head executor for both representations.
Positive-work grow count and matched comparison execute span/work, debt credit
and partial-mirror rebuilding in one sweep. The comparison includes its output
control and both cursor moves. Other active rows retain their previous selection.
-/
set_option autoImplicit false
namespace PalPeg.PhysicalLoanDispatch
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract
open PalPeg.PhysicalLoanInvariant (Enc NeedsLoan enc_full enc_partial)
open PalPeg.PhysicalScanCount (RestCommands)
open PalPeg.PhysicalShiftDispatch (RoutedState RoutedStep RoutedControl RoutedCore liftConfig liftStep select select_apply Entry)
open PalPeg.PhysicalCacheMachine (successor)
open PalPeg.PhysicalBootFeed (feedStep)
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.Local (readWin)
open PalPeg.LocalRoleRouting (hold decode)

noncomputable def transportTest (q : RoutedControl) (input : Option (Fin 2))
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm macroRadius) : Bool :=
  match q.2, input with
  | .inr _, some _ => true
  | .inr c, none => PalPeg.PhysicalTickDispatch.starvedRead c (fun j => ws (q.1 j))
  | .inl _, _ => false

noncomputable def growTest (q : RoutedControl) (input : Option (Fin 2))
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm macroRadius) : Bool :=
  match q.2, input with
  | .inr c, none => PalPeg.PhysicalGrowCount.guard c (fun j => ws (q.1 j))
  | _, _ => false

noncomputable def matchTest (q : RoutedControl) (input : Option (Fin 2))
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm macroRadius) : Bool :=
  match q.2, input with
  | .inr c, none => PalPeg.PhysicalGrowMatchCase.guard c (fun j => ws (q.1 j))
  | _, _ => false

noncomputable def machine (rest : RestCommands) : RoutedStep :=
  let old := PalPeg.PhysicalSnapshotEntryDispatch.machine rest
  select transportTest (liftStep (hold feedStep) old)
    (select growTest (liftStep (hold PalPeg.PhysicalGrowCount.step) old)
      (select matchTest (liftStep PalPeg.PhysicalGrowMatchTick.step old) old))

theorem apply_previous (rest : RestCommands) (p : RoutedState) (input : Option (Fin 2))
    (h : transportTest p.1 input (fun j => readWin blankM macroRadius (p.2 j)) = false)
    (hg : growTest p.1 input (fun j => readWin blankM macroRadius (p.2 j)) = false)
    (hm : matchTest p.1 input (fun j => readWin blankM macroRadius (p.2 j)) = false) :
    (machine rest).apply blankM p input = (PalPeg.PhysicalSnapshotEntryDispatch.machine rest).apply blankM p input := by
  rw [machine, select_apply, h, if_neg Bool.false_ne_true, select_apply, hg, if_neg Bool.false_ne_true, select_apply, hm, if_neg Bool.false_ne_true]

theorem forward_feed (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : RoutedState) (a : Fin 2) (he : Enc w x p) :
    Enc w (PalPeg.GalilArriveChain.arriveState' a x) ((machine rest).apply blankM p (some a)) := by
  rcases p with ⟨⟨roles, q⟩, T⟩
  cases q with
  | inl tag =>
    have hn : ¬ NeedsLoan x := by
      intro hn
      exact ((enc_partial w x _ hn).mp he).2
    rw [apply_previous rest _ (some a) rfl rfl rfl]
    apply (enc_full w _ _ (fun h => hn ((PalPeg.PhysicalLoanInvariant.needs_feed (some a) x).mp h))).mpr
    exact PalPeg.PhysicalSnapshotEntryDispatch.forward_feed rest w x _ a ((enc_full w x _ hn).mp he)
  | inr q =>
    change Enc w _ ((machine rest).apply blankM (liftConfig ((roles, q), T)) (some a))
    rw [machine, select_apply, show transportTest _ (some a) _ = true from rfl, if_pos rfl,
      PalPeg.PhysicalShiftDispatch.lift_apply]
    exact PalPeg.PhysicalLoanInvariant.running_feed w x ((roles, q), T) (some a) he

theorem forward_starved (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : RoutedState) (he : Enc w x p) (hs : PalPeg.FrameFunction.starvedTest x = true) :
    Enc w x ((machine rest).apply blankM p none) := by
  rcases p with ⟨⟨roles, q⟩, T⟩
  cases q with
  | inl tag =>
    have hn : ¬ NeedsLoan x := by
      intro hn
      exact ((enc_partial w x _ hn).mp he).2
    rw [apply_previous rest _ none rfl rfl rfl]
    apply (enc_full w x _ hn).mpr
    exact PalPeg.PhysicalSnapshotEntryDispatch.forward_starved rest w x _ ((enc_full w x _ hn).mp he) hs
  | inr q =>
    have htest : transportTest (liftConfig ((roles, q), T)).1 none
        (fun j => readWin blankM macroRadius ((liftConfig ((roles, q), T)).2 j)) = true :=
      (PalPeg.PhysicalLoanInvariant.starved_running w x ((roles, q), T) he).trans hs
    change Enc w x ((machine rest).apply blankM (liftConfig ((roles, q), T)) none)
    rw [machine, select_apply, htest, if_pos rfl, PalPeg.PhysicalShiftDispatch.lift_apply]
    exact PalPeg.PhysicalLoanInvariant.running_feed w x ((roles, q), T) none he

theorem previous_active (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : RoutedState) (he : Enc w x p) (hs : PalPeg.FrameFunction.starvedTest x = false)
    (hg : ¬ PalPeg.PhysicalGrowCount.CountGrow x) (hm : ¬ PalPeg.PhysicalGrowMatchCase.MatchGrow x) :
    (machine rest).apply blankM p none = (PalPeg.PhysicalSnapshotEntryDispatch.machine rest).apply blankM p none := by
  apply apply_previous
  · rcases p with ⟨⟨roles, q⟩, T⟩
    cases q with
    | inl tag => rfl
    | inr q => exact (PalPeg.PhysicalLoanInvariant.starved_running w x ((roles, q), T) he).trans hs
  · rcases p with ⟨⟨roles, q⟩, T⟩
    cases q with
    | inl tag => rfl
    | inr q =>
      have hr := PalPeg.PhysicalGrowCount.guard_running w x ((roles, q), T) he
      simpa only [growTest, liftConfig, decode, hg, decide_false] using hr
  · rcases p with ⟨⟨roles, q⟩, T⟩
    cases q with
    | inl tag => rfl
    | inr q =>
      have hr := PalPeg.PhysicalGrowMatchCase.guard_running w x ((roles, q), T) he hs
      simpa only [matchTest, liftConfig, decode, hm, decide_false] using hr

theorem forward_grow (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : RoutedState) (he : Enc w x p) (hs : PalPeg.FrameFunction.starvedTest x = false)
    (hg : PalPeg.PhysicalGrowCount.CountGrow x) :
    Enc w (successor w x) ((machine rest).apply blankM p none) := by
  rcases p with ⟨⟨roles, q⟩, T⟩
  cases q with
  | inl tag => exact ((enc_partial w x _ (PalPeg.PhysicalGrowCount.needs_source x hg)).mp he).2.elim
  | inr q =>
    have htrans : transportTest (liftConfig ((roles, q), T)).1 none
        (fun j => readWin blankM macroRadius ((liftConfig ((roles, q), T)).2 j)) = false :=
      (PalPeg.PhysicalLoanInvariant.starved_running w x ((roles, q), T) he).trans hs
    have htest : growTest (liftConfig ((roles, q), T)).1 none
        (fun j => readWin blankM macroRadius ((liftConfig ((roles, q), T)).2 j)) = true := by
      have hr := PalPeg.PhysicalGrowCount.guard_running w x ((roles, q), T) he
      simpa only [growTest, liftConfig, decode, hg, decide_true] using hr
    change Enc w _ ((machine rest).apply blankM (liftConfig ((roles, q), T)) none)
    rw [machine, select_apply, htrans, if_neg Bool.false_ne_true, select_apply, htest, if_pos rfl,
      PalPeg.PhysicalShiftDispatch.lift_apply]
    exact PalPeg.PhysicalGrowCount.forward w x ((roles, q), T) he hg hs


/-- The arrived prefix comes from the same execution ledger as the other
comparison rows; every tape and readiness fact is supplied at the call site. -/
theorem forward_match (rest : RestCommands) (w arrived : List (Fin 2)) (x : State GalilVM)
    (p : RoutedState) (he : Enc w x p) (hs : PalPeg.FrameFunction.starvedTest x = false)
    (hg : PalPeg.PhysicalGrowMatchCase.MatchGrow x)
    (hrep : PalPeg.GalilScaffoldInputTrace.Represents x.vm.right.head arrived)
    (hlen : arrived.length ≤ w.length) :
    Enc w (successor w x) ((machine rest).apply blankM p none) := by
  rcases p with ⟨⟨roles, q⟩, T⟩
  cases q with
  | inl tag => exact ((enc_partial w x _ (PalPeg.PhysicalGrowMatchCase.needs_source x hg)).mp he).2.elim
  | inr q =>
    have htrans : transportTest (liftConfig ((roles, q), T)).1 none
        (fun j => readWin blankM macroRadius ((liftConfig ((roles, q), T)).2 j)) = false :=
      (PalPeg.PhysicalLoanInvariant.starved_running w x ((roles, q), T) he).trans hs
    have hn : ¬ PalPeg.PhysicalGrowCount.CountGrow x := by
      intro hn
      have hc := hg.1.2.1
      have hnclock := hn.2.1
      omega
    have hcount : growTest (liftConfig ((roles, q), T)).1 none
        (fun j => readWin blankM macroRadius ((liftConfig ((roles, q), T)).2 j)) = false := by
      have hr := PalPeg.PhysicalGrowCount.guard_running w x ((roles, q), T) he
      simpa only [growTest, liftConfig, decode, hn, decide_false] using hr
    have htest : matchTest (liftConfig ((roles, q), T)).1 none
        (fun j => readWin blankM macroRadius ((liftConfig ((roles, q), T)).2 j)) = true := by
      have hr := PalPeg.PhysicalGrowMatchCase.guard_running w x ((roles, q), T) he hs
      simpa only [matchTest, liftConfig, decode, hg, decide_true] using hr
    change Enc w _ ((machine rest).apply blankM (liftConfig ((roles, q), T)) none)
    rw [machine, select_apply, htrans, if_neg Bool.false_ne_true,
      select_apply, hcount, if_neg Bool.false_ne_true, select_apply, htest, if_pos rfl,
      PalPeg.PhysicalShiftDispatch.lift_apply]
    exact PalPeg.PhysicalGrowMatchCase.forward w arrived x ((roles, q), T) he hg hs hrep hlen


open PalPeg.GalilFinalAssembly2 (centreC placeC)
open PalPeg.CloseoutCheckW (PreTraceIMW CanonTrace)
open PalPeg.LocalSysConcrete (absSC)
open PalPeg.LocalReplayParked (Mirrored1)
open PalPeg.LocalBlankState (tapeCount)
open PalPeg.ShadowedLocalFinal (localGood postPhase frozenAt heldAfter)

/-- Shift cannot produce an active idle-chain search: its chain stays live. -/
theorem shift_nonidle_tick {w : List (Fin 2)} {x y : State GalilVM}
    (ht : Tick (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x y) :
    y.ctl.mode = .shift → y.vm.chain ≠ .idle := by
  cases ht with
  | scan_shift c s t u hm ha hc hcmp hmis hr hg hb =>
    obtain ⟨v, _, rfl⟩ := hb
    exact fun _ h => by cases h
  | shift_one c s t hm hp ho =>
    obtain ⟨_, _, _, wv, hw, hget⟩ := ho.1
    have hset := ho.2
    rw [hget] at hset
    rw [hset]
    exact fun _ h => by cases h
  | init | scan_wait | scan_count | scan_match | scan_fallback | shift_done
  | copy_one | copy_done | home_start | home_step | fpp_slice | fpp_done
  | markEnd_found | markEnd_step | choose_select | choose_step
  | rewind_done | rewind_one | rewind_pair | replayStart | restart =>
    intro hm
    simp_all

theorem shift_nonidle_onRun (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ)
    (hpre : PreTraceIMW centreC placeC 0 1 0 w st Tc)
    (m : Mirrored1 (tapeCount 0))
    (hon : PalPeg.LocalShadowConcrete.OnRun (localGood (spare := 0)) (postPhase 0 1 0) w
      (heldAfter (Tc w.length) st) m) (hnf : ¬ frozenAt w m)
    (hm : (absSC m).ctl.mode = .shift) : (absSC m).vm.chain ≠ .idle := by
  rcases hon with htracked | ⟨hpost, _, _, _⟩
  · obtain ⟨k, j, _, hsource⟩ := htracked.track
    have hstart : (st 0).ctl.mode = .shift → (st 0).vm.chain ≠ .idle := by
      rw [hpre.base.pre.start]
      intro h
      cases h
    have hi := hpre.base.pre.trace.carried
      (Pk := fun x => x.ctl.mode = .shift → x.vm.chain ≠ .idle)
      hstart (fun _ _ ht _ => shift_nonidle_tick ht)
      (min k (Tc w.length)) (Nat.min_le_right _ _)
    have hmode : (st (min k (Tc w.length))).ctl.mode = .shift :=
      (congrArg (fun z : State GalilVM => z.ctl.mode) hsource).symm.trans hm
    change (PalPeg.LocalReplayParked.absState'' m.vm).vm.chain ≠ .idle
    rw [hsource]
    intro h
    exact hi hmode ((PalPeg.GalilTruncTick.truncChain_idle_iff _ _).mp h)
  · rcases hpost with hplateau | hfrozen
    · have hbad := hplateau.scan.symm.trans hm
      cases hbad
    · exact (hnf hfrozen).elim

theorem not_loan_chain (x : State GalilVM) (ha : x.vm.chain ≠ .idle) : ¬ NeedsLoan x :=
  fun h => ha h.2.1

theorem not_loan_shift (x : State GalilVM) (hm : x.ctl.mode = .shift) : ¬ NeedsLoan x := by
  intro h
  have hbad := h.1.symm.trans hm
  cases hbad

theorem not_loan_rest (x : State GalilVM) (h : PalPeg.PhysicalScanCount.CountAtRest x) : ¬ NeedsLoan x := by
  intro hn
  rcases h.2.2.2 with hs | hs <;> simp [NeedsLoan, searchActive, hs] at hn

theorem not_loan_count_target (w : List (Fin 2)) (x : State GalilVM)
    (hm : x.ctl.mode = .scan) (hs : PalPeg.FrameFunction.starvedTest x = false)
    (hc : 1 < x.ctl.clock) (hr : restartGuardTest x.vm = false)
    (ha : x.vm.chain ≠ .idle) : ¬ NeedsLoan (successor w x) := by
  apply not_loan_chain
  rw [successor, PalPeg.PhysicalGuardProbe.tickFun_nonstarved_count _ _ 0 1 0 w _ 2048 x hm hs hr hc]
  change (backgroundFun _ x.vm).chain ≠ .idle
  rw [backgroundFun_of_active _ x.vm ha]
  exact PalPeg.PhysicalRestartStorage.chainStep_active _ ha

theorem not_loan_rest_target (w : List (Fin 2)) (x : State GalilVM)
    (hs : PalPeg.FrameFunction.starvedTest x = false)
    (h : PalPeg.PhysicalScanCount.CountAtRest x) : ¬ NeedsLoan (successor w x) := by
  have hr : restartGuardTest x.vm = false := by simp [restartGuardTest, h.2.2.1]
  rw [successor, PalPeg.PhysicalGuardProbe.tickFun_nonstarved_count _ _ 0 1 0 w _ 2048 x h.1 hs hr h.2.1]
  change ¬ NeedsLoan ⟨_, backgroundFun _ x.vm⟩
  rw [backgroundFun_id_of_searchAtRest _ x.vm h.2.2.1 h.2.2.2]
  intro hn
  have ha := hn.2.2
  rcases h.2.2.2 with hsearch | hsearch <;> simp [searchActive, hsearch] at ha

theorem not_loan_entry_target (w : List (Fin 2)) (x : State GalilVM)
    (hs : PalPeg.FrameFunction.starvedTest x = false)
    (ht : Tick (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x (successor w x))
    (he : Entry w x) : ¬ NeedsLoan (successor w x) := by
  obtain ⟨t, hcmp, hmis, hg⟩ := PalPeg.PhysicalShiftDispatch.comparison_of_entry w x hs ht he
  obtain ⟨u, hu⟩ := beginShift_exists t hg
  have hcan : PalPeg.GalilScaffoldChainVerifier.canRight x.vm.right := by
    apply (canRightTest_iff _).mpr
    simpa [PalPeg.FrameFunction.starvedTest, PalPeg.FrameFunction.starvedOf, he.1] using hs
  obtain ⟨wm, hw, _⟩ := he.2.2
  rw [successor, PalPeg.PhysicalShiftLanding.tick_eq_entry centreC placeC 0 1 0 w x t u
    he.1 he.2.1 ⟨wm, hw⟩ hcan hcmp hmis hg hu]
  exact not_loan_shift _ rfl

theorem not_loan_shift_target (w : List (Fin 2)) (x : State GalilVM)
    (hm : x.ctl.mode = .shift) (ha : x.vm.chain ≠ .idle) : ¬ NeedsLoan (successor w x) := by
  simp only [successor, tickFun, hm]
  split
  · exact not_loan_shift _ hm
  · exact not_loan_chain _ ha

/-- Reuse a verified active row when its source and destination both use the
full mirror. The dispatcher equality is proved from the source encoding. -/
theorem active_of_previous (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : RoutedState) (he : Enc w x p) (hs : PalPeg.FrameFunction.starvedTest x = false)
    (hx : ¬ NeedsLoan x) (hy : ¬ NeedsLoan (successor w x))
    (hstep : PalPeg.PhysicalSnapshotInvariant.Enc w x p →
      PalPeg.PhysicalSnapshotInvariant.Enc w (successor w x)
        ((PalPeg.PhysicalSnapshotEntryDispatch.machine rest).apply blankM p none)) :
    Enc w (successor w x) ((machine rest).apply blankM p none) := by
  rw [previous_active rest w x p he hs (fun hg => hx (PalPeg.PhysicalGrowCount.needs_source x hg))
    (fun hm => hx (PalPeg.PhysicalGrowMatchCase.needs_source x hm))]
  exact (enc_full w _ _ hy).mpr (hstep ((enc_full w x p hx).mp he))

/-- The active dispatcher proof with its residual continuation at this exact
source. This permits wrappers to carry additional invariants without assuming
that invariant for every hypothetical source of the old encoding. -/
theorem active_of_remaining (rest : RestCommands) (w : List (Fin 2))
    (st : ℕ → State GalilVM) (Tc : ℕ → ℕ)
    (hpre : PreTraceIMW centreC placeC 0 1 0 w st Tc) (_hcanon : CanonTrace 0 w st Tc)
    (m : Mirrored1 (tapeCount 0)) (p : RoutedState)
    (hon : PalPeg.LocalShadowConcrete.ArrivedOnRun (localGood (spare := 0)) (postPhase 0 1 0) w
      (heldAfter (Tc w.length) st) m)
    (hnotFrozen : ¬ frozenAt w m) (henc : Enc w (absSC m) p)
    (hstarved : PalPeg.FrameFunction.starvedTest (absSC m) = false)
    (htick : Tick (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 (absSC m)
      (successor w (absSC m)))
    (hother : ¬ PalPeg.PhysicalScanCount.CountAtRest (absSC m) →
      ¬ PalPeg.PhysicalBoundaryCount.CountWatch (absSC m) →
      ¬ PalPeg.PhysicalBoundaryCount.CountBackReady (absSC m) →
      (absSC m).ctl.mode ≠ .shift → ¬ Entry w (absSC m) →
      ¬ PalPeg.PhysicalGrowCount.CountGrow (absSC m) →
      ¬ PalPeg.PhysicalGrowMatchCase.MatchGrow (absSC m) →
      Enc w (successor w (absSC m)) ((machine rest).apply blankM p none)) :
    Enc w (successor w (absSC m)) ((machine rest).apply blankM p none) := by
  by_cases hgrow : PalPeg.PhysicalGrowCount.CountGrow (absSC m)
  · exact forward_grow rest w (absSC m) p henc hstarved hgrow
  by_cases hmatch : PalPeg.PhysicalGrowMatchCase.MatchGrow (absSC m)
  · obtain ⟨arrived, hlen, hh⟩ := PalPeg.PhysicalShiftSource.heads_onRun w st Tc hpre m hon hnotFrozen hmatch.1.1
    exact forward_match rest w arrived (absSC m) p henc hstarved hmatch hh.rightRep hlen
  by_cases hentry : Entry w (absSC m)
  · obtain ⟨wm, hw, _⟩ := hentry.2.2
    apply active_of_previous rest w (absSC m) p henc hstarved
      (not_loan_chain _ (by simp [hw]))
      (not_loan_entry_target w (absSC m) hstarved htick hentry)
    intro henc
    exact PalPeg.PhysicalSnapshotEntryDispatch.forward_entry rest w st Tc hpre m p hon hnotFrozen henc hstarved htick hentry
  by_cases hshift : (absSC m).ctl.mode = .shift
  · apply active_of_previous rest w (absSC m) p henc hstarved (not_loan_shift _ hshift)
      (not_loan_shift_target w (absSC m) hshift
        (shift_nonidle_onRun w st Tc hpre m hon.onRun hnotFrozen hshift))
    intro henc
    rw [PalPeg.PhysicalSnapshotEntryDispatch.previous_when rest w (absSC m) p henc (Or.inl (by rw [hshift]; decide))]
    exact PalPeg.PhysicalSnapshotShiftDispatch.forward_shift rest w (absSC m) p henc hshift hstarved
      (PalPeg.PhysicalShift.copyIdle_onRun w st Tc hpre m hon.onRun hnotFrozen hshift)
      (PalPeg.PhysicalShift.remainingBound_onRun w st Tc hpre m hon.onRun hnotFrozen) htick
  by_cases hrest : PalPeg.PhysicalScanCount.CountAtRest (absSC m)
  · apply active_of_previous rest w (absSC m) p henc hstarved (not_loan_rest _ hrest)
      (not_loan_rest_target w (absSC m) hstarved hrest)
    intro henc
    obtain ⟨hmode, hclock, hidle, hsearch⟩ := hrest
    rw [PalPeg.PhysicalSnapshotEntryDispatch.previous_when rest w (absSC m) p henc (Or.inr (by omega)),
      PalPeg.PhysicalSnapshotShiftDispatch.previous_nonshift rest w (absSC m) p henc hshift]
    exact PalPeg.PhysicalSnapshotMachine.forward_atRest rest w (absSC m) p henc hmode hstarved hclock hidle hsearch
  by_cases hwatch : PalPeg.PhysicalBoundaryCount.CountWatch (absSC m)
  · obtain ⟨hmode, hclock, wm, hchain⟩ := hwatch
    apply active_of_previous rest w (absSC m) p henc hstarved (not_loan_chain _ (by simp [hchain]))
      (not_loan_count_target w (absSC m) hmode hstarved hclock
        (by simp [restartGuardTest, hchain]) (by simp [hchain]))
    intro henc
    rw [PalPeg.PhysicalSnapshotEntryDispatch.previous_when rest w (absSC m) p henc (Or.inr (by omega)),
      PalPeg.PhysicalSnapshotShiftDispatch.previous_nonshift rest w (absSC m) p henc hshift]
    exact PalPeg.PhysicalSnapshotMachine.forward_watch rest w (absSC m) p henc hmode hstarved hclock htick wm hchain
  by_cases hback : PalPeg.PhysicalBoundaryCount.CountBackReady (absSC m)
  · obtain ⟨v, h, lag, credit, ver, hb, _⟩ := hback.2.2
    apply active_of_previous rest w (absSC m) p henc hstarved (not_loan_chain _ (by simp [hb]))
      (not_loan_count_target w (absSC m) hback.1 hstarved hback.2.1
        (by simp [restartGuardTest, hb]) (by simp [hb]))
    intro henc
    have hperiod := PalPeg.PhysicalChainShape.period_onRun w st Tc hpre m hon.onRun hnotFrozen
    obtain ⟨hmode, hclock, first, last, xs, h, lag, credit, ver, hchain⟩ :=
      PalPeg.PhysicalBoundaryCount.entry_of_backReady hperiod.1 hback
    rw [PalPeg.PhysicalSnapshotEntryDispatch.previous_when rest w (absSC m) p henc (Or.inr (by omega)),
      PalPeg.PhysicalSnapshotShiftDispatch.previous_nonshift rest w (absSC m) p henc hshift]
    exact PalPeg.PhysicalSnapshotMachine.forward_entry rest w (absSC m) p henc first last xs h lag credit ver
      hchain hmode hstarved hclock hperiod.2
  exact hother hrest hwatch hback hshift hentry hgrow hmatch

/-- All previously connected cases are retained. The residual obligation now
uses the same encoding as the actual borrowed-mirror feed and starvation rows. -/
theorem cases_of_remaining (rest : RestCommands)
    (hother : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC 0 1 0 w st Tc → CanonTrace 0 w st Tc →
      ∀ (m : Mirrored1 (tapeCount 0)) (p : RoutedState),
        PalPeg.LocalShadowConcrete.ArrivedOnRun (localGood (spare := 0)) (postPhase 0 1 0) w
          (heldAfter (Tc w.length) st) m →
        ¬ frozenAt w m → Enc w (absSC m) p →
        PalPeg.FrameFunction.starvedTest (absSC m) = false →
        Tick (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 (absSC m)
          (successor w (absSC m)) →
        ¬ PalPeg.PhysicalScanCount.CountAtRest (absSC m) →
        ¬ PalPeg.PhysicalBoundaryCount.CountWatch (absSC m) →
        ¬ PalPeg.PhysicalBoundaryCount.CountBackReady (absSC m) →
        (absSC m).ctl.mode ≠ .shift → ¬ Entry w (absSC m) →
        ¬ PalPeg.PhysicalGrowCount.CountGrow (absSC m) →
        ¬ PalPeg.PhysicalGrowMatchCase.MatchGrow (absSC m) →
        Enc w (successor w (absSC m)) ((machine rest).apply blankM p none)) :
    TickCases (machine rest) blankM Enc := by
  constructor
  · intro w st Tc hpre hcanon m p hon hnotFrozen henc hstarved
    exact forward_starved rest w (absSC m) p henc hstarved
  · intro w st Tc hpre hcanon m p hon hnotFrozen henc hstarved htick
    exact active_of_remaining rest w st Tc hpre hcanon m p hon hnotFrozen henc hstarved htick
      (hother w st Tc hpre hcanon m p hon hnotFrozen henc hstarved htick)

/-- info: 'PalPeg.PhysicalLoanDispatch.forward_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forward_match

/-- info: 'PalPeg.PhysicalLoanDispatch.forward_grow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forward_grow

/-- info: 'PalPeg.PhysicalLoanDispatch.forward_feed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forward_feed

/-- info: 'PalPeg.PhysicalLoanDispatch.forward_starved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forward_starved

/-- info: 'PalPeg.PhysicalLoanDispatch.cases_of_remaining' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cases_of_remaining

/-- info: 'PalPeg.PhysicalLoanDispatch.active_of_remaining' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms active_of_remaining

end PalPeg.PhysicalLoanDispatch
