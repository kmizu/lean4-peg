import PalPeg.PhysicalSnapshotEntryTick
import PalPeg.PhysicalSnapshotShiftDispatch

/-! # Shift entry on the common machine carrying restart copies -/
set_option autoImplicit false
namespace PalPeg.PhysicalSnapshotEntryDispatch
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract
open PalPeg.PhysicalSearchSnapshots (saved put)
open PalPeg.PhysicalRestartStorage
open PalPeg.PhysicalSnapshotInvariant (Enc OldEnc)
open PalPeg.PhysicalCacheInvariant (Running running_core)
open PalPeg.PhysicalCacheMachine (successor)
open PalPeg.PhysicalScanCount (RestCommands)
open PalPeg.PhysicalShiftDispatch (RoutedState RoutedStep RoutedCore liftConfig liftStep select select_apply Entry)
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilScaffoldCounter (Counter positive)
open PalPeg.GalilScaffoldChainVerifier (canRight)
open PalPeg.GalilFinalAssembly2 (centreC placeC)
open PalPeg.Local (readWin)
open PalPeg.LocalRoleRouting (decode)
open PalPeg.CloseoutCheckW (PreTraceIMW CanonTrace)
open PalPeg.LocalSysConcrete (absSC)
open PalPeg.LocalReplayParked (Mirrored1)
open PalPeg.LocalBlankState (tapeCount)
open PalPeg.ShadowedLocalFinal (localGood postPhase frozenAt heldAfter)

noncomputable def machine (rest : RestCommands) : RoutedStep :=
  let old := PalPeg.PhysicalSnapshotShiftDispatch.machine rest
  select PalPeg.PhysicalShiftDispatch.entryTest
    (select PalPeg.PhysicalShiftDispatch.consumeTest
      (liftStep (PalPeg.PhysicalSnapshotEntryTick.step true) old)
      (liftStep (PalPeg.PhysicalSnapshotEntryTick.step false) old)) old

theorem apply_previous (rest : RestCommands) (p : RoutedState) (input : Option (Fin 2))
    (htest : PalPeg.PhysicalShiftDispatch.entryTest p.1 input
      (fun j => readWin blankM macroRadius (p.2 j)) = false) :
    (machine rest).apply blankM p input = (PalPeg.PhysicalSnapshotShiftDispatch.machine rest).apply blankM p input := by
  rw [machine, select_apply, htest, if_neg Bool.false_ne_true]

theorem entry_saved (w : List (Fin 2)) (x : State GalilVM) (boundary last spare : Counter)
    (hentry : Entry w x) : Entry w (saved x boundary last spare) := by
  obtain ⟨hmode, hclock, wm, hchain, hne, hguard⟩ := hentry
  refine ⟨hmode, hclock, wm, hchain, hne, ?_⟩
  change shiftGuardTest (compareFun _ (replace x.vm boundary last spare spare)) = true
  rw [compare_replace _ x.vm boundary last spare spare (by simp [hchain])]
  exact hguard

/-- Guard selection needs verifier availability, which comes from the original
canonical tick even when the encoded search counters hold restart copies. -/
theorem entryTest_ready (w : List (Fin 2)) (x : State GalilVM) (p : RoutedCore)
    (henc : Running w x (decode p)) (hstarved : PalPeg.FrameFunction.starvedTest x = false)
    (hentry : Entry w x)
    (hready : ∀ wm : PalPeg.GalilScaffoldChainWatch.State,
      x.vm.chain = .watch wm → positive wm.lag = true → canRight wm.machine.verifier) :
    PalPeg.PhysicalShiftDispatch.entryTest (liftConfig p).1 none
      (fun j => readWin blankM macroRadius (p.2 j)) = true := by
  obtain ⟨hmode, hclock, wm, hchain, hne, hguard⟩ := hentry
  have hcan : canRight x.vm.right := by
    apply (canRightTest_iff _).mpr
    simpa [PalPeg.FrameFunction.starvedTest, PalPeg.FrameFunction.starvedOf, hmode] using hstarved
  obtain ⟨T, hT, _⟩ := running_core henc
  have hm : (decode p).1.ctl.mode = x.ctl.mode := congrArg PalPeg.GalilScaffoldController.Control.mode hT.1.1.ctl
  have hc : (decode p).1.ctl.clock.val = x.ctl.clock := congrArg PalPeg.GalilScaffoldController.Control.clock hT.1.1.ctl
  have htag : (decode p).1.chainTag = chainTagOf x.vm.chain := hT.1.1.chainTag
  change PalPeg.PhysicalShiftDispatch.entryRead (decode p).1
    (PalPeg.PhysicalShiftDispatch.microWindows p.1.1 _) = true
  rw [PalPeg.PhysicalShiftDispatch.microWindows_read w x p henc]
  rw [PalPeg.PhysicalShiftDispatch.entryRead, hm, hc, htag,
    PalPeg.PhysicalShiftDispatch.starvedRead_micro w x (decode p) henc, hstarved,
    PalPeg.PhysicalShiftDispatch.agreeRead_running w x (decode p) henc hcan,
    PalPeg.PhysicalCompareGuard.scanShiftRead_running_ready w x (decode p) henc hmode hstarved wm hchain
      (hready wm hchain) hne]
  simp [hmode, hclock, hchain, hne, hguard, chainTagOf]

theorem forward_feed (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : RoutedState) (a : Fin 2) (henc : Enc w x p) :
    Enc w (PalPeg.GalilArriveChain.arriveState' a x) ((machine rest).apply blankM p (some a)) := by
  rw [apply_previous rest p (some a) (by cases hq : p.1.2 <;> simp [PalPeg.PhysicalShiftDispatch.entryTest, hq])]
  exact PalPeg.PhysicalSnapshotShiftDispatch.forward_feed rest w x p a henc

theorem forward_starved (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : RoutedState) (henc : Enc w x p) (hstarved : PalPeg.FrameFunction.starvedTest x = true) :
    Enc w x ((machine rest).apply blankM p none) := by
  obtain ⟨y, hrelated, hy⟩ := henc.1
  rw [apply_previous rest p none (PalPeg.PhysicalShiftDispatch.entryTest_starved w y p hy
    ((related_starved hrelated).trans hstarved))]
  exact PalPeg.PhysicalSnapshotShiftDispatch.forward_starved rest w x p henc hstarved

theorem previous_when (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : RoutedState) (henc : Enc w x p) (hskip : x.ctl.mode ≠ .scan ∨ x.ctl.clock ≠ 1) :
    (machine rest).apply blankM p none = (PalPeg.PhysicalSnapshotShiftDispatch.machine rest).apply blankM p none := by
  obtain ⟨y, hrelated, hy⟩ := henc.1
  apply apply_previous
  rcases p with ⟨⟨roles, q⟩, T⟩
  cases q with
  | inl tag => rfl
  | inr q =>
    obtain ⟨U, hU, _⟩ := running_core (p := (q, fun j => T (roles j))) hy
    have hcontrol : ctlAbs q.ctl = x.ctl := hU.1.1.ctl.trans hrelated.1.symm
    have hm : q.ctl.mode = x.ctl.mode := congrArg PalPeg.GalilScaffoldController.Control.mode hcontrol
    have hc : q.ctl.clock.val = x.ctl.clock := congrArg PalPeg.GalilScaffoldController.Control.clock hcontrol
    change PalPeg.PhysicalShiftDispatch.entryRead q _ = false
    rcases hskip with hmode | hclock
    · simp [PalPeg.PhysicalShiftDispatch.entryRead, hm, hmode]
    · simp [PalPeg.PhysicalShiftDispatch.entryRead, hc, hclock]

/-- All source facts are supplied from the original consumer run and legal
tick. The saved representation is never assumed to lie on that run. -/
theorem forward_entry (rest : RestCommands) (w : List (Fin 2))
    (st : ℕ → State GalilVM) (Tc : ℕ → ℕ)
    (hpre : PreTraceIMW centreC placeC 0 1 0 w st Tc)
    (m : Mirrored1 (tapeCount 0)) (p : RoutedState)
    (hon : PalPeg.LocalShadowConcrete.ArrivedOnRun (localGood (spare := 0))
      (postPhase 0 1 0) w (heldAfter (Tc w.length) st) m)
    (hnf : ¬ frozenAt w m) (henc : Enc w (absSC m) p)
    (hstarved : PalPeg.FrameFunction.starvedTest (absSC m) = false)
    (htick : Tick (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048
      (absSC m) (successor w (absSC m))) (hentry : Entry w (absSC m)) :
    Enc w (successor w (absSC m)) ((machine rest).apply blankM p none) := by
  obtain ⟨t, hcmp, hmis, hguard⟩ := PalPeg.PhysicalShiftDispatch.comparison_of_entry w (absSC m) hstarved htick hentry
  obtain ⟨wm, hchain, hfirst, hmid⟩ := PalPeg.PhysicalShiftStart.source_of_guard hcmp hmis hguard
  obtain ⟨h, age, spare, hInv, hsaved⟩ := henc.2 wm (Or.inl hchain)
  rcases p with ⟨⟨roles, q⟩, T⟩
  cases q with
  | inl tag =>
    have hsourceStarved : PalPeg.FrameFunction.starvedTest
        (saved (absSC m) wm.machine.control.boundary wm.machine.control.last spare) = false := hstarved
    rw [hsaved.1, PalPeg.PhysicalBootFeed.initial_starved] at hsourceStarved
    cases hsourceStarved
  | inr q =>
    let p : RoutedCore := ((roles, q), T)
    let sx := saved (absSC m) wm.machine.control.boundary wm.machine.control.last spare
    have htest := entryTest_ready w sx p hsaved hstarved
      (entry_saved w (absSC m) _ _ _ hentry) (fun other hother =>
        PalPeg.PhysicalCompareGuard.verifier_ready_of_scanTick w htick hentry.1 other hother)
    change PalPeg.PhysicalShiftDispatch.entryTest (liftConfig p).1 none
      (fun j => readWin blankM macroRadius ((liftConfig p).2 j)) = true at htest
    change Enc w _ ((machine rest).apply blankM (liftConfig p) none)
    rw [machine, select_apply, htest, if_pos rfl,
      PalPeg.PhysicalShiftDispatch.select_lift_apply PalPeg.PhysicalShiftDispatch.consumeTest
        PalPeg.PhysicalSnapshotEntryTick.step _ p none (positive wm.lag)
        (PalPeg.PhysicalShiftDispatch.consumeTest_running w sx p hsaved wm hchain)]
    have hcan : canRight (absSC m).vm.right := by
      apply (canRightTest_iff _).mpr
      simpa [PalPeg.FrameFunction.starvedTest, PalPeg.FrameFunction.starvedOf, hentry.1] using hstarved
    obtain ⟨arrived, hlen, hheads⟩ := PalPeg.PhysicalShiftSource.heads_onRun w st Tc hpre m hon hnf hentry.1
    have hsecond := PalPeg.PhysicalShiftSource.immediate_good arrived (absSC m) hheads hcan hcmp hmis hguard _ hmid
    have hblock := (PalPeg.PhysicalChainShape.period_onRun w st Tc hpre m hon.onRun hnf).1
    obtain ⟨old, hold, hinternal⟩ := PalPeg.WindowPack.source_watch_of_guard hcmp hmis hguard
    have holdEq : old = wm := ChainVM.watch.inj (hold.symm.trans hchain)
    subst old
    have hmidBlock := PalPeg.GalilBranchInvariants.blockInv_step
      (ChainStep.watchStep wm _ (hinternal _ hmid)) (hchain ▸ hblock)
    obtain ⟨u, hu⟩ := beginShift_exists t hguard
    have hlanding : PalPeg.PhysicalShiftTick.moved (positive wm.lag) (absSC m) wm = successor w (absSC m) :=
      (PalPeg.PhysicalShiftLanding.moved_eq_entry (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w)
        1 0 (absSC m) wm hchain t u hcmp hmis hmid hmidBlock hu).trans
      (PalPeg.PhysicalShiftLanding.tick_eq_entry centreC placeC 0 1 0 w (absSC m) t u
        hentry.1 hentry.2.1 ⟨wm, hchain⟩ hcan hcmp hmis hguard hu).symm
    obtain ⟨hnextInv, hout⟩ := PalPeg.PhysicalSnapshotEntryTick.running (positive wm.lag)
      w arrived (absSC m) p wm hchain spare h age hInv hsaved hentry.1 hfirst hsecond hcan hheads.rightRep hlen
    rw [hlanding] at hout
    apply PalPeg.PhysicalSnapshotInvariant.of_watching w (successor w (absSC m)) _
      (PalPeg.GalilScaffoldChainWatch.immediate (PalPeg.PhysicalWatchStep.afterInternal (positive wm.lag) wm))
      (Or.inl (by rw [← hlanding]; rfl)) h _ _ hnextInv
    exact hout

theorem enc_initial (w : List (Fin 2)) :
    Enc w initialState (PalPeg.PhysicalRoles.initialControl, fun _ => PalPeg.Program.STape.blankTape blankM) :=
  PalPeg.PhysicalSnapshotInvariant.enc_initial w

/-- The new common machine now closes shift entry with the same copies that
count/watch entry/shift/feed preserve. Other comparison and restart arms remain
explicit obligations on this machine. -/
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
        Enc w (successor w (absSC m)) ((machine rest).apply blankM p none)) :
    TickCases (machine rest) blankM Enc := by
  constructor
  · intro w st Tc hpre hcanon m p hon hnotFrozen henc hstarved
    exact forward_starved rest w (absSC m) p henc hstarved
  · intro w st Tc hpre hcanon m p hon hnotFrozen henc hstarved htick
    by_cases hentry : Entry w (absSC m)
    · exact forward_entry rest w st Tc hpre m p hon hnotFrozen henc hstarved htick hentry
    by_cases hshift : (absSC m).ctl.mode = .shift
    · rw [previous_when rest w (absSC m) p henc (Or.inl (by rw [hshift]; decide))]
      exact PalPeg.PhysicalSnapshotShiftDispatch.forward_shift rest w (absSC m) p henc hshift hstarved
        (PalPeg.PhysicalShift.copyIdle_onRun w st Tc hpre m hon.onRun hnotFrozen hshift)
        (PalPeg.PhysicalShift.remainingBound_onRun w st Tc hpre m hon.onRun hnotFrozen) htick
    by_cases hrest : PalPeg.PhysicalScanCount.CountAtRest (absSC m)
    · obtain ⟨hmode, hclock, hidle, hsearch⟩ := hrest
      rw [previous_when rest w (absSC m) p henc (Or.inr (by omega)),
        PalPeg.PhysicalSnapshotShiftDispatch.previous_nonshift rest w (absSC m) p henc hshift]
      exact PalPeg.PhysicalSnapshotMachine.forward_atRest rest w (absSC m) p henc hmode hstarved hclock hidle hsearch
    by_cases hwatch : PalPeg.PhysicalBoundaryCount.CountWatch (absSC m)
    · obtain ⟨hmode, hclock, wm, hchain⟩ := hwatch
      rw [previous_when rest w (absSC m) p henc (Or.inr (by omega)),
        PalPeg.PhysicalSnapshotShiftDispatch.previous_nonshift rest w (absSC m) p henc hshift]
      exact PalPeg.PhysicalSnapshotMachine.forward_watch rest w (absSC m) p henc hmode hstarved hclock htick wm hchain
    by_cases hback : PalPeg.PhysicalBoundaryCount.CountBackReady (absSC m)
    · have hperiod := PalPeg.PhysicalChainShape.period_onRun w st Tc hpre m hon.onRun hnotFrozen
      obtain ⟨hmode, hclock, first, last, xs, h, lag, credit, ver, hchain⟩ :=
        PalPeg.PhysicalBoundaryCount.entry_of_backReady hperiod.1 hback
      rw [previous_when rest w (absSC m) p henc (Or.inr (by omega)),
        PalPeg.PhysicalSnapshotShiftDispatch.previous_nonshift rest w (absSC m) p henc hshift]
      exact PalPeg.PhysicalSnapshotMachine.forward_entry rest w (absSC m) p henc first last xs h lag credit ver
        hchain hmode hstarved hclock hperiod.2
    exact hother w st Tc hpre hcanon m p hon hnotFrozen henc hstarved htick hrest hwatch hback hshift hentry

/-- info: 'PalPeg.PhysicalSnapshotEntryDispatch.forward_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forward_entry

/-- info: 'PalPeg.PhysicalSnapshotEntryDispatch.cases_of_remaining' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cases_of_remaining

end PalPeg.PhysicalSnapshotEntryDispatch
