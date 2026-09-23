import PalPeg.PhysicalCacheInvariant
import PalPeg.PhysicalRoles
import PalPeg.PhysicalChainShape

/-!
# One machine for the cache-bearing branch proofs

The source window selects watch entry or spare preparation. Boot, arrivals and
starvation remain the existing transitions. This module proves the represented
branches against the same strengthened encoding; the remaining branches are
still required before the final physical obligation can be supplied.
-/
set_option autoImplicit false
namespace PalPeg.PhysicalCacheMachine
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract PalPeg.PhysicalBootFeed
open PalPeg.PhysicalScanCount PalPeg.PhysicalTickDispatch
open PalPeg.PhysicalCacheInvariant (Running running_core running_cache)
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilFinalAssembly2 (centreC placeC)
open PalPeg.Local (readWin)
open PalPeg.Program (STape)
open PalPeg.PhysicalPeriodMirror (mirrorIndex)
open PalPeg.PhysicalSpare (Rep)
open PalPeg.GalilScaffoldCounter (Counter ofNat)
open PalPeg.GalilScaffoldChainPeriod (Token)

/-- Only successful internal count consumption advances the spare. -/
noncomputable def prepareRead (q : CoreControl)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm macroRadius) : Bool :=
  countRead q ws && chainConsumesTest q ws && decide (watchVerdictTest q ws = some true)

noncomputable def activeStep (rest : RestCommands) : CoreStep :=
  PalPeg.PhysicalWatchEntry.withWatchEntry
    (branchStep prepareRead (PalPeg.PhysicalCountSpare.countStep rest) (countedStep (workStep rest)))

noncomputable def machine (rest : RestCommands) := PalPeg.PhysicalTickDispatch.machine (activeStep rest)

abbrev Enc := PalPeg.PhysicalCacheInvariant.Enc

noncomputable def successor (w : List (Fin 2)) (x : State GalilVM) : State GalilVM :=
  tickFun (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w)
    (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x

theorem forward_feed (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : PhysicalState) (a : Fin 2) (he : Enc w x p) :
    Enc w (PalPeg.GalilArriveChain.arriveState' a x) ((machine rest).apply blankM p (some a)) :=
  PalPeg.PhysicalCacheInvariant.forward_feed _ w x p a he

theorem forward_starved (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : PhysicalState) (he : Enc w x p) (hs : PalPeg.FrameFunction.starvedTest x = true) :
    Enc w x ((machine rest).apply blankM p none) :=
  PalPeg.PhysicalCacheInvariant.forward_starved _ w x p he hs

/-- Macro-window reads are supplied by the encoding and the verifier's legal
right move, not by hypotheses about the physical branch result. -/
theorem prepareRead_match (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : PalPeg.MachineStep.sweepClosure blankM (CoreEnc w) x p)
    (hmode : x.ctl.mode = .scan) (hstarved : PalPeg.FrameFunction.starvedTest x = false)
    (hclock : 1 < x.ctl.clock) (wm : PalPeg.GalilScaffoldChainWatch.State)
    (hchain : x.vm.chain = .watch wm) (a : Fin 3)
    (htok : PalPeg.GalilScaffoldChainConsume.symbol wm.machine.control.period.focus = some a)
    (hseen : PalPeg.GalilScaffoldInputHead.read
      (PalPeg.GalilScaffoldChainVerifier.right wm.machine.verifier) = some a)
    (hlag : PalPeg.GalilScaffoldCounter.positive wm.lag = true)
    (hcan : PalPeg.GalilScaffoldChainVerifier.canRight wm.machine.verifier) :
    prepareRead p.1 (fun j => readWin blankM macroRadius (p.2 j)) = true := by
  have hrestart : restartGuardTest x.vm = false := by simp [restartGuardTest, hchain]
  have htag : p.1.chainTag = .watchers := by
    obtain ⟨T, hT, _⟩ := he
    rw [hT.1.1.chainTag, hchain]
    rfl
  apply read_from_running prepareRead (fun _ => true) w x p he
  intro T hT
  let slots := fun slot => T (slotIndex slot)
  let ws := fun j => readWin blankM macroRadius (tapesOf slots j)
  have hws : ws = fun j => readWin blankM macroRadius (T j) := by
    funext j
    simp [ws, slots, tapesOf]
  have hperiod : periodOf x = some wm.machine.control.period := by simp [periodOf, hchain]
  have htoken : decToken (centreRead ws periodSlot) = wm.machine.control.period.focus := by
    rw [centreRead_periodSlot (K := macroRadius) hT.1.2 (le_refl margin) _ hperiod, decToken_encToken]
    rfl
  have hpos := (counterPositive_iff_belowRead hT.1.2 (by decide : 1 ≤ macroRadius)
    (le_refl margin) 11 wm.lag (by simp [counterOf, hchain])).mp hlag
  have hconsume : chainConsumesTest p.1 ws = true := by
    simpa [chainConsumesTest, htag, htoken, htok] using hpos
  have htest : watchVerdictTest p.1 ws = some true := by
    rw [watchVerdictTest_eq p.1 ws wm (by rw [htoken])
      (landingLetter_of_encoded (K := macroRadius) hT.1.2 (le_refl margin) 3 wm.machine.verifier
        (by simp [headOf, hchain]) hcan)]
    simp [watchVerdict, htok, hseen]
  have hcount : countRead p.1 ws = true :=
    countRead_eq hT.1 (by decide : 1 ≤ macroRadius) (le_refl margin)
      hmode hstarved hrestart hclock
  rw [← hws]
  simp only [prepareRead, hcount, hconsume, htest, decide_true, Bool.and_self]

theorem selected_match (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : PalPeg.MachineStep.sweepClosure blankM (CoreEnc w) x p)
    (hmode : x.ctl.mode = .scan) (hstarved : PalPeg.FrameFunction.starvedTest x = false)
    (hclock : 1 < x.ctl.clock) (wm : PalPeg.GalilScaffoldChainWatch.State)
    (hchain : x.vm.chain = .watch wm) (a : Fin 3)
    (htok : PalPeg.GalilScaffoldChainConsume.symbol wm.machine.control.period.focus = some a)
    (hseen : PalPeg.GalilScaffoldInputHead.read
      (PalPeg.GalilScaffoldChainVerifier.right wm.machine.verifier) = some a)
    (hlag : PalPeg.GalilScaffoldCounter.positive wm.lag = true)
    (hcan : PalPeg.GalilScaffoldChainVerifier.canRight wm.machine.verifier) :
    (activeStep rest).apply blankM p none =
      (PalPeg.PhysicalCountSpare.countStep rest).apply blankM p none := by
  have htag : p.1.chainTag = .watchers := by
    obtain ⟨T, hT, _⟩ := he
    rw [hT.1.1.chainTag, hchain]
    rfl
  have hentry : PalPeg.PhysicalWatchEntry.entryRead p.1 (fun j => readWin blankM macroRadius (p.2 j)) = false := by
    simp [PalPeg.PhysicalWatchEntry.entryRead, htag]
  have hp := prepareRead_match w x p he hmode hstarved hclock wm hchain a htok hseen hlag hcan
  rw [activeStep, PalPeg.PhysicalWatchEntry.withWatchEntry, branch_apply, hentry]
  simp only [Bool.false_eq_true, if_false]
  rw [branch_apply, hp]
  rfl

theorem match_successor (w : List (Fin 2)) (x : State GalilVM)
    (hmode : x.ctl.mode = .scan) (hstarved : PalPeg.FrameFunction.starvedTest x = false)
    (hclock : 1 < x.ctl.clock) (wm : PalPeg.GalilScaffoldChainWatch.State)
    (hchain : x.vm.chain = .watch wm) (a : Fin 3)
    (htok : PalPeg.GalilScaffoldChainConsume.symbol wm.machine.control.period.focus = some a)
    (hseen : PalPeg.GalilScaffoldInputHead.read
      (PalPeg.GalilScaffoldChainVerifier.right wm.machine.verifier) = some a)
    (hlag : PalPeg.GalilScaffoldCounter.positive wm.lag = true) :
    successor w x = countState (PalPeg.PhysicalCountConsume.caughtState x wm) := by
  have hrestart : restartGuardTest x.vm = false := by simp [restartGuardTest, hchain]
  have hactive : x.vm.chain ≠ .idle := by simp [hchain]
  rw [successor, PalPeg.PhysicalGuardProbe.tickFun_nonstarved_count _ _ 0 1 0 w _ 2048 x
    hmode hstarved hrestart hclock]
  change (⟨_, backgroundFun _ x.vm⟩ : State GalilVM) = _
  rw [backgroundFun_of_active _ x.vm hactive, hchain]
  simp only [chainStepFun, if_pos hlag]
  have hv : watchVerdict wm = some true := by
    simp [watchVerdict, htok, hseen]
  rw [hv]
  rfl

/-- The strengthened encoding supplies the cache to this final none-step case. -/
theorem forward_plain (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : PhysicalState) (he : Enc w x p)
    (hmode : x.ctl.mode = .scan) (hstarved : PalPeg.FrameFunction.starvedTest x = false)
    (hclock : 1 < x.ctl.clock) {y : State GalilVM}
    (htick : Tick (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x y)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm) (a : Fin 3)
    (htok : wm.machine.control.period.focus = .plain a)
    (hseen : PalPeg.GalilScaffoldInputHead.read
      (PalPeg.GalilScaffoldChainVerifier.right wm.machine.verifier) = some a)
    (hforward : wm.machine.control.forward = true)
    (hlag : PalPeg.GalilScaffoldCounter.positive wm.lag = true) :
    Enc w (successor w x) ((machine rest).apply blankM p none) := by
  have hcan := PalPeg.PhysicalCountReady.verifier_canRight_of_countTick w htick hmode hclock wm hchain hlag
  rw [match_successor w x hmode hstarved hclock wm hchain a
    (by simp [htok, PalPeg.GalilScaffoldChainConsume.symbol]) hseen hlag]
  rcases p with ⟨q, T⟩
  cases q with
  | inl tag => rw [he.1, initial_starved] at hstarved; cases hstarved
  | inr q =>
    rw [machine, apply_active (activeStep rest) w x (q, T) (running_core he) hstarved]
    change Running w (countState (PalPeg.PhysicalCountConsume.caughtState x wm))
      ((activeStep rest).apply blankM (q, T) none)
    rw [selected_match rest w x (q, T) (running_core he) hmode hstarved hclock wm hchain a
      (by simp [htok, PalPeg.GalilScaffoldChainConsume.symbol]) hseen hlag hcan]
    exact PalPeg.PhysicalCacheInvariant.running_plain rest w x (q, T) he hmode hstarved hclock
      htick wm hchain a htok hseen hforward hlag

/-- Watch entry is selected on this same machine, with the same boot/feed
encoding; the marked period premise is retained until supplied along the run. -/
theorem forward_entry (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : PhysicalState) (he : Enc w x p)
    (first last : Fin 3) (xs : List (Fin 3)) (h lag credit : PalPeg.GalilScaffoldCounter.Counter)
    (ver : PalPeg.GalilScaffoldInputHead.PlaceHead)
    (hback : x.vm.chain = .back ⟨[], .first first, xs.map PalPeg.GalilScaffoldChainPeriod.Token.plain ++ [.last last]⟩ h lag credit ver)
    (hmode : x.ctl.mode = .scan) (hstarved : PalPeg.FrameFunction.starvedTest x = false)
    (hclock : 1 < x.ctl.clock) (hperiod : PalPeg.ChainStoredPeriod.Stored x.vm.chain) :
    Enc w (successor w x) ((machine rest).apply blankM p none) := by
  rcases p with ⟨q, T⟩
  cases q with
  | inl tag => rw [he.1, initial_starved] at hstarved; cases hstarved
  | inr q =>
    rw [machine, apply_active (activeStep rest) w x (q, T) (running_core he) hstarved]
    change Running w (successor w x) ((activeStep rest).apply blankM (q, T) none)
    exact PalPeg.PhysicalCacheInvariant.running_entry _ w x (q, T) first last xs h lag credit ver
      hback he hmode hstarved hclock hperiod

/-- info: 'PalPeg.PhysicalCacheMachine.forward_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forward_plain

/-- info: 'PalPeg.PhysicalCacheMachine.forward_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forward_entry

theorem still_counter (rest : RestCommands) (p : CoreState)
    (hslot : p.1.slot.val = 0) (hmode : p.1.ctl.mode = .scan)
    (hphase : scanPhase p.1 (fun j => readWin blankM microRadius (p.2 j)) ≠ .compare)
    (hconsume : chainConsumesTest p.1 (fun j => readWin blankM microRadius (p.2 j)) = false)
    (c : Fin 16) :
    (PalPeg.LocalStepFusion.idealRun (workRule rest) blankM p none 12).2 (slotIndex (counterSlot c)) =
      p.2 (slotIndex (counterSlot c)) := by
  rw [workRule_eq, tickPhysRule_eq, tickRule_otherSlots _ _ _ _ _ p none hslot
    (slotIndex (counterSlot c)) (by simp [counterSlot])]
  have ha : ruleActs 1 0 p.1 (fun j => readWin blankM microRadius (p.2 j)) =
      withErase p.1.fppLive (fun j => readWin blankM microRadius (p.2 j)) (fun _ => []) :=
    physRule_acts_scan 1 0 fppBound_gt_start (by decide) p.1 _ hmode hphase hconsume
  rw [ha, withErase_at_other _ _ _ (counterSlot c)
    (by intro k; cases p.1.fppLive <;> simp [progSlotOf, counterSlot])]
  rfl

theorem core_still (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : PalPeg.PhysicalCacheInvariant.CoreInv w x p) (hmode : p.1.ctl.mode = .scan)
    (hphase : scanPhase p.1 (fun j => readWin blankM microRadius (p.2 j)) ≠ .compare)
    (hconsume : chainConsumesTest p.1 (fun j => readWin blankM microRadius (p.2 j)) = false) :
    PalPeg.PhysicalCacheInvariant.CoreInv w x
      (PalPeg.LocalStepFusion.idealRun (workRule rest) blankM p none 12) := by
  have hbase := PalPeg.PhysicalScanCount.core_still rest w x p he.1.1 hmode hphase hconsume
  have hcounter : ∀ c : Fin 16,
      (PalPeg.LocalStepFusion.idealRun (workRule rest) blankM p none 12).2 (slotIndex (counterSlot c)) =
        p.2 (slotIndex (counterSlot c)) := still_counter rest p he.1.1.2.1 hmode hphase hconsume
  have hmirror := PalPeg.PhysicalPeriodMirror.ideal_scan rest p he.1.1.2.1 hmode hphase
  generalize hr : PalPeg.LocalStepFusion.idealRun (workRule rest) blankM p none 12 = result at hbase hcounter hmirror ⊢
  refine ⟨⟨hbase, ?_⟩, ?_⟩
  · intro c
    obtain ⟨seg, ht⟩ := he.1.2 c
    exact ⟨seg, (hcounter c).trans ht⟩
  · have hf := tickRule_headFree (by decide : 2 ≤ microRadius)
      (fun q _ ws => ruleNext 1 0 fppBound_gt_start q ws) (modeCommands 0 rest)
      (fun q _ ws => ruleActs 1 0 q ws)
      (fun q _ ws j => ruleActs_length 1 0 (by decide : 1 + 3 ≤ microRadius) q ws j)
      p none he.1.1.2.1
    rw [← tickPhysRule_eq 1 0 fppBound_gt_start (by decide) (by decide) rest, ← workRule_eq, hr] at hf
    have hb : ruleNext 1 0 fppBound_gt_start p.1 (fun j => readWin blankM microRadius (p.2 j)) = p.1 := by
      simp only [ruleNext, hmode]
      rw [scanNext_background p.1 _ hphase, if_neg (by simp [hconsume])]
    rw [hb] at hf
    simp only [headFreeFields, Prod.mk.injEq] at hf
    have hp : result.1.polarity = p.1.polarity := hf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    change PalPeg.PhysicalCacheInvariant.Cache x (result.1.polarity 10) (result.2 (slotIndex (counterSlot 10)))
      (result.2 mirrorIndex)
    rw [hp, hcounter, hmirror]
    exact he.2

/-- Idle count retains even unnamed counters, which are needed at the next birth. -/
theorem running_still (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : Running w x p) (hmode : x.ctl.mode = .scan)
    (hstarved : PalPeg.FrameFunction.starvedTest x = false) (hclock : 1 < x.ctl.clock)
    (hidle : x.vm.chain = .idle) :
    Running w x ((workStep rest).apply blankM p none) := by
  have hrestart : restartGuardTest x.vm = false := by simp [restartGuardTest, hidle]
  apply PalPeg.PhysicalCacheInvariant.running_fused (workRule rest) w x x p none he
  intro T hT
  have hqmode := congrArg PalPeg.GalilScaffoldController.Control.mode hT.1.1.1.1.ctl
  change p.1.ctl.mode = x.ctl.mode at hqmode
  have hcount := countRead_eq hT.1.1.1 (by decide : 1 ≤ microRadius) micro_le_margin
    hmode hstarved hrestart hclock
  have hp : scanPhase p.1 (fun j => readWin blankM microRadius (T j)) ≠ .compare := by
    have hc := of_decide_eq_true (Bool.and_eq_true_iff.mp hcount).2
    simp only [tapesOf, Equiv.apply_symm_apply] at hc
    rw [hc]
    decide
  have hn : chainConsumesTest p.1 (fun j => readWin blankM microRadius (T j)) = false := by
    unfold chainConsumesTest
    rw [hT.1.1.1.1.chainTag, hidle]
    rfl
  exact core_still rest w x (p.1, T) hT (hqmode.trans hmode) hp hn

theorem running_clockDown {w : List (Fin 2)} {x : State GalilVM} {p : CoreState}
    (he : Running w x p) : Running w (countState x) (clockDown p.1, p.2) := by
  obtain ⟨T, hT, ht⟩ := he
  exact ⟨T, ⟨⟨core_clockDown hT.1.1, hT.1.2⟩, hT.2⟩, ht⟩

theorem selected_idle (rest : RestCommands) {w : List (Fin 2)} {x : State GalilVM} {p : CoreState}
    (he : Running w x p) (hidle : x.vm.chain = .idle) :
    (activeStep rest).apply blankM p none = (countedStep (workStep rest)).apply blankM p none := by
  have htag : p.1.chainTag = .idle := by
    obtain ⟨T, hT, _⟩ := running_core he
    rw [hT.1.1.chainTag, hidle]
    rfl
  simp [activeStep, PalPeg.PhysicalWatchEntry.withWatchEntry, branch_apply,
    PalPeg.PhysicalWatchEntry.entryRead, prepareRead, chainConsumesTest, htag]

theorem forward_atRest (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : PhysicalState) (he : Enc w x p)
    (hmode : x.ctl.mode = .scan) (hstarved : PalPeg.FrameFunction.starvedTest x = false)
    (hclock : 1 < x.ctl.clock) (hidle : x.vm.chain = .idle)
    (hsearch : x.vm.search.mode = .idle ∨ x.vm.search.mode = .missed) :
    Enc w (successor w x) ((machine rest).apply blankM p none) := by
  have hrestart : restartGuardTest x.vm = false := by simp [restartGuardTest, hidle]
  have hsuccessor : successor w x = countState x := by
    rw [successor, PalPeg.PhysicalGuardProbe.tickFun_nonstarved_count _ _ 0 1 0 w _ 2048 x
      hmode hstarved hrestart hclock]
    change (⟨_, backgroundFun _ x.vm⟩ : State GalilVM) = _
    rw [backgroundFun_id_of_searchAtRest _ x.vm hidle hsearch]
    rfl
  rw [hsuccessor]
  rcases p with ⟨q, T⟩
  cases q with
  | inl tag => rw [he.1, initial_starved] at hstarved; cases hstarved
  | inr q =>
    rw [machine, apply_active (activeStep rest) w x (q, T) (running_core he) hstarved]
    change Running w (countState x) ((activeStep rest).apply blankM (q, T) none)
    rw [selected_idle rest he hidle,
      counted_apply, countRead_running (running_core he) hmode hstarved hrestart hclock]
    simp only [if_true]
    exact running_clockDown (running_still rest w x (q, T) he hmode hstarved hclock hidle)

/-- info: 'PalPeg.PhysicalCacheMachine.forward_atRest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forward_atRest

open PalPeg.CloseoutCheckW (PreTraceIMW CanonTrace)
open PalPeg.LocalSysConcrete (absSC)
open PalPeg.LocalReplayParked (Mirrored1)
open PalPeg.LocalShadowConcrete (OnRun)
open PalPeg.LocalBlankState (tapeCount)
open PalPeg.ShadowedLocalFinal (localGood postPhase frozenAt heldAfter)
open PalPeg.PhysicalCountConsume (CountPlainMatch)

def CountWatchEntry (x : State GalilVM) : Prop :=
  x.ctl.mode = .scan ∧ 1 < x.ctl.clock ∧
    ∃ (first last : Fin 3) (xs : List (Fin 3)) (h lag credit : PalPeg.GalilScaffoldCounter.Counter)
      (ver : PalPeg.GalilScaffoldInputHead.PlaceHead),
      x.vm.chain = .back ⟨[], .first first, xs.map PalPeg.GalilScaffoldChainPeriod.Token.plain ++ [.last last]⟩ h lag credit ver

/-- Same finite machine and invariant for all proved cases. The residual keeps
OnRun and the legal tick, including the supply of marked periods at other back states. -/
theorem cases_of_remaining (rest : RestCommands)
    (hother : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC 0 1 0 w st Tc → CanonTrace 0 w st Tc →
      ∀ (m : Mirrored1 (tapeCount 0)) (p : PhysicalState),
        PalPeg.LocalShadowConcrete.ArrivedOnRun (localGood (spare := 0)) (postPhase 0 1 0) w (heldAfter (Tc w.length) st) m →
        ¬ frozenAt w m → Enc w (absSC m) p →
        PalPeg.FrameFunction.starvedTest (absSC m) = false →
        Tick (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 (absSC m)
          (successor w (absSC m)) →
        ¬ CountAtRest (absSC m) → ¬ CountPlainMatch (absSC m) → ¬ CountWatchEntry (absSC m) →
        Enc w (successor w (absSC m)) ((machine rest).apply blankM p none)) :
    TickCases (machine rest) blankM Enc := by
  constructor
  · intro w st Tc hpre hcanon m p hon hnotFrozen he hs
    exact forward_starved rest w (absSC m) p he hs
  · intro w st Tc hpre hcanon m p hon hnotFrozen he hs htick
    by_cases hrest : CountAtRest (absSC m)
    · obtain ⟨hmode, hclock, hidle, hsearch⟩ := hrest
      exact forward_atRest rest w (absSC m) p he hmode hs hclock hidle hsearch
    · by_cases hplain : CountPlainMatch (absSC m)
      · obtain ⟨hmode, hclock, wm, a, hchain, htok, hseen, hforward, hlag⟩ := hplain
        exact forward_plain rest w (absSC m) p he hmode hs hclock htick wm hchain a htok hseen hforward hlag
      · by_cases hentry : CountWatchEntry (absSC m)
        · obtain ⟨hmode, hclock, first, last, xs, h, lag, credit, ver, hback⟩ := hentry
          exact forward_entry rest w (absSC m) p he first last xs h lag credit ver hback hmode hs hclock
            (PalPeg.PhysicalChainShape.period_onRun w st Tc hpre m hon.onRun hnotFrozen).2
        · exact hother w st Tc hpre hcanon m p hon hnotFrozen he hs htick hrest hplain hentry

/-- info: 'PalPeg.PhysicalCacheMachine.cases_of_remaining' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cases_of_remaining

/-- The finite roles already allocated for boundary exchange wrap this same
machine and invariant. This version retains the assignment during each step. -/
noncomputable def routedMachine (rest : RestCommands) := PalPeg.LocalRoleRouting.hold (machine rest)

def routedEnc (w : List (Fin 2)) (x : State GalilVM) (p : PalPeg.PhysicalRoles.PhysicalState) : Prop :=
  Enc w x (PalPeg.LocalRoleRouting.decode p)

theorem routed_initial (w : List (Fin 2)) :
    routedEnc w initialState (PalPeg.PhysicalRoles.initialControl, fun _ => STape.blankTape blankM) :=
  PalPeg.PhysicalCacheInvariant.enc_initial w

theorem routed_feed (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : PalPeg.PhysicalRoles.PhysicalState) (a : Fin 2) (he : routedEnc w x p) :
    routedEnc w (PalPeg.GalilArriveChain.arriveState' a x) ((routedMachine rest).apply blankM p (some a)) := by
  rw [routedEnc, routedMachine, PalPeg.LocalRoleRouting.decode_hold]
  exact forward_feed rest w x (PalPeg.LocalRoleRouting.decode p) a he

theorem routed_cases (rest : RestCommands) (hc : TickCases (machine rest) blankM Enc) :
    TickCases (routedMachine rest) blankM routedEnc := by
  constructor
  · intro w st Tc hpre hcanon m p hon hnotFrozen he hs
    rw [routedEnc, routedMachine, PalPeg.LocalRoleRouting.decode_hold]
    exact hc.starved w st Tc hpre hcanon m (PalPeg.LocalRoleRouting.decode p) hon hnotFrozen he hs
  · intro w st Tc hpre hcanon m p hon hnotFrozen he hs htick
    rw [routedEnc, routedMachine, PalPeg.LocalRoleRouting.decode_hold]
    exact hc.active w st Tc hpre hcanon m (PalPeg.LocalRoleRouting.decode p) hon hnotFrozen he hs htick

/-- info: 'PalPeg.PhysicalCacheMachine.routed_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms routed_cases

/-- The real none-step selected by the common finite dispatcher retains h,
including its outer wrapper and count-clock update. -/
theorem periodMirror_entry (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : PhysicalState) (he : PalPeg.PhysicalCacheInvariant.Enc w x p)
    (hs : PalPeg.ChainStoredPeriod.Stored x.vm.chain)
    (first last : Fin 3) (xs : List (Fin 3)) (h lag credit : Counter)
    (ver : PalPeg.GalilScaffoldInputHead.PlaceHead)
    (hback : x.vm.chain = .back ⟨[], .first first, xs.map Token.plain ++ [.last last]⟩ h lag credit ver)
    (hmode : x.ctl.mode = .scan) (hstarved : PalPeg.FrameFunction.starvedTest x = false)
    (hclock : 1 < x.ctl.clock) :
    Rep true (ofNat (xs.length + 1))
      (((PalPeg.PhysicalCacheMachine.machine rest).apply blankM p none).2 mirrorIndex) := by
  rcases p with ⟨q, T⟩
  cases q with
  | inl tag => rw [he.1, PalPeg.PhysicalBootFeed.initial_starved] at hstarved; cases hstarved
  | inr q =>
    have hcore := PalPeg.PhysicalCacheInvariant.running_core he
    rw [PalPeg.PhysicalCacheMachine.machine,
      apply_active (PalPeg.PhysicalCacheMachine.activeStep rest) w x (q, T) hcore hstarved]
    change Rep true (ofNat (xs.length + 1))
      (((PalPeg.PhysicalCacheMachine.activeStep rest).apply blankM (q, T) none).2 mirrorIndex)
    rw [PalPeg.PhysicalCacheMachine.activeStep,
      PalPeg.PhysicalWatchEntry.selected_entry _ w x (q, T) _ h lag credit ver hback rfl
        hcore hmode hstarved hclock, counted_apply]
    exact PalPeg.PhysicalPeriodMirror.entry w x (q, T) hcore hs first last xs h lag credit ver hback none

end PalPeg.PhysicalCacheMachine
