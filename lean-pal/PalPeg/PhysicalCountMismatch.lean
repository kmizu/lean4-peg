import PalPeg.PhysicalCacheMachine

/-!
# Count consumption that breaks the watching chain

The failed comparison advances only the verifier. All counters, the period and
the prepared boundary spare are retained, including their signed representations.
The existing twelve-slot rule and the common cache invariant are used throughout.
-/
set_option autoImplicit false
namespace PalPeg.PhysicalCountMismatch
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract PalPeg.PhysicalBoundary
open PalPeg.PhysicalBootFeed PalPeg.PhysicalScanCount PalPeg.PhysicalTickDispatch
open PalPeg.PhysicalCountReady
open PalPeg.PhysicalCacheInvariant (CoreInv Running Cache running_core running_cache)
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilFinalAssembly2 (centreC placeC)
open PalPeg.GalilScaffoldChainVerifier (canRight)
open PalPeg.Program (STape)
open PalPeg.Local (readWin)
open PalPeg.CloseoutCoreEnc12 PalPeg.LocalStepFusion

def brokenWatch (wm : PalPeg.GalilScaffoldChainWatch.State) : PalPeg.GalilScaffoldChainWatch.State :=
  {wm with machine := {wm.machine with verifier := PalPeg.GalilScaffoldChainVerifier.right wm.machine.verifier}}

def brokenState (x : State GalilVM) (wm : PalPeg.GalilScaffoldChainWatch.State) : State GalilVM :=
  ⟨x.ctl, {x.vm with chain := .broken (brokenWatch wm)}⟩

theorem broken_control (w : List (Fin 2)) (x : State GalilVM) (q : CoreControl)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm)
    (he : EncControl w x q) : EncControl w (brokenState x wm) {q with chainTag := .broken} where
  ctl := he.ctl
  chainTag := rfl
  chainPhase := by simpa only [hchain, chainConsumeOf, brokenState, brokenWatch] using he.chainPhase
  chainForward := by simpa only [hchain, chainConsumeOf, brokenState, brokenWatch] using he.chainForward
  chainBroken := by simpa only [hchain, chainConsumeOf, brokenState, brokenWatch] using he.chainBroken
  fppMode := he.fppMode
  fppFinalStage := he.fppFinalStage
  fppPc := he.fppPc
  fppDone := he.fppDone
  dpPc := he.dpPc
  dpDone := he.dpDone
  searchMode := he.searchMode
  searchFinalStage := he.searchFinalStage
  searchQuarter := he.searchQuarter
  periodOnly := he.periodOnly
  placeGap := by
    intro i place hp
    apply he.placeGap i place
    have hh : placeOf (brokenState x wm) i = placeOf x i := by
      fin_cases i <;> simp only [placeOf, brokenState, hchain]
    rw [← hh]
    exact hp
  onLetter := he.onLetter
  leftFirst := he.leftFirst

/-- Before the view command moves the verifier, the watch/broken tag change
has no tape observation. Background program erasure is handled separately. -/
theorem broken_tapes (x : State GalilVM) (q : CoreControl) (T : Slot → STape Γm)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm)
    (he : EncTapes margin x q.polarity q.gap q.micro q.fppLive q.dpLive T) :
    EncTapes margin (stepState (brokenState x wm) wm.machine.verifier)
      q.polarity q.gap q.micro q.fppLive q.dpLive T := by
  apply encTapes_congr margin x (stepState (brokenState x wm) wm.machine.verifier) q.polarity q.gap q.micro q.fppLive q.dpLive T
    (fun _ => rfl) (fun _ => rfl) ?_ ?_ ?_ ?_ ?_ he
  · funext c
    fin_cases c <;> simp only [counterOf, stepState, brokenState, chainVerifierBack, hchain] <;> rfl
  · funext v
    fin_cases v <;> simp only [headOf, stepState, brokenState, chainVerifierBack, hchain]
  · funext i
    fin_cases i <;> simp only [placeOf, stepState, brokenState, chainVerifierBack, hchain]
  · simp only [periodOf, stepState, brokenState, chainVerifierBack, hchain]
    rfl
  · simp only [answerOf, stepState, brokenState, chainVerifierBack, hchain]

/-- A failed verdict writes no chain tape, including at FIRST/LAST. -/
theorem failed_acts (q : CoreControl) (ws : Fin tapeCountM → PalPeg.Local.Window Γm microRadius)
    (hv : watchVerdictTest q ws = some false) : scanConsumeActs q ws = fun _ => [] := by
  funext j
  simp [scanConsumeActs, hv]

theorem core_mismatch (rest : RestCommands) (w : List (Fin 2))
    (x : State GalilVM) (p : CoreState) (he : CoreInv w x p)
    (hmode : p.1.ctl.mode = .scan)
    (hphase : scanPhase p.1 (fun tape => readWin blankM microRadius (p.2 tape)) ≠ .compare)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm) (a : Fin 3)
    (htok : PalPeg.GalilScaffoldChainConsume.symbol wm.machine.control.period.focus = some a)
    (hseen : PalPeg.GalilScaffoldInputHead.read
      (PalPeg.GalilScaffoldChainVerifier.right wm.machine.verifier) ≠ some a)
    (hlag : PalPeg.GalilScaffoldCounter.positive wm.lag = true)
    (hcan : canRight wm.machine.verifier) :
    CoreInv w (brokenState x wm) (idealRun (workRule rest) blankM p none 12) := by
  generalize hrun : idealRun (workRule rest) blankM p none 12 = result
  have henc : CoreEnc w x p := he.1.1
  let T := fun slot => p.2 (slotIndex slot)
  have hT : tapesOf T = p.2 := by funext tape; simp [T, tapesOf]
  let ws := fun tape => readWin blankM microRadius (tapesOf T tape)
  have hbackground : scanPhase p.1 ws ≠ .compare := by
    dsimp only [ws]
    rw [hT]
    exact hphase
  have hx3 : headOf x 3 = some wm.machine.verifier := by simp only [headOf, hchain]
  have hperiod : periodOf x = some wm.machine.control.period := by simp only [periodOf, hchain]
  have htoken : decToken (centreRead ws periodSlot) = wm.machine.control.period.focus := by
    rw [centreRead_periodSlot henc.1.2 micro_le_margin _ hperiod, decToken_encToken]
    rfl
  have htag : p.1.chainTag = .watchers := by rw [henc.1.1.chainTag, hchain]; rfl
  have hpos := (counterPositive_iff_belowRead henc.1.2 (by decide : 1 ≤ microRadius)
    micro_le_margin 11 wm.lag (by simp only [counterOf, hchain])).mp hlag
  have hconsume : chainConsumesTest p.1 ws = true := by
    simpa [chainConsumesTest, htag, htoken, htok] using hpos
  have hverdict : watchVerdict wm = some false := by
    simp [watchVerdict, htok, hseen]
  have htest : watchVerdictTest p.1 ws = watchVerdict wm :=
    watchVerdictTest_eq p.1 ws wm (by rw [htoken])
      (landingLetter_of_encoded henc.1.2 micro_le_margin 3 wm.machine.verifier hx3 hcan)
  have hrule : ruleNext 1 0 fppBound_gt_start p.1 ws = scanConsumeNext p.1 ws := by
    unfold ruleNext
    rw [hmode]
    dsimp only
    rw [scanNext_background p.1 ws hbackground, if_pos hconsume]
  have hheadOther : ∀ v : Fin 4, v ≠ 3 → headOf (brokenState x wm) v = headOf x v := by
    intro v hv
    fin_cases v <;> first | rfl | exact (hv rfl).elim
  have hy3 : headOf (brokenState x wm) 3 =
      some (PalPeg.GalilScaffoldChainVerifier.right wm.machine.verifier) := rfl
  have hready : ∀ v view, HeadSlotsRepAt margin p.1.gap p.1.micro T v view →
      HeadReady (scanCommands p.1 ws v) view := by
    intro v view hv
    by_cases hview : v = 3
    · subst v
      have hcmd : scanCommands p.1 ws 3 = .moveRight := by
        simp [scanCommands, hbackground, hconsume]
      rw [hcmd]
      exact moveRight_ready henc.1.2 micro_le_margin 3 wm.machine.verifier hx3 hcan view hv
    · simp only [scanCommands, if_neg hbackground, if_neg hview]
      trivial
  have hencoded : PalPeg.PhysicalEncoding.Enc w margin (brokenState x wm)
      ((idealRun (tickPhysRule 1 0 fppBound_gt_start (by decide : 1 + 3 ≤ microRadius)
        (by decide : 2 ≤ microRadius) rest) blankM (p.1, tapesOf T) none 12).1,
        fun slot => (idealRun (tickPhysRule 1 0 fppBound_gt_start (by decide : 1 + 3 ≤ microRadius)
          (by decide : 2 ≤ microRadius) rest) blankM (p.1, tapesOf T) none 12).2 (slotIndex slot)) := by
    refine enc_afterTickOfState margin 1 0 fppBound_gt_start (by decide) (by decide)
      micro_le_margin rest w x (brokenState x wm) p.1 T none henc.2.1 henc.2.2
      (scanCommands p.1 ws) (fun v => by rw [modeCommands_scan 0 rest p.1 none _ hmode])
      (fun v => if v = 3 ∧ chainConsumesTest p.1 ws then
        PalPeg.GalilScaffoldChainVerifier.right else id)
      (fun v => headOp_scanCommands p.1 ws v hbackground) ?_ ?_ hready henc.1.2 ?_
      (z := stepState (brokenState x wm) wm.machine.verifier)
      (fun _ => rfl) (fun _ => rfl) (counterOf_stepState _ _) (placeOf_stepState _ _)
      (periodOf_stepState _ _) (answerOf_stepState _ _) ?_
    · intro v
      by_cases hv : v = 3
      · subst v
        rw [hx3, hy3]
        rfl
      · rw [hheadOther v hv]
    · intro v head hhead
      by_cases hv : v = 3
      · subst v
        rw [hx3] at hhead
        rw [hy3, ← Option.some.inj hhead, if_pos ⟨rfl, hconsume⟩]
      · rw [hheadOther v hv, hhead, if_neg (fun h => hv h.1)]
        rfl
    · rw [hrule]
      simp only [scanConsumeNext, htest, hverdict]
      exact broken_control w x p.1 wm hchain henc.1.1
    · have hnext : scanConsumeNext p.1 ws = {p.1 with chainTag := .broken} := by
        simp only [scanConsumeNext, htest, hverdict]
      rw [hrule, hnext]
      have ha : ruleActs 1 0 p.1 ws = withErase p.1.fppLive ws (fun _ => []) := by
        simp only [ruleActs, hmode]
        rw [scanActs_background p.1 ws hbackground, failed_acts p.1 ws (htest.trans hverdict)]
      change EncTapes margin (stepState (brokenState x wm) wm.machine.verifier)
        p.1.polarity p.1.gap p.1.micro p.1.fppLive p.1.dpLive
        (fun slot => actList blankM (T slot) (ruleActs 1 0 p.1 ws (slotIndex slot)))
      rw [ha]
      apply encTapes_idleOnly margin _ p.1.polarity p.1.gap p.1.micro p.1.fppLive p.1.dpLive T _
        (broken_tapes x p.1 T wm hchain henc.1.2)
      · intro slot hslot
        rw [withErase_at_other _ _ _ slot hslot]
        rfl
      · exact idle_shape_withErase margin (by decide) (by decide) T p.1.fppLive _
          (fun _ => rfl) henc.1.2.idleShape
  have hcore : CoreEnc w (brokenState x wm) result := by
    constructor
    · simpa only [← workRule_eq, hT, Prod.eta, hrun] using hencoded
    · have hb := macroBoundary_tickRule
        (fun q _ ws => ruleNext 1 0 fppBound_gt_start q ws) (modeCommands 0 rest)
        (fun q _ ws => ruleActs 1 0 q ws)
        (fun q _ ws j => ruleActs_length 1 0 (by decide : 1 + 3 ≤ microRadius) q ws j)
        w x p none henc
      simpa only [← tickPhysRule_eq 1 0 fppBound_gt_start (by decide) (by decide) rest,
        ← workRule_eq, hrun] using hb
  have hcounter : ∀ c : Fin 16, result.2 (slotIndex (counterSlot c)) = p.2 (slotIndex (counterSlot c)) := by
    intro c
    rw [← hrun, workRule_eq, tickPhysRule_eq,
      tickRule_otherSlots _ _ _ _ _ p none henc.2.1 (slotIndex (counterSlot c)) (by simp [counterSlot])]
    have ha : ruleActs 1 0 p.1 ws = withErase p.1.fppLive ws (fun _ => []) := by
      simp only [ruleActs, hmode]
      rw [scanActs_background p.1 ws hbackground, failed_acts p.1 ws (htest.trans hverdict)]
    change actList blankM (p.2 (slotIndex (counterSlot c)))
      (ruleActs 1 0 p.1 (fun j => readWin blankM microRadius (p.2 j)) (slotIndex (counterSlot c))) = _
    rw [← hT]
    change actList blankM (tapesOf T (slotIndex (counterSlot c))) (ruleActs 1 0 p.1 ws (slotIndex (counterSlot c))) = _
    rw [ha, withErase_at_other _ _ _ (counterSlot c)
      (by intro k; cases p.1.fppLive <;> simp [progSlotOf, counterSlot])]
    rfl
  have hpol : result.1.polarity = p.1.polarity := by
    have hf := tickRule_headFree (by decide : 2 ≤ microRadius)
      (fun q _ ws => ruleNext 1 0 fppBound_gt_start q ws) (modeCommands 0 rest)
      (fun q _ ws => ruleActs 1 0 q ws)
      (fun q _ ws j => ruleActs_length 1 0 (by decide : 1 + 3 ≤ microRadius) q ws j)
      p none henc.2.1
    rw [← tickPhysRule_eq 1 0 fppBound_gt_start (by decide) (by decide) rest, ← workRule_eq, hrun] at hf
    have hbase : ruleNext 1 0 fppBound_gt_start p.1 (fun j => readWin blankM microRadius (p.2 j)) =
        {p.1 with chainTag := .broken} := by
      rw [← hT]
      change ruleNext 1 0 fppBound_gt_start p.1 ws = _
      rw [hrule]
      simp only [scanConsumeNext, htest, hverdict]
    rw [hbase] at hf
    simp only [headFreeFields, Prod.mk.injEq] at hf
    exact hf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨⟨hcore, ?_⟩, ?_⟩
  · intro c
    obtain ⟨seg, ht⟩ := he.1.2 c
    exact ⟨seg, (hcounter c).trans ht⟩
  · have hc := he.2
    rw [Cache, hchain] at hc
    have hmirror := PalPeg.PhysicalPeriodMirror.ideal_scan rest p he.1.1.2.1 hmode hphase
    rw [hrun] at hmirror
    change Cache (brokenState x wm) (result.1.polarity 10) (result.2 (slotIndex (counterSlot 10)))
      (result.2 PalPeg.PhysicalPeriodMirror.mirrorIndex)
    rw [hpol, hcounter, hmirror]
    exact hc


/-- The common strengthened invariant, including the spare, survives the sweep. -/
theorem running_mismatch (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : Running w x p) (hmode : x.ctl.mode = .scan)
    (hs : PalPeg.FrameFunction.starvedTest x = false) (hclock : 1 < x.ctl.clock)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm) (a : Fin 3)
    (htok : PalPeg.GalilScaffoldChainConsume.symbol wm.machine.control.period.focus = some a)
    (hseen : PalPeg.GalilScaffoldInputHead.read
      (PalPeg.GalilScaffoldChainVerifier.right wm.machine.verifier) ≠ some a)
    (hlag : PalPeg.GalilScaffoldCounter.positive wm.lag = true) (hcan : canRight wm.machine.verifier) :
    Running w (brokenState x wm) ((workStep rest).apply blankM p none) := by
  have hrestart : restartGuardTest x.vm = false := by simp [restartGuardTest, hchain]
  apply PalPeg.PhysicalCacheInvariant.running_fused (workRule rest) w x (brokenState x wm) p none he
  intro T hT
  have hqmode := congrArg PalPeg.GalilScaffoldController.Control.mode hT.1.1.1.1.ctl
  change p.1.ctl.mode = x.ctl.mode at hqmode
  have hcount := countRead_eq hT.1.1.1 (by decide : 1 ≤ microRadius) micro_le_margin
    hmode hs hrestart hclock
  have hp : scanPhase p.1 (fun j => readWin blankM microRadius (T j)) ≠ .compare := by
    have hc := of_decide_eq_true (Bool.and_eq_true_iff.mp hcount).2
    simp only [tapesOf, Equiv.apply_symm_apply] at hc
    rw [hc]
    decide
  exact core_mismatch rest w x (p.1, T) hT (hqmode.trans hmode) hp wm hchain a htok hseen hlag hcan

/-- A failed verdict never prepares or rotates the spare. The verdict itself
comes from the encoded token and the legally available moved verifier. -/
theorem prepareRead_mismatch (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : Running w x p) (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm)
    (a : Fin 3) (htok : PalPeg.GalilScaffoldChainConsume.symbol wm.machine.control.period.focus = some a)
    (hseen : PalPeg.GalilScaffoldInputHead.read
      (PalPeg.GalilScaffoldChainVerifier.right wm.machine.verifier) ≠ some a)
    (hcan : canRight wm.machine.verifier) :
    PalPeg.PhysicalCacheMachine.prepareRead p.1 (fun j => readWin blankM macroRadius (p.2 j)) = false := by
  apply read_from_running PalPeg.PhysicalCacheMachine.prepareRead (fun _ => false) w x p (running_core he)
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
  have htest : watchVerdictTest p.1 ws = some false := by
    rw [watchVerdictTest_eq p.1 ws wm (by rw [htoken])
      (landingLetter_of_encoded (K := macroRadius) hT.1.2 (le_refl margin) 3 wm.machine.verifier
        (by simp [headOf, hchain]) hcan)]
    exact watchVerdict_of_mismatch htok hseen
  rw [← hws]
  simp [PalPeg.PhysicalCacheMachine.prepareRead, htest]

theorem selected_mismatch (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : Running w x p) (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm)
    (a : Fin 3) (htok : PalPeg.GalilScaffoldChainConsume.symbol wm.machine.control.period.focus = some a)
    (hseen : PalPeg.GalilScaffoldInputHead.read
      (PalPeg.GalilScaffoldChainVerifier.right wm.machine.verifier) ≠ some a)
    (hcan : canRight wm.machine.verifier) :
    (PalPeg.PhysicalCacheMachine.activeStep rest).apply blankM p none =
      (countedStep (workStep rest)).apply blankM p none := by
  have htag : p.1.chainTag = .watchers := by
    obtain ⟨T, hT, _⟩ := running_core he
    rw [hT.1.1.chainTag, hchain]
    rfl
  have hentry : PalPeg.PhysicalWatchEntry.entryRead p.1 (fun j => readWin blankM macroRadius (p.2 j)) = false := by
    simp [PalPeg.PhysicalWatchEntry.entryRead, htag]
  rw [PalPeg.PhysicalCacheMachine.activeStep, PalPeg.PhysicalWatchEntry.withWatchEntry, branch_apply, hentry]
  simp only [Bool.false_eq_true, if_false]
  rw [branch_apply, prepareRead_mismatch w x p he wm hchain a htok hseen hcan]
  rfl

theorem mismatch_successor (w : List (Fin 2)) (x : State GalilVM)
    (hmode : x.ctl.mode = .scan) (hs : PalPeg.FrameFunction.starvedTest x = false) (hclock : 1 < x.ctl.clock)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm) (a : Fin 3)
    (htok : PalPeg.GalilScaffoldChainConsume.symbol wm.machine.control.period.focus = some a)
    (hseen : PalPeg.GalilScaffoldInputHead.read
      (PalPeg.GalilScaffoldChainVerifier.right wm.machine.verifier) ≠ some a)
    (hlag : PalPeg.GalilScaffoldCounter.positive wm.lag = true) :
    PalPeg.PhysicalCacheMachine.successor w x = countState (brokenState x wm) := by
  have hrestart : restartGuardTest x.vm = false := by simp [restartGuardTest, hchain]
  have hactive : x.vm.chain ≠ .idle := by simp [hchain]
  rw [PalPeg.PhysicalCacheMachine.successor,
    PalPeg.PhysicalGuardProbe.tickFun_nonstarved_count _ _ 0 1 0 w _ 2048 x hmode hs hrestart hclock]
  change (⟨_, backgroundFun _ x.vm⟩ : State GalilVM) = _
  rw [backgroundFun_of_active _ x.vm hactive, hchain]
  simp only [chainStepFun, if_pos hlag, watchVerdict_of_mismatch htok hseen]
  rfl

theorem forward_count (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : PhysicalState) (he : PalPeg.PhysicalCacheInvariant.Enc w x p)
    (hmode : x.ctl.mode = .scan) (hs : PalPeg.FrameFunction.starvedTest x = false) (hclock : 1 < x.ctl.clock)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm) (a : Fin 3)
    (htok : PalPeg.GalilScaffoldChainConsume.symbol wm.machine.control.period.focus = some a)
    (hseen : PalPeg.GalilScaffoldInputHead.read
      (PalPeg.GalilScaffoldChainVerifier.right wm.machine.verifier) ≠ some a)
    (hlag : PalPeg.GalilScaffoldCounter.positive wm.lag = true) (hcan : canRight wm.machine.verifier) :
    PalPeg.PhysicalCacheInvariant.Enc w (PalPeg.PhysicalCacheMachine.successor w x)
      ((PalPeg.PhysicalCacheMachine.machine rest).apply blankM p none) := by
  have hrestart : restartGuardTest x.vm = false := by simp [restartGuardTest, hchain]
  rw [mismatch_successor w x hmode hs hclock wm hchain a htok hseen hlag]
  rcases p with ⟨q, T⟩
  cases q with
  | inl tag => rw [he.1, initial_starved] at hs; cases hs
  | inr q =>
    rw [PalPeg.PhysicalCacheMachine.machine,
      apply_active (PalPeg.PhysicalCacheMachine.activeStep rest) w x (q, T) (running_core he) hs]
    change Running w (countState (brokenState x wm))
      ((PalPeg.PhysicalCacheMachine.activeStep rest).apply blankM (q, T) none)
    rw [selected_mismatch rest w x (q, T) he wm hchain a htok hseen hcan,
      counted_apply, countRead_running (running_core he) hmode hs hrestart hclock]
    simp only [if_true]
    exact PalPeg.PhysicalCacheMachine.running_clockDown
      (running_mismatch rest w x (q, T) he hmode hs hclock wm hchain a htok hseen hlag hcan)

/-- info: 'PalPeg.PhysicalCountMismatch.forward_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forward_count

end PalPeg.PhysicalCountMismatch
