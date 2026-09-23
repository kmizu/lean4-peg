import PalPeg.PhysicalConsumeStage
import PalPeg.PhysicalCacheInvariant

/-!
# Selecting shift after the comparison's internal chain step

The shift guard observes the chain after Internal, while its right-hand letter
is the comparison cursor's landing. Both observations come from the same source
windows. Boundary snapshots need not yet be renamed: the guard does not read
those counters.
-/
set_option autoImplicit false
namespace PalPeg.PhysicalCompareGuard
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract PalPeg.PhysicalConsumeStage
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilScaffoldCounter (Counter zero dec positive singlePositive)
open PalPeg.GalilScaffoldChainWatch (caught)
open PalPeg.GalilScaffoldChainVerifier (right canRight)
open PalPeg.GalilScaffoldInputHead (read left)
open PalPeg.Program (STape)
open PalPeg.Local (readWin)
open PalPeg.CloseoutCoreEnc12 PalPeg.LocalStepFusion

theorem singlePositiveRead_eq {K : ℕ} (x : State GalilVM) (q : CoreControl) (T : Slot → STape Γm)
    (he : EncTapes margin x q.polarity q.gap q.micro q.fppLive q.dpLive T)
    (hK : 2 ≤ K) (hmargin : K ≤ margin) (c : Fin 16) (value : Counter)
    (hc : counterOf x c = some value) :
    singlePositiveRead q (fun j => readWin blankM K (tapesOf T j)) c = singlePositive value := by
  let ws := fun j => readWin blankM K (tapesOf T j)
  obtain ⟨seg, ha, ht⟩ := he.counters c value hc
  obtain ⟨result, hresult, hresultTape⟩ := counter_dec_at q.polarity c
    (decSignAt (q.polarity c) (counterSlot c) ws) seg value ha
    (decSignAt_eq (by omega) (by omega) (q.polarity c) c T seg ht) (T (counterSlot c)) ht
  change actList blankM (T (counterSlot c)) [decAct q c ws]
    = padLeft margin (mapTape encSeg result) at hresultTape
  have hw : windowAfter K 1 (ws (slotIndex (counterSlot c))) [decAct q c ws]
      = readWin blankM 1 (padLeft margin (mapTape encSeg result)) := by
    dsimp only [ws]
    rw [tapesOf_apply, windowAfter_readWin blankM _ _ (by simp; omega)
      (hmargin.trans (he.margins _))]
    exact congrArg (readWin blankM 1) hresultTape
  have hz : decide ((windowAfter K 1 (ws (slotIndex (counterSlot c))) [decAct q c ws]) 0
      ≠ encSeg PalPeg.LocalCounter.mark) = zero (dec value) := by
    rw [hw, ← hresult, PalPeg.LocalCounter.zero_iff, Bool.eq_iff_iff]
    simp only [decide_eq_true_eq]
    simpa using (counterZero_iff_below (K := 1) (margin := margin) (by decide) (by decide) result).symm
  unfold singlePositiveRead
  rw [show decide ((windowAfter K 1 (ws (slotIndex (counterSlot c))) [decAct q c ws]) 0
      ≠ encSeg PalPeg.LocalCounter.mark) = zero (dec value) from hz,
    counterPositiveTest_eq he (by omega) hmargin c value hc]
  have hcanonical : PalPeg.GalilScaffoldCounter.Canonical value := by
    rw [← ha]
    exact PalPeg.LocalCounter.absCtr_canonical _ _
  rw [Bool.eq_iff_iff, Bool.and_eq_true,
    PalPeg.GalilScaffoldCounter.singlePositive_iff value hcanonical,
    PalPeg.GalilScaffoldCounter.positive_iff value hcanonical,
    PalPeg.GalilScaffoldCounter.zero_iff (dec value)
      (PalPeg.GalilScaffoldCounter.dec_canonical value hcanonical)]
  simp only [PalPeg.GalilScaffoldCounter.dec_value]
  omega

theorem shiftRead_eq {K : ℕ} (w : List (Fin 2)) (x : State GalilVM) (q : CoreControl)
    (T : Slot → STape Γm) (he : PalPeg.PhysicalEncoding.Enc w margin x (q,T))
    (hK : 2 ≤ K) (hmargin : K ≤ margin) (head : PalPeg.GalilScaffoldInputHead.PlaceHead) :
    shiftRead q (fun j => readWin blankM K (tapesOf T j)) (read head)
      = shiftGuardTest {x.vm with right := head} := by
  unfold shiftRead
  rw [he.1.chainTag, he.1.periodOnly]
  cases hchain : x.vm.chain with
  | watch wm =>
    have hphase : q.chainPhase = wm.machine.control.phase := by
      simpa only [hchain, chainConsumeOf] using he.1.chainPhase
    have hbroken : q.chainBroken = wm.machine.control.broken := by
      simpa only [hchain, chainConsumeOf] using he.1.chainBroken
    rw [hphase, hbroken,
      counterZeroTest_eq he.2 (by omega) hmargin 11 wm.lag (by simp [counterOf,hchain]),
      counterNegativeTest_eq he.2 (by omega) hmargin 12 wm.margin (by simp [counterOf,hchain]),
      singlePositiveRead_eq x q T he.2 hK hmargin 0 x.vm.cycle rfl,
      symbol_centreRead_periodSlot he.2 hmargin wm.machine.control.period (by simp [periodOf,hchain])]
    simp [shiftGuardTest,hchain,chainTagOf]
  | idle | copy | back | broken => simp [shiftGuardTest,hchain,chainTagOf]

noncomputable def internalTapes (q : CoreControl) (T : Slot → STape Γm) : Slot → STape Γm :=
  fun slot => actList blankM (T slot) (withErase q.fppLive
    (fun j => readWin blankM microRadius (tapesOf T j))
    (scanConsumeActs q (fun j => readWin blankM microRadius (tapesOf T j))) (slotIndex slot))

theorem internalWindows_eq (q : CoreControl) (T : Slot → STape Γm)
    (hm : ∀ slot, microRadius ≤ PalPeg.Local.pos (T slot)) :
    internalWindows q (fun j => readWin blankM microRadius (tapesOf T j))
      = fun j => readWin blankM 2 (tapesOf (internalTapes q T) j) := by
  funext j
  unfold internalWindows
  rw [windowAfter_readWin blankM (tapesOf T j) _
    (by
      have hlen := withErase_length (b := 1) (bound := 2) (by decide) q.fppLive
        (fun k => readWin blankM microRadius (tapesOf T k))
        (scanConsumeActs q (fun k => readWin blankM microRadius (tapesOf T k)))
        (fun k => scanConsumeActs_length q _ k) j
      have hk : 4 ≤ microRadius := by decide
      omega)
    (hm (slotIndex.symm j))]
  simp only [tapesOf, internalTapes, Equiv.apply_symm_apply]

/-- With an active watch, mismatching changes radius and the two comparison
cursors; the chain performs Internal once and the search stays idle. -/
theorem compare_mismatch (P : Shared) (s : GalilVM) (wm : PalPeg.GalilScaffoldChainWatch.State)
    (hchain : s.chain = .watch wm) (hne : read (left s.left) ≠ read (right s.right)) :
    compareFun P s = afterMismatch s ⟨left s.left, right s.right, chainStepFun s.chain⟩
      (searchLens.get s) := by
  have hactive : s.chain ≠ ChainVM.idle := by rw [hchain]; intro h; cases h
  unfold compareFun
  simp only [decide_eq_false hne, Bool.false_eq_true, if_false]
  rw [afterBirth_of_ne_idle (s := s) hactive]
  have hsearch : searchEffectFun P false s = searchLens.get s := by
    simp only [searchEffectFun,hchain]
  rw [hsearch,hchain]
  simp only [chainAtFun,chainTickFun,Bool.false_eq_true,if_false]

/-- These intermediate changes are invisible to the finite control fields. -/
theorem stagedControl {fb db : ℕ} {w : List (Fin 2)} {x : State GalilVM}
    {q : QPhys fb db} {wm : PalPeg.GalilScaffoldChainWatch.State}
    (hc : EncControl w (PalPeg.PhysicalCountConsume.caughtState x wm) q) :
    EncControl w (stepState (stagedState x wm) wm.machine.verifier) q :=
  ⟨hc.ctl,hc.chainTag,hc.chainPhase,hc.chainForward,hc.chainBroken,
    hc.fppMode,hc.fppFinalStage,hc.fppPc,hc.fppDone,hc.dpPc,hc.dpDone,
    hc.searchMode,hc.searchFinalStage,hc.searchQuarter,hc.periodOnly,
    hc.placeGap,hc.onLetter,hc.leftFirst⟩

/-- The guard reads after a successful Internal consume in either direction,
including FIRST/LAST. The staged boundary snapshots do not enter this test. -/
theorem scanShiftRead_consumed (P : Shared) (w : List (Fin 2)) (x : State GalilVM)
    (q : CoreControl) (T : Slot → STape Γm)
    (he : PalPeg.PhysicalEncoding.Enc w margin x (q,T))
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm)
    (a : Fin 3) (htok : PalPeg.GalilScaffoldChainConsume.symbol wm.machine.control.period.focus = some a)
    (hseen : read (right wm.machine.verifier) = some a)
    (hlag : positive wm.lag = true) (hcanVer : canRight wm.machine.verifier)
    (hleft : (caught wm).machine.control.forward = false → wm.machine.control.period.left ≠ [])
    (hcanRight : canRight x.vm.right) (hne : read (left x.vm.left) ≠ read (right x.vm.right)) :
    scanShiftRead q (fun j => readWin blankM microRadius (tapesOf T j))
      = shiftGuardTest (compareFun P x.vm) := by
  let ws := fun j => readWin blankM microRadius (tapesOf T j)
  let nextQ := scanConsumeNext q ws
  let z := stepState (stagedState x wm) wm.machine.verifier
  have htoken : decToken (centreRead ws periodSlot) = wm.machine.control.period.focus := by
    rw [centreRead_periodSlot he.2 micro_le_margin wm.machine.control.period
      (by simp [periodOf,hchain]),decToken_encToken]
    rfl
  have htag : q.chainTag = .watchers := by rw [he.1.chainTag,hchain]; rfl
  have hpos := (counterPositive_iff_belowRead he.2 (by decide : 1 ≤ microRadius) micro_le_margin
    11 wm.lag (by simp [counterOf,hchain])).mp hlag
  have hconsume : chainConsumesTest q ws = true := by
    simpa [chainConsumesTest,htag,htoken,htok] using hpos
  have hverdict : watchVerdict wm = some true := by simp [watchVerdict,htok,hseen]
  have htest : watchVerdictTest q ws = watchVerdict wm :=
    watchVerdictTest_eq q ws wm (by rw [htoken])
      (landingLetter_of_encoded he.2 micro_le_margin 3 wm.machine.verifier
        (by simp [headOf,hchain]) hcanVer)
  have hmatch : watchVerdictTest q ws = some true := htest.trans hverdict
  have hstep : chainStepFun x.vm.chain = .watch (caught wm) := by
    simp [hchain,chainStepFun,hlag,hverdict]
  have hcontrol : EncControl w (PalPeg.PhysicalCountConsume.caughtState x wm) nextQ := by
    have hc := encControl_scanConsume x q T wm he.1 hconsume htest hverdict htoken hchain hlag
    simpa only [hstep, nextQ, ws, PalPeg.PhysicalCountConsume.caughtState] using hc
  have hforward : nextQ.chainForward = (caught wm).machine.control.forward :=
    hcontrol.chainForward
  have hzt : EncTapes margin z nextQ.polarity nextQ.gap nextQ.micro nextQ.fppLive nextQ.dpLive
      (internalTapes q T) := by
    have ht := stagedTapes x q T hconsume hmatch wm hchain a htok hseen hforward hleft he.2
    change EncTapes margin z nextQ.polarity q.gap q.micro q.fppLive q.dpLive (internalTapes q T) at ht
    have hgap : nextQ.gap = q.gap := by simp only [nextQ,scanConsumeNext,hmatch]
    have hm : nextQ.micro = q.micro := by simp only [nextQ,scanConsumeNext,hmatch]
    have hf : nextQ.fppLive = q.fppLive := by simp only [nextQ,scanConsumeNext,hmatch]
    have hd : nextQ.dpLive = q.dpLive := by simp only [nextQ,scanConsumeNext,hmatch]
    rw [hgap,hm,hf,hd]
    exact ht
  have hzc : EncControl w z nextQ := stagedControl hcontrol
  have hcontrolRead : internalControl q ws = nextQ := by
    simp only [internalControl,hconsume,if_true]
    rfl
  have hguard : shiftGuardTest {z.vm with right := right x.vm.right} =
      shiftGuardTest (compareFun P x.vm) := by
    rw [compare_mismatch P x.vm wm hchain hne,hstep]
    rfl
  generalize hq : nextQ = outputQ at hzt hzc hcontrolRead
  generalize hz : z = state at hzt hzc hguard
  unfold scanShiftRead
  rw [hcontrolRead,
    internalWindows_eq q T (fun slot => micro_le_margin.trans (he.2.margins slot)),
    landingLetter_of_encoded he.2 micro_le_margin 2 x.vm.right rfl hcanRight]
  exact (shiftRead_eq w state outputQ (internalTapes q T) ⟨hzc,hzt⟩
    (by decide) (by decide) (right x.vm.right)).trans hguard

theorem internalTapes_still (x : State GalilVM) (q : CoreControl) (T : Slot → STape Γm)
    (he : EncTapes margin x q.polarity q.gap q.micro q.fppLive q.dpLive T)
    (hno : chainConsumesTest q (fun j => readWin blankM microRadius (tapesOf T j)) = false) :
    EncTapes margin x q.polarity q.gap q.micro q.fppLive q.dpLive (internalTapes q T) := by
  apply encTapes_idleOnly margin x q.polarity q.gap q.micro q.fppLive q.dpLive T _ he
  · intro slot hidle
    unfold internalTapes
    rw [withErase_at_other q.fppLive _ _ slot hidle]
    simp [scanConsumeActs,hno]
  · exact idle_shape_withErase margin (by decide) (by decide) T q.fppLive _
      (fun k => by simp [scanConsumeActs,hno]) he.idleShape

theorem scanShiftRead_still (P : Shared) (w : List (Fin 2)) (x : State GalilVM)
    (q : CoreControl) (T : Slot → STape Γm)
    (he : PalPeg.PhysicalEncoding.Enc w margin x (q,T))
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm)
    (hno : chainConsumesTest q (fun j => readWin blankM microRadius (tapesOf T j)) = false)
    (hstep : chainStepFun x.vm.chain = x.vm.chain)
    (hcanRight : canRight x.vm.right) (hne : read (left x.vm.left) ≠ read (right x.vm.right)) :
    scanShiftRead q (fun j => readWin blankM microRadius (tapesOf T j))
      = shiftGuardTest (compareFun P x.vm) := by
  unfold scanShiftRead
  rw [show internalControl q (fun j => readWin blankM microRadius (tapesOf T j)) = q from
      by simp only [internalControl,hno,Bool.false_eq_true,if_false],
    internalWindows_eq q T (fun slot => micro_le_margin.trans (he.2.margins slot)),
    landingLetter_of_encoded he.2 micro_le_margin 2 x.vm.right rfl hcanRight,
    shiftRead_eq w x q (internalTapes q T) ⟨he.1,internalTapes_still x q T he.2 hno⟩
      (by decide) (by decide) (right x.vm.right),
    compare_mismatch P x.vm wm hchain hne,hstep]
  rfl

/-- All Internal verdicts of a watching source use the same reader. -/
theorem scanShiftRead_watch (P : Shared) (w : List (Fin 2)) (x : State GalilVM)
    (q : CoreControl) (T : Slot → STape Γm)
    (he : PalPeg.PhysicalEncoding.Enc w margin x (q,T))
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm)
    (a : Fin 3) (htok : PalPeg.GalilScaffoldChainConsume.symbol wm.machine.control.period.focus = some a)
    (hcanVer : positive wm.lag = true → canRight wm.machine.verifier)
    (hleft : read (right wm.machine.verifier) = some a →
      (caught wm).machine.control.forward = false → wm.machine.control.period.left ≠ [])
    (hcanRight : canRight x.vm.right) (hne : read (left x.vm.left) ≠ read (right x.vm.right)) :
    scanShiftRead q (fun j => readWin blankM microRadius (tapesOf T j))
      = shiftGuardTest (compareFun P x.vm) := by
  let ws := fun j => readWin blankM microRadius (tapesOf T j)
  have htoken : decToken (centreRead ws periodSlot) = wm.machine.control.period.focus := by
    rw [centreRead_periodSlot he.2 micro_le_margin wm.machine.control.period
      (by simp [periodOf,hchain]),decToken_encToken]
    rfl
  have htag : q.chainTag = .watchers := by rw [he.1.chainTag,hchain]; rfl
  have hconsume : chainConsumesTest q ws = positive wm.lag := by
    simp only [chainConsumesTest,htag,decide_true,Bool.true_and,htoken,htok,
      Option.isSome_some,Bool.and_true]
    simpa [counterPositiveTest,counterZeroTest] using
      counterPositiveTest_eq he.2 (by decide : 1 ≤ microRadius) micro_le_margin 11 wm.lag
        (by simp [counterOf,hchain])
  cases hp : positive wm.lag with
  | false =>
    exact scanShiftRead_still P w x q T he wm hchain (hconsume.trans hp)
      (by simp [chainStepFun,hchain,hp]) hcanRight hne
  | true =>
    by_cases hseen : read (right wm.machine.verifier) = some a
    · exact scanShiftRead_consumed P w x q T he wm hchain a htok hseen hp (hcanVer hp)
        (hleft hseen) hcanRight hne
    · have hverdict : watchVerdict wm = some false := by simp [watchVerdict,htok,hseen]
      have htest : watchVerdictTest q ws = some false :=
        (watchVerdictTest_eq q ws wm (by rw [htoken])
          (landingLetter_of_encoded he.2 micro_le_margin 3 wm.machine.verifier
            (by simp [headOf,hchain]) (hcanVer hp))).trans hverdict
      have hcontrol : internalControl q ws = {q with chainTag := .broken} := by
        rw [internalControl,if_pos (hconsume.trans hp)]
        simp only [scanConsumeNext,htest]
      unfold scanShiftRead
      rw [hcontrol,compare_mismatch P x.vm wm hchain hne]
      simp [shiftRead,shiftGuardTest,afterMismatch,scanLens,searchLens,chainStepFun,hchain,hp,hverdict]

/-- A legal comparison supplies verifier availability when Internal consumes. -/
theorem verifier_ready_of_compare (P : Shared) (q : ℕ) (first : Fin 9)
    {s t : GalilVM} (hc : (galilFrameS P q first).compare s t)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : s.chain = .watch wm)
    (hlag : positive wm.lag = true) : canRight wm.machine.verifier := by
  obtain ⟨vs,vq,a,_,_,_,_,hch,_⟩ : compareFound P q first s t := hc
  rcases hch with ⟨_,mid,hstep,_⟩ | ⟨hi,_⟩ | ⟨hi,_⟩
  · rw [hchain] at hstep
    cases hstep with
    | watchStep _ _ hstep =>
      cases hstep with
      | idle hz => simp [hlag] at hz
      | take _ hg => exact hg.1
    | watchBreak _ hb => exact hb.2.1
  · rw [hchain] at hi
    cases hi
  · rw [hchain] at hi
    cases hi

/-- The source condition is furnished by the Tick already received by the
final dispatcher; it is not an additional reachability obligation. -/
theorem verifier_ready_of_scanTick (w : List (Fin 2)) {x y : State GalilVM}
    (htick : Tick (galilFrameS (PalPeg.GalilRunSkeleton.PofC
      PalPeg.GalilFinalAssembly2.centreC PalPeg.GalilFinalAssembly2.placeC 0 w) 1 0) 2048 x y)
    (hmode : x.ctl.mode = .scan)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm)
    (hlag : positive wm.lag = true) : canRight wm.machine.verifier := by
  cases htick <;> simp_all
  all_goals first
    | exact PalPeg.PhysicalCountReady.verifier_canRight_of_background _ 1 0 ‹_› wm hchain hlag
    | exact verifier_ready_of_compare _ 1 0 ‹_› wm hchain hlag
    | skip
  case restart c s t hm hb =>
    change restartVM 0 s t at hb
    obtain ⟨wm',hbroken,_⟩ := hb
    rw [hchain] at hbroken
    cases hbroken

/-- From the actual swept source, cache and legal tick supply every condition
of the post-comparison reader, including both boundary directions. -/
theorem scanShiftRead_running_ready (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : PalPeg.PhysicalCacheInvariant.Running w x p)
    (hmode : x.ctl.mode = .scan) (hs : PalPeg.FrameFunction.starvedTest x = false)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm)
    (hready : positive wm.lag = true → canRight wm.machine.verifier)
    (hne : read (left x.vm.left) ≠ read (right x.vm.right)) :
    scanShiftRead p.1 (fun j => readWin blankM microRadius (p.2 j)) =
      shiftGuardTest (compareFun (PalPeg.GalilRunSkeleton.PofC
        PalPeg.GalilFinalAssembly2.centreC PalPeg.GalilFinalAssembly2.placeC 0 w) x.vm) := by
  have hcan : canRight x.vm.right := by
    apply (canRightTest_iff _).mpr
    simpa [PalPeg.FrameFunction.starvedTest,PalPeg.FrameFunction.starvedOf,hmode] using hs
  have hc := PalPeg.PhysicalCacheInvariant.running_cache he
  rw [PalPeg.PhysicalCacheInvariant.Cache,hchain] at hc
  obtain ⟨h,age,spare,hi,_,_⟩ := hc
  have hsym : ∃ a, PalPeg.GalilScaffoldChainConsume.symbol wm.machine.control.period.focus = some a := by
    obtain ⟨passed,future,first,last,_,_,hshape⟩ := hi.cursor
    cases hfwd : wm.machine.control.forward <;> simp only [hfwd,Bool.false_eq_true,if_false,if_true] at hshape
    all_goals
      cases future with
      | nil =>
        have hf := (List.cons.inj (by simpa using hshape.2)).1
        simp [hf,PalPeg.GalilScaffoldChainConsume.symbol]
      | cons a rest =>
        have hf := (List.cons.inj (by simpa using hshape.2)).1
        exact ⟨a,by simp [hf,PalPeg.GalilScaffoldChainConsume.symbol]⟩
  obtain ⟨a,htok⟩ := hsym
  apply PalPeg.PhysicalTickDispatch.read_from_running scanShiftRead _ w x p
    (PalPeg.PhysicalCacheInvariant.running_core he)
  intro T hT
  have htapes : tapesOf (fun slot => T (slotIndex slot)) = T := by
    funext j
    simp [tapesOf]
  have hread := scanShiftRead_watch (PalPeg.GalilRunSkeleton.PofC
    PalPeg.GalilFinalAssembly2.centreC PalPeg.GalilFinalAssembly2.placeC 0 w) w x p.1 (fun slot => T (slotIndex slot)) hT.1 wm hchain a htok
    hready
    (fun hseen => cursor_left hi.cursor a htok hseen) hcan hne
  simpa only [htapes] using hread


theorem scanShiftRead_running (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : PalPeg.PhysicalCacheInvariant.Running w x p)
    (hmode : x.ctl.mode = .scan) (hs : PalPeg.FrameFunction.starvedTest x = false)
    {y : State GalilVM}
    (htick : Tick (galilFrameS (PalPeg.GalilRunSkeleton.PofC
      PalPeg.GalilFinalAssembly2.centreC PalPeg.GalilFinalAssembly2.placeC 0 w) 1 0) 2048 x y)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm)
    (hne : read (left x.vm.left) ≠ read (right x.vm.right)) :
    scanShiftRead p.1 (fun j => readWin blankM microRadius (p.2 j)) =
      shiftGuardTest (compareFun (PalPeg.GalilRunSkeleton.PofC
        PalPeg.GalilFinalAssembly2.centreC PalPeg.GalilFinalAssembly2.placeC 0 w) x.vm) :=
  scanShiftRead_running_ready w x p he hmode hs wm hchain
    (verifier_ready_of_scanTick w htick hmode wm hchain) hne

/-- The real command table now issues the entry's extra half-cell motion.
Internal may already have moved once, so the emitted command is either one
half-cell or the existing whole-cell command. No simulated guard is assumed. -/
theorem modeCommands_shift_verifier (rest : PalPeg.PhysicalScanCount.RestCommands)
    (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : PalPeg.PhysicalCacheInvariant.Running w x p)
    (hmode : x.ctl.mode = .scan) (hs : PalPeg.FrameFunction.starvedTest x = false)
    (hclock : x.ctl.clock ≤ 1) {y : State GalilVM}
    (htick : Tick (galilFrameS (PalPeg.GalilRunSkeleton.PofC
      PalPeg.GalilFinalAssembly2.centreC PalPeg.GalilFinalAssembly2.placeC 0 w) 1 0) 2048 x y)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm)
    (hne : read (left x.vm.left) ≠ read (right x.vm.right))
    (hshift : shiftGuardTest (compareFun (PalPeg.GalilRunSkeleton.PofC
      PalPeg.GalilFinalAssembly2.centreC PalPeg.GalilFinalAssembly2.placeC 0 w) x.vm) = true) :
    modeCommands 0 rest p.1 none (fun j => readWin blankM microRadius (p.2 j)) 3 =
      if chainConsumesTest p.1 (fun j => readWin blankM microRadius (p.2 j))
        then .stepRight else .moveRight := by
  have hav : canRightTest x.vm.right = true := by
    simpa [PalPeg.FrameFunction.starvedTest,PalPeg.FrameFunction.starvedOf,hmode] using hs
  have hsource : p.1.ctl.mode = .scan ∧
      scanPhase p.1 (fun j => readWin blankM microRadius (p.2 j)) = .compare ∧
      agreeTest p.1 (fun j => readWin blankM microRadius (p.2 j)) = false := by
    obtain ⟨T,hT,hteq⟩ := PalPeg.PhysicalCacheInvariant.running_core he
    have hw : (fun j => readWin blankM microRadius (p.2 j)) =
        (fun j => readWin blankM microRadius (T j)) := by
      funext j
      exact (readWin_congr_teqG (hteq j)).symm
    rw [hw]
    let U := fun slot => T (slotIndex slot)
    have hU : tapesOf U = T := by funext j; simp [tapesOf,U]
    rw [← hU]
    refine ⟨?_,?_,?_⟩
    · have hm := congrArg PalPeg.GalilScaffoldController.Control.mode hT.1.1.ctl
      exact hm.trans hmode
    · rw [scanPhase_eq hT.1 (by decide : 1 ≤ microRadius) micro_le_margin]
      simp [scanPhaseOf,restartGuardTest,hchain,hav,show ¬ 1 < x.ctl.clock by omega]
    · rw [agreeTest_of_encoded hT.1.2 (by decide : 1 ≤ microRadius) micro_le_margin
        ((canRightTest_iff _).mpr hav)]
      exact decide_eq_false hne
  rw [modeCommands_scan 0 rest p.1 none _ hsource.1,
    scanCommands_compare_verifier p.1 _ hsource.2.1,hsource.2.2,if_neg Bool.false_ne_true,
    scanShiftRead_running w x p he hmode hs htick wm hchain hne,hshift]
  cases chainConsumesTest p.1 (fun j => readWin blankM microRadius (p.2 j)) <;> rfl

/-- info: 'PalPeg.PhysicalCompareGuard.modeCommands_shift_verifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms modeCommands_shift_verifier

/-- info: 'PalPeg.PhysicalCompareGuard.shiftRead_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms shiftRead_eq

/-- info: 'PalPeg.PhysicalCompareGuard.scanShiftRead_running' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms scanShiftRead_running

end PalPeg.PhysicalCompareGuard
