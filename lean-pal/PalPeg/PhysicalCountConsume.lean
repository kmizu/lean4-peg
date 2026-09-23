import PalPeg.PhysicalCountReady

/-!
# Plain-token consumption in the nonstarved count arm

This uses the existing lag/distance/period actions and the same twelve-slot view
rule as the other branches. Source encoding supplies every window equality;
the legal abstract tick supplies verifier availability. Clock decrement is the
already connected `countedStep`, within the same physical step.
-/
set_option autoImplicit false

namespace PalPeg.PhysicalCountConsume
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract PalPeg.PhysicalBoundary
open PalPeg.PhysicalBootFeed PalPeg.PhysicalTickDispatch PalPeg.PhysicalScanCount
open PalPeg.PhysicalCountReady
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilFinalAssembly2 (centreC placeC)
open PalPeg.GalilScaffoldChainVerifier (canRight)
open PalPeg.Program (STape)
open PalPeg.Local (readWin)
open PalPeg.LocalStepFusion

def caughtState (x : State GalilVM) (wm : PalPeg.GalilScaffoldChainWatch.State) : State GalilVM :=
  ⟨x.ctl, {x.vm with chain := .watch (PalPeg.GalilScaffoldChainWatch.caught wm)}⟩

/-- The physical VM update. There are no assumed window verdicts, sign updates,
or view readiness facts: all are proved below from the source representation. -/
theorem core_consume (rest : RestCommands) (w : List (Fin 2))
    (x : State GalilVM) (p : CoreState) (henc : CoreEnc w x p)
    (hmode : p.1.ctl.mode = .scan)
    (hphase : scanPhase p.1 (fun tape => readWin blankM microRadius (p.2 tape)) ≠ .compare)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm) (a : Fin 3)
    (htok : wm.machine.control.period.focus = .plain a)
    (hseen : PalPeg.GalilScaffoldInputHead.read
      (PalPeg.GalilScaffoldChainVerifier.right wm.machine.verifier) = some a)
    (hforward : wm.machine.control.forward = true)
    (hlag : PalPeg.GalilScaffoldCounter.positive wm.lag = true)
    (hcan : canRight wm.machine.verifier) :
    CoreEnc w (caughtState x wm) (idealRun (workRule rest) blankM p none 12) := by
  generalize hrun : idealRun (workRule rest) blankM p none 12 = result
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
    simpa [chainConsumesTest, htag, htoken, htok, PalPeg.GalilScaffoldChainConsume.symbol] using hpos
  have hverdict : watchVerdict wm = some true := by
    simp [watchVerdict, htok, PalPeg.GalilScaffoldChainConsume.symbol, hseen]
  have htest : watchVerdictTest p.1 ws = watchVerdict wm :=
    watchVerdictTest_eq p.1 ws wm (by rw [htoken])
      (landingLetter_of_encoded henc.1.2 micro_le_margin 3 wm.machine.verifier hx3 hcan)
  have hfwdBit : (scanConsumeNext p.1 ws).chainForward = true := by
    have hqforward : p.1.chainForward = true := by
      rw [henc.1.1.chainForward, hchain]
      exact hforward
    simp [scanConsumeNext, htest, hverdict, htoken, htok,
      PalPeg.GalilScaffoldChainPeriod.isFirst, PalPeg.GalilScaffoldChainConsume.isLast, hqforward]
  have hstep : chainStepFun x.vm.chain = .watch (PalPeg.GalilScaffoldChainWatch.caught wm) := by
    rw [hchain]
    simp only [chainStepFun]
    rw [if_pos hlag, hverdict]
  have hrule : ruleNext 1 0 fppBound_gt_start p.1 ws = scanConsumeNext p.1 ws := by
    unfold ruleNext
    rw [hmode]
    dsimp only
    rw [scanNext_background p.1 ws hbackground, if_pos hconsume]
  have hheadOther : ∀ v : Fin 4, v ≠ 3 → headOf (caughtState x wm) v = headOf x v := by
    intro v hv
    fin_cases v <;> first | rfl | exact (hv rfl).elim
  have hy3 : headOf (caughtState x wm) 3 =
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
  have hencoded : PalPeg.PhysicalEncoding.Enc w margin (caughtState x wm)
      ((idealRun (tickPhysRule 1 0 fppBound_gt_start (by decide : 1 + 3 ≤ microRadius)
        (by decide : 2 ≤ microRadius) rest) blankM (p.1, tapesOf T) none 12).1,
        fun slot => (idealRun (tickPhysRule 1 0 fppBound_gt_start (by decide : 1 + 3 ≤ microRadius)
          (by decide : 2 ≤ microRadius) rest) blankM (p.1, tapesOf T) none 12).2 (slotIndex slot)) := by
    refine enc_afterTickOfState margin 1 0 fppBound_gt_start (by decide) (by decide)
      micro_le_margin rest w x (caughtState x wm) p.1 T none henc.2.1 henc.2.2
      (scanCommands p.1 ws) (fun v => by rw [modeCommands_scan 0 rest p.1 none _ hmode])
      (fun v => if v = 3 ∧ chainConsumesTest p.1 ws then
        PalPeg.GalilScaffoldChainVerifier.right else id)
      (fun v => headOp_scanCommands p.1 ws v hbackground) ?_ ?_ hready henc.1.2 ?_
      (z := stepState (caughtState x wm) wm.machine.verifier)
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
      have hc := encControl_scanConsume x p.1 T wm henc.1.1 hconsume htest hverdict htoken
        hchain hlag
      simpa only [hstep, caughtState] using hc
    · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hgap, hmicro, hfl, hdl⟩ :=
        scanConsumeNext_untouched p.1 ws
      rw [hrule, hgap, hmicro, hfl, hdl]
      exact physRule_scan_consume margin 1 0 fppBound_gt_start (by decide) (by decide)
        micro_le_margin (by decide) x p.1 T hmode hbackground hconsume
        (by rw [htest, hverdict]) hfwdBit wm hchain a htok hseen hforward henc.1.2
  constructor
  · simpa only [← workRule_eq, hT, Prod.eta, hrun] using hencoded
  · have hb := macroBoundary_tickRule
      (fun q _ ws => ruleNext 1 0 fppBound_gt_start q ws) (modeCommands 0 rest)
      (fun q _ ws => ruleActs 1 0 q ws)
      (fun q _ ws j => ruleActs_length 1 0 (by decide : 1 + 3 ≤ microRadius) q ws j)
      w x p none henc
    simpa only [← tickPhysRule_eq 1 0 fppBound_gt_start (by decide) (by decide) rest,
      ← workRule_eq, hrun] using hb

/-- The same consuming rule, transported to the real sweep closure. -/
theorem running_consume (rest : RestCommands) (w : List (Fin 2))
    (x : State GalilVM) (p : CoreState)
    (henc : PalPeg.MachineStep.sweepClosure blankM (CoreEnc w) x p)
    (hmode : x.ctl.mode = .scan) (hstarved : PalPeg.FrameFunction.starvedTest x = false)
    (hclock : 1 < x.ctl.clock)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm) (a : Fin 3)
    (htok : wm.machine.control.period.focus = .plain a)
    (hseen : PalPeg.GalilScaffoldInputHead.read
      (PalPeg.GalilScaffoldChainVerifier.right wm.machine.verifier) = some a)
    (hforward : wm.machine.control.forward = true)
    (hlag : PalPeg.GalilScaffoldCounter.positive wm.lag = true)
    (hcan : canRight wm.machine.verifier) :
    PalPeg.MachineStep.sweepClosure blankM (CoreEnc w) (caughtState x wm)
      ((workStep rest).apply blankM p none) := by
  have hrestart : restartGuardTest x.vm = false := by simp [restartGuardTest, hchain]
  apply running_fused_step (workRule rest) w x (caughtState x wm) p none henc
  intro T hT
  have hqmode := congrArg PalPeg.GalilScaffoldController.Control.mode hT.1.1.ctl
  change p.1.ctl.mode = x.ctl.mode at hqmode
  have hcount := countRead_eq hT.1 (by decide : 1 ≤ microRadius) micro_le_margin
    hmode hstarved hrestart hclock
  have hphase : scanPhase p.1
      (fun tape => readWin blankM microRadius (tapesOf (fun slot => T (slotIndex slot)) tape))
        = .count := of_decide_eq_true (Bool.and_eq_true_iff.mp hcount).2
  have hphaseT : scanPhase p.1 (fun tape => readWin blankM microRadius (T tape)) = .count := by
    simpa only [tapesOf, Equiv.apply_symm_apply] using hphase
  exact core_consume rest w x (p.1, T) hT (hqmode.trans hmode)
    (by rw [hphaseT]; decide) wm hchain a htok hseen hforward hlag hcan

/-- A nonstarved count step consumes a matching plain token in the forward
period direction. Its only extra premise is the actual legal abstract tick that
the final consumer already supplies; every local reading and head side condition
has been discharged. -/
theorem forward_count_plain (rest : RestCommands) (w : List (Fin 2))
    (x : State GalilVM) (p : PhysicalState)
    (henc : PalPeg.PhysicalContract.Enc w x p)
    (hmode : x.ctl.mode = .scan) (hstarved : PalPeg.FrameFunction.starvedTest x = false)
    (hclock : 1 < x.ctl.clock) {y : State GalilVM}
    (htick : Tick (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x y)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm) (a : Fin 3)
    (htok : wm.machine.control.period.focus = .plain a)
    (hseen : PalPeg.GalilScaffoldInputHead.read
      (PalPeg.GalilScaffoldChainVerifier.right wm.machine.verifier) = some a)
    (hforward : wm.machine.control.forward = true)
    (hlag : PalPeg.GalilScaffoldCounter.positive wm.lag = true) :
    PalPeg.PhysicalContract.Enc w
      (tickFun (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w)
        (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x)
      ((scanMachine rest).apply blankM p none) := by
  have hcan := verifier_canRight_of_countTick w htick hmode hclock wm hchain hlag
  have hrestart : restartGuardTest x.vm = false := by simp [restartGuardTest, hchain]
  have hactive : x.vm.chain ≠ .idle := by rw [hchain]; exact fun h => ChainVM.noConfusion h
  have hverdict : watchVerdict wm = some true := by
    simp [watchVerdict, htok, PalPeg.GalilScaffoldChainConsume.symbol, hseen]
  have hstep : chainStepFun x.vm.chain = .watch (PalPeg.GalilScaffoldChainWatch.caught wm) := by
    rw [hchain]
    simp only [chainStepFun]
    rw [if_pos hlag, hverdict]
  have htickFun : tickFun (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w)
      (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x =
        countState (caughtState x wm) := by
    rw [PalPeg.PhysicalGuardProbe.tickFun_nonstarved_count centreC placeC 0 1 0 w _ 2048 x
      hmode hstarved hrestart hclock]
    change (⟨_, backgroundFun _ x.vm⟩ : State GalilVM) = _
    rw [backgroundFun_of_active _ x.vm hactive, hstep]
    rfl
  rw [htickFun]
  rcases p with ⟨q, T⟩
  cases q with
  | inl bootTag =>
    rw [henc.1, initial_starved] at hstarved
    cases hstarved
  | inr control =>
    rw [scanMachine, apply_active (countedStep (workStep rest)) w x (control, T) henc hstarved,
      enc_running, counted_apply, countRead_running henc hmode hstarved hrestart hclock]
    simp only [if_true]
    exact running_clockDown (running_consume rest w x (control, T) henc hmode hstarved hclock
      wm hchain a htok hseen hforward hlag hcan)

/-- The source case handled by the theorem above. Reverse-direction, mismatch,
and block-boundary cases remain explicitly outside this predicate. -/
def CountPlainMatch (x : State GalilVM) : Prop :=
  x.ctl.mode = .scan ∧ 1 < x.ctl.clock ∧
    ∃ (wm : PalPeg.GalilScaffoldChainWatch.State) (a : Fin 3), x.vm.chain = .watch wm ∧
      wm.machine.control.period.focus = .plain a ∧
      PalPeg.GalilScaffoldInputHead.read
        (PalPeg.GalilScaffoldChainVerifier.right wm.machine.verifier) = some a ∧
      wm.machine.control.forward = true ∧ PalPeg.GalilScaffoldCounter.positive wm.lag = true

open PalPeg.CloseoutCheckW (PreTraceIMW CanonTrace)
open PalPeg.LocalSysConcrete (absSC)
open PalPeg.LocalReplayParked (Mirrored1)
open PalPeg.LocalShadowConcrete (OnRun)
open PalPeg.LocalBlankState (tapeCount)
open PalPeg.ShadowedLocalFinal (localGood postPhase frozenAt heldAfter)

/-- The same final tick contract now removes the plain-consumption case from
its active remainder too. All OnRun, trace and legal-Tick information is kept. -/
theorem cases_of_remaining (rest : RestCommands)
    (hother : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC 0 1 0 w st Tc → CanonTrace 0 w st Tc →
      ∀ (m : Mirrored1 (tapeCount 0)) (p : PhysicalState),
        PalPeg.LocalShadowConcrete.ArrivedOnRun (localGood (spare := 0)) (postPhase 0 1 0) w (heldAfter (Tc w.length) st) m →
        ¬ frozenAt w m → PalPeg.PhysicalContract.Enc w (absSC m) p →
        PalPeg.FrameFunction.starvedTest (absSC m) = false →
        Tick (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 (absSC m)
          (tickFun (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w)
            (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 (absSC m)) →
        ¬ CountAtRest (absSC m) → ¬ CountPlainMatch (absSC m) →
        PalPeg.PhysicalContract.Enc w
          (tickFun (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w)
            (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 (absSC m))
          ((scanMachine rest).apply blankM p none)) :
    TickCases (scanMachine rest) blankM PalPeg.PhysicalContract.Enc := by
  apply PalPeg.PhysicalScanCount.cases_of_remaining rest
  intro w st Tc hpre hcanon m p hon hnotFrozen henc hstarved htick hnotRest
  by_cases hplain : CountPlainMatch (absSC m)
  · obtain ⟨hmode, hclock, wm, a, hchain, htok, hseen, hforward, hlag⟩ := hplain
    exact forward_count_plain rest w (absSC m) p henc hmode hstarved hclock htick
      wm hchain a htok hseen hforward hlag
  · exact hother w st Tc hpre hcanon m p hon hnotFrozen henc hstarved htick hnotRest hplain

/-- info: 'PalPeg.PhysicalCountConsume.forward_count_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forward_count_plain

/-- info: 'PalPeg.PhysicalCountConsume.cases_of_remaining' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cases_of_remaining

end PalPeg.PhysicalCountConsume
