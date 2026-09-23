import PalPeg.PhysicalTickDispatch

/-!
# The nonstarved count arm

The existing twelve-slot rule performs the background VM work. The same local
step updates the bounded controller clock at its exit, using the source window
to select count. This adds no physical tick and leaves every tape action intact.
-/
set_option autoImplicit false

namespace PalPeg.PhysicalScanCount
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract PalPeg.PhysicalBoundary
open PalPeg.PhysicalBootFeed PalPeg.PhysicalTickDispatch
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilFinalAssembly2 (centreC placeC)
open PalPeg.Program (STape)
open PalPeg.Local (LocalStep readWin)
open PalPeg.LocalStepFusion
open PalPeg.CloseoutCoreEnc12 (compStep)

def clockDown (q : CoreControl) : CoreControl :=
  {q with ctl := {q.ctl with clock := ⟨q.ctl.clock.val - 1,
    lt_of_le_of_lt (Nat.sub_le _ _) q.ctl.clock.isLt⟩}}

def countState (x : State GalilVM) : State GalilVM :=
  ⟨{x.ctl with clock := x.ctl.clock - 1}, x.vm⟩

theorem encControl_clockDown {w : List (Fin 2)} {x : State GalilVM} {q : CoreControl}
    (henc : EncControl w x q) : EncControl w (countState x) (clockDown q) := by
  refine {henc with ctl := ?_}
  change ctlAbs (clockDown q).ctl = {x.ctl with clock := x.ctl.clock - 1}
  rw [← henc.ctl]
  rfl

theorem core_clockDown {w : List (Fin 2)} {x : State GalilVM} {p : CoreState}
    (henc : CoreEnc w x p) : CoreEnc w (countState x) (clockDown p.1, p.2) := by
  refine ⟨⟨encControl_clockDown henc.1.1, ?_⟩, henc.2⟩
  exact encTapes_congr margin x (countState x) p.1.polarity p.1.gap p.1.micro
    p.1.fppLive p.1.dpLive _ (fun _ => rfl) (fun _ => rfl) rfl rfl rfl rfl rfl henc.1.2

theorem running_clockDown {w : List (Fin 2)} {x : State GalilVM} {p : CoreState}
    (henc : PalPeg.MachineStep.sweepClosure blankM (CoreEnc w) x p) :
    PalPeg.MachineStep.sweepClosure blankM (CoreEnc w) (countState x) (clockDown p.1, p.2) := by
  obtain ⟨T, hT, hteq⟩ := henc
  exact ⟨T, core_clockDown hT, hteq⟩

noncomputable def countRead {K : ℕ} (q : CoreControl)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) : Bool :=
  decide (q.ctl.mode = .scan) && decide (scanPhase q ws = .count)

theorem countRead_eq {K : ℕ} {w : List (Fin 2)} {x : State GalilVM}
    {q : CoreControl} {T : Slot → STape Γm}
    (henc : PalPeg.PhysicalEncoding.Enc w margin x (q, T))
    (hK : 1 ≤ K) (hmargin : K ≤ margin)
    (hmode : x.ctl.mode = .scan) (hstarved : PalPeg.FrameFunction.starvedTest x = false)
    (hrestart : restartGuardTest x.vm = false) (hclock : 1 < x.ctl.clock) :
    countRead q (fun tape => readWin blankM K (tapesOf T tape)) = true := by
  have hqmode := congrArg PalPeg.GalilScaffoldController.Control.mode henc.1.ctl
  change q.ctl.mode = x.ctl.mode at hqmode
  have hquiet := PalPeg.PhysicalGuardProbe.nonstarved_scan_not_quiet x hmode hstarved
  unfold countRead
  rw [hqmode, hmode, scanPhase_eq henc hK hmargin]
  simp [scanPhaseOf, hrestart, hquiet, hclock]

theorem countRead_running {w : List (Fin 2)} {x : State GalilVM} {p : CoreState}
    (henc : PalPeg.MachineStep.sweepClosure blankM (CoreEnc w) x p)
    (hmode : x.ctl.mode = .scan) (hstarved : PalPeg.FrameFunction.starvedTest x = false)
    (hrestart : restartGuardTest x.vm = false) (hclock : 1 < x.ctl.clock) :
    countRead p.1 (fun tape => readWin blankM macroRadius (p.2 tape)) = true := by
  apply read_from_running countRead (fun _ => true) w x p henc
  intro T hT
  simpa only [tapesOf, Equiv.apply_symm_apply] using
    countRead_eq hT.1 (by decide : 1 ≤ macroRadius) (le_refl margin)
      hmode hstarved hrestart hclock

noncomputable def countedStep (work : CoreStep) : CoreStep where
  next := fun q input ws =>
    let result := work.next q input ws
    (if countRead q ws then clockDown result.1 else result.1, result.2)
  disp_le := fun q input ws tape => work.disp_le q input ws tape

theorem counted_apply (work : CoreStep) (p : CoreState) (input : Option (Fin 2)) :
    (countedStep work).apply blankM p input =
      (if countRead p.1 (fun tape => readWin blankM macroRadius (p.2 tape)) then
        clockDown (work.apply blankM p input).1 else (work.apply blankM p input).1,
        (work.apply blankM p input).2) := rfl

abbrev RestCommands := CoreControl → Option (Fin 2) →
  (Fin tapeCountM → PalPeg.Local.Window Γm microRadius) →
  Fin 4 → PalPeg.ConcreteLocalMachine.ViewCommand

noncomputable def workRule (rest : RestCommands) :=
  tickPhysRule 1 0 fppBound_gt_start (by decide : 1 + 3 ≤ microRadius)
    (by decide : 2 ≤ microRadius) rest

theorem workRule_eq (rest : RestCommands) : workRule rest =
    tickPhysRule 1 0 fppBound_gt_start (by decide : 1 + 3 ≤ microRadius)
      (by decide : 2 ≤ microRadius) rest := rfl

noncomputable def workStep (rest : RestCommands) : CoreStep := compStep (iterRule (workRule rest) 12)

noncomputable def scanMachine (rest : RestCommands) := machine (countedStep (workStep rest))

/-- A standing background branch of the original rule, independent of the quiet/count guard.
Only the running VM work is done here; `countedStep` supplies the controller decrement. -/
theorem core_still (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (henc : CoreEnc w x p) (hmode : p.1.ctl.mode = .scan)
    (hphase : scanPhase p.1 (fun tape => readWin blankM microRadius (p.2 tape)) ≠ .compare)
    (hconsume : chainConsumesTest p.1 (fun tape => readWin blankM microRadius (p.2 tape)) = false) :
    CoreEnc w x (idealRun (workRule rest) blankM p none 12) := by
  generalize hrun : idealRun (workRule rest) blankM p none 12 = result
  let T := fun slot => p.2 (slotIndex slot)
  have hT : tapesOf T = p.2 := by funext tape; simp [T, tapesOf]
  have hphaseT : scanPhase p.1 (fun tape => readWin blankM microRadius (tapesOf T tape)) ≠ .compare := by
    rw [hT]; exact hphase
  have hconsumeT : chainConsumesTest p.1 (fun tape => readWin blankM microRadius (tapesOf T tape)) = false := by
    rw [hT]; exact hconsume
  let R := physRule (dpBound := dpBound) 1 0 fppBound_gt_start (by decide : 1 + 3 ≤ microRadius)
  have hacts : R.acts p.1 none (fun tape => readWin blankM microRadius (tapesOf T tape)) =
      withErase p.1.fppLive (fun tape => readWin blankM microRadius (tapesOf T tape)) (fun _ => []) :=
    physRule_acts_scan 1 0 fppBound_gt_start (by decide) p.1 _ hmode hphaseT hconsumeT
  have hcontrol : (idealStep R blankM (p.1, tapesOf T) none).1 = p.1 :=
    physRule_nq_scan 1 0 fppBound_gt_start (by decide) p.1 _ hmode hphaseT hconsumeT
  have hbranch : PalPeg.PhysicalEncoding.Enc w margin x
      ((idealStep R blankM (p.1, tapesOf T) none).1,
        fun slot => (idealStep R blankM (p.1, tapesOf T) none).2 (slotIndex slot)) := by
    rw [hcontrol]
    refine ⟨henc.1.1, encTapes_idleOnly margin x p.1.polarity p.1.gap p.1.micro
      p.1.fppLive p.1.dpLive T _ henc.1.2 ?_ ?_⟩
    · intro slot hslot
      rw [idealStep_withErase R p.1 T p.1.fppLive _ hacts slot hslot]
      rfl
    · exact idle_shape_after_erase margin (by decide) (by decide) R p.1 T p.1.fppLive
        _ hacts (fun _ => rfl) henc.1.2.idleShape
  constructor
  · have hnext := enc_ofBranchStep_stay margin 1 0 fppBound_gt_start (by decide)
      (by decide) micro_le_margin rest w x x p.1 T none henc.2.1
      (by
        rw [modeCommands_scan 0 rest p.1 none _ hmode]
        exact scanCommands_eq_stay p.1 _ hphaseT hconsumeT)
      henc.2.2 (fun _ => rfl) henc.1.2 hbranch
    simpa only [← workRule_eq, hT, Prod.eta, hrun] using hnext
  · have hb := macroBoundary_tickRule
      (fun q _ ws => ruleNext 1 0 fppBound_gt_start q ws) (modeCommands 0 rest)
      (fun q _ ws => ruleActs 1 0 q ws)
      (fun q _ ws j => ruleActs_length 1 0 (by decide : 1 + 3 ≤ microRadius) q ws j)
      w x p none henc
    simpa only [← tickPhysRule_eq 1 0 fppBound_gt_start (by decide) (by decide) rest,
      ← workRule_eq, hrun] using hb

/-- The source's idle-chain tag supplies the nonconsumption premise; all head and
macro-boundary premises come from the running encoding. -/
theorem running_still (rest : RestCommands) (w : List (Fin 2))
    (x : State GalilVM) (p : CoreState)
    (henc : PalPeg.MachineStep.sweepClosure blankM (CoreEnc w) x p)
    (hmode : x.ctl.mode = .scan) (hstarved : PalPeg.FrameFunction.starvedTest x = false)
    (hrestart : restartGuardTest x.vm = false) (hclock : 1 < x.ctl.clock)
    (hidle : x.vm.chain = .idle) :
    PalPeg.MachineStep.sweepClosure blankM (CoreEnc w) x
      ((workStep rest).apply blankM p none) := by
  apply running_fused_step (workRule rest) w x x p none henc
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
  apply core_still rest w x (p.1, T) hT (hqmode.trans hmode)
  · rw [hphaseT]; decide
  · unfold chainConsumesTest
    rw [hT.1.1.chainTag, hidle]
    rfl

/-- One count case of the final none-step contract. The source case split is
idle chain and stopped search; there are no target-encoding, readiness, margin,
slot or owed-work assumptions left for its caller to supply. -/
theorem forward_count_atRest (rest : RestCommands) (w : List (Fin 2))
    (x : State GalilVM) (p : PhysicalState)
    (henc : PalPeg.PhysicalContract.Enc w x p)
    (hmode : x.ctl.mode = .scan) (hstarved : PalPeg.FrameFunction.starvedTest x = false)
    (hclock : 1 < x.ctl.clock) (hidle : x.vm.chain = .idle)
    (hsearch : x.vm.search.mode = .idle ∨ x.vm.search.mode = .missed) :
    PalPeg.PhysicalContract.Enc w
      (tickFun (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w)
        (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x)
      ((scanMachine rest).apply blankM p none) := by
  have hrestart : restartGuardTest x.vm = false := by simp [restartGuardTest, hidle]
  have htick : tickFun (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w)
      (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x = countState x := by
    rw [PalPeg.PhysicalGuardProbe.tickFun_nonstarved_count centreC placeC 0 1 0 w _ 2048 x
      hmode hstarved hrestart hclock]
    change (⟨_, backgroundFun _ x.vm⟩ : State GalilVM) = _
    rw [backgroundFun_id_of_searchAtRest _ x.vm hidle hsearch]
    rfl
  rw [htick]
  rcases p with ⟨q, T⟩
  cases q with
  | inl bootTag =>
    rw [henc.1, initial_starved] at hstarved
    cases hstarved
  | inr control =>
    rw [scanMachine, apply_active (countedStep (workStep rest)) w x (control, T) henc hstarved,
      enc_running, counted_apply, countRead_running henc hmode hstarved hrestart hclock]
    simp only [if_true]
    exact running_clockDown (running_still rest w x (control, T) henc hmode hstarved
      hrestart hclock hidle)

/-- The same machine retains both verified input branches. -/
theorem forward_feed (rest : RestCommands) (w : List (Fin 2))
    (x : State GalilVM) (p : PhysicalState) (a : Fin 2)
    (henc : PalPeg.PhysicalContract.Enc w x p) :
    PalPeg.PhysicalContract.Enc w (PalPeg.GalilArriveChain.arriveState' a x)
      ((scanMachine rest).apply blankM p (some a)) :=
  PhysicalBootFeed.forwardFeed _ w x p a henc

/-- A source-state case split, rather than a hypothesis about the desired successor. -/
def CountAtRest (x : State GalilVM) : Prop :=
  x.ctl.mode = .scan ∧ 1 < x.ctl.clock ∧ x.vm.chain = .idle ∧
    (x.vm.search.mode = .idle ∨ x.vm.search.mode = .missed)

open PalPeg.CloseoutCheckW (PreTraceIMW CanonTrace)
open PalPeg.LocalSysConcrete (absSC)
open PalPeg.LocalReplayParked (Mirrored1)
open PalPeg.LocalShadowConcrete (OnRun)
open PalPeg.LocalBlankState (tapeCount)
open PalPeg.ShadowedLocalFinal (localGood postPhase frozenAt heldAfter)

/-- The final dispatcher already handles all starvation and the at-rest count case.
Only the complementary active cases remain; their original OnRun/trace premises
are retained for supplying availability and other reachable-state invariants. -/
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
        ¬ CountAtRest (absSC m) → PalPeg.PhysicalContract.Enc w
          (tickFun (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w)
            (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 (absSC m))
          ((scanMachine rest).apply blankM p none)) :
    TickCases (scanMachine rest) blankM PalPeg.PhysicalContract.Enc where
  starved := by
    intro w st Tc hpre hcanon m p hon hnotFrozen henc hstarved
    exact forward_starved (countedStep (workStep rest)) w (absSC m) p henc hstarved
  active := by
    intro w st Tc hpre hcanon m p hon hnotFrozen henc hstarved htick
    by_cases hcount : CountAtRest (absSC m)
    · exact forward_count_atRest rest w (absSC m) p henc hcount.1 hstarved
        hcount.2.1 hcount.2.2.1 hcount.2.2.2
    · exact hother w st Tc hpre hcanon m p hon hnotFrozen henc hstarved htick hcount

/-- info: 'PalPeg.PhysicalScanCount.cases_of_remaining' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cases_of_remaining

/-- info: 'PalPeg.PhysicalScanCount.forward_count_atRest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forward_count_atRest

/-- info: 'PalPeg.PhysicalScanCount.forward_feed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forward_feed

end PalPeg.PhysicalScanCount
