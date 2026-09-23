import PalPeg.PhysicalPhaseStill
import PalPeg.PhysicalCacheMachine
import PalPeg.PhysicalBoundaryCount
import PalPeg.PhysicalShiftDispatch
import PalPeg.PhysicalSnapshotMachine
import PalPeg.PhysicalDpCleanupDispatch

/-!
# Non-scan ticks pass through the dispatcher layers

Every branch test of the dispatcher layers reads `countRead` (or another scan-only test), so
outside scan each layer runs the layer below it. This file carries a non-scan tick from the
fused work step up the layers.
-/
set_option autoImplicit false
namespace PalPeg.PhysicalPhaseLayers
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract PalPeg.PhysicalScanCount
open PalPeg.Program (STape)
open PalPeg.Local (readWin pos)
open PalPeg.CloseoutCoreEnc12 PalPeg.LocalStepFusion
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilFinalAssembly2 (centreC placeC)

/-- Outside scan every branch test of the cache machine is off: it runs the work step. -/
theorem selected_nonscan (rest : RestCommands) (p : CoreState)
    (hmode : p.1.ctl.mode ≠ .scan) :
    (PalPeg.PhysicalCacheMachine.activeStep rest).apply blankM p none =
      (workStep rest).apply blankM p none := by
  have hcount : countRead p.1 (fun tape => readWin blankM macroRadius (p.2 tape)) = false := by
    simp [countRead, hmode]
  simp [PalPeg.PhysicalCacheMachine.activeStep, PalPeg.PhysicalWatchEntry.withWatchEntry,
    PalPeg.PhysicalTickDispatch.branch_apply, PalPeg.PhysicalWatchEntry.entryRead,
    PalPeg.PhysicalCacheMachine.prepareRead, counted_apply, hcount]
  rfl

/-- **A non-scan tick through the cache machine**, from its fused `Running` step. -/
theorem forward_nonscan (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : PalPeg.PhysicalContract.PhysicalState) (he : PalPeg.PhysicalCacheMachine.Enc w x p)
    (hmode : x.ctl.mode ≠ .scan) (hstarved : PalPeg.FrameFunction.starvedTest x = false)
    (hrun : ∀ q : CoreControl, p.1 = Sum.inr q → PalPeg.PhysicalCacheInvariant.Running w x (q, p.2) →
      PalPeg.PhysicalCacheInvariant.Running w (PalPeg.PhysicalCacheMachine.successor w x)
        ((workStep rest).apply blankM (q, p.2) none)) :
    PalPeg.PhysicalCacheMachine.Enc w (PalPeg.PhysicalCacheMachine.successor w x)
      ((PalPeg.PhysicalCacheMachine.machine rest).apply blankM p none) := by
  rcases p with ⟨q, T⟩
  cases q with
  | inl tag =>
    rw [he.1, PalPeg.PhysicalBootFeed.initial_starved] at hstarved
    cases hstarved
  | inr q =>
    have hr : PalPeg.PhysicalCacheInvariant.Running w x (q, T) := he
    rw [PalPeg.PhysicalCacheMachine.machine,
      PalPeg.PhysicalTickDispatch.apply_active (PalPeg.PhysicalCacheMachine.activeStep rest) w x
        (q, T) (PalPeg.PhysicalCacheInvariant.running_core hr) hstarved]
    have hqmode : q.ctl.mode ≠ .scan := by
      obtain ⟨T', hT', _⟩ := PalPeg.PhysicalCacheInvariant.running_core hr
      have hc : q.ctl.mode = x.ctl.mode :=
        congrArg PalPeg.GalilScaffoldController.Control.mode hT'.1.1.ctl
      rw [hc]; exact hmode
    rw [selected_nonscan rest (q, T) hqmode]
    have h := hrun q rfl hr
    generalize (workStep rest).apply blankM (q, T) none = r at h ⊢
    exact h

/-- The fused step of a non-scan tick keeps the running invariant (the per-mode lemmas). -/
def RunsNonscan (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM) : Prop :=
  ∀ p : CoreState, PalPeg.PhysicalCacheInvariant.Running w x p →
    PalPeg.PhysicalCacheInvariant.Running w (PalPeg.PhysicalCacheMachine.successor w x)
      ((workStep rest).apply blankM p none)

/-- **A non-scan tick through the role-routing layer**: no role change outside scan. -/
theorem forward_nonscan_routed (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : PalPeg.PhysicalRoles.PhysicalState) (he : PalPeg.PhysicalBoundaryCount.Enc w x p)
    (hmode : x.ctl.mode ≠ .scan) (hs : PalPeg.FrameFunction.starvedTest x = false)
    (hrun : RunsNonscan rest w x) :
    PalPeg.PhysicalBoundaryCount.Enc w (PalPeg.PhysicalCacheMachine.successor w x)
      ((PalPeg.PhysicalBoundaryCount.machine rest).apply blankM p none) := by
  change PalPeg.PhysicalCacheInvariant.Enc w _ (PalPeg.LocalRoleRouting.decode _)
  rw [PalPeg.PhysicalBoundaryCount.decode_machine]
  rcases p with ⟨⟨roles, q⟩, T⟩
  cases q with
  | inl tag => rw [he.1, PalPeg.PhysicalBootFeed.initial_starved] at hs; cases hs
  | inr q =>
    let U := fun j => T (roles j)
    have hr : PalPeg.PhysicalCacheInvariant.Running w x (q, U) := he
    have hcore := PalPeg.PhysicalCacheInvariant.running_core hr
    have hm : q.ctl.mode ≠ .scan := by
      obtain ⟨ideal, hi, _⟩ := hcore
      have hc : q.ctl.mode = x.ctl.mode :=
        congrArg PalPeg.GalilScaffoldController.Control.mode hi.1.1.ctl
      rw [hc]; exact hmode
    have hchange : PalPeg.PhysicalBoundaryCount.boundaryRead q
        (fun j => readWin blankM macroRadius (U j)) = false := by
      simp only [PalPeg.PhysicalBoundaryCount.boundaryRead, PalPeg.PhysicalCacheMachine.prepareRead,
        countRead, hm, decide_false, Bool.false_and, Bool.and_false]
    change PalPeg.PhysicalCacheInvariant.Enc w _
      (PalPeg.PhysicalBoundaryCount.completedOuter
        (PalPeg.PhysicalBoundaryCount.boundaryRead q (fun j => readWin blankM macroRadius (U j)))
        ((PalPeg.PhysicalCacheMachine.machine rest).apply blankM (.inr q, U) none))
    rw [hchange, PalPeg.PhysicalBoundaryCount.completedOuter, if_neg Bool.false_ne_true]
    exact forward_nonscan rest w x (.inr q, U) hr hmode hs (fun q' hq hr' => by
      cases hq; exact hrun _ hr')

/-- **A non-scan tick through the shift-entry layer**: the entry test reads scan. -/
theorem forward_nonscan_shiftDispatch (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : PalPeg.PhysicalShiftDispatch.RoutedState) (he : PalPeg.PhysicalShiftDispatch.Enc w x p)
    (hmode : x.ctl.mode ≠ .scan) (hs : PalPeg.FrameFunction.starvedTest x = false)
    (hrun : RunsNonscan rest w x) :
    PalPeg.PhysicalShiftDispatch.Enc w (PalPeg.PhysicalCacheMachine.successor w x)
      ((PalPeg.PhysicalShiftDispatch.machine rest).apply blankM p none) := by
  have hentry : PalPeg.PhysicalShiftDispatch.entryTest p.1 none
      (fun j => readWin blankM macroRadius (p.2 j)) = false := by
    rcases p with ⟨⟨roles, q⟩, T⟩
    cases q with
    | inl tag => rfl
    | inr c =>
      have hr : PalPeg.PhysicalCacheInvariant.Running w x (c, fun j => T (roles j)) := he
      obtain ⟨ideal, hi, _⟩ := PalPeg.PhysicalCacheInvariant.running_core hr
      have hc : c.ctl.mode = x.ctl.mode :=
        congrArg PalPeg.GalilScaffoldController.Control.mode hi.1.1.ctl
      simp [PalPeg.PhysicalShiftDispatch.entryTest, PalPeg.PhysicalShiftDispatch.entryRead, hc, hmode]
  rw [PalPeg.PhysicalShiftDispatch.apply_previous rest p none hentry]
  exact forward_nonscan_routed rest w x p he hmode hs hrun

/-- A quiet phase tick never touches the search counters that a saved snapshot replaces. -/
theorem successor_put_quiet (w : List (Fin 2)) (x : State GalilVM)
    (v : Fin 4 → PalPeg.GalilScaffoldCounter.Counter)
    (hq : PalPeg.PhysicalPhaseStill.QuietPhase x.ctl.mode) :
    PalPeg.PhysicalCacheMachine.successor w (PalPeg.PhysicalSearchSnapshots.put x v) =
      PalPeg.PhysicalSearchSnapshots.put (PalPeg.PhysicalCacheMachine.successor w x) v := by
  unfold PalPeg.PhysicalCacheMachine.successor PalPeg.PhysicalSearchSnapshots.put
  unfold PalPeg.GalilScaffoldTop.tickFun
  rcases hq with h | h | h | h | h | h <;> simp only [h] <;> (repeat' split) <;>
    first | rfl | contradiction | simp_all [PalPeg.PhysicalRestartStorage.replace]

theorem quiet_ne_scan {m : PalPeg.GalilScaffoldController.Mode}
    (hq : PalPeg.PhysicalPhaseStill.QuietPhase m) : m ≠ .scan := by
  rcases hq with h | h | h | h | h | h <;> rw [h] <;> decide

theorem quiet_ne_shift {m : PalPeg.GalilScaffoldController.Mode}
    (hq : PalPeg.PhysicalPhaseStill.QuietPhase m) : m ≠ .shift := by
  rcases hq with h | h | h | h | h | h <;> rw [h] <;> decide

/-- The per-mode step facts, for every state with the same control and first-period program.
Snapshots and representatives differ from the source only in the search counters. -/
def RunsQuiet (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM) : Prop :=
  ∀ y : State GalilVM, y.ctl = x.ctl → PalPeg.PhysicalRestartStorage.Same x.vm y.vm →
    RunsNonscan rest w y

/-- **A quiet phase tick through the snapshot layer.** The representative and every saved copy
step with the source; the chain, hence the copy's boundary cache, does not move. -/
theorem forward_quiet_snapshot (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : PalPeg.PhysicalShiftDispatch.RoutedState) (he : PalPeg.PhysicalSnapshotInvariant.Enc w x p)
    (hq : PalPeg.PhysicalPhaseStill.QuietPhase x.ctl.mode)
    (hs : PalPeg.FrameFunction.starvedTest x = false) (hrun : RunsQuiet rest w x) :
    PalPeg.PhysicalSnapshotInvariant.Enc w (PalPeg.PhysicalCacheMachine.successor w x)
      ((PalPeg.PhysicalSnapshotMachine.machine rest).apply blankM p none) := by
  have hmode := quiet_ne_scan hq
  obtain ⟨⟨y, hr, hold⟩, hcopies⟩ := he
  have hctl : y.ctl = x.ctl := hr.1.symm
  have hmodey : y.ctl.mode ≠ .scan := by rw [hctl]; exact hmode
  have hsy : PalPeg.FrameFunction.starvedTest y = false := by
    rw [PalPeg.PhysicalRestartStorage.related_starved hr]; exact hs
  have htests : PalPeg.PhysicalSnapshotMachine.entryTest p.1 none
        (fun j => readWin blankM macroRadius (p.2 j)) = false ∧
      PalPeg.PhysicalSnapshotMachine.matchTest p.1 none
        (fun j => readWin blankM macroRadius (p.2 j)) = false := by
    rcases p with ⟨⟨roles, q⟩, T⟩
    cases q with
    | inl tag => exact ⟨rfl, rfl⟩
    | inr c =>
      have hrun' : PalPeg.PhysicalCacheInvariant.Running w y (c, fun j => T (roles j)) := hold
      obtain ⟨ideal, hi, _⟩ := PalPeg.PhysicalCacheInvariant.running_core hrun'
      have hc : c.ctl.mode = y.ctl.mode :=
        congrArg PalPeg.GalilScaffoldController.Control.mode hi.1.1.ctl
      have hcount : countRead c (fun j => readWin blankM macroRadius (T (roles j))) = false := by
        simp [countRead, hc, hmodey]
      constructor
      · simp [PalPeg.PhysicalSnapshotMachine.entryTest, PalPeg.PhysicalWatchEntry.entryRead, hcount]
      · simp [PalPeg.PhysicalSnapshotMachine.matchTest, PalPeg.PhysicalCacheMachine.prepareRead,
          hcount]
  rw [PalPeg.PhysicalSnapshotMachine.apply_previous rest p none htests.1 htests.2]
  refine ⟨⟨PalPeg.PhysicalCacheMachine.successor w y,
    PalPeg.PhysicalRestartStorage.related_tick w hr,
    forward_nonscan_shiftDispatch rest w y p hold hmodey hsy (hrun y hctl hr.2.1)⟩, ?_⟩
  intro wm hwm
  rw [show (PalPeg.PhysicalCacheMachine.successor w x).vm.chain = x.vm.chain from
    PalPeg.PhysicalPhaseStill.chain_tickFun w x hq] at hwm
  obtain ⟨h, age, spare, hinv, hsaved⟩ := hcopies wm hwm
  refine ⟨h, age, spare, hinv, ?_⟩
  unfold PalPeg.PhysicalSearchSnapshots.saved
  rw [← successor_put_quiet w x _ hq]
  exact forward_nonscan_shiftDispatch rest w _ p hsaved hmode hs (hrun _ rfl (PalPeg.PhysicalRestartStorage.same_replace _ _ _ _ _))

/-- **A quiet phase tick through the whole common machine.** Each dispatcher above the
snapshot layer tests scan (or shift), so it runs the layer below; the cleanup layer carries its
finite state. -/
theorem forward_quiet_machine (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : PalPeg.PhysicalDpCleanup.Config) (he : PalPeg.PhysicalDpCleanup.Enc w x p)
    (hq : PalPeg.PhysicalPhaseStill.QuietPhase x.ctl.mode)
    (hs : PalPeg.FrameFunction.starvedTest x = false)
    (hloan : ¬ PalPeg.PhysicalLoanInvariant.NeedsLoan (PalPeg.PhysicalCacheMachine.successor w x))
    (hrun : RunsQuiet rest w x) :
    PalPeg.PhysicalDpCleanup.Enc w (PalPeg.PhysicalCacheMachine.successor w x)
      ((PalPeg.PhysicalDpCleanup.machine rest).apply blankM p none) := by
  have hmode := quiet_ne_scan hq
  apply PalPeg.PhysicalDpCleanupDispatch.forward_of_previous rest w x _ p none he
  have hx : ¬ PalPeg.PhysicalLoanInvariant.NeedsLoan x := fun h => hmode h.1
  apply PalPeg.PhysicalLoanDispatch.active_of_previous rest w x _ he.1 hs hx hloan
  intro hsnap
  rw [PalPeg.PhysicalSnapshotEntryDispatch.previous_when rest w x _ hsnap (.inl hmode),
    PalPeg.PhysicalSnapshotShiftDispatch.previous_nonshift rest w x _ hsnap (quiet_ne_shift hq)]
  exact forward_quiet_snapshot rest w x _ hsnap hq hs hrun

/-- `home` and `markEnd` step unconditionally. -/
theorem runsQuiet_home (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (hmode : x.ctl.mode = .home) : RunsQuiet rest w x := fun y hy _ p hp =>
  PalPeg.PhysicalPhaseStill.running_quiet rest w y p hp (fun T hT =>
    PalPeg.PhysicalPhaseStill.ideal_home rest w y (p.1, T) hT (by rw [hy]; exact hmode))

theorem runsQuiet_markEnd (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (hmode : x.ctl.mode = .markEnd) : RunsQuiet rest w x := fun y hy _ p hp =>
  PalPeg.PhysicalPhaseStill.running_quiet rest w y p hp (fun T hT =>
    PalPeg.PhysicalPhaseStill.ideal_markEnd rest w y (p.1, T) hT (by rw [hy]; exact hmode))

theorem runsQuiet_chooseBack (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (hmode : x.ctl.mode = .choose)
    (hkeep : (x.ctl.odd && (decide ((x.vm.fpp.program.config.tapes 8).focus = 8)
        || decide ((x.vm.fpp.program.config.tapes 8).focus = 0))) = false) :
    RunsQuiet rest w x := fun y hy hsame p hp =>
  PalPeg.PhysicalPhaseStill.running_quiet rest w y p hp (fun T hT =>
    PalPeg.PhysicalPhaseStill.ideal_chooseBack rest w y (p.1, T) hT (by rw [hy]; exact hmode)
      (by unfold PalPeg.PhysicalRestartStorage.Same at hsame; rw [hy, hsame]; exact hkeep))

theorem runsQuiet_fpp (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (hmode : x.ctl.mode = .fpp)
    (hcomp : ∀ t : Fin 9, microRadius ≤ PalPeg.Local.pos (encTape (x.vm.fpp.program.config.tapes t)))
    (hfloorRun : ∀ k, ∀ t : Fin 9, ((PalPeg.ProgramFunction.runFun PalPeg.GalilFppMarkedCode.code
      (List.replicate k true) x.vm.fpp.program).config.tapes t).left ≠ [])
    (hin : x.vm.fpp.program.config.pc < fppBound) :
    RunsQuiet rest w x := fun y hy hsame p hp => by
  unfold PalPeg.PhysicalRestartStorage.Same at hsame
  exact PalPeg.PhysicalPhaseStill.running_quiet rest w y p hp (fun T hT =>
    PalPeg.PhysicalPhaseStill.ideal_fpp rest w y (p.1, T) hT (by rw [hy]; exact hmode)
      (by rw [hsame]; exact hcomp) (by rw [hsame]; exact hfloorRun) (by rw [hsame]; exact hin))

/-- A rewind step back along the marks tape: not at the first mark, off the floor. -/
def RewindStep (w : List (Fin 2)) (x : State GalilVM) : Prop :=
  x.ctl.mode = .rewind ∧
    (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w).atFirst x.vm = false ∧
    (x.vm.fpp.program.config.tapes 8).left ≠ []

theorem runsQuiet_rewindStep (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (hstep : RewindStep w x) : RunsQuiet rest w x := fun y hy hsame p hp => by
  unfold PalPeg.PhysicalRestartStorage.Same at hsame
  exact PalPeg.PhysicalPhaseStill.running_quiet rest w y p hp (fun T hT =>
    PalPeg.PhysicalPhaseStill.ideal_rewindStep rest w y (p.1, T) hT (by rw [hy]; exact hstep.1)
      (by rw [hsame]; exact hstep.2.1) (by rw [hsame]; exact hstep.2.2))

/-- The copy tick whose walker can read the letter it copies. -/
def CopyReady (w : List (Fin 2)) (x : State GalilVM) : Prop :=
  x.ctl.mode = .copy ∧
    ((PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w).remainingPos x.vm = true →
      ∃ a, PalPeg.GalilScaffoldPlace.read x.vm.fpp.walker = some a)

theorem runsQuiet_copy (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (hready : CopyReady w x) : RunsQuiet rest w x := fun y hy hsame p hp => by
  unfold PalPeg.PhysicalRestartStorage.Same at hsame
  exact PalPeg.PhysicalPhaseStill.running_quiet rest w y p hp (fun T hT =>
    PalPeg.PhysicalPhaseStill.ideal_copy rest w y (p.1, T) hT (by rw [hy]; exact hready.1)
      (by rw [hsame]; exact hready.2))

/-- A quiet phase moves only among the phases and `rewind`: it never returns to scan. -/
theorem successor_ne_scan (w : List (Fin 2)) (x : State GalilVM)
    (hq : PalPeg.PhysicalPhaseStill.QuietPhase x.ctl.mode) :
    (PalPeg.PhysicalCacheMachine.successor w x).ctl.mode ≠ .scan := by
  unfold PalPeg.PhysicalCacheMachine.successor PalPeg.GalilScaffoldTop.tickFun
  rcases hq with h | h | h | h | h | h <;> rw [h] <;> dsimp only <;> (repeat' split) <;> simp_all

theorem successor_not_loan (w : List (Fin 2)) (x : State GalilVM)
    (hq : PalPeg.PhysicalPhaseStill.QuietPhase x.ctl.mode) :
    ¬ PalPeg.PhysicalLoanInvariant.NeedsLoan (PalPeg.PhysicalCacheMachine.successor w x) :=
  fun h => successor_ne_scan w x hq h.1

open PalPeg.GalilFinalAssembly2 (centreC placeC)
open PalPeg.CloseoutCheckW (PreTraceIMW CanonTrace)
open PalPeg.LocalSysConcrete (absSC)
open PalPeg.LocalReplayParked (Mirrored1)
open PalPeg.LocalBlankState (tapeCount)
open PalPeg.ShadowedLocalFinal (localGood postPhase frozenAt heldAfter)

/-- The back half of `choose`: not the tick that selects and leaves for `rewind`. -/
def ChooseBack (x : State GalilVM) : Prop :=
  x.ctl.mode = .choose ∧
    (x.ctl.odd && (decide ((x.vm.fpp.program.config.tapes 8).focus = 8)
        || decide ((x.vm.fpp.program.config.tapes 8).focus = 0))) = false

/-- **`home`, `markEnd`, the back half of `choose`, `copy` and the rewind steps join the handled cases** of the common machine's final tick API.
The residual now also excludes these. -/
theorem cases_of_remaining_quiet (rest : RestCommands)
    (hother : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC 0 1 0 w st Tc → CanonTrace 0 w st Tc →
      ∀ (m : Mirrored1 (tapeCount 0)) (p : PalPeg.PhysicalDpCleanup.Config),
        PalPeg.LocalShadowConcrete.ArrivedOnRun (localGood (spare := 0)) (postPhase 0 1 0) w
          (heldAfter (Tc w.length) st) m →
        ¬ frozenAt w m → PalPeg.PhysicalDpCleanup.Enc w (absSC m) p →
        PalPeg.FrameFunction.starvedTest (absSC m) = false →
        Tick (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 (absSC m)
          (PalPeg.PhysicalCacheMachine.successor w (absSC m)) →
        ¬ PalPeg.PhysicalScanCount.CountAtRest (absSC m) →
        ¬ PalPeg.PhysicalBoundaryCount.CountWatch (absSC m) →
        ¬ PalPeg.PhysicalBoundaryCount.CountBackReady (absSC m) →
        (absSC m).ctl.mode ≠ .shift → ¬ PalPeg.PhysicalShiftDispatch.Entry w (absSC m) →
        ¬ PalPeg.PhysicalGrowCount.CountGrow (absSC m) →
        ¬ PalPeg.PhysicalGrowMatchCase.MatchGrow (absSC m) →
        (absSC m).ctl.mode ≠ .home → (absSC m).ctl.mode ≠ .markEnd →
        ¬ ChooseBack (absSC m) → ¬ CopyReady w (absSC m) → ¬ RewindStep w (absSC m) →
        PalPeg.PhysicalDpCleanup.Enc w (PalPeg.PhysicalCacheMachine.successor w (absSC m))
          ((PalPeg.PhysicalDpCleanup.machine rest).apply blankM p none)) :
    TickCases (PalPeg.PhysicalDpCleanup.machine rest) blankM PalPeg.PhysicalDpCleanup.Enc := by
  apply PalPeg.PhysicalDpCleanupDispatch.cases_of_remaining rest
  intro w st Tc hpre hcanon m p hon hf he hs htick h1 h2 h3 h4 h5 h6 h7
  by_cases hhome : (absSC m).ctl.mode = .home
  · have hq : PalPeg.PhysicalPhaseStill.QuietPhase (absSC m).ctl.mode := Or.inr (Or.inl hhome)
    exact forward_quiet_machine rest w _ p he hq hs (successor_not_loan w _ hq)
      (runsQuiet_home rest w _ hhome)
  by_cases hmark : (absSC m).ctl.mode = .markEnd
  · have hq : PalPeg.PhysicalPhaseStill.QuietPhase (absSC m).ctl.mode := Or.inl hmark
    exact forward_quiet_machine rest w _ p he hq hs (successor_not_loan w _ hq)
      (runsQuiet_markEnd rest w _ hmark)
  by_cases hback : ChooseBack (absSC m)
  · have hq : PalPeg.PhysicalPhaseStill.QuietPhase (absSC m).ctl.mode := Or.inr (Or.inr (Or.inr (Or.inl hback.1)))
    exact forward_quiet_machine rest w _ p he hq hs (successor_not_loan w _ hq)
      (runsQuiet_chooseBack rest w _ hback.1 hback.2)
  by_cases hcopy : CopyReady w (absSC m)
  · have hq : PalPeg.PhysicalPhaseStill.QuietPhase (absSC m).ctl.mode :=
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hcopy.1))))
    exact forward_quiet_machine rest w _ p he hq hs (successor_not_loan w _ hq)
      (runsQuiet_copy rest w _ hcopy)
  by_cases hrewind : RewindStep w (absSC m)
  · have hq : PalPeg.PhysicalPhaseStill.QuietPhase (absSC m).ctl.mode :=
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hrewind.1))))
    exact forward_quiet_machine rest w _ p he hq hs (successor_not_loan w _ hq)
      (runsQuiet_rewindStep rest w _ hrewind)
  exact hother w st Tc hpre hcanon m p hon hf he hs htick h1 h2 h3 h4 h5 h6 h7 hhome hmark hback
    hcopy hrewind

/-- info: 'PalPeg.PhysicalPhaseLayers.cases_of_remaining_quiet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cases_of_remaining_quiet

end PalPeg.PhysicalPhaseLayers
