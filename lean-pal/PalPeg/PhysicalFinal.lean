import PalPeg.PhysicalDpCleanupDispatch
import PalPeg.PhysicalConnection

/-!
# The final theorem from the current common machine

The final consumer is reached from `PhysicalDpCleanup.machine rest` now, not
after every branch exists. Initial encoding, every input feed and every starved
tick are proved. What remains is stated here exactly: the not yet implemented
tick cases (`hother` of `PhysicalDpCleanupDispatch.cases_of_remaining`), and
the report/output/freeze contracts of `ReportResiduals`.
-/
set_option autoImplicit false
namespace PalPeg.PhysicalFinal
open PalPeg PegSeparation
open PalPeg.GalilScaffoldTop
open PalPeg.Program (STape)
open PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilFinalAssembly2 (centreC placeC)
open PalPeg.CloseoutCheckW (PreTraceIMW CanonTrace)
open PalPeg.LocalSysConcrete (absSC)
open PalPeg.LocalShadowConcrete (OnRun)
open PalPeg.ShadowedLocalFinal (localGood postPhase frozenAt heldAfter reportCaught)
open PalPeg.PhysicalEncoding (blankM Γm tapeCountM)
open PalPeg.PhysicalDpCleanup (Config Enc machine initialControl)

/-- The stop, report and output contracts of the fixed consumer, for the common
machine. These are the M5 contracts; none is assumed elsewhere. -/
structure ReportResiduals (rest : PalPeg.PhysicalScanCount.RestCommands)
    (repQ : PalPeg.PhysicalDpCleanup.Control →
      (Fin tapeCountM → PalPeg.Local.Window Γm PalPeg.PhysicalContract.macroRadius) → Bool)
    (outQ : PalPeg.PhysicalDpCleanup.Control → Bool)
    (PhysFrozen : List (Fin 2) → Config → Prop) : Prop where
  frozenEnter : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC 0 1 0 w st Tc → CanonTrace 0 w st Tc →
      ∀ m p, OnRun (localGood (spare := 0)) (postPhase 0 1 0) w (heldAfter (Tc w.length) st) m →
        frozenAt w m → Enc w (absSC m) p → PhysFrozen w p
  frozenKeep : ∀ (w : List (Fin 2)) p, PhysFrozen w p →
      PhysFrozen w ((machine rest).apply blankM p none)
  frozenQuiet : ∀ (w : List (Fin 2)) p, PhysFrozen w p → repQ p.1 (fun j => PalPeg.Local.readWin blankM PalPeg.PhysicalContract.macroRadius (p.2 j)) = false
  encRep : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC 0 1 0 w st Tc → CanonTrace 0 w st Tc →
      ∀ m p, OnRun (localGood (spare := 0)) (postPhase 0 1 0) w (heldAfter (Tc w.length) st) m →
        Enc w (absSC m) p → reportCaught w (absSC m) = repQ p.1 (fun j => PalPeg.Local.readWin blankM PalPeg.PhysicalContract.macroRadius (p.2 j))
  encOut : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC 0 1 0 w st Tc → CanonTrace 0 w st Tc →
      ∀ m p, OnRun (localGood (spare := 0)) (postPhase 0 1 0) w (heldAfter (Tc w.length) st) m →
        Enc w (absSC m) p → reportCaught w (absSC m) = true →
        m.vm.ctl.output = outQ p.1

/-- `PAL ∈ PEG` from the common machine: only the tick cases and the report
contracts remain. -/
theorem given_tickCases_and_reports (rest : PalPeg.PhysicalScanCount.RestCommands)
    (hcases : PalPeg.PhysicalContract.TickCases (machine rest) blankM Enc)
    (repQ : PalPeg.PhysicalDpCleanup.Control →
      (Fin tapeCountM → PalPeg.Local.Window Γm PalPeg.PhysicalContract.macroRadius) → Bool)
    (outQ : PalPeg.PhysicalDpCleanup.Control → Bool)
    (PhysFrozen : List (Fin 2) → Config → Prop)
    (hreports : ReportResiduals rest repQ outQ PhysFrozen) :
    RecognizedByTotalPEG PAL :=
  PalPeg.PhysicalContract.given_obligations (machine rest) blankM initialControl repQ outQ Enc
    PhysFrozen (by decide)
    { hencInit := fun w => PalPeg.PhysicalDpCleanup.enc_initial w
      hforwardTick := fun w st Tc hpre hcanon m p successor hon hnotFrozen henc hsucc =>
        PalPeg.PhysicalContract.forwardTick_of_cases (machine rest) blankM Enc hcases
          w st Tc hpre hcanon m p successor hon hnotFrozen henc hsucc
      hforwardFeed := fun w _ _ _ _ letter m p _ henc =>
        PalPeg.PhysicalDpCleanupBoot.forward_feed rest w (absSC m) p letter henc
      hfrozenEnter := hreports.frozenEnter
      hfrozenKeep := hreports.frozenKeep
      hfrozenQuiet := hreports.frozenQuiet
      hencRep := hreports.encRep
      hencOut := hreports.encOut }

/-- The same with the tick cases reduced to the unimplemented branches. -/
theorem given_remainingCases_and_reports (rest : PalPeg.PhysicalScanCount.RestCommands)
    (hother : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC 0 1 0 w st Tc → CanonTrace 0 w st Tc →
      ∀ (m : PalPeg.LocalReplayParked.Mirrored1 (PalPeg.LocalBlankState.tapeCount 0))
        (p : Config),
        PalPeg.LocalShadowConcrete.ArrivedOnRun (localGood (spare := 0)) (postPhase 0 1 0) w
          (heldAfter (Tc w.length) st) m →
        ¬ frozenAt w m → Enc w (absSC m) p →
        PalPeg.FrameFunction.starvedTest (absSC m) = false →
        Tick (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 (absSC m)
          (PalPeg.PhysicalCacheMachine.successor w (absSC m)) →
        ¬ PalPeg.PhysicalScanCount.CountAtRest (absSC m) →
        ¬ PalPeg.PhysicalBoundaryCount.CountWatch (absSC m) →
        ¬ PalPeg.PhysicalBoundaryCount.CountBackReady (absSC m) →
        (absSC m).ctl.mode ≠ .shift → ¬ PalPeg.PhysicalShiftDispatch.Entry w (absSC m) →
        ¬ PalPeg.PhysicalGrowCount.CountGrow (absSC m) →
        ¬ PalPeg.PhysicalGrowMatchCase.MatchGrow (absSC m) →
        Enc w (PalPeg.PhysicalCacheMachine.successor w (absSC m))
          ((machine rest).apply blankM p none))
    (repQ : PalPeg.PhysicalDpCleanup.Control →
      (Fin tapeCountM → PalPeg.Local.Window Γm PalPeg.PhysicalContract.macroRadius) → Bool)
    (outQ : PalPeg.PhysicalDpCleanup.Control → Bool)
    (PhysFrozen : List (Fin 2) → Config → Prop)
    (hreports : ReportResiduals rest repQ outQ PhysFrozen) :
    RecognizedByTotalPEG PAL :=
  given_tickCases_and_reports rest
    (PalPeg.PhysicalDpCleanupDispatch.cases_of_remaining rest hother) repQ outQ PhysFrozen hreports

/-- info: 'PalPeg.PhysicalFinal.given_remainingCases_and_reports' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms given_remainingCases_and_reports

end PalPeg.PhysicalFinal
