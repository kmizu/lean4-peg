import PalPeg.PhysicalReportTest
import PalPeg.PhysicalPhaseLayers

/-!
# The final theorem, from the ticks the common machine does not handle yet

`given_remainingCases_and_frozen` took the whole tick API as an argument. Here the handled ticks
(the seven source cases of the dispatchers, and the quiet phases `home`, `markEnd`, the back half of
`choose`, `copy` and the rewind steps) are supplied, and only `UnhandledTicks` and the freeze are
left.
-/
set_option autoImplicit false
namespace PalPeg.PhysicalFinalResidual
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract

theorem given_unhandledTicks_and_frozen (rest : PalPeg.PhysicalScanCount.RestCommands)
    (hunhandled : PalPeg.PhysicalPhaseLayers.UnhandledTicks rest)
    (PhysFrozen : List (Fin 2) → PalPeg.PhysicalDpCleanup.Config → Prop)
    (hfrozenEnter : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PalPeg.CloseoutCheckW.PreTraceIMW PalPeg.GalilFinalAssembly2.centreC
        PalPeg.GalilFinalAssembly2.placeC 0 1 0 w st Tc → PalPeg.CloseoutCheckW.CanonTrace 0 w st Tc →
      ∀ m p, PalPeg.LocalShadowConcrete.OnRun (PalPeg.ShadowedLocalFinal.localGood (spare := 0))
          (PalPeg.ShadowedLocalFinal.postPhase 0 1 0) w
          (PalPeg.ShadowedLocalFinal.heldAfter (Tc w.length) st) m →
        PalPeg.ShadowedLocalFinal.frozenAt w m →
        PalPeg.PhysicalDpCleanup.Enc w (PalPeg.LocalSysConcrete.absSC m) p → PhysFrozen w p)
    (hfrozenKeep : ∀ (w : List (Fin 2)) p, PhysFrozen w p →
      PhysFrozen w ((PalPeg.PhysicalDpCleanup.machine rest).apply blankM p none))
    (hfrozenQuiet : ∀ (w : List (Fin 2)) p, PhysFrozen w p →
      PalPeg.PhysicalReportTest.repW p.1
        (fun j => PalPeg.Local.readWin blankM macroRadius (p.2 j)) = false) :
    PegSeparation.RecognizedByTotalPEG PalPeg.PAL :=
  PalPeg.PhysicalReportTest.given_remainingCases_and_frozen rest
    (PalPeg.PhysicalPhaseLayers.cases_of_remaining_quiet rest hunhandled)
    PhysFrozen hfrozenEnter hfrozenKeep hfrozenQuiet

/-- info: 'PalPeg.PhysicalFinalResidual.given_unhandledTicks_and_frozen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms given_unhandledTicks_and_frozen

end PalPeg.PhysicalFinalResidual
