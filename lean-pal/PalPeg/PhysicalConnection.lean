import PalPeg.PhysicalContract
import PalPeg.PalInPegUnconditional

/-!
# Conditional final connection for the fixed physical witness

This module checks the final consumer using the existing abstract contracts.
It is deliberately downstream of `PhysicalContract`: concrete machine modules
may import the contract without importing the unfinished target theorem.
-/
set_option autoImplicit false

namespace PalPeg.PhysicalContract
open PalPeg PegSeparation
open PalPeg.GalilScaffoldTop
open PalPeg.Program (STape)
open PalPeg.GalilScaffoldChainInputSupply (GalilVM)
open PalPeg.GalilFinalAssembly2 (centreC placeC)
open PalPeg.Local (LocalStep)

/-- Conditional type-check of the final connection, with all three abstract
contracts supplied at 0 / 1 / 0. The remaining input is exactly `Obligations`. -/
theorem given_obligations {Q Γ : Type} {t K : ℕ} [Fintype Q] [DecidableEq Q] [Fintype Γ] [DecidableEq Γ]
    (L0 : LocalStep (Fin 2) Q Γ t K) (blankSymbol : Γ) (q0 : Q) (repQ outQ : Q → Bool)
    (Enc : List (Fin 2) → State GalilVM → Q × (Fin t → STape Γ) → Prop)
    (PhysFrozen : List (Fin 2) → Q × (Fin t → STape Γ) → Prop)
    (htape : 0 < t) (h : Obligations L0 blankSymbol q0 repQ outQ Enc PhysFrozen) :
    RecognizedByTotalPEG PAL := by
  exact PalPeg.ShadowedLocalFinal.given_physicalMachine_indexed (spare := 0)
    0 1 0 (by decide) (by decide) (by decide) (by decide) (by decide)
    PalPeg.PalInPeg.cycleOracleOnPackedRun
    (fun w st Tc hPreTraceIMW =>
      PalPeg.BranchSupply.scanLandingObligations_alongTrace_of_matchRest centreC placeC 0 1 0
        hPreTraceIMW
        (PalPeg.PalInPeg.obligation_shiftPalAlongTrace 0 1 0 w st Tc hPreTraceIMW)
        (PalPeg.BranchSupply.shiftExitLedgerAt_alongTrace centreC placeC 0 1 0
          hPreTraceIMW (PalPeg.BranchSupply.marksInv_alongTrace_ofPreTrace centreC placeC 0 1 0 (by decide)
            hPreTraceIMW.base.pre))
        (PalPeg.BranchSupply.marksInv_alongTrace_ofPreTrace centreC placeC 0 1 0 (by decide)
          hPreTraceIMW.base.pre)
        (PalPeg.BranchSupply.matchRest_alongTrace centreC placeC 0 1 0 hPreTraceIMW
          (PalPeg.BranchSupply.marksInv_alongTrace_ofPreTrace centreC placeC 0 1 0 (by decide)
            hPreTraceIMW.base.pre)))
    (fun w st Tc hw hPreTraceIMW =>
      PalPeg.BranchSupply.chainVerifierSupply_alongTrace centreC placeC 0 1 0 hw hPreTraceIMW
        (PalPeg.BranchSupply.marksInv_alongTrace_ofPreTrace centreC placeC 0 1 0 (by decide)
          hPreTraceIMW.base.pre)
        (hPreTraceIMW.base.tc1 ▸ hPreTraceIMW.base.pre.mono 1 w.length hw le_rfl))
    L0 blankSymbol q0 repQ outQ htape Enc h.hencInit h.hforwardTick h.hforwardFeed
    PhysFrozen h.hfrozenEnter h.hfrozenKeep h.hfrozenQuiet h.hencRep h.hencOut

/-- info: 'PalPeg.PhysicalContract.given_obligations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms given_obligations

end PalPeg.PhysicalContract
