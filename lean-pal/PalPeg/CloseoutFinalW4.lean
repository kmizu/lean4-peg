import PalPeg.CloseoutFinalW3
import PalPeg.CloseoutMarksPack

/-!
# `pal_in_peg_final37` — `hme` gone: four hypotheses

`CloseoutMarksPack` showed that `hme` was never independent of `hpack`.  Its two
uses inside `packRunR_MW` both produce `MarksInv'`, which is a **field** of the
`ChainPack` bundle `hpack` already hands out; the bundle's premise
`ChainPosInv2` is available at the `InvLPC` origin (idle chain) and travels
along the run on the four supplies `H_bgP2` / `H_matchP2` / `H_shiftEntry2` /
`H_shiftDoneRad2`, which `final36` already derives from `hpack` itself.

So nothing replaces `hme`: the four supplies are computed once here and used
both for `packRunR_MWP` and for `pal_in_peg_final5MW3`.

Remaining: `hSP` (the `ShiftPal` move lemma), `hor` (`CycleOracleMC3`), `hC`
(local realization), `hpack` (the `ChainSide` residue).

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutFinalW4


open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open PalPeg.GalilThrottledRun PalPeg.GalilTrailProof PalPeg.GalilFinalAssembly
open PalPeg.GalilRunSkeleton PalPeg.GalilCheckpoints PalPeg.GalilTraceCost
open PalPeg.GalilOracleDischarge PalPeg.GalilOracleLocal
open PalPeg.GalilInvPlus PalPeg.GalilInvPlus2 PalPeg.GalilOracleMC PalPeg.GalilOracleMC2
open PalPeg.GalilFinalAssembly2 PalPeg.GalilFinalAssembly4
open PalPeg.CloseoutOracleI PalPeg.CloseoutOracleI2 PalPeg.GalilInvPlus3
open PalPeg.CloseoutPackRun PalPeg.CloseoutPackRun2 PalPeg.CloseoutPackRun3
open PalPeg.CloseoutPackRun5 PalPeg.CloseoutPackRun7 PalPeg.CloseoutPackRun8
open PalPeg.CloseoutPackRun9 PalPeg.CloseoutPackRun10 PalPeg.CloseoutPackRun11
open PalPeg.CloseoutPackRun12 PalPeg.CloseoutPackRun16 PalPeg.CloseoutPackRun18
open PalPeg.CloseoutPackRun19 PalPeg.CloseoutPackRun20 PalPeg.CloseoutPackRun21
open PalPeg.CloseoutPackRun23 PalPeg.CloseoutPackRun24 PalPeg.CloseoutPackRun26
open PalPeg.CloseoutPackRun29 PalPeg.CloseoutPackRun30 PalPeg.CloseoutPackRun33
open PalPeg.CloseoutPackRun35 PalPeg.CloseoutPackRun36 PalPeg.CloseoutPackRun43
open PalPeg.CloseoutPreload37 PalPeg.CloseoutPackRun22 PalPeg.CloseoutPackRun45
open PalPeg.CloseoutLPack PalPeg.CloseoutLPack2 PalPeg.CloseoutLPack3
open PalPeg.CloseoutLPack4 PalPeg.CloseoutLPack5 PalPeg.CloseoutLPack6
open GalilScaffoldInputHead GalilScaffoldCounter GalilScaffoldChainVerifier
open PalPeg.CloseoutPackRun46 PalPeg.CloseoutFrontExtra
open PalPeg.CloseoutExtraFree
open PalPeg.CloseoutShiftWeak
open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open PalPeg.GalilThrottledRun PalPeg.GalilTrailProof PalPeg.GalilFinalAssembly
open PalPeg.CloseoutRadPack PalPeg.CloseoutRadPack2 PalPeg.CloseoutRadPack3
open PalPeg.CloseoutRadPack4 PalPeg.CloseoutLPack PalPeg.CloseoutLPack2
open PalPeg.CloseoutLPack3 PalPeg.CloseoutLPack4 PalPeg.CloseoutLPack5
open PalPeg.CloseoutLPack6
open PalPeg.GalilRunSkeleton PalPeg.GalilCheckpoints PalPeg.GalilTraceCost
open PalPeg.GalilOracleDischarge PalPeg.GalilOracleLocal PalPeg.GalilLexMeasure
open PalPeg.GalilInvPlus PalPeg.GalilInvPlus2 PalPeg.GalilOracleMC PalPeg.GalilOracleMC2
open PalPeg.GalilLookRefined PalPeg.GalilFinalBaseNeed PalPeg.GalilFinalAssembly2
open PalPeg.GalilLedgerQ64 PalPeg.GalilLedgerAssembly PalPeg.GalilIntervalCost
open PalPeg.GalilLatchTracking PalPeg.GalilArriveChain PalPeg.GalilTickArrive
open PalPeg.GalilTruncTick PalPeg.GalilFinalAssembly4
open PalPeg.GalilTrailScan PalPeg.GalilTrailBudget PalPeg.GalilTrailChain
open PalPeg.GalilTrailAssembly PalPeg.GalilTrailRad PalPeg.GalilFrontMono
open PalPeg.CloseoutOracleI PalPeg.CloseoutOracleI2 PalPeg.GalilInvPlus3
open PalPeg.CloseoutPackRun PalPeg.CloseoutPackRun2 PalPeg.CloseoutPackRun3
open PalPeg.CloseoutPackRun5 PalPeg.CloseoutPackRun7 PalPeg.CloseoutPackRun8
open PalPeg.CloseoutPackRun9 PalPeg.CloseoutPackRun10 PalPeg.CloseoutPackRun11
open PalPeg.CloseoutPackRun12 PalPeg.CloseoutPackRun16 PalPeg.CloseoutPackRun18
open PalPeg.CloseoutPackRun19 PalPeg.CloseoutPackRun20 PalPeg.CloseoutPackRun21
open PalPeg.CloseoutPackRun23 PalPeg.CloseoutPackRun24 PalPeg.CloseoutPackRun26
open PalPeg.CloseoutPackRun29 PalPeg.CloseoutPackRun30 PalPeg.CloseoutPackRun33
open PalPeg.CloseoutPackRun35
open GalilScaffoldInputHead GalilScaffoldCounter GalilScaffoldChainVerifier
open PalPeg.CloseoutPackRun36 PalPeg.CloseoutPackW PalPeg.CloseoutStageCheck
open PalPeg.CloseoutCheckW PalPeg.CloseoutExtraOracle PalPeg.CloseoutExtraFree
open PalPeg.CloseoutFrontExtra PalPeg.CloseoutStageOracle PalPeg.CloseoutStageBoot
open PalPeg.CloseoutShiftS PalPeg.CloseoutPackRun34 PalPeg.GalilLookRefined
open PalPeg.CloseoutOracleW PalPeg.CloseoutCheckW PalPeg.CloseoutPackW
open PalPeg.CloseoutShiftFinal PalPeg.CloseoutShiftLocalFree
open PalPeg.CloseoutOracleW PalPeg.CloseoutCheckW PalPeg.CloseoutPackW
open PalPeg.CloseoutFinalW PalPeg.CloseoutShiftLocalFree
open PalPeg.CloseoutPackRun41 PalPeg.CloseoutPackRun44 PalPeg.CloseoutPackRun47
open PalPeg.CloseoutPackRun48 PalPeg.CloseoutShiftS2 PalPeg.CloseoutTrailS2
open PalPeg.CloseoutOracleW PalPeg.CloseoutCheckW PalPeg.CloseoutPackW
open PalPeg.CloseoutFinalW PalPeg.CloseoutShiftLocalFree
open PalPeg.CloseoutPackRun41 PalPeg.CloseoutPackRun44 PalPeg.CloseoutPackRun47
open PalPeg.CloseoutPackRun48 PalPeg.CloseoutShiftS2 PalPeg.CloseoutTrailS2
open PalPeg.CloseoutChainPack PalPeg.CloseoutWatchSupply PalPeg.CloseoutFinalS2
open PalPeg.CloseoutFinalPack

open PalPeg.CloseoutFinalW3 PalPeg.CloseoutMarksPack PalPeg.CloseoutPackRun41
open PalPeg.CloseoutShiftS2 PalPeg.CloseoutShiftLocalFree

/-- **`pal_in_peg_final36` with `hme` gone: four hypotheses.** -/
theorem pal_in_peg_final37 (entry q : ℕ) (first : Fin 9)
    (hSP : ∀ (w : List (Fin 2)) (x : GalilScaffoldTop.State GalilVM),
      BigPack2MG7W centreC placeC entry q first w x →
      ScanNR x → ShiftPal centreC placeC entry q first w x.vm)
    (hor : ∀ w : List (Fin 2), 0 < w.length →
      CycleOracleMC3 (PofC centreC placeC entry w) q first w)
    (hC : H_realizeLIMW' centreC placeC entry q first)
    (hpack : ∀ (w : List (Fin 2)) (c : Control) (s : GalilVM),
      ChainPosInv2 w c s → ChainPack q first w c s)
    :
    RecognizedByTotalPEG PAL := by
  have hbgP : ∀ w : List (Fin 2), H_bgP2 centreC placeC entry q first w := fun w =>
    h_bgP2_of_chainPack centreC placeC entry q first (hpack w)
      (bgStartP2_of_chainPack centreC placeC entry q first (hpack w)
        (scanBudget_of_chainPack centreC placeC entry q first (hpack w)))
  have hmatchP : ∀ w : List (Fin 2), H_matchP2 centreC placeC entry q first w := fun w =>
    h_matchP2_of_target centreC placeC entry q first
      (h_matchRes2_of_chainPack centreC placeC entry q first (hpack w)
        (scanBudget_of_chainPack centreC placeC entry q first (hpack w)))
  have hentry : ∀ w : List (Fin 2), H_shiftEntry2 centreC placeC entry q first w := fun w =>
    h_shiftEntry2_of_target centreC placeC entry q first
      (h_shiftRes2_of_chainPack centreC placeC entry q first (hpack w)
        (scanBudget_of_chainPack centreC placeC entry q first (hpack w)))
  have hsdP : ∀ w : List (Fin 2), H_shiftDoneRad2 centreC placeC entry q first w := fun w =>
    h_shiftDoneRad2_of_chainPack centreC placeC entry q first (hpack w)
  exact pal_in_peg_final5MW3 entry q first
    (h_bootIMW_of_bootIPack centreC placeC entry q first
      (fun w => h_shiftLocalG centreC placeC entry q first (raw := w))
      (bootIPack_of_parts centreC placeC entry q first h_lrepC
        (CloseoutPackRun6.h_bootShift centreC placeC entry q first)
        (CloseoutPackRun6.h_landShift centreC placeC entry q first)))
    (h_oracleIMW_of_MC3_W centreC placeC entry q first
      (fun w => packRunR_MWP centreC placeC entry q first (hSP w)
        (hbgP w) (hmatchP w) (hentry w) (hsdP w) (hpack w))
      (fun w => h_shiftLocalG centreC placeC entry q first (raw := w))
      hor)
    hC hbgP hmatchP hentry hsdP
    (fun w st hst => by rw [hst]; exact chainPosInv2_of_idle (boot_chain_idle w))
    (fun w => hpack w)

#print axioms pal_in_peg_final37

end PalPeg.CloseoutFinalW4
