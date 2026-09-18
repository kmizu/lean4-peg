import PalPeg.CloseoutShiftWeak
import PalPeg.CloseoutShiftFinal

/-!
# `pal_in_peg_final29` — the false `hws` replaced by `ShiftLocalG`

`pal_in_peg_final27`'s `hws : ∀ w y, WatchShiftG … w y` is **false**
(`CloseoutPackRun32`: a watch born at `ChainStep.backDone` has `distance =
reset`).  Two independent weakenings land here:

* the trail bridge no longer touches it at all — `pal_in_peg_final5MG2T`
  (`CloseoutShiftFinal`) runs on `ChainPositionInvariant`;
* the run pack only ever needed `ShiftLocalG`, which `WatchShiftG` merely
  *implies* (`shiftLocalG_of_watchShiftG`) — `packRunR_MG27L`
  (`CloseoutShiftWeak`).

So this theorem's hypothesis is `∀ w y, ShiftLocalG … w y`, strictly weaker than
`hws`, plus `CloseoutPackRun34`'s four **guarded** branch hypotheses for the
trail side.  Of `ShiftLocalG`'s four fields, `move` is wave 7's `Extra7` payload
and already free on a run; `guard` / `coupled` / `ver` are the residue, and
`CloseoutPackRun34.ShiftLocalS` is the guarded form they can take.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutWeakFinal

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilTickArrive PalPeg.GalilLatchTracking PalPeg.GalilArriveChain
open PalPeg.GalilThrottledRun PalPeg.GalilThrottledRunGen PalPeg.GalilLedgerQ64
open PalPeg.GalilRunSkeleton PalPeg.GalilCheckpoints PalPeg.GalilTraceCost
open PalPeg.GalilOracleDischarge PalPeg.GalilOracleLocal PalPeg.GalilLexMeasure
open PalPeg.GalilInvPlus PalPeg.GalilInvPlus2 PalPeg.GalilOracleMC PalPeg.GalilOracleMC2
open PalPeg.GalilGlueBLeaves PalPeg.GalilBranchInvariants2 PalPeg.GalilSegmentConstruct
open PalPeg.GalilTruncTick PalPeg.GalilFinalAssembly PalPeg.GalilFinalAssembly2
open PalPeg.GalilFinalBaseNeed PalPeg.GalilFinalAssembly3 PalPeg.GalilOracleLeaves2
open PalPeg.GalilFinalAssembly4 PalPeg.GalilInvPlus3 PalPeg.CloseoutOracleI2
open PalPeg.CloseoutPackRun36 PalPeg.CloseoutStageCheck PalPeg.CloseoutStageBoot
open PalPeg.CloseoutPackRun PalPeg.CloseoutPackRun2 PalPeg.CloseoutPackRun3
open PalPeg.CloseoutPackRun5 PalPeg.CloseoutPackRun7 PalPeg.CloseoutPackRun8
open PalPeg.CloseoutPackRun9 PalPeg.CloseoutPackRun10 PalPeg.CloseoutPackRun11
open PalPeg.CloseoutPackRun12 PalPeg.CloseoutPackRun16 PalPeg.CloseoutPackRun18
open PalPeg.CloseoutPackRun19 PalPeg.CloseoutPackRun20 PalPeg.CloseoutPackRun21
open PalPeg.CloseoutPackRun23 PalPeg.CloseoutPackRun24 PalPeg.CloseoutPackRun29
open PalPeg.CloseoutPackRun30 PalPeg.CloseoutPackRun33 PalPeg.CloseoutPackRun35
open PalPeg.CloseoutPackRun26 PalPeg.CloseoutStageSupply
open PalPeg.CloseoutLPack PalPeg.CloseoutLPack2 PalPeg.CloseoutLPack3
open PalPeg.CloseoutLPack4 PalPeg.CloseoutLPack5 PalPeg.CloseoutLPack6
open PalPeg.GalilLookRefined PalPeg.CloseoutOracleI PalPeg.CloseoutLPack5
open PalPeg.CloseoutStageOracle PalPeg.CloseoutPackRun43 PalPeg.CloseoutPackRun45
open PalPeg.CloseoutPackRun46 PalPeg.CloseoutPreload37 PalPeg.CloseoutPackRun22
open PalPeg.CloseoutShiftLocalFree
open PalPeg.CloseoutStageFinal PalPeg.CloseoutExtraOracle PalPeg.CloseoutExtraFree
open PalPeg.CloseoutExtraFinal PalPeg.CloseoutShiftS PalPeg.CloseoutPackRun34
open PalPeg.CloseoutShiftLocalFree
open PalPeg.CloseoutStageFinal PalPeg.CloseoutExtraOracle PalPeg.CloseoutExtraFree
open PalPeg.CloseoutShiftS PalPeg.CloseoutPackRun34 PalPeg.CloseoutShiftLocalFree
open PalPeg.CloseoutShiftWeak PalPeg.CloseoutShiftFinal

/-- **`pal_in_peg_final27` with the false `hws` weakened to `ShiftLocalG`.** -/
theorem pal_in_peg_final29 (entry q : ℕ) (first : Fin 9)
    (hSP : ∀ (w : List (Fin 2)) (x : GalilScaffoldTop.State GalilVM),
      BigPack2MG7 centreC placeC entry q first w x →
      ScanNR x → ShiftPal centreC placeC entry q first w x.vm)
    (hsl : ∀ (w : List (Fin 2)) (y : GalilScaffoldTop.State GalilVM),
      ShiftLocalG centreC placeC entry q first w y)
    (hme : ∀ w : List (Fin 2), H_marksEntry' (PofC centreC placeC entry w) q first)
    (hor : ∀ w : List (Fin 2), 0 < w.length →
      CycleOracleMC3 (PofC centreC placeC entry w) q first w)
    (hC : H_realizeLIMG2' centreC placeC entry q first)
    (hfour : ∀ w : List (Fin 2), H_FourSemiperiodsLeDistance centreC placeC entry q first w)
    (hbgP : ∀ w : List (Fin 2), H_BackgroundLandingPayload centreC placeC entry q first w)
    (hmatchP : ∀ w : List (Fin 2), H_MatchLandingPayload centreC placeC entry q first w)
    (hsdP : ∀ w : List (Fin 2), H_ShiftExitPayload centreC placeC entry q first w) :
    RecognizedByTotalPEG PAL :=
  pal_in_peg_final5MG2T entry q first
    (h_bootIMG2S_of_bootIPack centreC placeC entry q first
      (fun w => h_shiftLocalG centreC placeC entry q first (raw := w))
      (bootIPack_of_parts centreC placeC entry q first h_lrepC
        (CloseoutPackRun6.h_bootShift centreC placeC entry q first)
        (CloseoutPackRun6.h_landShift centreC placeC entry q first)))
    (h_oracleIMG2S_of_MC3_P centreC placeC entry q first
      (fun w => packRunR_MG27L centreC placeC entry q first (hsl w) (hSP w) (hme w))
      (fun w => h_shiftLocalG centreC placeC entry q first (raw := w))
      hor)
    hC hfour hbgP hmatchP hsdP

#print axioms pal_in_peg_final29

end PalPeg.CloseoutWeakFinal
