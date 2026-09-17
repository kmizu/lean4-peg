import PalPeg.CloseoutExtraOracle
import PalPeg.CloseoutStageFinal

/-!
# `pal_in_peg_final27` — `hee` and `het` gone: **five** hypotheses

`pal_in_peg_final26` has seven.  Two of them, `hee` (`H_extraEntry7`) and `het`
(the `Extra7` tick), exist for one purpose: to build `packRunR_MG27`'s
`hprefix`, i.e. `canRight` at every scan / non-replaying state of the run.

That bound travels on its own.  `GalilRunTrace.front s = position s.right +
value s.replay` is monotone along any `CentreLive` run
(`GalilFrontMono.front_stepsAll_mono`), and `FrontPack.rest` makes a
non-replaying state satisfy `s.replay = reset`, hence `front s = position
s.right` there.  So for any `x` in a run whose exit `y` is non-replaying and
carries the cycle's bound,

```
position x.right = front x ≤ front y = position y.right ≤ 2*m-1
```

and `CloseoutCanRightBound.canRight_of_position_bound` finishes.  The right
head's own monotonicity — the 34-case `Tick` analysis — is never needed.

The two remaining inputs of `extra7_of_bound` (`Represents … w`, `focus ≠ none`)
come from `LPackM.scanGeom`'s `ScanInvariant`, which is available exactly where
`Extra7` speaks.  And the induction's circularity (`Extra7 (g (n+1))` needs the
pack being built) is broken by `bigPack2MG7''_tickE`, which takes the `Extra7` as
a function of that pack.

Five hypotheses remain: `hSP`, `hws`, `hme`, `hor`, `hC`.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutExtraFinal

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
open PalPeg.CloseoutShiftLocalFree

/-- **`pal_in_peg_final26` with `hee`/`het` gone: five hypotheses.** -/
theorem pal_in_peg_final27 (entry q : ℕ) (first : Fin 9)
    (hSP : ∀ (w : List (Fin 2)) (x : GalilScaffoldTop.State GalilVM),
      BigPack2MG7 centreC placeC entry q first w x →
      ScanNR x → ShiftPal centreC placeC entry q first w x.vm)
    (hws : ∀ w : List (Fin 2), ∀ y : GalilScaffoldTop.State GalilVM,
      WatchShiftG centreC placeC entry q first w y)
    (hme : ∀ w : List (Fin 2), H_marksEntry' (PofC centreC placeC entry w) q first)
    (hor : ∀ w : List (Fin 2), 0 < w.length →
      CycleOracleMC3 (PofC centreC placeC entry w) q first w)
    (hC : H_realizeLIMG2' centreC placeC entry q first) :
    RecognizedByTotalPEG PAL :=
  pal_in_peg_final5MG2S entry q first
    (h_bootIMG2S_of_bootIPack centreC placeC entry q first
      (fun w => h_shiftLocalG centreC placeC entry q first (raw := w))
      (bootIPack_of_parts centreC placeC entry q first h_lrepC
        (CloseoutPackRun6.h_bootShift centreC placeC entry q first)
        (CloseoutPackRun6.h_landShift centreC placeC entry q first)))
    (h_oracleIMG2S_of_MC3_P centreC placeC entry q first
      (fun w => packRunR_MG27P centreC placeC entry q first (hws w) (hSP w) (hme w))
      (fun w => h_shiftLocalG centreC placeC entry q first (raw := w))
      hor)
    hC

#print axioms pal_in_peg_final27

end PalPeg.CloseoutExtraFinal
