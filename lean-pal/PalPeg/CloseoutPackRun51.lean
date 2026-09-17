import PalPeg.CloseoutPackRun46
import PalPeg.CloseoutShiftLocalFree

/-!
# `pal_in_peg_final25` — `H_bootShift` and `H_landShift` discharged

Two of `pal_in_peg_final24`'s eleven hypotheses were never obligations at all:
`CloseoutPackRun6` already proves both as theorems.  `ShiftLocal` collapses at an
idle chain (`shiftLocal_of_chainIdle`, `CloseoutPackRun6:156`), `GalilBootVM.initVM0`
sets `chain := .idle`, and the only tick out of `GalilScaffoldController.initial`
is `Tick.init`, which keeps it idle.  So both hold for free.

This file supplies them, leaving **eight** hypotheses on the main path (`hsl` goes the same way).

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false

namespace PalPeg.CloseoutPackRun51

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
open PalPeg.GalilScaffoldChainInputSupply
open PegSeparation
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
open PalPeg.CloseoutPackRun46


/-- **`pal_in_peg_final24` with `hbs`/`hls` discharged.**  Eight hypotheses remain:
`hSP`, `hws`, `hee`, `het`, `hme`, `hsc`, `hor`, `hC`.  `hsl` is also free:
every `InvLPC` state has an idle chain, so `ShiftLocalG` is vacuous there
(`CloseoutShiftLocalFree.h_shiftLocalG`). -/
theorem pal_in_peg_final25 (entry q : ℕ) (first : Fin 9)
    (hSP : ∀ (w : List (Fin 2)) (x : GalilScaffoldTop.State GalilVM),
      BigPack2MG7 centreC placeC entry q first w x →
      ScanNR x → ShiftPal centreC placeC entry q first w x.vm)
    (hws : ∀ w : List (Fin 2), ∀ y : GalilScaffoldTop.State GalilVM, WatchShiftG centreC placeC entry q first w y)
    (hee : ∀ w : List (Fin 2), H_extraEntry7 centreC placeC entry w)
    (het : ∀ w : List (Fin 2), ∀ x y : GalilScaffoldTop.State GalilVM, Extra7 x →
      Tick (GalilScaffoldChainInputSupply.galilFrameS (PofC centreC placeC entry w) q first) 2048 x y → Extra7 y)
    (hme : ∀ w : List (Fin 2), H_marksEntry' (PofC centreC placeC entry w) q first)
    (hsc : ∀ w : List (Fin 2), H_stageScan centreC placeC entry q first w)
    (hor : ∀ w : List (Fin 2), 0 < w.length →
      CycleOracleMC3 (PofC centreC placeC entry w) q first w)
    (hC : H_realizeLIMG2' centreC placeC entry q first) :
    RecognizedByTotalPEG PAL :=
  pal_in_peg_final24 entry q first hSP hws hee het hme
    (fun w => CloseoutShiftLocalFree.h_shiftLocalG centreC placeC entry q first (raw := w))
    hsc hor
    (CloseoutPackRun6.h_bootShift centreC placeC entry q first)
    (CloseoutPackRun6.h_landShift centreC placeC entry q first)
    hC

#print axioms pal_in_peg_final25

end PalPeg.CloseoutPackRun51
