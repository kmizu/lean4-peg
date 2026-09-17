import PalPeg.CloseoutPackRun30
import PalPeg.CloseoutPackRun29

/-!
# `CloseoutPackRun33`: `BigResid6G` from `LPackM2` on the guarded pack

`CloseoutPackRun29.bigResid6_of_lpackM2` builds `BigResid6` from
`∀ x, BigPack2M x → LPackM2 …` and `∀ y, WatchShift y`.  The five non-shift
contracts (Run19/20/21/23) read only `LPackM2` at the pack state and
`AuxPack.front.notInit`; none reads `ShiftLocal.mode`.  So they restate
verbatim over `BigPack2MG`, and `rShiftNext` is
`CloseoutPackRun30.rShiftNextMG_of_watchShiftG`.  `pal_in_peg_final18` is
`pal_in_peg_final17` with `BigResid6G` replaced by those two hypotheses.

Standard axioms only; unconditional `PAL ∈ PEG` remains open.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPackRun33

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation
open PalPeg.CloseoutLPack PalPeg.CloseoutLPack5
open PalPeg.CloseoutPackRun10 PalPeg.CloseoutPackRun11 PalPeg.CloseoutPackRun16
open PalPeg.CloseoutPackRun19 PalPeg.CloseoutPackRun20 PalPeg.CloseoutPackRun21
open PalPeg.CloseoutPackRun23 PalPeg.CloseoutPackRun24 PalPeg.CloseoutPackRun26
open PalPeg.CloseoutPackRun30
open PalPeg.GalilTrailProof PalPeg.GalilFinalAssembly PalPeg.GalilFinalAssembly2
open PalPeg.GalilFinalAssembly4 PalPeg.GalilOracleMC PalPeg.GalilOracleMC2
open PalPeg.GalilInvPlus PalPeg.GalilInvPlus3 PalPeg.GalilLookRefined PalPeg.GalilFinalBaseNeed
open PalPeg.CloseoutOracleI PalPeg.CloseoutOracleI2 PalPeg.CloseoutPackRun
open PalPeg.CloseoutPackRun2 PalPeg.CloseoutPackRun3 PalPeg.CloseoutPackRun5
open PalPeg.CloseoutPackRun7 PalPeg.CloseoutPackRun8 PalPeg.CloseoutPackRun9
open PalPeg.CloseoutPackRun12 PalPeg.CloseoutPackRun18 PalPeg.GalilTrailRad
open PalPeg.GalilRunSkeleton PalPeg.GalilInvPlus2
open GalilScaffoldInputHead GalilScaffoldCounter

section PiecesG
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- `rScanInvR` over `BigPack2MG` (`CloseoutPackRun23.scanGeomReplay_of_lpackM2`
+ `LPackM.scanGeom`). -/
theorem rScanInvRG_of_lpackM2 {w : List (Fin 2)}
    (hall : ∀ x : State GalilVM, BigPack2MG centre place entry q first w x → LPackM2 w x.ctl x.vm) :
    ∀ x : State GalilVM, BigPack2MG centre place entry q first w x →
      x.ctl.mode = Mode.scan →
      ∃ r, ScanInvariant w (position x.vm.center) r x.vm.left x.vm.right := by
  intro x hx hm
  cases hrep : x.ctl.replaying with
  | false => exact hx.ipackM.pack.scanGeom hm hrep
  | true => exact (hall x hx).scanGeomR hm hrep

/-- `rShiftDoneScan` over `BigPack2MG` (`CloseoutPackRun23.shiftDoneGeom_of_lpackM2`). -/
theorem rShiftDoneScanG_of_lpackM2 {w : List (Fin 2)}
    (hall : ∀ x : State GalilVM, BigPack2MG centre place entry q first w x → LPackM2 w x.ctl x.vm) :
    ∀ x : State GalilVM, BigPack2MG centre place entry q first w x →
      x.ctl.mode = Mode.shift →
      ¬ (galilFrameS (PofC centre place entry w) q first).remainingPos x.vm →
      ∃ r, ScanInvariant w (position x.vm.center) r x.vm.left x.vm.right := by
  intro x hx hm hnp
  have hz : positive x.vm.remaining = false := by
    cases hpos : positive x.vm.remaining with
    | false => rfl
    | true => exact absurd (Or.inl hpos) hnp
  exact shiftGeom_exit ((hall x hx).shiftGeom hm) hz

/-- `rInitPackM` over `BigPack2MG` (`CloseoutPackRun21.rInitPackM_of_pack`). -/
theorem rInitPackMG_of_pack {w : List (Fin 2)} :
    ∀ x : State GalilVM, BigPack2MG centre place entry q first w x →
      x.ctl.mode = Mode.init → ∀ t : GalilVM,
      (galilFrameS (PofC centre place entry w) q first).init x.vm t →
      LPackM w {x.ctl with mode := Mode.scan, output := true} t :=
  fun _ hx hm _ _ => absurd hm hx.aux.front.notInit

/-- `rChoosePackL` over `BigPack2MG` (`CloseoutPackRun20.rChoosePackL_of_pack`
+ `CloseoutPackRun23.rrepChoose_of_lpackM2`). -/
theorem rChoosePackLG_of_lpackM2 {w : List (Fin 2)}
    (hall : ∀ x : State GalilVM, BigPack2MG centre place entry q first w x → LPackM2 w x.ctl x.vm) :
    ∀ x : State GalilVM, BigPack2MG centre place entry q first w x →
      x.ctl.mode = Mode.choose → x.ctl.odd = true → ∀ t : GalilVM,
      (galilFrameS (PofC centre place entry w) q first).choose x.vm t →
      GalilScaffoldInputTrace.Represents t.left.head w ∧ t.left.head.focus ≠ none := by
  intro x hx hm _ t ht
  rw [choose_left_eq_right (PofC centre place entry w) q first ht]
  exact (hall x hx).rrep (by rw [hm]; decide)

/-- `rReplayPackM` over `BigPack2MG` (`CloseoutPackRun21.rReplayPackM_of_pack`
+ `CloseoutPackRun23.centreReplay_of_lpackM2`). -/
theorem rReplayPackMG_of_lpackM2 {w : List (Fin 2)}
    (hall : ∀ x : State GalilVM, BigPack2MG centre place entry q first w x → LPackM2 w x.ctl x.vm) :
    ∀ x : State GalilVM, BigPack2MG centre place entry q first w x →
      x.ctl.mode = Mode.replayStart → ∀ (t : GalilVM) (o : Bool),
      (galilFrameS (PofC centre place entry w) q first).replayStart x.vm t →
      LPackM w {x.ctl with mode := Mode.scan, clock := 2048, output := o, replaying := (galilFrameS (PofC centre place entry w) q first).replayPos t} t :=
  fun x hx hm _ _ h =>
    lpackM_replayStart_of_centreRep centre place entry q first
      ((hall x hx).centreRep (Or.inr hm)) h

/-- **`BigResid6G` from `LPackM2` at every guarded-pack state and `WatchShiftG`.** -/
theorem bigResid6G_of_lpackM2 {w : List (Fin 2)}
    (hall : ∀ x : State GalilVM, BigPack2MG centre place entry q first w x → LPackM2 w x.ctl x.vm)
    (hws : ∀ y : State GalilVM, WatchShiftG centre place entry q first w y) :
    BigResid6G centre place entry q first w where
  rInitPackM := rInitPackMG_of_pack centre place entry q first
  rScanInvR := rScanInvRG_of_lpackM2 centre place entry q first hall
  rShiftDoneScan := rShiftDoneScanG_of_lpackM2 centre place entry q first hall
  rChoosePackL := rChoosePackLG_of_lpackM2 centre place entry q first hall
  rReplayPackM := rReplayPackMG_of_lpackM2 centre place entry q first hall
  rShiftNext := rShiftNextMG_of_watchShiftG centre place entry q first hws

end PiecesG

#print axioms bigResid6G_of_lpackM2

/-- **`pal_in_peg_final17` with `BigResid6G` replaced by `LPackM2` on the
guarded pack and `WatchShiftG`.** -/
theorem pal_in_peg_final18 (entry q : ℕ) (first : Fin 9)
    (hall : ∀ w : List (Fin 2), ∀ x : State GalilVM,
      BigPack2MG centreC placeC entry q first w x → LPackM2 w x.ctl x.vm)
    (hws : ∀ w : List (Fin 2), ∀ y : State GalilVM, WatchShiftG centreC placeC entry q first w y)
    (hee : ∀ w : List (Fin 2), H_extraEntry3 centreC placeC entry w)
    (het : ∀ w : List (Fin 2), H_extraTick3 centreC placeC entry q first w)
    (hme : ∀ w : List (Fin 2), H_marksEntry' (PofC centreC placeC entry w) q first)
    (hsl : ∀ w : List (Fin 2), H_shiftLocalG centreC placeC entry q first w)
    (hsc : ∀ w : List (Fin 2), H_stageScan centreC placeC entry q first w)
    (hor : ∀ w : List (Fin 2), 0 < w.length →
      CycleOracleMC3 (PofC centreC placeC entry w) q first w)
    (hbs : H_bootShift centreC placeC entry q first)
    (hls : H_landShift centreC placeC entry q first)
    (hC : H_realizeLIMG' centreC placeC entry q first) :
    RecognizedByTotalPEG PAL :=
  pal_in_peg_final17 entry q first
    (fun w => bigResid6G_of_lpackM2 centreC placeC entry q first (hall w) (hws w))
    hee het hme hsl hsc hor hbs hls hC

#print axioms pal_in_peg_final18

end PalPeg.CloseoutPackRun33
