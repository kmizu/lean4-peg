import PalPeg.CloseoutPackRun16

/-!
# `CloseoutPackRun19`: the two `ScanInvariant` contracts of `BigResid6`

`CloseoutPackRun11.BigResid6` has two contracts that ask for the fixed-centre
scan geometry `ScanInvariant w (position C) r L R`:

* `rScanInvR` — at every `scan` state;
* `rShiftDoneScan` — at every `shift` state with no remaining position.

The pack `BigPack2M` carries the geometry in exactly one place,
`LPackM.scanGeom`, and that field is guarded by `replaying = false`
(`CloseoutPackRun10`).  So:

* §1 the **non-replaying half of `rScanInvR` is free**
  (`scanInvR_nonreplay_of_packM`, the `BigPack2M` form of
  `CloseoutPackRun4.scanInvR_of_nonreplaying`);
* §2 the **replaying half** is the single named hypothesis
  `H_scanGeomReplay` — the field `LPackM.scanGeom` with its
  `replaying = false` guard dropped.  Nothing else in `BigPack2M` mentions
  the heads during a replay: `FrontPack.replayPos`/`frontier`/`rest` pin
  `replay` and `position R`, not `L` and `C`, and `ShiftLocal`/`Extra'` are
  stated at `replaying = false` or off `scan`.
* §3 the **shift exit** is the single named hypothesis `H_shiftDoneGeom` —
  a new field `shiftGeom` of `LPackM`; `Extra'.cand` gives a `Candidate` for
  the window at `shift`, but no field records the heads at the exit (the
  fact is `GalilScaffoldChainReadOrigin.reshift_palindrome` at the state where
  `remainingPos` first fails, a whole-round statement).
* §4 `rScanInvR_of_pack` / `rShiftDoneScan_of_pack` — the two contracts as
  theorems under those hypotheses, and `bigResid6_of_leaves` assembling
  `BigResid6` from them plus the four remaining contracts.

## Honest status

Standard axioms only; unconditional `PAL ∈ PEG` remains open.  The two
hypotheses are not proved here; `BigPack2M` does not carry them.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPackRun19

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open PalPeg.CloseoutLPack PalPeg.CloseoutLPack5
open PalPeg.CloseoutPackRun10 PalPeg.CloseoutPackRun11
open PalPeg.GalilRunSkeleton PalPeg.GalilTrailSane
open GalilScaffoldInputHead GalilScaffoldCounter

section Geom
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-! ## 1. The non-replaying half of `rScanInvR` is free -/

/-- **`rScanInvR` off a replay**, read straight off `LPackM.scanGeom`. -/
theorem scanInvR_nonreplay_of_packM {w : List (Fin 2)} {x : State GalilVM}
    (hx : BigPack2M centre place entry q first w x)
    (hm : x.ctl.mode = Mode.scan) (hnr : x.ctl.replaying = false) :
    ∃ r, ScanInvariant w (position x.vm.center) r x.vm.left x.vm.right :=
  hx.ipackM.pack.scanGeom hm hnr

/-! ## 2. The replaying half: one named hypothesis -/

/-- **(NAMED) the scan geometry during a replay.**  This is `LPackM.scanGeom`
with the `replaying = false` guard dropped; it is the field of `LPackM` that
should carry it. -/
def H_scanGeomReplay (w : List (Fin 2)) : Prop :=
  ∀ x : State GalilVM, BigPack2M centre place entry q first w x →
    x.ctl.mode = Mode.scan → x.ctl.replaying = true →
    ∃ r, ScanInvariant w (position x.vm.center) r x.vm.left x.vm.right

/-! ## 3. The shift exit: one named hypothesis -/

/-- **(NAMED) the scan geometry at the shift exit.**  A new field `shiftGeom`
of `LPackM` should carry it (`ShiftLocal` and `Extra'.cand` speak about the
shift *entry* and the window, not the heads at the exit). -/
def H_shiftDoneGeom (w : List (Fin 2)) : Prop :=
  ∀ x : State GalilVM, BigPack2M centre place entry q first w x →
    x.ctl.mode = Mode.shift →
    ¬ (galilFrameS (PofC centre place entry w) q first).remainingPos x.vm →
    ∃ r, ScanInvariant w (position x.vm.center) r x.vm.left x.vm.right

/-! ## 4. The two contracts -/

/-- **`BigResid6.rScanInvR`** under `H_scanGeomReplay`: the non-replaying case
is `scanInvR_nonreplay_of_packM`, the replaying case is the hypothesis. -/
theorem rScanInvR_of_pack {w : List (Fin 2)} (hR : H_scanGeomReplay centre place entry q first w) :
    ∀ x : State GalilVM, BigPack2M centre place entry q first w x →
      x.ctl.mode = Mode.scan →
      ∃ r, ScanInvariant w (position x.vm.center) r x.vm.left x.vm.right := by
  intro x hx hm
  cases hrep : x.ctl.replaying with
  | false => exact scanInvR_nonreplay_of_packM centre place entry q first hx hm hrep
  | true => exact hR x hx hm hrep

/-- **`BigResid6.rShiftDoneScan`** is exactly `H_shiftDoneGeom`. -/
theorem rShiftDoneScan_of_pack {w : List (Fin 2)}
    (hS : H_shiftDoneGeom centre place entry q first w) :
    ∀ x : State GalilVM, BigPack2M centre place entry q first w x →
      x.ctl.mode = Mode.shift →
      ¬ (galilFrameS (PofC centre place entry w) q first).remainingPos x.vm →
      ∃ r, ScanInvariant w (position x.vm.center) r x.vm.left x.vm.right :=
  hS

/-- `BigResid6` from the two geometry hypotheses and the four other contracts. -/
theorem bigResid6_of_leaves {w : List (Fin 2)}
    (hR : H_scanGeomReplay centre place entry q first w)
    (hS : H_shiftDoneGeom centre place entry q first w)
    (hInit : ∀ x : State GalilVM, BigPack2M centre place entry q first w x →
      x.ctl.mode = Mode.init → ∀ t : GalilVM,
      (galilFrameS (PofC centre place entry w) q first).init x.vm t →
      LPackM w {x.ctl with mode := Mode.scan, output := true} t)
    (hChoose : ∀ x : State GalilVM, BigPack2M centre place entry q first w x →
      x.ctl.mode = Mode.choose → x.ctl.odd = true → ∀ t : GalilVM,
      (galilFrameS (PofC centre place entry w) q first).choose x.vm t →
      GalilScaffoldInputTrace.Represents t.left.head w ∧ t.left.head.focus ≠ none)
    (hReplay : ∀ x : State GalilVM, BigPack2M centre place entry q first w x →
      x.ctl.mode = Mode.replayStart → ∀ (t : GalilVM) (o : Bool),
      (galilFrameS (PofC centre place entry w) q first).replayStart x.vm t →
      LPackM w {x.ctl with mode := Mode.scan, clock := 2048, output := o, replaying := (galilFrameS (PofC centre place entry w) q first).replayPos t} t)
    (hShiftNext : ∀ x y : State GalilVM, BigPack2M centre place entry q first w x →
      Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y →
      SoundScanNR w y → ShiftLocal centre place entry q first w y) :
    BigResid6 centre place entry q first w where
  rInitPackM := hInit
  rScanInvR := rScanInvR_of_pack centre place entry q first hR
  rShiftDoneScan := rShiftDoneScan_of_pack centre place entry q first hS
  rChoosePackL := hChoose
  rReplayPackM := hReplay
  rShiftNext := hShiftNext

end Geom

#print axioms scanInvR_nonreplay_of_packM
#print axioms rScanInvR_of_pack
#print axioms rShiftDoneScan_of_pack
#print axioms bigResid6_of_leaves

end PalPeg.CloseoutPackRun19
