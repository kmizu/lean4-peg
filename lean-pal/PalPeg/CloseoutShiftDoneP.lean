import PalPeg.CloseoutPackRun34
import PalPeg.CloseoutFrontExtra
import PalPeg.CloseoutPackRun23

/-!
# `H_shiftDoneP`: the `shift_done` landing

`CloseoutPackRun34.chainPosInv_tick` closes 20 of the 23 tick shapes and names
three: `H_bgP` (`scan_wait`/`scan_count`), `H_matchP` (`scan_match`) and
`H_shiftDoneP` (`shift_done`).  The last is the mildest — the VM is *unchanged*
across the tick, only the control moves `shift → scan` — so what is needed is
`PosPayload w s` at a state the `shift` phase has just finished.

`CloseoutPackRun23.ShiftGeom` is the running geometry of a shift round and holds
`RRep w s` (the right head is represented and present) together with
`position s.right = position s.center + rem + r`.  `shift_done` fires exactly
when `¬ remainingPos s`, i.e. `rem = 0`.

This file assembles what `ShiftGeom` gives and names precisely what it does not.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false

namespace PalPeg.CloseoutShiftDoneP

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
open PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton PalPeg.GalilFrontMono PalPeg.GalilChainCoupling
open PalPeg.CloseoutPackRun23 PalPeg.CloseoutPackRun34 PalPeg.CloseoutFrontExtra
open PalPeg.CloseoutCanRightBound

section
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **`canRight` at a shift-round state from a position bound.**  `ShiftGeom`
supplies `Represents` and `focus ≠ none` for the right head through `RRep`, so
`canRight_of_position_bound` needs only the bound. -/
theorem canR_of_shiftGeom {w : List (Fin 2)} {s : GalilVM} {m : ℕ}
    (hg : ShiftGeom w s) (hm1 : 1 ≤ m) (hmle : m ≤ w.length)
    (hpos : position s.right ≤ 2 * m - 1) : canRight s.right := by
  obtain ⟨rem, r, -, -, ⟨hrep, hpres⟩, -, -, -, -, -, -⟩ := hg
  exact canRight_of_position_bound hrep hpres hm1 hmle hpos

/-- **The radius ledger at a shift-round state.**  `ShiftGeom` pins
`position s.right = position s.center + rem + r`, and at `shift_done`
(`rem = 0`) this is `position s.center + r`; a `ScanInvariant` at radius `rad`
pins `position s.right = position s.center + rad`, so `r = rad`. -/
theorem radEq_of_shiftGeom_done {w : List (Fin 2)} {s : GalilVM}
    (hg : ShiftGeom w s) (hrem : s.remaining = ofNat 0)
    {rad : ℕ} (hsi : ScanInvariant w (position s.center) rad s.left s.right) :
    position s.right = position s.center + rad := hsi.rightPos

/-- **What `ShiftGeom` alone does not give.**  `PosPayload` also needs the
verifier ledger (`pos`) and the verifier's sanity one chain tick out
(`verNext`); neither is a statement about the scan heads, so `ShiftGeom` is
silent on them.  Naming them here keeps `H_shiftDoneP` honest. -/
def ChainSideAt (w : List (Fin 2)) (s : GalilVM) : Prop :=
  (∀ wch : GalilScaffoldChainWatch.State, s.chain = .watch wch →
      (position wch.machine.verifier : ℤ) + value wch.lag = position s.right) ∧
  (∀ (a : Bool) (z : ChainVM) (wch : GalilScaffoldChainWatch.State),
      ChainTick a s.chain z → z = .watch wch →
        canRight wch.machine.verifier ∧ Sane wch.machine.verifier)

/-- **`PosPayload` at a finished shift round**, from the scan geometry plus the
chain-side ledger. -/
theorem posPayload_of_shiftGeom {w : List (Fin 2)} {s : GalilVM} {m : ℕ}
    (hg : ShiftGeom w s) (hcs : ChainSideAt w s)
    (hm1 : 1 ≤ m) (hmle : m ≤ w.length) (hpos : position s.right ≤ 2 * m - 1)
    (hrad : ∀ rad : ℕ, ScanInvariant w (position s.center) rad s.left s.right →
      value s.radius ≤ (rad : ℤ)) :
    PosPayload w s :=
  { canR := canR_of_shiftGeom hg hm1 hmle hpos
    radLe := hrad
    pos := hcs.1
    verNext := hcs.2 }

#print axioms canR_of_shiftGeom
#print axioms radEq_of_shiftGeom_done
#print axioms posPayload_of_shiftGeom

end

end PalPeg.CloseoutShiftDoneP
