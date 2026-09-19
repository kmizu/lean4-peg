import PalPeg.PackedRun
import PalPeg.CloseoutLPack

/-!
# `CloseoutLPack2`: the pack by induction, and the shift half-bound by arithmetic

`CloseoutLPack.h_trailF_final` closes `H_trailF` from three named residuals:
`H_lpack`, `H_shiftHalf` and `H_shiftCanRight`.  This file replaces the first
two by strictly smaller statements.

What is **proved** here, unconditionally:

* `lpack_steps` / `h_lpack_of_tick` — **`H_lpack` is a one-step statement.**
  `LPack` holds at the boot state (`CloseoutLPack.lpack_boot`) and `PreTrace`
  supplies `st 0 = boot w` together with a `Tick` chain, so the whole trace
  statement `H_lpack` follows from the *tick* residual `LPackTick` by a plain
  induction on the tick index.  This is the `L`-analogue of
  `GalilLengthFloor.fpack_tick → fpack_steps`.
* `half_of_places` — **the arithmetic of the Galil half-bound.**  From
  `GalilCatchUpDistance.places_of_guard`'s `4·h ≤ distance` and a bound
  `distance ≤ 2·rad` one gets `2·h ≤ rad` over `ℕ`, with the `ℤ`/`ℕ` cast
  handled here once and for all.
* `h_shiftHalf_of_parts` — **`H_shiftHalf` from the pack plus two leaves.**
  The `ScanInvariant` component is read off `LPack.scanInv` (so it is no longer
  a separate hypothesis once `H_lpack` is available), and the numeric component
  is `H_shiftPlaces` below.
* `h_trailF_lpack2` / `h_trailF_C2` — `H_trailF` from `LPackTick`,
  `H_shiftScan`, `H_shiftPlaces` and `H_shiftCanRight`.

## The named residuals

* `LPackTick` — **NAMED**: `LPack` is preserved by one tick of
  `galilFrameS (PofC centre place entry w) q first` at delay `2048`.  This is
  all that is left of `H_lpack`.  Its hard corners are unchanged and are stated
  in `CloseoutLPack`: at a *mismatched* comparison the left head lands on
  `position L - 1` (off the origin only through `GalilLiveCentre.Live`), a
  `rewind` walk lowers the centre so `MInv` returns through
  `minv_after_fallback`, and `scanInv` after `shift_done` needs the new
  centre's palindrome radius (`GalilLiveCentreShift.leftmost_shift` plus
  `GalilPeriodCentre`), which is not tick-local.  Note the statement is a real
  reduction even so: it is quantified over *two states and one tick*, not over
  a trace.
* `H_shiftScan` — **NAMED**: at a shift entry the controller is in a
  non-replaying `scan` mode.  `compare` is a VM-level relation, so the
  controller mode is not recoverable from `compare`/`beginShiftVM'` alone; on
  the actual route the entry comes from the `scan_shift` constructor of
  `GalilScaffoldTop.Tick`, whose `hm : c.mode = .scan` and
  `h : c.replaying = true ∨ F.available s` carry exactly this.
* `H_shiftPlaces` — **NAMED**: at a shift entry, for the watching chain,
  `4 · periodLength wch ≤ distance` and `distance ≤ 2 · rad` for the radius of
  the scan invariant.  The first conjunct is
  `GalilCatchUpDistance.places_of_guard` (the guard's `0 ≤ margin`); the second
  is the chain/scan coupling of `distance_at_terminal`, i.e. the same `hdist`
  leaf that `GalilLengthFloor.budget_of_guard` already takes as a hypothesis.
  Together with `canRight` this is all that survives of `H_shiftHalf`.
* `H_shiftCanRight` — unchanged from `CloseoutLPack`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutLPack2

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open PalPeg.GalilThrottledRun PalPeg.GalilTrailProof PalPeg.GalilFinalAssembly
open PalPeg.CloseoutRadPack PalPeg.CloseoutRadPack2 PalPeg.CloseoutRadPack3
open PalPeg.CloseoutRadPack4 PalPeg.CloseoutLPack
open PalPeg.GalilRunSkeleton
open GalilScaffoldInputHead GalilScaffoldCounter

/-! ## 1. The tick residual, and `H_lpack` by induction -/

section Tick
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **(NAMED) `LPack` survives one tick.**  See the module docstring for the
corners. -/
def LPackTick : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → ∀ x y : State GalilVM,
    Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y →
    LPack w x.ctl x.vm → LPack w y.ctl y.vm

/-- **The pack along a pre-loaded trace, from the tick residual.**  Boot gives
the base case, `PreTrace.trace.tick` the step. -/
theorem lpack_steps (h : LPackTick centre place entry q first)
    (w : List (Fin 2)) (hw : 0 < w.length) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ)
    (hP : PreTrace centre place entry q first w st Tc) :
    ∀ i, i ≤ Tc w.length → LPack w (st i).ctl (st i).vm :=
  hP.trace.carried (Pk := fun z => LPack w z.ctl z.vm)
    (by rw [hP.start]; exact lpack_boot w)
    (fun i _ ht hp => h w hw (st i) (st (i + 1)) ht hp)

/-- **`H_lpack` from `LPackTick`.** -/
theorem h_lpack_of_tick (h : LPackTick centre place entry q first) :
    H_lpack centre place entry q first :=
  fun w hw st Tc hP i hi => lpack_steps centre place entry q first h w hw st Tc hP i hi

end Tick

#print axioms lpack_steps
#print axioms h_lpack_of_tick

/-! ## 2. The arithmetic of the Galil half-bound -/

/-- **`4h ≤ d` and `d ≤ 2r` give `2h ≤ r`.**  The cast bookkeeping of
`GalilCatchUpDistance.places_of_guard` (which lives in `ℤ`) against the
`ℕ`-valued radius of `ScanInvariant`, once. -/
theorem half_of_places {h : ℕ} {d : ℤ} {rad : ℕ}
    (h4 : 4 * (h : ℤ) ≤ d) (hd : d ≤ 2 * (rad : ℤ)) : 2 * h ≤ rad := by
  have : 4 * (h : ℤ) ≤ 2 * (rad : ℤ) := le_trans h4 hd
  have h2 : (2 * h : ℤ) ≤ (rad : ℤ) := by linarith
  exact_mod_cast h2

#print axioms half_of_places

/-! ## 3. The two shift-entry leaves, and `H_shiftHalf` -/

section Shift
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **(NAMED) the controller is in a non-replaying scan at a shift entry.** -/
def H_shiftScan : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTrace centre place entry q first w st Tc →
    ∀ i, i ≤ Tc w.length → ∀ s'' t'' : GalilVM,
      (galilFrameS (PofC centre place entry w) q first).compare (st i).vm s'' →
      beginShiftVM' s'' t'' →
      (st i).ctl.mode = Mode.scan ∧ (st i).ctl.replaying = false ∧
        GalilScaffoldChainVerifier.canRight (st i).vm.right

/-- **(NAMED) the place count and the chain/scan coupling at a shift entry.**
`4h ≤ distance` is `GalilCatchUpDistance.places_of_guard`; `distance ≤ 2·rad`
is the `hdist` leaf of `GalilLengthFloor.budget_of_guard`, here against the
radius of the scan invariant carried by `LPack`. -/
def H_shiftPlaces : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTrace centre place entry q first w st Tc →
    ∀ i, i ≤ Tc w.length → ∀ s'' t'' : GalilVM,
      (galilFrameS (PofC centre place entry w) q first).compare (st i).vm s'' →
      beginShiftVM' s'' t'' →
      ∀ wch : GalilScaffoldChainWatch.State, s''.chain = .watch wch →
        ∀ rad : ℕ,
          ScanInvariant w (position (st i).vm.center) rad (st i).vm.left (st i).vm.right →
          4 * (periodLength wch : ℤ) ≤ value wch.machine.control.distance ∧
            value wch.machine.control.distance ≤ 2 * (rad : ℤ)

/-- **`H_shiftHalf` from the pack and the two leaves.** -/
theorem h_shiftHalf_of_parts (hlp : H_lpack centre place entry q first)
    (hsc : H_shiftScan centre place entry q first)
    (hpl : H_shiftPlaces centre place entry q first) :
    H_shiftHalf centre place entry q first := by
  intro w hw st Tc hP i hi s'' t'' hcmp hb
  obtain ⟨hm, hr, hcan⟩ := hsc w hw st Tc hP i hi s'' t'' hcmp hb
  obtain ⟨rad, hscan⟩ := (hlp w hw st Tc hP i hi).scanInv hm hr
  refine ⟨rad, hscan, hcan, ?_⟩
  intro wch hwch
  obtain ⟨h4, hd⟩ := hpl w hw st Tc hP i hi s'' t'' hcmp hb wch hwch rad hscan
  exact half_of_places h4 hd

end Shift

#print axioms h_shiftHalf_of_parts

/-! ## 4. `H_trailF` from the refined residuals -/

section Final
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **`H_trailF` from `LPackTick`, `H_shiftScan`, `H_shiftPlaces` and
`H_shiftCanRight`.**  `H_lpack` (a trace statement) has become a tick
statement, and `H_shiftHalf`'s scan-invariant component has been absorbed into
the pack. -/
theorem h_trailF_lpack2 (htk : LPackTick centre place entry q first)
    (hsc : H_shiftScan centre place entry q first)
    (hpl : H_shiftPlaces centre place entry q first)
    (hcan : H_shiftCanRight centre place entry q first) :
    H_trailF centre place entry q first :=
  have hlp : H_lpack centre place entry q first :=
    h_lpack_of_tick centre place entry q first htk
  h_trailF_final centre place entry q first hlp
    (h_shiftHalf_of_parts centre place entry q first hlp hsc hpl) hcan

end Final

#print axioms h_trailF_lpack2

/-- **The concrete instance** at `centreC` / `placeC`. -/
theorem h_trailF_C2 (entry q : ℕ) (first : Fin 9)
    (htk : LPackTick PalPeg.GalilFinalAssembly2.centreC PalPeg.GalilFinalAssembly2.placeC
      entry q first)
    (hsc : H_shiftScan PalPeg.GalilFinalAssembly2.centreC PalPeg.GalilFinalAssembly2.placeC
      entry q first)
    (hpl : H_shiftPlaces PalPeg.GalilFinalAssembly2.centreC PalPeg.GalilFinalAssembly2.placeC
      entry q first)
    (hcan : H_shiftCanRight PalPeg.GalilFinalAssembly2.centreC PalPeg.GalilFinalAssembly2.placeC
      entry q first) :
    H_trailF PalPeg.GalilFinalAssembly2.centreC PalPeg.GalilFinalAssembly2.placeC entry q first :=
  h_trailF_lpack2 _ _ entry q first htk hsc hpl hcan

#print axioms h_trailF_C2

end PalPeg.CloseoutLPack2
