import PalPeg.CloseoutRadPack4

/-!
# `LPack`: the left-head carrier, and two sharper residuals

`CloseoutRadPack4.h_trailF_C'` closes `H_trailF` from three named hypotheses:
`H_shiftEntry` (`CloseoutRadPack3`), `H_leftLive` (`CloseoutRadPack2`) and
`H_shiftVerSane` (`CloseoutRadPack4`).  This file is the left-head analogue of
`GalilCentreLive.CPack` / `cpack_tick`, and it replaces two of the three by
strictly weaker statements.

What is **proved** here, unconditionally:

* `pos_of_rep` / `leftLive_of_pos` — `LeftLive` is exactly `0 < position L`,
  which is exactly presence of a represented left head.
* `compare_heads` — a comparison moves `L` one place left, `R` one place right
  and leaves `C` alone (both the matched and the mismatched landing).
* `shiftBud_of_scanInv` — **the whole arithmetic of `H_shiftEntry`.**  From
  `ScanInvariant w C rad L R` at the comparison source, `canRight R`, and the
  Galil half-bound `2 * periodLength wch ≤ rad`, the landing of `beginShiftVM`
  satisfies `ShiftBud`: the heads become `C - rad - 1` and `C + rad + 1`, and
  `remaining = ofNat h`, so `L + 2h + 1 ≤ C` and `C + h + 1 ≤ R` are `2h ≤ rad`.
* `saneVer_beginShift` — **the whole of `H_shiftVerSane` at one entry.**
  `beginShiftVM` applies `GalilScaffoldChainWatch.immediate`, whose verifier is
  one right move of the watching verifier, so `GalilFrontMono.right_sane`
  closes it from the verifier's own `canRight` and `Sane`.
* `LPack` / `leftLive_of_lpack` / `lpack_boot` — the carrier (left head
  represented and present off `init`; the scan invariant in a non-replaying
  scan; `MInv` off `init`), `LeftLive` read off it, and its boot instance.
* `h_shiftEntry_of_half`, `h_shiftVerSane_of_canRight`, `h_leftLive_of_lpack`,
  and `h_trailF_final` / `h_trailF_C''` — `H_trailF` from the three residuals
  below.

## The named residuals

* `H_lpack` — **NAMED**: the pack along every pre-loaded trace.  This is
  `H_leftLive` strengthened to what a tick induction would carry.  Its corners
  are the ones `CPack` never meets: at a *mismatched* comparison `L` lands on
  `position L - 1`, off the origin only because `GalilLiveCentre.Live` carries
  `position R < 2 * position C`; and a `rewind` walk lowers the centre, so
  `MInv` has to come back through `minv_after_fallback`.  Note that a full
  `lpack_tick` cannot re-establish `scanInv` after `shift_done`: the shift
  moves `C` by one and `L` by two per unit, and the new centre's palindrome
  radius is not a tick-local fact.
* `H_shiftHalf` — **NAMED**: the scan invariant at the comparison source
  together with `2 * periodLength wch ≤ rad`.  Strictly weaker than
  `H_shiftEntry`, whose arithmetic is now discharged; the intended proof is
  `GalilCatchUpDistance.places_of_guard` (`4h ≤ distance`) plus the chain/scan
  coupling that turns `distance` into the radius.
* `H_shiftCanRight` — **NAMED**: `canRight` and `Sane` of the watching chain's
  own verifier at a shift entry.  Strictly weaker than `H_shiftVerSane`, whose
  `Sane`-transport is now discharged.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutLPack

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open PalPeg.GalilThrottledRun PalPeg.GalilTrailProof PalPeg.GalilFinalAssembly
open PalPeg.CloseoutRadPack PalPeg.CloseoutRadPack2 PalPeg.CloseoutRadPack3
open PalPeg.CloseoutRadPack4
open PalPeg.GalilRunSkeleton
open GalilScaffoldInputHead GalilScaffoldCounter

/-! ## 1. Positivity of a represented head -/

theorem pos_of_rep {w : List (Fin 2)} {p : PlaceHead}
    (hh : GalilScaffoldInputTrace.Represents p.head w) (hp : p.head.focus ≠ none) :
    0 < position p := by
  have h := (represented_position p.head w hh hp).1
  unfold position
  split <;> omega

/-- `LeftLive` is exactly positivity of the left head. -/
theorem leftLive_of_pos {c : Control} {s : GalilVM} (h : 0 < position s.left) :
    PalPeg.GalilTrailSane.LeftLive c s := ⟨fun _ _ => h, fun _ => h⟩

/-! ## 2. The heads at a comparison -/

section Heads
variable (onLetter leftFirst : GalilVM → Prop) (centre : GalilVM → Fin 3)
  (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)

theorem compare_heads {s s' : GalilVM}
    (hcmp : (galilFrameS (sharedC onLetter leftFirst centre place entry) q first).compare s s') :
    s'.left = GalilScaffoldInputHead.left s.left ∧
      s'.right = GalilScaffoldChainVerifier.right s.right ∧ s'.center = s.center := by
  obtain ⟨vs, vq, a, hvl, hvr, -, -, -, hteq⟩ :
    compareFound (sharedC onLetter leftFirst centre place entry) q first s s' := hcmp
  cases a with
  | true =>
    rw [if_pos rfl] at hteq
    subst hteq
    exact ⟨by rw [afterCompare_left, hvl], by rw [afterCompare_right, hvr],
      afterCompare_center _ _ _⟩
  | false =>
    rw [if_neg (by simp)] at hteq
    subst hteq
    exact ⟨by rw [afterMismatch_left, hvl], by rw [afterMismatch_right, hvr],
      afterMismatch_center _ _ _⟩

end Heads

#print axioms pos_of_rep
#print axioms leftLive_of_pos
#print axioms compare_heads


/-! ## 3. `ShiftBud` at the shift entry, from the scan invariant -/

section Entry
variable (onLetter leftFirst : GalilVM → Prop) (centre : GalilVM → Fin 3)
  (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)

/-- **The shift-entry budget is pure arithmetic on the scan invariant.**  At a
comparison the left head moves one place left and the right head one place
right, so `L = C - rad` and `R = C + rad` become `C - rad - 1` and
`C + rad + 1`; `beginShiftVM` sets `remaining := ofNat h` and touches no head.
The two bounds `L + 2h + 1 <= C` and `C + h + 1 <= R` are then exactly
`2h <= rad`. -/
theorem shiftBud_of_scanInv {w : List (Fin 2)} {s s'' t'' : GalilVM} {rad : ℕ}
    (hi : ScanInvariant w (position s.center) rad s.left s.right)
    (hcan : GalilScaffoldChainVerifier.canRight s.right)
    (hcmp : (galilFrameS (sharedC onLetter leftFirst centre place entry) q first).compare s s'')
    (hb : beginShiftVM' s'' t'')
    (hh : ∀ wch : GalilScaffoldChainWatch.State, s''.chain = .watch wch →
      2 * periodLength wch ≤ rad) :
    ShiftBud t'' := by
  obtain ⟨hL, hR, hC⟩ :=
    compare_heads onLetter leftFirst centre place entry q first hcmp
  obtain ⟨wch, hchain, ht⟩ : beginShiftVM' s'' t'' := hb
  have h2 := hh wch hchain
  have hlpos : 0 < s.left.head.left.length :=
    (represented_position s.left.head w hi.leftRep hi.leftPresent).1
  have hrpos : 0 < s.right.head.left.length :=
    (represented_position s.right.head w hi.rightRep hi.rightPresent).1
  have hleft : position s''.left + 1 = position s.left := by
    rw [hL]; exact left_position s.left hlpos
  have hright : position s''.right = position s.right + 1 := by
    rw [hR]; exact right_position s.right hcan hrpos
  have hlt : rad < position s.center := scan_radius_lt hi
  have hlp := hi.leftPos
  have hrp := hi.rightPos
  have htL : t''.left = s''.left := by rw [ht]
  have htR : t''.right = s''.right := by rw [ht]
  have htC : t''.center = s''.center := by rw [ht]
  have htrem : t''.remaining = ofNat (periodLength wch) := by rw [ht]
  refine ⟨?_, ?_, ?_⟩
  · rw [htrem, ofNat_value]; positivity
  · rw [htL, htC, htrem, ofNat_value, hC]
    have : position s''.left + 2 * periodLength wch + 1 ≤ position s.center := by omega
    exact_mod_cast this
  · rw [htR, htC, htrem, ofNat_value, hC]
    have : position s.center + periodLength wch + 1 ≤ position s''.right := by omega
    exact_mod_cast this

end Entry

#print axioms shiftBud_of_scanInv


/-! ## 4. `SaneVer` at the shift entry -/

/-- **The shift entry keeps the chain verifier sane, given its own `canRight`.**
`beginShiftVM` applies `GalilScaffoldChainWatch.immediate`, whose verifier is
one guarded right move of the watching verifier; `GalilFrontMono.right_sane`
does the rest.  This is the whole content of `CloseoutRadPack4.H_shiftVerSane`
at one entry. -/
theorem saneVer_beginShift {s'' t'' : GalilVM} (hb : beginShiftVM' s'' t'')
    (hc : ∀ wch : GalilScaffoldChainWatch.State, s''.chain = .watch wch →
      GalilScaffoldChainVerifier.canRight wch.machine.verifier ∧
        GalilFrontMono.Sane wch.machine.verifier) :
    SaneVer t''.chain := by
  obtain ⟨wch, hchain, ht⟩ : beginShiftVM' s'' t'' := hb
  obtain ⟨hcan, hsane⟩ := hc wch hchain
  have htc : t''.chain = ChainVM.watch (GalilScaffoldChainWatch.immediate wch) := by rw [ht]
  intro p hp
  rw [htc] at hp
  obtain rfl : GalilScaffoldChainVerifier.right wch.machine.verifier = p := Option.some.inj hp
  exact sane_right hsane hcan

#print axioms saneVer_beginShift


/-! ## 5. `LPack`, the left-head carrier -/

/-- **The left-head pack.**  The `L` analogue of `GalilCentreLive.CPack`: off
`init` the left head still represents the input word and is present (which is
`0 < position L`, i.e. `LeftLive`), in a non-replaying scan the scan invariant
pins `L = C - rad` and `R = C + rad`, and the centre invariant travels through
the replay. -/
structure LPack (w : List (Fin 2)) (c : Control) (s : GalilVM) : Prop where
  lrep : c.mode ≠ Mode.init →
    GalilScaffoldInputTrace.Represents s.left.head w ∧ s.left.head.focus ≠ none
  scanInv : c.mode = Mode.scan → c.replaying = false →
    ∃ rad : ℕ, ScanInvariant w (position s.center) rad s.left s.right
  minv : c.mode ≠ Mode.init → MInv w c s

/-- **`LeftLive` is read off the pack**, exactly as `CentreLive` is read off
`CPack`. -/
theorem leftLive_of_lpack {w : List (Fin 2)} {c : Control} {s : GalilVM}
    (h : LPack w c s) : PalPeg.GalilTrailSane.LeftLive c s := by
  refine ⟨fun hm _ => ?_, fun hm => ?_⟩
  · obtain ⟨hh, hp⟩ := h.lrep (by rw [hm]; decide)
    exact pos_of_rep hh hp
  · obtain ⟨hh, hp⟩ := h.lrep (by rw [hm]; decide)
    exact pos_of_rep hh hp

/-- The scan half of the pack, at a non-replaying scan state. -/
theorem lpack_scanInv {w : List (Fin 2)} {c : Control} {s : GalilVM} (h : LPack w c s)
    (hm : c.mode = Mode.scan) (hr : c.replaying = false) :
    ∃ rad : ℕ, ScanInvariant w (position s.center) rad s.left s.right := h.scanInv hm hr

/-- **The pack holds at the boot state**, where every field is vacuous: the
boot controller is in `init` mode. -/
theorem lpack_boot (w : List (Fin 2)) :
    LPack w (boot w).ctl (boot w).vm := by
  have hm : (boot w).ctl.mode = Mode.init := rfl
  refine ⟨fun h => absurd hm h, fun h => ?_, fun h => absurd hm h⟩
  rw [hm] at h; cases h

#print axioms leftLive_of_lpack
#print axioms lpack_boot

/-! ## 6. The trace-level hypotheses -/

section Trace
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **(NAMED) the left-head pack along every pre-loaded trace.**  This is
`CloseoutRadPack2.H_leftLive` strengthened to the carrier that would prove it
by a tick induction: `GalilCentreLive.cpack_steps` for `L` instead of the
centre head.  The corners it still has to survive are the ones the centre
version does not meet: at a *mismatched* comparison the left head moves onto
`position L - 1`, which stays off the origin only because `Live` carries
`position R < 2 * position C` (`GalilLiveCentre.Live`), and a `rewind`
walk lowers the centre, so `MInv` has to be re-established through
`minv_after_fallback`. -/
def H_lpack : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTrace centre place entry q first w st Tc →
    ∀ i, i ≤ Tc w.length → LPack w (st i).ctl (st i).vm

/-- **(NAMED) the Galil half-bound at a shift entry.**  The scan invariant at
the comparison source together with `2 * h <= rad`, `h` the semiperiod of the
watching chain.  This is what `CloseoutRadPack3.H_shiftEntry` was reduced
*from*: the arithmetic step `ScanInvariant + 2h <= rad -> ShiftBud` is proved
below, so only the Galil fact `2h <= rad` (the chain shift never exceeds the
radius, via `GalilCatchUpDistance.places_of_guard`'s `4h <= distance`) is
left. -/
def H_shiftHalf : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTrace centre place entry q first w st Tc →
    ∀ i, i ≤ Tc w.length → ∀ s'' t'' : GalilVM,
      (galilFrameS (PofC centre place entry w) q first).compare (st i).vm s'' →
      beginShiftVM' s'' t'' →
      ∃ rad : ℕ,
        ScanInvariant w (position (st i).vm.center) rad (st i).vm.left (st i).vm.right ∧
        GalilScaffoldChainVerifier.canRight (st i).vm.right ∧
        ∀ wch : GalilScaffoldChainWatch.State, s''.chain = .watch wch →
          2 * periodLength wch ≤ rad

/-- **(NAMED) the chain verifier can move at a shift entry.**  All that is
left of `CloseoutRadPack4.H_shiftVerSane` once `GalilFrontMono.right_sane` is
applied: the watching verifier's own `canRight` and `Sane`. -/
def H_shiftCanRight : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTrace centre place entry q first w st Tc →
    ∀ i, i ≤ Tc w.length → ∀ s'' t'' : GalilVM,
      (galilFrameS (PofC centre place entry w) q first).compare (st i).vm s'' →
      beginShiftVM' s'' t'' →
      ∀ wch : GalilScaffoldChainWatch.State, s''.chain = .watch wch →
        GalilScaffoldChainVerifier.canRight wch.machine.verifier ∧
          GalilFrontMono.Sane wch.machine.verifier

/-- **`H_leftLive` from the pack.** -/
theorem h_leftLive_of_lpack (h : H_lpack centre place entry q first) :
    H_leftLive centre place entry q first :=
  fun w hw st Tc hP i hi => leftLive_of_lpack (h w hw st Tc hP i hi)

/-- **`H_shiftEntry` from the half-bound.** -/
theorem h_shiftEntry_of_half (h : H_shiftHalf centre place entry q first) :
    H_shiftEntry centre place entry q first := by
  intro w hw st Tc hP i hi s'' t'' hcmp hb
  obtain ⟨rad, hscan, hcan, hh⟩ := h w hw st Tc hP i hi s'' t'' hcmp hb
  exact shiftBud_of_scanInv (onLetterVM w) leftFirstVM centre place entry q first
    hscan hcan hcmp hb hh

/-- **`H_shiftVerSane` from the verifier's `canRight`.** -/
theorem h_shiftVerSane_of_canRight (h : H_shiftCanRight centre place entry q first) :
    H_shiftVerSane centre place entry q first :=
  fun w hw st Tc hP i hi s'' t'' hcmp hb =>
    saneVer_beginShift hb (h w hw st Tc hP i hi s'' t'' hcmp hb)

/-- **`H_trailF` from the three refined residuals.** -/
theorem h_trailF_final (hlp : H_lpack centre place entry q first)
    (hhalf : H_shiftHalf centre place entry q first)
    (hcan : H_shiftCanRight centre place entry q first) :
    H_trailF centre place entry q first :=
  h_trailF_of_named' centre place entry q first
    (h_shiftEntry_of_half centre place entry q first hhalf)
    (h_leftLive_of_lpack centre place entry q first hlp)
    (h_shiftVerSane_of_canRight centre place entry q first hcan)

end Trace

#print axioms h_leftLive_of_lpack
#print axioms h_shiftEntry_of_half
#print axioms h_shiftVerSane_of_canRight
#print axioms h_trailF_final

/-- **The concrete instance** at `centreC` / `placeC`. -/
theorem h_trailF_C'' (entry q : ℕ) (first : Fin 9)
    (hlp : H_lpack PalPeg.GalilFinalAssembly2.centreC PalPeg.GalilFinalAssembly2.placeC
      entry q first)
    (hhalf : H_shiftHalf PalPeg.GalilFinalAssembly2.centreC PalPeg.GalilFinalAssembly2.placeC
      entry q first)
    (hcan : H_shiftCanRight PalPeg.GalilFinalAssembly2.centreC PalPeg.GalilFinalAssembly2.placeC
      entry q first) :
    H_trailF PalPeg.GalilFinalAssembly2.centreC PalPeg.GalilFinalAssembly2.placeC entry q first :=
  h_trailF_final _ _ entry q first hlp hhalf hcan

#print axioms h_trailF_C''

end PalPeg.CloseoutLPack
