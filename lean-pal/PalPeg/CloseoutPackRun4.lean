import PalPeg.CloseoutPackRun3
import PalPeg.GalilLiveCentreMismatch

/-!
# `CloseoutPackRun4`: auditing the nine contracts of `CloseoutPackRun3.BigResid5`

This file does **not** add a new contract.  It takes the nine fields of
`CloseoutPackRun3.BigResid5` together with `H_extraEntry` / `H_extraTick` and,
for each of them, either proves it from `BigPack2`, refutes it, or names the one
missing machine fact.  The two results that are *theorems* are:

* **`rScanInvR` splits, and its non-replaying half is free.**
  `scanInvR_of_nonreplaying` is literally `LPack.scanInv`; what is left of the
  contract is the *replaying* scan, where `LPack` says nothing.  (§1)

* **`rMismatchMinv` is FALSE.**  `minv_false_at_mismatch`: at a non-replaying
  scan carrying the pack, every comparison whose two reads disagree has a
  landing at which `MInv w {x.ctl with clock := 2048} s''` **fails**.  The proof
  is three lines of existing material: the comparison moves `R` to
  `position R + 1` and keeps `C` (`CloseoutLPack4.beginShift_heads`-style
  `CloseoutLPack.compare_heads`), `MInv` off a replay is
  `Leftmost w (position R + 1) C`, hence `Live w (position R + 1) C`, and
  `GalilLiveCentreMismatch.not_live_of_mismatch` says a mismatching comparison
  kills exactly that.  `rMismatchMinv_absurd` turns this into `False` from the
  contract itself.

  The consequence reaches further than this one field: `lticks_of_big5` derives
  `LTickLeaves.shiftMinv` and `LTickLeaves.fallbackMinv` from `rMismatchMinv` by
  `minv_of_mismatch`, and neither entry moves a head — so **those two corners of
  `CloseoutLPack3.LTickLeaves` are false as well**, and with them the claim that
  `LPack.minv` survives a mismatch tick with the *old* centre still installed.
  `CloseoutLPack4`'s own docstring already anticipates this ("holds only while
  the centre survives; when it dies the route is … `minv_after_fallback`"), but
  the statement it settled on quantifies over every comparison, including the
  dying one.  The repair is not a lemma but a re-cut: `MInv` must be demanded at
  the *fallback/shift landing*, whose centre is the new one
  (`GalilLiveCentreFallback.leftmost_after_fallback` +
  `GalilLiveCentreReplay.minv_after_fallback`), not at the comparison target.

## Verdicts on the remaining seven contracts and the two `Extra` obligations

Each entry names the single machine fact that is missing; none of them is an
arithmetic gap that the available material closes.

* `rInitPack` — *missing fact*: `(galilFrameS …).init` lands with the left head
  represented and focused on place 1 and with `Leftmost w (position R) C` at the
  boot centre; `CloseoutLPack.lpack_boot` only covers the `init` state itself,
  where every field of `LPack` is vacuous.
* `rScanInvR` — *proved off a replay* (§1); *missing fact* in a replay: that the
  replayed scan re-reads the same letters, i.e. `GalilLiveCentreReplay`'s
  `minv_matchR` bookkeeping lifted to `ScanInvariant` (the replay counter
  `s.replay = ofNat m` pins `position R + m`, but no lemma turns that into the
  scan invariant at the *current* `R`).
* `rMismatchMinv` — **false** (§2).
* `rShiftOneMinv` — *missing fact*: `shiftOne` lowers `C` by one place, and
  `GalilLiveCentreShift.leftmost_shift` needs the shift amount `h` to be the
  *period* of the current span (`GalilPeriodCentre.no_centre_below_period`);
  `Extra.cand` supplies a `Candidate` for the *window*, but nothing identifies
  the `h` a single `shiftOne` unit consumes with that candidate's period.
* `rShiftDoneScan` — *missing fact*: the new centre's palindrome radius at the
  shift exit, i.e. `GalilScaffoldChainReadOrigin.reshift_palindrome` at the
  state where `remainingPos` first fails.  This is a statement about the whole
  shift round; a single exiting tick does not see how many units ran.
* `rChoosePack` — *missing fact*: the `choose` re-centring moves `C` to the odd
  centre and leaves `Leftmost` at the same `R`; `GalilLiveCentreShift.live_shift_of_palAt`
  gives liveness of the new centre but not minimality, which needs the DP's
  failure at every smaller odd centre (`Extra.failed` is stated for `scan` only).
* `rRewindPairMinv` — *missing fact*: a `rewindPair` unit moves `L` two places
  and `C` one, and `MInv` must survive with `R` fixed; no lemma relates a rewind
  unit to `Leftmost` (the rewind walk *lowers* the centre, so the leftmost-live
  centre can change under it).
* `rReplayPack` — *missing fact*: `replayStart` lands in `Restarted w t 0 reset`
  with `t.replay = ofNat r` and `position t.center = n + 1 - r`, the exact
  hypotheses of `minv_after_fallback`; the frame-level `replayStart` relation has
  not been connected to `Restarted`.
* `rShiftNext` — *missing fact*: `ShiftLocal` is a property of the landing, so it
  is the tick-level form of `H_shiftHalf`/`H_shiftCanRight`
  (`GalilCatchUpDistance.places_of_guard` gives `4h ≤ distance` only at a guard
  that has already been entered).
* `H_extraEntry` — the `ready` field is
  `GalilSearchReadyInv.searchReady_restarted`; `scanMargin`/`rewindMargin` follow
  from `Restarted` (`L = C = R`); *missing fact*: `failed`/`cand`/`scanAvail` at
  the entry, since an entry is in `copy`/`restart` shape and the guards are
  vacuous there only if the entry mode is never `scan` — which the entry relation
  does not currently state.
* `H_extraTick` — `ready` travels by `GalilSearchReadyInv.searchReady_step`;
  *missing fact*: `failed` is **not** tick-local — a matched comparison raises
  the radius, so `StageFailed` at the new radius is exactly the DP's next
  verdict, which only `GalilLeafDp`'s round-level lemmas produce.

## Honest status

Standard axioms only.  One contract refuted, one half-proved, seven reduced to a
named machine fact.  Unconditional `PAL ∈ PEG` remains open.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPackRun4

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton PalPeg.GalilCheckpoints
open PalPeg.GalilFinalAssembly PalPeg.GalilFinalAssembly4
open PalPeg.CloseoutLPack PalPeg.CloseoutLPack3 PalPeg.CloseoutLPack4 PalPeg.CloseoutLPack5
open PalPeg.CloseoutPackRun PalPeg.CloseoutPackRun2 PalPeg.CloseoutPackRun3

section Audit
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-! ## 1. `rScanInvR` off a replay is free -/

/-- **The non-replaying half of `rScanInvR`.**  `LPack.scanInv` *is* the
contract as soon as the scan is not replaying, so the residue of `rScanInvR` is
the replaying scan alone. -/
theorem scanInvR_of_nonreplaying {w : List (Fin 2)} {x : State GalilVM}
    (hx : BigPack2 centre place entry q first w x)
    (hm : x.ctl.mode = Mode.scan) (hnr : x.ctl.replaying = false) :
    ∃ r, ScanInvariant w (position x.vm.center) r x.vm.left x.vm.right :=
  hx.big.ipack.pack.scanInv hm hnr

/-! ## 2. `rMismatchMinv` is false -/

/-- **A mismatching comparison out of a packed non-replaying scan falsifies
`MInv` at its landing.**  The comparison keeps `C` and moves `R` to
`position R + 1`; off a replay `MInv` there is `Leftmost w (position R + 1) C`,
whose liveness half is exactly what the mismatch destroys. -/
theorem minv_false_at_mismatch {w : List (Fin 2)} {x : State GalilVM} {s'' : GalilVM}
    (hx : BigPack2 centre place entry q first w x)
    (hm : x.ctl.mode = Mode.scan) (hnr : x.ctl.replaying = false)
    (hcmp : (galilFrameS (PofC centre place entry w) q first).compare x.vm s'')
    (hmis : read (GalilScaffoldInputHead.left x.vm.left) ≠ read (right x.vm.right)) :
    ¬ MInv w {x.ctl with clock := 2048} s'' := by
  intro hMI
  obtain ⟨rad, hi⟩ := scanInvR_of_nonreplaying centre place entry q first hx hm hnr
  have hav : canRight x.vm.right :=
    canR_of_bigPack2 centre place entry q first hx.big hx.extra hm
  obtain ⟨-, hR, hC⟩ :=
    compare_heads (onLetterVM w) leftFirstVM centre place entry q first hcmp
  have hlen : 0 < x.vm.right.head.left.length :=
    (represented_position _ w hi.rightRep hi.rightPresent).1
  have hpos : position s''.right = position x.vm.right + 1 := by
    rw [hR]; exact right_position x.vm.right hav hlen
  have hLm := hMI.2 hnr
  rw [hpos, hC] at hLm
  exact not_live_of_mismatch hi hav hmis hLm.1

/-- **`BigResid5.rMismatchMinv` is refuted by any such comparison.** -/
theorem rMismatchMinv_absurd {w : List (Fin 2)}
    (hr : BigResid5 centre place entry q first w)
    {x : State GalilVM} {s'' : GalilVM}
    (hx : BigPack2 centre place entry q first w x)
    (hm : x.ctl.mode = Mode.scan) (hnr : x.ctl.replaying = false)
    (hcmp : (galilFrameS (PofC centre place entry w) q first).compare x.vm s'')
    (hmis : read (GalilScaffoldInputHead.left x.vm.left) ≠ read (right x.vm.right)) :
    False :=
  minv_false_at_mismatch centre place entry q first hx hm hnr hcmp hmis
    (hr.rMismatchMinv x hx hm s'' hcmp)

end Audit

#print axioms scanInvR_of_nonreplaying
#print axioms minv_false_at_mismatch
#print axioms rMismatchMinv_absurd

end PalPeg.CloseoutPackRun4
