import PalPeg.GalilOracleDischarge
import PalPeg.GalilRunInv2
import PalPeg.GalilFallbackLanding
import PalPeg.GalilChosenRadiusLe
import PalPeg.GalilCycleProgress
import PalPeg.GalilReplaySegment

/-!
# Glue B: discharging `hmismatch` of `cycleOracle_of_pieces`

`PalPeg.GalilOracleDischarge.cycleOracle_of_pieces` leaves the mismatching
comparison of the chain-idle segment as the named hypothesis

```
hmismatch : ∀ c r c' t, InvS raw c r → SegReached … c r c' t →
  c'.replaying = false → c'.clock = 1 → canRight t.right →
  read (left t.left) ≠ read (right t.right) →
  FallbackRoute centre place entry q first raw c r
```

This module produces the two *non-report* routes of `FallbackRoute` — `landed`
(the FPP chose radius `0`) and `replaying` (it chose a positive radius) — for
that exit.  The `report` route (the mismatch that consumed the last letter) is
Glue A's business and never arises here.

## What is actually run

`fallback_landing` (`PalPeg/GalilFallbackLanding.lean`) is run for real at the
segment exit, and everything the two routes need is read off its own exports:

* `Inv` / `ReplayLanding` — `minv_after_fallback` plus `inv_of_parts` and the
  restart-derived fields (`stage_of_restarted_zero`, `searchReady_of_restarted`,
  `blockInv_of_restarted`, `input_of_restarted`).  This is the body of
  `PalPeg.GalilScaffoldChainInputSupply.inv_after_fallback'`, re-run here
  because that lemma packs its conclusion and *drops* the landing centre's
  position, which the oracle's progress clause needs (see below), and drops
  `Restarted raw t 0 reset`, which `ReplayLanding.rest` asks for verbatim.
* `Frontier` at a positive-radius landing — `frontier_after_fallback'`
  (`PalPeg/GalilChosenRadiusLe.lean`), whose rewind-legality side condition is
  derived from the landing palindrome.  So `inv_after_fallback'`'s `hfrT`
  hypothesis is *discharged*, not propagated.
* the progress `position r.center < position t.center` — `fallback_progress`
  (`PalPeg/GalilCycleProgress.lean`), applied to the very witnesses
  `fallback_landing` produced.
* `hout : OutputRel raw c' t` — `stepsAll_last` on the segment's own
  `SoundScanNR` run: the exit is a scan state (`SegReached.mode`) and the
  mismatch exit is not replaying, which is exactly `SoundScanNR`'s two
  premises.  Nothing is assumed here.

## What is *not* derivable, and travels as a hypothesis

At the segment exit `SegReached` publishes `MInv`, `SearchReady`,
`Represents`, `Frontier`, `ShiftIdle`, chain idleness and *some*
`ScanInvariant`.  It does **not** publish the counter invariants the fallback
needs, nor the shape of the fallback tick itself:

* `FallbackCounters` — a radius `Rad` with the scan invariant, `RadiusRep`,
  `SpanRep`, `Canonical t.length`, and the even length of the fallback window.
  The evenness is *not* a consequence of `SpanRep`/`ScanInvariant`: the window
  is `(stream …).take (ℓ+1)` with length `min (ℓ+1) (position t.right + 1)`
  (`stream_length_of_place`), i.e. `min (2·Rad+2) (C+Rad+1)`, whose second
  branch is odd whenever `Rad = C`.  It is the "every place is an even place"
  fact of the encoded word.
* `FallbackTick` — the fallback tick's own data (`vs`, `vq`, the search
  effect, the `chainAt` clause and the failure of the shift guard).
  `SegEnd.mismatch` carries none of it.
-/

set_option autoImplicit false

namespace PalPeg.GalilOracleGlueB

open PalPeg PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilRunSkeleton
open PalPeg.GalilOracleDischarge PalPeg.GalilCycleProgress
open Manacher GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-- `PofC` is the `galilShared` record the fallback lemmas speak about. -/
theorem PofC_eq (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry : ℕ) (raw : List (Fin 2)) :
    PofC centre place entry raw =
      galilShared (onLetterVM raw) leftFirstVM shiftGuardVM beginShiftVM' beginFallbackVM'
        (restartVM entry) centre place entry := rfl

/-! ## The fallback tick's own data -/

/-- Everything a mismatching comparison needs *besides* the controller facts:
the scan projection, the background search effect, the chain clause and the
failure of the shift guard.  `SegEnd.mismatch` publishes none of this. -/
structure FallbackTick (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry : ℕ) (raw : List (Fin 2)) (s : GalilVM) : Prop where
  /-- the scan projection at the comparison, and the search witness -/
  data : ∃ (vs : ScanVM) (vq : SearchVM),
    vs.left = left s.left ∧ vs.right = right s.right ∧
    searchEffect (PofC centre place entry raw) false s vq ∧
    chainAt false (decide (vq.search.mode = .found)) (vq.dp.config.tapes 11)
      (centre s) (place s) s.center s.radius s.chain vs.chain ∧
    ¬ shiftGuardVM (afterMismatch s vs vq)

/-- The counter invariants at the comparison that `SegReached` does not carry. -/
structure FallbackCounters (raw : List (Fin 2)) (s : GalilVM) : Prop where
  /-- a radius with the scan invariant and both counter representations -/
  rad : ∃ Rad : ℕ, ScanInvariant raw (position s.center) Rad s.left s.right ∧
    RadiusRep s.radius Rad ∧ SpanRep s
  /-- the span counter is canonical -/
  canon : Canonical s.length
  /-- the span counter's natural value, and the even length of the fallback window -/
  span : ∃ ℓ : ℕ, value s.length = ℓ ∧
    ∀ (a : Fin 2) (xs rs' q' : List (Fin 2)),
      right s.right = represent ⟨a :: xs, (right s.right).gap⟩ (rs'.map some) q' →
      ((GalilScaffoldPlace.stream ⟨a :: xs, (right s.right).gap⟩).take (ℓ + 1)).length % 2 = 0

/-! ## One fallback cycle, with the landing centre kept -/

/-- **`fallback_pack`.**  One fallback cycle from a mismatching, non-replaying
scan state at clock one.  Unlike
`PalPeg.GalilScaffoldChainInputSupply.inv_after_fallback'` this keeps the two
facts the oracle needs at the landing: the centre has strictly advanced, and
the radius-`0` restart derivation is exported for `ReplayLanding.rest`.  The
positive-radius `Frontier` obligation (`hfrT` there) is discharged here by
`frontier_after_fallback'`. -/
theorem fallback_pack (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (hq0 : 0 < q) (first : Fin 9) (h7 : first ≠ 7) (h8 : first ≠ 8)
    (raw : List (Fin 2)) (c : Control) (s : GalilVM)
    (hm : c.mode = .scan) (hr : c.replaying = false) (hc : c.clock = 1)
    (hsi : ShiftIdle s) (hav : canRight s.right)
    (hmis : read (left s.left) ≠ read (right s.right))
    (hM : MInv raw c s) (hK : FallbackCounters raw s)
    (hT : FallbackTick centre place entry raw s)
    (hout : OutputRel raw c s) :
    ∃ (n R : ℕ) (cT : Control) (t : GalilVM),
      StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048 (SoundScanNR raw)
        (1 + (n + 1)) ⟨c, s⟩ ⟨cT, t⟩ ∧
      position s.center < position t.center ∧
      (R = 0 → Inv raw cT t) ∧
      (0 < R → ReplayLanding raw cT t R) := by
  obtain ⟨⟨Rad, hscan, hRR, hS⟩, hcan, ℓ, hv, heven⟩ := hK
  obtain ⟨vs, vq, hl, hrr, hq, hch, hg⟩ := hT.data
  have hrep : GalilScaffoldInputTrace.Represents (right s.right).head raw :=
    right_word s.right raw hscan.rightRep hav
  have hfoc : (right s.right).head.focus ≠ none :=
    right_present s.right raw hscan.rightRep hscan.rightPresent hav
  obtain ⟨a, xs, rs', q', hdec, hraw, n, o, t, hstA, hRst, hposT, hpal, hmax, hrepT, hsiT, hchT,
      hRit, hCR⟩ :=
    fallback_landing (onLetterVM raw) leftFirstVM (restartVM entry) centre place entry q hq0 first
      h7 h8 2048 c hm hr hc s hsi hav vs vq hl hrr hmis hq hch hg hrep hfoc hcan
      ℓ hv heven rfl rfl hout
  -- the leftmost live centre at the landing
  have hL : Leftmost raw (position (right s.right)) (position t.center) :=
    leftmost_after_fallback_landing raw hM hr hscan hRR hS hav hmis a xs rs' q' hdec
      ℓ hv hpal hmax hposT
  -- the mismatch place is one past the right head
  have hrpos : position (right s.right) = position s.right + 1 :=
    right_position s.right hav (represented_position _ raw hscan.rightRep hscan.rightPresent).1
  -- the centre has strictly advanced
  have hprog : position s.center < position t.center :=
    fallback_progress raw hM hr hscan hRR hS hav hmis a xs rs' q' hdec ℓ hv
      hpal hmax hposT
  -- the centre invariant at the landing, in both clauses at once
  have hMT : MInv raw
      { c with
        mode := .scan, clock := 2048, output := o,
        replaying := decide (0 < chosenRadius
          ((GalilScaffoldPlace.stream ⟨a :: xs, (right s.right).gap⟩).take (ℓ + 1))),
        odd := oddAt false
          (((GalilScaffoldPlace.stream ⟨a :: xs, (right s.right).gap⟩).take
              (ℓ + 1)).length -
            (2 * chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs, (right s.right).gap⟩).take
              (ℓ + 1)) + 1)),
        pair := pairAt (2 * chosenRadius
          ((GalilScaffoldPlace.stream ⟨a :: xs, (right s.right).gap⟩).take
            (ℓ + 1))) } t :=
    minv_after_fallback hRst hrepT (by rw [hposT, hrpos]) (by rw [← hrpos]; exact hL) rfl
  refine ⟨n, chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs, (right s.right).gap⟩).take
      (ℓ + 1)), _, t, hstA, hprog, ?_, ?_⟩
  · -- radius zero: the full `Inv`
    intro hz
    have htrp : t.replay = reset := by rw [hrepT, hz]; rfl
    exact inv_of_parts hRst hMT ⟨rfl, by simp [hz], rfl⟩ (frontier_of_reset htrp)
      (replayRest_of_reset htrp) hsiT
  · -- positive radius: the replaying landing
    intro hz
    exact
      { pos := hz
        rest := hRst
        mode := rfl
        clock := rfl
        replaying := by simp [hz]
        replay := hrepT
        minv := hMT
        frontier := frontier_after_fallback' hRit hrepT hpal
        shiftIdle := hsiT }

/-! ## `hmismatch`, discharged -/

/-- **The mismatch exit of the chain-idle segment produces a `FallbackRoute`.**
This is exactly the shape of `cycleOracle_of_pieces`'s `hmismatch`, with the
two counter/tick gaps named (`hK`, `hT`).  The `report` route never arises:
the mismatch that consumed the last letter leaves the segment through
`SegEnd.lastLetter`, not `SegEnd.mismatch`. -/
theorem fallbackRoute_of_mismatch (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (hq0 : 0 < q) (first : Fin 9)
    (h7 : first ≠ 7) (h8 : first ≠ 8) (raw : List (Fin 2))
    (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM)
    (hs : SegReached centre place entry q first raw c r c' t)
    (hnr : c'.replaying = false) (hc1 : c'.clock = 1) (hav : canRight t.right)
    (hmis : read (left t.left) ≠ read (right t.right))
    (hK : FallbackCounters raw t) (hT : FallbackTick centre place entry raw t) :
    FallbackRoute centre place entry q first raw c r := by
  obtain ⟨k0, hrun⟩ := hs.run
  have hout : OutputRel raw c' t := stepsAll_last hrun hs.mode hnr
  obtain ⟨n, R, cT, sT, hstA, hprog, hz, hp⟩ :=
    fallback_pack centre place entry q hq0 first h7 h8 raw c' t hs.mode hnr hc1 hs.shiftIdle hav
      hmis hs.minv hK hT hout
  have hst : ∃ k, StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048
      (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩ :=
    ⟨k0 + (1 + (n + 1)), stepsAll_trans hrun hstA⟩
  have hprog' : position r.center < position sT.center := by
    rw [← hs.center]; exact hprog
  rcases Nat.eq_zero_or_pos R with h0 | h0
  · exact .landed cT sT hst (hz h0) hprog'
  · exact .replaying cT sT R hst (hp h0) hprog'

#print axioms PofC_eq
#print axioms fallback_pack
#print axioms fallbackRoute_of_mismatch

end PalPeg.GalilOracleGlueB
