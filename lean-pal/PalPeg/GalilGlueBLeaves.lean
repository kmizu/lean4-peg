import PalPeg.GalilOracleGlueB
import PalPeg.GalilSegmentConstruct
import PalPeg.GalilSpanCounter
import PalPeg.GalilLiveCentreFallback
import PalPeg.GalilOracleDischarge

/-!
# Glue B leaves: `FallbackCounters` and `FallbackTick`

`PalPeg.GalilOracleGlueB.fallbackRoute_of_mismatch` takes two packs at the
mismatch exit `t` of the chain-idle segment as hypotheses.  This module
discharges both.

* `FallbackCounters raw t` — the counters are carried along the segment
  (`WatchSegE`) from the entering state: `scanInvariant_watchSegE`,
  `radiusRep_watchSegE`, `spanRep_watchSegE` (already in
  `GalilSpanCounter`), `canonical_length_watchSegE`.  The **even window** is
  *derived*: the left head is represented and present, so it sits at place
  `≥ 1`, and `position left = C − Rad` with `Rad ≤ C` gives `Rad + 1 ≤ C`;
  the window length `min (2·Rad+2) (C+Rad+1)` is therefore `2·Rad+2`.
* `FallbackTick` — `vs := ⟨left t.left, right t.right, chain'⟩`, with
  `chain' = idle` when the background search effect is not `found` and
  `chain' = chainStart …` when it is (`chainAt`'s idle clauses).  In both
  cases the chain after the mismatch is not `watch`, so the shift guard fails.
  No case split on the exit is needed.

What is **not** derivable from `SegReached` and travels as a hypothesis:

* the segment itself (`WatchSegE … c r c' t`) — `SegReached` keeps only its
  `StepsAll` shadow;
* `EntryCounters raw r` at the entering state.  From `Inv` the scan
  invariant, `RadiusRep` and `Canonical length` come from `Restarted`, but
  `SpanRep` does not (`entryCounters_of_inv` takes it); from `InvScan` only
  the scan invariant is available (`entryCounters_of_invScan`).
-/

set_option autoImplicit false

namespace PalPeg.GalilGlueBLeaves

open PalPeg PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilRunSkeleton
open PalPeg.GalilOracleDischarge PalPeg.GalilOracleGlueB
open Manacher GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-! ## Counters along the chain-idle segment -/

theorem scanInvariant_watchSegE (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    {es : List Bool} {c c' : Control} {s t : GalilVM}
    (h : WatchSegE P q first delay es c s c' t) {raw : List (Fin 2)} {cen Rad : ℕ}
    (hi : ScanInvariant raw cen Rad s.left s.right) :
    ScanInvariant raw cen (Rad + es.count true) t.left t.right :=
  scan_events_invariant ((watchSegE_heads P q first delay h).1 raw cen Rad) hi

theorem radiusRep_watchSegE (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    {es : List Bool} {c c' : Control} {s t : GalilVM}
    (h : WatchSegE P q first delay es c s c' t) {Rad : ℕ} (hR : RadiusRep s.radius Rad) :
    RadiusRep t.radius (Rad + es.count true) := by
  obtain ⟨-, -, hrad, hrc, -⟩ := watchSegE_heads P q first delay h
  refine ⟨hrc hR.1, ?_⟩
  rw [hrad, hR.2]
  push_cast
  ring

theorem canonical_length_watchSegE (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    {es : List Bool} {c c' : Control} {s t : GalilVM}
    (h : WatchSegE P q first delay es c s c' t) (hL : Canonical s.length) :
    Canonical t.length :=
  (watchSegE_heads P q first delay h).2.2.2.2 hL

/-! ## The entering counters -/

/-- The counter invariants at the state the segment starts from. -/
def EntryCounters (raw : List (Fin 2)) (r : GalilVM) : Prop :=
  ∃ Rad : ℕ, ScanInvariant raw (position r.center) Rad r.left r.right ∧
    RadiusRep r.radius Rad ∧ SpanRep r ∧ Canonical r.length

/-- From `Inv`: everything but `SpanRep` comes from `Restarted`. -/
theorem entryCounters_of_inv {raw : List (Fin 2)} {c : Control} {r : GalilVM}
    (h : Inv raw c r) (hS : SpanRep r) : EntryCounters raw r := by
  obtain ⟨Rad, last, hR⟩ := h.rest
  obtain ⟨-, -, -, hi, hRR, hL, -⟩ := hR
  exact ⟨Rad, hi, hRR, hS, hL⟩

/-- From `InvScan`: only the scan invariant is carried. -/
theorem entryCounters_of_invScan {raw : List (Fin 2)} {c : Control} {r : GalilVM} {k : ℕ}
    (h : PalPeg.GalilReplaySegment.InvScan 2048 raw c r k) (hR : RadiusRep r.radius k)
    (hS : SpanRep r) (hL : Canonical r.length) : EntryCounters raw r :=
  ⟨k, h.scan, hR, hS, hL⟩

/-! ## The even fallback window -/

/-- A represented, present left head is never at place `0`, so the scan
radius is strictly below the centre. -/
theorem radius_lt_centre {raw : List (Fin 2)} {cen Rad : ℕ} {l r : PlaceHead}
    (hi : ScanInvariant raw cen Rad l r) : Rad + 1 ≤ cen := by
  have hlp := hi.leftPos
  have hRC : Rad ≤ cen := hi.palindrome.1
  have hl1 : 1 ≤ position l := by
    have h0 := (represented_position l.head raw hi.leftRep hi.leftPresent).1
    unfold position
    split <;> omega
  omega

/-- **`fallbackCounters_of_seg`.**  The counter pack at the exit of a chain-idle
segment, from the entering counters. -/
theorem fallbackCounters_of_seg (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    {raw : List (Fin 2)} {es : List Bool} {c c' : Control} {r t : GalilVM}
    (hseg : WatchSegE P q first delay es c r c' t) (hcen : t.center = r.center)
    (hE : EntryCounters raw r) (hav : canRight t.right) : FallbackCounters raw t := by
  obtain ⟨Rad, hi0, hR0, hS0, hL0⟩ := hE
  have hi : ScanInvariant raw (position t.center) (Rad + es.count true) t.left t.right := by
    rw [hcen]; exact scanInvariant_watchSegE P q first delay hseg hi0
  have hR : RadiusRep t.radius (Rad + es.count true) := radiusRep_watchSegE P q first delay hseg hR0
  have hS : SpanRep t := spanRep_watchSegE P q first delay hseg hS0
  have hL : Canonical t.length := canonical_length_watchSegE P q first delay hseg hL0
  set K := Rad + es.count true with hK
  refine ⟨⟨K, hi, hR, hS⟩, hL, 2 * K + 1, ?_, ?_⟩
  · have h1 : value t.length = 2 * value t.radius + 1 := hS
    rw [h1, hR.2]
    push_cast
    ring
  · intro a xs rs' q' hdec
    have hstream := stream_length_of_place a xs rs' q' hdec
    have hpos : position (right t.right) = position t.right + 1 :=
      right_position t.right hav (represented_position _ raw hi.rightRep hi.rightPresent).1
    have hrp := hi.rightPos
    have hlt := radius_lt_centre hi
    rw [List.length_take, hstream, hpos]
    have e : min (2 * K + 1 + 1) (position t.right + 1) = 2 * K + 2 := by omega
    rw [e]
    omega

/-! ## The fallback tick -/

/-- **`fallbackTick_of_mismatch`.**  At an idle-chain state whose search
projection is covered, the fallback tick's data exists. -/
theorem fallbackTick_of_mismatch (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry : ℕ) (raw : List (Fin 2))
    (hsearch : ∀ s : GalilVM, PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get s) →
      ∀ a : Bool, ∃ v, searchEffect (PofC centre place entry raw) a s v)
    (t : GalilVM) (hidle : t.chain = ChainVM.idle)
    (hsr : PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get t)) :
    FallbackTick centre place entry raw t := by
  classical
  obtain ⟨vq, hq⟩ := hsearch t hsr false
  refine ⟨?_⟩
  by_cases hf : vq.search.mode = .found
  · refine ⟨⟨left t.left, right t.right,
      chainStart (vq.dp.config.tapes 11) (centre t) (place t) t.center t.radius⟩,
      vq, rfl, rfl, hq, ?_, ?_⟩
    · exact Or.inr (Or.inr ⟨hidle, decide_eq_true hf, rfl⟩)
    · rintro ⟨w, hw, -⟩
      rw [afterMismatch_chain] at hw
      cases hw
  · refine ⟨⟨left t.left, right t.right, ChainVM.idle⟩, vq, rfl, rfl, hq, ?_, ?_⟩
    · exact Or.inr (Or.inl ⟨hidle, decide_eq_false hf, rfl⟩)
    · rintro ⟨w, hw, -⟩
      rw [afterMismatch_chain] at hw
      cases hw

/-! ## `fallbackRoute_of_mismatch` without the two packs -/

/-- **`fallbackRoute_of_mismatch'`.**  `fallbackRoute_of_mismatch` with
`FallbackCounters` and `FallbackTick` discharged.  In their place: the segment
itself (`hseg`, which `SegReached` does not keep), the entering counters
(`hE`), and the oracle's own `hsearch`. -/
theorem fallbackRoute_of_mismatch' (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (hq0 : 0 < q) (first : Fin 9)
    (h7 : first ≠ 7) (h8 : first ≠ 8) (raw : List (Fin 2))
    (hsearch : ∀ s : GalilVM, PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get s) →
      ∀ a : Bool, ∃ v, searchEffect (PofC centre place entry raw) a s v)
    (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM)
    (hs : SegReached centre place entry q first raw c r c' t)
    (hseg : ∃ es, WatchSegE (PofC centre place entry raw) q first 2048 es c r c' t)
    (hE : EntryCounters raw r)
    (hnr : c'.replaying = false) (hc1 : c'.clock = 1) (hav : canRight t.right)
    (hmis : read (left t.left) ≠ read (right t.right)) :
    FallbackRoute centre place entry q first raw c r := by
  obtain ⟨es, hw⟩ := hseg
  exact fallbackRoute_of_mismatch centre place entry q hq0 first h7 h8 raw c r c' t hs hnr hc1
    hav hmis (fallbackCounters_of_seg _ q first 2048 hw hs.center hE hav)
    (fallbackTick_of_mismatch centre place entry raw hsearch t hs.idle hs.search)

#print axioms scanInvariant_watchSegE
#print axioms radiusRep_watchSegE
#print axioms canonical_length_watchSegE
#print axioms entryCounters_of_inv
#print axioms entryCounters_of_invScan
#print axioms radius_lt_centre
#print axioms fallbackCounters_of_seg
#print axioms fallbackTick_of_mismatch
#print axioms fallbackRoute_of_mismatch'

end PalPeg.GalilGlueBLeaves
