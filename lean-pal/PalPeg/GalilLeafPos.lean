import PalPeg.GalilLeafMismatch

/-!
# The `hpos` residue of `GalilLeafMismatch.hmismatch_of_residues`

The residue asks, at a segment exit `t` that mismatches, for

    `position (right t.right) ≤ 2 * m - 1`,

from the entry bound `position r.right ≤ 2 * m - 1` and `SegReachedW`.

**As stated it is false.**  `SegReachedW` records nothing about the checkpoint
`m`: `GalilOracleDischarge.SegReached` carries the run, the centre, the mode,
the clock, `MInv`, the scan invariant and the head representations, and no
bound involving `m`; and along the segment the right head *moves*, by
`GalilOneFallback.watchSegE_right_position`:

    `position t.right = position r.right + es.count true`.

So already the empty segment out of an entry at the extreme allowed place
`position r.right = 2 * m - 1` refutes it (`not_hpos_of_report_place`): the
comparison lands on `2 * m`, the gap place just past the checkpoint.

**No weaker bound helps the callers.**  `GalilOracleMC2.FallbackRouteMC2`
needs `≤ 2 * m - 1` at the *mismatch place* and not merely at the landing
`sT`, because the landing does not rewind the right head:
`GalilCostedFallback.costedRun_fallback_zero` ends with
`position t.right = position (right s.right)` (and the replayed landing is put
back on the same place by `replay_right_eq_place`), and
`cycleOutMC2C_of_fallback` feeds exactly that equation into
`CycleOutMC2C`'s `position sT.right ≤ 2 * m - 1`.  Only the centre and the
left head are rewound.  The same holds for `GalilTraceCost`'s
`CycleOutMC`/`GalilOracleMC.FallbackRouteMC`.

**What is true.**  The residue is equivalent to `position t.right ≤ 2 * m - 2`
(`hpos_iff_place`), i.e. to the segment not having passed the checkpoint; the
`AtTarget` exit satisfies it with equality (`hpos_of_atTarget`), and in the
only bad case the exit state *is* the report point at `m`
(`reportPointAt_of_seg`, `hpos_or_reportPoint`).  `hpos_of_segBudget` is the
drop-in replacement for the residue: it derives it from a budget on the
segment, which is where the missing fact belongs, since `hsegmentM` — the leaf
that produces `SegReachedW` together with `AtTarget m c' t ∨ SegEnd …` — is
the only place that knows the segment is target-bounded, and it is itself
still an assumption in `GalilOracleMC2.cycleOracleMC2C_of_pieces`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.GalilLeafPos

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton PalPeg.GalilOracleDischarge PalPeg.GalilOracleLocal
open PalPeg.GalilInvPlus PalPeg.GalilInvPlus2 PalPeg.GalilOracleMC PalPeg.GalilOracleMC2
open PalPeg.GalilOracleM PalPeg.GalilOneFallback PalPeg.GalilFinalAssembly2

/-! ## 1. One comparison is one place -/

/-- The comparison the mismatch leaf is about moves the right head by exactly
one place.  This is the whole content of the residue: it turns the place of the
*comparison* into the place of the segment *exit*. -/
theorem right_succ {w : List (Fin 2)} {C Rad : ℕ} {lh rh : PlaceHead}
    (hi : ScanInvariant w C Rad lh rh) (hav : canRight rh) :
    position (right rh) = position rh + 1 :=
  right_position rh hav (represented_position _ w hi.rightRep hi.rightPresent).1

/-- **The residue, restated.**  `hpos` says exactly that the segment exit is
still strictly before the checkpoint place `2m-1`. -/
theorem hpos_iff_place {w : List (Fin 2)} {m C Rad : ℕ} {lh rh : PlaceHead} (hm1 : 1 ≤ m)
    (hi : ScanInvariant w C Rad lh rh) (hav : canRight rh) :
    position (right rh) ≤ 2 * m - 1 ↔ position rh ≤ 2 * m - 2 := by
  rw [right_succ hi hav]; omega

/-! ## 2. Where the segment exit sits -/

/-- **The segment moves the right head.**  `watchSegE_right_position` at an
`InvLPC` entry: the exit place is the entry place plus the number of
comparisons the segment made.  Hence nothing in `SegReachedW` alone bounds the
exit by the checkpoint. -/
theorem seg_right_place (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (w : List (Fin 2)) {c : Control} {r : GalilVM} {c' : Control} {t : GalilVM} {es : List Bool}
    (hIC : InvLPC w c r)
    (hw : WatchSegE (PofC centre place entry w) q first 2048 es c r c' t) :
    position t.right = position r.right + es.count true := by
  obtain ⟨⟨R0, hi0⟩, -, -⟩ := invL_entry (invLPC_invL hIC)
  exact (watchSegE_right_position w (PofC centre place entry w) q first 2048 hw hi0).2

/-! ## 3. The good case: the target-bounded exit -/

/-- The residue, from the bound that actually carries it. -/
theorem hpos_of_le (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (m : ℕ) (hm1 : 1 ≤ m) {c : Control} {r : GalilVM} {c' : Control}
    {t : GalilVM} (hs : SegReachedW centre place entry q first w c r c' t)
    (hav : canRight t.right) (hb : position t.right ≤ 2 * m - 2) :
    position (right t.right) ≤ 2 * m - 1 := by
  obtain ⟨R, hi⟩ := hs.1.scan
  exact (hpos_iff_place hm1 hi hav).2 hb

/-- **The `AtTarget` exit satisfies the residue, with equality.**  `AtTarget`
puts the right head on `2m-2`, the gap just before the checkpoint letter, so
the comparison lands exactly on `2m-1`. -/
theorem hpos_of_atTarget (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (m : ℕ) (hm1 : 1 ≤ m) {c : Control} {r : GalilVM} {c' : Control}
    {t : GalilVM} (hs : SegReachedW centre place entry q first w c r c' t)
    (hT : AtTarget m c' t) :
    position (right t.right) = 2 * m - 1 := by
  obtain ⟨R, hi⟩ := hs.1.scan
  rw [right_succ hi hT.2.2.1, hT.2.2.2.1]
  omega

/-! ## 4. The bad case: the exit already *is* the report point -/

/-- **The residue is false at the checkpoint place.**  If the segment exit
already sits on `2m-1` — which the residue's own hypothesis
`position r.right ≤ 2 * m - 1` permits, with `es.count true = 0` — then the
comparison lands on the gap place `2m`, and the conclusion fails. -/
theorem not_hpos_of_report_place (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (m : ℕ) (hm1 : 1 ≤ m) {c : Control} {r : GalilVM} {c' : Control}
    {t : GalilVM} (hs : SegReachedW centre place entry q first w c r c' t)
    (hav : canRight t.right) (hat : position t.right = 2 * m - 1) :
    ¬ position (right t.right) ≤ 2 * m - 1 := by
  obtain ⟨R, hi⟩ := hs.1.scan
  have hm : 1 ≤ m := hm1
  rw [right_succ hi hav, hat]
  omega

/-- The refutation at the extreme entry allowed by the residue's hypotheses:
an entry on `2m-1` and a segment with no comparison. -/
theorem not_hpos_of_tight_entry (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (m : ℕ) (hm1 : 1 ≤ m) {c : Control} {r : GalilVM} {c' : Control}
    {t : GalilVM} {es : List Bool} (hIC : InvLPC w c r)
    (hs : SegReachedW centre place entry q first w c r c' t)
    (hw : WatchSegE (PofC centre place entry w) q first 2048 es c r c' t)
    (hav : canRight t.right) (hentry : position r.right = 2 * m - 1)
    (hquiet : es.count true = 0) :
    ¬ position (right t.right) ≤ 2 * m - 1 :=
  not_hpos_of_report_place centre place entry q first w m hm1 hs hav
    (by rw [seg_right_place centre place entry q first w hIC hw, hentry, hquiet]; omega)

/-- **In the bad case the exit state is the report point at `m`.**  Every field
of `ReportPointAt` is already in `SegReachedW` plus the leaf's own
`c'.replaying = false`; only `atPlace` is new.  So the `report` constructor of
`FallbackRouteMC2`, not `landed`/`replaying`, is the route there. -/
theorem reportPointAt_of_seg (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (m : ℕ) {c : Control} {r : GalilVM} {c' : Control} {t : GalilVM}
    (hs : SegReachedW centre place entry q first w c r c' t) (hnr : c'.replaying = false)
    (hm1 : 1 ≤ m) (hmle : m ≤ w.length) (hat : position t.right = 2 * m - 1) :
    PalPeg.GalilReportPrefix.ReportPointAt w m ⟨c', t⟩ :=
  ⟨hnr, hs.1.scan, hs.1.minv, hat, hm1, hmle⟩

/-- **The true dichotomy.**  Under the exit bound the segment construction is
supposed to give (`position t.right ≤ 2m-1`), either the residue holds, or the
exit is the report point at `m`. -/
theorem hpos_or_reportPoint (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (m : ℕ) (hm1 : 1 ≤ m) (hmle : m ≤ w.length) {c : Control} {r : GalilVM}
    {c' : Control} {t : GalilVM} (hs : SegReachedW centre place entry q first w c r c' t)
    (hnr : c'.replaying = false) (hav : canRight t.right)
    (hle : position t.right ≤ 2 * m - 1) :
    position (right t.right) ≤ 2 * m - 1 ∨
      PalPeg.GalilReportPrefix.ReportPointAt w m ⟨c', t⟩ := by
  rcases Nat.lt_or_ge (position t.right) (2 * m - 1) with hlt | hge
  · exact Or.inl (hpos_of_le centre place entry q first w m hm1 hs hav (by omega))
  · exact Or.inr (reportPointAt_of_seg centre place entry q first w m hs hnr hm1 hmle (by omega))

/-! ## 5. The drop-in replacement for the residue -/

/-- **`hpos` from a segment budget.**  Exactly the shape
`GalilLeafMismatch.hmismatch_of_residues` takes, with the missing fact moved to
where it lives: the segment makes at most `2m-2 - position r.right`
comparisons, i.e. it stops at the `AtTarget` state rather than crossing the
checkpoint.  Discharging `hbudget` belongs to `hsegmentM`. -/
theorem hpos_of_segBudget (entry q : ℕ) (first : Fin 9)
    (hbudget : ∀ (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) (c' : Control)
      (t : GalilVM) (es : List Bool), 1 ≤ m → m ≤ w.length → InvLPC w c r →
      position r.right ≤ 2 * m - 1 →
      WatchSegE (PofC centreC placeC entry w) q first 2048 es c r c' t →
      canRight t.right → position r.right + es.count true ≤ 2 * m - 2) :
    ∀ (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ w.length → InvLPC w c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centreC placeC entry q first w c r c' t → canRight t.right →
      position (right t.right) ≤ 2 * m - 1 := by
  intro w m c r c' t hm1 hmle hIC hrt hs hav
  obtain ⟨-, es, hw⟩ := id hs
  refine hpos_of_le centreC placeC entry q first w m hm1 hs hav ?_
  rw [seg_right_place centreC placeC entry q first w hIC hw]
  exact hbudget w m c r c' t es hm1 hmle hIC hrt hw hav

#print axioms right_succ
#print axioms hpos_iff_place
#print axioms seg_right_place
#print axioms hpos_of_le
#print axioms hpos_of_atTarget
#print axioms not_hpos_of_report_place
#print axioms not_hpos_of_tight_entry
#print axioms reportPointAt_of_seg
#print axioms hpos_or_reportPoint
#print axioms hpos_of_segBudget

end PalPeg.GalilLeafPos
