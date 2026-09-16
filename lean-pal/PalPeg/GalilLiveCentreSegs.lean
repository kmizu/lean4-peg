import PalPeg.GalilLiveCentreReplay
import PalPeg.GalilScaffoldTopWatchSeg
import PalPeg.GalilScaffoldTopScanSeg

/-!
# The centre invariant, through the watch and scan segments

The centre invariant `MInv` established in `GalilLiveCentreReplay` for
chain-idle segments (`WatchSegE`) also holds along the two other segment
kinds, `WatchSeg` and `ScanSeg`, whose constructors (`stop`, `wait`, `count`,
`match`) are a subset of `WatchSegE`'s with no replay steps.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open Manacher GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-- The invariant along a general watch segment. -/
theorem minv_watchSeg (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    {c c' : Control} {s t : GalilVM} (h : WatchSeg P q first delay c s c' t) :
    ∀ r, ScanInvariant raw (position s.center) r s.left s.right → MInv raw c s → MInv raw c' t := by
  induction h with
  | stop c s => intro r _ hM; exact hM
  | wait c s s' _ _ _ hb _ ih =>
    intro r hi hM
    obtain ⟨hl, hr, _, hC, _, _, _, _, _, hrep, _, _⟩ := backgroundS_fields P q first hb
    refine ih r (by rw [hl, hr, hC]; exact hi) (minv_same rfl hr hC hrep hM)
  | count c s s' _ _ _ _ hb _ ih =>
    intro r hi hM
    obtain ⟨hl, hr, _, hC, _, _, _, _, _, hrep, _, _⟩ := backgroundS_fields P q first hb
    refine ih r (by rw [hl, hr, hC]; exact hi) (minv_same rfl hr hC hrep hM)
  | «match» c s vs vq o hm hr ha hc hne hcmp hmt hq ho _ ih =>
    intro r hi hM
    have hmatch : read (left s.left) = read (right s.right) := by
      obtain ⟨⟨hl0, hr0, _⟩, _⟩ := hcmp
      rw [scanLens.get_set] at hl0 hr0
      have := matched_parts P q first hmt
      rw [hl0, hr0] at this; exact this
    obtain ⟨hl, hrr, _⟩ := compare_parts P q first hcmp hmatch
    have hi' := matched_invariant raw P q first vq hcmp hmt ha hi
    exact ih (r+1) hi' (minv_match o _ hr hl hrr ha hmatch hi hM)

/-- The invariant along a scan segment. -/
theorem minv_scanSeg (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) {n : ℕ}
    {c c' : Control} {s t : GalilVM} (h : ScanSeg P q first delay n c s c' t) :
    ∀ r, ScanInvariant raw (position s.center) r s.left s.right → MInv raw c s → MInv raw c' t := by
  induction h with
  | stop c s => intro r _ hM; exact hM
  | wait c s s' _ _ _ hb _ ih =>
    intro r hi hM
    obtain ⟨hl, hr, _, hC, _, _, _, _, _, hrep, _, _⟩ := backgroundS_fields P q first hb
    refine ih r (by rw [hl, hr, hC]; exact hi) (minv_same rfl hr hC hrep hM)
  | count c s s' _ _ _ _ hb _ ih =>
    intro r hi hM
    obtain ⟨hl, hr, _, hC, _, _, _, _, _, hrep, _, _⟩ := backgroundS_fields P q first hb
    refine ih r (by rw [hl, hr, hC]; exact hi) (minv_same rfl hr hC hrep hM)
  | «match» c s vs vq o hm hr ha hc hcont hcmp hmt hwatch hq ho _ ih =>
    intro r hi hM
    have hmatch : read (left s.left) = read (right s.right) := by
      obtain ⟨⟨hl0, hr0, _⟩, _⟩ := hcmp
      rw [scanLens.get_set] at hl0 hr0
      have := matched_parts P q first hmt
      rw [hl0, hr0] at this; exact this
    obtain ⟨hl, hrr, _⟩ := compare_parts P q first hcmp hmatch
    have hi' := matched_invariant raw P q first vq hcmp hmt ha hi
    exact ih (r+1) hi' (minv_match o _ hr hl hrr ha hmatch hi hM)

#print axioms minv_watchSeg
#print axioms minv_scanSeg

end PalPeg.GalilScaffoldChainInputSupply
