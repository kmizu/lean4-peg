import PalPeg.GalilSpanCounter

/-!
# The leftmost live centre along a scan segment

A matched comparison moves the right head one place to the right and grows
the scan invariant's radius by one, so the centre — fixed along the whole
segment — stays live at the new right place; `leftmost_match` then keeps it
leftmost. A non-matching event leaves both heads where they are, so nothing
is to prove. Running this along the event list of a segment
(`ScanEvents`) gives the segment-level statements for `WatchSegE`,
`WatchSeg` and `ScanSeg`: if the centre is the leftmost live centre at the
right head's place when the segment starts, it still is when it ends.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open Manacher GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-- Along the scan events of a segment the centre stays the leftmost live
centre at the right head's place. -/
theorem leftmost_scanEvents {raw : List (Fin 2)} {c0 r : ℕ} {l r0 : PlaceHead} {es : List Bool}
    {l' r' : PlaceHead} (he : ScanEvents raw c0 r l r0 es l' r')
    (hi : ScanInvariant raw c0 r l r0) (hL : Leftmost raw (position r0) c0) :
    Leftmost raw (position r') c0 := by
  revert hi hL
  induction he with
  | stop r l rr => exact fun _ h => h
  | skip r l rr _ ih => exact ih
  | matched r l rr hc hm _ ih =>
    intro hi hL
    have hi' := scan_matched hi hc hm
    refine ih hi' ?_
    have hpos : position (right rr) = position rr + 1 :=
      right_position rr hc (represented_position rr.head raw hi.rightRep hi.rightPresent).1
    have hlive : Live raw (position rr + 1) c0 := by
      rw [← hpos]; exact live_of_scanInvariant hi'
    rw [hpos]
    exact leftmost_match hL hlive

/-- An event-indexed segment keeps the leftmost live centre. -/
theorem leftmost_watchSegE (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    {es : List Bool} {c c' : Control} {s t : GalilVM} (h : WatchSegE P q first delay es c s c' t)
    {r : ℕ} (hi : ScanInvariant raw (position s.center) r s.left s.right)
    (hL : Leftmost raw (position s.right) (position s.center)) :
    Leftmost raw (position t.right) (position t.center) := by
  rw [watchSegE_center P q first delay h]
  exact leftmost_scanEvents ((watchSegE_heads P q first delay h).1 raw (position s.center) r) hi hL

/-- A general segment (any non-idle chain) keeps the leftmost live centre. -/
theorem leftmost_watchSeg (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    {c c' : Control} {s t : GalilVM} (h : WatchSeg P q first delay c s c' t) (hne : s.chain ≠ .idle)
    {r : ℕ} (hi : ScanInvariant raw (position s.center) r s.left s.right)
    (hL : Leftmost raw (position s.right) (position s.center)) :
    Leftmost raw (position t.right) (position t.center) := by
  obtain ⟨es, _, hsc, hcen, _⟩ := watchSeg_events P q first delay h hne
  rw [hcen]
  exact leftmost_scanEvents (hsc raw (position s.center) r) hi hL

/-- The scan events of a matched scan segment. -/
theorem scanSeg_heads (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) {n : ℕ}
    {c c' : Control} {s t : GalilVM} (h : ScanSeg P q first delay n c s c' t) :
    ∃ es : List Bool,
      ∀ (raw : List (Fin 2)) (c0 r : ℕ), ScanEvents raw c0 r s.left s.right es t.left t.right := by
  induction h with
  | stop c s => exact ⟨[], fun _ _ _ => .stop _ _ _⟩
  | wait c s s' _ _ _ hb _ ih =>
    obtain ⟨es, hsc⟩ := ih
    obtain ⟨hl, hr, _⟩ := background_frame P q first hb
    refine ⟨false :: es, fun raw c0 r => ?_⟩
    have hev := hsc raw c0 r
    rw [hl, hr] at hev
    exact .skip _ _ _ hev
  | count c s s' _ _ _ _ hb _ ih =>
    obtain ⟨es, hsc⟩ := ih
    obtain ⟨hl, hr, _⟩ := background_frame P q first hb
    refine ⟨false :: es, fun raw c0 r => ?_⟩
    have hev := hsc raw c0 r
    rw [hl, hr] at hev
    exact .skip _ _ _ hev
  | «match» c s vs vq o _ _ ha _ _ hcmp hmt _ _ _ _ ih =>
    obtain ⟨es, hsc⟩ := ih
    have hmatch : read (left s.left) = read (right s.right) := by
      obtain ⟨⟨hl0, hr0, _⟩, _⟩ := hcmp
      rw [scanLens.get_set] at hl0 hr0
      have hp := matched_parts P q first hmt
      rw [hl0, hr0] at hp; exact hp
    obtain ⟨hl, hr, _⟩ := compare_parts P q first hcmp hmatch
    refine ⟨true :: es, fun raw c0 r => ?_⟩
    have hev := hsc raw c0 (r+1)
    rw [afterCompare_left, afterCompare_right, hl, hr] at hev
    exact .matched _ _ _ ha hmatch hev

/-- A matched scan segment keeps the leftmost live centre. -/
theorem leftmost_scanSeg (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    {n : ℕ} {c c' : Control} {s t : GalilVM} (h : ScanSeg P q first delay n c s c' t)
    {r : ℕ} (hi : ScanInvariant raw (position s.center) r s.left s.right)
    (hL : Leftmost raw (position s.right) (position s.center)) :
    Leftmost raw (position t.right) (position t.center) := by
  obtain ⟨es, hsc⟩ := scanSeg_heads P q first delay h
  rw [scanSeg_center P q first delay h]
  exact leftmost_scanEvents (hsc raw (position s.center) r) hi hL

#print axioms leftmost_scanEvents
#print axioms leftmost_watchSegE
#print axioms leftmost_watchSeg
#print axioms scanSeg_heads
#print axioms leftmost_scanSeg

end PalPeg.GalilScaffoldChainInputSupply
