import PalPeg.GalilScaffoldTopCentre

/-!
# Heads and counters along segments

The scan events of any event-indexed segment drive the heads
(`ScanEvents`), and the radius counts the matched comparisons; the centre,
`periodOnly` and the counters' canonical form are kept. The same for the
matched scan segments of the rounds. No condition on the chain.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-- Heads and counters of an event-indexed segment. -/
theorem watchSegE_heads (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) {es : List Bool}
    {c c' : Control} {s t : GalilVM} (h : WatchSegE P q first delay es c s c' t) :
    (∀ (raw : List (Fin 2)) (c0 r : ℕ), ScanEvents raw c0 r s.left s.right es t.left t.right) ∧
      t.periodOnly = s.periodOnly ∧
      value t.radius = value s.radius + es.count true ∧
      (Canonical s.radius → Canonical t.radius) ∧ (Canonical s.length → Canonical t.length) := by
  induction h with
  | stop c s =>
    exact ⟨fun _ _ _ => .stop _ _ _, rfl, by simp, id, id⟩
  | wait c s s' _ _ _ hb _ ih =>
    obtain ⟨hsc, hpo, hrad, hrc, hlc⟩ := ih
    obtain ⟨hl, hr, _, hpo', hrad', hlen'⟩ := background_frame P q first hb
    refine ⟨fun raw c0 r => ?_, by rw [hpo, hpo'], by rw [hrad, hrad']; simp,
      fun h0 => hrc (by rw [hrad']; exact h0), fun h0 => hlc (by rw [hlen']; exact h0)⟩
    have := hsc raw c0 r
    rw [hl, hr] at this
    exact .skip _ _ _ this
  | count c s s' _ _ _ _ hb _ ih =>
    obtain ⟨hsc, hpo, hrad, hrc, hlc⟩ := ih
    obtain ⟨hl, hr, _, hpo', hrad', hlen'⟩ := background_frame P q first hb
    refine ⟨fun raw c0 r => ?_, by rw [hpo, hpo'], by rw [hrad, hrad']; simp,
      fun h0 => hrc (by rw [hrad']; exact h0), fun h0 => hlc (by rw [hlen']; exact h0)⟩
    have := hsc raw c0 r
    rw [hl, hr] at this
    exact .skip _ _ _ this
  | «match» c s vs vq o _ _ ha _ _ hcmp hmt _ _ _ ih =>
    obtain ⟨hsc, hpo, hrad, hrc, hlc⟩ := ih
    have hmatch : read (left s.left) = read (right s.right) := by
      obtain ⟨⟨hl0, hr0, _⟩, _⟩ := hcmp
      rw [scanLens.get_set] at hl0 hr0
      have := matched_parts P q first hmt
      rw [hl0, hr0] at this; exact this
    obtain ⟨hl, hr, _⟩ := compare_parts P q first hcmp hmatch
    rw [afterCompare_periodOnly] at hpo
    rw [afterCompare_radius, inc_value] at hrad
    rw [afterCompare_radius] at hrc
    rw [afterCompare_length] at hlc
    refine ⟨fun raw c0 r => ?_, hpo, by rw [hrad]; simp; ring,
      fun hc => hrc (inc_canonical _ hc), fun hc => hlc (inc_canonical _ (inc_canonical _ hc))⟩
    have := hsc raw c0 (r+1)
    rw [afterCompare_left, afterCompare_right, hl, hr] at this
    exact .matched _ _ _ ha hmatch this
  | matchIdle c s vs vq o _ _ ha _ _ hl hr _ hmt _ _ _ _ ih =>
    obtain ⟨hsc, hpo, hrad, hrc, hlc⟩ := ih
    have hmatch : read (left s.left) = read (right s.right) := by
      have := matched_parts P q first hmt
      rw [hl, hr] at this; exact this
    rw [afterCompare_periodOnly] at hpo
    rw [afterCompare_radius, inc_value] at hrad
    rw [afterCompare_radius] at hrc
    rw [afterCompare_length] at hlc
    refine ⟨fun raw c0 r => ?_, hpo, by rw [hrad]; simp; ring,
      fun hc => hrc (inc_canonical _ hc), fun hc => hlc (inc_canonical _ (inc_canonical _ hc))⟩
    have := hsc raw c0 (r+1)
    rw [afterCompare_left, afterCompare_right, hl, hr] at this
    exact .matched _ _ _ ha hmatch this
  | countR c s s' _ _ _ _ hb _ ih =>
    obtain ⟨hsc, hpo, hrad, hrc, hlc⟩ := ih
    obtain ⟨hl, hr, _, hpo', hrad', hlen'⟩ := background_frame P q first hb
    refine ⟨fun raw c0 r => ?_, by rw [hpo, hpo'], by rw [hrad, hrad']; simp,
      fun h0 => hrc (by rw [hrad']; exact h0), fun h0 => hlc (by rw [hlen']; exact h0)⟩
    have := hsc raw c0 r
    rw [hl, hr] at this
    exact .skip _ _ _ this
  | matchIdleR c s vs vq o _ _ _ ha _ hl hr _ hmt _ _ _ _ ih =>
    obtain ⟨hsc, hpo, hrad, hrc, hlc⟩ := ih
    have hmatch : read (left s.left) = read (right s.right) := by
      have := matched_parts P q first hmt
      rw [hl, hr] at this; exact this
    rw [replayDec_periodOnly, afterCompare_periodOnly] at hpo
    rw [replayDec_radius, afterCompare_radius, inc_value] at hrad
    rw [replayDec_radius, afterCompare_radius] at hrc
    rw [replayDec_length, afterCompare_length] at hlc
    refine ⟨fun raw c0 r => ?_, hpo, by rw [hrad]; simp; ring,
      fun hc => hrc (inc_canonical _ hc), fun hc => hlc (inc_canonical _ (inc_canonical _ hc))⟩
    have := hsc raw c0 (r+1)
    rw [replayDec_left, replayDec_right, afterCompare_left, afterCompare_right, hl, hr] at this
    exact .matched _ _ _ ha hmatch this

/-- Counters of a matched scan segment. -/
theorem scanSeg_counters (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) {n : ℕ}
    {c c' : Control} {s t : GalilVM} (h : ScanSeg P q first delay n c s c' t) :
    (Canonical s.radius → Canonical t.radius) ∧ (Canonical s.length → Canonical t.length) := by
  induction h with
  | stop c s => exact ⟨id, id⟩
  | wait c s s' _ _ _ hb _ ih =>
    obtain ⟨hrc, hlc⟩ := ih
    obtain ⟨_, _, _, _, hrad', hlen'⟩ := background_frame P q first hb
    exact ⟨fun h0 => hrc (by rw [hrad']; exact h0), fun h0 => hlc (by rw [hlen']; exact h0)⟩
  | count c s s' _ _ _ _ hb _ ih =>
    obtain ⟨hrc, hlc⟩ := ih
    obtain ⟨_, _, _, _, hrad', hlen'⟩ := background_frame P q first hb
    exact ⟨fun h0 => hrc (by rw [hrad']; exact h0), fun h0 => hlc (by rw [hlen']; exact h0)⟩
  | «match» c s vs vq o _ _ _ _ _ _ _ _ _ _ _ ih =>
    obtain ⟨hrc, hlc⟩ := ih
    rw [afterCompare_radius] at hrc
    rw [afterCompare_length] at hlc
    exact ⟨fun hc => hrc (inc_canonical _ hc), fun hc => hlc (inc_canonical _ (inc_canonical _ hc))⟩

#print axioms watchSegE_heads
#print axioms scanSeg_counters

end PalPeg.GalilScaffoldChainInputSupply
