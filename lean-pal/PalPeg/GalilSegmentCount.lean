import PalPeg.GalilScaffoldTopOutputCycle

/-!
# Counting ticks in `WatchSegE` and `ScanSeg`

Two structural facts about the tick-counting segments defined in
`GalilScaffoldTopWatchSegE` and `GalilScaffoldTopScanSeg`:

* `WatchSegE` takes exactly one `Tick` of `galilFrameS` per event of its
  index list (`watchSegE_steps_length`), refining the existential count of
  `watchSegE_steps` to the exact value `es.length`.
* The controller's clock stays within the match delay along a `WatchSegE`
  run whenever it starts within the delay (`watchSegE_clock_le`), since
  every constructor either leaves the clock unchanged, decrements it, or
  resets it to `delay`.
* `ScanSeg` with `n` matched comparisons takes at least `n` ticks
  (`scanSeg_steps_ge`), since every `match` constructor contributes one
  tick and increases the match count by one.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-- An event-indexed segment takes exactly one tick per event. -/
theorem watchSegE_steps_length (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) {es : List Bool}
    {c c' : Control} {s t : GalilVM} (h : WatchSegE P q first delay es c s c' t) :
    Steps (galilFrameS P q first) delay es.length ⟨c, s⟩ ⟨c', t⟩ := by
  induction h with
  | stop c s => simpa using Steps.zero (F := galilFrameS P q first) (delay := delay) (⟨c, s⟩)
  | wait c s s' hm hr hn hb _ ih =>
    simpa using Steps.succ (.scan_wait c s s' hm ⟨hr, hn⟩ hb) ih
  | count c s s' hm hr ha hc hb _ ih =>
    simpa using Steps.succ (.scan_count c s s' hm (Or.inr ha) hc hb) ih
  | «match» c s vs vq o hm hr ha hc hne hcmp hmt hq ho _ ih =>
    simpa using Steps.succ (scan_match_S P q first delay c s vs vq o hm hr ha hc hne hcmp hmt hq ho) ih
  | matchIdle c s vs vq o hm hr ha hc hidle hl hrr hvs hmt hq hnf ho _ ih =>
    simpa using
      Steps.succ (scan_match_idle_S P q first delay c s vs vq o hm hr ha hc hidle hl hrr hvs hmt hq hnf ho) ih
  | countR c s s' hm hr hc hidle hb _ ih =>
    simpa using Steps.succ (.scan_count c s s' hm (Or.inl hr) hc hb) ih
  | matchIdleR c s vs vq o hm hr hc ha hidle hl hrr hvs hmt hq hnf ho _ ih =>
    have ht := scan_match_idle_S' P q first delay c s vs vq o hm (Or.inl hr) hc hidle hl hrr hvs hmt hq hnf
      (by rw [hr]; exact ho)
    rw [hr] at ht
    simpa using Steps.succ (by simpa using ht) ih

/-- The clock stays within the match delay along a `WatchSegE` run whenever
it starts within the delay: `wait` leaves the clock unchanged, `count`/
`countR` only decrement it, and the two match constructors reset it to
`delay`. -/
theorem watchSegE_clock_le (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) {es : List Bool}
    {c c' : Control} {s t : GalilVM} (h : WatchSegE P q first delay es c s c' t)
    (hc : c.clock ≤ delay) : c'.clock ≤ delay := by
  induction h with
  | stop c s => exact hc
  | wait c s s' hm hr hn hb _ ih => exact ih hc
  | count c s s' hm hr ha hc' hb _ ih => exact ih (by dsimp only; omega)
  | «match» c s vs vq o hm hr ha hc' hne hcmp hmt hq ho _ ih => exact ih (le_refl delay)
  | matchIdle c s vs vq o hm hr ha hc' hidle hl hrr hvs hmt hq hnf ho _ ih => exact ih (le_refl delay)
  | countR c s s' hm hr hc' hidle hb _ ih => exact ih (by dsimp only; omega)
  | matchIdleR c s vs vq o hm hr hc' ha hidle hl hrr hvs hmt hq hnf ho _ ih => exact ih (le_refl delay)

/-- A matched scan segment of `n` matches takes at least `n` ticks: every
`match` constructor contributes exactly one tick and increases the match
count by one, while `wait`/`count` contribute one tick without changing the
match count. -/
theorem scanSeg_steps_ge (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) {n : ℕ}
    {c c' : Control} {s t : GalilVM} (h : ScanSeg P q first delay n c s c' t) :
    ∃ k, n ≤ k ∧ Steps (galilFrameS P q first) delay k ⟨c, s⟩ ⟨c', t⟩ := by
  induction h with
  | stop c s => exact ⟨0, le_refl 0, .zero _⟩
  | wait c s s' hm hr hn hb _ ih =>
    obtain ⟨k, hk, hs⟩ := ih
    exact ⟨k + 1, by omega, .succ (.scan_wait c s s' hm ⟨hr, hn⟩ hb) hs⟩
  | count c s s' hm hr ha hc hb _ ih =>
    obtain ⟨k, hk, hs⟩ := ih
    exact ⟨k + 1, by omega, .succ (.scan_count c s s' hm (Or.inr ha) hc hb) hs⟩
  | «match» c s vs vq o hm hr ha hc hcont hcmp hmt hwatch hq ho _ ih =>
    obtain ⟨k, hk, hs⟩ := ih
    have hmatch : read (left s.left) = read (right s.right) := by
      obtain ⟨⟨hl0, hr0, _⟩, _⟩ := hcmp
      rw [scanLens.get_set] at hl0 hr0
      have := matched_parts P q first hmt
      rw [hl0, hr0] at this; exact this
    obtain ⟨w', hw'⟩ := hwatch
    have hne : s.chain ≠ .idle :=
      chainTick_source_ne_idle (compare_parts P q first hcmp hmatch).2.2 (by rw [hw']; intro h0; cases h0)
    exact ⟨k + 1, by omega, .succ (scan_match_S P q first delay c s vs vq o hm hr ha hc hne hcmp hmt hq ho) hs⟩

#print axioms watchSegE_steps_length
#print axioms watchSegE_clock_le
#print axioms scanSeg_steps_ge

end PalPeg.GalilScaffoldChainInputSupply
