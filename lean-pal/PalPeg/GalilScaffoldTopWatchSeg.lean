import PalPeg.GalilScaffoldTopFreshEntry

/-!
# General scan segments (the watch period)

`WatchSeg`: counting ticks and matched comparisons in scan mode with no
restriction on the chain (the chain may be copying, walking back, or
watching with a lag). It is a run of `galilFrameS`, and its events (one
`Bool` per tick, `true` at a matched comparison) drive the chain
(`ChainTicks`) and the heads (`ScanEvents`); the centre, `periodOnly`, and
the counters' canonical form are preserved, the radius counts the matches.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

inductive WatchSeg (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) :
    Control → GalilVM → Control → GalilVM → Prop
  | stop (c : Control) (s : GalilVM) : WatchSeg P q first delay c s c s
  | wait (c : Control) (s s' : GalilVM) {c' : Control} {t : GalilVM}
      (hm : c.mode = .scan) (hr : c.replaying = false) (hn : ¬ canRight s.right)
      (hb : (galilFrameS P q first).background s s')
      (rest : WatchSeg P q first delay c s' c' t) : WatchSeg P q first delay c s c' t
  | count (c : Control) (s s' : GalilVM) {c' : Control} {t : GalilVM}
      (hm : c.mode = .scan) (hr : c.replaying = false) (ha : canRight s.right) (hc : 1 < c.clock)
      (hb : (galilFrameS P q first).background s s')
      (rest : WatchSeg P q first delay {c with clock := c.clock - 1} s' c' t) :
      WatchSeg P q first delay c s c' t
  | match (c : Control) (s : GalilVM) (vs : ScanVM) (vq : SearchVM) (o : Bool) {c' : Control} {t : GalilVM}
      (hm : c.mode = .scan) (hr : c.replaying = false) (ha : canRight s.right) (hc : c.clock = 1)
      (hne : s.chain ≠ .idle)
      (hcmp : (galilFrame P q first).compare s (scanLens.set s vs))
      (hmt : (galilFrame P q first).matched (scanLens.set s vs))
      (hq : searchEffect P true s vq)
      (ho : refresh (galilFrame P q first) (afterCompare s vs vq) c.output o)
      (rest : WatchSeg P q first delay {c with clock := delay, output := o, replaying := false}
        (afterCompare s vs vq) c' t) :
      WatchSeg P q first delay c s c' t

/-- A general segment is a run of `galilFrameS`. -/
theorem watchSeg_steps (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    {c c' : Control} {s t : GalilVM} (h : WatchSeg P q first delay c s c' t) :
    ∃ k, Steps (galilFrameS P q first) delay k ⟨c, s⟩ ⟨c', t⟩ := by
  induction h with
  | stop c s => exact ⟨0, .zero _⟩
  | wait c s s' hm hr hn hb _ ih =>
    obtain ⟨k, hs⟩ := ih
    exact ⟨k+1, .succ (.scan_wait c s s' hm ⟨hr, hn⟩ hb) hs⟩
  | count c s s' hm hr ha hc hb _ ih =>
    obtain ⟨k, hs⟩ := ih
    exact ⟨k+1, .succ (.scan_count c s s' hm (Or.inr ha) hc hb) hs⟩
  | «match» c s vs vq o hm hr ha hc hne hcmp hmt hq ho _ ih =>
    obtain ⟨k, hs⟩ := ih
    exact ⟨k+1, .succ (scan_match_S P q first delay c s vs vq o hm hr ha hc hne hcmp hmt hq ho) hs⟩

theorem afterCompare_periodOnly (s : GalilVM) (vs : ScanVM) (vq : SearchVM) :
    (afterCompare s vs vq).periodOnly = s.periodOnly := rfl

/-- A background tick keeps everything outside the scan lens (and the search). -/
theorem background_frame (P : Shared) (q : ℕ) (first : Fin 9) {s s' : GalilVM}
    (hb : (galilFrameS P q first).background s s') :
    s'.left = s.left ∧ s'.right = s.right ∧
      s'.center = s.center ∧ s'.periodOnly = s.periodOnly ∧ s'.radius = s.radius ∧
      s'.length = s.length := by
  obtain ⟨hl, hr, _, hcen, hpo, hrad, hlen, _⟩ := backgroundS_fields P q first hb
  exact ⟨hl, hr, hcen, hpo, hrad, hlen⟩

/-- A chain tick never returns to `idle`. -/
theorem chainTick_ne_idle' {a : Bool} {x z : ChainVM} (h : ChainTick a x z) (hx : x ≠ .idle) :
    z ≠ .idle := by
  obtain ⟨y, hs, hm⟩ := h
  have hy : y ≠ .idle := by
    intro hy; subst hy
    cases hs; exact hx rfl
  cases a
  · simp at hm; subst hm; exact hy
  · simp at hm
    intro hz; subst hz
    cases hm; exact hy rfl

/-- The events of a general segment. -/
theorem watchSeg_events (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    {c c' : Control} {s t : GalilVM} (h : WatchSeg P q first delay c s c' t) (hne : s.chain ≠ .idle) :
    ∃ events : List Bool,
      ChainTicks events s.chain t.chain ∧
      (∀ (raw : List (Fin 2)) (c0 r : ℕ), ScanEvents raw c0 r s.left s.right events t.left t.right) ∧
      t.center = s.center ∧ t.periodOnly = s.periodOnly ∧
      value t.radius = value s.radius + events.count true ∧
      (Canonical s.radius → Canonical t.radius) ∧ (Canonical s.length → Canonical t.length) := by
  induction h with
  | stop c s =>
    exact ⟨[], .nil _, fun _ _ _ => .stop _ _ _, rfl, rfl, by simp, id, id⟩
  | wait c s s' _ _ _ hb _ ih =>
    have ht := backgroundS_chainTick P q first hb hne
    obtain ⟨es, hch, hsc, hcen, hpo, hrad, hrc, hlc⟩ := ih (chainTick_ne_idle' ht hne)
    obtain ⟨hl, hr, hcen', hpo', hrad', hlen'⟩ := background_frame P q first hb
    refine ⟨false :: es, .cons ht hch, fun raw c0 r => ?_, by rw [hcen, hcen'], by rw [hpo, hpo'],
      by rw [hrad, hrad']; simp, fun h0 => hrc (by rw [hrad']; exact h0), fun h0 => hlc (by rw [hlen']; exact h0)⟩
    have := hsc raw c0 r
    rw [hl, hr] at this
    exact .skip _ _ _ this
  | count c s s' _ _ _ _ hb _ ih =>
    have ht := backgroundS_chainTick P q first hb hne
    obtain ⟨es, hch, hsc, hcen, hpo, hrad, hrc, hlc⟩ := ih (chainTick_ne_idle' ht hne)
    obtain ⟨hl, hr, hcen', hpo', hrad', hlen'⟩ := background_frame P q first hb
    refine ⟨false :: es, .cons ht hch, fun raw c0 r => ?_, by rw [hcen, hcen'], by rw [hpo, hpo'],
      by rw [hrad, hrad']; simp, fun h0 => hrc (by rw [hrad']; exact h0), fun h0 => hlc (by rw [hlen']; exact h0)⟩
    have := hsc raw c0 r
    rw [hl, hr] at this
    exact .skip _ _ _ this
  | «match» c s vs vq o _ _ ha _ _ hcmp hmt _ _ _ ih =>
    have hmatch : read (left s.left) = read (right s.right) := by
      obtain ⟨⟨hl0, hr0, _⟩, _⟩ := hcmp
      rw [scanLens.get_set] at hl0 hr0
      have := matched_parts P q first hmt
      rw [hl0, hr0] at this; exact this
    obtain ⟨hl, hr, ht⟩ := compare_parts P q first hcmp hmatch
    obtain ⟨es, hch, hsc, hcen, hpo, hrad, hrc, hlc⟩ := ih (by rw [afterCompare_chain]; exact chainTick_ne_idle' ht hne)
    rw [afterCompare_chain] at hch
    rw [afterCompare_center] at hcen
    rw [afterCompare_periodOnly] at hpo
    rw [afterCompare_radius, inc_value] at hrad
    rw [afterCompare_radius] at hrc
    rw [afterCompare_length] at hlc
    refine ⟨true :: es, .cons ht hch, fun raw c0 r => ?_, hcen, hpo, by rw [hrad]; simp; ring,
      fun hc => hrc (inc_canonical _ hc), fun hc => hlc (inc_canonical _ (inc_canonical _ hc))⟩
    have := hsc raw c0 (r+1)
    rw [afterCompare_left, afterCompare_right, hl, hr] at this
    exact .matched _ _ _ ha hmatch this

#print axioms watchSeg_steps
#print axioms watchSeg_events

end PalPeg.GalilScaffoldChainInputSupply
