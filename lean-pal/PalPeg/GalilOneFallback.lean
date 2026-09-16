import PalPeg.GalilIntervalCost
import PalPeg.GalilFallbackLanding
import PalPeg.GalilReplayGeneral
import PalPeg.GalilReplaySegment
import PalPeg.GalilTickFun2

/-!
# At most one fallback per place

`GalilIntervalCost.AtMostOneFallback` is the single isolated hypothesis of the
interval cost.  This module proves its machine content.

A fallback is triggered at place `n1` by a mismatching comparison whose right
head moves onto `n1` (`FallbackTrigger`).  The fallback lands with the centre
`C' = n1 - R` and the right head on it (`fallback_landing`).

* `R = 0`: the landing right head is already at `n1`
  (`zero_radius_landing_at_place`); the place is consumed by the fallback.
* `R > 0`: the replay re-reads `C'+1 … n1`; every comparison of the replay
  matches — structurally, since neither `WatchSegE` nor `ReplayChainSeg` nor
  `FoundTick` has a mismatching comparison constructor
  (`watchSegE_comparison_matched`, `replayChainSeg_comparison_matched`,
  `foundTick_comparison_matched`) — and the last one is at `n1`
  (`replay_reaches_place_matched`).

After that the right head is at `n1` with the scan invariant, and along any
further scan segment it never goes back (`watchSegE_right_position`,
`replayChainSeg_right_position`), so the next mismatch trigger is at a place
`≥ n1 + 1` (`next_trigger_beyond`).  `at_most_one_fallback_per_place` packages
this; `atMostOneFallback_of_places` turns "all fallbacks of a place event are
triggered at one place, and at most one trigger is at that place" into
`AtMostOneFallback`.
-/

set_option autoImplicit false

namespace PalPeg.GalilOneFallback

open PalPeg PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilTickFun PalPeg.GalilTickFun2
  PalPeg.GalilReplayGeneral PalPeg.GalilBranchInvariants2 PalPeg.GalilSegmentConstruct
  PalPeg.GalilReplayChainSeg PalPeg.GalilChainTickable PalPeg.GalilReplaySegment
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-! ## 1. Scan events: every comparison matches, at a known place -/

/-- Each `true` event of a `ScanEvents` run from a scan invariant is a matched
comparison whose right head moves onto `c0 + r + (earlier matches) + 1`. -/
theorem scanEvents_true_split {raw : List (Fin 2)} {c0 : ℕ} :
    ∀ (es1 : List Bool) {es2 : List Bool} {r : ℕ} {l rr l' rr' : PlaceHead},
      ScanInvariant raw c0 r l rr → ScanEvents raw c0 r l rr (es1 ++ true :: es2) l' rr' →
      ∃ l1 rr1 : PlaceHead, ScanInvariant raw c0 (r + es1.count true) l1 rr1 ∧ canRight rr1 ∧
        read (left l1) = read (right rr1) ∧ position (right rr1) = c0 + r + es1.count true + 1 := by
  intro es1
  induction es1 with
  | nil =>
    intro es2 r l rr l' rr' hi he
    cases he with
    | matched _ _ _ hc hm _ =>
      have hp := right_position rr hc (represented_position _ raw hi.rightRep hi.rightPresent).1
      refine ⟨l, rr, by simpa using hi, hc, hm, ?_⟩
      rw [hp, hi.rightPos]; simp
  | cons a es1 ih =>
    intro es2 r l rr l' rr' hi he
    cases he with
    | skip _ _ _ rest =>
      obtain ⟨l1, rr1, h1, h2, h3, h4⟩ := ih hi rest
      exact ⟨l1, rr1, by simpa using h1, h2, h3, by simpa using h4⟩
    | matched _ _ _ hc hm rest =>
      obtain ⟨l1, rr1, h1, h2, h3, h4⟩ := ih (scan_matched hi hc hm) rest
      refine ⟨l1, rr1, ?_, h2, h3, ?_⟩
      · have e : r + 1 + es1.count true = r + (true :: es1).count true := by simp; omega
        rw [← e]; exact h1
      · rw [h4]; simp; omega

/-- A list with `k+1` `true`s splits at its `(k+1)`-st `true`. -/
theorem split_at_true : ∀ (es : List Bool) (k : ℕ), es.count true = k + 1 →
    ∃ es1 es2 : List Bool, es = es1 ++ true :: es2 ∧ es1.count true = k ∧ es2.count true = 0 := by
  intro es
  induction es with
  | nil => intro k h; simp at h
  | cons a es ih =>
    intro k h
    cases a with
    | false =>
      obtain ⟨es1, es2, h1, h2, h3⟩ := ih k (by simpa using h)
      exact ⟨false :: es1, es2, by rw [h1]; rfl, by simpa using h2, h3⟩
    | true =>
      cases k with
      | zero => exact ⟨[], es, rfl, by simp, by simpa using h⟩
      | succ k =>
        obtain ⟨es1, es2, h1, h2, h3⟩ := ih k (by simp at h; omega)
        exact ⟨true :: es1, es2, by rw [h1]; rfl, by simp [h2], h3⟩

/-! ## 2. No mismatch inside the segments (structural) -/

/-- Every comparison of a `WatchSegE` segment is a match. -/
theorem watchSegE_comparison_matched (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    (es1 : List Bool) {es2 : List Bool} {c c' : Control} {s t : GalilVM}
    (h : WatchSegE P q first delay (es1 ++ true :: es2) c s c' t) :
    ∃ (c1 : Control) (s1 : GalilVM), WatchSegE P q first delay es1 c s c1 s1 ∧
      c1.mode = .scan ∧ c1.clock = 1 ∧ canRight s1.right ∧
      read (left s1.left) = read (right s1.right) := by
  obtain ⟨c1, s1, h1, h2⟩ := watchSegE_append P q first delay es1 h
  refine ⟨c1, s1, h1, ?_⟩
  cases h2 with
  | «match» _ _ vs vq o hm hr ha hc hne hcmp hmt hq ho rest =>
    refine ⟨hm, hc, ha, ?_⟩
    obtain ⟨⟨hl0, hr0, _⟩, _⟩ := hcmp
    rw [scanLens.get_set] at hl0 hr0
    have := matched_parts P q first hmt
    rw [hl0, hr0] at this; exact this
  | matchIdle _ _ vs vq o hm hr ha hc hidle hl hrr hvs hmt hq hnf ho rest =>
    refine ⟨hm, hc, ha, ?_⟩
    have := matched_parts P q first hmt
    rw [hl, hrr] at this; exact this
  | matchIdleR _ _ vs vq o hm hr hc ha hidle hl hrr hvs hmt hq hnf ho rest =>
    refine ⟨hm, hc, ha, ?_⟩
    have := matched_parts P q first hmt
    rw [hl, hrr] at this; exact this

/-- Every comparison of a `ReplayChainSeg` segment is a match. -/
theorem replayChainSeg_comparison_matched (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    (es1 : List Bool) {es2 : List Bool} {c c' : Control} {s t : GalilVM}
    (h : ReplayChainSeg P q first delay (es1 ++ true :: es2) c s c' t) :
    ∃ (c1 : Control) (s1 : GalilVM), ReplayChainSeg P q first delay es1 c s c1 s1 ∧
      c1.mode = .scan ∧ c1.clock = 1 ∧ canRight s1.right ∧
      read (left s1.left) = read (right s1.right) := by
  obtain ⟨c1, s1, h1, h2⟩ := replayChainSeg_append P q first delay es1 h
  refine ⟨c1, s1, h1, ?_⟩
  cases h2 with
  | matchC _ _ vs vq o hm hr hc ha hne hcmp hmt hq ho rest =>
    exact ⟨hm, hc, ha, matchC_read P q first hcmp hmt⟩

/-- The comparison form of the chain-starting tick is a match. -/
theorem foundTick_comparison_matched (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    {c c' : Control} {s s' : GalilVM} (h : FoundTick P q first delay c s c' s')
    (hc : c.clock = 1) :
    canRight s.right ∧ read (left s.left) = read (right s.right) := by
  cases h with
  | bg _ _ _ hc' _ _ _ => omega
  | cmp vs vq o hm hr hc ha hidle hl hrr hmt hq hf hch ho =>
    refine ⟨ha, ?_⟩
    have := matched_parts P q first hmt
    rw [hl, hrr] at this; exact this

/-! ## 3. The right head along a segment -/

/-- Along a `WatchSegE` segment from a scan invariant the right head moves one
place per matched comparison and never back. -/
theorem watchSegE_right_position (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9)
    (delay : ℕ) {es : List Bool} {c c' : Control} {s t : GalilVM}
    (h : WatchSegE P q first delay es c s c' t) {C k : ℕ}
    (hi : ScanInvariant raw C k s.left s.right) :
    ScanInvariant raw C (k + es.count true) t.left t.right ∧
      position t.right = position s.right + es.count true := by
  have he := (watchSegE_heads P q first delay h).1 raw C k
  have hi' := scan_events_invariant he hi
  refine ⟨hi', ?_⟩
  rw [hi'.rightPos, hi.rightPos]; omega

theorem replayChainSeg_right_position (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9)
    (delay : ℕ) {es : List Bool} {c c' : Control} {s t : GalilVM}
    (h : ReplayChainSeg P q first delay es c s c' t) {C k : ℕ}
    (hi : ScanInvariant raw C k s.left s.right) :
    ScanInvariant raw C (k + es.count true) t.left t.right ∧
      position t.right = position s.right + es.count true := by
  have hi' := replayChainSeg_scanInvariant raw P q first delay h C k hi
  refine ⟨hi', ?_⟩
  rw [hi'.rightPos, hi.rightPos]; omega

/-- The places of the comparisons of a `WatchSegE` segment from a scan
invariant: the one after `es1` is a match at `position s.right + es1.count true + 1`. -/
theorem watchSegE_comparison_place (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9)
    (delay : ℕ) (es1 : List Bool) {es2 : List Bool} {c c' : Control} {s t : GalilVM}
    (h : WatchSegE P q first delay (es1 ++ true :: es2) c s c' t) {C k : ℕ}
    (hi : ScanInvariant raw C k s.left s.right) :
    ∃ l1 rr1 : PlaceHead, canRight rr1 ∧ read (left l1) = read (right rr1) ∧
      position (right rr1) = position s.right + es1.count true + 1 := by
  have he := (watchSegE_heads P q first delay h).1 raw C k
  obtain ⟨l1, rr1, _, h2, h3, h4⟩ := scanEvents_true_split es1 hi he
  exact ⟨l1, rr1, h2, h3, by rw [h4, hi.rightPos]⟩

/-! ## 4. The fallback's mismatching place is reached again, matched -/

/-- A comparison that mismatches with the right head moving onto place `n`. -/
structure FallbackTrigger (raw : List (Fin 2)) (n : ℕ) (c : Control) (s : GalilVM) : Prop where
  mode : c.mode = .scan
  clock : c.clock = 1
  canR : canRight s.right
  mismatch : read (left s.left) ≠ read (right s.right)
  scan : ∃ C k, ScanInvariant raw C k s.left s.right
  place : position (right s.right) = n

/-- The trigger place is one past the right head. -/
theorem trigger_place {raw : List (Fin 2)} {n : ℕ} {c : Control} {s : GalilVM}
    (h : FallbackTrigger raw n c s) : n = position s.right + 1 := by
  obtain ⟨C, k, hi⟩ := h.scan
  rw [← h.place]
  exact right_position s.right h.canR (represented_position _ raw hi.rightRep hi.rightPresent).1

/-- **`R = 0`.**  The landing right head is already on the mismatching place
`n1`, with the scan invariant at radius `0` there and the controller not
replaying. -/
theorem zero_radius_landing_at_place (raw : List (Fin 2)) {c : Control} {t : GalilVM} {n1 : ℕ}
    (hR : Restarted raw t 0 reset) (hpos : position t.center = n1 - 0)
    (hCR : t.center = t.right) (hrpl : c.replaying = decide (0 < 0)) :
    position t.right = n1 ∧ ScanInvariant raw (position t.center) 0 t.left t.right ∧
      c.replaying = false := by
  refine ⟨by rw [← hCR, hpos]; simp, hR.2.2.2.1, by rw [hrpl]; simp⟩

/-- **`replay_reaches_place_matched`.**  From the fallback landing with chosen
radius `R > 0` (centre and right head at `n1 - R`), the replay either

(i) is a `WatchSegE` segment with exactly `R` comparisons, all matched, ending
with the right head at `n1` in `InvScan`, whose last comparison moves the right
head onto `n1`; or

(ii) starts a chain inside the replay (`FoundLanding`), and its end state is a
non-replaying scan state with the right head at `n1`. -/
theorem replay_reaches_place_matched (raw : List (Fin 2)) (P : Shared)
    (hP : P.onLetter = onLetterVM raw) (hP' : P.leftFirst = leftFirstVM) (q : ℕ) (first : Fin 9)
    (delay : ℕ) (hex : ∀ s, P.replayExhausted s = zero s.replay) (hd : 1 ≤ delay)
    (hsearch : ∀ s : GalilVM, SearchReady (searchLens.get s) → ∀ a : Bool,
      ∃ v, searchEffect P a s v)
    (hpres : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s) → searchEffect P a s v → SearchReady v)
    {Ok : WState → Prop} (hOk : WatchOk Ok)
    (hgood : ∀ w, Ok w → GalilScaffoldChainWatch.Good w) (hstart : StartOk P Ok)
    (n1 R : ℕ) (hR0 : 0 < R) (hRle : R ≤ n1) (c : Control) (t : GalilVM)
    (hm : c.mode = Mode.scan) (hc : c.clock = delay) (hrpl : c.replaying = true)
    (hR : Restarted raw t 0 reset) (hrep : t.replay = ofNat R)
    (hpos : position t.center = n1 - R) (hCR : t.center = t.right)
    (hM : MInv raw c t) (hfr : Frontier t) (hsi : ShiftIdle t) :
    (∃ (es : List Bool) (c' : Control) (t' : GalilVM),
      WatchSegE P q first delay es c t c' t' ∧ es.count true = R ∧
      position t'.right = n1 ∧ InvScan delay raw c' t' R ∧
      (∀ es1 es2 : List Bool, es = es1 ++ true :: es2 →
        ∃ (c1 : Control) (s1 : GalilVM), WatchSegE P q first delay es1 c t c1 s1 ∧
          c1.mode = .scan ∧ c1.clock = 1 ∧ canRight s1.right ∧
          read (left s1.left) = read (right s1.right)) ∧
      (∀ es1 es2 : List Bool, es = es1 ++ true :: es2 →
        ∃ l1 rr1 : PlaceHead, canRight rr1 ∧ read (left l1) = read (right rr1) ∧
          position (right rr1) = n1 - R + es1.count true + 1 ∧
          position (right rr1) ≤ n1) ∧
      (∃ es1 es2 : List Bool, es = es1 ++ true :: es2 ∧ es2.count true = 0 ∧
        ∃ l1 rr1 : PlaceHead, canRight rr1 ∧ read (left l1) = read (right rr1) ∧
          position (right rr1) = n1)) ∨
    (FoundLanding raw P q first delay Ok c t 0 R ∧
      ∃ (c' : Control) (t' : GalilVM) (k : ℕ),
        StepsAll (galilFrameS P q first) delay (SoundScanNR raw) k ⟨c, t⟩ ⟨c', t'⟩ ∧
        c'.mode = .scan ∧ c'.replaying = false ∧ position t'.right = n1 ∧
        MInv raw c' t' ∧ ScanInvariant raw (position t'.center) R t'.left t'.right) := by
  have hi0 : ScanInvariant raw (position t.center) 0 t.left t.right := hR.2.2.2.1
  have hrpos : position t.right = n1 - R := by rw [← hCR, hpos]
  rcases replay_after_fallback_general raw P hP hP' q first delay hex hd hsearch hpres hOk hgood
      hstart R hR0 c t hm hc hrpl hR hrep hM hfr hsi with hA | hB
  · obtain ⟨es, c', t', hseg, _, _, hcnt, hpos', _, hinv⟩ := hA
    refine Or.inl ⟨es, c', t', hseg, hcnt, by rw [hpos', hrpos]; omega, hinv, ?_, ?_, ?_⟩
    · intro es1 es2 he
      rw [he] at hseg
      exact watchSegE_comparison_matched P q first delay es1 hseg
    · intro es1 es2 he
      have hcnt' := hcnt
      rw [he] at hseg hcnt'
      obtain ⟨l1, rr1, h1, h2, h3⟩ := watchSegE_comparison_place raw P q first delay es1 hseg hi0
      refine ⟨l1, rr1, h1, h2, by rw [h3, hrpos], ?_⟩
      simp [List.count_append] at hcnt'
      omega
    · obtain ⟨es1, es2, he, h1, h2⟩ := split_at_true es (R - 1) (by omega)
      refine ⟨es1, es2, he, h2, ?_⟩
      rw [he] at hseg
      obtain ⟨l1, rr1, g1, g2, g3⟩ := watchSegE_comparison_place raw P q first delay es1 hseg hi0
      exact ⟨l1, rr1, g1, g2, by rw [g3, hrpos, h1]; omega⟩
  · refine Or.inr ⟨hB, ?_⟩
    obtain ⟨-, -, -, -, -, -, c', t', k, -, -, -, -, -, hst, -, hm', -, hr', -, -, -, hM', hi', hp',
      -, -, -, -⟩ := hB
    exact ⟨c', t', k, hst, hm', hr', by rw [hp', hrpos]; omega, hM', by simpa using hi'⟩

/-! ## 5. No second trigger at the same place -/

/-- **`next_trigger_beyond`.**  From a state whose right head is at `n1` (with a
scan invariant), any scan segment (`WatchSegE`) that ends in a mismatch trigger
places that trigger at `n1 + (matches) + 1 > n1`. -/
theorem next_trigger_beyond (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9)
    (delay : ℕ) {es : List Bool} {c c2 : Control} {u0 u : GalilVM} {C k n1 n : ℕ}
    (hi : ScanInvariant raw C k u0.left u0.right) (hp : position u0.right = n1)
    (h : WatchSegE P q first delay es c u0 c2 u) (htr : FallbackTrigger raw n c2 u) :
    n = n1 + es.count true + 1 ∧ n1 < n := by
  have ⟨_, hpos⟩ := watchSegE_right_position raw P q first delay h hi
  have := trigger_place htr
  omega

/-- The same across a replay segment with a live chain. -/
theorem next_trigger_beyond_chain (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9)
    (delay : ℕ) {es : List Bool} {c c2 : Control} {u0 u : GalilVM} {C k n1 n : ℕ}
    (hi : ScanInvariant raw C k u0.left u0.right) (hp : position u0.right = n1)
    (h : ReplayChainSeg P q first delay es c u0 c2 u) (htr : FallbackTrigger raw n c2 u) :
    n = n1 + es.count true + 1 ∧ n1 < n := by
  have ⟨_, hpos⟩ := replayChainSeg_right_position raw P q first delay h hi
  have := trigger_place htr
  omega

/-- **`at_most_one_fallback_per_place`.**  A fallback triggered at place `n1`
lands (radius `R`, centre = right head at `n1 - R`).  Then:

* no comparison between the landing and the moment the right head is back on
  `n1` mismatches (for `R = 0` there is no such comparison; for `R > 0` every
  replay comparison matches, the last at `n1`);
* from that moment on (state `(c', t')`, right head at `n1`), every mismatch
  trigger reached along a scan segment is at a place `> n1`.

So `n1` sees exactly one fallback, namely the triggering one. -/
theorem at_most_one_fallback_per_place (raw : List (Fin 2)) (P : Shared)
    (hP : P.onLetter = onLetterVM raw) (hP' : P.leftFirst = leftFirstVM) (q : ℕ) (first : Fin 9)
    (delay : ℕ) (hex : ∀ s, P.replayExhausted s = zero s.replay) (hd : 1 ≤ delay)
    (hsearch : ∀ s : GalilVM, SearchReady (searchLens.get s) → ∀ a : Bool,
      ∃ v, searchEffect P a s v)
    (hpres : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s) → searchEffect P a s v → SearchReady v)
    {Ok : WState → Prop} (hOk : WatchOk Ok)
    (hgood : ∀ w, Ok w → GalilScaffoldChainWatch.Good w) (hstart : StartOk P Ok)
    (n1 R : ℕ) (hRle : R ≤ n1) (c : Control) (t : GalilVM)
    (hm : c.mode = Mode.scan) (hc : c.clock = delay) (hrpl : c.replaying = decide (0 < R))
    (hR : Restarted raw t 0 reset) (hrep : t.replay = ofNat R)
    (hpos : position t.center = n1 - R) (hCR : t.center = t.right)
    (hM : MInv raw c t) (hfr : Frontier t) (hsi : ShiftIdle t) :
    ∃ (c' : Control) (t' : GalilVM) (C K : ℕ),
      ScanInvariant raw C K t'.left t'.right ∧ position t'.right = n1 ∧ c'.replaying = false ∧
      (∀ (es : List Bool) (c2 : Control) (u : GalilVM) (n : ℕ),
        WatchSegE P q first delay es c' t' c2 u → FallbackTrigger raw n c2 u → n1 < n) ∧
      (∀ (es : List Bool) (c2 : Control) (u : GalilVM) (n : ℕ),
        ReplayChainSeg P q first delay es c' t' c2 u → FallbackTrigger raw n c2 u → n1 < n) := by
  rcases Nat.eq_zero_or_pos R with h0 | hpos0
  · subst h0
    obtain ⟨hp, hi, hr⟩ := zero_radius_landing_at_place raw hR hpos hCR hrpl
    exact ⟨c, t, _, _, hi, hp, hr,
      fun _ _ _ _ h htr => (next_trigger_beyond raw P q first delay hi hp h htr).2,
      fun _ _ _ _ h htr => (next_trigger_beyond_chain raw P q first delay hi hp h htr).2⟩
  · have hrt : c.replaying = true := by rw [hrpl]; simp [hpos0]
    rcases replay_reaches_place_matched raw P hP hP' q first delay hex hd hsearch hpres hOk hgood
        hstart n1 R hpos0 hRle c t hm hc hrt hR hrep hpos hCR hM hfr hsi with hA | hB
    · obtain ⟨_, c', t', _, _, hp, hinv, _, _, _⟩ := hA
      exact ⟨c', t', _, _, hinv.scan, hp, hinv.mode.2.1,
        fun _ _ _ _ h htr => (next_trigger_beyond raw P q first delay hinv.scan hp h htr).2,
        fun _ _ _ _ h htr => (next_trigger_beyond_chain raw P q first delay hinv.scan hp h htr).2⟩
    · obtain ⟨_, c', t', _, _, _, hr, hp, _, hi⟩ := hB
      exact ⟨c', t', _, _, hi, hp, hr,
        fun _ _ _ _ h htr => (next_trigger_beyond raw P q first delay hi hp h htr).2,
        fun _ _ _ _ h htr => (next_trigger_beyond_chain raw P q first delay hi hp h htr).2⟩

/-! ## 6. Into `AtMostOneFallback` -/

/-- If each fallback of a place event is tagged with its trigger place, all
tags are the event's place `n`, and at most one trigger of the run is at `n`,
then the place event has at most one fallback. -/
theorem atMostOneFallback_of_places {M : ℕ} (e : GalilIntervalCost.PlaceEvent M) (n : ℕ)
    (places : List ℕ) (hlen : e.fallbacks.length = places.length)
    (hall : ∀ p ∈ places, p = n) (hone : places.count n ≤ 1) :
    e.AtMostOneFallback := by
  unfold GalilIntervalCost.PlaceEvent.AtMostOneFallback
  have : places.count n = places.length :=
    List.count_eq_length.2 (fun p hp => by rw [hall p hp])
  omega

#print axioms scanEvents_true_split
#print axioms split_at_true
#print axioms watchSegE_comparison_matched
#print axioms replayChainSeg_comparison_matched
#print axioms foundTick_comparison_matched
#print axioms watchSegE_right_position
#print axioms replayChainSeg_right_position
#print axioms watchSegE_comparison_place
#print axioms trigger_place
#print axioms zero_radius_landing_at_place
#print axioms replay_reaches_place_matched
#print axioms next_trigger_beyond
#print axioms next_trigger_beyond_chain
#print axioms at_most_one_fallback_per_place
#print axioms atMostOneFallback_of_places

end PalPeg.GalilOneFallback
