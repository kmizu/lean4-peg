import PalPeg.GalilReportReplay
import PalPeg.GalilTickFun
import PalPeg.GalilCycleFoundBackground
import PalPeg.GalilPreludeDone

/-!
# Replay segments with a *live* chain

`PalPeg.GalilReplayFound` established that the model really does let the
co-running search reach `.found` — and hence `chain.start()` — while
`c.replaying = true`: `backgroundS`'s chain effect never consults the
`replaying` flag.  `WatchSegE` cannot express such a run: its two replaying
constructors `countR` and `matchIdleR` both carry `hidle : s.chain = .idle`.

`ReplayChainSeg` is the missing shape: the replay segment of a controller
whose chain is **not** idle.

* `countC` — a background tick while `replaying = true` and `1 < clock`.  The
  chain is non-idle, so `chainAt false …` is its first disjunct, i.e. a bare
  `ChainTick false` (`backgroundS_chainTick`); the search is frozen
  (`searchEffect`'s active disjunct).
* `matchC` — the forced comparison at `clock = 1`: exactly `WatchSegE.matchIdleR`'s
  fields with the idle chain replaced by an active one, i.e.
  `WatchSegE.match`'s `hcmp`/`hmt` (whose chain part is `ChainTick true`), the
  `replayDec true` of `Tick.scan_match`'s `matchedPlace`, and the control
  `replaying := c.replaying && !P.replayExhausted …` — written, as in
  `matchIdleR`, with `c.replaying` already rewritten to `true`.

The tick lemma behind `matchC` is `scan_match_S'` (active chain, replaying or
not), which is the exact counterpart of the `scan_match_idle_S'` behind
`matchIdleR`.

## What is assumed, and what is still missing

* `ChainTickable` — a live, *ready* chain can tick, on either event, into a
  chain that is ready again.  `PalPeg.GalilTickFun.chainAt_exists` gives the
  existence half outright; the *preservation* of `ChainReady` (and the
  exclusion of `ChainMatched.breaks`, which lands in `.broken`, where
  `ChainReady` is `False`) is the assumed half.  It is the same obligation the
  `WatchSegE`-based construction discharges through its own chain hypotheses.
* `active_background_exists` is copied here because `PalPeg.GalilPrepConstruct`
  is *not* imported by the root `PalPeg.lean` and so may not be imported.
* `replayChainSeg_construct` returns the segment, not a `StepsAll` run: the run
  is `replayChainSeg_stepsAll` applied to it (it needs `hP`/`hP'`, which the
  construction itself does not).
* The prep-shape bookkeeping — `prep_watch_start` / `prep_watch_start_least`
  and `PreludeEnds` of `PalPeg.GalilPreludeDone` — is still *stated against
  `WatchSegE`*.  `replayChainSeg_chain` exports the `ChainTicks` trace, which
  is the only thing those lemmas use of the segment (they conclude through
  `chainTicks_unique`), so the reduction is mechanical; but restating them
  against the common `ChainTicks` trace (or against `ReplayChainSeg`) has not
  been done here.
* `replayChainSeg_end` shows the landing state is a legitimate entry for
  `life_from_prep_stepsAll` / `life_from_prep_minv` as far as the control is
  concerned (`replaying = false`, chain alive).  Their remaining premises
  (`hprepSeg`'s own `WatchSegE`, the watch, the terminal mismatch) are not
  produced here.
-/

set_option autoImplicit false

namespace PalPeg.GalilReplayChainSeg

open PalPeg PalPeg.GalilTickFun PalPeg.GalilTickFun2 PalPeg.GalilReportReplay
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier GalilScaffoldChainInputSupply GalilStructuredSkeleton

/-! ## The segment -/

/-- A replay segment carrying a live (non-idle) chain. -/
inductive ReplayChainSeg (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) :
    List Bool → Control → GalilVM → Control → GalilVM → Prop
  | stop (c : Control) (s : GalilVM) : ReplayChainSeg P q first delay [] c s c s
  | countC (c : Control) (s s' : GalilVM) {es : List Bool} {c' : Control} {t : GalilVM}
      (hm : c.mode = .scan) (hr : c.replaying = true) (hc : 1 < c.clock)
      (hne : s.chain ≠ .idle)
      (hb : (galilFrameS P q first).background s s')
      (rest : ReplayChainSeg P q first delay es {c with clock := c.clock - 1} s' c' t) :
      ReplayChainSeg P q first delay (false :: es) c s c' t
  | matchC (c : Control) (s : GalilVM) (vs : ScanVM) (vq : SearchVM) (o : Bool)
      {es : List Bool} {c' : Control} {t : GalilVM}
      (hm : c.mode = .scan) (hr : c.replaying = true) (hc : c.clock = 1)
      (ha : canRight s.right) (hne : s.chain ≠ .idle)
      (hcmp : (galilFrame P q first).compare s (scanLens.set s vs))
      (hmt : (galilFrame P q first).matched (scanLens.set s vs))
      (hq : searchEffect P true s vq)
      (ho : refresh (galilFrame P q first) (replayDec true (afterCompare s vs vq)) c.output o)
      (rest : ReplayChainSeg P q first delay es
        {c with clock := delay, output := o, replaying := !P.replayExhausted (replayDec true (afterCompare s vs vq))} (replayDec true (afterCompare s vs vq)) c' t) :
      ReplayChainSeg P q first delay (true :: es) c s c' t

/-- The matched comparison of `matchC` really is a match of the outer
symbols. -/
theorem matchC_read (P : Shared) (q : ℕ) (first : Fin 9) {s : GalilVM} {vs : ScanVM}
    (hcmp : (galilFrame P q first).compare s (scanLens.set s vs))
    (hmt : (galilFrame P q first).matched (scanLens.set s vs)) :
    read (left s.left) = read (right s.right) := by
  obtain ⟨⟨hl0, hr0, _⟩, _⟩ := hcmp
  rw [scanLens.get_set] at hl0 hr0
  have := matched_parts P q first hmt
  rw [hl0, hr0] at this
  exact this

/-! ## The segment is a run -/

/-- A replay-chain segment is a run of `galilFrameS`. -/
theorem replayChainSeg_steps (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) {es : List Bool}
    {c c' : Control} {s t : GalilVM} (h : ReplayChainSeg P q first delay es c s c' t) :
    ∃ k, Steps (galilFrameS P q first) delay k ⟨c, s⟩ ⟨c', t⟩ := by
  induction h with
  | stop c s => exact ⟨0, .zero _⟩
  | countC c s s' hm hr hc hne hb _ ih =>
    obtain ⟨k, hs⟩ := ih
    exact ⟨k+1, .succ (.scan_count c s s' hm (Or.inl hr) hc hb) hs⟩
  | matchC c s vs vq o hm hr hc ha hne hcmp hmt hq ho _ ih =>
    obtain ⟨k, hs⟩ := ih
    have ht := scan_match_S' P q first delay c s vs vq o hm (Or.inl hr) hc hne hcmp hmt hq
      (by rw [hr]; exact ho)
    rw [hr] at ht
    exact ⟨k+1, .succ (by simpa using ht) hs⟩


/-! ## The chain trace -/

/-- **The chain evolves by `ChainTicks es`.**  Exporting the trace is what
lets the prep-shape bookkeeping — `prep_watch_start` / `prep_watch_start_least`
and `PreludeEnds` of `PalPeg.GalilPreludeDone`, all of which reduce to a
`ChainTicks` run over the same event list — be applied to a replay segment. -/
theorem replayChainSeg_chain (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) {es : List Bool}
    {c c' : Control} {s t : GalilVM} (h : ReplayChainSeg P q first delay es c s c' t)
    (hne : s.chain ≠ .idle) : ChainTicks es s.chain t.chain := by
  induction h with
  | stop c s => exact .nil _
  | countC c s s' hm hr hc hne' hb _ ih =>
    have ht := backgroundS_chainTick P q first hb hne'
    exact .cons ht (ih (chainTick_ne_idle' ht hne'))
  | matchC c s vs vq o hm hr hc ha hne' hcmp hmt hq ho _ ih =>
    have ht : ChainTick true s.chain vs.chain :=
      (compare_parts P q first hcmp (matchC_read P q first hcmp hmt)).2.2
    have hch : (replayDec true (afterCompare s vs vq)).chain = vs.chain := by
      rw [replayDec_chain, afterCompare_chain]
    exact .cons ht (by rw [← hch] at ht ⊢; exact ih (chainTick_ne_idle' ht hne'))

/-- A live chain stays live along a replay segment. -/
theorem replayChainSeg_ne_idle (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) {es : List Bool}
    {c c' : Control} {s t : GalilVM} (h : ReplayChainSeg P q first delay es c s c' t) :
    s.chain ≠ .idle → t.chain ≠ .idle := by
  induction h with
  | stop c s => exact id
  | countC c s s' hm hr hc hne' hb _ ih =>
    intro hne
    exact ih (chainTick_ne_idle' (backgroundS_chainTick P q first hb hne) hne)
  | matchC c s vs vq o hm hr hc ha hne' hcmp hmt hq ho _ ih =>
    intro hne
    have ht : ChainTick true s.chain vs.chain :=
      (compare_parts P q first hcmp (matchC_read P q first hcmp hmt)).2.2
    refine ih ?_
    rw [replayDec_chain, afterCompare_chain]
    exact chainTick_ne_idle' ht hne

/-! ## The scan invariant and the centre invariant -/

/-- The scan invariant grows by one place per matched comparison. -/
theorem replayChainSeg_scanInvariant (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9)
    (delay : ℕ) {es : List Bool} {c c' : Control} {s t : GalilVM}
    (h : ReplayChainSeg P q first delay es c s c' t) (cen : ℕ) :
    ∀ r : ℕ, ScanInvariant raw cen r s.left s.right →
      ScanInvariant raw cen (r + es.count true) t.left t.right := by
  induction h with
  | stop c s => intro r hi; simpa using hi
  | countC c s s' hm hr hc hne hb _ ih =>
    intro r hi
    obtain ⟨hl, hr', _, _⟩ := background_frame P q first hb
    have := ih r (by rw [hl, hr']; exact hi)
    simpa using this
  | matchC c s vs vq o hm hr hc ha hne hcmp hmt hq ho _ ih =>
    intro r hi
    have hmatch := matchC_read P q first hcmp hmt
    obtain ⟨hl, hrr, _⟩ := compare_parts P q first hcmp hmatch
    have hi' : ScanInvariant raw cen (r+1) (replayDec true (afterCompare s vs vq)).left
        (replayDec true (afterCompare s vs vq)).right := by
      rw [replayDec_left, replayDec_right]
      exact matched_invariant' raw vq hl hrr hmatch ha hi
    have h2 := ih (r+1) hi'
    rw [Nat.add_right_comm] at h2
    simp only [List.count_cons, beq_self_eq_true, if_true, ← Nat.add_assoc]
    exact h2

/-- **The centre invariant travels along a replay segment with a live chain.**
`minv_same` at a background tick, `minv_matchR` at the forced comparison —
exactly as `minv_watchSegE` does for `countR`/`matchIdleR`. -/
theorem replayChainSeg_minv (raw : List (Fin 2)) (P : Shared)
    (hex : ∀ s, P.replayExhausted s = zero s.replay) (q : ℕ) (first : Fin 9) (delay : ℕ)
    {es : List Bool} {c c' : Control} {s t : GalilVM}
    (h : ReplayChainSeg P q first delay es c s c' t) :
    ∀ r : ℕ, ScanInvariant raw (position s.center) r s.left s.right → MInv raw c s →
      MInv raw c' t := by
  induction h with
  | stop c s => intro r _ hM; exact hM
  | countC c s s' hm hr hc hne hb _ ih =>
    intro r hi hM
    obtain ⟨hl, hr', _, hC, _, _, _, _, _, hrep, _, _⟩ := backgroundS_fields P q first hb
    exact ih r (by rw [hl, hr', hC]; exact hi) (minv_same rfl hr' hC hrep hM)
  | matchC c s vs vq o hm hr hc ha hne hcmp hmt hq ho _ ih =>
    intro r hi hM
    have hmatch := matchC_read P q first hcmp hmt
    obtain ⟨hl, hrr, _⟩ := compare_parts P q first hcmp hmatch
    have hM' := minv_matchR P hex (vs := vs) (vq := vq) o delay hr hrr ha hi hM
    have hi' : ScanInvariant raw (position (replayDec true (afterCompare s vs vq)).center) (r+1)
        (replayDec true (afterCompare s vs vq)).left (replayDec true (afterCompare s vs vq)).right := by
      rw [replayDec_left, replayDec_right, replayDec_center, afterCompare_center]
      exact matched_invariant' raw vq hl hrr hmatch ha hi
    exact ih (r+1) hi' hM'

/-! ## Splitting and concatenating -/

/-- Segments split at any point of the event list. -/
theorem replayChainSeg_append (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) (es1 : List Bool) :
    ∀ {es2 : List Bool} {c c' : Control} {s t : GalilVM},
      ReplayChainSeg P q first delay (es1 ++ es2) c s c' t →
      ∃ (c'' : Control) (s'' : GalilVM), ReplayChainSeg P q first delay es1 c s c'' s'' ∧
        ReplayChainSeg P q first delay es2 c'' s'' c' t := by
  induction es1 with
  | nil => intro es2 c c' s t h; exact ⟨c, s, .stop _ _, h⟩
  | cons a es1 ih =>
    intro es2 c c' s t h
    cases h with
    | countC _ _ s' hm hr hc hne hb rest =>
      obtain ⟨c'', s'', h1, h2⟩ := ih rest
      exact ⟨c'', s'', .countC c s s' hm hr hc hne hb h1, h2⟩
    | matchC _ _ vs vq o hm hr hc ha hne hcmp hmt hq ho rest =>
      obtain ⟨c'', s'', h1, h2⟩ := ih rest
      exact ⟨c'', s'', .matchC c s vs vq o hm hr hc ha hne hcmp hmt hq ho h1, h2⟩

/-- Concatenation of segments. -/
theorem replayChainSeg_trans (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) {es1 : List Bool}
    {c c' : Control} {s t : GalilVM} (h1 : ReplayChainSeg P q first delay es1 c s c' t) :
    ∀ {es2 : List Bool} {c'' : Control} {u : GalilVM},
      ReplayChainSeg P q first delay es2 c' t c'' u →
      ReplayChainSeg P q first delay (es1 ++ es2) c s c'' u := by
  induction h1 with
  | stop c s => intro es2 c'' u h2; simpa using h2
  | countC c s s' hm hr hc hne hb _ ih =>
    intro es2 c'' u h2; exact .countC c s s' hm hr hc hne hb (ih h2)
  | matchC c s vs vq o hm hr hc ha hne hcmp hmt hq ho _ ih =>
    intro es2 c'' u h2; exact .matchC c s vs vq o hm hr hc ha hne hcmp hmt hq ho (ih h2)

/-! ## Soundness along the segment -/

/-- **The segment is a `SoundScanNR` run.**  The intermediate states are all
replaying, so `SoundScanNR` is vacuous there (`soundScanNR_of_replaying`); the
*last* comparison may flip `replaying` to `false`, and there soundness comes
from the refresh, exactly as `watchSegE_stepsAll` treats `matchIdleR`. -/
theorem replayChainSeg_stepsAll (raw : List (Fin 2)) (P : Shared)
    (hP : P.onLetter = onLetterVM raw) (hP' : P.leftFirst = leftFirstVM)
    (q : ℕ) (first : Fin 9) (delay : ℕ) {es : List Bool} {c c' : Control} {s t : GalilVM}
    (h : ReplayChainSeg P q first delay es c s c' t) (cen : ℕ) :
    ∀ r : ℕ, ScanInvariant raw cen r s.left s.right → SoundScanNR raw ⟨c, s⟩ →
      ∃ k, StepsAll (galilFrameS P q first) delay (SoundScanNR raw) k ⟨c, s⟩ ⟨c', t⟩ := by
  induction h with
  | stop c s => intro r _ hQ; exact ⟨0, .zero _ hQ⟩
  | countC c s s' hm hr hc hne hb _ ih =>
    intro r hi hQ
    obtain ⟨hl, hr', _, _⟩ := background_frame P q first hb
    obtain ⟨k, hs⟩ := ih r (by rw [hl, hr']; exact hi) (soundScanNR_of_replaying raw hr)
    exact ⟨k+1, .succ hQ (.scan_count c s s' hm (Or.inl hr) hc hb) hs⟩
  | matchC c s vs vq o hm hr hc ha hne hcmp hmt hq ho _ ih =>
    intro r hi hQ
    have hmatch := matchC_read P q first hcmp hmt
    obtain ⟨hl, hrr, _⟩ := compare_parts P q first hcmp hmatch
    have hi' : ScanInvariant raw cen (r+1) (replayDec true (afterCompare s vs vq)).left
        (replayDec true (afterCompare s vs vq)).right := by
      rw [replayDec_left, replayDec_right]
      exact matched_invariant' raw vq hl hrr hmatch ha hi
    obtain ⟨k, hs⟩ := ih (r+1) hi'
      (fun _ _ => outputRel_of_refresh' raw P hP hP' q first _ c.output o hi' ho _ rfl)
    have ht := scan_match_S' P q first delay c s vs vq o hm (Or.inl hr) hc hne hcmp hmt hq
      (by rw [hr]; exact ho)
    rw [hr] at ht
    exact ⟨k+1, .succ hQ (by simpa using ht) hs⟩

/-! ## The end of the replay -/

/-- **When the counter hits zero the replay is over.**  A segment whose last
event is a comparison lands at a control with `replaying = false` and a chain
that is still alive — i.e. exactly a state at which a `WatchSegE` may resume
(its `wait`/`count`/`match` constructors all require `replaying = false`), so
the result is a legitimate `hprepSeg`-style entry state for
`life_from_prep_stepsAll` / `life_from_prep_minv`. -/
theorem replayChainSeg_end (P : Shared) (hex : ∀ s, P.replayExhausted s = zero s.replay)
    (q : ℕ) (first : Fin 9) (delay : ℕ) {es0 : List Bool} {c c' : Control} {s t : GalilVM}
    (h : ReplayChainSeg P q first delay (es0 ++ [true]) c s c' t)
    (hz : zero t.replay = true) (hne : s.chain ≠ .idle) :
    c'.replaying = false ∧ t.chain ≠ .idle := by
  refine ⟨?_, replayChainSeg_ne_idle P q first delay h hne⟩
  obtain ⟨c2, s2, -, h2⟩ := replayChainSeg_append P q first delay es0 h
  cases h2 with
  | matchC c0 s0 vs vq o hm hr hc ha hne0 hcmp hmt hq ho rest =>
    cases rest
    show (!P.replayExhausted (replayDec true (afterCompare _ vs vq))) = false
    rw [hex]
    simpa using hz

/-! ## Existence: the replay really runs with the chain alive -/

/-- **Totality of a background tick on a non-idle chain** (a local copy of
`PalPeg.GalilPrepConstruct.active_background_exists`, which is not reachable
from the root import).  `searchEffect`'s active disjunct freezes the search and
`chainAt`'s non-idle disjunct is a bare `ChainStep`. -/
theorem active_background_exists (P : Shared) (q : ℕ) (first : Fin 9) (s : GalilVM)
    (hne : s.chain ≠ ChainVM.idle) {z : ChainVM} (hstep : ChainStep s.chain z) :
    ∃ s', (galilFrameS P q first).background s s' ∧ s'.chain = z ∧
      s'.left = s.left ∧ s'.right = s.right ∧ s'.center = s.center ∧
      s'.replay = s.replay := by
  refine ⟨searchLens.set (scanLens.set s ⟨s.left, s.right, z⟩) (searchLens.get s),
    ?_, rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨rfl, rfl, Or.inr ⟨hne, rfl⟩, Or.inl ⟨hne, ⟨z, hstep, rfl⟩⟩, ?_⟩
  rw [afterBirth_of_ne_idle hne]
  rfl

/-- The chain-side enabling hypothesis of the construction: a live, ready
chain can always tick, on either event, into a chain that is ready again.
(Existence alone is `PalPeg.GalilTickFun.chainAt_exists`; the *preservation*
of `ChainReady` is the part that is assumed here.) -/
def ChainTickable : Prop :=
  ∀ (a : Bool) (x : ChainVM), ChainReady x → x ≠ ChainVM.idle →
    ∃ z, ChainTick a x z ∧ ChainReady z

/-- The countdown to the next comparison, with the chain ticking along. -/
theorem replayChainSeg_countdown (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    (hready : ChainTickable) :
    ∀ (k : ℕ) (c : Control) (s : GalilVM), c.mode = .scan → c.replaying = true →
      c.clock = k + 1 → s.chain ≠ ChainVM.idle → ChainReady s.chain →
      ∃ (es : List Bool) (s' : GalilVM),
        ReplayChainSeg P q first delay es c s {c with clock := 1} s' ∧
        es.length = k ∧ es.count true = 0 ∧
        s'.chain ≠ ChainVM.idle ∧ ChainReady s'.chain ∧
        s'.left = s.left ∧ s'.right = s.right ∧ s'.center = s.center ∧ s'.replay = s.replay := by
  intro k
  induction k with
  | zero =>
    intro c s hm hrp hclk hne hrd
    have hc1 : c.clock = 1 := by omega
    have hc : ({c with clock := 1} : Control) = c := by rw [← hc1]
    refine ⟨[], s, ?_, rfl, rfl, hne, hrd, rfl, rfl, rfl, rfl⟩
    rw [hc]; exact .stop _ _
  | succ k ih =>
    intro c s hm hrp hclk hne hrd
    obtain ⟨z, htz, hrz⟩ := hready false s.chain hrd hne
    have hstep : ChainStep s.chain z := by
      obtain ⟨y, hst, hy⟩ := htz
      have hzy : z = y := hy
      rw [hzy]; exact hst
    obtain ⟨s1, hb, hch1, hl1, hr1, hC1, hrep1⟩ := active_background_exists P q first s hne hstep
    have hne1 : s1.chain ≠ ChainVM.idle := by
      rw [hch1]; exact chainTick_ne_idle' htz hne
    have hrd1 : ChainReady s1.chain := by rw [hch1]; exact hrz
    obtain ⟨es, s2, hseg, hlen, hcnt, hne2, hrd2, hl2, hr2, hC2, hrep2⟩ :=
      ih {c with clock := c.clock - 1} s1 hm hrp (by simp; omega) hne1 hrd1
    refine ⟨false :: es, s2, ?_, by simp [hlen], by simpa using hcnt, hne2, hrd2,
      by rw [hl2, hl1], by rw [hr2, hr1], by rw [hC2, hC1], by rw [hrep2, hrep1]⟩
    exact .countC c s s1 hm hrp (by omega) hne hb hseg

/-- **One replay comparison with a live chain**, the counterpart of
`PalPeg.GalilReportReplay.replay_one`: the clock counts down, the comparison is
forced to match (`replay_match_of_minv`), the right head advances one cell, the
counter drops by one, the scan invariant grows and the output is refreshed. -/
theorem replayChainSeg_one (raw : List (Fin 2)) (P : Shared)
    (hex : ∀ s, P.replayExhausted s = zero s.replay)
    (q : ℕ) (first : Fin 9) (delay : ℕ) (hd : 1 ≤ delay) (hready : ChainTickable)
    {c : Control} {s : GalilVM} {rad m : ℕ}
    (hm : c.mode = Mode.scan) (hclk : 1 ≤ c.clock) (hrp : c.replaying = true)
    (hrepl : s.replay = ofNat (m + 1))
    (hne : s.chain ≠ ChainVM.idle) (hrd : ChainReady s.chain)
    (hM : MInv raw c s)
    (hi : ScanInvariant raw (position s.center) rad s.left s.right)
    (hinc : s.right.head.incoming = [])
    (hlast : position s.right + (m + 1) = 2 * raw.length - 1) :
    ∃ (es : List Bool) (c' : Control) (t : GalilVM),
      ReplayChainSeg P q first delay es c s c' t ∧
      c'.mode = Mode.scan ∧ 1 ≤ c'.clock ∧ c'.replaying = decide (0 < m) ∧
      t.replay = ofNat m ∧ t.chain ≠ ChainVM.idle ∧ ChainReady t.chain ∧
      position t.right = position s.right + 1 ∧ t.right.head.incoming = [] ∧
      MInv raw c' t ∧ ScanInvariant raw (position t.center) (rad + 1) t.left t.right ∧
      Refreshed P q first ⟨c', t⟩ ∧ (∃ es0, es = es0 ++ [true]) := by
  classical
  obtain ⟨k, hk⟩ : ∃ k, c.clock = k + 1 := ⟨c.clock - 1, by omega⟩
  obtain ⟨es0, s1, hseg0, -, -, hne1, hrd1, hl1, hr1, hC1, hrepl1⟩ :=
    replayChainSeg_countdown P q first delay hready k c s hm hrp hk hne hrd
  set c1 : Control := {c with clock := 1} with hc1def
  have hm1 : c1.mode = Mode.scan := hm
  have hrp1 : c1.replaying = true := hrp
  have hclk1 : c1.clock = 1 := rfl
  have hM1 : MInv raw c1 s1 := minv_same rfl hr1 hC1 hrepl1 hM
  have hi1 : ScanInvariant raw (position s1.center) rad s1.left s1.right := by
    rw [hl1, hr1, hC1]; exact hi
  have hrepl1' : s1.replay = ofNat (m + 1) := by rw [hrepl1]; exact hrepl
  have hinc1 : s1.right.head.incoming = [] := by rw [hr1]; exact hinc
  have hav : canRight s1.right := canRight_of_lt hi1.rightRep hinc1 (by rw [hr1]; omega)
  have hpos1 : position (right s1.right) = position s1.right + 1 :=
    right_position s1.right hav (represented_position _ raw hi1.rightRep hi1.rightPresent).1
  have hmatch : read (left s1.left) = read (right s1.right) :=
    replay_match_of_minv hM1 hrp1 hav hi1
  -- the chain tick of the comparison
  obtain ⟨z, htz, hrz⟩ := hready true s1.chain hrd1 hne1
  set vs : ScanVM := ⟨left s1.left, right s1.right, z⟩ with hvsdef
  have hcmp : (galilFrame P q first).compare s1 (scanLens.set s1 vs) := by
    refine ⟨?_, ?_⟩
    · rw [scanLens.get_set]
      refine ⟨rfl, rfl, ?_⟩
      show ChainTick (decide (read (left s1.left) = read (right s1.right))) s1.chain vs.chain
      rw [decide_eq_true hmatch]; exact htz
    · rw [scanLens.get_set]
  have hmt : (galilFrame P q first).matched (scanLens.set s1 vs) := hmatch
  set vq : SearchVM := searchLens.get s1 with hvqdef
  have hq : searchEffect P true s1 vq := Or.inr ⟨hne1, rfl⟩
  set u : GalilVM := replayDec true (afterCompare s1 vs vq) with hudef
  set o : Bool := if P.onLetter u then decide (P.leftFirst u) else c1.output with hodef
  have ho : refresh (galilFrame P q first) u c1.output o := by
    refine ⟨fun hl => ?_, fun hl => ?_⟩
    · have hl' : P.onLetter u := hl
      show (if P.onLetter u then decide (P.leftFirst u) else c1.output) = true ↔ P.leftFirst u
      rw [if_pos hl']; exact decide_eq_true_iff
    · have hl' : ¬ P.onLetter u := hl
      show (if P.onLetter u then decide (P.leftFirst u) else c1.output) = c1.output
      rw [if_neg hl']
  have hreplU : u.replay = ofNat m := by
    rw [hudef, replayDec_true_replay, afterCompare_replay, hrepl1', dec_ofNat_succ]
  have hchU : u.chain = z := by rw [hudef, replayDec_chain, afterCompare_chain]
  have hneU : u.chain ≠ ChainVM.idle := by rw [hchU]; exact chainTick_ne_idle' htz hne1
  have hrdU : ChainReady u.chain := by rw [hchU]; exact hrz
  have hrightU : u.right = right s1.right := by
    rw [hudef, replayDec_right, afterCompare_right]
  have hposU : position u.right = position s.right + 1 := by rw [hrightU, hpos1, hr1]
  have hincU : u.right.head.incoming = [] := by
    rw [hrightU]; exact right_incoming_nil hinc1
  set c2 : Control :=
    { c1 with clock := delay, output := o, replaying := !P.replayExhausted u } with hc2def
  have hMU : MInv raw c2 u := minv_matchR P hex o delay hrp1 rfl hav hi1 hM1
  have hiU : ScanInvariant raw (position u.center) (rad + 1) u.left u.right := by
    have h0 := matched_invariant' raw vq (vs := vs) rfl rfl hmatch hav hi1
    rw [hudef, replayDec_left, replayDec_right, replayDec_center, afterCompare_center]
    exact h0
  have hzU : P.replayExhausted u = decide (m = 0) := by
    rw [hex, hreplU]
    cases m with
    | zero => simpa using (zero_ofNat_iff 0).2 rfl
    | succ j => simpa using zero_ofNat_succ j
  refine ⟨es0 ++ [true], c2, u, ?_, hm1, ?_, ?_, hreplU, hneU, hrdU, hposU, hincU, hMU, hiU,
    ⟨c1.output, ho⟩, ⟨es0, rfl⟩⟩
  · refine replayChainSeg_trans P q first delay hseg0 ?_
    exact .matchC c1 s1 vs vq o hm1 hrp1 hclk1 hav hne1 hcmp hmt hq ho (.stop _ _)
  · show 1 ≤ delay; exact hd
  · show (!P.replayExhausted u) = decide (0 < m)
    rw [hzU]; cases m <;> simp

/-- **The whole replay runs with the chain alive.**  `replay_run` of
`PalPeg.GalilReportReplay` with `ChainReady s.chain` in place of
`s.chain = .idle`. -/
theorem replayChainSeg_construct (raw : List (Fin 2)) (P : Shared)
    (hex : ∀ s, P.replayExhausted s = zero s.replay)
    (q : ℕ) (first : Fin 9) (delay : ℕ) (hd : 1 ≤ delay) (hready : ChainTickable) :
    ∀ (m : ℕ) (c : Control) (s : GalilVM) (rad : ℕ),
      c.mode = Mode.scan → 1 ≤ c.clock → c.replaying = true →
      s.replay = ofNat (m + 1) → s.chain ≠ ChainVM.idle → ChainReady s.chain →
      MInv raw c s → ScanInvariant raw (position s.center) rad s.left s.right →
      s.right.head.incoming = [] → position s.right + (m + 1) = 2 * raw.length - 1 →
      ∃ (es : List Bool) (c' : Control) (t : GalilVM),
        ReplayChainSeg P q first delay es c s c' t ∧
        c'.mode = Mode.scan ∧ c'.replaying = false ∧
        position t.right = 2 * raw.length - 1 ∧ t.right.head.incoming = [] ∧
        t.chain ≠ ChainVM.idle ∧ ChainReady t.chain ∧ t.replay = ofNat 0 ∧ MInv raw c' t ∧
        (∃ rad', ScanInvariant raw (position t.center) rad' t.left t.right) ∧
        Refreshed P q first ⟨c', t⟩ ∧ (∃ es0, es = es0 ++ [true]) := by
  intro m
  induction m with
  | zero =>
    intro c s rad hm hclk hrp hrepl hne hrd hM hi hinc hlast
    obtain ⟨es, c', t, hseg, hm', -, hrp', hreplT, hneT, hrdT, hposR, hincR, hMt, hit, hfr, hsplit⟩ :=
      replayChainSeg_one raw P hex q first delay hd hready hm hclk hrp hrepl hne hrd hM hi hinc hlast
    exact ⟨es, c', t, hseg, hm', by simpa using hrp', by omega, hincR, hneT, hrdT, hreplT, hMt,
      ⟨rad + 1, hit⟩, hfr, hsplit⟩
  | succ j ih =>
    intro c s rad hm hclk hrp hrepl hne hrd hM hi hinc hlast
    obtain ⟨es1, c1, t1, hseg1, hm1, hclk1, hrp1, hrepl1, hne1, hrd1, hposR, hincR, hMt, hit, -, -⟩ :=
      replayChainSeg_one raw P hex q first delay hd hready hm hclk hrp hrepl hne hrd hM hi hinc hlast
    have hrp1' : c1.replaying = true := by simpa using hrp1
    obtain ⟨es2, c2, t2, hseg2, hm2, hrp2, hpos2, hinc2, hne2, hrd2, hrepl2, hM2, hi2, hfr2, hsp2⟩ :=
      ih c1 t1 (rad + 1) hm1 hclk1 hrp1' hrepl1 hne1 hrd1 hMt hit hincR (by omega)
    exact ⟨es1 ++ es2, c2, t2, replayChainSeg_trans P q first delay hseg1 hseg2, hm2, hrp2,
      hpos2, hinc2, hne2, hrd2, hrepl2, hM2, hi2, hfr2,
      by obtain ⟨es0, rfl⟩ := hsp2; exact ⟨es1 ++ es0, by simp⟩⟩

#print axioms replayChainSeg_steps
#print axioms replayChainSeg_chain
#print axioms replayChainSeg_ne_idle
#print axioms replayChainSeg_scanInvariant
#print axioms replayChainSeg_minv
#print axioms replayChainSeg_append
#print axioms replayChainSeg_stepsAll
#print axioms replayChainSeg_end
#print axioms active_background_exists
#print axioms replayChainSeg_countdown
#print axioms replayChainSeg_one
#print axioms replayChainSeg_construct

end PalPeg.GalilReplayChainSeg
