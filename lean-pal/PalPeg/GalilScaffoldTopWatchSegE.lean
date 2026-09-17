import PalPeg.GalilScaffoldTopChainLife

/-!
# Event-indexed general segments and the preparation period

`WatchSegE es` is `WatchSeg` with its event list explicit (`false` at a
counting/waiting tick, `true` at a matched comparison). Segments split at
any point of the event list, and their events drive the chain and the
heads as for `WatchSeg`. The preparation period after the chain start — `h`
copy ticks, the done tick, `h+1` back ticks — ends with the chain watching
at `watchStart` (`found_to_watchStart` plus determinism).
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

inductive WatchSegE (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) :
    List Bool → Control → GalilVM → Control → GalilVM → Prop
  | stop (c : Control) (s : GalilVM) : WatchSegE P q first delay [] c s c s
  | wait (c : Control) (s s' : GalilVM) {es : List Bool} {c' : Control} {t : GalilVM}
      (hm : c.mode = .scan) (hr : c.replaying = false) (hn : ¬ canRight s.right)
      (hb : (galilFrameS P q first).background s s')
      (rest : WatchSegE P q first delay es c s' c' t) : WatchSegE P q first delay (false :: es) c s c' t
  | count (c : Control) (s s' : GalilVM) {es : List Bool} {c' : Control} {t : GalilVM}
      (hm : c.mode = .scan) (hr : c.replaying = false) (ha : canRight s.right) (hc : 1 < c.clock)
      (hb : (galilFrameS P q first).background s s')
      (rest : WatchSegE P q first delay es {c with clock := c.clock - 1} s' c' t) :
      WatchSegE P q first delay (false :: es) c s c' t
  | match (c : Control) (s : GalilVM) (vs : ScanVM) (vq : SearchVM) (o : Bool) {es : List Bool}
      {c' : Control} {t : GalilVM}
      (hm : c.mode = .scan) (hr : c.replaying = false) (ha : canRight s.right) (hc : c.clock = 1)
      (hne : s.chain ≠ .idle)
      (hcmp : (galilFrame P q first).compare s (scanLens.set s vs))
      (hmt : (galilFrame P q first).matched (scanLens.set s vs))
      (hq : searchEffect P true s vq)
      (ho : refresh (galilFrame P q first) (afterCompare s vs vq) c.output o)
      (rest : WatchSegE P q first delay es {c with clock := delay, output := o, replaying := false}
        (afterCompare s vs vq) c' t) :
      WatchSegE P q first delay (true :: es) c s c' t
  | matchIdle (c : Control) (s : GalilVM) (vs : ScanVM) (vq : SearchVM) (o : Bool) {es : List Bool}
      {c' : Control} {t : GalilVM}
      (hm : c.mode = .scan) (hr : c.replaying = false) (ha : canRight s.right) (hc : c.clock = 1)
      (hidle : s.chain = .idle) (hl : vs.left = left s.left) (hrr : vs.right = right s.right)
      (hvs : vs.chain = .idle)
      (hmt : (galilFrame P q first).matched (scanLens.set s vs))
      (hq : searchEffect P true s vq) (hnf : vq.search.mode ≠ .found)
      (ho : refresh (galilFrame P q first) (afterCompare s vs vq) c.output o)
      (rest : WatchSegE P q first delay es {c with clock := delay, output := o, replaying := false}
        (afterCompare s vs vq) c' t) :
      WatchSegE P q first delay (true :: es) c s c' t
  | countR (c : Control) (s s' : GalilVM) {es : List Bool} {c' : Control} {t : GalilVM}
      (hm : c.mode = .scan) (hr : c.replaying = true) (hc : 1 < c.clock) (hidle : s.chain = .idle)
      (hb : (galilFrameS P q first).background s s')
      (rest : WatchSegE P q first delay es {c with clock := c.clock - 1} s' c' t) :
      WatchSegE P q first delay (false :: es) c s c' t
  | matchIdleR (c : Control) (s : GalilVM) (vs : ScanVM) (vq : SearchVM) (o : Bool) {es : List Bool}
      {c' : Control} {t : GalilVM}
      (hm : c.mode = .scan) (hr : c.replaying = true) (hc : c.clock = 1) (ha : canRight s.right)
      (hidle : s.chain = .idle) (hl : vs.left = left s.left) (hrr : vs.right = right s.right)
      (hvs : vs.chain = .idle)
      (hmt : (galilFrame P q first).matched (scanLens.set s vs))
      (hq : searchEffect P true s vq) (hnf : vq.search.mode ≠ .found)
      (ho : refresh (galilFrame P q first) (replayDec true (afterCompare s vs vq)) c.output o)
      (rest : WatchSegE P q first delay es {c with clock := delay, output := o, replaying := !P.replayExhausted (replayDec true (afterCompare s vs vq))} (replayDec true (afterCompare s vs vq)) c' t) :
      WatchSegE P q first delay (true :: es) c s c' t

theorem watchSeg_of_E (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) {es : List Bool}
    {c c' : Control} {s t : GalilVM} (h : WatchSegE P q first delay es c s c' t) (hne : s.chain ≠ .idle) :
    WatchSeg P q first delay c s c' t := by
  induction h with
  | stop c s => exact .stop _ _
  | wait c s s' hm hr hn hb _ ih =>
    exact .wait c s s' hm hr hn hb (ih (chainTick_ne_idle' (backgroundS_chainTick P q first hb hne) hne))
  | count c s s' hm hr ha hc hb _ ih =>
    exact .count c s s' hm hr ha hc hb (ih (chainTick_ne_idle' (backgroundS_chainTick P q first hb hne) hne))
  | «match» c s vs vq o hm hr ha hc hne' hcmp hmt hq ho _ ih =>
    have hmatch : read (left s.left) = read (right s.right) := by
      obtain ⟨⟨hl0, hr0, _⟩, _⟩ := hcmp
      rw [scanLens.get_set] at hl0 hr0
      have := matched_parts P q first hmt
      rw [hl0, hr0] at this; exact this
    obtain ⟨_, _, ht⟩ := compare_parts P q first hcmp hmatch
    exact .match c s vs vq o hm hr ha hc hne' hcmp hmt hq ho
      (ih (by rw [afterCompare_chain]; exact chainTick_ne_idle' ht hne))
  | matchIdle c s _ _ _ _ _ _ _ hidle _ _ _ _ _ _ _ _ _ => exact absurd hidle hne
  | countR c s _ _ _ _ hidle _ _ _ => exact absurd hidle hne
  | matchIdleR c s _ _ _ _ _ _ _ hidle _ _ _ _ _ _ _ _ _ => exact absurd hidle hne

/-- An event-indexed segment is a run of `galilFrameS`. -/
theorem watchSegE_steps (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) {es : List Bool}
    {c c' : Control} {s t : GalilVM} (h : WatchSegE P q first delay es c s c' t) :
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
  | matchIdle c s vs vq o hm hr ha hc hidle hl hrr hvs hmt hq hnf ho _ ih =>
    obtain ⟨k, hs⟩ := ih
    exact ⟨k+1, .succ (scan_match_idle_S P q first delay c s vs vq o hm hr ha hc hidle hl hrr hvs hmt hq hnf ho) hs⟩
  | countR c s s' hm hr hc hidle hb _ ih =>
    obtain ⟨k, hs⟩ := ih
    exact ⟨k+1, .succ (.scan_count c s s' hm (Or.inl hr) hc hb) hs⟩
  | matchIdleR c s vs vq o hm hr hc ha hidle hl hrr hvs hmt hq hnf ho _ ih =>
    obtain ⟨k, hs⟩ := ih
    have ht := scan_match_idle_S' P q first delay c s vs vq o hm (Or.inl hr) hc hidle hl hrr hvs hmt hq hnf
      (by rw [hr]; exact ho)
    rw [hr] at ht
    exact ⟨k+1, .succ (by simpa using ht) hs⟩

/-- Segments split at any point of the event list. -/
theorem watchSegE_append (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) (es1 : List Bool) :
    ∀ {es2 : List Bool} {c c' : Control} {s t : GalilVM},
      WatchSegE P q first delay (es1 ++ es2) c s c' t →
      ∃ (c'' : Control) (s'' : GalilVM), WatchSegE P q first delay es1 c s c'' s'' ∧
        WatchSegE P q first delay es2 c'' s'' c' t := by
  induction es1 with
  | nil =>
    intro es2 c c' s t h
    exact ⟨c, s, .stop _ _, h⟩
  | cons a es1 ih =>
    intro es2 c c' s t h
    cases h with
    | wait _ _ s' hm hr hn hb rest =>
      obtain ⟨c'', s'', h1, h2⟩ := ih rest
      exact ⟨c'', s'', .wait c s s' hm hr hn hb h1, h2⟩
    | count _ _ s' hm hr ha hc hb rest =>
      obtain ⟨c'', s'', h1, h2⟩ := ih rest
      exact ⟨c'', s'', .count c s s' hm hr ha hc hb h1, h2⟩
    | «match» _ _ vs vq o hm hr ha hc hne hcmp hmt hq ho rest =>
      obtain ⟨c'', s'', h1, h2⟩ := ih rest
      exact ⟨c'', s'', .match c s vs vq o hm hr ha hc hne hcmp hmt hq ho h1, h2⟩
    | matchIdle _ _ vs vq o hm hr ha hc hidle hl hrr hvs hmt hq hnf ho rest =>
      obtain ⟨c'', s'', h1, h2⟩ := ih rest
      exact ⟨c'', s'', .matchIdle c s vs vq o hm hr ha hc hidle hl hrr hvs hmt hq hnf ho h1, h2⟩
    | countR _ _ s' hm hr hc hidle hb rest =>
      obtain ⟨c'', s'', h1, h2⟩ := ih rest
      exact ⟨c'', s'', .countR c s s' hm hr hc hidle hb h1, h2⟩
    | matchIdleR _ _ vs vq o hm hr hc ha hidle hl hrr hvs hmt hq hnf ho rest =>
      obtain ⟨c'', s'', h1, h2⟩ := ih rest
      exact ⟨c'', s'', .matchIdleR c s vs vq o hm hr hc ha hidle hl hrr hvs hmt hq hnf ho h1, h2⟩

/-- Concatenation of segments. -/
theorem watchSegE_trans (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) {es1 : List Bool}
    {c c' : Control} {s t : GalilVM} (h1 : WatchSegE P q first delay es1 c s c' t) :
    ∀ {es2 : List Bool} {c'' : Control} {u : GalilVM}, WatchSegE P q first delay es2 c' t c'' u →
      WatchSegE P q first delay (es1 ++ es2) c s c'' u := by
  induction h1 with
  | stop c s => intro es2 c'' u h2; simpa using h2
  | wait c s s' hm hr hn hb _ ih => intro es2 c'' u h2; exact .wait c s s' hm hr hn hb (ih h2)
  | count c s s' hm hr ha hc hb _ ih => intro es2 c'' u h2; exact .count c s s' hm hr ha hc hb (ih h2)
  | «match» c s vs vq o hm hr ha hc hne hcmp hmt hq ho _ ih =>
    intro es2 c'' u h2; exact .match c s vs vq o hm hr ha hc hne hcmp hmt hq ho (ih h2)
  | matchIdle c s vs vq o hm hr ha hc hidle hl hrr hvs hmt hq hnf ho _ ih =>
    intro es2 c'' u h2; exact .matchIdle c s vs vq o hm hr ha hc hidle hl hrr hvs hmt hq hnf ho (ih h2)
  | countR c s s' hm hr hc hidle hb _ ih =>
    intro es2 c'' u h2; exact .countR c s s' hm hr hc hidle hb (ih h2)
  | matchIdleR c s vs vq o hm hr hc ha hidle hl hrr hvs hmt hq hnf ho _ ih =>
    intro es2 c'' u h2; exact .matchIdleR c s vs vq o hm hr hc ha hidle hl hrr hvs hmt hq hnf ho (ih h2)

/-- The events of an event-indexed segment are its index. -/
theorem watchSegE_events (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) {es : List Bool}
    {c c' : Control} {s t : GalilVM} (h : WatchSegE P q first delay es c s c' t) (hne : s.chain ≠ .idle) :
    ChainTicks es s.chain t.chain ∧
      (∀ (raw : List (Fin 2)) (c0 r : ℕ), ScanEvents raw c0 r s.left s.right es t.left t.right) ∧
      t.center = s.center ∧ t.periodOnly = s.periodOnly ∧
      value t.radius = value s.radius + es.count true ∧
      (Canonical s.radius → Canonical t.radius) ∧ (Canonical s.length → Canonical t.length) := by
  induction h with
  | stop c s =>
    exact ⟨.nil _, fun _ _ _ => .stop _ _ _, rfl, rfl, by simp, id, id⟩
  | wait c s s' _ _ _ hb _ ih =>
    have ht := backgroundS_chainTick P q first hb hne
    obtain ⟨hch, hsc, hcen, hpo, hrad, hrc, hlc⟩ := ih (chainTick_ne_idle' ht hne)
    obtain ⟨hl, hr, hcen', hpo', hrad', hlen'⟩ := background_frame_ne_idle P q first hb hne
    refine ⟨.cons ht hch, fun raw c0 r => ?_, by rw [hcen, hcen'], by rw [hpo, hpo'],
      by rw [hrad, hrad']; simp, fun h0 => hrc (by rw [hrad']; exact h0), fun h0 => hlc (by rw [hlen']; exact h0)⟩
    have := hsc raw c0 r
    rw [hl, hr] at this
    exact .skip _ _ _ this
  | count c s s' _ _ _ _ hb _ ih =>
    have ht := backgroundS_chainTick P q first hb hne
    obtain ⟨hch, hsc, hcen, hpo, hrad, hrc, hlc⟩ := ih (chainTick_ne_idle' ht hne)
    obtain ⟨hl, hr, hcen', hpo', hrad', hlen'⟩ := background_frame_ne_idle P q first hb hne
    refine ⟨.cons ht hch, fun raw c0 r => ?_, by rw [hcen, hcen'], by rw [hpo, hpo'],
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
    obtain ⟨hch, hsc, hcen, hpo, hrad, hrc, hlc⟩ := ih (by rw [afterCompare_chain]; exact chainTick_ne_idle' ht hne)
    rw [afterCompare_chain] at hch
    rw [afterCompare_center] at hcen
    rw [afterCompare_periodOnly] at hpo
    rw [afterCompare_radius, inc_value] at hrad
    rw [afterCompare_radius] at hrc
    rw [afterCompare_length] at hlc
    refine ⟨.cons ht hch, fun raw c0 r => ?_, hcen, hpo, by rw [hrad]; simp; ring,
      fun hc => hrc (inc_canonical _ hc), fun hc => hlc (inc_canonical _ (inc_canonical _ hc))⟩
    have := hsc raw c0 (r+1)
    rw [afterCompare_left, afterCompare_right, hl, hr] at this
    exact .matched _ _ _ ha hmatch this
  | matchIdle c s _ _ _ _ _ _ _ hidle _ _ _ _ _ _ _ _ _ => exact absurd hidle hne
  | countR c s _ _ _ _ hidle _ _ _ => exact absurd hidle hne
  | matchIdleR c s _ _ _ _ _ _ _ hidle _ _ _ _ _ _ _ _ _ => exact absurd hidle hne

/-- The preparation period after a matched chain start: `h` copy ticks, the
done tick, `h+1` back ticks, and the chain watches at `watchStart`. -/
theorem prep_watch_start (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    {s t : GalilScaffoldSearchFinish.State} {x y : GalilScaffoldControl.Machine 12}
    {as : List Bool} {w : List (Fin 3)} {lower span : ℕ} (p : GalilScaffoldPlace.Place)
    (hw : w = (GalilScaffoldPlace.stream p).take (span+1))
    (hr : GalilScaffoldSearchRun.SafeQuanta s x as t y) (hs : s.mode = .run) (ht : t.mode = .found)
    (hv : GalilDpCorrect.Result w lower 0 (GalilScaffoldProgram.denote y.config))
    (ver : PlaceHead) (r0 : ℕ) (dm : Bool) :
    ∃ (h : ℕ) (c : Fin 3) (ys : List (Fin 3)) (b : Fin 3),
      GalilDpCorrect.Candidate w lower h ∧ GalilScaffoldPlace.read p = some c ∧ ys.length + 1 = h ∧
      ∀ (bs cs : List Bool), bs.length = h → cs.length = h+1 →
        ∀ (ch : ChainVM), ChainMatched (chainStart (y.config.tapes 11) c p ver (ofNat (r0+1))) ch →
        ∀ {c0 c1 : Control} {v0 v1 : GalilVM},
          WatchSegE P q first delay (bs ++ dm :: cs) c0 v0 c1 v1 → v0.chain = ch →
          v1.chain = .watch (watchStart ver c ys b (GalilScaffoldChainCredits.run
            (GalilScaffoldChainCredits.start (ofNat (r0+1)))
            (GalilScaffoldChainCredits.prepEvents true dm bs cs))) := by
  obtain ⟨h, c, ys, b, hcand, hread, hlen, hrest⟩ := found_to_watchStart p hw hr hs ht hv ver r0 true dm
  refine ⟨h, c, ys, b, hcand, hread, hlen, ?_⟩
  intro bs cs hbs hcs ch hch c0 c1 v0 v1 hseg hv0
  obtain ⟨x1, hx1, hticks⟩ := hrest bs cs hbs hcs
  simp only [ite_true] at hx1
  have hx : ch = x1 := chainMatched_unique hch hx1
  subst hx
  obtain ⟨hch', _⟩ := watchSegE_events P q first delay hseg (by rw [hv0]; intro h0; rw [h0] at hch; cases hch)
  rw [hv0] at hch'
  exact chainTicks_unique hch' hticks

#print axioms watchSegE_append
#print axioms watchSegE_events
#print axioms prep_watch_start

end PalPeg.GalilScaffoldChainInputSupply
