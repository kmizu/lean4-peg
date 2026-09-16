import PalPeg.GalilTraceCost
import PalPeg.GalilPlaceEvents
import PalPeg.GalilOneFallback
import PalPeg.GalilReplaySegment

/-!
# Costed runs for scan segments, the target match and fallback + replay

`GalilTraceCost.CostedRun` asks for a decomposition of a run into place-tagged
`Piece`s.  This module supplies it for three exit kinds of the cycle oracle.

1. **Scan segments** (`WatchSegE`).  One piece per matched comparison, tagged
   with the place the right head moves onto, `cmp = true`, no shifts, no
   fallbacks, `adv = 0`.  The background ticks before a comparison are its
   `wait`.  They are bounded by the clock: between two reloads (to `2048`) the
   clock only decrements (`count`/`countR`, both need `1 < clock`), so a
   comparison (at `clock = 1`) has at most `2047` background ticks before it.
   `wait` ticks (right head blocked, clock kept) are excluded by the end state
   being able to move right (`watchSegE_noRight`: once blocked outside a
   replay, a segment stays blocked).  Background ticks *after* the last
   comparison belong to no piece yet: `costedRun_watchSegE_pend` hands them out
   as a pending wait `w1` (`k' + w1 = w + |es|`, `w1 + clock' ≤ 2048`), to be
   charged to the next comparison piece.
2. **The target match** (`costedRun_target_match`): segment + the comparison
   onto `2m−1` (the landing state `afterCompare t ⟨left t.left, right t.right, idle⟩ vq`
   of `reachAt_of_target_match`), `|es| + 1` ticks.
3. **Fallback + replay** (`costedRun_fallback_replay`): segment + the
   mismatching comparison at `n1 = position (right s.right)` + the fallback
   phase + the replay, as ONE piece at `n1` carrying the `FallbackEv` of
   `fallbackEv2048_of_landing`.  The replay's comparisons re-read places
   `≤ n1` and are charged in the event's `replay` field; the right head after
   the replay is exactly `n1` (`replay_right_eq_place`).  `R = 0`:
   `costedRun_fallback_zero`; `R > 0` with the machine replay
   (`replay_after_fallback`): `costedRun_fallback_replay_machine`.
-/

set_option autoImplicit false

namespace PalPeg.GalilCostedFallback

open PalPeg PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilTraceCost PalPeg.GalilIntervalCost
  PalPeg.GalilPlaceEvents PalPeg.GalilOneFallback PalPeg.GalilReplaySegment
  PalPeg.GalilBranchInvariants2 PalPeg.GalilSegmentConstruct
open Manacher GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-! ## Pieces -/

/-- A matched comparison at place `n` after `w` background ticks. -/
def cmpPiece (n w : ℕ) (hw : w ≤ 2048) : Piece :=
  ⟨n, [], [], w, true, hw, (fun h => by cases h), by simp⟩

theorem cmpPiece_ticks (n w : ℕ) (hw : w ≤ 2048) : (cmpPiece n w hw).ticks = w + 1 := by
  simp [cmpPiece, Piece.ticks, Piece.ev, Piece.cmpN, PlaceEvent.slot, PlaceEvent.shiftTicks,
    PlaceEvent.fbTicks, PlaceEvent.replayTicks]

theorem cmpPiece_adv (n w : ℕ) (hw : w ≤ 2048) : (cmpPiece n w hw).adv = 0 := by
  simp [cmpPiece, Piece.adv, Piece.ev, PlaceEvent.adv, PlaceEvent.shiftAdv, PlaceEvent.fbAdv]

/-- The mismatching comparison at `n` after `w` background ticks, with its
fallback and replay. -/
def fbPiece (n w : ℕ) (hw : w ≤ 2048) (e : FallbackEv 2048) : Piece :=
  ⟨n, [], [e], w, true, hw, (fun h => by cases h), by simp⟩

theorem fbPiece_ticks (n w : ℕ) (hw : w ≤ 2048) (e : FallbackEv 2048) :
    (fbPiece n w hw e).ticks = w + 1 + e.fb + e.replay := by
  simp [fbPiece, Piece.ticks, Piece.ev, Piece.cmpN, PlaceEvent.slot, PlaceEvent.shiftTicks,
    PlaceEvent.fbTicks, PlaceEvent.replayTicks]
  omega

theorem fbPiece_adv (n w : ℕ) (hw : w ≤ 2048) (e : FallbackEv 2048) :
    (fbPiece n w hw e).adv = e.adv := by
  simp [fbPiece, Piece.adv, Piece.ev, PlaceEvent.adv, PlaceEvent.shiftAdv, PlaceEvent.fbAdv]

/-- A plain matched piece. -/
def Matched (p : Piece) : Prop := p.cmp = true ∧ p.shifts = [] ∧ p.fallbacks = []

/-- `CostedRun` only looks at the start state's centre and right head. -/
theorem costedRun_congr_start {a a' b : GalilVM} {k : ℕ} {L : List Piece}
    (hc : a'.center = a.center) (hr : a'.right = a.right) (h : CostedRun a' b k L) :
    CostedRun a b k L := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, by rw [h2, hc], by rw [← hr]; exact h3, fun p hp => by rw [← hr]; exact h4 p hp, h5⟩

/-- A one-piece costed run. -/
theorem costedRun_single {a b : GalilVM} (p : Piece)
    (hpl : position a.right < p.place ∧ p.place ≤ position b.right)
    (hcen : position b.center = position a.center + p.adv) :
    CostedRun a b p.ticks [p] :=
  ⟨by simp, by simpa using hcen, by omega, fun x hx => by
    rw [List.mem_singleton] at hx; subst hx; exact hpl, List.pairwise_singleton _ _⟩

/-! ## 1. Scan segments -/

/-- Outside a replay, a segment whose right head is blocked stays blocked. -/
theorem watchSegE_noRight (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) {es : List Bool}
    {c c' : Control} {s t : GalilVM} (h : WatchSegE P q first delay es c s c' t) :
    c.replaying = false → ¬ canRight s.right → ¬ canRight t.right := by
  induction h with
  | stop => intro _ h; exact h
  | wait c s s' _ _ _ hb _ ih =>
    intro hr hn
    have hrr := (background_frame P q first hb).2.1
    exact ih hr (by rw [hrr]; exact hn)
  | count _ _ _ _ _ ha => intro _ hn; exact absurd ha hn
  | «match» _ _ _ _ _ _ _ ha => intro _ hn; exact absurd ha hn
  | matchIdle _ _ _ _ _ _ _ ha => intro _ hn; exact absurd ha hn
  | countR _ _ _ _ hr => intro hr' _; rw [hr] at hr'; cases hr'
  | matchIdleR _ _ _ _ _ _ _ _ ha => intro _ hn; exact absurd ha hn

/-- One matched comparison as a costed run, with the scan invariant carried. -/
theorem costedRun_one_match (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9)
    (delay : ℕ) {c c1 : Control} {s u : GalilVM} (h1 : WatchSegE P q first delay [true] c s c1 u)
    {C k : ℕ} (hi : ScanInvariant raw C k s.left s.right) (w : ℕ) (hw : w ≤ 2048) :
    ScanInvariant raw C (k + 1) u.left u.right ∧
      position u.right = position s.right + 1 ∧ u.center = s.center ∧
      CostedRun s u (w + 1) [cmpPiece (position s.right + 1) w hw] := by
  obtain ⟨hi1, hp1⟩ := watchSegE_right_position raw P q first delay h1 hi
  have hc1 := watchSegE_center P q first delay h1
  simp only [List.count_singleton_self] at hi1 hp1
  refine ⟨hi1, hp1, hc1, ?_⟩
  have := costedRun_single (a := s) (b := u) (cmpPiece (position s.right + 1) w hw)
    (by simp only [cmpPiece]; omega) (by rw [cmpPiece_adv, hc1]; rfl)
  rwa [cmpPiece_ticks] at this

/-- **`costedRun_watchSegE_pend`.**  A scan segment at clock `2048`, entered with
`w` pending background ticks (`w + clock ≤ 2048`), from a scan invariant, ending
with the right head able to move: its matched comparisons are pieces (plain,
`cmp = true`), and the background ticks after the last one are pending
(`w1`), with `k' + w1 = w + |es|` and `w1 + clock' ≤ 2048`. -/
theorem costedRun_watchSegE_pend (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9)
    {es : List Bool} {c c' : Control} {s t : GalilVM}
    (h : WatchSegE P q first 2048 es c s c' t) :
    ∀ (C k w : ℕ), ScanInvariant raw C k s.left s.right → w + c.clock ≤ 2048 →
      canRight t.right →
      ∃ (L : List Piece) (k' w1 : ℕ), CostedRun s t k' L ∧ k' + w1 = w + es.length ∧
        w1 + c'.clock ≤ 2048 ∧ L.length = es.count true ∧ (∀ p ∈ L, Matched p) := by
  induction h with
  | stop c s =>
    intro C k w _ hw _
    exact ⟨[], 0, w, costedRun_nil s, by simp, hw, by simp, fun p hp => absurd hp List.not_mem_nil⟩
  | wait c s s' _ hr hn hb rest _ =>
    intro C k w _ _ htR
    have hrr := (background_frame P q first hb).2.1
    exact absurd htR (watchSegE_noRight P q first 2048 rest hr (by rw [hrr]; exact hn))
  | count c s s' _ _ _ hc hb _ ih =>
    intro C k w hi hw htR
    obtain ⟨hl, hrr, hcen, _⟩ := background_frame P q first hb
    obtain ⟨L, k', w1, hcr, he, hw1, hlen, hL⟩ :=
      ih C k (w + 1) (by rw [hl, hrr]; exact hi) (by dsimp only; omega) htR
    exact ⟨L, k', w1, costedRun_congr_start hcen hrr hcr, by simp; omega, hw1,
      by simpa using hlen, hL⟩
  | countR c s s' _ _ hc _ hb _ ih =>
    intro C k w hi hw htR
    obtain ⟨hl, hrr, hcen, _⟩ := background_frame P q first hb
    obtain ⟨L, k', w1, hcr, he, hw1, hlen, hL⟩ :=
      ih C k (w + 1) (by rw [hl, hrr]; exact hi) (by dsimp only; omega) htR
    exact ⟨L, k', w1, costedRun_congr_start hcen hrr hcr, by simp; omega, hw1,
      by simpa using hlen, hL⟩
  | «match» c s vs vq o hm hr ha hc hne hcmp hmt hq ho _ ih =>
    intro C k w hi hw htR
    obtain ⟨hi1, _, _, hcr1⟩ := costedRun_one_match raw P q first 2048
      (.match c s vs vq o hm hr ha hc hne hcmp hmt hq ho (.stop _ _)) hi w (by omega)
    obtain ⟨L, k', w1, hcr, he, hw1, hlen, hL⟩ := ih C (k + 1) 0 hi1 (by simp) htR
    refine ⟨_ :: L, (w + 1) + k', w1, costedRun_trans hcr1 hcr, by simp; omega, hw1,
      by simp [hlen], ?_⟩
    intro p hp
    rcases List.mem_cons.1 hp with hp | hp
    · subst hp; exact ⟨rfl, rfl, rfl⟩
    · exact hL p hp
  | matchIdle c s vs vq o hm hr ha hc hidle hl hrr hvs hmt hq hnf ho _ ih =>
    intro C k w hi hw htR
    obtain ⟨hi1, _, _, hcr1⟩ := costedRun_one_match raw P q first 2048
      (.matchIdle c s vs vq o hm hr ha hc hidle hl hrr hvs hmt hq hnf ho (.stop _ _)) hi w
      (by omega)
    obtain ⟨L, k', w1, hcr, he, hw1, hlen, hL⟩ := ih C (k + 1) 0 hi1 (by simp) htR
    refine ⟨_ :: L, (w + 1) + k', w1, costedRun_trans hcr1 hcr, by simp; omega, hw1,
      by simp [hlen], ?_⟩
    intro p hp
    rcases List.mem_cons.1 hp with hp | hp
    · subst hp; exact ⟨rfl, rfl, rfl⟩
    · exact hL p hp
  | matchIdleR c s vs vq o hm hr hc ha hidle hl hrr hvs hmt hq hnf ho _ ih =>
    intro C k w hi hw htR
    obtain ⟨hi1, _, _, hcr1⟩ := costedRun_one_match raw P q first 2048
      (.matchIdleR c s vs vq o hm hr hc ha hidle hl hrr hvs hmt hq hnf ho (.stop _ _)) hi w
      (by omega)
    obtain ⟨L, k', w1, hcr, he, hw1, hlen, hL⟩ := ih C (k + 1) 0 hi1 (by simp) htR
    refine ⟨_ :: L, (w + 1) + k', w1, costedRun_trans hcr1 hcr, by simp; omega, hw1,
      by simp [hlen], ?_⟩
    intro p hp
    rcases List.mem_cons.1 hp with hp | hp
    · subst hp; exact ⟨rfl, rfl, rfl⟩
    · exact hL p hp

/-- **`costedRun_watchSegE`.**  The same from a fresh entry (`clock ≤ 2048`, no
pending wait); the centre is unchanged (all advances are `0`). -/
theorem costedRun_watchSegE (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9)
    {es : List Bool} {c c' : Control} {s t : GalilVM}
    (h : WatchSegE P q first 2048 es c s c' t) {C k : ℕ}
    (hi : ScanInvariant raw C k s.left s.right) (hc : c.clock ≤ 2048) (htR : canRight t.right) :
    ∃ (L : List Piece) (k' w1 : ℕ), CostedRun s t k' L ∧ k' + w1 = es.length ∧
      w1 + c'.clock ≤ 2048 ∧ L.length = es.count true ∧ (∀ p ∈ L, Matched p) ∧
      position t.center = position s.center ∧
      position t.right = position s.right + es.count true := by
  obtain ⟨L, k', w1, hcr, he, hw1, hlen, hL⟩ :=
    costedRun_watchSegE_pend raw P q first h C k 0 hi (by omega) htR
  exact ⟨L, k', w1, hcr, by omega, hw1, hlen, hL,
    by rw [watchSegE_center P q first 2048 h],
    (watchSegE_right_position raw P q first 2048 h hi).2⟩

/-- A segment that ends on a fresh clock (e.g. right after a comparison) has no
pending ticks: it is a costed run of exactly `|es|` ticks. -/
theorem costedRun_watchSegE_closed (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9)
    {es : List Bool} {c c' : Control} {s t : GalilVM}
    (h : WatchSegE P q first 2048 es c s c' t) {C k : ℕ}
    (hi : ScanInvariant raw C k s.left s.right) (hc : c.clock ≤ 2048) (htR : canRight t.right)
    (hc' : c'.clock = 2048) :
    ∃ L : List Piece, CostedRun s t es.length L ∧ L.length = es.count true ∧
      (∀ p ∈ L, Matched p) := by
  obtain ⟨L, k', w1, hcr, he, hw1, hlen, hL, -, -⟩ := costedRun_watchSegE raw P q first h hi hc htR
  have hk : k' = es.length := by omega
  exact ⟨L, hk ▸ hcr, hlen, hL⟩

/-! ## 2. The target match -/

/-- **`costedRun_target_match`.**  A scan segment into the `AtTarget` state
(`clock = 1`, right head on `2m−2`, able to move) followed by the matching
comparison onto `2m−1` (landing in `afterCompare t ⟨left t.left, right t.right, idle⟩ vq`,
the landing state of `reachAt_of_target_match`): `|es| + 1` ticks, the last
piece a comparison piece at `2m−1`. -/
theorem costedRun_target_match (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9)
    {es : List Bool} {c c' : Control} {r t : GalilVM}
    (h : WatchSegE P q first 2048 es c r c' t) {C k : ℕ}
    (hi : ScanInvariant raw C k r.left r.right) (hc : c.clock ≤ 2048)
    (hc1 : c'.clock = 1) (hav : canRight t.right) (m : ℕ) (hm1 : 1 ≤ m)
    (hpos : position t.right = 2 * m - 2) (vq : SearchVM) :
    ∃ (L : List Piece) (w : ℕ) (hw : w ≤ 2048),
      CostedRun r (afterCompare t ⟨left t.left, right t.right, ChainVM.idle⟩ vq) (es.length + 1)
        (L ++ [cmpPiece (2 * m - 1) w hw]) ∧
      (∀ p ∈ L, Matched p) ∧
      position (afterCompare t ⟨left t.left, right t.right, ChainVM.idle⟩ vq).right = 2 * m - 1 := by
  obtain ⟨L, k', w1, hcr, he, hw1, _, hL, _, _⟩ := costedRun_watchSegE raw P q first h hi hc hav
  have hit := (watchSegE_right_position raw P q first 2048 h hi).1
  have hrp : position (right t.right) = position t.right + 1 :=
    right_position t.right hav (represented_position _ raw hit.rightRep hit.rightPresent).1
  set u := afterCompare t ⟨left t.left, right t.right, ChainVM.idle⟩ vq with hu
  have hur : position u.right = 2 * m - 1 := by
    rw [hu, afterCompare_right]; dsimp only; omega
  have hw : w1 ≤ 2048 := by omega
  have h2 : CostedRun t u (w1 + 1) [cmpPiece (2 * m - 1) w1 hw] := by
    have := costedRun_single (a := t) (b := u) (cmpPiece (2 * m - 1) w1 hw)
      (by simp only [cmpPiece]; omega) (by rw [cmpPiece_adv, hu, afterCompare_center]; rfl)
    rwa [cmpPiece_ticks] at this
  refine ⟨L, w1, hw, ?_, hL, hur⟩
  have := costedRun_trans hcr h2
  rwa [show k' + (w1 + 1) = es.length + 1 by omega] at this

/-! ## 3. Fallback + replay -/

/-- **The fallback piece.**  The mismatching comparison at `n1` (one past the
right head of `s`), the fallback landing `t` (centre = right head at `n1 − R`,
centre advance `e.adv`) and a replay to `t'` moving the right head by `R`
without moving the centre: one piece at `n1`. -/
theorem costedRun_fallback_core {s t t' : GalilVM} (n1 R w : ℕ) (hw : w ≤ 2048)
    (e : FallbackEv 2048) (hn1 : n1 = position s.right + 1)
    (hcen : position t.center = position s.center + e.adv)
    (hland : position t.center = n1 - R) (hCR : t.center = t.right) (hRn : R ≤ n1)
    (hrr : position t'.right = position t.right + R) (hcc : t'.center = t.center) :
    CostedRun s t' (w + 1 + e.fb + e.replay) [fbPiece n1 w hw e] ∧ position t'.right = n1 := by
  have hr' : position t'.right = n1 := by rw [hrr, ← hCR, hland]; omega
  have := costedRun_single (a := s) (b := t') (fbPiece n1 w hw e)
    (by simp only [fbPiece]; omega) (by rw [fbPiece_adv, hcc, hcen])
  rw [fbPiece_ticks] at this
  exact ⟨this, hr'⟩

/-- The mismatch place is `C + Rad + 1`, one past the right head. -/
theorem mismatch_place {raw : List (Fin 2)} {s : GalilVM} {Rad : ℕ}
    (hi : ScanInvariant raw (position s.center) Rad s.left s.right) (hav : canRight s.right) :
    position (right s.right) = position s.right + 1 ∧
      position (right s.right) = position s.center + Rad + 1 := by
  have := right_position s.right hav (represented_position _ raw hi.rightRep hi.rightPresent).1
  have h2 := hi.rightPos
  omega

/-- **`costedRun_fallback_replay`.**  A scan segment `s0 ⇝ s` (entry clock
`≤ 2048`, exit at the comparison tick, right head able to move), the
mismatching comparison at `n1 = position (right s.right)`, the fallback phase
of `fb` ticks landing in `t`, and a replay `t ⇝ t'` of `|es| = R·2048` ticks
moving the right head by `R` and keeping the centre.  The whole run is a
costed run of `|es0| + 1 + fb + |es|` ticks: the segment's matched pieces and
ONE fallback piece at `n1` (wait = the segment's pending ticks), whose event is
`fallbackEv2048_of_landing`'s.  The right head ends exactly on `n1`.

The search-contract inputs (`hres`, `hidle`, `hlow`, …), `hfb`, and the replay
facts `hrr`/`hcc` are named hypotheses. -/
theorem costedRun_fallback_replay (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9)
    {es0 : List Bool} {c0 c : Control} {s0 s : GalilVM}
    (hseg : WatchSegE P q first 2048 es0 c0 s0 c s) {C0 k0 : ℕ}
    (hi0 : ScanInvariant raw C0 k0 s0.left s0.right) (hc0 : c0.clock ≤ 2048)
    (hc1 : c.clock = 1)
    -- the mismatching state (inputs of `fallbackEv2048_of_landing`)
    {t t' : GalilVM} {Rad : ℕ}
    (hi : ScanInvariant raw (position s.center) Rad s.left s.right) (hav : canRight s.right)
    (hRR : RadiusRep s.radius Rad) (hS : SpanRep s) (ℓ : ℕ) (hv : value s.length = ℓ)
    (hkC : Rad < position s.center)
    (a : Fin 2) (xs rs' q' : List (Fin 2))
    (hdec : right s.right = represent ⟨a :: xs,(right s.right).gap⟩ (rs'.map some) q')
    (hraw : raw = (a :: xs).reverse ++ rs' ++ q')
    (a₀ : Fin 2) (ls₀ rs₀ q₀ : List (Fin 2)) (gap₀ : Bool) {lower span : ℕ}
    {y : GalilFppWide.Config 12}
    (hraw₀ : raw = (a₀ :: ls₀).reverse ++ rs₀ ++ q₀)
    (hC₀ : position s.center = position (represent ⟨a₀ :: ls₀,gap₀⟩ (rs₀.map some) q₀))
    (hspan : Rad ≤ span)
    (hres : GalilDpCorrect.Result
      ((GalilScaffoldPlace.stream ⟨a₀ :: ls₀,gap₀⟩).take (span+1)) lower 0 y)
    (hidle : y.pc = 347)
    (hlow : ∀ δ, 0 < δ → δ ≤ lower → ¬ HasPeriod (Span raw (position s.center) Rad) (2*δ))
    (fb : ℕ) (es : List Bool) (R : ℕ)
    (hR : R = chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)))
    (hfb : fb ≤ 1588*(ℓ+1) + 836) (hes : es.length = R * 2048)
    -- the landing
    (hpos : position t.center = position (right s.right) - R) (hCR : t.center = t.right)
    -- the replay
    (hrr : position t'.right = position t.right + R) (hcc : t'.center = t.center) :
    ∃ (L : List Piece) (w : ℕ) (hw : w ≤ 2048) (e : FallbackEv 2048),
      CostedRun s0 t' (es0.length + 1 + fb + es.length)
        (L ++ [fbPiece (position (right s.right)) w hw e]) ∧
      (∀ p ∈ L, Matched p) ∧
      e.k = Rad ∧ e.r = R ∧ e.fb = fb ∧ e.replay = es.length ∧
      position t'.right = position (right s.right) := by
  obtain ⟨L, k', w1, hcr, he, hw1, _, hL, _, _⟩ := costedRun_watchSegE raw P q first hseg hi0 hc0 hav
  obtain ⟨e, hek, her, hefb, herep, _, hecen⟩ :=
    fallbackEv2048_of_landing hi hav hRR hS ℓ hv hkC a xs rs' q' hdec hraw a₀ ls₀ rs₀ q₀ gap₀
      hraw₀ hC₀ hspan hres hidle hlow fb es R hR hfb hes hpos
  obtain ⟨hn1, hn1'⟩ := mismatch_place hi hav
  have hRn : R ≤ position (right s.right) := by have := e.r_le; omega
  have hw : w1 ≤ 2048 := by omega
  obtain ⟨h2, hr'⟩ := costedRun_fallback_core (s := s) (t := t) (t' := t') (position (right s.right))
    R w1 hw e hn1 hecen hpos hCR hRn hrr hcc
  refine ⟨L, w1, hw, e, ?_, hL, hek, her, hefb, herep, hr'⟩
  have := costedRun_trans hcr h2
  rwa [hefb, herep, show k' + (w1 + 1 + fb + es.length) = es0.length + 1 + fb + es.length by omega]
    at this

/-- **`costedRun_fallback_zero`.**  `R = 0`: no replay; the landing `t` is the
end state, its right head already on `n1`. -/
theorem costedRun_fallback_zero (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9)
    {es0 : List Bool} {c0 c : Control} {s0 s : GalilVM}
    (hseg : WatchSegE P q first 2048 es0 c0 s0 c s) {C0 k0 : ℕ}
    (hi0 : ScanInvariant raw C0 k0 s0.left s0.right) (hc0 : c0.clock ≤ 2048)
    (hc1 : c.clock = 1)
    {t : GalilVM} {Rad : ℕ}
    (hi : ScanInvariant raw (position s.center) Rad s.left s.right) (hav : canRight s.right)
    (hRR : RadiusRep s.radius Rad) (hS : SpanRep s) (ℓ : ℕ) (hv : value s.length = ℓ)
    (hkC : Rad < position s.center)
    (a : Fin 2) (xs rs' q' : List (Fin 2))
    (hdec : right s.right = represent ⟨a :: xs,(right s.right).gap⟩ (rs'.map some) q')
    (hraw : raw = (a :: xs).reverse ++ rs' ++ q')
    (a₀ : Fin 2) (ls₀ rs₀ q₀ : List (Fin 2)) (gap₀ : Bool) {lower span : ℕ}
    {y : GalilFppWide.Config 12}
    (hraw₀ : raw = (a₀ :: ls₀).reverse ++ rs₀ ++ q₀)
    (hC₀ : position s.center = position (represent ⟨a₀ :: ls₀,gap₀⟩ (rs₀.map some) q₀))
    (hspan : Rad ≤ span)
    (hres : GalilDpCorrect.Result
      ((GalilScaffoldPlace.stream ⟨a₀ :: ls₀,gap₀⟩).take (span+1)) lower 0 y)
    (hidle : y.pc = 347)
    (hlow : ∀ δ, 0 < δ → δ ≤ lower → ¬ HasPeriod (Span raw (position s.center) Rad) (2*δ))
    (fb : ℕ)
    (hR : 0 = chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)))
    (hfb : fb ≤ 1588*(ℓ+1) + 836)
    (hpos : position t.center = position (right s.right) - 0) (hCR : t.center = t.right) :
    ∃ (L : List Piece) (w : ℕ) (hw : w ≤ 2048) (e : FallbackEv 2048),
      CostedRun s0 t (es0.length + 1 + fb) (L ++ [fbPiece (position (right s.right)) w hw e]) ∧
      (∀ p ∈ L, Matched p) ∧
      e.k = Rad ∧ e.r = 0 ∧ e.fb = fb ∧ e.replay = 0 ∧
      position t.right = position (right s.right) := by
  obtain ⟨L, w, hw, e, h1, h2, h3, h4, h5, h6, h7⟩ :=
    costedRun_fallback_replay raw P q first hseg hi0 hc0 hc1 (t' := t) hi hav hRR hS ℓ hv hkC
      a xs rs' q' hdec hraw a₀ ls₀ rs₀ q₀ gap₀ hraw₀ hC₀ hspan hres hidle hlow fb [] 0 hR hfb
      (by simp) hpos hCR (by simp) rfl
  exact ⟨L, w, hw, e, by simpa using h1, h2, h3, h4, h5, by simpa using h6, h7⟩

/-- **`replay_right_eq_place`.**  From a fallback landing with chosen radius
`R > 0` (centre = right head at `n1 − R`, `R ≤ n1`), the machine replay
(`replay_after_fallback`) is a `WatchSegE` of `R·2048` ticks whose end state has
its right head exactly on `n1` and the centre unchanged. -/
theorem replay_right_eq_place (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9)
    (hex : ∀ s, P.replayExhausted s = zero s.replay)
    (hsearch : ∀ s : GalilVM, SearchReady (searchLens.get s) → ∀ a : Bool,
      ∃ v, searchEffect P a s v)
    (hpres : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s) → searchEffect P a s v → SearchReady v)
    (hquiet : SearchQuiet P)
    (n1 R : ℕ) (hR0 : 0 < R) (hRle : R ≤ n1) (c : Control) (t : GalilVM)
    (hm : c.mode = Mode.scan) (hc : c.clock = 2048) (hrpl : c.replaying = true)
    (hR : Restarted raw t 0 reset) (hrep : t.replay = ofNat R)
    (hpos : position t.center = n1 - R) (hCR : t.center = t.right)
    (hM : MInv raw c t) (hfr : Frontier t) (hsi : ShiftIdle t) :
    ∃ (es : List Bool) (c' : Control) (t' : GalilVM),
      WatchSegE P q first 2048 es c t c' t' ∧
      (SoundScanNR raw ⟨c', t'⟩ →
        StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) es.length ⟨c, t⟩ ⟨c', t'⟩) ∧
      es.length = R * 2048 ∧ position t'.right = position t.right + R ∧
      t'.center = t.center ∧ position t'.right = n1 ∧ InvScan 2048 raw c' t' R := by
  obtain ⟨es, c', t', hseg, hst, hlen, _, hrr, hcc, hinv⟩ :=
    replay_after_fallback raw P q first 2048 hex (by norm_num) hsearch hpres hquiet R hR0 c t
      hm hc hrpl hR hrep hM hfr hsi
  refine ⟨es, c', t', hseg, hst, hlen, hrr, hcc, ?_, hinv⟩
  rw [hrr, ← hCR, hpos]; omega

/-- **`costedRun_fallback_replay_machine`.**  `costedRun_fallback_replay` with
the replay supplied by the machine (`replay_after_fallback`), for `R > 0`. -/
theorem costedRun_fallback_replay_machine (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9)
    (hex : ∀ s, P.replayExhausted s = zero s.replay)
    (hsearch : ∀ s : GalilVM, SearchReady (searchLens.get s) → ∀ a : Bool,
      ∃ v, searchEffect P a s v)
    (hpres : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s) → searchEffect P a s v → SearchReady v)
    (hquiet : SearchQuiet P)
    {es0 : List Bool} {c0 c : Control} {s0 s : GalilVM}
    (hseg : WatchSegE P q first 2048 es0 c0 s0 c s) {C0 k0 : ℕ}
    (hi0 : ScanInvariant raw C0 k0 s0.left s0.right) (hc0 : c0.clock ≤ 2048)
    (hc1 : c.clock = 1)
    {t : GalilVM} {Rad : ℕ}
    (hi : ScanInvariant raw (position s.center) Rad s.left s.right) (hav : canRight s.right)
    (hRR : RadiusRep s.radius Rad) (hS : SpanRep s) (ℓ : ℕ) (hv : value s.length = ℓ)
    (hkC : Rad < position s.center)
    (a : Fin 2) (xs rs' q' : List (Fin 2))
    (hdec : right s.right = represent ⟨a :: xs,(right s.right).gap⟩ (rs'.map some) q')
    (hraw : raw = (a :: xs).reverse ++ rs' ++ q')
    (a₀ : Fin 2) (ls₀ rs₀ q₀ : List (Fin 2)) (gap₀ : Bool) {lower span : ℕ}
    {y : GalilFppWide.Config 12}
    (hraw₀ : raw = (a₀ :: ls₀).reverse ++ rs₀ ++ q₀)
    (hC₀ : position s.center = position (represent ⟨a₀ :: ls₀,gap₀⟩ (rs₀.map some) q₀))
    (hspan : Rad ≤ span)
    (hres : GalilDpCorrect.Result
      ((GalilScaffoldPlace.stream ⟨a₀ :: ls₀,gap₀⟩).take (span+1)) lower 0 y)
    (hidle : y.pc = 347)
    (hlow : ∀ δ, 0 < δ → δ ≤ lower → ¬ HasPeriod (Span raw (position s.center) Rad) (2*δ))
    (fb R : ℕ) (hR0 : 0 < R)
    (hR : R = chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)))
    (hfb : fb ≤ 1588*(ℓ+1) + 836)
    -- the landing (`fallback_landing`)
    (cT : Control) (hm : cT.mode = Mode.scan) (hc : cT.clock = 2048) (hrpl : cT.replaying = true)
    (hRst : Restarted raw t 0 reset) (hrep : t.replay = ofNat R)
    (hpos : position t.center = position (right s.right) - R) (hCR : t.center = t.right)
    (hM : MInv raw cT t) (hfr : Frontier t) (hsi : ShiftIdle t) :
    ∃ (es : List Bool) (c' : Control) (t' : GalilVM),
      WatchSegE P q first 2048 es cT t c' t' ∧
      (SoundScanNR raw ⟨c', t'⟩ →
        StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) es.length ⟨cT, t⟩ ⟨c', t'⟩) ∧
      es.length = R * 2048 ∧ InvScan 2048 raw c' t' R ∧
      ∃ (L : List Piece) (w : ℕ) (hw : w ≤ 2048) (e : FallbackEv 2048),
        CostedRun s0 t' (es0.length + 1 + fb + es.length)
          (L ++ [fbPiece (position (right s.right)) w hw e]) ∧
        (∀ p ∈ L, Matched p) ∧
        e.k = Rad ∧ e.r = R ∧ e.fb = fb ∧ e.replay = es.length ∧
        position t'.right = position (right s.right) := by
  obtain ⟨es, c', t', hrseg, hst, hlen, _, hrr, hcc, hinv⟩ :=
    replay_after_fallback raw P q first 2048 hex (by norm_num) hsearch hpres hquiet R hR0 cT t
      hm hc hrpl hRst hrep hM hfr hsi
  exact ⟨es, c', t', hrseg, hst, hlen, hinv,
    costedRun_fallback_replay raw P q first hseg hi0 hc0 hc1 hi hav hRR hS ℓ hv hkC a xs rs' q'
      hdec hraw a₀ ls₀ rs₀ q₀ gap₀ hraw₀ hC₀ hspan hres hidle hlow fb es R hR hfb hlen hpos hCR
      hrr hcc⟩

#print axioms cmpPiece_ticks
#print axioms cmpPiece_adv
#print axioms fbPiece_ticks
#print axioms fbPiece_adv
#print axioms costedRun_congr_start
#print axioms costedRun_single
#print axioms watchSegE_noRight
#print axioms costedRun_one_match
#print axioms costedRun_watchSegE_pend
#print axioms costedRun_watchSegE
#print axioms costedRun_watchSegE_closed
#print axioms costedRun_target_match
#print axioms costedRun_fallback_core
#print axioms mismatch_place
#print axioms costedRun_fallback_replay
#print axioms costedRun_fallback_zero
#print axioms replay_right_eq_place
#print axioms costedRun_fallback_replay_machine

end PalPeg.GalilCostedFallback
