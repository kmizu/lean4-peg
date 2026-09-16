import PalPeg.GalilScaffoldTopFallbackFound

/-!
# The initial state, and the premises of a mismatch after a segment

The `init` tick puts all heads on the first place with the search started
from lower bound `0`: a `Restarted` state with radius `0`. Along a
chain-idle segment from a restarted state the right head stays represented,
so a mismatching comparison there has the premises of `fallback_next_found`.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

theorem afterCompare_remaining (s : GalilVM) (vs : ScanVM) (vq : SearchVM) :
    (afterCompare s vs vq).remaining = s.remaining := rfl

/-- A segment keeps the shift counter. -/
theorem watchSegE_remaining (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) {es : List Bool}
    {c c' : Control} {s t : GalilVM} (h : WatchSegE P q first delay es c s c' t) :
    t.remaining = s.remaining := by
  induction h with
  | stop c s => rfl
  | wait c s s' _ _ _ hb _ ih =>
    obtain ⟨_, _, _, _, _, _, _, _, hrem, _⟩ := backgroundS_fields P q first hb
    rw [ih, hrem]
  | count c s s' _ _ _ _ hb _ ih =>
    obtain ⟨_, _, _, _, _, _, _, _, hrem, _⟩ := backgroundS_fields P q first hb
    rw [ih, hrem]
  | «match» c s vs vq o _ _ _ _ _ _ _ _ _ _ ih => rw [ih, afterCompare_remaining]
  | matchIdle c s vs vq o _ _ _ _ _ _ _ _ _ _ _ _ _ ih => rw [ih, afterCompare_remaining]
  | countR c s s' _ _ _ _ hb _ ih =>
    obtain ⟨_, _, _, _, _, _, _, _, hrem, _⟩ := backgroundS_fields P q first hb
    rw [ih, hrem]
  | matchIdleR c s vs vq o _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    rw [ih, replayDec_remaining, afterCompare_remaining]

/-- The input head before the first place: on the gap, the word to come. -/
def initialHead (raw : List (Fin 2)) : PlaceHead := ⟨⟨none, [], [], raw⟩, true⟩

theorem initialHead_canRight (raw : List (Fin 2)) (h : raw ≠ []) : canRight (initialHead raw) :=
  Or.inr (Or.inr h)

theorem initialHead_right_represents (a : Fin 2) (rest : List (Fin 2)) :
    GalilScaffoldInputTrace.Represents (right (initialHead (a :: rest))).head (a :: rest) :=
  ⟨[a], [], rest, rfl, rfl⟩

theorem initialHead_right_focus (a : Fin 2) (rest : List (Fin 2)) :
    (right (initialHead (a :: rest))).head.focus ≠ none := by
  intro h; cases h

theorem initialHead_right_position (a : Fin 2) (rest : List (Fin 2)) :
    position (right (initialHead (a :: rest))) = 1 := rfl

/-- The `init` tick on `galilFrameS`: a restarted state with radius `0` on
the first place. -/
theorem init_restarted (onLetter leftFirst guard : GalilVM → Prop) (bs bf rs : GalilVM → GalilVM → Prop)
    (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place) (entry : ℕ)
    (q : ℕ) (first : Fin 9) (delay : ℕ) (c : Control) (hm : c.mode = .init) (s0 : GalilVM)
    (a : Fin 2) (rest : List (Fin 2)) (h0 : s0.right = initialHead (a :: rest))
    (hrad : s0.radius = reset) (hlen : s0.length = reset) :
    ∃ t : GalilVM,
      Tick (galilFrameS (galilShared onLetter leftFirst guard bs bf rs centre place entry) q first) delay ⟨c, s0⟩
        ⟨{c with mode := .scan, output := true}, t⟩ ∧
      Restarted (a :: rest) t 0 reset ∧ position t.center = 1 ∧
      t.left = t.center ∧ t.right = t.center ∧ t.remaining = s0.remaining ∧ t.replay = s0.replay := by
  obtain ⟨t, ht, hR, hL, hC, hlen', hrad', hrem, hrep, _, _, hchain, hsearch, hlower, _⟩ :=
    init_tick onLetter leftFirst guard bs bf rs centre place entry q first delay c hm s0
  have htS := tick_S_of_tick _ q first delay ht (by rw [hm]; decide)
  rw [h0] at hR hL hC
  refine ⟨t, htS, ?_, by rw [hC, initialHead_right_position], by rw [hL, hC], by rw [hR, hC], hrem, hrep⟩
  refine ⟨hchain, ?_, ?_, ?_, ?_, ?_, ?_, hlower, ofNat_canonical 0, by rw [reset_eq_ofNat, ofNat_value]; simp⟩
  · rw [hC]; exact initialHead_right_represents a rest
  · rw [hC]; exact initialHead_right_focus a rest
  · rw [hL, hR, hC]
    exact scan_initial _ _ (initialHead_right_represents a rest) (initialHead_right_focus a rest)
  · rw [hrad', hrad, reset_eq_ofNat]; exact ⟨ofNat_canonical 0, ofNat_value 0⟩
  · rw [hlen', hlen, reset_eq_ofNat, inc_ofNat]; exact ofNat_canonical 1
  · rw [hsearch, hrad']

/-- After a chain-idle segment from a restarted state, the right head is
represented and on a real symbol after its move: the premises of a
mismatching comparison's fallback. -/
theorem segment_mismatch_ready (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    {raw : List (Fin 2)} {r : GalilVM} {Rad : ℕ} {last : Counter} (hR : Restarted raw r Rad last)
    {es : List Bool} {c0 c1 : Control} {s : GalilVM} (hseg : WatchSegE P q first delay es c0 r c1 s)
    (hav : canRight s.right) :
    GalilScaffoldInputTrace.Represents (right s.right).head raw ∧ (right s.right).head.focus ≠ none ∧
      Canonical s.length ∧ s.remaining = r.remaining ∧
      ScanInvariant raw (position r.center) (Rad + es.count true) s.left s.right := by
  obtain ⟨_, _, _, hscan, ⟨hrc, _⟩, hlc, _⟩ := hR
  obtain ⟨hsc, _, _, _, hlc1⟩ := watchSegE_heads P q first delay hseg
  have hinv : ScanInvariant raw (position r.center) (Rad + es.count true) s.left s.right :=
    scan_events_invariant (hsc raw (position r.center) Rad) hscan
  have hrep := right_word s.right raw hinv.rightRep hav
  have hpos : position (right s.right) = position s.right + 1 :=
    right_position s.right hav (represented_position _ raw hinv.rightRep hinv.rightPresent).1
  refine ⟨hrep, present_of_position _ hrep (by rw [hpos]; omega), hlc1 hlc,
    watchSegE_remaining P q first delay hseg, hinv⟩

#print axioms init_restarted
#print axioms segment_mismatch_ready

end PalPeg.GalilScaffoldChainInputSupply
