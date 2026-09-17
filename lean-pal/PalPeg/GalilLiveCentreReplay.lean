import PalPeg.GalilLiveCentreFallback
import PalPeg.GalilLiveCentreSeg

/-!
# The centre invariant of the controller, through replays

`MInv raw c s`: while replaying, the replay counter is the distance left to
the saved place, where the centre is the leftmost live centre; when not
replaying, the centre is the leftmost live centre at the right head. The
invariant is carried along chain-idle segments (`WatchSegE`), including the
replay steps, and is established after a fallback by
`leftmost_after_fallback`.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open Manacher GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-- The centre invariant of the controller. -/
def MInv (raw : List (Fin 2)) (c : Control) (s : GalilVM) : Prop :=
  (c.replaying = true →
    ∃ m, 0 < m ∧ s.replay = ofNat m ∧ Leftmost raw (position s.right + m) (position s.center)) ∧
  (c.replaying = false → Leftmost raw (position s.right) (position s.center))

theorem minv_of_leftmost {raw : List (Fin 2)} {c : Control} {s : GalilVM}
    (h : Leftmost raw (position s.right) (position s.center)) (hr : c.replaying = false) : MInv raw c s :=
  ⟨(fun h1 => by rw [hr] at h1; cases h1), fun _ => h⟩

theorem minv_leftmost {raw : List (Fin 2)} {c : Control} {s : GalilVM} (h : MInv raw c s)
    (hr : c.replaying = false) : Leftmost raw (position s.right) (position s.center) := h.2 hr

theorem minv_same {raw : List (Fin 2)} {c c' : Control} {s s' : GalilVM} (hr : c'.replaying = c.replaying)
    (hR : s'.right = s.right) (hC : s'.center = s.center) (hrep : s'.replay = s.replay) (h : MInv raw c s) :
    MInv raw c' s' := by
  unfold MInv at *
  rw [hr, hR, hC, hrep]
  exact h

theorem afterCompare_replay (s : GalilVM) (vs : ScanVM) (vq : SearchVM) : (afterCompare s vs vq).replay = s.replay := rfl

theorem replayDec_true_replay (s : GalilVM) : (replayDec true s).replay = dec s.replay := rfl

/-- A matched comparison outside a replay keeps the invariant. -/
theorem minv_match {raw : List (Fin 2)} {c : Control} {s : GalilVM} {vs : ScanVM} {vq : SearchVM}
    (o : Bool) (delay : ℕ) (hr : c.replaying = false) (hl : vs.left = left s.left)
    (hrr : vs.right = right s.right) (hav : canRight s.right)
    (hmatch : read (left s.left) = read (right s.right)) {r : ℕ}
    (hi : ScanInvariant raw (position s.center) r s.left s.right) (h : MInv raw c s) :
    MInv raw {c with clock := delay, output := o, replaying := false} (afterCompare s vs vq) := by
  have hL := h.2 hr
  have hi' := scan_matched hi hav hmatch
  have hpos : position (right s.right) = position s.right + 1 :=
    right_position s.right hav (represented_position _ raw hi.rightRep hi.rightPresent).1
  refine ⟨(fun h1 => by cases h1), fun _ => ?_⟩
  rw [afterCompare_right, afterCompare_center, hrr, hpos]
  have hlive := live_of_scanInvariant hi'
  rw [hpos] at hlive
  exact leftmost_match hL hlive

/-- `MInv` reads only `replay`, `right` and `center`, none of which the chain
birth touches. -/
theorem minv_afterBirth {raw : List (Fin 2)} {c : Control} {s : GalilVM} (b : Bool)
    (h : MInv raw c s) : MInv raw c (afterBirth b s) := by
  refine ⟨fun hr => ?_, fun hr => ?_⟩
  · obtain ⟨m, hm0, hm1, hm2⟩ := h.1 hr
    exact ⟨m, hm0, by rw [afterBirth_replay]; exact hm1,
      by rw [afterBirth_right, afterBirth_center]; exact hm2⟩
  · rw [afterBirth_right, afterBirth_center]; exact h.2 hr

/-- A matched comparison during a replay: the counter decreases with the
distance; when it reaches zero the right head is at the saved place. -/
theorem minv_matchR {raw : List (Fin 2)} (P : Shared) (hex : ∀ s, P.replayExhausted s = zero s.replay)
    {c : Control} {s : GalilVM} {vs : ScanVM} {vq : SearchVM} (o : Bool) (delay : ℕ)
    (hr : c.replaying = true) (hrr : vs.right = right s.right) (hav : canRight s.right)
    {r : ℕ} (hi : ScanInvariant raw (position s.center) r s.left s.right) (h : MInv raw c s) :
    MInv raw {c with clock := delay, output := o, replaying := !P.replayExhausted (replayDec true (afterCompare s vs vq))} (replayDec true (afterCompare s vs vq)) := by
  obtain ⟨m, hm, hrep, hL⟩ := h.1 hr
  have hpos : position (right s.right) = position s.right + 1 :=
    right_position s.right hav (represented_position _ raw hi.rightRep hi.rightPresent).1
  obtain ⟨m', rfl⟩ : ∃ m', m = m'+1 := ⟨m-1, by omega⟩
  have hrep' : (replayDec true (afterCompare s vs vq)).replay = ofNat m' := by
    rw [replayDec_true_replay, afterCompare_replay, hrep, dec_ofNat_succ]
  have hR : (replayDec true (afterCompare s vs vq)).right = right s.right := by
    rw [replayDec_right, afterCompare_right, hrr]
  have hC : (replayDec true (afterCompare s vs vq)).center = s.center := by
    rw [replayDec_center, afterCompare_center]
  cases m' with
  | zero =>
    have hz : P.replayExhausted (replayDec true (afterCompare s vs vq)) = true := by
      rw [hex, hrep']; exact (zero_ofNat_iff 0).2 rfl
    refine ⟨fun h1 => ?_, fun _ => ?_⟩
    · simp [hz] at h1
    · rw [hR, hC, hpos]
      simpa using hL
  | succ k =>
    have hz : P.replayExhausted (replayDec true (afterCompare s vs vq)) = false := by
      rw [hex, hrep']; exact zero_ofNat_succ k
    refine ⟨fun _ => ⟨k+1, by omega, hrep', ?_⟩, fun h2 => ?_⟩
    · rw [hR, hC, hpos]
      have e : position s.right + 1 + (k + 1) = position s.right + (k + 1 + 1) := by omega
      rw [e]; exact hL
    · simp [hz] at h2

/-- The invariant along a chain-idle segment, replay steps included. -/
theorem minv_watchSegE (raw : List (Fin 2)) (P : Shared) (hex : ∀ s, P.replayExhausted s = zero s.replay)
    (q : ℕ) (first : Fin 9) (delay : ℕ) {es : List Bool} {c c' : Control} {s t : GalilVM}
    (h : WatchSegE P q first delay es c s c' t) :
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
  | countR c s s' _ _ _ _ hb _ ih =>
    intro r hi hM
    obtain ⟨hl, hr, _, hC, _, _, _, _, _, hrep, _, _⟩ := backgroundS_fields P q first hb
    refine ih r (by rw [hl, hr, hC]; exact hi) (minv_same rfl hr hC hrep hM)
  | «match» c s vs vq o _ hr ha _ _ hcmp hmt _ _ _ ih =>
    intro r hi hM
    have hmatch : read (left s.left) = read (right s.right) := by
      obtain ⟨⟨hl0, hr0, _⟩, _⟩ := hcmp
      rw [scanLens.get_set] at hl0 hr0
      have := matched_parts P q first hmt
      rw [hl0, hr0] at this; exact this
    obtain ⟨hl, hrr, _⟩ := compare_parts P q first hcmp hmatch
    have hi' := matched_invariant raw P q first vq hcmp hmt ha hi
    exact ih (r+1) hi' (minv_match o _ hr hl hrr ha hmatch hi hM)
  | matchIdle c s vs vq o _ hr ha _ _ hl hrr _ hmt _ _ _ _ ih =>
    intro r hi hM
    have hmatch : read (left s.left) = read (right s.right) := by
      have := matched_parts P q first hmt
      rw [hl, hrr] at this; exact this
    have hi' := matched_invariant' raw vq hl hrr hmatch ha hi
    exact ih (r+1) hi' (minv_match o _ hr hl hrr ha hmatch hi hM)
  | matchIdleR c s vs vq o _ hr _ ha _ hl hrr _ hmt _ _ _ _ ih =>
    intro r hi hM
    have hmatch : read (left s.left) = read (right s.right) := by
      have := matched_parts P q first hmt
      rw [hl, hrr] at this; exact this
    have hi' := matched_invariant' raw vq hl hrr hmatch ha hi
    have hi'' : ScanInvariant raw (position (replayDec true (afterCompare s vs vq)).center) (r+1)
        (replayDec true (afterCompare s vs vq)).left (replayDec true (afterCompare s vs vq)).right := by
      rw [replayDec_left, replayDec_right, replayDec_center, afterCompare_center]; exact hi'
    exact ih (r+1) hi'' (minv_matchR P hex o _ hr hrr ha hi hM)

/-- The invariant right after a fallback: the new centre is leftmost at the
saved place `n+1`, the replay counter is the distance back to it. -/
theorem minv_after_fallback {raw : List (Fin 2)} {t : GalilVM} {c : Control} {n r : ℕ}
    (hR : Restarted raw t 0 reset) (hrep : t.replay = ofNat r) (hpos : position t.center = n + 1 - r)
    (hL : Leftmost raw (n+1) (position t.center)) (hc : c.replaying = decide (0 < r)) :
    MInv raw c t := by
  have hright : position t.right = position t.center := by
    have := hR.2.2.2.1.rightPos; omega
  have hle : r ≤ n + 1 - r := by
    have := hL.1.2.2.1; rw [hpos] at this; omega
  rw [hpos] at hL
  refine ⟨fun h1 => ?_, fun h2 => ?_⟩
  · rw [hc] at h1
    have hr0 : 0 < r := by simpa using h1
    refine ⟨r, hr0, hrep, ?_⟩
    rw [hright, hpos]
    have e : n + 1 - r + r = n + 1 := by omega
    rw [e]; exact hL
  · rw [hc] at h2
    have hr0 : r = 0 := by simpa using h2
    subst hr0
    rw [hright, hpos]
    simpa using hL

#print axioms minv_watchSegE
#print axioms minv_after_fallback

end PalPeg.GalilScaffoldChainInputSupply
