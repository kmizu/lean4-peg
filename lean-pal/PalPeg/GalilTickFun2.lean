import PalPeg.GalilTickFun
import PalPeg.GalilLiveCentreReplay

/-!
# The clock and the replay branch of the scaffold tick

Two additions to `PalPeg.GalilTickFun`:

* `clock_pos_invariant`: no `Tick` constructor lowers the clock to zero, so a
  positive clock is preserved as long as the match delay is positive.  Every
  constructor either keeps the clock (`init`, `scan_wait`, the shift/copy/
  home/fpp/markEnd/choose/rewind units), decrements it from `1 < clock`
  (`scan_count`), or resets it to `delay` (`scan_match`, `scan_shift`,
  `scan_fallback`, `replayStart`, `restart`).

* `replay_match_of_minv`: under the centre invariant `MInv`, a comparison made
  while replaying always matches, so the constructors excluded from `Enabled`
  (a mismatching comparison with `replaying = true`) are unreachable.  `EnabledR`
  adds that branch to `Enabled` and `tick_exists_R` gives it a successor.
-/

set_option autoImplicit false
namespace PalPeg.GalilTickFun2

open PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilTickFun
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter
open GalilScaffoldInputHead GalilScaffoldChainVerifier Manacher

/-! ## 1. The clock never reaches zero -/

/-- Along a tick of `galilFrameS` a positive clock stays positive, provided the
match delay is positive.  No constructor sets `clock := 0`. -/
theorem clock_pos_invariant (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    {x y : State GalilVM} (h : Tick (galilFrameS P q first) delay x y)
    (hc : 1 ≤ x.ctl.clock) (hd : 1 ≤ delay) : 1 ≤ y.ctl.clock := by
  cases h <;> dsimp only at hc ⊢ <;> omega

/-! ## 2. A comparison while replaying matches -/

/-- The outer symbols agree whenever the centre is still live at the next
place.  (The contrapositive of `not_live_of_mismatch`, proved directly.) -/
theorem read_eq_of_live {raw : List (Fin 2)} {C k : ℕ} {l r : PlaceHead}
    (hi : ScanInvariant raw C k l r) (hav : canRight r)
    (hlive : Live raw (position r + 1) C) :
    read (left l) = read (right r) := by
  obtain ⟨_, hlt, hp⟩ := hlive
  have hpl := hi.leftPos
  have hpr := hi.rightPos
  have hkC : k + 1 < C := by omega
  have hb : k < C := by omega
  have hposl : 0 < l.head.left.length := by
    rcases Nat.eq_zero_or_pos l.head.left.length with h0 | hpos
    · exfalso
      have : position l = 0 := by unfold position; rw [h0]; split <;> simp
      omega
    · exact hpos
  have hposr : 0 < r.head.left.length := by
    rcases Nat.eq_zero_or_pos r.head.left.length with h0 | hpos
    · exfalso
      have : position r = 0 := by unfold position; rw [h0]; split <;> simp
      omega
    · exact hpos
  obtain ⟨heq_left, heq_right⟩ := comparison_positions l r C k hposl hposr hav hb hpl hpr
  have hposr1 : position r + 1 - C = k + 1 := by omega
  rw [hposr1] at hp
  have hleftWordRep : GalilScaffoldInputTrace.Represents (left l).head raw :=
    left_word l raw hi.leftRep hi.leftPresent
  have hrightWordRep : GalilScaffoldInputTrace.Represents (right r).head raw :=
    right_word r raw hi.rightRep hav
  have hleftFocus : (left l).head.focus ≠ none :=
    present_of_position (left l) hleftWordRep (by omega)
  have hrightFocus : (right r).head.focus ≠ none :=
    present_of_position (right r) hrightWordRep (by omega)
  have e1 : read (left l) = (encoded raw)[position (left l)]? :=
    represented_read (left l) raw hleftWordRep hleftFocus
  have e2 : read (right r) = (encoded raw)[position (right r)]? :=
    represented_read (right r) raw hrightWordRep hrightFocus
  rw [e1, e2, heq_left, heq_right]
  exact hp.2.2 (k + 1) le_rfl

/-- Liveness descends: a centre live at `n + m` and not past `n` is live at `n`. -/
theorem live_descend {raw : List (Fin 2)} {n C : ℕ} (hC : C ≤ n) :
    ∀ m, Live raw (n + m) C → Live raw n C := by
  intro m
  induction m with
  | zero => intro h; simpa using h
  | succ m ih =>
    intro h
    have h' : Live raw ((n + m) + 1) C := by
      have e : n + (m + 1) = (n + m) + 1 := by omega
      rwa [e] at h
    exact ih (live_pred h' (by omega))

/-- **The replay branch matches.**  While replaying, `MInv` places the centre
as the leftmost live centre at `position s.right + m` with `m > 0`, so the
palindrome about the centre reaches past the current right place and the next
comparison agrees. -/
theorem replay_match_of_minv {raw : List (Fin 2)} {c : Control} {s : GalilVM} {r : ℕ}
    (hM : MInv raw c s) (hr : c.replaying = true) (hav : canRight s.right)
    (hi : ScanInvariant raw (position s.center) r s.left s.right) :
    read (left s.left) = read (right s.right) := by
  obtain ⟨m, hm, _, hL⟩ := hM.1 hr
  have hlive : Live raw (position s.right + m) (position s.center) := hL.1
  have hCr : position s.center ≤ position s.right := by have := hi.rightPos; omega
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hlive' : Live raw ((position s.right + 1) + m') (position s.center) := by
    have e : position s.right + (m' + 1) = (position s.right + 1) + m' := by omega
    rwa [e] at hlive
  exact read_eq_of_live hi hav (live_descend (by omega) m' hlive')

/-! ## 3. The enabling condition with the replay branch -/

section Fixed

variable (onLetter leftFirst : GalilVM → Prop) (centre : GalilVM → Fin 3)
  (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9) (delay : ℕ)

/-- The replay branch of a scan tick: replaying, a positive clock, a matching
comparison, a search effect for both events and a chain able to tick. -/
def ReplayEnabled (c : Control) (s : GalilVM) : Prop :=
  c.replaying = true ∧ 1 ≤ c.clock ∧
    read (left s.left) = read (right s.right) ∧
    (∀ a : Bool, ∃ v, searchEffect (sharedFun onLetter leftFirst centre place entry) a s v) ∧
    ChainReady s.chain

/-- `Enabled` widened by the replay branch. -/
def EnabledR (x : State GalilVM) : Prop :=
  Enabled onLetter leftFirst centre place entry x ∨
    (x.ctl.mode = .scan ∧ ReplayEnabled onLetter leftFirst centre place entry x.ctl x.vm)

theorem tick_exists_R (x : State GalilVM)
    (hx : EnabledR onLetter leftFirst centre place entry x) :
    ∃ y, Tick (galilFrameS (sharedFun onLetter leftFirst centre place entry) q first) delay x y := by
  classical
  rcases hx with h | h
  · exact tick_exists onLetter leftFirst centre place entry q first delay x h
  obtain ⟨c, s⟩ := x
  obtain ⟨hm, hr, hclk, hmatch, hsearch, hchain⟩ := h
  set P : Shared := sharedFun onLetter leftFirst centre place entry with hP
  have hchain' : ∀ (a : Bool) (v : SearchVM), ∃ z, chainAt a (decide (v.search.mode = .found))
      (v.dp.config.tapes 11) (P.centre s) (P.place s) s.center s.radius s.chain z :=
    fun a v => chainAt_exists a (decide (v.search.mode = .found)) (v.dp.config.tapes 11)
      _ _ _ _ s.chain hchain
  rcases Nat.lt_or_ge 1 c.clock with hlt | hle
  · obtain ⟨s', hb⟩ := backgroundS_exists P q first s (hsearch false) (hchain' false)
    exact ⟨_, Tick.scan_count (F := galilFrameS P q first) (delay := delay) c s s' hm
      (Or.inl hr) hlt hb⟩
  · have hc1 : c.clock = 1 := le_antisymm hle hclk
    obtain ⟨vq, hq⟩ := hsearch true
    obtain ⟨z, hz⟩ := hchain' true vq
    let vs : ScanVM := ⟨left s.left, right s.right, z⟩
    have hmt0 : (galilFrame P q first).matched (scanLens.set s vs) := hmatch
    have hcmp : (galilFrameS P q first).compare s
        (afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterCompare s vs vq)) :=
      ⟨vs, vq, true, rfl, rfl, ⟨fun _ => hmt0, fun _ => rfl⟩, hq, hz, rfl⟩
    have hmt1 : (galilFrameS P q first).matched
        (afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterCompare s vs vq)) := by
      show GalilScaffoldInputHead.read (afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterCompare s vs vq)).left
        = GalilScaffoldInputHead.read (afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterCompare s vs vq)).right
      rw [afterBirth_left, afterBirth_right]
      exact hmatch
    let s'' : GalilVM := replayDec c.replaying (afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterCompare s vs vq))
    let o : Bool := if P.onLetter s'' then decide (P.leftFirst s'') else c.output
    have ho : refresh (galilFrameS P q first) s'' c.output o := by
      refine ⟨fun hl => ?_, fun hl => ?_⟩
      · have hl' : P.onLetter s'' := hl
        show (if P.onLetter s'' then decide (P.leftFirst s'') else c.output) = true ↔ P.leftFirst s''
        rw [if_pos hl']
        exact decide_eq_true_iff
      · have hl' : ¬ P.onLetter s'' := hl
        show (if P.onLetter s'' then decide (P.leftFirst s'') else c.output) = c.output
        rw [if_neg hl']
    exact ⟨_, Tick.scan_match (F := galilFrameS P q first) (delay := delay) c s _ s'' o hm
      (Or.inl hr) hc1 hcmp hmt1 (matchedPlace_replayDec P q first c.replaying _) ho⟩

/-- Under `MInv` the replay branch is enabled as soon as the scan data are
there: the match is derived, not assumed. -/
theorem enabledR_of_minv {raw : List (Fin 2)} {c : Control} {s : GalilVM} {r : ℕ}
    (hM : MInv raw c s) (hm : c.mode = .scan) (hr : c.replaying = true) (hclk : 1 ≤ c.clock)
    (hav : canRight s.right) (hi : ScanInvariant raw (position s.center) r s.left s.right)
    (hsearch : ∀ a : Bool, ∃ v, searchEffect (sharedFun onLetter leftFirst centre place entry) a s v)
    (hchain : ChainReady s.chain) :
    EnabledR onLetter leftFirst centre place entry ⟨c, s⟩ :=
  Or.inr ⟨hm, hr, hclk, replay_match_of_minv hM hr hav hi, hsearch, hchain⟩

end Fixed

#print axioms clock_pos_invariant
#print axioms read_eq_of_live
#print axioms live_descend
#print axioms replay_match_of_minv
#print axioms tick_exists_R
#print axioms enabledR_of_minv

end PalPeg.GalilTickFun2
