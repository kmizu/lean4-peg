import PalPeg.GalilScaffoldTopOutputCycle

/-!
# Progress of a scan tick on `galilFrameS`

`compare_progress` gives progress at a comparison for `galilFrame`, where a
comparison is only the scan/chain step. On `galilFrameS` the comparison also
carries one search quantum and the chain effect `chainAt` (which may start
the chain when the quantum lands in `found`), so the two existence facts of
the co-process — a search effect for the event and a chain effect for the
resulting answer tape — replace the plain `ChainTick` existence.

This module proves the `galilFrameS` analogues:

* `backgroundS_exists`: a background state exists from the search and chain
  existence facts (used by `scan_wait` and `scan_count`);
* `compare_progress_S`: at clock one, with R available and not replaying,
  the comparison has a tick (`scan_match`, `scan_shift` or `scan_fallback`);
* `scan_tick_exists`: every scan-mode state with a positive clock has a tick.

Both progress theorems assume `c.replaying = false`, exactly as
`compare_progress` does: `Tick.scan_shift` and `Tick.scan_fallback` both
carry `hr : c.replaying = false`, so a *mismatching* comparison while
replaying has no constructor other than `Tick.restart`, whose effect `rs` is
an unconstrained parameter here. (`scan_match` and `scan_count` themselves are
fine while replaying — see `scan_match_S'`.)
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-- A background state exists as soon as the search has an effect for the
event `false` and the chain has an effect for the answer tape that effect
leaves. Heads and counters are kept; the chain becomes the witness `z`. -/
theorem backgroundS_exists (P : Shared) (q : ℕ) (first : Fin 9) (s : GalilVM)
    (hsearch : ∃ v, searchEffect P false s v)
    (hchain : ∀ (v : SearchVM), ∃ z, chainAt false (decide (v.search.mode = .found)) (v.dp.config.tapes 11)
      (P.centre s) (P.place s) s.center s.radius s.chain z) :
    ∃ s', (galilFrameS P q first).background s s' := by
  obtain ⟨v, hv⟩ := hsearch
  obtain ⟨z, hz⟩ := hchain v
  refine ⟨afterBirth (chainBorn (decide (v.search.mode = .found)) s.chain)
    (searchLens.set (scanLens.set s ⟨s.left, s.right, z⟩) v), ?_⟩
  show backgroundS P q first s _
  have hv' : searchLens.get (afterBirth (chainBorn (decide (v.search.mode = .found)) s.chain)
      (searchLens.set (scanLens.set s ⟨s.left, s.right, z⟩) v)) = v := by
    rw [afterBirth_searchGet]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [afterBirth_left]; rfl
  · rw [afterBirth_right]; rfl
  · rw [hv']; exact hv
  · rw [hv', afterBirth_chain]; exact hz
  · have hs' : scanLens.get (afterBirth (chainBorn (decide (v.search.mode = .found)) s.chain)
        (searchLens.set (scanLens.set s ⟨s.left, s.right, z⟩) v)) = ⟨s.left, s.right, z⟩ := by
      rw [afterBirth_scanGet]; rfl
    rw [hv', hs']

/-- Progress at a comparison on `galilFrameS`: with R available, the clock
at one and the controller not replaying, the outer symbols either agree
(`scan_match`, the chain effect recorded by `chainAt true`) or differ, and
then the shift guard selects a shift (`scan_shift`) or a fallback
(`scan_fallback`). The concrete entries `beginShiftVM'`/`beginFallbackVM'`
supply the entry existence outright. -/
theorem compare_progress_S (onLetter leftFirst : GalilVM → Prop) (rs : GalilVM → GalilVM → Prop)
    (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place) (entry : ℕ)
    (q : ℕ) (first : Fin 9) (delay : ℕ) (c : Control) (s : GalilVM)
    (hm : c.mode = .scan) (hc : c.clock = 1) (hr : c.replaying = false) (hav : canRight s.right)
    (hsearch : ∀ a : Bool, ∃ v, searchEffect (galilShared onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' rs centre place entry) a s v)
    (hchain : ∀ (a : Bool) (v : SearchVM), ∃ z, chainAt a (decide (v.search.mode = .found)) (v.dp.config.tapes 11)
      (centre s) (place s) s.center s.radius s.chain z) :
    ∃ st', Tick (galilFrameS (galilShared onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' rs centre place entry) q first) delay ⟨c, s⟩ st' := by
  classical
  set P : Shared := galilShared onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' rs centre place entry with hP
  have hav' : (galilFrameS P q first).available s := hav
  by_cases hmt : read (left s.left) = read (right s.right)
  · -- the outer symbols agree: `scan_match`
    obtain ⟨vq, hq⟩ := hsearch true
    obtain ⟨z, hz⟩ := hchain true vq
    let vs : ScanVM := ⟨left s.left, right s.right, z⟩
    let u : GalilVM := afterBirth (chainBorn (decide (vq.search.mode = .found)) s.chain)
      (afterCompare s vs vq)
    have hmt0 : (galilFrame P q first).matched (scanLens.set s vs) := hmt
    have hcmp : (galilFrameS P q first).compare s u :=
      ⟨vs, vq, true, rfl, rfl, ⟨fun _ => hmt0, fun _ => rfl⟩, hq, hz, rfl⟩
    have hmt1 : (galilFrameS P q first).matched u := by
      show (galilFrame P q first).matched u
      have : GalilScaffoldInputHead.read (scanLens.get u).left =
        GalilScaffoldInputHead.read (scanLens.get u).right := by
        rw [show scanLens.get u = scanLens.get (afterCompare s vs vq) from afterBirth_scanGet _ _]
        exact hmt
      exact this
    let s'' : GalilVM := replayDec c.replaying u
    let o : Bool := if onLetter s'' then decide (leftFirst s'') else c.output
    have ho : refresh (galilFrameS P q first) s'' c.output o := by
      refine ⟨fun hl => ?_, fun hl => ?_⟩
      · have hl' : onLetter s'' := hl
        show (if onLetter s'' then decide (leftFirst s'') else c.output) = true ↔ leftFirst s''
        rw [if_pos hl']
        exact decide_eq_true_iff
      · have hl' : ¬ onLetter s'' := hl
        show (if onLetter s'' then decide (leftFirst s'') else c.output) = c.output
        rw [if_neg hl']
    exact ⟨_, Tick.scan_match (F := galilFrameS P q first) (delay := delay) c s _ s'' o hm
      (Or.inr hav') hc hcmp hmt1 (matchedPlace_replayDec P q first c.replaying _) ho⟩
  · -- the outer symbols differ: `scan_shift` or `scan_fallback`
    obtain ⟨vq, hq⟩ := hsearch false
    obtain ⟨z, hz⟩ := hchain false vq
    let vs : ScanVM := ⟨left s.left, right s.right, z⟩
    let u : GalilVM := afterBirth (chainBorn (decide (vq.search.mode = .found)) s.chain)
      (afterMismatch s vs vq)
    have hmt0 : ¬ (galilFrame P q first).matched (scanLens.set s vs) := hmt
    have hcmp : (galilFrameS P q first).compare s u :=
      ⟨vs, vq, false, rfl, rfl, Iff.intro (fun h0 => by cases h0) (fun h0 => absurd h0 hmt0), hq, hz, rfl⟩
    have hmt1 : ¬ (galilFrameS P q first).matched u := by
      intro h0
      have h1 : GalilScaffoldInputHead.read (scanLens.get u).left =
        GalilScaffoldInputHead.read (scanLens.get u).right := h0
      rw [show scanLens.get u = scanLens.get (afterMismatch s vs vq) from afterBirth_scanGet _ _] at h1
      exact hmt h1
    by_cases hg : shiftGuardVM u
    · obtain ⟨t, hb⟩ := beginShift_exists u hg
      exact ⟨_, Tick.scan_shift (F := galilFrameS P q first) (delay := delay) c s _ t hm
        (Or.inr hav') hc hcmp hmt1 hr hg hb⟩
    · obtain ⟨t, hb⟩ := beginFallback_exists u
      exact ⟨_, Tick.scan_fallback (F := galilFrameS P q first) (delay := delay) c s _ t hm
        (Or.inr hav') hc hcmp hmt1 (Or.inr hg) hr hb⟩

#print axioms backgroundS_exists
#print axioms compare_progress_S

/-- Every scan-mode state with a positive clock has a tick: R unavailable is
`scan_wait`, a clock above one is `scan_count`, and a clock of one is a
comparison (`compare_progress_S`). The hypotheses are the search and chain
existence facts of the co-process, and `c.replaying = false` (see the module
docstring). -/
theorem scan_tick_exists (onLetter leftFirst : GalilVM → Prop) (rs : GalilVM → GalilVM → Prop)
    (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place) (entry : ℕ)
    (q : ℕ) (first : Fin 9) (delay : ℕ) (c : Control) (s : GalilVM)
    (hm : c.mode = .scan) (hclk : 1 ≤ c.clock) (hr : c.replaying = false)
    (hsearch : ∀ a : Bool, ∃ v, searchEffect (galilShared onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' rs centre place entry) a s v)
    (hchain : ∀ (a : Bool) (v : SearchVM), ∃ z, chainAt a (decide (v.search.mode = .found)) (v.dp.config.tapes 11)
      (centre s) (place s) s.center s.radius s.chain z) :
    ∃ st', Tick (galilFrameS (galilShared onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' rs centre place entry) q first) delay ⟨c, s⟩ st' := by
  classical
  set P : Shared := galilShared onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' rs centre place entry with hP
  by_cases hav : canRight s.right
  · rcases Nat.lt_or_ge 1 c.clock with hlt | hle
    · obtain ⟨s', hb⟩ := backgroundS_exists P q first s (hsearch false) (hchain false)
      have hav' : (galilFrameS P q first).available s := hav
      exact ⟨_, Tick.scan_count (F := galilFrameS P q first) (delay := delay) c s s' hm
        (Or.inr hav') hlt hb⟩
    · have hc : c.clock = 1 := le_antisymm hle hclk
      exact compare_progress_S onLetter leftFirst rs centre place entry q first delay c s hm hc hr
        hav hsearch hchain
  · obtain ⟨s', hb⟩ := backgroundS_exists P q first s (hsearch false) (hchain false)
    have hav' : ¬ (galilFrameS P q first).available s := hav
    exact ⟨_, Tick.scan_wait (F := galilFrameS P q first) (delay := delay) c s s' hm ⟨hr, hav'⟩ hb⟩

#print axioms scan_tick_exists

end PalPeg.GalilScaffoldChainInputSupply
