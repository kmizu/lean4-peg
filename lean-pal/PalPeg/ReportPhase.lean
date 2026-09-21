import PalPeg.GalilFrontier
import PalPeg.GalilStructuredSkeleton
import PalPeg.GalilFinalAssembly2

/-!
# The report phase is kept by the ticks of a scan

A refreshed report point in `scan` (`GalilStructuredSkeleton.ReportPoint`, `Refreshed`) reads the
three heads and the `replaying` and `output` bits of the control, nothing else.  A tick out of a
scan state that is not replaying either keeps all of these (`scan_wait`, `scan_count`, `restart`),
or moves the right head one place to the right (`scan_match`, `scan_shift`, `scan_fallback`):
`scanTick_kept_or_moved`.  At the last letter the second case leaves the word
(`position_right_of_atLast`).  Hence `reportPhase_tick`: the phase after the last report point is
kept by every tick, with no reference to a trace.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldInputHead

/-- A tick out of a scan state that is not replaying either keeps the three heads and
the reporting part of the control, or moves the right head one place to the right. -/
theorem scanTick_kept_or_moved (onLetter leftFirst : GalilVM → Prop) (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9) (delay : ℕ)
    {c c' : Control} {s t : GalilVM} (hscan : c.mode = Mode.scan)
    (hnotReplaying : c.replaying = false)
    (h : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay
      ⟨c, s⟩ ⟨c', t⟩) :
    (t.left = s.left ∧ t.center = s.center ∧ t.right = s.right ∧ c'.replaying = false ∧
        c'.output = c.output ∧ c'.mode = Mode.scan) ∨
      t.right = GalilScaffoldChainVerifier.right s.right := by
  cases h <;> first
    | (exfalso; simp_all; done)
    | skip
  case scan_wait =>
    rename_i hm hav hb
    obtain ⟨hl, hr, -, hcen, -⟩ :=
      backgroundS_fields (sharedC onLetter leftFirst centre place entry) q first hb
    exact Or.inl ⟨hl, hcen, hr, hnotReplaying, rfl, hscan⟩
  case scan_count =>
    rename_i hm hc hav hb
    obtain ⟨hl, hr, -, hcen, -⟩ :=
      backgroundS_fields (sharedC onLetter leftFirst centre place entry) q first hb
    exact Or.inl ⟨hl, hcen, hr, hnotReplaying, rfl, hscan⟩
  case scan_match =>
    rename_i s' o hmt hm hc hcmp hav hpl ho
    obtain ⟨vs, vq, a, -, hvr, -, -, -, hteq⟩ :
      compareFound (sharedC onLetter leftFirst centre place entry) q first s s' := hcmp
    have hs'r : s'.right = GalilScaffoldChainVerifier.right s.right := by
      rw [hteq, GalilScaffoldChainInputSupply.afterBirth_right]; cases a <;> exact hvr
    have hpl' : t = (if c.replaying then
        {s' with replay := GalilScaffoldCounter.dec s'.replay} else s') := hpl
    rw [hnotReplaying, if_neg (by simp)] at hpl'
    exact Or.inr (by rw [hpl', hs'r])
  case scan_shift =>
    rename_i s' hmt hg hm hc hr hcmp hav hb
    obtain ⟨vs, vq, a, -, hvr, -, -, -, hteq⟩ :
      compareFound (sharedC onLetter leftFirst centre place entry) q first s s' := hcmp
    have hs'r : s'.right = GalilScaffoldChainVerifier.right s.right := by
      rw [hteq, GalilScaffoldChainInputSupply.afterBirth_right]; cases a <;> exact hvr
    obtain ⟨w, -, ht⟩ : beginShiftVM' s' t := hb
    exact Or.inr (by rw [ht]; show s'.right = _; exact hs'r)
  case scan_fallback =>
    rename_i s' hmt hm hc hg hr hcmp hav hb
    obtain ⟨vs, vq, a, -, hvr, -, -, -, hteq⟩ :
      compareFound (sharedC onLetter leftFirst centre place entry) q first s s' := hcmp
    have hs'r : s'.right = GalilScaffoldChainVerifier.right s.right := by
      rw [hteq, GalilScaffoldChainInputSupply.afterBirth_right]; cases a <;> exact hvr
    obtain ⟨pl, ht, -⟩ : beginFallbackVM' s' t := hb
    exact Or.inr (by rw [ht]; show s'.right = _; exact hs'r)
  case restart =>
    rename_i hm hb
    obtain ⟨w, -, -, -, -, ht⟩ : restartVM entry s t := hb
    exact Or.inl ⟨by rw [ht], by rw [ht], by rw [ht], hnotReplaying, rfl, hscan⟩

/-- One place to the right of the last letter is the place after the word. -/
theorem position_right_of_atLast {p : PlaceHead} {n : ℕ} (hn : 0 < n)
    (h : position p = 2 * n - 1) :
    position (GalilScaffoldChainVerifier.right p) = 2 * n := by
  rcases p with ⟨⟨f, ls, rs, qs⟩, g⟩
  cases g with
  | true => simp only [position, if_true] at h; omega
  | false =>
    simp only [position, Bool.false_eq_true, if_false] at h
    simp only [position, GalilScaffoldChainVerifier.right, Bool.false_eq_true, if_false,
      Bool.not_false, if_true]
    omega

end PalPeg.GalilScaffoldChainInputSupply

namespace PalPeg.ReportPhase
open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
open PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilRunSkeleton
open PalPeg.GalilStructuredSkeleton GalilScaffoldInputHead

/-- **The report phase is kept.**  Out of a refreshed report point in scan, a tick lands on a refreshed report point
in scan again, or its right head has left the word. -/
theorem reportPhase_tick (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9) (delay : ℕ)
    {w : List (Fin 2)} {c c' : Control} {s t : GalilVM}
    (hpoint : ReportPoint w ⟨c, s⟩)
    (hrefreshed : Refreshed (PofC centre place entry w) q first ⟨c, s⟩)
    (hscan : c.mode = Mode.scan)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) delay ⟨c, s⟩ ⟨c', t⟩) :
    (ReportPoint w ⟨c', t⟩ ∧ Refreshed (PofC centre place entry w) q first ⟨c', t⟩ ∧
        c'.mode = Mode.scan) ∨
      2 * w.length ≤ position t.right := by
  rcases scanTick_kept_or_moved (onLetterVM w) leftFirstVM centre place entry q first delay hscan
      hpoint.notReplaying h with
    ⟨hleft, hcenter, hright, hreplaying, houtput, hmode⟩ | hmoved
  · left
    refine ⟨⟨hreplaying, ?_, ?_, ?_, hpoint.nonempty⟩, ?_, hmode⟩
    · obtain ⟨r, hinv⟩ := hpoint.scanInv
      exact ⟨r, by
        show ScanInvariant w (position t.center) r t.left t.right
        rw [hcenter, hleft, hright]; exact hinv⟩
    · have hcentre := hpoint.centre
      refine ⟨fun htrue => absurd (hreplaying.symm.trans htrue) (by decide), fun _ => ?_⟩
      show Leftmost w (position t.right) (position t.center)
      rw [hright, hcenter]
      exact hcentre.2 hpoint.notReplaying
    · show position t.right = _
      rw [hright]; exact hpoint.atLast
    · obtain ⟨old, hon, hoff⟩ := hrefreshed
      have honLetter : onLetterVM w t ↔ onLetterVM w s := by
        unfold onLetterVM; rw [hright]
      have hleftFirst : leftFirstVM t ↔ leftFirstVM s := by
        unfold leftFirstVM; rw [hleft]
      refine ⟨old, fun hletter => ?_, fun hnotLetter => ?_⟩
      · show c'.output = true ↔ leftFirstVM t
        rw [houtput, hleftFirst]
        exact hon (honLetter.mp hletter)
      · show c'.output = old
        rw [houtput]
        exact hoff (fun hletter => hnotLetter (honLetter.mpr hletter))
  · right
    rw [hmoved, position_right_of_atLast hpoint.nonempty hpoint.atLast]

#print axioms reportPhase_tick

end PalPeg.ReportPhase

