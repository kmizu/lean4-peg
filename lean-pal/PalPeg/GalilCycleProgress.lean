import PalPeg.GalilRunSkeleton
import PalPeg.GalilChainReadyProgress
import PalPeg.GalilFallbackLanding

/-!
# The progress clause of the cycle oracle

`PalPeg.GalilRunSkeleton.CycleOracle`'s right disjunct demands
`position r.center < position sT.center`, and the two glue lemmas
`oracle_right_of_found` / `oracle_right_of_fallback` take that fact as a
hypothesis `hprog`.  This file discharges it for both cycles, so the glue
lemmas can be restated without `hprog`.

* `leftmost_progress` — the purely combinatorial core: if the old leftmost
  live centre dies at the next place and *any* centre is live there, the new
  one is strictly further right.
* `fallback_radius_lt` — the boundary case `2*R = position (right sF.right)`
  is impossible: the landing centre is live at the next place
  (`leftmost_after_fallback_landing`), and `Live`'s `n < 2*c` at
  `c = n - R` forces `2*R < n`.  (Concretely, `2*R = n` would put the landing
  centre at place `R` with radius `R`, i.e. its palindrome would reach the
  origin place `0`, and such a centre is never live.)
* `fallback_progress` — the fallback's landing centre, via
  `fallback_cycle_center_progress`.
* `fallbackCycle_step_progress` / `foundCycle_step_progress` — the two cycle
  steps of `PalPeg.GalilMainLoopMInv`, re-run with the progress conclusion
  added.  The found cycle's landing VM is a field update of
  `afterCompare s3 vs3 vq3`, so its centre is that of `afterCompare s3 vs3 vq3`,
  which `found_cycle_center_progress` places `(m+1)*h` to the right of
  `sF.center = r.center` (`watchSegE_center`).
* `oracle_right_of_found'` / `oracle_right_of_fallback'` — the glue lemmas of
  `GalilRunSkeleton` with `hprog` discharged.
-/

set_option autoImplicit false

namespace PalPeg.GalilCycleProgress

open PalPeg PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilChainReadyProgress
open PalPeg.GalilRunSkeleton (inv_of_residual)
open Manacher GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-! ## The combinatorial core -/

/-- If the leftmost live centre at `n` is dead at `n+1`, every centre that is
live at `n+1` lies strictly to its right. -/
theorem leftmost_progress {raw : List (Fin 2)} {n C c : ℕ} (hL : Leftmost raw n C)
    (hdead : ¬ Live raw (n+1) C) (hlive : Live raw (n+1) c) : C < c := by
  by_cases hcn : c ≤ n
  · have hle := hL.2 _ (live_pred hlive hcn)
    have hne : c ≠ C := fun e => hdead (e ▸ hlive)
    omega
  · have := hL.1.1
    omega

/-! ## (a) The fallback cycle -/

/-- **The boundary case is impossible.**  The fallback's chosen radius `R`
satisfies `2*R < position (right sF.right)` strictly, because the landing
centre `position (right sF.right) - R` is live at `position (right sF.right)`
and `Live` demands `n < 2*c`. -/
theorem fallback_radius_lt (raw : List (Fin 2)) {cF : Control} {sF t : GalilVM} {Rad : ℕ}
    (hM : MInv raw cF sF) (hnr : cF.replaying = false)
    (hinv : ScanInvariant raw (position sF.center) Rad sF.left sF.right)
    (hRR : RadiusRep sF.radius Rad) (hS : SpanRep sF) (hav : canRight sF.right)
    (hmis : read (left sF.left) ≠ read (right sF.right))
    (a : Fin 2) (xs rs' q' : List (Fin 2))
    (hdec : right sF.right = represent ⟨a :: xs,(right sF.right).gap⟩ (rs'.map some) q')
    (ℓ : ℕ) (hv : value sF.length = ℓ)
    (hpal : Manacher.PalAt (encoded raw)
      (position (right sF.right) - chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right sF.right).gap⟩).take (ℓ+1)))
      (chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right sF.right).gap⟩).take (ℓ+1))))
    (hmax : ∀ r', 2*r'+1 ≤ ((GalilScaffoldPlace.stream ⟨a :: xs,(right sF.right).gap⟩).take (ℓ+1)).length →
      Manacher.PalAt (encoded raw) (position (right sF.right) - r') r' →
      r' ≤ chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right sF.right).gap⟩).take (ℓ+1)))
    (hpos : position t.center = position (right sF.right) -
      chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right sF.right).gap⟩).take (ℓ+1))) :
    2 * chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right sF.right).gap⟩).take (ℓ+1))
      < position (right sF.right) := by
  have hLT := leftmost_after_fallback_landing raw hM hnr hinv hRR hS hav hmis a xs rs' q' hdec
    ℓ hv hpal hmax hpos
  obtain ⟨hle, hlt, -⟩ := hLT.1
  rw [hpos] at hle hlt
  omega

/-- **The fallback cycle's centre progress.**  Under the mismatching
comparison at `sF` (whose centre is the leftmost live one) the landing centre
of `fallback_landing` is strictly further right. -/
theorem fallback_progress (raw : List (Fin 2)) {cF : Control} {sF t : GalilVM} {Rad : ℕ}
    (hM : MInv raw cF sF) (hnr : cF.replaying = false)
    (hinv : ScanInvariant raw (position sF.center) Rad sF.left sF.right)
    (hRR : RadiusRep sF.radius Rad) (hS : SpanRep sF) (hav : canRight sF.right)
    (hmis : read (left sF.left) ≠ read (right sF.right))
    (a : Fin 2) (xs rs' q' : List (Fin 2))
    (hdec : right sF.right = represent ⟨a :: xs,(right sF.right).gap⟩ (rs'.map some) q')
    (ℓ : ℕ) (hv : value sF.length = ℓ)
    (hpal : Manacher.PalAt (encoded raw)
      (position (right sF.right) - chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right sF.right).gap⟩).take (ℓ+1)))
      (chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right sF.right).gap⟩).take (ℓ+1))))
    (hmax : ∀ r', 2*r'+1 ≤ ((GalilScaffoldPlace.stream ⟨a :: xs,(right sF.right).gap⟩).take (ℓ+1)).length →
      Manacher.PalAt (encoded raw) (position (right sF.right) - r') r' →
      r' ≤ chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right sF.right).gap⟩).take (ℓ+1)))
    (hpos : position t.center = position (right sF.right) -
      chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right sF.right).gap⟩).take (ℓ+1))) :
    position sF.center < position t.center := by
  have hrn := fallback_radius_lt raw hM hnr hinv hRR hS hav hmis a xs rs' q' hdec ℓ hv hpal hmax hpos
  have hL : Leftmost raw (position sF.right) (position sF.center) := minv_leftmost hM hnr
  have h := (fallback_cycle_center_progress hinv hav hmis hL hpos hpal hrn).2
  omega

/-! ## (b) The two cycle steps, with progress -/

/-- **`fallbackCycle_step` with progress.**  The body of
`PalPeg.GalilScaffoldChainInputSupply.fallbackCycle_step`, re-run with the
extra conclusion that the tracked centre has strictly advanced. -/
theorem fallbackCycle_step_progress (P : Shared) (qq : ℕ) (first : Fin 9) (delay : ℕ)
    (raw : List (Fin 2)) (c0 : Control) (r : GalilVM)
    (hC : FallbackCycle P qq first delay raw c0 r)
    (Rad : ℕ) (last : Counter) (hR : Restarted raw r Rad last) (hM0 : MInv raw c0 r) :
    ∃ (cT : Control) (sT : GalilVM),
      (∃ k, StepsAll (galilFrameS P qq first) delay (SoundScanNR raw) k ⟨c0, r⟩ ⟨cT, sT⟩) ∧
      MInv raw cT sT ∧ (∃ (Rad' : ℕ) (last' : Counter), Restarted raw sT Rad' last') ∧
      position r.center < position sT.center := by
  obtain ⟨onLetter, leftFirst, rsl, centre, place, entry, es0, cF, sF, vs, vq, ℓ,
    hPeq, hq0, h7, h8, honL, hlF, hi0, hS0, hout0, hseg0, hm, hr, hc, hav, hl, hrr, hmis, hq,
    hch, hg, hv, heven⟩ := hC
  subst hPeq
  have hscan0 := hR.2.2.2.1
  have hRR0 := hR.2.2.2.2.1
  have hMF : MInv raw cF sF :=
    minv_watchSegE raw _ (fun _ => rfl) qq first delay hseg0 Rad hscan0 hM0
  have hLF : Leftmost raw (position sF.right) (position sF.center) := minv_leftmost hMF hr
  obtain ⟨hrep, hfoc, hcan, _, hinvF⟩ := segment_mismatch_ready _ qq first delay hR hseg0 hav
  have hcen : sF.center = r.center := watchSegE_center _ qq first delay hseg0
  have hinvF' : ScanInvariant raw (position sF.center) (Rad + es0.count true) sF.left sF.right := by
    rw [hcen]; exact hinvF
  obtain ⟨_, _, hradv, hradc, _⟩ := watchSegE_heads _ qq first delay hseg0
  have hRRF : RadiusRep sF.radius (Rad + es0.count true) := by
    refine ⟨hradc hRR0.1, ?_⟩
    rw [hradv, hRR0.2]; push_cast; ring
  have hSF : SpanRep sF := spanRep_watchSegE _ qq first delay hseg0 hS0
  have hrpos : position (right sF.right) = position sF.right + 1 :=
    right_position sF.right hav (represented_position _ raw hinvF'.rightRep hinvF'.rightPresent).1
  have hdead : ¬ Live raw (position (right sF.right)) (position sF.center) := by
    rw [hrpos]; exact not_live_of_mismatch hinvF' hav hmis
  have hiF : ShiftIdle sF := by
    rw [shiftIdle_iff, watchSegE_remaining _ qq first delay hseg0]
    exact (shiftIdle_iff r).1 hi0
  obtain ⟨k1, h1⟩ :=
    watchSegE_stepsAll raw _ honL hlF qq first delay hseg0 (position r.center) Rad hscan0 hout0
  have houtF : OutputRel raw cF sF := stepsAll_last h1
  have lift1 : ∀ st, SoundOut raw st → SoundScanNR raw st := fun st h0 _ _ => h0
  obtain ⟨a, xs, rs', q', hdec, hraw, n, o, t, hstA, hRst, hrep', hpos, hpal, hmax, ho0⟩ :=
    fallback_restarted_All onLetter leftFirst rsl centre place entry qq hq0 first h7 h8 delay cF hm
      hr hc sF hiF hav vs vq hl hrr hmis hq hch hg hrep hfoc hcan ℓ hv heven
  have hprog : position sF.center < position t.center :=
    fallback_progress raw hMF hr hinvF' hRRF hSF hav hmis a xs rs' q' hdec ℓ hv hpal hmax hpos
  have hL' := leftmost_after_fallback raw hinvF' hRRF hSF hLF hav hdead a xs rs' q' hdec ℓ hv hpal hmax
  rw [hrpos] at hpos hL'
  refine ⟨_, t, ⟨_, stepsAll_trans (stepsAll_mono lift1 h1)
      (hstA (SoundScanNR raw) (fun st hns hsc => absurd hsc hns) (fun _ _ => houtF) ?_)⟩,
    minv_after_fallback hRst hrep' hpos (by rw [hpos]; exact hL') rfl, ⟨0, reset, hRst⟩,
    by rw [← hcen]; exact hprog⟩
  intro _ hrepl
  have hr0 : chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right sF.right).gap⟩).take (ℓ+1)) = 0 := by
    simp at hrepl; omega
  obtain ⟨_, _, _, hscanT, _⟩ := hRst
  intro hout' k hk hk2 hrk
  refine output_sound raw t cF.output o hscanT k hk hk2 hrk ?_ hout'
  have hoo := ho0 hr0
  rw [honL, hlF] at hoo
  exact hoo

/-- **`foundCycle_step` with progress.**  The body of
`PalPeg.GalilScaffoldChainInputSupply.foundCycle_step`, re-run with the extra
conclusion supplied by `found_cycle_center_progress`: the landing VM is a
field update of `afterCompare s3 vs3 vq3`, whose centre sits `(m+1)*h` to the
right of `sF.center`, and `sF.center = r.center`. -/
theorem foundCycle_step_progress (P : Shared) (qq : ℕ) (first : Fin 9) (delay : ℕ)
    (raw : List (Fin 2)) (c0 : Control) (r : GalilVM)
    (hC : FoundCycle P qq first delay raw c0 r)
    (Rad : ℕ) (last : Counter) (hR : Restarted raw r Rad last) (hM0 : MInv raw c0 r) :
    ∃ (cT : Control) (sT : GalilVM),
      (∃ k, StepsAll (galilFrameS P qq first) delay (SoundScanNR raw) k ⟨c0, r⟩ ⟨cT, sT⟩) ∧
      MInv raw cT sT ∧ (∃ (Rad' : ℕ) (last' : Counter), Restarted raw sT Rad' last') ∧
      position r.center < position sT.center := by
  obtain ⟨a, ls, rs, q, gap, es0, cF, sF, vq, ch, oF, es, c2, s2, cM, sM, h, w, vs, vq', s2',
    t', v, cycle, o, org, lower, span, m, c', s', n, c3, s3, w3, vs3, vq3, o3, cen3, r3, w3', entry,
    hP, hP', hex, hraw, hout0, hseg0, hmF, hrF, hcF, havF, hidle, hCen, hq, hfound, hmt, hch, hchne,
    hoF, hprepSeg, hseg, hm1, hr1, hc1, hs1, hz, hav, hcmp, hmis, hq', hg, hb, hs2', hi2, hchain,
    ho, hint, he, hoc, hdp, hpc, hposout, hlow, hrounds, hseg3, hm3, hr3, hc3, hs3, hav3, hcmp3,
    hmt3, hq3, ho3, hinv3, hbroken, hmargin, hlast, hlag, hrestart, Rad', hRnext⟩ := hC
  have hcen : sF.center = r.center := watchSegE_center P qq first delay hseg0
  have hprog := found_cycle_center_progress raw P qq first delay h w hz vs vq' s2' hs2' hchain
    org hint he hoc hrounds hseg3 vs3 vq3
  refine ⟨_, _, cycle_found_stepsAll raw P hP hP' qq first delay hR hout0 hseg0 hmF hrF hcF havF
    hidle vq hq hfound hmt ch hch hchne oF hoF hprepSeg hseg h hm1 hr1 hc1 w hs1 hz hav vs vq'
    hcmp hmis hq' hg s2' hb hs2' hi2 hchain o ho org hint he hrounds hseg3 hm3 hr3 hc3 w3 hs3 hav3
    vs3 vq3 hcmp3 hmt3 hq3 o3 ho3 hinv3 w3' hbroken hmargin hlast hlag entry hrestart,
    cycle_found_minv raw P hex qq first delay a ls rs q gap hraw hR hM0 hseg0 hmF hrF hcF havF
      hidle hCen vq hq hfound hmt ch hch hchne oF hoF hprepSeg hseg h hm1 hr1 hc1 w hs1 hz hav vs
      vq' hcmp hmis hq' hg s2' hb hs2' hi2 hchain o ho org hint he hoc hdp hpc hposout hlow hrounds
      hseg3 hm3 hr3 hc3 w3 hs3 hav3 vs3 vq3 hcmp3 hmt3 hq3 o3 ho3 w3' hbroken entry,
    ⟨Rad', _, hRnext⟩, ?_⟩
  show position r.center < position (afterCompare s3 vs3 vq3).center
  rw [hcen] at hprog
  omega

/-! ## The glue lemmas without `hprog` -/

/-- `oracle_right_of_found` with the progress hypothesis discharged. -/
theorem oracle_right_of_found' (P : Shared) (qq : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (c : Control) (r : GalilVM) (hC : FoundCycle P qq first 2048 raw c r) (hI : Inv raw c r)
    (hres : ∀ (cT : Control) (sT : GalilVM), MInv raw cT sT →
      (∃ (Rad' : ℕ) (last' : Counter), Restarted raw sT Rad' last') → FoundResidual raw cT sT) :
    ∃ (cT : Control) (sT : GalilVM) (k : ℕ),
      StepsAll (galilFrameS P qq first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩ ∧
      Inv raw cT sT ∧ position r.center < position sT.center := by
  obtain ⟨Rad, last, hR⟩ := hI.rest
  obtain ⟨cT, sT, ⟨k, hst⟩, hM, hRT, hlt⟩ :=
    foundCycle_step_progress P qq first 2048 raw c r hC Rad last hR hI.minv
  exact ⟨cT, sT, k, hst, inv_of_residual hM hRT (hres cT sT hM hRT), hlt⟩

/-- `oracle_right_of_fallback` with the progress hypothesis discharged. -/
theorem oracle_right_of_fallback' (P : Shared) (qq : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (c : Control) (r : GalilVM) (hC : FallbackCycle P qq first 2048 raw c r) (hI : Inv raw c r)
    (hres : ∀ (cT : Control) (sT : GalilVM), MInv raw cT sT →
      (∃ (Rad' : ℕ) (last' : Counter), Restarted raw sT Rad' last') → FoundResidual raw cT sT) :
    ∃ (cT : Control) (sT : GalilVM) (k : ℕ),
      StepsAll (galilFrameS P qq first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩ ∧
      Inv raw cT sT ∧ position r.center < position sT.center := by
  obtain ⟨Rad, last, hR⟩ := hI.rest
  obtain ⟨cT, sT, ⟨k, hst⟩, hM, hRT, hlt⟩ :=
    fallbackCycle_step_progress P qq first 2048 raw c r hC Rad last hR hI.minv
  exact ⟨cT, sT, k, hst, inv_of_residual hM hRT (hres cT sT hM hRT), hlt⟩

#print axioms leftmost_progress
#print axioms fallback_radius_lt
#print axioms fallback_progress
#print axioms fallbackCycle_step_progress
#print axioms foundCycle_step_progress
#print axioms oracle_right_of_found'
#print axioms oracle_right_of_fallback'

end PalPeg.GalilCycleProgress
