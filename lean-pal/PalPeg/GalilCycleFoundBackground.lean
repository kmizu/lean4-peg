import PalPeg.GalilLiveCentreCycle2
import PalPeg.GalilBackgroundNotFound

/-!
# The found cycle when the chain starts on a *background* tick

`cycle_found_stepsAll` (`PalPeg.GalilScaffoldTopOutputCycle`) and
`cycle_found_minv` (`PalPeg.GalilLiveCentreCycle2`) both assume that the
chain of the cycle is started by a *comparison* tick: the found tick with
`hidle`, `hq : searchEffect P true sF vq`, `hfound` and
`hch : ChainMatched (chainStart …) ch`.

`GalilBackgroundNotFound.background_found_starts_chain` shows that the
search can just as well report `found` on a *background* tick, and
`chainAt_background_found` shows that `backgroundS` then installs
`chainStart …` plainly (no `ChainMatched`). This module proves the
variants of the two cycle lemmas for that case.

The reduction is the "simpler" one: a background tick is an ordinary
`WatchSegE.count` step, so the idle segment, the background-found tick and
the segment that follows it (with the chain already started) concatenate
into a *single* `WatchSegE` (`watchSegE_trans`) running from the restarted
state to the first comparison of the chain's life. What the life lemmas
actually need at their preparation segment is only

* the output relation and the scan invariant at the state entering it, and
* for `MInv`, the centre invariant there, the segment's centre and the fact
  that the chain is active at the segment's end,

none of which mentions the found comparison. `life_from_prep_stepsAll` and
`life_from_prep_minv` below are exactly `life_stepsAll` / `life_minv` with
the found tick removed and those data taken as hypotheses at the entering
state; the background variants then instantiate them at the restarted
state itself with the merged segment.

Nothing here is assumed beyond the hypotheses of the originals: the pieces
that a background start cannot provide (the centre of the read origin, the
DP result certifying the chain) are the same named hypotheses as in
`life_minv`, now stated at the restarted state (`hoc`, `hCen`) instead of
at the found tick — legitimate because a `WatchSegE` keeps the centre
(`watchSegE_center`).
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open Manacher GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier GalilBackgroundNotFound

/-! ## The life of a chain, entered at its preparation segment -/

/-- `life_stepsAll` without its found tick: from any state entering the
preparation segment with a sound output and the scan invariant, every state
of the chain's life in scan mode has a sound output. -/
theorem life_from_prep_stepsAll (raw : List (Fin 2)) (P : Shared) (hP : P.onLetter = onLetterVM raw)
    (hP' : P.leftFirst = leftFirstVM) (qq : ℕ) (first : Fin 9) (delay : ℕ)
    -- the state entering the preparation segment
    {cP : Control} {sP : GalilVM} {cen R : ℕ}
    (hinvP : ScanInvariant raw cen R sP.left sP.right) (houtP : OutputRel raw cP sP)
    -- the preparation and the watch
    {es : List Bool} {c2 : Control} {s2 : GalilVM}
    (hprepSeg : WatchSegE P qq first delay es cP sP c2 s2)
    {c1 : Control} {s1 : GalilVM} (hseg : WatchSeg P qq first delay c2 s2 c1 s1)
    -- the terminal comparison and the first shift
    (h : ℕ) (hm1 : c1.mode = .scan) (hr1 : c1.replaying = false) (hc1 : c1.clock = 1)
    (w : GalilScaffoldChainWatch.State) (hs1 : s1.chain = .watch w) (hz : zero w.lag = true)
    (hav : canRight s1.right) (vs : ScanVM) (vq' : SearchVM)
    (hcmp : (galilFrame P qq first).compare s1 (scanLens.set s1 vs))
    (hmis : ¬ (galilFrame P qq first).matched (scanLens.set s1 vs))
    (hq' : searchEffect P false s1 vq')
    (hg : P.shiftGuard (afterMismatch s1 vs vq'))
    (s2' : GalilVM) (hb : P.beginShift (afterMismatch s1 vs vq') s2')
    (hs2' : beginShiftVM h w (afterMismatch s1 vs vq') s2') (hi2 : CopyIdle s2')
    {t' : ShiftState} {v : GalilScaffoldChainWatch.State} {cycle : Counter}
    (hchain : ChainShiftRun ⟨s1.center, left s1.left, ofNat h, inc s1.radius, inc (inc s1.length)⟩
      (GalilScaffoldChainWatch.immediate w) reset h t' v cycle)
    (o : Bool)
    (ho : refresh (galilFrameS P qq first) (shiftLens.set s2' ⟨t', .watch v, cycle⟩) c1.output o)
    (org : ReadOrigin raw) (hint : org.interior.length+1 = h)
    (he : Entry raw org (toOnly (shiftLens.set s2' ⟨t', .watch v, cycle⟩) v))
    -- the re-shift rounds
    {m : ℕ} {c' : Control} {s' : GalilVM}
    (hrounds : Rounds P qq first delay h m {c1 with mode := .scan, clock := delay, output := o}
      (shiftLens.set s2' ⟨t', .watch v, cycle⟩) c' s')
    -- the final segment and the breaking comparison
    {n : ℕ} {c3 : Control} {s3 : GalilVM} (hseg3 : ScanSeg P qq first delay n c' s' c3 s3)
    (hm3 : c3.mode = .scan) (hr3 : c3.replaying = false) (hc3 : c3.clock = 1)
    (w3 : GalilScaffoldChainWatch.State) (hs3 : s3.chain = .watch w3) (hav3 : canRight s3.right)
    (vs3 : ScanVM) (vq3 : SearchVM)
    (hcmp3 : (galilFrame P qq first).compare s3 (scanLens.set s3 vs3))
    (hmt3 : (galilFrame P qq first).matched (scanLens.set s3 vs3))
    (hq3 : searchEffect P true s3 vq3)
    (o3 : Bool) (ho3 : refresh (galilFrame P qq first) (afterCompare s3 vs3 vq3) c3.output o3)
    {cen3 r3 : ℕ}
    (hinv3 : ScanInvariant raw cen3 r3 (afterCompare s3 vs3 vq3).left (afterCompare s3 vs3 vq3).right) :
    ∃ k, StepsAll (galilFrameS P qq first) delay (SoundScan raw) k ⟨cP, sP⟩
      ⟨{c3 with clock := delay, output := o3, replaying := false}, afterCompare s3 vs3 vq3⟩ := by
  -- the preparation
  obtain ⟨k1, hst1⟩ := watchSegE_stepsAll raw P hP hP' qq first delay hprepSeg cen R hinvP houtP
  have hinv2 := (watchSegE_output_inv raw P hP hP' qq first delay hprepSeg cen R hinvP houtP).2
  have hout2 : OutputRel raw c2 s2 := stepsAll_last hst1
  -- the watch
  obtain ⟨k2, hst2⟩ := watchSeg_stepsAll raw P hP hP' qq first delay hseg cen _ hinv2 hout2
  have hout3 : OutputRel raw c1 s1 := stepsAll_last hst2
  -- the first shift
  have hiEnd := entry_scanInvariant he
  have hst3 := first_shift_stepsAll raw P hP hP' qq first delay h hm1 hr1 hc1 w hs1 hav vs vq' hcmp hmis hq'
    hg s2' hb hs2' hi2 hchain o ho hz hout3 hiEnd
  -- the rounds
  have hp2 : (shiftLens.set s2' ⟨t', .watch v, cycle⟩).periodOnly = true := by
    show s2'.periodOnly = true; rw [hs2'.2]
  have hz2 : zero v.lag = true := by rw [chain_shift_lag hchain]; exact hz
  obtain ⟨k4, hst4⟩ := rounds_stepsAll raw P hP hP' qq first delay h hrounds v hp2 rfl hz2 org hint he
    (outputRel_of_refreshS' raw P hP hP' qq first _ _ o hiEnd ho _ rfl)
  -- the final segment
  obtain ⟨_, w', hw', hz', hp', hcr⟩ := rounds_lift P qq first delay h hrounds v hp2 rfl hz2
  obtain ⟨org', he', _, _, _, _, _, _, _⟩ := rounds_origin hcr org hint he
  have hinv' := entry_scanInvariant he'
  have hout' : OutputRel raw c' s' := stepsAll_last hst4 (scanSeg_mode P qq first delay hseg3 hm3)
  obtain ⟨k5, hst5⟩ := scanSeg_stepsAll raw P hP hP' qq first delay hseg3 _ _ hinv' hout'
  -- the breaking comparison
  have hne3 : s3.chain ≠ .idle := by rw [hs3]; intro h0; cases h0
  have htick3 := scan_match_S P qq first delay c3 s3 vs3 vq3 o3 hm3 hr3 hav3 hc3 hne3 hcmp3 hmt3 hq3 ho3
  have hQ3 : SoundScan raw ⟨c3, s3⟩ := fun _ => stepsAll_last hst5
  have hQ4 : SoundScan raw ⟨{c3 with clock := delay, output := o3, replaying := false}, afterCompare s3 vs3 vq3⟩ :=
    fun _ => outputRel_of_refresh' raw P hP hP' qq first _ c3.output o3 hinv3 ho3 _ rfl
  have lift : ∀ st, SoundOut raw st → SoundScan raw st := fun st h0 _ => h0
  exact ⟨_, stepsAll_trans (stepsAll_mono lift hst1)
    (stepsAll_trans (stepsAll_mono lift hst2) (stepsAll_trans hst3 (stepsAll_trans hst4
      (stepsAll_trans (stepsAll_mono lift hst5) (.succ hQ3 htick3 (.zero _ hQ4))))))⟩

/-- `life_minv` without its found tick: the centre invariant travels from any
state entering the preparation segment to the restart state at the end of
the chain's life. -/
theorem life_from_prep_minv (raw : List (Fin 2)) (P : Shared)
    (hex : ∀ s, P.replayExhausted s = zero s.replay)
    (qq : ℕ) (first : Fin 9) (delay : ℕ)
    (a : Fin 2) (ls rs q : List (Fin 2)) (gap : Bool)
    (hraw : raw = (a :: ls).reverse ++ rs ++ q)
    -- the state entering the preparation segment
    {cP : Control} {sP : GalilVM} {R : ℕ}
    (hinvP : ScanInvariant raw (position sP.center) R sP.left sP.right) (hMP : MInv raw cP sP)
    (hCen : sP.center = represent ⟨a :: ls,gap⟩ (rs.map some) q)
    -- the preparation and the watch
    {es : List Bool} {c2 : Control} {s2 : GalilVM}
    (hprepSeg : WatchSegE P qq first delay es cP sP c2 s2)
    (hne2 : s2.chain ≠ .idle)
    {c1 : Control} {s1 : GalilVM} (hseg : WatchSeg P qq first delay c2 s2 c1 s1)
    -- the terminal comparison and the first shift
    (h : ℕ) (hm1 : c1.mode = .scan) (hr1 : c1.replaying = false) (hc1 : c1.clock = 1)
    (w : GalilScaffoldChainWatch.State) (hs1 : s1.chain = .watch w) (hz : zero w.lag = true)
    (hav : canRight s1.right) (vs : ScanVM) (vq' : SearchVM)
    (hcmp : (galilFrame P qq first).compare s1 (scanLens.set s1 vs))
    (hmis : ¬ (galilFrame P qq first).matched (scanLens.set s1 vs))
    (hq' : searchEffect P false s1 vq')
    (hg : P.shiftGuard (afterMismatch s1 vs vq'))
    (s2' : GalilVM) (hb : P.beginShift (afterMismatch s1 vs vq') s2')
    (hs2' : beginShiftVM h w (afterMismatch s1 vs vq') s2') (hi2 : CopyIdle s2')
    {t' : ShiftState} {v : GalilScaffoldChainWatch.State} {cycle : Counter}
    (hchain : ChainShiftRun ⟨s1.center, left s1.left, ofNat h, inc s1.radius, inc (inc s1.length)⟩
      (GalilScaffoldChainWatch.immediate w) reset h t' v cycle)
    (o : Bool)
    (ho : refresh (galilFrameS P qq first) (shiftLens.set s2' ⟨t', .watch v, cycle⟩) c1.output o)
    (org : ReadOrigin raw) (hint : org.interior.length+1 = h)
    (he : Entry raw org (toOnly (shiftLens.set s2' ⟨t', .watch v, cycle⟩) v))
    -- the origin's centre, the DP result certifying the chain and the short periods
    (hoc : org.center = position sP.center)
    (vq : SearchVM) {lower span : ℕ}
    (hres : GalilDpCorrect.Result ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (span+1)) lower 0
      (GalilScaffoldProgram.denote vq.dp.config))
    (hpc : (GalilScaffoldProgram.denote vq.dp.config).pc = 346)
    (hout : (GalilScaffoldProgram.denote vq.dp.config).pos 11 = h)
    (hlow : ∀ δ, 0 < δ → δ ≤ lower → ¬ HasPeriod (Span raw org.center org.radius) (2*δ))
    -- the re-shift rounds
    {m : ℕ} {c' : Control} {s' : GalilVM}
    (hrounds : Rounds P qq first delay h m {c1 with mode := .scan, clock := delay, output := o}
      (shiftLens.set s2' ⟨t', .watch v, cycle⟩) c' s')
    -- the final segment and the breaking comparison
    {n : ℕ} {c3 : Control} {s3 : GalilVM} (hseg3 : ScanSeg P qq first delay n c' s' c3 s3)
    (hm3 : c3.mode = .scan) (hr3 : c3.replaying = false) (hc3 : c3.clock = 1)
    (w3 : GalilScaffoldChainWatch.State) (hs3 : s3.chain = .watch w3) (hav3 : canRight s3.right)
    (vs3 : ScanVM) (vq3 : SearchVM)
    (hcmp3 : (galilFrame P qq first).compare s3 (scanLens.set s3 vs3))
    (hmt3 : (galilFrame P qq first).matched (scanLens.set s3 vs3))
    (hq3 : searchEffect P true s3 vq3)
    (o3 : Bool) (ho3 : refresh (galilFrame P qq first) (afterCompare s3 vs3 vq3) c3.output o3)
    -- the restart tick
    (w3' : GalilScaffoldChainWatch.State) (hbroken : (afterCompare s3 vs3 vq3).chain = .broken w3')
    (entry : ℕ) :
    MInv raw {c3 with clock := delay, output := o3, replaying := false}
      {(afterCompare s3 vs3 vq3) with chain := .idle, lower := w3'.machine.control.last, search := GalilScaffoldSearchFinish.begin w3'.machine.control.last (afterCompare s3 vs3 vq3).radius, dp := GalilScaffoldControl.reset entry (afterCompare s3 vs3 vq3).dp} := by
  subst hraw
  -- the preparation segment
  have hM2 := minv_watchSegE _ P hex qq first delay hprepSeg R hinvP hMP
  have hcen2 : s2.center = sP.center := watchSegE_center P qq first delay hprepSeg
  have hinv2 : ScanInvariant ((a :: ls).reverse ++ rs ++ q) (position sP.center)
      (R+es.count true) s2.left s2.right :=
    scan_events_invariant ((watchSegE_heads P qq first delay hprepSeg).1 _ (position sP.center) R)
      hinvP
  -- the watch segment
  obtain ⟨es2, _, hsc2, hcen21, _⟩ := watchSeg_events P qq first delay hseg hne2
  have hM3 := minv_watchSeg _ P qq first delay hseg _ (by rw [hcen2]; exact hinv2) hM2
  have hi1 : ScanInvariant ((a :: ls).reverse ++ rs ++ q) (position sP.center)
      (R+es.count true+es2.count true) s1.left s1.right :=
    scan_events_invariant (hsc2 _ (position sP.center) (R+es.count true)) hinv2
  have hcen1 : s1.center = sP.center := by rw [hcen21, hcen2]
  -- the terminal mismatch
  have hcmpl : vs.left = left s1.left ∧ vs.right = right s1.right := by
    obtain ⟨⟨hl0, hr0, _⟩, _⟩ := hcmp
    rw [scanLens.get_set] at hl0 hr0
    exact ⟨hl0, hr0⟩
  have hmatch0 : read (left s1.left) ≠ read (right s1.right) := by
    intro h0
    apply hmis
    show read (scanLens.get (scanLens.set s1 vs)).left = read (scanLens.get (scanLens.set s1 vs)).right
    rw [scanLens.get_set]
    show read vs.left = read vs.right
    rw [hcmpl.1, hcmpl.2]; exact h0
  -- the places of the two heads
  have hrpos : position (right s1.right) = position s1.right + 1 :=
    right_position s1.right hav (represented_position s1.right.head _ hi1.rightRep hi1.rightPresent).1
  have hSright : s2'.right = right s1.right := by
    rw [hs2'.2]; simp [afterMismatch, searchLens, scanLens, hcmpl.2]
  have hposR : position s2'.right = position s1.right + 1 := by rw [hSright]; exact hrpos
  -- the origin's sizes and palindromes
  have hh : 0 < h := by omega
  have hk : 2*h ≤ org.radius := by have h0 := org.size; omega
  have hpal0 : PalAt (encoded ((a :: ls).reverse ++ rs ++ q)) org.center org.radius := org.scan.palindrome
  have hRA : org.radius ≤ org.center := hpal0.1
  have hlenX : org.center + org.radius < (encoded ((a :: ls).reverse ++ rs ++ q)).length := hpal0.2.1
  have hi' : ScanInvariant ((a :: ls).reverse ++ rs ++ q) (org.center + h) (org.radius+1-h)
      t'.left s2'.right := by
    have h0 := entry_scanInvariant he
    rw [hint] at h0
    exact h0
  have hcp' : position t'.center = org.center + h := by
    have h0 := he.centerPos; rw [hint] at h0; exact h0
  have hprA : position s1.right = org.center + org.radius := by
    have e1 := hi'.rightPos; omega
  -- no short period of the span at the first terminal comparison
  have hnb := noBelow_first_of_result a ls rs q gap org (by rw [hoc, hCen]) he hres hpc
    (by rw [hout]; exact hint.symm) hlow
  have hmin0 : ∀ p, 0 < p → p < 2*h →
      ¬ PeriodOn (encoded ((a :: ls).reverse ++ rs ++ q)) p
        (org.center - org.radius) (org.center + org.radius) := by
    intro p hp0 hp2 hcon
    apply hnb p hp0 (by omega)
    unfold Span
    have ea : 2*org.radius+1 = (org.center + org.radius) + 1 - (org.center - org.radius) := by omega
    rw [ea]
    exact (hasPeriod_slice_iff (x := encoded ((a :: ls).reverse ++ rs ++ q)) (p := p) hlenX
      (by omega)).mpr hcon
  -- the `2h` period of the whole span
  have hpal1 : PalAt (encoded ((a :: ls).reverse ++ rs ++ q)) (org.center + h) (org.radius + 1 - h) :=
    hi'.palindrome
  have hright : PeriodOn (encoded ((a :: ls).reverse ++ rs ++ q)) (2*h)
      (org.center+1) (org.center+org.radius+1) := by
    have h2 := org.origin_periodOn_right; rw [hint] at h2; exact h2
  have hper0 : PeriodOn (encoded ((a :: ls).reverse ++ rs ++ q)) (2*h)
      (org.center - org.radius) (org.center + org.radius) :=
    (periodOn_span_of_next hh hk hpal0 hpal1 hright).mono (le_refl _) (by omega)
  -- the first shift moves the leftmost live centre by `h`
  have hL1 : Leftmost ((a :: ls).reverse ++ rs ++ q) (position s1.right) (position sP.center) := by
    have h0 := minv_leftmost hM3 hr1
    rw [hcen1] at h0; exact h0
  have hdead : ¬ Live ((a :: ls).reverse ++ rs ++ q) (position s1.right + 1) (position sP.center) :=
    not_live_of_mismatch hi1 hav hmatch0
  have hlive : Live ((a :: ls).reverse ++ rs ++ q) (position s1.right + 1) (position sP.center + h) := by
    have h0 := live_of_scanInvariant hi'
    rw [hposR] at h0
    rw [← hoc]; exact h0
  have hmin : ∀ p, 0 < p → p < 2*h →
      ¬ HasPeriod (Span ((a :: ls).reverse ++ rs ++ q) (position sP.center)
        (position s1.right - position sP.center)) p := by
    intro p hp0 hp2 hcon
    apply hnb p hp0 (by omega)
    have e2 : position s1.right - position sP.center = org.radius := by omega
    rw [e2, ← hoc] at hcon
    exact hcon
  have hLS : Leftmost ((a :: ls).reverse ++ rs ++ q)
      (position (shiftLens.set s2' ⟨t', .watch v, cycle⟩).right)
      (position (shiftLens.set s2' ⟨t', .watch v, cycle⟩).center) := by
    show Leftmost _ (position s2'.right) (position t'.center)
    rw [hposR, hcp', hoc]
    exact leftmost_shift hL1 hdead hlive hmin
  have hMs : MInv _ {c1 with mode := .scan, clock := delay, output := o}
      (shiftLens.set s2' ⟨t', .watch v, cycle⟩) := minv_of_leftmost hLS hr1
  -- the re-shift rounds
  have hp2 : (shiftLens.set s2' ⟨t', .watch v, cycle⟩).periodOnly = true := by
    show s2'.periodOnly = true; rw [hs2'.2]
  have hz2 : zero v.lag = true := by rw [chain_shift_lag hchain]; exact hz
  obtain ⟨org', w', hint', _, _, _, _, _, he', _, _, hr', hM'⟩ :=
    rounds_leftmost _ P qq first delay h hrounds v hp2 rfl hz2 org hint he hper0 hmin0 hr1 hMs
  -- the final segment
  have hcp3 : position s'.center = org'.center + h := by
    have h0 := he'.centerPos; rw [hint'] at h0; exact h0
  have hinv' : ScanInvariant ((a :: ls).reverse ++ rs ++ q) (position s'.center)
      (org'.radius+1-h) s'.left s'.right := by
    have h0 := entry_scanInvariant he'
    rw [hint'] at h0
    rw [hcp3]; exact h0
  have hM3' := minv_scanSeg _ P qq first delay hseg3 _ hinv' hM'
  -- the breaking comparison
  have hmatch3 : read (left s3.left) = read (right s3.right) := by
    obtain ⟨⟨hl0, hr0, _⟩, _⟩ := hcmp3
    rw [scanLens.get_set] at hl0 hr0
    have hp0 := matched_parts P qq first hmt3
    rw [hl0, hr0] at hp0; exact hp0
  obtain ⟨hl3, hrr3, _⟩ := compare_parts P qq first hcmp3 hmatch3
  obtain ⟨es3, hsc3⟩ := scanSeg_heads P qq first delay hseg3
  have hi3 : ScanInvariant ((a :: ls).reverse ++ rs ++ q) (position s3.center)
      (org'.radius+1-h+es3.count true) s3.left s3.right := by
    have h0 := scan_events_invariant (hsc3 _ (position s'.center) (org'.radius+1-h)) hinv'
    rw [scanSeg_center P qq first delay hseg3]
    exact h0
  have hM4 := minv_match (vq := vq3) o3 delay hr3 hl3 hrr3 hav3 hmatch3 hi3 hM3'
  exact minv_same rfl rfl rfl rfl hM4

/-! ## The background-found tick -/

/-- The chain installed by a background tick whose search effect is `found`
on an idle chain: `chainStart` plainly. -/
theorem background_found_chain (P : Shared) (qq : ℕ) (first : Fin 9) {sB sB' : GalilVM}
    (hbg : (galilFrameS P qq first).background sB sB') (hidleB : sB.chain = .idle)
    (hfoundB : (searchLens.get sB').search.mode = .found) :
    sB'.chain = chainStart ((searchLens.get sB').dp.config.tapes 11) (P.centre sB) (P.place sB)
      sB.center sB.radius := by
  obtain ⟨_, _, hch, _⟩ := backgroundS_fields P qq first hbg
  rw [hidleB, decide_eq_true hfoundB] at hch
  exact (chainAt_background_found _ _ _ _ _ _).1 hch

/-- A started chain is not idle. -/
theorem chainStart_ne_idle (answer : GalilScaffoldTape.Tape) (c : Fin 3)
    (walker : GalilScaffoldPlace.Place) (ver : GalilScaffoldInputHead.PlaceHead)
    (radius : Counter) : chainStart answer c walker ver radius ≠ ChainVM.idle := by
  intro h0; cases h0

/-! ## The found cycle with a background start -/

/-- `cycle_found_stepsAll` when the chain of the cycle is started by a
background tick instead of a found comparison: from a restarted state, an
idle segment to a state `sB` whose *background* event reports `found`, the
background tick that installs `chainStart`, then the chain's life and the
restart tick. Every state in scan mode and not replaying has a sound
output. -/
theorem cycle_found_stepsAll_bg (raw : List (Fin 2)) (P : Shared) (hP : P.onLetter = onLetterVM raw)
    (hP' : P.leftFirst = leftFirstVM) (qq : ℕ) (first : Fin 9) (delay : ℕ)
    -- the restarted state and the idle segment
    {Rad : ℕ} {last : Counter} {r : GalilVM} (hR : Restarted raw r Rad last)
    {c0 : Control} (hout0 : OutputRel raw c0 r)
    {es0 : List Bool} {cB : Control} {sB : GalilVM} (hseg0 : WatchSegE P qq first delay es0 c0 r cB sB)
    -- the background-found tick
    (hmB : cB.mode = .scan) (hrB : cB.replaying = false) (havB : canRight sB.right)
    (hcB : 1 < cB.clock) (hidleB : sB.chain = .idle)
    {sB' : GalilVM} (hbg : (galilFrameS P qq first).background sB sB')
    (hfoundB : (searchLens.get sB').search.mode = .found)
    -- the preparation (with the chain already started) and the watch
    {es : List Bool} {c2 : Control} {s2 : GalilVM}
    (hprepSeg : WatchSegE P qq first delay es {cB with clock := cB.clock - 1} sB' c2 s2)
    {c1 : Control} {s1 : GalilVM} (hseg : WatchSeg P qq first delay c2 s2 c1 s1)
    -- the terminal comparison and the first shift
    (h : ℕ) (hm1 : c1.mode = .scan) (hr1 : c1.replaying = false) (hc1 : c1.clock = 1)
    (w : GalilScaffoldChainWatch.State) (hs1 : s1.chain = .watch w) (hz : zero w.lag = true)
    (hav : canRight s1.right) (vs : ScanVM) (vq' : SearchVM)
    (hcmp : (galilFrame P qq first).compare s1 (scanLens.set s1 vs))
    (hmis : ¬ (galilFrame P qq first).matched (scanLens.set s1 vs))
    (hq' : searchEffect P false s1 vq')
    (hg : P.shiftGuard (afterMismatch s1 vs vq'))
    (s2' : GalilVM) (hb : P.beginShift (afterMismatch s1 vs vq') s2')
    (hs2' : beginShiftVM h w (afterMismatch s1 vs vq') s2') (hi2 : CopyIdle s2')
    {t' : ShiftState} {v : GalilScaffoldChainWatch.State} {cycle : Counter}
    (hchain : ChainShiftRun ⟨s1.center, left s1.left, ofNat h, inc s1.radius, inc (inc s1.length)⟩
      (GalilScaffoldChainWatch.immediate w) reset h t' v cycle)
    (o : Bool)
    (ho : refresh (galilFrameS P qq first) (shiftLens.set s2' ⟨t', .watch v, cycle⟩) c1.output o)
    (org : ReadOrigin raw) (hint : org.interior.length+1 = h)
    (he : Entry raw org (toOnly (shiftLens.set s2' ⟨t', .watch v, cycle⟩) v))
    -- the re-shift rounds
    {m : ℕ} {c' : Control} {s' : GalilVM}
    (hrounds : Rounds P qq first delay h m {c1 with mode := .scan, clock := delay, output := o}
      (shiftLens.set s2' ⟨t', .watch v, cycle⟩) c' s')
    -- the final segment and the breaking comparison
    {n : ℕ} {c3 : Control} {s3 : GalilVM} (hseg3 : ScanSeg P qq first delay n c' s' c3 s3)
    (hm3 : c3.mode = .scan) (hr3 : c3.replaying = false) (hc3 : c3.clock = 1)
    (w3 : GalilScaffoldChainWatch.State) (hs3 : s3.chain = .watch w3) (hav3 : canRight s3.right)
    (vs3 : ScanVM) (vq3 : SearchVM)
    (hcmp3 : (galilFrame P qq first).compare s3 (scanLens.set s3 vs3))
    (hmt3 : (galilFrame P qq first).matched (scanLens.set s3 vs3))
    (hq3 : searchEffect P true s3 vq3)
    (o3 : Bool) (ho3 : refresh (galilFrame P qq first) (afterCompare s3 vs3 vq3) c3.output o3)
    {cen3 r3 : ℕ}
    (hinv3 : ScanInvariant raw cen3 r3 (afterCompare s3 vs3 vq3).left (afterCompare s3 vs3 vq3).right)
    -- the restart tick
    (w3' : GalilScaffoldChainWatch.State) (hbroken : (afterCompare s3 vs3 vq3).chain = .broken w3')
    (hmargin : negative w3'.margin = false) (hlast : positive w3'.machine.control.last = true)
    (hlag : zero w3'.lag = true) (entry : ℕ) (hres : ∀ s t, restartVM entry s t → P.restart s t) :
    ∃ k, StepsAll (galilFrameS P qq first) delay (SoundScanNR raw) k ⟨c0, r⟩
      ⟨{c3 with clock := delay, output := o3, replaying := false}, {(afterCompare s3 vs3 vq3) with chain := .idle, lower := w3'.machine.control.last, search := GalilScaffoldSearchFinish.begin w3'.machine.control.last (afterCompare s3 vs3 vq3).radius, dp := GalilScaffoldControl.reset entry (afterCompare s3 vs3 vq3).dp}⟩ := by
  obtain ⟨_, _, _, hscanR, _⟩ := hR
  -- the idle segment, the background-found tick and the preparation are one segment
  have hsegAll : WatchSegE P qq first delay (es0 ++ (false :: es)) c0 r c2 s2 :=
    watchSegE_trans P qq first delay hseg0 (.count cB sB sB' hmB hrB havB hcB hbg hprepSeg)
  obtain ⟨k2, h2⟩ := life_from_prep_stepsAll raw P hP hP' qq first delay hscanR hout0 hsegAll hseg
    h hm1 hr1 hc1 w hs1 hz hav vs vq' hcmp hmis hq' hg s2' hb hs2' hi2 hchain o ho org hint he
    hrounds hseg3 hm3 hr3 hc3 w3 hs3 hav3 vs3 vq3 hcmp3 hmt3 hq3 o3 ho3 hinv3
  have htick : Tick (galilFrameS P qq first) delay
      ⟨{c3 with clock := delay, output := o3, replaying := false}, afterCompare s3 vs3 vq3⟩
      ⟨{c3 with clock := delay, output := o3, replaying := false}, {(afterCompare s3 vs3 vq3) with chain := .idle, lower := w3'.machine.control.last, search := GalilScaffoldSearchFinish.begin w3'.machine.control.last (afterCompare s3 vs3 vq3).radius, dp := GalilScaffoldControl.reset entry (afterCompare s3 vs3 vq3).dp}⟩ :=
    .restart _ _ _ hm3 (hres _ _ ⟨w3', hbroken, hmargin, hlast, hlag, rfl⟩)
  have lift2 : ∀ st, SoundScan raw st → SoundScanNR raw st := fun st h0 hm _ => h0 hm
  exact ⟨_, stepsAll_keep_tick raw P qq first delay (stepsAll_mono lift2 h2) htick rfl⟩

/-- `cycle_found_minv` when the chain of the cycle is started by a background
tick: the centre invariant survives the cycle. -/
theorem cycle_found_minv_bg (raw : List (Fin 2)) (P : Shared)
    (hex : ∀ s, P.replayExhausted s = zero s.replay)
    (qq : ℕ) (first : Fin 9) (delay : ℕ)
    (a : Fin 2) (ls rs q : List (Fin 2)) (gap : Bool)
    (hraw : raw = (a :: ls).reverse ++ rs ++ q)
    -- the restarted state and the idle segment
    {Rad : ℕ} {last : Counter} {r : GalilVM} (hR : Restarted raw r Rad last)
    {c0 : Control} (hM0 : MInv raw c0 r) (hCen : r.center = represent ⟨a :: ls,gap⟩ (rs.map some) q)
    {es0 : List Bool} {cB : Control} {sB : GalilVM} (hseg0 : WatchSegE P qq first delay es0 c0 r cB sB)
    -- the background-found tick
    (hmB : cB.mode = .scan) (hrB : cB.replaying = false) (havB : canRight sB.right)
    (hcB : 1 < cB.clock) (hidleB : sB.chain = .idle)
    {sB' : GalilVM} (hbg : (galilFrameS P qq first).background sB sB')
    (hfoundB : (searchLens.get sB').search.mode = .found)
    -- the preparation (with the chain already started) and the watch
    {es : List Bool} {c2 : Control} {s2 : GalilVM}
    (hprepSeg : WatchSegE P qq first delay es {cB with clock := cB.clock - 1} sB' c2 s2)
    {c1 : Control} {s1 : GalilVM} (hseg : WatchSeg P qq first delay c2 s2 c1 s1)
    -- the terminal comparison and the first shift
    (h : ℕ) (hm1 : c1.mode = .scan) (hr1 : c1.replaying = false) (hc1 : c1.clock = 1)
    (w : GalilScaffoldChainWatch.State) (hs1 : s1.chain = .watch w) (hz : zero w.lag = true)
    (hav : canRight s1.right) (vs : ScanVM) (vq' : SearchVM)
    (hcmp : (galilFrame P qq first).compare s1 (scanLens.set s1 vs))
    (hmis : ¬ (galilFrame P qq first).matched (scanLens.set s1 vs))
    (hq' : searchEffect P false s1 vq')
    (hg : P.shiftGuard (afterMismatch s1 vs vq'))
    (s2' : GalilVM) (hb : P.beginShift (afterMismatch s1 vs vq') s2')
    (hs2' : beginShiftVM h w (afterMismatch s1 vs vq') s2') (hi2 : CopyIdle s2')
    {t' : ShiftState} {v : GalilScaffoldChainWatch.State} {cycle : Counter}
    (hchain : ChainShiftRun ⟨s1.center, left s1.left, ofNat h, inc s1.radius, inc (inc s1.length)⟩
      (GalilScaffoldChainWatch.immediate w) reset h t' v cycle)
    (o : Bool)
    (ho : refresh (galilFrameS P qq first) (shiftLens.set s2' ⟨t', .watch v, cycle⟩) c1.output o)
    (org : ReadOrigin raw) (hint : org.interior.length+1 = h)
    (he : Entry raw org (toOnly (shiftLens.set s2' ⟨t', .watch v, cycle⟩) v))
    -- the origin's centre, the DP result of the background-found tick and the short periods
    (hoc : org.center = position r.center)
    {lower span : ℕ}
    (hres : GalilDpCorrect.Result ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (span+1)) lower 0
      (GalilScaffoldProgram.denote (searchLens.get sB').dp.config))
    (hpc : (GalilScaffoldProgram.denote (searchLens.get sB').dp.config).pc = 346)
    (hout : (GalilScaffoldProgram.denote (searchLens.get sB').dp.config).pos 11 = h)
    (hlow : ∀ δ, 0 < δ → δ ≤ lower → ¬ HasPeriod (Span raw org.center org.radius) (2*δ))
    -- the re-shift rounds
    {m : ℕ} {c' : Control} {s' : GalilVM}
    (hrounds : Rounds P qq first delay h m {c1 with mode := .scan, clock := delay, output := o}
      (shiftLens.set s2' ⟨t', .watch v, cycle⟩) c' s')
    -- the final segment and the breaking comparison
    {n : ℕ} {c3 : Control} {s3 : GalilVM} (hseg3 : ScanSeg P qq first delay n c' s' c3 s3)
    (hm3 : c3.mode = .scan) (hr3 : c3.replaying = false) (hc3 : c3.clock = 1)
    (w3 : GalilScaffoldChainWatch.State) (hs3 : s3.chain = .watch w3) (hav3 : canRight s3.right)
    (vs3 : ScanVM) (vq3 : SearchVM)
    (hcmp3 : (galilFrame P qq first).compare s3 (scanLens.set s3 vs3))
    (hmt3 : (galilFrame P qq first).matched (scanLens.set s3 vs3))
    (hq3 : searchEffect P true s3 vq3)
    (o3 : Bool) (ho3 : refresh (galilFrame P qq first) (afterCompare s3 vs3 vq3) c3.output o3)
    -- the restart tick
    (w3' : GalilScaffoldChainWatch.State) (hbroken : (afterCompare s3 vs3 vq3).chain = .broken w3')
    (entry : ℕ) :
    MInv raw {c3 with clock := delay, output := o3, replaying := false}
      {(afterCompare s3 vs3 vq3) with chain := .idle, lower := w3'.machine.control.last, search := GalilScaffoldSearchFinish.begin w3'.machine.control.last (afterCompare s3 vs3 vq3).radius, dp := GalilScaffoldControl.reset entry (afterCompare s3 vs3 vq3).dp} := by
  have hscanR := hR.2.2.2.1
  -- the chain really starts at the background tick, so it is active at `s2`
  have hstart := background_found_chain P qq first hbg hidleB hfoundB
  have hneB : sB'.chain ≠ .idle := by
    rw [hstart]; exact chainStart_ne_idle _ _ _ _ _
  have hne2 : s2.chain ≠ .idle := watchSegE_ne_idle P qq first delay hprepSeg hneB
  -- the idle segment, the background-found tick and the preparation are one segment
  have hsegAll : WatchSegE P qq first delay (es0 ++ (false :: es)) c0 r c2 s2 :=
    watchSegE_trans P qq first delay hseg0 (.count cB sB sB' hmB hrB havB hcB hbg hprepSeg)
  exact life_from_prep_minv raw P hex qq first delay a ls rs q gap hraw hscanR hM0 hCen hsegAll hne2
    hseg h hm1 hr1 hc1 w hs1 hz hav vs vq' hcmp hmis hq' hg s2' hb hs2' hi2 hchain o ho org hint he
    hoc (searchLens.get sB') hres hpc hout hlow hrounds hseg3 hm3 hr3 hc3 w3 hs3 hav3 vs3 vq3 hcmp3
    hmt3 hq3 o3 ho3 w3' hbroken entry

end PalPeg.GalilScaffoldChainInputSupply

#print axioms PalPeg.GalilScaffoldChainInputSupply.life_from_prep_stepsAll
#print axioms PalPeg.GalilScaffoldChainInputSupply.life_from_prep_minv
#print axioms PalPeg.GalilScaffoldChainInputSupply.background_found_chain
#print axioms PalPeg.GalilScaffoldChainInputSupply.cycle_found_stepsAll_bg
#print axioms PalPeg.GalilScaffoldChainInputSupply.cycle_found_minv_bg
