import PalPeg.GalilLiveCentreCycle2
import PalPeg.GalilScaffoldTopLifeRestart

/-!
# The found cycle that breaks before any shift

`cycle_found_stepsAll` / `cycle_found_minv`
(`PalPeg.GalilScaffoldTopOutputCycle`, `PalPeg.GalilLiveCentreCycle2`) take
the found cycle whose watch phase ends at a *mismatching* comparison, which
starts the first shift and the re-shift rounds.  The watch phase can also end
in the other way (`WatchStop.broke`, `PalPeg.GalilSegmentConstruct2`): the
first terminal is a **matched** comparison whose chain effect breaks the
chain, and the restart tick fires before any shift ever happens.

This module proves the `StepsAll`, `MInv` and `Restarted` facts for that
cycle.  The shape is the one of the found cycle with the shift, the rounds
and the final scan segment all removed: the idle segment, the found tick, the
preparation segment, the watch segment, the breaking matched comparison and
the restart tick.  Since the centre never moves, no period minimality is
needed: `MInv` travels by `minv_watchSegE` / `minv_watchSeg` / `minv_match`
alone, and the restart tick keeps the right head, the centre and the replay
counter (`minv_same`).
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open Manacher GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-- One main-loop cycle through a found comparison whose watch phase ends at
a breaking *match*: from a restarted state, an idle segment, the found tick,
the preparation, the watch, the breaking comparison and the restart tick.
Every state in scan mode and not replaying has a sound output. -/
theorem cycle_found_noshift_stepsAll (raw : List (Fin 2)) (P : Shared)
    (hP : P.onLetter = onLetterVM raw) (hP' : P.leftFirst = leftFirstVM)
    (qq : ℕ) (first : Fin 9) (delay : ℕ)
    -- the restarted state and the idle segment
    {Rad : ℕ} {last : Counter} {r : GalilVM} (hR : Restarted raw r Rad last)
    {c0 : Control} (hout0 : OutputRel raw c0 r)
    {es0 : List Bool} {cF : Control} {sF : GalilVM} (hseg0 : WatchSegE P qq first delay es0 c0 r cF sF)
    -- the found tick
    (hmF : cF.mode = .scan) (hrF : cF.replaying = false)
    (hcF : cF.clock = 1) (havF : canRight sF.right) (hidle : sF.chain = .idle)
    (vq : SearchVM) (hq : searchEffect P true sF vq) (hfound : vq.search.mode = .found)
    (hmt : read (left sF.left) = read (right sF.right))
    (ch : ChainVM)
    (hch : ChainMatched (chainStart (vq.dp.config.tapes 11) (P.centre sF) (P.place sF) sF.center sF.radius) ch)
    (hchne : ch ≠ .idle) (oF : Bool)
    (hoF : refresh (galilFrame P qq first)
      (afterBirth true (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq)) cF.output oF)
    -- the preparation and the watch
    {es : List Bool} {c2 : Control} {s2 : GalilVM}
    (hprepSeg : WatchSegE P qq first delay es {cF with clock := delay, output := oF, replaying := false}
      (afterBirth true (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq)) c2 s2)
    {c3 : Control} {s3 : GalilVM} (hseg : WatchSeg P qq first delay c2 s2 c3 s3)
    -- the terminal comparison: a match at which the chain breaks
    (hm3 : c3.mode = .scan) (hr3 : c3.replaying = false) (hc3 : c3.clock = 1)
    (w3 : GalilScaffoldChainWatch.State) (hs3 : s3.chain = .watch w3)
    (hz3 : GalilScaffoldCounter.zero w3.lag = true) (hav3 : canRight s3.right)
    (vs3 : ScanVM) (vq3 : SearchVM)
    (hcmp3 : (galilFrame P qq first).compare s3 (scanLens.set s3 vs3))
    (hmt3 : (galilFrame P qq first).matched (scanLens.set s3 vs3))
    (hq3 : searchEffect P true s3 vq3)
    (o3 : Bool) (ho3 : refresh (galilFrame P qq first) (afterCompare s3 vs3 vq3) c3.output o3)
    -- the restart tick
    (w3' : GalilScaffoldChainWatch.State) (hbroken : (afterCompare s3 vs3 vq3).chain = .broken w3')
    (hmargin : negative w3'.margin = false) (hlast : positive w3'.machine.control.last = true)
    (hlag : zero w3'.lag = true) (entry : ℕ) (hres : ∀ s t, restartVM entry s t → P.restart s t) :
    ∃ k, StepsAll (galilFrameS P qq first) delay (SoundScanNR raw) k ⟨c0, r⟩
      ⟨{c3 with clock := delay, output := o3, replaying := false}, {(afterCompare s3 vs3 vq3) with chain := .idle, lower := w3'.machine.control.last, search := GalilScaffoldSearchFinish.begin w3'.machine.control.last (afterCompare s3 vs3 vq3).radius, dp := GalilScaffoldControl.reset entry (afterCompare s3 vs3 vq3).dp}⟩ := by
  obtain ⟨_, _, _, hscanR, _⟩ := hR
  -- the idle segment
  obtain ⟨k1, h1⟩ := watchSegE_stepsAll raw P hP hP' qq first delay hseg0 (position r.center) Rad hscanR hout0
  have hinvF : ScanInvariant raw (position r.center) (Rad + es0.count true) sF.left sF.right :=
    scan_events_invariant ((watchSegE_heads P qq first delay hseg0).1 raw (position r.center) Rad) hscanR
  have houtF : OutputRel raw cF sF := stepsAll_last h1
  -- the found tick
  have htickF := found_start_match P qq first delay cF sF hmF hrF hcF havF hidle vq hq hfound hmt ch hch oF hoF
  have hoF' : refresh (galilFrame P qq first)
      (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq) cF.output oF :=
    (refresh_afterBirth_iff hP hP' true _ _ _).1 hoF
  obtain ⟨hinv1, hout1⟩ := outputRel_matched_refresh' raw P hP hP' qq first vq rfl rfl hmt havF hinvF
    cF.output oF hoF' {cF with clock := delay, output := oF, replaying := false} rfl
  -- the preparation segment
  obtain ⟨k2, hst1⟩ := watchSegE_stepsAll raw P hP hP' qq first delay hprepSeg (position r.center) _ hinv1 hout1
  have hinv2 : ScanInvariant raw (position r.center) (Rad + es0.count true + 1 + es.count true)
      s2.left s2.right :=
    scan_events_invariant ((watchSegE_heads P qq first delay hprepSeg).1 raw (position r.center) _) hinv1
  have hout2 : OutputRel raw c2 s2 := stepsAll_last hst1
  -- the watch segment
  obtain ⟨k3, hst2⟩ := watchSeg_stepsAll raw P hP hP' qq first delay hseg (position r.center) _ hinv2 hout2
  have hout3 : OutputRel raw c3 s3 := stepsAll_last hst2
  have hne2 : s2.chain ≠ .idle :=
    watchSegE_ne_idle P qq first delay hprepSeg (by rw [afterBirth_chain, afterCompare_chain]; exact hchne)
  obtain ⟨es2, _, hsc2, _, _, _, _, _⟩ := watchSeg_events P qq first delay hseg hne2
  have hi3 : ScanInvariant raw (position r.center)
      (Rad + es0.count true + 1 + es.count true + es2.count true) s3.left s3.right :=
    scan_events_invariant (hsc2 raw (position r.center) _) hinv2
  have hinv3 := matched_invariant raw P qq first vq3 hcmp3 hmt3 hav3 hi3
  -- the breaking comparison
  have hne3 : s3.chain ≠ .idle := by rw [hs3]; intro h0; cases h0
  have htick3 := scan_match_S P qq first delay c3 s3 vs3 vq3 o3 hm3 hr3 hav3 hc3 hne3 hcmp3 hmt3 hq3 ho3
  have hQ4 : SoundOut raw ⟨{c3 with clock := delay, output := o3, replaying := false},
      afterCompare s3 vs3 vq3⟩ :=
    outputRel_of_refresh' raw P hP hP' qq first _ c3.output o3 hinv3 ho3 _ rfl
  -- the run up to the breaking comparison
  have hmain : StepsAll (galilFrameS P qq first) delay (SoundOut raw) _ ⟨c0, r⟩
      ⟨{c3 with clock := delay, output := o3, replaying := false}, afterCompare s3 vs3 vq3⟩ :=
    stepsAll_trans h1 (.succ houtF htickF (stepsAll_trans hst1
      (stepsAll_trans hst2 (.succ hout3 htick3 (.zero _ hQ4)))))
  -- the restart tick
  have htick : Tick (galilFrameS P qq first) delay
      ⟨{c3 with clock := delay, output := o3, replaying := false}, afterCompare s3 vs3 vq3⟩
      ⟨{c3 with clock := delay, output := o3, replaying := false}, {(afterCompare s3 vs3 vq3) with chain := .idle, lower := w3'.machine.control.last, search := GalilScaffoldSearchFinish.begin w3'.machine.control.last (afterCompare s3 vs3 vq3).radius, dp := GalilScaffoldControl.reset entry (afterCompare s3 vs3 vq3).dp}⟩ :=
    .restart _ _ _ hm3 (hres _ _ ⟨w3', hbroken, hmargin, hlast, hlag, rfl⟩)
  have lift1 : ∀ st, SoundOut raw st → SoundScanNR raw st := fun st h0 _ _ => h0
  exact ⟨_, stepsAll_keep_tick raw P qq first delay (stepsAll_mono lift1 hmain) htick rfl⟩

#print axioms cycle_found_noshift_stepsAll

/-- The centre invariant survives the no-shift found cycle.  The centre never
moves here, so no period minimality is needed. -/
theorem cycle_found_noshift_minv (raw : List (Fin 2)) (P : Shared)
    (hex : ∀ s, P.replayExhausted s = zero s.replay)
    (qq : ℕ) (first : Fin 9) (delay : ℕ)
    -- the restarted state and the idle segment
    {Rad : ℕ} {last : Counter} {r : GalilVM} (hR : Restarted raw r Rad last)
    {c0 : Control} (hM0 : MInv raw c0 r)
    {es0 : List Bool} {cF : Control} {sF : GalilVM} (hseg0 : WatchSegE P qq first delay es0 c0 r cF sF)
    -- the found tick
    (hmF : cF.mode = .scan) (hrF : cF.replaying = false)
    (hcF : cF.clock = 1) (havF : canRight sF.right) (hidle : sF.chain = .idle)
    (vq : SearchVM) (hq : searchEffect P true sF vq) (hfound : vq.search.mode = .found)
    (hmt : read (left sF.left) = read (right sF.right))
    (ch : ChainVM)
    (hch : ChainMatched (chainStart (vq.dp.config.tapes 11) (P.centre sF) (P.place sF) sF.center sF.radius) ch)
    (hchne : ch ≠ .idle) (oF : Bool)
    (hoF : refresh (galilFrame P qq first)
      (afterBirth true (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq)) cF.output oF)
    -- the preparation and the watch
    {es : List Bool} {c2 : Control} {s2 : GalilVM}
    (hprepSeg : WatchSegE P qq first delay es {cF with clock := delay, output := oF, replaying := false}
      (afterBirth true (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq)) c2 s2)
    {c3 : Control} {s3 : GalilVM} (hseg : WatchSeg P qq first delay c2 s2 c3 s3)
    -- the terminal comparison: a match at which the chain breaks
    (hm3 : c3.mode = .scan) (hr3 : c3.replaying = false) (hc3 : c3.clock = 1)
    (w3 : GalilScaffoldChainWatch.State) (hs3 : s3.chain = .watch w3)
    (hz3 : GalilScaffoldCounter.zero w3.lag = true) (hav3 : canRight s3.right)
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
  -- the idle segment
  have hMF : MInv raw cF sF := minv_watchSegE raw P hex qq first delay hseg0 Rad hscanR hM0
  have hcen : sF.center = r.center := watchSegE_center P qq first delay hseg0
  have hinvF : ScanInvariant raw (position sF.center) (Rad + es0.count true) sF.left sF.right := by
    rw [hcen]
    exact scan_events_invariant ((watchSegE_heads P qq first delay hseg0).1 raw (position r.center) Rad)
      hscanR
  -- the found comparison
  have hM1 : MInv raw {cF with clock := delay, output := oF, replaying := false}
      (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq) :=
    minv_match oF delay hrF rfl rfl havF hmt hinvF hMF
  have hinv1 : ScanInvariant raw (position sF.center) (Rad + es0.count true + 1)
      (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq).left
      (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq).right :=
    matched_invariant' raw vq rfl rfl hmt havF hinvF
  -- the preparation segment
  have hM2 := minv_watchSegE raw P hex qq first delay hprepSeg _ hinv1 hM1
  have hcen2 : s2.center = sF.center := by
    have h0 := watchSegE_center P qq first delay hprepSeg
    rw [afterBirth_center, afterCompare_center] at h0; exact h0
  have hinv2 : ScanInvariant raw (position sF.center) (Rad + es0.count true + 1 + es.count true)
      s2.left s2.right :=
    scan_events_invariant
      ((watchSegE_heads P qq first delay hprepSeg).1 raw (position sF.center) _) hinv1
  -- the watch segment
  have hne2 : s2.chain ≠ .idle :=
    watchSegE_ne_idle P qq first delay hprepSeg (by rw [afterBirth_chain, afterCompare_chain]; exact hchne)
  obtain ⟨es2, _, hsc2, hcen21, _, _, _, _⟩ := watchSeg_events P qq first delay hseg hne2
  have hM3 := minv_watchSeg raw P qq first delay hseg _ (by rw [hcen2]; exact hinv2) hM2
  have hi3 : ScanInvariant raw (position s3.center)
      (Rad + es0.count true + 1 + es.count true + es2.count true) s3.left s3.right := by
    rw [hcen21, hcen2]
    exact scan_events_invariant (hsc2 raw (position sF.center) _) hinv2
  -- the breaking comparison
  have hmatch3 : read (left s3.left) = read (right s3.right) := by
    obtain ⟨⟨hl0, hr0, _⟩, _⟩ := hcmp3
    rw [scanLens.get_set] at hl0 hr0
    have hp0 := matched_parts P qq first hmt3
    rw [hl0, hr0] at hp0; exact hp0
  obtain ⟨hl3, hrr3, _⟩ := compare_parts P qq first hcmp3 hmatch3
  have hM4 := minv_match (vq := vq3) o3 delay hr3 hl3 hrr3 hav3 hmatch3 hi3 hM3
  -- the restart tick keeps the right head, the centre and the replay counter
  exact minv_same rfl rfl rfl rfl hM4

#print axioms cycle_found_noshift_minv

/-- The no-shift found cycle lands in a `Restarted` state: the centre never
moved, so the represented centre travels unchanged from the previous restart,
and the radius grows by one per matched comparison. -/
theorem cycle_found_noshift_restarted (raw : List (Fin 2)) (P : Shared)
    (qq : ℕ) (first : Fin 9) (delay : ℕ)
    -- the restarted state and the idle segment
    {Rad : ℕ} {last : Counter} {r : GalilVM} (hR : Restarted raw r Rad last)
    {c0 : Control}
    {es0 : List Bool} {cF : Control} {sF : GalilVM} (hseg0 : WatchSegE P qq first delay es0 c0 r cF sF)
    -- the found tick
    (havF : canRight sF.right) (hmt : read (left sF.left) = read (right sF.right))
    (vq : SearchVM) (ch : ChainVM) (hchne : ch ≠ .idle) (oF : Bool)
    -- the preparation and the watch
    {es : List Bool} {c2 : Control} {s2 : GalilVM}
    (hprepSeg : WatchSegE P qq first delay es {cF with clock := delay, output := oF, replaying := false}
      (afterBirth true (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq)) c2 s2)
    {c3 : Control} {s3 : GalilVM} (hseg : WatchSeg P qq first delay c2 s2 c3 s3)
    -- the terminal comparison: a match at which the chain breaks
    (hav3 : canRight s3.right) (vs3 : ScanVM) (vq3 : SearchVM)
    (hcmp3 : (galilFrame P qq first).compare s3 (scanLens.set s3 vs3))
    (hmt3 : (galilFrame P qq first).matched (scanLens.set s3 vs3))
    -- the restart tick's new lower bound
    (w3' : GalilScaffoldChainWatch.State) (hcanon : Canonical w3'.machine.control.last)
    (hlast : positive w3'.machine.control.last = true) (entry : ℕ) :
    ∃ Rad' : ℕ, Restarted raw {(afterCompare s3 vs3 vq3) with chain := .idle, lower := w3'.machine.control.last, search := GalilScaffoldSearchFinish.begin w3'.machine.control.last (afterCompare s3 vs3 vq3).radius, dp := GalilScaffoldControl.reset entry (afterCompare s3 vs3 vq3).dp} Rad' w3'.machine.control.last := by
  obtain ⟨hidleR, hrep, hfoc, hscanR, ⟨hrc, hrv⟩, hlc, _, _, _, _⟩ := hR
  -- the idle segment
  obtain ⟨hsc0, _, hrad0, hrc0, hlc0⟩ := watchSegE_heads P qq first delay hseg0
  have hcen : sF.center = r.center := watchSegE_center P qq first delay hseg0
  have hinvF : ScanInvariant raw (position sF.center) (Rad + es0.count true) sF.left sF.right := by
    rw [hcen]
    exact scan_events_invariant (hsc0 raw (position r.center) Rad) hscanR
  have hRadF : RadiusRep sF.radius (Rad + es0.count true) := by
    refine ⟨hrc0 hrc, ?_⟩
    rw [hrad0, hrv]; push_cast; ring
  -- the found comparison
  have hinv1 : ScanInvariant raw (position sF.center) (Rad + es0.count true + 1)
      (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq).left
      (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq).right :=
    matched_invariant' raw vq rfl rfl hmt havF hinvF
  have hRad1 : RadiusRep (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq).radius
      (Rad + es0.count true + 1) := by
    rw [afterCompare_radius]; exact radius_rep_inc hRadF
  have hlc1 : Canonical (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq).length := by
    rw [afterCompare_length]; exact inc_canonical _ (inc_canonical _ (hlc0 hlc))
  -- the preparation segment
  obtain ⟨hsc1, _, hrad1, hrc1, hlc1'⟩ := watchSegE_heads P qq first delay hprepSeg
  have hcen2 : s2.center = sF.center := by
    have h0 := watchSegE_center P qq first delay hprepSeg
    rw [afterBirth_center, afterCompare_center] at h0; exact h0
  have hinv2 : ScanInvariant raw (position sF.center) (Rad + es0.count true + 1 + es.count true)
      s2.left s2.right :=
    scan_events_invariant (hsc1 raw (position sF.center) _) hinv1
  have hRad2 : RadiusRep s2.radius (Rad + es0.count true + 1 + es.count true) := by
    refine ⟨hrc1 hRad1.1, ?_⟩
    rw [afterBirth_radius] at hrad1
    rw [hrad1, hRad1.2]; push_cast; ring
  -- the watch segment
  have hne2 : s2.chain ≠ .idle :=
    watchSegE_ne_idle P qq first delay hprepSeg (by rw [afterBirth_chain, afterCompare_chain]; exact hchne)
  obtain ⟨es2, _, hsc2, hcen21, _, hrad2, hrc2, hlc2⟩ := watchSeg_events P qq first delay hseg hne2
  have hi3 : ScanInvariant raw (position s3.center)
      (Rad + es0.count true + 1 + es.count true + es2.count true) s3.left s3.right := by
    rw [hcen21, hcen2]
    exact scan_events_invariant (hsc2 raw (position sF.center) _) hinv2
  have hRad3 : RadiusRep s3.radius (Rad + es0.count true + 1 + es.count true + es2.count true) := by
    refine ⟨hrc2 hRad2.1, ?_⟩
    rw [hrad2, hRad2.2]; push_cast; ring
  -- the breaking comparison
  have hinv3 := matched_invariant raw P qq first vq3 hcmp3 hmt3 hav3 hi3
  have hcenE : (afterCompare s3 vs3 vq3).center = r.center := by
    rw [afterCompare_center, hcen21, hcen2, hcen]
  refine ⟨Rad + es0.count true + 1 + es.count true + es2.count true + 1,
    rfl, ?_, ?_, ?_, ?_, ?_, rfl, rfl, hcanon, ((positive_iff _ hcanon).1 hlast).le⟩
  · show GalilScaffoldInputTrace.Represents (afterCompare s3 vs3 vq3).center.head raw
    rw [hcenE]; exact hrep
  · show (afterCompare s3 vs3 vq3).center.head.focus ≠ none
    rw [hcenE]; exact hfoc
  · show ScanInvariant raw (position (afterCompare s3 vs3 vq3).center) _
      (afterCompare s3 vs3 vq3).left (afterCompare s3 vs3 vq3).right
    rw [afterCompare_center, hcen21, hcen2] at *
    exact hinv3
  · show RadiusRep (afterCompare s3 vs3 vq3).radius _
    rw [afterCompare_radius]; exact radius_rep_inc hRad3
  · show Canonical (afterCompare s3 vs3 vq3).length
    rw [afterCompare_length]
    exact inc_canonical _ (inc_canonical _ (hlc2 (hlc1' hlc1)))

#print axioms cycle_found_noshift_restarted

end PalPeg.GalilScaffoldChainInputSupply
