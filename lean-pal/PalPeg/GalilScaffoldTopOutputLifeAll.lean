import PalPeg.GalilScaffoldTopOutputRound

/-!
# Output soundness at every state of a chain's life

From the found tick through the preparation, the watch, the first shift,
the re-shift rounds, the final segment and the breaking comparison: every
state in scan mode has a sound output. The refresh points are the found
comparison, the shift ends (under the read origins' invariants) and the
breaking comparison (under the exported invariant).
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

theorem scanSeg_mode (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) {n : ℕ} {c c' : Control}
    {s t : GalilVM} (h : ScanSeg P q first delay n c s c' t) (hm' : c'.mode = .scan) : c.mode = .scan := by
  cases h <;> assumption

theorem first_shift_stepsAll (raw : List (Fin 2)) (P : Shared) (hP : P.onLetter = onLetterVM raw)
    (hP' : P.leftFirst = leftFirstVM) (q : ℕ) (first : Fin 9) (delay : ℕ) (h : ℕ)
    {c1 : Control} {s1 : GalilVM}
    -- the terminal comparison
    (hm1 : c1.mode = .scan) (hr1 : c1.replaying = false) (hc1 : c1.clock = 1)
    (w : GalilScaffoldChainWatch.State) (hs1 : s1.chain = .watch w)
    (hav : canRight s1.right) (vs : ScanVM) (vq : SearchVM)
    (hcmp : (galilFrame P q first).compare s1 (scanLens.set s1 vs))
    (hmis : ¬ (galilFrame P q first).matched (scanLens.set s1 vs))
    (hq : searchEffect P false s1 vq)
    (hg : P.shiftGuard (afterMismatch s1 vs vq))
    -- the shift entry and run
    (s2 : GalilVM) (hb : P.beginShift (afterMismatch s1 vs vq) s2)
    (hs2 : beginShiftVM h w (afterMismatch s1 vs vq) s2) (hi2 : CopyIdle s2)
    {t' : ShiftState} {v : GalilScaffoldChainWatch.State} {cycle : Counter}
    (hchain : ChainShiftRun ⟨s1.center, left s1.left, ofNat h, inc s1.radius, inc (inc s1.length)⟩
      (GalilScaffoldChainWatch.immediate w) reset h t' v cycle)
    -- the exit output
    (o : Bool)
    (ho : refresh (galilFrameS P q first) (shiftLens.set s2 ⟨t', .watch v, cycle⟩) c1.output o)
    (hz : zero w.lag = true) (hout : OutputRel raw c1 s1)
    {cen' r' : ℕ} (hiEnd : ScanInvariant raw cen' r' (shiftLens.set s2 ⟨t', .watch v, cycle⟩).left
      (shiftLens.set s2 ⟨t', .watch v, cycle⟩).right) :
    StepsAll (galilFrameS P q first) delay (SoundScan raw) (1 + (h+1)) ⟨c1, s1⟩
        ⟨{c1 with mode := .scan, clock := delay, output := o}, shiftLens.set s2 ⟨t', .watch v, cycle⟩⟩ := by
  -- the terminal comparison
  have hcmp0 := hcmp
  obtain ⟨⟨hl, hr, ht⟩, _⟩ := hcmp0
  rw [scanLens.get_set] at hl hr ht
  have hmatch0 : ¬ read (left s1.left) = read (right s1.right) := by
    intro h0
    apply hmis
    show read (scanLens.get (scanLens.set s1 vs)).left = read (scanLens.get (scanLens.set s1 vs)).right
    rw [scanLens.get_set]
    have hl' : vs.left = left s1.left := hl
    have hr' : vs.right = right s1.right := hr
    show read vs.left = read vs.right
    rw [hl', hr']; exact h0
  have ht' : ChainTick (decide (read (left s1.left) = read (right s1.right))) s1.chain vs.chain := ht
  rw [decide_eq_false hmatch0, hs1] at ht'
  have hvs : vs.chain = .watch w := chainTick_false_idle hz ht'
  have hne1 : s1.chain ≠ .idle := by rw [hs1]; intro h0; cases h0
  have ht2 : ChainTick false s1.chain vs.chain := by
    have h0 : ChainTick (decide (read (left s1.left) = read (right s1.right))) s1.chain vs.chain := ht
    rw [decide_eq_false hmatch0] at h0
    exact h0
  have hcmpS : (galilFrameS P q first).compare s1 (afterMismatch s1 vs vq) :=
    ⟨vs, vq, false, hl, hr, Iff.intro (fun h0 => by cases h0) (fun h0 => absurd h0 hmis), hq,
      Or.inl ⟨hne1, ht2⟩,
      by simp [afterBirth_of_ne_idle (found := decide (vq.search.mode = .found)) hne1]⟩
  have hmisS : ¬ (galilFrameS P q first).matched (afterMismatch s1 vs vq) := by
    intro h0
    apply hmatch0
    have h1 : read (afterMismatch s1 vs vq).left = read (afterMismatch s1 vs vq).right := h0
    rw [afterMismatch_left, afterMismatch_right] at h1
    have hl' : vs.left = left s1.left := hl
    have hr' : vs.right = right s1.right := hr
    rw [hl', hr'] at h1
    exact h1
  have hav' : (galilFrameS P q first).available s1 := hav
  have htick : Tick (galilFrameS P q first) delay ⟨c1, s1⟩
      ⟨{c1 with clock := delay, mode := .shift}, s2⟩ :=
    .scan_shift c1 s1 (afterMismatch s1 vs vq) s2 hm1 (Or.inr hav') hc1 hcmpS hmisS hr1 hg hb
  -- the shift phase
  have hs2' := hs2.2
  have hl' : vs.left = left s1.left := hl
  have hr' : vs.right = right s1.right := hr
  have hstart : (⟨s2.center, s2.left, s2.remaining, s2.radius, s2.length⟩ : ShiftState) =
      ⟨s1.center, left s1.left, ofNat h, inc s1.radius, inc (inc s1.length)⟩ := by
    rw [hs2']
    simp [afterMismatch, searchLens, scanLens, radiusAfter, hl']
  have hcyc : s2.cycle = reset := by rw [hs2']
  have hs2c : s2.chain = .watch (GalilScaffoldChainWatch.immediate w) := by rw [hs2']
  have hchain' : ChainShiftRun ⟨s2.center, s2.left, s2.remaining, s2.radius, s2.length⟩
      (GalilScaffoldChainWatch.immediate w) s2.cycle h t' v cycle := by
    rw [hstart, hcyc]; exact hchain
  have hzr : positive t'.remaining = false :=
    chain_shift_exhausts h (by rw [hs2']) hchain'
  have hm2 : ({c1 with clock := delay, mode := .shift} : Control).mode = .shift := rfl
  have hsh := shift_phase_stepsAll_S (SoundScan raw) (fun c s hm hsc => by rw [hm] at hsc; cases hsc)
    P q first delay _ hm2 s2 hi2 _ hs2c hchain' hzr o ho
    (fun _ => outputRel_of_refreshS' raw P hP hP' q first _ _ o hiEnd ho _ rfl)
  have hQ1 : SoundScan raw ⟨c1, s1⟩ := fun _ => hout
  have hQ2 : SoundScan raw ⟨{c1 with clock := delay, mode := .shift}, s2⟩ := fun h0 => by cases h0
  exact stepsAll_trans (.succ hQ1 htick (.zero _ hQ2)) hsh

/-- Every state of a chain's life has a sound output in scan mode. -/
theorem life_stepsAll (raw : List (Fin 2)) (P : Shared) (hP : P.onLetter = onLetterVM raw)
    (hP' : P.leftFirst = leftFirstVM) (qq : ℕ) (first : Fin 9) (delay : ℕ)
    -- the found tick
    {cF : Control} {sF : GalilVM} (hmF : cF.mode = .scan) (hrF : cF.replaying = false)
    (hcF : cF.clock = 1) (havF : canRight sF.right) (hidle : sF.chain = .idle)
    {cen R : ℕ} (hscan : ScanInvariant raw cen R sF.left sF.right) (houtF : OutputRel raw cF sF)
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
    ∃ k, StepsAll (galilFrameS P qq first) delay (SoundScan raw) k ⟨cF, sF⟩
      ⟨{c3 with clock := delay, output := o3, replaying := false}, afterCompare s3 vs3 vq3⟩ := by
  -- the found tick
  have htickF := found_start_match P qq first delay cF sF hmF hrF hcF havF hidle vq hq hfound hmt ch hch oF hoF
  have hoF' : refresh (galilFrame P qq first)
      (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq) cF.output oF :=
    (refresh_afterBirth raw P hP hP' qq first true _ _ _).mp hoF
  obtain ⟨hinv1, hout1⟩ := outputRel_matched_refresh' raw P hP hP' qq first vq rfl rfl hmt havF hscan cF.output oF hoF'
    {cF with clock := delay, output := oF, replaying := false} rfl
  -- the preparation
  obtain ⟨k1, hst1⟩ := watchSegE_stepsAll raw P hP hP' qq first delay hprepSeg cen (R+1) hinv1 hout1
  have hinv2 := (watchSegE_output_inv raw P hP hP' qq first delay hprepSeg cen (R+1) hinv1 hout1).2
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
  refine ⟨_, stepsAll_trans (.succ (fun _ => houtF) htickF (stepsAll_mono lift hst1))
    (stepsAll_trans (stepsAll_mono lift hst2) (stepsAll_trans hst3 (stepsAll_trans hst4
      (stepsAll_trans (stepsAll_mono lift hst5) (.succ hQ3 htick3 (.zero _ hQ4))))))⟩

#print axioms first_shift_stepsAll
#print axioms life_stepsAll

end PalPeg.GalilScaffoldChainInputSupply
