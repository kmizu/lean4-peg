import PalPeg.GalilScaffoldTopOutputTrace

/-!
# Output soundness at every state of a re-shift round

`SoundScan raw`: in scan mode the output is sound with respect to the right
head. The shift phase never ticks from scan mode, so the transfer of the
shift run to `galilFrameS` carries any predicate that holds in shift mode
and at the exit; the exit output is refreshed under the scan invariant of
the resumed heads.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-- Output sound in scan mode. -/
def SoundScan (raw : List (Fin 2)) (st : State GalilVM) : Prop :=
  st.ctl.mode = .scan → OutputRel raw st.ctl st.vm

theorem stepsAll_transfer_generic {σ' : Type} (L : Lens GalilVM σ') (F' : Frame σ') (G : Frame GalilVM)
    (delay : ℕ) (M E : Mode → Prop) (Inv : GalilVM → Prop) (Q : State GalilVM → Prop)
    (hQM : ∀ (c : Control) (s : GalilVM), M c.mode → Q ⟨c, s⟩)
    (hinv : ∀ {c c' : Control} {s t : GalilVM}, Tick (Frame.pull L F') delay ⟨c, s⟩ ⟨c', t⟩ → Inv s → Inv t)
    (hstep : ∀ {c c' : Control} {s t : GalilVM}, M c.mode →
      Tick (Frame.pull L F') delay ⟨c, s⟩ ⟨c', t⟩ → M c'.mode ∨ E c'.mode)
    (hexit : ∀ {c c' : Control} {s t : GalilVM}, E c.mode → ¬ Tick (Frame.pull L F') delay ⟨c, s⟩ ⟨c', t⟩)
    (htr : ∀ {c c' : Control} {s t : GalilVM}, M c.mode → Inv s →
      Tick (Frame.pull L F') delay ⟨c, s⟩ ⟨c', t⟩ → Tick G delay ⟨c, s⟩ ⟨c', t⟩)
    (n : ℕ) : ∀ {c c' : Control} {s t : GalilVM}, M c.mode → Inv s →
      Steps (Frame.pull L F') delay n ⟨c, s⟩ ⟨c', t⟩ → Q ⟨c', t⟩ →
      StepsAll G delay Q n ⟨c, s⟩ ⟨c', t⟩ ∧ Inv t := by
  induction n with
  | zero =>
    intro c c' s t _ hi h hq
    cases h
    exact ⟨.zero _ hq, hi⟩
  | succ n ih =>
    intro c c' s t hm hi h hq
    cases h with
    | succ ht hr =>
      rename_i y
      obtain ⟨c1, s1⟩ := y
      have hg := htr hm hi ht
      have hi1 := hinv ht hi
      rcases hstep hm ht with hm1 | he1
      · obtain ⟨hs, hit⟩ := ih hm1 hi1 hr hq
        exact ⟨.succ (hQM c s hm) hg hs, hit⟩
      · cases hr with
        | zero => exact ⟨.succ (hQM c s hm) hg (.zero _ hq), hi1⟩
        | succ ht2 _ => exact absurd ht2 (hexit he1)

theorem shift_stepsAll_S (Q : State GalilVM → Prop) (hQM : ∀ (c : Control) (s : GalilVM), c.mode = .shift → Q ⟨c, s⟩)
    (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) (c : Control)
    (hm : c.mode = .shift) (s2 : GalilVM) (hi : CopyIdle s2) {k : ℕ} {c' : Control} {v : ShiftVM}
    (hs' : Steps (Frame.pull shiftLens (shiftFrame (fun v => P.onLetter (shiftLens.set s2 v))
      (fun v => P.leftFirst (shiftLens.set s2 v)))) delay k ⟨c, s2⟩ ⟨c', shiftLens.set s2 v⟩) 
    (hQend : Q ⟨c', shiftLens.set s2 v⟩) :
    StepsAll (galilFrameS P q first) delay Q k ⟨c, s2⟩ ⟨c', shiftLens.set s2 v⟩ := by
  have := stepsAll_transfer_generic shiftLens
    (shiftFrame (fun v => P.onLetter (shiftLens.set s2 v)) (fun v => P.leftFirst (shiftLens.set s2 v)))
    (galilFrameS P q first) delay (fun m => m = .shift) (fun m => m = .scan)
    (fun s => CopyIdle s ∧ ∃ v0, s = shiftLens.set s2 v0) Q (fun c s hm' => hQM c s hm')
    (by
      intro c c' s t ht ⟨hi, v0, hv0⟩
      refine ⟨copyIdle_shift delay _ ht hi, ?_⟩
      obtain ⟨v1, hv1⟩ := tick_pull_shape shiftLens _ delay ht
      exact ⟨v1, by rw [hv1, hv0, shiftLens.set_set]⟩)
    (by
      intro c c' s t hm' ht
      rcases tick_mode _ delay ht with h1 | h1
      · rw [h1]; exact Or.inl hm'
      · generalize c.mode = a at *
        generalize c'.mode = b at *
        subst hm'
        cases h1 <;> simp_all)
    (by
      intro c c' s t hm' ht
      exact no_scan_tick_shift _ _ delay hm' ht)
    (by
      intro c c' s t hm' ⟨hi, v0, hv0⟩ ht
      have hfr : (fun v => P.onLetter (shiftLens.set s2 v)) = (fun v => P.onLetter (shiftLens.set s v)) := by
        subst hv0; funext v; rw [shiftLens.set_set]
      have hfr' : (fun v => P.leftFirst (shiftLens.set s2 v)) = (fun v => P.leftFirst (shiftLens.set s v)) := by
        subst hv0; funext v; rw [shiftLens.set_set]
      rw [hfr, hfr'] at ht
      have hg := shift_transfer P q first delay hm' hi ht
      exact tick_S_of_tick P q first delay hg (by rw [hm']; decide))
    k hm ⟨hi, shiftLens.get s2, (shiftLens.set_get s2).symm⟩ hs' hQend
  exact this.1

theorem shift_phase_stepsAll_S (Q : State GalilVM → Prop) (hQM : ∀ (c : Control) (s : GalilVM), c.mode = .shift → Q ⟨c, s⟩)
    (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) (c : Control)
    (hm : c.mode = .shift) (s2 : GalilVM) (hi : CopyIdle s2) (w : GalilScaffoldChainWatch.State)
    (hs : s2.chain = .watch w) {n : ℕ} {t : ShiftState} {v : GalilScaffoldChainWatch.State}
    {finish : Counter}
    (hr : ChainShiftRun ⟨s2.center, s2.left, s2.remaining, s2.radius, s2.length⟩ w s2.cycle n t v finish)
    (hz : positive t.remaining = false) (o : Bool)
    (ho : refresh (galilFrameS P q first) (shiftLens.set s2 ⟨t, .watch v, finish⟩) c.output o) 
    (hQend : Q ⟨{c with mode := .scan, output := o}, shiftLens.set s2 ⟨t, .watch v, finish⟩⟩) :
    StepsAll (galilFrameS P q first) delay Q (n+1) ⟨c, s2⟩
      ⟨{c with mode := .scan, output := o}, shiftLens.set s2 ⟨t, .watch v, finish⟩⟩ := by
  apply shift_stepsAll_S Q hQM P q first delay c hm s2 hi (hQend := hQend)
  have h1 := shift_run_lift (fun v => P.onLetter (shiftLens.set s2 v))
    (fun v => P.leftFirst (shiftLens.set s2 v)) delay c hm n hr
  have hexit : Tick (shiftFrame (fun v => P.onLetter (shiftLens.set s2 v))
      (fun v => P.leftFirst (shiftLens.set s2 v))) delay ⟨c, ⟨t, .watch v, finish⟩⟩
      ⟨{c with mode := .scan, output := o}, ⟨t, .watch v, finish⟩⟩ :=
    .shift_done c _ o hm (by show ¬ positive t.remaining = true; rw [hz]; decide) ho
  have h := steps_trans h1 (.succ hexit (.zero _))
  rw [← hs] at h
  exact steps_pull shiftLens _ delay (n+1) c _ s2 _ h

theorem round_stepsAll (raw : List (Fin 2)) (P : Shared) (hP : P.onLetter = onLetterVM raw)
    (hP' : P.leftFirst = leftFirstVM) (q : ℕ) (first : Fin 9) (delay : ℕ) (h : ℕ)
    -- the matched segment
    {n : ℕ} {c c1 : Control} {s s1 : GalilVM} (hseg : ScanSeg P q first delay n c s c1 s1)
    (w0 : GalilScaffoldChainWatch.State) (hp0 : s.periodOnly = true) (hs0 : s.chain = .watch w0)
    (hz0 : zero w0.lag = true)
    -- the terminal comparison
    (hm1 : c1.mode = .scan) (hr1 : c1.replaying = false) (hc1 : c1.clock = 1)
    (w : GalilScaffoldChainWatch.State) (hs1 : s1.chain = .watch w)
    (hav : canRight s1.right) (vs : ScanVM) (vq : SearchVM)
    (hcmp : (galilFrame P q first).compare s1 (scanLens.set s1 vs))
    (hmis : ¬ (galilFrame P q first).matched (scanLens.set s1 vs))
    (hq : searchEffect P false s1 vq)
    (hend : singlePositive s1.cycle = true)
    (hpred : read (right s1.right) = GalilScaffoldChainConsume.symbol w.machine.control.period.focus)
    (hlen : Canonical s1.length)
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
    -- the invariants and the output
    {cen r : ℕ} (hi : ScanInvariant raw cen r s.left s.right) (hout : OutputRel raw c s)
    {cen' r' : ℕ} (hiEnd : ScanInvariant raw cen' r' (shiftLens.set s2 ⟨t', .watch v, cycle⟩).left
      (shiftLens.set s2 ⟨t', .watch v, cycle⟩).right) :
    ∃ k : ℕ, StepsAll (galilFrameS P q first) delay (SoundScan raw) (k + 1 + (h+1)) ⟨c, s⟩
        ⟨{c1 with mode := .scan, clock := delay, output := o}, shiftLens.set s2 ⟨t', .watch v, cycle⟩⟩ := by
  -- the segment on the projection
  obtain ⟨w', hw', hz', hp', hrun⟩ := scanSeg_only P q first delay hseg w0 hp0 hs0 hz0
  have hww : w' = w := by rw [hs1] at hw'; cases hw'; rfl
  have hz : zero w.lag = true := by rw [hww] at hz'; exact hz'
  have hrun' : OnlyMatchedRun (toOnly s w0) n (toOnly s1 w) := by rw [hww] at hrun; exact hrun
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
      Or.inl ⟨hne1, ht2⟩, rfl⟩
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
  obtain ⟨k, hsteps⟩ := scanSeg_stepsAll raw P hP hP' q first delay hseg cen r hi hout
  have hsteps' := stepsAll_mono (fun st (h0 : SoundOut raw st) (_ : st.ctl.mode = .scan) => h0) hsteps
  have hQ1 : SoundScan raw ⟨c1, s1⟩ := stepsAll_last hsteps'
  have hQ2 : SoundScan raw ⟨{c1 with clock := delay, mode := .shift}, s2⟩ := fun h0 => by cases h0
  refine ⟨k, ?_⟩
  have e : k + 1 + (h+1) = k + (0 + 1 + (h+1)) := by omega
  rw [e]
  exact stepsAll_trans hsteps' (stepsAll_trans (.succ hQ1 htick (.zero _ hQ2)) hsh)

/-- Every state across the re-shift rounds has a sound output in scan mode. -/
theorem rounds_stepsAll (raw : List (Fin 2)) (P : Shared) (hP : P.onLetter = onLetterVM raw)
    (hP' : P.leftFirst = leftFirstVM) (q : ℕ) (first : Fin 9) (delay h : ℕ) {m : ℕ}
    {c c' : Control} {s s' : GalilVM} (hr : Rounds P q first delay h m c s c' s') :
    ∀ w0 : GalilScaffoldChainWatch.State, s.periodOnly = true → s.chain = .watch w0 →
      zero w0.lag = true → ∀ org : ReadOrigin raw, org.interior.length+1 = h →
      Entry raw org (toOnly s w0) → OutputRel raw c s →
      ∃ k, StepsAll (galilFrameS P q first) delay (SoundScan raw) k ⟨c, s⟩ ⟨c', s'⟩ := by
  induction hr with
  | stop c s => intro w0 _ _ _ org _ _ ho; exact ⟨0, .zero _ (fun _ => ho)⟩
  | next c s hseg hm1 hr1 hc1 w hs1 hav vs vq hcmp hmis hq hend hpred hlen hg s2 hb hs2 hi2 hchain o ho rest ih =>
    intro w0 hp hs hz org hint he hout
    have hi : ScanInvariant raw _ _ s.left s.right := entry_scanInvariant he
    obtain ⟨_, hcr1⟩ := round_next P q first delay h hseg w0 hp hs hz hm1 hr1 hc1 w hs1 hav vs vq
      hcmp hmis hq hend hpred hlen hg s2 hb hs2 hi2 hchain o ho
    obtain ⟨org', he', _, hinterior, _, _, _, _, _⟩ := rounds_origin hcr1 org hint he
    have hi2' := entry_scanInvariant he'
    obtain ⟨k1, hst1⟩ := round_stepsAll raw P hP hP' q first delay h hseg w0 hp hs hz hm1 hr1 hc1 w hs1 hav
      vs vq hcmp hmis hq hend hpred hlen hg s2 hb hs2 hi2 hchain o ho hi hout hi2'
    obtain ⟨w1, hw1, hz1, _, _⟩ := scanSeg_only P q first delay hseg w0 hp hs hz
    have hww : w1 = w := by rw [hs1] at hw1; injection hw1 with e; exact e.symm
    subst hww
    obtain ⟨k2, hst2⟩ := ih _ (by show s2.periodOnly = true; rw [hs2.2]) rfl
      (by rw [chain_shift_lag hchain]; exact hz1) org' (by rw [hinterior]; exact hint) he'
      (outputRel_of_refreshS' raw P hP hP' q first _ _ o hi2' ho _ rfl)
    exact ⟨_, stepsAll_trans hst1 hst2⟩

#print axioms rounds_stepsAll

#print axioms round_stepsAll

end PalPeg.GalilScaffoldChainInputSupply
