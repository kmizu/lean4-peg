import PalPeg.GalilScaffoldTopScanSeg
import PalPeg.GalilScaffoldTopShiftRound

/-!
# One controller round as a `CompareRounds` step

A round of the controller in `periodOnly` watch mode: a scan segment of
matched comparisons, the terminal comparison at the last continuation cell
whose outer symbols differ while the prediction agrees with R, the shift
entry, and the `h` unit shifts back to scan mode. On the only-compare
projection this is exactly `CompareRounds.next … (.stop _)`: the segment is
the `OnlyMatchedRun`, the terminal data are `hend`/`hc`/`hprediction`, the
shift runs are the lower layer's `ShiftRun`/`ChainShiftRun`, and the state
after the shift projects to the round's end state.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-- A chain shift run is a shift run (its head/counter part). -/
theorem shiftRun_of_chain {s t : ShiftState} {w v : GalilScaffoldChainWatch.State}
    {cycle finish : Counter} {n : ℕ} (hr : ChainShiftRun s w cycle n t v finish) : ShiftRun s n t := by
  induction hr with
  | stop => exact .stop _
  | next _ _ _ enabled hc hl hl' _ ih => exact .next _ enabled hc hl hl' ih

/-- Transfer of a shift-phase run on the pulled shift frame to `galilFrameS`
(the shift phase never ticks in scan mode). -/
theorem shift_steps_S (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) (c : Control)
    (hm : c.mode = .shift) (s2 : GalilVM) (hi : CopyIdle s2) {k : ℕ} {c' : Control} {v : ShiftVM}
    (hs' : Steps (Frame.pull shiftLens (shiftFrame (fun v => P.onLetter (shiftLens.set s2 v))
      (fun v => P.leftFirst (shiftLens.set s2 v)))) delay k ⟨c, s2⟩ ⟨c', shiftLens.set s2 v⟩) :
    Steps (galilFrameS P q first) delay k ⟨c, s2⟩ ⟨c', shiftLens.set s2 v⟩ := by
  have := steps_transfer_generic shiftLens
    (shiftFrame (fun v => P.onLetter (shiftLens.set s2 v)) (fun v => P.leftFirst (shiftLens.set s2 v)))
    (galilFrameS P q first) delay (fun m => m = .shift) (fun m => m = .scan)
    (fun s => CopyIdle s ∧ ∃ v0, s = shiftLens.set s2 v0)
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
    k hm ⟨hi, shiftLens.get s2, (shiftLens.set_get s2).symm⟩ hs'
  exact this.1

/-- The shift phase on `galilFrameS`, with the exit output given by `refresh`
(so that the round can be chained with the actual continuation). -/
theorem shift_phase_S (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) (c : Control)
    (hm : c.mode = .shift) (s2 : GalilVM) (hi : CopyIdle s2) (w : GalilScaffoldChainWatch.State)
    (hs : s2.chain = .watch w) {n : ℕ} {t : ShiftState} {v : GalilScaffoldChainWatch.State}
    {finish : Counter}
    (hr : ChainShiftRun ⟨s2.center, s2.left, s2.remaining, s2.radius, s2.length⟩ w s2.cycle n t v finish)
    (hz : positive t.remaining = false) (o : Bool)
    (ho : refresh (galilFrameS P q first) (shiftLens.set s2 ⟨t, .watch v, finish⟩) c.output o) :
    Steps (galilFrameS P q first) delay (n+1) ⟨c, s2⟩
      ⟨{c with mode := .scan, output := o}, shiftLens.set s2 ⟨t, .watch v, finish⟩⟩ := by
  apply shift_steps_S P q first delay c hm s2 hi
  have h1 := shift_run_lift (fun v => P.onLetter (shiftLens.set s2 v))
    (fun v => P.leftFirst (shiftLens.set s2 v)) delay c hm n hr
  have hexit : Tick (shiftFrame (fun v => P.onLetter (shiftLens.set s2 v))
      (fun v => P.leftFirst (shiftLens.set s2 v))) delay ⟨c, ⟨t, .watch v, finish⟩⟩
      ⟨{c with mode := .scan, output := o}, ⟨t, .watch v, finish⟩⟩ :=
    .shift_done c _ o hm (by show ¬ positive t.remaining = true; rw [hz]; decide) ho
  have h := steps_trans h1 (.succ hexit (.zero _))
  rw [← hs] at h
  exact steps_pull shiftLens _ delay (n+1) c _ s2 _ h

theorem afterMismatch_left (s : GalilVM) (vs : ScanVM) (vq : SearchVM) : (afterMismatch s vs vq).left = vs.left := rfl
theorem afterMismatch_right (s : GalilVM) (vs : ScanVM) (vq : SearchVM) : (afterMismatch s vs vq).right = vs.right := rfl
theorem afterMismatch_center (s : GalilVM) (vs : ScanVM) (vq : SearchVM) : (afterMismatch s vs vq).center = s.center := rfl
theorem afterMismatch_radius (s : GalilVM) (vs : ScanVM) (vq : SearchVM) : (afterMismatch s vs vq).radius = inc s.radius := rfl
theorem afterMismatch_length (s : GalilVM) (vs : ScanVM) (vq : SearchVM) : (afterMismatch s vs vq).length = s.length := rfl
theorem afterMismatch_cycle (s : GalilVM) (vs : ScanVM) (vq : SearchVM) : (afterMismatch s vs vq).cycle = s.cycle := rfl
theorem afterMismatch_chain (s : GalilVM) (vs : ScanVM) (vq : SearchVM) : (afterMismatch s vs vq).chain = vs.chain := rfl

/-- One round of the controller is one `CompareRounds` step. -/
theorem round_next (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) (h : ℕ)
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
    (ho : refresh (galilFrameS P q first) (shiftLens.set s2 ⟨t', .watch v, cycle⟩) c1.output o) :
    (∃ k : ℕ, Steps (galilFrameS P q first) delay (k + 1 + (h+1)) ⟨c, s⟩
        ⟨{c1 with mode := .scan, clock := delay, output := o}, shiftLens.set s2 ⟨t', .watch v, cycle⟩⟩) ∧
      CompareRounds h (toOnly s w0) 1 (toOnly (shiftLens.set s2 ⟨t', .watch v, cycle⟩) v) := by
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
  have hsh := shift_phase_S P q first delay _ hm2 s2 hi2 _ hs2c hchain' hzr o ho
  obtain ⟨k, hsteps⟩ := scanSeg_steps P q first delay hseg
  refine ⟨⟨k, ?_⟩, ?_⟩
  · have e : k + 1 + (h+1) = k + (0 + 1 + (h+1)) := by omega
    rw [e]
    exact steps_trans hsteps (steps_trans (.succ htick (.zero _)) hsh)
  · -- the projection of the end state
    have hright : s2.right = right s1.right := by rw [hs2']; simp [afterMismatch, searchLens, scanLens, hr']
    have hend' : toOnly (shiftLens.set s2 ⟨t', .watch v, cycle⟩) v =
        ⟨t'.center, t'.left, right (toOnly s1 w).right, v, cycle, t'.radius⟩ := by
      simp only [toOnly, shiftLens]
      rw [hright]
    rw [hend']
    exact .next (toOnly s w0) hrun' hend hav hpred (inc_canonical _ (inc_canonical _ hlen))
      (shiftRun_of_chain hchain) hchain (.stop _)

#print axioms shift_steps_S
#print axioms shift_phase_S
#print axioms round_next

end PalPeg.GalilScaffoldChainInputSupply
