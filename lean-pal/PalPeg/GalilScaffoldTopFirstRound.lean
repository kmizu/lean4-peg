import PalPeg.GalilScaffoldTopWatchSeg

/-!
# The first round: from the found search to the first shift's `Entry`

The watch period after the chain start is a general segment (`WatchSeg`),
its terminal comparison is a mismatch on the outer symbols with the
prediction agreeing with R, and the shift entry follows. On the controller
this is a run of `galilFrameS` ending in scan mode with the chain watching
at lag zero in `periodOnly` mode; on the projection the state after the
shift carries the `Entry` of the first shift's read origin
(`found_shift_entry`), the start of `rounds_lift`/`rounds_break`.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-- The terminal mismatch comparison and the shift, as controller steps. -/
theorem terminal_shift_steps (P : Shared) (q : ℕ) (first : Fin 9) (delay h : ℕ)
    (c1 : Control) (s1 : GalilVM)
    (hm1 : c1.mode = .scan) (hr1 : c1.replaying = false) (hc1 : c1.clock = 1)
    (w : GalilScaffoldChainWatch.State) (hs1 : s1.chain = .watch w) (hz : zero w.lag = true)
    (hav : canRight s1.right) (vs : ScanVM) (vq : SearchVM)
    (hcmp : (galilFrame P q first).compare s1 (scanLens.set s1 vs))
    (hmis : ¬ (galilFrame P q first).matched (scanLens.set s1 vs))
    (hq : searchEffect P false s1 vq)
    (hg : P.shiftGuard (afterMismatch s1 vs vq))
    (s2 : GalilVM) (hb : P.beginShift (afterMismatch s1 vs vq) s2)
    (hs2 : beginShiftVM h w (afterMismatch s1 vs vq) s2) (hi2 : CopyIdle s2)
    {t' : ShiftState} {v : GalilScaffoldChainWatch.State} {cycle : Counter}
    (hchain : ChainShiftRun ⟨s1.center, left s1.left, ofNat h, inc s1.radius, inc (inc s1.length)⟩
      (GalilScaffoldChainWatch.immediate w) reset h t' v cycle)
    (o : Bool)
    (ho : refresh (galilFrameS P q first) (shiftLens.set s2 ⟨t', .watch v, cycle⟩) c1.output o) :
    Steps (galilFrameS P q first) delay (1 + (h+1)) ⟨c1, s1⟩
        ⟨{c1 with mode := .scan, clock := delay, output := o}, shiftLens.set s2 ⟨t', .watch v, cycle⟩⟩ ∧
      vs.left = left s1.left ∧ vs.right = right s1.right ∧ s2.right = right s1.right ∧
      s2.periodOnly = true ∧ read (left s1.left) ≠ read (right s1.right) := by
  have hcmp0 := hcmp
  obtain ⟨⟨hl, hr, ht⟩, _⟩ := hcmp0
  rw [scanLens.get_set] at hl hr ht
  have hl' : vs.left = left s1.left := hl
  have hr' : vs.right = right s1.right := hr
  have hmatch0 : ¬ read (left s1.left) = read (right s1.right) := by
    intro h0
    apply hmis
    show read (scanLens.get (scanLens.set s1 vs)).left = read (scanLens.get (scanLens.set s1 vs)).right
    rw [scanLens.get_set]
    show read vs.left = read vs.right
    rw [hl', hr']; exact h0
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
    rw [afterMismatch_left, afterMismatch_right, hl', hr'] at h1
    exact h1
  have hav' : (galilFrameS P q first).available s1 := hav
  have htick : Tick (galilFrameS P q first) delay ⟨c1, s1⟩
      ⟨{c1 with clock := delay, mode := .shift}, s2⟩ :=
    .scan_shift c1 s1 (afterMismatch s1 vs vq) s2 hm1 (Or.inr hav') hc1 hcmpS hmisS hr1 hg hb
  have hs2' := hs2.2
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
  refine ⟨?_, hl', hr', ?_, ?_, hmatch0⟩
  · have e : 1 + (h+1) = 0 + 1 + (h+1) := by omega
    rw [e]
    exact steps_trans (.succ htick (.zero _)) hsh
  · rw [hs2']; simp [afterMismatch, searchLens, scanLens, hr']
  · rw [hs2']

/-- The first round, from the found search. -/
theorem first_round (P : Shared) (qq : ℕ) (first : Fin 9) (delay : ℕ)
    {s t : GalilScaffoldSearchFinish.State}
    {x y : GalilScaffoldControl.Machine 12} {as : List Bool}
    (a : Fin 2) (ls rs q : List (Fin 2)) (gap : Bool) (cen : PlaceHead)
    (hcen : cen = represent ⟨a :: ls,gap⟩ (rs.map some) q)
    (c : Fin 3) (hc : GalilScaffoldPlace.read ⟨a :: ls,gap⟩ = some c)
    (span lower : ℕ)
    (hr : GalilScaffoldSearchRun.SafeQuanta s x as t y) (hs : s.mode = .run)
    (ht : t.mode = .found)
    (hv : GalilDpCorrect.Result ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (span+1)) lower 0
      (GalilScaffoldProgram.denote y.config))
    (radius : GalilScaffoldCounter.Counter) (hrc : GalilScaffoldCounter.Canonical radius)
    (hrp : 0 < GalilScaffoldCounter.value radius) (sm dm : Bool) :
    let raw := (a :: ls).reverse ++ (rs ++ q)
    ∀ (h : ℕ) (ys : List (Fin 3)) (b : Fin 3),
      GalilDpCorrect.Candidate ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (span+1)) lower h →
      ys.length+1 = h →
      ∀ (copyMatches backMatches : List Bool), copyMatches.length = h → backMatches.length = h+1 →
      let final := GalilScaffoldChainCredits.run (GalilScaffoldChainCredits.start radius)
        (GalilScaffoldChainCredits.prepEvents sm dm copyMatches backMatches)
      let s0 := watchStart cen c ys b final
      ∀ (initialRadius : ℕ) (hlag : GalilScaffoldCounter.value s0.lag = initialRadius)
        -- the watch period
        {c0 c1 : Control} {v0 s1 : GalilVM} (hseg : WatchSeg P qq first delay c0 v0 c1 s1)
        (hchain0 : v0.chain = .watch s0) (hcen0 : v0.center = cen)
        (hrad0 : value v0.radius = initialRadius) (hrc0 : Canonical v0.radius)
        (hlc0 : Canonical v0.length)
        (hi0 : ScanInvariant raw (position cen) initialRadius v0.left v0.right)
        -- the terminal comparison
        (hm1 : c1.mode = .scan) (hr1 : c1.replaying = false) (hc1 : c1.clock = 1)
        (w : GalilScaffoldChainWatch.State) (hs1 : s1.chain = .watch w)
        (hphase : w.machine.control.phase = 4) (hz : zero w.lag = true)
        (hav : canRight s1.right) (vs : ScanVM) (vq : SearchVM)
        (hcmp : (galilFrame P qq first).compare s1 (scanLens.set s1 vs))
        (hmis : ¬ (galilFrame P qq first).matched (scanLens.set s1 vs))
        (hq : searchEffect P false s1 vq)
        (predicted : Fin 3)
        (hpred : GalilScaffoldChainConsume.symbol w.machine.control.period.focus = some predicted)
        (hread : read (right s1.right) = some predicted)
        -- the shift
        (hg : P.shiftGuard (afterMismatch s1 vs vq))
        (s2 : GalilVM) (hb : P.beginShift (afterMismatch s1 vs vq) s2)
        (hs2 : beginShiftVM h w (afterMismatch s1 vs vq) s2) (hi2 : CopyIdle s2)
        {t' : ShiftState} {v : GalilScaffoldChainWatch.State} {cycle : Counter}
        (hchain : ChainShiftRun ⟨s1.center, left s1.left, ofNat h, inc s1.radius, inc (inc s1.length)⟩
          (GalilScaffoldChainWatch.immediate w) reset h t' v cycle)
        (o : Bool)
        (ho : refresh (galilFrameS P qq first) (shiftLens.set s2 ⟨t', .watch v, cycle⟩) c1.output o),
      let e := shiftLens.set s2 ⟨t', .watch v, cycle⟩
      (∃ k : ℕ, Steps (galilFrameS P qq first) delay k ⟨c0, v0⟩
          ⟨{c1 with mode := .scan, clock := delay, output := o}, e⟩) ∧
        e.chain = .watch v ∧ zero v.lag = true ∧ e.periodOnly = true ∧
        ∃ o' : ReadOrigin raw, Entry raw o' (toOnly e v) ∧ o'.interior.length+1 = h ∧
          o'.center = position cen ∧ o'.shifts = 0 ∧ read t'.center ≠ none := by
  intro raw h ys b hcand hys
  have hrest := found_shift_entry a ls rs q gap cen hcen c hc span lower hr hs ht hv radius hrc hrp
    sm dm h ys b hcand hys
  intro copyMatches backMatches hcl hbl final s0 initialRadius hlag c0 c1 v0 s1 hseg hchain0 hcen0
    hrad0 hrc0 hlc0 hi0 hm1 hr1 hc1 w hs1 hphase hz hav vs vq hcmp hmis hq predicted hpred hread
    hg s2 hb hs2 hi2 t' v cycle hchain o ho e
  -- the events of the watch period
  obtain ⟨es, hch, hsc, hcen1, hpo1, hrad1, hrc1, hlc1⟩ := watchSeg_events P qq first delay hseg (by rw [hchain0]; intro h0; cases h0)
  rw [hchain0, hs1] at hch
  have hrun := chainTicks_watch_run es hch
  have hi1 : ScanInvariant raw (position cen) (initialRadius + es.count true) s1.left s1.right :=
    scan_events_invariant (hsc raw (position cen) initialRadius) hi0
  -- the steps
  obtain ⟨k1, hst1⟩ := watchSeg_steps P qq first delay hseg
  obtain ⟨hst2, hl, hr', hright, hpo2, hmatch0⟩ := terminal_shift_steps P qq first delay h c1 s1
    hm1 hr1 hc1 w hs1 hz hav vs vq hcmp hmis hq hg s2 hb hs2 hi2 hchain o ho
  refine ⟨⟨_, steps_trans hst1 hst2⟩, rfl, by rw [chain_shift_lag hchain]; exact hz, hpo2, ?_⟩
  -- the entry
  have hc1c : s1.center = cen := by rw [hcen1, hcen0]
  rw [hc1c] at hchain
  obtain ⟨o', he, hint, hocen, _, hshifts, hread'⟩ := hrest copyMatches backMatches hcl hbl hrun hphase
    initialRadius (initialRadius + es.count true) hlag hz rfl s1.left s1.right hi1 hav predicted
    hpred hread (inc s1.radius) (inc (inc s1.length))
    (by rw [inc_value, hrad1, hrad0]; push_cast; ring)
    (inc_canonical _ (hrc1 hrc0)) (inc_canonical _ (inc_canonical _ (hlc1 hlc0))) hmatch0 hchain
  have hend' : toOnly e v = ⟨t'.center, t'.left, right s1.right, v, cycle, t'.radius⟩ := by
    simp only [e, toOnly, shiftLens]
    rw [hright]
  rw [hend']
  exact ⟨o', he, hint, hocen, hshifts, hread'⟩

#print axioms terminal_shift_steps
#print axioms first_round

end PalPeg.GalilScaffoldChainInputSupply
