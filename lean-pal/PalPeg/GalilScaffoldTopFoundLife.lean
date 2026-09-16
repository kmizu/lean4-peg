import PalPeg.GalilScaffoldTopWatchSegE

/-!
# From the found tick to the broken chain

The matched comparison whose search quantum ends `found` starts the chain
(`found_start_match`); the preparation period (`prep_watch_start`) brings
it to `watchStart`; the watch period, the first shift, the re-shift rounds
and the breaking comparison are `chain_life`. Everything is one run of
`galilFrameS` from the found state, and the restart entry conditions hold
at its end. The scan invariant at the found state and the decoding of the
centre (`P.centre`/`P.place`) are the external premises.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

theorem found_life (P : Shared) (qq : ℕ) (first : Fin 9) (delay : ℕ)
    (a : Fin 2) (ls rs q : List (Fin 2)) (gap : Bool)
    -- the found tick
    {cF : Control} {sF : GalilVM} (hmF : cF.mode = .scan) (hrF : cF.replaying = false)
    (hcF : cF.clock = 1) (havF : canRight sF.right) (hidle : sF.chain = .idle)
    (hcen : sF.center = represent ⟨a :: ls,gap⟩ (rs.map some) q)
    (R : ℕ) (hscan : ScanInvariant ((a :: ls).reverse ++ (rs ++ q)) (position sF.center) R sF.left sF.right)
    (hR : value sF.radius = R) (hrc : Canonical sF.radius) (hlc : Canonical sF.length)
    (hRpos : 0 < R)
    (vq : SearchVM) (hq : searchEffect P true sF vq)
    (hrun : sF.search.mode = .run) (hfound : vq.search.mode = .found)
    (span lower : ℕ)
    (hv : GalilDpCorrect.Result ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (span+1)) lower 0
      (GalilScaffoldProgram.denote vq.dp.config))
    (hcentre : GalilScaffoldPlace.read ⟨a :: ls,gap⟩ = some (P.centre sF))
    (hplace : P.place sF = ⟨a :: ls,gap⟩)
    (hmt : read (left sF.left) = read (right sF.right))
    (ch : ChainVM)
    (hch : ChainMatched (chainStart (vq.dp.config.tapes 11) (P.centre sF) (P.place sF) sF.center sF.radius) ch)
    (oF : Bool)
    (hoF : refresh (galilFrame P qq first) (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq) cF.output oF)
    (dm : Bool) :
    ∃ (h : ℕ) (ys : List (Fin 3)) (b : Fin 3),
      GalilDpCorrect.Candidate ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (span+1)) lower h ∧
      ys.length+1 = h ∧
      ∀ (bs cs : List Bool), bs.length = h → cs.length = h+1 →
      ∀ {c2 : Control} {s2 : GalilVM},
        WatchSegE P qq first delay (bs ++ dm :: cs)
          {cF with clock := delay, output := oF, replaying := false}
          (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq) c2 s2 →
      ∀ {c1 : Control} {s1 : GalilVM} (hseg : WatchSeg P qq first delay c2 s2 c1 s1)
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
        (ho : refresh (galilFrameS P qq first) (shiftLens.set s2 ⟨t', .watch v, cycle⟩) c1.output o)
        -- the re-shift rounds
        {m : ℕ} {c' : Control} {s' : GalilVM}
        (hrounds : Rounds P qq first delay h m {c1 with mode := .scan, clock := delay, output := o}
          (shiftLens.set s2 ⟨t', .watch v, cycle⟩) c' s')
        (hcenter : read s'.center ≠ none)
        -- the final segment and the breaking comparison
        {n : ℕ} {c3 : Control} {s3 : GalilVM} (hseg3 : ScanSeg P qq first delay n c' s' c3 s3)
        (hm3 : c3.mode = .scan) (hr3 : c3.replaying = false) (hc3 : c3.clock = 1)
        (w3 : GalilScaffoldChainWatch.State) (hs3 : s3.chain = .watch w3) (hav3 : canRight s3.right)
        (vs3 : ScanVM) (vq3 : SearchVM)
        (hcmp3 : (galilFrame P qq first).compare s3 (scanLens.set s3 vs3))
        (hmt3 : (galilFrame P qq first).matched (scanLens.set s3 vs3))
        (hq3 : searchEffect P true s3 vq3)
        (hend3 : singlePositive s3.cycle = true)
        (w3' : GalilScaffoldChainWatch.State) (hbr3 : vs3.chain = .broken w3')
        (o3 : Bool) (ho3 : refresh (galilFrame P qq first) (afterCompare s3 vs3 vq3) c3.output o3),
      (∃ k : ℕ, Steps (galilFrameS P qq first) delay k ⟨cF, sF⟩
          ⟨{c3 with clock := delay, output := o3, replaying := false}, afterCompare s3 vs3 vq3⟩) ∧
        w3' = GalilScaffoldChainWatch.immediate w3 ∧ (afterCompare s3 vs3 vq3).chain = .broken w3' ∧
        ∃ org : ReadOrigin ((a :: ls).reverse ++ (rs ++ q)), org.interior.length+1 = h ∧ org.center = position sF.center ∧
          org.shifts = 0 ∧
          Entry ((a :: ls).reverse ++ (rs ++ q)) org (toOnly (shiftLens.set s2 ⟨t', .watch v, cycle⟩) v) ∧
          ScanInvariant ((a :: ls).reverse ++ (rs ++ q)) (org.center+(m+1)*h) (org.radius+1+m*h-h+n+1)
              (afterCompare s3 vs3 vq3).left (afterCompare s3 vs3 vq3).right ∧
            w3'.machine.control.broken = true ∧
            negative w3'.margin = false ∧
            positive w3'.machine.control.last = true ∧
            zero w3'.lag = true ∧
            read (afterCompare s3 vs3 vq3).center ≠ none ∧
            RadiusRep (afterCompare s3 vs3 vq3).radius (org.radius+1+m*h-h+n+1) ∧
            negative (afterCompare s3 vs3 vq3).radius = false ∧
            (GalilScaffoldSearchFinish.begin w3'.machine.control.last
              (afterCompare s3 vs3 vq3).radius).work = w3'.machine.control.last ∧
            Canonical w3'.machine.control.last := by
  obtain ⟨r0, hr0⟩ : ∃ r0, R = r0+1 := ⟨R-1, by omega⟩
  subst hr0
  have hrad : sF.radius = ofNat (r0+1) := GalilScaffoldChainCatch.canonical_nat _ hrc _ hR
  have hc : GalilScaffoldPlace.read ⟨a :: ls,gap⟩ = some (P.centre sF) := hcentre
  have hchF := hch
  rw [hplace, hrad] at hch
  obtain ⟨h, c, ys, b, hcand, hreadc, hys, hprep⟩ :=
    prep_watch_start P qq first delay ⟨a :: ls,gap⟩ rfl (searchEffect_run P hq hidle hrun).1 hrun hfound hv sF.center r0 dm
  have hcc : c = P.centre sF := by rw [hreadc] at hc; injection hc
  subst hcc
  refine ⟨h, ys, b, hcand, hys, ?_⟩
  intro bs cs hbs hcs c2 s2 hprepSeg c1 s1 hseg hm1 hr1 hc1 w hs1 hphase hz hav vs vq' hcmp hmis hq'
    predicted hpred hread hg s2' hb hs2' hi2 t' v cycle hchain o ho m c' s' hrounds hcenter n c3 s3
    hseg3 hm3 hr3 hc3 w3 hs3 hav3 vs3 vq3 hcmp3 hmt3 hq3 hend3 w3' hbr3 o3 ho3
  -- the found tick
  have htickF := found_start_match P qq first delay cF sF hmF hrF hcF havF hidle vq hq hfound hmt ch hchF oF hoF
  -- the chain after the preparation
  have hchain0 := hprep bs cs hbs hcs ch hch hprepSeg (by rw [afterCompare_chain])
  -- the scan invariant after the found tick and the preparation
  have hinvF : ScanInv ((a :: ls).reverse ++ (rs ++ q)) sF (r0+1) :=
    ⟨hscan, hR, hrc, hlc, ⟨a, ls, rs, q, gap, hcen, by simp [List.append_assoc]⟩⟩
  have hinv1 := scanInv_compare_matched hinvF ⟨left sF.left, right sF.right, ch⟩ vq rfl rfl havF hmt
  obtain ⟨_, hscP, hcenP, _, hradP, hrcP, hlcP⟩ := watchSegE_events P qq first delay hprepSeg (by rw [afterCompare_chain]; show ch ≠ .idle; intro h0; rw [h0] at hchF; cases hchF)
  rw [afterCompare_center] at hcenP
  have hi0 : ScanInvariant ((a :: ls).reverse ++ (rs ++ q)) (position sF.center)
      (r0+1+1 + (bs ++ dm :: cs).count true) s2.left s2.right := by
    have := scan_events_invariant (hscP ((a :: ls).reverse ++ (rs ++ q)) (position sF.center) (r0+1+1)) (by
      have h0 := hinv1.scan
      rw [afterCompare_center] at h0
      exact h0)
    exact this
  have hrad0 : value s2.radius = ((r0+1+1 + (bs ++ dm :: cs).count true : ℕ) : ℤ) := by
    rw [hradP, afterCompare_radius, inc_value, hR]; push_cast; ring
  have hrc0 : Canonical s2.radius := hrcP (by rw [afterCompare_radius]; exact inc_canonical _ hrc)
  have hlc0 : Canonical s2.length := hlcP (by rw [afterCompare_length]; exact inc_canonical _ (inc_canonical _ hlc))
  have hlag : value (watchStart sF.center (P.centre sF) ys b (GalilScaffoldChainCredits.run
      (GalilScaffoldChainCredits.start sF.radius)
      (GalilScaffoldChainCredits.prepEvents true dm bs cs))).lag =
      ((r0+1+1 + (bs ++ dm :: cs).count true : ℕ) : ℤ) := by
    rw [watchStart_lag, (GalilScaffoldChainCredits.prep_value sF.radius true dm bs cs).2, hR]
    simp [List.count_cons]
    push_cast; ring
  have hchain0' : s2.chain = .watch (watchStart sF.center (P.centre sF) ys b (GalilScaffoldChainCredits.run
      (GalilScaffoldChainCredits.start sF.radius)
      (GalilScaffoldChainCredits.prepEvents true dm bs cs))) := by
    rw [hrad]; exact hchain0
  have hrp : 0 < value sF.radius := by rw [hR]; push_cast; omega
  obtain ⟨⟨k2, hst2⟩, hw3, hbroken, org, hint, hocen, hshifts, he, hres⟩ :=
    chain_life P qq first delay a ls rs q gap sF.center hcen (P.centre sF) hreadc span lower (searchEffect_run P hq hidle hrun).1 hrun hfound hv
      sF.radius hrc hrp true dm h ys b hcand hys bs cs hbs hcs _ hlag hseg hchain0' hcenP hrad0 hrc0 hlc0 hi0
      hm1 hr1 hc1 w hs1 hphase hz hav vs vq' hcmp hmis hq' predicted hpred hread hg s2' hb hs2' hi2 hchain o ho
      hrounds hcenter hseg3 hm3 hr3 hc3 w3 hs3 hav3 vs3 vq3 hcmp3 hmt3 hq3 hend3 w3' hbr3 o3 ho3
  obtain ⟨k1, hst1⟩ := watchSeg_steps P qq first delay (watchSeg_of_E P qq first delay hprepSeg (by rw [afterCompare_chain]; show ch ≠ .idle; intro h0; rw [h0] at hchF; cases hchF))
  refine ⟨⟨_, steps_trans (.succ htickF hst1) hst2⟩, hw3, hbroken, org, hint, hocen, hshifts, he, hres⟩

#print axioms found_life

end PalPeg.GalilScaffoldChainInputSupply
