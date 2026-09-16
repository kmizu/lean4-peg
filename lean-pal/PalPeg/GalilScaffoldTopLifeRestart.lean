import PalPeg.GalilScaffoldTopReadyFound

/-!
# The life of a chain ends in a restarted state

`found_life` followed by the restart tick: the state after the restart is
`Restarted` — the entry of `restarted_next_found`. Together they give one
turn of the controller's main loop, from a found state to the next.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-- Counters of a general segment (no condition on the chain). -/
theorem watchSeg_counters (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    {c c' : Control} {s t : GalilVM} (h : WatchSeg P q first delay c s c' t) :
    (Canonical s.radius → Canonical t.radius) ∧ (Canonical s.length → Canonical t.length) := by
  induction h with
  | stop c s => exact ⟨id, id⟩
  | wait c s s' _ _ _ hb _ ih =>
    obtain ⟨hrc, hlc⟩ := ih
    obtain ⟨_, _, _, _, hrad', hlen'⟩ := background_frame P q first hb
    exact ⟨fun h0 => hrc (by rw [hrad']; exact h0), fun h0 => hlc (by rw [hlen']; exact h0)⟩
  | count c s s' _ _ _ _ hb _ ih =>
    obtain ⟨hrc, hlc⟩ := ih
    obtain ⟨_, _, _, _, hrad', hlen'⟩ := background_frame P q first hb
    exact ⟨fun h0 => hrc (by rw [hrad']; exact h0), fun h0 => hlc (by rw [hlen']; exact h0)⟩
  | «match» c s vs vq o _ _ _ _ _ _ _ _ _ _ ih =>
    obtain ⟨hrc, hlc⟩ := ih
    rw [afterCompare_radius] at hrc
    rw [afterCompare_length] at hlc
    exact ⟨fun hc => hrc (inc_canonical _ hc), fun hc => hlc (inc_canonical _ (inc_canonical _ hc))⟩

theorem life_restarted (P : Shared) (qq : ℕ) (first : Fin 9) (delay : ℕ)
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
    (dm : Bool) (entry : ℕ) (hres : ∀ s t, restartVM entry s t → P.restart s t) :
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
        (o3 : Bool) (ho3 : refresh (galilFrame P qq first) (afterCompare s3 vs3 vq3) c3.output o3)
,
      (∃ k : ℕ, Steps (galilFrameS P qq first) delay k ⟨cF, sF⟩
          ⟨{c3 with clock := delay, output := o3, replaying := false}, {(afterCompare s3 vs3 vq3) with chain := .idle, lower := w3'.machine.control.last, search := GalilScaffoldSearchFinish.begin w3'.machine.control.last (afterCompare s3 vs3 vq3).radius, dp := GalilScaffoldControl.reset entry (afterCompare s3 vs3 vq3).dp}⟩) ∧
      ∃ Rad : ℕ, Restarted ((a :: ls).reverse ++ (rs ++ q)) {(afterCompare s3 vs3 vq3) with chain := .idle, lower := w3'.machine.control.last, search := GalilScaffoldSearchFinish.begin w3'.machine.control.last (afterCompare s3 vs3 vq3).radius, dp := GalilScaffoldControl.reset entry (afterCompare s3 vs3 vq3).dp} Rad w3'.machine.control.last := by
  obtain ⟨h, ys, b, hcand, hys, hlife⟩ := found_life P qq first delay a ls rs q gap hmF hrF hcF havF hidle
    hcen R hscan hR hrc hlc hRpos vq hq hrun hfound span lower hv hcentre hplace hmt ch hch oF hoF dm
  refine ⟨h, ys, b, hcand, hys, ?_⟩
  intro bs cs hbs hcs c2 s2 hprepSeg c1 s1 hseg hm1 hr1 hc1 w hs1 hphase hz hav vs vq' hcmp hmis hq'
    predicted hpred hread hg s2' hb hs2' hi2 t' v cycle hchain o ho m c' s' hrounds hcenter n c3 s3
    hseg3 hm3 hr3 hc3 w3 hs3 hav3 vs3 vq3 hcmp3 hmt3 hq3 hend3 w3' hbr3 o3 ho3
  obtain ⟨⟨k1, hst⟩, hw3, hbroken, org, hint, hocen, hshifts, he, hinv, hbr, hmargin, hlast, hlag,
      hreadc, hrr3, hneg, hwork, hcanon⟩ :=
    hlife bs cs hbs hcs hprepSeg hseg hm1 hr1 hc1 w hs1 hphase hz hav vs vq' hcmp hmis hq'
      predicted hpred hread hg s2' hb hs2' hi2 hchain o ho hrounds hcenter hseg3 hm3 hr3 hc3 w3 hs3
      hav3 vs3 vq3 hcmp3 hmt3 hq3 hend3 w3' hbr3 o3 ho3
  -- the restart tick
  have htick : Tick (galilFrameS P qq first) delay
      ⟨{c3 with clock := delay, output := o3, replaying := false}, afterCompare s3 vs3 vq3⟩
      ⟨{c3 with clock := delay, output := o3, replaying := false}, {(afterCompare s3 vs3 vq3) with chain := .idle, lower := w3'.machine.control.last, search := GalilScaffoldSearchFinish.begin w3'.machine.control.last (afterCompare s3 vs3 vq3).radius, dp := GalilScaffoldControl.reset entry (afterCompare s3 vs3 vq3).dp}⟩ :=
    .restart _ _ _ hm3 (hres _ _ ⟨w3', hbroken, hmargin, hlast, hlag, rfl⟩)
  refine ⟨⟨_, steps_trans hst (.succ htick (.zero _))⟩, org.radius+1+m*h-h+n+1, ?_⟩
  -- the centre after the rounds
  have hpo : (shiftLens.set s2' ⟨t', .watch v, cycle⟩).periodOnly = true := by
    show s2'.periodOnly = true
    rw [hs2'.2]
  have hzv : zero v.lag = true := by rw [chain_shift_lag hchain]; exact hz
  obtain ⟨hrep, hfoc, hposS⟩ := rounds_centerRep P qq first delay h hrounds v hpo rfl hzv org hint he
  have hcen3 : s3.center = s'.center := scanSeg_center P qq first delay hseg3
  have hcenE : (afterCompare s3 vs3 vq3).center = s'.center := by rw [afterCompare_center, hcen3]
  -- the counters after the rounds
  have hprepStart : Canonical (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq).radius ∧
      Canonical (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq).length := by
    rw [afterCompare_radius, afterCompare_length]
    exact ⟨inc_canonical _ hrc, inc_canonical _ (inc_canonical _ hlc)⟩
  obtain ⟨_, _, _, hrc2, hlc2⟩ := watchSegE_heads P qq first delay hprepSeg
  obtain ⟨hrc1, hlc1⟩ := watchSeg_counters P qq first delay hseg
  obtain ⟨_, hrt, hlt⟩ := shift_run_canonical (shiftRun_of_chain hchain)
    ⟨ofNat_canonical h, inc_canonical _ (hrc1 (hrc2 hprepStart.1)),
      inc_canonical _ (inc_canonical _ (hlc1 (hlc2 hprepStart.2)))⟩
  obtain ⟨_, hlcS'⟩ := rounds_counters P qq first delay h hrounds hrt hlt
  obtain ⟨_, hlcS3⟩ := scanSeg_counters P qq first delay hseg3
  refine ⟨rfl, ?_, ?_, ?_, hrr3, ?_, rfl, rfl, hcanon, ((positive_iff _ hcanon).1 hlast).le⟩
  · show GalilScaffoldInputTrace.Represents (afterCompare s3 vs3 vq3).center.head _
    rw [hcenE]; exact hrep
  · show (afterCompare s3 vs3 vq3).center.head.focus ≠ none
    rw [hcenE]; exact hfoc
  · show ScanInvariant _ (position (afterCompare s3 vs3 vq3).center) _ (afterCompare s3 vs3 vq3).left
      (afterCompare s3 vs3 vq3).right
    rw [hcenE, hposS]
    have e1 : org.center + m*h + h = org.center + (m+1)*h := by ring
    rw [e1]; exact hinv
  · show Canonical (afterCompare s3 vs3 vq3).length
    rw [afterCompare_length]
    exact inc_canonical _ (inc_canonical _ (hlcS3 hlcS'))

#print axioms life_restarted

end PalPeg.GalilScaffoldChainInputSupply
