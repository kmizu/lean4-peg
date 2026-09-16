import PalPeg.GalilScaffoldTopLifeRestart

/-!
# One turn of the main loop: from a found state to the next

`life_restarted` (the found tick, the chain's life, the restart) followed by
`restarted_next_found` (the chain-idle search segment and the next found
comparison). The static premises of `found_life` (`FoundReady`) are
re-established at the next found state, with the DP result of its search
when it is the first stage's `found`.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

theorem found_to_found (P : Shared) (qq : ℕ) (first : Fin 9) (delay : ℕ)
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
    (dm : Bool) (entry : ℕ) (hres : ∀ s t, restartVM entry s t → P.restart s t)
    (hP : Decodes P) (hd : delay = 2048) :
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
        -- the next search: a chain-idle segment and the found comparison
        (hstage : ∀ (Rad k : ℕ), value (afterCompare s3 vs3 vq3).radius = Rad →
          value w3'.machine.control.last = k → 3 * Rad ≤ 5 * k)
        {es1 : List Bool} {c1' : Control} {s1' : GalilVM}
        (hseg' : WatchSegE P qq first 2048 es1 {c3 with clock := delay, output := o3, replaying := false}
          {(afterCompare s3 vs3 vq3) with chain := .idle, lower := w3'.machine.control.last, search := GalilScaffoldSearchFinish.begin w3'.machine.control.last (afterCompare s3 vs3 vq3).radius, dp := GalilScaffoldControl.reset entry (afterCompare s3 vs3 vq3).dp} c1' s1')
        (hs1' : s1'.chain = .idle) (hpos' : 0 < (value (afterCompare s3 vs3 vq3).radius).toNat + es1.count true)
        (hc1' : c1'.clock = 1) (vq'' : SearchVM)
        (hq'' : searchEffect P true s1' vq'') (hfound' : vq''.search.mode = .found),
      (∃ k : ℕ, Steps (galilFrameS P qq first) delay k ⟨cF, sF⟩ ⟨c1', s1'⟩) ∧
      FoundReady P ((a :: ls).reverse ++ (rs ++ q)) s1' ∧
      ((s1'.search.mode = .run ∧
        ∃ (a' : Fin 2) (ls' rs' q' : List (Fin 2)) (gap' : Bool) (k : ℕ),
          s1'.center = represent ⟨a' :: ls',gap'⟩ (rs'.map some) q' ∧
          value w3'.machine.control.last = k ∧
          (∃ dpv, vq''.dp = ⟨dpv, true⟩ ∧
            GalilDpCorrect.Result ((GalilScaffoldPlace.stream ⟨a' :: ls',gap'⟩).take (8*max k 1+1)) k 0
              (GalilScaffoldProgram.denote dpv)) ∧
          (∀ (rad' : Counter), Canonical rad' → ∀ (r0 : ℕ), value rad' = r0 → 0 < r0 → ∀ (sm dm : Bool),
            ∃ (h : ℕ) (ys : List (Fin 3)) (b : Fin 3),
              GalilDpCorrect.Candidate ((GalilScaffoldPlace.stream ⟨a' :: ls',gap'⟩).take (8*max k 1+1)) k h ∧
              ys.length+1 = h)) ∨
       (∃ (L : ℕ) (vL : SearchVM), L ≤ es1.length ∧
          SearchRun (P.place {(afterCompare s3 vs3 vq3) with chain := .idle, lower := w3'.machine.control.last, search := GalilScaffoldSearchFinish.begin w3'.machine.control.last (afterCompare s3 vs3 vq3).radius, dp := GalilScaffoldControl.reset entry (afterCompare s3 vs3 vq3).dp}) (es1.take L)
            (searchLens.get {(afterCompare s3 vs3 vq3) with chain := .idle, lower := w3'.machine.control.last, search := GalilScaffoldSearchFinish.begin w3'.machine.control.last (afterCompare s3 vs3 vq3).radius, dp := GalilScaffoldControl.reset entry (afterCompare s3 vs3 vq3).dp}) vL ∧
          vL.search.mode ≠ .run ∧ vL.search.mode ≠ .found)) := by
  obtain ⟨h, ys, b, hcand, hys, hlife⟩ := life_restarted P qq first delay a ls rs q gap hmF hrF hcF havF
    hidle hcen R hscan hR hrc hlc hRpos vq hq hrun hfound span lower hv hcentre hplace hmt ch hch oF hoF
    dm entry hres
  refine ⟨h, ys, b, hcand, hys, ?_⟩
  intro bs cs hbs hcs c2 s2 hprepSeg c1 s1 hseg hm1 hr1 hc1 w hs1 hphase hz hav vs vq' hcmp hmis hq'
    predicted hpred hread hg s2' hb hs2' hi2 t' v cycle hchain o ho m c' s' hrounds hcenter n c3 s3
    hseg3 hm3 hr3 hc3 w3 hs3 hav3 vs3 vq3 hcmp3 hmt3 hq3 hend3 w3' hbr3 o3 ho3 hstage es1 c1' s1'
    hseg' hs1' hpos' hc1' vq'' hq'' hfound'
  obtain ⟨⟨k1, hst⟩, Rad, hRst⟩ := hlife bs cs hbs hcs hprepSeg hseg hm1 hr1 hc1 w hs1 hphase hz hav vs
    vq' hcmp hmis hq' predicted hpred hread hg s2' hb hs2' hi2 hchain o ho hrounds hcenter hseg3 hm3 hr3
    hc3 w3 hs3 hav3 vs3 vq3 hcmp3 hmt3 hq3 hend3 w3' hbr3 o3 ho3
  subst hd
  obtain ⟨k2, hst2⟩ := watchSegE_steps P qq first 2048 hseg'
  have hRad : value (afterCompare s3 vs3 vq3).radius = Rad := hRst.2.2.2.2.1.2
  have hpos'' : 0 < Rad + es1.count true := by
    have : (value (afterCompare s3 vs3 vq3).radius).toNat = Rad := by rw [hRad]; simp
    rw [this] at hpos'; exact hpos'
  obtain ⟨hready, hout⟩ := restarted_next_found P qq first hP hRst rfl
    (fun k hk => hstage Rad k hRad hk) hseg' hs1' hpos'' hc1' vq'' hq'' hfound'
  refine ⟨⟨_, steps_trans hst hst2⟩, hready, ?_⟩
  rcases hout with ⟨hrun', a', ls', rs', q', gap', k, hcen', hk, hdp, hcand'⟩ | hexit
  · exact Or.inl ⟨hrun', a', ls', rs', q', gap', k, hcen', hk, hdp, hcand'⟩
  · exact Or.inr hexit

#print axioms found_to_found

end PalPeg.GalilScaffoldChainInputSupply
