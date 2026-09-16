import PalPeg.GalilScaffoldTopFirstRound

/-!
# A chain's life on the controller

From the found search: the watch period and first shift (`first_round`),
`m` full re-shift rounds (`rounds_lift`), a final matched segment and the
breaking terminal comparison (`rounds_break`). The whole is a run of
`galilFrameS`, and at the broken state the restart entry conditions hold
with the centre advanced by `(m+1)` half periods from the found centre.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

theorem chain_life (P : Shared) (qq : ℕ) (first : Fin 9) (delay : ℕ)
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
    ∀ (h : ℕ) (ys : List (Fin 3)) (b : Fin 3),
      GalilDpCorrect.Candidate ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (span+1)) lower h →
      ys.length+1 = h →
      ∀ (copyMatches backMatches : List Bool), copyMatches.length = h → backMatches.length = h+1 →
      ∀ (initialRadius : ℕ) (hlag : GalilScaffoldCounter.value (watchStart cen c ys b (GalilScaffoldChainCredits.run (GalilScaffoldChainCredits.start radius) (GalilScaffoldChainCredits.prepEvents sm dm copyMatches backMatches))).lag = initialRadius)
        -- the watch period
        {c0 c1 : Control} {v0 s1 : GalilVM} (hseg : WatchSeg P qq first delay c0 v0 c1 s1)
        (hchain0 : v0.chain = .watch (watchStart cen c ys b (GalilScaffoldChainCredits.run (GalilScaffoldChainCredits.start radius) (GalilScaffoldChainCredits.prepEvents sm dm copyMatches backMatches)))) (hcen0 : v0.center = cen)
        (hrad0 : value v0.radius = initialRadius) (hrc0 : Canonical v0.radius)
        (hlc0 : Canonical v0.length)
        (hi0 : ScanInvariant ((a :: ls).reverse ++ (rs ++ q)) (position cen) initialRadius v0.left v0.right)
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
      (∃ k : ℕ, Steps (galilFrameS P qq first) delay k ⟨c0, v0⟩
          ⟨{c3 with clock := delay, output := o3, replaying := false}, afterCompare s3 vs3 vq3⟩) ∧
        w3' = GalilScaffoldChainWatch.immediate w3 ∧ (afterCompare s3 vs3 vq3).chain = .broken w3' ∧
        ∃ org : ReadOrigin ((a :: ls).reverse ++ (rs ++ q)), org.interior.length+1 = h ∧ org.center = position cen ∧
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
  intro h ys b hcand hys
  have hrest := first_round P qq first delay a ls rs q gap cen hcen c hc span lower hr hs ht hv
    radius hrc hrp sm dm h ys b hcand hys
  intro copyMatches backMatches hcl hbl initialRadius hlag c0 c1 v0 s1 hseg hchain0 hcen0
    hrad0 hrc0 hlc0 hi0 hm1 hr1 hc1 w hs1 hphase hz hav vs vq hcmp hmis hq predicted hpred hread
    hg s2 hb hs2 hi2 t' v cycle hchain o ho m c' s' hrounds hcenter n c3 s3 hseg3 hm3 hr3 hc3 w3 hs3
    hav3 vs3 vq3 hcmp3 hmt3 hq3 hend3 w3' hbr3 o3 ho3
  obtain ⟨⟨k1, hst1⟩, hev, hzv, hpo, o', he, hint, hocen, hshifts, _⟩ :=
    hrest copyMatches backMatches hcl hbl initialRadius hlag hseg hchain0 hcen0 hrad0 hrc0 hlc0 hi0
      hm1 hr1 hc1 w hs1 hphase hz hav vs vq hcmp hmis hq predicted hpred hread hg s2 hb hs2 hi2
      hchain o ho
  obtain ⟨⟨k2, hst2⟩, hw3, hbroken, hres⟩ := rounds_break P qq first delay h hrounds v hpo hev hzv
    hseg3 hm3 hr3 hc3 w3 hs3 hav3 vs3 vq3 hcmp3 hmt3 hq3 hend3 w3' hbr3 o3 ho3
  refine ⟨⟨_, steps_trans hst1 hst2⟩, hw3, hbroken, o', hint, hocen, hshifts, he, ?_⟩
  exact hres _ o' hint he hcenter

#print axioms chain_life

end PalPeg.GalilScaffoldChainInputSupply
