import PalPeg.GalilNoShiftStage
import PalPeg.GalilPrepConstruct
import PalPeg.GalilCandidatePeriod
import PalPeg.GalilScaffoldTopSegmentFacts
import PalPeg.GalilScaffoldTopRoundBreak

/-!
# Discharging the extra hypotheses of the no-shift found route

`GalilNoShiftStage.foundRouteMC_noshift'` asks for the preparation landing
(`hwatch2`, `hes0`) and for two palindromes around the centre (`hpal1`,
`hpal2`). The landing is the output of `prep_segment_construct`, restated
here with an all-`false` event list (`prep_segment_construct_bg`), so the
comparison count is zero by computation; the palindromes are
`candidate_palAt` read through the centre head's representation. The
wrapper `foundRouteMC_noshift_d` takes the found data in the style of
`foundRouteMC_shift` (word split, centre representation, DP candidate,
copy/back data) and the continuation as a hypothesis over the landing.
-/

set_option autoImplicit false
namespace PalPeg.GalilNoShiftDischarge
open PalPeg GalilScaffoldCounter PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilNoShiftStage PalPeg.GalilPrepConstruct
open PalPeg.Program PalPeg.GalilStructuredSkeleton
open PalPeg.GalilRunSkeleton PalPeg.GalilOracleDischarge PalPeg.GalilOracleGlueB
open PalPeg.GalilGlueBLeaves PalPeg.GalilOracleLocal PalPeg.GalilInvPlus
open Manacher GalilScaffoldTop GalilScaffoldController GalilScaffoldInputHead
open GalilScaffoldChainVerifier
open PalPeg.GalilTraceCost PalPeg.GalilCostedFound PalPeg.GalilFoundLandingL

/-- `prep_segment_construct` with the event list made explicit: all `2h+2`
preparation ticks are background ticks. -/
theorem prep_segment_construct_bg (P : Shared) (qq : ℕ) (first : Fin 9) (delay : ℕ)
    (answer : GalilScaffoldTape.Tape) (cen : Fin 3) (p q' : GalilScaffoldPlace.Place)
    (ver : PlaceHead) (radius : Counter) (u : GalilScaffoldTape.Tape)
    (h : ℕ) (ys : List (Fin 3)) (b : Fin 3)
    (hcopy : GalilScaffoldChainPeriod.Copy answer reset p (GalilScaffoldChainPeriod.start cen) h u
      (ofNat h) q' (GalilScaffoldChainPeriod.fill (GalilScaffoldChainPeriod.start cen) (ys ++ [b])))
    (hu : u.focus = 4) (hpos : positive (ofNat h) = true)
    (hfocus : (GalilScaffoldChainPeriod.fill (GalilScaffoldChainPeriod.start cen)
      (ys ++ [b])).focus = .plain b)
    (hback : GalilScaffoldChainPeriod.Back (GalilScaffoldChainPeriod.write
      (GalilScaffoldChainPeriod.fill (GalilScaffoldChainPeriod.start cen) (ys ++ [b])) (.last b))
      (h+1) (GalilScaffoldChainPeriod.moveRight ⟨[], .first cen,
        ys.map GalilScaffoldChainPeriod.Token.plain ++ [.last b]⟩))
    (ch : ChainVM) (hch : ChainMatched (chainStart answer cen p ver radius) ch)
    (cF' : Control) (sF : GalilVM)
    (hm : cF'.mode = .scan) (hr : cF'.replaying = false) (hclk : cF'.clock = delay)
    (hchain : sF.chain = ch) (hh : 2*h+2 < delay) :
    ∃ (c2 : Control) (s2 : GalilVM),
      WatchSegE P qq first delay (List.replicate (2*h+2) false) cF' sF c2 s2 ∧
      s2.chain = ChainVM.watch ⟨⟨ver, GalilScaffoldChainConsume.ready cen ys b⟩,
        inc radius, GalilScaffoldChainCredits.decFour^[h] (inc radius)⟩ ∧
      c2.mode = .scan ∧ c2.replaying = false ∧ c2.output = cF'.output ∧
      delay - (2*h+2) ≤ c2.clock ∧ c2.clock ≤ delay ∧
      s2.left = sF.left ∧ s2.right = sF.right ∧ s2.center = sF.center ∧
      s2.radius = sF.radius ∧ s2.length = sF.length ∧ s2.periodOnly = sF.periodOnly ∧
      s2.replay = sF.replay ∧ searchLens.get s2 = searchLens.get sF := by
  cases hch with
  | copy _ _ _ _ _ _ _ =>
    have hrun := prep_chain_run answer cen p q' ver u h ys b (inc radius) (inc radius)
      hcopy hu hpos hfocus hback
    have hne : ChainVM.copy answer reset p (GalilScaffoldChainPeriod.start cen)
        (inc radius) (inc radius) ver ≠ ChainVM.idle := by
      intro hc; exact ChainVM.noConfusion hc
    obtain ⟨c2, s2, hseg, hchz, hm2, hr2, ho2, hlo, hhi, hl2, hr2', hc2, hrad2, hlen2, hpo2,
        hrep2, hget2⟩ :=
      background_segE_of_chainSteps P qq first delay hrun cF' sF hm hr hchain hne (by omega)
    exact ⟨c2, s2, hseg, hchz, hm2, hr2, ho2, by omega, by omega, hl2, hr2', hc2, hrad2, hlen2,
      hpo2, hrep2, hget2⟩

/-- The two palindromes of the no-shift route, from the DP candidate and the
centre head's representation. -/
theorem pal_of_candidate {raw : List (Fin 2)} (a : Fin 2) (ls rs q : List (Fin 2)) (gap : Bool)
    (span lower h : ℕ) (hraw : raw = (a :: ls).reverse ++ rs ++ q)
    (hc : GalilDpCorrect.Candidate
      ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (span+1)) lower h)
    {s : GalilVM} (hCen : s.center = represent ⟨a :: ls,gap⟩ (rs.map some) q) :
    PalAt (encoded raw) (position s.center - h) h ∧
      PalAt (encoded raw) (position s.center - 2*h) (2*h) := by
  subst hraw
  rw [hCen]
  exact candidate_palAt a ls rs q gap span lower h hc

/-- **The no-shift found route with its preparation and palindrome
hypotheses discharged.** The found data is given as in `foundRouteMC_shift`
(word split `hraw`, centre head `hCen`, DP candidate `hc`, copy/back data);
the continuation after the preparation is a hypothesis over the landing
`(c2, s2)` that the construction produces. -/
theorem foundRouteMC_noshift_d (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2))
    (hex : ∀ s, (PofC centre place entry raw).replayExhausted s = zero s.replay)
    {c0 : Control} {r : GalilVM} (hI : InvLP raw c0 r)
    (hlive : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (PofC centre place entry raw) qq first) 2048 m ⟨c0, r⟩ z →
      CentreLive z.ctl z.vm)
    (hcenS : ∀ k : ℕ, PalPeg.GalilReplaySegment.InvScan 2048 raw c0 r k →
      GalilScaffoldInputTrace.Represents r.center.head raw ∧ r.center.head.focus ≠ none)
    -- the word and the centre head at the found comparison
    (a : Fin 2) (ls rs q : List (Fin 2)) (gap : Bool)
    (hraw : raw = (a :: ls).reverse ++ rs ++ q)
    {es0 : List Bool} {cF : Control} {sF : GalilVM}
    (hseg0 : WatchSegE (PofC centre place entry raw) qq first 2048 es0 c0 r cF sF)
    (hmF : cF.mode = .scan) (hrF : cF.replaying = false)
    (hcF : cF.clock = 1) (havF : canRight sF.right) (hidle : sF.chain = .idle)
    (hCen : sF.center = represent ⟨a :: ls,gap⟩ (rs.map some) q)
    (vq : SearchVM) (hq : searchEffect (PofC centre place entry raw) true sF vq)
    (hfound : vq.search.mode = .found)
    (hmt : read (left sF.left) = read (right sF.right))
    -- the DP candidate and the copy/back data of the found answer
    (span lower h : ℕ) (cen : Fin 3) (p q' : GalilScaffoldPlace.Place)
    (u : GalilScaffoldTape.Tape) (ys : List (Fin 3)) (b : Fin 3)
    (hc : GalilDpCorrect.Candidate
      ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (span+1)) lower h)
    (hlen : ys.length + 1 = h)
    (hcopy : GalilScaffoldChainPeriod.Copy (vq.dp.config.tapes 11) reset p
      (GalilScaffoldChainPeriod.start cen) h u (ofNat h) q'
      (GalilScaffoldChainPeriod.fill (GalilScaffoldChainPeriod.start cen) (ys ++ [b])))
    (hu : u.focus = 4) (hpos : positive (ofNat h) = true)
    (hfocus : (GalilScaffoldChainPeriod.fill (GalilScaffoldChainPeriod.start cen)
      (ys ++ [b])).focus = .plain b)
    (hback : GalilScaffoldChainPeriod.Back (GalilScaffoldChainPeriod.write
      (GalilScaffoldChainPeriod.fill (GalilScaffoldChainPeriod.start cen) (ys ++ [b])) (.last b))
      (h+1) (GalilScaffoldChainPeriod.moveRight ⟨[], .first cen,
        ys.map GalilScaffoldChainPeriod.Token.plain ++ [.last b]⟩))
    (hh : 2*h+2 < 2048)
    -- the chain at the found comparison
    (ch : ChainVM)
    (hch : ChainMatched (chainStart (vq.dp.config.tapes 11) cen p sF.center sF.radius) ch)
    (hch' : ChainMatched (chainStart (vq.dp.config.tapes 11) ((PofC centre place entry raw).centre sF)
      ((PofC centre place entry raw).place sF) sF.center sF.radius) ch)
    (hchne : ch ≠ .idle) (oF : Bool)
    (hoF : refresh (galilFrame (PofC centre place entry raw) qq first)
      (afterBirth true (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq)) cF.output oF)
    -- the continuation after the preparation, over the landing it produces
    (hcont : ∀ (c2 : Control) (s2 : GalilVM),
      WatchSegE (PofC centre place entry raw) qq first 2048 (List.replicate (2*h+2) false)
        {cF with clock := 2048, output := oF, replaying := false}
        (afterBirth true (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq)) c2 s2 →
      s2.chain = .watch (freshWatch sF.center cen ys b sF.radius) →
      c2.mode = .scan → c2.replaying = false → c2.output = oF →
      2048 - (2*h+2) ≤ c2.clock → c2.clock ≤ 2048 →
      s2.left = (afterBirth true (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq)).left →
      s2.right = (afterBirth true (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq)).right →
      s2.center = (afterBirth true (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq)).center →
      s2.radius = (afterBirth true (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq)).radius →
      ∃ (c3 : Control) (s3 : GalilVM) (w3 : GalilScaffoldChainWatch.State) (vs3 : ScanVM)
        (vq3 : SearchVM) (o3 : Bool) (w3' : GalilScaffoldChainWatch.State),
        WatchSeg (PofC centre place entry raw) qq first 2048 c2 s2 c3 s3 ∧
        c3.mode = .scan ∧ c3.replaying = false ∧ c3.clock = 1 ∧
        s3.chain = .watch w3 ∧ GalilScaffoldCounter.zero w3.lag = true ∧ canRight s3.right ∧
        (galilFrame (PofC centre place entry raw) qq first).compare s3 (scanLens.set s3 vs3) ∧
        (galilFrame (PofC centre place entry raw) qq first).matched (scanLens.set s3 vs3) ∧
        searchEffect (PofC centre place entry raw) true s3 vq3 ∧
        refresh (galilFrame (PofC centre place entry raw) qq first)
          (afterCompare s3 vs3 vq3) c3.output o3 ∧
        (afterCompare s3 vs3 vq3).chain = .broken w3' ∧
        negative w3'.margin = false) :
    ∃ (cT : Control) (sT : GalilVM) (k : ℕ) (L : List Piece),
      StepsAll (galilFrameS (PofC centre place entry raw) qq first) 2048 (SoundScanNR raw) k
        ⟨c0, r⟩ ⟨cT, sT⟩ ∧
      CostedRun r sT k L ∧ InvLP raw cT sT ∧
      position sT.center = position r.center ∧ position r.right < position sT.right ∧
      ∃ (s3 : GalilVM) (vs3 : ScanVM) (vq3 : SearchVM),
        sT.right = (afterCompare s3 vs3 vq3).right := by
  classical
  have hchain : (afterBirth true (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq)).chain
      = ch := by
    rw [afterBirth_chain]; exact afterCompare_chain _ _ _
  obtain ⟨c2, s2, hseg2, hchz, hm2, hr2, ho2, hlo, hhi, hl2, hr2', hc2, hrad2, _, _, _, _⟩ :=
    prep_segment_construct_bg (PofC centre place entry raw) qq first 2048 (vq.dp.config.tapes 11)
      cen p q' sF.center sF.radius u h ys b hcopy hu hpos hfocus hback ch hch
      {cF with clock := 2048, output := oF, replaying := false}
      (afterBirth true (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq)) hmF rfl rfl hchain hh
  have hwatch2 : s2.chain = .watch (freshWatch sF.center cen ys b sF.radius) := by
    rw [hchz, freshWatch_eq _ _ _ _ _ h hlen]
  obtain ⟨c3, s3, w3, vs3, vq3, o3, w3', hseg, hm3, hr3, hc3, hs3, hz3, hav3, hcmp3, hmt3, hq3, ho3,
      hbroken, hmargin⟩ :=
    hcont c2 s2 hseg2 hwatch2 hm2 hr2 ho2 hlo hhi hl2 hr2' hc2 hrad2
  have hpal := pal_of_candidate a ls rs q gap span lower h hraw hc hCen
  have hcen0 : sF.center = r.center := watchSegE_center _ _ _ _ hseg0
  rw [hcen0, ← hlen] at hpal
  obtain ⟨cT, sT, k, L, hst, hcr, hIT, hcenT, hlt, hright⟩ :=
    foundRouteMC_noshift' centre place entry qq first raw hex hI hlive hcenS hseg0 hmF hrF hcF
      havF hidle vq hq hfound hmt ch hch' hchne oF hoF hseg2 cen ys b hwatch2 (List.count_eq_zero.2 (by simp))
      hpal.1 hpal.2 hseg hm3 hr3 hc3 w3 hs3 hz3 hav3 vs3 vq3 hcmp3 hmt3 hq3 o3 ho3 w3' hbroken hmargin
  exact ⟨cT, sT, k, L, hst, hcr, hIT, hcenT, hlt, s3, vs3, vq3, hright⟩

#print axioms prep_segment_construct_bg
#print axioms pal_of_candidate
#print axioms foundRouteMC_noshift_d

end PalPeg.GalilNoShiftDischarge
