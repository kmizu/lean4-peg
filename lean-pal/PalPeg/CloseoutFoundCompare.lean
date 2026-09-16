import PalPeg.CloseoutContracts
import PalPeg.GalilReplayBudgetProof
import PalPeg.GalilPrepConstruct
import PalPeg.GalilCatchUpDistance
import PalPeg.GalilFoundLandingL
import PalPeg.GalilNoShiftDischarge
import PalPeg.GalilNoShiftStage
import PalPeg.GalilBreakTerminal

/-!
# The comparison-tick found leaf of the closeout

A found answer read at a **comparison** tick (`c'.clock = 1`, arrival bit
`true`, the chain idle, the letters matching) has to leave the cycle through
`CloseoutContracts.FoundExit`.  This file assembles that leaf out of the parts
the development already proves, and names — with their exact types — the pieces
that do not close.

Genuinely derived here:

* the **stage datum at the found state**: `StageEntryC.stage` gives
  `ReplayStage` at the *entry*, and `GalilFoundStageInv.replayStage_trans`
  carries it along the `WatchSegE` of the `SegReachedW`, so the restart `r₀`,
  its radius `Rad`, its lower bound `last` and the clock-`2048` segment control
  `c₀` are available at the found tick;
* the **search datum**: `GalilReplayBudgetProof.found_stage_data` on exactly
  that restart segment — the DP candidate for the block length `n`, `1 ≤ n`,
  and `value t.radius ≤ 2 * n`;
* the **preparation segment**:
  `GalilPrepConstruct.prep_segment_construct_of_found` over the post-comparison
  state, giving the `2h+2`-tick `WatchSegE`, the fresh watch chain, and the
  transport of the heads, the centre and the radius.

Open, as NAMED hypotheses with exact types:

* `PrepInputs` — the search machine's own quanta at the found tick
  (`SafeQuanta`/`Result`), the chain match, and "every candidate semiperiod fits
  in one delay".  These live inside the DP and are exported by no lemma
  reachable from `InvLPS`.
* `RoundsExit` / `BreakExit` — the two continuations after the preparation.  The
  rounds branch is `GalilCatchUpDistance.stageEntry_after_found_of_rounds`
  followed by `GalilFoundLandingL.foundRouteMC_shift`; the break branch is the
  `hcont` of `GalilNoShiftDischarge.foundRouteMC_noshift_d` together with
  `GalilNoShiftStage.fresh_break_stage` and
  `GalilBreakTerminal.hend3_of_matched_break`.  Both existing routes conclude in
  `InvLP`, whereas `FoundExit` demands the full landing record
  (`MInv`/`Restarted`/`FoundResidual`/`SpanRep`, resp.
  `InvLP2`/`CentreRep`/`ReplayStage`); that upgrade is the open part.  Each is
  stated over the *derived* preparation segment, never over an arbitrary state.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutFoundCompare

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton PalPeg.GalilInvPlus PalPeg.GalilInvPlus3
open PalPeg.GalilFoundStage PalPeg.GalilFoundStageInv
open PalPeg.GalilScaffoldChainInputSupply (Decodes)
open PalPeg.GalilBranchInvariants (AnswerAhead)
open PalPeg.GalilInvPlus2 (CentreRep)
open PalPeg.CloseoutContracts

/-! ## 1. The named search-machine datum at the found tick -/

/-- **NAMED hypothesis 1.**  The search machine's record of the found answer, in
exactly the shape `GalilPrepConstruct.prep_segment_construct_of_found` consumes.
`cP`/`sP` are the control and the state **after** the comparison tick, so no
premise is placed on a state other than the one the preparation starts from. -/
def PrepInputs (P : Shared) (qq : ℕ) (first : Fin 9) (p : GalilScaffoldPlace.Place)
    (lower span : ℕ) (cP : Control) (sP : GalilVM) : Prop :=
  ∃ (sq tq : GalilScaffoldSearchFinish.State) (x y : GalilScaffoldControl.Machine 12)
    (as : List Bool),
    GalilScaffoldSearchRun.SafeQuanta sq x as tq y ∧ sq.mode = .run ∧ tq.mode = .found ∧
    GalilDpCorrect.Result ((GalilScaffoldPlace.stream p).take (span+1)) lower 0
      (GalilScaffoldProgram.denote y.config) ∧
    cP.mode = .scan ∧ cP.replaying = false ∧ cP.clock = 2048 ∧
    (∀ cen : Fin 3, GalilScaffoldPlace.read p = some cen →
      ChainMatched (chainStart (y.config.tapes 11) cen p sP.center sP.radius) sP.chain) ∧
    (∀ k : ℕ, GalilDpCorrect.Candidate ((GalilScaffoldPlace.stream p).take (span+1)) lower k →
      2*k+2 < 2048)

/-- The preparation segment, **derived** from `PrepInputs`: the `2h+2`-tick
watched segment out of the post-comparison state, with the fresh watch chain and
the transport of the heads, the centre and the radius. -/
theorem prep_of_prepInputs (P : Shared) (qq : ℕ) (first : Fin 9)
    (p : GalilScaffoldPlace.Place) (lower span : ℕ) {cP : Control} {sP : GalilVM}
    (h : PrepInputs P qq first p lower span cP sP) :
    ∃ (hh : ℕ) (bs cs : List Bool) (dm : Bool) (c2 : Control) (s2 : GalilVM),
      GalilDpCorrect.Candidate ((GalilScaffoldPlace.stream p).take (span+1)) lower hh ∧
      WatchSegE P qq first 2048 (bs ++ dm :: cs) cP sP c2 s2 ∧
      bs.length = hh ∧ cs.length = hh+1 ∧ dm = false ∧
      (∃ ww : GalilScaffoldChainWatch.State, s2.chain = ChainVM.watch ww) ∧
      c2.mode = .scan ∧ c2.replaying = false ∧ c2.output = cP.output ∧
      2048 - (2*hh+2) ≤ c2.clock ∧ c2.clock ≤ 2048 ∧
      s2.left = sP.left ∧ s2.right = sP.right ∧ s2.center = sP.center ∧
      s2.radius = sP.radius ∧ s2.length = sP.length ∧ s2.periodOnly = sP.periodOnly ∧
      s2.replay = sP.replay ∧ searchLens.get s2 = searchLens.get sP := by
  obtain ⟨sq, tq, x, y, as, hrq, hsq, htq, hv, hm, hr, hclk, hchv, hfit⟩ := h
  exact GalilPrepConstruct.prep_segment_construct_of_found P qq first 2048 p rfl hrq hsq htq hv
    sP.center sP.radius cP sP hm hr hclk hchv hfit

/-! ## 2. The two named continuations -/

/-- **NAMED hypothesis 2 (the rounds branch).**  After the preparation the
machine shifts by the candidate semiperiod and runs `m` rounds plus a final
`ScanSeg` (`stageEntry_after_found_of_rounds` → `foundRouteMC_shift`).  Its
landing is assumed to carry the full `FoundExit.landed` record — the part
`foundRouteMC_shift`, which stops at `InvLP`, does not supply. -/
def RoundsExit (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ)
    (c : Control) (r : GalilVM) (cP : Control) (sP : GalilVM) : Prop :=
  ∀ (hh : ℕ) (es : List Bool) (c2 : Control) (s2 : GalilVM),
    WatchSegE P q first 2048 es cP sP c2 s2 → es.length = 2*hh+2 →
    (∃ ww : GalilScaffoldChainWatch.State, s2.chain = ChainVM.watch ww) →
    ∃ (cT : Control) (sT : GalilVM) (k : ℕ) (L : List GalilTraceCost.Piece),
      StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩ ∧
      GalilTraceCost.CostedRun r sT k L ∧
      MInv raw cT sT ∧ (∃ (Rad : ℕ) (last : Counter), Restarted raw sT Rad last) ∧
      FoundResidual raw cT sT ∧ SpanRep sT ∧
      position r.center < position sT.center ∧ position sT.right ≤ 2 * m - 1

/-- **NAMED hypothesis 3 (the break branch).**  The `hcont` of
`foundRouteMC_noshift_d`: the watched segment after the preparation ends in a
matched comparison whose chain breaks (`fresh_break_stage`,
`hend3_of_matched_break`), and its landing is assumed to carry the
`FoundExit.broke` record — including the `ReplayStage` datum, which the break
landing does not export on its own. -/
def BreakExit (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ)
    (c : Control) (r : GalilVM) (cP : Control) (sP : GalilVM) : Prop :=
  ∀ (hh : ℕ) (es : List Bool) (c2 : Control) (s2 : GalilVM),
    WatchSegE P q first 2048 es cP sP c2 s2 → es.length = 2*hh+2 →
    (∃ ww : GalilScaffoldChainWatch.State, s2.chain = ChainVM.watch ww) →
    ∃ (cT : Control) (sT : GalilVM) (k : ℕ) (L : List GalilTraceCost.Piece),
      StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩ ∧
      GalilTraceCost.CostedRun r sT k L ∧
      GalilInvPlus2.InvLP2 raw cT sT ∧ CentreRep raw sT ∧
      ReplayStage raw P q first cT sT ∧
      position sT.center = position r.center ∧ position r.right < position sT.right ∧
      position sT.right ≤ 2 * m - 1

/-! ## 3. The leaf -/

/-- **The comparison-tick found leaf.**  Entry `StageEntryC`, one watched segment
`SegReachedW` to the comparison tick, the found answer, the position bound; exit
`FoundExit`. -/
theorem foundExit_of_compare (centreC : GalilVM → Fin 3)
    (placeC : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (m : ℕ) (hP : Decodes (PofC centreC placeC entry w))
    {c c' cP : Control} {r t sP : GalilVM}
    (hE : StageEntryC (PofC centreC placeC entry w) q first w c r)
    (hsW : SegReachedW centreC placeC entry q first w c r c' t)
    (hcl : c'.clock = 1) (hav : canRight t.right) (hidle : t.chain = .idle)
    (hmt : read (left t.left) = read (right t.right))
    (a : Fin 2) (ls rs qq : List (Fin 2)) (gap : Bool)
    (hcen : t.center = represent ⟨a :: ls, gap⟩ (rs.map some) qq)
    (vq : SearchVM) (hq : searchEffect (PofC centreC placeC entry w) true t vq)
    (hfound : vq.search.mode = .found)
    {n : ℕ} (han : AnswerAhead (vq.dp.config.tapes 11) n)
    (hpos : position t.right ≤ 2 * m - 2)
    {lower span : ℕ}
    (hprep : PrepInputs (PofC centreC placeC entry w) q first ⟨a :: ls, gap⟩ lower span cP sP)
    (hbranch : RoundsExit (PofC centreC placeC entry w) q first w m c r cP sP ∨
      BreakExit (PofC centreC placeC entry w) q first w m c r cP sP) :
    FoundExit (PofC centreC placeC entry w) q first w m c r := by
  classical
  -- the stage datum, carried from the entry to the found state
  obtain ⟨-, es, hseg⟩ := hsW
  have hstage : ReplayStage w (PofC centreC placeC entry w) q first c' t :=
    replayStage_trans hE.stage hseg
  obtain ⟨r0, Rad, last, es0, c0, hR0, hSt0, hcl0, hseg0⟩ := hstage
  -- the search datum of the found answer: candidate, block length, radius bound
  have hdata := GalilReplayBudgetProof.found_stage_data (PofC centreC placeC entry w) q first hP
    a ls rs qq gap hR0 (by rw [← watchSegE_center _ _ _ _ hseg0]; exact hcen) hcl0 hSt0
    hseg0 hidle hcl vq hq hfound han
  obtain ⟨⟨lo, sp, hcand⟩, hn1, hrad⟩ := hdata
  -- the preparation segment out of the post-comparison state
  obtain ⟨hh, bs, cs, dm, c2, s2, hc, hseg2, hbs, hcs, hdm, hwatch, -, -, -, -, -, -, -, -, -,
    -, -, -, -⟩ := prep_of_prepInputs (PofC centreC placeC entry w) q first ⟨a :: ls, gap⟩
      lower span hprep
  have hlen : (bs ++ dm :: cs).length = 2*hh+2 := by
    simp only [List.length_append, List.length_cons, hbs, hcs]
    omega
  rcases hbranch with hro | hbr
  · obtain ⟨cT, sT, k, L, hst, hcr, hM, hR, hres, hSpan, hprog, hp⟩ :=
      hro hh (bs ++ dm :: cs) c2 s2 hseg2 hlen hwatch
    exact .landed cT sT k L hst hcr hM hR hres hSpan hprog hp
  · obtain ⟨cT, sT, k, L, hst, hcr, hIT, hcenT, hstg, hcc, hlt, hp⟩ :=
      hbr hh (bs ++ dm :: cs) c2 s2 hseg2 hlen hwatch
    exact .broke cT sT k L hst hcr hIT hcenT hstg hcc hlt hp

end PalPeg.CloseoutFoundCompare

#print axioms PalPeg.CloseoutFoundCompare.prep_of_prepInputs
#print axioms PalPeg.CloseoutFoundCompare.foundExit_of_compare
