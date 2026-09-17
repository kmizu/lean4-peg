import PalPeg.CloseoutWatchRound14

/-!
# Round 15: the landing invariant carried out of the found routes

Round 14 closed everything the watch phase needed except one contract,
`CloseoutWatchPhase2.LandingRestartReach`, and named the exact missing fact:

> a variant of `GalilFoundLandingL.foundRouteMC_shift` /
> `GalilInvPlus2.foundRouteMC_noshift''` that exports `Inv raw cT sT`
> (equivalently `Restarted raw sT Rad last ∧ StageEntry Rad last`) at the
> landing it already constructs, instead of only `InvLP` / `InvLP2`.

That fact is now available: `GalilFoundLandingL.foundRouteMC_shift_Inv`,
`GalilFoundLandingL.foundRouteMC_noshift_Inv`,
`GalilInvPlus2.foundRouteMC_noshift'_Inv` and
`GalilInvPlus2.foundRouteMC_noshift''_Inv` are the four originals with the
landing's full `Inv` pack — which every one of those proofs already builds
before weakening it to `InvLP` — added to the conclusion.

## What is proved here (unconditionally, no `sorry`)

1. `roundsRouteLP_of_tail` — **the shift route past the sharpening, with no
   `LandingRestartReach`.**  `CloseoutWatchPhase2.roundsRouteLPraw_of_tail` run
   on `foundRouteMC_shift_Inv`: the landing's `LandingRestart` comes from
   `CloseoutWatchPhase2.landingRestart_of_inv` applied to the pack the route
   itself hands back, so the reach statement is not consulted.
2. `breakRouteLP_of_tail` — the same on the break side, through
   `foundRouteMC_noshift''_Inv`.
3. `watchRouteLP_of_tails'` — `CloseoutWatchPhase3.watchRouteLP_of_tails`
   without its `hLR` argument.
4. `foundExit_compare_final8` — **`foundExit_compare_final7` with `hLR`
   removed.**  The hypothesis list is that of Round 14 minus
   `LandingRestartReach`; the composition is
   `Round3.terminalTailsC'_of_split` + `Round2.terminalC'_of_align` +
   3 + `CloseoutPrepInputs3.foundExit_of_compare3`, i.e. Round 2/3/4/6's own
   composition re-run on the `hLR`-free route.

## Attempted and NOT closed, with the exact missing fact

* **`LandingRestartReach` itself.**  As stated it quantifies over *every*
  `InvLP` landing reachable from the cycle entry, whereas the `_Inv` routes
  export the pack at the *one* landing they construct.  Closing the `∀`-form
  needs determinism of `StepsAll (galilFrameS …) 2048 (SoundScanNR raw)` out of
  a fixed state — **missing fact (one sentence):** that two sound runs of the
  same length from `⟨c, r⟩` end at the same state, which no lemma in the tree
  states (and which is false as stated for the relational `compare` /
  `searchEffect` steps unless they are first shown functional).  1–4 above make
  the contract unnecessary for the watch phase instead of proving it: every
  consumer of `LandingRestartReach` inside `foundExit_compare_final7` uses it
  exactly at a landing one of the routes produced.
  `CloseoutWatchPhase2.mismatchExitG_of_raw` (the *fallback* sibling) still
  takes it; `foundExit_compare_final8` therefore still takes `MismatchExitG`
  itself as an input, as Round 14 did.
* **Weakening `CloseoutWatchRound2.TerminalRunC` to an existential landing.**
  `TerminalRunC` is *already* closed unconditionally — `terminalRunC_of_align`
  discharges the `∀ es, WatchSegE … → …` form without ever looking at the
  segment — so there is nothing to weaken there.  The `es.length ≤ 2*h+2`
  problem named in Round 14's header lives one layer down, in the `∀ es`
  quantifier of `ShiftTailC` / `NoShiftTailC0` / `RoundsRouteLPraw`, and that
  quantifier cannot be weakened to an existential here: its consumer
  `CloseoutFoundCompare.RoundsExit` (and `BreakExit`) is itself stated with
  `∀ (hh : ℕ) (es : List Bool) …`, in a file this round may not edit.
  **Missing fact (one sentence):** an existential-landing restatement of
  `CloseoutFoundCompare.RoundsExit` / `BreakExit`, or landing determinism for
  `WatchSegE` (from two landings of the same preparation with `es'.length ≤
  es.length`, that `es'` is a prefix of `es`), neither of which the tree has.
* **The three-way exit split.**  Splitting `CloseoutWatchRound3.ExitSplitC`
  into shift / matched chain break / outer mismatch needs the third branch to
  route a `BreakEndC` landing (outer symbols *disagree*) into the prep-time
  fallback.  The fallback route available at this point,
  `CloseoutWatchPhase2.FallbackRouteLP`, is consumed only through
  `mismatchExitG_of_raw`, i.e. it produces `MismatchExitG` — which
  `foundExit_compare_final7/8` already take as an input `hmis` covering the
  *preparation* mismatch, not a mismatch discovered after the rounds.
  **Missing fact (one sentence):** a `FoundExit` route from a post-rounds
  `BreakEndC` landing (a scan-mode, clock-`1`, `canRight` state whose outer
  symbols disagree and whose chain is a watch, reached by `WatchSeg` from the
  preparation landing) back to `CloseoutPrepInputs3.FallbackRouteG`, which
  requires `GalilPrepMatch.PrepChain` of a *watching* chain and is not
  available: `FallbackRouteLP` asks for `PrepChain s1.chain`, and no lemma in
  the tree derives `PrepChain` from `s.chain = ChainVM.watch w`.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

namespace PalPeg.CloseoutWatchRound15

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton PalPeg.GalilInvPlus PalPeg.GalilInvPlus2
open PalPeg.GalilFoundStage PalPeg.GalilTraceCost
open PalPeg.CloseoutContracts
open PalPeg.CloseoutWatchRun (LiveScanWatch roundFuel)
open PalPeg.CloseoutWatchPhase2 (ShiftTailC NoShiftTailC LandingRestartReach
  landingRestart_of_inv)
open PalPeg.CloseoutWatchPhase3 (NoShiftTailC0 noShiftTailC_of_0)
open PalPeg.CloseoutWatchRound2 (FoundCompareCtxC TerminalC' terminalC'_of_align)
open PalPeg.CloseoutWatchRound3 (TerminalRunShiftC TerminalRunBreakC ExitSplitC
  DistanceNonnegC CompareKeepsWatchC)
open PalPeg.CloseoutWatchRound5 (PrepLandingLiveC)
open PalPeg.CloseoutWatchRound7 (PrepLandingWatchC ShiftReachC ShiftRoundAtC BreakTermData)
open PalPeg.CloseoutWatchRound10 (FoundDpAtC)

/-! ## 1. The two routes, past the sharpening, with no reach statement -/

/-- **Derived — the shift route with its `LandingRestart`.**  The proof of
`CloseoutWatchPhase2.roundsRouteLPraw_of_tail`, run on
`GalilFoundLandingL.foundRouteMC_shift_Inv`; the extra `Inv` the route exports
is turned into the missing conjunct by `landingRestart_of_inv`. -/
theorem roundsRouteLP_of_tail (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m : ℕ)
    (hex : ∀ s, (PofC centre place entry raw).replayExhausted s = zero s.replay)
    {c0 cP : Control} {r sP : GalilVM}
    (hE : StageEntryC (PofC centre place entry raw) qq first raw c0 r)
    (htail : ShiftTailC centre place entry qq first raw m c0 r cP sP) :
    PalPeg.CloseoutWatchPhase.RoundsRouteLP (PofC centre place entry raw) qq first raw m
      c0 r cP sP := by
  classical
  obtain ⟨a, ls, rs, qw, gap, es0, cF, sF, vq, ch, oF, lower, span, hraw, hseg0, hmF, hrF, hcF,
    havF, hidle, hCen, hq, hfound, hmt, hch, hchne, hoF, hcPeq, hsPeq, hdp, hpc, htl⟩ := htail
  subst hcPeq
  subst hsPeq
  intro hh es c2 s2 hprepSeg hlen hw
  obtain ⟨c1, s1, h, w, vs, vq', s2', t', v, cycle, o, org, mm, c', s', n, c3, s3, w3, vs3, vq3,
    o3, w3', hseg, hm1, hr1, hc1, hs1, hz, hav, hcmp, hmis, hq', hg, hb, hs2', hi2, hchain, ho,
    hint, he, hoc, ha, hpos11, hlow, hrounds, hseg3, hm3, hr3, hc3, hs3, hav3, hcmp3, hmt3, hq3,
    ho3, hbroken, hmargin, hlast, hlag, hbound⟩ := htl es c2 s2 hprepSeg
  obtain ⟨cT, sT, k, L, hst, hcr, hLP, hprog, hright, hInv⟩ :=
    PalPeg.GalilFoundLandingL.foundRouteMC_shift_Inv centre place entry qq first raw hex
      (PalPeg.GalilOracleMC2.invLPC_invLP hE.invLPC)
      (PalPeg.GalilOracleLeaves2.hlive_of_invLPC centre place entry qq first hE.invLPC)
      a ls rs qw gap hraw hseg0 hmF hrF hcF havF hidle hCen vq hq hfound hmt ch hch hchne oF hoF
      hprepSeg hseg h hm1 hr1 hc1 w hs1 hz hav vs vq' hcmp hmis hq' hg s2' hb hs2' hi2 hchain o ho
      org hint he hoc ha hdp hpc hpos11 hlow hrounds hseg3 hm3 hr3 hc3 w3 hs3 hav3 vs3 vq3 hcmp3
      hmt3 hq3 o3 ho3 w3' hbroken hmargin hlast hlag
  refine ⟨cT, sT, k, L, hst, hcr, hLP, landingRestart_of_inv hInv, hprog, ?_⟩
  rw [hright]
  exact hbound

/-- **Derived — the break route with its `LandingRestart`**, through
`GalilInvPlus2.foundRouteMC_noshift''_Inv`. -/
theorem breakRouteLP_of_tail (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m : ℕ)
    (hex : ∀ s, (PofC centre place entry raw).replayExhausted s = zero s.replay)
    {c0 cP : Control} {r sP : GalilVM}
    (hE : StageEntryC (PofC centre place entry raw) qq first raw c0 r)
    (htail : NoShiftTailC centre place entry qq first raw m c0 r cP sP) :
    PalPeg.CloseoutWatchPhase.BreakRouteLP (PofC centre place entry raw) qq first raw m
      c0 r cP sP := by
  classical
  obtain ⟨es0, cF, sF, vq, ch, oF, hseg0, hmF, hrF, hcF, havF, hidle, hq, hfound, hmt, hch,
    hchne, hoF, hcPeq, hsPeq, htl⟩ := htail
  subst hcPeq
  subst hsPeq
  intro hh es c2 s2 hprepSeg hlen hw
  obtain ⟨cen, ys, b, c3, s3, w3, vs3, vq3, o3, w3', hwatch2, hes0, hpal1, hpal2, hseg, hm3, hr3,
    hc3, hs3, hav3, hcmp3, hmt3, hq3, ho3, hbroken, hmargin, hbound⟩ := htl es c2 s2 hprepSeg
  obtain ⟨cT, sT, k, L, hst, hcr, hLP2, hc, hlt, hright, hInv⟩ :=
    PalPeg.GalilInvPlus2.foundRouteMC_noshift''_Inv centre place entry qq first raw hex hE.invLPC
      (PalPeg.GalilOracleLeaves2.hlive_of_invLPC centre place entry qq first hE.invLPC)
      hseg0 hmF hrF hcF havF hidle vq hq hfound hmt ch hch hchne oF hoF hprepSeg cen ys b hwatch2
      hes0 hpal1 hpal2 hseg hm3 hr3 hc3 w3 hs3 hav3 vs3 vq3 hcmp3 hmt3 hq3 o3 ho3 w3' hbroken
      hmargin
  refine ⟨cT, sT, k, L, hst, hcr, hLP2, landingRestart_of_inv hInv, hc, hlt, ?_⟩
  rw [hright]
  exact hbound

/-- **Derived — `CloseoutWatchPhase3.watchRouteLP_of_tails` with no `hLR`.** -/
theorem watchRouteLP_of_tails' (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m : ℕ)
    (hex : ∀ s, (PofC centre place entry raw).replayExhausted s = zero s.replay)
    {c0 cP : Control} {r sP : GalilVM}
    (hE : StageEntryC (PofC centre place entry raw) qq first raw c0 r)
    (htail : ShiftTailC centre place entry qq first raw m c0 r cP sP ∨
      NoShiftTailC centre place entry qq first raw m c0 r cP sP) :
    PalPeg.CloseoutWatchPhase.RoundsRouteLP (PofC centre place entry raw) qq first raw m
        c0 r cP sP ∨
    PalPeg.CloseoutWatchPhase.BreakRouteLP (PofC centre place entry raw) qq first raw m
        c0 r cP sP := by
  rcases htail with hs | hn
  · exact Or.inl (roundsRouteLP_of_tail centre place entry qq first raw m hex hE hs)
  · exact Or.inr (breakRouteLP_of_tail centre place entry qq first raw m hex hE hn)

/-! ## 2. `foundExit_compare_final7` without `LandingRestartReach` -/

open PalPeg.CloseoutWatchRound4 (LagStepC LedgerReachC ZeroLagAtMatchC)
open PalPeg.CloseoutWatchRound6 (RightCanC RightSaneC StartLeC LedgerOriginC PeriodMatchC)
open PalPeg.CloseoutPrepInputs2 (MismatchExitG)
open PalPeg.CloseoutPrepInputs3 (PrepInputsG3 foundExit_of_compare3)

/-- **Derived — `CloseoutWatchRound14.foundExit_compare_final7` with `hLR`
removed.**  Every hypothesis is Round 14's, minus
`CloseoutWatchPhase2.LandingRestartReach`: the two landings the watch phase
actually reaches now carry their own `Inv` out of the route theorems, so the
uniform reach statement is never consulted. -/
theorem foundExit_compare_final8 (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (m h lower span : ℕ)
    (hP : Decodes (PofC centre place entry w))
    (hex : ∀ s, (PofC centre place entry w).replayExhausted s = zero s.replay)
    (hready : PalPeg.GalilReplayChainSeg.ChainTickable)
    (hcan : RightCanC) (hsane : RightSaneC) (hstart : StartLeC)
    (hor : LedgerOriginC centre place entry q first 2048 w)
    (hzl : ZeroLagAtMatchC) (hnn : DistanceNonnegC) (hpm : PeriodMatchC)
    {c c' cP : Control} {r t sP : GalilVM}
    (hE : StageEntryC (PofC centre place entry w) q first w c r)
    (hsW : SegReachedW centre place entry q first w c r c' t)
    (a : Fin 2) (ls rs qw : List (Fin 2)) (gap : Bool)
    (hprep : PrepInputsG3 (PofC centre place entry w) q first ⟨a :: ls, gap⟩ lower span cP sP)
    (hmis : MismatchExitG (PofC centre place entry w) q first w m c r cP sP)
    (hctx : FoundCompareCtxC centre place entry q first w c r cP sP)
    (hsplit : ExitSplitC centre place entry q first w h cP sP)
    (hstage : ReplayStage w (PofC centre place entry w) q first c r)
    (hmP : cP.mode = .scan) (hrP : cP.replaying = false) (hcP : 1 ≤ cP.clock)
    (hwatch : PrepLandingWatchC (PofC centre place entry w) q first cP sP)
    (hat : FoundDpAtC centre place entry q first w lower span h c r)
    (hreach : ShiftReachC centre place entry q first w h)
    (hround : ShiftRoundAtC centre place entry q first w m h lower)
    (hland : ∀ sF : GalilVM,
      PalPeg.CloseoutWatchRound5.BreakLandingC centre place entry q first w h sF cP sP)
    (hstepBreak : ∀ (c0 : Control) (s0 : GalilVM), LiveScanWatch c0 s0 →
      PalPeg.CloseoutWatchRun.RoundStepC (PofC centre place entry w) q first (roundFuel h)
        (BreakTermData centre place entry q first w m h) c0 s0) :
    FoundExit (PofC centre place entry w) q first w m c r := by
  classical
  -- the ledger, exactly as in Round 14
  have hstp : LagStepC := PalPeg.CloseoutWatchRound6.lagStepC_of_parts hcan hsane hstart
  have hre : LedgerReachC :=
    PalPeg.CloseoutWatchRound6.ledgerReachC_of_origin centre place entry q first 2048 w hstp hor
  have hled := PalPeg.CloseoutWatchRound4.watchLedgerC_of_reach hstp hre
  have hcaught := PalPeg.CloseoutWatchRound4.caughtAtMatchC_of_zeroLag hled hzl
  have hpred := PalPeg.CloseoutWatchRound6.predictC_of_match hled hzl hpm
  have havail := PalPeg.CloseoutWatchRound6.landingCanRightC_of_reach hstp hre
  have hkeep : CompareKeepsWatchC (PofC centre place entry w) q first :=
    PalPeg.CloseoutWatchRound6.compareKeepsWatchC_of_reach (PofC centre place entry w) q first
      hstp hre hled hcaught hpred
  have hlive : PrepLandingLiveC (PofC centre place entry w) q first cP sP :=
    PalPeg.CloseoutWatchRound7.prepLandingLiveC_of_watch (PofC centre place entry w) q first
      hmP hrP hcP hwatch
  -- the two tails, from the per-landing pieces (Round 14, §2–3)
  have hshift := PalPeg.CloseoutWatchRound5.shiftExitTailC_of_parts centre place entry q first w m h
    lower span hlive
    (PalPeg.CloseoutWatchRound10.foundDpShiftC_of_at centre place entry q first w hP
      lower span h hstage hat)
    (PalPeg.CloseoutWatchRound7.shiftRoundC_of_parts centre place entry q first w m h lower
      hreach hround)
  have hbreak := PalPeg.CloseoutWatchRound5.breakExitTailC_of_parts centre place entry q first w m h
    lower span hkeep hnn hlive
    (PalPeg.CloseoutWatchRound10.foundDpBreakC_of_at centre place entry q first w hP
      lower span h hstage hat)
    hland
    (PalPeg.CloseoutWatchRound7.breakTerminalC_of_roundStep centre place entry q first w m h
      hstepBreak)
  -- the terminal record and the classifier (Round 2 §5, Round 3 §5)
  have hT : TerminalC' centre place entry q first w h c r cP sP :=
    terminalC'_of_align centre place entry q first w h hready
      (PalPeg.CloseoutWatchRound3.matchTickC_of_parts hled hcaught hpred)
      (PalPeg.CloseoutWatchRound3.landingReadyC_of_parts hled havail hnn) hctx
  have htail : ShiftTailC centre place entry q first w m c r cP sP ∨
      NoShiftTailC centre place entry q first w m c r cP sP := by
    rcases PalPeg.CloseoutWatchRound3.terminalTailsC'_of_split centre place entry q first w m h
      c r cP sP hsplit hshift hbreak hT with hs | hn
    · exact Or.inl hs
    · exact Or.inr (noShiftTailC_of_0 centre place entry q first w m hn)
  -- the route, with no reach statement
  have hroute := watchRouteLP_of_tails' centre place entry q first w m hex hE htail
  have hbranch : PalPeg.CloseoutFoundCompare.RoundsExit (PofC centre place entry w) q first w m
        c r cP sP ∨
      PalPeg.CloseoutFoundCompare.BreakExit (PofC centre place entry w) q first w m c r cP sP := by
    rcases hroute with hro | hbr
    · exact Or.inl (PalPeg.CloseoutWatchPhase.roundsExit_of_LP hro)
    · exact Or.inr (PalPeg.CloseoutWatchPhase.breakExit_of_LP hbr)
  exact foundExit_of_compare3 centre place entry q first w m hP hE hsW a ls rs qw gap
    hprep hmis hbranch

end PalPeg.CloseoutWatchRound15

#print axioms PalPeg.CloseoutWatchRound15.roundsRouteLP_of_tail
#print axioms PalPeg.CloseoutWatchRound15.breakRouteLP_of_tail
#print axioms PalPeg.CloseoutWatchRound15.watchRouteLP_of_tails'
#print axioms PalPeg.CloseoutWatchRound15.foundExit_compare_final8
