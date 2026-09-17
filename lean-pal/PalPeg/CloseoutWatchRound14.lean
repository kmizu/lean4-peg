import PalPeg.CloseoutWatchRound6
import PalPeg.CloseoutWatchRound10
import PalPeg.CloseoutWatchRound13

/-!
# Round 14: the watch-phase tails assembled, and `foundExit_compare_final7`

Round 5 cut the two terminal tails of the watch round into state-local pieces,
Round 7 cut the shift round at its mismatching landing and the break terminal at
its per-landing round step, and Round 10 rebuilt the break family over the
*ledger* landing.  What was missing was the composition: a statement that
produces `CloseoutWatchPhase2.ShiftTailC` and
`CloseoutWatchPhase3.NoShiftTailC0L` from the named per-landing pieces alone,
and a re-derivation of `CloseoutWatchRound6.foundExit_compare_final6` on those
pieces instead of on the two monolithic tails.

## What is proved here (unconditionally, no `sorry`)

1. `foundCentre_eq` — **`hpr` discharged.**  `position r.center =
   position sF.center` at the found comparison is `watchSegE_center`: the
   preparation prefix does not move the centre tape.  (Round 10 uses this inline
   inside `foundDpBreakC_of_at`; here it is the standalone fact the shift-side
   consumers ask for.)
2. `shiftTailC_of_parts` — **`ShiftTailC` from the per-landing pieces.**
   `CloseoutWatchRound7.shiftRoundC_of_parts` turns `ShiftReachC` +
   `ShiftRoundAtC` into `CloseoutWatchRound5.ShiftRoundC`,
   `CloseoutWatchRound10.foundDpShiftC_of_at` supplies `FoundDpShiftC` from
   `FoundDpAtC` + `ReplayStage`, and `CloseoutWatchRound5.shiftExitTailC_of_parts`
   assembles the tail; the exit's own `FoundCompareCtxC` and `TerminalRunShiftC`
   are applied here, so the conclusion is the bare `ShiftTailC`.
3. `noShiftTailC0L_of_parts` — **`NoShiftTailC0L` from the per-landing pieces.**
   Same shape on the break side: `CloseoutWatchRound7.breakTerminalC_of_roundStep`
   builds `BreakTerminalC` from the per-landing `RoundStepC … BreakTermData`,
   `foundDpBreakC_of_at` supplies `FoundDpBreakC`, and
   `CloseoutWatchRound10.breakExitTailLC_of_parts` (whose margin conjunct is
   `margin_false_of_run`) assembles the ledger tail.
4. `breakRouteLPraw_of_parts` — 3 composed with
   `CloseoutWatchPhase3.breakRouteLPraw_of_tail0L`: the raw break route straight
   from the pieces.
5. `foundExit_compare_final7` — **`foundExit_compare_final6` with both tails
   replaced by the per-landing pieces.**  The watch side now asks only for
   `RightCanC` / `RightSaneC` / `StartLeC` / `LedgerOriginC` / `ZeroLagAtMatchC` /
   `DistanceNonnegC` / `PeriodMatchC` / `ExitSplitC` (unchanged), plus the seven
   per-landing contracts `PrepLandingWatchC`, `FoundDpAtC`, `ShiftReachC`,
   `ShiftRoundAtC`, `BreakLandingC`, the break round step, and `ReplayStage` —
   `CompareKeepsWatchC` is *derived* here (`caughtAtMatchC_of_zeroLag` +
   `predictC_of_match` + `compareKeepsWatchC_of_reach`), so it is no longer an
   input.  The entry data (`StageEntryC`, `SegReachedW`, `LandingRestartReach`,
   `PrepInputsG3`, `MismatchExitG`, `FoundCompareCtxC`) is unchanged.

## Attempted and NOT closed, with the exact missing fact

* **`CloseoutWatchPhase2.LandingRestartReach`.**  `landingRestart_of_inv` says
  the statement *is* `Inv.rest` + `Inv.stage`, and both route theorems do build
  that `Inv` internally at their landing `foundLandingVM (afterCompare s3 vs3 vq3)
  w3' entry` (`GalilFoundLandingL.foundRouteMC_shift`, the `hInv` there).  But
  both theorems **existentially quantify the landing and export only `InvLP`**,
  and no lemma in the tree re-derives `Restarted` at an arbitrary `InvLP` state
  reached from the entry: `landingRestart_of_break` needs the *whole* found-cycle
  tail (`hpo`, `hzv`, `hee`, `hrounds`, `hseg3`, the matched break), which the
  reach statement does not carry.  **Missing fact (one sentence):** a variant of
  `GalilFoundLandingL.foundRouteMC_shift` / `GalilInvPlus2.foundRouteMC_noshift''`
  that exports `Inv raw cT sT` (equivalently `Restarted raw sT Rad last ∧
  StageEntry Rad last`) at the landing it already constructs, instead of only
  `InvLP` / `InvLP2`.
* **Every preparation landing has `es.length ≤ 2*h+2`.**
  `CloseoutPrepInputs3.prep_of_prepInputsG3` branch A produces *one* landing with
  `es.length = 2*hh+2`; the statement quantifies over all landings.  **Missing
  fact (one sentence):** landing determinism for `WatchSegE` — from
  `WatchSegE P q first 2048 es cP sP c2 s2` and
  `WatchSegE P q first 2048 es' cP sP c2' s2'` with `es'.length ≤ es.length`,
  that `es'` is a prefix of `es` (so no landing is longer than the constructed
  one), which no lemma in the tree provides.

* **`CloseoutWatchRound7.ShiftRoundAtC`** (the shift round at the mismatching
  landing) is *not* closed by `CloseoutWatchRound9` + `CloseoutWatchRound11`.
  `roundOne_of_segRun` produces either a terminal `ScanSeg` or a single
  `Rounds … 1` step, whereas `ShiftRoundData` asks for `Rounds … h mm` followed
  by a terminal `ScanSeg` with a *matched breaking* comparison and, on top of the
  run, the origin data (`org.interior.length + 1 = h`, `Entry`, `org.center =
  position sF.center`, `Aligned`, the period lower bound) and the three break
  counters.  **Missing fact (one sentence):** an iteration of
  `GalilSegmentConstruct3.rounds_construct_of_measure` whose round invariant
  carries the `Entry`/`Aligned` origin across rounds and whose `RoundEnd` is
  restricted to the `BreakEnd` branch, which no lemma in the tree states.
  `CloseoutWatchRound11.watchPhase_or_report` supplies only the last conjunct
  (the terminal head bound), and even that under its own NAMED `hfit`.
* **`CloseoutWatchRound5.BreakTerminalC` from `TerminalC` / `BreakEndC`.**
  `BreakEndC` records a clock-`1` landing whose *outer symbols disagree*
  (`read (left s1.left) ≠ read (right s1.right)`), while `BreakTermData` needs a
  landing whose comparison is `matched` and whose chain tick lands on
  `ChainVM.broken` (the `ChainMatched.breaks` side of a *matched* outer
  comparison).  **Missing fact (one sentence):** that the break family of exits
  reaches such a matched-but-chain-breaking comparison — i.e. exactly the
  per-landing `RoundStepC … BreakTermData` that `breakTerminalC_of_roundStep`
  takes as input and that is left as a hypothesis of `noShiftTailC0L_of_parts`
  and `foundExit_compare_final7` below.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

namespace PalPeg.CloseoutWatchRound14

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton PalPeg.GalilInvPlus PalPeg.GalilInvPlus2
open PalPeg.GalilFoundStage PalPeg.GalilTraceCost
open PalPeg.CloseoutContracts
open PalPeg.CloseoutWatchRun (LiveScanWatch roundFuel)
open PalPeg.CloseoutWatchPhase2 (ShiftTailC LandingRestartReach BreakRouteLPraw)
open PalPeg.CloseoutWatchPhase3 (NoShiftTailC0L)
open PalPeg.CloseoutWatchRound2 (FoundCompareCtxC)
open PalPeg.CloseoutWatchRound3 (TerminalRunShiftC TerminalRunBreakC ExitSplitC
  DistanceNonnegC CompareKeepsWatchC)
open PalPeg.CloseoutWatchRound5 (PrepLandingLiveC FoundDpShiftC FoundDpBreakC
  BreakTerminalC ShiftRoundC)
open PalPeg.CloseoutWatchRound7 (PrepLandingWatchC ShiftReachC ShiftRoundAtC BreakTermData)
open PalPeg.CloseoutWatchRound10 (BreakLandingLedgerC FoundDpAtC)

/-! ## 1. `hpr`: the centre of the found comparison is the centre of the entry -/

/-- **Derived — `hpr`.**  A `WatchSegE` never moves the centre tape
(`watchSegE_center`), so the found comparison sits at the entry's centre. -/
theorem foundCentre_eq (P : Shared) (qq : ℕ) (first : Fin 9) {es0 : List Bool}
    {c0 cF : Control} {r sF : GalilVM}
    (hseg0 : WatchSegE P qq first 2048 es0 c0 r cF sF) :
    position r.center = position sF.center := by
  rw [watchSegE_center P qq first 2048 hseg0]

/-! ## 2. The shift tail -/

/-- **Derived — `ShiftTailC` from the per-landing pieces.** -/
theorem shiftTailC_of_parts (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m h lower span : ℕ)
    (hP : Decodes (PofC centre place entry raw))
    {c0 cP : Control} {r sP : GalilVM}
    (hst : ReplayStage raw (PofC centre place entry raw) qq first c0 r)
    (hlive : PrepLandingLiveC (PofC centre place entry raw) qq first cP sP)
    (hat : FoundDpAtC centre place entry qq first raw lower span h c0 r)
    (hreach : ShiftReachC centre place entry qq first raw h)
    (hround : ShiftRoundAtC centre place entry qq first raw m h lower)
    (hctx : FoundCompareCtxC centre place entry qq first raw c0 r cP sP)
    (hrun : TerminalRunShiftC (PofC centre place entry raw) qq first h cP sP) :
    ShiftTailC centre place entry qq first raw m c0 r cP sP :=
  PalPeg.CloseoutWatchRound5.shiftExitTailC_of_parts centre place entry qq first raw m h
    lower span hlive
    (PalPeg.CloseoutWatchRound10.foundDpShiftC_of_at centre place entry qq first raw hP
      lower span h hst hat)
    (PalPeg.CloseoutWatchRound7.shiftRoundC_of_parts centre place entry qq first raw m h lower
      hreach hround)
    hctx hrun

/-! ## 3. The break tail, over the ledger landing -/

/-- **Derived — `NoShiftTailC0L` from the per-landing pieces.** -/
theorem noShiftTailC0L_of_parts (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m h lower span : ℕ)
    (hP : Decodes (PofC centre place entry raw))
    {c0 cP : Control} {r sP : GalilVM}
    (hst : ReplayStage raw (PofC centre place entry raw) qq first c0 r)
    (hkeep : CompareKeepsWatchC (PofC centre place entry raw) qq first)
    (hnn : DistanceNonnegC)
    (hlive : PrepLandingLiveC (PofC centre place entry raw) qq first cP sP)
    (hat : FoundDpAtC centre place entry qq first raw lower span h c0 r)
    (hland : ∀ sF : GalilVM, BreakLandingLedgerC centre place entry qq first raw h sF cP sP)
    (hstep : ∀ (c : Control) (s : GalilVM), LiveScanWatch c s →
      PalPeg.CloseoutWatchRun.RoundStepC (PofC centre place entry raw) qq first (roundFuel h)
        (BreakTermData centre place entry qq first raw m h) c s)
    (hctx : FoundCompareCtxC centre place entry qq first raw c0 r cP sP)
    (hrun : TerminalRunBreakC (PofC centre place entry raw) qq first h cP sP) :
    NoShiftTailC0L centre place entry qq first raw m c0 r cP sP :=
  PalPeg.CloseoutWatchRound10.breakExitTailLC_of_parts centre place entry qq first raw m h
    lower span hkeep hnn hlive
    (PalPeg.CloseoutWatchRound10.foundDpBreakC_of_at centre place entry qq first raw hP
      lower span h hst hat)
    hland
    (PalPeg.CloseoutWatchRound7.breakTerminalC_of_roundStep centre place entry qq first raw m h
      hstep)
    hctx hrun

/-- **Derived — the raw break route straight from the pieces.** -/
theorem breakRouteLPraw_of_parts (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m h lower span : ℕ)
    (hP : Decodes (PofC centre place entry raw))
    (hex : ∀ s, (PofC centre place entry raw).replayExhausted s = zero s.replay)
    {c0 cP : Control} {r sP : GalilVM}
    (hE : StageEntryC (PofC centre place entry raw) qq first raw c0 r)
    (hst : ReplayStage raw (PofC centre place entry raw) qq first c0 r)
    (hkeep : CompareKeepsWatchC (PofC centre place entry raw) qq first)
    (hnn : DistanceNonnegC)
    (hlive : PrepLandingLiveC (PofC centre place entry raw) qq first cP sP)
    (hat : FoundDpAtC centre place entry qq first raw lower span h c0 r)
    (hland : ∀ sF : GalilVM, BreakLandingLedgerC centre place entry qq first raw h sF cP sP)
    (hstep : ∀ (c : Control) (s : GalilVM), LiveScanWatch c s →
      PalPeg.CloseoutWatchRun.RoundStepC (PofC centre place entry raw) qq first (roundFuel h)
        (BreakTermData centre place entry qq first raw m h) c s)
    (hctx : FoundCompareCtxC centre place entry qq first raw c0 r cP sP)
    (hrun : TerminalRunBreakC (PofC centre place entry raw) qq first h cP sP) :
    BreakRouteLPraw (PofC centre place entry raw) qq first raw m c0 r cP sP :=
  PalPeg.CloseoutWatchPhase3.breakRouteLPraw_of_tail0L centre place entry qq first raw m hex hE
    (noShiftTailC0L_of_parts centre place entry qq first raw m h lower span hP hst
      hkeep hnn hlive hat hland hstep hctx hrun)

/-! ## 4. `foundExit_compare_final6` on the per-landing pieces -/

open PalPeg.CloseoutWatchRound4 (LagStepC LedgerReachC ZeroLagAtMatchC)
open PalPeg.CloseoutWatchRound6 (RightCanC RightSaneC StartLeC LedgerOriginC PeriodMatchC)
open PalPeg.CloseoutPrepInputs2 (MismatchExitG)
open PalPeg.CloseoutPrepInputs3 (PrepInputsG3)

/-- **Derived — `CloseoutWatchRound6.foundExit_compare_final6` re-derived on the
per-landing pieces.**  The two monolithic tails `ShiftExitTailC` /
`BreakExitTailC` are gone, replaced by `PrepLandingWatchC`, `FoundDpAtC`,
`ShiftReachC`, `ShiftRoundAtC`, `BreakLandingC` and the per-landing break round
step; `CompareKeepsWatchC` is derived here from `ZeroLagAtMatchC` +
`PeriodMatchC` + the ledger, so it is not an input.

**Remaining hypotheses**, in groups:
* frame: `hP`, `hex`, `hready`;
* scan side: `hcan`, `hsane`, `hstart`;
* ledger: `hor`, `hzl`, `hnn`, `hpm`;
* entry data: `hE`, `hsW`, `hLR` (see the header: `LandingRestartReach` is the
  one contract this round could *not* close), `hprep`, `hmis`, `hctx`;
* classifier: `hsplit`;
* per-landing watch data: `hstage` (`ReplayStage`), `hmP`/`hrP`/`hcP`
  (the preparation entry's control), `hwatch` (`PrepLandingWatchC`), `hat`
  (`FoundDpAtC`), `hreach` / `hround` (the shift round), `hland` /
  `hstepBreak` (the break landing and its round step). -/
theorem foundExit_compare_final7 (centre : GalilVM → Fin 3)
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
    (hLR : LandingRestartReach (PofC centre place entry w) q first w c r)
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
    FoundExit (PofC centre place entry w) q first w m c r :=
  have hstp : LagStepC := PalPeg.CloseoutWatchRound6.lagStepC_of_parts hcan hsane hstart
  have hre : LedgerReachC :=
    PalPeg.CloseoutWatchRound6.ledgerReachC_of_origin centre place entry q first 2048 w hstp hor
  have hled := PalPeg.CloseoutWatchRound4.watchLedgerC_of_reach hstp hre
  have hkeep : CompareKeepsWatchC (PofC centre place entry w) q first :=
    PalPeg.CloseoutWatchRound6.compareKeepsWatchC_of_reach (PofC centre place entry w) q first
      hstp hre hled (PalPeg.CloseoutWatchRound4.caughtAtMatchC_of_zeroLag hled hzl)
      (PalPeg.CloseoutWatchRound6.predictC_of_match hled hzl hpm)
  have hlive : PrepLandingLiveC (PofC centre place entry w) q first cP sP :=
    PalPeg.CloseoutWatchRound7.prepLandingLiveC_of_watch (PofC centre place entry w) q first
      hmP hrP hcP hwatch
  PalPeg.CloseoutWatchRound6.foundExit_compare_final6 centre place entry q first w m h
    hP hex hready hcan hsane hstart hor hzl hnn hpm hE hsW hLR a ls rs qw gap hprep hmis hctx
    hsplit
    (PalPeg.CloseoutWatchRound5.shiftExitTailC_of_parts centre place entry q first w m h
      lower span hlive
      (PalPeg.CloseoutWatchRound10.foundDpShiftC_of_at centre place entry q first w hP
        lower span h hstage hat)
      (PalPeg.CloseoutWatchRound7.shiftRoundC_of_parts centre place entry q first w m h lower
        hreach hround))
    (PalPeg.CloseoutWatchRound5.breakExitTailC_of_parts centre place entry q first w m h
      lower span hkeep hnn hlive
      (PalPeg.CloseoutWatchRound10.foundDpBreakC_of_at centre place entry q first w hP
        lower span h hstage hat)
      hland
      (PalPeg.CloseoutWatchRound7.breakTerminalC_of_roundStep centre place entry q first w m h
        hstepBreak))

end PalPeg.CloseoutWatchRound14

#print axioms PalPeg.CloseoutWatchRound14.foundCentre_eq
#print axioms PalPeg.CloseoutWatchRound14.shiftTailC_of_parts
#print axioms PalPeg.CloseoutWatchRound14.noShiftTailC0L_of_parts
#print axioms PalPeg.CloseoutWatchRound14.breakRouteLPraw_of_parts
#print axioms PalPeg.CloseoutWatchRound14.foundExit_compare_final7
