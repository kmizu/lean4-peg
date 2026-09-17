import PalPeg.CloseoutWatchRound44

/-!
# Closeout watch round 45 — the landing lag leaf re-based on the corrected pieces

Round 44 refuted `LandingFreshC` (Round 41) and split it into the `h`-free
residue `LandingFreshC'` plus the period clause.  This round re-bases the
consumer on the corrected pieces:

* `period_of_beginShift` — the period clause is **not** a leaf at all: it is
  derivable from the route data, because `ShiftRoundDataL` carries both
  `P.beginShift s1' s2'` (i.e. `beginShiftVM (periodLength w₀) w₀ …` for some
  `w₀`) and `beginShiftVM h w' …`; the chain field identifies `w₀ = w'` and the
  `remaining` field gives `ofNat (periodLength w') = ofNat h`.  This is exactly
  Round 33's `h := periodLength w'` choice, recovered at the consumer.
* `PrepBirthLagC'` — `PrepBirthLagC` with the birth clause
  `value w0.machine.control.distance = 0` added (it is what `SumRel` needs at
  the birth end); `watchStart_distance_zero` shows the clause holds for every
  chain born through `watchStart`, so adding it costs nothing at the producer.
* `WatchDrainC'` — `WatchDrainC` with that distance-zero input and the
  consumer's `broken = false` added as hypotheses (without them the statement
  is false: `SumRel (.watch w') Rnow` is vacuous when broken, and unbroken it
  reads `distance w' + lag w'`).
* `mismatchLandingLagZeroL_of_ctx'` and `foundExit_compare_final17` — Round
  41's consumer and route with the corrected leaves.

Not discharged here: the bodies of `PrepBirthLagC'` (prep-segment transport of
`found_to_watchStart`/`prepEvents`) and `WatchDrainC'` (the radius-ledger
growth `Rnow = value w0.lag + m'` from the clock structure).

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

namespace PalPeg.CloseoutWatchRound45

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.CloseoutContracts
open PalPeg.GalilRunSkeleton PalPeg.GalilInvPlus PalPeg.GalilInvPlus2
open PalPeg.GalilFoundStage PalPeg.GalilTraceCost
open PalPeg.CloseoutWatchRun (LiveScanWatch roundFuel watchSeg_append)
open PalPeg.CloseoutWatchPhase2 (ShiftTailC)
open PalPeg.CloseoutWatchRound2 (FoundCompareCtxC)
open PalPeg.CloseoutWatchRound3 (DistanceNonnegC)
open PalPeg.CloseoutWatchRound5 (PrepLandingLiveC)
open PalPeg.CloseoutWatchRound6 (RightCanC RightSaneC StartLeC LedgerOriginC PeriodMatchC)
open PalPeg.CloseoutWatchRound4 (ZeroLagAtMatchC)
open PalPeg.CloseoutWatchRound7 (PrepLandingWatchC ShiftReachC ShiftRoundAtC BreakTermData)
open PalPeg.CloseoutWatchRound10 (FoundDpAtC)
open PalPeg.CloseoutPrepInputs2 (MismatchExitG)
open PalPeg.CloseoutPrepInputs3 (PrepInputsG3 foundExit_of_compare3)
open PalPeg.CloseoutWatchRound23 (MismatchGuardFails TerminalRunMismatchShiftC ExitSplit4C
  exitSplit4C_of_tick terminalRunFallbackC_of_G)
open PalPeg.CloseoutWatchRound30 (ShiftCopyIdleC MismatchClassifierTieC)
open PalPeg.CloseoutWatchRound2 (TerminalC' terminalC'_of_align)
open PalPeg.CloseoutWatchRound18 (ExitSplit3C)
open PalPeg.CloseoutWatchRound20 (watchPrefixC_of_unique)
open PalPeg.CloseoutWatchRound31 (FoundExitLPS FallbackReachS foundExit_compare_final9S')
open PalPeg.CloseoutWatchRound33 (ShiftRoundDataL ShiftRunCL)
open PalPeg.CloseoutWatchRound34 (ShiftBreakOracleC ShiftBreakFitC)
open PalPeg.CloseoutWatchRound37 (shiftRoundData_of_dataL MismatchShiftRouteL
  ShiftRoundInvCL ShiftOriginRestCL mismatchShiftRouteL_of_tick)
open PalPeg.CloseoutWatchRound39 (watchSegE_lag landing_lag_zero_of_budget)
open PalPeg.GalilChainCoupling (FreshC SumRel)
open PalPeg.CloseoutWatchRound41 (LandingL MismatchLandingLagZeroL PrepBirthLagC WatchDrainC
  shiftTailC_of_dataL')
open PalPeg.CloseoutWatchRound44 (LandingFreshC')

/-! ## 1. The period clause is derivable from the route data -/

/-- **The period clause, recovered.**  `Shared.beginShift` of `PofC` is
`beginShiftVM'`, i.e. it already says that the shift countdown is the
semiperiod of *some* watch; the route data additionally names the watch
(`beginShiftVM h w'`).  The two agree, so `periodLength w' = h`. -/
theorem period_of_beginShift (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry : ℕ) (raw : List (Fin 2))
    {h : ℕ} {w' : GalilScaffoldChainWatch.State} {s t : GalilVM}
    (hb : (PofC centre place entry raw).beginShift s t)
    (hs : beginShiftVM h w' s t) : periodLength w' = h := by
  obtain ⟨w0, hc0, he0⟩ := hb
  obtain ⟨hc1, he1⟩ := hs
  have hww : w0 = w' := ChainVM.watch.inj (hc0.symm.trans hc1)
  subst hww
  have hre := congrArg GalilVM.remaining (he0.symm.trans he1)
  exact ofNat_inj (by simpa using hre)

/-! ## 2. A chain born through `watchStart` has zero distance and is unbroken -/

theorem watchStart_distance_zero (cen : PlaceHead) (c : Fin 3) (ys : List (Fin 3)) (b : Fin 3)
    (final : GalilScaffoldChainCredits.State) :
    value (watchStart cen c ys b final).machine.control.distance
      = 0 := by
  simp [watchStart, GalilScaffoldChainConsume.ready, value, reset]

theorem watchStart_broken_false (cen : PlaceHead) (c : Fin 3) (ys : List (Fin 3)) (b : Fin 3)
    (final : GalilScaffoldChainCredits.State) :
    (watchStart cen c ys b final).machine.control.broken = false :=
  rfl

/-! ## 3. The corrected pieces -/

/-- **(2') NAMED — prep accounting, with the birth ledger clause.**  Identical
to `PrepBirthLagC` except that the birth state's consume distance is recorded
as zero (`watchStart_distance_zero`: free at the producer). -/
def PrepBirthLagC' (P : Shared) (q : ℕ) (first : Fin 9) (c0 : Control) (r : GalilVM)
    (cP : Control) (sP : GalilVM) : Prop :=
  ∀ (es0 : List Bool) (cF : Control) (sF : GalilVM) (vq : SearchVM) (ch : ChainVM)
    (a : Fin 2) (ls rs qw : List (Fin 2)) (gap : Bool),
    WatchSegE P q first 2048 es0 c0 r cF sF →
    sF.chain = ChainVM.idle → cF.clock = 1 →
    sF.center = represent ⟨a :: ls, gap⟩ (rs.map some) qw →
    searchEffect P true sF vq → vq.search.mode = .found →
    ChainMatched (chainStart (vq.dp.config.tapes 11) (P.centre sF) (P.place sF)
      sF.center sF.radius) ch →
    sP = afterBirth true (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq) →
    ∀ (c1 : Control) (s1 : GalilVM) (w : GalilScaffoldChainWatch.State),
      LandingL P q first cP sP c1 s1 → c1.clock = 1 → s1.chain = ChainVM.watch w →
      ∃ (m : ℤ) (w0 : GalilScaffoldChainWatch.State) (es2 : List Bool) (cb : Control)
        (sb : GalilVM),
        WatchSegE P q first 2048 es2 cb sb c1 s1 ∧ sb.chain = ChainVM.watch w0 ∧
        GalilScaffoldChainWatch.CanonicalState w0 ∧ 0 ≤ value w0.lag ∧
        value w0.machine.control.distance = 0 ∧
        value w0.lag = value sF.radius + m ∧ 0 ≤ m ∧
        2048 * m ≤ 2 * ((GalilScaffoldProgram.denote vq.dp.config).pos 11 : ℤ) + 2

/-- `PrepBirthLagC'` is a strengthening of `PrepBirthLagC` (the split is
faithful in the direction the consumer needs). -/
theorem prepBirthLagC_of_prime (P : Shared) (q : ℕ) (first : Fin 9) (c0 : Control) (r : GalilVM)
    (cP : Control) (sP : GalilVM) (hpr : PrepBirthLagC' P q first c0 r cP sP) :
    PrepBirthLagC P q first c0 r cP sP := by
  intro es0 cF sF vq ch a ls rs qw gap hseg hidle hcF hcen hq hf hch hsP c1 s1 w hland hc1 hw
  obtain ⟨m, w0, es2, cb, sb, h1, h2, h3, h4, -, h5, h6, h7⟩ :=
    hpr es0 cF sF vq ch a ls rs qw gap hseg hidle hcF hcen hq hf hch hsP c1 s1 w hland hc1 hw
  exact ⟨m, w0, es2, cb, sb, h1, h2, h3, h4, h5, h6, h7⟩

/-- **(3') NAMED — the watch clock structure, with the two missing inputs.**
`WatchDrainC` with the birth distance and the landing chain's unbrokenness as
hypotheses (Round 44: without them the statement is false). -/
def WatchDrainC' (P : Shared) (q : ℕ) (first : Fin 9) : Prop :=
  ∀ (es2 : List Bool) (cb c1 : Control) (sb s1 : GalilVM)
    (w0 w w' : GalilScaffoldChainWatch.State) (Rnow : ℤ),
    WatchSegE P q first 2048 es2 cb sb c1 s1 → sb.chain = ChainVM.watch w0 →
    value w0.machine.control.distance = 0 →
    w'.machine.control.broken = false →
    s1.chain = ChainVM.watch w → GalilScaffoldChainWatch.Internal w w' →
    SumRel (.watch w') Rnow →
    ∃ m' d1 : ℤ, 0 ≤ m' ∧ 0 ≤ d1 ∧ 2047 * m' + d1 ≤ (es2.count false : ℤ) ∧
      Rnow = value w0.lag + m'

/-- `WatchDrainC` (Round 41) implies the weakened `WatchDrainC'`. -/
theorem watchDrainC'_of_watchDrainC (P : Shared) (q : ℕ) (first : Fin 9)
    (hd : WatchDrainC P q first) : WatchDrainC' P q first := by
  intro es2 cb c1 sb s1 w0 w w' Rnow hseg hsb _ _ hw hint hs
  exact hd es2 cb c1 sb s1 w0 w w' Rnow hseg hsb hw hint hs

/-! ## 4. The leaf at the consumer level, re-based -/

/-- **Round 41's `mismatchLandingLagZeroL_of_ctx` with the corrected leaves.**
`LandingFreshC` (false) is replaced by `LandingFreshC'`; the period clause is
`period_of_beginShift` from the route data; `PrepBirthLagC'`/`WatchDrainC'`
carry the ledger input at the birth end. -/
theorem mismatchLandingLagZeroL_of_ctx' (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m lower : ℕ) {c0 cP : Control} {r sP : GalilVM}
    (hP : Decodes (PofC centre place entry raw))
    (hE : StageEntryC (PofC centre place entry raw) qq first raw c0 r)
    (h2 : PrepBirthLagC' (PofC centre place entry raw) qq first c0 r cP sP)
    (h3 : WatchDrainC' (PofC centre place entry raw) qq first)
    (h4 : LandingFreshC' (PofC centre place entry raw) qq first cP sP) :
    MismatchLandingLagZeroL centre place entry qq first raw m lower c0 r cP sP := by
  intro es0 cF sF vq ch a ls rs qw gap hseg0 hidle hcF hcen hq hfound hch hsPeq c1 s1 h hland
    hdL w hw
  obtain ⟨w1, w', vs, vq', s2', t', v, cycle, o, org, mm, c', s', n, c3, s3, w3, vs3, vq3, o3, w3',
    hm1, hr1, hc1, hw1, hint', hvs, hz, hav, hcmp, hmis, hq', hg, hb, hs2', hi2, hchain, ho, hint,
    he, hoc, ha, hpos11, hlow, hrounds, hseg3, hm3, hr3, hc3, hs3, hav3, hcmp3, hmt3, hq3, ho3,
    hbroken, hmargin, hlast, hlag3, hbound⟩ := hdL
  rw [hw] at hw1
  obtain rfl := ChainVM.watch.inj hw1
  have hg' : shiftGuardVM (afterMismatch s1 vs vq') := hg
  obtain ⟨w'', hw'', -, hph, hbr, -, -⟩ := hg'
  rw [afterMismatch_chain, hvs] at hw''
  obtain rfl := ChainVM.watch.inj hw''
  -- (1) the found-radius budget, from the stage entry
  obtain ⟨r', Rad, last, esPre, c0', hR, hSt, hcl, hsegPre⟩ := hE.stage
  have hsegAll := watchSegE_trans (PofC centre place entry raw) qq first 2048 hsegPre hseg0
  have hcen' : r'.center = represent ⟨a :: ls, gap⟩ (rs.map some) qw := by
    rw [← watchSegE_center (PofC centre place entry raw) qq first 2048 hsegAll]; exact hcen
  obtain ⟨k, h1, span, -, -, hpos1, hh1, hRf⟩ :=
    PalPeg.GalilReplayBudgetProof.found_radius_le_two_period (PofC centre place entry raw) qq
      first hP a ls rs qw gap hR hcen' hcl hSt hsegAll hidle hcF vq hq hfound
  have hh : h1 = h := hpos1.symm.trans hpos11
  subst hh
  -- (4') coupling at the landing, and the period from the route data
  obtain ⟨hcw, hf, Rnow, hs⟩ := h4 c1 s1 w w' hland hw hint'
  have hper : periodLength w' = h1 := period_of_beginShift centre place entry raw hb hs2'
  -- (2') the birth lag, with the ledger clause
  obtain ⟨mI, w0, es2, cb, sb, hseg2, hsb, hc0, hn0, hd0, hlag0, hm0, hm⟩ :=
    h2 es0 cF sF vq ch a ls rs qw gap hseg0 hidle hcF hcen hq hfound hch hsPeq c1 s1 w hland hc1 hw
  rw [hpos11] at hm
  -- (3') the drain supply
  obtain ⟨m', d1, hm'0, hd10, hk, hnow⟩ :=
    h3 es2 cb c1 sb s1 w0 w w' Rnow hseg2 hsb hd0 hbr hw hint' hs
  have hdrain := (watchSegE_lag (PofC centre place entry raw) qq first 2048 hseg2 hsb hw hc0 hn0).2
  rw [hlag0] at hdrain
  exact landing_lag_zero_of_budget hint' hz hcw hf hph hbr hs hper (value sF.radius) mI m' d1
    (k := es2.count false) hk hdrain (by omega) (by exact_mod_cast hh1) hRf hm hm0 hm'0 hd10

/-! ## 5. The route with the corrected leaves -/

/-- **`foundExit_compare_final16` with the corrected leaves.**  `LandingFreshC`
is gone (it is false); in its place `LandingFreshC'`, and the birth/drain
pieces carry the ledger input. -/
theorem foundExit_compare_final17 (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (m h lower span : ℕ) (μ : ℕ → Control → GalilVM → ℕ)
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
    (hfbS : FallbackReachS (PofC centre place entry w) q first w m c r cP sP)
    (hstage : ReplayStage w (PofC centre place entry w) q first c r)
    (hmP : cP.mode = .scan) (hrP : cP.replaying = false) (hcP : 1 ≤ cP.clock)
    (hwatch : PrepLandingWatchC (PofC centre place entry w) q first cP sP)
    (hat : FoundDpAtC centre place entry q first w lower span h c r)
    (hreach : ShiftReachC centre place entry q first w h)
    (hround : ShiftRoundAtC centre place entry q first w m h lower)
    (h3 : ShiftCopyIdleC) (h4 : ShiftRunCL)
    (hinv : ShiftRoundInvCL w)
    (horacle : ∀ h', ShiftBreakOracleC centre place entry q first w h' (μ h'))
    (hfit : ∀ h', ShiftBreakFitC centre place entry q first w m h')
    (hrest : ShiftOriginRestCL centre place entry q first w lower)
    (htie : MismatchClassifierTieC (PofC centre place entry w) q first)
    (hbirth : PrepBirthLagC' (PofC centre place entry w) q first c r cP sP)
    (hdrain : WatchDrainC' (PofC centre place entry w) q first)
    (hfresh : LandingFreshC' (PofC centre place entry w) q first cP sP)
    (hland : ∀ sF : GalilVM,
      PalPeg.CloseoutWatchRound5.BreakLandingC centre place entry q first w h sF cP sP)
    (hstepBreak : ∀ (c0 : Control) (s0 : GalilVM), LiveScanWatch c0 s0 →
      PalPeg.CloseoutWatchRun.RoundStepC (PofC centre place entry w) q first (roundFuel h)
        (BreakTermData centre place entry q first w m h) c0 s0) :
    FoundExitLPS (PofC centre place entry w) q first w m c r := by
  classical
  have hlag0 := mismatchLandingLagZeroL_of_ctx' centre place entry q first w m lower hP hE hbirth
    hdrain hfresh
  have hlive : PrepLandingLiveC (PofC centre place entry w) q first cP sP :=
    PalPeg.CloseoutWatchRound7.prepLandingLiveC_of_watch (PofC centre place entry w) q first
      hmP hrP hcP hwatch
  have hrouteL := mismatchShiftRouteL_of_tick centre place entry q first w m lower μ h3 h4 hinv
    horacle hfit hrest htie
  have hsplit4 : ExitSplit4C centre place entry q first w h cP sP :=
    exitSplit4C_of_tick centre place entry q first w h cP sP (hlive [] cP sP (.stop _ _))
      (watchPrefixC_of_unique _ _ _ _ _)
  have hstp := PalPeg.CloseoutWatchRound6.lagStepC_of_parts hcan hsane hstart
  have hre := PalPeg.CloseoutWatchRound6.ledgerReachC_of_origin centre place entry q first 2048 w
    hstp hor
  have hled := PalPeg.CloseoutWatchRound4.watchLedgerC_of_reach hstp hre
  have hcaught := PalPeg.CloseoutWatchRound4.caughtAtMatchC_of_zeroLag hled hzl
  have hpred := PalPeg.CloseoutWatchRound6.predictC_of_match hled hzl hpm
  have havail := PalPeg.CloseoutWatchRound6.landingCanRightC_of_reach hstp hre
  have hT : TerminalC' centre place entry q first w h c r cP sP :=
    terminalC'_of_align centre place entry q first w h hready
      (PalPeg.CloseoutWatchRound3.matchTickC_of_parts hled hcaught hpred)
      (PalPeg.CloseoutWatchRound3.landingReadyC_of_parts hled havail hnn) hctx
  have via3 : ∀ (hs3 : ExitSplit3C centre place entry q first w h cP sP),
      FoundExitLPS (PofC centre place entry w) q first w m c r := fun hs3 =>
    foundExit_compare_final9S' (h := h) (fun hsplit =>
      PalPeg.CloseoutWatchRound15.foundExit_compare_final8 centre place entry q first w m h
        lower span hP hex hready hcan hsane hstart hor hzl hnn hpm hE hsW a ls rs qw gap hprep
        hmis hctx hsplit hstage hmP hrP hcP hwatch hat hreach hround hland hstepBreak)
      hT.2 hs3 hfbS hlive
  rcases hsplit4 hT.2 with hs | hb | hf | hm
  · exact via3 (fun _ => Or.inl hs)
  · exact via3 (fun _ => Or.inr (Or.inl hb))
  · exact via3 (fun _ => Or.inr (Or.inr (terminalRunFallbackC_of_G hf)))
  · have htail : ShiftTailC centre place entry q first w m c r cP sP :=
      shiftTailC_of_dataL' centre place entry q first w m h lower span hlive
        (PalPeg.CloseoutWatchRound10.foundDpShiftC_of_at centre place entry q first w hP
          lower span h hstage hat)
        hrouteL hlag0 hctx hm
    have hroute := PalPeg.CloseoutWatchRound15.roundsRouteLP_of_tail centre place entry q first
      w m hex hE htail
    exact .exit (foundExit_of_compare3 centre place entry q first w m hP hE hsW a ls rs qw gap
      hprep hmis (Or.inl (PalPeg.CloseoutWatchPhase.roundsExit_of_LP hroute)))

end PalPeg.CloseoutWatchRound45

#print axioms PalPeg.CloseoutWatchRound45.period_of_beginShift
#print axioms PalPeg.CloseoutWatchRound45.watchStart_distance_zero
#print axioms PalPeg.CloseoutWatchRound45.prepBirthLagC_of_prime
#print axioms PalPeg.CloseoutWatchRound45.mismatchLandingLagZeroL_of_ctx'
#print axioms PalPeg.CloseoutWatchRound45.foundExit_compare_final17
