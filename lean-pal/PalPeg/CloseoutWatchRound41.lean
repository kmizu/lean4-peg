import PalPeg.CloseoutWatchRound39
import PalPeg.CloseoutWatchRound37

/-!
# Closeout watch round 41 — the landing lag leaf at the consumer level

Round 39 showed that the bare leaf `MismatchLandingLagZeroC` (Round 37) is
FALSE as a global proposition and TRUE at the landings that occur only through
the found-radius budget `R_f ≤ 2h`, which lives one level above
`shiftTailC_of_dataL` (it needs `Decodes`/`Restarted`/`StageEntry`).  This
round moves the leaf to that level.

* `MismatchLandingLagZeroL` — the leaf restricted to exactly the data
  `shiftTailC_of_dataL` has when it applies it: a landing reached from the
  prep landing `(cP, sP)` (`LandingL`), the found tick's data, and the route
  data `ShiftRoundDataL` (which carries `Internal w w'`, `zero w'.lag`, the
  guard, and `pos 11 = h`).
* `mismatchLandingLagZeroL_of_ctx` — the leaf from the four pieces:
  (1) `R_f ≤ 2h` DERIVED from `StageEntryC.stage` + `found_radius_le_two_period`
  (the found tick's `pos 11` is the route's `h` by `ShiftRoundDataL`);
  (2) `PrepBirthLagC` NAMED — the watch was born with lag `R_f + m`,
  `2048·m ≤ 2h+2`, canonical and non-negative, at a state on the way to the
  landing (`found_to_watchStart` + `prepEvents`, to be transported through the
  prep segment);
  (3) `WatchDrainC` NAMED — along the watch segment `#false ≥ 2047·m' + d1`
  with `R_now = birth lag + m'` (the `WatchSegE` clock structure,
  `watchSegE_clock`);
  (4) `LandingFreshC` NAMED — at the landing the pre-compare watch is
  canonical, the post-compare chain is `FreshC` with a `SumRel` ledger, and
  the guard's `h` is its `periodLength` (`minv_watchSegE`/`fresh` transport;
  the last clause is Round 33's `h := periodLength w'` choice).
  The lag drain itself is Round 39's proven `watchSegE_lag`, the arithmetic
  Round 39's `landing_lag_zero_of_budget`.
* `shiftTailC_of_dataL'` and `foundExit_compare_final16` — Round 37's
  consumer and route with `hlag0` replaced by the three named pieces.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

namespace PalPeg.CloseoutWatchRound41

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

/-! ## 1. The landings and the restricted leaf -/

/-- A landing reached from the prep landing: an event-indexed segment followed
by a plain one (the shape `shiftTailC_of_dataL` has in hand). -/
def LandingL (P : Shared) (q : ℕ) (first : Fin 9) (cP : Control) (sP : GalilVM)
    (c1 : Control) (s1 : GalilVM) : Prop :=
  ∃ (es : List Bool) (c2 : Control) (s2 : GalilVM),
    WatchSegE P q first 2048 es cP sP c2 s2 ∧ WatchSeg P q first 2048 c2 s2 c1 s1

/-- **The leaf at the consumer level.**  For the found tick's data (the fields
of `FoundCompareCtxC`) and a landing reached from `(cP, sP)` carrying the route
data, the pre-compare watch has lag zero. -/
def MismatchLandingLagZeroL (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m lower : ℕ) (c0 : Control) (r : GalilVM)
    (cP : Control) (sP : GalilVM) : Prop :=
  ∀ (es0 : List Bool) (cF : Control) (sF : GalilVM) (vq : SearchVM) (ch : ChainVM)
    (a : Fin 2) (ls rs qw : List (Fin 2)) (gap : Bool),
    WatchSegE (PofC centre place entry raw) qq first 2048 es0 c0 r cF sF →
    sF.chain = ChainVM.idle → cF.clock = 1 →
    sF.center = represent ⟨a :: ls, gap⟩ (rs.map some) qw →
    searchEffect (PofC centre place entry raw) true sF vq → vq.search.mode = .found →
    ChainMatched (chainStart (vq.dp.config.tapes 11)
      ((PofC centre place entry raw).centre sF) ((PofC centre place entry raw).place sF)
      sF.center sF.radius) ch →
    sP = afterBirth true (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq) →
    ∀ (c1 : Control) (s1 : GalilVM) (h : ℕ),
      LandingL (PofC centre place entry raw) qq first cP sP c1 s1 →
      ShiftRoundDataL centre place entry qq first raw m h lower sF vq c1 s1 →
      ∀ w : GalilScaffoldChainWatch.State, s1.chain = ChainVM.watch w → zero w.lag = true

/-! ## 2. The three named pieces -/

/-- **(2) NAMED — prep accounting.**  On the way from the prep landing to a
clock-`1` watch landing there is a state whose chain watches with a canonical,
non-negative lag `R_f + m` (`R_f` the found radius), and `2048·m ≤ 2h+2` for
the found tick's `h = pos 11` (`found_to_watchStart` + `prepEvents`). -/
def PrepBirthLagC (P : Shared) (q : ℕ) (first : Fin 9) (c0 : Control) (r : GalilVM)
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
        value w0.lag = value sF.radius + m ∧ 0 ≤ m ∧
        2048 * m ≤ 2 * ((GalilScaffoldProgram.denote vq.dp.config).pos 11 : ℤ) + 2

/-- **(3) NAMED — the watch clock structure.**  Along a segment that watches
throughout, the disabled ticks number at least `2047·m' + d1`, where `m'` is
the growth of the radius ledger since birth (`watchSegE_clock`). -/
def WatchDrainC (P : Shared) (q : ℕ) (first : Fin 9) : Prop :=
  ∀ (es2 : List Bool) (cb c1 : Control) (sb s1 : GalilVM)
    (w0 w w' : GalilScaffoldChainWatch.State) (Rnow : ℤ),
    WatchSegE P q first 2048 es2 cb sb c1 s1 → sb.chain = ChainVM.watch w0 →
    s1.chain = ChainVM.watch w → GalilScaffoldChainWatch.Internal w w' →
    SumRel (.watch w') Rnow →
    ∃ m' d1 : ℤ, 0 ≤ m' ∧ 0 ≤ d1 ∧ 2047 * m' + d1 ≤ (es2.count false : ℤ) ∧
      Rnow = value w0.lag + m'

/-- **(4) NAMED — coupling at the landing.**  The pre-compare watch is
canonical, the post-compare chain is fresh with a radius ledger, and the
shift's `h` is its semiperiod (`minv_watchSegE`/`fresh` transport; Round 33's
`h := periodLength w'`). -/
def LandingFreshC (P : Shared) (q : ℕ) (first : Fin 9) (cP : Control) (sP : GalilVM) : Prop :=
  ∀ (c1 : Control) (s1 : GalilVM) (w w' : GalilScaffoldChainWatch.State) (h : ℕ)
    (vs : ScanVM) (vq' : SearchVM) (s2' : GalilVM),
    LandingL P q first cP sP c1 s1 → s1.chain = ChainVM.watch w →
    GalilScaffoldChainWatch.Internal w w' → beginShiftVM h w' (afterMismatch s1 vs vq') s2' →
    GalilScaffoldChainWatch.CanonicalState w ∧ FreshC w'.machine.control ∧
      (∃ Rnow : ℤ, SumRel (.watch w') Rnow) ∧ periodLength w' = h

/-! ## 3. The leaf from the context and the pieces -/

/-- **The leaf at the consumer level.**  Piece (1) is derived from
`StageEntryC.stage` and `found_radius_le_two_period`; (2)–(4) are the named
pieces; the drain is `watchSegE_lag`, the arithmetic
`landing_lag_zero_of_budget`. -/
theorem mismatchLandingLagZeroL_of_ctx (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m lower : ℕ) {c0 cP : Control} {r sP : GalilVM}
    (hP : Decodes (PofC centre place entry raw))
    (hE : StageEntryC (PofC centre place entry raw) qq first raw c0 r)
    (h2 : PrepBirthLagC (PofC centre place entry raw) qq first c0 r cP sP)
    (h3 : WatchDrainC (PofC centre place entry raw) qq first)
    (h4 : LandingFreshC (PofC centre place entry raw) qq first cP sP) :
    MismatchLandingLagZeroL centre place entry qq first raw m lower c0 r cP sP := by
  intro es0 cF sF vq ch a ls rs qw gap hseg0 hidle hcF hcen hq hfound hch hsPeq c1 s1 h hland
    hdL w hw
  obtain ⟨w1, w', vs, vq', s2', t', v, cycle, o, org, mm, c', s', n, c3, s3, w3, vs3, vq3, o3, w3',
    hm1, hr1, hc1, hw1, hint', hvs, hz, hav, hcmp, hmis, hq', hg, hb, hs2', hi2, hchain, ho, hint,
    he, hoc, ha, hpos11, hlow, hrounds, hseg3, hm3, hr3, hc3, hs3, hav3, hcmp3, hmt3, hq3, ho3,
    hbroken, hmargin, hlast, hlag3, hbound⟩ := hdL
  -- the route's pre-compare watch is `w`
  rw [hw] at hw1
  obtain rfl := ChainVM.watch.inj hw1
  -- the guard: phase `4`, unbroken, on the post-compare chain `w'`
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
  -- (4) coupling at the landing
  obtain ⟨hcw, hf, ⟨Rnow, hs⟩, hper⟩ := h4 c1 s1 w w' h1 vs vq' s2' hland hw hint' hs2'
  -- (2) the birth lag
  obtain ⟨mI, w0, es2, cb, sb, hseg2, hsb, hc0, hn0, hlag0, hm0, hm⟩ :=
    h2 es0 cF sF vq ch a ls rs qw gap hseg0 hidle hcF hcen hq hfound hch hsPeq c1 s1 w hland hc1 hw
  rw [hpos11] at hm
  -- (3) the drain supply
  obtain ⟨m', d1, hm'0, hd10, hk, hnow⟩ := h3 es2 cb c1 sb s1 w0 w w' Rnow hseg2 hsb hw hint' hs
  -- the drain (Round 39) and the arithmetic (Round 39)
  have hdrain := (watchSegE_lag (PofC centre place entry raw) qq first 2048 hseg2 hsb hw hc0 hn0).2
  rw [hlag0] at hdrain
  exact landing_lag_zero_of_budget hint' hz hcw hf hph hbr hs hper (value sF.radius) mI m' d1
    (k := es2.count false) hk hdrain (by omega) (by exact_mod_cast hh1) hRf hm hm0 hm'0 hd10

/-! ## 4. The consumer and the route with the leaf moved up -/

/-- **`shiftTailC_of_dataL` with the restricted leaf.** -/
theorem shiftTailC_of_dataL' (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m h lower span : ℕ) {c0 cP : Control} {r sP : GalilVM}
    (hdp : PalPeg.CloseoutWatchRound5.FoundDpShiftC centre place entry qq first raw lower span
      c0 r)
    (hroute : MismatchShiftRouteL centre place entry qq first raw m lower)
    (hlag0 : MismatchLandingLagZeroL centre place entry qq first raw m lower c0 r cP sP)
    (hctx : FoundCompareCtxC centre place entry qq first raw c0 r cP sP)
    (hrun : TerminalRunMismatchShiftC (PofC centre place entry raw) qq first h cP sP) :
    ShiftTailC centre place entry qq first raw m c0 r cP sP := by
  obtain ⟨es0, cF, sF, vq, ch, oF, a, ls, rs, qw, gap, hraw, hseg0, hmF, hrF, hcF, havF,
    hidle, hCen, hq, hfound, hmt, hch, hchne, hoF, hcPeq, hsPeq⟩ := hctx
  obtain ⟨hres, hpc⟩ := hdp a ls rs qw gap es0 cF sF vq hseg0 hCen hq hfound
  refine ⟨a, ls, rs, qw, gap, es0, cF, sF, vq, ch, oF, lower, span, hraw, hseg0, hmF, hrF, hcF,
    havF, hidle, hCen, hq, hfound, hmt, hch, hchne, hoF, hcPeq, hsPeq, hres, hpc, ?_⟩
  intro es c2 s2 hseg hwLanding
  obtain ⟨hmL, hrL, hcL⟩ := watchSegE_live_control (delay := 2048) (by omega) hseg
    (by rw [hcPeq]; exact hmF) (by rw [hcPeq]) (by simp [hcPeq])
  obtain ⟨cT, sT, hsegT, hLT, c1, s1, hseg1, hclk, hlive1, hav1, hne1, hnG⟩ :=
    hrun es c2 s2 hseg ⟨hmL, hrL, hcL, hwLanding⟩
  obtain ⟨h1, hdL⟩ := hroute sF vq c1 s1 hlive1 hclk hav1 hne1 hnG
  have hd := shiftRoundData_of_dataL centre place entry qq first raw m h1 lower sF vq c1 s1
    (hlag0 es0 cF sF vq ch a ls rs qw gap hseg0 hidle hcF hCen hq hfound hch hsPeq c1 s1 h1
      ⟨es, c2, s2, hseg, watchSeg_append hsegT hseg1⟩ hdL) hdL
  obtain ⟨w, vs, vq', s2', t', v, cycle, o, org, mm, c', s', n, c3, s3, w3, vs3, vq3, o3, w3',
    hm1, hr1, hc1, hs1, hz, hav, hcmp, hmis, hq', hg, hb, hs2', hi2, hchain, ho, hint, he,
    hoc, ha, hpos11, hlow, hrounds, hseg3, hm3, hr3, hc3, hs3, hav3, hcmp3, hmt3, hq3, ho3,
    hbroken, hmargin, hlast, hlag, hbound⟩ := hd
  exact ⟨c1, s1, h1, w, vs, vq', s2', t', v, cycle, o, org, mm, c', s', n, c3, s3, w3, vs3, vq3,
    o3, w3', watchSeg_append hsegT hseg1, hm1, hr1, hc1, hs1, hz, hav, hcmp, hmis, hq', hg, hb,
    hs2', hi2, hchain, ho, hint, he, hoc, ha, hpos11, hlow, hrounds, hseg3, hm3, hr3, hc3, hs3,
    hav3, hcmp3, hmt3, hq3, ho3, hbroken, hmargin, hlast, hlag, hbound⟩

/-- **`foundExit_compare_final15` with `MismatchLandingLagZeroC` removed**: in
its place the three named pieces `PrepBirthLagC`, `WatchDrainC`,
`LandingFreshC`; the found-radius budget comes from `hP`/`hE`. -/
theorem foundExit_compare_final16 (centre : GalilVM → Fin 3)
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
    (hreachWatch : ∃ (es : List Bool) (c2 : Control) (s2 : GalilVM),
      WatchSegE (PofC centre place entry w) q first 2048 es cP sP c2 s2 ∧
        PalPeg.CloseoutWatchRun.LiveScanWatch c2 s2)
    (hat : FoundDpAtC centre place entry q first w lower span h c r)
    (hreach : ShiftReachC centre place entry q first w h)
    (hround : ShiftRoundAtC centre place entry q first w m h lower)
    (h3 : ShiftCopyIdleC) (h4 : ShiftRunCL)
    (hinv : ShiftRoundInvCL w)
    (horacle : ∀ h', ShiftBreakOracleC centre place entry q first w h' (μ h'))
    (hfit : ∀ h', ShiftBreakFitC centre place entry q first w m h')
    (hrest : ShiftOriginRestCL centre place entry q first w lower)
    (htie : MismatchClassifierTieC (PofC centre place entry w) q first)
    (hbirth : PrepBirthLagC (PofC centre place entry w) q first c r cP sP)
    (hdrain : WatchDrainC (PofC centre place entry w) q first)
    (hfresh : LandingFreshC (PofC centre place entry w) q first cP sP)
    (hland : ∀ sF : GalilVM,
      PalPeg.CloseoutWatchRound5.BreakLandingC centre place entry q first w h sF cP sP)
    (hstepBreak : ∀ (c0 : Control) (s0 : GalilVM), LiveScanWatch c0 s0 →
      PalPeg.CloseoutWatchRun.RoundStepC (PofC centre place entry w) q first (roundFuel h)
        (BreakTermData centre place entry q first w m h) c0 s0) :
    FoundExitLPS (PofC centre place entry w) q first w m c r := by
  classical
  have hlag0 := mismatchLandingLagZeroL_of_ctx centre place entry q first w m lower hP hE hbirth
    hdrain hfresh
  have hrouteL := mismatchShiftRouteL_of_tick centre place entry q first w m lower μ h3 h4 hinv
    horacle hfit hrest htie
  have hsplit4 : ExitSplit4C centre place entry q first w h cP sP :=
    exitSplit4C_of_tick centre place entry q first w h cP sP
      (PalPeg.CloseoutWatchRound2.chain_ne_idle_of_foundCompareCtx hctx)
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
        hmis hctx hsplit hstage hmP hrP hcP hat hreach hround hland hstepBreak)
      hT.2 hs3 hfbS (PalPeg.CloseoutWatchRound2.chain_ne_idle_of_foundCompareCtx hctx)
      hreachWatch
  rcases hsplit4 hT.2 with hs | hb | hf | hm
  · exact via3 (fun _ => Or.inl hs)
  · exact via3 (fun _ => Or.inr (Or.inl hb))
  · exact via3 (fun _ => Or.inr (Or.inr (terminalRunFallbackC_of_G hf)))
  · have htail : ShiftTailC centre place entry q first w m c r cP sP :=
      shiftTailC_of_dataL' centre place entry q first w m h lower span
        (PalPeg.CloseoutWatchRound10.foundDpShiftC_of_at centre place entry q first w hP
          lower span h hstage hat)
        hrouteL hlag0 hctx hm
    have hroute := PalPeg.CloseoutWatchRound15.roundsRouteLP_of_tail centre place entry q first
      w m hex hE htail
    exact .exit (foundExit_of_compare3 centre place entry q first w m hP hE hsW a ls rs qw gap
      hprep hmis (Or.inl (PalPeg.CloseoutWatchPhase.roundsExit_of_LP hroute)))

end PalPeg.CloseoutWatchRound41

#print axioms PalPeg.CloseoutWatchRound41.mismatchLandingLagZeroL_of_ctx
#print axioms PalPeg.CloseoutWatchRound41.shiftTailC_of_dataL'
#print axioms PalPeg.CloseoutWatchRound41.foundExit_compare_final16
