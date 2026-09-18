import PalPeg.CloseoutWatchRound51

/-!
# Closeout watch round 52 — the match clock, re-cut at the landing

Round 51 refuted `WatchFreshC` as a schema and proved the landing-restricted
`WatchFreshAtC` from the compare context.  This round re-cuts the leaf per
birth and locates the gap precisely.

* `WatchClockAtC` — `WatchClockC` (Round 47:111) restricted to one birth
  `(cb, sb)`; `watchClockC_of_at` shows the restriction is faithful.
* `watchClockAtC_of_freshAt` — Round 49's arithmetic, relativised: freshness
  at the birth gives the pace at the birth.
* `WatchDrainAtC'` / `watchDrainAtC'_of_clockAt` — Round 47:119 relativised.
* `landing_chain_copy` / `landing_not_watch` — **the landing is not a watch
  birth**: `chainStart` is `ChainVM.copy` and `ChainMatched` preserves the
  constructor.  Hence `watchFreshAtC_vacuous`: Round 51's `WatchFreshAtC` at
  the landing is **vacuous**, and the fresh clock does *not* reach the watch
  birth, which is `2h + 3` preparation ticks later.
* `WatchBirthFreshC` — the leaf that actually remains.
* `foundExit_compare_final20` — `final18` with the refuted `WatchFreshC`
  schema off the route, the leaf now per-birth `WatchClockAtC`.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

namespace PalPeg.CloseoutWatchRound52

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.CloseoutContracts
open PalPeg.GalilRunSkeleton PalPeg.GalilInvPlus PalPeg.GalilInvPlus2
open PalPeg.GalilFoundStage PalPeg.GalilTraceCost
open PalPeg.GalilChainCoupling (FreshC SumRel)
open PalPeg.GalilBranchInvariants (BlockInv)
open PalPeg.CloseoutWatchRound47 (WatchClockC sumRel_ticks blockInv_ticks sumRel_internal)
open PalPeg.CloseoutWatchRound49 (fresh_advances_pace pace_of_length)
open PalPeg.CloseoutWatchRound51 (WatchFreshAtC watchFreshAtC_of_ctx)
open PalPeg.CloseoutWatchRound45 (WatchDrainC' period_of_beginShift)
open PalPeg.CloseoutWatchRound39 (watchSegE_lag landing_lag_zero_of_budget)
open PalPeg.CloseoutWatchRound41 (LandingL MismatchLandingLagZeroL shiftTailC_of_dataL')

/-! ## 1. The match clock, restricted to one birth -/

/-- **NAMED — `WatchClockC` at a fixed birth `(cb, sb)`.** -/
def WatchClockAtC (P : Shared) (q : ℕ) (first : Fin 9) (cb : Control) (sb : GalilVM) : Prop :=
  ∀ (es2 : List Bool) (c1 : Control) (s1 : GalilVM)
    (w0 w : GalilScaffoldChainWatch.State),
    WatchSegE P q first 2048 es2 cb sb c1 s1 → sb.chain = ChainVM.watch w0 →
    s1.chain = ChainVM.watch w →
    BlockInv (ChainVM.watch w0) ∧ 2047 * (es2.count true : ℤ) ≤ (es2.count false : ℤ)

/-- The restriction is faithful: quantifying the birth recovers `WatchClockC`. -/
theorem watchClockC_of_at (P : Shared) (q : ℕ) (first : Fin 9)
    (h : ∀ cb sb, WatchClockAtC P q first cb sb) : WatchClockC P q first :=
  fun es2 cb c1 sb s1 w0 w hseg hsb hw => h cb sb es2 c1 s1 w0 w hseg hsb hw

/-- **(1) CLOSED at the landing.**  Round 49's arithmetic, relativised. -/
theorem watchClockAtC_of_freshAt (P : Shared) (q : ℕ) (first : Fin 9)
    (cb : Control) (sb : GalilVM) (hf : WatchFreshAtC P q first cb sb) :
    WatchClockAtC P q first cb sb := by
  intro es2 c1 s1 w0 w hseg hsb hw
  obtain ⟨hblock, hclk⟩ := hf es2 c1 s1 w0 w hseg hsb hw
  refine ⟨hblock, ?_⟩
  obtain ⟨av, hlen, he, -, -⟩ := watchSegE_clock P q first 2048 hseg
  rw [hclk] at he
  refine pace_of_length es2 ?_
  have hp := fresh_advances_pace av
  rw [← he] at hp
  omega

/-! ## 2. The drain, at the same birth -/

/-- **NAMED — `WatchDrainC'` at a fixed birth `(cb, sb)`.** -/
def WatchDrainAtC' (P : Shared) (q : ℕ) (first : Fin 9) (cb : Control) (sb : GalilVM) : Prop :=
  ∀ (es2 : List Bool) (c1 : Control) (s1 : GalilVM)
    (w0 w w' : GalilScaffoldChainWatch.State) (Rnow : ℤ),
    WatchSegE P q first 2048 es2 cb sb c1 s1 → sb.chain = ChainVM.watch w0 →
    value w0.machine.control.distance = 0 →
    w'.machine.control.broken = false →
    s1.chain = ChainVM.watch w → GalilScaffoldChainWatch.Internal w w' →
    SumRel (.watch w') Rnow →
    ∃ m' d1 : ℤ, 0 ≤ m' ∧ 0 ≤ d1 ∧ 2047 * m' + d1 ≤ (es2.count false : ℤ) ∧
      Rnow = value w0.lag + m'

/-- **(3') CLOSED modulo `WatchClockAtC`.**  Round 47:119, relativised. -/
theorem watchDrainAtC'_of_clockAt (P : Shared) (q : ℕ) (first : Fin 9)
    (cb : Control) (sb : GalilVM) (hclk : WatchClockAtC P q first cb sb) :
    WatchDrainAtC' P q first cb sb := by
  intro es2 c1 s1 w0 w w' Rnow hseg hsb hd0 hbr hw hint hs
  obtain ⟨hblock, hpace⟩ := hclk es2 c1 s1 w0 w hseg hsb hw
  have hne : sb.chain ≠ ChainVM.idle := by rw [hsb]; exact fun h => ChainVM.noConfusion h
  obtain ⟨hct, -, -, -, -, -, -⟩ := watchSegE_events P q first 2048 hseg hne
  rw [hsb, hw] at hct
  have hs0 : SumRel (ChainVM.watch w0) (value w0.lag) := by
    intro _; rw [hd0]; omega
  have hs1 : SumRel (ChainVM.watch w) (value w0.lag + (es2.count true : ℤ)) :=
    sumRel_ticks hct hblock hs0
  have hbw : BlockInv (ChainVM.watch w) := blockInv_ticks hct hblock
  have hs2 : SumRel (ChainVM.watch w') (value w0.lag + (es2.count true : ℤ)) :=
    sumRel_internal hint hbw hs1
  have heq : value w'.machine.control.distance + value w'.lag
      = value w0.lag + (es2.count true : ℤ) := hs2 hbr
  have heq' : value w'.machine.control.distance + value w'.lag = Rnow := hs hbr
  refine ⟨(es2.count true : ℤ), 0, by positivity, le_refl 0, by simpa using hpace, ?_⟩
  omega

/-! ## 3. The watch birth is **not** the landing -/

open PalPeg.CloseoutWatchRound2 (FoundCompareCtxC)

/-- **NAMED — the landing chain is a `copy`, not a `watch`.**  `chainStart` is
`ChainVM.copy` and `ChainMatched` preserves the constructor, so the landing
`sP` sits at the *start* of the preparation stream. -/
theorem landing_chain_copy (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) {c0 cP : Control} {r sP : GalilVM}
    (hctx : FoundCompareCtxC centre place entry qq first raw c0 r cP sP) :
    ∃ (t : GalilScaffoldTape.Tape) (hh : Counter) (p : GalilScaffoldPlace.Place)
      (v : GalilScaffoldChainPeriod.Tape) (lag margin : Counter) (ver : PlaceHead),
      sP.chain = ChainVM.copy t hh p v lag margin ver := by
  obtain ⟨es0, cF, sF, vq, ch, oF, a, ls, rs, qw, gap, -, -, -, -, -, -, -, -, -, -, -, hch, -, -,
    -, hsP⟩ := hctx
  rw [hsP, afterCompare_chain]
  unfold chainStart at hch
  cases hch
  exact ⟨_, _, _, _, _, _, _, rfl⟩

/-- **REFUTED — the landing is not a watch birth.** -/
theorem landing_not_watch (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) {c0 cP : Control} {r sP : GalilVM}
    (hctx : FoundCompareCtxC centre place entry qq first raw c0 r cP sP)
    (w0 : GalilScaffoldChainWatch.State) : sP.chain ≠ ChainVM.watch w0 := by
  obtain ⟨t, hh, p, v, lag, margin, ver, hc⟩ :=
    landing_chain_copy centre place entry qq first raw hctx
  rw [hc]; exact fun h => ChainVM.noConfusion h

/-- **CONSEQUENCE — Round 51's `WatchFreshAtC` at the landing is VACUOUS.**
Its hypothesis `sP.chain = ChainVM.watch w0` is unsatisfiable, so
`watchFreshAtC_of_ctx` carries no information: the fresh clock sits at the
landing, but the *watch birth* is `2h + 3` preparation ticks later. -/
theorem watchFreshAtC_vacuous (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) {c0 cP : Control} {r sP : GalilVM}
    (hctx : FoundCompareCtxC centre place entry qq first raw c0 r cP sP) :
    WatchFreshAtC (PofC centre place entry raw) qq first cP sP := by
  intro es2 c1 s1 w0 w hseg hsP hw
  exact absurd hsP (landing_not_watch centre place entry qq first raw hctx w0)

/-- **NAMED — the leaf that actually remains.**  Freshness at the *watch
birth* `(cb, sb)`, i.e. the preparation stream ends on a match-clock boundary.
This is `WatchFreshAtC` at the birth, and it is *not* free from the context. -/
abbrev WatchBirthFreshC (P : Shared) (q : ℕ) (first : Fin 9)
    (cb : Control) (sb : GalilVM) : Prop := WatchFreshAtC P q first cb sb

/-! ## 4. The route, with the false schema bypassed -/

open PalPeg.CloseoutWatchRound3 (DistanceNonnegC)
open PalPeg.CloseoutWatchRound6 (RightCanC RightSaneC StartLeC LedgerOriginC PeriodMatchC)
open PalPeg.CloseoutWatchRound4 (ZeroLagAtMatchC)
open PalPeg.CloseoutWatchRound7 (PrepLandingWatchC ShiftReachC ShiftRoundAtC BreakTermData)
open PalPeg.CloseoutWatchRound10 (FoundDpAtC)
open PalPeg.CloseoutPrepInputs2 (MismatchExitG)
open PalPeg.CloseoutPrepInputs3 (PrepInputsG3)
open PalPeg.CloseoutWatchRound30 (ShiftCopyIdleC MismatchClassifierTieC)
open PalPeg.CloseoutWatchRound31 (FoundExitLPS FallbackReachS)
open PalPeg.CloseoutWatchRound33 (ShiftRunCL)
open PalPeg.CloseoutWatchRound34 (ShiftBreakOracleC ShiftBreakFitC)
open PalPeg.CloseoutWatchRound37 (ShiftRoundInvCL ShiftOriginRestCL)
open PalPeg.CloseoutWatchRound44 (LandingFreshC')
open PalPeg.CloseoutWatchRound45 (PrepBirthLagC')
open PalPeg.CloseoutWatchRun (LiveScanWatch roundFuel)

/-- **`foundExit_compare_final19` with the false `WatchFreshC` removed.**
The watch leaf is now the *per-birth* `WatchClockAtC`; Round 49's refuted
schema no longer appears on the route. -/
theorem foundExit_compare_final20 (centre : GalilVM → Fin 3)
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
    (hbirth : PrepBirthLagC' (PofC centre place entry w) q first c r cP sP)
    (hclockAt : ∀ cb sb, WatchClockAtC (PofC centre place entry w) q first cb sb)
    (hfresh : LandingFreshC' (PofC centre place entry w) q first cP sP)
    (hland : ∀ sF : GalilVM,
      PalPeg.CloseoutWatchRound5.BreakLandingC centre place entry q first w h sF cP sP)
    (hstepBreak : ∀ (c0 : Control) (s0 : GalilVM), LiveScanWatch c0 s0 →
      PalPeg.CloseoutWatchRun.RoundStepC (PofC centre place entry w) q first (roundFuel h)
        (BreakTermData centre place entry q first w m h) c0 s0) :
    FoundExitLPS (PofC centre place entry w) q first w m c r :=
  PalPeg.CloseoutWatchRound47.foundExit_compare_final18 centre place entry q first w m h lower
    span μ hP hex hready hcan hsane hstart hor hzl hnn hpm hE hsW a ls rs qw gap hprep hmis hctx
    hfbS hstage hmP hrP hcP hreachWatch hat hreach hround h3 h4 hinv horacle hfit hrest htie hbirth
    (watchClockC_of_at _ _ _ hclockAt) hfresh hland hstepBreak

end PalPeg.CloseoutWatchRound52

#print axioms PalPeg.CloseoutWatchRound52.watchClockC_of_at
#print axioms PalPeg.CloseoutWatchRound52.watchClockAtC_of_freshAt
#print axioms PalPeg.CloseoutWatchRound52.watchDrainAtC'_of_clockAt
#print axioms PalPeg.CloseoutWatchRound52.landing_chain_copy
#print axioms PalPeg.CloseoutWatchRound52.landing_not_watch
#print axioms PalPeg.CloseoutWatchRound52.watchFreshAtC_vacuous
#print axioms PalPeg.CloseoutWatchRound52.foundExit_compare_final20
