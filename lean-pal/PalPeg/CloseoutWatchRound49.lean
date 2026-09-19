import PalPeg.CloseoutWatchRound47

/-!
# Closeout watch round 49 — the match-clock leaves, reduced to freshness

Round 47 left `WatchClockC` (the watch-segment match clock) as the last
hypothesis of `foundExit_compare_final18`, and reported a second leaf of the
same shape for the preparation stream.  This round proves the **counting**
half of both, so that what remains is purely a *phase* statement.

* `fresh_advances_pace` — the arithmetic core: if a segment's event list is
  `advances 2048 2048 (av.map (·, true))` (i.e. the clock is fresh at the
  segment's start), then `2048 * count true ≤ av.length`.  This is
  `advances_le_compares` followed by `MatchClock.compare_budget`; note that
  `CloseoutPreload22.ClockInv` is only the *phase* `1 ≤ clock ≤ delay` and is
  by itself too weak — with `clock < 2048` the invariant
  `av.count true + run.1 = clock + fires * 2048` leaves up to one extra fire.
* `pace_of_length` — `2048 * #true ≤ length` is exactly `2047 * #true ≤ #false`.
* `watchClockC_of_fresh` — `WatchClockC` from `WatchFreshC`: the birth
  `BlockInv` (free from `blockInv_chainStart` at `watchStart`) together with
  `cb.clock = 2048` at the segment's start.  **(1) closed modulo freshness.**
* `prepClockC_of_length` — for the preparation stream the requested bound
  `2048 * m ≤ 2h + 2` follows from `2048 * m ≤ 2h + 3` by parity alone
  (`2048 * m` is even, `2h + 3` is odd).  **(2) reduced to `PrepPaceC`.**
  The controller clock is *not* available on `prepEvents`: that is a
  chain-side stream, and the lemma that would carry the controller's clock
  onto it does not exist — the missing transport is a `WatchSegE` from the
  found tick to the landing matching `found_to_watchStart`, after which
  `watchSegE_clock` applies and `PrepPaceC` becomes an instance of
  `fresh_advances_pace`.
* `foundExit_compare_final19` — `final18` with `WatchClockC` replaced by
  `WatchFreshC`.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

namespace PalPeg.CloseoutWatchRound49

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.CloseoutContracts
open PalPeg.GalilRunSkeleton PalPeg.GalilInvPlus PalPeg.GalilInvPlus2
open PalPeg.GalilFoundStage PalPeg.GalilTraceCost
open PalPeg.GalilBranchInvariants (BlockInv)
open PalPeg.CloseoutWatchRound45 (WatchDrainC' PrepBirthLagC')
open PalPeg.CloseoutWatchRound47 (WatchClockC foundExit_compare_final18)

/-! ## 1. The arithmetic core of the match clock -/

/-- **NAMED — the fresh-clock pace.**  A segment whose event list is produced
by `advances` from a *fresh* clock fires at most once per `2048` availability
ticks.  The freshness matters: `ClockInv` alone (`1 ≤ clock ≤ 2048`) allows
one extra fire. -/
theorem fresh_advances_pace (av : List Bool) :
    2048 * ((GalilScaffoldAdvanceClock.advances 2048 2048
      (av.map (fun b => (b, true)))).count true) ≤ av.length := by
  have h1 := GalilScaffoldAdvanceClock.advances_le_compares 2048 2048
    (av.map (fun b => (b, true)))
  have hmap : (av.map (fun b => (b, true))).map Prod.fst = av := by
    simp [List.map_map, Function.comp_def]
  rw [hmap] at h1
  have h2 := GalilScaffoldMatchClock.compare_budget 2048 av (by omega)
  have h3 : av.count true ≤ av.length := List.count_le_length
  have h4 := Nat.mul_le_mul_left 2048 h1
  omega

/-- `2048 * #true ≤ length` is exactly `2047 * #true ≤ #false`. -/
theorem pace_of_length (es : List Bool)
    (h : 2048 * es.count true ≤ es.length) :
    2047 * (es.count true : ℤ) ≤ (es.count false : ℤ) := by
  have hb := PalPeg.GalilScaffoldChainLag.bool_counts es
  have hn : (2047 * es.count true : ℕ) ≤ es.count false := by omega
  exact_mod_cast hn

/-! ## 2. `WatchClockC` from freshness -/

/-- **NAMED — the watch segment starts fresh.**  What is left of
`WatchClockC` once the counting is done: the birth chain satisfies the block
invariant (free from `blockInv_chainStart` at `watchStart`), and the
controller's clock is fresh at the segment's start. -/
def WatchFreshC (P : Shared) (q : ℕ) (first : Fin 9) : Prop :=
  ∀ (es2 : List Bool) (cb c1 : Control) (sb s1 : GalilVM)
    (w0 w : GalilScaffoldChainWatch.State),
    WatchSegE P q first 2048 es2 cb sb c1 s1 → sb.chain = ChainVM.watch w0 →
    s1.chain = ChainVM.watch w →
    BlockInv (ChainVM.watch w0) ∧ cb.clock = 2048

/-- **(1) CLOSED modulo freshness.**  `WatchClockC` from `WatchFreshC`. -/
theorem watchClockC_of_fresh (P : Shared) (q : ℕ) (first : Fin 9)
    (hf : WatchFreshC P q first) : WatchClockC P q first := by
  intro es2 cb c1 sb s1 w0 w hseg hsb hw
  obtain ⟨hblock, hclk⟩ := hf es2 cb c1 sb s1 w0 w hseg hsb hw
  refine ⟨hblock, ?_⟩
  obtain ⟨av, hlen, he, -, -⟩ := watchSegE_clock P q first 2048 hseg
  rw [hclk] at he
  refine pace_of_length es2 ?_
  have hp := fresh_advances_pace av
  rw [← he] at hp
  omega

/-! ## 3. The preparation stream -/

/-- **NAMED — the preparation stream is paced.**  The counting statement, at
the stream's own length `2h + 3`. -/
def PrepPaceC (h m : ℕ) : Prop := 2048 * m ≤ 2 * h + 3

/-- **(2) CLOSED by parity, modulo `PrepPaceC`.**  The bound asked by
`PrepBirthLagC'` is `2048 * m ≤ 2h + 2`; since `2048 * m` is even and
`2h + 3` is odd, the stream-length bound already gives it.  What is *not*
available here is the clock itself: `prepEvents` is a chain-side stream, so
`PrepPaceC` needs the controller clock transported onto it. -/
theorem prepClockC_of_length (h m : ℕ) (hp : PrepPaceC h m) :
    2048 * m ≤ 2 * h + 2 := by
  unfold PrepPaceC at hp
  omega

/-! ## 4. The route with the watch clock replaced by freshness -/

open PalPeg.CloseoutWatchRound2 (FoundCompareCtxC)
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
open PalPeg.CloseoutWatchRun (LiveScanWatch roundFuel)

/-- **`foundExit_compare_final18` with the watch match clock discharged.**
The watch-segment leaf is now the *phase* statement `WatchFreshC`. -/
theorem foundExit_compare_final19 (centre : GalilVM → Fin 3)
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
    (hfreshClk : WatchFreshC (PofC centre place entry w) q first)
    (hfresh : LandingFreshC' (PofC centre place entry w) q first cP sP)
    (hland : ∀ sF : GalilVM,
      PalPeg.CloseoutWatchRound5.BreakLandingC centre place entry q first w h sF cP sP)
    (hstepBreak : ∀ (c0 : Control) (s0 : GalilVM), LiveScanWatch c0 s0 →
      PalPeg.CloseoutWatchRun.RoundStepC (PofC centre place entry w) q first (roundFuel h)
        (BreakTermData centre place entry q first w m h) c0 s0) :
    FoundExitLPS (PofC centre place entry w) q first w m c r :=
  foundExit_compare_final18 centre place entry q first w m h lower span μ hP hex hready hcan
    hsane hstart hor hzl hnn hpm hE hsW a ls rs qw gap hprep hmis hctx hfbS hstage hmP hrP
    hcP hreachWatch hat hreach hround h3 h4 hinv horacle hfit hrest htie hbirth
    (watchClockC_of_fresh _ _ _ hfreshClk) hfresh hland hstepBreak

end PalPeg.CloseoutWatchRound49

#print axioms PalPeg.CloseoutWatchRound49.fresh_advances_pace
#print axioms PalPeg.CloseoutWatchRound49.pace_of_length
#print axioms PalPeg.CloseoutWatchRound49.watchClockC_of_fresh
#print axioms PalPeg.CloseoutWatchRound49.prepClockC_of_length
#print axioms PalPeg.CloseoutWatchRound49.foundExit_compare_final19
