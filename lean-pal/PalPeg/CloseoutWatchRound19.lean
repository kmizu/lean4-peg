import PalPeg.CloseoutWatchRound18

/-!
# Round 19: `ExitSplit3C` discharged under run comparability

Round 18 named `ExitSplit3C` — "the watch phase takes one of the three exit
families *uniformly*", i.e. the per-segment disjunction inside
`CloseoutWatchRound2.TerminalRunC` can be pulled out of the `∀ es` quantifier —
and left it open.  This round discharges it.

## Why it needs a hypothesis (and which one)

`TerminalRunC` is `∀ segment, ∃ terminal, (A ∨ B ∨ C ∨ D)`; `ExitSplit3C` asks
for `(∀ …, A∨B) ∨ (∀ …, C) ∨ (∀ …, D')`.  Pulling a disjunction out of a
universal quantifier is not valid in general, and here it cannot be: `WatchSeg`
is a relation (its `background`, `compare`, `searchEffect` steps are not known
to be functional — the exact "landing determinism" gap Round 15's header names),
so two segments out of the same preparation landing are not, as far as the
tree knows, on one run, and nothing forces them to reach the same *kind* of
terminal landing.

The **one** extra hypothesis is therefore precisely that missing fact, in its
weakest usable form:

* `WatchPrefixC P q first cP sP` — any two `WatchSeg` runs out of the
  preparation landing are comparable (one extends the other).  This is
  Round 15's "landing determinism for `WatchSegE`" restated on `WatchSeg`
  without lengths; on the machine it follows from step determinism
  (`GalilTickFair`: `Tick ∧ Fair` is unique), which is not yet available at the
  `galilFrameS` level.

No side condition on `centre`, `¬PrepChain`, or a landing invariant is needed.
`LiveScanWatch cP sP` is also taken, but it is not new: it is what
`PrepLandingLiveC` yields at the empty segment and what `foundExit_compare_final9`
already derives from `hwatch`.

## What is proved here (unconditionally, no `sorry`)

1. `watchSeg_not_canRight` — **exhaustion is absorbing.**  `wait`/`count` keep
   the right head (`background_frame`), and `match` needs `canRight`; so once
   the right head is exhausted every later `WatchSeg` landing is exhausted.
2. `watchSeg_stuck_of_mismatch` — **an available clock-one mismatch is stuck.**
   `wait` needs `¬ canRight`, `count` needs `1 < clock`, `match` needs the
   outer symbols to agree (`matched_parts` through `compare`); only `stop`
   applies, so the segment is empty.
3. `split3_of_prefix` — **the split, for an arbitrary `P`.**  Instead of
   classifying the empty-segment terminal (which does not survive past a
   fuel-zero landing, since `WatchSeg` does not stop at the shift guard), the
   family is chosen by which *stuck-or-absorbing* landing is reachable at all:
   * some reachable live landing is exhausted → `TerminalRunBreak0C`, by
     comparability plus 1;
   * else some reachable live landing is a clock-one available mismatch →
     `TerminalRunFallbackC`, by comparability plus 2;
   * else `TerminalRunShiftC`: every terminal `TerminalRunC` hands back is
     reachable (`watchSeg_append`), so its `¬ canRight` and `BreakEndC` branches
     are excluded by the two failed searches, leaving fuel zero / shift guard.
   Only the first two branches consult `WatchPrefixC`.
4. `exitSplit3C_of_tick` — **the target**: 3 at `PofC centre place entry raw`.
5. `foundExit_compare_final10` — `CloseoutWatchRound18.foundExit_compare_final9`
   with `hsplit3` replaced by `WatchPrefixC`; `LiveScanWatch cP sP` is derived
   from `hwatch` inside.

## Remaining contracts

* `WatchPrefixC` — **NAMED (open)** by this round.  Its producer is
  determinism of the `galilFrameS` scan steps out of a live watch landing, which
  is the `Fair`-side work item of `GalilTickFair` and is not consumed here.
* `CloseoutWatchRound17.FallbackRouteW`, `CloseoutWatchPhase2.LandingRestartReach`,
  `CloseoutPrepInputs2.MismatchExitG` and everything Round 15/18 list — unchanged.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

namespace PalPeg.CloseoutWatchRound19

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton PalPeg.GalilInvPlus PalPeg.GalilInvPlus2
open PalPeg.GalilFoundStage PalPeg.GalilTraceCost
open PalPeg.CloseoutContracts
open PalPeg.CloseoutWatchRun (LiveScanWatch roundFuel watchSeg_append)
open PalPeg.CloseoutWatchRound (BreakEndC TerminalC)
open PalPeg.CloseoutWatchPhase2 (LandingRestartReach)
open PalPeg.CloseoutWatchRound2 (FoundCompareCtxC TerminalRunC)
open PalPeg.CloseoutWatchRound3 (TerminalRunShiftC DistanceNonnegC)
open PalPeg.CloseoutWatchRound5 (PrepLandingLiveC)
open PalPeg.CloseoutWatchRound7 (PrepLandingWatchC ShiftReachC ShiftRoundAtC BreakTermData)
open PalPeg.CloseoutWatchRound10 (FoundDpAtC)
open PalPeg.CloseoutWatchRound6 (RightCanC RightSaneC StartLeC LedgerOriginC PeriodMatchC)
open PalPeg.CloseoutWatchRound4 (ZeroLagAtMatchC)
open PalPeg.CloseoutPrepInputs2 (MismatchExitG)
open PalPeg.CloseoutPrepInputs3 (PrepInputsG3)
open PalPeg.CloseoutWatchRound17 (FallbackRouteW)
open PalPeg.CloseoutWatchRound18 (BreakEndAvC TerminalRunBreak0C TerminalRunFallbackC
  ExitSplit3C watchSeg_of_watchSegE')

/-! ## 1. The hypothesis -/

/-- **NAMED (open) — run comparability out of the preparation landing.**  Any
two `WatchSeg` runs from `(cP, sP)` are prefix-comparable.  This is the
"landing determinism" Round 15 named as missing, on `WatchSeg` and without
lengths; on the machine it is a consequence of step determinism. -/
def WatchPrefixC (P : Shared) (q : ℕ) (first : Fin 9) (cP : Control) (sP : GalilVM) : Prop :=
  ∀ (c2 c3 : Control) (s2 s3 : GalilVM),
    WatchSeg P q first 2048 cP sP c2 s2 → WatchSeg P q first 2048 cP sP c3 s3 →
      WatchSeg P q first 2048 c2 s2 c3 s3 ∨ WatchSeg P q first 2048 c3 s3 c2 s2

/-! ## 2. Two facts about `WatchSeg` -/

/-- **Derived — exhaustion is absorbing along a segment.** -/
theorem watchSeg_not_canRight {P : Shared} {q : ℕ} {first : Fin 9} {delay : ℕ}
    {c c' : Control} {s t : GalilVM} (h : WatchSeg P q first delay c s c' t)
    (hn : ¬ canRight s.right) : ¬ canRight t.right := by
  induction h with
  | stop c s => exact hn
  | wait c s s' hm hr hn' hb _ ih =>
    apply ih
    obtain ⟨-, hr', -, -, -, -⟩ := background_frame P q first hb
    rw [hr']; exact hn
  | count c s s' hm hr ha hc hb _ ih =>
    exact absurd ha hn
  | «match» c s vs vq o hm hr ha hc hne hcmp hmt hq ho _ ih =>
    exact absurd ha hn

/-- **Derived — an available clock-one mismatch admits only the empty segment.** -/
theorem watchSeg_stuck_of_mismatch {P : Shared} {q : ℕ} {first : Fin 9} {delay : ℕ}
    {c c' : Control} {s t : GalilVM} (h : WatchSeg P q first delay c s c' t)
    (hclk : c.clock = 1) (hav : canRight s.right)
    (hne : read (left s.left) ≠ read (right s.right)) : c' = c ∧ t = s := by
  cases h with
  | stop c s => exact ⟨rfl, rfl⟩
  | wait c s s' hm hr hn hb rest => exact absurd hav hn
  | count c s s' hm hr ha hc hb rest => omega
  | «match» c s vs vq o hm hr ha hc hne' hcmp hmt hq ho rest =>
    exfalso
    apply hne
    obtain ⟨⟨hl0, hr0, _⟩, _⟩ := hcmp
    rw [scanLens.get_set] at hl0 hr0
    have := matched_parts P q first hmt
    rw [hl0, hr0] at this; exact this

/-! ## 3. The split -/

/-- **Derived — the three-way split under run comparability, for any `P`.**
The family is chosen by which stuck-or-absorbing landing is reachable from the
preparation landing at all; comparability is consulted only in the first two
branches. -/
theorem split3_of_prefix (P : Shared) (q : ℕ) (first : Fin 9) (h : ℕ)
    (cP : Control) (sP : GalilVM)
    (hneP : sP.chain ≠ ChainVM.idle) (hpre : WatchPrefixC P q first cP sP)
    (hrun : TerminalRunC P q first h cP sP) :
    TerminalRunShiftC P q first h cP sP ∨ TerminalRunBreak0C P q first h cP sP ∨
      TerminalRunFallbackC P q first h cP sP := by
  classical
  have toSeg : ∀ {es : List Bool} {c2 : Control} {s2 : GalilVM},
      WatchSegE P q first 2048 es cP sP c2 s2 → WatchSeg P q first 2048 cP sP c2 s2 :=
    fun hE => watchSeg_of_watchSegE' hE hneP
  by_cases hEx : ∃ (cW : Control) (sW : GalilVM),
      WatchSeg P q first 2048 cP sP cW sW ∧ LiveScanWatch cW sW ∧ ¬ canRight sW.right
  · -- some reachable live landing is exhausted: the input-exhausted family
    obtain ⟨cW, sW, hW, hliveW, hnW⟩ := hEx
    refine Or.inr (Or.inl ?_)
    intro es c2 s2 hE hlive2
    rcases hpre c2 cW s2 sW (toSeg hE) hW with hfw | hbw
    · exact ⟨cW, sW, hfw, hliveW, hnW⟩
    · exact ⟨c2, s2, .stop _ _, hlive2, watchSeg_not_canRight hbw hnW⟩
  · by_cases hMis : ∃ (c1 : Control) (s1 : GalilVM),
        WatchSeg P q first 2048 cP sP c1 s1 ∧ c1.clock = 1 ∧ LiveScanWatch c1 s1 ∧
          canRight s1.right ∧ read (left s1.left) ≠ read (right s1.right)
    · -- some reachable live landing is an available clock-one mismatch: fallback
      obtain ⟨c1, s1, h1, hclk, hlive1, hav1, hne1⟩ := hMis
      refine Or.inr (Or.inr ?_)
      intro es c2 s2 hE hlive2
      rcases hpre c2 c1 s2 s1 (toSeg hE) h1 with hfw | hbw
      · exact ⟨c2, s2, .stop _ _, hlive2, c1, s1, hfw, hclk, hlive1, hav1, hne1⟩
      · obtain ⟨hc, hs⟩ := watchSeg_stuck_of_mismatch hbw hclk hav1 hne1
        subst hc; subst hs
        exact ⟨_, _, .stop _ _, hlive2, _, _, .stop _ _, hclk, hlive1, hav1, hne1⟩
    · -- neither: every terminal the run hands back is on the shift side
      refine Or.inl ?_
      intro es c2 s2 hE hlive2
      obtain ⟨cT, sT, hseg, hliveT, hT⟩ := hrun es c2 s2 hE hlive2
      obtain ⟨-, -, hT⟩ := hT
      have hreachT : WatchSeg P q first 2048 cP sP cT sT := watchSeg_append (toSeg hE) hseg
      refine ⟨cT, sT, hseg, hliveT, ?_⟩
      rcases hT with h0 | hsg | hnc | hbe
      · exact Or.inl h0
      · exact Or.inr hsg
      · exact absurd ⟨cT, sT, hreachT, hliveT, hnc⟩ hEx
      · obtain ⟨c1, s1, hseg1, hclk, hlive1, hne1⟩ := hbe
        have hreach1 : WatchSeg P q first 2048 cP sP c1 s1 := watchSeg_append hreachT hseg1
        by_cases hav1 : canRight s1.right
        · exact absurd ⟨c1, s1, hreach1, hclk, hlive1, hav1, hne1⟩ hMis
        · exact absurd ⟨c1, s1, hreach1, hlive1, hav1⟩ hEx

/-- **The target — `ExitSplit3C` discharged** under `WatchPrefixC` (and the
preparation landing being live, which `PrepLandingLiveC` supplies). -/
theorem exitSplit3C_of_tick (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (h : ℕ) (cP : Control) (sP : GalilVM)
    (hneP : sP.chain ≠ ChainVM.idle)
    (hpre : WatchPrefixC (PofC centre place entry raw) qq first cP sP) :
    ExitSplit3C centre place entry qq first raw h cP sP :=
  fun hrun => split3_of_prefix (PofC centre place entry raw) qq first h cP sP hneP hpre hrun

/-! ## 4. The consumer -/

/-- **Derived — `CloseoutWatchRound18.foundExit_compare_final9` with
`ExitSplit3C` replaced by `WatchPrefixC`.** -/
theorem foundExit_compare_final10 (centre : GalilVM → Fin 3)
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
    (hpre : WatchPrefixC (PofC centre place entry w) q first cP sP)
    (hfb : FallbackRouteW (PofC centre place entry w) q first w m c r cP sP)
    (hLR : LandingRestartReach (PofC centre place entry w) q first w c r)
    (hstage : ReplayStage w (PofC centre place entry w) q first c r)
    (hmP : cP.mode = .scan) (hrP : cP.replaying = false) (hcP : 1 ≤ cP.clock)
    (hreachWatch : ∃ (es : List Bool) (c2 : Control) (s2 : GalilVM),
      WatchSegE (PofC centre place entry w) q first 2048 es cP sP c2 s2 ∧
        PalPeg.CloseoutWatchRun.LiveScanWatch c2 s2)
    (hat : FoundDpAtC centre place entry q first w lower span h c r)
    (hreach : ShiftReachC centre place entry q first w h)
    (hround : ShiftRoundAtC centre place entry q first w m h lower)
    (hland : ∀ sF : GalilVM,
      PalPeg.CloseoutWatchRound5.BreakLandingC centre place entry q first w h sF cP sP)
    (hstepBreak : ∀ (c0 : Control) (s0 : GalilVM), LiveScanWatch c0 s0 →
      PalPeg.CloseoutWatchRun.RoundStepC (PofC centre place entry w) q first (roundFuel h)
        (BreakTermData centre place entry q first w m h) c0 s0) :
    FoundExit (PofC centre place entry w) q first w m c r := by
  have hsplit3 : ExitSplit3C centre place entry q first w h cP sP :=
    exitSplit3C_of_tick centre place entry q first w h cP sP
      (PalPeg.CloseoutWatchRound2.chain_ne_idle_of_foundCompareCtx hctx) hpre
  exact PalPeg.CloseoutWatchRound18.foundExit_compare_final9 centre place entry q first w m h
    lower span hP hex hready hcan hsane hstart hor hzl hnn hpm hE hsW a ls rs qw gap hprep hmis
    hctx hsplit3 hfb hLR hstage hmP hrP hcP hreachWatch hat hreach hround hland hstepBreak

end PalPeg.CloseoutWatchRound19

#print axioms PalPeg.CloseoutWatchRound19.watchSeg_not_canRight
#print axioms PalPeg.CloseoutWatchRound19.watchSeg_stuck_of_mismatch
#print axioms PalPeg.CloseoutWatchRound19.split3_of_prefix
#print axioms PalPeg.CloseoutWatchRound19.exitSplit3C_of_tick
#print axioms PalPeg.CloseoutWatchRound19.foundExit_compare_final10
