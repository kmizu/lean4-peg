import PalPeg.CopyPhaseNoShift
import PalPeg.CloseoutWatchRound21

/-!
# Closeout watch round 22 — `WatchFallbackC` from the landing sources

`CloseoutWatchRound21.WatchFallbackC` bundles, at every clock-`1` available
outer mismatch of a watching chain reached from the preparation landing
`⟨cP, sP⟩`, (a) the tick pack `ShiftIdle ∧ MInv ∧ FallbackCounters ∧
FallbackTick ∧ OutputRel` and (b) the cost closure from the stage entry.

## What is derived here

* **(a), the four transported conjuncts.**  `ShiftIdle` (the shift counter is
  segment-constant, `watchSegE_remaining`), `MInv` (`minv_watchSegE`),
  `FallbackCounters` (`fallbackCounters_of_seg` over `watchSegE_center`) and
  `OutputRel` (`watchSegE_outputM`) are carried along the `WatchSegE` from
  their sources at `⟨cP, sP⟩` — `tickPack_of_landing`.
* **(a), `FallbackTick` from the guard alone.**  At a *watching* chain the
  search witness is free (`searchEffect` is the identity on a non-idle chain),
  and the chain clause of `chainAt` is the first disjunct, so `FallbackTick`
  reduces to one disabled chain tick `z` together with the failure of
  `shiftGuardVM` after the mismatch — `fallbackTick_of_watchTick`.

## What is NOT derivable, and why: the shift/fallback decision

The prompt's premise "shift requires the chain to be at a match, so a mismatch
cannot shift" is **false on the machine**.  In `ScaffoldGalil.stepScan` the
shift branch is tested *only* on the outer-mismatch side:

    if (left.read() == right.read()) matchedPlace()
    else if (!replaying && chain.canShift && chain.prediction() == right.read()) beginChainShift()
    else beginFallback()

`canShift` (`watch ∧ lag = 0 ∧ phase = 4 ∧ (periodOnly → cycleEnd | margin ≥ 0)`)
and `prediction()` (the period symbol under the focus) never consult the outer
symbols.  In the Lean model the disabled watch tick is
`GalilScaffoldChainWatch.Internal` (`ChainTick false (.watch w) z`), which does
not read `left`/`right` either, so `shiftGuardVM (afterMismatch s1 vs vq)` is
independent of `read (left s1.left) ≠ read (right s1.right)`: a watching
mismatch whose chain predicts the *right* symbol is precisely the shift exit.
Hence `FallbackTick`'s `¬ shiftGuardVM` clause is a genuine classifier and
stays a hypothesis.

## The ONE hypothesis left: `WatchFallbackResidC`

Two conjuncts, one per half of `WatchFallbackC`:

1. **(a)-residual** `WatchMismatchNoShiftC`: at each such mismatch a disabled
   chain tick exists and every disabled chain tick fails the shift guard — the
   same shape `CloseoutPrepInputs2.MismatchExitG` takes as a premise and
   `CloseoutPrepInputs3.prep_of_prepInputsG3` *discharges* for a preparing
   chain.  For a watching chain it is the shift/fallback dichotomy above and
   should be supplied by the exit classifier (`ExitSplit3C`'s fallback family
   `TerminalRunFallbackC` currently lands at `BreakEndAvC`, which does not
   record it).
2. **(b)** `WatchFallbackCostC`: the cost closure, verbatim the second conjunct
   of `WatchFallbackC` (Round 21's reasons stand: no run from `⟨c, r⟩` to
   `⟨cP, sP⟩` is in scope, and `CostedRun` pieces are clock-`2048` aligned).

The four sources at `⟨cP, sP⟩` (`ShiftIdle sP`, `MInv raw cP sP`,
`EntryCounters raw sP`, `OutputRel raw cP sP`) are taken as premises of the
consumer theorem; their derivation from `FoundCompareCtxC` is not done here.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutWatchRound22

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton PalPeg.GalilOracleDischarge PalPeg.GalilOracleLocal
open PalPeg.GalilCheckpoints PalPeg.GalilTraceCost PalPeg.GalilLexMeasure
open PalPeg.GalilInvPlus PalPeg.GalilInvPlus2 PalPeg.GalilOracleMC
open PalPeg.GalilGlueBLeaves PalPeg.GalilBranchInvariants2 PalPeg.GalilSegmentConstruct
open PalPeg.GalilOracleM PalPeg.GalilOracleMC2 PalPeg.GalilOracleGlueB
open PalPeg.CloseoutContracts
open PalPeg.CloseoutWatchRun (LiveScanWatch)
open PalPeg.CloseoutWatchRound21 (FallbackLanding WatchFallbackC)
open PalPeg.GalilLeafOutReplay (watchSegE_outputM)

/-! ## 1. `FallbackTick` at a watching chain, from the guard alone -/

/-- **Derived.**  At a watching chain, one disabled chain tick `z` whose
post-mismatch state fails the shift guard is all `FallbackTick` needs: the
search witness is `searchLens.get s1` (the chain is not idle), and the chain
clause is the first disjunct of `chainAt`. -/
theorem fallbackTick_of_watchTick (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry : ℕ) (raw : List (Fin 2))
    {s1 : GalilVM} (hne : s1.chain ≠ ChainVM.idle)
    {z : ChainVM} (htick : ChainTick false s1.chain z)
    (hg : ¬ shiftGuardVM (afterMismatch s1 ⟨left s1.left, right s1.right, z⟩ (searchLens.get s1))) :
    FallbackTick centre place entry raw s1 := by
  refine ⟨⟨⟨left s1.left, right s1.right, z⟩, searchLens.get s1, rfl, rfl, Or.inr ⟨hne, rfl⟩,
    Or.inl ⟨hne, htick⟩, hg⟩⟩

/-! ## 2. The four transported conjuncts -/

/-- **Derived.**  `ShiftIdle`, `MInv`, `FallbackCounters` and `OutputRel` at a
segment landing, from their sources at the segment's start. -/
theorem tickPack_of_landing (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2))
    (hex : ∀ s, (PofC centre place entry raw).replayExhausted s = zero s.replay)
    {es : List Bool} {cP c1 : Control} {sP s1 : GalilVM}
    (hseg : WatchSegE (PofC centre place entry raw) q first 2048 es cP sP c1 s1)
    (hav : canRight s1.right)
    (hsiP : ShiftIdle sP) (hMP : MInv raw cP sP) (hEP : EntryCounters raw sP)
    (houtP : OutputRel raw cP sP) :
    ShiftIdle s1 ∧ MInv raw c1 s1 ∧ FallbackCounters raw s1 ∧ OutputRel raw c1 s1 := by
  obtain ⟨Rad, hi, -, -, -⟩ := id hEP
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [shiftIdle_iff, watchSegE_remaining _ q first 2048 hseg]
    exact (shiftIdle_iff sP).1 hsiP
  · exact minv_watchSegE raw _ hex q first 2048 hseg Rad hi hMP
  · exact fallbackCounters_of_seg _ q first 2048 hseg (watchSegE_center _ q first 2048 hseg)
      hEP hav
  · exact watchSegE_outputM raw _ (PofC_onLetter _ _ _ _) (PofC_leftFirst _ _ _ _) q first 2048
      hseg (position sP.center) Rad hi (Or.inl houtP)

/-! ## 3. The one hypothesis -/

/-- **(a)-residual.**  At every clock-`1` available mismatch reached from `⟨cP, sP⟩`
whose chain is in a **tickable phase**: a disabled chain tick exists, and every
disabled chain tick fails the shift guard after the mismatch.

**n130/n131**: guard を `LiveScanWatch` から `LiveScanTickable` に広げた。
copy/back 相でも成り立ち（`CopyPhaseNoShift.watchMismatchNoShift_parts_of_copyOrBack`）、
found 誕生直後の不一致 fallback がこの契約に載る。 -/
def WatchMismatchNoShiftC (P : Shared) (q : ℕ) (first : Fin 9)
    (cP : Control) (sP : GalilVM) : Prop :=
  ∀ (es : List Bool) (c1 : Control) (s1 : GalilVM),
    WatchSegE P q first 2048 es cP sP c1 s1 →
    PalPeg.CopyPhaseNoShift.LiveScanTickable c1 s1 →
    c1.clock = 1 → canRight s1.right →
    read (left s1.left) ≠ read (right s1.right) →
    (∃ z, ChainTick false s1.chain z) ∧
    (∀ (vs : ScanVM) (vq : SearchVM), ChainTick false s1.chain vs.chain →
      ¬ shiftGuardVM (afterMismatch s1 vs vq))

/-- **(b).**  The cost closure — the second conjunct of `WatchFallbackC`,
verbatim. -/
def WatchFallbackCostC (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ)
    (c : Control) (r : GalilVM) (cP : Control) (sP : GalilVM) : Prop :=
  ∀ (es : List Bool) (c1 : Control) (s1 : GalilVM),
    WatchSegE (PofC centre place entry raw) q first 2048 es cP sP c1 s1 →
    PalPeg.CopyPhaseNoShift.LiveScanTickable c1 s1 →
    c1.clock = 1 → canRight s1.right →
    read (left s1.left) ≠ read (right s1.right) →
    ∀ (n R : ℕ) (cT : Control) (sT : GalilVM),
      FallbackLanding (PofC centre place entry raw) q first raw c1 s1 n R cT sT →
      ∃ (cT' : Control) (sT' : GalilVM) (k : ℕ) (L : List Piece),
        StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048 (SoundScanNR raw) k
          ⟨c, r⟩ ⟨cT', sT'⟩ ∧
        CostedRun r sT' k L ∧ InvLP raw cT' sT' ∧
        position sT.center ≤ position sT'.center ∧ position r.center ≤ position s1.center ∧
        position sT'.right ≤ 2 * m - 1

/-- **NAMED (open) — the ONE hypothesis.**  Conjunct 1 is half (a) of
`WatchFallbackC` reduced to the shift/fallback decision; conjunct 2 is half (b). -/
def WatchFallbackResidC (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ)
    (c : Control) (r : GalilVM) (cP : Control) (sP : GalilVM) : Prop :=
  WatchMismatchNoShiftC (PofC centre place entry raw) q first cP sP ∧
    WatchFallbackCostC centre place entry q first raw m c r cP sP

/-! ## 4. The consumer -/

/-- **`WatchFallbackC` from the landing sources and the residual.** -/
theorem watchFallbackC_of_context (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) (cP : Control) (sP : GalilVM)
    (hex : ∀ s, (PofC centre place entry raw).replayExhausted s = zero s.replay)
    (hsiP : ShiftIdle sP) (hMP : MInv raw cP sP) (hEP : EntryCounters raw sP)
    (houtP : OutputRel raw cP sP)
    (hres : WatchFallbackResidC centre place entry q first raw m c r cP sP) :
    WatchFallbackC centre place entry q first raw m c r cP sP := by
  intro es c1 s1 hseg hlive hclk hav hne
  obtain ⟨hns, hcost⟩ := hres
  obtain ⟨⟨z, hz⟩, hg⟩ := hns es c1 s1 hseg hlive hclk hav hne
  have hneChain : s1.chain ≠ ChainVM.idle :=
    PalPeg.CopyPhaseNoShift.liveScanTickable_ne_idle hlive
  obtain ⟨hsi, hM, hK, hout⟩ :=
    tickPack_of_landing centre place entry q first raw hex hseg hav hsiP hMP hEP houtP
  refine ⟨⟨hsi, hM, hK, ?_, hout⟩, hcost es c1 s1 hseg hlive hclk hav hne⟩
  exact fallbackTick_of_watchTick centre place entry raw hneChain hz
    (hg ⟨left s1.left, right s1.right, z⟩ (searchLens.get s1) hz)

end PalPeg.CloseoutWatchRound22

#print axioms PalPeg.CloseoutWatchRound22.fallbackTick_of_watchTick
#print axioms PalPeg.CloseoutWatchRound22.tickPack_of_landing
#print axioms PalPeg.CloseoutWatchRound22.watchFallbackC_of_context
