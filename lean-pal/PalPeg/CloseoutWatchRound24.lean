import PalPeg.CloseoutWatchRound22

/-!
# Closeout watch round 24 — half (b) of `WatchFallbackResidC`

`CloseoutWatchRound22.WatchFallbackCostC` is the cost closure of a watch-round
fallback: from the stage entry `⟨c, r⟩`, through the preparation landing
`⟨cP, sP⟩`, the watch segment, the mismatch, the fallback tick and (for `R > 0`)
the replay segment, a `StepsAll` run with a `CostedRun` record, landing in
`InvLP`.

## The three pieces

1. **`stepsAll_entry_to_landing` (closed).**  The run from the stage entry:
   the context's run `⟨c, r⟩ ⇝ ⟨cP, sP⟩` (`EntryCostC`, first conjunct),
   the watch segment (`watchSegE_stepsAll_len` over `SoundOut`, weakened to
   `SoundScanNR`; its sources `EntryCounters raw sP` and `OutputRel raw cP sP`
   are the same premises `CloseoutWatchRound22.watchFallbackC_of_context`
   already takes), the fallback landing run of `FallbackLanding`, and the
   replay run (`ReplayRun`).
2. **`costedRun_of_pieces` (closed modulo ONE hypothesis).**  `costedRun_trans`
   of the entry cost (`EntryCostC`, second conjunct) with the fallback piece
   `FallbackCostPieceC` — the output shape of
   `GalilCostedFallback.costedRun_fallback_replay/zero`, whose inputs (the DP
   `Result`, `hlow`, `chosenRadius`, the tick bound `hfb` of
   `GalilLeafFb.fallback_landing_len_le`) are not among the parameters here;
   the pending ticks of the watch segment are absorbed into the fallback
   piece's `wait`, which is why the piece starts at `sP` (clock `2048`) and not
   at the mismatch.  The right-head bound `≤ 2m − 1` (the region budget of
   `GalilOracleMC4`) rides in the same record.
3. **`invLP_of_landing_replay` (closed modulo ONE hypothesis).**  `R = 0`:
   `CloseoutWatchRound21.invLP_of_fallbackLanding_zero`.  `R > 0`: the
   `invLP_after_replayLanding` pattern on a replay run `ReplayRun` — the first
   disjunct of `GalilReplaySpan.replay_after_fallback_general''_R_of_decodes`
   (or `replay_after_fallback` under `SearchQuiet`, which is false in general).
   `ReplayRunC` names it.

## Named hypotheses (one per piece)

* `EntryCostC` — supplied by the consumer's `FoundCompareCtxC`
  (`WatchSegE … c0 r cF sF` + the found comparison tick), costed with
  `costedRun_watchSegE_closed` and a comparison piece.  Not done here.
* `FallbackCostPieceC` — `costedRun_fallback_replay/zero` + the region budget.
* `ReplayRunC` — `replay_after_fallback_general''_R_of_decodes`, first branch.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutWatchRound24

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
open PalPeg.CloseoutWatchRound21 (FallbackLanding invLP_of_fallbackLanding_zero)
open PalPeg.CloseoutWatchRound22 (WatchFallbackCostC)

/-! ## 1. The named hypotheses -/

/-- **NAMED (open) — piece 1/2 source.**  The costed run from the stage entry to
the preparation landing.  Context field: `FoundCompareCtxC`'s
`WatchSegE … c0 r cF sF` and the found comparison tick. -/
def EntryCostC (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (c : Control) (r : GalilVM) (cP : Control) (sP : GalilVM) : Prop :=
  ∃ (k0 : ℕ) (L0 : List Piece),
    StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k0 ⟨c, r⟩ ⟨cP, sP⟩ ∧
    CostedRun r sP k0 L0

/-- The replay run out of a positive-radius fallback landing: the first
disjunct of `GalilReplaySpan.replay_after_fallback_general''_R_of_decodes`
(with `SoundScanNR` at the landing already discharged). -/
def ReplayRun (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (cT : Control) (sT : GalilVM) (R : ℕ) (esR : List Bool) (c' : Control) (t' : GalilVM) : Prop :=
  WatchSegE P q first 2048 esR cT sT c' t' ∧
    StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) esR.length ⟨cT, sT⟩ ⟨c', t'⟩ ∧
    esR.count true = R ∧ t'.center = sT.center ∧
    PalPeg.GalilReplaySegment.InvScan 2048 raw c' t' R

/-- **NAMED (open) — piece 3 source.**  Every positive-radius fallback landing
out of a watch mismatch has a replay run. -/
def ReplayRunC (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (cP : Control) (sP : GalilVM) : Prop :=
  ∀ (es : List Bool) (c1 : Control) (s1 : GalilVM),
    WatchSegE P q first 2048 es cP sP c1 s1 →
    ∀ (n R : ℕ) (cT : Control) (sT : GalilVM), 0 < R →
      FallbackLanding P q first raw c1 s1 n R cT sT →
      ∃ (esR : List Bool) (c' : Control) (t' : GalilVM), ReplayRun P q first raw cT sT R esR c' t'

/-- **NAMED (open) — piece 2 source.**  The fallback piece from the preparation
landing `sP` (clock `2048`) through the watch segment, the mismatch, the
fallback and the replay run: the output of
`GalilCostedFallback.costedRun_fallback_replay` (`R > 0`) /
`costedRun_fallback_zero` (`R = 0`, `esR = []`), plus the region budget on the
right head. -/
def FallbackCostPieceC (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ)
    (cP : Control) (sP : GalilVM) : Prop :=
  ∀ (es : List Bool) (c1 : Control) (s1 : GalilVM),
    WatchSegE P q first 2048 es cP sP c1 s1 → c1.clock = 1 → canRight s1.right →
    read (left s1.left) ≠ read (right s1.right) →
    ∀ (n R : ℕ) (cT : Control) (sT : GalilVM),
      FallbackLanding P q first raw c1 s1 n R cT sT →
      ∀ (esR : List Bool) (c' : Control) (t' : GalilVM),
        StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) esR.length ⟨cT, sT⟩ ⟨c', t'⟩ →
        ∃ L1 : List Piece,
          CostedRun sP t' (es.length + (1 + (n + 1)) + esR.length) L1 ∧
          position t'.right ≤ 2 * m - 1

/-! ## 2. Piece 1 — the run from the stage entry -/

/-- **Closed.**  The watch segment out of `⟨cP, sP⟩` as a `SoundScanNR` run of
`|es|` ticks, from `EntryCounters raw sP` and `OutputRel raw cP sP`. -/
theorem stepsAll_watchSeg (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) {es : List Bool} {cP c1 : Control} {sP s1 : GalilVM}
    (hseg : WatchSegE (PofC centre place entry raw) q first 2048 es cP sP c1 s1)
    (hEP : EntryCounters raw sP) (houtP : OutputRel raw cP sP) :
    StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048 (SoundScanNR raw)
      es.length ⟨cP, sP⟩ ⟨c1, s1⟩ := by
  obtain ⟨Rad, hi, -, -, -⟩ := id hEP
  exact stepsAll_mono (fun st h _ _ => h)
    (watchSegE_stepsAll_len raw _ (PofC_onLetter _ _ _ _) (PofC_leftFirst _ _ _ _) q first 2048
      hseg (position sP.center) Rad hi houtP)

/-- **Closed.**  Entry → landing → watch segment → fallback landing → replay:
one `StepsAll` run of `k0 + |es| + (1 + (n+1)) + |esR|` ticks. -/
theorem stepsAll_entry_to_landing (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) {k0 : ℕ} {c cP c1 cT c' : Control} {r sP s1 sT t' : GalilVM}
    (hrun : StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048 (SoundScanNR raw)
      k0 ⟨c, r⟩ ⟨cP, sP⟩)
    {es : List Bool}
    (hseg : WatchSegE (PofC centre place entry raw) q first 2048 es cP sP c1 s1)
    (hEP : EntryCounters raw sP) (houtP : OutputRel raw cP sP)
    {n R : ℕ} (hL : FallbackLanding (PofC centre place entry raw) q first raw c1 s1 n R cT sT)
    {esR : List Bool}
    (hrep : StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048 (SoundScanNR raw)
      esR.length ⟨cT, sT⟩ ⟨c', t'⟩) :
    StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048 (SoundScanNR raw)
      (k0 + es.length + (1 + (n + 1)) + esR.length) ⟨c, r⟩ ⟨c', t'⟩ :=
  stepsAll_trans (stepsAll_trans (stepsAll_trans hrun
    (stepsAll_watchSeg centre place entry q first raw hseg hEP houtP)) hL.1) hrep

/-! ## 3. Piece 2 — the cost record -/

/-- **Closed.**  The entry cost and the fallback piece sum. -/
theorem costedRun_of_pieces {r sP t' : GalilVM} {k0 k1 : ℕ} {L0 L1 : List Piece}
    (h0 : CostedRun r sP k0 L0) (h1 : CostedRun sP t' k1 L1) :
    CostedRun r t' (k0 + k1) (L0 ++ L1) :=
  costedRun_trans h0 h1

/-! ## 4. Piece 3 — `InvLP` at the end of the replay -/

/-- **Closed.**  A positive-radius landing followed by a `ReplayRun` is `InvLP`
(the `invLP_after_replayLanding` pattern). -/
theorem invLP_of_landing_replay (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) {k : ℕ} {x : State GalilVM} {cT c' : Control} {sT t' : GalilVM} {R : ℕ}
    (hL : ReplayLanding raw cT sT R) (hS : SpanRep sT) {esR : List Bool}
    (hrep : ReplayRun (PofC centre place entry raw) q first raw cT sT R esR c' t')
    (hall : StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048 (SoundScanNR raw)
      k x ⟨c', t'⟩) :
    InvLP raw c' t' := by
  obtain ⟨hseg, -, hcnt, -, hIS⟩ := hrep
  have hRR : RadiusRep t'.radius R := by
    have h0 := radiusRep_watchSegE _ q first 2048 hseg hL.rest.2.2.2.2.1
    rw [hcnt, Nat.zero_add] at h0
    exact h0
  have hE : EntryCounters raw t' :=
    entryCounters_of_invScan hIS hRR (spanRep_watchSegE _ q first 2048 hseg hS)
      (canonical_length_watchSegE _ q first 2048 hseg hL.rest.2.2.2.2.2.1)
  exact ⟨invL_of_run hall (Or.inr ⟨R, hIS⟩), hE⟩

/-! ## 5. The target -/

/-- **`WatchFallbackCostC` from the three named sources.** -/
theorem watchFallbackCostC_of_context (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) (cP : Control) (sP : GalilVM)
    (hEP : EntryCounters raw sP) (houtP : OutputRel raw cP sP)
    (hentry : EntryCostC (PofC centre place entry raw) q first raw c r cP sP)
    (hpiece : FallbackCostPieceC (PofC centre place entry raw) q first raw m cP sP)
    (hreplay : ReplayRunC (PofC centre place entry raw) q first raw cP sP) :
    WatchFallbackCostC centre place entry q first raw m c r cP sP := by
  intro es c1 s1 hseg hlive hclk hav hne n R cT sT hL
  obtain ⟨k0, L0, hrun, hcost0⟩ := hentry
  -- centre: `r ≤ sP = s1`
  have hr1 : position r.center ≤ position s1.center := by
    rw [watchSegE_center _ q first 2048 hseg]
    have := hcost0.centre
    omega
  rcases Nat.eq_zero_or_pos R with hR0 | hRpos
  · -- radius `0`: no replay, `t' = sT`
    subst hR0
    have hsound : SoundScanNR raw ⟨cT, sT⟩ := stepsAll_last hL.1
    have hrep0 : StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048
        (SoundScanNR raw) ([] : List Bool).length ⟨cT, sT⟩ ⟨cT, sT⟩ := .zero _ hsound
    obtain ⟨L1, hcost1, hbound⟩ := hpiece es c1 s1 hseg hclk hav hne n 0 cT sT hL [] cT sT hrep0
    refine ⟨cT, sT, k0 + es.length + (1 + (n + 1)) + ([] : List Bool).length, L0 ++ L1,
      stepsAll_entry_to_landing centre place entry q first raw hrun hseg hEP houtP hL hrep0,
      ?_, invLP_of_fallbackLanding_zero hL, le_rfl, hr1, hbound⟩
    have := costedRun_of_pieces hcost0 hcost1
    rwa [show k0 + (es.length + (1 + (n + 1)) + ([] : List Bool).length) =
      k0 + es.length + (1 + (n + 1)) + ([] : List Bool).length by omega] at this
  · -- radius `R > 0`: the replay run
    obtain ⟨esR, c', t', hrep⟩ := hreplay es c1 s1 hseg n R cT sT hRpos hL
    obtain ⟨-, hrepAll, -, hcen, -⟩ := id hrep
    obtain ⟨L1, hcost1, hbound⟩ :=
      hpiece es c1 s1 hseg hclk hav hne n R cT sT hL esR c' t' hrepAll
    have hall := stepsAll_entry_to_landing centre place entry q first raw hrun hseg hEP houtP hL
      hrepAll
    refine ⟨c', t', k0 + es.length + (1 + (n + 1)) + esR.length, L0 ++ L1, hall, ?_,
      invLP_of_landing_replay centre place entry q first raw (hL.2.2.2.1 hRpos) hL.2.2.2.2 hrep
        hall, by rw [hcen], hr1, hbound⟩
    have := costedRun_of_pieces hcost0 hcost1
    rwa [show k0 + (es.length + (1 + (n + 1)) + esR.length) =
      k0 + es.length + (1 + (n + 1)) + esR.length by omega] at this

end PalPeg.CloseoutWatchRound24

#print axioms PalPeg.CloseoutWatchRound24.stepsAll_watchSeg
#print axioms PalPeg.CloseoutWatchRound24.stepsAll_entry_to_landing
#print axioms PalPeg.CloseoutWatchRound24.costedRun_of_pieces
#print axioms PalPeg.CloseoutWatchRound24.invLP_of_landing_replay
#print axioms PalPeg.CloseoutWatchRound24.watchFallbackCostC_of_context
