import PalPeg.CloseoutWatchRound24

/-!
# Closeout watch round 28 — `ReplayRunC` and `FallbackCostPieceC`

Both named hypotheses of `CloseoutWatchRound24` are discharged from explicit,
named inputs.

## (1) `replayRunC_of_decodes`

`GalilReplaySpan.replay_after_fallback_general''_R_of_decodes` at the
`ReplayLanding` of a watch-mode fallback landing.  Its three branches:

* **first** — the replay run; this is `ReplayRun` except that the `StepsAll`
  is guarded by `SoundScanNR raw ⟨c', t'⟩`.  `InvScan` gives `c'.mode = scan`
  and `c'.replaying = false`, so the guard is exactly `OutputRel raw c' t'` at
  the replay landing — the `houtReplay` leaf, refuted in the universal form
  (`GalilLeafOutReplay`), so it is a named hypothesis restricted to replay
  landings (`ReplayOutC`).
* **`ChainEnd`** / **`BrokeAndRestarted`** — a chain *started during the
  replay* survives to / breaks before the landing.  The fresh landing's chain
  is idle (`Restarted`) and `ShiftIdle`, but nothing at the landing prevents a
  found tick inside the replay from starting a chain, so neither branch is
  excluded by the landing data alone; `ReplayNoBusyC` names the exclusion.

## (2) `fallbackCostPieceC_of_inputs`

`GalilCostedFallback.costedRun_fallback_replay` (uniform in `R`, including
`R = 0` with `esR = []`, exactly as `costedRun_fallback_zero` is derived from
it) with its inputs bundled in `FallbackCostInputsC`, and the region budget
`position sP.right + #true ≤ 2m − 2` (`GalilOracleMC4`'s `≤ 2m − 2` at the
segment end) converted through `right_position` into
`position (right s1.right) ≤ 2m − 1`, the right head of the replay landing.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutWatchRound28

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton PalPeg.GalilOracleDischarge PalPeg.GalilOracleLocal
open PalPeg.GalilCheckpoints PalPeg.GalilTraceCost PalPeg.GalilLexMeasure
open PalPeg.GalilInvPlus PalPeg.GalilInvPlus2 PalPeg.GalilOracleMC
open PalPeg.GalilGlueBLeaves PalPeg.GalilBranchInvariants2 PalPeg.GalilSegmentConstruct
open PalPeg.GalilOracleM PalPeg.GalilOracleMC2 PalPeg.GalilOracleGlueB
open PalPeg.CloseoutContracts
open PalPeg.GalilOneFallback PalPeg.GalilCostedFallback PalPeg.GalilIntervalCost
open PalPeg.CloseoutWatchRound21 (FallbackLanding)
open PalPeg.CloseoutWatchRound24 (ReplayRun ReplayRunC FallbackCostPieceC)
open PalPeg.GalilReplaySpan (ChainEnd BrokeAndRestarted ReadyClosure ReplayBudgetRD RestartShapeL)

/-! ## 1. `ReplayRunC` -/

/-- **NAMED (open).**  Output soundness at the landing of the replay run out
of a watch-mode fallback landing (the `houtReplay` leaf, restricted to replay
landings reached from `⟨cP, sP⟩`). -/
def ReplayOutC (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (cP : Control) (sP : GalilVM) : Prop :=
  ∀ (es : List Bool) (c1 : Control) (s1 : GalilVM),
    WatchSegE P q first 2048 es cP sP c1 s1 →
    ∀ (n R : ℕ) (cT : Control) (sT : GalilVM), 0 < R →
      FallbackLanding P q first raw c1 s1 n R cT sT →
      ∀ (esR : List Bool) (c' : Control) (t' : GalilVM),
        WatchSegE P q first 2048 esR cT sT c' t' →
        PalPeg.GalilReplaySegment.InvScan 2048 raw c' t' R →
        OutputRel raw c' t'

/-- **NAMED (open).**  No chain started inside the replay out of a watch-mode
fallback landing survives to the landing or breaks (branches (ii)/(iii) of
`replay_after_fallback_general''_R_of_decodes`). -/
def ReplayNoBusyC (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (cP : Control) (sP : GalilVM) : Prop :=
  ∀ (es : List Bool) (c1 : Control) (s1 : GalilVM),
    WatchSegE P q first 2048 es cP sP c1 s1 →
    ∀ (n R : ℕ) (cT : Control) (sT : GalilVM), 0 < R →
      FallbackLanding P q first raw c1 s1 n R cT sT →
      ¬ ChainEnd raw P q first 2048 (position sT.right + R) cT sT 0 R ∧
      ¬ BrokeAndRestarted raw P q first 2048 cT sT

/-- **`ReplayRunC` from the first branch of
`replay_after_fallback_general''_R_of_decodes`.** -/
theorem replayRunC_of_decodes (raw : List (Fin 2)) (P : Shared)
    (hP : P.onLetter = onLetterVM raw) (hP' : P.leftFirst = leftFirstVM) (q : ℕ) (first : Fin 9)
    (hex : ∀ s, P.replayExhausted s = zero s.replay)
    (hsearch : ∀ s : GalilVM, SearchReady (searchLens.get s) → ∀ a : Bool,
      ∃ v, searchEffect P a s v)
    {Rd : Control → GalilVM → Prop} (hcl : ReadyClosure raw P q first 2048 Rd)
    (hdec : Decodes P) (hbudget : ReplayBudgetRD raw P q first 2048)
    (hrs : RestartShapeL P)
    (cP : Control) (sP : GalilVM)
    (hout : ReplayOutC P q first raw cP sP) (hbusy : ReplayNoBusyC P q first raw cP sP) :
    ReplayRunC P q first raw cP sP := by
  intro es c1 s1 hseg n R cT sT hR hL
  have hRL : ReplayLanding raw cT sT R := hL.2.2.2.1 hR
  rcases PalPeg.GalilReplaySpan.replay_after_fallback_general''_R_of_decodes raw P hP hP' q first
      hex hsearch hcl hdec hbudget hrs R hR cT sT hRL.mode hRL.clock hRL.replaying hRL.rest
      hRL.replay hRL.minv hRL.frontier hRL.shiftIdle with
    ⟨esR, c', t', hsegR, hrun, -, hcnt, -, hcen, hIS⟩ | hCE | ⟨hBR, -⟩
  · refine ⟨esR, c', t', hsegR, hrun ?_, hcnt, hcen, hIS⟩
    intro _ _
    exact hout es c1 s1 hseg n R cT sT hR hL esR c' t' hsegR hIS
  · exact absurd hCE (hbusy es c1 s1 hseg n R cT sT hR hL).1
  · exact absurd hBR (hbusy es c1 s1 hseg n R cT sT hR hL).2

#print axioms replayRunC_of_decodes

/-! ## 2. `FallbackCostPieceC` -/

/-- **NAMED (open).**  The inputs of `costedRun_fallback_replay` at a watch
mismatch `⟨c1, s1⟩` reached from `⟨cP, sP⟩`, its fallback landing `⟨cT, sT⟩`
and a replay run to `⟨c', t'⟩`.  Suppliers:
* `hkC`, `hv`/`ℓ` — the mismatch state (`FoundCompareCtxC` + the watch segment);
* `hdec`, `hraw`, `hR`, `hfb`, `hpos`, `hCR` — `GalilLeafFb.fallback_landing_len_le`
  at the mismatch (`fb = n + 1`);
* `hraw₀`, `hC₀`, `hspan`, `hres`, `hidle` — the DP `Result` at the centre
  (`PrepInputsG3`);
* `hlow` — the stage failure `StageFailed` (`MismatchDp`);
* `hes`, `hrr`, `hcc` — the replay run (first branch of
  `replay_after_fallback_general''_R_of_decodes`: `es.length = r·2048`,
  `position t'.right = position t.right + r`, `t'.center = t.center`). -/
def FallbackCostInputsC (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (cP : Control) (sP : GalilVM) : Prop :=
  ∀ (es : List Bool) (c1 : Control) (s1 : GalilVM),
    WatchSegE P q first 2048 es cP sP c1 s1 → c1.clock = 1 → canRight s1.right →
    read (left s1.left) ≠ read (right s1.right) →
    ∀ (n R : ℕ) (cT : Control) (sT : GalilVM),
      FallbackLanding P q first raw c1 s1 n R cT sT →
      ∀ (esR : List Bool) (c' : Control) (t' : GalilVM),
        StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) esR.length ⟨cT, sT⟩ ⟨c', t'⟩ →
        ∃ (Rad ℓ : ℕ) (a : Fin 2) (xs rs' q' : List (Fin 2))
          (a₀ : Fin 2) (ls₀ rs₀ q₀ : List (Fin 2)) (gap₀ : Bool) (lower span : ℕ)
          (y : GalilFppWide.Config 12),
          ScanInvariant raw (position s1.center) Rad s1.left s1.right ∧
          RadiusRep s1.radius Rad ∧
          value s1.length = ℓ ∧ Rad < position s1.center ∧
          right s1.right = represent ⟨a :: xs,(right s1.right).gap⟩ (rs'.map some) q' ∧
          raw = (a :: xs).reverse ++ rs' ++ q' ∧
          raw = (a₀ :: ls₀).reverse ++ rs₀ ++ q₀ ∧
          position s1.center = position (represent ⟨a₀ :: ls₀,gap₀⟩ (rs₀.map some) q₀) ∧
          Rad ≤ span ∧
          GalilDpCorrect.Result
            ((GalilScaffoldPlace.stream ⟨a₀ :: ls₀,gap₀⟩).take (span+1)) lower 0 y ∧
          y.pc = 347 ∧
          (∀ δ, 0 < δ → δ ≤ lower →
            ¬ HasPeriod (Span raw (position s1.center) Rad) (2*δ)) ∧
          R = chosenRadius
            ((GalilScaffoldPlace.stream ⟨a :: xs,(right s1.right).gap⟩).take (ℓ+1)) ∧
          n + 1 ≤ 1588*(ℓ+1) + 836 ∧
          esR.length = R * 2048 ∧
          position sT.center = position (right s1.right) - R ∧ sT.center = sT.right ∧
          position t'.right = position sT.right + R ∧ t'.center = sT.center

/-- **NAMED (open).**  The region budget at the preparation landing:
`position sP.right + #true ≤ 2m − 2` along every watch segment
(`GalilOracleMC4`, the `≤ 2m − 2` handed to the segment-ending leaves). -/
def RegionBudgetC (P : Shared) (q : ℕ) (first : Fin 9) (m : ℕ)
    (cP : Control) (sP : GalilVM) : Prop :=
  ∀ (es : List Bool) (c1 : Control) (s1 : GalilVM),
    WatchSegE P q first 2048 es cP sP c1 s1 →
    position sP.right + es.count true ≤ 2 * m - 2

/-- **`FallbackCostPieceC` from `costedRun_fallback_replay` and the named
inputs.**  `EntryCounters raw sP` is the premise
`CloseoutWatchRound24.watchFallbackCostC_of_context` already takes; `1 ≤ m` is
`GalilOracleMC4`'s standing bound (at `m = 0` the ℕ-subtraction claim is false). -/
theorem fallbackCostPieceC_of_inputs (P : Shared) (q : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m : ℕ) (hm1 : 1 ≤ m) (cP : Control) (sP : GalilVM)
    (hEP : EntryCounters raw sP) (hcP : cP.clock ≤ 2048)
    (hin : FallbackCostInputsC P q first raw cP sP)
    (hbud : RegionBudgetC P q first m cP sP) :
    FallbackCostPieceC P q first raw m cP sP := by
  intro es c1 s1 hseg hclk hav hne n R cT sT hL esR c' t' hrep
  obtain ⟨Rad0, hi0, hRR0, hS0, hcan0⟩ := hEP
  obtain ⟨Rad, ℓ, a, xs, rs', q', a₀, ls₀, rs₀, q₀, gap₀, lower, span, y,
    hi, hRR, hv, hkC, hdec, hraw, hraw₀, hC₀, hspan, hres, hidle, hlow, hR, hfb, hes,
    hpos, hCR, hrr, hcc⟩ := hin es c1 s1 hseg hclk hav hne n R cT sT hL esR c' t' hrep
  have hS : SpanRep s1 := spanRep_watchSegE P q first 2048 hseg hS0
  obtain ⟨L, w, hw, e, hcost, -, -, -, -, -, hend⟩ :=
    costedRun_fallback_replay raw P q first hseg hi0 hcP hclk (t := sT) (t' := t') hi hav hRR hS
      ℓ hv hkC a xs rs' q' hdec hraw a₀ ls₀ rs₀ q₀ gap₀ hraw₀ hC₀ hspan hres hidle hlow
      (n + 1) esR R hR hfb hes hpos hCR hrr hcc
  refine ⟨L ++ [fbPiece (position (right s1.right)) w hw e], ?_, ?_⟩
  · rwa [show es.length + (1 + (n + 1)) + esR.length = es.length + 1 + (n + 1) + esR.length
      by omega]
  · -- the region budget: `s1.right = sP.right + #true`, and `right` steps once
    obtain ⟨hi1, hp1⟩ := watchSegE_right_position raw P q first 2048 hseg hi0
    have hstep : position (right s1.right) = position s1.right + 1 :=
      right_position s1.right hav (represented_position _ raw hi1.rightRep hi1.rightPresent).1
    have hb := hbud es c1 s1 hseg
    rw [hend, hstep, hp1]
    omega

#print axioms fallbackCostPieceC_of_inputs

end PalPeg.CloseoutWatchRound28
