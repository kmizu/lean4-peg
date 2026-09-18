import PalPeg.CloseoutWatchRound35

/-!
# Closeout watch round 36 — `ReplayRunW`: the replay run widened to all three
landings, no busy-exclusion

`CloseoutWatchRound35` established that `ReplayNoBusyC` is false in general (a
watch chain may start inside the replay), so `replayRunC_of_decodes`
(`CloseoutWatchRound28`) cannot be closed.  This round replaces `ReplayRun` by
`ReplayRunW`, which consumes **all three** branches of
`GalilReplaySpan.replay_after_fallback_general''_R_of_decodes`:

* (i) the replay run (`ReplayRun`; its `StepsAll` guard is discharged by
  `replayOutC_of_landing`, unconditional);
* (ii) `ChainEnd` — the last chain started in the replay survives to the span
  end (a scan landing with a live chain, `t.chain ≠ .idle`);
* (iii) `BrokeAndRestarted` with the idle landing the theorem already supplies
  (`InvScan ∧ OutputRel`, so its `StepsAll` guard is discharged outright).

`replayRunW_of_decodes` needs **no** `ReplayOutC` / `ReplayNoBusyC`.  The
consumers `fallbackReachS_of_context'` and `foundExit_compare_final15` are
re-derived with `ReplayRunWC`; branch (i) is Round 31's proof verbatim, and
branches (ii)/(iii) each leave exactly one named route hypothesis:

* `ChainEndLandingC` — from the `ChainEnd` landing (chain live, clock `2048`,
  replaying off) the chain's own round ends in a shift/fallback landing that is
  `InvLPS`, with its cost and the right-head budget.  Supplier: the shift/fallback
  route of the chain's round (`CloseoutWatchRound15.roundsRouteLP_of_tail` /
  `ShiftTailC` pattern, with `ChainW` at window `B` as the chain state).
* `RestartLandingC` — the (iii) landing is `InvScan R ∧ OutputRel`, centre kept,
  right head `+ R`; what is missing is `RadiusRep`/`SpanRep` (no `WatchSegE`
  through the break, so `radiusRep_watchSegE` does not apply), the
  `ReplayStage` witness, and the cost piece from `⟨cT, sT⟩`.  Supplier: a
  `BrokeAndRestarted`-aware variant of `invLP_of_landing_replay` +
  `replayStage_after_replayLanding` (`GalilInvPlus3`), with the cost from
  `costedRun_fallback_replay` uniform in the break.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutWatchRound36

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton PalPeg.GalilOracleDischarge PalPeg.GalilOracleLocal
open PalPeg.GalilCheckpoints PalPeg.GalilTraceCost PalPeg.GalilLexMeasure
open PalPeg.GalilInvPlus PalPeg.GalilInvPlus2 PalPeg.GalilOracleMC
open PalPeg.GalilGlueBLeaves PalPeg.GalilBranchInvariants2 PalPeg.GalilSegmentConstruct
open PalPeg.GalilOracleM PalPeg.GalilOracleMC2 PalPeg.GalilOracleGlueB
open PalPeg.GalilFoundStage
open PalPeg.GalilInvPlus3 (InvLPS replayStage_after_replayLanding)
open PalPeg.CloseoutContracts
open PalPeg.CloseoutWatchRun (LiveScanWatch roundFuel)
open PalPeg.CloseoutWatchPhase (LandingRestart)
open PalPeg.CloseoutWatchRound2 (FoundCompareCtxC)
open PalPeg.CloseoutWatchRound3 (DistanceNonnegC)
open PalPeg.CloseoutWatchRound6 (RightCanC RightSaneC StartLeC LedgerOriginC PeriodMatchC)
open PalPeg.CloseoutWatchRound4 (ZeroLagAtMatchC)
open PalPeg.CloseoutWatchRound7 (PrepLandingWatchC ShiftReachC ShiftRoundAtC BreakTermData)
open PalPeg.CloseoutWatchRound10 (FoundDpAtC)
open PalPeg.CloseoutPrepInputs2 (MismatchExitG)
open PalPeg.CloseoutPrepInputs3 (PrepInputsG3)
open PalPeg.CloseoutWatchRound21 (FallbackLanding fallbackLanding_of_pack
  invLP_of_fallbackLanding_zero)
open PalPeg.CloseoutWatchRound22 (WatchMismatchNoShiftC tickPack_of_landing
  fallbackTick_of_watchTick)
open PalPeg.CloseoutWatchRound24 (EntryCostC FallbackCostPieceC ReplayRun
  stepsAll_entry_to_landing costedRun_of_pieces invLP_of_landing_replay)
open PalPeg.CloseoutWatchRound25 (MismatchShiftRouteC)
open PalPeg.CloseoutWatchRound29 (landingRestart_of_fallbackLanding_zero)
open PalPeg.CloseoutWatchRound31 (FoundExitLPS FallbackReachS foundExit_compare_final14)
open PalPeg.CloseoutWatchRound35 (replayOutC_of_landing)
open PalPeg.GalilReplaySpan (ChainEnd BrokeAndRestarted ReadyClosure ReplayBudgetRD RestartShapeL)

/-! ## 1. `ReplayRunW` -/

/-- **`ReplayRun` widened to the three landing shapes of
`replay_after_fallback_general''_R_of_decodes`.**  (i) a replay run to an
`InvScan` landing; (ii) `ChainEnd` at the span end `position sT.right + R`;
(iii) a chain broke and the search restarted, then an idle replay landing
(`InvScan ∧ OutputRel`, unguarded `StepsAll`). -/
def ReplayRunW (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (cT : Control) (sT : GalilVM) (R : ℕ) : Prop :=
  (∃ (esR : List Bool) (c' : Control) (t' : GalilVM), ReplayRun P q first raw cT sT R esR c' t') ∨
  ChainEnd raw P q first 2048 (position sT.right + R) cT sT 0 R ∨
  (BrokeAndRestarted raw P q first 2048 cT sT ∧
    ∃ (n : ℕ) (c' : Control) (t' : GalilVM),
      StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) n ⟨cT, sT⟩ ⟨c', t'⟩ ∧
      position t'.right = position sT.right + R ∧ t'.center = sT.center ∧
      PalPeg.GalilReplaySegment.InvScan 2048 raw c' t' R ∧ OutputRel raw c' t')

/-- `ReplayRunC` with `ReplayRunW` in place of `ReplayRun`. -/
def ReplayRunWC (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (cP : Control) (sP : GalilVM) : Prop :=
  ∀ (es : List Bool) (c1 : Control) (s1 : GalilVM),
    WatchSegE P q first 2048 es cP sP c1 s1 →
    ∀ (n R : ℕ) (cT : Control) (sT : GalilVM), 0 < R →
      FallbackLanding P q first raw c1 s1 n R cT sT →
      ReplayRunW P q first raw cT sT R

/-- **`ReplayRunWC` from all three branches, with no busy-exclusion and no
output hypothesis** (`replayOutC_of_landing` closes the (i) guard, the (iii)
landing carries its own `OutputRel`). -/
theorem replayRunW_of_decodes (raw : List (Fin 2)) (P : Shared)
    (hP : P.onLetter = onLetterVM raw) (hP' : P.leftFirst = leftFirstVM) (q : ℕ) (first : Fin 9)
    (hex : ∀ s, P.replayExhausted s = zero s.replay)
    (hsearch : ∀ s : GalilVM, SearchReady (searchLens.get s) → ∀ a : Bool,
      ∃ v, searchEffect P a s v)
    {Rd : Control → GalilVM → Prop} (hcl : ReadyClosure raw P q first 2048 Rd)
    (hdec : Decodes P) (hbudget : ReplayBudgetRD raw P q first 2048)
    (hrs : RestartShapeL P)
    (cP : Control) (sP : GalilVM) :
    ReplayRunWC P q first raw cP sP := by
  intro es c1 s1 hseg n R cT sT hR hL
  have hRL : ReplayLanding raw cT sT R := hL.2.2.2.1 hR
  have hout := replayOutC_of_landing raw P hP hP' q first cP sP
  rcases PalPeg.GalilReplaySpan.replay_after_fallback_general''_R_of_decodes raw P hP hP' q first
      hex hsearch hcl hdec hbudget hrs R hR cT sT hRL.mode hRL.clock hRL.replaying hRL.rest
      hRL.replay hRL.minv hRL.frontier hRL.shiftIdle with
    ⟨esR, c', t', hsegR, hrun, -, hcnt, -, hcen, hIS⟩ | hCE | ⟨hBR, n', c', t', hst, hpos, hcen, hIS, hO⟩
  · refine Or.inl ⟨esR, c', t', hsegR, hrun ?_, hcnt, hcen, hIS⟩
    intro _ _
    exact hout es c1 s1 hseg n R cT sT hR hL esR c' t' hsegR hIS
  · exact Or.inr (Or.inl hCE)
  · exact Or.inr (Or.inr ⟨hBR, n', c', t', hst (fun _ _ => hO), hpos, hcen, hIS, hO⟩)

#print axioms replayRunW_of_decodes

/-! ## 2. The two branch hypotheses -/

/-- **NAMED (open) — branch (ii).**  From a `ChainEnd` landing of the replay
out of a positive-radius fallback landing `⟨cT, sT⟩`, the chain's own round
ends in an `InvLPS` landing, with its cost from `sT`, centre monotone and the
right-head budget.  Supplier: the shift/fallback route of the chain's round
(`roundsRouteLP_of_tail` / `ShiftTailC` pattern). -/
def ChainEndLandingC (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ)
    (cP : Control) (sP : GalilVM) : Prop :=
  ∀ (es : List Bool) (c1 : Control) (s1 : GalilVM),
    WatchSegE P q first 2048 es cP sP c1 s1 →
    ∀ (n R : ℕ) (cT : Control) (sT : GalilVM), 0 < R →
      FallbackLanding P q first raw c1 s1 n R cT sT →
      ChainEnd raw P q first 2048 (position sT.right + R) cT sT 0 R →
      ∃ (cT' : Control) (sT' : GalilVM) (k : ℕ) (L : List Piece),
        StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨cT, sT⟩ ⟨cT', sT'⟩ ∧
        CostedRun sT sT' k L ∧ InvLPS P q first raw cT' sT' ∧
        position sT.center ≤ position sT'.center ∧ position sT'.right ≤ 2 * m - 1

/-- **NAMED (open) — branch (iii).**  The idle landing `⟨c', t'⟩` after a
chain broke and the search restarted inside the replay (`InvScan R ∧
OutputRel`, centre kept) is `InvLPS`, with its cost from `sT` and the
right-head budget.  Supplier: `invLP_of_landing_replay` +
`replayStage_after_replayLanding` generalised over the break, and
`costedRun_fallback_replay`. -/
def RestartLandingC (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ)
    (cP : Control) (sP : GalilVM) : Prop :=
  ∀ (es : List Bool) (c1 : Control) (s1 : GalilVM),
    WatchSegE P q first 2048 es cP sP c1 s1 →
    ∀ (n R : ℕ) (cT : Control) (sT : GalilVM), 0 < R →
      FallbackLanding P q first raw c1 s1 n R cT sT →
      BrokeAndRestarted raw P q first 2048 cT sT →
      ∀ (n' : ℕ) (c' : Control) (t' : GalilVM),
        StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) n' ⟨cT, sT⟩ ⟨c', t'⟩ →
        position t'.right = position sT.right + R → t'.center = sT.center →
        PalPeg.GalilReplaySegment.InvScan 2048 raw c' t' R → OutputRel raw c' t' →
        ∃ L : List Piece,
          CostedRun sT t' n' L ∧ InvLPS P q first raw c' t' ∧ position t'.right ≤ 2 * m - 1

/-! ## 3. `fallbackReachS_of_context'` -/

/-- **`CloseoutWatchRound31.fallbackReachS_of_context` with `ReplayRunC`
replaced by `ReplayRunWC` + the two branch hypotheses.**  Branch (i) is Round
31's proof; (ii) chains `ChainEndLandingC` after the empty replay piece; (iii)
chains `RestartLandingC` after the empty replay piece. -/
theorem fallbackReachS_of_context' (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (hq0 : 0 < q) (first : Fin 9)
    (h7 : first ≠ 7) (h8 : first ≠ 8) (raw : List (Fin 2)) (m : ℕ)
    (c : Control) (r : GalilVM) (cP : Control) (sP : GalilVM)
    (hcopy : PalPeg.GalilChainCoupling.CopyPack c r)
    (hex : ∀ s, (PofC centre place entry raw).replayExhausted s = zero s.replay)
    (hsiP : ShiftIdle sP) (hMP : MInv raw cP sP) (hEP : EntryCounters raw sP)
    (houtP : OutputRel raw cP sP)
    (hns : WatchMismatchNoShiftC (PofC centre place entry raw) q first cP sP)
    (hentry : EntryCostC (PofC centre place entry raw) q first raw c r cP sP)
    (hpiece : FallbackCostPieceC (PofC centre place entry raw) q first raw m cP sP)
    (hreplay : ReplayRunWC (PofC centre place entry raw) q first raw cP sP)
    (hce : ChainEndLandingC (PofC centre place entry raw) q first raw m cP sP)
    (hbr : RestartLandingC (PofC centre place entry raw) q first raw m cP sP) :
    FallbackReachS (PofC centre place entry raw) q first raw m c r cP sP := by
  intro es c1 s1 hseg hlive hclk hav hne
  -- the tick pack at the mismatch (Round 22's `watchFallbackC_of_context`, (a) part)
  obtain ⟨⟨z, hz⟩, hg⟩ := hns es c1 s1 hseg hlive hclk hav hne
  obtain ⟨w, hw⟩ := hlive.2.2.2
  obtain ⟨hsi, hM, hK, hout⟩ :=
    tickPack_of_landing centre place entry q first raw hex hseg hav hsiP hMP hEP houtP
  have hT : FallbackTick centre place entry raw s1 :=
    fallbackTick_of_watchTick centre place entry raw (by rw [hw]; exact ChainVM.noConfusion) hz
      (hg ⟨left s1.left, right s1.right, z⟩ (searchLens.get s1) hz)
  obtain ⟨n, R, cT, sT, hL⟩ :=
    fallbackLanding_of_pack centre place entry q hq0 first h7 h8 raw ⟨hlive.1, hlive.2.1⟩ hclk
      hav hne hsi hM hK
      hT hout
  obtain ⟨k0, L0, hrun, hcost0⟩ := hentry
  have hr1 : position r.center ≤ position s1.center := by
    rw [watchSegE_center _ q first 2048 hseg]
    have := hcost0.centre
    omega
  have hprog1 := hL.2.1
  -- the empty replay piece: `⟨cT, sT⟩` itself, reached from `⟨c, r⟩`
  have hsound : SoundScanNR raw ⟨cT, sT⟩ := stepsAll_last hL.1
  have hrep0 : StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048
      (SoundScanNR raw) ([] : List Bool).length ⟨cT, sT⟩ ⟨cT, sT⟩ := .zero _ hsound
  have hall0 := stepsAll_entry_to_landing centre place entry q first raw hrun hseg hEP houtP hL
    hrep0
  obtain ⟨L1, hcost1, hbound0⟩ := hpiece es c1 s1 hseg hclk hav hne n R cT sT hL [] cT sT hrep0
  have hcostT : CostedRun r sT (k0 + es.length + (1 + (n + 1)) + ([] : List Bool).length)
      (L0 ++ L1) := by
    have := costedRun_of_pieces hcost0 hcost1
    rwa [show k0 + (es.length + (1 + (n + 1)) + ([] : List Bool).length) =
      k0 + es.length + (1 + (n + 1)) + ([] : List Bool).length by omega] at this
  rcases Nat.eq_zero_or_pos R with hR0 | hRpos
  · subst hR0
    exact ⟨cT, sT, _, L0 ++ L1, hall0, hcostT,
      Or.inl ⟨invLP_of_fallbackLanding_zero hL, landingRestart_of_fallbackLanding_zero hL⟩,
      by omega, hbound0⟩
  · have hRL : ReplayLanding raw cT sT R := hL.2.2.2.1 hRpos
    rcases hreplay es c1 s1 hseg n R cT sT hRpos hL with
      ⟨esR, c', t', hrep⟩ | hCE | ⟨hBR, n', c', t', hst, hpos, hcen, hIS, hO⟩
    · -- (i): Round 31 verbatim
      obtain ⟨-, hrepAll, -, hcen, -⟩ := id hrep
      obtain ⟨L1', hcost1', hbound⟩ :=
        hpiece es c1 s1 hseg hclk hav hne n R cT sT hL esR c' t' hrepAll
      have hall := stepsAll_entry_to_landing centre place entry q first raw hrun hseg hEP houtP hL
        hrepAll
      have hLP : InvLP raw c' t' :=
        invLP_of_landing_replay centre place entry q first raw hRL hL.2.2.2.2 hrep hall
      have hS : InvLPS (PofC centre place entry raw) q first raw c' t' :=
        ⟨⟨invLP2_of_stepsAll centre place entry q first hcopy hall hLP,
          centreRep_congr hcen (centreRep_of_restarted hRL.rest)⟩,
          replayStage_after_replayLanding hRL hrep.1⟩
      refine ⟨c', t', k0 + es.length + (1 + (n + 1)) + esR.length, L0 ++ L1', hall, ?_,
        Or.inr hS, by rw [hcen]; omega, hbound⟩
      have := costedRun_of_pieces hcost0 hcost1'
      rwa [show k0 + (es.length + (1 + (n + 1)) + esR.length) =
        k0 + es.length + (1 + (n + 1)) + esR.length by omega] at this
    · -- (ii): `ChainEnd` — the chain's own round
      obtain ⟨cT', sT', k, L, hst, hcost, hS, hmono, hbound⟩ :=
        hce es c1 s1 hseg n R cT sT hRpos hL hCE
      exact ⟨cT', sT', _, (L0 ++ L1) ++ L, stepsAll_trans hall0 hst,
        costedRun_of_pieces hcostT hcost, Or.inr hS, by omega, hbound⟩
    · -- (iii): `BrokeAndRestarted` — the idle landing after the restart
      obtain ⟨L, hcost, hS, hbound⟩ :=
        hbr es c1 s1 hseg n R cT sT hRpos hL hBR n' c' t' hst hpos hcen hIS hO
      exact ⟨c', t', _, (L0 ++ L1) ++ L, stepsAll_trans hall0 hst,
        costedRun_of_pieces hcostT hcost, Or.inr hS, by rw [hcen]; omega, hbound⟩

#print axioms fallbackReachS_of_context'

/-! ## 4. `foundExit_compare_final15` -/

/-- **`foundExit_compare_final14` from the fallback-branch sources with
`ReplayRunC` replaced by `ReplayRunWC` + `ChainEndLandingC` +
`RestartLandingC`.**  The statement is `foundExit_compare_final14_of_context`
with the `hreplay` slot widened. -/
theorem foundExit_compare_final15 (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (hq0 : 0 < q) (first : Fin 9)
    (h7 : first ≠ 7) (h8 : first ≠ 8)
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
    (hsiP : ShiftIdle sP) (hMP : MInv w cP sP) (hEP : EntryCounters w sP)
    (houtP : OutputRel w cP sP)
    (hns : WatchMismatchNoShiftC (PofC centre place entry w) q first cP sP)
    (hentry : EntryCostC (PofC centre place entry w) q first w c r cP sP)
    (hpiece : FallbackCostPieceC (PofC centre place entry w) q first w m cP sP)
    (hreplay : ReplayRunWC (PofC centre place entry w) q first w cP sP)
    (hce : ChainEndLandingC (PofC centre place entry w) q first w m cP sP)
    (hbr : RestartLandingC (PofC centre place entry w) q first w m cP sP)
    (hstage : ReplayStage w (PofC centre place entry w) q first c r)
    (hmP : cP.mode = .scan) (hrP : cP.replaying = false) (hcP : 1 ≤ cP.clock)
    (hreachWatch : ∃ (es : List Bool) (c2 : Control) (s2 : GalilVM),
      WatchSegE (PofC centre place entry w) q first 2048 es cP sP c2 s2 ∧
        PalPeg.CloseoutWatchRun.LiveScanWatch c2 s2)
    (hat : FoundDpAtC centre place entry q first w lower span h c r)
    (hreach : ShiftReachC centre place entry q first w h)
    (hround : ShiftRoundAtC centre place entry q first w m h lower)
    (hmsr : MismatchShiftRouteC centre place entry q first w m h lower)
    (hland : ∀ sF : GalilVM,
      PalPeg.CloseoutWatchRound5.BreakLandingC centre place entry q first w h sF cP sP)
    (hstepBreak : ∀ (c0 : Control) (s0 : GalilVM), LiveScanWatch c0 s0 →
      PalPeg.CloseoutWatchRun.RoundStepC (PofC centre place entry w) q first (roundFuel h)
        (BreakTermData centre place entry q first w m h) c0 s0) :
    FoundExitLPS (PofC centre place entry w) q first w m c r :=
  foundExit_compare_final14 centre place entry q first w m h lower span hP hex hready hcan hsane
    hstart hor hzl hnn hpm hE hsW a ls rs qw gap hprep hmis hctx
    (fallbackReachS_of_context' centre place entry q hq0 first h7 h8 w m c r cP sP hE.inv.1.1.2
      hex hsiP hMP hEP houtP hns hentry hpiece hreplay hce hbr)
    hstage hmP hrP hcP hreachWatch hat hreach hround hmsr hland hstepBreak

#print axioms foundExit_compare_final15

end PalPeg.CloseoutWatchRound36
