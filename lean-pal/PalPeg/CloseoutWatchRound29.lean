import PalPeg.CloseoutWatchRound25
import PalPeg.CloseoutWatchRound24

/-!
# Closeout watch round 29 — `LandingRestartReach` on the fallback branch only

`CloseoutWatchPhase2.LandingRestartReach P q first raw c r` quantifies over
*every* `InvLP` landing reachable from the stage entry `⟨c, r⟩`.  Inside
`CloseoutWatchRound25.foundExit_compare_final12` it is consumed at exactly one
place: `foundExit_compare_final9` → `foundExit_compare_final9'` →
`CloseoutWatchRound18.foundExit_of_split3` →
`CloseoutWatchRound17.foundExitW_of_breakEndE` → `foundExitW_of_route`, i.e.
only at the landing that `CloseoutWatchRound17.FallbackRouteW` exports out of a
clock-`1` watching mismatch (the fallback branch of `ExitSplit3C`/`ExitSplit4C`).
Round 15's `roundsRouteLP_of_tail` (families 1, 2 and 4) never reads it.

## What is proved here (unconditionally, no `sorry`)

1. `LandingRestartReachF` — the fallback-branch-only form: `FallbackRouteW`
   with `CloseoutWatchPhase.LandingRestart` added at the exported landing.
2. `landingRestartReach_fallback` — the producer.  Round 21's fallback landing
   (`fallbackLanding_of_pack`: `1 + (n+1)` ticks, `Inv` at `R = 0`,
   `ReplayLanding` at `R > 0`, `SpanRep`, strict centre progress) is composed
   with Round 24's three cost pieces exactly as `watchFallbackCostC_of_context`
   does, and at the **radius-`0` landing** the restart data is free:
   `Inv.rest`/`Inv.stage` (`landingRestart_of_inv`).  So on the fallback branch
   the restart witness is the fallback tick's own `Restarted raw sT 0 reset`
   with `StageEntry 0 reset` (`stageEntry_zero`), and no determinism of
   `StepsAll` is needed — the landing is the one the route constructs.
3. `foundExitW_of_routeF` / `foundExit_of_split3F` /
   `foundExit_compare_final9F'` — Rounds 17/18's consumers with `hLR` removed.
4. `foundExit_compare_final13` — `foundExit_compare_final12` with the pair
   `FallbackRouteW` + `LandingRestartReach` replaced by `LandingRestartReachF`.

## The ONE hypothesis left: `ReplayedLandingRestartC`

At a **positive**-radius fallback landing the route (Round 24) exports the
*post-replay* state `⟨c', t'⟩` (`ReplayRun`, `InvScan … R`), because the
fallback landing itself has `replaying = true` and is not `InvLP`.  The
consumer `FoundExit.landed` charges `Restarted raw t' Rad last` together with
`StageEntry Rad last` at that state.  Nothing in the tree gives it: `InvScan`
carries `SearchReady`, not `search = begin last radius`, and even if the
post-replay state were `Restarted`, its radius representation forces
`Rad = R` while the lower bound installed by the fallback is `reset`
(`value reset = 0`), so `StageEntry R reset` would read `3R ≤ 0`.  The
hypothesis is therefore stated verbatim as what the consumer reads —
`LandingRestart raw c' t'` at the replayed landing — and flagged: closing it
honestly needs either a `FoundExit` constructor for `InvLP ∧ ReplayStage`
landings (the `InvLPS` shape `CycleOutMC3` already accepts, via
`replayStage_after_replayLanding`), or a proof that a watch-mismatch fallback
always chooses radius `0`.  It is vacuous whenever `R = 0`.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutWatchRound29

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton PalPeg.GalilOracleDischarge PalPeg.GalilOracleLocal
open PalPeg.GalilCheckpoints PalPeg.GalilTraceCost PalPeg.GalilLexMeasure
open PalPeg.GalilInvPlus PalPeg.GalilInvPlus2 PalPeg.GalilOracleMC
open PalPeg.GalilGlueBLeaves PalPeg.GalilBranchInvariants2 PalPeg.GalilSegmentConstruct
open PalPeg.GalilOracleM PalPeg.GalilOracleMC2 PalPeg.GalilOracleGlueB
open PalPeg.GalilFoundStage
open PalPeg.CloseoutContracts
open PalPeg.CloseoutWatchRun (LiveScanWatch roundFuel)
open PalPeg.CloseoutWatchPhase (LandingRestart)
open PalPeg.CloseoutWatchPhase2 (landingRestart_of_inv)
open PalPeg.CloseoutWatchRound2 (FoundCompareCtxC TerminalRunC TerminalC' terminalC'_of_align)
open PalPeg.CloseoutWatchRound3 (DistanceNonnegC ExitSplitC)
open PalPeg.CloseoutWatchRound5 (PrepLandingLiveC)
open PalPeg.CloseoutWatchRound6 (RightCanC RightSaneC StartLeC LedgerOriginC PeriodMatchC)
open PalPeg.CloseoutWatchRound4 (ZeroLagAtMatchC)
open PalPeg.CloseoutWatchRound7 (PrepLandingWatchC ShiftReachC ShiftRoundAtC BreakTermData)
open PalPeg.CloseoutWatchRound10 (FoundDpAtC)
open PalPeg.CloseoutPrepInputs2 (MismatchExitG)
open PalPeg.CloseoutPrepInputs3 (PrepInputsG3 foundExit_of_compare3)
open PalPeg.CloseoutWatchRound17 (FallbackRouteW)
open PalPeg.CloseoutWatchRound18 (ExitSplit3C TerminalRunFallbackC watchSegE_of_watchSeg
  terminalRunBreakC_of_break0)
open PalPeg.CloseoutWatchRound21 (FallbackLanding fallbackLanding_of_pack
  invLP_of_fallbackLanding_zero)
open PalPeg.CloseoutWatchRound22 (WatchMismatchNoShiftC watchFallbackC_of_context)
open PalPeg.CloseoutWatchRound24 (EntryCostC FallbackCostPieceC ReplayRunC ReplayRun
  stepsAll_entry_to_landing costedRun_of_pieces invLP_of_landing_replay
  watchFallbackCostC_of_context)
open PalPeg.CloseoutWatchRound23 (MismatchGuardFails ExitSplit4C exitSplit4C_of_tick
  terminalRunFallbackC_of_G)
open PalPeg.CloseoutWatchRound25 (MismatchShiftRouteC mismatchShift_to_shiftRoute)
open PalPeg.CloseoutWatchRound20 (watchPrefixC_of_unique)

/-! ## 1. The fallback-branch-only contract -/

/-- **`LandingRestartReach`, restricted to the fallback branch.**
`CloseoutWatchRound17.FallbackRouteW` with the restart data
`CloseoutWatchPhase.LandingRestart` at the landing it exports.  This is the
only place `foundExit_compare_final12` reads `LandingRestartReach`. -/
def LandingRestartReachF (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ)
    (c : Control) (r : GalilVM) (cP : Control) (sP : GalilVM) : Prop :=
  ∀ (es : List Bool) (c1 : Control) (s1 : GalilVM),
    WatchSegE P q first 2048 es cP sP c1 s1 → LiveScanWatch c1 s1 →
    c1.clock = 1 → canRight s1.right →
    read (left s1.left) ≠ read (right s1.right) →
    ∃ (cT : Control) (sT : GalilVM) (k : ℕ) (L : List Piece),
      StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩ ∧
      CostedRun r sT k L ∧ InvLP raw cT sT ∧ LandingRestart raw cT sT ∧
      position r.center < position sT.center ∧ position sT.right ≤ 2 * m - 1

/-- The fallback-branch form implies the route Round 17 consumes. -/
theorem fallbackRouteW_of_reachF {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    {m : ℕ} {c cP : Control} {r sP : GalilVM}
    (h : LandingRestartReachF P q first raw m c r cP sP) :
    FallbackRouteW P q first raw m c r cP sP := by
  intro es c1 s1 hseg hlive hclk hav hne
  obtain ⟨cT, sT, k, L, hst, hcr, hLP, -, hprog, hpos⟩ := h es c1 s1 hseg hlive hclk hav hne
  exact ⟨cT, sT, k, L, hst, hcr, hLP, hprog, hpos⟩

/-! ## 2. The ONE hypothesis: the replayed landing -/

/-- **NAMED (open) — the ONE hypothesis.**  At a positive-radius fallback
landing out of a watch mismatch, the state at the end of the replay run carries
the restart data.  See the header: this is exactly what `FoundExit.landed`
reads at the exported landing; it is vacuous when every such fallback chooses
radius `0`, and suspect otherwise (`StageEntry R reset`). -/
def ReplayedLandingRestartC (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (cP : Control) (sP : GalilVM) : Prop :=
  ∀ (es : List Bool) (c1 : Control) (s1 : GalilVM),
    WatchSegE P q first 2048 es cP sP c1 s1 →
    ∀ (n R : ℕ) (cT : Control) (sT : GalilVM), 0 < R →
      FallbackLanding P q first raw c1 s1 n R cT sT →
      ∀ (esR : List Bool) (c' : Control) (t' : GalilVM),
        ReplayRun P q first raw cT sT R esR c' t' → LandingRestart raw c' t'

/-! ## 3. The producer -/

/-- **The radius-`0` fallback landing carries the restart data outright.** -/
theorem landingRestart_of_fallbackLanding_zero {P : Shared} {q : ℕ} {first : Fin 9}
    {raw : List (Fin 2)} {c1 cT : Control} {s1 sT : GalilVM} {n : ℕ}
    (h : FallbackLanding P q first raw c1 s1 n 0 cT sT) : LandingRestart raw cT sT :=
  landingRestart_of_inv (h.2.2.1 rfl)

/-- **`landingRestartReach_fallback`.**  The fallback-branch reach statement
from the landing sources of Rounds 21/22/24: the tick pack at the preparation
landing (`hex`, `hsiP`, `hMP`, `hEP`, `houtP`), the shift/fallback classifier
`WatchMismatchNoShiftC`, the three cost pieces (`EntryCostC`,
`FallbackCostPieceC`, `ReplayRunC`), and — for the positive-radius replayed
landing only — `ReplayedLandingRestartC`. -/
theorem landingRestartReach_fallback (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (hq0 : 0 < q) (first : Fin 9)
    (h7 : first ≠ 7) (h8 : first ≠ 8) (raw : List (Fin 2)) (m : ℕ)
    (c : Control) (r : GalilVM) (cP : Control) (sP : GalilVM)
    (hex : ∀ s, (PofC centre place entry raw).replayExhausted s = zero s.replay)
    (hsiP : ShiftIdle sP) (hMP : MInv raw cP sP) (hEP : EntryCounters raw sP)
    (houtP : OutputRel raw cP sP)
    (hns : WatchMismatchNoShiftC (PofC centre place entry raw) q first cP sP)
    (hentry : EntryCostC (PofC centre place entry raw) q first raw c r cP sP)
    (hpiece : FallbackCostPieceC (PofC centre place entry raw) q first raw m cP sP)
    (hreplay : ReplayRunC (PofC centre place entry raw) q first raw cP sP)
    (hrest : ReplayedLandingRestartC (PofC centre place entry raw) q first raw cP sP) :
    LandingRestartReachF (PofC centre place entry raw) q first raw m c r cP sP := by
  intro es c1 s1 hseg hlive hclk hav hne
  -- the tick pack at the mismatch, from Round 22
  have hW := watchFallbackC_of_context centre place entry q first raw m c r cP sP hex hsiP hMP
    hEP houtP ⟨hns, watchFallbackCostC_of_context centre place entry q first raw m c r cP sP
      hEP houtP hentry hpiece hreplay⟩
  obtain ⟨⟨hsi, hM, hK, hT, hout⟩, -⟩ := hW es c1 s1 hseg hlive hclk hav hne
  -- the fallback landing, from Round 21
  obtain ⟨n, R, cT, sT, hL⟩ :=
    fallbackLanding_of_pack centre place entry q hq0 first h7 h8 raw hlive hclk hav hne hsi hM hK
      hT hout
  obtain ⟨k0, L0, hrun, hcost0⟩ := hentry
  have hr1 : position r.center ≤ position s1.center := by
    rw [watchSegE_center _ q first 2048 hseg]
    have := hcost0.centre
    omega
  have hprog1 := hL.2.1
  rcases Nat.eq_zero_or_pos R with hR0 | hRpos
  · -- radius `0`: the landing is the restart state itself
    subst hR0
    have hsound : SoundScanNR raw ⟨cT, sT⟩ := stepsAll_last hL.1
    have hrep0 : StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048
        (SoundScanNR raw) ([] : List Bool).length ⟨cT, sT⟩ ⟨cT, sT⟩ := .zero _ hsound
    obtain ⟨L1, hcost1, hbound⟩ := hpiece es c1 s1 hseg hclk hav hne n 0 cT sT hL [] cT sT hrep0
    refine ⟨cT, sT, k0 + es.length + (1 + (n + 1)) + ([] : List Bool).length, L0 ++ L1,
      stepsAll_entry_to_landing centre place entry q first raw hrun hseg hEP houtP hL hrep0,
      ?_, invLP_of_fallbackLanding_zero hL, landingRestart_of_fallbackLanding_zero hL,
      by omega, hbound⟩
    have := costedRun_of_pieces hcost0 hcost1
    rwa [show k0 + (es.length + (1 + (n + 1)) + ([] : List Bool).length) =
      k0 + es.length + (1 + (n + 1)) + ([] : List Bool).length by omega] at this
  · -- radius `R > 0`: the replayed landing, restart data from the hypothesis
    obtain ⟨esR, c', t', hrep⟩ := hreplay es c1 s1 hseg n R cT sT hRpos hL
    obtain ⟨-, hrepAll, -, hcen, -⟩ := id hrep
    obtain ⟨L1, hcost1, hbound⟩ :=
      hpiece es c1 s1 hseg hclk hav hne n R cT sT hL esR c' t' hrepAll
    have hall := stepsAll_entry_to_landing centre place entry q first raw hrun hseg hEP houtP hL
      hrepAll
    refine ⟨c', t', k0 + es.length + (1 + (n + 1)) + esR.length, L0 ++ L1, hall, ?_,
      invLP_of_landing_replay centre place entry q first raw (hL.2.2.2.1 hRpos) hL.2.2.2.2 hrep
        hall,
      hrest es c1 s1 hseg n R cT sT hRpos hL esR c' t' hrep, by rw [hcen]; omega, hbound⟩
    have := costedRun_of_pieces hcost0 hcost1
    rwa [show k0 + (es.length + (1 + (n + 1)) + esR.length) =
      k0 + es.length + (1 + (n + 1)) + esR.length by omega] at this

/-! ## 4. The consumers, without `LandingRestartReach` -/

/-- `CloseoutWatchRound17.foundExitW_of_route` with `hLR` removed. -/
theorem foundExitW_of_routeF {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    {m : ℕ} {c cP : Control} {r sP : GalilVM}
    (h : LandingRestartReachF P q first raw m c r cP sP)
    (es : List Bool) (c1 : Control) (s1 : GalilVM)
    (hseg : WatchSegE P q first 2048 es cP sP c1 s1) (hlive : LiveScanWatch c1 s1)
    (hclk : c1.clock = 1) (hav : canRight s1.right)
    (hne : read (left s1.left) ≠ read (right s1.right)) :
    FoundExit P q first raw m c r := by
  obtain ⟨cT, sT, k, L, hst, hcr, hLP, hL, hprog, hpos⟩ := h es c1 s1 hseg hlive hclk hav hne
  have hI := PalPeg.CloseoutWatchPhase.inv_of_invLP hLP hL
  have hS := PalPeg.CloseoutWatchPhase.spanRep_of_invLP hLP
  obtain ⟨hM, hR, hres, hSpan⟩ := PalPeg.CloseoutFoundExits.landed_pack hI hS
  exact .landed cT sT k L hst hcr hM hR hres hSpan hprog hpos

/-- `CloseoutWatchRound18.foundExit_of_split3` with `hLR` removed. -/
theorem foundExit_of_split3F {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    {m h : ℕ} {c cP : Control} {r sP : GalilVM}
    (hfb : LandingRestartReachF P q first raw m c r cP sP)
    (hlive : PrepLandingLiveC P q first cP sP)
    (hf : TerminalRunFallbackC P q first h cP sP) :
    FoundExit P q first raw m c r := by
  have hliveP : LiveScanWatch cP sP := hlive [] cP sP (.stop _ _)
  obtain ⟨cT, sT, hseg1, hliveT, hbe⟩ := hf [] cP sP (.stop _ _) hliveP
  obtain ⟨c1, s1, hseg2, hclk, hlive1, hav, hne⟩ := hbe
  obtain ⟨es, hsegE⟩ :=
    watchSegE_of_watchSeg (PalPeg.CloseoutWatchRun.watchSeg_append hseg1 hseg2)
  exact foundExitW_of_routeF hfb es c1 s1 hsegE hlive1 hclk hav hne

/-- `CloseoutWatchRound18.foundExit_compare_final9'` with `hLR` removed. -/
theorem foundExit_compare_final9F' {centre : GalilVM → Fin 3}
    {place : GalilVM → GalilScaffoldPlace.Place} {entry q : ℕ} {first : Fin 9}
    {w : List (Fin 2)} {m h : ℕ} {c cP : Control} {r sP : GalilVM}
    (hTwo : ExitSplitC centre place entry q first w h cP sP →
      FoundExit (PofC centre place entry w) q first w m c r)
    (hrun : TerminalRunC (PofC centre place entry w) q first h cP sP)
    (hsplit3 : ExitSplit3C centre place entry q first w h cP sP)
    (hfb : LandingRestartReachF (PofC centre place entry w) q first w m c r cP sP)
    (hlive : PrepLandingLiveC (PofC centre place entry w) q first cP sP) :
    FoundExit (PofC centre place entry w) q first w m c r := by
  rcases hsplit3 hrun with hs | hb | hf
  · exact hTwo (fun _ => Or.inl hs)
  · exact hTwo (fun _ => Or.inr (terminalRunBreakC_of_break0 hb))
  · exact foundExit_of_split3F hfb hlive hf

/-! ## 5. `foundExit_compare_final13` -/

/-- **`CloseoutWatchRound25.foundExit_compare_final12` with `FallbackRouteW` +
`LandingRestartReach` replaced by `LandingRestartReachF`.**  The body is
Round 25's verbatim; families 1–3 go through `foundExit_compare_final9F'` on
Round 15's `foundExit_compare_final8`, family 4 through
`mismatchShift_to_shiftRoute` as before. -/
theorem foundExit_compare_final13 (centre : GalilVM → Fin 3)
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
    (hfbF : LandingRestartReachF (PofC centre place entry w) q first w m c r cP sP)
    (hstage : ReplayStage w (PofC centre place entry w) q first c r)
    (hmP : cP.mode = .scan) (hrP : cP.replaying = false) (hcP : 1 ≤ cP.clock)
    (hwatch : PrepLandingWatchC (PofC centre place entry w) q first cP sP)
    (hat : FoundDpAtC centre place entry q first w lower span h c r)
    (hreach : ShiftReachC centre place entry q first w h)
    (hround : ShiftRoundAtC centre place entry q first w m h lower)
    (hmsr : MismatchShiftRouteC centre place entry q first w m h lower)
    (hland : ∀ sF : GalilVM,
      PalPeg.CloseoutWatchRound5.BreakLandingC centre place entry q first w h sF cP sP)
    (hstepBreak : ∀ (c0 : Control) (s0 : GalilVM), LiveScanWatch c0 s0 →
      PalPeg.CloseoutWatchRun.RoundStepC (PofC centre place entry w) q first (roundFuel h)
        (BreakTermData centre place entry q first w m h) c0 s0) :
    FoundExit (PofC centre place entry w) q first w m c r := by
  classical
  have hlive : PrepLandingLiveC (PofC centre place entry w) q first cP sP :=
    PalPeg.CloseoutWatchRound7.prepLandingLiveC_of_watch (PofC centre place entry w) q first
      hmP hrP hcP hwatch
  have hsplit4 : ExitSplit4C centre place entry q first w h cP sP :=
    exitSplit4C_of_tick centre place entry q first w h cP sP (hlive [] cP sP (.stop _ _))
      (watchPrefixC_of_unique _ _ _ _ _)
  -- the terminal record, exactly as in Rounds 18/25
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
  -- families 1–3: the three-way split into Round 15, through `final9F'`
  have via3 : ∀ (hs3 : ExitSplit3C centre place entry q first w h cP sP),
      FoundExit (PofC centre place entry w) q first w m c r := fun hs3 =>
    foundExit_compare_final9F' (h := h) (fun hsplit =>
      PalPeg.CloseoutWatchRound15.foundExit_compare_final8 centre place entry q first w m h
        lower span hP hex hready hcan hsane hstart hor hzl hnn hpm hE hsW a ls rs qw gap hprep
        hmis hctx hsplit hstage hmP hrP hcP hwatch hat hreach hround hland hstepBreak)
      hT.2 hs3 hfbF hlive
  rcases hsplit4 hT.2 with hs | hb | hf | hm
  · exact via3 (fun _ => Or.inl hs)
  · exact via3 (fun _ => Or.inr (Or.inl hb))
  · exact via3 (fun _ => Or.inr (Or.inr (terminalRunFallbackC_of_G hf)))
  · -- family 4: the mismatch-shift landing, through the shift route
    have htail : PalPeg.CloseoutWatchPhase2.ShiftTailC centre place entry q first w m c r cP sP :=
      mismatchShift_to_shiftRoute centre place entry q first w m h lower span hlive
        (PalPeg.CloseoutWatchRound10.foundDpShiftC_of_at centre place entry q first w hP
          lower span h hstage hat)
        hmsr hctx hm
    have hroute := PalPeg.CloseoutWatchRound15.roundsRouteLP_of_tail centre place entry q first
      w m hex hE htail
    exact foundExit_of_compare3 centre place entry q first w m hP hE hsW a ls rs qw gap
      hprep hmis (Or.inl (PalPeg.CloseoutWatchPhase.roundsExit_of_LP hroute))

end PalPeg.CloseoutWatchRound29

#print axioms PalPeg.CloseoutWatchRound29.fallbackRouteW_of_reachF
#print axioms PalPeg.CloseoutWatchRound29.landingRestart_of_fallbackLanding_zero
#print axioms PalPeg.CloseoutWatchRound29.landingRestartReach_fallback
#print axioms PalPeg.CloseoutWatchRound29.foundExitW_of_routeF
#print axioms PalPeg.CloseoutWatchRound29.foundExit_of_split3F
#print axioms PalPeg.CloseoutWatchRound29.foundExit_compare_final9F'
#print axioms PalPeg.CloseoutWatchRound29.foundExit_compare_final13
