import PalPeg.CloseoutWatchRound29
import PalPeg.CloseoutWatchRound28

/-!
# Closeout watch round 31 — `ReplayedLandingRestartC` is not the honest landing

Round 29 left one hypothesis, `ReplayedLandingRestartC`: at a positive-radius
(`R > 0`) fallback out of a watch-mode clock-`1` mismatch, the post-replay
landing `⟨c', t'⟩` carries `LandingRestart raw c' t'`.  Round 29 flagged it as
suspect.  This round settles the two questions.

## (A) Does a watch-mode fallback always choose radius `0`?  **No.**

`chosenRadius` (`GalilScaffoldChainFallback`) is the longest odd palindromic
prefix of the reversed scan window, i.e. the longest odd palindrome of the
*encoded* text ending at the right head — nothing about the chain enters it.
In the Scala machine (`ScaffoldGalil.stepScan`) a watching chain falls back
whenever `chain.canShift && chain.prediction() == right.read()` fails; with
`canShift` requiring `phase == 4 ∧ lag == 0 ∧ margin ≥ 0`, this covers both
"prediction broken" and "chain not yet verified".  Concrete witness of the
first kind: raw `c · (abb)^8 · a` followed by `a`.  The centre of `(abb)^8 a`
has radius `12`, period `3` (`h = 3`, four semiperiods verified, so the chain
is watching with `phase = 4`), the prediction is `s[r − 3] = b`, the new
symbol is `a`, so the machine falls back — and the encoded suffix `a#a` is a
palindrome of radius `1`, so `chosenRadius = 1 > 0`.  So `R > 0` is possible
and `ReplayedLandingRestartC` is *not* vacuous.

## (B) `ReplayedLandingRestartC` is false at every `R > 0` landing — proved.

`replayedLanding_not_restart`: at the post-replay landing of an `R > 0`
fallback, `LandingRestart raw c' t'` is contradictory.  Restart data would
give `Restarted raw t' Rad last`; the replay's `WatchSegE` transports
`RadiusRep` (`radiusRep_watchSegE`) so `Rad = R`, and — new here — it also
transports the lower bound (`watchSegE_lower`: no scan/background/replay tick
writes `lower`, only `restart` does), so `last = t'.lower = sT.lower = reset`
from `ReplayLanding.rest : Restarted raw sT 0 reset`.  Then
`StageEntry R reset` reads `3R ≤ 0`, contradicting `0 < R`.  Hence
(`replayedLandingRestartC_iff`) `ReplayedLandingRestartC` is *equivalent* to
"no `R > 0` fallback with a replay run is reachable from the preparation
landing", which (A) refutes semantically.

## The honest landing: `FoundExitLPS`

`FoundExit` has no constructor for the replayed landing: it is `InvLP` and
`ReplayStage` (`replayStage_after_replayLanding`) but not `Restarted`.  The
consumer `CycleOutMC3` only ever needs `InvLPS = InvLPC ∧ ReplayStage` at the
landing (`cycleOutMC3_of_centre`), and the replayed landing *is* `InvLPS`:
`InvLP` from Round 24, `CopyPack` transported from the stage entry
(`invLP2_of_stepsAll`, the entry's `StageEntryC.inv` is `InvLPS`), `CentreRep`
from the fallback's restart (the replay keeps the centre).  So

* `FoundExitLPS` — `FoundExit` plus the constructor `landedS` for an `InvLPS`
  landing with centre progress; `cycleOutMC3_of_foundExitLPS` consumes it
  exactly as `cycleOutMC3_of_foundExit` does.
* `FallbackReachS` — `LandingRestartReachF` with the landing shape
  `(InvLP ∧ LandingRestart) ∨ InvLPS`; `fallbackReachS_of_context` produces it
  from Round 29's producer inputs **without** `ReplayedLandingRestartC` (the
  only new input is `CopyPack c r`, which the stage entry supplies).
* `foundExit_compare_final14` — `foundExit_compare_final13` with the
  conclusion `FoundExitLPS`; `foundExit_compare_final14_of_context` states it
  directly from the fallback-branch sources (`WatchMismatchNoShiftC`,
  `EntryCostC`, `FallbackCostPieceC`, `ReplayRunC`, the preparation-landing
  tick pack).  **No hypothesis remains at the landing itself**; what is left is
  upstream, unchanged from Rounds 22/24/28.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutWatchRound31

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton PalPeg.GalilOracleDischarge PalPeg.GalilOracleLocal
open PalPeg.GalilCheckpoints PalPeg.GalilTraceCost PalPeg.GalilLexMeasure
open PalPeg.GalilInvPlus PalPeg.GalilInvPlus2 PalPeg.GalilOracleMC
open PalPeg.GalilGlueBLeaves PalPeg.GalilBranchInvariants2 PalPeg.GalilSegmentConstruct
open PalPeg.GalilOracleM PalPeg.GalilOracleMC2 PalPeg.GalilOracleGlueB
open PalPeg.GalilFoundStage
open PalPeg.GalilInvPlus3 (InvLPS CycleOutMC3 cycleOutMC3_of_centre replayStage_after_replayLanding)
open PalPeg.CloseoutContracts
open PalPeg.CloseoutWatchRun (LiveScanWatch roundFuel)
open PalPeg.CloseoutWatchPhase (LandingRestart)
open PalPeg.CloseoutWatchRound2 (FoundCompareCtxC TerminalRunC TerminalC' terminalC'_of_align)
open PalPeg.CloseoutWatchRound3 (DistanceNonnegC ExitSplitC)
open PalPeg.CloseoutWatchRound5 (PrepLandingLiveC)
open PalPeg.CloseoutWatchRound6 (RightCanC RightSaneC StartLeC LedgerOriginC PeriodMatchC)
open PalPeg.CloseoutWatchRound4 (ZeroLagAtMatchC)
open PalPeg.CloseoutWatchRound7 (PrepLandingWatchC ShiftReachC ShiftRoundAtC BreakTermData)
open PalPeg.CloseoutWatchRound10 (FoundDpAtC)
open PalPeg.CloseoutPrepInputs2 (MismatchExitG)
open PalPeg.CloseoutPrepInputs3 (PrepInputsG3 foundExit_of_compare3)
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
open PalPeg.CloseoutWatchRound29 (LandingRestartReachF ReplayedLandingRestartC
  landingRestart_of_fallbackLanding_zero)

/-! ## 1. The lower bound survives a segment -/

/-- No search quantum writes the lower bound. -/
theorem searchStep_lower (center : GalilScaffoldPlace.Place) (a : Bool) {v v' : SearchVM}
    (h : searchStep center a v v') : v'.lower = v.lower := by
  unfold searchStep at h
  split at h
  · rw [h]
  · rw [h]
  · rw [h]
  · split at h <;> (rw [h]; try rfl)
  · obtain ⟨y, -, h⟩ := h; rw [h]; try rfl
  · obtain ⟨y, -, h⟩ := h; rw [h]; try rfl
  · obtain ⟨y, -, h⟩ := h; rw [h]; try rfl
  · obtain ⟨y, -, h⟩ := h; rw [h]; try rfl
  · exact h.2.1
  · rw [h]
  · split at h <;> (rw [h]; try rfl)

/-- Nor does the search effect of a tick. -/
theorem searchEffect_lower (P : Shared) (a : Bool) {s : GalilVM} {vq : SearchVM}
    (h : searchEffect P a s vq) : vq.lower = s.lower := by
  rcases h with ⟨-, hs⟩ | ⟨-, hv⟩
  · exact searchStep_lower _ _ hs
  · rw [hv]; rfl

/-- Nor a background tick. -/
theorem backgroundS_lower (P : Shared) (q : ℕ) (first : Fin 9) {s s' : GalilVM}
    (hb : (galilFrameS P q first).background s s') : s'.lower = s.lower := by
  obtain ⟨-, -, hse, -, -⟩ := hb
  exact searchEffect_lower P false hse

theorem afterCompare_lower (s : GalilVM) (vs : ScanVM) (vq : SearchVM) :
    (afterCompare s vs vq).lower = vq.lower := rfl

theorem replayDec_lower' (b : Bool) (s : GalilVM) : (replayDec b s).lower = s.lower := by
  cases b <;> rfl

/-- **A `WatchSegE` keeps the lower bound.**  Only `restart` writes `lower`,
and a segment never restarts. -/
theorem watchSegE_lower (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) {es : List Bool}
    {c c' : Control} {s t : GalilVM} (h : WatchSegE P q first delay es c s c' t) :
    t.lower = s.lower := by
  induction h with
  | stop c s => rfl
  | wait c s s' _ _ _ hb _ ih => rw [ih, backgroundS_lower P q first hb]
  | count c s s' _ _ _ _ hb _ ih => rw [ih, backgroundS_lower P q first hb]
  | «match» c s vs vq o _ _ _ _ _ _ _ hq _ _ ih =>
    rw [ih, afterCompare_lower, searchEffect_lower P true hq]
  | matchIdle c s vs vq o _ _ _ _ _ _ _ _ _ hq _ _ _ ih =>
    rw [ih, afterCompare_lower, searchEffect_lower P true hq]
  | countR c s s' _ _ _ _ hb _ ih => rw [ih, backgroundS_lower P q first hb]
  | matchIdleR c s vs vq o _ _ _ _ _ _ _ _ _ hq _ _ _ ih =>
    rw [ih, replayDec_lower', afterCompare_lower, searchEffect_lower P true hq]

/-! ## 2. The refutation -/

theorem radiusRep_eq {r : Counter} {a b : ℕ} (h1 : RadiusRep r a) (h2 : RadiusRep r b) :
    a = b := by
  have : (a : ℤ) = b := h1.2.symm.trans h2.2
  exact_mod_cast this

/-- **The post-replay landing of a positive-radius fallback never carries the
restart data.**  `Rad = R` by `radiusRep_watchSegE`, `last = reset` by
`watchSegE_lower`, and `StageEntry R reset` is `3R ≤ 0`. -/
theorem replayedLanding_not_restart {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    {c1 cT c' : Control} {s1 sT t' : GalilVM} {n R : ℕ} {esR : List Bool}
    (hR : 0 < R) (hL : FallbackLanding P q first raw c1 s1 n R cT sT)
    (hrep : ReplayRun P q first raw cT sT R esR c' t') (h : LandingRestart raw c' t') : False := by
  have hRL : ReplayLanding raw cT sT R := hL.2.2.2.1 hR
  obtain ⟨hseg, -, hcnt, -, -⟩ := hrep
  obtain ⟨⟨Rad, last, hRst⟩, hstage⟩ := h
  have hSt := hstage Rad last hRst
  obtain ⟨-, -, -, -, hRR, -, -, hlow, -, -⟩ := hRst
  have hRR' : RadiusRep t'.radius R := by
    have h0 := radiusRep_watchSegE _ q first 2048 hseg hRL.rest.2.2.2.2.1
    rw [hcnt, Nat.zero_add] at h0
    exact h0
  have hRad : Rad = R := radiusRep_eq hRR hRR'
  have hlowT : t'.lower = reset := by
    rw [watchSegE_lower P q first 2048 hseg]
    exact hRL.rest.2.2.2.2.2.2.2.1
  have hlast : last = reset := hlow.symm.trans hlowT
  have h0 : value last = 0 := by rw [hlast]; rfl
  have := hSt 0 h0
  omega

/-- **`ReplayedLandingRestartC` says exactly that no positive-radius fallback
with a replay run is reachable.**  Given (A), it is false. -/
theorem replayedLandingRestartC_iff (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (cP : Control) (sP : GalilVM) :
    ReplayedLandingRestartC P q first raw cP sP ↔
      ∀ (es : List Bool) (c1 : Control) (s1 : GalilVM),
        WatchSegE P q first 2048 es cP sP c1 s1 →
        ∀ (n R : ℕ) (cT : Control) (sT : GalilVM), 0 < R →
          FallbackLanding P q first raw c1 s1 n R cT sT →
          ∀ (esR : List Bool) (c' : Control) (t' : GalilVM),
            ¬ ReplayRun P q first raw cT sT R esR c' t' := by
  constructor
  · intro h es c1 s1 hseg n R cT sT hR hL esR c' t' hrep
    exact replayedLanding_not_restart hR hL hrep (h es c1 s1 hseg n R cT sT hR hL esR c' t' hrep)
  · intro h es c1 s1 hseg n R cT sT hR hL esR c' t' hrep
    exact absurd hrep (h es c1 s1 hseg n R cT sT hR hL esR c' t')

/-! ## 3. The honest landing shape -/

/-- **`FoundExit` with the `InvLPS` landing.**  `landedS` is the replayed
landing of a positive-radius fallback: `InvLP ∧ ReplayStage` (+ `CopyPack`,
`CentreRep`), with centre progress — exactly what `cycleOutMC3_of_centre`
consumes. -/
inductive FoundExitLPS (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ)
    (c : Control) (r : GalilVM) : Prop
  | exit (h : FoundExit P q first raw m c r)
  | landedS (cT : Control) (sT : GalilVM) (k : ℕ) (L : List Piece)
      (hst : StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩)
      (hcr : CostedRun r sT k L)
      (hIT : InvLPS P q first raw cT sT)
      (hprog : position r.center < position sT.center)
      (hpos : position sT.right ≤ 2 * m - 1)

/-- **Consumer.**  `cycleOutMC3_of_foundExit` extended by `cycleOutMC3_of_centre`. -/
theorem cycleOutMC3_of_foundExitLPS (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m : ℕ) {c : Control} {r : GalilVM}
    (hIN : InvLPS (PofC centre place entry raw) q first raw c r)
    (h : FoundExitLPS (PofC centre place entry raw) q first raw m c r) :
    CycleOutMC3 (PofC centre place entry raw) q first raw m c r := by
  cases h with
  | exit h => exact cycleOutMC3_of_foundExit centre place entry q first raw m hIN h
  | landedS cT sT k L hst hcr hIT hprog hpos => exact cycleOutMC3_of_centre hIN hst hcr hIT hprog hpos

/-! ## 4. The fallback reach with the honest landing -/

/-- `LandingRestartReachF` with the landing `(InvLP ∧ LandingRestart) ∨ InvLPS`. -/
def FallbackReachS (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ)
    (c : Control) (r : GalilVM) (cP : Control) (sP : GalilVM) : Prop :=
  ∀ (es : List Bool) (c1 : Control) (s1 : GalilVM),
    WatchSegE P q first 2048 es cP sP c1 s1 → LiveScanWatch c1 s1 →
    c1.clock = 1 → canRight s1.right →
    read (left s1.left) ≠ read (right s1.right) →
    ∃ (cT : Control) (sT : GalilVM) (k : ℕ) (L : List Piece),
      StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩ ∧
      CostedRun r sT k L ∧
      ((InvLP raw cT sT ∧ LandingRestart raw cT sT) ∨ InvLPS P q first raw cT sT) ∧
      position r.center < position sT.center ∧ position sT.right ≤ 2 * m - 1

theorem fallbackReachS_of_reachF {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    {m : ℕ} {c cP : Control} {r sP : GalilVM}
    (h : LandingRestartReachF P q first raw m c r cP sP) : FallbackReachS P q first raw m c r cP sP := by
  intro es c1 s1 hseg hlive hclk hav hne
  obtain ⟨cT, sT, k, L, hst, hcr, hLP, hLR, hprog, hpos⟩ := h es c1 s1 hseg hlive hclk hav hne
  exact ⟨cT, sT, k, L, hst, hcr, Or.inl ⟨hLP, hLR⟩, hprog, hpos⟩

/-- **The producer, without `ReplayedLandingRestartC`.**  Round 29's
`landingRestartReach_fallback` with the positive-radius branch landing in
`InvLPS`: `InvLP` (Round 24), `CopyPack` transported from the entry,
`CentreRep` from the fallback restart through the replay, `ReplayStage` by
`replayStage_after_replayLanding`. -/
theorem fallbackReachS_of_context (centre : GalilVM → Fin 3)
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
    (hreplay : ReplayRunC (PofC centre place entry raw) q first raw cP sP) :
    FallbackReachS (PofC centre place entry raw) q first raw m c r cP sP := by
  intro es c1 s1 hseg hlive hclk hav hne
  have hW := watchFallbackC_of_context centre place entry q first raw m c r cP sP hex hsiP hMP
    hEP houtP ⟨hns, watchFallbackCostC_of_context centre place entry q first raw m c r cP sP
      hEP houtP hentry hpiece hreplay⟩
  obtain ⟨⟨hsi, hM, hK, hT, hout⟩, -⟩ := hW es c1 s1 hseg hlive hclk hav hne
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
  · subst hR0
    have hsound : SoundScanNR raw ⟨cT, sT⟩ := stepsAll_last hL.1
    have hrep0 : StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048
        (SoundScanNR raw) ([] : List Bool).length ⟨cT, sT⟩ ⟨cT, sT⟩ := .zero _ hsound
    obtain ⟨L1, hcost1, hbound⟩ := hpiece es c1 s1 hseg hclk hav hne n 0 cT sT hL [] cT sT hrep0
    refine ⟨cT, sT, k0 + es.length + (1 + (n + 1)) + ([] : List Bool).length, L0 ++ L1,
      stepsAll_entry_to_landing centre place entry q first raw hrun hseg hEP houtP hL hrep0,
      ?_, Or.inl ⟨invLP_of_fallbackLanding_zero hL, landingRestart_of_fallbackLanding_zero hL⟩,
      by omega, hbound⟩
    have := costedRun_of_pieces hcost0 hcost1
    rwa [show k0 + (es.length + (1 + (n + 1)) + ([] : List Bool).length) =
      k0 + es.length + (1 + (n + 1)) + ([] : List Bool).length by omega] at this
  · obtain ⟨esR, c', t', hrep⟩ := hreplay es c1 s1 hseg n R cT sT hRpos hL
    obtain ⟨-, hrepAll, -, hcen, -⟩ := id hrep
    obtain ⟨L1, hcost1, hbound⟩ :=
      hpiece es c1 s1 hseg hclk hav hne n R cT sT hL esR c' t' hrepAll
    have hall := stepsAll_entry_to_landing centre place entry q first raw hrun hseg hEP houtP hL
      hrepAll
    have hRL : ReplayLanding raw cT sT R := hL.2.2.2.1 hRpos
    have hLP : InvLP raw c' t' :=
      invLP_of_landing_replay centre place entry q first raw hRL hL.2.2.2.2 hrep hall
    have hS : InvLPS (PofC centre place entry raw) q first raw c' t' :=
      ⟨⟨invLP2_of_stepsAll centre place entry q first hcopy hall hLP,
        centreRep_congr hcen (centreRep_of_restarted hRL.rest)⟩,
        replayStage_after_replayLanding hRL hrep.1⟩
    refine ⟨c', t', k0 + es.length + (1 + (n + 1)) + esR.length, L0 ++ L1, hall, ?_, Or.inr hS,
      by rw [hcen]; omega, hbound⟩
    have := costedRun_of_pieces hcost0 hcost1
    rwa [show k0 + (es.length + (1 + (n + 1)) + esR.length) =
      k0 + es.length + (1 + (n + 1)) + esR.length by omega] at this

/-! ## 5. The consumers -/

/-- `CloseoutWatchRound29.foundExitW_of_routeF` at the honest landing. -/
theorem foundExitW_of_routeS {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    {m : ℕ} {c cP : Control} {r sP : GalilVM}
    (h : FallbackReachS P q first raw m c r cP sP)
    (es : List Bool) (c1 : Control) (s1 : GalilVM)
    (hseg : WatchSegE P q first 2048 es cP sP c1 s1) (hlive : LiveScanWatch c1 s1)
    (hclk : c1.clock = 1) (hav : canRight s1.right)
    (hne : read (left s1.left) ≠ read (right s1.right)) :
    FoundExitLPS P q first raw m c r := by
  obtain ⟨cT, sT, k, L, hst, hcr, hland, hprog, hpos⟩ := h es c1 s1 hseg hlive hclk hav hne
  rcases hland with ⟨hLP, hL⟩ | hS
  · have hI := PalPeg.CloseoutWatchPhase.inv_of_invLP hLP hL
    have hSp := PalPeg.CloseoutWatchPhase.spanRep_of_invLP hLP
    obtain ⟨hM, hR, hres, hSpan⟩ := PalPeg.CloseoutFoundExits.landed_pack hI hSp
    exact .exit (.landed cT sT k L hst hcr hM hR hres hSpan hprog hpos)
  · exact .landedS cT sT k L hst hcr hS hprog hpos

/-- `CloseoutWatchRound29.foundExit_of_split3F` at the honest landing. -/
theorem foundExit_of_split3S {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    {m h : ℕ} {c cP : Control} {r sP : GalilVM}
    (hfb : FallbackReachS P q first raw m c r cP sP)
    (hneP : sP.chain ≠ ChainVM.idle)
    (hreachWatch : ∃ (es : List Bool) (c2 : Control) (s2 : GalilVM),
      WatchSegE P q first 2048 es cP sP c2 s2 ∧ LiveScanWatch c2 s2)
    (hf : TerminalRunFallbackC P q first h cP sP) :
    FoundExitLPS P q first raw m c r := by
  obtain ⟨es0, c2, s2, hsegE0, hlive2⟩ := hreachWatch
  obtain ⟨cT, sT, hseg1, hliveT, hbe⟩ := hf es0 c2 s2 hsegE0 hlive2
  obtain ⟨c1, s1, hseg2, hclk, hlive1, hav, hne⟩ := hbe
  obtain ⟨es, hsegE⟩ :=
    watchSegE_of_watchSeg (PalPeg.CloseoutWatchRun.watchSeg_append
      (PalPeg.CloseoutWatchRun.watchSeg_append
        (PalPeg.CloseoutWatchRound18.watchSeg_of_watchSegE' hsegE0 hneP) hseg1) hseg2)
  exact foundExitW_of_routeS hfb es c1 s1 hsegE hlive1 hclk hav hne

/-- `CloseoutWatchRound29.foundExit_compare_final9F'` at the honest landing. -/
theorem foundExit_compare_final9S' {centre : GalilVM → Fin 3}
    {place : GalilVM → GalilScaffoldPlace.Place} {entry q : ℕ} {first : Fin 9}
    {w : List (Fin 2)} {m h : ℕ} {c cP : Control} {r sP : GalilVM}
    (hTwo : ExitSplitC centre place entry q first w h cP sP →
      FoundExit (PofC centre place entry w) q first w m c r)
    (hrun : TerminalRunC (PofC centre place entry w) q first h cP sP)
    (hsplit3 : ExitSplit3C centre place entry q first w h cP sP)
    (hfb : FallbackReachS (PofC centre place entry w) q first w m c r cP sP)
    (hneP : sP.chain ≠ ChainVM.idle)
    (hreachWatch : ∃ (es : List Bool) (c2 : Control) (s2 : GalilVM),
      WatchSegE (PofC centre place entry w) q first 2048 es cP sP c2 s2 ∧ LiveScanWatch c2 s2) :
    FoundExitLPS (PofC centre place entry w) q first w m c r := by
  rcases hsplit3 hrun with hs | hb | hf
  · exact .exit (hTwo (fun _ => Or.inl hs))
  · exact .exit (hTwo (fun _ => Or.inr (terminalRunBreakC_of_break0 hb)))
  · exact foundExit_of_split3S hfb hneP hreachWatch hf

/-! ## 6. `foundExit_compare_final14` -/

/-- **`foundExit_compare_final13` with `LandingRestartReachF` replaced by
`FallbackReachS` and the conclusion `FoundExitLPS`.**  Families 1–3 through
`foundExit_compare_final9S'`, family 4 through the shift route as before. -/
theorem foundExit_compare_final14 (centre : GalilVM → Fin 3)
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
    (hfbS : FallbackReachS (PofC centre place entry w) q first w m c r cP sP)
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
    FoundExitLPS (PofC centre place entry w) q first w m c r := by
  classical
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
  · have htail : PalPeg.CloseoutWatchPhase2.ShiftTailC centre place entry q first w m c r cP sP :=
      mismatchShift_to_shiftRoute centre place entry q first w m h lower span
        (PalPeg.CloseoutWatchRound10.foundDpShiftC_of_at centre place entry q first w hP
          lower span h hstage hat)
        hmsr hctx hm
    have hroute := PalPeg.CloseoutWatchRound15.roundsRouteLP_of_tail centre place entry q first
      w m hex hE htail
    exact .exit (foundExit_of_compare3 centre place entry q first w m hP hE hsW a ls rs qw gap
      hprep hmis (Or.inl (PalPeg.CloseoutWatchPhase.roundsExit_of_LP hroute)))

/-- **`foundExit_compare_final14` from the fallback-branch sources.**  The
`FallbackReachS` input is replaced by Round 29's producer inputs minus
`ReplayedLandingRestartC`; `CopyPack c r` comes from the stage entry.  The
hypotheses left are all upstream: the preparation-landing tick pack
(`hsiP`/`hMP`/`hEP`/`houtP`), `WatchMismatchNoShiftC`, `EntryCostC`,
`FallbackCostPieceC`, `ReplayRunC` — none at the landing. -/
theorem foundExit_compare_final14_of_context (centre : GalilVM → Fin 3)
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
    (hreplay : ReplayRunC (PofC centre place entry w) q first w cP sP)
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
    (fallbackReachS_of_context centre place entry q hq0 first h7 h8 w m c r cP sP hE.inv.1.1.2
      hex hsiP hMP hEP houtP hns hentry hpiece hreplay)
    hstage hmP hrP hcP hreachWatch hat hreach hround hmsr hland hstepBreak

end PalPeg.CloseoutWatchRound31

#print axioms PalPeg.CloseoutWatchRound31.watchSegE_lower
#print axioms PalPeg.CloseoutWatchRound31.replayedLanding_not_restart
#print axioms PalPeg.CloseoutWatchRound31.replayedLandingRestartC_iff
#print axioms PalPeg.CloseoutWatchRound31.cycleOutMC3_of_foundExitLPS
#print axioms PalPeg.CloseoutWatchRound31.fallbackReachS_of_context
#print axioms PalPeg.CloseoutWatchRound31.foundExit_compare_final14
#print axioms PalPeg.CloseoutWatchRound31.foundExit_compare_final14_of_context
