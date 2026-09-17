import PalPeg.CloseoutWatchRound20

/-!
# Closeout watch round 21 — a producer for `FallbackRouteW`

`CloseoutWatchRound17.FallbackRouteW` is the outer-mismatch exit of a watch
round: a clock-`1` available mismatch at a *watching* chain, followed by the
fallback tick, landing in a state with the route record the found landing
needs (a costed `StepsAll` run from the stage entry `⟨c, r⟩`, `InvLP`, centre
progress, right-head bound).

## What is derived here

The fallback tick itself.  `GalilInvPlus.fallback_pack_span` needs nothing
about the chain being idle — its premises are all local to the mismatch state
(`ShiftIdle`, `MInv`, `FallbackCounters`, `FallbackTick`, `OutputRel`), so the
landing of the fallback tick out of a **watch** mismatch is obtained from it
verbatim: a `1 + (n+1)`-tick run into a restarted state that is `Inv` (radius
`0`) or a `ReplayLanding` (radius `R > 0`), with `SpanRep` and strict centre
progress.  In the radius-`0` case the landing is already `InvLP`
(`invLP_of_landed`).

## The ONE hypothesis left: `WatchFallbackC`

Two things are **not** derivable from the round structure, and are packaged
as one named contract per mismatch landing:

1. the *tick pack* at the watch mismatch — `MInv`, `FallbackCounters`,
   `FallbackTick`, `ShiftIdle`, `OutputRel`.  `FallbackTick` is the genuine
   content: at a watching chain the outer mismatch may instead satisfy
   `shiftGuardVM` (chain at phase `4`, lag `0`, unbroken, period focus
   matching), in which case the machine shifts rather than falls back; the
   contract asserts the fallback branch.  The other four are segment-transported
   facts (`minv_watchSegE`, `fallbackCounters_of_seg`, `stepsAll_last`) whose
   *sources* at the preparation landing `⟨cP, sP⟩` are not among the
   parameters of `FallbackRouteW`.
2. the *cost closure* — the route record from the stage entry `⟨c, r⟩` through
   the fallback landing (and, when `0 < R`, through the replay segment that
   turns a `ReplayLanding` into `InvLP`).  `FallbackRouteW` quantifies over
   `⟨c, r⟩` with no run from it to `⟨cP, sP⟩` in scope, and `CostedRun` pieces
   are aligned at clock-`2048` boundaries (`costedRun_fallback_zero/replay` start
   from an `InvL` entry with a single `WatchSegE`), so the cost of a mid-phase
   fallback cannot be assembled from the tick alone.

Which conjunct needed it: the `StepsAll … ⟨c, r⟩ ⟨cT, sT⟩ ∧ CostedRun r sT k L`
pair (the run from the *entry*), and — through the replay case — `InvLP`; the
existence of the landing, its `Inv`/`ReplayLanding`/`SpanRep` shape and the
centre progress out of the mismatch state are derived.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutWatchRound21

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
open PalPeg.CloseoutWatchRound17 (FallbackRouteW)

/-! ## 1. The one hypothesis -/

/-- The fallback landing record out of a mismatch state `⟨c1, s1⟩`, exactly as
`GalilInvPlus.fallback_pack_span` produces it. -/
def FallbackLanding (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (c1 : Control) (s1 : GalilVM) (n R : ℕ) (cT : Control) (sT : GalilVM) : Prop :=
  StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) (1 + (n + 1)) ⟨c1, s1⟩ ⟨cT, sT⟩ ∧
    position s1.center < position sT.center ∧
    (R = 0 → Inv raw cT sT) ∧ (0 < R → ReplayLanding raw cT sT R) ∧ SpanRep sT

/-- **NAMED (open).**  The watch-mismatch contract: at every clock-`1`
available outer mismatch reached from the preparation landing while the chain
is watching, (1) the tick pack that makes the next tick a fallback, and (2) the
cost closure of its landing from the stage entry. -/
def WatchFallbackC (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ)
    (c : Control) (r : GalilVM) (cP : Control) (sP : GalilVM) : Prop :=
  ∀ (es : List Bool) (c1 : Control) (s1 : GalilVM),
    WatchSegE (PofC centre place entry raw) q first 2048 es cP sP c1 s1 → LiveScanWatch c1 s1 →
    c1.clock = 1 → canRight s1.right →
    read (left s1.left) ≠ read (right s1.right) →
    (ShiftIdle s1 ∧ MInv raw c1 s1 ∧ FallbackCounters raw s1 ∧
      FallbackTick centre place entry raw s1 ∧ OutputRel raw c1 s1) ∧
    (∀ (n R : ℕ) (cT : Control) (sT : GalilVM),
      FallbackLanding (PofC centre place entry raw) q first raw c1 s1 n R cT sT →
      ∃ (cT' : Control) (sT' : GalilVM) (k : ℕ) (L : List Piece),
        StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048 (SoundScanNR raw) k
          ⟨c, r⟩ ⟨cT', sT'⟩ ∧
        CostedRun r sT' k L ∧ InvLP raw cT' sT' ∧
        position sT.center ≤ position sT'.center ∧ position r.center ≤ position s1.center ∧
        position sT'.right ≤ 2 * m - 1)

/-! ## 2. The derived part: the fallback tick out of a watch mismatch -/

/-- **Derived.**  The fallback tick out of a *watching* clock-`1` mismatch
lands: `fallback_pack_span` needs no idle chain. -/
theorem fallbackLanding_of_pack (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (hq0 : 0 < q) (first : Fin 9)
    (h7 : first ≠ 7) (h8 : first ≠ 8) (raw : List (Fin 2))
    {c1 : Control} {s1 : GalilVM} (hlive : LiveScanWatch c1 s1) (hclk : c1.clock = 1)
    (hav : canRight s1.right) (hne : read (left s1.left) ≠ read (right s1.right))
    (hsi : ShiftIdle s1) (hM : MInv raw c1 s1) (hK : FallbackCounters raw s1)
    (hT : FallbackTick centre place entry raw s1) (hout : OutputRel raw c1 s1) :
    ∃ (n R : ℕ) (cT : Control) (sT : GalilVM),
      FallbackLanding (PofC centre place entry raw) q first raw c1 s1 n R cT sT := by
  obtain ⟨hm, hr, -, -⟩ := hlive
  obtain ⟨n, R, cT, sT, hst, hprog, hz, hp, hS⟩ :=
    fallback_pack_span centre place entry q hq0 first h7 h8 raw c1 s1 hm hr hclk hsi hav hne hM hK
      hT hout
  exact ⟨n, R, cT, sT, hst, hprog, hz, hp, hS⟩

/-- **Derived.**  In the radius-`0` case the fallback landing is already
`InvLP`, with no replay segment needed. -/
theorem invLP_of_fallbackLanding_zero {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    {c1 cT : Control} {s1 sT : GalilVM} {n : ℕ}
    (h : FallbackLanding P q first raw c1 s1 n 0 cT sT) : InvLP raw cT sT :=
  invLP_of_landed h.1 (h.2.2.1 rfl) h.2.2.2.2

/-! ## 3. The producer -/

/-- **The producer for `FallbackRouteW`, under `WatchFallbackC`.** -/
theorem fallbackRouteW_of_tick (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (hq0 : 0 < q) (first : Fin 9)
    (h7 : first ≠ 7) (h8 : first ≠ 8) (raw : List (Fin 2)) (m : ℕ)
    (c : Control) (r : GalilVM) (cP : Control) (sP : GalilVM)
    (hW : WatchFallbackC centre place entry q first raw m c r cP sP) :
    FallbackRouteW (PofC centre place entry raw) q first raw m c r cP sP := by
  intro es c1 s1 hseg hlive hclk hav hne
  obtain ⟨⟨hsi, hM, hK, hT, hout⟩, hclose⟩ := hW es c1 s1 hseg hlive hclk hav hne
  obtain ⟨n, R, cT, sT, hL⟩ :=
    fallbackLanding_of_pack centre place entry q hq0 first h7 h8 raw hlive hclk hav hne hsi hM hK
      hT hout
  obtain ⟨cT', sT', k, L, hst, hcr, hLP, hle, hr1, hpos⟩ := hclose n R cT sT hL
  refine ⟨cT', sT', k, L, hst, hcr, hLP, ?_, hpos⟩
  have hprog := hL.2.1
  omega

end PalPeg.CloseoutWatchRound21

#print axioms PalPeg.CloseoutWatchRound21.fallbackLanding_of_pack
#print axioms PalPeg.CloseoutWatchRound21.invLP_of_fallbackLanding_zero
#print axioms PalPeg.CloseoutWatchRound21.fallbackRouteW_of_tick
