import PalPeg.CloseoutFoundRoutes
import PalPeg.GalilFoundLandingL
import PalPeg.GalilNoShiftDischarge

/-!
# The watch phase: what the two found routes still owe

`CloseoutFoundRoutes` restates `RoundsRoute` / `BreakRoute` in the vocabulary
the route theorems export (`RoundsRouteRes` / `BreakRouteRes`: `MInv` +
`Restarted` + `FoundResidual` + `SpanRep`), but leaves both open, saying only
that they are `GalilFoundLandingL.foundRouteMC_shift` /
`GalilNoShiftDischarge.foundRouteMC_noshift_d` "with their landing sharpened
from `InvLP` to the `Inv` disjunct".

This file measures that sharpening exactly.  Both route theorems conclude with
`InvLP raw cT sT`, and `InvLP = InvL ∧ EntryCounters` where
`InvL = InvS ∧ OutputRel` and `InvS = Inv ∨ ∃ k, InvScan 2048 raw c s k`.

## Derived here

1. **`SpanRep` is free.**  `spanRep_of_invLP` — it is the third component of
   `EntryCounters`, so the routes already deliver the `SpanRep` conjunct of
   `RoundsRouteRes` with no extra work.
2. **Four of the five residual facts are free.**  `minv_of_invLP`,
   `mode_of_invLP`, `frontier_of_invLP`, `replayRest_of_invLP`,
   `shiftIdle_of_invLP` — `Inv` and `InvScan` carry `minv`, `mode`, `frontier`,
   `rest_replay` and `shiftIdle` alike, so the case split on `InvS` is
   immaterial for them.
3. **The sharpening costs exactly `Restarted` + `StageEntry`.**
   `res_of_invLP` / `inv_of_invLP`: `InvLP` plus a restart witness plus its
   stage budget *is* the whole landing record, in **both** `InvS` disjuncts.
   So "sharpen `InvLP` to the `Inv` disjunct" is not a disjunct-elimination
   problem; it is the two fields `Inv.rest` and `Inv.stage`, and nothing else.
   In particular a radius-`0` restart pays only `rest`
   (`res_of_invLP_restart0`, via
   `GalilScaffoldChainInputSupply.stage_of_restarted_zero`).
4. **The routes in `InvLP` form, and their reduction.**  `RoundsRouteLP` /
   `BreakRouteLP` are literally the conclusions of `foundRouteMC_shift` /
   `foundRouteMC_noshift_d` (`InvLP`, resp. `InvLP2`) together with the right
   bound `position sT.right ≤ 2*m-1` that `CloseoutFoundCompare` charges;
   `roundsRouteRes_of_LP` / `breakRouteRes_of_LP` turn them into
   `CloseoutFoundRoutes.RoundsRouteRes` / `BreakRouteRes` given the pointwise
   `LandingRestart`.  `roundsExit_of_LP` / `breakExit_of_LP` carry them to
   `CloseoutFoundCompare`'s exits, and `bgLanding_of_breakLP` to the background
   leaf.

## Open, NAMED with exact types

* `RoundsRouteLP P q first raw m c r cP sP` — the rounds continuation itself:
  `GalilCatchUpDistance.stageEntry_after_found_of_rounds` followed by
  `GalilFoundLandingL.foundRouteMC_shift`.  Its per-instance premises are the
  shift data (`a/ls/rs/q/gap`, `hraw`, `hCen`, `beginShiftVM`, `ChainShiftRun`,
  `shiftGuardVM`, the period tape, `Entry raw org`, `Aligned org`), `hlive`
  (`GalilOracleLeaves2.hlive_of_invLPC`), the dp `GalilDpCorrect.Result` with
  `pc = 346` / `pos 11 = h`, `hlow`, `Rounds`
  (`GalilScaffoldTopFoundLoop.found_to_found`), `ScanSeg`, and the breaking
  match at clock `1`.  None is reachable from the closeout's entry data
  (`WatchSegE` from `cP sP` alone), so this file does not close it.
* `BreakRouteLP P q first raw m c r cP sP` — likewise for
  `GalilNoShiftDischarge.foundRouteMC_noshift_d`, whose `hcont` is supplied by
  `GalilNoShiftStage.fresh_break_ledger`,
  `GalilBreakTerminal.hend3_of_matched_break` and
  `GalilReplaySpan.chainW_break'`, and whose `InvLP2` needs the entering
  `CopyPack` of `GalilInvPlus2.invLP2_of_stepsAll`.
* `LandingRestart raw cT sT` — the residual sharpening: a restart witness at
  the landing together with its stage budget.  By (3) this is *all* that the
  `InvLP` conclusion lacks.

The branch decision (whether the rounds reach the shift guard or a mismatch
breaks first) is `GalilEarlyBreak.stageEntry_after_found_final` /
`GalilBreakTerminal.stageEntry_after_found_closed`; it selects which of the two
NAMED routes applies and is not itself an obligation of this file.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutWatchPhase

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton PalPeg.GalilTraceCost
open PalPeg.GalilInvPlus PalPeg.GalilInvPlus3
open PalPeg.GalilFoundStage PalPeg.GalilFoundStageInv
open PalPeg.GalilInvPlus2 (CentreRep InvLP2 invLP2_invLP)
open PalPeg.CloseoutContracts
open PalPeg.CloseoutFoundExits
open PalPeg.CloseoutFoundRoutes

/-! ## 1. What `InvLP` already gives -/

/-- **Derived.**  `SpanRep` is the third component of `EntryCounters`. -/
theorem spanRep_of_invLP {raw : List (Fin 2)} {c : Control} {s : GalilVM}
    (h : InvLP raw c s) : SpanRep s := by
  obtain ⟨-, ⟨Rad, -, -, hS, -⟩⟩ := h
  exact hS

/-- **Derived.**  `MInv` is a field of both `InvS` disjuncts. -/
theorem minv_of_invLP {raw : List (Fin 2)} {c : Control} {s : GalilVM}
    (h : InvLP raw c s) : MInv raw c s := by
  rcases h.1.1 with hI | ⟨k, hI⟩
  · exact hI.minv
  · exact hI.minv

/-- **Derived.**  So is the parked-scan mode at the full delay. -/
theorem mode_of_invLP {raw : List (Fin 2)} {c : Control} {s : GalilVM}
    (h : InvLP raw c s) : c.mode = .scan ∧ c.replaying = false ∧ c.clock = 2048 := by
  rcases h.1.1 with hI | ⟨k, hI⟩
  · exact hI.mode
  · exact hI.mode

/-- **Derived.**  So is `Frontier`. -/
theorem frontier_of_invLP {raw : List (Fin 2)} {c : Control} {s : GalilVM}
    (h : InvLP raw c s) : Frontier s := by
  rcases h.1.1 with hI | ⟨k, hI⟩
  · exact hI.frontier
  · exact hI.frontier

/-- **Derived.**  So is `ReplayRest`. -/
theorem replayRest_of_invLP {raw : List (Fin 2)} {c : Control} {s : GalilVM}
    (h : InvLP raw c s) : ReplayRest c s := by
  rcases h.1.1 with hI | ⟨k, hI⟩
  · exact hI.rest_replay
  · exact hI.rest_replay

/-- **Derived.**  So is `ShiftIdle`. -/
theorem shiftIdle_of_invLP {raw : List (Fin 2)} {c : Control} {s : GalilVM}
    (h : InvLP raw c s) : ShiftIdle s := by
  rcases h.1.1 with hI | ⟨k, hI⟩
  · exact hI.shiftIdle
  · exact hI.shiftIdle

/-! ## 2. The sharpening, measured -/

/-- **NAMED (open), pointwise.**  The two fields of `Inv` that `InvLP` does not
contain: a restart witness and its stage budget. -/
def LandingRestart (raw : List (Fin 2)) (c : Control) (s : GalilVM) : Prop :=
  (∃ (Rad : ℕ) (last : Counter), Restarted raw s Rad last) ∧
    (∀ (Rad : ℕ) (last : Counter), Restarted raw s Rad last → StageEntry Rad last)

/-- **Derived.**  `InvLP` plus `LandingRestart` is the whole landing record of
`CloseoutFoundRoutes`.  Note the proof never needs to know which `InvS`
disjunct the landing sits in. -/
theorem res_of_invLP {raw : List (Fin 2)} {c : Control} {s : GalilVM}
    (h : InvLP raw c s) (hL : LandingRestart raw c s) :
    MInv raw c s ∧ (∃ (Rad : ℕ) (last : Counter), Restarted raw s Rad last) ∧
      FoundResidual raw c s ∧ SpanRep s :=
  ⟨minv_of_invLP h, hL.1,
    ⟨mode_of_invLP h, hL.2, frontier_of_invLP h, replayRest_of_invLP h, shiftIdle_of_invLP h⟩,
    spanRep_of_invLP h⟩

/-- **Derived.**  Hence the `Inv` pack itself. -/
theorem inv_of_invLP {raw : List (Fin 2)} {c : Control} {s : GalilVM}
    (h : InvLP raw c s) (hL : LandingRestart raw c s) : Inv raw c s :=
  have hr := res_of_invLP h hL
  inv_of_residual hr.1 hr.2.1 hr.2.2.1

/-- **Derived.**  At a radius-`0` restart the stage half of `LandingRestart` is
free, so the sharpening costs only the restart witness. -/
theorem landingRestart_of_restart0 {raw : List (Fin 2)} {c : Control} {s : GalilVM}
    {last0 : Counter} (hR : Restarted raw s 0 last0) : LandingRestart raw c s :=
  ⟨⟨0, last0, hR⟩, stage_of_restarted_zero hR⟩

/-- **Derived.**  The radius-`0` case of `res_of_invLP`. -/
theorem res_of_invLP_restart0 {raw : List (Fin 2)} {c : Control} {s : GalilVM}
    {last0 : Counter} (h : InvLP raw c s) (hR : Restarted raw s 0 last0) :
    MInv raw c s ∧ (∃ (Rad : ℕ) (last : Counter), Restarted raw s Rad last) ∧
      FoundResidual raw c s ∧ SpanRep s :=
  res_of_invLP h (landingRestart_of_restart0 hR)

/-- **Derived.**  A landing in `InvLP` is a `ReplayStage` entry as soon as it is
sharpened, so the break route's stage datum is also covered. -/
theorem replayStage_of_invLP {raw : List (Fin 2)} {P : Shared} {q : ℕ} {first : Fin 9}
    {c : Control} {s : GalilVM} (h : InvLP raw c s) (hL : LandingRestart raw c s) :
    ReplayStage raw P q first c s :=
  CloseoutFoundRoutes.replayStage_of_inv (inv_of_invLP h hL)

/-- **Derived.**  `CentreRep`, which `CloseoutFoundCompare.BreakExit` charges,
likewise follows from the sharpened landing. -/
theorem centreRep_of_invLP {raw : List (Fin 2)} {c : Control} {s : GalilVM}
    (h : InvLP raw c s) (hL : LandingRestart raw c s) : CentreRep raw s :=
  PalPeg.GalilNoShiftStage.centreRep_of_inv (inv_of_invLP h hL)

/-! ## 3. The two routes in the shape the route theorems conclude -/

/-- **NAMED (open).**  The rounds route exactly as
`GalilFoundLandingL.foundRouteMC_shift` states it (landing in `InvLP`), plus the
right-head bound `CloseoutFoundCompare` charges. -/
def RoundsRouteLP (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ)
    (c : Control) (r : GalilVM) (cP : Control) (sP : GalilVM) : Prop :=
  ∀ (hh : ℕ) (es : List Bool) (c2 : Control) (s2 : GalilVM),
    WatchSegE P q first 2048 es cP sP c2 s2 → es.length = 2*hh+2 →
    (∃ ww : GalilScaffoldChainWatch.State, s2.chain = ChainVM.watch ww) →
    ∃ (cT : Control) (sT : GalilVM) (k : ℕ) (L : List Piece),
      StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩ ∧
      CostedRun r sT k L ∧ InvLP raw cT sT ∧ LandingRestart raw cT sT ∧
      position r.center < position sT.center ∧ position sT.right ≤ 2 * m - 1

/-- **NAMED (open).**  The break route exactly as
`GalilNoShiftDischarge.foundRouteMC_noshift_d` states it (landing in `InvLP2`,
hence in `InvLP`), plus the right-head bound. -/
def BreakRouteLP (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ)
    (c : Control) (r : GalilVM) (cP : Control) (sP : GalilVM) : Prop :=
  ∀ (hh : ℕ) (es : List Bool) (c2 : Control) (s2 : GalilVM),
    WatchSegE P q first 2048 es cP sP c2 s2 → es.length = 2*hh+2 →
    (∃ ww : GalilScaffoldChainWatch.State, s2.chain = ChainVM.watch ww) →
    ∃ (cT : Control) (sT : GalilVM) (k : ℕ) (L : List Piece),
      StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩ ∧
      CostedRun r sT k L ∧ InvLP2 raw cT sT ∧ LandingRestart raw cT sT ∧
      position sT.center = position r.center ∧ position r.right < position sT.right ∧
      position sT.right ≤ 2 * m - 1

/-- **Derived.**  `RoundsRouteLP` is `CloseoutFoundRoutes.RoundsRouteRes`: every
component of the landing record but `LandingRestart` comes from `InvLP`. -/
theorem roundsRouteRes_of_LP {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)} {m : ℕ}
    {c cP : Control} {r sP : GalilVM} (h : RoundsRouteLP P q first raw m c r cP sP) :
    RoundsRouteRes P q first raw m c r cP sP := by
  intro hh es c2 s2 hseg hlen hw
  obtain ⟨cT, sT, k, L, hst, hcr, hLP, hLR, hprog, hpos⟩ := h hh es c2 s2 hseg hlen hw
  obtain ⟨hM, hR, hres, hS⟩ := res_of_invLP hLP hLR
  exact ⟨cT, sT, k, L, hst, hcr, hM, hR, hres, hS, hprog, hpos⟩

/-- **Derived.**  `BreakRouteLP` is `CloseoutFoundRoutes.BreakRouteRes`. -/
theorem breakRouteRes_of_LP {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)} {m : ℕ}
    {c cP : Control} {r sP : GalilVM} (h : BreakRouteLP P q first raw m c r cP sP) :
    BreakRouteRes P q first raw m c r cP sP := by
  intro hh es c2 s2 hseg hlen hw
  obtain ⟨cT, sT, k, L, hst, hcr, hLP2, hLR, hc, hlt, hpos⟩ := h hh es c2 s2 hseg hlen hw
  obtain ⟨hM, hR, hres, -⟩ := res_of_invLP (invLP2_invLP hLP2) hLR
  exact ⟨cT, sT, k, L, hst, hcr, hLP2, hM, hR, hres, hc, hlt, hpos⟩

/-- **Derived.**  …hence `CloseoutFoundExits.RoundsRoute`. -/
theorem roundsRoute_of_LP {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)} {m : ℕ}
    {c cP : Control} {r sP : GalilVM} (h : RoundsRouteLP P q first raw m c r cP sP) :
    RoundsRoute P q first raw m c r cP sP :=
  roundsRoute_of_res (roundsRouteRes_of_LP h)

/-- **Derived.**  …hence `CloseoutFoundExits.BreakRoute`. -/
theorem breakRoute_of_LP {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)} {m : ℕ}
    {c cP : Control} {r sP : GalilVM} (h : BreakRouteLP P q first raw m c r cP sP) :
    BreakRoute P q first raw m c r cP sP :=
  breakRoute_of_res (breakRouteRes_of_LP h)

/-- **Derived.**  …and the two `CloseoutFoundCompare` exits. -/
theorem roundsExit_of_LP {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)} {m : ℕ}
    {c cP : Control} {r sP : GalilVM} (h : RoundsRouteLP P q first raw m c r cP sP) :
    PalPeg.CloseoutFoundCompare.RoundsExit P q first raw m c r cP sP :=
  roundsExit_of_res (roundsRouteRes_of_LP h)

theorem breakExit_of_LP {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)} {m : ℕ}
    {c cP : Control} {r sP : GalilVM} (h : BreakRouteLP P q first raw m c r cP sP) :
    PalPeg.CloseoutFoundCompare.BreakExit P q first raw m c r cP sP :=
  breakExit_of_res (breakRouteRes_of_LP h)

/-- **Derived.**  A single break landing in `InvLP2` feeds the background leaf,
with `ReplayStage` and `CentreRep` reconstructed from the sharpening. -/
theorem bgLanding_of_breakLP {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    {m k : ℕ} {c cT : Control} {r sT : GalilVM} {L : List Piece}
    (hst : StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩)
    (hcr : CostedRun r sT k L) (hLP2 : InvLP2 raw cT sT) (hLR : LandingRestart raw cT sT)
    (hc : position sT.center = position r.center)
    (hlt : position r.right < position sT.right)
    (hpos : position sT.right ≤ 2 * m - 1) :
    PalPeg.CloseoutFoundBackground.BgLanding P q first raw m c r :=
  have hI : Inv raw cT sT := inv_of_invLP (invLP2_invLP hLP2) hLR
  bgLanding_of_break hst hcr hLP2 hI (CloseoutFoundRoutes.replayStage_of_inv hI) hc hlt hpos

/-- **Derived.**  The rounds landing likewise feeds the background leaf's first
disjunct once its run is a `FoundCost`. -/
theorem bgLanding_of_roundsLP {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)} {m : ℕ}
    {c cT : Control} {r sT : GalilVM}
    (hcost : PalPeg.GalilOracleMC.FoundCost P q first raw c r cT sT)
    (hLP : InvLP raw cT sT) (hLR : LandingRestart raw cT sT)
    (hprog : position r.center < position sT.center)
    (hpos : position sT.right ≤ 2 * m - 1) :
    PalPeg.CloseoutFoundBackground.BgLanding P q first raw m c r :=
  bgLanding_of_route hcost (inv_of_invLP hLP hLR) (spanRep_of_invLP hLP) hprog hpos

/-! ## 4. The in-replay leaf's continuation, sharpened the same way -/

/-- **Derived.**  `CloseoutFoundExits.continuesToRestart_of_run` over an `InvLP`
landing. -/
theorem continuesToRestart_of_invLP {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    {m : ℕ} {cT cU : Control} {sT sU : GalilVM} {k' : ℕ} {L' : List Piece}
    (hst : StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k' ⟨cT, sT⟩ ⟨cU, sU⟩)
    (hcr : CostedRun sT sU k' L') (hLP : InvLP raw cU sU) (hLR : LandingRestart raw cU sU)
    (hmono : position sT.center ≤ position sU.center)
    (hpos : position sU.right ≤ 2 * m - 1) :
    PalPeg.CloseoutFoundReplay.ContinuesToRestart P q first raw m cT sT :=
  continuesToRestart_of_run hst hcr (inv_of_invLP hLP hLR) (spanRep_of_invLP hLP) hmono hpos

end PalPeg.CloseoutWatchPhase

#print axioms PalPeg.CloseoutWatchPhase.spanRep_of_invLP
#print axioms PalPeg.CloseoutWatchPhase.minv_of_invLP
#print axioms PalPeg.CloseoutWatchPhase.mode_of_invLP
#print axioms PalPeg.CloseoutWatchPhase.frontier_of_invLP
#print axioms PalPeg.CloseoutWatchPhase.replayRest_of_invLP
#print axioms PalPeg.CloseoutWatchPhase.shiftIdle_of_invLP
#print axioms PalPeg.CloseoutWatchPhase.res_of_invLP
#print axioms PalPeg.CloseoutWatchPhase.inv_of_invLP
#print axioms PalPeg.CloseoutWatchPhase.res_of_invLP_restart0
#print axioms PalPeg.CloseoutWatchPhase.replayStage_of_invLP
#print axioms PalPeg.CloseoutWatchPhase.centreRep_of_invLP
#print axioms PalPeg.CloseoutWatchPhase.roundsRouteRes_of_LP
#print axioms PalPeg.CloseoutWatchPhase.breakRouteRes_of_LP
#print axioms PalPeg.CloseoutWatchPhase.roundsRoute_of_LP
#print axioms PalPeg.CloseoutWatchPhase.breakRoute_of_LP
#print axioms PalPeg.CloseoutWatchPhase.roundsExit_of_LP
#print axioms PalPeg.CloseoutWatchPhase.breakExit_of_LP
#print axioms PalPeg.CloseoutWatchPhase.bgLanding_of_breakLP
#print axioms PalPeg.CloseoutWatchPhase.bgLanding_of_roundsLP
#print axioms PalPeg.CloseoutWatchPhase.continuesToRestart_of_invLP
