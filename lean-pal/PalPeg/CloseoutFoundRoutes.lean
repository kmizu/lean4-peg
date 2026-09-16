import PalPeg.CloseoutFoundExits

/-!
# The three named routes of `CloseoutFoundExits`

`CloseoutFoundExits` leaves `RoundsRoute`, `BreakRoute` and `PrefixCostAt` open
and says of the first two only that they are
`GalilFoundLandingL.foundRouteMC_shift` / `GalilNoShiftDischarge.foundRouteMC_noshift_d`
"with their landing sharpened from `InvLP` to the `Inv` disjunct".

This file settles how much of that sharpening is *free* and reduces each route
to the smallest datum that is genuinely missing.

## Derived here

1. `replayStage_of_inv` — **`BreakRoute.stage` is not an obligation.**
   `ReplayStage` asks for a restart with its stage budget and a clock-`2048`
   entry, and those are literally `Inv.rest`, `Inv.stage` and `Inv.mode.2.2`.
   The note in `CloseoutFoundExits` that
   "`GalilFoundStageInv.replayStage_entry` applies only after a restart" is
   answered by the fact that `Inv` *is* a restart pack.
2. `inv_of_restart0` — a landing at a **radius-`0`** restart needs no stage
   argument at all (`GalilScaffoldChainInputSupply.stage_of_restarted_zero`),
   so the pack there costs only the four residual facts.
3. `RoundsRouteRes` / `BreakRouteRes` and `roundsRoute_of_res` /
   `breakRoute_of_res` — the two routes restated in the vocabulary the route
   theorems actually export (`MInv` + `Restarted` + `FoundResidual` + `SpanRep`,
   never `Inv`), with `roundsExit_of_res` / `breakExit_of_res` carrying them all
   the way to `CloseoutFoundCompare`'s exits.
4. `prefixCostAt_parked`, `prefixCostAt_of_parked`,
   `prefixCostAt_progress_forces_right` — the sharp form of the third open.
   A parked right head forces the piece list to be **empty**, hence `k = 0` and
   the centre to stand still; conversely a parked, centre-preserving stretch has
   `PrefixCostAt _ _ 0` for free.  Since `CloseoutFoundExits.foundExit_of_leaf'`
   also demands strict centre progress, the in-replay leaf's `PrefixCostAt`
   **cannot** be about a parked stretch: `prefixCostAt_progress_forces_right`
   shows the leaf's own prefix run must advance the right head.  That is the
   pointwise replacement for `GalilCostedFallback.costedRun_fallback_replay`'s
   quiet hypothesis: the replay itself contributes no piece, the prefix does.

## Open, NAMED with exact types

* `RoundsRouteRes P q first raw m c r cP sP` — the rounds continuation itself.
  Exactly `GalilCatchUpDistance.stageEntry_after_found_of_rounds` followed by
  `GalilFoundLandingL.foundRouteMC_shift`, whose per-instance premises (the
  shift data `a/ls/rs/q/gap`, `hlive`, the dp `Result`, `hlow`, `Rounds`,
  `ScanSeg`, the breaking match) are not reachable from the closeout's entry
  data.  What this file removes from it is only the record half.
* `BreakRouteRes P q first raw m c r cP sP` — likewise for
  `GalilNoShiftDischarge.foundRouteMC_noshift_d` with `hcont` supplied by
  `GalilNoShiftStage.fresh_break_ledger` / `fresh_break_stage`,
  `GalilBreakTerminal.hend3_of_matched_break` and
  `GalilReplaySpan.chainW_break'`; its `InvLP2` still needs the entering
  `CopyPack` of `GalilInvPlus2.invLP2_of_stepsAll`.
* `PrefixCostAt r sT k` for the in-replay leaf — by
  `prefixCostAt_progress_forces_right` this is the statement that the leaf's
  prefix run is a right-advancing costed stretch; the piece list itself still
  comes from `GalilCostedFallback`.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutFoundRoutes

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton PalPeg.GalilTraceCost
open PalPeg.GalilInvPlus PalPeg.GalilInvPlus3
open PalPeg.GalilFoundStage PalPeg.GalilFoundStageInv
open PalPeg.GalilInvPlus2 (CentreRep InvLP2)
open PalPeg.CloseoutContracts
open PalPeg.CloseoutFoundExits

/-! ## 1. The stage datum of a landing is free -/

/-- **Derived.**  Every restart pack is a `ReplayStage` entry point.  The three
ingredients `GalilFoundStageInv.replayStage_entry` wants — a `Restarted`, its
`StageEntry` and a clock at the full delay — are fields of `Inv`, and the
segment witnessing `ReplayStage` is the empty one. -/
theorem replayStage_of_inv {raw : List (Fin 2)} {P : Shared} {q : ℕ} {first : Fin 9}
    {c : Control} {s : GalilVM} (hI : Inv raw c s) : ReplayStage raw P q first c s := by
  obtain ⟨Rad, last, hR⟩ := hI.rest
  exact replayStage_entry hR (hI.stage Rad last hR) hI.mode.2.2

/-- **Derived.**  The same from the record half of `landed_pack`, i.e. without
ever building `Inv`. -/
theorem replayStage_of_residual {raw : List (Fin 2)} {P : Shared} {q : ℕ} {first : Fin 9}
    {c : Control} {s : GalilVM} (hM : MInv raw c s)
    (hR : ∃ (Rad : ℕ) (last : Counter), Restarted raw s Rad last)
    (hres : FoundResidual raw c s) : ReplayStage raw P q first c s :=
  replayStage_of_inv (inv_of_landed_pack hM hR hres)

/-! ## 2. A radius-`0` restart pays no stage -/

/-- **Derived.**  At a radius-`0` restart the stage budget is vacuous
(`stage_of_restarted_zero`), so the pack is exactly `MInv` plus the four
mechanical residual facts. -/
theorem inv_of_restart0 {raw : List (Fin 2)} {c : Control} {s : GalilVM} {last0 : Counter}
    (hM : MInv raw c s) (hR : Restarted raw s 0 last0)
    (hmode : c.mode = .scan ∧ c.replaying = false ∧ c.clock = 2048)
    (hfr : Frontier s) (hrr : ReplayRest c s) (hsi : ShiftIdle s) : Inv raw c s :=
  inv_of_residual hM ⟨0, last0, hR⟩ ⟨hmode, stage_of_restarted_zero hR, hfr, hrr, hsi⟩

/-- **Derived.**  Hence a radius-`0` landing is already a `ReplayStage` entry. -/
theorem replayStage_of_restart0 {raw : List (Fin 2)} {P : Shared} {q : ℕ} {first : Fin 9}
    {c : Control} {s : GalilVM} {last0 : Counter}
    (hM : MInv raw c s) (hR : Restarted raw s 0 last0)
    (hmode : c.mode = .scan ∧ c.replaying = false ∧ c.clock = 2048)
    (hfr : Frontier s) (hrr : ReplayRest c s) (hsi : ShiftIdle s) :
    ReplayStage raw P q first c s :=
  replayStage_of_inv (inv_of_restart0 hM hR hmode hfr hrr hsi)

/-! ## 3. The two routes in the route theorems' own vocabulary -/

/-- **NAMED (open).**  The rounds continuation, stated with the landing record
the route theorems export instead of the pack.  `roundsRoute_of_res` shows this
is the same requirement as `CloseoutFoundExits.RoundsRoute`. -/
def RoundsRouteRes (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ)
    (c : Control) (r : GalilVM) (cP : Control) (sP : GalilVM) : Prop :=
  ∀ (hh : ℕ) (es : List Bool) (c2 : Control) (s2 : GalilVM),
    WatchSegE P q first 2048 es cP sP c2 s2 → es.length = 2*hh+2 →
    (∃ ww : GalilScaffoldChainWatch.State, s2.chain = ChainVM.watch ww) →
    ∃ (cT : Control) (sT : GalilVM) (k : ℕ) (L : List Piece),
      StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩ ∧
      CostedRun r sT k L ∧ MInv raw cT sT ∧
      (∃ (Rad : ℕ) (last : Counter), Restarted raw sT Rad last) ∧
      FoundResidual raw cT sT ∧ SpanRep sT ∧
      position r.center < position sT.center ∧ position sT.right ≤ 2 * m - 1

/-- **Derived.**  `RoundsRouteRes` is `CloseoutFoundExits.RoundsRoute`. -/
theorem roundsRoute_of_res {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)} {m : ℕ}
    {c cP : Control} {r sP : GalilVM} (h : RoundsRouteRes P q first raw m c r cP sP) :
    RoundsRoute P q first raw m c r cP sP := by
  intro hh es c2 s2 hseg hlen hw
  obtain ⟨cT, sT, k, L, hst, hcr, hM, hR, hres, hS, hprog, hpos⟩ := h hh es c2 s2 hseg hlen hw
  exact ⟨cT, sT, k, L, hst, hcr, inv_of_landed_pack hM hR hres, hS, hprog, hpos⟩

/-- **Derived.**  …and therefore `CloseoutFoundCompare.RoundsExit`. -/
theorem roundsExit_of_res {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)} {m : ℕ}
    {c cP : Control} {r sP : GalilVM} (h : RoundsRouteRes P q first raw m c r cP sP) :
    PalPeg.CloseoutFoundCompare.RoundsExit P q first raw m c r cP sP :=
  roundsExit_of_route (roundsRoute_of_res h)

/-- **NAMED (open).**  The break continuation, with the stage datum **dropped**:
by `replayStage_of_inv` it is implied by the landing record. -/
def BreakRouteRes (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ)
    (c : Control) (r : GalilVM) (cP : Control) (sP : GalilVM) : Prop :=
  ∀ (hh : ℕ) (es : List Bool) (c2 : Control) (s2 : GalilVM),
    WatchSegE P q first 2048 es cP sP c2 s2 → es.length = 2*hh+2 →
    (∃ ww : GalilScaffoldChainWatch.State, s2.chain = ChainVM.watch ww) →
    ∃ (cT : Control) (sT : GalilVM) (k : ℕ) (L : List Piece),
      StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩ ∧
      CostedRun r sT k L ∧ InvLP2 raw cT sT ∧ MInv raw cT sT ∧
      (∃ (Rad : ℕ) (last : Counter), Restarted raw sT Rad last) ∧
      FoundResidual raw cT sT ∧
      position sT.center = position r.center ∧ position r.right < position sT.right ∧
      position sT.right ≤ 2 * m - 1

/-- **Derived.**  `BreakRouteRes` is `CloseoutFoundExits.BreakRoute`: the
`ReplayStage` component is reconstructed by `replayStage_of_inv`. -/
theorem breakRoute_of_res {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)} {m : ℕ}
    {c cP : Control} {r sP : GalilVM} (h : BreakRouteRes P q first raw m c r cP sP) :
    BreakRoute P q first raw m c r cP sP := by
  intro hh es c2 s2 hseg hlen hw
  obtain ⟨cT, sT, k, L, hst, hcr, hIT, hM, hR, hres, hc, hlt, hpos⟩ := h hh es c2 s2 hseg hlen hw
  have hI : Inv raw cT sT := inv_of_landed_pack hM hR hres
  exact ⟨cT, sT, k, L, hst, hcr, hIT, hI, replayStage_of_inv hI, hc, hlt, hpos⟩

/-- **Derived.**  …and therefore `CloseoutFoundCompare.BreakExit`. -/
theorem breakExit_of_res {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)} {m : ℕ}
    {c cP : Control} {r sP : GalilVM} (h : BreakRouteRes P q first raw m c r cP sP) :
    PalPeg.CloseoutFoundCompare.BreakExit P q first raw m c r cP sP :=
  breakExit_of_route (breakRoute_of_res h)

/-- **Derived.**  The break landing also feeds `CloseoutFoundExits.bgLanding_of_break`
once the route is available, so the background leaf shares the same datum. -/
theorem bgLanding_of_breakRes {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    {m k : ℕ} {c cT : Control} {r sT : GalilVM} {L : List Piece}
    (hst : StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩)
    (hcr : CostedRun r sT k L) (hIT : InvLP2 raw cT sT) (hM : MInv raw cT sT)
    (hR : ∃ (Rad : ℕ) (last : Counter), Restarted raw sT Rad last)
    (hres : FoundResidual raw cT sT)
    (hc : position sT.center = position r.center)
    (hlt : position r.right < position sT.right)
    (hpos : position sT.right ≤ 2 * m - 1) :
    PalPeg.CloseoutFoundBackground.BgLanding P q first raw m c r :=
  have hI : Inv raw cT sT := inv_of_landed_pack hM hR hres
  bgLanding_of_break hst hcr hIT hI (replayStage_of_inv hI) hc hlt hpos

/-! ## 4. `PrefixCostAt` of a parked stretch -/

/-- **Derived.**  `PrefixCostAt` is reflexive on a state pair with the same
centre and a monotone right head: the empty decomposition works. -/
theorem prefixCostAt_of_parked {r sT : GalilVM}
    (hc : position sT.center = position r.center)
    (hmono : position r.right ≤ position sT.right) : PrefixCostAt r sT 0 :=
  ⟨[], ⟨rfl, by simpa using hc, hmono, fun _ h => absurd h (List.not_mem_nil), List.Pairwise.nil⟩⟩

/-- **Derived.**  Conversely, a parked right head forces the decomposition to be
empty — every piece's place must sit in the empty interval
`(position r.right, position sT.right]` — hence `k = 0` and the centre stands
still.  This is the exact content of `costedRun_right_progress` at the level of
`PrefixCostAt`. -/
theorem prefixCostAt_parked {r sT : GalilVM} {k : ℕ} (h : PrefixCostAt r sT k)
    (hp : position sT.right ≤ position r.right) :
    k = 0 ∧ position sT.center = position r.center := by
  obtain ⟨L, hcr⟩ := h
  have hnil : L = [] := by
    cases hL : L with
    | nil => rfl
    | cons p ps =>
        have hp' : p ∈ L := by rw [hL]; exact List.mem_cons_self
        have h1 := (hcr.places p hp').1
        have h2 := (hcr.places p hp').2
        omega
  subst hnil
  refine ⟨?_, ?_⟩
  · have := hcr.ticks; simpa using this.symm
  · have := hcr.centre; simpa using this

/-- **Derived.**  The in-replay leaf of `CloseoutFoundExits.foundExit_of_leaf'`
also demands strict centre progress, and a parked stretch has a standing centre.
So the leaf's prefix run **must** advance the right head: `PrefixCostAt` is never
about the parked part of a replay. -/
theorem prefixCostAt_progress_forces_right {r sT : GalilVM} {k : ℕ}
    (h : PrefixCostAt r sT k) (hprog : position r.center < position sT.center) :
    position r.right < position sT.right := by
  by_contra hcon
  obtain ⟨-, hc⟩ := prefixCostAt_parked h (by omega)
  omega

/-- **Derived.**  `PrefixCostAt` composes, so the leaf's prefix may be assembled
segment by segment. -/
theorem prefixCostAt_trans {a b c : GalilVM} {k1 k2 : ℕ}
    (h1 : PrefixCostAt a b k1) (h2 : PrefixCostAt b c k2) : PrefixCostAt a c (k1 + k2) := by
  obtain ⟨L1, h1⟩ := h1
  obtain ⟨L2, h2⟩ := h2
  exact ⟨L1 ++ L2, costedRun_trans h1 h2⟩

/-- **Derived.**  The in-replay leaf with the prefix cost assembled from two
stretches, the second of which is parked (the replay proper). -/
theorem foundExit_of_leaf_split {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    {m k R : ℕ} {c cT : Control} {r u sT : GalilVM}
    (hpc : PrefixCostAt r u k)
    (hpark : position sT.center = position u.center)
    (hmono : position u.right ≤ position sT.right)
    (hch : PalPeg.CloseoutFoundReplay.ChainContinuation P q first raw m)
    (hrc : PalPeg.CloseoutFoundReplay.RestartContinuation P q first raw m)
    (hst : StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩)
    (hL : PalPeg.GalilOracleDischarge.ReplayLanding raw cT sT R) (hSpan : SpanRep sT)
    (hprog : position r.center < position sT.center)
    (hpos : position sT.right ≤ 2 * m - 1)
    (hor : PalPeg.GalilReplaySpan.ChainEnd raw P q first 2048 (position sT.right + R) cT sT 0 R ∨
      PalPeg.GalilReplaySpan.BrokeAndRestarted raw P q first 2048 cT sT) :
    FoundExit P q first raw m c r := by
  have hk : PrefixCostAt r sT k := by
    have := prefixCostAt_trans hpc (prefixCostAt_of_parked hpark hmono)
    simpa using this
  exact foundExit_of_leaf' hk hch hrc hst hL hSpan hprog hpos hor

end PalPeg.CloseoutFoundRoutes

#print axioms PalPeg.CloseoutFoundRoutes.replayStage_of_inv
#print axioms PalPeg.CloseoutFoundRoutes.replayStage_of_residual
#print axioms PalPeg.CloseoutFoundRoutes.inv_of_restart0
#print axioms PalPeg.CloseoutFoundRoutes.replayStage_of_restart0
#print axioms PalPeg.CloseoutFoundRoutes.roundsRoute_of_res
#print axioms PalPeg.CloseoutFoundRoutes.roundsExit_of_res
#print axioms PalPeg.CloseoutFoundRoutes.breakRoute_of_res
#print axioms PalPeg.CloseoutFoundRoutes.breakExit_of_res
#print axioms PalPeg.CloseoutFoundRoutes.bgLanding_of_breakRes
#print axioms PalPeg.CloseoutFoundRoutes.prefixCostAt_of_parked
#print axioms PalPeg.CloseoutFoundRoutes.prefixCostAt_parked
#print axioms PalPeg.CloseoutFoundRoutes.prefixCostAt_progress_forces_right
#print axioms PalPeg.CloseoutFoundRoutes.prefixCostAt_trans
#print axioms PalPeg.CloseoutFoundRoutes.foundExit_of_leaf_split
