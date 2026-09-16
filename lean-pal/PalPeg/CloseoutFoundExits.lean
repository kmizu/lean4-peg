import PalPeg.CloseoutFoundCompare
import PalPeg.CloseoutFoundReplay
import PalPeg.CloseoutFoundBackground
import PalPeg.GalilNoShiftStage

/-!
# The post-preparation exits of the three found leaves

`CloseoutFoundCompare.RoundsExit` / `BreakExit`,
`CloseoutFoundReplay.ChainContinuation` / `RestartContinuation` / `PrefixCost`
and `CloseoutFoundBackground`'s `H_after` all ask the same question: *what does
the machine do after the derived preparation segment, and does its landing carry
the full record the closeout charges?*

This file settles the **record half** of that question and isolates the rest.

## Derived here

1. `landed_pack` — a landing in the restart pack `Inv` with `SpanRep` **is**
   the whole `FoundExit.landed` record: `MInv` is `Inv.minv`, `Restarted` is
   `Inv.rest`, and `FoundResidual` is literally the tuple
   `⟨Inv.mode, Inv.stage, Inv.frontier, Inv.rest_replay, Inv.shiftIdle⟩`.
   So the "upgrade from `InvLP` to the landing record", named open in
   `CloseoutFoundCompare`, is **not** an extra proof obligation: it is exactly
   the statement that the landing sits in the `Inv` disjunct of
   `GalilOracleDischarge.InvS`, and nothing more.
2. `roundsExit_of_route`, `breakExit_of_route`, `continuesToRestart_of_run`,
   `bgLanding_of_route` — the four consumers, each reduced to that single
   residual fact.  `CentreRep` in the break branch is likewise derived
   (`GalilNoShiftStage.centreRep_of_inv`).
3. `costedRun_right_progress` / `prefixCost_forces_right_progress` — a
   **negative** result about `CloseoutFoundReplay.PrefixCost`: a `CostedRun` of
   `k > 0` ticks forces `position r.right < position sT.right`, because its
   pieces must live in `(position r.right, position sT.right]` and their ticks
   sum to `k`.  A replay stretch parks the right head, so `PrefixCost` as
   stated (**for every** sound run) is unusable there.  `foundExit_of_leaf'`
   replaces it by the pointwise `PrefixCostAt`.

## Open, NAMED with exact types

* `RoundsRoute` / `BreakRoute` / `BgRoute` — the continuation of the machine
  after the derived preparation segment, landing in `Inv` (resp. `InvLP2`).
  These are `GalilFoundLandingL.foundRouteMC_shift` /
  `GalilNoShiftDischarge.foundRouteMC_noshift_d` with their landing sharpened
  from `InvLP` to the `Inv` disjunct; the per-instance premise lists of those
  theorems are not reachable from the closeout's entry data.
* `BreakRoute.stage` — the `ReplayStage` of the break landing
  (`GalilFoundStageInv.replayStage_entry` applies only after a restart).
* `PrefixCostAt` — the cost of the in-replay leaf's own prefix run.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutFoundExits

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton PalPeg.GalilTraceCost
open PalPeg.GalilInvPlus PalPeg.GalilInvPlus3
open PalPeg.GalilFoundStage PalPeg.GalilFoundStageInv
open PalPeg.GalilInvPlus2 (CentreRep InvLP2)
open PalPeg.CloseoutContracts

/-! ## 1. A restart landing is the whole landing record -/

/-- **Derived.**  The four components `FoundExit.landed` charges are the fields
of `GalilRunInv.Inv` plus `SpanRep`.  No reinforcement step is needed. -/
theorem landed_pack {raw : List (Fin 2)} {cT : Control} {sT : GalilVM}
    (hI : Inv raw cT sT) (hS : SpanRep sT) :
    MInv raw cT sT ∧ (∃ (Rad : ℕ) (last : Counter), Restarted raw sT Rad last) ∧
      FoundResidual raw cT sT ∧ SpanRep sT :=
  ⟨hI.minv, hI.rest, ⟨hI.mode, hI.stage, hI.frontier, hI.rest_replay, hI.shiftIdle⟩, hS⟩

/-- **Derived.**  Conversely the record is the pack (`inv_of_residual`), so
"landing in `Inv` with `SpanRep`" and "carrying the landing record" are the same
condition — the open part of the exits is the *route*, never the upgrade. -/
theorem inv_of_landed_pack {raw : List (Fin 2)} {cT : Control} {sT : GalilVM}
    (hM : MInv raw cT sT) (hR : ∃ (Rad : ℕ) (last : Counter), Restarted raw sT Rad last)
    (hres : FoundResidual raw cT sT) : Inv raw cT sT := inv_of_residual hM hR hres

/-! ## 2. The rounds and break exits of the comparison leaf -/

/-- **NAMED (open).**  The rounds continuation after the derived preparation
segment: `GalilCatchUpDistance.stageEntry_after_found_of_rounds` followed by
`GalilFoundLandingL.foundRouteMC_shift`, with the landing sharpened from
`InvLP` to the restart pack `Inv` (plus `SpanRep`). -/
def RoundsRoute (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ)
    (c : Control) (r : GalilVM) (cP : Control) (sP : GalilVM) : Prop :=
  ∀ (hh : ℕ) (es : List Bool) (c2 : Control) (s2 : GalilVM),
    WatchSegE P q first 2048 es cP sP c2 s2 → es.length = 2*hh+2 →
    (∃ ww : GalilScaffoldChainWatch.State, s2.chain = ChainVM.watch ww) →
    ∃ (cT : Control) (sT : GalilVM) (k : ℕ) (L : List Piece),
      StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩ ∧
      CostedRun r sT k L ∧ Inv raw cT sT ∧ SpanRep sT ∧
      position r.center < position sT.center ∧ position sT.right ≤ 2 * m - 1

/-- **Derived.**  `RoundsRoute` is `CloseoutFoundCompare.RoundsExit`. -/
theorem roundsExit_of_route {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)} {m : ℕ}
    {c cP : Control} {r sP : GalilVM}
    (h : RoundsRoute P q first raw m c r cP sP) :
    PalPeg.CloseoutFoundCompare.RoundsExit P q first raw m c r cP sP := by
  intro hh es c2 s2 hseg hlen hw
  obtain ⟨cT, sT, k, L, hst, hcr, hI, hS, hprog, hpos⟩ := h hh es c2 s2 hseg hlen hw
  obtain ⟨hM, hR, hres, -⟩ := landed_pack hI hS
  exact ⟨cT, sT, k, L, hst, hcr, hM, hR, hres, hS, hprog, hpos⟩

/-- **NAMED (open).**  The break continuation: the `hcont` of
`GalilNoShiftDischarge.foundRouteMC_noshift_d` (equivalently
`GalilInvPlus2.foundRouteMC_noshift''`), whose landing is `InvLP2` with the
`Inv` pack — `CentreRep` is derived from the latter — together with the break
landing's stage datum. -/
def BreakRoute (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ)
    (c : Control) (r : GalilVM) (cP : Control) (sP : GalilVM) : Prop :=
  ∀ (hh : ℕ) (es : List Bool) (c2 : Control) (s2 : GalilVM),
    WatchSegE P q first 2048 es cP sP c2 s2 → es.length = 2*hh+2 →
    (∃ ww : GalilScaffoldChainWatch.State, s2.chain = ChainVM.watch ww) →
    ∃ (cT : Control) (sT : GalilVM) (k : ℕ) (L : List Piece),
      StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩ ∧
      CostedRun r sT k L ∧ InvLP2 raw cT sT ∧ Inv raw cT sT ∧
      ReplayStage raw P q first cT sT ∧
      position sT.center = position r.center ∧ position r.right < position sT.right ∧
      position sT.right ≤ 2 * m - 1

/-- **Derived.**  `BreakRoute` is `CloseoutFoundCompare.BreakExit`; `CentreRep`
comes from the pack via `GalilNoShiftStage.centreRep_of_inv`. -/
theorem breakExit_of_route {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)} {m : ℕ}
    {c cP : Control} {r sP : GalilVM}
    (h : BreakRoute P q first raw m c r cP sP) :
    PalPeg.CloseoutFoundCompare.BreakExit P q first raw m c r cP sP := by
  intro hh es c2 s2 hseg hlen hw
  obtain ⟨cT, sT, k, L, hst, hcr, hIT, hI, hstg, hc, hlt, hpos⟩ := h hh es c2 s2 hseg hlen hw
  exact ⟨cT, sT, k, L, hst, hcr, hIT, PalPeg.GalilNoShiftStage.centreRep_of_inv hI, hstg,
    hc, hlt, hpos⟩

/-! ## 3. The two continuations of the in-replay leaf -/

/-- **Derived.**  A run from the replay landing to a restart pack is a
`CloseoutFoundReplay.ContinuesToRestart`. -/
theorem continuesToRestart_of_run {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    {m : ℕ} {cT cU : Control} {sT sU : GalilVM} {k' : ℕ} {L' : List Piece}
    (hst : StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k' ⟨cT, sT⟩ ⟨cU, sU⟩)
    (hcr : CostedRun sT sU k' L') (hI : Inv raw cU sU) (hS : SpanRep sU)
    (hmono : position sT.center ≤ position sU.center)
    (hpos : position sU.right ≤ 2 * m - 1) :
    PalPeg.CloseoutFoundReplay.ContinuesToRestart P q first raw m cT sT := by
  obtain ⟨hM, hR, hres, -⟩ := landed_pack hI hS
  exact ⟨cU, sU, k', L', hst, hcr, hM, hR, hres, hS, hmono, hpos⟩

/-! ## 4. The background exit -/

/-- **Derived.**  The first disjunct of `CloseoutFoundBackground.BgLanding` from
a `FoundCost` route whose landing is the restart pack. -/
theorem bgLanding_of_route {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)} {m : ℕ}
    {c cT : Control} {r sT : GalilVM}
    (hcost : PalPeg.GalilOracleMC.FoundCost P q first raw c r cT sT) (hI : Inv raw cT sT) (hS : SpanRep sT)
    (hprog : position r.center < position sT.center)
    (hpos : position sT.right ≤ 2 * m - 1) :
    PalPeg.CloseoutFoundBackground.BgLanding P q first raw m c r := by
  obtain ⟨hM, hR, hres, -⟩ := landed_pack hI hS
  exact Or.inl ⟨cT, sT, hcost, hM, hR, hres, hS, hprog, hpos⟩

/-- **Derived.**  The break disjunct of `BgLanding`, with `CentreRep` from the
pack. -/
theorem bgLanding_of_break {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)} {m k : ℕ}
    {c cT : Control} {r sT : GalilVM} {L : List Piece}
    (hst : StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩)
    (hcr : CostedRun r sT k L) (hIT : InvLP2 raw cT sT) (hI : Inv raw cT sT)
    (hstage : ReplayStage raw P q first cT sT)
    (hc : position sT.center = position r.center)
    (hlt : position r.right < position sT.right)
    (hpos : position sT.right ≤ 2 * m - 1) :
    PalPeg.CloseoutFoundBackground.BgLanding P q first raw m c r :=
  Or.inr ⟨cT, sT, k, L, hst, hcr, hIT, PalPeg.GalilNoShiftStage.centreRep_of_inv hI, hstage,
    hc, hlt, hpos⟩

/-! ## 5. `PrefixCost` is too strong as stated -/

/-- **Derived (negative).**  A costed run of at least one tick must advance the
right head: its pieces carry all `k` ticks and every piece's place lies in
`(position r0.right, position r1.right]`. -/
theorem costedRun_right_progress {r0 r1 : GalilVM} {k : ℕ} {L : List Piece}
    (h : CostedRun r0 r1 k L) (hk : 0 < k) : position r0.right < position r1.right := by
  cases hL : L with
  | nil =>
      have := h.ticks
      rw [hL] at this
      simp at this
      omega
  | cons p ps =>
      have hp : p ∈ L := by rw [hL]; exact List.mem_cons_self
      have := (h.places p hp).1
      have := (h.places p hp).2
      omega

/-- **Derived (negative).**  Hence `CloseoutFoundReplay.PrefixCost`, quantified
over *every* sound run, entails that no sound run of positive length parks the
right head.  A replay stretch does exactly that, so this contract cannot be
discharged in the shape it is stated; the pointwise `PrefixCostAt` below is what
the leaf actually needs. -/
theorem prefixCost_forces_right_progress {P : Shared} {q : ℕ} {first : Fin 9}
    {raw : List (Fin 2)} (h : PalPeg.CloseoutFoundReplay.PrefixCost P q first raw)
    {c cT : Control} {r sT : GalilVM} {k : ℕ} (hk : 0 < k)
    (hst : StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩) :
    position r.right < position sT.right := by
  obtain ⟨L, hcr⟩ := h c r cT sT k hst
  exact costedRun_right_progress hcr hk

/-- **NAMED (open), pointwise.**  The cost of *this* leaf's prefix run only. -/
def PrefixCostAt (r sT : GalilVM) (k : ℕ) : Prop := ∃ L : List Piece, CostedRun r sT k L

/-- **Derived.**  `CloseoutFoundReplay.foundExit_of_continues` with the
pointwise cost in place of the universally quantified `PrefixCost`. -/
theorem foundExit_of_continues' {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    {m k : ℕ} {c cT : Control} {r sT : GalilVM}
    (hpc : PrefixCostAt r sT k)
    (hst : StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩)
    (hprog : position r.center < position sT.center)
    (hcont : PalPeg.CloseoutFoundReplay.ContinuesToRestart P q first raw m cT sT) :
    FoundExit P q first raw m c r := by
  obtain ⟨L, hcr⟩ := hpc
  obtain ⟨cU, sU, k', L', hst', hcr', hM, hR, hres, hSpan, hmono, hpos⟩ := hcont
  refine FoundExit.landed cU sU (k + k') (L ++ L') (stepsAll_trans hst hst')
    (costedRun_trans hcr hcr') hM hR hres hSpan ?_ hpos
  omega

/-- **Derived.**  The in-replay leaf with the pointwise cost and the two
continuations. -/
theorem foundExit_of_leaf' {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    {m k R : ℕ} {c cT : Control} {r sT : GalilVM}
    (hpc : PrefixCostAt r sT k)
    (hch : PalPeg.CloseoutFoundReplay.ChainContinuation P q first raw m)
    (hrc : PalPeg.CloseoutFoundReplay.RestartContinuation P q first raw m)
    (hst : StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩)
    (hL : PalPeg.GalilOracleDischarge.ReplayLanding raw cT sT R) (hSpan : SpanRep sT)
    (hprog : position r.center < position sT.center)
    (hpos : position sT.right ≤ 2 * m - 1)
    (hor : PalPeg.GalilReplaySpan.ChainEnd raw P q first 2048 (position sT.right + R) cT sT 0 R ∨
      PalPeg.GalilReplaySpan.BrokeAndRestarted raw P q first 2048 cT sT) :
    FoundExit P q first raw m c r := by
  rcases hor with h | h
  · exact foundExit_of_continues' hpc hst hprog (hch cT sT R hL hSpan hpos h)
  · exact foundExit_of_continues' hpc hst hprog (hrc cT sT R hL hSpan hpos h)

end PalPeg.CloseoutFoundExits

#print axioms PalPeg.CloseoutFoundExits.landed_pack
#print axioms PalPeg.CloseoutFoundExits.inv_of_landed_pack
#print axioms PalPeg.CloseoutFoundExits.roundsExit_of_route
#print axioms PalPeg.CloseoutFoundExits.breakExit_of_route
#print axioms PalPeg.CloseoutFoundExits.continuesToRestart_of_run
#print axioms PalPeg.CloseoutFoundExits.bgLanding_of_route
#print axioms PalPeg.CloseoutFoundExits.bgLanding_of_break
#print axioms PalPeg.CloseoutFoundExits.costedRun_right_progress
#print axioms PalPeg.CloseoutFoundExits.prefixCost_forces_right_progress
#print axioms PalPeg.CloseoutFoundExits.foundExit_of_continues'
#print axioms PalPeg.CloseoutFoundExits.foundExit_of_leaf'
