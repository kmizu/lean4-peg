import PalPeg.CloseoutOracle8
import PalPeg.CloseoutInvScanS

/-!
# `hor` is `H_oracle` plus one landing lift — and the earlier claim was wrong

## Correction

An earlier ledger entry recorded that `hor` (`CycleOracleMC3`) "has producers
via `h_oracle_of_leaves''`".  **That is wrong.**  Reading the definitions:

| name | origin | landing invariant |
|---|---|---|
| `GalilTraceCost.CycleOracleMC` (what `H_oracle` unfolds to) | `InvL raw c r` | `InvL raw cT sT` |
| `GalilInvPlus3.CycleOracleMC3` (what `hor` is) | `InvLPS P q first raw c r` | `InvLPS P q first raw cT sT` |

and `ReachAtC` / `ReachAtC3` differ in exactly the same one place
(`GalilTraceCost:115` vs `GalilInvPlus3:194`).  Every `h_oracle_of_leaves*`
in the tree — `GalilOracleMC2`, `GalilOracleLeaves2`, `GalilOracleMC3`,
`GalilSegmentConstructB`, `GalilReadyFuelUses`, `GalilLeafReport`,
`CloseoutOracle5`–`CloseoutOracle8` — concludes
`GalilFinalAssembly.H_oracle`, i.e. the `CycleOracleMC` version.  So `hor`
has **no** producer in the tree, and the two are not interchangeable: the
`MC3` version must *deliver* the stronger landing invariant.

## What the bridge costs, exactly

`cycleOracleMC3_of_MC` below is the bridge, with the gap as an explicit
hypothesis rather than a claim: an `InvL` landing must be liftable to `InvLPS`.
The origin costs nothing (`InvLPS → InvL` by `.1.1.1.1`, since
`InvLPS = InvLPC ∧ ReplayStage`, `InvLPC = InvLP2 ∧ CentreRep`,
`InvLP2 = InvLP ∧ CopyPack`, `InvLP = InvL ∧ EntryCounters`).

The lift is **not** free: `GalilInvPlus3.invLPS_of_landed` produces it from
`Inv raw cT sT` (not merely `InvL`, whose `InvS` half is `Inv ∨ InvScan`),
`SpanRep sT`, and `CopyPack` at the origin.  So the honest statement of `hor`'s
residue is

```
hor  =  H_oracle (eleven leaves, CloseoutOracle8.h_oracle_of_leaves7)
      +  the InvLPS landing lift (Inv + SpanRep at every reachable landing)
```

which is the same `InvLPS`-lifting work `CloseoutStageBoot` / `CloseoutStageCheck`
did for the boot state.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutOracleBridge

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton PalPeg.GalilOracleLocal PalPeg.GalilTraceCost
open PalPeg.GalilInvPlus PalPeg.GalilInvPlus2 PalPeg.GalilInvPlus3
open PalPeg.GalilLexMeasure

/-- **`InvLPS` forgets to `InvL` at no cost.**  Four projections. -/
theorem invL_of_invLPS {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    {c : Control} {r : GalilVM} (h : InvLPS P q first raw c r) : InvL raw c r :=
  h.1.1.1.1

/-- **`ReachAtC` lifts to `ReachAtC3` given the landing lift.** -/
theorem reachAtC3_of_C {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)} {m : ℕ}
    {c : Control} {r : GalilVM}
    (hlift : ∀ (cT : Control) (sT : GalilVM), InvL raw cT sT → InvLPS P q first raw cT sT)
    (h : ReachAtC P q first raw m c r) : ReachAtC3 P q first raw m c r := by
  obtain ⟨y, k, L, hst, hcr, hrp, hfr, hcont⟩ := h
  refine ⟨y, k, L, hst, hcr, hrp, hfr, fun hlt => ?_⟩
  obtain ⟨c', r', k', L', hst', hcr', hI, hp⟩ := hcont hlt
  exact ⟨c', r', k', L', hst', hcr', hlift c' r' hI, hp⟩

/-- **`CycleOutMC'` lifts to `CycleOutMC3` given the landing lift.**  The
measure is already the lexicographic one in `MC'`; only the invariant moves. -/
theorem cycleOutMC3_of_MC' {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)} {m : ℕ}
    {c : Control} {r : GalilVM}
    (hlift : ∀ (cT : Control) (sT : GalilVM), InvL raw cT sT → InvLPS P q first raw cT sT)
    (h : CycleOutMC' P q first raw m c r) : CycleOutMC3 P q first raw m c r := by
  rcases h with h | ⟨cT, sT, k, L, hst, hcr, hI, hmu, hp⟩
  · exact Or.inl (reachAtC3_of_C hlift h)
  · exact Or.inr ⟨cT, sT, k, L, hst, hcr, hlift cT sT hI, hmu, hp⟩

/-- **`CycleOutMC` lifts to `CycleOutMC3`.**  Two differences, not one:
`GalilLexMeasure.cycleOutMC'_of_MC` turns the centre-progress exit into the
`mu`-progress exit (via `mu_lt_of_centre`), and the lift moves the invariant. -/
theorem cycleOutMC3_of_MC {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)} {m : ℕ}
    {c : Control} {r : GalilVM}
    (hlift : ∀ (cT : Control) (sT : GalilVM), InvL raw cT sT → InvLPS P q first raw cT sT)
    (hI : InvL raw c r)
    (h : CycleOutMC P q first raw m c r) : CycleOutMC3 P q first raw m c r :=
  cycleOutMC3_of_MC' hlift (cycleOutMC'_of_MC hI h)

/-- **The bridge.**  `hor` from `H_oracle`'s oracle plus the landing lift.  The
origin side is free; the landing side is the whole gap. -/
theorem cycleOracleMC3_of_MC {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    (hlift : ∀ (cT : Control) (sT : GalilVM), InvL raw cT sT → InvLPS P q first raw cT sT)
    (hMC : CycleOracleMC P q first raw) : CycleOracleMC3 P q first raw := by
  intro m c r hm1 hmle hI hp
  have hIL := invL_of_invLPS hI
  exact cycleOutMC3_of_MC hlift hIL (hMC m c r hm1 hmle hIL hp)

/-! ## The tight bridge: `CycleOracleMC2C` differs from `CycleOracleMC3` only in
`ReplayStage`

`GalilOracleMC2.CycleOutMC2C` (`:75`) and `GalilInvPlus3.CycleOutMC3` (`:206`)
are the *same* statement — same `mu` progress, same shape — except that the
landing carries `InvLPC raw cT sT` in one and
`InvLPS P q first raw cT sT = InvLPC raw cT sT ∧ ReplayStage raw P q first cT sT`
in the other.  So the whole gap between `H_oracle2`
(`GalilFinalAssembly4:248`, which `h_oracle2_of_leaves` proves) and `hor` is
**`ReplayStage` at the landings**, and `CloseoutFoundRoutes.replayStage_of_inv`
supplies it from `Inv`.

`GalilOracleMC2.FallbackRouteMC2`'s `landed` and `replaying` constructors
(`:289` / `:295`) already carry `hI : Inv raw cT sT` as a field, so the
fallback route's landings satisfy the lift outright.
-/

/-- **`ReachAtC2` lifts to `ReachAtC3` given the `ReplayStage` lift.** -/
theorem reachAtC3_of_C2 {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)} {m : ℕ}
    {c : Control} {r : GalilVM}
    (hlift : ∀ (cT : Control) (sT : GalilVM), InvLPC raw cT sT →
      PalPeg.GalilFoundStage.ReplayStage raw P q first cT sT)
    (h : PalPeg.GalilOracleMC2.ReachAtC2 P q first raw m c r) :
    ReachAtC3 P q first raw m c r := by
  obtain ⟨y, k, L, hst, hcr, hrp, hfr, hcont⟩ := h
  refine ⟨y, k, L, hst, hcr, hrp, hfr, fun hlt => ?_⟩
  obtain ⟨c', r', k', L', hst', hcr', hI, hp⟩ := hcont hlt
  exact ⟨c', r', k', L', hst', hcr', ⟨hI, hlift c' r' hI⟩, hp⟩

/-- **`CycleOutMC2C` lifts to `CycleOutMC3`.**  Only `ReplayStage` moves. -/
theorem cycleOutMC3_of_MC2C {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)} {m : ℕ}
    {c : Control} {r : GalilVM}
    (hlift : ∀ (cT : Control) (sT : GalilVM), InvLPC raw cT sT →
      PalPeg.GalilFoundStage.ReplayStage raw P q first cT sT)
    (h : PalPeg.GalilOracleMC2.CycleOutMC2C P q first raw m c r) :
    CycleOutMC3 P q first raw m c r := by
  rcases h with h | ⟨cT, sT, k, L, hst, hcr, hI, hmu, hp⟩
  · exact Or.inl (reachAtC3_of_C2 hlift h)
  · exact Or.inr ⟨cT, sT, k, L, hst, hcr, ⟨hI, hlift cT sT hI⟩, hmu, hp⟩

/-- **The tight bridge.**  `hor` from `H_oracle2`'s oracle plus the
`ReplayStage` lift.  The origin is free (`InvLPS → InvLPC` is `.1`). -/
theorem cycleOracleMC3_of_MC2C {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    (hlift : ∀ (cT : Control) (sT : GalilVM), InvLPC raw cT sT →
      PalPeg.GalilFoundStage.ReplayStage raw P q first cT sT)
    (hMC : PalPeg.GalilOracleMC2.CycleOracleMC2C P q first raw) :
    CycleOracleMC3 P q first raw := by
  intro m c r hm1 hmle hI hp
  exact cycleOutMC3_of_MC2C hlift (hMC m c r hm1 hmle hI.1 hp)

section
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **`hor` from `H_oracle2` and the `ReplayStage` lift.**  This is the tight
route: `h_oracle2_of_leaves` proves `H_oracle2`, and the only thing left is
`ReplayStage` at the landings. -/
theorem hor_of_H_oracle2
    (hlift : ∀ (w : List (Fin 2)) (cT : Control) (sT : GalilVM), InvLPC w cT sT →
      PalPeg.GalilFoundStage.ReplayStage w (PofC centre place entry w) q first cT sT)
    (hOr : PalPeg.GalilFinalAssembly4.H_oracle2 centre place entry q first) :
    ∀ w : List (Fin 2), 0 < w.length →
      CycleOracleMC3 (PofC centre place entry w) q first w :=
  fun w hw => cycleOracleMC3_of_MC2C (hlift w) (hOr w hw)

/-- **The tightest form: `hor` from `H_oracle2` and the scan-branch stage
datum.**  `CloseoutInvScanS.InvSS` is `InvS` with `ReplayStage` bundled into its
scan branch, and `replayStage_of_invSS` extracts it.  So the whole remaining gap
between `H_oracle2` and `hor` is exactly the `hsc` reformulation: *the landing's
scan branch carries its stage datum*.  Nothing else. -/
theorem hor_of_H_oracle2_invSS
    (hSS : ∀ (w : List (Fin 2)) (cT : Control) (sT : GalilVM), InvLPC w cT sT →
      PalPeg.CloseoutInvScanS.InvSS centre place entry q first w cT sT)
    (hOr : PalPeg.GalilFinalAssembly4.H_oracle2 centre place entry q first) :
    ∀ w : List (Fin 2), 0 < w.length →
      CycleOracleMC3 (PofC centre place entry w) q first w :=
  hor_of_H_oracle2 centre place entry q first
    (fun w cT sT hI =>
      PalPeg.CloseoutInvScanS.replayStage_of_invSS centre place entry q first (hSS w cT sT hI))
    hOr

/-- **`hor` from `H_oracle` and the lift, at the concrete frame.** -/
theorem hor_of_H_oracle
    (hlift : ∀ (w : List (Fin 2)) (cT : Control) (sT : GalilVM), InvL w cT sT →
      InvLPS (PofC centre place entry w) q first w cT sT)
    (hOr : PalPeg.GalilFinalAssembly.H_oracle centre place entry q first) :
    ∀ w : List (Fin 2), 0 < w.length →
      CycleOracleMC3 (PofC centre place entry w) q first w :=
  fun w hw => cycleOracleMC3_of_MC (hlift w) (hOr w hw)

end

#print axioms invL_of_invLPS
#print axioms reachAtC3_of_C
#print axioms cycleOutMC3_of_MC'
#print axioms cycleOutMC3_of_MC
#print axioms cycleOracleMC3_of_MC
#print axioms reachAtC3_of_C2
#print axioms cycleOutMC3_of_MC2C
#print axioms cycleOracleMC3_of_MC2C
#print axioms hor_of_H_oracle2
#print axioms hor_of_H_oracle2_invSS
#print axioms hor_of_H_oracle

end PalPeg.CloseoutOracleBridge
