import PalPeg.CloseoutFrontExtra
import PalPeg.CloseoutChainPack
import PalPeg.CloseoutPackRefute
import PalPeg.CloseoutPackW

/-!
# `ScanBudget` is supplied by the run, exactly like `Extra7` was

`CloseoutPackRefute` refuted `hpack` and diagnosed the cause: `ChainPack` is a
bundle of **run** facts written as a one-state predicate, premised on the
three-field one-state invariant `ChainPosInv2`.  Its worst field is

```
scanBound : c.mode = Mode.scan → ∃ m, 1 ≤ m ∧ m < w.length ∧ position s.right ≤ 2 * m - 1
```

which came from folding the earlier separate leaf
`CloseoutFinalPack.hbudget` (`ChainPack.ScanBudget`) into the bundle.

That leaf, however, **already has a producer** — the very mechanism that removed
`hee` / `het` for `Extra7` in `final27`.  `CloseoutFrontExtra`:

* `front s = position s.right` at a non-replaying state (`front_eq_position`);
* `front_stepsAll_mono`: the potential is monotone along a run;
* hence `position_le_of_front_run`: **the cycle's exit bound travels backwards**,
  giving `position x.vm.right ≤ 2 * m - 1` at *every* state of the run.

`extra7_of_front_run_pack` already uses exactly this to build `Extra7`; the only
extra thing `ScanBudget` wants is to keep `m` and its two side conditions, and
`m < w.length` is what the cycle carries for every non-final checkpoint.

So `scanBudget_of_front_run` below is the missing producer, and the two
consumers of the bound — `canRight s.right` and `canRight (right s.right)` —
come out with it (`avail2_of_front_run`).  What is *not* repaired here is
`hpack`'s premise: `ChainPosInv2` cannot yield `repR`, `centreCanR`, `saneR`, …
either, so the bundle has to be read off the run-carried
`CloseoutPackW.BigPack2MG7W''` instead.  This file closes the one field that was
outright contradictory.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutBudgetFree

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
open PalPeg.GalilScaffoldChainInputSupply PegSeparation
open PalPeg.GalilFrontMono PalPeg.GalilRunTrace PalPeg.GalilRunSkeleton
open PalPeg.CloseoutCanRightBound PalPeg.CloseoutFrontExtra
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.CloseoutPackW (BigPack2MG7W'')

/-- **`ScanBudget`'s content at every state of a run.**  `position_le_of_front_run`
carries the cycle's exit bound backwards; `m` and its side conditions ride
along. -/
theorem scanBudget_of_front_run {onLetter leftFirst : GalilVM → Prop}
    {centre : GalilVM → Fin 3} {place : GalilVM → GalilScaffoldPlace.Place} {entry q : ℕ}
    {first : Fin 9} {delay : ℕ} {Q : State GalilVM → Prop} {n : ℕ} {x y : State GalilVM}
    {w : List (Fin 2)} {m : ℕ}
    (h : StepsAll (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay Q
      n x y)
    (hg : ∀ (j : ℕ) (z : State GalilVM),
      Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay j x z →
      CentreLive z.ctl z.vm)
    (hPx : FrontPack x.ctl x.vm) (hPy : FrontPack y.ctl y.vm)
    (hrx : x.ctl.replaying = false) (hry : y.ctl.replaying = false)
    (hm1 : 1 ≤ m) (hmlt : m < w.length)
    (hy : position y.vm.right ≤ 2 * m - 1) :
    ∃ m' : ℕ, 1 ≤ m' ∧ m' < w.length ∧ position x.vm.right ≤ 2 * m' - 1 :=
  ⟨m, hm1, hmlt, position_le_of_front_run h hg hPx hPy hrx hry hy⟩

/-- **Both `canRight` facts the budget is used for.**  `canR` is one step of
room, `canRNext` two; the latter is where the strict `m < w.length` is spent. -/
theorem avail2_of_front_run {onLetter leftFirst : GalilVM → Prop}
    {centre : GalilVM → Fin 3} {place : GalilVM → GalilScaffoldPlace.Place} {entry q : ℕ}
    {first : Fin 9} {delay : ℕ} {Q : State GalilVM → Prop} {n : ℕ} {x y : State GalilVM}
    {w : List (Fin 2)} {m : ℕ}
    (h : StepsAll (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay Q
      n x y)
    (hg : ∀ (j : ℕ) (z : State GalilVM),
      Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay j x z →
      CentreLive z.ctl z.vm)
    (hPx : FrontPack x.ctl x.vm) (hPy : FrontPack y.ctl y.vm)
    (hrx : x.ctl.replaying = false) (hry : y.ctl.replaying = false)
    (hpack : PalPeg.CloseoutPackRun10.LPackM w x.ctl x.vm)
    (hmx : x.ctl.mode = Mode.scan)
    (hm1 : 1 ≤ m) (hmlt : m < w.length)
    (hy : position y.vm.right ≤ 2 * m - 1) :
    canRight x.vm.right ∧ canRight (right x.vm.right) := by
  obtain ⟨hrep, hpres⟩ := rrep_of_lpackM hpack hmx hrx
  have hpos := position_le_of_front_run h hg hPx hPy hrx hry hy
  have hcan : canRight x.vm.right :=
    canRight_of_position_bound hrep hpres hm1 (by omega) hpos
  have hlv : 0 < x.vm.right.head.left.length :=
    (represented_position x.vm.right.head w hrep hpres).1
  refine ⟨hcan, canRight_next_of_bound (right_word _ w hrep hcan)
    (PalPeg.CloseoutScanMargin4.right_present hrep hpres hcan) hcan hlv hm1 hmlt hpos⟩

/-! ## The reformulated hypothesis

With the budget produced from the run, the remaining defect in
`hpack : ∀ w c s, ChainPosInv2 w c s → ChainPack q first w c s` is its
**premise**.  `ChainPosInv2` has three fields; `ChainPack` also asserts
`repR` (the right head represents `w`), `centreCanR` (the centre head can move),
`saneR`, `centreSane`, `scanCentre`, `lenNonneg`, `cpack`, `wpack`, `marks` …
none of which a three-field chain-position invariant can give.

Every one of them *is* in the run-carried pack `CloseoutPackW.BigPack2MG7W''`
(`IPackMW` = `LPackM` + `LPackM2`, plus `AuxPack`, `CentreLive`, `MarksInv'`,
`Extra7`):

| `ChainPack` field | source in the run pack |
|---|---|
| `repR` | `LPackM.scanGeom` / `LPackM2.scanGeomR` → `ScanInvariant.rightRep` / `rightPresent` |
| `marks` | `BigPack2MG7W''.marks` |
| `scanBound` | this file |
| `canR` at scan | `Extra7.scanAvail` |
| `Canonical s.length`, `CentreLedger`, `centreSane`, `centreCanR` | `CentreLive` |
| `replayPay` | `ChainPosInv2.payload` |
| `walkerPin`, `walkerOrigin` | **model defect (e)** — still open |

`ChainSideW` names the repaired shape.  It is *not* proved here; what is
established is that its premise is the run-carried pack rather than a one-state
invariant, so it is no longer refutable by `chainPosInv2_of_idle`. -/
def ChainSideW (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9) (w : List (Fin 2)) : Prop :=
  ∀ x : State GalilVM,
    BigPack2MG7W'' centre place entry q first w x →
    PalPeg.CloseoutPackRun41.ChainPosInv2 w x.ctl x.vm →
    (∃ m : ℕ, 1 ≤ m ∧ m < w.length ∧ position x.vm.right ≤ 2 * m - 1) →
    PalPeg.CloseoutChainPack.ChainPack q first w x.ctl x.vm

/-- **The old hypothesis implies the new one.**  So nothing is lost by moving to
`ChainSideW`; what is gained is that the premise is no longer free at an idle
chain. -/
theorem chainSideW_of_hpack {centre : GalilVM → Fin 3}
    {place : GalilVM → GalilScaffoldPlace.Place} {entry q : ℕ} {first : Fin 9}
    {w : List (Fin 2)}
    (hp : ∀ (c : Control) (s : GalilVM),
      PalPeg.CloseoutPackRun41.ChainPosInv2 w c s →
      PalPeg.CloseoutChainPack.ChainPack q first w c s) :
    ChainSideW centre place entry q first w :=
  fun x _ hx _ => hp x.ctl x.vm hx

#print axioms scanBudget_of_front_run
#print axioms avail2_of_front_run
#print axioms chainSideW_of_hpack

end PalPeg.CloseoutBudgetFree
