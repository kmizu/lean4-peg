import PalPeg.CloseoutLenNonneg
import PalPeg.CloseoutPackRun17

/-!
# `H_marksEntry'` is not needed: the marks invariant travels on its own

`CloseoutPackRun17.marks_steps` (:406) carries `CPack`, `WPack` and `MarksInv'`
along a run **with no `H_marksEntry'`** — it feeds `marksInv'_tick` with
`marksEntry'_of_layout (chooseLayout_of_wpack h4 hW hm hs)` instead, i.e. the
layout read off `WPack`.

Its three side inputs are:

* `h4 : first ≠ 4` — a side condition on the choice of `first`;
* `hfl : … → 0 ≤ value z.vm.length` — proved in `CloseoutLenNonneg`
  (`lenNonneg_of_entryCounters`: `SpanRep` plus `RadiusRep` give
  `value length = 2·Rad + 1`);
* `hwin : … → z.ctl.mode = Mode.copy → WindowInOrigin z.vm` — a single-state
  property (`(stream s.fpp.walker).length ≤ position s.right`), so it belongs in
  a run-carried bundle exactly like `ChainPack`'s fields.

This file packages the three so that the `H_marksEntry'`-free route is usable
from the run pack.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutMarksFree

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead
open PalPeg.GalilRunSkeleton PalPeg.GalilFrontMono
open PalPeg.CloseoutPackRun16 PalPeg.CloseoutPackRun17 PalPeg.CloseoutLenNonneg
open PalPeg.GalilGlueBLeaves PalPeg.GalilCentreLive

section
variable (onLetter leftFirst : GalilVM → Prop) (centre : GalilVM → Fin 3)
  (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9) (delay : ℕ)

/-- **(NAMED) the marks-side run bundle.**  `WindowInOrigin` at the run's `copy`
states and `EntryCounters` at its `scan` states — the two inputs
`marksInv'_of_run'` still needs beyond `first ≠ 4`. -/
def MarksRun (raw : List (Fin 2)) (x : State GalilVM) : Prop :=
  (∀ (m : ℕ) (z : State GalilVM),
    Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay m x z →
    z.ctl.mode = Mode.copy → WindowInOrigin z.vm) ∧
  (∀ (m : ℕ) (z : State GalilVM),
    Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay m x z →
    z.ctl.mode = Mode.scan → EntryCounters raw z.vm)

/-- **`MarksInv'` along a run from `MarksRun`, with no `H_marksEntry'`.**  The
`hfl` input is discharged by `lenNonneg_of_entryCounters`. -/
theorem marksInv'_of_marksRun {raw : List (Fin 2)} (h4 : first ≠ 4)
    {n : ℕ} {x y : State GalilVM}
    (h : Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay n x y)
    (hM : MarksRun onLetter leftFirst centre place entry q first delay raw x)
    (hP : CPack q x.ctl x.vm) (hx : x.ctl.mode = Mode.scan) :
    MarksInv' first y.ctl y.vm :=
  marksInv'_of_run' onLetter leftFirst centre place entry q first delay h4 h
    (fun m z hz hm => lenNonneg_of_entryCounters (hM.2 m z hz hm))
    hM.1 hP hx

#print axioms marksInv'_of_marksRun

end

end PalPeg.CloseoutMarksFree
