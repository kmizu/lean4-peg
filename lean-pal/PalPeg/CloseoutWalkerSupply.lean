import PalPeg.CloseoutReplayCanRight
import PalPeg.CloseoutPlaceBound

/-!
# Supplying `walkerInOrigin_of_run`'s two inputs

`CloseoutPackRun28.walkerInOrigin_of_run` (:526) — the producer of
`WalkerInOrigin`, and through it of `hme` — takes two open inputs:

* `hcan` — at every reachable state with `replaying = true`, `canRight right`;
* `hplace` — `∀ u, (stream (place u)).length ≤ position u.right`.

`hcan` is a theorem (`CloseoutReplayCanRight.hcan_of_cpack`): `CPack.front` *is*
a `FrontPack`, whose `replayPos` and `frontier` plus
`GalilFrontier.consume_not_replaying_false` give it.

`hplace` as stated (`∀ u`) is **false** (`CloseoutPlaceBound.hplace_false`): the
left side reads the centre head and the right side the right head, and nothing
couples them.  Its honest form is `hplace_of_order`, guarded by
`GalilTrailOrder.Order`.

So what remains under `hme` is the quantifier mismatch: `wpack_of_fair` runs over
`FairSteps` while `marksEntry'_of_run` runs over `Steps`, because
`windowInOrigin_tick` (`CloseoutPackRun25:80`) needs `Fair`.  `Fair` uniqueness
itself is already proved (`GalilTickFair.tick_fair_unique`, no `sorry`).

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false

namespace PalPeg.CloseoutWalkerSupply

open PalPeg.CloseoutReplayCanRight
open PalPeg.CloseoutPlaceBound
open PalPeg.GalilCentreLive
open PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop
open GalilScaffoldController

variable (onLetter leftFirst : GalilVM → Prop) (centre : GalilVM → Fin 3)
  (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9) (delay : ℕ)

/-- **`hcan` in the exact shape `walkerInOrigin_of_run` wants**, from the
`CPack` that `CloseoutPackRun25.wpack_of_fair` already carries. -/
theorem hcan_for_walker {x : State GalilVM}
    (hfl : ∀ (m : ℕ) (y : State GalilVM),
      Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay m x y →
      y.ctl.mode = Mode.scan → 0 ≤ GalilScaffoldCounter.value y.vm.length)
    (hP : CPack q x.ctl x.vm) (m : ℕ) (z : State GalilVM)
    (hz : PalPeg.CloseoutPackRun25.FairSteps
      (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) entry delay m x z)
    (hr : z.ctl.replaying = true) :
    GalilScaffoldChainVerifier.canRight z.vm.right :=
  hcan_of_cpack onLetter leftFirst centre place entry q first delay hfl hP m z hz hr

#print axioms hcan_for_walker

end PalPeg.CloseoutWalkerSupply
