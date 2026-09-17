import PalPeg.GalilEndOfInput
import PalPeg.GalilTraceCost

/-!
# `canRight` from the cycle's own position bound

`CloseoutClockFront` derives `canRight` from the *length* of the run, which needs
an upper bound on the tick count that `PackRunRMG2` (`CloseoutPackRun36:588`)
does not carry — its run index is `∀ (j : ℕ)`.

The closeout already has a better handle.  `CycleOutIMG2` (`CloseoutPackRun36:247`)
and `CycleOracleIMG2` (:256) both keep `position r.right ≤ 2 * m - 1` at the
entry *and* at the exit of a cycle, with `1 ≤ m` and `m ≤ w.length`.  Since the
input is exhausted only at `position right = 2 * w.length`
(`GalilEndOfInput.not_canRight_iff`), that bound already says the head can move:

```
position right ≤ 2 * m - 1 ≤ 2 * w.length - 1 < 2 * w.length.
```

And `CostedRun.right_mono` (`GalilTraceCost:80`) says the right head never goes
back, so the bound at the exit bounds every intermediate state of the same run.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false

namespace PalPeg.CloseoutCanRightBound

open PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilTraceCost
open GalilScaffoldChainVerifier (canRight)

/-- **The position bound gives `canRight`.**  `2 * m - 1 < 2 * w.length` for
`1 ≤ m ≤ w.length`, and the head stops only at `2 * w.length`. -/
theorem canRight_of_position_bound {p : GalilScaffoldInputHead.PlaceHead}
    {w : List (Fin 2)} {m : ℕ}
    (hrep : GalilScaffoldInputTrace.Represents p.head w)
    (hpres : p.head.focus ≠ none)
    (hm1 : 1 ≤ m) (hmle : m ≤ w.length) (hpos : position p ≤ 2 * m - 1) :
    canRight p := by
  by_contra hc
  have hend : position p = 2 * w.length := (GalilEndOfInput.not_canRight_iff p w hrep hpres).1 hc
  omega

/-- **The same along a costed run.**  `CostedRun.right_mono` carries the exit
bound back to the source, so every state of the run inherits it. -/
theorem canRight_of_costedRun {r0 r1 : GalilVM} {k : ℕ} {L : List Piece}
    {w : List (Fin 2)} {m : ℕ}
    (hcr : CostedRun r0 r1 k L)
    (hrep : GalilScaffoldInputTrace.Represents r0.right.head w)
    (hpres : r0.right.head.focus ≠ none)
    (hm1 : 1 ≤ m) (hmle : m ≤ w.length) (hexit : position r1.right ≤ 2 * m - 1) :
    canRight r0.right :=
  canRight_of_position_bound hrep hpres hm1 hmle (le_trans hcr.right_mono hexit)

/-- **`Extra7` at a bounded entry.**  The re-cut of `H_extraEntry7`
(`CloseoutPackRun46:87`): instead of quantifying over *every* `InvLPC` state, ask
only at states the cycle oracle actually visits, which carry
`position r.right ≤ 2 * m - 1` with `1 ≤ m ≤ w.length`.  There the head is
movable, so `Extra7` holds outright. -/
theorem extra7_of_bound {c : GalilScaffoldController.Control} {r : GalilVM}
    {w : List (Fin 2)} {m : ℕ}
    (hrep : GalilScaffoldInputTrace.Represents r.right.head w)
    (hpres : r.right.head.focus ≠ none)
    (hm1 : 1 ≤ m) (hmle : m ≤ w.length) (hpos : position r.right ≤ 2 * m - 1) :
    c.mode = GalilScaffoldController.Mode.scan → c.replaying = false →
      canRight r.right :=
  fun _ _ => canRight_of_position_bound hrep hpres hm1 hmle hpos

/-- **`canRNext` from the same bound.**  `MatchRest.canRNext`
(`CloseoutPackRun49:414`) asks that the head can still move *after* one more
step.  One comparison advances the head by exactly one
(`right_position`), so the bound `position right ≤ 2 * m - 1` with `m < w.length`
leaves `position (right right) ≤ 2 * m ≤ 2 * w.length - 2 < 2 * w.length`. -/
theorem canRight_next_of_bound {p : GalilScaffoldInputHead.PlaceHead}
    {w : List (Fin 2)} {m : ℕ}
    (hrep : GalilScaffoldInputTrace.Represents (GalilScaffoldChainVerifier.right p).head w)
    (hpres : (GalilScaffoldChainVerifier.right p).head.focus ≠ none)
    (hcan : canRight p) (hlv : 0 < p.head.left.length)
    (hm1 : 1 ≤ m) (hmlt : m < w.length) (hpos : position p ≤ 2 * m - 1) :
    canRight (GalilScaffoldChainVerifier.right p) := by
  by_contra hc
  have hend : position (GalilScaffoldChainVerifier.right p) = 2 * w.length :=
    (GalilEndOfInput.not_canRight_iff _ w hrep hpres).1 hc
  have hstep : position (GalilScaffoldChainVerifier.right p) = position p + 1 :=
    right_position p hcan hlv
  omega

#print axioms canRight_next_of_bound
#print axioms extra7_of_bound
#print axioms canRight_of_position_bound
#print axioms canRight_of_costedRun

end PalPeg.CloseoutCanRightBound
