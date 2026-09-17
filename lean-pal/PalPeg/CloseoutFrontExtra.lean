import PalPeg.CloseoutCanRightBound
import PalPeg.GalilFrontMono
import PalPeg.CloseoutPackRun46
import PalPeg.CloseoutLPack

/-!
# `Extra7` along a run, from the frontier potential

`CloseoutPackRun46`'s run pack asks for `Extra7` at every state of an
`InvLPC`-rooted run (`hprefix`, `:229`), i.e. `canRight` at every scan /
non-replaying state.  `CloseoutCanRightBound.extra7_of_bound` gives exactly that
from a *position* bound — but `PackRunRMG2` carries no position bound, which is
why `hee` and `het` were left as hypotheses.

The bound travels anyway, through the frontier potential rather than the
position.  `GalilRunTrace.front s = position s.right + value s.replay` is
monotone along any `CentreLive` run (`GalilFrontMono.front_stepsAll_mono`), and
`FrontPack.rest : ReplayRest c s` says a non-replaying state has
`s.replay = reset`.  So at a non-replaying state `front s = position s.right`
exactly, and

```
position x.right = front x ≤ front y = position y.right ≤ 2*m-1
```

whenever `x` and `y` are both non-replaying and `y` carries the cycle's own exit
bound.  The right head's own monotonicity — which would need the full 34-case
`Tick` analysis — is never needed.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false

namespace PalPeg.CloseoutFrontExtra

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
open PalPeg.GalilScaffoldChainInputSupply PegSeparation
open PalPeg.GalilFrontMono PalPeg.GalilRunTrace PalPeg.GalilRunSkeleton
open PalPeg.CloseoutCanRightBound
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier

/-- **At a non-replaying state the potential *is* the position.**  `FrontPack`'s
`rest` field is `ReplayRest`, which sends `c.replaying = false` to
`s.replay = reset`, and `value reset = 0`. -/
theorem front_eq_position {c : Control} {s : GalilVM} (hP : FrontPack c s)
    (hr : c.replaying = false) : front s = (position s.right : ℤ) := by
  have : s.replay = GalilScaffoldCounter.reset := hP.rest (Or.inl hr)
  unfold front
  rw [this]
  simp [GalilScaffoldCounter.reset, GalilScaffoldCounter.value]

/-- **The exit bound travels backwards along the run.**  No property of the right
head is used beyond `front`'s monotonicity. -/
theorem position_le_of_front_run {onLetter leftFirst : GalilVM → Prop}
    {centre : GalilVM → Fin 3} {place : GalilVM → GalilScaffoldPlace.Place} {entry q : ℕ}
    {first : Fin 9} {delay : ℕ} {Q : State GalilVM → Prop} {n : ℕ} {x y : State GalilVM}
    (h : StepsAll (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay Q
      n x y)
    (hg : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay m x z →
      CentreLive z.ctl z.vm)
    (hPx : FrontPack x.ctl x.vm) (hPy : FrontPack y.ctl y.vm)
    (hrx : x.ctl.replaying = false) (hry : y.ctl.replaying = false)
    {m : ℕ} (hy : position y.vm.right ≤ 2 * m - 1) :
    position x.vm.right ≤ 2 * m - 1 := by
  have hmono := front_stepsAll_mono onLetter leftFirst centre place entry q first delay h hg hPx
  rw [front_eq_position hPx hrx, front_eq_position hPy hry] at hmono
  omega

/-- **`Extra7` at any state of a run whose exit carries the cycle bound.**  This
is the shape `CloseoutPackRun46.packRunR_MG27` asks of `hprefix`, so supplying it
discharges both `hee` (the entry) and `het` (the tick), which exist only to build
`hprefix`. -/
theorem extra7_of_front_run {onLetter leftFirst : GalilVM → Prop}
    {centre : GalilVM → Fin 3} {place : GalilVM → GalilScaffoldPlace.Place} {entry q : ℕ}
    {first : Fin 9} {delay : ℕ} {Q : State GalilVM → Prop} {n : ℕ} {x y : State GalilVM}
    {w : List (Fin 2)} {m : ℕ}
    (h : StepsAll (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay Q
      n x y)
    (hg : ∀ (j : ℕ) (z : State GalilVM),
      Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay j x z →
      CentreLive z.ctl z.vm)
    (hPx : FrontPack x.ctl x.vm) (hPy : FrontPack y.ctl y.vm)
    (hry : y.ctl.replaying = false)
    (hrep : GalilScaffoldInputTrace.Represents x.vm.right.head w)
    (hpres : x.vm.right.head.focus ≠ none)
    (hm1 : 1 ≤ m) (hmle : m ≤ w.length)
    (hy : position y.vm.right ≤ 2 * m - 1) :
    CloseoutPackRun46.Extra7 x :=
  ⟨fun hm hrx => extra7_of_bound hrep hpres hm1 hmle
    (position_le_of_front_run h hg hPx hPy hrx hry hy) hm hrx⟩

#print axioms front_eq_position
#print axioms position_le_of_front_run
#print axioms extra7_of_front_run

/-! ## The pack supplies the two head facts

`Extra7` only speaks at `scan` / non-replaying states, and that is exactly where
`CloseoutLPack.LPack.scanInv` hands over a `ScanInvariant`, whose `rightRep` and
`rightPresent` fields are the two hypotheses `extra7_of_bound` still needs.
-/

/-- **The right head is represented and present at a non-replaying scan state.** -/
theorem rrep_of_lpack {w : List (Fin 2)} {c : Control} {s : GalilVM}
    (h : PalPeg.CloseoutLPack.LPack w c s) (hm : c.mode = Mode.scan)
    (hr : c.replaying = false) :
    GalilScaffoldInputTrace.Represents s.right.head w ∧ s.right.head.focus ≠ none := by
  obtain ⟨rad, hsi⟩ := h.scanInv hm hr
  exact ⟨hsi.rightRep, hsi.rightPresent⟩

/-- **`Extra7` from the run pack alone.**  The two head facts come from the pack
at the state where `Extra7` actually speaks, so no new input is needed beyond the
exit bound the cycle already carries. -/
theorem extra7_of_front_run_pack {onLetter leftFirst : GalilVM → Prop}
    {centre : GalilVM → Fin 3} {place : GalilVM → GalilScaffoldPlace.Place} {entry q : ℕ}
    {first : Fin 9} {delay : ℕ} {Q : State GalilVM → Prop} {n : ℕ} {x y : State GalilVM}
    {w : List (Fin 2)} {m : ℕ}
    (h : StepsAll (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay Q
      n x y)
    (hg : ∀ (j : ℕ) (z : State GalilVM),
      Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay j x z →
      CentreLive z.ctl z.vm)
    (hPx : FrontPack x.ctl x.vm) (hPy : FrontPack y.ctl y.vm)
    (hry : y.ctl.replaying = false)
    (hpack : PalPeg.CloseoutLPack.LPack w x.ctl x.vm)
    (hm1 : 1 ≤ m) (hmle : m ≤ w.length)
    (hy : position y.vm.right ≤ 2 * m - 1) :
    CloseoutPackRun46.Extra7 x := by
  refine ⟨fun hm hrx => ?_⟩
  obtain ⟨hrep, hpres⟩ := rrep_of_lpack hpack hm hrx
  exact extra7_of_bound hrep hpres hm1 hmle
    (position_le_of_front_run h hg hPx hPy hrx hry hy) hm hrx

#print axioms rrep_of_lpack
#print axioms extra7_of_front_run_pack

end PalPeg.CloseoutFrontExtra
