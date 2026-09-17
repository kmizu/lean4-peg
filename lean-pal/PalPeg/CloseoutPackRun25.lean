import PalPeg.CloseoutPackRun17
import PalPeg.GalilTickFair

/-!
# `CloseoutPackRun25`: `WindowInOrigin` from `Fair`

`CloseoutPackRun17` named one hypothesis, `WindowInOrigin` at every `copy`
state of a run: the FPP walker's stream is at most `position R` long.  Its
diagnosis: the landing place of `beginFallbackVM'` is existential, so the
model ties nothing to `R`; the `Fair` refinement (`GalilTickFair`) fixes it.

What `Fair` literally gives (`Fair.fallbackPlace`): at a `scan → copy` tick
the landing satisfies `t.fpp.walker = t.walker`, the *search's own cursor*
(`beginFallback_walker`: `t.walker = s'.walker`; the search loads it from
`P.place s` in `prepare` and only ever moves it left).  It does **not** say
`t.fpp.walker = stream (P.place s)`.  So `WindowInOrigin` at the landing is
exactly the bound on the search cursor, `WalkerInOrigin`
(`|stream s.walker| ≤ position s.right`), and that is the one remaining gap:
it is an invariant of the search co-process (loaded at `P.place s`, moved
left, `R` moves right), not of the fallback entry.

* `windowInOrigin_of_fair` — `Fair` + `WalkerInOrigin` at the landing gives
  `WindowInOrigin` there.
* `windowInOrigin_tick` — along one `Fair` tick, `WindowInOrigin` at `copy`
  states is preserved (`copy_one` moves the walker left, `left_stream`) and
  created at the `scan_fallback` landing from `WalkerInOrigin`.
* `FairSteps` — runs whose every tick is `Fair`; `wpack_of_fair` carries
  `CPack ∧ WPack ∧ WindowInOrigin` along them, so `hwin` of Run17 is
  discharged along `Fair` runs from `WalkerInOrigin` at the run's `copy`
  states.

## Honest status

Standard axioms only; unconditional `PAL ∈ PEG` remains open.  Remaining
hypothesis: `WalkerInOrigin` at `copy` states of the run (the search cursor
never crosses the origin), plus `hfl` as in Run17.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPackRun25

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldInputHead GalilScaffoldCounter
open PalPeg.CloseoutPackRun17
open PalPeg.GalilTickFair (Fair)
open PalPeg.GalilCentreLive (CPack cpack_tick)

/-! ## 1. The search cursor and the origin -/

/-- **(NAMED) the search's own cursor never crosses the origin.** -/
def WalkerInOrigin (s : GalilVM) : Prop :=
  (GalilScaffoldPlace.stream s.walker).length ≤ position s.right

/-- At a `Fair` `scan → copy` landing, `WindowInOrigin` is `WalkerInOrigin`. -/
theorem windowInOrigin_of_fair {entry delay : ℕ} {x y : State GalilVM}
    (hf : Fair entry delay x y) (hm : x.ctl.mode = Mode.scan) (hm' : y.ctl.mode = Mode.copy)
    (hw : WalkerInOrigin y.vm) : WindowInOrigin y.vm := by
  unfold WindowInOrigin
  rw [hf.fallbackPlace hm hm']
  exact hw

/-- Moving the FPP walker left (with `R` fixed) keeps `WindowInOrigin`. -/
theorem windowInOrigin_left {s t : GalilVM}
    (h : t.fpp.walker = GalilScaffoldPlace.left s.fpp.walker) (hr : t.right = s.right)
    (hw : WindowInOrigin s) : WindowInOrigin t := by
  unfold WindowInOrigin at *
  rw [h, hr, GalilScaffoldPlace.left_stream, List.length_tail]
  omega

/-! ## 2. One `Fair` tick -/

section Tick
variable (onLetter leftFirst : GalilVM → Prop) (centre : GalilVM → Fin 3)
  (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9) (delay : ℕ)

/-- Along a `Fair` tick, `WindowInOrigin` holds at a `copy` target: created at
the `scan_fallback` landing from `WalkerInOrigin`, preserved by `copy_one`. -/
theorem windowInOrigin_tick {c c' : Control} {s t : GalilVM}
    (hf : Fair entry delay ⟨c, s⟩ ⟨c', t⟩)
    (h : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay
      ⟨c, s⟩ ⟨c', t⟩)
    (hx : c.mode = Mode.copy → WindowInOrigin s)
    (hw : c'.mode = Mode.copy → WalkerInOrigin t)
    (hm' : c'.mode = Mode.copy) : WindowInOrigin t := by
  cases h
  all_goals try (exfalso; revert hm'; simp [‹Control.mode _ = _›]; done)
  case scan_fallback =>
    exact windowInOrigin_of_fair hf ‹Control.mode c = Mode.scan› hm' (hw hm')
  case copy_one =>
    rename_i hm hp hi
    obtain ⟨a, ha, hv⟩ : ∃ a : Fin 3, GalilScaffoldPlace.read s.fpp.walker = some a ∧
        t.fpp = {s.fpp with program := FppControl.tape s.fpp 7 (fun t => GalilScaffoldTape.moveRight (GalilScaffoldTape.write t (GalilFppPreparation.symbol a))), work := GalilScaffoldCounter.dec s.fpp.work, walker := GalilScaffoldPlace.left s.fpp.walker} := hi.1
    have ht : t = {s with fpp := t.fpp} := hi.2
    refine windowInOrigin_left ?_ ?_ (hx hm)
    · rw [hv]
    · rw [ht]

#print axioms windowInOrigin_tick

/-! ## 3. `Fair` runs -/

/-- Runs every tick of which is `Fair`. -/
inductive FairSteps (F : Frame GalilVM) (entry delay : ℕ) :
    ℕ → State GalilVM → State GalilVM → Prop
  | zero (x : State GalilVM) : FairSteps F entry delay 0 x x
  | succ {n : ℕ} {x y z : State GalilVM} (h : Tick F delay x y) (hf : Fair entry delay x y)
      (hr : FairSteps F entry delay n y z) : FairSteps F entry delay (n+1) x z

theorem FairSteps.toSteps {F : Frame GalilVM} {n : ℕ} {x y : State GalilVM}
    (h : FairSteps F entry delay n x y) : Steps F delay n x y := by
  induction h with
  | zero x => exact .zero x
  | succ ht _ _ ih => exact .succ ht ih

/-- **`CPack`, `WPack` and `WindowInOrigin` travel together along `Fair`
runs**, given `hfl` (as in Run17) and `WalkerInOrigin` at the run's `copy`
states.  This discharges `hwin` of `CloseoutPackRun17.wpack_steps` along
`Fair` runs. -/
theorem wpack_of_fair {n : ℕ} {x y : State GalilVM}
    (h : FairSteps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first)
      entry delay n x y)
    (hfl : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay m x z →
      z.ctl.mode = Mode.scan → 0 ≤ value z.vm.length)
    (hwalk : ∀ (m : ℕ) (z : State GalilVM),
      FairSteps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first)
        entry delay m x z → z.ctl.mode = Mode.copy → WalkerInOrigin z.vm)
    (hx : x.ctl.mode = Mode.copy → WindowInOrigin x.vm)
    (hP : CPack q x.ctl x.vm) (hW : WPack q first x.ctl x.vm) :
    CPack q y.ctl y.vm ∧ WPack q first y.ctl y.vm ∧
      (y.ctl.mode = Mode.copy → WindowInOrigin y.vm) := by
  induction h with
  | zero x => exact ⟨hP, hW, hx⟩
  | @succ n x w y ht hf hr ih =>
    have hw1 : w.ctl.mode = Mode.copy → WindowInOrigin w.vm := fun hm =>
      windowInOrigin_tick onLetter leftFirst centre place entry q first delay hf ht hx
        (fun hm => hwalk 1 w (.succ ht hf (.zero w)) hm) hm
    exact ih (fun m z hz => hfl (m+1) z (.succ ht hz))
      (fun m z hz => hwalk (m+1) z (.succ ht hf hz)) hw1
      (cpack_tick onLetter leftFirst centre place entry q first delay hP (hfl 0 x (.zero x)) ht)
      (wpack_tick onLetter leftFirst centre place entry q first delay hP
        (hfl 0 x (.zero x)) hw1 hW ht)

#print axioms wpack_of_fair

end Tick

#print axioms windowInOrigin_of_fair
#print axioms windowInOrigin_left
#print axioms FairSteps.toSteps

end PalPeg.CloseoutPackRun25
