import PalPeg.GalilScaffoldTopShift

/-!
# Fallback-mode instantiation of the controller frame

`FppControl.Tick` (in `GalilScaffoldChainFallback`) is the VM-side content of
the Scala `stepCopy` / `stepHome` / `fpp.start()` blocks: copy the reversed
candidate window to the FPP SOURCE tape, walk SOURCE back to LEFT, start the
program. This module instantiates the copy/home predicates of
`GalilScaffoldTop.Frame` with it and lifts every enabled `FppControl.Tick` to
the matching controller tick, with the controller mode following
`FppControl.Mode` (`copy ↦ copy`, `home ↦ home`, `run ↦ fpp`), and whole
`FppControl.Run`s to `Steps`.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController

def FppControl.Mode.toController : FppControl.Mode → GalilScaffoldController.Mode
  | .copy => .copy
  | .home => .home
  | .run => .fpp

def fallbackFrame (onLetter leftFirst : FppControl.State → Prop) : Frame FppControl.State where
  init := fun _ _ => False
  available := fun _ => False
  background := fun _ _ => False
  compare := fun _ _ => False
  matched := fun _ => False
  shiftGuard := fun _ => False
  matchedPlace := fun _ _ _ => False
  replayExhausted := fun _ => false
  onLetter := onLetter
  leftFirst := leftFirst
  beginShift := fun _ _ => False
  beginFallback := fun _ _ => False
  remainingPos := fun x => ¬ (GalilScaffoldPlace.read x.walker = none ∨
    GalilScaffoldCounter.zero x.work = true)
  shiftOne := fun _ _ => False
  copyOne := fun x y => ∃ a : Fin 3, GalilScaffoldPlace.read x.walker = some a ∧
    y = {x with program := FppControl.tape x 7 (fun t => GalilScaffoldTape.moveRight (GalilScaffoldTape.write t (GalilFppPreparation.symbol a))), work := GalilScaffoldCounter.dec x.work, walker := GalilScaffoldPlace.left x.walker}
  copyEnd := fun x y =>
    y = {x with program := FppControl.tape x 7 (fun t => GalilScaffoldTape.write t 5), mode := .home, finalStage := (GalilScaffoldPlace.read x.walker).isNone}
  atLeft := fun x => (x.program.config.tapes 7).focus = 4
  fppStart := fun x y => y = {x with program := GalilScaffoldControl.start 320 x.program, mode := .run}
  homeStep := fun x y => (x.program.config.tapes 7).left ≠ [] ∧
    y = {x with program := FppControl.tape x 7 GalilScaffoldTape.moveLeft}
  fppSlice := fun _ _ => False
  fppDone := fun _ _ => False
  atEnd := fun _ => False
  markBack := fun _ _ => False
  markForward := fun _ _ => False
  markSet := fun _ => False
  choose := fun _ _ => False
  atFirst := fun _ => False
  fppReset := fun _ _ => False
  rewindOne := fun _ _ => False
  rewindPair := fun _ _ => False
  replayStart := fun _ _ => False
  replayPos := fun _ => false
  restart := fun _ _ => False

/-- Every enabled fpp-control tick is a controller tick; the controller mode
tracks `FppControl.Mode` and nothing else in the record changes. -/
theorem fpp_control_lift (onLetter leftFirst : FppControl.State → Prop) (delay : ℕ)
    (c : Control) {x y : FppControl.State} (hm : c.mode = x.mode.toController)
    (ht : FppControl.Tick true x y) :
    GalilScaffoldTop.Tick (fallbackFrame onLetter leftFirst) delay ⟨c, x⟩
      ⟨{c with mode := y.mode.toController}, y⟩ := by
  cases ht with
  | copyBit x a hx ha hw =>
    have hc : c.mode = .copy := by rw [hm, hx]; rfl
    have hy : ({c with mode := FppControl.Mode.toController x.mode} : Control) = c := by
      rw [hx]; cases c; simp_all [FppControl.Mode.toController]
    rw [show ({x with program := FppControl.tape x 7 (fun t => GalilScaffoldTape.moveRight (GalilScaffoldTape.write t (GalilFppPreparation.symbol a))), work := GalilScaffoldCounter.dec x.work, walker := GalilScaffoldPlace.left x.walker} : FppControl.State).mode = x.mode from rfl, hy]
    refine GalilScaffoldTop.Tick.copy_one c x _ hc ?_ ⟨a, ha, rfl⟩
    show ¬ (GalilScaffoldPlace.read x.walker = none ∨ GalilScaffoldCounter.zero x.work = true)
    rintro (h | h)
    · rw [ha] at h; cases h
    · rw [hw] at h; cases h
  | copyEnd x hx he =>
    have hc : c.mode = .copy := by rw [hm, hx]; rfl
    exact GalilScaffoldTop.Tick.copy_done c x _ hc (fun h => h he) rfl
  | sourceLeft x hx hf hl =>
    have hc : c.mode = .home := by rw [hm, hx]; rfl
    have hy : ({c with mode := FppControl.Mode.toController x.mode} : Control) = c := by
      rw [hx]; cases c; simp_all [FppControl.Mode.toController]
    rw [show ({x with program := FppControl.tape x 7 GalilScaffoldTape.moveLeft} : FppControl.State).mode = x.mode from rfl, hy]
    exact GalilScaffoldTop.Tick.home_step c x _ hc hf ⟨hl, rfl⟩
  | startRun x hx hf =>
    have hc : c.mode = .home := by rw [hm, hx]; rfl
    exact GalilScaffoldTop.Tick.home_start c x _ hc hf rfl

/-- A run of `n` enabled fpp-control ticks is `n` controller ticks. -/
theorem fpp_control_run_lift (onLetter leftFirst : FppControl.State → Prop) (delay : ℕ)
    (n : ℕ) : ∀ (c : Control) {x y : FppControl.State}, c.mode = x.mode.toController →
    FppControl.Run x (List.replicate n true) y →
    Steps (fallbackFrame onLetter leftFirst) delay n ⟨c, x⟩ ⟨{c with mode := y.mode.toController}, y⟩ := by
  induction n with
  | zero =>
    intro c x y hm hr
    cases hr
    have : ({c with mode := FppControl.Mode.toController x.mode} : Control) = c := by
      rw [← hm]
    rw [this]
    exact .zero _
  | succ n ih =>
    intro c x y hm hr
    cases hr with
    | cons _ z _ _ _ ht hr' =>
      exact .succ (fpp_control_lift onLetter leftFirst delay c hm ht)
        (ih _ rfl hr')

#print axioms fpp_control_lift
#print axioms fpp_control_run_lift

end PalPeg.GalilScaffoldChainInputSupply
