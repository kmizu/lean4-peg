import PalPeg.GalilScaffoldChainFallback
import PalPeg.GalilScaffoldTop
import PalPeg.GalilScaffoldTopChainVM

/-!
# Shift-mode instantiation of the controller frame

`ChainShiftRun` (centre and L heads, the remaining/radius/length counters,
the chain watch and the cycle counter) is the VM-side content of the Scala
`stepShift` loop: while `remaining.sign > 0` one unit move of C and two of L,
`radius--`, `length -= 2`, `chain.shiftOne()`; otherwise back to scan with the
output refreshed. This module instantiates the shift-side predicates of
`GalilScaffoldTop.Frame`, lifts one `ChainShiftRun.next` to `Tick.shift_one`,
the exit to `Tick.shift_done`, and a whole `ChainShiftRun` of `n` units to a
run of `n` controller ticks ending in scan mode.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldInputHead GalilScaffoldChainVerifier
open GalilScaffoldTop GalilScaffoldController

structure ShiftVM where
  shift : ShiftState
  chain : ChainVM
  cycle : GalilScaffoldCounter.Counter

def shiftFrame (onLetter leftFirst : ShiftVM → Prop) : Frame ShiftVM where
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
  remainingPos := fun s => GalilScaffoldCounter.positive s.shift.remaining = true
  shiftOne := fun s s' => canRight s.shift.center ∧ canRight s.shift.left ∧
    canRight (right s.shift.left) ∧
    ∃ w, s.chain = .watch w ∧ s' = ⟨shiftTick s.shift, .watch (chainShiftOne w), GalilScaffoldCounter.inc (GalilScaffoldCounter.inc s.cycle)⟩
  copyOne := fun _ _ => False
  copyEnd := fun _ _ => False
  atLeft := fun _ => False
  fppStart := fun _ _ => False
  homeStep := fun _ _ => False
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

/-- `n` controller ticks. -/
inductive Steps {σ : Type} (F : Frame σ) (delay : ℕ) : ℕ → State σ → State σ → Prop
  | zero (x : State σ) : Steps F delay 0 x x
  | succ {n : ℕ} {x y z : State σ} (h : GalilScaffoldTop.Tick F delay x y) (hr : Steps F delay n y z) :
      Steps F delay (n+1) x z

theorem steps_trans {σ : Type} {F : Frame σ} {delay m n : ℕ} {x y z : State σ}
    (h1 : Steps F delay m x y) (h2 : Steps F delay n y z) : Steps F delay (m+n) x z := by
  induction h1 with
  | zero => simpa using h2
  | succ h _ ih =>
    rw [Nat.add_right_comm]
    exact .succ h (ih h2)

/-- A whole chain shift of `n` units is `n` `shift_one` ticks; the controller
record is untouched. -/
theorem shift_run_lift (onLetter leftFirst : ShiftVM → Prop) (delay : ℕ) (c : Control)
    (hm : c.mode = .shift) (n : ℕ) :
    ∀ {s t : ShiftState} {w v : GalilScaffoldChainWatch.State}
      {cycle finish : GalilScaffoldCounter.Counter},
      ChainShiftRun s w cycle n t v finish →
      Steps (shiftFrame onLetter leftFirst) delay n ⟨c, ⟨s, .watch w, cycle⟩⟩ ⟨c, ⟨t, .watch v, finish⟩⟩ := by
  induction n with
  | zero =>
    intro s t w v cycle finish hr
    cases hr
    exact .zero _
  | succ n ih =>
    intro s t w v cycle finish hr
    cases hr with
    | next _ _ _ enabled hc hl hl' rest =>
      refine .succ (GalilScaffoldTop.Tick.shift_one c (⟨s, .watch w, cycle⟩ : ShiftVM)
        (⟨shiftTick s, .watch (chainShiftOne w),
          GalilScaffoldCounter.inc (GalilScaffoldCounter.inc cycle)⟩ : ShiftVM) hm enabled ?_) (ih rest)
      exact ⟨hc, hl, hl', w, rfl, rfl⟩

/-- The exit of the shift loop: `remaining` exhausted, back to scan with the
output refreshed from `onLetter`/`leftFirst`. -/
theorem shift_exit_lift (onLetter leftFirst : ShiftVM → Prop) (delay : ℕ) (c : Control)
    (hm : c.mode = .shift) (s : ShiftVM)
    (hz : GalilScaffoldCounter.positive s.shift.remaining = false) :
    ∃ o : Bool, GalilScaffoldTop.Tick (shiftFrame onLetter leftFirst) delay ⟨c, s⟩
      ⟨{c with mode := .scan, output := o}, s⟩ := by
  classical
  refine ⟨if onLetter s then decide (leftFirst s) else c.output, ?_⟩
  refine GalilScaffoldTop.Tick.shift_done c s _ hm ?_ ?_
  · show ¬ GalilScaffoldCounter.positive s.shift.remaining = true
    rw [hz]; decide
  · refine ⟨fun hl => ?_, fun hl => ?_⟩
    · have hl' : onLetter s := hl
      show (if onLetter s then decide (leftFirst s) else c.output) = true ↔ leftFirst s
      rw [if_pos hl']
      exact decide_eq_true_iff
    · have hl' : ¬ onLetter s := hl
      show (if onLetter s then decide (leftFirst s) else c.output) = c.output
      rw [if_neg hl']

/-- A chain shift followed by its exit: `n+1` ticks from shift mode back to
scan mode. -/
theorem shift_phase_lift (onLetter leftFirst : ShiftVM → Prop) (delay : ℕ) (c : Control)
    (hm : c.mode = .shift) {n : ℕ} {s t : ShiftState} {w v : GalilScaffoldChainWatch.State}
    {cycle finish : GalilScaffoldCounter.Counter}
    (hr : ChainShiftRun s w cycle n t v finish)
    (hz : GalilScaffoldCounter.positive t.remaining = false) :
    ∃ o : Bool, Steps (shiftFrame onLetter leftFirst) delay (n+1) ⟨c, ⟨s, .watch w, cycle⟩⟩
      ⟨{c with mode := .scan, output := o}, ⟨t, .watch v, finish⟩⟩ := by
  obtain ⟨o, ho⟩ := shift_exit_lift onLetter leftFirst delay c hm ⟨t, .watch v, finish⟩ hz
  refine ⟨o, ?_⟩
  have h1 := shift_run_lift onLetter leftFirst delay c hm n hr
  exact steps_trans h1 (.succ ho (.zero _))

#print axioms shift_run_lift
#print axioms shift_phase_lift

end PalPeg.GalilScaffoldChainInputSupply
