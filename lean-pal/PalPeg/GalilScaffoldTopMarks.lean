import PalPeg.GalilScaffoldTopFpp

/-!
# MarkEnd-mode instantiation of the controller frame

`stepMarkEnd` walks the MARKS tape to the right until it reads END (`5`),
then steps back one cell, clears `odd` and enters `Choose`. This module
instantiates `atEnd`/`markForward`/`markBack` with the physical tape 8 of the
FPP program and proves the walk: from a head whose next END lies `k` cells
to the right, the controller takes `k+1` ticks and ends in `choose` mode with
the head one cell before END, the tape contents unchanged.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController

def marksTape (x : FppControl.State) : GalilScaffoldTape.Tape := x.program.config.tapes 8

def markStep (x : FppControl.State) (f : GalilScaffoldTape.Tape → GalilScaffoldTape.Tape) :
    FppControl.State := {x with program := FppControl.tape x 8 f}

theorem markStep_tape (x : FppControl.State) (f : GalilScaffoldTape.Tape → GalilScaffoldTape.Tape) :
    marksTape (markStep x f) = f (marksTape x) := by
  simp [marksTape, markStep, FppControl.tape, GalilScaffoldLoading.put]

theorem markStep_other (x : FppControl.State) (f : GalilScaffoldTape.Tape → GalilScaffoldTape.Tape)
    (i : Fin 9) (hi : i ≠ 8) : (markStep x f).program.config.tapes i = x.program.config.tapes i := by
  simp [markStep, FppControl.tape, GalilScaffoldLoading.put, hi]

/-- Everything but the MARKS head position is preserved by the walk. -/
structure MarksSame (x y : FppControl.State) : Prop where
  mode : y.mode = x.mode
  walker : y.walker = x.walker
  work : y.work = x.work
  finalStage : y.finalStage = x.finalStage
  pc : y.program.config.pc = x.program.config.pc
  done : y.program.done = x.program.done
  other : ∀ i : Fin 9, i ≠ 8 → y.program.config.tapes i = x.program.config.tapes i
  denote : GalilScaffoldTape.denote (marksTape y) = GalilScaffoldTape.denote (marksTape x)

theorem MarksSame.refl (x : FppControl.State) : MarksSame x x := ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, rfl⟩

theorem MarksSame.trans {x y z : FppControl.State} (h1 : MarksSame x y) (h2 : MarksSame y z) :
    MarksSame x z :=
  ⟨h2.mode.trans h1.mode, h2.walker.trans h1.walker, h2.work.trans h1.work,
    h2.finalStage.trans h1.finalStage, h2.pc.trans h1.pc, h2.done.trans h1.done,
    fun i hi => (h2.other i hi).trans (h1.other i hi), h2.denote.trans h1.denote⟩

theorem markStep_same (x : FppControl.State) (f : GalilScaffoldTape.Tape → GalilScaffoldTape.Tape)
    (hf : GalilScaffoldTape.denote (f (marksTape x)) = GalilScaffoldTape.denote (marksTape x)) :
    MarksSame x (markStep x f) :=
  ⟨rfl, rfl, rfl, rfl, by simp [markStep, FppControl.tape, GalilScaffoldLoading.put],
    rfl, markStep_other x f, by rw [markStep_tape]; exact hf⟩

def marksFrame (first : Fin 9) (onLetter leftFirst : FppControl.State → Prop) : Frame FppControl.State where
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
  remainingPos := fun _ => False
  shiftOne := fun _ _ => False
  copyOne := fun _ _ => False
  copyEnd := fun _ _ => False
  atLeft := fun _ => False
  fppStart := fun _ _ => False
  homeStep := fun _ _ => False
  fppSlice := fun _ _ => False
  fppDone := fun _ _ => False
  atEnd := fun x => (marksTape x).focus = 5
  markBack := fun x y => (marksTape x).left ≠ [] ∧ y = markStep x GalilScaffoldTape.moveLeft
  markForward := fun x y => y = markStep x GalilScaffoldTape.moveRight
  markSet := fun x => (marksTape x).focus = 8 ∨ (marksTape x).focus = first
  choose := fun _ _ => False
  atFirst := fun x => (marksTape x).focus = first
  fppReset := fun _ _ => False
  rewindOne := fun _ _ => False
  rewindPair := fun _ _ => False
  replayStart := fun _ _ => False
  replayPos := fun _ => false
  restart := fun _ _ => False

/-- Walking right over `k` non-END cells: `k` `markEnd_step` ticks, head
advanced by `k`, contents preserved. -/
theorem markEnd_walk (first : Fin 9) (onLetter leftFirst : FppControl.State → Prop) (delay : ℕ)
    (c : Control) (hm : c.mode = .markEnd) (x : FppControl.State) :
    ∀ k, (∀ j, j < k → GalilScaffoldTape.denote (marksTape x) (GalilScaffoldTape.head (marksTape x) + j) ≠ 5) →
      ∃ y, Steps (marksFrame first onLetter leftFirst) delay k ⟨c, x⟩ ⟨c, y⟩ ∧ MarksSame x y ∧
        GalilScaffoldTape.head (marksTape y) = GalilScaffoldTape.head (marksTape x) + k := by
  intro k
  induction k with
  | zero => intro _; exact ⟨x, .zero _, MarksSame.refl x, rfl⟩
  | succ k ih =>
    intro hne
    obtain ⟨y, hs, hsame, hhead⟩ := ih (fun j hj => hne j (by omega))
    have hfocus : (marksTape y).focus ≠ 5 := by
      rw [← GalilScaffoldTape.focus_eq, hsame.denote, hhead]
      exact hne k (by omega)
    refine ⟨markStep y GalilScaffoldTape.moveRight, ?_, ?_, ?_⟩
    · refine steps_trans hs (.succ (GalilScaffoldTop.Tick.markEnd_step c y _ hm hfocus rfl) (.zero _))
    · exact hsame.trans (markStep_same y _ (GalilScaffoldTape.right_denote _))
    · rw [markStep_tape, GalilScaffoldTape.right_head, hhead]
      omega

/-- The MarkEnd phase: END `k` cells to the right of the head, no END before
it. `k+1` ticks later the controller is in `choose` mode with `odd = false`
and the MARKS head one cell before END. -/
theorem markEnd_phase (first : Fin 9) (onLetter leftFirst : FppControl.State → Prop) (delay : ℕ)
    (c : Control) (hm : c.mode = .markEnd) (x : FppControl.State) (k : ℕ)
    (hne : ∀ j, j < k → GalilScaffoldTape.denote (marksTape x) (GalilScaffoldTape.head (marksTape x) + j) ≠ 5)
    (hend : GalilScaffoldTape.denote (marksTape x) (GalilScaffoldTape.head (marksTape x) + k) = 5)
    (hpos : 0 < GalilScaffoldTape.head (marksTape x) + k) :
    ∃ y, Steps (marksFrame first onLetter leftFirst) delay (k+1) ⟨c, x⟩
        ⟨{c with mode := .choose, odd := false}, y⟩ ∧ MarksSame x y ∧
      GalilScaffoldTape.head (marksTape y) = GalilScaffoldTape.head (marksTape x) + k - 1 := by
  obtain ⟨y, hs, hsame, hhead⟩ := markEnd_walk first onLetter leftFirst delay c hm x k hne
  have hfocus : (marksTape y).focus = 5 := by
    rw [← GalilScaffoldTape.focus_eq, hsame.denote, hhead]; exact hend
  have hleft : (marksTape y).left ≠ [] := by
    rw [GalilScaffoldTape.left_legal, hhead]; exact hpos
  refine ⟨markStep y GalilScaffoldTape.moveLeft, ?_, ?_, ?_⟩
  · exact steps_trans hs (.succ (GalilScaffoldTop.Tick.markEnd_found c y _ hm hfocus ⟨hleft, rfl⟩) (.zero _))
  · exact hsame.trans (markStep_same y _ (GalilScaffoldTape.left_denote _))
  · rw [markStep_tape, GalilScaffoldTape.left_head _ (by rw [hhead]; exact hpos), hhead]

#print axioms markEnd_phase

end PalPeg.GalilScaffoldChainInputSupply
