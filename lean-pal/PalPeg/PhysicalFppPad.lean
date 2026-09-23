import PalPeg.FrameFunction

/-!
# Left padding of the program machine

The physical program tapes lie on padding that decodes to the program's blank `6`, while an
abstract program tape may end right at its head (a freshly reset tape has `left = []`). The window
machine therefore agrees with the abstract machine **padded on the left with `6`s**, not with the
abstract machine itself. A step that does not move left at the floor commutes with this padding,
and the abstract program's own step relation forbids exactly that move
(`GalilScaffoldProgram.Execute.left` demands `left ≠ []`).
-/
set_option autoImplicit false
namespace PalPeg.PhysicalFppPad
open PalPeg.GalilScaffoldTape PalPeg.GalilScaffoldProgram PalPeg.ProgramFunction
open PalPeg.GalilFppWide (Instruction)

/-- `n` blanks under the leftmost cell. -/
def padTape (n : ℕ) (t : Tape) : Tape := ⟨t.left ++ List.replicate n 6, t.focus, t.right⟩

def padConfig {k : ℕ} (n : ℕ) (x : Config k) : Config k := ⟨x.pc, fun t => padTape n (x.tapes t)⟩

def padMachine {k : ℕ} (n : ℕ) (m : PalPeg.GalilScaffoldControl.Machine k) :
    PalPeg.GalilScaffoldControl.Machine k := ⟨padConfig n m.config, m.done⟩

@[simp] theorem padTape_focus (n : ℕ) (t : Tape) : (padTape n t).focus = t.focus := rfl

theorem moveRight_pad (n : ℕ) (t : Tape) : moveRight (padTape n t) = padTape n (moveRight t) := by
  cases t with
  | mk l f r => cases r <;> rfl

theorem moveLeft_pad (n : ℕ) (t : Tape) (h : t.left ≠ []) :
    moveLeft (padTape n t) = padTape n (moveLeft t) := by
  cases t with
  | mk l f r =>
    cases l with
    | nil => exact absurd rfl h
    | cons a ls => rfl

theorem write_pad (n : ℕ) (t : Tape) (s : Fin 9) : write (padTape n t) s = padTape n (write t s) :=
  rfl

theorem changed_pad {k : ℕ} (n : ℕ) (x : Config k) (t : Fin k) (v : Tape) (pc : ℕ) :
    changed (padConfig n x) t (padTape n v) pc = padConfig n (changed x t v pc) := by
  unfold changed padConfig
  congr 1
  funext j
  by_cases hj : j = t
  · subst hj; simp
  · simp [Function.update_of_ne hj]

/-- An instruction that does not step left at the floor. -/
def OffFloor {k : ℕ} : Instruction k → Config k → Prop
  | .move t false _, x => (x.tapes t).left ≠ []
  | _, _ => True

theorem executeFun_pad {k : ℕ} (n : ℕ) (i : Instruction k) (x : Config k) (h : OffFloor i x) :
    executeFun i (padConfig n x) = padConfig n (executeFun i x) := by
  cases i with
  | halt => rfl
  | move t dir pc =>
    cases dir
    · show changed _ t (moveLeft (padTape n (x.tapes t))) pc = _
      rw [moveLeft_pad n _ h, changed_pad]; rfl
    · show changed _ t (moveRight (padTape n (x.tapes t))) pc = _
      rw [moveRight_pad, changed_pad]; rfl
  | write t s pc =>
    show changed _ t (write (padTape n (x.tapes t)) s) pc = _
    rw [write_pad, changed_pad]; rfl
  | read t cs =>
    simp only [executeFun, padConfig, padTape_focus]
    split <;> split
    · rename_i _ c1 h1 _ c2 h2
      cases Option.some.inj (h1.symm.trans h2)
      rfl
    · rename_i _ c1 h1 _ h2
      cases (h1.symm.trans h2)
    · rename_i _ h1 _ c2 h2
      cases (h1.symm.trans h2)
    · rfl

/-- The relational step never steps left at the floor. -/
theorem offFloor_of_execute {k : ℕ} {i : Instruction k} {x y : Config k} (h : Execute i x y) :
    OffFloor i x := by
  cases h with
  | left _ t pc hl => exact hl
  | right => trivial
  | write => trivial
  | read => trivial

end PalPeg.PhysicalFppPad
