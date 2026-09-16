import PalPeg.GalilScaffoldLoad

set_option autoImplicit false
namespace PalPeg.GalilScaffoldLoading
open GalilScaffoldProgram (Config)
open GalilScaffoldTape

def put {n : ℕ} (x : Config n) (t : Fin n) (v : Tape) : Config n :=
  { x with tapes := Function.update x.tapes t v }

theorem config_ext {n : ℕ} {x y : Config n} (hp : x.pc = y.pc) (ht : x.tapes = y.tapes) : x = y := by
  cases x; cases y; simp_all

theorem put_put {n : ℕ} (x : Config n) (t : Fin n) (a b : Tape) :
    put (put x t a) t b = put x t b := by
  apply config_ext
  · rfl
  · funext k; by_cases hk : k = t <;> simp [put, hk]

theorem put_same {n : ℕ} (x : Config n) (t : Fin n) : put x t (x.tapes t) = x := by
  apply config_ext
  · rfl
  · funext k; by_cases hk : k = t <;> simp [put, hk]

/-- External controller tape operations leave the kernel PC unchanged.
This records primitive operations, not an already-verified controller circuit. -/
inductive Run {n : ℕ} : Config n → ℕ → Config n → Prop
  | nil (x : Config n) : Run x 0 x
  | write (x y : Config n) (t : Fin n) (s : Fin 9) (k : ℕ)
      (hr : Run (put x t (GalilScaffoldTape.write (x.tapes t) s)) k y) : Run x (k+1) y
  | right (x y : Config n) (t : Fin n) (k : ℕ)
      (hr : Run (put x t (moveRight (x.tapes t))) k y) : Run x (k+1) y
  | left (x y : Config n) (t : Fin n) (k : ℕ) (hp : (x.tapes t).left ≠ [])
      (hr : Run (put x t (moveLeft (x.tapes t))) k y) : Run x (k+1) y

theorem run_append {n : ℕ} {x y z : Config n} {k l : ℕ}
    (hk : Run x k y) (hl : Run y l z) : Run x (k+l) z := by
  induction hk with
  | nil => simpa using hl
  | write x y t s k hr ih => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Run.write x z t s _ (ih hl)
  | right x y t k hr ih => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Run.right x z t _ (ih hl)
  | left x y t k hp hr ih => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Run.left x z t _ hp (ih hl)

theorem lift_run {n : ℕ} {a b : Tape} {k : ℕ} (hr : GalilScaffoldLoad.Run a k b)
    (x : Config n) (t : Fin n) (hx : x.tapes t = a) : Run x k (put x t b) := by
  induction hr generalizing x with
  | nil a => rw [← hx, put_same]; exact .nil _
  | write a b s k hr ih =>
    have hs := ih (put x t (write (x.tapes t) s)) (by simp [put, hx])
    rw [put_put] at hs
    exact .write _ _ _ _ _ hs
  | right a b k hr ih =>
    have hs := ih (put x t (moveRight (x.tapes t))) (by simp [put, hx])
    rw [put_put] at hs
    exact .right _ _ _ _ hs
  | left a b k hp hr ih =>
    have hs := ih (put x t (moveLeft (x.tapes t))) (by simp [put, hx])
    rw [put_put] at hs
    exact .left _ _ _ _ (by rw [hx]; exact hp) hs

/-- LOWER first, SOURCE second, as in Search.prepare/copy. Other tapes
remain reset. The cost excludes reset, guards and counter/head control. -/
theorem load_program (w : List (Fin 3)) (lower : ℕ) (old : GalilScaffoldControl.Machine 12) :
    Run (GalilScaffoldControl.reset 320 old).config (3*(lower+w.length)+8)
      (GalilScaffoldPreload.initial w lower) := by
  let x := (GalilScaffoldControl.reset 320 old).config
  let a := put x 10 (GalilScaffoldPreload.bounded (List.replicate lower 8))
  have hl : Run x (3*lower+4) a := lift_run (GalilScaffoldLoad.load_lower lower) x 10 rfl
  have hs := lift_run (GalilScaffoldLoad.load_source w) a 7 (by simp [a, put, x, GalilScaffoldControl.reset])
  have he : put a 7 (GalilScaffoldPreload.bounded (w.map GalilFppPreparation.symbol)) =
      GalilScaffoldPreload.initial w lower := by
    apply config_ext
    · rfl
    · funext t
      by_cases h7 : t = 7
      · subst t; simp [put, GalilScaffoldPreload.initial]
      · by_cases h10 : t = 10
        · subst t; simp [put, a, GalilScaffoldPreload.initial]
        · simp [put, a, x, GalilScaffoldControl.reset, GalilScaffoldPreload.initial, h7, h10]
  rw [he] at hs
  convert run_append hl hs using 1; omega

theorem load_then_dp (w : List (Fin 3)) (lower : ℕ) (old : GalilScaffoldControl.Machine 12) :
    Run (GalilScaffoldControl.reset 320 old).config (3*(lower+w.length)+8)
      (GalilScaffoldPreload.initial w lower) ∧
    ∃ v qs, GalilScaffoldProgram.Completed GalilDpCode.code (GalilScaffoldPreload.initial w lower) qs v ∧
      GalilDpCorrect.Result w lower 0 (GalilScaffoldProgram.denote v) ∧
      ∀ bs : List Bool, qs.length ≤ bs.count true →
        GalilScaffoldControl.Run GalilDpCode.code
          (GalilScaffoldControl.start 320 ⟨GalilScaffoldPreload.initial w lower,true⟩) bs ⟨v,true⟩ := by
  refine ⟨load_program w lower old, ?_⟩
  exact GalilScaffoldPreload.scheduled_correct w lower

#print axioms load_program
#print axioms load_then_dp
end PalPeg.GalilScaffoldLoading
