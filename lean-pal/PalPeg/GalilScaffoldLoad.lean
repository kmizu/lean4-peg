import PalPeg.GalilScaffoldPreload

set_option autoImplicit false
namespace PalPeg.GalilScaffoldLoad
open GalilScaffoldTape

def fill : List (Fin 9) → Tape → Tape
  | [], t => t
  | a :: xs, t => fill xs (moveRight (write t a))

theorem fill_stack (xs ls : List (Fin 9)) :
    fill xs ⟨ls,6,[]⟩ = ⟨xs.reverse ++ ls,6,[]⟩ := by
  induction xs generalizing ls with
  | nil => rfl
  | cons a xs ih =>
    simpa [fill, moveRight, write, List.reverse_cons, List.append_assoc] using ih (a :: ls)

/-- Primitive tape-operation execution; costs here count writes and
moves, not controller ticks or heap allocation. -/
inductive Run : Tape → ℕ → Tape → Prop
  | nil (x : Tape) : Run x 0 x
  | write (x y : Tape) (s : Fin 9) (n : ℕ) (hr : Run (GalilScaffoldTape.write x s) n y) : Run x (n+1) y
  | right (x y : Tape) (n : ℕ) (hr : Run (moveRight x) n y) : Run x (n+1) y
  | left (x y : Tape) (n : ℕ) (hp : x.left ≠ []) (hr : Run (moveLeft x) n y) : Run x (n+1) y

theorem run_append {x y z : Tape} {n m : ℕ} (hn : Run x n y) (hm : Run y m z) : Run x (n+m) z := by
  induction hn with
  | nil => simpa using hm
  | write x y s n hr ih => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Run.write x z s _ (ih hm)
  | right x y n hr ih => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Run.right x z _ (ih hm)
  | left x y n hp hr ih => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Run.left x z _ hp (ih hm)

theorem fill_run (xs : List (Fin 9)) (x : Tape) : Run x (2*xs.length) (fill xs x) := by
  induction xs generalizing x with
  | nil => exact .nil _
  | cons a xs ih =>
    simpa [fill, Nat.mul_add, Nat.add_assoc] using
      Run.write x _ a _ (Run.right _ _ _ (ih (moveRight (write x a))))

/-- The actual home loop tests focus for LEFT; it does not use an
externally supplied rewind distance to choose when to stop. -/
inductive Home : Tape → ℕ → Tape → Prop
  | done (x : Tape) (h : x.focus = 4) : Home x 0 x
  | left (x y : Tape) (n : ℕ) (hc : x.focus ≠ 4) (hp : x.left ≠ [])
      (hr : Home (moveLeft x) n y) : Home x (n+1) y

theorem home_run {x y : Tape} {n : ℕ} (hr : Home x n y) : Run x n y := by
  induction hr with
  | done => exact .nil _
  | left x y n hc hp hr ih => exact .left _ _ _ hp ih

theorem home_exact (ls : List (Fin 9)) (a : Fin 9) (rs : List (Fin 9))
    (ha : a ≠ 4) (hl : (4 : Fin 9) ∉ ls) :
    Home ⟨ls ++ [4],a,rs⟩ (ls.length+1) ⟨[],4,ls.reverse ++ a :: rs⟩ := by
  induction ls generalizing a rs with
  | nil => exact .left _ _ 0 ha (by simp) (.done _ rfl)
  | cons b ls ih =>
    have hb : b ≠ 4 := by intro he; apply hl; simp [he]
    have ht : (4 : Fin 9) ∉ ls := by intro he; apply hl; simp [he]
    have hr := ih b (a :: rs) hb ht
    have hstep := Home.left ⟨(b :: ls) ++ [4],a,rs⟩ _ _ ha (by simp)
      (by simpa [moveLeft] using hr)
    convert hstep using 1 <;> simp [List.reverse_cons, List.append_assoc, Nat.add_assoc]

/-- Reset, write LEFT, write the payload while moving right, write END,
then home by marker tests: this constructs the concrete bounded preload. -/
theorem load (xs : List (Fin 9)) (hx : (4 : Fin 9) ∉ xs) :
    Run reset (3*xs.length+4) (GalilScaffoldPreload.bounded xs) := by
  have hf : Run (moveRight (write reset 4)) (2*xs.length) ⟨xs.reverse ++ [4],6,[]⟩ := by
    simpa [reset, write, moveRight, fill_stack] using fill_run xs (moveRight (write reset 4))
  have hh := home_exact xs.reverse 5 [] (by decide) (by simpa using hx)
  have hw : Run (⟨xs.reverse ++ [4],6,[]⟩ : Tape) (xs.length+2) (GalilScaffoldPreload.bounded xs) := by
    simpa [write, GalilScaffoldPreload.bounded] using
      Run.write ⟨xs.reverse ++ [4],6,[]⟩ _ 5 _ (home_run hh)
  have hr := Run.write reset _ 4 _ (Run.right _ _ _ (run_append hf hw))
  convert hr using 1; omega

theorem load_source (w : List (Fin 3)) :
    Run reset (3*w.length+4)
      (GalilScaffoldPreload.bounded (w.map GalilFppPreparation.symbol)) := by
  have hn : (4 : Fin 9) ∉ w.map GalilFppPreparation.symbol := by
    intro hm
    obtain ⟨a, _, ha⟩ := List.mem_map.mp hm
    have hv := congrArg Fin.val ha
    have := a.isLt
    simp [GalilFppPreparation.symbol] at hv
    omega
  simpa using load (w.map GalilFppPreparation.symbol) hn

theorem load_lower (lower : ℕ) :
    Run reset (3*lower+4) (GalilScaffoldPreload.bounded (List.replicate lower 8)) := by
  simpa using load (List.replicate lower 8) (by simp)

#print axioms load
#print axioms load_source
#print axioms load_lower
end PalPeg.GalilScaffoldLoad
