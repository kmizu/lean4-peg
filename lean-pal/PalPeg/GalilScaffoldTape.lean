import PalPeg.GalilFppWide

set_option autoImplicit false
namespace PalPeg.GalilScaffoldTape

/-- List-level interpretation of ScaffoldCircuitStructs.Tape's two stack
roots and focus. This is not yet a refinement of the physical StackPool. -/
structure Tape where
  left : List (Fin 9)
  focus : Fin 9
  right : List (Fin 9)

def read : List (Fin 9) → ℕ → Fin 9
  | [], _ => 6
  | a :: _, 0 => a
  | _ :: xs, n+1 => read xs n

def denote (t : Tape) : ℕ → Fin 9 := read (t.left.reverse ++ t.focus :: t.right)
def head (t : Tape) : ℕ := t.left.length
def reset : Tape := ⟨[], 6, []⟩
def write (t : Tape) (s : Fin 9) : Tape := { t with focus := s }

def moveRight (t : Tape) : Tape :=
  match t.right with
  | [] => ⟨t.focus :: t.left, 6, []⟩
  | a :: rs => ⟨t.focus :: t.left, a, rs⟩

def moveLeft (t : Tape) : Tape :=
  match t.left with
  | [] => t
  | a :: ls => ⟨ls, a, t.focus :: t.right⟩

theorem read_append_blank (xs : List (Fin 9)) : ∀ i, read (xs ++ [6]) i = read xs i := by
  induction xs with
  | nil => intro i; cases i <;> simp [read]
  | cons a xs ih => intro i; cases i <;> simp [read, ih]

theorem read_at_append (xs : List (Fin 9)) (a : Fin 9) (ys : List (Fin 9)) :
    read (xs ++ a :: ys) xs.length = a := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simpa [read] using ih

theorem focus_eq (t : Tape) : denote t (head t) = t.focus := by
  have h := read_at_append t.left.reverse t.focus t.right
  simpa [denote, head] using h

theorem read_replace (xs : List (Fin 9)) (ys : List (Fin 9)) (a b : Fin 9) (i : ℕ) :
    read (xs ++ b :: ys) i =
      Function.update (read (xs ++ a :: ys)) xs.length b i := by
  induction xs generalizing i with
  | nil => cases i <;> simp [read]
  | cons c xs ih =>
    cases i with
    | zero => simp [read]
    | succ i => simpa [read, Function.update_apply] using ih i

theorem write_denote (t : Tape) (s : Fin 9) :
    denote (write t s) = Function.update (denote t) (head t) s := by
  funext i
  simpa [denote, head, write] using read_replace t.left.reverse t.right t.focus s i

theorem write_head (t : Tape) (s : Fin 9) : head (write t s) = head t := rfl

theorem reset_blank : denote reset = fun _ => 6 := by
  funext i
  cases i <;> rfl

theorem reset_head : head reset = 0 := rfl

/-- Moving right preserves every cell, including when the right stack is
empty and a new blank focus is materialized. -/
theorem right_denote (t : Tape) : denote (moveRight t) = denote t := by
  rcases t with ⟨ls, a, rs⟩
  cases rs with
  | nil =>
    funext i
    simpa [denote, moveRight, List.reverse_cons, List.append_assoc] using
      read_append_blank (ls.reverse ++ [a]) i
  | cons b rs => simp [denote, moveRight, List.reverse_cons, List.append_assoc]

theorem right_head (t : Tape) : head (moveRight t) = head t+1 := by
  rcases t with ⟨ls, a, rs⟩
  cases rs <;> simp [head, moveRight]

theorem left_denote (t : Tape) : denote (moveLeft t) = denote t := by
  rcases t with ⟨ls, a, rs⟩
  cases ls with
  | nil => rfl
  | cons b ls => simp [denote, moveLeft, List.reverse_cons, List.append_assoc]

/-- Scala permits a left move exactly when its left stack is nonempty. -/
theorem left_legal (t : Tape) : t.left ≠ [] ↔ 0 < head t := by
  simp [head, List.length_pos_iff]

theorem left_head (t : Tape) (h : 0 < head t) : head (moveLeft t) = head t-1 := by
  rcases t with ⟨ls, a, rs⟩
  cases ls with
  | nil => simp [head] at h
  | cons b ls => simp [head, moveLeft]

#print axioms right_denote
#print axioms left_denote
#print axioms reset_blank
#print axioms write_denote
end PalPeg.GalilScaffoldTape
