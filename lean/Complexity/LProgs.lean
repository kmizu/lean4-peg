import Complexity.LKit

/-!
# Basic list programs

`skip`, `moveTop i j` (move the last element of `i` onto `j`), `moveAll i j` (move every element, reversing), with
their specifications.
-/

namespace Complexity

variable {k : Nat}

/-- Does nothing (one step). -/
def skipP (i : Fin k) : LProg k := .loop i (fun _ => false) (.halt false)

def moveTop (i j : Fin k) : LProg k := .seq (.copy i j) (.pop i)

def moveAll (i j : Fin k) : LProg k := .loop i (· != 3) (moveTop i j)

section
variable {Q : Lists k → Prop}

theorem runs_skip (i : Fin k) {L : Lists k} (h : Q L) : Runs Q (skipP i) L L 1 :=
  ⟨1, Nat.le_refl _, .loopF h rfl⟩

theorem lastSym_eq_three {l : List Nat} : lastSym l = 3 ↔ l = [] := by
  constructor
  · intro h
    cases hl : l.getLast? with
    | none => exact List.getLast?_eq_none_iff.1 hl
    | some e => simp [lastSym, hl] at h
  · rintro rfl; rfl

/-- The state after moving the top of `i` (nonempty) onto `j`. -/
def Lists.moveTop (L : Lists k) (i j : Fin k) : Lists k :=
  (L.set j (L j ++ (L i).getLast?.toList)).set i (L i).dropLast

theorem runs_moveTop {i j : Fin k} (hij : i ≠ j) {L : Lists k} (h₀ : Q L)
    (h₁ : Q (L.set j (L j ++ (L i).getLast?.toList))) (h₂ : Q (L.moveTop i j)) :
    Runs Q (moveTop i j) L (L.moveTop i j) 2 := by
  have e : ((L.set j (L j ++ (L i).getLast?.toList)) i).dropLast = (L i).dropLast := by
    rw [Lists.set_ne _ _ hij]
  have := (runs_copy hij h₀ h₁).seq (runs_pop h₁ (by rw [e]; exact h₂))
  rw [e] at this
  exact this

theorem moveTop_i {L : Lists k} {i j : Fin k} : (L.moveTop i j) i = (L i).dropLast := by
  simp [Lists.moveTop]

theorem moveTop_j {L : Lists k} {i j : Fin k} (hij : i ≠ j) :
    (L.moveTop i j) j = L j ++ (L i).getLast?.toList := by
  simp [Lists.moveTop, Lists.set_ne _ _ (Ne.symm hij)]

theorem moveTop_other {L : Lists k} {i j x : Fin k} (hi : x ≠ i) (hj : x ≠ j) : (L.moveTop i j) x = L x := by
  simp [Lists.moveTop, Lists.set_ne _ _ hi, Lists.set_ne _ _ hj]

/-- After moving everything from `i` to `j`. -/
def Lists.moveAll (L : Lists k) (i j : Fin k) : Lists k := (L.set j (L j ++ (L i).reverse)).set i []

/-- After moving `m` elements onto `j` while `i` is cut to its first `(L i).length - n` elements. -/
def Lists.moving (L : Lists k) (i j : Fin k) (n m : Nat) : Lists k :=
  (L.set j (L j ++ ((L i).reverse.take m))).set i ((L i).take ((L i).length - n))

end

end Complexity
