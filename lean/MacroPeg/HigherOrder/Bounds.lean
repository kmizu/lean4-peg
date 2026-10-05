import MacroPeg.HigherOrder.Decide
import MacroPeg.HigherOrder.Tower

/-!
# Closed-form bounds by order

With `P = (N+1)(N+2)` (`N` the input length) and `Ty.size` the number of nodes of a type:

* `sizeBound_le_tower`: a type of order `≤ j` has at most `tower (j+1) (P · size)` values;
* `maxCount_le_tower`: a type of order `≤ k+1` has at most `tower (k+1) (P · size)` defined entries — so the rule
  values of a grammar whose rule types have order `≤ k+1` stop growing after `tower (k+1) (P · Σ size + |R|)` rounds
  (`maxEnv_le_tower`).

For a first-order grammar (`k = 0`) the number of rounds is exponential, for order 2 doubly exponential, and so on.
-/

namespace Shallot.MacroPeg.HO

def Ty.size : Ty → Nat
  | .p => 1
  | .arr a b => a.size + b.size + 1

theorem Ty.size_pos : ∀ τ : Ty, 1 ≤ τ.size
  | .p => Nat.le_refl _
  | .arr _ _ => by simp only [Ty.size]; omega

/-- The polynomial `(N+1)(N+2)`. -/
def polyP (N : Nat) : Nat := (N + 1) * (N + 2)

theorem two_le_polyP (N : Nat) : 2 ≤ polyP N := by
  unfold polyP
  have := Nat.mul_le_mul (show 1 ≤ N + 1 by omega) (show 2 ≤ N + 2 by omega)
  omega

theorem pow_le_pow_both {x X y Y : Nat} (hx : 1 ≤ x) (hxX : x ≤ X) (hyY : y ≤ Y) : x ^ y ≤ X ^ Y :=
  Nat.le_trans (Nat.pow_le_pow_left hxX y) (Nat.pow_le_pow_right (by omega) hyY)

theorem tower_height_mono {k k' x : Nat} (h : k ≤ k') : tower k x ≤ tower k' x := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih => exact Nat.le_trans (ih (by omega)) (tower_le_succ _ _)

/-- Parsers: `(N+3)^(N+1) ≤ 2^((N+1)(N+2))`. -/
theorem sizeBound_p_le (N : Nat) : sizeBound N .p ≤ tower 1 (polyP N) := by
  simp only [sizeBound, tower_succ, tower_zero, polyP]
  have h : N + 3 ≤ 2 ^ (N + 2) := by
    have := Nat.lt_two_pow_self (n := N + 2)
    have h4 : 4 ≤ 2 ^ (N + 2) := by
      rw [Nat.pow_succ, Nat.pow_succ]; have := Nat.one_le_two_pow (n := N); omega
    omega
  calc (N + 3) ^ (N + 1) ≤ (2 ^ (N + 2)) ^ (N + 1) := Nat.pow_le_pow_left h _
    _ = 2 ^ ((N + 1) * (N + 2)) := by rw [← Nat.pow_mul, Nat.mul_comm]

/-- **Values of a type of order `≤ j`**: at most a `(j+1)`-fold exponential. -/
theorem sizeBound_le_tower (N : Nat) : ∀ (τ : Ty) (j : Nat), τ.order ≤ j →
    sizeBound N τ ≤ tower (j + 1) (polyP N * τ.size)
  | .p, j, _ => by
    have hs : polyP N * Ty.p.size = polyP N := by simp [Ty.size]
    rw [hs]
    exact Nat.le_trans (sizeBound_p_le N) (tower_height_mono (x := polyP N) (show 1 ≤ j + 1 by omega))
  | .arr a b, j, h => by
    simp only [Ty.order] at h
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have ha := sizeBound_le_tower N a i (by omega)
    have hb := sizeBound_le_tower N b (i + 1) (by omega)
    have hP := two_le_polyP N
    simp only [sizeBound]
    calc sizeBound N b ^ sizeBound N a ≤ tower (i + 2) (polyP N * b.size) ^ tower (i + 1) (polyP N * a.size) :=
          pow_le_pow_both (sizeBound_pos N b) hb ha
      _ ≤ tower (i + 2) (polyP N * b.size + polyP N * a.size + 2) := tower_pow i _ _
      _ ≤ tower (i + 2) (polyP N * (a ⇒ b).size) := tower_mono _ (by
          simp only [Ty.size, Nat.mul_add, Nat.mul_one]; omega)

/-- **Defined entries of a type of order `≤ k+1`**: at most a `(k+1)`-fold exponential. -/
theorem maxCount_le_tower (N k : Nat) : ∀ τ : Ty, τ.order ≤ k + 1 →
    maxCount N τ ≤ tower (k + 1) (polyP N * τ.size)
  | .p, _ => by
    simp only [maxCount, Ty.size, Nat.mul_one]
    refine Nat.le_trans ?_ (le_tower _ _)
    unfold polyP; exact Nat.le_mul_of_pos_right _ (by omega)
  | .arr a b, h => by
    simp only [Ty.order] at h
    have ha := Nat.le_trans (elems_length_le N a) (sizeBound_le_tower N a k (by omega))
    have hb := maxCount_le_tower N k b (by omega)
    have hP := two_le_polyP N
    simp only [maxCount]
    calc (elems N a).length * maxCount N b ≤ tower (k + 1) (polyP N * a.size) * tower (k + 1) (polyP N * b.size) :=
          Nat.mul_le_mul ha hb
      _ ≤ tower (k + 1) (polyP N * a.size + polyP N * b.size + 2) := tower_mul k _ _
      _ ≤ tower (k + 1) (polyP N * (a ⇒ b).size) := tower_mono _ (by
          simp only [Ty.size, Nat.mul_add, Nat.mul_one]; omega)

/-- The total size of the rule types. -/
def tySizeSum : List Ty → Nat
  | [] => 0
  | τ :: R => τ.size + tySizeSum R

theorem maxEnv_le_sum (N k : Nat) : ∀ R : List Ty, (∀ τ ∈ R, τ.order ≤ k + 1) →
    maxEnv N R ≤ R.length * tower (k + 1) (polyP N * tySizeSum R)
  | [], _ => by simp [maxEnv]
  | τ :: R, h => by
    have h₁ := maxCount_le_tower N k τ (h τ List.mem_cons_self)
    have h₂ := maxEnv_le_sum N k R (fun σ hσ => h σ (List.mem_cons_of_mem _ hσ))
    have m₁ : tower (k + 1) (polyP N * τ.size) ≤ tower (k + 1) (polyP N * tySizeSum (τ :: R)) :=
      tower_mono _ (Nat.mul_le_mul_left _ (by simp only [tySizeSum]; omega))
    have m₂ : tower (k + 1) (polyP N * tySizeSum R) ≤ tower (k + 1) (polyP N * tySizeSum (τ :: R)) :=
      tower_mono _ (Nat.mul_le_mul_left _ (by simp only [tySizeSum]; omega))
    have m₃ := Nat.mul_le_mul_left R.length m₂
    simp only [maxEnv, List.length_cons, Nat.succ_mul]
    omega

/-- **Rounds of the iteration**: for rule types of order `≤ k+1`, at most a `(k+1)`-fold exponential in `|x|`. -/
theorem maxEnv_le_tower (N k : Nat) (R : List Ty) (h : ∀ τ ∈ R, τ.order ≤ k + 1) :
    maxEnv N R ≤ tower (k + 1) (polyP N * tySizeSum R + R.length) :=
  Nat.le_trans (maxEnv_le_sum N k R h) (tower_mul_const k _ _)

end Shallot.MacroPeg.HO
