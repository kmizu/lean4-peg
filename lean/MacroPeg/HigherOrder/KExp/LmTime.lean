import MacroPeg.HigherOrder.KExp.Hard
import Complexity.ListTime

/-!
# A list program with a tower-of-height-`j` budget puts a language in `KEXP j`

`kexp_of_lm`: if a list program decides `L` within `tower j (c (n+1)^d)` steps with lists of that length, then
`L ∈ KEXP j` (for `j ≥ 1`): the machine of `lm_time` halts within `lmTime`, a polynomial in the budget, and a
polynomial in `tower j (·)` of a polynomial is again below `tower j` of a polynomial (`tower_mul`, `tower_add`).
-/

namespace Shallot.MacroPeg.KExp

open Complexity
open Shallot.MacroPeg.HO

/-- The budget absorbs the input length. -/
def budget (c d n : Nat) : Nat := c * (n + 1) ^ d + n + 1

theorem lmTime_le_tower (j : Nat) (c d : Nat) (s T : Nat → Nat)
    (hs : ∀ n, s n ≤ tower (j + 1) (c * (n + 1) ^ d)) (hT : ∀ n, T n ≤ tower (j + 1) (c * (n + 1) ^ d)) (n : Nat) :
    lmTime s T n ≤ tower (j + 1) ((3 * c + 72) * (n + 1) ^ (d + 1)) := by
  let A := budget c d n
  let u := tower (j + 1) A
  have hA : c * (n + 1) ^ d ≤ A := by simp only [A, budget]; omega
  have hsu : s n ≤ u := Nat.le_trans (hs n) (tower_mono _ hA)
  have hTu : T n ≤ u := Nat.le_trans (hT n) (tower_mono _ hA)
  have hnu : n + 1 ≤ u := Nat.le_trans (by simp only [A, budget]; omega) (le_tower (j + 1) A)
  -- `lmTime ≤ 16 u² + 40 u + 8`
  have h1 : lmTime s T n ≤ 16 * (u * u) + 40 * u + 8 := by
    simp only [lmTime]
    have hm : T n * (8 * (s n + (n + 2)) + 20) ≤ u * (16 * u + 36) :=
      Nat.mul_le_mul hTu (by omega)
    have : u * (16 * u + 36) = 16 * (u * u) + 36 * u := by
      rw [Nat.mul_add, Nat.mul_comm u (16 * u), Nat.mul_assoc, Nat.mul_comm 36 u]
    omega
  have h2 : 16 * (u * u) ≤ tower (j + 1) (A + A + 2 + 16) :=
    Nat.le_trans (Nat.mul_le_mul_left 16 (tower_mul j A A)) (tower_mul_const j _ 16)
  have h3 : 40 * u ≤ tower (j + 1) (A + 40) := tower_mul_const j A 40
  have h4 := tower_add (j + 1) (A + A + 2 + 16) (A + 40)
  have h5 := tower_add_const (j + 1) ((A + A + 2 + 16) + (A + 40) + 2) 6
  have hle : (A + A + 2 + 16) + (A + 40) + 2 + 6 ≤ (3 * c + 72) * (n + 1) ^ (d + 1) := by
    have hp1 : (n + 1) ^ d ≤ (n + 1) ^ (d + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have hp2 : n + 1 ≤ (n + 1) ^ (d + 1) := by
      rw [Nat.pow_succ]; exact Nat.le_mul_of_pos_left _ (Nat.pow_pos (by omega))
    have hcp : c * (n + 1) ^ d ≤ c * (n + 1) ^ (d + 1) := Nat.mul_le_mul_left c hp1
    have e : (3 * c + 72) * (n + 1) ^ (d + 1) = 3 * (c * (n + 1) ^ (d + 1)) + 72 * (n + 1) ^ (d + 1) := by
      rw [Nat.add_mul, Nat.mul_assoc]
    simp only [A, budget]
    omega
  calc lmTime s T n ≤ 16 * (u * u) + 40 * u + 8 := h1
    _ ≤ tower (j + 1) ((A + A + 2 + 16) + (A + 40) + 2) + 6 := by omega
    _ ≤ tower (j + 1) ((A + A + 2 + 16) + (A + 40) + 2 + 6) := h5
    _ ≤ _ := tower_mono _ hle

/-- **List programs within a `tower j` budget decide `KEXP j` languages** (`j ≥ 1`). -/
theorem kexp_of_lm {j : Nat} (hj : 1 ≤ j) {k : Nat} (h1 : 1 < k) (lp : LProg k) (E : Nat) (hE : 2 ≤ E)
    (hc : lp.ConstOK E) (L : Lang) (c d : Nat) (s T : Nat → Nat)
    (hs : ∀ n, s n ≤ tower j (c * (n + 1) ^ d)) (hT : ∀ n, T n ≤ tower j (c * (n + 1) ^ d))
    (h : ∀ w, ∃ t b L', t ≤ T w.length ∧ LExec (LenOK (s w.length)) lp (initLists k w) t (.stop b L') ∧
      (b = true ↔ L w)) :
    KEXP j L := by
  obtain ⟨M, hdec, hhalt⟩ := lm_time h1 lp E hE hc L s T h
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  exact ⟨k, M, lmTime s T, 3 * c + 72, d + 1, lmTime_le_tower j' c d s T hs hT, hdec, hhalt⟩

end Shallot.MacroPeg.KExp
