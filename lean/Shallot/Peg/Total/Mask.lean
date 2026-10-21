import Shallot.Peg.Syntax

/-!
# Sets of open nonterminals as bit masks

The run-time circularity check keeps, at each position, the set of nonterminals that are currently open there. Such
a set is a subset of the rule indices `< n`, coded as a bit mask `S < 2 ^ n`: `A ∈ S` is `S.testBit A`, adding `A` is
`ins S A = S ||| 2 ^ A`. The number of indices `< n` not in the set (`free n S`) strictly drops when an absent index
is added (`free_ins_lt`); this is the measure for termination.

A nonterminal `(k, A, S)` of the transformed grammar (kind `k < 3`, rule `A < n`, mask `S < 2 ^ n`) is coded as the
index `idx n k A S = 3 * (S * n + A) + k`, below `3 * (2 ^ n * n)` (`idx_lt`), and decoded back (`idx_mod`,
`idx_A`, `idx_S`).
-/

namespace Shallot

/-- Add the index `A` to the mask `S`. -/
def ins (S A : Nat) : Nat := S ||| 2 ^ A

/-- Membership in `ins S A`. -/
theorem testBit_ins (S A B : Nat) : (ins S A).testBit B = (S.testBit B || decide (A = B)) := by
  simp [ins, Nat.testBit_or, Nat.testBit_two_pow]

/-- `ins` keeps masks below `2 ^ n`. -/
theorem ins_lt {n S A : Nat} (hS : S < 2 ^ n) (hA : A < n) : ins S A < 2 ^ n :=
  Nat.or_lt_two_pow hS (Nat.pow_lt_pow_right (by omega) hA)

/-- The number of indices `< k` that are not in `S`. -/
def free : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, S => free k S + (if S.testBit k then 0 else 1)

/-- Adding an index never increases `free`. -/
theorem free_ins_le (S A : Nat) : ∀ k, free k (ins S A) ≤ free k S
  | 0 => Nat.le_refl _
  | k + 1 => by
    have ih := free_ins_le S A k
    simp only [free, testBit_ins]
    by_cases h : A = k
    · subst h
      cases S.testBit A <;> simp <;> omega
    · cases S.testBit k <;> simp [h] <;> omega

/-- Adding an absent index `A < k` strictly decreases `free k`. -/
theorem free_ins_lt_aux (S A : Nat) (hA : S.testBit A = false) : ∀ k, A < k → free k (ins S A) < free k S
  | 0, h => absurd h (Nat.not_lt_zero _)
  | k + 1, h => by
    simp only [free, testBit_ins]
    by_cases hk : A = k
    · subst hk
      have := free_ins_le S A A
      simp [hA]
      omega
    · have ih := free_ins_lt_aux S A hA k (by omega)
      cases S.testBit k <;> simp [hk] <;> omega

/-- **The measure drops**: adding an absent index `A < n` strictly decreases `free n`. -/
theorem free_ins_lt {n S A : Nat} (hA : A < n) (hm : S.testBit A = false) : free n (ins S A) < free n S :=
  free_ins_lt_aux S A hm n hA

/-- The empty mask has no members. -/
theorem testBit_zero_mask (A : Nat) : (0 : Nat).testBit A = false := Nat.zero_testBit A

/-! ## Coding nonterminals of the transformed grammar -/

/-- The index of the nonterminal of kind `k`, rule `A` and mask `S`. -/
def idx (n k A S : Nat) : Nat := 3 * (S * n + A) + k

theorem idx_mod {n k A S : Nat} (hk : k < 3) : idx n k A S % 3 = k := by
  unfold idx; generalize S * n + A = X; omega

theorem idx_div {n k A S : Nat} (hk : k < 3) : idx n k A S / 3 = S * n + A := by
  unfold idx; generalize S * n + A = X; omega

theorem idx_A {n A S : Nat} (hA : A < n) : (S * n + A) % n = A := by
  rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hA]

theorem idx_S {n A S : Nat} (hA : A < n) : (S * n + A) / n = S := by
  rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hA, Nat.zero_add]

/-- Coded nonterminals lie below `3 * (2 ^ n * n)`. -/
theorem idx_lt {n k A S : Nat} (hk : k < 3) (hA : A < n) (hS : S < 2 ^ n) : idx n k A S < 3 * (2 ^ n * n) := by
  have h1 : S * n + A < (S + 1) * n := by rw [Nat.succ_mul]; omega
  have h2 : (S + 1) * n ≤ 2 ^ n * n := Nat.mul_le_mul_right n hS
  unfold idx
  generalize S * n + A = X at h1
  generalize 2 ^ n * n = Y at h2
  omega

/-- Decoding: an index below `3 * (2 ^ n * n)` has rule part `< n` and mask part `< 2 ^ n`. -/
theorem decode_lt {n i : Nat} (hi : i < 3 * (2 ^ n * n)) : (i / 3) % n < n ∧ (i / 3) / n < 2 ^ n := by
  have hq : i / 3 < 2 ^ n * n := by omega
  have hn : 0 < n := by
    cases n with
    | zero => simp at hq
    | succ n => omega
  exact ⟨Nat.mod_lt _ hn, (Nat.div_lt_iff_lt_mul hn).2 hq⟩

end Shallot
