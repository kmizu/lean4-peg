import MacroPeg.HigherOrder.ExpSpace.Machine

/-!
# Bits of natural numbers

Level-1 numbers of the order-`k` construction are bit vectors, most significant bit first (`bitsMSB`); higher levels
index the bits of a number by smaller numbers, least significant first (`Nat.testBit`). The successor flips bit `i`
iff all lower bits are set (`testBit_succ`), the predecessor iff all lower bits are clear (`testBit_pred`).
-/

namespace Shallot.MacroPeg.Levels

open Shallot.MacroPeg.ExpSpace (incBits decBits)

/-- All bits of `x` below `i` are set. -/
def allBelow (x i : Nat) : Bool := (List.range i).all (fun j => x.testBit j)

/-- All bits of `x` below `i` are clear. -/
def noneBelow (x i : Nat) : Bool := (List.range i).all (fun j => !x.testBit j)

/-- The lowest `m` bits of `x`, most significant first. -/
def bitsMSB : Nat → Nat → List Bool
  | 0, _ => []
  | m + 1, x => x.testBit m :: bitsMSB m x

private theorem nb_allBelow_zero (x : Nat) : allBelow x 0 = true := by
  simp [allBelow]

private theorem nb_noneBelow_zero (x : Nat) : noneBelow x 0 = true := by
  simp [noneBelow]

private theorem nb_allBelow_succ_left (x i : Nat) :
    allBelow x (i + 1) = (x.testBit 0 && allBelow (x / 2) i) := by
  simp [allBelow, List.range_succ_eq_map, Nat.testBit_succ, Function.comp_def]

private theorem nb_noneBelow_succ_left (x i : Nat) :
    noneBelow x (i + 1) = (!x.testBit 0 && noneBelow (x / 2) i) := by
  simp [noneBelow, List.range_succ_eq_map, Nat.testBit_succ, Function.comp_def]

private theorem nb_allBelow_succ_right (x m : Nat) :
    allBelow x (m + 1) = (allBelow x m && x.testBit m) := by
  simp [allBelow, List.range_succ]

private theorem nb_noneBelow_succ_right (x m : Nat) :
    noneBelow x (m + 1) = (noneBelow x m && !x.testBit m) := by
  simp [noneBelow, List.range_succ]

private theorem nb_allBelow_iff (x i : Nat) :
    allBelow x i = true ↔ ∀ j < i, x.testBit j = true := by
  simp [allBelow]

private theorem nb_noneBelow_iff (x i : Nat) :
    noneBelow x i = true ↔ ∀ j < i, x.testBit j = false := by
  simp [noneBelow]

theorem testBit_succ (x i : Nat) : (x + 1).testBit i = (x.testBit i != allBelow x i) := by
  induction i generalizing x with
  | zero =>
    rw [nb_allBelow_zero]
    simp only [Nat.testBit_zero]
    by_cases h : x % 2 = 1 <;> simp [h] <;> omega
  | succ i ih =>
    rw [nb_allBelow_succ_left, Nat.testBit_succ, Nat.testBit_succ]
    by_cases h : x % 2 = 1
    · have h1 : (x + 1) / 2 = x / 2 + 1 := by omega
      rw [h1, ih]
      simp [h]
    · have h1 : (x + 1) / 2 = x / 2 := by omega
      rw [h1]
      simp [h]

theorem testBit_pred (x i : Nat) (hx : 0 < x) :
    (x - 1).testBit i = (x.testBit i != noneBelow x i) := by
  induction i generalizing x with
  | zero =>
    rw [nb_noneBelow_zero]
    simp only [Nat.testBit_zero]
    by_cases h : x % 2 = 1 <;> simp [h] <;> omega
  | succ i ih =>
    rw [nb_noneBelow_succ_left, Nat.testBit_succ, Nat.testBit_succ]
    by_cases h : x % 2 = 1
    · have h1 : (x - 1) / 2 = x / 2 := by omega
      rw [h1]
      simp [h]
    · have h1 : (x - 1) / 2 = x / 2 - 1 := by omega
      have h2 : 0 < x / 2 := by omega
      rw [h1, ih _ h2]
      simp [h]

theorem testBit_ge {E x : Nat} (hx : x < 2 ^ E) {i : Nat} (hi : E ≤ i) : x.testBit i = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hi))

theorem eq_iff_testBit {E x y : Nat} (hx : x < 2 ^ E) (hy : y < 2 ^ E) :
    x = y ↔ ∀ i < E, x.testBit i = y.testBit i := by
  constructor
  · intro h i _; rw [h]
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < E
    · exact h i hi
    · rw [testBit_ge hx (by omega), testBit_ge hy (by omega)]

theorem eq_zero_iff_testBit {E x : Nat} (hx : x < 2 ^ E) : x = 0 ↔ ∀ i < E, x.testBit i = false := by
  have h0 : (0 : Nat) < 2 ^ E := Nat.two_pow_pos _
  rw [eq_iff_testBit hx h0]
  simp

theorem eq_max_iff_testBit {E x : Nat} (hx : x < 2 ^ E) :
    x = 2 ^ E - 1 ↔ ∀ i < E, x.testBit i = true := by
  have h0 : 2 ^ E - 1 < 2 ^ E := Nat.sub_lt (Nat.two_pow_pos _) (by decide)
  rw [eq_iff_testBit hx h0]
  constructor
  · intro h i hi; rw [h i hi]; simp [hi]
  · intro h i hi; rw [h i hi]; simp [hi]

theorem length_bitsMSB (m x : Nat) : (bitsMSB m x).length = m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [bitsMSB, ih]

theorem bitsMSB_getD {m x j : Nat} (hj : j < m) :
    (bitsMSB m x).getD j false = x.testBit (m - 1 - j) := by
  induction m generalizing j with
  | zero => omega
  | succ m ih =>
    cases j with
    | zero => simp [bitsMSB]
    | succ j =>
      have h := ih (j := j) (by omega)
      have e : m + 1 - 1 - (j + 1) = m - 1 - j := by omega
      rw [e, ← h]
      simp [bitsMSB]

theorem bitsMSB_all (m x : Nat) : (bitsMSB m x).all id = allBelow x m := by
  induction m with
  | zero => simp [bitsMSB, nb_allBelow_zero]
  | succ m ih =>
    rw [nb_allBelow_succ_right, ← ih]
    simp [bitsMSB, Bool.and_comm]

theorem bitsMSB_none (m x : Nat) : (bitsMSB m x).all (! ·) = noneBelow x m := by
  induction m with
  | zero => simp [bitsMSB, nb_noneBelow_zero]
  | succ m ih =>
    rw [nb_noneBelow_succ_right, ← ih]
    simp [bitsMSB, Bool.and_comm]

theorem bitsMSB_inj {m x y : Nat} (hx : x < 2 ^ m) (hy : y < 2 ^ m)
    (h : bitsMSB m x = bitsMSB m y) : x = y := by
  rw [eq_iff_testBit hx hy]
  intro i hi
  have h1 := bitsMSB_getD (m := m) (x := x) (j := m - 1 - i) (by omega)
  have h2 := bitsMSB_getD (m := m) (x := y) (j := m - 1 - i) (by omega)
  have e : m - 1 - (m - 1 - i) = i := by omega
  rw [e] at h1 h2
  rw [← h1, ← h2, h]

theorem incBits_bitsMSB (m x : Nat) : incBits (bitsMSB m x) = bitsMSB m (x + 1) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [bitsMSB, incBits, bitsMSB_all, ih]
    rw [testBit_succ]

theorem decBits_bitsMSB (m x : Nat) (hx : 0 < x) :
    decBits (bitsMSB m x) = bitsMSB m (x - 1) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [bitsMSB, decBits, bitsMSB_none, ih]
    rw [testBit_pred x m hx]

theorem allBelow_iff {E x : Nat} (hx : x < 2 ^ E) : allBelow x E = true ↔ x = 2 ^ E - 1 := by
  rw [nb_allBelow_iff, eq_max_iff_testBit hx]

theorem noneBelow_iff {E x : Nat} (hx : x < 2 ^ E) : noneBelow x E = true ↔ x = 0 := by
  rw [nb_noneBelow_iff, eq_zero_iff_testBit hx]

theorem bitsMSB_zero (m : Nat) : bitsMSB m 0 = List.replicate m false := by
  induction m with
  | zero => rfl
  | succ m ih => simp [bitsMSB, ih, List.replicate_succ]

theorem bitsMSB_max (m : Nat) : bitsMSB m (2 ^ m - 1) = List.replicate m true := by
  apply List.ext_getElem
  · simp [length_bitsMSB]
  · intro j h1 h2
    have hj : j < m := by simpa [length_bitsMSB] using h1
    have := bitsMSB_getD (m := m) (x := 2 ^ m - 1) hj
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1] at this
    simp only [Option.getD_some] at this
    rw [this]
    simp; omega

end Shallot.MacroPeg.Levels
