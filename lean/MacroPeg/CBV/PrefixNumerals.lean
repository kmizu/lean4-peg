import MacroPeg.CBV.PrefixSuccessor

namespace Shallot.MacroPeg.CBV.PrefixCounters

open CBVtoCBN (clockValue)

/-- An external numeric index as a fixed-width tuple of prefix lengths. -/
def digitsOf (n : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | d + 1, p => (p % (n + 1)) :: digitsOf n d (p / (n + 1))

theorem digitsOf_length (n d p : Nat) : (digitsOf n d p).length = d := by
  induction d generalizing p with
  | zero => rfl
  | succ d ih => simp only [digitsOf, List.length_cons, ih]

theorem digitsOf_valid (n d p : Nat) : ∀ a ∈ digitsOf n d p, a ≤ n := by
  induction d generalizing p with
  | zero => intro a ha; cases ha
  | succ d ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · have := Nat.mod_lt p (by omega : 0 < n + 1); omega
    · exact ih _ a ha

theorem digitsOf_value (n d p : Nat) (hp : p < (n + 1) ^ d) :
    clockValue n (digitsOf n d p) = p := by
  induction d generalizing p with
  | zero =>
    have hn : p = 0 := by simp only [Nat.pow_zero] at hp; omega
    subst p
    rfl
  | succ d ih =>
    have hd : p / (n + 1) < (n + 1) ^ d := by
      apply (Nat.div_lt_iff_lt_mul (by omega : 0 < n + 1)).mpr
      simpa only [Nat.pow_succ] using hp
    simp only [digitsOf, clockValue, ih _ hd]
    exact Nat.mod_add_div _ _

theorem clockValue_lt (n : Nat) (ds : List Nat) (hv : ∀ a ∈ ds, a ≤ n) :
    clockValue n ds < (n + 1) ^ ds.length := by
  induction ds with
  | nil => simp [clockValue]
  | cons a ds ih =>
    have ha := hv a (by simp)
    have ht := ih (fun b hb => hv b (by simp [hb]))
    have hm := Nat.mul_le_mul_left (n + 1) (Nat.succ_le_of_lt ht)
    simp only [clockValue, List.length_cons, Nat.pow_succ]
    rw [Nat.mul_comm ((n + 1) ^ ds.length) (n + 1)]
    rw [Nat.mul_succ] at hm
    omega

end Shallot.MacroPeg.CBV.PrefixCounters
