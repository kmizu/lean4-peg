import MacroPeg.HigherOrder.Mach.ItemsOK
import MacroPeg.HigherOrder.Cost

/-!
# The tables are at most a tower of height `j`

With `X = polyP N · cap`: a small type has at most `tower j X` rows (`rowsT_length_le`), and the lengths of values
and the numbers of environments grow at most by a factor `tower j X` per type or context number (`valT_le`,
`envT_le`).
-/

namespace Shallot.MacroPeg.Mach

open Shallot.MacroPeg.HO
open Shallot.MacroPeg.Flat

variable {j cap N : Nat} {tt ct : List (Nat × Nat)}

theorem tower_le_succ_level (k x : Nat) : tower k x ≤ tower (k + 1) x := by
  rw [tower_succ]; exact Nat.le_of_lt Nat.lt_two_pow_self

/-- **A small type has few rows.** -/
theorem rowsT_length_le (hj : 1 ≤ j) (hcap : 1 ≤ cap) (hw : TTWF tt) (k : Nat) (hk : k ≤ tt.length) :
    (rowsT j cap N tt k).length ≤ tower j (polyP N * cap) := by
  unfold rowsT
  split
  · rename_i hs
    obtain ⟨τ, hτ⟩ := tyOf_some hw k hk
    rw [rowsNum_length hτ]
    have hord : τ.order ≤ j - 1 := by have := hs.1; rw [ordNum_eq k hτ] at this; omega
    have hsize : τ.size < cap := by
      have := hs.2; rw [iok_sizeNum_eq hcap k hτ] at this
      rcases Nat.le_total cap τ.size with h | h
      · rw [Nat.min_eq_left h] at this; omega
      · rw [Nat.min_eq_right h] at this; exact this
    have h₁ := elems_le_T N (j - 1) hord
    rw [show j - 1 + 1 = j by omega] at h₁
    exact Nat.le_trans h₁ (tower_mono j (Nat.mul_le_mul_left _ (by omega)))
  · exact Nat.zero_le _

theorem polyP_ge (N : Nat) : N + 1 ≤ polyP N := le_P N

theorem mul_tower (hj : 1 ≤ j) (a b : Nat) : tower j a * tower j b ≤ tower j (a + b + 2) := by
  have := tower_mul (j - 1) a b
  rwa [show j - 1 + 1 = j by omega] at this

theorem X_ge (hcap : 1 ≤ cap) : N + 1 ≤ polyP N * cap :=
  Nat.le_trans (polyP_ge N) (Nat.le_mul_of_pos_right _ (by omega))

/-- **The lengths of values** grow at most by `tower j X` per type number. -/
theorem valT_le (hj : 1 ≤ j) (hcap : 1 ≤ cap) (hw : TTWF tt) :
    ∀ k, valT j cap N tt k ≤ tower j ((k + 1) * (polyP N * cap + 2))
  | 0 => by
    rw [valT]
    exact Nat.le_trans (X_ge hcap) (Nat.le_trans (by omega) (le_tower _ _))
  | k + 1 => by
    rw [valT]
    rcases hk : tt[k]? with _ | ⟨a, b⟩
    · exact Nat.zero_le _
    · simp only []
      split
      · rename_i hab
        have hkl : k < tt.length := (List.getElem?_eq_some_iff.1 hk).1
        have h₁ := rowsT_length_le (N := N) hj hcap hw a (by omega)
        have h₂ := valT_le hj hcap hw b
        refine Nat.le_trans (Nat.mul_le_mul h₁ h₂) (Nat.le_trans (mul_tower hj _ _) (tower_mono j ?_))
        have : (b + 1) * (polyP N * cap + 2) ≤ (k + 1) * (polyP N * cap + 2) :=
          Nat.mul_le_mul_right _ (by omega)
        rw [Nat.succ_mul (k + 1)]; omega
      · exact Nat.zero_le _

/-- **The numbers of environments** grow at most by `tower j X` per context number. -/
theorem envT_le (hj : 1 ≤ j) (hcap : 1 ≤ cap) (hw : TTWF tt) (hc : CTWF tt ct) :
    ∀ c, envT j cap N tt ct c ≤ tower j ((c + 1) * (polyP N * cap + 2))
  | 0 => by rw [envT]; exact Nat.le_trans (by omega) (le_tower _ _)
  | k + 1 => by
    rw [envT]
    rcases hk : ct[k]? with _ | ⟨par, t⟩
    · exact Nat.zero_le _
    · simp only []
      split
      · rename_i hp
        have hkl : k < ct.length := (List.getElem?_eq_some_iff.1 hk).1
        have ht : t ≤ tt.length := by
          have := (hc k hkl).2
          rw [show ct[k] = (par, t) from (List.getElem?_eq_some_iff.1 hk).2] at this; exact this
        have h₁ := envT_le hj hcap hw hc par
        have h₂ := rowsT_length_le (N := N) hj hcap hw t ht
        refine Nat.le_trans (Nat.mul_le_mul h₁ h₂) (Nat.le_trans (mul_tower hj _ _) (tower_mono j ?_))
        have : (par + 1) * (polyP N * cap + 2) ≤ (k + 1) * (polyP N * cap + 2) :=
          Nat.mul_le_mul_right _ (by omega)
        rw [Nat.succ_mul (k + 1)]; omega
      · exact Nat.zero_le _

end Shallot.MacroPeg.Mach
