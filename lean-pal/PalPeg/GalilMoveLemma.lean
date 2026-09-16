import PalPeg.GalilScaffoldChainFallback

/-!
# The combinatorial half of Galil's move lemma

A palindrome with a palindromic prefix of length `k` has period `|x| - k`
(the prefix is then also a suffix). At a nonchain mismatch the fallback
selects the longest odd palindromic prefix of the reversed window, so the
window has period `|w| - (2r+1)` = twice the centre advance. Galil's move
inequality `k ≤ 4δ` then needs only the search contract that every period
at most half the radius has already been caught by the chain.
-/

set_option autoImplicit false
namespace PalPeg

variable {α : Type}

/-- A palindromic prefix of a palindrome yields the length difference as a
period. -/
theorem hasPeriod_of_isPal_take {x : List α} (hx : IsPal x) {k : ℕ} (hk : k ≤ x.length)
    (hy : IsPal (x.take k)) : HasPeriod x (x.length - k) := by
  intro i hi
  have hi' : i < k := by omega
  have e1 : x = x.take k ++ x.drop k := (List.take_append_drop k x).symm
  have e2 : x.reverse = (x.drop k).reverse ++ x.take k := by
    conv_lhs => rw [e1]
    rw [List.reverse_append]
    have hy' : (x.take k).reverse = x.take k := hy
    rw [hy']
  have hlen : ((x.drop k).reverse).length = x.length - k := by simp
  have a1 : x[i]? = (x.take k)[i]? := (List.getElem?_take_of_lt hi').symm
  have a2 : x[i + (x.length - k)]? = (x.take k)[i]? := by
    calc x[i + (x.length - k)]? = x.reverse[i + (x.length - k)]? := by rw [hx]
      _ = ((x.drop k).reverse ++ x.take k)[i + (x.length - k)]? := by rw [e2]
      _ = (x.take k)[i + (x.length - k) - ((x.drop k).reverse).length]? :=
          List.getElem?_append_right (by rw [hlen]; omega)
      _ = (x.take k)[i]? := by
          rw [hlen]
          have e : i + (x.length - k) - (x.length - k) = i := by omega
          rw [e]
  rw [a1, a2]

/-- The fallback window (a palindrome) has period twice the centre advance:
`|T| - (2·chosenRadius T + 1)`. -/
theorem window_hasPeriod_of_chosen (T : List (Fin 3)) (hT : T ≠ []) (hpal : IsPal T) :
    HasPeriod T (T.length - (2*GalilScaffoldChainInputSupply.chosenRadius T+1)) :=
  hasPeriod_of_isPal_take hpal (GalilScaffoldChainInputSupply.chosen_spec T hT).1
    (GalilScaffoldChainInputSupply.chosen_spec T hT).2

/-- Conversely, a period `p` of a palindrome makes its prefix of length
`|x| - p` a palindrome. -/
theorem isPal_take_of_hasPeriod {x : List α} (hx : IsPal x) {p : ℕ} (hp : p ≤ x.length)
    (hper : HasPeriod x p) : IsPal (x.take (x.length - p)) := by
  rw [isPal_take_iff hx (Nat.sub_le _ _)]
  have e : x.length - (x.length - p) = p := by omega
  rw [e]
  exact ((hasPeriod_iff_drop_eq_take hp).1 hper).symm

/-- The fallback never advances the centre past half a period of the window:
a period `p` with `|T| - p` odd gives `chosenRadius T ≥ (|T| - p - 1)/2`. -/
theorem chosenRadius_ge_of_period (T : List (Fin 3)) (hpal : IsPal T) {p : ℕ} (hp : p ≤ T.length)
    (hper : HasPeriod T p) (hodd : (T.length - p) % 2 = 1) :
    (T.length - p - 1)/2 ≤ GalilScaffoldChainInputSupply.chosenRadius T := by
  apply GalilScaffoldChainInputSupply.chosen_greatest T ((T.length - p - 1)/2) (by omega)
  have e : 2*((T.length - p - 1)/2)+1 = T.length - p := by omega
  rw [e]
  exact isPal_take_of_hasPeriod hpal hp hper

#print axioms chosenRadius_ge_of_period

/-- The fallback window is the new symbol followed by the matched palindrome
`P`; the chosen palindromic prefix of length `2r+1` strips to a palindromic
prefix of `P` of length `2r-1`, so `P` has period `|P|+1-2r` — twice the
centre advance `δ = k+1-r` for `|P| = 2k+1`. -/
theorem fallback_window_period (x : Fin 3) (P : List (Fin 3)) (hP : IsPal P) :
    HasPeriod P (P.length + 1 - 2*GalilScaffoldChainInputSupply.chosenRadius (x :: P)) := by
  obtain ⟨hle, hpal⟩ := GalilScaffoldChainInputSupply.chosen_spec (x :: P) (List.cons_ne_nil x P)
  rw [List.length_cons] at hle
  rcases Nat.eq_zero_or_pos (GalilScaffoldChainInputSupply.chosenRadius (x :: P)) with h0 | hpos
  · rw [h0]; exact hasPeriod_of_length_le (by omega)
  · have hQ : (x :: P).take (2*GalilScaffoldChainInputSupply.chosenRadius (x :: P)+1)
        = x :: P.take (2*GalilScaffoldChainInputSupply.chosenRadius (x :: P)) := by
      rw [List.take_succ_cons]
    rw [hQ] at hpal
    have hlenQ : (x :: P.take (2*GalilScaffoldChainInputSupply.chosenRadius (x :: P))).length
        = 2*GalilScaffoldChainInputSupply.chosenRadius (x :: P)+1 := by
      simp only [List.length_cons, List.length_take]; omega
    have hin := isPal_drop_take_center hpal (k := 1) (by rw [hlenQ]; omega)
    have e : ((x :: P.take (2*GalilScaffoldChainInputSupply.chosenRadius (x :: P))).drop 1).take
        ((x :: P.take (2*GalilScaffoldChainInputSupply.chosenRadius (x :: P))).length - 2*1)
        = P.take (2*GalilScaffoldChainInputSupply.chosenRadius (x :: P) - 1) := by
      rw [hlenQ, List.drop_succ_cons, List.drop_zero, List.take_take]
      congr 1; omega
    rw [e] at hin
    have h := hasPeriod_of_isPal_take hP (k := 2*GalilScaffoldChainInputSupply.chosenRadius (x :: P) - 1)
      (by omega) hin
    have e2 : P.length - (2*GalilScaffoldChainInputSupply.chosenRadius (x :: P) - 1)
        = P.length + 1 - 2*GalilScaffoldChainInputSupply.chosenRadius (x :: P) := by omega
    rw [e2] at h
    exact h

/-- Galil's move inequality under the search contract: if the matched
palindrome `P` (radius `k`) has no period at most `k/2`, the fallback
advances the centre by `δ = k+1-r` with `k ≤ 4δ`. The contract — every
short period has already been caught by the chain — is what remains. -/
theorem galil_move_of_contract (x : Fin 3) (P : List (Fin 3)) (hP : IsPal P) (k : ℕ)
    (hlen : P.length = 2*k+1)
    (contract : ∀ p, 0 < p → HasPeriod P p → k < 2*p) :
    k ≤ 4*(k + 1 - GalilScaffoldChainInputSupply.chosenRadius (x :: P)) := by
  have hper := fallback_window_period x P hP
  obtain ⟨hle, _⟩ := GalilScaffoldChainInputSupply.chosen_spec (x :: P) (List.cons_ne_nil x P)
  rw [List.length_cons, hlen] at hle
  rw [hlen] at hper
  have hp := contract _ (by omega) hper
  omega

#print axioms fallback_window_period
#print axioms galil_move_of_contract

#print axioms hasPeriod_of_isPal_take
#print axioms window_hasPeriod_of_chosen

end PalPeg
