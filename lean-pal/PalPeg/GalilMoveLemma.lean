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

/-- The newly read symbol is the boundary symbol selected by the fallback
period.  This is the one-place fact which turns divisibility by an old period
into an impossible extension across the mismatching comparison. -/
theorem fallback_window_boundary (x : Fin 3) (P : List (Fin 3)) (hP : IsPal P)
    (hr : 0 < GalilScaffoldChainInputSupply.chosenRadius (x :: P)) :
    some x = P[P.length + 1 -
      2*GalilScaffoldChainInputSupply.chosenRadius (x :: P) - 1]? := by
  let r := GalilScaffoldChainInputSupply.chosenRadius (x :: P)
  obtain ⟨hle,hpal⟩ := GalilScaffoldChainInputSupply.chosen_spec
    (x :: P) (List.cons_ne_nil x P)
  have htlen : ((x :: P).take (2*r+1)).length = 2*r+1 := by
    rw [List.length_take]
    omega
  have hmirror := (isPal_iff_getElem?.mp hpal) 0 (by rw [htlen]; omega)
  rw [htlen, show 2*r+1-1-0 = 2*r by omega] at hmirror
  have hx : some x = P[2*r-1]? := by
    change some x = ((x :: P).take (2*r+1))[2*r]? at hmirror
    rw [List.getElem?_take_of_lt (by omega)] at hmirror
    rw [show 2*r = (2*r-1)+1 by omega] at hmirror
    simpa only [List.getElem?_cons_zero,List.getElem?_cons_succ] using hmirror
  have hpidx := (isPal_iff_getElem?.mp hP) (2*r-1) (by
    change 2*r+1 ≤ P.length+1 at hle
    omega)
  rw [show P.length - 1 - (2*r-1) = P.length+1-2*r-1 by omega] at hpidx
  exact hx.trans hpidx

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

/-- The move inequality only needs a non-strict half-period contract.  The
extra `+1` in the centre advance covers the equality case `k = 2*p`. -/
theorem galil_move_of_weakContract (x : Fin 3) (P : List (Fin 3)) (hP : IsPal P) (k : ℕ)
    (hlen : P.length = 2*k+1)
    (contract : ∀ p, 0 < p → HasPeriod P p → k ≤ 2*p) :
    k ≤ 4*(k + 1 - GalilScaffoldChainInputSupply.chosenRadius (x :: P)) := by
  have hper := fallback_window_period x P hP
  obtain ⟨hle, _⟩ := GalilScaffoldChainInputSupply.chosen_spec (x :: P) (List.cons_ne_nil x P)
  rw [List.length_cons, hlen] at hle
  rw [hlen] at hper
  have hp := contract _ (by omega) hper
  omega

/-- The coefficient-parametric form used by the packed-run fallback proof.
The fallback period is twice the centre advance, so a contract
`2*k ≤ B*p` yields `k ≤ B*advance`. -/
theorem galil_move_of_scaledContract (B : ℕ) (x : Fin 3) (P : List (Fin 3))
    (hP : IsPal P) (k : ℕ) (hlen : P.length = 2*k+1)
    (contract : ∀ p, 0 < p → HasPeriod P p → 2*k ≤ B*p) :
    k ≤ B*(k + 1 - GalilScaffoldChainInputSupply.chosenRadius (x :: P)) := by
  have hper := fallback_window_period x P hP
  obtain ⟨hle, _⟩ := GalilScaffoldChainInputSupply.chosen_spec (x :: P) (List.cons_ne_nil x P)
  rw [List.length_cons, hlen] at hle
  rw [hlen] at hper
  have hp := contract _ (by omega) hper
  have he : 2*k+1+1-2*GalilScaffoldChainInputSupply.chosenRadius (x :: P) =
      2*(k+1-GalilScaffoldChainInputSupply.chosenRadius (x :: P)) := by omega
  rw [he] at hp
  have hmul : B * (2*(k+1-GalilScaffoldChainInputSupply.chosenRadius (x :: P))) =
      2*(B*(k+1-GalilScaffoldChainInputSupply.chosenRadius (x :: P))) := by ring
  rw [hmul] at hp
  omega

/-- Extending a `p`-periodic word one place to the left preserves period `p`
when the new symbol agrees at a later boundary whose offset is a multiple of
`p`.  This is the boundary step used by the long-radius fallback case. -/
theorem hasPeriod_cons_of_boundary {α : Type} (x : α) (P : List α) {p q : ℕ}
    (hp0 : 0 < p) (hp : HasPeriod P p) (hpq : p ∣ q)
    (hq0 : 0 < q) (hq : q ≤ P.length)
    (hboundary : some x = P[q-1]?) : HasPeriod (x :: P) p := by
  intro i hi
  rcases i with _ | i
  · have hp1 : 1 ≤ p := hp0
    have htarget : (x :: P)[p]? = P[p-1]? := by
      rw [show p = (p-1)+1 by omega,List.getElem?_cons_succ]
      congr 2
      omega
    have hqmod : (q - 1) % p = p - 1 := by
      obtain ⟨m, hqm⟩ := hpq
      cases m with
      | zero => simp at hqm; omega
      | succ m =>
        rw [hqm,Nat.mul_succ]
        have he : p*m+p-1 = p*m+(p-1) := by omega
        rw [he,Nat.add_mod]
        simp [Nat.mod_eq_of_lt (by omega)]
    have hread := hasPeriod_getElem?_mod hp (i := q-1) (by omega)
    rw [hqmod] at hread
    rw [Nat.zero_add,List.getElem?_cons_zero,htarget]
    exact hboundary.trans hread.symm
  · simp only [List.length_cons] at hi
    rw [List.getElem?_cons_succ,
      show i+1+p = (i+p)+1 by omega,List.getElem?_cons_succ]
    exact hp i (by omega)

/-- The long-radius half of Galil's move argument.  `2*h` is the retained
least period, while `2*d` is the fallback period.  If the move were shorter
than a quarter-radius, Fine--Wilf would force `2*h ∣ 2*d`; the boundary symbol
would then extend period `2*h` across the mismatch, a contradiction. -/
theorem galil_move_of_minimal_period_boundary (x : Fin 3) (P : List (Fin 3))
    (k h d : ℕ) (hlen : P.length = 2*k+1)
    (hh0 : 0 < h) (hhk : 2*h ≤ k)
    (hperiod : HasPeriod P (2*h))
    (hminimal : ∀ p, 0 < p → p < 2*h → ¬ HasPeriod P p)
    (hd0 : 0 < d) (hdlen : 2*d ≤ P.length)
    (hdperiod : HasPeriod P (2*d))
    (hboundary : some x = P[2*d-1]?)
    (hbreak : ¬ HasPeriod (x :: P) (2*h)) :
    k ≤ 4*d := by
  by_contra hmove
  have hlong : 4*d < k := by omega
  let g := Nat.gcd (2*d) (2*h)
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ (by omega)
  have hfw : HasPeriod P g := by
    apply fineWilf hdperiod hperiod (by omega) (by omega)
    rw [hlen]
    have hg_le : g ≤ 2*d := Nat.gcd_le_left _ (by omega)
    omega
  have hgh : 2*h ≤ g := by
    by_contra hn
    exact hminimal g hg0 (by omega) hfw
  have hgle : g ≤ 2*h := Nat.gcd_le_right _ (by omega)
  have hgeq : g = 2*h := by omega
  have hdiv : 2*h ∣ 2*d := by
    have := Nat.gcd_dvd_left (2*d) (2*h)
    rwa [← hgeq]
  apply hbreak
  exact hasPeriod_cons_of_boundary x P (by omega) hperiod hdiv (by omega)
    hdlen hboundary

/-- Packaged long-radius move lemma for the actual fallback choice.  The
chosen prefix supplies both period `2*d` and its boundary symbol; callers only
have to show that the retained period does not extend across the mismatch. -/
theorem galil_move_of_minimal_period_break (x : Fin 3) (P : List (Fin 3))
    (hP : IsPal P) (k h : ℕ) (hlen : P.length = 2*k+1)
    (hh0 : 0 < h) (hhk : 2*h ≤ k)
    (hperiod : HasPeriod P (2*h))
    (hminimal : ∀ p, 0 < p → p < 2*h → ¬ HasPeriod P p)
    (hbreak : ¬ HasPeriod (x :: P) (2*h)) :
    k ≤ 4*(k+1-GalilScaffoldChainInputSupply.chosenRadius (x :: P)) := by
  let r := GalilScaffoldChainInputSupply.chosenRadius (x :: P)
  let d := k+1-r
  by_cases hr0 : r = 0
  · simp only [r] at hr0
    rw [hr0]
    omega
  obtain ⟨hle,-⟩ := GalilScaffoldChainInputSupply.chosen_spec
    (x :: P) (List.cons_ne_nil x P)
  have hrk : r ≤ k := by
    rw [List.length_cons,hlen] at hle
    omega
  have hd0 : 0 < d := by simp only [d]; omega
  have hdlen : 2*d ≤ P.length := by simp only [d]; rw [hlen]; omega
  have hdperiod : HasPeriod P (2*d) := by
    simpa only [d,r,hlen,show 2*k+1+1-2*r = 2*(k+1-r) by omega] using
      fallback_window_period x P hP
  have hboundary : some x = P[2*d-1]? := by
    simpa only [d,r,hlen,show 2*k+1+1-2*r-1 = 2*(k+1-r)-1 by omega] using
      fallback_window_boundary x P hP (by simpa only [r] using
        (show 0 < r from Nat.pos_of_ne_zero hr0))
  have hm := galil_move_of_minimal_period_boundary x P k h d hlen hh0 hhk
    hperiod hminimal hd0 hdlen hdperiod hboundary hbreak
  simpa only [d,r] using hm

#print axioms galil_move_of_scaledContract

#print axioms fallback_window_period
#print axioms galil_move_of_contract
#print axioms galil_move_of_weakContract

#print axioms hasPeriod_of_isPal_take
#print axioms window_hasPeriod_of_chosen

end PalPeg
