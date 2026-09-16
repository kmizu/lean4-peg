import PalPeg.GalilLiveCentreReplay
import PalPeg.GalilPeriodCentre

/-!
# The leftmost live centre across a chain shift

At the terminal comparison of a round the centre `C` dies at the next place
`n+1`, while `C+h` is live there (`ReadOrigin.reshift_palindrome`). If the
span of the palindrome centred at `C` has no period below `2h`, no live
centre lies strictly between `C` and `C+h`, so `C+h` is the new leftmost
live centre.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open Manacher GalilScaffoldInputHead GalilScaffoldChainVerifier

/-- The span of the palindrome centred at `C` with radius `k` on the encoded word. -/
def Span (raw : List (Fin 2)) (C k : ℕ) : List (Fin 3) := ((encoded raw).drop (C - k)).take (2*k+1)

/-- The chain shift: `C` dies at `n+1`, `C+h` is live, and the span has no
period below `2h`; then `C+h` is the leftmost live centre at `n+1`. -/
theorem leftmost_shift {raw : List (Fin 2)} {n C h : ℕ} (hL : Leftmost raw n C)
    (hdead : ¬ Live raw (n+1) C) (hlive : Live raw (n+1) (C+h))
    (hmin : ∀ p, 0 < p → p < 2*h → ¬ HasPeriod (Span raw C (n - C)) p) :
    Leftmost raw (n+1) (C+h) := by
  refine ⟨hlive, fun c hc => ?_⟩
  by_cases hcn : c ≤ n
  · have hlivec := live_pred hc hcn
    have hCc := hL.2 c hlivec
    have hne : c ≠ C := fun e => hdead (e ▸ hc)
    have hlt : C < c := Nat.lt_of_le_of_ne hCc (fun e => hne e.symm)
    have h1 : PalAt (encoded raw) C (n - C) := hL.1.2.2
    have h2 : PalAt (encoded raw) c (C + (n - C) - c) := by
      have e : C + (n - C) - c = n - c := by have := hL.1.1; omega
      rw [e]; exact hlivec.2.2
    exact no_centre_below_period h1 h2 hlt (by have := hL.1.1; omega) hmin
  · have := hlive.1
    omega

/-- The live centre `C+h` at `n+1` from the shifted palindrome of
`ReadOrigin.reshift_palindrome`: centre `C+h`, radius `n+1-(C+h)`, and its
left end stays inside the word since the old span did. -/
theorem live_shift_of_palAt {raw : List (Fin 2)} {n C h : ℕ} (hL : Live raw n C) (hh : 0 < h)
    (hhn : C + h ≤ n + 1) (hp : PalAt (encoded raw) (C + h) (n + 1 - (C + h))) :
    Live raw (n+1) (C+h) := by
  refine ⟨hhn, ?_, hp⟩
  have := hL.2.1
  omega

#print axioms leftmost_shift
#print axioms live_shift_of_palAt

end PalPeg.GalilScaffoldChainInputSupply
