import PalPeg.GalilPeriodNext

/-!
# No other period survives a break of the minimal period

The old chain certified the minimal period `p` on `[a, b0]`; one place inside `[a, b]` breaks
period `p`.  A period `q` of the longer interval `[a, b]` with `p + q ≤ b0 + 1 - a` is then
impossible: Fine–Wilf gives period `gcd p q` on `[a, b0]`, minimality forces `gcd p q = p`, so
`p ∣ q` and period `p` extends to `[a, b]`, across the break.
-/

set_option autoImplicit false

namespace PalPeg

theorem no_period_across_break {α : Type} {x : List α} {p q a b0 b j : ℕ}
    (hperiod : PeriodOn x p a b0)
    (hminimal : ∀ r, 0 < r → r < p → ¬ PeriodOn x r a b0)
    (hother : PeriodOn x q a b) (hp0 : 0 < p) (hq0 : 0 < q)
    (hb0 : b0 ≤ b) (hb : b < x.length) (hab : a ≤ b0)
    (hlen : p + q ≤ b0 + 1 - a)
    (hj : a ≤ j) (hjb : j + p ≤ b) (hbreak : x[j]? ≠ x[j + p]?) : False := by
  have hotherOld : PeriodOn x q a b0 := hother.mono (le_refl a) hb0
  have hgcd : PeriodOn x (Nat.gcd p q) a b0 :=
    periodOn_fineWilf hperiod hotherOld hp0 hq0 (by omega) hab (by omega)
  have hgcdPos : 0 < Nat.gcd p q := Nat.gcd_pos_of_pos_left q hp0
  have hgcdLe : Nat.gcd p q ≤ p := Nat.gcd_le_left q hp0
  have hgcdEq : Nat.gcd p q = p := by
    rcases Nat.lt_or_eq_of_le hgcdLe with hlt | heq
    · exact absurd hgcd (hminimal _ hgcdPos hlt)
    · exact heq
  have hdvd : p ∣ q := hgcdEq ▸ Nat.gcd_dvd_right p q
  have hextended : PeriodOn x p a b :=
    periodOn_extend_dvd hother hperiod hdvd hp0 hq0 hb ⟨le_refl a, hb0⟩ (by omega)
  exact hbreak (hextended j hj hjb)

end PalPeg
