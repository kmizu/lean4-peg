import MacroPeg.HigherOrder.Mach.MainCost
import MacroPeg.HigherOrder.KExp.LmTime
import MacroPeg.HigherOrder.KExp.UniformHard

/-!
# The uniform problem is in j-EXPTIME on Turing machines

The stack program `mainP j` decides `UMPEG j` (`mainP_halts`, `numDecideT_iff`). When its steps are below a tower
of height `j` of a polynomial, a Turing machine decides `UMPEG j` within such a tower (`umpeg_kexp_of_cost`), and the steps are
below such a tower (`mainCost_le`): `UMPEG j` is in j-EXPTIME (`umpeg_kexp`), and with `uniform_hard` it is
j-EXPTIME-complete (`umpeg_complete`).
-/

namespace Shallot.MacroPeg.KExp

open Complexity
open Shallot.MacroPeg.HO

/-- **From a tower bound on the steps of `mainP j` to a Turing machine.** -/
theorem umpeg_kexp_of_cost {j : Nat} (hj : 1 ≤ j)
    (hc : ∃ c d : Nat, ∀ w : List Bool, Mach.mainCost j w ≤ tower j (c * (w.length + 1) ^ d)) :
    KEXP j (UMPEG j) := by
  obtain ⟨c, d, hcd⟩ := hc
  refine kexp_of_nprog_time hj (K := Mach.NK) (by decide) (Mach.mainP j) (UMPEG j)
    (fun n => tower j (c * (n + 1) ^ d)) ⟨c, d, fun n => Nat.le_refl _⟩ (fun w => ?_)
  obtain ⟨S', t, ht, hx⟩ := Mach.mainP_halts j w
  exact ⟨t, Mach.numDecideT j w, S', Nat.le_trans ht (hcd w), hx, Mach.numDecideT_iff j hj w⟩

/-- **The uniform problem of order `j` is in j-EXPTIME**, on Turing machines. -/
theorem umpeg_kexp {j : Nat} (hj : 1 ≤ j) : KEXP j (UMPEG j) :=
  umpeg_kexp_of_cost hj (Mach.mainCost_le hj)

/-- **The uniform problem of order `j` is j-EXPTIME-complete**: it is in j-EXPTIME, and every language in
j-EXPTIME reduces to it. -/
theorem umpeg_complete {j : Nat} (hj : 1 ≤ j) : KEXP j (UMPEG j) ∧ ∀ L, KEXP j L → Reduces L (UMPEG j) :=
  ⟨umpeg_kexp hj, fun _ hL => uniform_hard hj hL⟩

end Shallot.MacroPeg.KExp
