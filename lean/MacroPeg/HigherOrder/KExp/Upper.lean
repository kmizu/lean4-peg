import MacroPeg.HigherOrder.Mach.MainRun
import MacroPeg.HigherOrder.KExp.LmTime
import MacroPeg.HigherOrder.KExp.UniformHard

/-!
# The uniform problem is in j-EXPTIME on Turing machines

The stack program `mainP j` decides `UMPEG j` (`mainP_halts`, `numDecideT_iff`). When its steps are below a tower
of height `j` of a polynomial, a Turing machine decides `UMPEG j` within such a tower (`umpeg_kexp_of_cost`).
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

end Shallot.MacroPeg.KExp
