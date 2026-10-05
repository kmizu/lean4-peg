import MacroPeg.HigherOrder.Mach.LitLen
import MacroPeg.HigherOrder.Mach.DecideT
import MacroPeg.HigherOrder.Mach.EvalCostBound

/-!
# The sizes of the final reading state, in the number of bits

For the bits `w` (`n = |w|`) and the final state `st = finalSt (ofBits w)`: every table has at most
`(4n+1)(n+2)` entries (`fin_tsize`), there are at most `4n+1` items (`fin_items`), and the encodings of the bodies,
the start and the literals are polynomially long, with entries below `itemValBound n + tsize + 13`
(`fin_encBodies`, `fin_encItems`, `fin_encLits`).
-/

namespace Shallot.MacroPeg.Mach

open Shallot.MacroPeg.HO
open Shallot.MacroPeg.Flat

/-- The size bound `(4n+1)(n+2)`. -/
def finS (n : Nat) : Nat := (4 * n + 1) * (n + 2)

theorem finS_mono {m n : Nat} (h : m ≤ n) : finS m ≤ finS n :=
  Nat.mul_le_mul (by omega) (by omega)

theorem fin_tsize (w : List Bool) : tsize (finalSt (Complexity.ofBits w)) ≤ finS w.length :=
  Nat.le_trans (finalSt_tsize_le _) (finS_mono (ofBits_length_le w))

theorem fin_items (w : List Bool) :
    (finalSt (Complexity.ofBits w)).bodies.flatten.length + (finalSt (Complexity.ofBits w)).start.length ≤
      4 * w.length + 1 := by
  have := finalSt_items_le (Complexity.ofBits w)
  have := ofBits_length_le w
  omega

theorem encBodies_length (bodies : List (List MItem)) :
    (encBodies bodies).length = 4 * bodies.flatten.length + bodies.length := by
  induction bodies with
  | nil => simp [encBodies]
  | cons b bodies ih =>
    simp only [encBodies, List.flatMap_cons, List.length_append, List.flatten_cons, List.length_cons,
      List.length_nil] at ih ⊢
    rw [encItems_length]; omega

theorem fin_encBodies_length (w : List Bool) :
    (encBodies (finalSt (Complexity.ofBits w)).bodies).length ≤ 4 * (4 * w.length + 1) + finS w.length := by
  rw [encBodies_length]
  have h₁ := fin_items w
  have h₂ := fin_tsize w
  simp only [tsize] at h₂
  omega

theorem fin_encItems_length (w : List Bool) :
    (encItems (finalSt (Complexity.ofBits w)).start).length ≤ 4 * (4 * w.length + 1) := by
  rw [encItems_length]
  have := fin_items w
  omega

end Shallot.MacroPeg.Mach
