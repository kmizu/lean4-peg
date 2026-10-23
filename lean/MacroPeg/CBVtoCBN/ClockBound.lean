import MacroPeg.CBVtoCBN.CounterStep
import MacroPeg.CBVtoCBN.SpanValues

namespace Shallot.MacroPeg.CBVtoCBN

/-- Least-significant digit first, in base `n+1`. Every digit fits on the original input. -/
def clockValue (n : Nat) : List Nat → Nat
  | [] => 0
  | digit :: ds => digit + (n + 1) * clockValue n ds

/-- The number of digits depends only on the source grammar and its maximum arity. -/
def clockDigits (g : MGrammar) (K : Nat) : Nat := g.rules.length + (K + K + 1)

theorem fullClock_value (n d : Nat) : clockValue n (List.replicate d n) + 1 = (n + 1) ^ d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    simp only [List.replicate_succ, clockValue, Nat.pow_succ]
    rw [← ih, Nat.mul_add, Nat.mul_one]
    have hc : (clockValue n (List.replicate d n) + 1) * (n + 1) =
        (n + 1) * (clockValue n (List.replicate d n) + 1) := Nat.mul_comm _ _
    simp only [Nat.mul_add, Nat.mul_one] at hc
    omega

/-- On every nonempty input, a fixed tuple of input-bounded digits dominates the CBV table iteration bound.
The empty input must be handled separately by the final translation. -/
theorem fullClock_sufficient (g : MGrammar) (x : List Char) (K : Nat)
    (hK : ∀ rule ∈ g.rules, rule.arity ≤ K) (hx : 0 < x.length) :
    iterBoundV g x ≤ clockValue x.length (List.replicate (clockDigits g K) x.length) := by
  have he : ((x.length + 1) * (x.length + 1)) ^ K * (x.length + 1) =
      (x.length + 1) ^ (K + K + 1) := by
    rw [Nat.mul_pow, ← Nat.pow_add, ← Nat.pow_succ]
  have hc : g.rules.length < (x.length + 1) ^ g.rules.length := Nat.lt_pow_self (by omega)
  have hp := Nat.mul_lt_mul_of_pos_right hc
    (Nat.pow_pos (n := K + K + 1) (show 0 < x.length + 1 by omega))
  rw [← Nat.pow_add] at hp
  have hi := iterBoundV_le g x hK
  rw [he] at hi
  have hv := fullClock_value x.length (clockDigits g K)
  unfold clockDigits at hv ⊢
  omega

/-- The clock bound reaches exactly the same finite observations as the saturated source evaluator.
This holds for either CBV strategy, including explicit failure as well as success. -/
theorem fullClock_eval_iff (g : MGrammar) (x : List Char) (s : Strategy) (K : Nat)
    (hK : ∀ rule ∈ g.rules, rule.arity ≤ K) (hx : 0 < x.length)
    (e : MExp) (p : Nat) (hp : p ≤ x.length) (v : Option Nat) :
    evV g x s (tblV g x s (clockValue x.length (List.replicate (clockDigits g K) x.length))) [] e p = some v ↔
      ∃ m, evV g x s (tblV g x s m) [] e p = some v := by
  constructor
  · intro h; exact ⟨_, h⟩
  · intro h
    exact evV_lift (fullClock_sufficient g x K hK hx) ((tblV_stable g x s hp).mp h)

end Shallot.MacroPeg.CBVtoCBN
