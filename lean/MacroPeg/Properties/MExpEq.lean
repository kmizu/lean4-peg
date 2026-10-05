import MacroPeg.Syntax

/-!
# Decidable equality of Macro PEG expressions

`deriving DecidableEq` does not apply to `MExp` (a nested inductive through `List`), so equality is decided by a
hand-written Boolean comparison `MExp.beqE` (mutual with its list version `MExp.beqArgs`), and `MExp.beqE_iff` shows
it is exactly equality. The defunctionalization (`Defun.lean`) needs this to find a lambda in a finite list.
-/

namespace Shallot.MacroPeg

mutual
  /-- Structural Boolean equality of expressions. -/
  def MExp.beqE : MExp → MExp → Bool
    | .eps, .eps => true
    | .any, .any => true
    | .chr c, .chr d => c == d
    | .range a b, .range c d => a == c && b == d
    | .lit s, .lit t => s == t
    | .param k, .param l => k == l
    | .call i as, .call j bs => i == j && MExp.beqArgs as bs
    | .seq a b, .seq c d => MExp.beqE a c && MExp.beqE b d
    | .alt a b, .alt c d => MExp.beqE a c && MExp.beqE b d
    | .star a, .star b => MExp.beqE a b
    | .notP a, .notP b => MExp.beqE a b
    | .dbg a, .dbg b => MExp.beqE a b
    | .lam n a, .lam m b => n == m && MExp.beqE a b
    | .callParam k as, .callParam l bs => k == l && MExp.beqArgs as bs
    | .invoke n a as, .invoke m b bs => n == m && MExp.beqE a b && MExp.beqArgs as bs
    | _, _ => false

  /-- Structural Boolean equality of argument lists. -/
  def MExp.beqArgs : List MExp → List MExp → Bool
    | [], [] => true
    | a :: as, b :: bs => MExp.beqE a b && MExp.beqArgs as bs
    | _, _ => false
end

mutual
  theorem MExp.beqE_iff : ∀ (a b : MExp), MExp.beqE a b = true ↔ a = b
    | .eps, b | .any, b | .chr _, b | .range _ _, b | .lit _, b | .param _, b => by
      cases b <;> simp [MExp.beqE]
    | .call i as, b => by
      cases b <;> simp [MExp.beqE, MExp.beqArgs_iff as]
    | .seq a₁ a₂, b | .alt a₁ a₂, b => by
      cases b <;> simp [MExp.beqE, MExp.beqE_iff a₁, MExp.beqE_iff a₂]
    | .star a, b | .notP a, b | .dbg a, b => by
      cases b <;> simp [MExp.beqE, MExp.beqE_iff a]
    | .lam n a, b => by
      cases b <;> simp [MExp.beqE, MExp.beqE_iff a]
    | .callParam k as, b => by
      cases b <;> simp [MExp.beqE, MExp.beqArgs_iff as]
    | .invoke n a as, b => by
      cases b <;> simp [MExp.beqE, MExp.beqE_iff a, MExp.beqArgs_iff as, Bool.and_assoc]

  theorem MExp.beqArgs_iff : ∀ (as bs : List MExp), MExp.beqArgs as bs = true ↔ as = bs
    | [], bs => by cases bs <;> simp [MExp.beqArgs]
    | a :: as, bs => by
      cases bs <;> simp [MExp.beqArgs, MExp.beqE_iff a, MExp.beqArgs_iff as]
end

instance : DecidableEq MExp := fun a b => decidable_of_iff _ (MExp.beqE_iff a b)

end Shallot.MacroPeg
