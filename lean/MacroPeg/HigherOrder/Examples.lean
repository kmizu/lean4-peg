import MacroPeg.HigherOrder.Semantics

/-!
# Higher-order Macro PEG: examples

Rules (`v0` is the innermost bound variable):

* `twice : (p ⇒ p) ⇒ p ⇒ p = λf. λx. f (f x)` — order 2;
* `a : p ⇒ p = λx. "a" x`;
* `pre : p ⇒ p ⇒ p = λy. λx. y x` — `pre y` is a closure that remembers `y`;
* `twice twice f` applies `f` four times, `twice twice twice f` sixteen times: iterating an order-2 rule gives a tower
  of exponentials, which no first-order grammar of fixed size can do with its argument lists.
-/

namespace Shallot.MacroPeg.HO.Examples

open HExp

def twice : HRule := ⟨(.p ⇒ .p) ⇒ .p ⇒ .p, lam (.p ⇒ .p) (lam .p (app (var 1) (app (var 1) (var 0))))⟩
def aRule : HRule := ⟨.p ⇒ .p, lam .p (seq (chr 'a') (var 0))⟩
def pre : HRule := ⟨.p ⇒ .p ⇒ .p, lam .p (lam .p (seq (var 1) (var 0)))⟩

def g : HGrammar := ⟨[twice, aRule, pre]⟩

def as (n : Nat) : List Char := List.replicate n 'a'

-- `twice a ε` reads exactly two `a`s.
#guard hrun g 100 (apps (rule 0) [rule 1, eps]) (as 3) = some (some ['a'])
-- A closure: `twice (pre "b") ε` reads `bb`.
#guard hrun g 100 (apps (rule 0) [app (rule 2) (chr 'b'), eps]) "bbc".toList = some (some ['c'])
-- `twice twice a ε` reads four `a`s, `twice twice twice a ε` sixteen.
#guard hrun g 200 (apps (rule 0) [rule 0, rule 1, eps]) (as 5) = some (some ['a'])
#guard hrun g 1000 (apps (rule 0) [rule 0, rule 0, rule 1, eps]) (as 17) = some (some ['a'])
-- Too few `a`s: failure.
#guard hrun g 1000 (apps (rule 0) [rule 0, rule 0, rule 1, eps]) (as 15) = some none
-- Too little fuel: no result.
#guard hrun g 3 (apps (rule 0) [rule 1, eps]) (as 3) = none

/-- The grammar is well typed. -/
example : g.WellTyped := by
  intro r hr
  simp only [g, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact .lam (.lam (.app (.var rfl) (.app (.var rfl) (.var rfl))))
  · exact .lam (.seq (.chr _ _) (.var rfl))
  · exact .lam (.lam (.seq (.var rfl) (.var rfl)))

-- `twice` has order 2.
#guard twice.ty.order = 2
#guard g.order = 2

end Shallot.MacroPeg.HO.Examples
