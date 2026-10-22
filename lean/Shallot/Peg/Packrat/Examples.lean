import Shallot.Peg.Packrat.Stored

/-!
# Boundary cases for bounded recognition

These kernel-checked computations exercise divergence, priority, missing
rules, semantic failure, and successful parsing with an unconsumed suffix.
-/

namespace Shallot.Packrat.Examples

private def leftLoop : Grammar := ⟨[.nt 0], 0⟩
private def emptyStar : Grammar := ⟨[.star .eps], 0⟩
private def blocked : Grammar := ⟨[.alt (.nt 0) .eps], 0⟩
private def shortCircuit : Grammar := ⟨[.alt .eps (.nt 0)], 0⟩
private def greedy : Grammar := ⟨[.star (.chr 'a')], 0⟩

example : storedParse leftLoop [] = none := by decide
example : storedParse emptyStar [] = none := by decide
example : storedParse blocked [] = none := by decide
example : storedParse shortCircuit [] = some (some 0) := by decide
example : storedParse ⟨[], 0⟩ [] = some none := by decide
example : storedParse ⟨[.chr 'a'], 0⟩ ['b'] = some none := by decide
example : storedParse ⟨[.lit ['a', 'b']], 0⟩ ['a', 'b', 'c'] = some (some 2) := by decide
example : storedParse greedy ['a', 'b'] = some (some 1) := by decide

/-- Priority does not recover from a divergent first alternative. -/
theorem blocked_no_derivation : ∀ o, ¬ Derives blocked (.nt 0) [] o :=
  storedParse_none_iff.mp (by decide)

/-- Repetition of an empty success has no finite derivation. -/
theorem emptyStar_no_derivation : ∀ o, ¬ Derives emptyStar (.nt 0) [] o :=
  storedParse_none_iff.mp (by decide)

end Shallot.Packrat.Examples
