import Shallot.Peg.Packrat.Machine.Sweep

/-!
# Lexical encoding boundary cases

Check the end marker separately from an actual NUL character, rejection
outside a finite test's cutoff, reversed ranges, and literal cursor behavior.
-/

namespace Shallot.Packrat.Machine.Examples

example : inputRow [Char.ofNat 0, 'a'] = [1, 98, 0] := by decide
example : (chrTest (Char.ofNat 0)).eval 0 = false := by decide
example : (chrTest (Char.ofNat 0)).eval 1 = true := by decide
example : (chrTest 'a').eval (symbolCode 'λ') = false := by decide
example : (rangeTest 'z' 'a').eval (symbolCode 'a') = false := by decide
example : (rangeTest 'a' 'z').eval 0 = false := by decide
example : literalScan ['a', 'b'] ['a', 'b', 'c'] 0 = (4, 2) := by decide
example : literalScan ['a', 'b'] ['a', 'c'] 0 = (1, 1) := by decide
example : literalScan ['a', 'b'] ['a'] 0 = (1, 1) := by decide
example : literalScan [] ['a'] 1 = (3, 1) := by decide

end Shallot.Packrat.Machine.Examples
