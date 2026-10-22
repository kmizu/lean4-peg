import Shallot.Peg.Packrat.Machine.TM

/-!
# End-to-end certificates for complete stack programs

These instantiate the full-program theorem from the actual bit-input
state, checking success, leftover-input rejection, and both priority cases
involving a looping alternative.
-/

namespace Shallot.Packrat.Machine.EndToEnd

open Complexity

private def chars (b : Bool) : Char := if b then 'b' else 'a'
private def literalG : Grammar := ⟨[.lit ['a']], 0⟩
private def blockedG : Grammar := ⟨[.alt (.nt 0) .eps], 0⟩
private def shortG : Grammar := ⟨[.alt .eps (.nt 0)], 0⟩

example : ∃ S', NHalts (program literalG chars) (nInit (NK literalG) [false]) true S'
    (programCost literalG chars 1) := by
  have ha : fullAccepts literalG ([false].map chars) = true := by decide
  simpa only [ha, List.length_cons, List.length_nil] using program_halts_fullAccepts literalG chars [false]

example : ∃ S', NHalts (program literalG chars) (nInit (NK literalG) [false, true]) false S'
    (programCost literalG chars 2) := by
  have ha : fullAccepts literalG ([false, true].map chars) = false := by decide
  simpa only [ha, List.length_cons, List.length_nil] using program_halts_fullAccepts literalG chars [false, true]

example : ∃ S', NHalts (program blockedG chars) (nInit (NK blockedG) []) false S'
    (programCost blockedG chars 0) := by
  have ha : fullAccepts blockedG ([].map chars) = false := by decide
  simpa only [ha, List.length_nil] using program_halts_fullAccepts blockedG chars []

example : ∃ S', NHalts (program shortG chars) (nInit (NK shortG) []) true S'
    (programCost shortG chars 0) := by
  have ha : fullAccepts shortG ([].map chars) = true := by decide
  simpa only [ha, List.length_nil] using program_halts_fullAccepts shortG chars []

end Shallot.Packrat.Machine.EndToEnd
