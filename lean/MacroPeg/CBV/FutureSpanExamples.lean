import MacroPeg.CBV.SequentialFutureQueries
import MacroPeg.CBV.SequentialAddressedExamples

namespace Shallot.MacroPeg.CBV.FutureSpanExamples

open FutureSpanRepresentatives
open SequentialFutureQueries (run)

/-- Both used values have old origins before the entry, but their replacements
lie entirely inside the remaining suffix. They remain independent fields. -/
theorem independent_future_copies :
    let x := "ab#ab".toList
    normalize x 2 [(5,3),(4,3)] = [some (2,0),some (1,0)] ∧
    run ⟨[]⟩ x 0 [(5,3),(4,3)] (.seq (.notP (.param 1)) (.param 0)) 2 = some (some 0) := by
  decide +kernel

/-- Dead values are really read, under a predicate and as an actual. The
placeholder empty span alone is incorrect; the failure view is essential. -/
theorem dead_is_not_empty :
    let x := "ab#c".toList
    normalize x 1 [(4,2),(4,4)] = [none,some (0,0)] ∧
    run ⟨[]⟩ x 0 [(4,2)] (.param 0) 1 = some none ∧
    run ⟨[]⟩ x 0 [(4,2)] (.notP (.param 0)) 1 = some (some 1) ∧
    run ⟨[⟨1,.eps⟩]⟩ x 1 [(4,2)] (.call 0 [.param 0]) 1 = some none ∧
    SequentialSpanRecompute.eval ⟨[]⟩ x (fun _ _ _ => none)
      (environment (normalize x 1 [(4,2)])) (.param 0) 1 = some (some 1) := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- Every entry selects new future copies; recursive aa/bb captures and the
caller's a/b are restored by the ordinary lexical environment discipline. -/
theorem recursive_captures_and_parent :
    let x := "ab!aabb#bbaaba".toList
    run SequentialAddressedExamples.recursive x 2 []
      SequentialAddressedExamples.recursiveStart x.length = some (some 0) ∧
    run SequentialAddressedExamples.recursive x 1 []
      SequentialAddressedExamples.recursiveStart x.length = none := by
  decide +kernel

theorem nullable_star_stays_undefined (x : List Char) (m : Nat) :
    run ⟨[]⟩ x m [] (.star .eps) x.length = none := by
  rw [SequentialFutureQueries.run_correct (by intro r hr; cases hr) x m []
    (by intro span hs; cases hs) _ (by trivial) _ (Nat.le_refl _)]
  simp [evV,evStar]

theorem invalid_call_preflight :
    let g : MGrammar := ⟨[⟨1,.eps⟩]⟩
    run g ['a'] 1 [] (.call 4 [.star .eps]) 1 = some none ∧
    run g ['a'] 1 [] (.call 0 [.star .eps,.eps]) 1 = some none := by
  decide +kernel

/-- Slot representatives and the body mask cannot be chosen independently. -/
theorem body_mask_matters :
    let x := "ab#c".toList
    let dead := normalize x 1 [(4,2)]
    let empty := normalize x 1 [(4,4)]
    environment dead = environment empty ∧ views dead ≠ views empty := by
  constructor
  · decide +kernel
  · change [MExp.failAlways] ≠ [MExp.param 0]
    simp [MExp.failAlways]

end Shallot.MacroPeg.CBV.FutureSpanExamples
