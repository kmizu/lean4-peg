import MacroPeg.CBV.SequentialAddressedEvaluator
import MacroPeg.CBV.SequentialFiniteExamples

namespace Shallot.MacroPeg.CBV.SequentialAddressedExamples

open SequentialAddressedEvaluator

theorem independent_values_at_one_position :
    let g := SequentialFiniteExamples.grammar
    let x := SequentialFiniteExamples.input
    query g x.length (rows g x 1) 0 [(5,4),(4,3)] 3 = some (some 0) ∧
    query g x.length (rows g x 1) 0 [(6,4),(4,3)] 3 = some none ∧
    run g x 1 [] SequentialFiniteExamples.start x.length = some (some 0) := by decide +kernel

def recursive : MGrammar := ⟨[⟨2,
  .alt (.seq (.chr '#') (.seq (.param 1) (.param 0)))
    (.seq (.chr '!')
      (.seq (.call 0 [.seq (.param 0) (.param 0), .seq (.param 1) (.param 1)])
        (.seq (.param 1) (.param 0))))⟩]⟩

def recursiveStart : MExp := .call 0 [.chr 'a', .chr 'b']

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- The child retains aa/bb, then the caller returns to its independent a/b.
The table construction itself uses only numeric environments and addresses. -/
theorem new_captures_and_parent_return :
    let x := "ab!aabb#bbaaba".toList
    run recursive x 2 [] recursiveStart x.length = some (some 0) ∧
    run recursive x 1 [] recursiveStart x.length = none := by decide +kernel

theorem empty_actuals_keep_repeated_endpoints :
    let g : MGrammar := ⟨[⟨2, .seq (.param 1) (.param 0)⟩]⟩
    let x := ['a','a']
    run g x 1 [] (.call 0 [.eps, .chr 'a']) 2 = some (some 0) ∧
    query g x.length (rows g x 1) 0 [(2,2),(2,1)] 1 = some (some 0) := by decide +kernel

theorem nullable_star_stays_undefined (x : List Char) (m : Nat) :
    run ⟨[]⟩ x m [] (.star .eps) x.length = none := by
  rw [run_correct _ _ _ [] (by intro span hs; cases hs) _ _ (Nat.le_refl _)]
  simp [evStar, evV]

/-- Bad rule indices and wrong arities never evaluate their undefined actuals. -/
theorem invalid_call_preflight :
    let g : MGrammar := ⟨[⟨1, .eps⟩]⟩
    run g ['a'] 1 [] (.call 4 [.star .eps]) 1 = some none ∧
    run g ['a'] 1 [] (.call 0 [.star .eps, .eps]) 1 = some none := by decide +kernel

end Shallot.MacroPeg.CBV.SequentialAddressedExamples
