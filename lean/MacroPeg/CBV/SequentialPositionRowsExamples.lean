import MacroPeg.CBV.SequentialPositionRows
import MacroPeg.CBV.SequentialAddressedExamples

namespace Shallot.MacroPeg.CBV.SequentialPositionRowsExamples

open SequentialPositionRows

def chain : MGrammar := ⟨[⟨0,.call 1 []⟩,⟨0,.call 2 []⟩,⟨0,.eps⟩]⟩

theorem local_rounds_are_materialized :
    localRounds chain [] 0 #[] 2 ⟨0,by decide⟩ = none ∧
    localRounds chain [] 0 #[] 3 ⟨0,by decide⟩ = some (some 0) ∧
    decide chain [] (.call 0 []) = some (some []) := by decide +kernel

/-- A zero-width actual captures empty, even when its predicate reads a
nonempty caller parameter. Reusing the caller environment would be incorrect. -/
theorem same_position_resets_captures :
    let g : MGrammar := ⟨[⟨1,.param 0⟩]⟩
    run g ['a'] [(1,0)] (.call 0 [.andP (.param 0)]) 1 = some (some 1) ∧
    run g ['a'] [(1,0)] (.call 0 [.param 0]) 1 = some none ∧
    run g ['a'] [] (.call 0 [.eps]) 1 = some (some 1) := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem recursive_captures_and_parent :
    let x := "ab!aabb#bbaaba".toList
    decide SequentialAddressedExamples.recursive x
      SequentialAddressedExamples.recursiveStart = some (some []) := by decide +kernel

theorem failure_and_undefined :
    decide ⟨[⟨0,.alt (.call 0 []) .eps⟩]⟩ ['a'] (.call 0 []) = none ∧
    decide ⟨[⟨0,.notP (.call 0 [])⟩]⟩ ['a'] (.call 0 []) = none ∧
    decide ⟨[⟨0,MExp.failAlways⟩]⟩ ['a'] (.call 0 []) = some none := by decide +kernel

theorem invalid_call_preflight :
    let g : MGrammar := ⟨[⟨1,.eps⟩]⟩
    decide g ['a'] (.call 4 [.star .eps]) = some none ∧
    decide g ['a'] (.call 0 [.star .eps,.eps]) = some none := by decide +kernel

theorem nullable_star_stays_undefined (x : List Char) :
    decide ⟨[]⟩ x (.star .eps) = none := by
  unfold SequentialPositionRows.decide
  rw [run_correct _ _ [] (by intro span hs; cases hs) _ _ (Nat.le_refl _)]
  simp [evV,evStar]

end Shallot.MacroPeg.CBV.SequentialPositionRowsExamples
