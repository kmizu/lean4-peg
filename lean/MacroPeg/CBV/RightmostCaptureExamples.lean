import MacroPeg.CBV.SequentialIndexedFutureQueries
import MacroPeg.CBV.SequentialAddressedExamples

namespace Shallot.MacroPeg.CBV.RightmostCaptureExamples

open RightmostCaptureIndex
open SequentialIndexedFutureQueries (run)

/-- One whole-input cell serves every bound. It preserves a copy until the
cursor passes its rightmost start, where all subsequent matches fail. -/
theorem one_cell_for_all_bounds :
    let x := "ab#ab".toList
    let A := table x
    A[address x.length (5,3)]? = some (some (2,0)) ∧
    lookup x.length A 5 (5,3) = some (2,0) ∧
    lookup x.length A 2 (5,3) = some (2,0) ∧
    lookup x.length A 1 (5,3) = none ∧
    indexedMatch x A (5,3) 2 = some (some 0) ∧
    indexedMatch x A (5,3) 1 = some none := by decide +kernel

/-- Passing the last copy makes a value dead, but ordered-choice backtracking
restores the earlier cursor and the same retained value becomes usable again. -/
theorem cursor_restore_revives_value :
    let x := "ab#ab".toList
    let E := [(5,3)]
    run ⟨[]⟩ x 0 E (.seq (.chr 'a') (.notP (.param 0))) 2 = some (some 1) ∧
    run ⟨[]⟩ x 0 E (.alt (.seq (.chr 'a') (.param 0)) (.param 0)) 2 = some (some 0) ∧
    run ⟨[]⟩ x 0 E (.seq (.param 0) (.param 0)) 2 = some none := by decide +kernel

theorem empty_stays_live :
    let x := "ab#ab".toList
    let A := table x
    lookup x.length A 0 (5,5) = some (0,0) ∧
    lookup x.length A 1 (5,5) = some (0,0) ∧
    indexedMatch x A (5,5) 1 = some (some 1) := by decide +kernel

/-- Full-input indexing is essential to this implementation: an equal prefix
can have different rightmost copies depending on the unseen suffix. -/
theorem index_depends_on_suffix :
    (table "ab#ab".toList)[address 5 (5,3)]? = some (some (2,0)) ∧
    (table "ab#cc".toList)[address 5 (5,3)]? = some (some (5,3)) := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem recursive_captures_and_parent :
    let x := "ab!aabb#bbaaba".toList
    run SequentialAddressedExamples.recursive x 2 []
      SequentialAddressedExamples.recursiveStart x.length = some (some 0) ∧
    run SequentialAddressedExamples.recursive x 1 []
      SequentialAddressedExamples.recursiveStart x.length = none := by decide +kernel

theorem actuals_are_preserved :
    let x := "ab#c".toList
    run ⟨[⟨1,.eps⟩]⟩ x 1 [(4,2)] (.call 0 [.param 0]) 1 = some none ∧
    run ⟨[⟨1,.eps⟩]⟩ x 1 [] (.call 0 [.star .eps]) 1 = none ∧
    run ⟨[⟨1,.eps⟩]⟩ x 1 [] (.call 4 [.star .eps]) 1 = some none := by decide +kernel

theorem nullable_star_stays_undefined (x : List Char) (m : Nat) :
    run ⟨[]⟩ x m [] (.star .eps) x.length = none := by
  rw [SequentialIndexedFutureQueries.run_correct _ x m []
    (by intro span hs; cases hs) _ _ (Nat.le_refl _)]
  simp [evV,evStar]

end Shallot.MacroPeg.CBV.RightmostCaptureExamples
