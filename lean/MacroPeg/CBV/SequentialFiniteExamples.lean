import MacroPeg.CBV.SequentialFiniteEvaluator

namespace Shallot.MacroPeg.CBV.SequentialFiniteExamples

open SequentialFiniteEvaluator SequentialFiniteRows

def grammar : MGrammar :=
  ⟨[⟨2, .seq (.chr '#') (.seq (.param 1) (.param 0))⟩]⟩

def input : List Char := "aab#ba".toList
def start : MExp := .seq (.chr 'a') (.call 0 [.chr 'a', .chr 'b'])

/-- The two adjacent captures are independently retained and read in the
opposite order. Another adjacent tuple at exactly the same callee position
has a different real result; emptiness-only finite control would not suffice. -/
theorem independent_values_at_one_position :
    lookup input (cells grammar input 1) 0 [['a'],['b']] 3 = some (some 0) ∧
    lookup input (cells grammar input 1) 0 [['a','a'],['b']] 3 = some none ∧
    run grammar input 1 [] start input.length = some (some 0) := by decide

theorem key_width : (SequentialTupleKeys.keys grammar input.length).length = 343 := by
  rw [SequentialTupleKeys.keys_length]
  rfl

/-- Nonempty tuples at the original origin are not Seq-created call tuples.
The compressed table is intentionally not an oracle for such arbitrary
queries, although expression evaluation in arbitrary incoming environments
is covered by run_correct. -/
theorem arbitrary_nonadjacent_query_is_not_a_stored_row :
    let g : MGrammar := ⟨[⟨1, .param 0⟩]⟩
    valAt (tblV g ['a'] .callByValueSeq 1 0 [['a']]) 1 = some (some 0) ∧
    lookup ['a'] (cells g ['a'] 1) 0 [['a']] 1 = none := by decide

end Shallot.MacroPeg.CBV.SequentialFiniteExamples
