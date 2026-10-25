import MacroPeg.CBV.SequentialPositionEvaluator
import MacroPeg.CBV.RecursiveFieldProofs

namespace Shallot.MacroPeg.CBV.SequentialLocalExamples
open SequentialLocalClosure SequentialPositionEvaluator
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def chain : MGrammar := ⟨[⟨0,.call 1 []⟩,⟨0,.call 2 []⟩,⟨0,.eps⟩]⟩
def bottom : SequentialClock.Table := fun _ _ => []

theorem rule_count_rounds_can_be_needed :
    rounds chain [] 0 bottom 2 ⟨0,by decide⟩=none ∧
    saturated chain [] 0 bottom ⟨0,by decide⟩=some (some 0) ∧
    decide chain [] (.call 0 [])=some (some []) := by decide +kernel

def cycle : MGrammar := ⟨[⟨0,.alt (.call 0 []) .eps⟩]⟩
def negCycle : MGrammar := ⟨[⟨0,.notP (.call 0 [])⟩]⟩
def fails : MGrammar := ⟨[⟨0,MExp.failAlways⟩]⟩
def nullable : MGrammar := ⟨[⟨0,.star .eps⟩]⟩

theorem failure_and_undefined_are_distinct :
    decide cycle ['a'] (.call 0 [])=none ∧
    decide negCycle ['a'] (.call 0 [])=none ∧
    decide fails ['a'] (.call 0 [])=some none ∧
    decide nullable ['a'] (.call 0 [])=none := by decide +kernel

def unary : MGrammar := ⟨[⟨1,.param 0⟩]⟩
theorem positive_call_uses_its_actual_incoming_value :
    decide unary ['a','a'] (.call 0 [.lit ['a']])=some (some []) ∧
    decide unary ['a'] (.call 0 [.lit ['a']])=some none ∧
    decide unary ['a'] (.call 0 [.eps])=some (some ['a']) := by decide +kernel

def wide : MGrammar := ⟨[⟨25,.param 24⟩]⟩
theorem local_vector_does_not_enumerate_parameter_tuples :
    wide.rules.length=1 ∧
    saturated wide ['a'] 1 bottom ⟨0,by decide⟩=some (some 1) ∧
    decide wide ['a'] (.call 0 (List.replicate 25 .eps))=some (some ['a']) := by decide +kernel

theorem invalid_calls_still_fail :
    decide unary ['a'] (.call 2 [])=some none ∧
    decide unary ['a'] (.call 0 [])=some none ∧
    decide unary ['a'] (.param 3)=some none := by decide +kernel

theorem lower_data_at_the_current_position_is_ignored :
    saturated chain [] 0 bottom=
      saturated chain [] 0 (fun _ _ => [some (some 0)]) := by
  exact rounds_lower_agree chain [] 0 (by decide) bottom _
    (by intro i W p; exact okR_none p) (by intro q hq; omega) chain.rules.length

theorem arbitrary_depth_and_fresh_words (n depth : Nat) :
    decide RecursiveFieldExamples.generated (RecursiveFieldExamples.tree n depth)
      RecursiveFieldExamples.generatedRoot=some (some []) := by
  let g := RecursiveFieldExamples.generated
  let x := RecursiveFieldExamples.tree n depth
  let e := RecursiveFieldExamples.generatedRoot
  have hs := (RecursiveFieldProofs.source_and_target_all_trees n depth).2
  have hc : evV g x .callByValueSeq (SequentialLocalCorrectness.canonical g x) [] e x.length=some (some 0) :=
    (SequentialClock.finite_eval_iff g x [] e x.length (Nat.le_refl _) (some 0)).mp ⟨depth+1,hs⟩
  change (match run g x [] e x.length with
    | none => none | some none => some none | some (some q) => some (some (sfx x q)))=_
  rw [run_correct g x [] e _ (Nat.le_refl _),hc]
  simp [sfx]

end Shallot.MacroPeg.CBV.SequentialLocalExamples
