import MacroPeg.CBV.SequentialTotalSyntax
import MacroPeg.CBV.SequentialLocalExamples

/-! Kernel checks of the unrestricted totalization candidate. These concrete
checks do not replace the missing all-grammars correctness/termination proof. -/
namespace Shallot.MacroPeg.CBV.SequentialTotalExamples
open SequentialTotalSyntax
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def eval (g : MGrammar) (e : MExp) (x : List Char) (k : Nat) : Res :=
  evV (target g) x .callByValueSeq (tblV (target g) x .callByValueSeq k) []
    (start g e) x.length
def flag (g : MGrammar) (e : MExp) (m : Mode) (x : List Char) (k : Nat) : Res :=
  evV (target g) x .callByValueSeq (tblV (target g) x .callByValueSeq k) []
    ((compile g g.rules.length e).get m) x.length

theorem empty_call_chain_is_unrolled :
    eval SequentialLocalExamples.chain (.call 0 []) [] 5=some (some 0) ∧
    (target SequentialLocalExamples.chain).rules.length=60 := by decide +kernel

theorem divergence_does_not_enable_choice_or_negation :
    eval SequentialLocalExamples.cycle (.call 0 []) ['a'] 5=some none ∧
    eval SequentialLocalExamples.cycle (.alt (.call 0 []) .eps) ['a'] 5=some none ∧
    eval SequentialLocalExamples.cycle (.notP (.call 0 [])) ['a'] 5=some none ∧
    flag SequentialLocalExamples.cycle (.call 0 []) .failure ['a'] 5=some none ∧
    eval SequentialLocalExamples.negCycle (.call 0 []) [] 5=some none := by decide +kernel

theorem finite_failure_remains_available_to_source_choice :
    flag SequentialLocalExamples.fails (.call 0 []) .failure ['a'] 5=some (some 1) ∧
    eval SequentialLocalExamples.fails (.alt (.call 0 []) .eps) ['a'] 5=some (some 1) := by decide +kernel

theorem nullable_iteration_does_not_become_success :
    eval ⟨[]⟩ (.star .eps) ['a'] 0=some none ∧
    eval ⟨[]⟩ (.star (.alt (.chr 'a') .eps)) ['a','a'] 0=some none ∧
    flag ⟨[]⟩ (.star (.alt (.chr 'a') .eps)) .failure ['a','a'] 0=some none ∧
    eval ⟨[]⟩ (.star (.chr 'a')) ['a','a'] 0=some (some 0) := by decide +kernel

theorem consuming_actuals_use_the_original_values :
    eval SequentialLocalExamples.unary (.call 0 [.chr 'a']) ['a','a'] 4=some (some 0) ∧
    eval SequentialLocalExamples.unary (.call 0 [.chr 'a']) ['a'] 4=some none ∧
    flag SequentialLocalExamples.unary (.call 0 [.chr 'a']) .zero ['a','a'] 4=some none ∧
    flag SequentialLocalExamples.unary (.call 0 [.chr 'a']) .failure ['a'] 4=some (some 1) ∧
    eval SequentialLocalExamples.unary (.call 0 [.eps]) ['a'] 4=some (some 1) := by decide +kernel

def ignores : MGrammar := ⟨[⟨1,.eps⟩]⟩
theorem consuming_actuals_make_even_an_empty_callee_positive :
    flag ignores (.call 0 [.chr 'a']) .positive ['a'] 4=some (some 0) ∧
    flag ignores (.call 0 [.chr 'a']) .zero ['a'] 4=some none := by decide +kernel

def progress : MGrammar := ⟨[⟨1,.alt (.call 0 [.chr 'a']) .eps⟩]⟩
theorem positive_progress_resets_the_local_stage :
    eval progress (.call 0 [.eps]) ['a','a','a'] 8=some (some 0) := by decide +kernel

def retained : MGrammar := ⟨[⟨1,.alt (.seq (.param 0) (.call 0 [.param 0])) .eps⟩]⟩
theorem retained_actuals_and_parent_backtracking :
    eval retained (.call 0 [.chr 'a']) ['a','a','a','a','a'] 8=some (some 0) ∧
    eval retained (.call 0 [.chr 'a']) ['a','a','a','a'] 8=some (some 1) := by decide +kernel

theorem invalid_calls_skip_their_undefined_actuals :
    flag SequentialLocalExamples.cycle (.call 9 [.call 0 []]) .failure [] 0=some (some 0) ∧
    flag SequentialLocalExamples.cycle (.call 0 [.call 0 []]) .failure [] 0=some (some 0) ∧
    flag ignores (.param 9) .failure ['a'] 0=some (some 1) := by decide +kernel

def two : MGrammar := ⟨[⟨2,.seq (.param 0) (.param 1)⟩]⟩
theorem each_positive_argument_route_retains_separate_values :
    eval two (.call 0 [.eps,.chr 'a']) ['a','a'] 5=some (some 0) ∧
    eval two (.call 0 [.chr 'a',.eps]) ['a','a'] 5=some (some 0) ∧
    eval two (.call 0 [.chr 'a',.chr 'b']) ['a','b','a','b'] 5=some (some 0) := by decide +kernel

def argumentCycle : MGrammar := ⟨[⟨2,.eps⟩,⟨0,.call 1 []⟩]⟩
theorem argument_failure_and_unknown_after_progress_stay_distinct :
    flag argumentCycle (.call 0 [.chr 'a',MExp.failAlways]) .failure ['a'] 5=some (some 1) ∧
    flag argumentCycle (.call 0 [.chr 'a',.call 1 []]) .failure ['a'] 6=some none ∧
    eval argumentCycle (.alt (.call 0 [.chr 'a',.call 1 []]) .eps) ['a'] 6=some none := by decide +kernel

def mutualCalls : MGrammar := ⟨[⟨1,.call 1 [.param 0]⟩,
  ⟨1,.alt (.seq (.param 0) (.call 0 [.param 0])) .eps⟩]⟩
theorem mutual_parameterized_calls_can_progress_or_stay_undefined :
    eval mutualCalls (.call 0 [.chr 'a']) ['a','a','a','a','a'] 12=some (some 0) ∧
    eval mutualCalls (.call 0 [.eps]) ['a'] 12=some none := by decide +kernel

end Shallot.MacroPeg.CBV.SequentialTotalExamples
