import MacroPeg.CBV.SequentialTotalLanguage
import MacroPeg.CBV.SequentialLocalExamples
import MacroPeg.CBV.SequentialResultExamples

/-! Concrete kernel checks and symbolic clients of the unrestricted
totalization and original-string complement theorems. -/
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

def complementEval (g : MGrammar) (e : MExp) (x : List Char) (k : Nat) : Res :=
  evV (target g) x .callByValueSeq (tblV (target g) x .callByValueSeq k) []
    (SequentialTotalLanguage.complementStart g e) x.length

theorem complement_checks_full_consumption :
    complementEval ⟨[]⟩ (.chr 'a') ['a'] 0=some none ∧
    complementEval ⟨[]⟩ (.chr 'a') ['a','b'] 0=some (some 0) ∧
    complementEval ⟨[]⟩ (.chr 'a') [] 0=some (some 0) ∧
    complementEval ⟨[]⟩ .eps [] 0=some none ∧
    complementEval ⟨[]⟩ .eps ['a'] 0=some (some 0) := by decide +kernel

theorem cycle_complement_all_strings (x : List Char) :
    SObs (target SequentialResultExamples.cycle) .callByValueSeq
      (SequentialTotalLanguage.complementStart SequentialResultExamples.cycle (.call 0 [])) x (some []) := by
  apply (SequentialTotalLanguage.complement_recognizes _ SequentialResultExamples.cycle_firstOrder _ (by trivial) x).mpr
  intro h
  have hs := SequentialTotalCompiler.canonical_success_iff _ SequentialResultExamples.cycle_firstOrder
    (.call 0 []) (by trivial) x 0 (by omega)
  simp only [sfx,Nat.sub_zero,List.drop_length] at hs
  have hv := hs.mpr h
  have hu := SequentialResultExamples.cycle_undefined x
    (SequentialLocalCorrectness.clock SequentialResultExamples.cycle x) x.length (Nat.le_refl _)
  simp only [SequentialLocalCorrectness.canonical] at hv
  rw [hu] at hv
  cases hv

theorem arbitrary_depth_fresh_values_and_parent_return (n depth : Nat) :
    let g := RecursiveFieldExamples.generated
    let e := RecursiveFieldExamples.generatedRoot
    let x := RecursiveFieldExamples.tree n depth
    evV (target g) x .callByValueSeq
      (tblV (target g) x .callByValueSeq (SequentialLocalCorrectness.clock (target g) x)) []
      (start g e) x.length=some (some 0) := by
  intro g e x
  have hfo := RecursiveFieldCompiler.firstOrder RecursiveFieldExamples.original RecursiveFieldExamples.root [] 2 '#'
    RecursiveFieldExamples.pattern RecursiveFieldExamples.body RecursiveFieldExamples.root RecursiveFieldExamples.checked
  have hg : g.FirstOrder := hfo.2.2.1
  have he : e.FirstOrder := hfo.2.2.2
  have hs := (RecursiveFieldProofs.source_and_target_all_trees n depth).2
  have hc := (SequentialClock.finite_eval_iff g x [] e x.length (Nat.le_refl _) (some 0)).mp ⟨depth+1,hs⟩
  change evV g x .callByValueSeq (SequentialLocalCorrectness.canonical g x) [] e x.length=some (some 0) at hc
  have ht := SequentialTotalCorrectness.start_correct g hg x [] e he x.length (Nat.le_refl _)
  rw [hc] at ht
  exact ht

end Shallot.MacroPeg.CBV.SequentialTotalExamples
