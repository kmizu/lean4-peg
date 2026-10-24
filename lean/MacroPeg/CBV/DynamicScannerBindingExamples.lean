import MacroPeg.CBV.DynamicScannerBinding
import MacroPeg.CBV.StatefulActionExamples

namespace Shallot.MacroPeg.CBV.DynamicScannerBindingExamples
open DynamicScannerBinding
open DynamicScannerCapture (observer)
open DependentCaptureFilter (render)

abbrev machine := StatefulActionExamples.machine
def tail : MExp := .seq (.lit ['!']) (.param 0)
def source : MGrammar := ⟨[⟨1,.seq (.call 1 []) tail⟩] ++
  StatefulScanner.block machine (fun _ => true) 1⟩
def argument : Arg := .star (.lit ['a'])
def output := target [] machine 0 (fun _ => tail)
def start := entry [] machine [] argument

private theorem no_nodes : RegularCaptureProduct.Valid [] := by
  intro e he; cases he
private theorem no_values : DependentCaptureFilter.Accurate (observer machine) [] [] := by
  intro i w h; cases i <;> cases h

/-- The same generated grammar binds an odd or even capture in a different
profile row, resumes the right scanner, and then replays the entire value. -/
theorem odd_even_binding :
    evV source "abb!a".toList .callByValuePar (tblV source "abb!a".toList .callByValuePar 8)
      [] (.call 0 [render argument]) 5=some (some 0) ∧
    evV output "abb!a".toList .callByValueSeq
      (rounds [] machine 0 (fun _ => tail) "abb!a".toList 6) [] start 5=some (some 0) ∧
    evV source "aa!aa".toList .callByValuePar (tblV source "aa!aa".toList .callByValuePar 8)
      [] (.call 0 [render argument]) 5=some (some 0) ∧
    evV output "aa!aa".toList .callByValueSeq
      (rounds [] machine 0 (fun _ => tail) "aa!aa".toList 6) [] start 5=some (some 0) := by
  refine ⟨by decide +kernel,?_,by decide +kernel,?_⟩
  all_goals
    unfold output start
    rw [entry_step [] no_nodes machine 0 (fun _ => tail) source.rules _ 0 5 [] []
      no_values argument (by trivial) 5 (by decide)]
    decide +kernel

def dependent : Arg := .seq (.param 0) argument
def retained := [['a','c']]
def metadata := retained.map (CaptureTransitionProfile.profile (observer machine))
def parentReturn : MExp := .seq (.lit ['?']) (.param 0)
def parentStart : MExp := .seq (entry [] machine metadata dependent) parentReturn
def parentInput := "acaabb!acaa?ac".toList

/-- New capture acaa differs from retained ac. Both the real callee binding
and the caller environment after return are checked in the generated grammar. -/
theorem whole_capture_and_parent_return :
    evV source parentInput .callByValuePar (tblV source parentInput .callByValuePar 10)
      retained (.seq (.call 0 [render dependent]) parentReturn) parentInput.length=some (some 0) ∧
    evV output parentInput .callByValueSeq
      (rounds [] machine 0 (fun _ => tail) parentInput 6) retained parentStart parentInput.length=some (some 0) := by
  constructor
  · decide +kernel
  · have he : evV output parentInput .callByValueSeq
        (rounds [] machine 0 (fun _ => tail) parentInput 6) retained
        (entry [] machine metadata dependent) parentInput.length=some (some 3) := by
      unfold output
      rw [entry_step [] no_nodes machine 0 (fun _ => tail) source.rules parentInput 0 5 metadata retained
        (DependentCaptureFilter.environment_accurate _ retained) dependent (by trivial) parentInput.length (Nat.le_refl _)]
      decide +kernel
    unfold parentStart
    rw [evV_seq_ok he]
    decide +kernel

theorem short_capture_rejected :
    evV output "abb!".toList .callByValueSeq
      (rounds [] machine 0 (fun _ => tail) "abb!".toList 6) [] start 4=some none ∧
    evV output "aa!a".toList .callByValueSeq
      (rounds [] machine 0 (fun _ => tail) "aa!a".toList 6) [] start 4=some none := by
  constructor
  all_goals
    unfold output start
    rw [entry_step [] no_nodes machine 0 (fun _ => tail) source.rules _ 0 5 [] []
      no_values argument (by trivial) 4 (by decide)]
    decide +kernel

theorem actual_resumption_states :
    resume (CaptureTransitionProfile.profile (observer machine) ['a']) (0 : Fin 2)=some 1 ∧
    resume (CaptureTransitionProfile.profile (observer machine) ['a','a']) (0 : Fin 2)=some 0 := by
  decide +kernel

theorem original_string_observations :
    SObs output .callByValueSeq start "abb!a".toList (some []) ∧
    SObs output .callByValueSeq start "aa!aa".toList (some []) := by
  constructor
  · exact (observations_iff [] no_nodes machine 0 (fun _ => tail) (fun _ _ => by trivial)
      "abb!a".toList argument (some [])).mpr ⟨6,some 0,odd_even_binding.2.1,by decide⟩
  · exact (observations_iff [] no_nodes machine 0 (fun _ => tail) (fun _ _ => by trivial)
      "aa!aa".toList argument (some [])).mpr ⟨6,some 0,odd_even_binding.2.2.2,by decide⟩

/-- The new value and the restored parent are also checked at an ordinary
physical table, using the proved bound rather than an analytic scan oracle. -/
theorem physical_parent_return : ∃ clock,
    evV output parentInput .callByValueSeq (tblV output parentInput .callByValueSeq clock)
      retained parentStart parentInput.length=some (some 0) := by
  exact ⟨_,physical [] machine 0 (fun _ => tail) parentInput 6 retained parentStart
    parentInput.length (some 0) whole_capture_and_parent_return.2⟩

def committedBody (P : List Nat) : MExp :=
  if resume P (0 : Fin 2)=some 0 then tail else .lit ['Z']

theorem committed_binding :
    evV (target [] machine 0 committedBody) "aa!aa".toList .callByValueSeq
      (rounds [] machine 0 committedBody "aa!aa".toList 6) []
      (entry [] machine [] (.alt (.lit ['a']) (.lit ['a','a']))) 5=some none ∧
    evV (target [] machine 0 committedBody) "aa!aa".toList .callByValueSeq
      (rounds [] machine 0 committedBody "aa!aa".toList 6) []
      (entry [] machine [] (.lit ['a','a'])) 5=some (some 0) := by
  constructor
  all_goals
    rw [entry_step [] no_nodes machine 0 committedBody source.rules _ 0 5 [] []
      no_values _ (by trivial) 5 (by decide)]
    decide +kernel

theorem undefined_argument_all_physical (clock : Nat) :
    evV output ['!'] .callByValueSeq (tblV output ['!'] .callByValueSeq clock) []
      (entry [] machine [] (.star (.lit []))) 1=none := by
  exact entry_undefined [] no_nodes machine 0 (fun _ => tail) source.rules ['!'] 0 [] [] no_values
    (.star (.lit [])) (by trivial) 1 (by decide) (by decide +kernel) clock

def childArgument : Arg := .seq (.param 0) (.lit ['a'])
def recursiveBody (P : List Nat) : MExp :=
  .alt tail (.seq (.lit ['Z']) (.seq (entry [] machine [P] childArgument)
    (.seq (.lit ['?']) (.param 0))))
def recursiveSource : MGrammar := ⟨[⟨1,.seq (.call 1 [])
  (.alt tail (.seq (.lit ['Z']) (.seq (.call 0 [render childArgument])
    (.seq (.lit ['?']) (.param 0)))))⟩] ++ StatefulScanner.block machine (fun _ => true) 1⟩
def recursiveTarget := target [] machine 0 recursiveBody
def recursiveInput := ("abZ"++"aaZ"++"aaab!aaa"++"?aa?a").toList

/-- The generated profile variants can call the same logical user again.
Captures a → aa → aaa change the actual metadata and resumption 1 → 0 → 1;
returning then reuses the whole aa and a values in their own environments. -/
theorem recursive_rebinding :
    evV recursiveSource recursiveInput .callByValuePar
      (tblV recursiveSource recursiveInput .callByValuePar 12) []
      (.call 0 [render argument]) recursiveInput.length=some (some 0) ∧
    evV recursiveTarget recursiveInput .callByValueSeq
      (rounds [] machine 0 recursiveBody recursiveInput 9) [] start recursiveInput.length=some (some 0) := by
  constructor
  · decide +kernel
  · unfold recursiveTarget start
    rw [entry_step [] no_nodes machine 0 recursiveBody recursiveSource.rules recursiveInput 0 8 [] []
      no_values argument (by trivial) recursiveInput.length (Nat.le_refl _)]
    decide +kernel

theorem recursive_physical : ∃ clock,
    evV recursiveTarget recursiveInput .callByValueSeq
      (tblV recursiveTarget recursiveInput .callByValueSeq clock) [] start recursiveInput.length=some (some 0) := by
  exact ⟨_,physical [] machine 0 recursiveBody recursiveInput 9 [] start
    recursiveInput.length (some 0) recursive_rebinding.2⟩

theorem recursive_body_firstOrder (P : List Nat) : (recursiveBody P).FirstOrder := by
  exact ⟨⟨True.intro,True.intro⟩,⟨True.intro,
    ⟨DependentProfileCall.entry_firstOrder [] (observer machine) [P] childArgument,
      ⟨True.intro,True.intro⟩⟩⟩⟩

theorem recursive_observation :
    SObs recursiveTarget .callByValueSeq start recursiveInput (some []) := by
  exact (observations_iff [] no_nodes machine 0 recursiveBody (fun P _ => recursive_body_firstOrder P)
    recursiveInput argument (some [])).mpr ⟨9,some 0,recursive_rebinding.2,by decide⟩

theorem recursive_short_copies :
    ∀ x∈["abZaaZaaab!aa?aa?a".toList,"abZaaZaaab!aaa?a?a".toList,"abZaaZaaab!aaa?aa?".toList],
    evV recursiveSource x .callByValuePar (tblV recursiveSource x .callByValuePar 12) []
      (.call 0 [render argument]) x.length=some none ∧
    evV recursiveTarget x .callByValueSeq (rounds [] machine 0 recursiveBody x 9)
      [] start x.length=some none := by
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl
  all_goals
    constructor
    · decide +kernel
    · unfold recursiveTarget start
      rw [entry_step [] no_nodes machine 0 recursiveBody recursiveSource.rules _ 0 8 [] []
        no_values argument (by trivial) _ (Nat.le_refl _)]
      decide +kernel

/-- The boundary is material: when a capture crosses the original scan's
stopping point, the generated entry rejects although the source can accept.
This limits the construction; it is not a language-class separation. -/
theorem frontier_boundary :
    StatefulScanner.advance machine 0 ['a','!']=none ∧
    evV source "a!a!".toList .callByValuePar (tblV source "a!a!".toList .callByValuePar 8)
      [] (.call 0 [.lit ['a','!']]) 4=some (some 0) ∧
    evV output "a!a!".toList .callByValueSeq
      (rounds [] machine 0 (fun _ => tail) "a!a!".toList 6) []
      (entry [] machine [] (.lit ['a','!'])) 4=some none := by
  refine ⟨by decide +kernel,by decide +kernel,?_⟩
  unfold output
  rw [entry_step [] no_nodes machine 0 (fun _ => tail) source.rules _ 0 5 [] []
    no_values _ (by trivial) 4 (by decide)]
  decide +kernel

end Shallot.MacroPeg.CBV.DynamicScannerBindingExamples
