import MacroPeg.CBV.FragmentConsumingEntry
import MacroPeg.CBV.ControlledFragmentExamples

namespace Shallot.MacroPeg.CBV.FragmentConsumingExamples
open PartialCodewordCapture (look)
open ControlledFragmentReplay (argument)
open ControlledFragmentExamples (source target)
open FragmentConsumingEntry (entry)

def aa : MExp := .seq (.chr 'a') (.chr 'a')
def chosen : MExp := .alt aa (.chr 'a')

theorem chosen_syntax : FragmentConsumingSyntax.Syntax chosen :=
  .alt (.seq .char .char) .char

/-- A mandatory, prioritized consuming fragment is captured in three
pieces and reused as the entire original value. It is not a star. -/
theorem consuming_choice_and_reuse :
    let x := "aaa#aaa#aaX!aaa#aa".toList
    evV source x .callByValuePar (tblV source x .callByValuePar 1) []
      (.call 0 [argument (.lit []) chosen]) x.length=some (some 0) ∧
    evV target x .callByValueSeq (tblV target x .callByValueSeq 1) []
      (entry 2 3 (.lit []) chosen) x.length=some (some 0) := by
  decide +kernel

/-- The later replay failure cannot reopen the successful aa branch and
select a instead, even though doing so would accept this input. -/
theorem choice_commit_rejected :
    let x := "aaa#aaa#aX!aaa#a".toList
    evV source x .callByValuePar (tblV source x .callByValuePar 1) []
      (.call 0 [argument (.lit []) chosen]) x.length=some none ∧
    evV target x .callByValueSeq (tblV target x .callByValueSeq 1) []
      (entry 2 3 (.lit []) chosen) x.length=some none ∧
    evV source x .callByValuePar (tblV source x .callByValuePar 1) []
      (.call 0 [argument (.lit []) (.chr 'a')]) x.length=some (some 0) := by
  decide +kernel

/-- Unlike a star-only fragment, a mandatory fragment may fail before
callee evaluation. Both physical calls preserve this finite failure. -/
theorem mandatory_fragment_failure :
    let x := "#X!".toList
    evV source x .callByValuePar (tblV source x .callByValuePar 1) []
      (.call 0 [argument (.lit []) (.chr 'a')]) x.length=some none ∧
    evV target x .callByValueSeq (tblV target x .callByValueSeq 1) []
      (entry 2 3 (.lit []) (.chr 'a')) x.length=some none := by
  decide +kernel

/-- Finite argument failure is already observable at clock zero; it
must not be collapsed into the missing callee row's None. -/
theorem mandatory_failure_zero :
    let x := "#X!".toList
    evV source x .callByValuePar (tblV source x .callByValuePar 0) []
      (.call 0 [argument (.lit []) (.chr 'a')]) x.length=some none ∧
    evV target x .callByValueSeq (tblV target x .callByValueSeq 0) []
      (entry 2 3 (.lit []) (.chr 'a')) x.length=some none := by
  decide +kernel

/-- A nullable inner loop is encountered before a missing delimiter.
The new syntax retains None rather than turning it into comparison failure. -/
theorem consuming_then_undefined :
    let H := MExp.seq (.chr 'a') (.star .eps)
    let x := "aaZ".toList
    evV source x .callByValuePar (tblV source x .callByValuePar 1) []
      (.call 0 [argument (.lit []) H]) x.length=none ∧
    evV target x .callByValueSeq (tblV target x .callByValueSeq 1) []
      (entry 2 3 (.lit []) H) x.length=none := by
  decide +kernel

theorem recursive_tests_in_consuming_syntax :
    FragmentConsumingSyntax.Syntax
      (.seq (.chr 'a') (.star (.alt
        (.seq (.chr 'a') (look (.call 2 [.param 0])))
        (.seq (.notP (.call 3 [])) (.chr 'a'))))) := by
  exact .seq .char (.star (.alt (.seq .char (.test _ (by simp [MExp.FirstOrder,MExp.FirstOrderArgs])))
    (.seq (.reject _ (by simp [MExp.FirstOrder,MExp.FirstOrderArgs])) .char)))

end Shallot.MacroPeg.CBV.FragmentConsumingExamples
