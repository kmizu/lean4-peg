import MacroPeg.CBV.FragmentBodyCompiler
import MacroPeg.CBV.FragmentConsumingRecursiveExamples

namespace Shallot.MacroPeg.CBV.FragmentBodyExamples
open FragmentBodyForm (Body)
open FragmentBodyCompiler
open PartialCodewordCapture (eof)

def users : List Body := [
  .seq (.notP (.leaf (.lit ['Q']))) (.leaf ((FragmentConsumingRecursiveExamples.tails[0]?).getD MExp.failAlways)),
  .seq (.leaf (.lit ['Y'])) (.leaf (.seq (.call 0 [.eps,FragmentConsumingRecursiveExamples.choice])
    (.seq (.lit ['?']) (.param 0)))),
  .leaf (.lit ['Y'])]
def root : MExp := FragmentConsumingRecursiveExamples.root

/-- User 0 sequences a negative zero-consuming output with a replay leaf;
user 1 sequences two consuming leaves, then invokes user 0 again. -/
theorem nested_sequence_mutual_returns :
    let x := ("a#aZ"++"aaa#aaa#aY"++"aaa#aaa#a"++"aa#aa!aa"++"?aaa#a?a").toList
    evV (source users) x .callByValuePar (tblV (source users) x .callByValuePar 3) []
      (sourceRender users root) x.length=some (some 0) ∧
    evV (target users) x .callByValueSeq (tblV (target users) x .callByValueSeq 3) []
      (targetRender users root) x.length=some (some 0) := by
  decide +kernel

theorem short_grandchild_copy_rejected :
    let x := ("a#aZ"++"aaa#aaa#aY"++"aaa#aaa#a"++"aa#aa!a"++"?aaa#a?a").toList
    evV (source users) x .callByValuePar (tblV (source users) x .callByValuePar 3) []
      (sourceRender users root) x.length=some none ∧
    evV (target users) x .callByValueSeq (tblV (target users) x .callByValueSeq 3) []
      (targetRender users root) x.length=some none := by
  decide +kernel

/-- A negative left body succeeds without consuming; the right body starts
at the original position with the same captured a. -/
theorem negative_left_sequence :
    let us : List Body := [.seq (.notP (.leaf (.lit ['Q'])))
      (.leaf (.seq (.lit ['X','!']) (.param 0)))]
    let e := MExp.seq (.call 0 [.eps,.chr 'a']) eof
    let x := "a#aX!a".toList
    evV (source us) x .callByValuePar (tblV (source us) x .callByValuePar 1) []
      (sourceRender us e) x.length=some (some 0) ∧
    evV (target us) x .callByValueSeq (tblV (target us) x .callByValueSeq 1) []
      (targetRender us e) x.length=some (some 0) := by
  decide +kernel

/-- A later failure does not reopen the successful x branch as xy. The
naive distributed body accepts exactly the input rejected by the real one. -/
theorem selected_branch_stays_committed :
    let a := Body.leaf (.lit ['x'])
    let b := Body.leaf (.lit ['x','y'])
    let c := Body.leaf (.seq (.lit ['!']) (.param 0))
    let us := [Body.seq (.alt a b) c]
    let naive := [Body.alt (.seq a c) (.seq b c)]
    let e := MExp.seq (.call 0 [.eps,.chr 'a']) eof
    let x := "a#axya#a!a".toList
    evV (source us) x .callByValuePar (tblV (source us) x .callByValuePar 1) []
      (sourceRender us e) x.length=some none ∧
    evV (target us) x .callByValueSeq (tblV (target us) x .callByValueSeq 1) []
      (targetRender us e) x.length=some none ∧
    evV (source naive) x .callByValuePar (tblV (source naive) x .callByValuePar 1) []
      (sourceRender naive e) x.length=some (some 0) := by
  decide +kernel

/-- Continuation None remains None after a zero-consuming negative success. -/
theorem undefined_right_continuation :
    let us : List Body := [.seq (.notP (.leaf (.lit ['Q']))) (.leaf (.star .eps))]
    let e := MExp.call 0 [.eps,.chr 'a']
    let x := "a#a".toList
    evV (source us) x .callByValuePar (tblV (source us) x .callByValuePar 1) []
      (sourceRender us e) x.length=none ∧
    evV (target us) x .callByValueSeq (tblV (target us) x .callByValueSeq 1) []
      (targetRender us e) x.length=none := by
  decide +kernel

end Shallot.MacroPeg.CBV.FragmentBodyExamples
