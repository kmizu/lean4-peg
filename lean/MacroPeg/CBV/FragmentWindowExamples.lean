import MacroPeg.CBV.FragmentMixedCompiler
import MacroPeg.CBV.FragmentConsumingRecursiveExamples

namespace Shallot.MacroPeg.CBV.FragmentWindowExamples
open FragmentMixedForm (Body)
open FragmentMixedCompiler
open PartialCodewordCapture (eof look)

private def loopBody : Body := .alt (.leaf (false,.lit ['X'])) (.leaf (true,.lit ['Y']))
private def users : List Body := [
  .leaf (true,.alt (.seq (.lit ['!']) (.param 0))
    (.seq (.lit ['Z']) (.seq (.call 1 [.param 0,.eps,FragmentConsumingRecursiveExamples.middle,
      .seq (.param 0) (.call 2 [.eps,.chr 'a'])]) (.seq (.lit ['?']) (.param 0))))),
  .seq (.star loopBody) (.leaf (true,.seq
    (.call 0 [.notP (.param 0),.eps,FragmentConsumingRecursiveExamples.choice,.chr '#'])
    (.seq (.lit ['?']) (.param 0)))),
  .leaf (true,.lit ['Y'])]
private def input := ("a#aZ"++"aaa#aaa#aY"++"aaa#aX"++"aaa#aaa#aY"++"aaa#aaa#a"++"aa#aa!aa"++"?aaa#a?a").toList
private def root := FragmentConsumingRecursiveExamples.root

/-- The public source uses one real capture with origin and endpoint
lookaheads, rather than four actual source arguments. -/
theorem actual_guarded_argument :
    sourceRender users (.call 1 [.param 0,.eps,.chr 'a',.param 0])=
      .call 1 [.seq (look (.param 0))
        (.seq (ControlledFragmentReplay.argument .eps (.chr 'a')) (look (.param 0)))] := by
  rfl

/-- Both tests inspect the caller's held value. The endpoint test also
executes user 2, while the body interleaves bare and shifted iterations,
freshly captures a grandchild, and restores both parents' whole values. -/
theorem guarded_mutual_returns :
    evV (source users) input .callByValuePar (tblV (source users) input .callByValuePar 3) []
      (sourceRender users root) input.length=some (some 0) ∧
    evV (target users) input .callByValueSeq (tblV (target users) input .callByValueSeq 3) []
      (targetRender users root) input.length=some (some 0) := by
  decide +kernel

/-- The endpoint check keeps the parent's environment: a succeeds, aa
fails on the same input even though both origin tests succeed. -/
theorem endpoint_parent_dependency :
    let x := ("aaa#aaa#aY"++"aaa#aX"++"aaa#aaa#aY"++"aaa#aaa#a"++"aa#aa!aa"++"?aaa#a").toList
    let e := MExp.call 1 [.param 0,.eps,FragmentConsumingRecursiveExamples.middle,
      .seq (.param 0) (.call 2 [.eps,.chr 'a'])]
    evV (source users) x .callByValuePar (tblV (source users) x .callByValuePar 2) [['a']]
      (sourceRender users e) x.length=some (some 0) ∧
    evV (target users) x .callByValueSeq (tblV (target users) x .callByValueSeq 2) [['a']]
      (targetRender users e) x.length=some (some 0) ∧
    evV (source users) x .callByValuePar (tblV (source users) x .callByValuePar 2) [['a','a']]
      (sourceRender users e) x.length=some none ∧
    evV (target users) x .callByValueSeq (tblV (target users) x .callByValueSeq 2) [['a','a']]
      (targetRender users e) x.length=some none := by
  decide +kernel

/-- Origin divergence precedes failed capture; endpoint divergence precedes
a rejected body. Finite endpoint failure also precedes the clock-zero row. -/
theorem argument_order :
    let us : List Body := [.notP (.leaf (true,.lit ['Q']))]
    let x := ['a','!']
    let beforeLoop := MExp.call 0 [.star .eps,.eps,MExp.failAlways,.eps]
    let afterLoop := MExp.call 0 [.eps,.eps,.chr 'a',.star .eps]
    let afterFail := MExp.call 0 [.eps,.eps,.chr 'a',.chr 'Q']
    (∀ e ∈ [beforeLoop,afterLoop],
      evV (source us) x .callByValuePar (tblV (source us) x .callByValuePar 1) []
        (sourceRender us e) 2=none ∧
      evV (target us) x .callByValueSeq (tblV (target us) x .callByValueSeq 1) []
        (targetRender us e) 2=none) ∧
    (∀ k ∈ [0,1],
      evV (source us) x .callByValuePar (tblV (source us) x .callByValuePar k) []
        (sourceRender us afterFail) 2=some none ∧
      evV (target us) x .callByValueSeq (tblV (target us) x .callByValueSeq k) []
        (targetRender us afterFail) 2=some none) := by
  decide +kernel

/-- A failed after-test cannot choose a shorter H alternative. -/
theorem endpoint_choice_commit :
    let us : List Body := [.leaf (true,.lit ['a','X'])]
    let x := "aa#aaX".toList
    let e := MExp.call 0 [.eps,.eps,FragmentConsumingRecursiveExamples.choice,.chr 'a']
    evV (source us) x .callByValuePar (tblV (source us) x .callByValuePar 1) []
      (sourceRender us e) x.length=some none ∧
    evV (target us) x .callByValueSeq (tblV (target us) x .callByValueSeq 1) []
      (targetRender us e) x.length=some none ∧
    evV (source us) x .callByValuePar (tblV (source us) x .callByValuePar 1) []
      (sourceRender us (.call 0 [.eps,.eps,.chr 'a',.chr 'a'])) x.length=some (some 0) ∧
    evV (target us) x .callByValueSeq (tblV (target us) x .callByValueSeq 1) []
      (targetRender us (.call 0 [.eps,.eps,.chr 'a',.chr 'a'])) x.length=some (some 0) := by
  decide +kernel

end Shallot.MacroPeg.CBV.FragmentWindowExamples
