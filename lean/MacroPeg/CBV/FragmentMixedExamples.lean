import MacroPeg.CBV.FragmentMixedCompiler
import MacroPeg.CBV.FragmentConsumingRecursiveExamples

namespace Shallot.MacroPeg.CBV.FragmentMixedExamples
open FragmentMixedForm (Body)
open FragmentMixedCompiler
open PartialCodewordCapture (eof)

private def loopBody : Body := .alt (.leaf (false,.lit ['X'])) (.leaf (true,.lit ['Y']))
private def users : List Body := [.seq (.star loopBody) (.leaf (false,.seq (.lit ['!']) (.param 0)))]
private def root : MExp := .seq (.call 0 [.eps,.chr 'a']) eof

/-- One held a passes through bare, shifted, and bare body iterations;
the post-star ordinary leaf reuses that same value after its delimiter. -/
theorem mixed_iterations_reuse_capture :
    let x := "aXa#aYaXa!a".toList
    evV (source users) x .callByValuePar (tblV (source users) x .callByValuePar 1) []
      (sourceRender users root) x.length=some (some 0) ∧
    evV (target users) x .callByValueSeq (tblV (target users) x .callByValueSeq 1) []
      (targetRender users root) x.length=some (some 0) := by
  decide +kernel

theorem short_final_capture_rejected :
    let x := "aXa#aYaXa!".toList
    evV (source users) x .callByValuePar (tblV (source users) x .callByValuePar 1) []
      (sourceRender users root) x.length=some none ∧
    evV (target users) x .callByValueSeq (tblV (target users) x .callByValueSeq 1) []
      (targetRender users root) x.length=some none := by
  decide +kernel

/-- A bare replay may itself be empty. The first iteration must remain
undefined instead of accepting zero iterations or advancing a fake scanner. -/
theorem empty_bare_replay_star :
    let us : List Body := [.star (.leaf (false,.eps))]
    let x := ['!']
    let e := MExp.call 0 [MExp.failAlways,.eps]
    evV (source us) x .callByValuePar (tblV (source us) x .callByValuePar 1) []
      (sourceRender us e) 1=none ∧
    evV (target us) x .callByValueSeq (tblV (target us) x .callByValueSeq 1) []
      (targetRender us e) 1=none := by
  decide +kernel

private def recursiveUsers : List Body := [
  .leaf (true,(FragmentConsumingRecursiveExamples.tails[0]?).getD MExp.failAlways),
  .seq (.star loopBody) (.leaf (true,.seq (.call 0 [.eps,FragmentConsumingRecursiveExamples.choice])
    (.seq (.lit ['?']) (.param 0)))),
  .leaf (true,.lit ['Y'])]

/-- A non-codeword child capture aaa#a is replayed first shifted, then
bare, then shifted again before a fresh grandchild aa. Both parents return. -/
theorem mixed_mutual_returns :
    let x := ("a#aZ"++"aaa#aaa#aY"++"aaa#aX"++"aaa#aaa#aY"++"aaa#aaa#a"++"aa#aa!aa"++"?aaa#a?a").toList
    let e := FragmentConsumingRecursiveExamples.root
    evV (source recursiveUsers) x .callByValuePar (tblV (source recursiveUsers) x .callByValuePar 3) []
      (sourceRender recursiveUsers e) x.length=some (some 0) ∧
    evV (target recursiveUsers) x .callByValueSeq (tblV (target recursiveUsers) x .callByValueSeq 3) []
      (targetRender recursiveUsers e) x.length=some (some 0) := by
  decide +kernel

theorem short_noncodeword_iteration_rejected :
    let x := ("a#aZ"++"aaa#aaa#aY"++"aaa#X"++"aaa#aaa#aY"++"aaa#aaa#a"++"aa#aa!aa"++"?aaa#a?a").toList
    let e := FragmentConsumingRecursiveExamples.root
    evV (source recursiveUsers) x .callByValuePar (tblV (source recursiveUsers) x .callByValuePar 3) []
      (sourceRender recursiveUsers e) x.length=some none ∧
    evV (target recursiveUsers) x .callByValueSeq (tblV (target recursiveUsers) x .callByValueSeq 3) []
      (targetRender recursiveUsers e) x.length=some none := by
  decide +kernel

/-- A short ordinary alternative has already succeeded when its following
leaf fails. It cannot be reopened as the longer shifted alternative. -/
theorem mixed_branch_commit :
    let a := Body.leaf (false,.lit ['#'])
    let b := Body.leaf (true,.lit ['y'])
    let c := Body.leaf (false,.lit ['!'])
    let us := [Body.seq (.alt a b) c]
    let naive := [Body.alt (.seq a c) (.seq b c)]
    let e := MExp.seq (.call 0 [MExp.failAlways,.eps]) eof
    let x := "#y!".toList
    evV (source us) x .callByValuePar (tblV (source us) x .callByValuePar 1) []
      (sourceRender us e) x.length=some none ∧
    evV (target us) x .callByValueSeq (tblV (target us) x .callByValueSeq 1) []
      (targetRender us e) x.length=some none ∧
    evV (source naive) x .callByValuePar (tblV (source naive) x .callByValuePar 1) []
      (sourceRender naive e) x.length=some (some 0) := by
  decide +kernel

/-- Predicate outputs coexist with both replay entries: finite stopping
and empty-success divergence remain distinct after a bare iteration. -/
theorem mixed_nullable_control :
    let operand := Body.alt (.leaf (false,.lit ['X'])) (.notP (.leaf (true,.lit ['Q'])))
    let us := [Body.seq (.star operand) (.leaf (true,.seq (.lit ['Q','!']) (.param 0)))]
    let good := "aXa#aQ!a".toList
    let bad := "aXa!".toList
    evV (source us) good .callByValuePar (tblV (source us) good .callByValuePar 1) []
      (sourceRender us root) good.length=some (some 0) ∧
    evV (target us) good .callByValueSeq (tblV (target us) good .callByValueSeq 1) []
      (targetRender us root) good.length=some (some 0) ∧
    evV (source us) bad .callByValuePar (tblV (source us) bad .callByValuePar 1) []
      (sourceRender us root) bad.length=none ∧
    evV (target us) bad .callByValueSeq (tblV (target us) bad .callByValueSeq 1) []
      (targetRender us root) bad.length=none := by
  decide +kernel

end Shallot.MacroPeg.CBV.FragmentMixedExamples
