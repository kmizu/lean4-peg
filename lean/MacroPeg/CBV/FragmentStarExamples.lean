import MacroPeg.CBV.FragmentStarCompiler
import MacroPeg.CBV.FragmentConsumingRecursiveExamples

namespace Shallot.MacroPeg.CBV.FragmentStarExamples
open FragmentStarForm (Body)
open FragmentStarCompiler
open PartialCodewordCapture (eof)

private def mixed : Body := .alt (.leaf (.lit ['X'])) (.notP (.leaf (.lit ['Q'])))
private def users : List Body := [.seq (.star mixed) (.leaf (.seq (.lit ['Q','!']) (.param 0)))]
private def root : MExp := .seq (.call 0 [.eps,.chr 'a']) eof

theorem mixed_operand_has_nullable_output :
    ¬LeafContinuation.Consumer (FragmentStarForm.normalize mixed).plan := by
  simp [mixed,FragmentStarForm.normalize,FragmentStarForm.choice,FragmentStarForm.join,
    FragmentStarForm.atom,FragmentStarForm.neg,LeafContinuation.Consumer,ContinuationFamily.shift]

/-- A non-Consumer operand repeats a consuming X branch, then fails its
negative branch at Q. The final leaf reuses the same capture after the star. -/
theorem mixed_star_consumes_then_stops :
    let x := "a#aXa#aXa#aQ!a".toList
    evV (source users) x .callByValuePar (tblV (source users) x .callByValuePar 1) []
      (sourceRender users root) x.length=some (some 0) ∧
    evV (target users) x .callByValueSeq (tblV (target users) x .callByValueSeq 1) []
      (targetRender users root) x.length=some (some 0) := by
  decide +kernel

theorem zero_iterations_and_short_copy :
    evV (source users) "a#aQ!a".toList .callByValuePar (tblV (source users) "a#aQ!a".toList .callByValuePar 1) []
      (sourceRender users root) 6=some (some 0) ∧
    evV (target users) "a#aQ!a".toList .callByValueSeq (tblV (target users) "a#aQ!a".toList .callByValueSeq 1) []
      (targetRender users root) 6=some (some 0) ∧
    evV (source users) "a#aXa#aQ!".toList .callByValuePar (tblV (source users) "a#aXa#aQ!".toList .callByValuePar 1) []
      (sourceRender users root) 9=some none ∧
    evV (target users) "a#aXa#aQ!".toList .callByValueSeq (tblV (target users) "a#aXa#aQ!".toList .callByValueSeq 1) []
      (targetRender users root) 9=some none := by
  decide +kernel

/-- After a real consuming iteration, the chosen negative output succeeds
without consuming. Undefinedness must happen there before the final leaf. -/
theorem nullable_after_consuming_iteration :
    let x := "a#aXa!".toList
    evV (source users) x .callByValuePar (tblV (source users) x .callByValuePar 1) []
      (sourceRender users root) x.length=none ∧
    evV (target users) x .callByValueSeq (tblV (target users) x .callByValueSeq 1) []
      (targetRender users root) x.length=none := by
  decide +kernel

/-- General nested stars are permitted in the body syntax; their empty
successful inner result makes the outer star undefined. -/
theorem nested_body_star :
    let us : List Body := [.star (.star (.leaf (.lit ['X'])))]
    let x := "a#aXa!".toList
    evV (source us) x .callByValuePar (tblV (source us) x .callByValuePar 1) []
      (sourceRender us root) x.length=none ∧
    evV (target us) x .callByValueSeq (tblV (target us) x .callByValueSeq 1) []
      (targetRender us root) x.length=none := by
  decide +kernel

private def recursiveUsers : List Body := [
  .leaf ((FragmentConsumingRecursiveExamples.tails[0]?).getD MExp.failAlways),
  .seq (.star (.leaf (.lit ['Y']))) (.leaf (.seq (.call 0 [.eps,FragmentConsumingRecursiveExamples.choice])
    (.seq (.lit ['?']) (.param 0)))),
  .leaf (.lit ['Y'])]

/-- Child user 1 replays its whole aaa#a capture through two body
iterations, then calls user 0 with fresh aa and restores both parents. -/
theorem mutual_star_returns :
    let x := ("a#aZ"++"aaa#aaa#aY"++"aaa#aaa#aY"++"aaa#aaa#a"++"aa#aa!aa"++"?aaa#a?a").toList
    let e := FragmentConsumingRecursiveExamples.root
    evV (source recursiveUsers) x .callByValuePar (tblV (source recursiveUsers) x .callByValuePar 3) []
      (sourceRender recursiveUsers e) x.length=some (some 0) ∧
    evV (target recursiveUsers) x .callByValueSeq (tblV (target recursiveUsers) x .callByValueSeq 3) []
      (targetRender recursiveUsers e) x.length=some (some 0) := by
  decide +kernel

end Shallot.MacroPeg.CBV.FragmentStarExamples
