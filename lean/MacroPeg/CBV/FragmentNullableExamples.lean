import MacroPeg.CBV.FragmentNullableControl
import MacroPeg.CBV.FragmentConsumingRecursiveExamples

namespace Shallot.MacroPeg.CBV.FragmentNullableExamples
open FragmentNullableControl
open PartialCodewordCapture (eof)

private def ts : List MExp := [.eps]
private def us : List Body := [.starNot (.leaf 0)]
private def callA : MExp := .call 0 [.eps,.chr 'a']

/-- The actual source body loops at the original caller position. A replay
wrapper around the divergent leaf would incorrectly turn this into failure. -/
theorem nullable_origin_before_replay :
    let x := "a!".toList
    evV (source ts us) x .callByValuePar (tblV (source ts us) x .callByValuePar 1) []
      (sourceRender ts us callA) x.length=none ∧
    evV (target ts us) x .callByValueSeq (tblV (target ts us) x .callByValueSeq 1) []
      (targetRender ts us callA) x.length=none ∧
    evV (target ts us) x .callByValueSeq (tblV (target ts us) x .callByValueSeq 1) [['a']]
      (.seq RuntimeShiftFilter.scanner (.seq (.param 0) FragmentStuckRecursive.stuck)) x.length=some none := by
  decide +kernel

/-- A failed negative test terminates the star with zero iterations and
returns the origin, rather than the argument's capture endpoint. -/
theorem zero_iteration_returns_origin :
    let x := "a#a".toList
    let e := MExp.seq callA (.seq (.lit x) eof)
    evV (source ts us) x .callByValuePar (tblV (source ts us) x .callByValuePar 1) []
      (sourceRender ts us e) x.length=some (some 0) ∧
    evV (target ts us) x .callByValueSeq (tblV (target ts us) x .callByValueSeq 1) []
      (targetRender ts us e) x.length=some (some 0) := by
  decide +kernel

theorem finite_argument_failure_first :
    ∀ k∈[0,1,2],
    evV (source ts us) ['#'] .callByValuePar (tblV (source ts us) ['#'] .callByValuePar k) []
      (sourceRender ts us callA) 1=some none ∧
    evV (target ts us) ['#'] .callByValueSeq (tblV (target ts us) ['#'] .callByValueSeq k) []
      (targetRender ts us callA) 1=some none := by
  decide +kernel

theorem undefined_argument_first :
    let x := "aaZ".toList
    let e := MExp.call 0 [.eps,.seq (.chr 'a') (.star .eps)]
    evV (source ts us) x .callByValuePar (tblV (source ts us) x .callByValuePar 1) []
      (sourceRender ts us e) x.length=none ∧
    evV (target ts us) x .callByValueSeq (tblV (target ts us) x .callByValueSeq 1) []
      (targetRender ts us e) x.length=none := by
  decide +kernel

theorem double_star_origin :
    let users : List Body := [.doubleStar (.leaf 0)]
    let x := "a!".toList
    evV (source ts users) x .callByValuePar (tblV (source ts users) x .callByValuePar 1) []
      (sourceRender ts users callA) x.length=none ∧
    evV (target ts users) x .callByValueSeq (tblV (target ts users) x .callByValueSeq 1) []
      (targetRender ts users callA) x.length=none := by
  decide +kernel

private def recursiveUsers : List Body := [.guard (.starNot (.leaf 0)) (.leaf 0),.leaf 1,.leaf 2]
private def recursiveTails := FragmentConsumingRecursiveExamples.tails

theorem recursive_valid : ∀ u∈recursiveUsers, u.Valid recursiveTails.length := by
  simp [recursiveUsers,recursiveTails,FragmentConsumingRecursiveExamples.tails,Body.Valid]

/-- 0→1→0 transfers consuming fragment captures, returns each parent's
whole value, and runs a nullable star in the actual recursive user body. -/
theorem mutual_nullable_body_returns :
    let x := "a#aZaaa#aaa#aYaa#aa!aa?aaa#a?a".toList
    let e := FragmentConsumingRecursiveExamples.root
    evV (source recursiveTails recursiveUsers) x .callByValuePar
      (tblV (source recursiveTails recursiveUsers) x .callByValuePar 3) []
      (sourceRender recursiveTails recursiveUsers e) x.length=some (some 0) ∧
    evV (target recursiveTails recursiveUsers) x .callByValueSeq
      (tblV (target recursiveTails recursiveUsers) x .callByValueSeq 3) []
      (targetRender recursiveTails recursiveUsers e) x.length=some (some 0) := by
  decide +kernel

end Shallot.MacroPeg.CBV.FragmentNullableExamples
