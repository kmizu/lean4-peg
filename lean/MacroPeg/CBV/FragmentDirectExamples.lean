import MacroPeg.CBV.FragmentMixedCompiler
import MacroPeg.CBV.FragmentConsumingRecursiveExamples

namespace Shallot.MacroPeg.CBV.FragmentDirectExamples
open FragmentMixedForm (Body)
open FragmentMixedCompiler
open PartialCodewordCapture (eof)

private def fresh : MExp := .seq (.param 0) (.seq (.lit [':'])
  (.seq (.star (.chr 'b')) (.call 2 [.eps,.chr 'a'])))
private def users : List Body := [
  .leaf (false,.alt (.seq (.lit ['!']) (.param 0))
    (.seq (.lit ['Z']) (.seq (.call 1 [.eps,FragmentConsumingRecursiveExamples.middle])
      (.seq (.lit ['?']) (.param 0))))),
  .leaf (true,.seq (.lit ['Y']) (.seq (.call 0 [fresh]) (.seq (.lit ['?']) (.param 0)))),
  .leaf (true,.lit ['Y'])]
private def root : MExp := .seq (.call 0 [.lit ['a','b']]) eof
private def whole := "aaa#a:bbba#aY".toList
private def input := "abZ".toList++"aaa#aaa#aY".toList++whole++['!']++whole++"?aaa#a?ab".toList

/-- Eligibility is computed from the generated body plans, not supplied as
a theorem about their behavior. Only the bare user accepts a direct argument. -/
theorem generated_argument_kinds :
    FragmentMixedRecursive.eligible ((tails users).map Prod.fst) (tails users).length (plans users) 0=true ∧
    FragmentMixedRecursive.eligible ((tails users).map Prod.fst) (tails users).length (plans users) 1=false := by
  decide +kernel

/-- The source root really passes the original literal ab as its argument. -/
theorem original_actual_argument :
    sourceRender users root=.seq (.call 0 [.lit ['a','b']]) eof := by
  rfl

/-- A general parent ab enters the fragment user with child aaa#a. Its
argument constructs a new capture from that value, ':', fresh b*, and an
actual recursive fragment-user call. Grandchild and both parents are reused. -/
theorem general_fragment_mutual_returns :
    evV (source users) input .callByValuePar (tblV (source users) input .callByValuePar 3) []
      (sourceRender users root) input.length=some (some 0) ∧
    evV (target users) input .callByValueSeq (tblV (target users) input .callByValueSeq 3) []
      (targetRender users root) input.length=some (some 0) := by
  decide +kernel

theorem short_general_grandchild_rejected :
    let x := "abZ".toList++"aaa#aaa#aY".toList++whole++['!']++"aaa#a:bbba#a".toList++"?aaa#a?ab".toList
    evV (source users) x .callByValuePar (tblV (source users) x .callByValuePar 3) []
      (sourceRender users root) x.length=some none ∧
    evV (target users) x .callByValueSeq (tblV (target users) x .callByValueSeq 3) []
      (targetRender users root) x.length=some none := by
  decide +kernel

/-- General arguments must run before a negative user body. A successful
body may return at the origin, before the argument's endpoint. -/
theorem general_argument_preview_and_rollback :
    let us : List Body := [.notP (.leaf (false,.lit ['Q']))]
    let x := "ab!".toList
    let e := MExp.seq (.call 0 [.lit ['a','b']]) (.seq (.lit x) eof)
    evV (source us) x .callByValuePar (tblV (source us) x .callByValuePar 1) []
      (sourceRender us e) x.length=some (some 0) ∧
    evV (target us) x .callByValueSeq (tblV (target us) x .callByValueSeq 1) []
      (targetRender us e) x.length=some (some 0) ∧
    evV (source us) ['!'] .callByValuePar (tblV (source us) ['!'] .callByValuePar 0) []
      (sourceRender us (.call 0 [.lit ['a','b']])) 1=some none ∧
    evV (target us) ['!'] .callByValueSeq (tblV (target us) ['!'] .callByValueSeq 0) []
      (targetRender us (.call 0 [.lit ['a','b']])) 1=some none ∧
    evV (source us) x .callByValuePar (tblV (source us) x .callByValuePar 1) []
      (sourceRender us (.call 0 [.star .eps])) x.length=none ∧
    evV (target us) x .callByValueSeq (tblV (target us) x .callByValueSeq 1) []
      (targetRender us (.call 0 [.star .eps])) x.length=none := by
  decide +kernel

/-- A chosen general argument remains committed if its later reuse fails. -/
theorem selected_general_argument :
    let us : List Body := [.leaf (false,.seq (.lit ['!']) (.param 0))]
    let e := MExp.seq (.call 0 [.alt (.lit ['a','a']) (.lit ['a'])]) eof
    evV (source us) "aa!aa".toList .callByValuePar (tblV (source us) "aa!aa".toList .callByValuePar 1) []
      (sourceRender us e) 5=some (some 0) ∧
    evV (target us) "aa!aa".toList .callByValueSeq (tblV (target us) "aa!aa".toList .callByValueSeq 1) []
      (targetRender us e) 5=some (some 0) ∧
    evV (source us) "aa!a".toList .callByValuePar (tblV (source us) "aa!a".toList .callByValuePar 1) []
      (sourceRender us e) 4=some none ∧
    evV (target us) "aa!a".toList .callByValueSeq (tblV (target us) "aa!a".toList .callByValueSeq 1) []
      (targetRender us e) 4=some none := by
  decide +kernel

end Shallot.MacroPeg.CBV.FragmentDirectExamples
