import MacroPeg.CBV.ControlledPartialRecursive

namespace Shallot.MacroPeg.CBV.ControlledPartialRecursiveExamples
open ControlledPartialRecursive
open PartialCodewordCapture (eof)
open RuntimeShiftFilter (scanner)

def tails : List MExp := [
  .alt (.seq (.lit ['!']) (.param 0))
    (.seq (.lit ['Z']) (.seq (.call 1 [.notP (.param 0)])
      (.seq (.lit ['?']) (.param 0)))),
  .seq (.lit ['#']) (.seq scanner (.seq (.lit ['Y'])
    (.seq (.call 0 [.notP (.param 0)]) (.seq (.lit ['?']) (.param 0)))))]
def root : MExp := .seq (.call 0 []) eof

/-- A real 0→1→0 call chain captures aa, a#a, aa. The middle
parent-dependent stop leaves the unequal aa# for its own continuation;
both parent values are reused after returning. -/
theorem mutual_returns :
    let x := "aa#aaZa#a#a#aa#Yaa#aa!aa?a#a?aa".toList
    evV (source tails) x .callByValuePar (tblV (source tails) x .callByValuePar 3)
      [] (render tails true root) x.length=some (some 0) ∧
    evV (target tails) x .callByValueSeq (tblV (target tails) x .callByValueSeq 3)
      [] (render tails false root) x.length=some (some 0) := by
  decide +kernel

/-- The stopping test invokes the very same user before the actual
call. Its successful first probe and failed second probe select a#a;
the actual callee later reuses that whole partial capture. -/
theorem recursive_test_selects_length :
    let ts := [MExp.alt (.lit ['X'])
      (.seq (.lit ['#','a','X','!']) (.seq (.param 0) eof))]
    let x := "a#a#a#aX!a#a".toList
    let e := MExp.call 0 [.call 0 []]
    evV (source ts) x .callByValuePar (tblV (source ts) x .callByValuePar 2)
      [] (ControlledPartialCapture.argument (render ts true (.call 0 []))) x.length=
        some (some 9) ∧
    pre x x.length 9="a#a".toList ∧
    evV (source ts) x .callByValuePar (tblV (source ts) x .callByValuePar 2)
      [] (render ts true e) x.length=some (some 0) ∧
    evV (target ts) x .callByValueSeq (tblV (target ts) x .callByValueSeq 2)
      [] (render ts false e) x.length=some (some 0) := by
  decide +kernel

theorem rejected_parent_and_child_copies :
    ∀ x ∈ ["aa#aaZa#a#a#aa#Yaa#aa!aa?a#?aa".toList,
      "aa#aaZa#a#a#aa#Yaa#aa!aa?a#a?a".toList,
      "aa#aaZa#a#a#aa#Yaa#aa!a?a#a?aa".toList],
    evV (source tails) x .callByValuePar (tblV (source tails) x .callByValuePar 3)
      [] (render tails true root) x.length=some none ∧
    evV (target tails) x .callByValueSeq (tblV (target tails) x .callByValueSeq 3)
      [] (render tails false root) x.length=some none := by
  decide +kernel

/-- Parent-held values change the successful stopping point on the same
input under the generated recursive compiler, with no input encoding. -/
theorem different_caller_lengths :
    let ts := [MExp.lit []]
    let x := "a#a#a#a#a#a!".toList
    let e := MExp.call 0 [.param 0]
    evV (source ts) x .callByValuePar (tblV (source ts) x .callByValuePar 1)
      ["a#a#".toList] (render ts true e) x.length=some (some 5) ∧
    evV (target ts) x .callByValueSeq (tblV (target ts) x .callByValueSeq 1)
      ["a#a#".toList] (render ts false e) x.length=some (some 5) ∧
    evV (source ts) x .callByValuePar (tblV (source ts) x .callByValuePar 1)
      ["a#a#a#".toList] (render ts true e) x.length=some (some 7) ∧
    evV (target ts) x .callByValueSeq (tblV (target ts) x .callByValueSeq 1)
      ["a#a#a#".toList] (render ts false e) x.length=some (some 7) := by
  decide +kernel

theorem zero_and_empty_capture :
    let ts := [MExp.seq (.lit ['#']) (.seq scanner
      (.seq (.lit ['!','?']) (.seq (.param 0) eof)))]
    ∀ x ∈ ["a#a#aa#!?a".toList,"##aa#!?".toList],
    evV (source ts) x .callByValuePar (tblV (source ts) x .callByValuePar 1)
      ["Z".toList] (render ts true (.call 0 [.param 0])) x.length=some (some 0) ∧
    evV (target ts) x .callByValueSeq (tblV (target ts) x .callByValueSeq 1)
      ["Z".toList] (render ts false (.call 0 [.param 0])) x.length=some (some 0) := by
  decide +kernel

theorem undefined_stopping_test (m : Nat) :
    let ts := [MExp.lit []]
    let x := ['#','#']
    let e := MExp.call 0 [.star (.lit [])]
    evV (source ts) x .callByValuePar (tblV (source ts) x .callByValuePar m)
      [] (render ts true e) x.length=none ∧
    evV (target ts) x .callByValueSeq (tblV (target ts) x .callByValueSeq m)
      [] (render ts false e) x.length=none := by
  dsimp only []
  let ts := [MExp.lit []]
  let x : List Char := ['#','#']
  let T := tblV (source ts) x .callByValuePar m
  have hfirst : evV (source ts) x .callByValuePar T [] scanner 2=some (some 1) := by
    exact PrefixCodeCapture.scanner_at _ _ _ _ _ 2 0 ['#'] (by decide) rfl
  have hnext : evV (source ts) x .callByValuePar T [] scanner 1=some (some 0) := by
    exact PrefixCodeCapture.scanner_at _ _ _ _ _ 1 0 [] (by decide) rfl
  have htest : evV (source ts) x .callByValuePar T [] (.star (.lit [])) 0=none := by
    rw [evV_star]
    apply evStar_stuck (j:=0)
    · simp [evV,Shallot.stripPrefix?,sfx]
    · omega
  have harg := ControlledPartialCapture.test_none (source ts) x .callByValuePar T []
    (.star (.lit [])) 2 1 0 hfirst hnext htest
  have hs : evV (source ts) x .callByValuePar T []
      (render ts true (.call 0 [.star (.lit [])])) x.length=none := by
    change evV (source ts) x .callByValuePar T []
      (.call 0 [ControlledPartialCapture.argument (.star (.lit []))]) 2=none
    rw [evV_call_par (source_rule ts 0 _ rfl) rfl (by decide)]
    simp only [evParArgs,harg]
  constructor
  · exact hs
  · rw [←evaluator_eq ts x m (.call 0 [.star (.lit [])]) [] x.length (Nat.le_refl _)]
    exact hs

end Shallot.MacroPeg.CBV.ControlledPartialRecursiveExamples
