import MacroPeg.CBV.ControlledFragmentRecursive

/-! Actual recursive tests select the final fragment and preserve parents
across source/target calls. These execute ordinary evaluator tables. -/
namespace Shallot.MacroPeg.CBV.ControlledFragmentRecursiveExamples
open ControlledFragmentRecursive
open PartialCodewordCapture (eof)

def tails : List MExp := [
  .alt (.seq (.lit ['!']) (.param 0))
    (.seq (.lit ['Z']) (.seq (.call 1 [.eps,.notP (.call 2 [])])
      (.seq (.lit ['?']) (.param 0)))),
  .seq (.lit ['Y']) (.seq (.call 0 []) (.seq (.lit ['?']) (.param 0))),
  .lit ['Y']]
def root : MExp := .seq (.call 0 []) eof

/-- Real 0→1→0 calls capture a → aaa#a → aa. The middle capture ends
inside aaa because J probes user 2; both parent values survive returns. -/
theorem mutual_returns :
    let x := "a#aZaaa#aaa#aYaa#aa!aa?aaa#a?a".toList
    evV (source tails) x .callByValuePar (tblV (source tails) x .callByValuePar 3)
      [] (render tails true root) x.length=some (some 0) ∧
    evV (target tails) x .callByValueSeq (tblV (target tails) x .callByValueSeq 3)
      [] (render tails false root) x.length=some (some 0) := by
  decide +kernel

/-- The fragment test invokes the very same user as the actual call. A
fresh aa capture fails its prefix, while a fresh a capture succeeds and
stops H one a before its greedy endpoint. -/
theorem same_user_probe_selects_fragment :
    let ts := [MExp.seq (.lit ['X','!']) (.param 0)]
    let e := MExp.seq (.call 0 [.eps,.notP (.call 0 [])]) eof
    let x := "aaa#aaa#aX!aaa#a".toList
    let a := ControlledFragmentReplay.argument .eps
      (ControlledFragmentPreflight.fragment (render ts true (.notP (.call 0 []))))
    evV (source ts) x .callByValuePar (tblV (source ts) x .callByValuePar 2)
      [] a x.length=some (some (x.length-5)) ∧
    pre x x.length (x.length-5)="aaa#a".toList ∧
    evV (source ts) x .callByValuePar (tblV (source ts) x .callByValuePar 2)
      [] (render ts true e) x.length=some (some 0) ∧
    evV (target ts) x .callByValueSeq (tblV (target ts) x .callByValueSeq 2)
      [] (render ts false e) x.length=some (some 0) := by
  decide +kernel

/-- Caller values change the final fragment, including the empty value;
the concrete recursive compiler retains the whole value in every case. -/
theorem caller_selected_fragments :
    let ts := [MExp.seq (.lit ['X','!']) (.param 0)]
    let e := MExp.seq (.call 0 [.eps,.notP (.seq (.param 0) (.lit ['#']))]) eof
    ∀ xp ∈ [("aaa#aaa#aX!aaa#a".toList,['a']),
      ("aaa#aaa#aaX!aaa#aa".toList,[]),
      ("aaa#aaa#X!aaa#".toList,['a','a']),
      ("aaa#aX!a".toList,['a']),
      ("#X!".toList,[])],
    let x := xp.1
    evV (source ts) x .callByValuePar (tblV (source ts) x .callByValuePar 1)
      [xp.2] (render ts true e) x.length=some (some 0) ∧
    evV (target ts) x .callByValueSeq (tblV (target ts) x .callByValueSeq 1)
      [xp.2] (render ts false e) x.length=some (some 0) := by
  decide +kernel

theorem short_parent_child_grandchild_rejected :
    ∀ x ∈ ["a#aZaaa#aaa#aYaa#aa!a?aaa#a?a".toList,
      "a#aZaaa#aaa#aYaa#aa!aa?aaa#?a".toList,
      "a#aZaaa#aaa#aYaa#aa!aa?aaa#a?".toList],
    evV (source tails) x .callByValuePar (tblV (source tails) x .callByValuePar 3)
      [] (render tails true root) x.length=some none ∧
    evV (target tails) x .callByValueSeq (tblV (target tails) x .callByValueSeq 3)
      [] (render tails false root) x.length=some none := by
  decide +kernel

/-- G stops while a further full word remains, while J independently
selects a proper final a-fragment using the caller's retained value. -/
theorem both_controls_select_capture :
    let ts := [MExp.seq RuntimeShiftFilter.scanner (.seq (.lit ['X','!']) (.param 0))]
    let e := MExp.seq (.call 0 [.notP (.lit ['X']),.notP (.seq (.param 0) (.lit ['#']))]) eof
    let x := "aaa#aaa#aaa#X!aaa#a".toList
    evV (source ts) x .callByValuePar (tblV (source ts) x .callByValuePar 1)
      [['a']] (render ts true e) x.length=some (some 0) ∧
    evV (target ts) x .callByValueSeq (tblV (target ts) x .callByValueSeq 1)
      [['a']] (render ts false e) x.length=some (some 0) := by
  decide +kernel

/-- The earlier recursive G probe remains a real user invocation in this
compiler, in addition to the recursive J probes exercised above. -/
theorem recursive_word_count_probe :
    let ts := [MExp.alt (.lit ['X'])
      (.seq (.lit ['#','a','X','!']) (.seq (.param 0) eof))]
    let e := MExp.seq (.call 0 [.call 0 []]) eof
    let x := "a#a#a#aX!a#a".toList
    evV (source ts) x .callByValuePar (tblV (source ts) x .callByValuePar 2)
      [] (render ts true e) x.length=some (some 0) ∧
    evV (target ts) x .callByValueSeq (tblV (target ts) x .callByValueSeq 2)
      [] (render ts false e) x.length=some (some 0) := by
  decide +kernel

/-- Undefined J is preserved at every ordinary clock, before the finite
failure of scanner on aaZ could be observed by a reordered comparison. -/
theorem undefined_fragment_probe (m : Nat) :
    let ts := [MExp.lit []]
    let e := MExp.call 0 [.eps,.star .eps]
    let x := "aaZ".toList
    evV (source ts) x .callByValuePar (tblV (source ts) x .callByValuePar m)
      [] (render ts true e) x.length=none ∧
    evV (target ts) x .callByValueSeq (tblV (target ts) x .callByValueSeq m)
      [] (render ts false e) x.length=none := by
  dsimp only []
  have hs : evV (source [.lit []]) "aaZ".toList .callByValuePar
      (tblV (source [.lit []]) "aaZ".toList .callByValuePar m) []
      (render [.lit []] true (.call 0 [.eps,.star .eps])) "aaZ".toList.length=none := by
    let g := source [MExp.lit []]
    let x := "aaZ".toList
    let T := tblV g x .callByValuePar m
    have hstep : evV g x .callByValuePar T [] (ControlledPartialCapture.step .eps) 3=some none := by
      have hpure : ParserPrefixFusion.Pure (ControlledPartialCapture.step .eps) := by
        simp [ControlledPartialCapture.step,PartialCodewordCapture.look,RuntimeShiftFilter.scanner,
          NestedScannerArguments.scan,NestedScannerArguments.choice,MExp.failAlways,ParserPrefixFusion.Pure]
      rw [ParserPrefixFusion.pure_eval g ⟨[]⟩ x .callByValuePar .callByValuePar T
        (fun _ _ => []) [] [] _ hpure 3]
      decide +kernel
    have hstar : evV g x .callByValuePar T [] (.star (ControlledPartialCapture.step .eps)) 3=
        some (some 3) := evStar_fail hstep
    have hloop : evV g x .callByValuePar T [] (.star .eps) 2=none :=
      evStar_stuck (j:=2) rfl (Nat.lt_irrefl 2)
    have hH : evV g x .callByValuePar T [] (ControlledFragmentPreflight.fragment (.star .eps)) 3=none := by
      apply evStar_none
      rw [evV_seq_ok (show evV g x .callByValuePar T [] (.chr 'a') 3=some (some 2) from rfl)]
      change evV g x .callByValuePar T [] (.andP (.star .eps)) 2=none
      rw [CallLookahead.evV_peek,hloop]; rfl
    have harg : evV g x .callByValuePar T []
        (ControlledFragmentReplay.argument .eps (ControlledFragmentPreflight.fragment (.star .eps))) 3=none := by
      rw [ControlledFragmentReplay.argument,evV_seq_ok hstar]; exact hH
    change evV g x .callByValuePar T []
      (.call 0 [ControlledFragmentReplay.argument .eps (ControlledFragmentPreflight.fragment (.star .eps))]) 3=none
    rw [evV_call_par (source_rule [.lit []] 0 (.lit []) rfl) rfl (by decide)]
    change (match (match evV g x .callByValuePar T []
        (ControlledFragmentReplay.argument .eps (ControlledFragmentPreflight.fragment (.star .eps))) 3 with
      | some (some j) => some (some [pre x 3 j]) | some none => some none | none => none) with
      | some (some W) => valAt (T 0 W) 3 | some none => some none | none => none)=none
    rw [harg]
  exact ⟨hs,(evaluator_eq [.lit []] "aaZ".toList m _ [] _ (Nat.le_refl _)).symm.trans hs⟩

end Shallot.MacroPeg.CBV.ControlledFragmentRecursiveExamples
