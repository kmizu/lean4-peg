import MacroPeg.CBV.ControlledFragmentPreflight

/-! Physical executions with a caller-selected, nongreedy final fragment.
These examples exercise the proposed entry, not a general compiler theorem. -/
namespace Shallot.MacroPeg.CBV.ControlledFragmentExamples
open PartialCodewordCapture (runA look eof)
open RuntimeShiftFilter (scanner)
open ControlledPartialCapture (step)

open ControlledFragmentReplay (argument preflight entry)

def tail : MExp := .seq (.lit ['X','!']) (.seq (.param 0) eof)
def whole : MExp := .seq (.param 0) (.seq (.param 1) (.param 2))
def source : MGrammar := ⟨[⟨1,.seq scanner (.seq (.param 0) tail)⟩]⟩
def target : MGrammar := ⟨[
  ⟨1,.param 0⟩,
  ⟨1,ControlledFragmentReplay.tailBody⟩,
  ⟨3,.seq scanner (.seq (.param 2)
    (.seq (.lit ['X','!']) (.seq whole eof)))⟩,
  ⟨1,.seq scanner (.seq (.param 0) tail)⟩]⟩

/-- The capture ends before the delimiter, with an a still remaining.
The three real Seq arguments preserve exactly the source's selected value. -/
theorem early_fragment_and_three_captures :
    let x := "aa#aa#aX!aa#a".toList
    let T := tblV source x .callByValuePar 1
    let U := tblV target x .callByValueSeq 1
    let args := [runA,.seq (.lit ['#']) (.star (step (.lit []))),MExp.param 0]
    let p := x.length-4
    evV source x .callByValuePar T [[ 'a' ]]
      (argument (.lit []) (.param 0)) x.length=some (some p) ∧
    pre x x.length p="aa#a".toList ∧
    (sfx x p).head?=some 'a' ∧
    evSeqArgs target x .callByValueSeq U [['a']] args x.length=
      some (some (["aa".toList,['#'],['a']],p)) ∧
    evV source x .callByValuePar T [['a']]
      (.call 0 [argument (.lit []) (.param 0)]) x.length=some (some 0) ∧
    evV target x .callByValueSeq U [['a']]
      (entry (.lit []) (.param 0)) x.length=some (some 0) := by
  decide +kernel

/-- Both choices stop strictly inside the same terminal a-run; changing
only the caller changes the actual fragment and the full retained value. -/
theorem caller_selects_fragment :
    let x := "aaa#aaa#aaaX!".toList
    let T := tblV source x .callByValuePar 1
    evV source x .callByValuePar T [['a']]
      (argument (.lit []) (.param 0)) x.length=some (some (x.length-5)) ∧
    pre x x.length (x.length-5)="aaa#a".toList ∧
    evV source x .callByValuePar T [['a','a']]
      (argument (.lit []) (.param 0)) x.length=some (some (x.length-6)) ∧
    pre x x.length (x.length-6)="aaa#aa".toList := by
  decide +kernel

/-- Empty fragments, longer traces, and the zero-full-word branch all
reuse the whole selected value after the source replay endpoint. -/
theorem varied_captures_and_reuse :
    ∀ xp ∈ [("aaa#aaa#aaX!aaa#aa".toList,"aa".toList),
      ("aa#aa#aa#aX!aa#aa#a".toList,"a".toList),
      ("aa#aa#X!aa#".toList,[]),
      ("aa#aX!a".toList,"a".toList),
      ("aa#X!".toList,[])],
    let x := xp.1
    let parent := xp.2
    evV source x .callByValuePar (tblV source x .callByValuePar 1) [parent]
      (.call 0 [argument (.lit []) (.param 0)]) x.length=some (some 0) ∧
    evV target x .callByValueSeq (tblV target x .callByValueSeq 1) [parent]
      (entry (.lit []) (.param 0)) x.length=some (some 0) := by
  decide +kernel

/-- Unequal adjacent words, wrong shifted fragments, and short later
copies cannot be accepted just because a local prefix comparison passed. -/
theorem malformed_copies_rejected :
    ∀ x ∈ ["aa#aaa#aX!aa#a".toList,"aa#aa#bX!aa#a".toList,
      "aa#aa#aX!aa#".toList,"aa#aa#aX!aa#aa".toList],
    evV source x .callByValuePar (tblV source x .callByValuePar 1) [['a']]
      (.call 0 [argument (.lit []) (.param 0)]) x.length=some none ∧
    evV target x .callByValueSeq (tblV target x .callByValueSeq 1) [['a']]
      (entry (.lit []) (.param 0)) x.length=some none := by
  decide +kernel

/-- A stopping test selects an earlier full-word count even though another
full word is available. The final partial capture still stops inside aa. -/
theorem controlled_stop_and_early_fragment :
    let b := MExp.seq scanner tail
    let S : MGrammar := ⟨[⟨1,.seq scanner (.seq (.param 0) b)⟩]⟩
    let U : MGrammar := ⟨[
      ⟨1,.param 0⟩,⟨1,ControlledFragmentReplay.tailBody⟩,
      ⟨3,.seq scanner (.seq (.param 2) (ControlledFragmentReplay.wholeView b))⟩,
      ⟨1,.seq scanner (.seq (.param 0) b)⟩]⟩
    let G := MExp.notP (.lit ['X'])
    let x := "aa#aa#aa#X!aa#a".toList
    evV S x .callByValuePar (tblV S x .callByValuePar 1) [['a']]
      (argument G (.param 0)) x.length=some (some (x.length-4)) ∧
    pre x x.length (x.length-4)="aa#a".toList ∧
    evV S x .callByValuePar (tblV S x .callByValuePar 1) [['a']]
      (.call 0 [argument G (.param 0)]) x.length=some (some 0) ∧
    evV U x .callByValueSeq (tblV U x .callByValueSeq 1) [['a']]
      (entry G (.param 0)) x.length=some (some 0) := by
  decide +kernel

/-- Reusing the old immediate-# body after this same actual capture
rejects: the real endpoint has a still left before the delimiter. -/
theorem immediate_delimiter_body_fails :
    let x := "aa#aa#aX!aa#a".toList
    let p := x.length-4
    evV target x .callByValueSeq (tblV target x .callByValueSeq 1)
      ["aa".toList,['#'],['a']] (.seq (.lit ['#']) (.param 2)) p=some none ∧
    evV target x .callByValueSeq (tblV target x .callByValueSeq 1)
      ["aa".toList,['#'],['a']] (.seq scanner (.param 2)) p=
        some (some 6) := by
  decide +kernel

theorem firstOrder_grammars_and_entry : source.FirstOrder ∧ target.FirstOrder ∧
    (entry (.lit []) (.param 0)).FirstOrder := by
  simp [MGrammar.FirstOrder,source,target,entry,preflight,argument,
    ControlledFragmentReplay.tailBody,tail,whole,scanner,runA,look,step,
    ControlledPartialPreflight.control,AdjacentCodewordControl.filter,
    CodewordControlFilter.render,NestedScannerArguments.scan,NestedScannerArguments.choice,
    MExp.FirstOrder,MExp.FirstOrderArgs,MExp.failAlways,MExp.andP,eof]

/-- A parser, rather than a promised capture value, selects the fragment
using the caller's retained word. Empty and shorter retained words choose
strictly different stopping points inside the same aaa run. -/
theorem syntactic_fragment_selects_and_reuses :
    let J := MExp.notP (.seq (.param 0) (.lit ['#']))
    let H := ControlledFragmentPreflight.fragment J
    ∀ xp ∈ [("aaa#aaa#aX!aaa#a".toList,['a']),
      ("aaa#aaa#aaX!aaa#aa".toList,[]),
      ("aaa#aaa#X!aaa#".toList,['a','a']),
      ("aaa#aX!a".toList,['a'])],
    let x := xp.1
    let E := [xp.2]
    evV source x .callByValuePar (tblV source x .callByValuePar 1) E
      (.call 0 [argument (.lit []) H]) x.length=some (some 0) ∧
    evV target x .callByValueSeq (tblV target x .callByValueSeq 1) E
      (entry (.lit []) H) x.length=some (some 0) := by
  decide +kernel

/-- These inputs have no valid terminal word. Preflight is finite failure,
including when the fragment itself successfully consumes the entire input. -/
theorem missing_terminal_delimiter :
    let J := MExp.notP (.seq (.param 0) (.lit ['#']))
    let H := ControlledFragmentPreflight.fragment J
    ∀ x ∈ ["".toList,"a".toList,"aaa".toList,"aaZ#".toList,"b#".toList],
    evV target x .callByValueSeq (tblV target x .callByValueSeq 1) [['a']]
      (preflight (.lit []) H) x.length=some none ∧
    evV source x .callByValuePar (tblV source x .callByValuePar 1) [['a']]
      (.call 0 [argument (.lit []) H]) x.length=some none := by
  decide +kernel

/-- Undefined caller tests inside the consuming fragment take precedence
on an input whose scanner comparison would otherwise fail. -/
theorem undefined_fragment_probe :
    let x := "aaZ".toList
    let H := ControlledFragmentPreflight.fragment (.star .eps)
    evV source x .callByValuePar (tblV source x .callByValuePar 1) []
      (.call 0 [argument (.lit []) H]) x.length=none ∧
    evV target x .callByValueSeq (tblV target x .callByValueSeq 1) []
      (preflight (.lit []) H) x.length=none ∧
    evV target x .callByValueSeq (tblV target x .callByValueSeq 1) []
      (entry (.lit []) H) x.length=none := by
  decide +kernel

end Shallot.MacroPeg.CBV.ControlledFragmentExamples
