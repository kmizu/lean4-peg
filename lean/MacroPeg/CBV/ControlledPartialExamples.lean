import MacroPeg.CBV.ControlledPartialPreflight

/-! Executions of a caller-controlled partial-capture candidate. The
candidate preflight is not yet an all-input recursive translation. -/
namespace Shallot.MacroPeg.CBV.ControlledPartialExamples
open ControlledPartialCapture
open ControlledPartialPreflight (preflight)
open PartialCodewordCapture (runA look eof)
open RuntimeShiftFilter (scanner)

def translated (test : MExp) : MExp := .seq (look (preflight test))
  (.alt (.seq (look (step test)) (.call 2 [runA,restArgument test]))
    (.seq (.notP (step test)) (.call 3 [runA])))

def tail : MExp := .seq (.lit ['#']) (.seq scanner
  (.seq (.lit ['!','?']) (.seq (.param 0) eof)))
def source : MGrammar := ⟨[⟨1,.seq scanner (.seq (.param 0) tail)⟩]⟩
def target : MGrammar := ⟨[
  ⟨1,.param 0⟩,
  ⟨1,.seq (.lit ['#']) (.param 0)⟩,
  ⟨2,.seq (.lit ['#']) (.seq (.param 0) (CodewordControlFilter.wholeView tail))⟩,
  ⟨1,.seq (.lit ['#']) (.seq (.param 0) tail)⟩]⟩

/-- The same input yields two different successful capture values when
only the retained parent changes. These are changes of length, not just
accept/reject guards around an otherwise fixed capture. -/
theorem retained_value_changes_capture :
    let x := "a#a#a#a#a#a!".toList
    let test := MExp.param 0
    let T := tblV source x .callByValuePar 1
    evV source x .callByValuePar T ["a#a#".toList] (argument test) x.length=
      some (some 7) ∧
    pre x x.length 7="a#a#a".toList ∧
    evV source x .callByValuePar T ["a#a#a#".toList] (argument test) x.length=
      some (some 9) ∧
    pre x x.length 9="a#a".toList := by
  decide +kernel

/-- A real earlier stop leaves a later, different codeword in the input.
The maximal-run checker rejects this successful source prefix. -/
theorem maximal_checker_rejects_valid_prefix :
    let x := "a#a#a#aa#!?a#a".toList
    let test := MExp.notP (.param 0)
    let T := tblV source x .callByValuePar 1
    evV source x .callByValuePar T ["aa".toList] (argument test) x.length=
      some (some 11) ∧
    pre x x.length 11="a#a".toList ∧
    evV source x .callByValuePar T ["a#a".toList]
      (.seq scanner (.param 0)) x.length=some (some 9) ∧
    evV ⟨[⟨1,PartialCodewordPreflight.checkBody⟩]⟩ x .callByValueSeq
      (tblV ⟨[⟨1,PartialCodewordPreflight.checkBody⟩]⟩ x .callByValueSeq 1)
      ["aa".toList] (.call 0 [runA]) x.length=some none := by
  decide +kernel

/-- Both actual grammars retain the earlier partial capture a#a and
reuse it after the later unequal aa# codeword and delimiter. -/
theorem controlled_entry_and_reuse :
    let x := "a#a#a#aa#!?a#a".toList
    let test := MExp.notP (.param 0)
    evV source x .callByValuePar (tblV source x .callByValuePar 1)
      ["aa".toList] (.call 0 [argument test]) x.length=some (some 0) ∧
    evV target x .callByValueSeq (tblV target x .callByValueSeq 1)
      ["aa".toList] (translated test) x.length=some (some 0) := by
  decide +kernel

theorem short_copy_rejected :
    let x := "a#a#a#aa#!?a#".toList
    let test := MExp.notP (.param 0)
    evV source x .callByValuePar (tblV source x .callByValuePar 1)
      ["aa".toList] (.call 0 [argument test]) x.length=some none ∧
    evV target x .callByValueSeq (tblV target x .callByValueSeq 1)
      ["aa".toList] (translated test) x.length=some none := by
  decide +kernel

/-- When the first iteration is rejected, the shorter unary branch keeps
the entire actual capture. The final run can be nonempty or empty. -/
theorem zero_and_empty_capture :
    ∀ x ∈ ["a#a#aa#!?a".toList,"##aa#!?".toList],
    evV source x .callByValuePar (tblV source x .callByValuePar 1)
      ["Z".toList] (.call 0 [argument (.param 0)]) x.length=some (some 0) ∧
    evV target x .callByValueSeq (tblV target x .callByValueSeq 1)
      ["Z".toList] (translated (.param 0)) x.length=some (some 0) := by
  decide +kernel

end Shallot.MacroPeg.CBV.ControlledPartialExamples
