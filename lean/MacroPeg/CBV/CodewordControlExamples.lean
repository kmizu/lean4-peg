import MacroPeg.CBV.CodewordControlGrammar
import MacroPeg.CBV.RuntimePrefixExamples
import MacroPeg.CBV.NullableStarControl

namespace Shallot.MacroPeg.CBV.CodewordControlExamples
open CodewordControlGrammar
open CodewordControlFilter (render filter)
open RuntimeShiftFilter (scanner)

def control : CodewordControlFilter.Expr :=
  .star (.seq .token (.notP (.test (.lit ['?']))))
def tail : MExp := .seq (.lit ['?']) (.param 0)
def original : MGrammar := source scanner tail
def compiled : MGrammar := target scanner control tail

theorem all_inputs (x : List Char) (r : Option (List Char)) :
    SObs original .callByValuePar (sourceEntry scanner control) x r ↔
      SObs compiled .callByValueSeq (targetEntry scanner control) x r := by
  exact observations_iff scanner control tail RuntimePrefixExamples.header.pure
    ⟨True.intro,True.intro⟩ ⟨True.intro,True.intro⟩ RuntimePrefixExamples.code_prefixFree
    (fun x p q hp h => RuntimePrefixExamples.scanner_captured _ x _ _ [] p q hp h) x r

/-- The target's two runtime values are disjoint parts of the source capture. -/
theorem split_capture :
    let x := "a#a#a#?a#a#".toList
    let T := tblV compiled x .callByValueSeq 1
    evSeqArgs compiled x .callByValueSeq T [] [scanner,render scanner control] x.length=
      some (some (["a#".toList,"a#".toList],7)) ∧
    pre x x.length 7="a#a#".toList := by
  decide +kernel

/-- Input-selected lengths and counts, followed by reuse of the entire
original capture. Short copies and unequal committed captures are rejected. -/
theorem boundaries :
    let eval := fun (text : String) =>
      let x := text.toList
      (evV original x .callByValuePar (tblV original x .callByValuePar 1) []
        (sourceEntry scanner control) x.length,
       evV compiled x .callByValueSeq (tblV compiled x .callByValueSeq 1) []
        (targetEntry scanner control) x.length)
    eval "a#a#?a#"=(some (some 0),some (some 0)) ∧
    eval "a#a#a#?a#a#"=(some (some 0),some (some 0)) ∧
    eval "aa#aa#aa#aa#?aa#aa#aa#"=(some (some 0),some (some 0)) ∧
    eval "###?##"=(some (some 0),some (some 0)) ∧
    eval "a#a#a#?a#"=(some none,some none) ∧
    eval "a#aa#a#?a#aa#"=(some none,some none) := by
  decide +kernel

/-- The raw left arm succeeds with an unequal word. Comparing its capture
must fail permanently, rather than choosing the empty right arm. -/
theorem committed_branch :
    let d : CodewordControlFilter.Expr := .alt (.seq .token (.test (.lit ['?']))) .eps
    let x := "aa#?".toList
    let g : MGrammar := ⟨[]⟩
    let T := tblV g x .callByValueSeq 0
    evV g x .callByValueSeq T ["a#".toList] (render scanner d) x.length=some (some 1) ∧
    evV g x .callByValueSeq T ["a#".toList] (filter scanner d) x.length=some none ∧
    evV g x .callByValueSeq T ["a#".toList]
      (.alt (.seq (.param 0) (.andP (.lit ['?']))) .eps) x.length=some (some x.length) := by
  decide +kernel

/-- Comparing inside star must not silently shorten a successful raw run. -/
theorem committed_star :
    let x := "a#aa#!".toList
    let g : MGrammar := ⟨[]⟩
    let T := tblV g x .callByValueSeq 0
    evV g x .callByValueSeq T ["a#".toList] (render scanner (.star .token)) x.length=some (some 1) ∧
    evV g x .callByValueSeq T ["a#".toList] (filter scanner (.star .token)) x.length=some none ∧
    evV g x .callByValueSeq T ["a#".toList] (.star (.param 0)) x.length=some (some 4) := by
  decide +kernel

/-- Nested empty-success repetitions remain undefined for every table,
input, position, and retained environment. -/
theorem nested_undefined (g : MGrammar) (x : List Char) (s : Strategy)
    (T : ClockFreezing.Table) (E : List (List Char)) (A : MExp) (p : Nat) :
    evV g x s T E (render A (.star (.star .token))) p=none ∧
    evV g x s T E (filter A (.star (.star .token))) p=none := by
  have hh : evV g x s T E (render A (.star (.star .token))) p=none :=
    NullableStarControl.nested_star_none (fun z => evV g x s T E A z) p
  exact ⟨hh,CodewordControlFilter.filter_none g x s T E A _ p hh⟩

/-- The preflight preserves nested undefinedness in the actual grammars. -/
theorem nested_entries_undefined :
    let d : CodewordControlFilter.Expr := .star (.star .token)
    let x := "a#a#".toList
    let g := source scanner tail
    let h := target scanner d tail
    evV g x .callByValuePar (tblV g x .callByValuePar 1) [] (sourceEntry scanner d) x.length=none ∧
    evV h x .callByValueSeq (tblV h x .callByValueSeq 1) [] (targetEntry scanner d) x.length=none := by
  decide +kernel

/-- A genuinely nested repetition consumes several inner iterations in a
single outer iteration and still leaves the exact last word for replay. -/
theorem nested_success :
    let d : CodewordControlFilter.Expr := .star
      (.seq (.star (.seq .token (.test (.seq scanner scanner)))) (.seq .token (.test scanner)))
    let x := "a#a#a#a#a#?a#a#a#a#".toList
    let g := source scanner tail
    let h := target scanner d tail
    let TS := tblV g x .callByValuePar 1
    evV g x .callByValuePar TS [] (render scanner d) (x.length-2)=some (some 11) ∧
    pre x (x.length-2) 11="a#a#a#".toList ∧
    evV g x .callByValuePar TS [] (sourceEntry scanner d) x.length=some (some 0) ∧
    evV h x .callByValueSeq (tblV h x .callByValueSeq 1) [] (targetEntry scanner d) x.length=some (some 0) := by
  decide +kernel

/-- A raw argument that diverges after an unequal word stays undefined,
even though the comparison alone could already finitely reject that word. -/
theorem undefined_argument :
    let d : CodewordControlFilter.Expr := .seq .token (.test (.star (.lit [])))
    let x := "a#aa#".toList
    let g := source scanner tail
    let h := target scanner d tail
    evV g x .callByValuePar (tblV g x .callByValuePar 1) [] (sourceEntry scanner d) x.length=none ∧
    evV h x .callByValueSeq (tblV h x .callByValueSeq 1) [] (targetEntry scanner d) x.length=none := by
  decide +kernel

theorem undefined_continuation :
    let x := "a#a#a#?a#a#".toList
    let b := MExp.star (.lit [])
    let g := source scanner b
    let h := target scanner control b
    evV g x .callByValuePar (tblV g x .callByValuePar 1) [] (sourceEntry scanner control) x.length=none ∧
    evV h x .callByValueSeq (tblV h x .callByValueSeq 1) [] (targetEntry scanner control) x.length=none := by
  decide +kernel

end Shallot.MacroPeg.CBV.CodewordControlExamples
