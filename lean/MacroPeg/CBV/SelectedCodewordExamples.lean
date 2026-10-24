import MacroPeg.CBV.SelectedCodewordGrammar
import MacroPeg.CBV.RuntimePrefixExamples

namespace Shallot.MacroPeg.CBV.SelectedCodewordExamples
open SelectedCodewordGrammar
open SelectedCodewordVerification (step argument)
open RuntimeShiftFilter (scanner)

def condition : MExp := .notP (.lit ['?'])
def tail : MExp := .seq scanner (.seq (.lit ['?']) (.param 0))
def original : MGrammar := source scanner tail
def compiled : MGrammar := target scanner condition tail

theorem all_inputs (x : List Char) (r : Option (List Char)) :
    SObs original .callByValuePar (sourceEntry scanner condition) x r ↔
      SObs compiled .callByValueSeq (targetEntry scanner condition) x r := by
  exact observations_iff scanner condition tail RuntimePrefixExamples.header.pure True.intro
    ⟨LastCodewordGrammar.pure_syntax scanner RuntimePrefixExamples.header.pure,True.intro,True.intro⟩
    RuntimePrefixExamples.code_prefixFree
    (fun x p q hp h => RuntimePrefixExamples.scanner_captured _ x _ _ [] p q hp h) x r

/-- The selected endpoint is before two later codewords, and is not the
endpoint chosen by the previous maximal-header argument. -/
theorem selected_capture :
    let x := "a#a#aa#?a#".toList
    let T := tblV original x .callByValuePar 1
    evV original x .callByValuePar T [] (argument scanner condition) x.length=some (some 8) ∧
    pre x x.length 8="a#".toList ∧
    evV original x .callByValuePar T [] (LastCodewordRotation.argument scanner) x.length=some (some 6) := by
  decide +kernel

/-- A later unequal word belongs to the continuation, not the replay.
The old maximal-run verifier rejects it; the selected verifier accepts. -/
theorem old_verifier_overrejects :
    let x := "a#a#aa#?a#".toList
    evV original x .callByValuePar (tblV original x .callByValuePar 1) []
      (sourceEntry scanner condition) x.length=some (some 0) ∧
    evV compiled x .callByValueSeq (tblV compiled x .callByValueSeq 1) []
      (targetEntry scanner condition) x.length=some (some 0) ∧
    LastCodewordVerification.probe original x .callByValuePar
      (tblV original x .callByValuePar 1) scanner x.length=some none := by
  decide +kernel

/-- Counts zero and three, and short/unequal retained copies. -/
theorem boundaries :
    let eval := fun (text : String) =>
      let x := text.toList
      (evV original x .callByValuePar (tblV original x .callByValuePar 1) []
        (sourceEntry scanner condition) x.length,
       evV compiled x .callByValueSeq (tblV compiled x .callByValueSeq 1) []
        (targetEntry scanner condition) x.length)
    eval "a#aa#?"=(some (some 0),some (some 0)) ∧
    eval "a#a#a#a#aa#?a#a#a#"=(some (some 0),some (some 0)) ∧
    eval "a#a#aa#?"=(some none,some none) ∧
    eval "a#aa#aaa#?a#"=(some none,some none) := by
  decide +kernel

/-- An undefined stop condition stays undefined before any verifier can
reject an unequal pair; preflighting the original argument is essential. -/
theorem undefined_condition :
    let G := MExp.alt condition (.star (.lit []))
    let x := "a#aa#aaa#?a#".toList
    let h := target scanner G tail
    evV original x .callByValuePar (tblV original x .callByValuePar 1) []
      (sourceEntry scanner G) x.length=none ∧
    evV h x .callByValueSeq (tblV h x .callByValueSeq 1) []
      (targetEntry scanner G) x.length=none := by
  decide +kernel

/-- An empty successful step loops at every table and position; the
argument preflight prevents either grammar from treating it as failure. -/
theorem nullable_argument (g : MGrammar) (x : List Char) (s : Strategy)
    (T : ClockFreezing.Table) (E : List (List Char)) (p : Nat) :
    evV g x s T E (argument .eps .eps) p=none := by
  have hh : evV g x s T E (step .eps .eps) p=some (some p) := by
    simp [step,MExp.andP,evV]
  exact evStar_stuck hh (by omega)

theorem undefined_tail :
    let b := MExp.star (.lit [])
    let x := "a#a#aa#?a#".toList
    let g := source scanner b
    let h := target scanner condition b
    evV g x .callByValuePar (tblV g x .callByValuePar 1) []
      (sourceEntry scanner condition) x.length=none ∧
    evV h x .callByValueSeq (tblV h x .callByValueSeq 1) []
      (targetEntry scanner condition) x.length=none := by
  decide +kernel

end Shallot.MacroPeg.CBV.SelectedCodewordExamples
