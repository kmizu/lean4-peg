import MacroPeg.CBV.LastCodewordGrammar
import MacroPeg.CBV.RuntimePrefixExamples

/-! The earlier positive candidate now has an all-input certificate. -/
namespace Shallot.MacroPeg.CBV.LastCodewordExamples
open LastCodewordCandidate (source target sourceEntry targetEntry)
open RuntimeShiftFilter (scanner)

/-- All finite observations, not merely the uniform positive family. -/
theorem all_inputs (x : List Char) (r : Option (List Char)) :
    SObs source .callByValuePar sourceEntry x r ↔
      SObs target .callByValueSeq targetEntry x r := by
  exact LastCodewordGrammar.observations_iff scanner LastCodewordCandidate.tail
    RuntimePrefixExamples.header.pure ⟨True.intro,True.intro⟩
    RuntimePrefixExamples.code_prefixFree
    (fun x p q hp h => RuntimePrefixExamples.scanner_captured _ x _ _ [] p q hp h) x r

/-- Unequal headers and a short retained copy are finite failures on both
sides. Zero captured words still retain and replay the empty string. -/
theorem boundaries :
    evV source "a#aa#!a#".toList .callByValuePar
      (tblV source "a#aa#!a#".toList .callByValuePar 1) [] sourceEntry 8=some none ∧
    evV target "a#aa#!a#".toList .callByValueSeq
      (tblV target "a#aa#!a#".toList .callByValueSeq 1) [] targetEntry 8=some none ∧
    evV source "a#a#!".toList .callByValuePar
      (tblV source "a#a#!".toList .callByValuePar 1) [] sourceEntry 5=some none ∧
    evV target "a#a#!".toList .callByValueSeq
      (tblV target "a#a#!".toList .callByValueSeq 1) [] targetEntry 5=some none ∧
    evV source "#!".toList .callByValuePar
      (tblV source "#!".toList .callByValuePar 1) [] sourceEntry 2=some (some 0) ∧
    evV target "#!".toList .callByValueSeq
      (tblV target "#!".toList .callByValueSeq 1) [] targetEntry 2=some (some 0) := by
  decide +kernel

/-- The arbitrary continuation may be undefined after successful header
verification; the compiler keeps that undefinedness. -/
theorem undefined_tail :
    let b := MExp.star (.lit [])
    let g := LastCodewordGrammar.source scanner b
    let h := LastCodewordGrammar.target scanner b
    evV g "a#a#".toList .callByValuePar (tblV g "a#a#".toList .callByValuePar 1) []
      (LastCodewordGrammar.sourceEntry scanner) 4=none ∧
    evV h "a#a#".toList .callByValueSeq (tblV h "a#a#".toList .callByValueSeq 1) []
      (LastCodewordGrammar.targetEntry scanner) 4=none := by
  decide +kernel

end Shallot.MacroPeg.CBV.LastCodewordExamples
