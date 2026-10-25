import MacroPeg.CBV.RepeatedFrontierTransfer

namespace Shallot.MacroPeg.CBV.RepeatedFrontierExamples
open DelimiterTemplate DelimitedWordPattern
open SynchronizedStarFrontier RepeatedFrontierTransfer

def d : Char := '#'
def pattern : List Nat := [1,0]
def args : List MExp := [.lit ['a'],.lit ['a','b']]
def original : MGrammar := ⟨[⟨2,.star (compile d (sourceParts d pattern))⟩]⟩
def projected : MGrammar := ⟨[⟨0,.eps⟩,⟨1,afterLoop d 0 pattern⟩,⟨1,afterLoop d 1 pattern⟩]⟩
def sourceValue (x : List Char) : Res :=
  evV original x .callByValuePar (tblV original x .callByValuePar 1) [] (.call 0 args) x.length
def viewValue (i : Nat) (x : List Char) : Res :=
  evV projected x .callByValueSeq (tblV projected x .callByValueSeq 1) []
    (.call (1+i) [DelimitedPatternEvaluation.argument args i]) x.length
def values := [['a'],['a','b']]
def earlySmall : List Char := ['a','b','#','a','#','a','b','#','b','#']
def earlyLarge : List Char := ['a','b','#','a','#','x','#','a','#']

theorem actual_captures :
    [earlySmall,earlyLarge].all (fun x => evParArgs original x .callByValuePar
      (tblV original x .callByValuePar 1) [] args x.length==some (some values))=true := by decide +kernel

theorem small_stops_first :
    sourceValue earlySmall=some (some 5) ∧
      viewValue 0 earlySmall=some (some 5) ∧ viewValue 1 earlySmall=some (some 0) := by decide +kernel

theorem large_stops_first :
    sourceValue earlyLarge=some (some 4) ∧
      viewValue 0 earlyLarge=some (some 0) ∧ viewValue 1 earlyLarge=some (some 4) := by decide +kernel

theorem exact_maximum :
    [earlySmall,earlyLarge].all (fun x =>
      sourceValue x==maximum [viewValue 0 x,viewValue 1 x])=true := by decide +kernel

/-- A fixed choice of the final consuming projection cannot implement
this bare-star translation on all inputs. No language-class claim follows. -/
theorem no_fixed_projection : ∀ i, i<2 → ∃ x, sourceValue x≠viewValue i x := by
  intro i hi
  cases i with
  | zero => exact ⟨earlyLarge,by decide +kernel⟩
  | succ i =>
    have hz : i=0 := by omega
    subst i
    exact ⟨earlySmall,by decide +kernel⟩

theorem continuation_uses_original_frontier :
    evV original earlySmall .callByValuePar (tblV original earlySmall .callByValuePar 1) []
      (.seq (.call 0 args) (.lit ['a','b','#','b','#'])) earlySmall.length=some (some 0) ∧
    evV original earlyLarge .callByValuePar (tblV original earlyLarge .callByValuePar 1) []
      (.seq (.call 0 args) (.lit ['x','#','a','#'])) earlyLarge.length=some (some 0) := by decide +kernel

theorem fixed_large_projection_loses_continuation :
    evV projected earlySmall .callByValueSeq (tblV projected earlySmall .callByValueSeq 1) []
      (.seq (.call 2 [.lit ['a','b']]) (.lit ['a','b','#','b','#'])) earlySmall.length=some none := by decide +kernel

theorem fixed_small_projection_loses_continuation :
    evV projected earlyLarge .callByValueSeq (tblV projected earlyLarge .callByValueSeq 1) []
      (.seq (.call 1 [.lit ['a']]) (.lit ['x','#','a','#'])) earlyLarge.length=some none := by decide +kernel

def zeroInput : List Char := ['a','b','#','b','#']
theorem zero_iterations_need_separate_branch :
    sourceValue zeroInput=some (some 5) ∧
      viewValue 0 zeroInput=some none ∧ viewValue 1 zeroInput=some (some 0) ∧
      maximum [viewValue 0 zeroInput,viewValue 1 zeroInput]=none := by decide +kernel

/-- Ordered argument failure is still observable before a zero-iteration
body. The endpoint calculation assumes successful actuals explicitly. -/
theorem actual_failure_before_loop :
    evV original ['x'] .callByValuePar (tblV original ['x'] .callByValuePar 1) [] (.call 0 args) 1=some none := by decide +kernel

theorem clock_zero_is_undefined :
    evV original earlySmall .callByValuePar (tblV original earlySmall .callByValuePar 0) [] (.call 0 args) earlySmall.length=none ∧
    evV projected earlySmall .callByValueSeq (tblV projected earlySmall .callByValueSeq 0) [] (.call 1 [.lit ['a']]) earlySmall.length=none := by decide +kernel

end Shallot.MacroPeg.CBV.RepeatedFrontierExamples
