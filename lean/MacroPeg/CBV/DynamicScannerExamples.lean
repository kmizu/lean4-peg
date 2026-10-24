import MacroPeg.CBV.DynamicScannerCapture

namespace Shallot.MacroPeg.CBV.DynamicScannerExamples
open DynamicScannerCapture
open DependentCaptureFilter (render table)

def machine : StatefulScanner.Machine 2 :=
  ⟨fun q => if q.val=0 then [('a',1),('c',0)] else [('a',0),('c',1)]⟩
def D := observer machine
def continuation (r : Nat) : MExp :=
  if r=0 then .lit ['Z'] else if r=1 then .lit ['!'] else .lit ['?']
def repeated : DependentCaptureFilter.Expr := .star (.lit ['a'])
def chosen : DependentCaptureFilter.Expr := .alt (.lit ['a']) (.lit ['a','a'])
def program (a : DependentCaptureFilter.Expr) := dispatch [] D [] a 0 continuation

/-- One argument has different transition actions at runtime. Its star
operand changes state, so fixed-action inference cannot type it. -/
theorem changing_star :
    CaptureActionSafety.infer machine CaptureActionSafety.identity (render repeated)=none ∧
    evV (RegularCaptureProduct.grammar [] D) "aaa!".toList .callByValueSeq
      (table [] D "aaa!".toList) [] (program repeated) 4=some (some 0) ∧
    evV (RegularCaptureProduct.grammar [] D) "aaZ".toList .callByValueSeq
      (table [] D "aaZ".toList) [] (program repeated) 3=some (some 0) := by
  decide +kernel

/-- The short successful branch is committed even if its state-selected
continuation fails. Explicitly choosing the long capture would succeed. -/
theorem unequal_choice_commit :
    CaptureActionSafety.infer machine CaptureActionSafety.identity (render chosen)=none ∧
    evV (RegularCaptureProduct.grammar [] D) "aaZ".toList .callByValueSeq
      (table [] D "aaZ".toList) [] (program chosen) 3=some none ∧
    evV (RegularCaptureProduct.grammar [] D) "aaZ".toList .callByValueSeq
      (table [] D "aaZ".toList) [] (program (.lit ['a','a'])) 3=some (some 0) := by
  decide +kernel

/-- Missing transitions remain observable after consuming the entire actual
capture, and are distinguished from both ordinary scanner states. -/
theorem missing_transition :
    evV (RegularCaptureProduct.grammar [] D) "ab?".toList .callByValueSeq
      (table [] D "ab?".toList) [] (program (.lit ['a','b'])) 3=some (some 0) ∧
    RegularCaptureProduct.run D 0 ['a','b','a']=2 ∧
    StatefulScanner.advance machine 0 ['a','b','a']=none := by
  decide +kernel

theorem argument_order :
    evV (RegularCaptureProduct.grammar [] D) ['Z'] .callByValueSeq
      (table [] D ['Z']) [] (program (.lit ['a'])) 1=some none ∧
    evV (RegularCaptureProduct.grammar [] D) ['Z'] .callByValueSeq
      (table [] D ['Z']) [] (program (.star (.lit []))) 1=none ∧
    evV (RegularCaptureProduct.grammar [] D) ['Z'] .callByValueSeq
      (table [] D ['Z']) [] (program repeated) 1=some (some 0) := by
  decide +kernel

/-- The finite observer metadata does not replace the retained string.
After a variable-action capture, the caller still reuses its whole value. -/
theorem retained_value :
    evV (RegularCaptureProduct.grammar [] D) "acaa!ac".toList .callByValueSeq
      (table [] D "acaa!ac".toList) [['a','c']]
      (dispatch [] D [CaptureTransitionProfile.profile D ['a','c']]
        (.seq (.param 0) repeated) 0
        (fun r => .seq (continuation r) (.param 0))) 7=some (some 0) ∧
    evV (RegularCaptureProduct.grammar [] D) "aaZ".toList .callByValueSeq
      (table [] D "aaZ".toList) []
      (dispatch [] D [] repeated 0 (fun r => if r=0 then .star .eps else .eps)) 3=none := by
  decide +kernel

end Shallot.MacroPeg.CBV.DynamicScannerExamples
