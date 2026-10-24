import MacroPeg.CBV.StatefulActionFusion
import MacroPeg.CBV.StatefulScannerFastTable
import MacroPeg.CBV.PartialCodewordCapture

namespace Shallot.MacroPeg.CBV.StatefulActionExamples
open StatefulActionFusion
open CaptureActionSafety (identity action)
open PartialCodewordCapture (eof)

def machine : StatefulScanner.Machine 2 :=
  ⟨fun q => if q.val=0 then [('a',1),('c',0)] else [('a',0),('b',1),('c',1)]⟩
def toggle := action machine ['a']
def childArgument : MExp := .seq (.notP (.call 2 [.lit ['a']]))
  (.seq (.param 0) (.seq (.star (.lit ['c'])) (.lit ['a'])))
def specs : List (Spec 2) := [
  ⟨toggle,.alt (.seq (.lit ['!']) (.param 0))
    (.seq (.lit ['Z']) (.seq (.call 3 [childArgument]) (.seq (.lit ['?']) (.param 0))))⟩,
  ⟨identity,.seq (.lit ['X']) (.seq (.call 2 [.seq (.param 0) (.lit ['a'])])
    (.seq (.lit ['?']) (.param 0)))⟩]
def root : MExp := .seq (.call 2 [.lit ['a']]) eof
def input := ("abbZ"++"accaabX"++"accaab!accaa"++"?acca?a").toList

theorem valid : Valid machine 0 specs ∧ Supported machine specs identity root := by
  constructor
  · intro r hr
    simp only [specs,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl <;>
      dsimp [Supported,childArgument,specs]
    all_goals simp only [List.getElem?_cons_zero]
    all_goals decide +kernel
  · dsimp [root,eof,Supported,specs]
    simp only [List.getElem?_cons_zero]
    decide +kernel

/-- Every source user starts its scan at 0. The generated target chooses
1 for the odd action and 0 for the identity action, using only finite data. -/
theorem generated_resumption_states :
    header (0 : Fin 2) true (specs[0])=0 ∧ header (0 : Fin 2) true (specs[1])=0 ∧
    header (0 : Fin 2) false (specs[0])=1 ∧ header (0 : Fin 2) false (specs[1])=0 := by
  decide +kernel

/-- Non-loop a → loop acca → non-loop accaa, with fresh c* and recursive
argument queries. Extra b/ab prefix transitions precede whole-value reuse. -/
theorem mutual_returns :
    evV (grammar machine 0 true specs) input .callByValuePar
      (tblV (grammar machine 0 true specs) input .callByValuePar (input.length+4)) [] root input.length=some (some 0) ∧
    evV (grammar machine 0 false specs) input .callByValueSeq
      (tblV (grammar machine 0 false specs) input .callByValueSeq (input.length+4)) [] root input.length=some (some 0) := by
  constructor
  · apply StatefulScannerFastTable.physical machine _ _ _ (helper_rule machine 0 true specs) 3
    decide +kernel
  · apply StatefulScannerFastTable.physical machine _ _ _ (helper_rule machine 0 false specs) 3
    decide +kernel

theorem actual_child_capture :
    let x := ("accaabX"++"accaab!accaa"++"?acca").toList
    evV (grammar machine 0 true specs) x .callByValuePar
      (tblV (grammar machine 0 true specs) x .callByValuePar (x.length+4)) [['a']] childArgument x.length=
        some (some (x.length-4)) ∧
    pre x x.length (x.length-4)="acca".toList ∧
    StatefulScanner.advance machine 0 (pre x x.length (x.length-4))=some 0 := by
  constructor
  · apply StatefulScannerFastTable.physical machine _ _ _ (helper_rule machine 0 true specs) 3
    decide +kernel
  · decide +kernel

theorem short_copies_rejected :
    ∀ x∈[("abbZ"++"accaabX"++"accaab!acca"++"?acca?a").toList,
      ("abbZ"++"accaabX"++"accaab!accaa"++"?acc?a").toList,
      ("abbZ"++"accaabX"++"accaab!accaa"++"?acca?").toList],
    evV (grammar machine 0 true specs) x .callByValuePar
      (tblV (grammar machine 0 true specs) x .callByValuePar (x.length+4)) [] root x.length=some none ∧
    evV (grammar machine 0 false specs) x .callByValueSeq
      (tblV (grammar machine 0 false specs) x .callByValueSeq (x.length+4)) [] root x.length=some none := by
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl
  all_goals
    constructor
    · apply StatefulScannerFastTable.physical machine _ _ _ (helper_rule machine 0 true specs) 3
      decide +kernel
    · apply StatefulScannerFastTable.physical machine _ _ _ (helper_rule machine 0 false specs) 3
      decide +kernel

theorem mutual_language (x : List Char) :
    SObs (grammar machine 0 true specs) .callByValuePar root x (some []) ↔
      SObs (grammar machine 0 false specs) .callByValueSeq root x (some []) :=
  observations_iff machine 0 specs valid.1 identity root valid.2 x (some [])

/-- The corrected Seq prefix must start at 1 after capturing a. Simply
running the original source grammar under Seq stops before b and rejects. -/
theorem state_change_requires_resumption :
    let rs : List (Spec 2) := [⟨toggle,.seq (.lit ['!']) (.param 0)⟩]
    let x := "ab!a".toList
    let e := MExp.seq (.call 2 [.lit ['a']]) eof
    StatefulScanner.advance machine 0 ['a']=some 1 ∧
    evV (grammar machine 0 true rs) x .callByValuePar
      (tblV (grammar machine 0 true rs) x .callByValuePar (x.length+2)) [] e x.length=some (some 0) ∧
    evV (grammar machine 0 false rs) x .callByValueSeq
      (tblV (grammar machine 0 false rs) x .callByValueSeq (x.length+2)) [] e x.length=some (some 0) ∧
    evV (grammar machine 0 true rs) x .callByValueSeq
      (tblV (grammar machine 0 true rs) x .callByValueSeq (x.length+2)) [] e x.length=some none := by
  refine ⟨by decide +kernel,?_,?_,?_⟩
  · apply StatefulScannerFastTable.physical machine _ _ _ (helper_rule machine 0 true _) 1
    decide +kernel
  · apply StatefulScannerFastTable.physical machine _ _ _ (helper_rule machine 0 false _) 1
    decide +kernel
  · apply StatefulScannerFastTable.physical machine _ _ _ (helper_rule machine 0 true _) 1
    decide +kernel

/-- A single endpoint state cannot type a parameter replay after another
prefix: a and ab agree from 0, but only a can advance from 1. -/
theorem whole_action_needed :
    StatefulScanner.advance machine 0 ['a']=some 1 ∧
    StatefulScanner.advance machine 0 ['a','b']=some 1 ∧
    StatefulScanner.advance machine 1 ['a']=some 0 ∧
    StatefulScanner.advance machine 1 ['a','b']=none ∧
    CaptureActionSafety.equal (action machine ['a']) (action machine ['a','b'])=false := by
  decide +kernel

/-- Both alternatives have the same finite action, but their selected
capture cannot change after its eventual replay fails. -/
theorem committed_same_action_choice :
    let rs : List (Spec 2) := [⟨toggle,.seq (.lit ['!']) (.param 0)⟩]
    let x := "acb!ac".toList
    let e := MExp.seq (.call 2 [.alt (.lit ['a']) (.lit ['a','c'])]) eof
    CaptureActionSafety.fits machine identity (.alt (.lit ['a']) (.lit ['a','c'])) toggle=true ∧
    evV (grammar machine 0 true rs) x .callByValuePar
      (tblV (grammar machine 0 true rs) x .callByValuePar (x.length+2)) [] e x.length=some none ∧
    evV (grammar machine 0 false rs) x .callByValueSeq
      (tblV (grammar machine 0 false rs) x .callByValueSeq (x.length+2)) [] e x.length=some none ∧
    evV (grammar machine 0 false rs) x .callByValueSeq
      (tblV (grammar machine 0 false rs) x .callByValueSeq (x.length+2)) []
        (.seq (.call 2 [.lit ['a','c']]) eof) x.length=some (some 0) := by
  refine ⟨by decide +kernel,?_,?_,?_⟩
  · apply StatefulScannerFastTable.physical machine _ _ _ (helper_rule machine 0 true _) 1
    decide +kernel
  · apply StatefulScannerFastTable.physical machine _ _ _ (helper_rule machine 0 false _) 1
    decide +kernel
  · apply StatefulScannerFastTable.physical machine _ _ _ (helper_rule machine 0 false _) 1
    decide +kernel

/-- The finite checker rejects unknown branch actions and a star whose
iterations can change the action. This remains a typed source family. -/
theorem inference_limits :
    CaptureActionSafety.fits machine identity (.alt (.lit ['a']) .eps) toggle=false ∧
    CaptureActionSafety.fits machine identity (.star (.lit ['a'])) identity=false := by
  decide +kernel

/-- Empty captures are retained. Failed and undefined arguments still run
before either source or specialized target user row, including clock zero. -/
theorem empty_and_argument_order :
    let ids : List (Spec 2) := [⟨identity,.seq (.lit ['!']) (.param 0)⟩]
    let odds : List (Spec 2) := [⟨toggle,.seq (.lit ['!']) (.param 0)⟩]
    let x := "ab!".toList
    let e := MExp.seq (.call 2 [.lit []]) eof
    evV (grammar machine 0 true ids) x .callByValuePar
      (tblV (grammar machine 0 true ids) x .callByValuePar (x.length+2)) [] e x.length=some (some 0) ∧
    evV (grammar machine 0 false ids) x .callByValueSeq
      (tblV (grammar machine 0 false ids) x .callByValueSeq (x.length+2)) [] e x.length=some (some 0) ∧
    (∀ k∈[0,1],
      evV (grammar machine 0 true odds) ['!'] .callByValuePar
        (tblV (grammar machine 0 true odds) ['!'] .callByValuePar k) [] (.call 2 [.lit ['a']]) 1=some none ∧
      evV (grammar machine 0 false odds) ['!'] .callByValueSeq
        (tblV (grammar machine 0 false odds) ['!'] .callByValueSeq k) [] (.call 2 [.lit ['a']]) 1=some none ∧
      evV (grammar machine 0 true ids) x .callByValuePar
        (tblV (grammar machine 0 true ids) x .callByValuePar k) [] (.call 2 [.star (.lit [])]) x.length=none ∧
      evV (grammar machine 0 false ids) x .callByValueSeq
        (tblV (grammar machine 0 false ids) x .callByValueSeq k) [] (.call 2 [.star (.lit [])]) x.length=none) := by
  refine ⟨?_,?_,?_⟩
  · apply StatefulScannerFastTable.physical machine _ _ _ (helper_rule machine 0 true _) 1
    decide +kernel
  · apply StatefulScannerFastTable.physical machine _ _ _ (helper_rule machine 0 false _) 1
    decide +kernel
  · decide +kernel

end Shallot.MacroPeg.CBV.StatefulActionExamples
