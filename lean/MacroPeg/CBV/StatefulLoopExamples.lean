import MacroPeg.CBV.StatefulScannerFastTable
import MacroPeg.CBV.PartialCodewordCapture
import MacroPeg.CBV.StatefulLoopFusion
import MacroPeg.CBV.ScannerArgumentFusion

namespace Shallot.MacroPeg.CBV.StatefulLoopExamples
open StatefulLoopFusion
open PartialCodewordCapture (eof)

/-- Alternating a/b and c loops, with the actual transition boundary. -/
def machine : StatefulScanner.Machine 2 :=
  ⟨fun q => if q.val=0 then [('a',1),('c',0)] else [('b',0)]⟩
def pair : MExp := .lit ['a','b']
def childArgument : MExp := .seq (.notP (.call 2 [.lit []])) (.seq (.param 0) (.star (.alt pair (.lit ['c']))))
def tails : List MExp := [
  .alt (.seq (.lit ['!']) (.param 0))
    (.seq (.lit ['Z']) (.seq (.call 3 [childArgument])
      (.seq (.lit ['?']) (.param 0)))),
  .seq (.lit ['X']) (.seq (.call 2 [.seq (.param 0) pair])
    (.seq (.lit ['?']) (.param 0)))]
def root : MExp := .seq (.call 2 [.lit ['c']]) eof
def input := ("caZ"++"cabaX"++"cabab!cabab"++"?cab?c").toList

theorem valid : Valid machine 0 tails ∧ Supported machine 0 root := by
  constructor
  · intro e he
    simp only [tails,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl <;> simp only [Supported,childArgument,pair,LoopCaptureSafety.Safe,LoopCaptureSafety.Loop] <;> decide +kernel
  · simp only [root,eof,Supported,LoopCaptureSafety.Safe,LoopCaptureSafety.Loop]
    decide +kernel

/-- Captures c → cab → cabab remain available after the stateful
consuming prefix, which reads additional characters before either body runs. -/
theorem mutual_returns :
    evV (grammar machine 0 tails) input .callByValuePar
      (tblV (grammar machine 0 tails) input .callByValuePar (input.length+4)) [] root input.length=some (some 0) ∧
    evV (grammar machine 0 tails) input .callByValueSeq
      (tblV (grammar machine 0 tails) input .callByValueSeq (input.length+4)) [] root input.length=some (some 0) := by
  constructor <;> apply StatefulScannerFastTable.physical machine _ _ _
    (helper_rule machine 0 tails) 3 <;> decide +kernel

/-- The actual child argument uses old c plus a fresh greedy star and a
recursive negative query. Its result ends before the body's extra a. -/
theorem actual_child_capture :
    let x := ("cabaX"++"cabab!cabab"++"?cab").toList
    evV (grammar machine 0 tails) x .callByValuePar
      (tblV (grammar machine 0 tails) x .callByValuePar (x.length+4)) [['c']] childArgument x.length=
        some (some (x.length-3)) ∧
    pre x x.length (x.length-3)="cab".toList ∧
    (StatefulScanner.run machine 0 x).2=("X"++"cabab!cabab"++"?cab").toList := by
  constructor
  · apply StatefulScannerFastTable.physical machine _ _ _ (helper_rule machine 0 tails) 3
    decide +kernel
  · decide +kernel

theorem short_copies_rejected :
    ∀ x∈[("caZ"++"cabaX"++"cabab!caba"++"?cab?c").toList,
      ("caZ"++"cabaX"++"cabab!cabab"++"?ca?c").toList,
      ("caZ"++"cabaX"++"cabab!cabab"++"?cab?").toList],
    evV (grammar machine 0 tails) x .callByValuePar
      (tblV (grammar machine 0 tails) x .callByValuePar (x.length+4)) [] root x.length=some none ∧
    evV (grammar machine 0 tails) x .callByValueSeq
      (tblV (grammar machine 0 tails) x .callByValueSeq (x.length+4)) [] root x.length=some none := by
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl
  all_goals
    constructor <;> apply StatefulScannerFastTable.physical machine _ _ _ (helper_rule machine 0 tails) 3 <;> decide +kernel

/-- Preservation is for all original strings, not only these executions. -/
theorem mutual_language (x : List Char) :
    SObs (grammar machine 0 tails) .callByValuePar root x (some []) ↔
      SObs (grammar machine 0 tails) .callByValueSeq root x (some []) :=
  observations_iff machine 0 tails valid.1 root valid.2 x (some [])

/-- A character-set scanner would consume one extra a and change the
boundary. The actual finite-state prefix keeps the original acceptance. -/
theorem stateful_boundary :
    let ts := [MExp.seq (.lit ['a','!']) (.param 0)]
    let g := grammar machine 0 ts
    let wrong : MGrammar := ⟨g.rules.take 2++[⟨1,.seq (NestedScannerArguments.scan ['a','b']) ((ts[0]?).getD MExp.failAlways)⟩]⟩
    let e := MExp.seq (.call 2 [pair]) eof
    let x := "ababaa!ab".toList
    evV g x .callByValuePar (tblV g x .callByValuePar (x.length+4)) [] e x.length=some (some 0) ∧
    evV g x .callByValueSeq (tblV g x .callByValueSeq (x.length+4)) [] e x.length=some (some 0) ∧
    evV wrong x .callByValuePar (tblV wrong x .callByValuePar (x.length+4)) [] e x.length=some none ∧
    evV wrong x .callByValueSeq (tblV wrong x .callByValueSeq (x.length+4)) [] e x.length=some none := by
  refine ⟨?_,?_,?_,?_⟩
  all_goals
    apply StatefulScannerFastTable.physical machine _ _ _ ?_ 3
    · decide +kernel
    · intro q
      rcases q with ⟨i,hi⟩
      cases i with
      | zero => rfl
      | succ i => cases i with
        | zero => rfl
        | succ i => omega

/-- Outside the loop condition, resetting the scanner state loses a real
transition. This refutes that reset method, not language-class equality. -/
theorem nonloop_boundary :
    let g := grammar machine 0 [MExp.seq (.lit ['a','!']) (.param 0)]
    let e := MExp.seq (.call 2 [.lit ['a']]) eof
    let x := "abaa!a".toList
    ¬ LoopCaptureSafety.Loop machine 0 ['a'] ∧
    evV g x .callByValuePar (tblV g x .callByValuePar (x.length+4)) [] e x.length=some (some 0) ∧
    evV g x .callByValueSeq (tblV g x .callByValueSeq (x.length+4)) [] e x.length=some none := by
  refine ⟨?_,?_,?_⟩
  · change StatefulScanner.advance machine 0 ['a']≠some 0
    decide +kernel
  all_goals apply StatefulScannerFastTable.physical machine _ _ _ (helper_rule machine 0 _) 3 <;> decide +kernel

/-- Empty captures are retained; failed or undefined arguments precede
user rows, including the empty physical table. -/
theorem empty_and_argument_order :
    let g := grammar machine 0 [MExp.seq (.lit ['!']) (.param 0)]
    let x := "abab!".toList
    let e := MExp.seq (.call 2 [.lit []]) eof
    evV g x .callByValuePar (tblV g x .callByValuePar (x.length+4)) [] e x.length=some (some 0) ∧
    evV g x .callByValueSeq (tblV g x .callByValueSeq (x.length+4)) [] e x.length=some (some 0) ∧
    (∀ k∈[0,8],
      evV g ['!'] .callByValuePar (tblV g ['!'] .callByValuePar k) [] (.call 2 [pair]) 1=some none ∧
      evV g ['!'] .callByValueSeq (tblV g ['!'] .callByValueSeq k) [] (.call 2 [pair]) 1=some none ∧
      evV g x .callByValuePar (tblV g x .callByValuePar k) [] (.call 2 [.star (.lit [])]) x.length=none ∧
      evV g x .callByValueSeq (tblV g x .callByValueSeq k) [] (.call 2 [.star (.lit [])]) x.length=none) := by
  refine ⟨?_,?_,?_⟩
  · apply StatefulScannerFastTable.physical machine _ _ _ (helper_rule machine 0 _) 3
    decide +kernel
  · apply StatefulScannerFastTable.physical machine _ _ _ (helper_rule machine 0 _) 3
    decide +kernel
  · decide +kernel

end Shallot.MacroPeg.CBV.StatefulLoopExamples
