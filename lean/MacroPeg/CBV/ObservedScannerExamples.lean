import MacroPeg.CBV.ObservedScannerDispatch
import MacroPeg.CBV.DynamicScannerCapture
import MacroPeg.CBV.StatefulActionExamples

namespace Shallot.MacroPeg.CBV.ObservedScannerExamples
open StatefulScanner
open StatefulScannerProduct (pack right)
open ObservedScanner
open ObservedScannerDispatch
abbrev scanner := StatefulActionExamples.machine
abbrev D := DynamicScannerCapture.observer scanner
abbrev valid := DynamicScannerCapture.observer_valid scanner

def before : List MRule := [⟨0,.eps⟩]
def after : Nat := before.length+(rules scanner D valid before.length).length

def tail (t : Fin (2*D.width)) : MExp :=
  if (right valid.1 t).val=2 then .seq (.lit ['!']) (.param 0) else MExp.failAlways

def extra : List MRule := [
  ⟨1,dispatch before.length (1 : Fin 2) (2 : Fin 3) tail⟩,
  ⟨1,dispatch before.length (0 : Fin 2) (1 : Fin 3) tail⟩,
  ⟨1,dispatch before.length (1 : Fin 2) (1 : Fin 3) tail⟩]
def g := ObservedScannerDispatch.grammar scanner D valid before extra

def root (i : Nat) : MExp := .seq (.call i [.lit ['a','b']]) (.seq (.lit ['?']) (.param 0))

set_option maxRecDepth 4000
set_option maxHeartbeats 0

/-- Starting observation at state 1 reaches the sink at b, but the original
scanner from state 0 still consumes ab and stops at !. A second partial
scanner would incorrectly stop one character earlier. -/
theorem sink_keeps_frontier :
    run (machine scanner D valid) (pack (0 : Fin 2) (1 : Fin 3)) "ab!".toList=
      (pack (1 : Fin 2) (2 : Fin 3),['!']) ∧
    (StatefulScannerProduct.common scanner scanner (0 : Fin 2) (1 : Fin 2) "ab!".toList).2=['b','!'] := by
  decide +kernel

theorem captured_handoff :
    advance scanner (0 : Fin 2) ['a','b']=some 1 ∧
    (finish D valid (1 : Fin 3) ['a','b']).val=2 ∧
    run (machine scanner D valid) (pack (0 : Fin 2) (1 : Fin 3)) "ab!ab?c".toList=
      run (machine scanner D valid) (pack (1 : Fin 2) (2 : Fin 3)) "!ab?c".toList := by
  refine ⟨by decide +kernel,by decide +kernel,?_⟩
  exact residual_run scanner D valid 0 1 (1 : Fin 3) ['a','b'] "!ab?c".toList (by decide +kernel)

/-- Actual unary calls bind ab, execute the installed observed scanner,
restore the outer c and accept. Resetting the observer alone rejects. -/
theorem physical_parent_return :
    evV g "ab!ab?c".toList .callByValuePar (tblV g "ab!ab?c".toList .callByValuePar 12)
      [['c']] (root (after+1)) 7=some (some 0) ∧
    evV g "ab!ab?c".toList .callByValueSeq (tblV g "ab!ab?c".toList .callByValueSeq 12)
      [['c']] (root after) 7=some (some 0) ∧
    evV g "ab!ab?c".toList .callByValueSeq (tblV g "ab!ab?c".toList .callByValueSeq 12)
      [['c']] (root (after+2)) 7=some none := by
  decide +kernel

def failing (t : Fin (2*D.width)) : MExp :=
  if (right valid.1 t).val=2 then MExp.failAlways else .lit ['!']
def looping (t : Fin (2*D.width)) : MExp :=
  if (right valid.1 t).val=2 then .star (.lit []) else .lit ['!']

/-- Neither later finite failure nor a nullable loop can select an earlier
scan endpoint or a different final observer state. -/
theorem continuation_commit :
    evV g "ab!".toList .callByValueSeq (tblV g "ab!".toList .callByValueSeq 8) []
      (dispatch before.length (0 : Fin 2) (1 : Fin 3) failing) 3=some none ∧
    evV g "ab!".toList .callByValueSeq (tblV g "ab!".toList .callByValueSeq 8) []
      (dispatch before.length (0 : Fin 2) (1 : Fin 3) looping) 3=none := by
  decide +kernel

theorem empty_scan :
    evV g ['!'] .callByValueSeq (tblV g ['!'] .callByValueSeq 2) []
      (dispatch before.length (0 : Fin 2) (1 : Fin 3)
        (fun t => if (right valid.1 t).val=1 then .lit ['!'] else MExp.failAlways)) 1=some (some 0) := by
  decide +kernel

end Shallot.MacroPeg.CBV.ObservedScannerExamples
