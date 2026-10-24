import MacroPeg.CBV.RecursiveScannerArguments
import MacroPeg.CBV.RecursiveCaptureSafety
import MacroPeg.CBV.FrozenCaptureControl
import MacroPeg.CBV.DynamicScannerCapture

namespace Shallot.MacroPeg.CBV.RecursiveCaptureExamples
open RegularCaptureProduct (Node body)
open RecursiveCaptureSafety
open DependentCaptureFilter (render)

set_option maxRecDepth 4000
set_option maxHeartbeats 0

def machine : StatefulScanner.Machine 2 :=
  ⟨fun q => [('a',if q.val=0 then 1 else 0),('c',q)]⟩

/-- Actual recursive parser H = a H c / empty. -/
def nodes : List Node := [.alt 1 2,.seq 3 4,.lit [],.lit ['a'],.seq 0 5,.lit ['c']]
def argument : DependentCaptureFilter.Expr := .seq (.param 0) (.helper 0)
def D := DynamicScannerCapture.observer machine

theorem syntax_checked : RegularCaptureProduct.Valid nodes ∧
    (nodes.map body).all (check machine nodes.length)=true ∧
    check machine nodes.length (render argument)=true ∧
    DependentCaptureFilter.Valid nodes argument := by
  constructor
  · intro v hv
    simp only [nodes,List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  · constructor
    · decide +kernel
    · refine ⟨by decide +kernel,?_⟩
      change True ∧ 0<nodes.length
      exact ⟨True.intro,by decide +kernel⟩

theorem component_safe : Component machine (nodes.map body) := by
  apply component_check_sound
  simpa using syntax_checked.2.1

/-- Every actual successful argument, with any safe retained environment,
produces a safe complete word. Neither its size nor recursive depth is supplied. -/
theorem actual_capture (extra : List MRule) (x : List Char) (s : Strategy)
    (k : Nat) (E : List (List Char)) (hE : TotalCaptureSafety.Environment machine E)
    (p q : Nat) (hp : p≤x.length)
    (h : evV (FilteredOverlapCaller.extend nodes D extra) x s
      (tblV (FilteredOverlapCaller.extend nodes D extra) x s k) E (render argument) p=some (some q)) :
    TotalCaptureSafety.Total machine (pre x p q) ∧ sfx x p=pre x p q++sfx x q :=
  capture machine (nodes.map body) component_safe _ (nodes_installed nodes D extra)
    x s k E hE _ (by simpa using check_sound machine nodes.length _ syntax_checked.2.2.1) p q hp h

/-- Real observer-product rows, arbitrary user extensions and independent
user clocks preserve the full partial filtering result for a recursive argument. -/
theorem recursive_filter (left right : List MRule) (x : List Char) (k l : Nat)
    (S : List (List Nat)) (E : List (List Char)) (hS : DependentCaptureFilter.Accurate D S E)
    (p q r : Nat) (hp : p≤x.length) (hq : q<D.width) (hr : r<D.width) :
    let helpers := RegularCaptureProduct.component nodes D
    let g := FilteredOverlapCaller.extend nodes D left
    let h := FilteredOverlapCaller.extend nodes D right
    evV h x .callByValueSeq (RecursiveParserStability.frozen helpers h x .callByValueSeq l)
        E (DependentCaptureFilter.filter nodes D S argument q r) p =
      RegularCaptureProduct.filtered D x q r p
        (evV g x .callByValuePar (RecursiveParserStability.frozen helpers g x .callByValuePar k)
          E (render argument) p) :=
  FrozenCaptureControl.filter_correct
    (RegularCaptureProduct.component_valid nodes syntax_checked.1 D (DynamicScannerCapture.observer_valid machine).1)
    nodes syntax_checked.1 D (DynamicScannerCapture.observer_valid machine)
    (RegularCaptureProduct.component_installed nodes D left)
    (RegularCaptureProduct.component_installed nodes D right)
    (RegularCaptureProduct.component_installed nodes D left)
    (RegularCaptureProduct.component_installed nodes D right)
    (by simp [RegularCaptureProduct.component]) x k l S E hS argument syntax_checked.2.2.2 p hp q r hq hr

/-- These physical computations enter H recursively and retain the old ac
before a fresh capture. They consume six and eight characters respectively. -/
theorem changing_captures :
    (let g := RecursiveParserStability.grammar (nodes.map body)
     evV g "acaacc!".toList .callByValuePar (tblV g "acaacc!".toList .callByValuePar 10)
       ["ac".toList] (render argument) 7=some (some 1)) ∧
    (let g := RecursiveParserStability.grammar (nodes.map body)
     evV g "acaaaccc!".toList .callByValueSeq (tblV g "acaaaccc!".toList .callByValueSeq 14)
       ["ac".toList] (render argument) 9=some (some 1)) := by
  decide +kernel

theorem different_actions :
    StatefulScanner.advance machine 0 "acaacc".toList=some 1 ∧
    StatefulScanner.advance machine 0 "acaaaccc".toList=some 0 := by decide +kernel

/-- A successful short recursive alternative stays committed even when its
later suffix rejects. Explicitly spelling the longer helper changes the result. -/
theorem committed_recursive_choice :
    (let g := RecursiveParserStability.grammar (nodes.map body)
     evV g "ac!".toList .callByValuePar (tblV g "ac!".toList .callByValuePar 10) []
       (.seq (render (.alt (.lit []) (.helper 0))) (.lit ['!'])) 3=some none) ∧
    (let g := RecursiveParserStability.grammar (nodes.map body)
     evV g "ac!".toList .callByValueSeq (tblV g "ac!".toList .callByValueSeq 10) []
       (.seq (render (.helper 0)) (.lit ['!'])) 3=some (some 0)) := by decide +kernel

/-- A safe recursive component may still diverge. The finite check does
not smuggle in a termination assumption. -/
theorem cycle_checked_and_undefined :
    check machine 1 (.call 0 [])=true ∧
    ∀ x s k p, p≤x.length →
      evV (RecursiveParserStability.grammar [.call 0 []]) x s
        (tblV (RecursiveParserStability.grammar [.call 0 []]) x s k) [] (.call 0 []) p=none := by
  refine ⟨rfl,?_⟩
  intro x s k p hp
  exact RecursiveParserStability.cycle_undefined (by simp [RecursiveParserStability.grammar,ruleAtM_eq_getElem?])
    x s k [] p hp

/-- The relocated real scanner and the real recursive argument share one
installed helper prefix. The endpoint agreement holds at every user stage. -/
theorem combined_residual (left right : List MRule) (x : List Char) (k l : Nat)
    (E : List (List Char)) (hE : TotalCaptureSafety.Environment machine E)
    (p j : Nat) (hp : p≤x.length)
    (h : evV (RecursiveScannerHelpers.grammar machine nodes left) x .callByValuePar
      (RecursiveParserStability.frozen (RecursiveScannerHelpers.bodies machine nodes)
        (RecursiveScannerHelpers.grammar machine nodes left) x .callByValuePar k)
      E (render argument) p=some (some j)) :
    ∃ r : Fin 2, StatefulScanner.advance machine 0 (pre x p j)=some r ∧
      evV (RecursiveScannerHelpers.grammar machine nodes left) x .callByValuePar
        (RecursiveParserStability.frozen (RecursiveScannerHelpers.bodies machine nodes)
          (RecursiveScannerHelpers.grammar machine nodes left) x .callByValuePar k)
        E (.call (RecursiveScannerHelpers.base machine nodes) []) p =
      evV (RecursiveScannerHelpers.grammar machine nodes right) x .callByValueSeq
        (RecursiveParserStability.frozen (RecursiveScannerHelpers.bodies machine nodes)
          (RecursiveScannerHelpers.grammar machine nodes right) x .callByValueSeq l)
        E (.call (RecursiveScannerHelpers.base machine nodes+r.val) []) j := by
  simpa only [Fin.val_zero,Nat.add_zero] using RecursiveScannerArguments.residual_scan machine nodes syntax_checked.2.1
    left right x k l E hE argument syntax_checked.2.2.1 p j hp 0 h

end Shallot.MacroPeg.CBV.RecursiveCaptureExamples
