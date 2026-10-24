import MacroPeg.CBV.ParameterizedCaptureSafety
import MacroPeg.CBV.SequentialCaptureObserverExamples

namespace Shallot.MacroPeg.CBV.ParameterizedCaptureSafetyExamples
open ParameterizedCaptureSafety
open TotalCaptureSafety (Environment Total)

/-- a toggles the scanner; b, # and ! preserve it; ? is a real frontier. -/
def M : StatefulScanner.Machine 2 := ⟨fun q =>
  [('a',⟨1-q.val,by omega⟩),('b',q),('#',q),('!',q)]⟩

abbrev g := SequentialCaptureObserverExamples.g
abbrev D := SequentialCaptureObserverExamples.D
abbrev hD := SequentialCaptureObserverExamples.observer_valid
abbrev argument := DependentCaptureFilter.render SequentialCaptureObserverExamples.argument

theorem checked : grammarCheck M g=true := by decide +kernel

/-- The positive unary call inside a fresh argument has safe whole output
on all inputs and stages, with no product-row or capture-shape premise. -/
theorem positive_call_capture (x : List Char) (s : Strategy) (k : Nat)
    (E : List (List Char)) (hE : Environment M E) (p j : Nat) (hp : p≤x.length)
    (h : evV g x s (tblV g x s k) E (.call 0 [argument]) p=some (some j)) :
    Total M (pre x p j) ∧ sfx x p=pre x p j++sfx x j :=
  capture M g (grammarCheck_sound M g checked) x s k E hE _ (by decide +kernel) p j hp h

/-- The observed residual scanner is derived from that actual whole call,
including its argument prefix and body, for every original input. -/
theorem positive_call_resumption (x : List Char) (s : Strategy) (k : Nat)
    (E : List (List Char)) (hE : Environment M E) (p j : Nat) (hp : p≤x.length)
    (h : evV g x s (tblV g x s k) E (.call 0 [argument]) p=some (some j))
    (q : Fin 2) (a : Fin D.width) :
    ∃ r, StatefulScanner.advance M q (pre x p j)=some r ∧
      StatefulScanner.run (ObservedScanner.machine M D hD) (StatefulScannerProduct.pack q a) (sfx x p)=
        StatefulScanner.run (ObservedScanner.machine M D hD)
          (StatefulScannerProduct.pack r (ObservedScanner.finish D hD a (pre x p j))) (sfx x j) :=
  observed_resumption M g checked x s k E hE _ (by decide +kernel) p j hp h D hD q a

/-- The whole inner call ab#ab, rather than its argument ab, determines
both state transfers. The scanner still stops at the actual ? frontier. -/
theorem whole_call_states :
    pre "ab#ab?".toList 6 1="ab#ab".toList ∧
    StatefulScanner.advance M 0 "ab#ab".toList=some 0 ∧
    (ObservedScanner.finish D hD (0 : Fin 2) "ab#ab".toList).val=0 ∧
    (StatefulScanner.run M 0 "ab#ab?".toList).2=['?'] := by decide +kernel

/-- Independent values are all checked, even when one argument is itself
a parameterized call. This certifies safety, not a Par/Seq translation. -/
def binary : MGrammar := ⟨[⟨1,.lit ['a']⟩,⟨2,.seq (.param 0) (.param 1)⟩]⟩
def binaryArgument : MExp := .call 1 [.call 0 [.param 0],.param 0]
theorem binary_checked : grammarCheck M binary=true ∧ check M binary.rules.length binaryArgument=true := by
  decide +kernel

theorem independent_captures :
    evV binary "aa?".toList .callByValuePar (tblV binary "aa?".toList .callByValuePar 2)
      [['a']] binaryArgument 3=some (some 1) ∧
    evV binary "aaaaaa?".toList .callByValueSeq (tblV binary "aaaaaa?".toList .callByValueSeq 2)
      [['a']] binaryArgument 7=some (some 1) := by decide +kernel

/-- An actual mutual unary cycle passes the finite checks. It invents no
successful result at any physical clock, on any input. -/
def cycle : MGrammar := ⟨[⟨1,.call 1 [.eps]⟩,⟨1,.call 0 [.eps]⟩]⟩
theorem cycle_checked : grammarCheck M cycle=true := by decide +kernel

theorem cycle_rows (x : List Char) (s : Strategy) (k : Nat) (p : Nat) (hp : p≤x.length) :
    valAt (tblV cycle x s k 0 [[]]) p=none ∧ valAt (tblV cycle x s k 1 [[]]) p=none := by
  induction k with
  | zero => exact ⟨rfl,rfl⟩
  | succ k ih =>
    have h0 : ruleAtM cycle.rules 0=some ⟨1,.call 1 [.eps]⟩ := by rfl
    have h1 : ruleAtM cycle.rules 1=some ⟨1,.call 0 [.eps]⟩ := by rfl
    rw [valAt_tblV_succ h0 [[]] hp,valAt_tblV_succ h1 [[]] hp]
    cases s <;> simpa only [evV,h0,h1,ite_true,evSeqArgs,evParArgs,pre,List.take_zero,
      Nat.sub_self,List.length_cons,List.length_nil] using And.intro ih.2 ih.1

/-- A word crossing the actual frontier is rejected by the finite check,
including inside a positive call argument. -/
theorem crossing_rejected :
    check M binary.rules.length (.call 0 [.lit ['?']])=false ∧
    check M binary.rules.length (.call 0 [.notP (.lit ['?'])])=true := by decide +kernel

end Shallot.MacroPeg.CBV.ParameterizedCaptureSafetyExamples
