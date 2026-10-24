import MacroPeg.CBV.RecursiveScannerHelpers

namespace Shallot.MacroPeg.CBV.RecursiveScannerArguments
open RecursiveScannerHelpers
open RegularCaptureProduct (Node)
open DynamicScannerCapture (observer)

/-- The original recursive helper nodes alone carry the consuming-word
certificate; generated scanner and observer rows do not need this restriction. -/
theorem capture {n : Nat} (M : StatefulScanner.Machine n) (nodes : List Node)
    (hNodes : (nodes.map RegularCaptureProduct.body).all
      (RecursiveCaptureSafety.check M nodes.length)=true)
    (extra : List MRule) (x : List Char) (s : Strategy) (k : Nat)
    (E : List (List Char)) (hE : TotalCaptureSafety.Environment M E)
    (a : DependentCaptureFilter.Expr)
    (ha : RecursiveCaptureSafety.check M nodes.length (DependentCaptureFilter.render a)=true)
    (p j : Nat) (hp : p≤x.length)
    (h : evV (grammar M nodes extra) x s
      (RecursiveParserStability.frozen (bodies M nodes) (grammar M nodes extra) x s k)
      E (DependentCaptureFilter.render a) p=some (some j)) :
    TotalCaptureSafety.Total M (pre x p j) ∧ sfx x p=pre x p j++sfx x j := by
  apply RecursiveCaptureSafety.frozen_capture M (nodes.map RegularCaptureProduct.body)
    (RecursiveCaptureSafety.component_check_sound M _ (by simpa using hNodes))
    (grammar M nodes extra) (originals_installed M nodes extra) x s
    (RecursiveParserStability.pick (bodies M nodes)) (RecursiveParserStability.floor (bodies M nodes) x) k
    _ E hE _ (by simpa using RecursiveCaptureSafety.check_sound M nodes.length _ ha) p j hp h
  intro i hi
  have hlen : nodes.length≤base M nodes := by
    simp [base,RegularCaptureProduct.grammar]
  have hi' : i<(bodies M nodes).length := by rw [length]; simp only [List.length_map] at hi; omega
  simp [RecursiveParserStability.pick,hi']

/-- All partial argument results agree between two actual grammars and
independent user stages, even when captures invoke recursive helper nodes. -/
theorem argument_eq {n : Nat} (M : StatefulScanner.Machine n) (nodes : List Node)
    (hNodes : RegularCaptureProduct.Valid nodes) (left right : List MRule)
    (x : List Char) (k l : Nat) (E : List (List Char))
    (a : DependentCaptureFilter.Expr) (ha : DependentCaptureFilter.Valid nodes a)
    (p : Nat) (hp : p≤x.length) :
    evV (grammar M nodes left) x .callByValuePar
      (RecursiveParserStability.frozen (bodies M nodes) (grammar M nodes left) x .callByValuePar k)
      E (DependentCaptureFilter.render a) p =
    evV (grammar M nodes right) x .callByValueSeq
      (RecursiveParserStability.frozen (bodies M nodes) (grammar M nodes right) x .callByValueSeq l)
      E (DependentCaptureFilter.render a) p := by
  rw [FrozenCaptureControl.base_eval (valid M nodes hNodes) nodes hNodes (observer M) (DynamicScannerCapture.observer_valid M).1
      (installed M nodes left) (product_installed M nodes left)
      (by simp [length,base]) x .callByValuePar k E _ (ParametricHelperControl.render_safe nodes (observer M) a ha) p hp,
    FrozenCaptureControl.base_eval (valid M nodes hNodes) nodes hNodes (observer M) (DynamicScannerCapture.observer_valid M).1
      (installed M nodes right) (product_installed M nodes right)
      (by simp [length,base]) x .callByValueSeq l E _ (ParametricHelperControl.render_safe nodes (observer M) a ha) p hp]

/-- Both real caller grammars install recursive parsing, observer products
and relocated residual scanners together. The full filter result is derived
from actual argument evaluation, without a row or capture oracle. -/
theorem filter_correct {n : Nat} (M : StatefulScanner.Machine n) (nodes : List Node)
    (hNodes : RegularCaptureProduct.Valid nodes) (left right : List MRule)
    (x : List Char) (k l : Nat) (S : List (List Nat)) (E : List (List Char))
    (hS : DependentCaptureFilter.Accurate (observer M) S E)
    (a : DependentCaptureFilter.Expr) (ha : DependentCaptureFilter.Valid nodes a)
    (p q r : Nat) (hp : p≤x.length) (hq : q<(observer M).width) (hr : r<(observer M).width) :
    evV (grammar M nodes right) x .callByValueSeq
      (RecursiveParserStability.frozen (bodies M nodes) (grammar M nodes right) x .callByValueSeq l)
      E (DependentCaptureFilter.filter nodes (observer M) S a q r) p =
      RegularCaptureProduct.filtered (observer M) x q r p
        (evV (grammar M nodes left) x .callByValuePar
          (RecursiveParserStability.frozen (bodies M nodes) (grammar M nodes left) x .callByValuePar k)
          E (DependentCaptureFilter.render a) p) :=
  FrozenCaptureControl.filter_correct (valid M nodes hNodes) nodes hNodes
    (observer M) (DynamicScannerCapture.observer_valid M)
    (installed M nodes left) (installed M nodes right)
    (product_installed M nodes left) (product_installed M nodes right)
    (by simp [length,base]) x k l S E hS a ha p hp q r hq hr

/-- The original scan and the residual scan meet at exactly the same
position after an actual recursive argument capture. Safety and the reached
state are consequences of syntax and execution, not input-shape premises. -/
theorem residual_scan {n : Nat} (M : StatefulScanner.Machine n) (nodes : List Node)
    (hNodes : (nodes.map RegularCaptureProduct.body).all
      (RecursiveCaptureSafety.check M nodes.length)=true)
    (left right : List MRule) (x : List Char) (k l : Nat)
    (E : List (List Char)) (hE : TotalCaptureSafety.Environment M E)
    (a : DependentCaptureFilter.Expr)
    (ha : RecursiveCaptureSafety.check M nodes.length (DependentCaptureFilter.render a)=true)
    (p j : Nat) (hp : p≤x.length) (state : Fin n)
    (h : evV (grammar M nodes left) x .callByValuePar
      (RecursiveParserStability.frozen (bodies M nodes) (grammar M nodes left) x .callByValuePar k)
      E (DependentCaptureFilter.render a) p=some (some j)) :
    ∃ r : Fin n, StatefulScanner.advance M state (pre x p j)=some r ∧
      evV (grammar M nodes left) x .callByValuePar
        (RecursiveParserStability.frozen (bodies M nodes) (grammar M nodes left) x .callByValuePar k)
        E (.call (base M nodes+state.val) []) p =
      evV (grammar M nodes right) x .callByValueSeq
        (RecursiveParserStability.frozen (bodies M nodes) (grammar M nodes right) x .callByValueSeq l)
        E (.call (base M nodes+r.val) []) j := by
  obtain ⟨ht,hcap⟩ := capture M nodes hNodes left x .callByValuePar k E hE a ha p j hp h
  have hj := evV_ok (ClockFreezing.frozen_ok _ _ _ _ _ _) _ p hp j h
  cases hadv : StatefulScanner.advance M state (pre x p j) with
  | none => exact False.elim (ht state hadv)
  | some r =>
    refine ⟨r,rfl,?_⟩
    rw [scanner_eval M nodes left state x .callByValuePar k p E hp,
      scanner_eval M nodes right r x .callByValueSeq l j E hj,hcap,
      StatefulScanner.run_after_prefix M (pre x p j) (sfx x j) state r hadv]

end Shallot.MacroPeg.CBV.RecursiveScannerArguments
