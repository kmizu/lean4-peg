import MacroPeg.CBV.SequentialCaptureObserver
import MacroPeg.CBV.IndependentCaptureControl

namespace Shallot.MacroPeg.CBV.SequentialCaptureObserverExamples
open SequentialCaptureObserver
open DependentCaptureFilter (render)
open CaptureTransitionProfile (profile)

def D : RegularCaptureProduct.Machine := ⟨2,fun q c => if c='b' then 1-q else q⟩
theorem observer_valid : D.Valid := by
  refine ⟨by decide,?_⟩
  intro q hq c
  change q<2 at hq
  simp only [D]
  split <;> omega

def body : DependentCaptureFilter.Expr := .seq (.lit ['#']) (.param 0)
def argument : DependentCaptureFilter.Expr := .seq (.param 0) (.lit ['b'])
def original : List MRule := [⟨1,render body⟩,⟨1,.seq (.lit ['!']) (.param 0)⟩]
def B (P : List Nat) (q r : Nat) : MExp := DependentCaptureFilter.filter [] D [P] body q r
def g := grammar D original B

theorem firstOrder : g.FirstOrder := by
  apply grammar_firstOrder
  · intro r hr
    simp only [original,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact DependentCaptureFilter.render_firstOrder body
    · exact ⟨True.intro,True.intro⟩
  · intro P q r
    exact DependentCaptureFilter.filter_firstOrder [] D [P] body q r

theorem source_rule : ruleAtM g.rules 0=some ⟨1,render body⟩ := by
  simp [g,grammar,original,ruleAtM_eq_getElem?]

/-- The row premise of the call theorem is discharged by actual installed
unary PEG rules, uniformly for all retained words and all physical stages. -/
theorem rows (x : List Char) (k : Nat) (w : List Char) (j q r : Nat)
    (hj : j≤x.length) (hq : q<D.width) (hr : r<D.width) :
    valAt (tblV g x .callByValueSeq k (address D original.length (profile D w) q r) [w]) j=
      RegularCaptureProduct.filtered D x q r j (valAt (tblV g x .callByValueSeq k 0 [w]) j) := by
  cases k with
  | zero => rfl
  | succ k =>
      have hprod : ruleAtM g.rules (address D original.length (profile D w) q r)=
          some ⟨1,B (profile D w) q r⟩ :=
        product_rule D original B _ (CaptureTransitionProfile.profile_mem D observer_valid w) q r hq hr
      rw [valAt_tblV_succ hprod [w] hj,valAt_tblV_succ source_rule [w] hj]
      exact IndependentCaptureControl.filter_correct D observer_valid g g x
        (tblV g x .callByValueSeq k) (tblV g x .callByValueSeq k)
        (tblV_ok g x .callByValueSeq k) (tblV_ok g x .callByValueSeq k) [profile D w] [w]
        (DependentCaptureFilter.environment_accurate D [w]) body (by trivial) j hj q r hq hr

/-- This actual parameterized callee is observed on every original input;
there is no externally supplied product-row or successful-argument premise. -/
theorem actual_call_filter (x : List Char) (k : Nat) (E : List (List Char)) (S : List (List Nat))
    (hS : DependentCaptureFilter.Accurate D S E) (p q r : Nat) (hp : p≤x.length)
    (hq : q<D.width) (hr : r<D.width) :
    evV g x .callByValueSeq (tblV g x .callByValueSeq k) E
      (call D original.length (render argument) (fun q r => DependentCaptureFilter.filter [] D S argument q r) q r) p =
      RegularCaptureProduct.filtered D x q r p
        (evV g x .callByValueSeq (tblV g x .callByValueSeq k) E (.call 0 [render argument]) p) := by
  apply call_correct D observer_valid original B 0 _ source_rule x _
    (tblV_sound firstOrder (by decide) k) E (render argument)
    (DependentCaptureFilter.render_firstOrder argument) _ p hp _ (rows x k) q r hq hr
  intro a b ha hb
  exact IndependentCaptureControl.filter_correct D observer_valid g g x
    (tblV g x .callByValueSeq k) (tblV g x .callByValueSeq k)
    (tblV_ok g x .callByValueSeq k) (tblV_ok g x .callByValueSeq k) S E hS argument (by trivial) p hp a b ha hb

theorem actual_call_profile (x : List Char) (k : Nat) (E : List (List Char))
    (p : Nat) (hp : p≤x.length) (K : List Nat → MExp) :
    evV g x .callByValueSeq (tblV g x .callByValueSeq k) E
      (select D original.length 0 (render argument)
        (fun q r => DependentCaptureFilter.filter [] D (E.map (profile D)) argument q r) K) p=
      match evV g x .callByValueSeq (tblV g x .callByValueSeq k) E (.call 0 [render argument]) p with
      | some (some j) => evV g x .callByValueSeq (tblV g x .callByValueSeq k) E (K (profile D (pre x p j))) p
      | other => other :=
  ProfileControl.select_correct D observer_valid g x .callByValueSeq _ E _ _ p
    (fun q r hq hr => actual_call_filter x k E (E.map (profile D))
      (DependentCaptureFilter.environment_accurate D E) p q r hp hq hr) K

def root : MExp := .seq
  (call D original.length (render argument) (fun q r => DependentCaptureFilter.filter [] D [[0,1]] argument q r) 0 0)
  (.seq (.lit ['!']) (.param 0))

def reset : MExp := ProfileControl.select D (render argument)
  (fun q r => DependentCaptureFilter.filter [] D [[0,1]] argument q r)
  (fun P => .call (address D original.length P 0 0) [render argument])

/-- The callee consumes #ab after capturing ab from the retained a plus b.
The parent's a is still present after the child returns. Resetting the
observer at the callee instead of advancing it across ab rejects. -/
theorem physical_parent_return :
    evV g "ab#ab!a".toList .callByValueSeq (tblV g "ab#ab!a".toList .callByValueSeq 2)
      [['a']] root 7=some (some 0) ∧
    evV g "ab#ab!a".toList .callByValueSeq (tblV g "ab#ab!a".toList .callByValueSeq 2)
      [['a']] reset 7=some none := by
  decide +kernel

theorem observer_handoff :
    RegularCaptureProduct.run D 0 "ab".toList=1 ∧
    RegularCaptureProduct.run D 1 "#ab".toList=0 ∧
    RegularCaptureProduct.run D 0 "#ab".toList=1 := by decide +kernel

/-- A failing argument is observed before any callee row. -/
theorem argument_failure :
    evV g ['#'] .callByValueSeq (tblV g ['#'] .callByValueSeq 0) [['a']]
      (call D original.length (render argument) (fun q r => DependentCaptureFilter.filter [] D [[0,1]] argument q r) 0 0) 1=
      some none := by decide +kernel

/-- At clock zero the argument itself succeeds, while the actual callee
row is still undefined. The observer call preserves that partial result. -/
theorem undefined_callee_clock_zero :
    evV g "ab#ab".toList .callByValueSeq (tblV g "ab#ab".toList .callByValueSeq 0) [['a']]
      (.call 0 [render argument]) 5=none ∧
    evV g "ab#ab".toList .callByValueSeq (tblV g "ab#ab".toList .callByValueSeq 0) [['a']]
      (call D original.length (render argument) (fun q r => DependentCaptureFilter.filter [] D [[0,1]] argument q r) 0 0) 5=none := by
  decide +kernel

def wholeArgument (wanted : List Nat) : MExp := select D original.length 0 (render argument)
  (fun q r => DependentCaptureFilter.filter [] D [[0,1]] argument q r)
  (fun P => if P=wanted then .call 0 [render argument] else MExp.failAlways)
def nested (wanted : List Nat) : MExp :=
  .seq (.call 1 [wholeArgument wanted]) (.seq (.lit ['?']) (.param 0))

/-- A new actual unary call retains the complete inner parameterized call
ab#ab and reuses it after !. Both children return to the parent's a. The
whole-call profile is identity, while the inner argument ab toggles parity. -/
theorem nested_whole_capture :
    evV g "ab#ab!ab#ab?a".toList .callByValueSeq
      (tblV g "ab#ab!ab#ab?a".toList .callByValueSeq 4) [['a']] (nested [0,1]) 13=some (some 0) ∧
    evV g "ab#ab!ab#ab?a".toList .callByValueSeq
      (tblV g "ab#ab!ab#ab?a".toList .callByValueSeq 4) [['a']] (nested [1,0]) 13=some none := by
  decide +kernel

end Shallot.MacroPeg.CBV.SequentialCaptureObserverExamples
