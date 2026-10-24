import MacroPeg.CBV.SequentialRecursiveObserver
import MacroPeg.CBV.SequentialCaptureObserverExamples

namespace Shallot.MacroPeg.CBV.SequentialRecursiveObserverExamples
open SequentialRecursiveObserver
open CaptureTransitionProfile (profile)
abbrev Arg := SequentialRecursiveObserver.Expr
abbrev D := SequentialCaptureObserverExamples.D
abbrev hD := SequentialCaptureObserverExamples.observer_valid

/-- The first two rules recurse with growing actual argument values.
The third retains an entire recursive call as a fresh argument. -/
def bodies : List Arg := [
  .alt (.seq (.lit ['c']) (.seq (.user 1 (.seq (.param 0) (.lit ['b']))) (.param 0))) (.param 0),
  .alt (.seq (.lit ['b']) (.seq (.user 0 (.seq (.param 0) (.lit ['b']))) (.param 0))) (.param 0),
  .seq (.lit ['!']) (.param 0)]
def inner : Arg := .user 0 (.param 0)
def outer : Arg := .seq (.user 2 inner) (.seq (.lit ['?']) (.param 0))
def w : List Char := ['a','c']++"ab".toList++['b']++"abb".toList++"abb".toList++"ab".toList++['a']
def input : List Char := w++['!']++w++['?','a']

set_option maxRecDepth 4000
set_option maxHeartbeats 0

theorem checked : bodies.all (check bodies.length)=true ∧
    check bodies.length inner=true ∧ check bodies.length outer=true := by decide +kernel

/-- Actual users 0 → 1 → 0 retain a → ab → abb. Each parent then reuses
its original whole value. The outer user captures and reuses the whole w. -/
theorem source_parent_return :
    evV (source bodies) input .callByValueSeq (tblV (source bodies) input .callByValueSeq 4)
      [['a']] (render inner) input.length=some (some (input.length-w.length)) ∧
    evV (source bodies) input .callByValueSeq (tblV (source bodies) input .callByValueSeq 4)
      [['a']] (render outer) input.length=some (some 0) := by decide +kernel

theorem whole_profile : profile D w=[1,0] ∧ profile D ['a']=[0,1] ∧
    profile D input=[0,1] ∧ pre input input.length (input.length-w.length)=w := by decide +kernel

/-- The generated ordinary table observes the entire recursive expression,
including argument consumption, body consumption and restored parent values. -/
theorem product_parent_return :
    evV (grammar D bodies) input .callByValueSeq (tblV (grammar D bodies) input .callByValueSeq 4)
      [['a']] (filter D bodies [[0,1]] outer 0 0) input.length=some (some 0) ∧
    evV (grammar D bodies) input .callByValueSeq (tblV (grammar D bodies) input .callByValueSeq 4)
      [['a']] (filter D bodies [[0,1]] outer 0 1) input.length=some none := by
  constructor
  · have h := source_filter_correct D hD bodies checked.1 input 4 outer checked.2.2 [['a']]
      input.length (Nat.le_refl _) 0 0 (by decide) (by decide)
    rw [source_parent_return.2] at h
    exact h.trans (by decide +kernel)
  · have h := source_filter_correct D hD bodies checked.1 input 4 outer checked.2.2 [['a']]
      input.length (Nat.le_refl _) 0 1 (by decide) (by decide)
    rw [source_parent_return.2] at h
    exact h.trans (by decide +kernel)

def continuation (wanted P : List Nat) : MExp :=
  if P=wanted then render outer else MExp.failAlways

def selected (wanted : List Nat) : MExp :=
  ProfileControl.select D (render inner) (fun q r => filter D bodies [[0,1]] inner q r) (continuation wanted)

/-- Choosing metadata for the entire inner recursive call accepts.
Choosing its initial argument's metadata rejects, in the same actual grammar. -/
theorem selected_whole_call :
    evV (grammar D bodies) input .callByValueSeq (tblV (grammar D bodies) input .callByValueSeq 4)
      [['a']] (selected [1,0]) input.length=some (some 0) ∧
    evV (grammar D bodies) input .callByValueSeq (tblV (grammar D bodies) input .callByValueSeq 4)
      [['a']] (selected [0,1]) input.length=some none := by
  have hi := (original_eval D bodies checked.1 input 4 inner checked.2.1 [['a']] input.length (Nat.le_refl _)).symm.trans source_parent_return.1
  have ho := (original_eval D bodies checked.1 input 4 outer checked.2.2 [['a']] input.length (Nat.le_refl _)).symm.trans source_parent_return.2
  have hs (wanted : List Nat) := select_result D hD bodies checked.1 input 4 inner checked.2.1 [['a']]
    input.length (Nat.le_refl _) (continuation wanted)
  constructor
  · have h := hs [1,0]
    rw [hi] at h
    simp only [whole_profile.2.2.2,whole_profile.1,continuation,ite_true] at h
    exact h.trans ho
  · have h := hs [0,1]
    rw [hi] at h
    simp only [whole_profile.2.2.2,whole_profile.1,continuation,show ([1,0] : List Nat)≠[0,1] by decide,if_false] at h
    exact h.trans rfl

/-- Empty-success loops in recursive arguments remain undefined at every
physical clock; filtering cannot turn them into a finite failure. -/
def loopArgument : Arg := .user 0 (.star (.lit []))
theorem nullable_argument (x : List Char) (k : Nat) (E : List (List Char)) (p : Nat) (hp : p≤x.length)
    (q r : Nat) (hq : q<D.width) (hr : r<D.width) :
    evV (grammar D bodies) x .callByValueSeq (tblV (grammar D bodies) x .callByValueSeq k) E
      (filter D bodies (E.map (profile D)) loopArgument q r) p=none := by
  rw [source_filter_correct D hD bodies checked.1 x k loopArgument (by decide +kernel) E p hp q r hq hr]
  have he : evV (source bodies) x .callByValueSeq (tblV (source bodies) x .callByValueSeq k) E (.star (.lit [])) p=none := by
    apply evStar_stuck (show evV (source bodies) x .callByValueSeq (tblV (source bodies) x .callByValueSeq k) E (.lit []) p=some (some p) from by
      simp [evV,Shallot.stripPrefix?,length_sfx x hp]) (Nat.not_lt.mpr (Nat.le_refl _))
  have hb := source_rule bodies 0 bodies[0] (by rfl)
  change RegularCaptureProduct.filtered D x q r p
    (evV (source bodies) x .callByValueSeq (tblV (source bodies) x .callByValueSeq k) E
      (.call 0 [.star (.lit [])]) p)=none
  rw [evV_call_seq hb rfl]
  simp only [evSeqArgs,he,RegularCaptureProduct.filtered]

def committed : Arg := .user 2 (.seq (.alt (.lit ['b','b']) (.lit ['b'])) (.lit ['b']))
def explicitShort : Arg := .user 2 (.seq (.lit ['b']) (.lit ['b']))

/-- Observing the original successful argument branch cannot select a
shorter branch after its continuation fails. Explicitly choosing that
shorter branch is a different successful source expression. -/
theorem choice_commit :
    evV (source bodies) "bb!bb".toList .callByValueSeq (tblV (source bodies) "bb!bb".toList .callByValueSeq 2)
      [] (render committed) 5=some none ∧
    evV (source bodies) "bb!bb".toList .callByValueSeq (tblV (source bodies) "bb!bb".toList .callByValueSeq 2)
      [] (render explicitShort) 5=some (some 0) ∧
    evV (grammar D bodies) "bb!bb".toList .callByValueSeq (tblV (grammar D bodies) "bb!bb".toList .callByValueSeq 2)
      [] (filter D bodies [] committed 0 0) 5=some none := by
  have h : evV (source bodies) "bb!bb".toList .callByValueSeq
      (tblV (source bodies) "bb!bb".toList .callByValueSeq 2) [] (render committed) 5=some none := by decide +kernel
  refine ⟨h,by decide +kernel,?_⟩
  have hf := source_filter_correct D hD bodies checked.1 "bb!bb".toList 2 committed
    (by decide +kernel) [] 5 (by decide) 0 0 (by decide) (by decide)
  rw [h] at hf
  exact hf

def repeatedCalls : Arg := .star (.user 2 (.alt (.lit ['b','b']) (.lit ['b'])))

/-- Successive actual calls inside one star capture b and bb respectively.
The original greedy stopping point is retained and observed, with the
observer advancing through each different argument before its callee. -/
theorem variable_arguments_star :
    evV (source bodies) "b!bbb!bb#".toList .callByValueSeq
      (tblV (source bodies) "b!bbb!bb#".toList .callByValueSeq 2) [] (render repeatedCalls) 9=some (some 1) ∧
    evV (grammar D bodies) "b!bbb!bb#".toList .callByValueSeq
      (tblV (grammar D bodies) "b!bbb!bb#".toList .callByValueSeq 2) [] (filter D bodies [] repeatedCalls 0 0) 9=some (some 1) ∧
    evV (grammar D bodies) "b!bbb!bb#".toList .callByValueSeq
      (tblV (grammar D bodies) "b!bbb!bb#".toList .callByValueSeq 2) [] (filter D bodies [] repeatedCalls 0 1) 9=some none := by
  have h : evV (source bodies) "b!bbb!bb#".toList .callByValueSeq
      (tblV (source bodies) "b!bbb!bb#".toList .callByValueSeq 2) [] (render repeatedCalls) 9=some (some 1) := by decide +kernel
  refine ⟨h,?_,?_⟩
  · have hf := source_filter_correct D hD bodies checked.1 "b!bbb!bb#".toList 2 repeatedCalls
      (by decide +kernel) [] 9 (by decide) 0 0 (by decide) (by decide)
    rw [h] at hf
    exact hf.trans (by decide +kernel)
  · have hf := source_filter_correct D hD bodies checked.1 "b!bbb!bb#".toList 2 repeatedCalls
      (by decide +kernel) [] 9 (by decide) 0 1 (by decide) (by decide)
    rw [h] at hf
    exact hf.trans (by decide +kernel)

end Shallot.MacroPeg.CBV.SequentialRecursiveObserverExamples
