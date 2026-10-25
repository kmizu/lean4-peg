import MacroPeg.CBV.FiniteSuffixObservedCompiler

namespace Shallot.MacroPeg.CBV.FiniteSuffixObservedExamples
open FiniteSuffixObservedSyntax
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def region := [['a','b']]
def peek (e : Term) : Term := .notP (.notP e)
def skipToPair : Term := .star (.seq (peek (.seq .any (.seq .any .any))) .any)
def isA (i : Nat) : Term := peek (.seq skipToPair (.seq (.replay i) (.seq (.chr 'b') (.notP .any))))
def isAB (i : Nat) : Term := peek (.seq skipToPair (.seq (.replay i) (.notP .any)))
def parentTail : Term := .seq (isA 0) (isAB 1)
/-- The first actual calls a parameterized wrapper; its own actual inspects
its parent's a. The second actual independently queries the parent's ab. -/
def childActuals : List Term := [.call 3 [.seq (isA 0) (.lit ['a'])],.seq (isAB 1) (.lit ['a'])]
def parentActuals : List Term := [.seq (isAB 0) (.lit ['a']),.call 3 [.seq (isA 1) (.lit ['a'])]]
def parentPrefix : Term := .seq parentTail (.seq (.lit ['a','b','{']) (.seq (.alt (.call 1 childActuals) .eps) (.chr '}')))
def parent : Term := .seq parentPrefix parentTail
def child : Term := .seq (isAB 0) (.seq (isA 1) (.seq (.lit ['a','b','['])
  (.seq (.alt (.call 0 parentActuals) .eps) (.seq (.chr ']') (.seq (isAB 0) (isA 1))))))
def outer : Term := .seq (isAB 0) (.seq (.call 0 [.lit ['a'],.call 4 []]) (.seq (isAB 0) (.replay 0)))
def wrapper : Term := .seq (isA 0) (.call 4 [])
def balanced : Term := .alt (.seq (.chr 'a') (.seq (.call 4 []) (.chr 'b'))) .eps
def specs : List Spec := [⟨2,parent⟩,⟨2,child⟩,⟨1,outer⟩,⟨1,wrapper⟩,⟨0,balanced⟩]
def entry : Term := .call 2 [.call 4 []]
abbrev originalGrammar := source region specs
abbrev generated := target region specs
def root := original region entry
def targetRoot := emit region specs [] none entry

def frame : Bool → Nat → List Char
  | first,0 => ['a','b',if first then '{' else '[',if first then '}' else ']']
  | first,n+1 => ['a','b',if first then '{' else '[']++frame (!first) n++[if first then '}' else ']']
def input (n : Nat) := frame true n++['a','b']

theorem checked : FiniteSuffixObservedCompiler.check originalGrammar root region specs entry=true := by decide +kernel

theorem source_arities : originalGrammar.rules.map MRule.arity=[2,2,1,1,0] := by decide +kernel

theorem fixed_target_size : generated.rules.length=1230 ∧ generated.rules.all (fun r => r.arity==0)=true := by decide +kernel

theorem source_runs : ∀ n∈[0,1,2],
    evV originalGrammar (input n) .callByValuePar (tblV originalGrammar (input n) .callByValuePar 8) [] root (input n).length=some (some 0) := by decide +kernel

theorem target_runs : ∀ n∈[0,1,2],
    evV generated (input n) .callByValueSeq (tblV generated (input n) .callByValueSeq 8) [] targetRoot (input n).length=some (some 0) := by decide +kernel

theorem actual_parent_dependent_child_tuple :
    evParArgs originalGrammar (input 1) .callByValuePar (tblV originalGrammar (input 1) .callByValuePar 8) [['a'],['a','b']]
      (FiniteSuffixDependentView.renderArgs region none childActuals) ((input 1).length-3)=some (some [['a','b'],['a']]) := by decide +kernel

def leakedChildView : MExp := .seq (emit region specs [some ['a'],some ['a','b']] none parentPrefix)
  (emit region specs [some ['a','b'],some ['a']] none parentTail)

theorem leaked_child_view_rejected :
    evV generated (input 1) .callByValueSeq (tblV generated (input 1) .callByValueSeq 8) [] leakedChildView (input 1).length=some none := by decide +kernel

theorem same_physical_clock (x : List Char) (k : Nat) :
    evV originalGrammar x .callByValuePar (tblV originalGrammar x .callByValuePar k) [] root x.length=
      evV generated x .callByValueSeq (tblV generated x .callByValueSeq k) [] targetRoot x.length :=
  FiniteSuffixObservedCompiler.physical originalGrammar root region specs entry checked x k

theorem original_language : (fun x => SObs originalGrammar .callByValuePar root x (some []))=
    (fun x => SObs generated .callByValueSeq targetRoot x (some [])) :=
  FiniteSuffixObservedCompiler.language_translation originalGrammar root region specs entry checked

theorem unchanged_source_seq_fails :
    evV originalGrammar (input 0) .callByValueSeq (tblV originalGrammar (input 0) .callByValueSeq 8) [] root (input 0).length=some none := by decide +kernel

def captureInput (n : Nat) := List.replicate n 'a'++List.replicate n 'b'++['{','}','a','b']
theorem unbounded_capture_samples : ∀ n∈[1,2,4],
    evParArgs originalGrammar (captureInput n) .callByValuePar (tblV originalGrammar (captureInput n) .callByValuePar 12) [['a'],['a','b']]
      (FiniteSuffixDependentView.renderArgs region none childActuals) (captureInput n).length=
        some (some [List.replicate n 'a'++List.replicate n 'b',['a']]) := by decide +kernel

/-- any/star actuals may contain characters outside all candidate alphabets.
A candidate-outside parent is retained as Other, not rejected at entry. -/
def anySpecs : List Spec := [⟨1,.notP (.replay 0)⟩]
def anyEntry : Term := .seq (.call 0 [.star .any]) (.lit ['X'])

theorem outside_alphabet_other_capture :
    evV (source region anySpecs) ['X'] .callByValuePar (tblV (source region anySpecs) ['X'] .callByValuePar 4) [] (original region anyEntry) 1=some (some 0) ∧
    evV (target region anySpecs) ['X'] .callByValueSeq (tblV (target region anySpecs) ['X'] .callByValueSeq 4) [] (emit region anySpecs [] none anyEntry) 1=some (some 0) := by decide +kernel

def rangeEntry : Term := .seq (.call 0 [.star (.range 'A' 'Z')]) (.lit ['X'])
theorem range_other_capture :
    evV (source region anySpecs) ['X'] .callByValuePar (tblV (source region anySpecs) ['X'] .callByValuePar 4) [] (original region rangeEntry) 1=some (some 0) ∧
    evV (target region anySpecs) ['X'] .callByValueSeq (tblV (target region anySpecs) ['X'] .callByValueSeq 4) [] (emit region anySpecs [] none rangeEntry) 1=some (some 0) := by decide +kernel

def nullableEntry : Term := .call 0 [.star .eps]
theorem nullable_source_all_inputs (x : List Char) (k : Nat) :
    evV (source region anySpecs) x .callByValuePar (tblV (source region anySpecs) x .callByValuePar k) [] (original region nullableEntry) x.length=none := by
  have hr := FiniteSuffixDependentView.source_rule region anySpecs 0 ⟨1,.notP (.replay 0)⟩ rfl
  rw [show original region nullableEntry=.call 0 [.star .eps] from rfl,evV_call_par hr rfl (by decide)]
  have hh : evV (source region anySpecs) x .callByValuePar (tblV (source region anySpecs) x .callByValuePar k) [] (.star .eps) x.length=none :=
    evStar_stuck rfl (by omega)
  rw [evPar_cons_none hh]

theorem nullable_target_all_inputs (x : List Char) (k : Nat) :
    evV (target region anySpecs) x .callByValueSeq (tblV (target region anySpecs) x .callByValueSeq k) [] (emit region anySpecs [] none nullableEntry) x.length=none :=
  ((FiniteSuffixObservedCorrespondence.physical region anySpecs x nullableEntry [] x.length k (Nat.le_refl _)).1).trans (nullable_source_all_inputs x k)

def orderedSpecs : List Spec := [⟨2,.eps⟩]
def orderedUndefined : Term := .call 0 [.star .eps,.notP .eps]
def orderedFailure : Term := .call 0 [.notP .eps,.star .eps]

theorem ordered_undefined_all_inputs (x : List Char) (k : Nat) :
    evV (source region orderedSpecs) x .callByValuePar (tblV (source region orderedSpecs) x .callByValuePar k) [] (original region orderedUndefined) x.length=none := by
  have hr := FiniteSuffixDependentView.source_rule region orderedSpecs 0 ⟨2,.eps⟩ rfl
  rw [show original region orderedUndefined=.call 0 [.star .eps,.notP .eps] from rfl,evV_call_par hr rfl (by decide)]
  have hh : evV (source region orderedSpecs) x .callByValuePar (tblV (source region orderedSpecs) x .callByValuePar k) [] (.star .eps) x.length=none := evStar_stuck rfl (by omega)
  rw [evPar_cons_none hh]

theorem ordered_undefined_target (x : List Char) (k : Nat) :
    evV (target region orderedSpecs) x .callByValueSeq (tblV (target region orderedSpecs) x .callByValueSeq k) [] (emit region orderedSpecs [] none orderedUndefined) x.length=none :=
  ((FiniteSuffixObservedCorrespondence.physical region orderedSpecs x orderedUndefined [] x.length k (Nat.le_refl _)).1).trans (ordered_undefined_all_inputs x k)

theorem failure_before_undefined :
    evV (source region orderedSpecs) ['a'] .callByValuePar (tblV (source region orderedSpecs) ['a'] .callByValuePar 0) [] (original region orderedFailure) 1=some none ∧
    evV (target region orderedSpecs) ['a'] .callByValueSeq (tblV (target region orderedSpecs) ['a'] .callByValueSeq 0) [] (emit region orderedSpecs [] none orderedFailure) 1=some none := by decide +kernel

theorem malformed_calls_skip_undefined : ∀ e∈[(.call 0 [.star .eps] : Term),.call 100 [.star .eps]],
    evV (source region orderedSpecs) ['a'] .callByValuePar (tblV (source region orderedSpecs) ['a'] .callByValuePar 0) [] (original region e) 1=some none ∧
    evV (target region orderedSpecs) ['a'] .callByValueSeq (tblV (target region orderedSpecs) ['a'] .callByValueSeq 0) [] (emit region orderedSpecs [] none e) 1=some none := by decide +kernel

/-- A parent-dependent nullable actual repeats the actual retained empty
word at the nonempty ab suffix. Both user rows are ordinary source rows. -/
def dependentNullableSpecs : List Spec := [⟨1,.call 1 [.star (.replay 0)]⟩,⟨1,.eps⟩]
def dependentNullableEntry : Term := .call 0 [.eps]

theorem dependent_nullable_rows (k : Nat) :
    valAt (tblV (source region dependentNullableSpecs) ['a','b'] .callByValuePar k 0 [[]]) 2=none := by
  cases k with
  | zero => rfl
  | succ k =>
    have h0 := FiniteSuffixDependentView.source_rule region dependentNullableSpecs 0 ⟨1,.call 1 [.star (.replay 0)]⟩ rfl
    have h1 := FiniteSuffixDependentView.source_rule region dependentNullableSpecs 1 ⟨1,.eps⟩ rfl
    rw [valAt_tblV_succ h0 [[]] (by decide)]
    change evV (source region dependentNullableSpecs) ['a','b'] .callByValuePar
      (tblV (source region dependentNullableSpecs) ['a','b'] .callByValuePar k) [[]]
      (.call 1 [.star (.seq (FiniteSuffixReplay.guard region) (.param 0))]) 2=none
    rw [evV_call_par h1 rfl (by decide)]
    have hh : evV (source region dependentNullableSpecs) ['a','b'] .callByValuePar
        (tblV (source region dependentNullableSpecs) ['a','b'] .callByValuePar k) [[]]
        (.star (.seq (FiniteSuffixReplay.guard region) (.param 0))) 2=none := evStar_stuck (j := 2) rfl (by omega)
    rw [evPar_cons_none hh]

theorem dependent_nullable_source (k : Nat) :
    evV (source region dependentNullableSpecs) ['a','b'] .callByValuePar (tblV (source region dependentNullableSpecs) ['a','b'] .callByValuePar k) []
      (original region dependentNullableEntry) 2=none := by
  have h0 := FiniteSuffixDependentView.source_rule region dependentNullableSpecs 0 ⟨1,.call 1 [.star (.replay 0)]⟩ rfl
  rw [show original region dependentNullableEntry=.call 0 [.eps] from rfl,evV_call_par h0 rfl (by decide),evPar_cons_ok rfl,evPar_nil]
  exact dependent_nullable_rows k

theorem dependent_nullable_target (k : Nat) :
    evV (target region dependentNullableSpecs) ['a','b'] .callByValueSeq (tblV (target region dependentNullableSpecs) ['a','b'] .callByValueSeq k) []
      (emit region dependentNullableSpecs [] none dependentNullableEntry) 2=none :=
  ((FiniteSuffixObservedCorrespondence.physical region dependentNullableSpecs ['a','b'] dependentNullableEntry [] 2 k (by decide)).1).trans (dependent_nullable_source k)

def recursiveActualSpecs : List Spec := [⟨1,.call 0 [.call 0 [.eps]]⟩]
def recursiveActualEntry : Term := .call 0 [.eps]

theorem recursive_actual_rows (x : List Char) (p : Nat) (hp : p≤x.length) : ∀ k,
    valAt (tblV (source region recursiveActualSpecs) x .callByValuePar k 0 [[]]) p=none
  | 0 => rfl
  | k+1 => by
    have h0 := FiniteSuffixDependentView.source_rule region recursiveActualSpecs 0 ⟨1,.call 0 [.call 0 [.eps]]⟩ rfl
    rw [valAt_tblV_succ h0 [[]] hp]
    change evV (source region recursiveActualSpecs) x .callByValuePar (tblV (source region recursiveActualSpecs) x .callByValuePar k) [[]]
      (.call 0 [.call 0 [.eps]]) p=none
    rw [evV_call_par h0 rfl (by decide)]
    have hh : evV (source region recursiveActualSpecs) x .callByValuePar
        (tblV (source region recursiveActualSpecs) x .callByValuePar k) [[]] (.call 0 [.eps]) p=none := by
      rw [evV_call_par h0 rfl (by decide),evPar_cons_ok rfl,evPar_nil]
      simpa [pre] using recursive_actual_rows x p hp k
    rw [evPar_cons_none hh]

theorem recursive_actual_source (x : List Char) (k : Nat) :
    evV (source region recursiveActualSpecs) x .callByValuePar (tblV (source region recursiveActualSpecs) x .callByValuePar k) []
      (original region recursiveActualEntry) x.length=none := by
  have h0 := FiniteSuffixDependentView.source_rule region recursiveActualSpecs 0 ⟨1,.call 0 [.call 0 [.eps]]⟩ rfl
  rw [show original region recursiveActualEntry=.call 0 [.eps] from rfl,evV_call_par h0 rfl (by decide),evPar_cons_ok rfl,evPar_nil]
  simpa [pre] using recursive_actual_rows x x.length (Nat.le_refl _) k

theorem recursive_actual_target (x : List Char) (k : Nat) :
    evV (target region recursiveActualSpecs) x .callByValueSeq (tblV (target region recursiveActualSpecs) x .callByValueSeq k) []
      (emit region recursiveActualSpecs [] none recursiveActualEntry) x.length=none :=
  ((FiniteSuffixObservedCorrespondence.physical region recursiveActualSpecs x recursiveActualEntry [] x.length k (Nat.le_refl _)).1).trans (recursive_actual_source x k)

def unguarded : MGrammar := ⟨[⟨1,.param 0⟩]⟩
theorem missing_guard_rejected : FiniteSuffixObservedCompiler.check unguarded (original region (.call 0 [.lit ['a']])) region [⟨1,.replay 0⟩] (.call 0 [.lit ['a']])=false := by decide +kernel

end Shallot.MacroPeg.CBV.FiniteSuffixObservedExamples
