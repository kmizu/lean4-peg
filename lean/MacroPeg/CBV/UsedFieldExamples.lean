import MacroPeg.CBV.MutualFieldCompiler

namespace Shallot.MacroPeg.CBV.UsedFieldExamples
open MutualFieldSyntax
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def word (n : Nat) : List Char := List.replicate n 'a'
def wordsA (n : Nat) (unused : List Char) : List (List Char) := [unused,word n,[]]
def wordsB (n : Nat) : List (List Char) := [word n,[]]
def doubled : MExp := .seq (.param 1) (.param 1)
def argsB : List MExp := [doubled,.eps]
def argsA : List MExp := [.eps,.param 0,.eps]
def bodyA : MExp := .alt
  (.seq (.lit ['(']) (.seq (.call 1 argsB) (.seq (.lit [')']) (.param 1))))
  (.seq (.lit ['!']) (.param 1))
def bodyB : MExp := .seq (.call 0 argsA) (.param 0)
def headers : List Header := [⟨3,[1],bodyA⟩,⟨2,[0],bodyB⟩]
def actuals : List MExp := [.alt (.lit ['a']) .eps,.star (.lit ['a']),.eps]
def root : MExp := .seq (.call 0 actuals) (.notP .any)
def original := source [] headers '#'
def generated := target [] headers '#'
def generatedRoot := emit 0 headers '#' root
def block (n : Nat) : List Char := word n++['#']
def treeA (n : Nat) : Nat → List Char
  | 0 => block n++'!'::word n
  | depth+1 => block n++'('::(block (2*n)++(treeA (2*n) depth++
      (word (2*n)++')'::word n)))
def treeB (n depth : Nat) : List Char := block n++(treeA n depth++word n)

theorem checked : MutualFieldCompiler.check original root [] headers '#' root=true := by decide +kernel

theorem all_original_parameters_need_not_be_replayed :
    original.rules.map MRule.arity=[3,2] ∧ generated.rules.map MRule.arity=[1,1,1,2,1,1,2] ∧
    ¬(∀ i, i<3 → i∈([1] : List Nat)) ∧ ¬(∀ i, i<2 → i∈([0] : List Nat)) := by decide +kernel

theorem every_input_every_clock (x : List Char) (k : Nat) :
    evV original x .callByValuePar (tblV original x .callByValuePar k) [] root x.length=
      evV generated x .callByValueSeq (tblV generated x .callByValueSeq k) [] generatedRoot x.length :=
  MutualFieldCompiler.physical original root [] headers '#' root checked x k

theorem recursive_inputs :
    ([0,1,2].flatMap (fun n => [0,1,2].map (fun depth => (n,depth)))).all (fun (n,depth) =>
      evV original (treeA n depth) .callByValuePar (tblV original (treeA n depth) .callByValuePar (2*depth+1)) []
        root (treeA n depth).length==some (some 0))=true := by decide +kernel

theorem generated_recursive_inputs :
    ([0,1,2].flatMap (fun n => [0,1,2].map (fun depth => (n,depth)))).all (fun (n,depth) =>
      evV generated (treeA n depth) .callByValueSeq (tblV generated (treeA n depth) .callByValueSeq (2*depth+1)) []
        generatedRoot (treeA n depth).length==some (some 0))=true := by decide +kernel

def failedActual : MExp := .call 0 [.lit ['X'],.star (.lit ['a']),.eps]
theorem unused_argument_failure_is_preserved :
    MutualFieldCompiler.check original failedActual [] headers '#' failedActual=true ∧
    evV original ['a','#','!','a'] .callByValuePar (tblV original ['a','#','!','a'] .callByValuePar 1) [] failedActual 4=some none ∧
    evV generated ['a','#','!','a'] .callByValueSeq (tblV generated ['a','#','!','a'] .callByValueSeq 1) []
      (emit 0 headers '#' failedActual) 4=some none := by decide +kernel

def undefinedActual : MExp := .call 0 [.star .eps,.star (.lit ['a']),.eps]
theorem undefined_actual_checked :
    MutualFieldCompiler.check original undefinedActual [] headers '#' undefinedActual=true := by decide +kernel

theorem unused_argument_undefinedness_all_clocks (x : List Char) (k : Nat) :
    evV original x .callByValuePar (tblV original x .callByValuePar k) [] undefinedActual x.length=none ∧
    evV generated x .callByValueSeq (tblV generated x .callByValueSeq k) []
      (emit 0 headers '#' undefinedActual) x.length=none := by
  have hr : ruleAtM original.rules 0=some ⟨3,TupleFieldTransfer.sourceBody '#' [1] bodyA⟩ := rfl
  have hs : evV original x .callByValuePar (tblV original x .callByValuePar k) [] undefinedActual x.length=none := by
    have hstar : evV original x .callByValuePar (tblV original x .callByValuePar k) [] (.star .eps) x.length=none :=
      evStar_stuck rfl (Nat.lt_irrefl _)
    rw [undefinedActual,evV_call_par hr rfl (by decide),evPar_cons_none hstar]
  exact ⟨hs,(MutualFieldCompiler.physical original undefinedActual [] headers '#' undefinedActual
    undefined_actual_checked x k).symm.trans hs⟩

theorem hidden_uses_in_predicates_repetition_and_actuals_are_rejected :
    headerCheck 0 headers '#' ⟨3,[1],.notP (.param 0)⟩=false ∧
    headerCheck 0 headers '#' ⟨3,[1],.star (.param 0)⟩=false ∧
    headerCheck 0 headers '#' ⟨3,[1],.call 1 [.param 0,.eps]⟩=false ∧
    headerCheck 0 headers '#' ⟨3,[1],.andP (.param 2)⟩=false := by decide +kernel

theorem missing_empty_value_is_not_an_empty_parser :
    evV generated [] .callByValueSeq (tblV generated [] .callByValueSeq 0) [[],[]]
      (MExp.subst (CopyFieldCapture.views 3 [1]) (.param 0)) 0=some none ∧
    evV original [] .callByValuePar (tblV original [] .callByValuePar 0) [[],[],[]] (.param 0) 0=some (some 0) := by decide +kernel

def unboundHeaders : List Header := [⟨1,[],.lit ['a']⟩]
def unboundSource := source [] unboundHeaders '#'
def unboundTarget := target [] unboundHeaders '#'
def unboundRoot : MExp := .call 0 [.lit ['a']]
theorem no_parameter_reads_require_no_replay :
    MutualFieldCompiler.check unboundSource unboundRoot [] unboundHeaders '#' unboundRoot=true ∧
    evV unboundSource ['a'] .callByValuePar (tblV unboundSource ['a'] .callByValuePar 1) [] unboundRoot 1=some (some 0) ∧
    evV unboundTarget ['a'] .callByValueSeq (tblV unboundTarget ['a'] .callByValueSeq 1) []
      (emit 0 unboundHeaders '#' unboundRoot) 1=some (some 0) ∧
    unboundTarget.rules.map MRule.arity=[1,0] := by decide +kernel

def emptyCycleHeaders : List Header := [⟨1,[],.alt (.call 0 [.eps]) .eps⟩]
def emptyCycleSource := source [] emptyCycleHeaders '#'
def emptyCycleTarget := target [] emptyCycleHeaders '#'
def emptyCycleRoot : MExp := .call 0 [.eps]
theorem empty_cycle_checked :
    MutualFieldCompiler.check emptyCycleSource emptyCycleRoot [] emptyCycleHeaders '#' emptyCycleRoot=true := by decide +kernel

theorem empty_anchor_does_not_force_termination (x : List Char) (k : Nat) :
    evV emptyCycleSource x .callByValuePar (tblV emptyCycleSource x .callByValuePar k) [] emptyCycleRoot x.length=none ∧
    evV emptyCycleTarget x .callByValueSeq (tblV emptyCycleTarget x .callByValueSeq k) []
      (emit 0 emptyCycleHeaders '#' emptyCycleRoot) x.length=none := by
  have hr : ruleAtM emptyCycleSource.rules 0=some ⟨1,TupleFieldTransfer.sourceBody '#' [] (.alt (.call 0 [.eps]) .eps)⟩ := rfl
  have row : valAt (tblV emptyCycleSource x .callByValuePar k 0 [[]]) x.length=none := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [valAt_tblV_succ hr _ (Nat.le_refl _),TupleFieldTransfer.sourceBody,
        evV_seq_ok (show evV emptyCycleSource x .callByValuePar (tblV emptyCycleSource x .callByValuePar k) [[]]
          (DelimiterTemplate.compile '#' (DelimitedWordPattern.sourceParts '#' [])) x.length=some (some x.length) from rfl)]
      apply evV_alt_none
      rw [evV_call_par hr rfl (by decide),evPar_cons_ok (show evV emptyCycleSource x .callByValuePar
        (tblV emptyCycleSource x .callByValuePar k) [[]] .eps x.length=some (some x.length) from rfl),evPar_nil]
      simpa only [pre,Nat.sub_self,List.take_zero] using ih
  have hs : evV emptyCycleSource x .callByValuePar (tblV emptyCycleSource x .callByValuePar k) [] emptyCycleRoot x.length=none := by
    rw [emptyCycleRoot,evV_call_par hr rfl (by decide),evPar_cons_ok (show evV emptyCycleSource x .callByValuePar
      (tblV emptyCycleSource x .callByValuePar k) [] .eps x.length=some (some x.length) from rfl),evPar_nil]
    simpa only [pre,Nat.sub_self,List.take_zero] using row
  exact ⟨hs,(MutualFieldCompiler.physical emptyCycleSource emptyCycleRoot [] emptyCycleHeaders '#' emptyCycleRoot
    empty_cycle_checked x k).symm.trans hs⟩

end Shallot.MacroPeg.CBV.UsedFieldExamples
