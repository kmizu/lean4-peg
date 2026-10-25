import MacroPeg.CBV.RetainedContinuationCompiler

namespace Shallot.MacroPeg.CBV.RetainedContinuationExamples
open RetainedContinuationSyntax
open ReplayControlFusion (Plan)
open TypedFieldSyntax (Header)
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def alphabet : List Char := ['a','#','@','!','?','(',')',';','b']
def doubled : MExp := .seq (.param 0) (.param 0)
def branch : MExp := .alt (.lit ['!'])
  (.seq (.lit ['(']) (.seq (.call 0 [doubled]) (.lit [')'])))
def after : MExp := .seq (.lit [';']) (.seq (.call 1 [.param 0]) (.param 0))
def parts : List Header := [
  ⟨[['a']],alphabet,'#',[0],branch⟩,
  ⟨[['a']],alphabet,'@',[0],.lit ['?']⟩,
  ⟨[['a']],alphabet,'?',[0],.eps⟩,
  ⟨[alphabet],alphabet++['$'],'$',[0],.eps⟩]
def mainPlan : Plan := .alt (.leaf 0) (.leaf 1)
def specs : List Spec := [
  ⟨mainPlan,⟨[['a']],alphabet,'%',after⟩⟩,
  ⟨.leaf 2,⟨[['a']],alphabet,'%',.eps⟩⟩,
  ⟨.leaf 3,⟨[alphabet],alphabet++['$'],'%',.param 0⟩⟩,
  ⟨.notP (.leaf 0),⟨[['a']],alphabet,'%',.lit ['b']⟩⟩,
  ⟨.guard (.notP (.leaf 1)) (.leaf 0),⟨[['a']],alphabet,'%',.lit ['b']⟩⟩]
def actual : MExp := .star (.lit ['a'])
def producer : MExp := .call 0 [actual]
def root : MExp := .seq (.call 2 [producer]) (.notP .any)
def original := source parts specs
def generated := RetainedContinuationCompiler.target parts specs
def generatedRoot := RetainedContinuationCompiler.targetStart parts specs root
def word (n : Nat) : List Char := List.replicate n 'a'
def ending (n : Nat) := [';']++word n++'?'::word n
def tree (n : Nat) : Nat → List Char
  | 0 => word n++['@','?']++ending n
  | depth+1 => word n++['#','(']++tree (2*n) depth++')'::ending n
def sample (n depth : Nat) := tree n depth++'$'::tree n depth

theorem checked : RetainedContinuationCompiler.check original root parts specs root=true := by decide +kernel
theorem generated_layout :
    original.rules.map MRule.arity=[1,1,1,1,1] ∧ (normalizedParts parts specs).length=10 ∧
    generated.rules.map MRule.arity=[1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,0,1,2] := by decide +kernel

theorem every_input_every_clock (x : List Char) (k : Nat) :
    evV original x .callByValuePar (tblV original x .callByValuePar k) [] root x.length=
      evV generated x .callByValueSeq (tblV generated x .callByValueSeq k) [] generatedRoot x.length :=
  RetainedContinuationCompiler.physical _ _ _ _ _ checked x k

theorem original_string_language :
    (fun x => SObs original .callByValuePar root x (some []))=
      (fun x => SObs generated .callByValueSeq generatedRoot x (some [])) :=
  RetainedContinuationCompiler.language_translation _ _ _ _ _ checked

theorem direct_consuming_continuation_runs :
    ([0,1].flatMap (fun n => [0,1,2].map (fun depth => (n,depth)))).all (fun (n,depth) =>
      evV generated (sample n depth) .callByValueSeq (tblV generated (sample n depth) .callByValueSeq (depth+3)) []
        generatedRoot (sample n depth).length==some (some 0))=true := by decide +kernel

theorem suffix_does_not_replace_the_parent_with_the_child :
    evV generated ['a','#','(','a','a','@','?',';','a','a','?','a','a',')',';','a','a','?','a','a']
      .callByValueSeq
      (tblV generated ['a','#','(','a','a','@','?',';','a','a','?','a','a',')',';','a','a','?','a','a'] .callByValueSeq 5) []
      (RetainedContinuationCompiler.targetStart parts specs (.seq producer (.notP .any))) 20=some none := by decide +kernel

theorem rerunning_the_actual_at_the_continuation_loses_the_value :
    evParArgs original (ending 1) .callByValuePar (tblV original (ending 1) .callByValuePar 1) [] [actual]
      (ending 1).length=some (some [[]]) ∧
    evV original (ending 1) .callByValuePar (tblV original (ending 1) .callByValuePar 1) [['a']] after
      (ending 1).length=some (some 0) ∧
    evV original (ending 1) .callByValuePar (tblV original (ending 1) .callByValuePar 1) [[]] after
      (ending 1).length=some none := by decide +kernel

def negativeRoot : MExp := .seq (.call 3 [actual]) (.notP .any)
def guardRoot : MExp := .seq (.call 4 [actual]) (.notP .any)
theorem predicate_continuations :
    RetainedContinuationCompiler.check original negativeRoot parts specs negativeRoot=true ∧
    RetainedContinuationCompiler.check original guardRoot parts specs guardRoot=true ∧
    evV generated ['b'] .callByValueSeq (tblV generated ['b'] .callByValueSeq 2) []
      (RetainedContinuationCompiler.targetStart parts specs negativeRoot) 1=some (some 0) ∧
    evV generated ['a','#','!','b'] .callByValueSeq (tblV generated ['a','#','!','b'] .callByValueSeq 2) []
      (RetainedContinuationCompiler.targetStart parts specs guardRoot) 4=some (some 0) := by decide +kernel

def priorityParts : List Header := [
  ⟨[['a']],['a','#','!',';'],'#',[0],.eps⟩,
  ⟨[['a']],['a','#','!',';'],'#',[0],.lit ['!']⟩]
def prioritySpecs : List Spec := [⟨.alt (.leaf 0) (.leaf 1),
  ⟨[['a']],['a','#','!',';'],'%',.seq (.lit [';']) (.param 0)⟩⟩]
def priorityRoot : MExp := .seq (.call 0 [actual]) (.notP .any)
def priorityTarget := RetainedContinuationCompiler.target priorityParts prioritySpecs
def naiveRoot : MExp := .seq (.alt (TupleFieldTransfer.head 4 1 '#' [0] [actual])
  (TupleFieldTransfer.head 6 1 '#' [0] [actual])) (.notP .any)
theorem simple_distribution_is_wrong :
    RetainedContinuationCompiler.check (source priorityParts prioritySpecs) priorityRoot priorityParts prioritySpecs priorityRoot=true ∧
    evV (source priorityParts prioritySpecs) ['a','#','!',';','a'] .callByValuePar
      (tblV (source priorityParts prioritySpecs) ['a','#','!',';','a'] .callByValuePar 2) [] priorityRoot 5=some none ∧
    evV priorityTarget ['a','#','!',';','a'] .callByValueSeq (tblV priorityTarget ['a','#','!',';','a'] .callByValueSeq 2) []
      (RetainedContinuationCompiler.targetStart priorityParts prioritySpecs priorityRoot) 5=some none ∧
    evV priorityTarget ['a','#','!',';','a'] .callByValueSeq (tblV priorityTarget ['a','#','!',';','a'] .callByValueSeq 2) []
      naiveRoot 5=some (some 0) := by decide +kernel

def missingParts : List Header := [⟨[['a'],['a']],['a','#'],'#',[0],.eps⟩]
def missingSpecs : List Spec := [⟨.leaf 0,⟨[['a'],['a']],['a','#'],'%',.param 1⟩⟩]
theorem future_live_fields_must_be_retained :
    RetainedContinuationCompiler.check (source missingParts missingSpecs) (.call 0 [.eps,.eps])
      missingParts missingSpecs (.call 0 [.eps,.eps])=false := by decide +kernel

def unboundParts : List Header := [⟨[['a']],['b'],'%',[],.lit ['b']⟩]
def unboundSpecs : List Spec := [⟨.leaf 0,⟨[['a']],['a','b'],'%',.param 0⟩⟩]
theorem independent_prefix_does_not_supply_a_live_binding :
    RetainedContinuationCompiler.check (source unboundParts unboundSpecs) (.call 0 [actual]) unboundParts unboundSpecs
      (.call 0 [actual])=false := by decide +kernel

def undefinedSpecs : List Spec := [⟨.leaf 0,⟨[['a']],alphabet,'%',.star .eps⟩⟩]
def undefinedParts : List Header := [⟨[['a']],alphabet,'#',[0],.eps⟩]
def undefinedRoot : MExp := .call 0 [.eps]
theorem undefined_suffix_checked :
    RetainedContinuationCompiler.check (source undefinedParts undefinedSpecs) undefinedRoot undefinedParts undefinedSpecs undefinedRoot=true := by decide +kernel
theorem nullable_suffix_never_becomes_a_fallback_success (x : List Char) (k : Nat) :
    evV (source undefinedParts undefinedSpecs) x .callByValuePar
      (tblV (source undefinedParts undefinedSpecs) x .callByValuePar k) [] undefinedRoot x.length≠some (some 0) := by
  cases k with
  | zero => simp [undefinedRoot,evV,source,undefinedSpecs,ruleAtM,evParArgs,tblV,valAt_nil]
  | succ k =>
    rw [undefinedRoot,evV_call_par (show ruleAtM (source undefinedParts undefinedSpecs).rules 0=some
      ⟨1,.seq ((Plan.leaf 0).exp (FieldPlanSyntax.sourceLeaf undefinedParts)) (.star .eps)⟩ from rfl) rfl (by decide),
      evPar_cons_ok (show evV (source undefinedParts undefinedSpecs) x .callByValuePar _ [] .eps x.length=some (some x.length) from rfl),evPar_nil]
    change valAt (tblV (source undefinedParts undefinedSpecs) x .callByValuePar (k+1) 0 [pre x x.length x.length]) x.length≠_
    rw [valAt_tblV_succ (show ruleAtM (source undefinedParts undefinedSpecs).rules 0=some
      ⟨1,.seq ((Plan.leaf 0).exp (FieldPlanSyntax.sourceLeaf undefinedParts)) (.star .eps)⟩ from rfl) _ (Nat.le_refl _)]
    cases h : evV (source undefinedParts undefinedSpecs) x .callByValuePar (tblV (source undefinedParts undefinedSpecs) x .callByValuePar k)
      [pre x x.length x.length] ((Plan.leaf 0).exp (FieldPlanSyntax.sourceLeaf undefinedParts)) x.length with
    | none => rw [evV_seq_none h]; simp
    | some r => cases r with
      | none => rw [evV_seq_fail h]; simp
      | some q => rw [evV_seq_ok h,evV_star,evStar_stuck rfl (Nat.lt_irrefl q)]; simp

theorem nullable_suffix_after_a_successful_prefix (k : Nat) :
    evV (source undefinedParts undefinedSpecs) ['#'] .callByValuePar
      (tblV (source undefinedParts undefinedSpecs) ['#'] .callByValuePar k) [] undefinedRoot 1=none ∧
    evV (RetainedContinuationCompiler.target undefinedParts undefinedSpecs) ['#'] .callByValueSeq
      (tblV (RetainedContinuationCompiler.target undefinedParts undefinedSpecs) ['#'] .callByValueSeq k) []
      (RetainedContinuationCompiler.targetStart undefinedParts undefinedSpecs undefinedRoot) 1=none := by
  have hs : evV (source undefinedParts undefinedSpecs) ['#'] .callByValuePar
      (tblV (source undefinedParts undefinedSpecs) ['#'] .callByValuePar k) [] undefinedRoot 1=none := by
    cases k with
    | zero => rfl
    | succ k =>
      have hr : ruleAtM (source undefinedParts undefinedSpecs).rules 0=some
        ⟨1,.seq ((Plan.leaf 0).exp (FieldPlanSyntax.sourceLeaf undefinedParts)) (.star .eps)⟩ := rfl
      rw [undefinedRoot,evV_call_par hr rfl (by decide),evPar_cons_ok (show
        evV (source undefinedParts undefinedSpecs) ['#'] .callByValuePar _ [] .eps 1=some (some 1) from rfl),evPar_nil]
      change valAt (tblV (source undefinedParts undefinedSpecs) ['#'] .callByValuePar (k+1) 0 [[]]) 1=none
      rw [valAt_tblV_succ hr _ (by decide),evV_seq_ok (show
        evV (source undefinedParts undefinedSpecs) ['#'] .callByValuePar _ [[]]
          ((Plan.leaf 0).exp (FieldPlanSyntax.sourceLeaf undefinedParts)) 1=some (some 0) from rfl),
        evV_star,evStar_stuck rfl (Nat.lt_irrefl 0)]
  exact ⟨hs,(RetainedContinuationCompiler.physical _ _ _ _ _ undefined_suffix_checked ['#'] k).symm.trans hs⟩

end Shallot.MacroPeg.CBV.RetainedContinuationExamples
