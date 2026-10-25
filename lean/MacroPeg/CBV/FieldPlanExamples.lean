import MacroPeg.CBV.FieldPlanCompiler

namespace Shallot.MacroPeg.CBV.FieldPlanExamples
open FieldPlanSyntax
open ReplayControlFusion (Plan)
open TypedFieldSyntax (Header)
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def alphabet : List Char := ['a','#','@','?','(',')','!','b']
def doubled : MExp := .seq (.param 0) (.param 0)
def firstTail : MExp := .alt (.seq (.lit ['!']) (.param 0))
  (.seq (.lit ['(']) (.seq (.call 0 [doubled,doubled]) (.seq (.lit [')']) (.param 0))))
def secondTail : MExp := .seq (.lit ['?']) (.param 1)
def fallback : MExp := .alt (.lit ['b']) (.lit ['@','?','b'])
def parts : List Header := [
  ⟨[['a'],['a']],alphabet,'#',[0],firstTail⟩,
  ⟨[['a'],['a']],alphabet,'@',[1],secondTail⟩,
  ⟨[['a'],['a']],alphabet,'%',[],fallback⟩,
  ⟨[alphabet],alphabet++['$'],'$',[0],.param 0⟩]
def mainPlan : Plan := .alt (.leaf 0) (.alt (.leaf 1) (.leaf 2))
def guardedPlan : Plan := .guard (.notP (.leaf 1)) (.alt (.leaf 0) (.leaf 2))
def specs : List Spec := [⟨2,mainPlan⟩,⟨1,.leaf 3⟩,⟨2,guardedPlan⟩,⟨2,.notP (.leaf 1)⟩]
def actual : MExp := .star (.lit ['a'])
def producer : MExp := .call 0 [actual,actual]
def root : MExp := .seq (.call 1 [producer]) (.notP .any)
def original := source parts specs
def generated := FieldPlanCompiler.target parts specs
def generatedRoot := FieldPlanCompiler.targetStart parts specs root
def shortActual : MExp := .alt (.lit ['a']) .eps
def shortRoot : MExp := .seq (.call 0 [shortActual,actual]) (.notP .any)
def guardedRoot : MExp := .seq (.call 2 [actual,actual]) (.notP .any)
def negatedRoot : MExp := .seq (.call 3 [actual,actual]) (.star .any)
def word (n : Nat) : List Char := List.replicate n 'a'
def tree (n : Nat) : Nat → List Char
  | 0 => word n++['@','?']++word n
  | depth+1 => word n++['#','(']++tree (2*n) depth++')'::word n
def sample (n depth : Nat) := tree n depth++'$'::tree n depth

theorem checked : FieldPlanCompiler.check original root parts specs root=true := by decide +kernel
theorem short_checked : FieldPlanCompiler.check original shortRoot parts specs shortRoot=true := by decide +kernel
theorem guard_checked : FieldPlanCompiler.check original guardedRoot parts specs guardedRoot=true := by decide +kernel
theorem negation_checked : FieldPlanCompiler.check original negatedRoot parts specs negatedRoot=true := by decide +kernel

theorem branch_patterns_and_rule_counts :
    parts.map Header.pattern=[[0],[1],[],[0]] ∧
    original.rules.map MRule.arity=[2,1,2,2] ∧
    generated.rules.map MRule.arity=[1,1,2,1,1,2,1,1,0,1,2] := by decide +kernel

theorem original_header_has_no_common_leading_anchor (d : Char) (js : List Nat) (body : MExp) :
    mainPlan.exp (sourceLeaf parts)≠TupleFieldTransfer.sourceBody d js body := by
  intro h
  cases h

theorem every_input_every_clock (x : List Char) (k : Nat) :
    evV original x .callByValuePar (tblV original x .callByValuePar k) [] root x.length=
      evV generated x .callByValueSeq (tblV generated x .callByValueSeq k) [] generatedRoot x.length :=
  FieldPlanCompiler.physical _ _ _ _ _ checked x k

theorem original_string_language :
    (fun x => SObs original .callByValuePar root x (some []))=
      (fun x => SObs generated .callByValueSeq generatedRoot x (some [])) :=
  FieldPlanCompiler.language_translation _ _ _ _ _ checked

theorem direct_recursive_runs :
    ([0,1,2].flatMap (fun n => [0,1,2].map (fun depth => (n,depth)))).all (fun (n,depth) =>
      evV generated (sample n depth) .callByValueSeq
        (tblV generated (sample n depth) .callByValueSeq (depth+2)) [] generatedRoot (sample n depth).length==some (some 0))=true := by decide +kernel

theorem branch_uses_the_second_distinct_value :
    [2,3,8].all (fun n => evV generated (tree n 0) .callByValueSeq
      (tblV generated (tree n 0) .callByValueSeq 2) []
      (FieldPlanCompiler.targetStart parts specs shortRoot) (tree n 0).length==some (some 0))=true := by decide +kernel

theorem consuming_independent_fallback :
    evV generated ['b'] .callByValueSeq (tblV generated ['b'] .callByValueSeq 1) []
      (FieldPlanCompiler.targetStart parts specs shortRoot) 1=some (some 0) := by decide +kernel

theorem guard_and_negation_commit :
    evV generated (tree 2 1) .callByValueSeq (tblV generated (tree 2 1) .callByValueSeq 3) []
      (FieldPlanCompiler.targetStart parts specs guardedRoot) (tree 2 1).length=some (some 0) ∧
    evV generated (tree 2 0) .callByValueSeq (tblV generated (tree 2 0) .callByValueSeq 3) []
      (FieldPlanCompiler.targetStart parts specs guardedRoot) (tree 2 0).length=some none ∧
    evV generated ['b'] .callByValueSeq (tblV generated ['b'] .callByValueSeq 1) []
      (FieldPlanCompiler.targetStart parts specs negatedRoot) 1=some (some 0) := by decide +kernel

def badPriorityRoot : MExp := .seq (.call 0 [.eps,.eps]) (.notP .any)
theorem committed_branch_does_not_retry_after_eof :
    FieldPlanCompiler.check original badPriorityRoot parts specs badPriorityRoot=true ∧
    evV generated ['@','?','b'] .callByValueSeq (tblV generated ['@','?','b'] .callByValueSeq 2) []
      (FieldPlanCompiler.targetStart parts specs badPriorityRoot) 3=some none ∧
    evV generated ['@','?','b'] .callByValueSeq (tblV generated ['@','?','b'] .callByValueSeq 2) []
      (.seq (.call 8 []) (.notP .any)) 3=some (some 0) := by decide +kernel

def strictFailureRoot : MExp := .seq (.call 0 [.lit ['a'],.eps]) (.notP .any)
theorem strict_preflight_before_independent_branch :
    FieldPlanCompiler.check original strictFailureRoot parts specs strictFailureRoot=true ∧
    evV generated ['b'] .callByValueSeq (tblV generated ['b'] .callByValueSeq 2) []
      (FieldPlanCompiler.targetStart parts specs strictFailureRoot) 1=some none ∧
    evV generated ['b'] .callByValueSeq (tblV generated ['b'] .callByValueSeq 2) []
      (.seq (.call 8 []) (.notP .any)) 1=some (some 0) := by decide +kernel

def undefinedRoot : MExp := .call 0 [.eps,.star .eps]
theorem undefined_actual_checked : FieldPlanCompiler.check original undefinedRoot parts specs undefinedRoot=true := by decide +kernel
theorem strict_actual_undefinedness (x : List Char) (k : Nat) :
    evV original x .callByValuePar (tblV original x .callByValuePar k) [] undefinedRoot x.length=none ∧
    evV generated x .callByValueSeq (tblV generated x .callByValueSeq k) []
      (FieldPlanCompiler.targetStart parts specs undefinedRoot) x.length=none := by
  have he : evV original x .callByValuePar (tblV original x .callByValuePar k) [] (.star .eps) x.length=none :=
    evStar_stuck rfl (Nat.lt_irrefl _)
  have hs : evV original x .callByValuePar (tblV original x .callByValuePar k) [] undefinedRoot x.length=none := by
    rw [undefinedRoot,evV_call_par (show ruleAtM original.rules 0=some ⟨2,mainPlan.exp (sourceLeaf parts)⟩ from rfl)
      rfl (by decide),evPar_cons_ok (show evV original x .callByValuePar _ [] .eps x.length=some (some x.length) from rfl),
      evPar_cons_none he]
  exact ⟨hs,(FieldPlanCompiler.physical _ _ _ _ _ undefined_actual_checked x k).symm.trans hs⟩

theorem negated_dispatch_zero_checked :
    FieldPlanCompiler.check original (.call 3 [.eps,.eps]) parts specs (.call 3 [.eps,.eps])=true := by decide +kernel

theorem negated_dispatch_at_zero_clock_is_still_unknown (x : List Char) :
    evV generated x .callByValueSeq (tblV generated x .callByValueSeq 0) []
      (FieldPlanCompiler.targetStart parts specs (.call 3 [.eps,.eps])) x.length=none :=
  (FieldPlanCompiler.physical _ _ _ _ _ negated_dispatch_zero_checked x 0).symm.trans rfl

theorem malformed_plans_and_declarations_rejected :
    FieldPlanSyntax.check parts [⟨1,mainPlan⟩]=false ∧
    FieldPlanSyntax.check parts [⟨2,.leaf 99⟩]=false ∧
    FieldPlanCompiler.check ⟨[⟨2,.eps⟩]⟩ root parts specs root=false ∧
    FieldPlanCompiler.check original .eps parts specs root=false := by decide +kernel

theorem invalid_calls_keep_their_early_failure :
    FieldPlanCompiler.check original (.call 99 [.star .eps]) parts specs (.call 99 [.star .eps])=true ∧
    FieldPlanCompiler.check original (.call 0 [.star .eps]) parts specs (.call 0 [.star .eps])=true ∧
    evV generated ['b'] .callByValueSeq (tblV generated ['b'] .callByValueSeq 1) []
      (FieldPlanCompiler.targetStart parts specs (.call 99 [.star .eps])) 1=some none ∧
    evV generated ['b'] .callByValueSeq (tblV generated ['b'] .callByValueSeq 1) []
      (FieldPlanCompiler.targetStart parts specs (.call 0 [.star .eps])) 1=some none := by decide +kernel

end Shallot.MacroPeg.CBV.FieldPlanExamples
