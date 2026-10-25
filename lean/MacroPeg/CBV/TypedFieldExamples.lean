import MacroPeg.CBV.TypedFieldCompiler
import MacroPeg.CBV.NestedFieldProducerProofs

namespace Shallot.MacroPeg.CBV.TypedFieldExamples
open TypedFieldSyntax
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def nestedHeaders : List Header := [
  ⟨[['a']],['a','#','!'],'#',[0],NestedFieldProducer.producerBody⟩,
  ⟨[['a','#','!']],['a','#','!','@'],'@',[0],.param 0⟩]

theorem nested_checked :
    TypedFieldCompiler.check NestedFieldProducer.source NestedFieldProducer.root nestedHeaders NestedFieldProducer.root=true := by decide +kernel

theorem nested_is_the_generated_grammar :
    source nestedHeaders=NestedFieldProducer.source ∧ target nestedHeaders=NestedFieldProducer.target ∧
      emit nestedHeaders NestedFieldProducer.root=NestedFieldProducer.generatedRoot := ⟨rfl,rfl,rfl⟩

/-- The preceding hand-connected producer is now admitted by the finite
family compiler, with exactly the same fixed target and all-input theorem. -/
theorem nested_physical (x : List Char) (k : Nat) :
    evV NestedFieldProducer.source x .callByValuePar (tblV NestedFieldProducer.source x .callByValuePar k) []
      NestedFieldProducer.root x.length=
      evV (target nestedHeaders) x .callByValueSeq (tblV (target nestedHeaders) x .callByValueSeq k) []
        (emit nestedHeaders NestedFieldProducer.root) x.length :=
  TypedFieldCompiler.physical _ _ _ _ nested_checked x k

theorem generated_nested_all_lengths_and_depths (n depth : Nat) :
    evV (target nestedHeaders) (NestedFieldProducerProofs.sample n depth) .callByValueSeq
      (tblV (target nestedHeaders) (NestedFieldProducerProofs.sample n depth) .callByValueSeq (depth+2)) []
      (emit nestedHeaders NestedFieldProducer.root) (NestedFieldProducerProofs.sample n depth).length=some (some 0) :=
  (NestedFieldProducerProofs.source_and_target_all_trees n depth).2

def mutualProducerBody : MExp := .seq (.notP (.call 1 [.eps,.eps])) NestedFieldProducer.producerBody
def mutualOuterBody : MExp := .seq (.andP (.alt (.call 0 [.eps]) .eps)) (.param 0)
def mutualHeaders : List Header := [
  ⟨[['a']],['a','#','!'],'#',[0],mutualProducerBody⟩,
  ⟨[['a','#','!'],['z']],['a','#','!','@'],'@',[0],mutualOuterBody⟩,
  ⟨[],['a'],'$',[],.alt (.call 2 []) (.lit ['a'])⟩]
def mutualRoot : MExp := .seq (.call 1 [NestedFieldProducer.producer,.eps]) (.notP .any)
def original := source mutualHeaders
def generated := target mutualHeaders
def generatedRoot := emit mutualHeaders mutualRoot

theorem mutual_checked : TypedFieldCompiler.check original mutualRoot mutualHeaders mutualRoot=true := by decide +kernel

theorem differing_delimiters_arities_and_partial_cover :
    mutualHeaders.map Header.delimiter=['#','@','$'] ∧ original.rules.map MRule.arity=[1,2,0] ∧
    generated.rules.map MRule.arity=[1,2,1,1,2,0] ∧
    ¬(∀ i, i<2 → i∈([0] : List Nat)) := by decide +kernel

theorem mutual_physical (x : List Char) (k : Nat) :
    evV original x .callByValuePar (tblV original x .callByValuePar k) [] mutualRoot x.length=
      evV generated x .callByValueSeq (tblV generated x .callByValueSeq k) [] generatedRoot x.length :=
  TypedFieldCompiler.physical _ _ _ _ mutual_checked x k

theorem mutual_language :
    (fun x => SObs original .callByValuePar mutualRoot x (some []))=
      (fun x => SObs generated .callByValueSeq generatedRoot x (some [])) :=
  TypedFieldCompiler.language_translation _ _ _ _ mutual_checked

theorem direct_mutual_runs :
    ([0,1,2].flatMap (fun n => [0,1,2].map (fun depth => (n,depth)))).all (fun (n,depth) =>
      evV generated (NestedFieldProducerProofs.sample n depth) .callByValueSeq
        (tblV generated (NestedFieldProducerProofs.sample n depth) .callByValueSeq 12) []
        generatedRoot (NestedFieldProducerProofs.sample n depth).length==some (some 0))=true := by decide +kernel

theorem bad_actual_alphabet_rejected :
    TypedFieldCompiler.check original (.call 1 [NestedFieldProducer.producer,.lit ['#']]) mutualHeaders
      (.call 1 [NestedFieldProducer.producer,.lit ['#']])=false := by decide +kernel

theorem uncovered_parameter_rejected :
    headerCheck mutualHeaders ⟨[['a','#','!'],['z']],['a','#','!','@'],'@',[],mutualOuterBody⟩=false ∧
    headerCheck mutualHeaders ⟨[['a','#','!'],['z']],['a','#','!','@'],'@',[0,2],mutualOuterBody⟩=false := by decide +kernel

theorem delimiter_in_parameter_alphabet_rejected :
    headerCheck mutualHeaders ⟨[['a','#','!','@'],['z']],['a','#','!','@'],'@',[0],mutualOuterBody⟩=false := by decide +kernel

theorem incorrect_raw_declarations_rejected :
    TypedFieldCompiler.check ⟨[⟨0,.eps⟩]⟩ mutualRoot mutualHeaders mutualRoot=false ∧
    TypedFieldCompiler.check original .eps mutualHeaders mutualRoot=false := by decide +kernel

def unusedUndefined : MExp := .call 1 [.eps,.star .eps]
theorem unused_undefined_checked :
    TypedFieldCompiler.check original unusedUndefined mutualHeaders unusedUndefined=true := by decide +kernel

theorem unused_argument_undefinedness (x : List Char) (k : Nat) :
    evV original x .callByValuePar (tblV original x .callByValuePar k) [] unusedUndefined x.length=none ∧
    evV generated x .callByValueSeq (tblV generated x .callByValueSeq k) []
      (emit mutualHeaders unusedUndefined) x.length=none := by
  have hstar : evV original x .callByValuePar (tblV original x .callByValuePar k) [] (.star .eps) x.length=none :=
    evStar_stuck rfl (Nat.lt_irrefl _)
  have hs : evV original x .callByValuePar (tblV original x .callByValuePar k) [] unusedUndefined x.length=none := by
    rw [unusedUndefined,evV_call_par (show ruleAtM original.rules 1=some
      ⟨2,TupleFieldTransfer.sourceBody '@' [0] mutualOuterBody⟩ from rfl) rfl (by decide),
      evPar_cons_ok (show evV original x .callByValuePar _ [] .eps x.length=some (some x.length) from rfl),
      evPar_cons_none hstar]
  exact ⟨hs,(TypedFieldCompiler.physical _ _ _ _ unused_undefined_checked x k).symm.trans hs⟩

def cycleRoot : MExp := .call 2 []
theorem empty_anchor_cycle_checked :
    TypedFieldCompiler.check original cycleRoot mutualHeaders cycleRoot=true := by decide +kernel

theorem empty_anchor_cycle_undefined (x : List Char) (k : Nat) :
    evV original x .callByValuePar (tblV original x .callByValuePar k) [] cycleRoot x.length=none ∧
    evV generated x .callByValueSeq (tblV generated x .callByValueSeq k) []
      (emit mutualHeaders cycleRoot) x.length=none := by
  have hr : ruleAtM original.rules 2=some ⟨0,TupleFieldTransfer.sourceBody '$' [] (.alt (.call 2 []) (.lit ['a']))⟩ := rfl
  have hrow : valAt (tblV original x .callByValuePar k 2 []) x.length=none := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [valAt_tblV_succ hr _ (Nat.le_refl _),TupleFieldTransfer.sourceBody,
        evV_seq_ok (show evV original x .callByValuePar _ []
          (DelimiterTemplate.compile '$' (DelimitedWordPattern.sourceParts '$' [])) x.length=some (some x.length) from rfl)]
      exact evV_alt_none (by rw [evV_call_par hr rfl (by decide),evPar_nil]; exact ih)
  have hs : evV original x .callByValuePar (tblV original x .callByValuePar k) [] cycleRoot x.length=none := by
    rw [cycleRoot,evV_call_par hr rfl (by decide),evPar_nil]; exact hrow
  exact ⟨hs,(TypedFieldCompiler.physical _ _ _ _ empty_anchor_cycle_checked x k).symm.trans hs⟩

def tripleHeaders : List Header := nestedHeaders++[
  ⟨[['a','#','!','@']],['a','#','!','@','$'],'$',[0],.param 0⟩]
def tripleRoot : MExp := .seq (.call 2 [.call 1 [NestedFieldProducer.producer]]) (.notP .any)
def tripleSample (n depth : Nat) : List Char :=
  NestedFieldProducerProofs.sample n depth++'$'::NestedFieldProducerProofs.sample n depth

theorem three_positive_capture_levels_checked :
    TypedFieldCompiler.check (source tripleHeaders) tripleRoot tripleHeaders tripleRoot=true ∧
    (target tripleHeaders).rules.map MRule.arity=[1,2,1,2,1,2] := by decide +kernel

theorem direct_three_level_runs :
    ([0,1,2].flatMap (fun n => [0,1,2].map (fun depth => (n,depth)))).all (fun (n,depth) =>
      evV (target tripleHeaders) (tripleSample n depth) .callByValueSeq
        (tblV (target tripleHeaders) (tripleSample n depth) .callByValueSeq (depth+3)) []
        (emit tripleHeaders tripleRoot) (tripleSample n depth).length==some (some 0))=true := by decide +kernel

theorem three_level_language :
    (fun x => SObs (source tripleHeaders) .callByValuePar tripleRoot x (some []))=
      (fun x => SObs (target tripleHeaders) .callByValueSeq (emit tripleHeaders tripleRoot) x (some [])) :=
  TypedFieldCompiler.language_translation _ _ _ _ three_positive_capture_levels_checked.1

def failedUnused : MExp := .seq (.call 1 [.eps,.lit ['z']]) (.notP .any)
def erasedUnused : MExp := .seq (.call 1 [.eps,.eps]) (.notP .any)
theorem unused_actual_preflight_matters :
    TypedFieldCompiler.check original failedUnused mutualHeaders failedUnused=true ∧
    evV generated ['@'] .callByValueSeq (tblV generated ['@'] .callByValueSeq 4) []
      (emit mutualHeaders failedUnused) 1=some none ∧
    evV generated ['@'] .callByValueSeq (tblV generated ['@'] .callByValueSeq 4) []
      (emit mutualHeaders erasedUnused) 1=some (some 0) := by decide +kernel

def falseEffectHeaders : List Header := [
  ⟨[['a']],['a','!'],'#',[0],NestedFieldProducer.producerBody⟩,
  ⟨[['a','#','!']],['a','#','!','@'],'@',[0],.param 0⟩]
theorem output_annotations_are_checked :
    TypedFieldCompiler.check (source falseEffectHeaders) NestedFieldProducer.root falseEffectHeaders
      NestedFieldProducer.root=false ∧
    exprCheck mutualHeaders [] (.call 1 [.eps])=false ∧
    exprCheck mutualHeaders [] (.call 99 [])=false := by decide +kernel

def tupleHeaders : List Header := [
  ⟨[['a']],['a','#','!'],'#',[0],NestedFieldProducer.producerBody⟩,
  ⟨[['a','#','!'],['a']],['a','#','!','@'],'@',[0,1],.seq (.param 1) (.param 0)⟩]
def tupleRoot : MExp := .seq (.call 1 [NestedFieldProducer.producer,.lit ['a']]) (.notP .any)
def tupleSample (n depth : Nat) : List Char := NestedFieldProducerProofs.tree n depth++
  (['@','a','@','a']++NestedFieldProducerProofs.tree n depth)

theorem independently_live_typed_fields_checked :
    TypedFieldCompiler.check (source tupleHeaders) tupleRoot tupleHeaders tupleRoot=true ∧
    (target tupleHeaders).rules.map MRule.arity=[1,2,1,1,4] := by decide +kernel

theorem independently_live_fields_language :
    (fun x => SObs (source tupleHeaders) .callByValuePar tupleRoot x (some []))=
      (fun x => SObs (target tupleHeaders) .callByValueSeq (emit tupleHeaders tupleRoot) x (some [])) :=
  TypedFieldCompiler.language_translation _ _ _ _ independently_live_typed_fields_checked.1

theorem independently_live_fields_direct_runs :
    ([1,2].flatMap (fun n => [0,1,2].map (fun depth => (n,depth)))).all (fun (n,depth) =>
      evV (target tupleHeaders) (tupleSample n depth) .callByValueSeq
        (tblV (target tupleHeaders) (tupleSample n depth) .callByValueSeq (depth+2)) []
        (emit tupleHeaders tupleRoot) (tupleSample n depth).length==some (some 0))=true := by decide +kernel

def swappedReturn : List Char := NestedFieldProducerProofs.tree 1 1++
  (['@','a','@']++NestedFieldProducerProofs.tree 1 1++['a'])
theorem independent_field_failures :
    evV (target tupleHeaders) (tupleSample 0 1) .callByValueSeq
      (tblV (target tupleHeaders) (tupleSample 0 1) .callByValueSeq 4) []
      (emit tupleHeaders tupleRoot) (tupleSample 0 1).length=some none ∧
    evV (target tupleHeaders) swappedReturn .callByValueSeq
      (tblV (target tupleHeaders) swappedReturn .callByValueSeq 4) []
      (emit tupleHeaders tupleRoot) swappedReturn.length=some none := by decide +kernel

def unsafeHeaders : List Header := [
  ⟨[['a']],['a','#','!'],'#',[0],NestedFieldProducer.producerBody⟩,
  ⟨[['a','#','!']],['a','#','!'],'#',[0],.param 0⟩]
def unsafeSample : List Char := ['a','#','!','a','#','a','#','!','a']
/-- The input-alphabet/delimiter check is substantive: if bypassed, the
generated field scanner can stop inside the retained producer output. -/
theorem omitted_delimiter_check_changes_the_language :
    TypedFieldCompiler.check (source unsafeHeaders) NestedFieldProducer.root unsafeHeaders NestedFieldProducer.root=false ∧
    evV (source unsafeHeaders) unsafeSample .callByValuePar
      (tblV (source unsafeHeaders) unsafeSample .callByValuePar 4) [] NestedFieldProducer.root unsafeSample.length=some (some 0) ∧
    evV (target unsafeHeaders) unsafeSample .callByValueSeq
      (tblV (target unsafeHeaders) unsafeSample .callByValueSeq 4) []
      (emit unsafeHeaders NestedFieldProducer.root) unsafeSample.length=some none := by decide +kernel

end Shallot.MacroPeg.CBV.TypedFieldExamples
