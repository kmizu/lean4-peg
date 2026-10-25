import MacroPeg.CBV.ControlledCopyCompiler
import MacroPeg.CBV.ConsumingPatternExamples

namespace Shallot.MacroPeg.CBV.ControlledCopyExamples
open RetainedPatternSyntax
open ControlledCopySyntax
open CopyBodyControl (Body)
abbrev Term := RetainedPatternSyntax.Expr
set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev bodies := ConsumingPatternExamples.bodies
abbrev clients := ConsumingPatternExamples.clients
abbrev arity := ConsumingPatternExamples.arity
abbrev alphabet := ConsumingPatternExamples.alphabet
abbrev d := ConsumingPatternExamples.d
abbrev required := ConsumingPatternExamples.required
abbrev entry := ConsumingPatternExamples.entry
abbrev actuals := ConsumingPatternExamples.actuals
abbrev words := ConsumingPatternExamples.words
abbrev block := ConsumingPatternExamples.block
abbrev tree := ConsumingPatternExamples.tree

def segments : List Nat → Body
  | [] => .eps | i::is => .seq (.segment i) (segments is)
/-- The second segment can be either value 1 or value 2. The negation is
evaluated after value 0 was consumed, with the original capture tuple. -/
def body : Body := .seq (.segment 0) (.seq (.alt (.seq (.notP (.segment 1)) (.segment 2)) (.segment 1)) (segments [1,0,3,2,1]))
def original := source bodies clients arity d body
def generated := target bodies clients arity d body
def originalRoot := render bodies.length clients.length true entry
def generatedRoot := emit bodies.length clients.length arity body entry

theorem checked : ControlledCopyCompiler.check original originalRoot bodies clients arity alphabet d body required entry=true := by decide +kernel
theorem source_arities : original.rules.map MRule.arity=[0,0,1,1,4] := by decide +kernel
theorem target_rule_count : generated.rules.length=97 := by decide +kernel
theorem target_arities : (generated.rules.take 5).map MRule.arity=[0,0,1,1,0] ∧
    (generated.rules.drop 5).all (fun r => r.arity==1)=true := by decide +kernel

theorem source_trees : [(0,0),(1,0),(1,1),(2,1),(1,2)].all (fun (n,depth) =>
    evV original (tree n depth) .callByValuePar (tblV original (tree n depth) .callByValuePar 14) [] originalRoot (tree n depth).length==some (some 0))=true := by decide +kernel
theorem target_trees : [(0,0),(1,0),(1,1),(2,1),(1,2)].all (fun (n,depth) =>
    evV generated (tree n depth) .callByValueSeq (tblV generated (tree n depth) .callByValueSeq 14) [] generatedRoot (tree n depth).length==some (some 0))=true := by decide +kernel

def alternateBlock (n : Nat) := [0,1,1,0,3,2,1].flatMap (fun i => (words n)[i]!++[d])
def alternateInput := ['a','|']++alternateBlock 1
theorem different_choice_path :
    evV original alternateInput .callByValuePar (tblV original alternateInput .callByValuePar 10) [] originalRoot alternateInput.length=some (some 0) ∧
    evV generated alternateInput .callByValueSeq (tblV generated alternateInput .callByValueSeq 10) [] generatedRoot alternateInput.length=some (some 0) := by decide +kernel

theorem actual_tuple_preserved :
    evParArgs original (block 2) .callByValuePar (tblV original (block 2) .callByValuePar 10) [List.replicate 2 'a']
      (renderArgs bodies.length clients.length true actuals) (block 2).length=some (some (words 2)) := by decide +kernel

def testArgs : List Term := [.lit ['a'],.lit ['a'],.eps,.eps]
def testEntry : Term := .copy testArgs
def committed : Body := .seq (.alt (.segment 0) .eps) (.segment 1)
def wrongDistribution : Body := .alt (.seq (.segment 0) (.segment 1)) (.segment 1)
def commitSource := source [] [] arity d committed
def commitTarget := target [] [] arity d committed

theorem committed_checked : ControlledCopyCompiler.check commitSource (render 0 0 true testEntry) [] [] arity alphabet d committed [] testEntry=true := by decide +kernel
theorem committed_choice_failure :
    evV commitSource ['a','#'] .callByValuePar (tblV commitSource ['a','#'] .callByValuePar 3) [] (render 0 0 true testEntry) 2=some none ∧
    evV commitTarget ['a','#'] .callByValueSeq (tblV commitTarget ['a','#'] .callByValueSeq 3) [] (emit 0 0 arity committed testEntry) 2=some none := by decide +kernel

theorem distributing_continuation_is_wrong :
    evV (source [] [] arity d wrongDistribution) ['a','#'] .callByValuePar (tblV (source [] [] arity d wrongDistribution) ['a','#'] .callByValuePar 3) [] (render 0 0 true testEntry) 2=some (some 0) := by decide +kernel

def emptyEntry : Term := .copy [.eps,.eps,.eps,.eps]
theorem empty_body_checked : ControlledCopyCompiler.check (source [] [] arity d .eps) (render 0 0 true emptyEntry) [] [] arity alphabet d .eps [] emptyEntry=true := by decide +kernel

theorem clock_zero_and_one :
    evV (source [] [] arity d .eps) ['a'] .callByValuePar (tblV (source [] [] arity d .eps) ['a'] .callByValuePar 0) [] (render 0 0 true emptyEntry) 1=none ∧
    evV (target [] [] arity d .eps) ['a'] .callByValueSeq (tblV (target [] [] arity d .eps) ['a'] .callByValueSeq 0) [] (emit 0 0 arity .eps emptyEntry) 1=none ∧
    evV (source [] [] arity d .eps) ['a'] .callByValuePar (tblV (source [] [] arity d .eps) ['a'] .callByValuePar 1) [] (render 0 0 true emptyEntry) 1=some (some 1) ∧
    evV (target [] [] arity d .eps) ['a'] .callByValueSeq (tblV (target [] [] arity d .eps) ['a'] .callByValueSeq 1) [] (emit 0 0 arity .eps emptyEntry) 1=some (some 1) := by decide +kernel

theorem initialization_gate_is_required :
    evV (target [] [] arity d .eps) ['a'] .callByValueSeq (tblV (target [] [] arity d .eps) ['a'] .callByValueSeq 0) []
      (CopyBodyEmission.emitPlan 0 arity .eps (emitArgs 0 0 arity .eps [.eps,.eps,.eps,.eps]) (CopyBodyControl.normalized .eps)) 1=some (some 1) := by decide +kernel

def nullableBody : Body := .star (.notP (.segment 0))
def nullableEntry : Term := .copy [.lit ['a'],.eps,.eps,.eps]
theorem nullable_checked : ControlledCopyCompiler.check (source [] [] arity d nullableBody) (render 0 0 true nullableEntry) [] [] arity alphabet d nullableBody [] nullableEntry=true := by decide +kernel

theorem nullable_can_stop :
    evV (source [] [] arity d nullableBody) ['a','#'] .callByValuePar (tblV (source [] [] arity d nullableBody) ['a','#'] .callByValuePar 3) [] (render 0 0 true nullableEntry) 2=some (some 2) ∧
    evV (target [] [] arity d nullableBody) ['a','#'] .callByValueSeq (tblV (target [] [] arity d nullableBody) ['a','#'] .callByValueSeq 3) [] (emit 0 0 arity nullableBody nullableEntry) 2=some (some 2) := by decide +kernel

theorem consuming_star_rejected : CopyBodyControl.check arity (.star (.segment 0))=false := by decide +kernel
theorem bad_body_scope_rejected : CopyBodyControl.check arity (.segment 99)=false := by decide +kernel
theorem wrong_source_rejected : ControlledCopyCompiler.check generated originalRoot bodies clients arity alphabet d body required entry=false := by decide +kernel

theorem same_physical_clock (x : List Char) (k : Nat) :
    evV original x .callByValuePar (tblV original x .callByValuePar k) [] originalRoot x.length=
      evV generated x .callByValueSeq (tblV generated x .callByValueSeq k) [] generatedRoot x.length :=
  ControlledCopyCompiler.physical original originalRoot bodies clients arity alphabet d body required entry checked x k

end Shallot.MacroPeg.CBV.ControlledCopyExamples
