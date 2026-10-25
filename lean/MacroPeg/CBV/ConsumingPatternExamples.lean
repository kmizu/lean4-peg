import MacroPeg.CBV.ConsumingPatternCompiler
import MacroPeg.CBV.RetainedPatternCompiler
import MacroPeg.CBV.DelimitedPatternExamples

namespace Shallot.MacroPeg.CBV.ConsumingPatternExamples
open RetainedPatternSyntax
abbrev Term := RetainedPatternSyntax.Expr
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def bodies := [FiniteResidualControl.balancedBody,FiniteResidualControl.consumePrefix]
def arity : Nat := 4
def d : Char := '#'
def alphabet : List Char := ['a','b','c']
def pattern : List Nat := [0,2,1,0,3,2,1]
def actuals : List Term := [.helper 0,.parent,.user 1 .parent,.helper 1]
def copying : Term := .copy actuals
def tail : Term := .seq (.chr '|') (.seq copying
  (.alt (.seq (.chr '!') (.seq (.user 0 (.seq .parent .parent)) (.seq (.chr ':') .parent))) .eps))
/-- For a parent a^n at a^(2n)b, the first branch returns ww. With an
empty parent this client is a real recursive a-star producer. -/
def producer : Term := .alt (.seq .parent (.notP (.chr 'a'))) (.seq (.chr 'a') (.user 1 .parent))
def clients : List Term := [tail,producer]
def required : List Bool := [true,false]
def entry : Term := .seq (.user 0 (.star (.chr 'a'))) (.notP .any)
def original := source bodies clients arity d pattern
def generated := target bodies clients arity d pattern
def originalRoot := render bodies.length clients.length true entry
def generatedRoot := render bodies.length clients.length false entry

def words (n : Nat) : List (List Char) :=
  [DelimitedCopyExamples.long (2*n),List.replicate n 'a',List.replicate (2*n) 'a',DelimitedCopyExamples.short (2*n)]
def block (n : Nat) : List Char := pattern.flatMap (fun i => (words n)[i]!++[d])
def tree (n : Nat) : Nat → List Char
  | 0 => List.replicate n 'a'++'|'::block n
  | depth+1 => List.replicate n 'a'++'|'::(block n++'!'::(tree (2*n) depth++':'::List.replicate n 'a'))

theorem checked : ConsumingPatternCompiler.check original originalRoot bodies clients arity alphabet d pattern required entry=true := by decide +kernel
theorem computed_return_effects : RetainedCaptureEffects.effects bodies clients alphabet=[false,true] := by decide +kernel
theorem source_arities : original.rules.map MRule.arity=[0,0,1,1,4] := by decide +kernel
theorem target_arities : generated.rules.map MRule.arity=[0,0,1,1,1,1,1,1] := by decide +kernel

def samples : List (Nat × Nat) := [(0,0),(1,0),(1,1),(2,1),(1,2)]
theorem source_trees : samples.all (fun (n,depth) =>
    evV original (tree n depth) .callByValuePar (tblV original (tree n depth) .callByValuePar 14) [] originalRoot (tree n depth).length==some (some 0))=true := by decide +kernel
theorem target_trees : samples.all (fun (n,depth) =>
    evV generated (tree n depth) .callByValueSeq (tblV generated (tree n depth) .callByValueSeq 14) [] generatedRoot (tree n depth).length==some (some 0))=true := by decide +kernel

theorem parent_and_recursive_result_are_actual_captures :
    evParArgs original (block 2) .callByValuePar (tblV original (block 2) .callByValuePar 8) [List.replicate 2 'a']
      (renderArgs bodies.length clients.length true actuals) (block 2).length=some (some (words 2)) := by decide +kernel

theorem old_query_only_checker_rejects :
    RetainedPatternCompiler.check original originalRoot bodies clients arity alphabet d pattern entry=false := by decide +kernel

theorem missing_parent_requirement_rejected :
    ConsumingPatternChecks.check bodies clients arity alphabet d pattern [false,false] entry=false := by decide +kernel

def badSeed : Term := .seq (.user 0 (.lit ['a','#'])) (.notP .any)
theorem separator_seed_rejected : ConsumingPatternChecks.check bodies clients arity alphabet d pattern required badSeed=false := by decide +kernel

def nonfreeProducerEntry : Term := .seq (.user 1 (.lit ['a','#'])) (.notP .any)
theorem unmarked_client_allows_separator_parent :
    ConsumingPatternCompiler.check original (render bodies.length clients.length true nonfreeProducerEntry) bodies clients arity alphabet d pattern required nonfreeProducerEntry=true ∧
    evV original ['a','#','a','#'] .callByValuePar (tblV original ['a','#','a','#'] .callByValuePar 8) [] (render bodies.length clients.length true nonfreeProducerEntry) 4=some (some 0) ∧
    evV generated ['a','#','a','#'] .callByValueSeq (tblV generated ['a','#','a','#'] .callByValueSeq 8) [] (render bodies.length clients.length false nonfreeProducerEntry) 4=some (some 0) := by decide +kernel

theorem recursive_producer_safe : RetainedCaptureEffects.safeCheck bodies clients (RetainedCaptureEffects.effects bodies clients alphabet) alphabet false (.user 1 .eps)=true := by decide +kernel

def unsafeProducerActual : Term := .copy [.helper 0,.parent,.user 0 .parent,.helper 1]
theorem separator_consuming_client_not_safe :
    ConsumingPatternChecks.termCheck bodies clients arity alphabet required true true unsafeProducerActual=false := by decide +kernel

def leakedChild := tree 1 1++['a']
theorem parent_restoration_rejects_child_value :
    evV original leakedChild .callByValuePar (tblV original leakedChild .callByValuePar 14) [] originalRoot leakedChild.length=some none ∧
    evV generated leakedChild .callByValueSeq (tblV generated leakedChild .callByValueSeq 14) [] generatedRoot leakedChild.length=some none := by decide +kernel

def shortChild : List Char := ['a','|']++block 1++['!','a','|']++block 2++[':','a']
theorem doubled_child_capture_is_real :
    evV original shortChild .callByValuePar (tblV original shortChild .callByValuePar 14) [] originalRoot shortChild.length=some none ∧
    evV generated shortChild .callByValueSeq (tblV generated shortChild .callByValueSeq 14) [] generatedRoot shortChild.length=some none := by decide +kernel

theorem wrong_source_rejected : ConsumingPatternCompiler.check generated originalRoot bodies clients arity alphabet d pattern required entry=false := by decide +kernel

theorem same_physical_clock (x : List Char) (k : Nat) :
    evV original x .callByValuePar (tblV original x .callByValuePar k) [] originalRoot x.length=
      evV generated x .callByValueSeq (tblV generated x .callByValueSeq k) [] generatedRoot x.length :=
  ConsumingPatternCompiler.physical original originalRoot bodies clients arity alphabet d pattern required entry checked x k

end Shallot.MacroPeg.CBV.ConsumingPatternExamples
