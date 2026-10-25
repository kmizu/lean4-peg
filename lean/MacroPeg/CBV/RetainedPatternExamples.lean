import MacroPeg.CBV.RetainedPatternCompiler
import MacroPeg.CBV.DelimitedPatternExamples

namespace Shallot.MacroPeg.CBV.RetainedPatternExamples
open RetainedPatternSyntax
abbrev Term := RetainedPatternSyntax.Expr
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def bodies := [FiniteResidualControl.balancedBody,FiniteResidualControl.consumePrefix]
def arity : Nat := 4
def d : Char := '#'
def alphabet : List Char := ['a','b','c']
def pattern : List Nat := [0,2,1,0,3,2,1]
def peek (a : Term) : Term := .notP (.notP a)
def selectActual : Term := .alt (.seq (peek (.user 1 .parent)) (.helper 1)) (.helper 0)
def actuals : List Term := [.helper 0,selectActual,.star (.chr 'a'),.eps]
def copying : Term := .copy actuals
/-- A child captures two copies of the current parent word. The suffix
then replays the original parent's word after the child has returned. -/
def tail : Term := .seq (.chr '|') (.seq copying
  (.alt (.seq (.chr '!') (.seq (.user 0 (.seq .parent .parent)) (.seq (.chr ':') .parent))) .eps))
def clients : List Term := [tail,.eps]
def entry : Term := .seq (.user 0 (.star (.chr 'a'))) (.notP .any)
def original := source bodies clients arity d pattern
def generated := target bodies clients arity d pattern
def originalRoot := render bodies.length clients.length true entry
def generatedRoot := render bodies.length clients.length false entry
abbrev block := DelimitedPatternExamples.block

def tree (n : Nat) : Nat → List Char
  | 0 => List.replicate n 'a'++'|'::block n
  | depth+1 => List.replicate n 'a'++'|'::(block n++'!'::(tree (2*n) depth++':'::List.replicate n 'a'))

theorem checked : RetainedPatternCompiler.check original originalRoot bodies clients arity alphabet d pattern entry=true := by decide +kernel
theorem source_arities : original.rules.map MRule.arity=[0,0,1,1,4] := by decide +kernel
theorem target_arities : generated.rules.map MRule.arity=[0,0,1,1,1,1,1,1] := by decide +kernel

def cases : List (Nat × Nat) := [(0,0),(1,0),(1,1),(2,1),(1,2)]
theorem source_trees : cases.all (fun (n,depth) =>
    evV original (tree n depth) .callByValuePar (tblV original (tree n depth) .callByValuePar 12) [] originalRoot (tree n depth).length==some (some 0))=true := by decide +kernel
theorem target_trees : cases.all (fun (n,depth) =>
    evV generated (tree n depth) .callByValueSeq (tblV generated (tree n depth) .callByValueSeq 12) [] generatedRoot (tree n depth).length==some (some 0))=true := by decide +kernel

/-- The same current input yields different real captured tuples under
two different parent values. A unary call occurs inside the actual query. -/
theorem actuals_depend_on_parent :
    evParArgs original (block 1) .callByValuePar (tblV original (block 1) .callByValuePar 8) [List.replicate 1 'a']
      (renderArgs bodies.length clients.length true actuals) (block 1).length=some (some [['a','b','c'],['a','b'],['a'],[]]) ∧
    evParArgs original (block 1) .callByValuePar (tblV original (block 1) .callByValuePar 8) [List.replicate 3 'a']
      (renderArgs bodies.length clients.length true actuals) (block 1).length=some (some [['a','b','c'],['a','b','c'],['a'],[]]) := by decide +kernel

def fallbackBlock : List Char := pattern.flatMap (fun i => ([['a','b','c'],['a','b','c'],['a'],[]] : List (List Char))[i]!++[d])
def fallbackInput : List Char := ['a','a','a','|']++fallbackBlock
theorem fallback_source_and_target :
    evV original fallbackInput .callByValuePar (tblV original fallbackInput .callByValuePar 8) [] originalRoot fallbackInput.length=some (some 0) ∧
    evV generated fallbackInput .callByValueSeq (tblV generated fallbackInput .callByValueSeq 8) [] generatedRoot fallbackInput.length=some (some 0) := by decide +kernel

def separatorParentEntry : Term := .seq (.user 0 (.lit ['a','#'])) (.notP .any)
def separatorParentInput := ['a','#','|']++fallbackBlock
theorem separator_parent_checked : RetainedPatternCompiler.check original (render bodies.length clients.length true separatorParentEntry)
    bodies clients arity alphabet d pattern separatorParentEntry=true := by decide +kernel
theorem separator_in_parent_is_allowed :
    evV original separatorParentInput .callByValuePar (tblV original separatorParentInput .callByValuePar 8) [] (render bodies.length clients.length true separatorParentEntry) separatorParentInput.length=some (some 0) ∧
    evV generated separatorParentInput .callByValueSeq (tblV generated separatorParentInput .callByValueSeq 8) [] (render bodies.length clients.length false separatorParentEntry) separatorParentInput.length=some (some 0) := by decide +kernel

def leakedChild := tree 1 1++['a']
theorem parent_restoration_rejects_child_value :
    evV original leakedChild .callByValuePar (tblV original leakedChild .callByValuePar 12) [] originalRoot leakedChild.length=some none ∧
    evV generated leakedChild .callByValueSeq (tblV generated leakedChild .callByValueSeq 12) [] generatedRoot leakedChild.length=some none := by decide +kernel

def shortChild : List Char := ['a','|']++block 1++['!','a','|']++block 2++[':','a']
theorem doubled_child_capture_is_real :
    evV original shortChild .callByValuePar (tblV original shortChild .callByValuePar 12) [] originalRoot shortChild.length=some none ∧
    evV generated shortChild .callByValueSeq (tblV generated shortChild .callByValueSeq 12) [] generatedRoot shortChild.length=some none := by decide +kernel

theorem root_parent_rejected : RetainedPatternSyntax.check bodies clients arity alphabet d pattern .parent=false := by decide +kernel
theorem consuming_parent_copy_actual_rejected :
    RetainedPatternSyntax.termCheck bodies clients arity alphabet true (.copy [.parent,.eps,.eps,.eps])=false := by decide +kernel
theorem out_of_scope_user_rejected : RetainedPatternSyntax.check bodies clients arity alphabet d pattern (.user 99 .eps)=false := by decide +kernel
theorem wrong_source_rejected : RetainedPatternCompiler.check generated originalRoot bodies clients arity alphabet d pattern entry=false := by decide +kernel

theorem same_physical_clock (x : List Char) (k : Nat) :
    evV original x .callByValuePar (tblV original x .callByValuePar k) [] originalRoot x.length=
      evV generated x .callByValueSeq (tblV generated x .callByValueSeq k) [] generatedRoot x.length :=
  RetainedPatternCompiler.physical original originalRoot bodies clients arity alphabet d pattern entry checked x k

end Shallot.MacroPeg.CBV.RetainedPatternExamples
