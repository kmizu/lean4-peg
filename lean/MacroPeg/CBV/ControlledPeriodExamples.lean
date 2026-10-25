import MacroPeg.CBV.ControlledPeriodCompiler
import MacroPeg.CBV.ConsumingPatternExamples

namespace Shallot.MacroPeg.CBV.ControlledPeriodExamples
open RetainedPatternSyntax ControlledPeriodSyntax
open CopyPeriodControl (Tail)
set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev bodies := ConsumingPatternExamples.bodies
abbrev clients := ConsumingPatternExamples.clients
abbrev arity := ConsumingPatternExamples.arity
abbrev alphabet := ConsumingPatternExamples.alphabet
abbrev d := ConsumingPatternExamples.d
abbrev pattern := ConsumingPatternExamples.pattern
abbrev actuals := ConsumingPatternExamples.actuals
abbrev words := ConsumingPatternExamples.words
abbrev block := ConsumingPatternExamples.block
abbrev required := ConsumingPatternExamples.required
abbrev entry := ConsumingPatternExamples.entry
def flow : Tail := .alt (.seq (.lit ['+']) .block) (.lit ['~'])
def original := ControlledPeriodSyntax.source bodies clients arity d pattern flow
def generated := ControlledPeriodSyntax.target bodies clients arity d pattern flow
def originalRoot := render bodies.length clients.length true entry
def generatedRoot := emit bodies.length clients.length arity d pattern flow entry
def step (n : Nat) (flag : Bool) : List Char :=
  if flag then block n++'+'::block n else block n++['~']
def steps (n : Nat) : List Bool → List Char
  | [] => [] | f::fs => step n f++steps n fs
def tree (n : Nat) (flags : List Bool) : Nat → List Char
  | 0 => List.replicate n 'a'++'|'::steps n flags
  | depth+1 => List.replicate n 'a'++'|'::(steps n flags++'!'::(tree (2*n) flags depth++':'::List.replicate n 'a'))

theorem checked : ControlledPeriodCompiler.check original originalRoot bodies clients arity alphabet d pattern flow required entry=true := by decide +kernel
theorem source_arities : original.rules.map MRule.arity=[0,0,1,1,4] := by decide +kernel
theorem target_arities : generated.rules.map MRule.arity=[0,0,1,1,1,1,1,1,1,1] := by decide +kernel
theorem source_trees : [(0,[false],0),(1,[true,false],1),(2,[false,true,false],0)].all (fun (n,flags,depth) =>
    evV original (tree n flags depth) .callByValuePar (tblV original (tree n flags depth) .callByValuePar 14) [] originalRoot (tree n flags depth).length==some (some 0))=true := by decide +kernel
theorem target_trees : [(0,[false],0),(1,[true,false],1),(2,[false,true,false],0)].all (fun (n,flags,depth) =>
    evV generated (tree n flags depth) .callByValueSeq (tblV generated (tree n flags depth) .callByValueSeq 14) [] generatedRoot (tree n flags depth).length==some (some 0))=true := by decide +kernel

def smallEntry : RetainedPatternSyntax.Expr := .copy [.lit ['a'],.lit ['a','b']]
def smallSource (t : Tail) := ControlledPeriodSyntax.source [] [] 2 d [1,0] t
def smallTarget (t : Tail) := ControlledPeriodSyntax.target [] [] 2 d [1,0] t
def smallRoot (t : Tail) := emit 0 0 2 d [1,0] t smallEntry
def B : List Char := ['a','b','#','a','#']
def mixed := B++['~']++B++['+']++B++['X']
theorem mixed_iterations_leave_suffix :
    evV (smallSource flow) mixed .callByValuePar (tblV (smallSource flow) mixed .callByValuePar 2) [] (render 0 0 true smallEntry) mixed.length=some (some 1) ∧
    evV (smallTarget flow) mixed .callByValueSeq (tblV (smallTarget flow) mixed .callByValueSeq 2) [] (smallRoot flow) mixed.length=some (some 1) := by decide +kernel

def committed : Tail := .seq (.alt (.chr '+') .eps) (.chr '+')
def rejectedIteration := B++['+']
theorem failed_suffix_rolls_back_whole_iteration :
    evV (smallSource committed) rejectedIteration .callByValuePar (tblV (smallSource committed) rejectedIteration .callByValuePar 1) [] (render 0 0 true smallEntry) rejectedIteration.length=some (some rejectedIteration.length) ∧
    evV (smallTarget committed) rejectedIteration .callByValueSeq (tblV (smallTarget committed) rejectedIteration .callByValueSeq 1) [] (smallRoot committed) rejectedIteration.length=some (some rejectedIteration.length) := by decide +kernel
theorem suffix_probe_is_required :
    evV (smallTarget committed) rejectedIteration .callByValueSeq (tblV (smallTarget committed) rejectedIteration .callByValueSeq 1) []
      (ControlledPeriodTransfer.recapture 3 d [1,0]) rejectedIteration.length=some none := by decide +kernel

theorem retained_negative_test_controls_whole_iteration :
    evV (smallSource (.notP .block)) (B++B++['X']) .callByValuePar (tblV (smallSource (.notP .block)) (B++B++['X']) .callByValuePar 1) []
      (render 0 0 true smallEntry) (B++B++['X']).length=some (some (B++B++['X']).length) ∧
    evV (smallTarget (.notP .block)) (B++B++['X']) .callByValueSeq (tblV (smallTarget (.notP .block)) (B++B++['X']) .callByValueSeq 1) []
      (smallRoot (.notP .block)) (B++B++['X']).length=some (some (B++B++['X']).length) ∧
    evV (smallTarget (.notP .block)) (B++['X']) .callByValueSeq (tblV (smallTarget (.notP .block)) (B++['X']) .callByValueSeq 1) []
      (smallRoot (.notP .block)) (B++['X']).length=some (some 1) := by decide +kernel

def innerStar : Tail := .seq (.star (.seq (.chr '+') .block)) (.chr '~')
def innerInput := B++['+']++B++['+']++B++['~']++B++['~','X']
theorem nested_consuming_star :
    evV (smallSource innerStar) innerInput .callByValuePar (tblV (smallSource innerStar) innerInput .callByValuePar 1) [] (render 0 0 true smallEntry) innerInput.length=some (some 1) ∧
    evV (smallTarget innerStar) innerInput .callByValueSeq (tblV (smallTarget innerStar) innerInput .callByValueSeq 1) [] (smallRoot innerStar) innerInput.length=some (some 1) := by decide +kernel

def emptyEntry : RetainedPatternSyntax.Expr := .copy [.eps]
def helperSource := ControlledPeriodSyntax.source [.chr '~'] [] 1 d [0] (.helper 0)
def helperTarget := ControlledPeriodSyntax.target [.chr '~'] [] 1 d [0] (.helper 0)
theorem helper_checked : ControlledPeriodCompiler.check helperSource (render 1 0 true emptyEntry) [.chr '~'] [] 1 [] d [0] (.helper 0) [] emptyEntry=true := by decide +kernel
theorem physical_helper_clock_is_preserved :
    evV helperSource ['#','~','X'] .callByValuePar (tblV helperSource ['#','~','X'] .callByValuePar 1) [] (render 1 0 true emptyEntry) 3=none ∧
    evV helperTarget ['#','~','X'] .callByValueSeq (tblV helperTarget ['#','~','X'] .callByValueSeq 1) [] (emit 1 0 1 d [0] (.helper 0) emptyEntry) 3=none ∧
    evV helperSource ['#','~','X'] .callByValuePar (tblV helperSource ['#','~','X'] .callByValuePar 2) [] (render 1 0 true emptyEntry) 3=some (some 1) ∧
    evV helperTarget ['#','~','X'] .callByValueSeq (tblV helperTarget ['#','~','X'] .callByValueSeq 2) [] (emit 1 0 1 d [0] (.helper 0) emptyEntry) 3=some (some 1) := by decide +kernel
theorem bad_helper_scope_rejected : ControlledPeriodSyntax.bodyCheck 0 2 [1,0] (.helper 0)=false := by decide +kernel

def divergent : Tail := .star .eps
def divergentSource := ControlledPeriodSyntax.source [] [] 1 d [0] divergent
def divergentTarget := ControlledPeriodSyntax.target [] [] 1 d [0] divergent
theorem divergent_checked : ControlledPeriodCompiler.check divergentSource (render 0 0 true emptyEntry) [] [] 1 [] d [0] divergent [] emptyEntry=true := by decide +kernel
theorem failed_anchor_skips_divergent_tail :
    evV divergentSource ['X'] .callByValuePar (tblV divergentSource ['X'] .callByValuePar 1) [] (render 0 0 true emptyEntry) 1=some (some 1) ∧
    evV divergentTarget ['X'] .callByValueSeq (tblV divergentTarget ['X'] .callByValueSeq 1) [] (emit 0 0 1 d [0] divergent emptyEntry) 1=some (some 1) := by decide +kernel

def recursiveFlow : Tail := .seq (.helper 0) .block
def recursiveSource := ControlledPeriodSyntax.source [FiniteResidualControl.balancedBody] [] 1 d [0] recursiveFlow
def recursiveTarget := ControlledPeriodSyntax.target [FiniteResidualControl.balancedBody] [] 1 d [0] recursiveFlow
def recursiveInput := '#'::(DelimitedCopyExamples.long 4++['#','#']++DelimitedCopyExamples.long 1++['#','X'])
theorem recursive_checked : ControlledPeriodCompiler.check recursiveSource (render 1 0 true emptyEntry)
    [FiniteResidualControl.balancedBody] [] 1 [] d [0] recursiveFlow [] emptyEntry=true := by decide +kernel
theorem recursive_helper_in_variable_iterations :
    evV recursiveSource recursiveInput .callByValuePar (tblV recursiveSource recursiveInput .callByValuePar 10) [] (render 1 0 true emptyEntry) recursiveInput.length=some (some 1) ∧
    evV recursiveTarget recursiveInput .callByValueSeq (tblV recursiveTarget recursiveInput .callByValueSeq 10) [] (emit 1 0 1 d [0] recursiveFlow emptyEntry) recursiveInput.length=some (some 1) := by decide +kernel

theorem all_physical_clocks (x : List Char) (k : Nat) :
    evV original x .callByValuePar (tblV original x .callByValuePar k) [] originalRoot x.length=
      evV generated x .callByValueSeq (tblV generated x .callByValueSeq k) [] generatedRoot x.length :=
  ControlledPeriodCompiler.physical original originalRoot bodies clients arity alphabet d pattern flow required entry checked x k

end Shallot.MacroPeg.CBV.ControlledPeriodExamples
