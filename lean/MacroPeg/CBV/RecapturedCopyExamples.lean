import MacroPeg.CBV.RecapturedCopyCompiler
import MacroPeg.CBV.ConsumingPatternExamples
import MacroPeg.CBV.RepeatedFrontierExamples

namespace Shallot.MacroPeg.CBV.RecapturedCopyExamples
open RetainedPatternSyntax RecapturedCopySyntax
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
def original := RecapturedCopySyntax.source bodies clients arity d pattern
def generated := RecapturedCopySyntax.target bodies clients arity d pattern
def originalRoot := render bodies.length clients.length true entry
def generatedRoot := emit bodies.length clients.length arity d pattern entry
def blocks (n : Nat) : Nat → List Char
  | 0 => []
  | r+1 => block n++blocks n r
def tree (n count : Nat) : Nat → List Char
  | 0 => List.replicate n 'a'++'|'::blocks n (count+1)
  | depth+1 => List.replicate n 'a'++'|'::(blocks n (count+1)++'!'::(tree (2*n) count depth++':'::List.replicate n 'a'))

theorem checked : RecapturedCopyCompiler.check original originalRoot bodies clients arity alphabet d pattern required entry=true := by decide +kernel
theorem source_arities : original.rules.map MRule.arity=[0,0,1,1,4] := by decide +kernel
theorem target_arities : generated.rules.map MRule.arity=[0,0,1,1,1,1,1,1,1] := by decide +kernel
theorem source_trees : [(0,0,0),(1,0,1),(1,1,1),(2,2,0)].all (fun (n,r,depth) =>
    evV original (tree n r depth) .callByValuePar (tblV original (tree n r depth) .callByValuePar 14) [] originalRoot (tree n r depth).length==some (some 0))=true := by decide +kernel
theorem target_trees : [(0,0,0),(1,0,1),(1,1,1),(2,2,0)].all (fun (n,r,depth) =>
    evV generated (tree n r depth) .callByValueSeq (tblV generated (tree n r depth) .callByValueSeq 14) [] generatedRoot (tree n r depth).length==some (some 0))=true := by decide +kernel

def twoEntry : RetainedPatternSyntax.Expr := .copy [.lit ['a'],.lit ['a','b']]
def twoSource := RecapturedCopySyntax.source [] [] 2 d [1,0]
def twoTarget := RecapturedCopySyntax.target [] [] 2 d [1,0]
def twoRoot := emit 0 0 2 d [1,0] twoEntry
theorem two_checked : RecapturedCopyCompiler.check twoSource (render 0 0 true twoEntry) [] [] 2 ['a','b'] d [1,0] [] twoEntry=true := by decide +kernel
theorem both_frontiers_and_zero :
    evV twoTarget RepeatedFrontierExamples.earlySmall .callByValueSeq (tblV twoTarget RepeatedFrontierExamples.earlySmall .callByValueSeq 1) [] twoRoot RepeatedFrontierExamples.earlySmall.length=some (some 5) ∧
    evV twoTarget RepeatedFrontierExamples.earlyLarge .callByValueSeq (tblV twoTarget RepeatedFrontierExamples.earlyLarge .callByValueSeq 1) [] twoRoot RepeatedFrontierExamples.earlyLarge.length=some (some 4) ∧
    evV twoTarget RepeatedFrontierExamples.zeroInput .callByValueSeq (tblV twoTarget RepeatedFrontierExamples.zeroInput .callByValueSeq 1) [] twoRoot RepeatedFrontierExamples.zeroInput.length=some (some 5) := by decide +kernel
theorem true_continuations :
    evV twoTarget RepeatedFrontierExamples.earlySmall .callByValueSeq (tblV twoTarget RepeatedFrontierExamples.earlySmall .callByValueSeq 1) []
      (.seq twoRoot (.lit ['a','b','#','b','#'])) RepeatedFrontierExamples.earlySmall.length=some (some 0) ∧
    evV twoTarget RepeatedFrontierExamples.earlyLarge .callByValueSeq (tblV twoTarget RepeatedFrontierExamples.earlyLarge .callByValueSeq 1) []
      (.seq twoRoot (.lit ['x','#','a','#'])) RepeatedFrontierExamples.earlyLarge.length=some (some 0) := by decide +kernel
theorem actual_block_capture :
    evSeqArgs twoTarget RepeatedFrontierExamples.earlySmall .callByValueSeq
      (tblV twoTarget RepeatedFrontierExamples.earlySmall .callByValueSeq 1) []
      [DelimiterTemplate.compile d (RecapturedCopyBlock.skeleton d [1,0])] RepeatedFrontierExamples.earlySmall.length=
      some (some ([['a','b','#','a','#']],5)) := by decide +kernel
theorem no_eof_and_no_gate : twoTarget.rules.map MRule.arity=[1,1,1] := by decide +kernel
theorem clock_zero_and_early_failure :
    evV twoTarget RepeatedFrontierExamples.earlySmall .callByValueSeq (tblV twoTarget RepeatedFrontierExamples.earlySmall .callByValueSeq 0) [] twoRoot RepeatedFrontierExamples.earlySmall.length=none ∧
    evV twoTarget ['x'] .callByValueSeq (tblV twoTarget ['x'] .callByValueSeq 0) [] twoRoot 1=some none := by decide +kernel

theorem first_block_verification_required :
    evV twoTarget RepeatedFrontierExamples.zeroInput .callByValueSeq (tblV twoTarget RepeatedFrontierExamples.zeroInput .callByValueSeq 1) []
      (.call 2 [DelimiterTemplate.compile d (RecapturedCopyBlock.skeleton d [1,0])]) RepeatedFrontierExamples.zeroInput.length=some (some 0) := by decide +kernel
theorem outer_preflight_required :
    evV twoTarget ['x'] .callByValueSeq (tblV twoTarget ['x'] .callByValueSeq 1) []
      (RootObservation.branch (.andP (DelimitedPatternEvaluation.targetHead 0 [.lit ['a'],.lit ['a','b']]))
        (.call 2 [DelimiterTemplate.compile d (RecapturedCopyBlock.skeleton d [1,0])]) .eps) 1=some (some 1) := by decide +kernel

def emptyEntry : RetainedPatternSyntax.Expr := .copy [.eps,.eps,.eps,.eps]
def emptySource := RecapturedCopySyntax.source [] [] arity d pattern
def emptyTarget := RecapturedCopySyntax.target [] [] arity d pattern
theorem empty_checked : RecapturedCopyCompiler.check emptySource (render 0 0 true emptyEntry) [] [] arity alphabet d pattern [] emptyEntry=true := by decide +kernel
theorem empty_captures_consume_and_stop :
    [([],0),(['X'],1),(List.replicate 6 d,6),(List.replicate 15 d++['X'],2),(List.replicate 21 d,0)].all (fun (x,q) =>
      evV emptySource x .callByValuePar (tblV emptySource x .callByValuePar 1) [] (render 0 0 true emptyEntry) x.length==some (some q) &&
      evV emptyTarget x .callByValueSeq (tblV emptyTarget x .callByValueSeq 1) [] (emit 0 0 arity d pattern emptyEntry) x.length==some (some q))=true := by decide +kernel

def recursiveEntry : RetainedPatternSyntax.Expr := .user 0 .eps
def recursiveWords : List (List Char) := [DelimitedCopyExamples.long 4,[],List.replicate 4 'a',DelimitedCopyExamples.short 4]
def recursiveBlock := DelimitedWordPattern.encode d recursiveWords pattern
def recursiveInput := '|'::(recursiveBlock++recursiveBlock++recursiveBlock)
theorem recursive_checked : RecapturedCopyCompiler.check original (render 2 2 true recursiveEntry) bodies clients arity alphabet d pattern required recursiveEntry=true := by decide +kernel
theorem consuming_recursive_producer :
    evV original recursiveInput .callByValuePar (tblV original recursiveInput .callByValuePar 14) [] (render 2 2 true recursiveEntry) recursiveInput.length=some (some 0) ∧
    evV generated recursiveInput .callByValueSeq (tblV generated recursiveInput .callByValueSeq 14) [] (emit 2 2 arity d pattern recursiveEntry) recursiveInput.length=some (some 0) := by decide +kernel

theorem all_physical_clocks (x : List Char) (k : Nat) :
    evV original x .callByValuePar (tblV original x .callByValuePar k) [] originalRoot x.length=
      evV generated x .callByValueSeq (tblV generated x .callByValueSeq k) [] generatedRoot x.length :=
  RecapturedCopyCompiler.physical original originalRoot bodies clients arity alphabet d pattern required entry checked x k

end Shallot.MacroPeg.CBV.RecapturedCopyExamples
