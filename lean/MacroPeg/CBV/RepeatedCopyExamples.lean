import MacroPeg.CBV.RepeatedCopyCompiler
import MacroPeg.CBV.ConsumingPatternExamples

namespace Shallot.MacroPeg.CBV.RepeatedCopyExamples
open RetainedPatternSyntax RepeatedCopySyntax
set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev bodies := ConsumingPatternExamples.bodies
abbrev arity := ConsumingPatternExamples.arity
abbrev alphabet := ConsumingPatternExamples.alphabet
abbrev d := ConsumingPatternExamples.d
abbrev body := ConsumingPatternExamples.pattern
abbrev actuals := ConsumingPatternExamples.actuals
abbrev words := ConsumingPatternExamples.words
abbrev block := ConsumingPatternExamples.block
abbrev required := ConsumingPatternExamples.required
def tail : RetainedPatternSyntax.Expr := .seq (.chr '|') (.copy actuals)
def clients := [tail,ConsumingPatternExamples.producer]
abbrev entry := ConsumingPatternExamples.entry
def original := RepeatedCopySyntax.source bodies clients arity d body
def generated := RepeatedCopySyntax.target bodies clients arity d body
def originalRoot := render bodies.length clients.length true entry
def generatedRoot := emit bodies.length clients.length arity body entry
def blocks (n : Nat) : Nat → List Char
  | 0 => []
  | r+1 => block n++blocks n r
def input (n r : Nat) := List.replicate n 'a'++'|'::blocks n r

theorem checked : RepeatedCopyCompiler.check original originalRoot bodies clients arity alphabet d body required entry=true := by decide +kernel
theorem source_arities : original.rules.map MRule.arity=[0,0,1,1,4] := by decide +kernel
theorem target_arities : generated.rules.map MRule.arity=[0,0,1,1,0,1,1,1,1] := by decide +kernel
theorem source_repetitions : [(0,1),(1,1),(1,2),(2,3)].all (fun (n,r) =>
    evV original (input n r) .callByValuePar (tblV original (input n r) .callByValuePar 14) [] originalRoot (input n r).length==some (some 0))=true := by decide +kernel
theorem target_repetitions : [(0,1),(1,1),(1,2),(2,3)].all (fun (n,r) =>
    evV generated (input n r) .callByValueSeq (tblV generated (input n r) .callByValueSeq 14) [] generatedRoot (input n r).length==some (some 0))=true := by decide +kernel
theorem actual_tuple : evParArgs original (blocks 2 3) .callByValuePar (tblV original (blocks 2 3) .callByValuePar 10) [List.replicate 2 'a']
    (renderArgs bodies.length clients.length true actuals) (blocks 2 3).length=some (some (words 2)) := by decide +kernel

def badInput := input 1 2++['x']
theorem leftover_rejected :
    evV original badInput .callByValuePar (tblV original badInput .callByValuePar 12) [] originalRoot badInput.length=some none ∧
    evV generated badInput .callByValueSeq (tblV generated badInput .callByValueSeq 12) [] generatedRoot badInput.length=some none := by decide +kernel

def emptyEntry : RetainedPatternSyntax.Expr := .copy [.eps,.eps,.eps,.eps]
theorem empty_checked : RepeatedCopyCompiler.check (RepeatedCopySyntax.source [] [] arity d body) (render 0 0 true emptyEntry)
    [] [] arity alphabet d body [] emptyEntry=true := by decide +kernel
theorem empty_and_delimiters :
    [[],List.replicate 7 d,List.replicate 21 d].all (fun x =>
      evV (RepeatedCopySyntax.source [] [] arity d body) x .callByValuePar (tblV (RepeatedCopySyntax.source [] [] arity d body) x .callByValuePar 1) [] (render 0 0 true emptyEntry) x.length==some (some 0) &&
      evV (RepeatedCopySyntax.target [] [] arity d body) x .callByValueSeq (tblV (RepeatedCopySyntax.target [] [] arity d body) x .callByValueSeq 1) [] (emit 0 0 arity body emptyEntry) x.length==some (some 0))=true := by decide +kernel
theorem clock_zero_undefined :
    evV (RepeatedCopySyntax.source [] [] arity d body) [] .callByValuePar (tblV (RepeatedCopySyntax.source [] [] arity d body) [] .callByValuePar 0) [] (render 0 0 true emptyEntry) 0=none ∧
    evV (RepeatedCopySyntax.target [] [] arity d body) [] .callByValueSeq (tblV (RepeatedCopySyntax.target [] [] arity d body) [] .callByValueSeq 0) [] (emit 0 0 arity body emptyEntry) 0=none := by decide +kernel

theorem initialization_cannot_be_omitted :
    evV (RepeatedCopySyntax.target [] [] arity d body) [] .callByValueSeq (tblV (RepeatedCopySyntax.target [] [] arity d body) [] .callByValueSeq 0) []
      (.seq (DelimitedPatternEvaluation.preflight (emitArgs 0 0 arity body [.eps,.eps,.eps,.eps]))
        (.alt (.notP .any) (DelimitedPatternEvaluation.passes 1 (emitArgs 0 0 arity body [.eps,.eps,.eps,.eps]) (List.range arity)))) 0=some (some 0) := by decide +kernel

theorem argument_failure_precedes_initialization :
    evV (RepeatedCopySyntax.source [] [] arity d body) ['a'] .callByValuePar (tblV (RepeatedCopySyntax.source [] [] arity d body) ['a'] .callByValuePar 0) []
      (render 0 0 true (.copy [.lit ['b'],.eps,.eps,.eps])) 1=some none ∧
    evV (RepeatedCopySyntax.target [] [] arity d body) ['a'] .callByValueSeq (tblV (RepeatedCopySyntax.target [] [] arity d body) ['a'] .callByValueSeq 0) []
      (emit 0 0 arity body (.copy [.lit ['b'],.eps,.eps,.eps])) 1=some none := by decide +kernel

def frontierInput : List Char := ['a','b','#','a','#','a','b','#','b','#']
/-- Without the common EOF, two real unary loops stop after different
numbers of iterations. This is not a class-separation claim. -/
theorem eof_is_needed :
    evV generated frontierInput .callByValueSeq (tblV generated frontierInput .callByValueSeq 0) [['a']]
      (.star (DelimiterTemplate.compile d (DelimitedWordPattern.viewParts d 0 [1,0]))) frontierInput.length=some (some 5) ∧
    evV generated frontierInput .callByValueSeq (tblV generated frontierInput .callByValueSeq 0) [['a','b']]
      (.star (DelimiterTemplate.compile d (DelimitedWordPattern.viewParts d 1 [1,0]))) frontierInput.length=some (some 0) := by decide +kernel
theorem empty_pattern_rejected : patternCheck arity []=false := by decide +kernel
theorem invalid_scope_rejected : patternCheck arity [4]=false := by decide +kernel

/-- The consuming producer really recurses with an empty retained parent;
the produced word then participates in three consuming copy iterations. -/
def recursiveEntry : RetainedPatternSyntax.Expr :=
  .user 0 .eps
def recursiveWords : List (List Char) :=
  [DelimitedCopyExamples.long 4,[],List.replicate 4 'a',DelimitedCopyExamples.short 4]
def recursiveBlock := DelimitedWordPattern.encode d recursiveWords body
def recursiveInput := '|'::(recursiveBlock++recursiveBlock++recursiveBlock)
theorem recursive_checked : RepeatedCopyCompiler.check original (render 2 2 true recursiveEntry)
    bodies clients arity alphabet d body required recursiveEntry=true := by decide +kernel
theorem recursive_actual_capture :
    evParArgs original (recursiveBlock++recursiveBlock++recursiveBlock) .callByValuePar
      (tblV original (recursiveBlock++recursiveBlock++recursiveBlock) .callByValuePar 12) [[]]
      (renderArgs 2 2 true actuals) (recursiveBlock++recursiveBlock++recursiveBlock).length=some (some recursiveWords) := by decide +kernel
theorem consuming_recursive_producer :
    evV original recursiveInput .callByValuePar (tblV original recursiveInput .callByValuePar 14) [] (render 2 2 true recursiveEntry) recursiveInput.length=some (some 0) ∧
    evV generated recursiveInput .callByValueSeq (tblV generated recursiveInput .callByValueSeq 14) [] (emit 2 2 arity body recursiveEntry) recursiveInput.length=some (some 0) := by decide +kernel

theorem same_physical_clock (x : List Char) (k : Nat) :
    evV original x .callByValuePar (tblV original x .callByValuePar k) [] originalRoot x.length=
      evV generated x .callByValueSeq (tblV generated x .callByValueSeq k) [] generatedRoot x.length :=
  RepeatedCopyCompiler.physical original originalRoot bodies clients arity alphabet d body required entry checked x k

end Shallot.MacroPeg.CBV.RepeatedCopyExamples
