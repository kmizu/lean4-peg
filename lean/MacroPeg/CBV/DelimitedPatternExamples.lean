import MacroPeg.CBV.DelimitedPatternCompiler
import MacroPeg.CBV.DelimitedCopyExamples

namespace Shallot.MacroPeg.CBV.DelimitedPatternExamples
open DelimitedPatternCompiler
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def d : Char := '#'
def alphabet : List Char := ['a','b','c']
def bodies := [FiniteResidualControl.balancedBody,FiniteResidualControl.consumePrefix]
def args : List MExp := [.call 0 [],.call 1 [],.star (.chr 'a'),.eps]
def pattern : List Nat := [0,2,1,0,3,2,1]
def original := source bodies args.length d pattern
def generated := target bodies args.length d pattern
def originalRoot := root bodies args
def generatedRoot := targetRoot bodies args

def words (n : Nat) : List (List Char) := [DelimitedCopyExamples.long n,DelimitedCopyExamples.short n,List.replicate n 'a',[]]
def block (n : Nat) : List Char := pattern.flatMap (fun i => (words n)[i]!++[d])

theorem checked : check original originalRoot bodies args alphabet d pattern=true := by decide +kernel
theorem source_arities : original.rules.map MRule.arity=[0,0,4] := by decide +kernel
theorem target_arities : generated.rules.map MRule.arity=[0,0,1,1,1,1] := by decide +kernel

theorem actual_four_words :
    evParArgs original (block 3) .callByValuePar (tblV original (block 3) .callByValuePar 8) [] args (block 3).length=some (some (words 3)) := by decide +kernel

theorem source_examples : [0,1,2,4].all (fun n =>
    evV original (block n) .callByValuePar (tblV original (block n) .callByValuePar 8) [] originalRoot (block n).length==some (some 0))=true := by decide +kernel

theorem target_examples : [0,1,2,4].all (fun n =>
    evV generated (block n) .callByValueSeq (tblV generated (block n) .callByValueSeq 8) [] generatedRoot (block n).length==some (some 0))=true := by decide +kernel

def wrongBlock : List Char := (DelimitedCopyExamples.long 2++[d])++(['a']++[d])++
  (pattern.drop 2).flatMap (fun i => (words 2)[i]!++[d])

theorem wrong_middle_copy :
    evV original wrongBlock .callByValuePar (tblV original wrongBlock .callByValuePar 8) [] originalRoot wrongBlock.length=some none ∧
    evV generated wrongBlock .callByValueSeq (tblV generated wrongBlock .callByValueSeq 8) [] generatedRoot wrongBlock.length=some none := by decide +kernel

theorem residual_preserved :
    evV original (block 2++['!','X']) .callByValuePar (tblV original (block 2++['!','X']) .callByValuePar 8) [] originalRoot (block 2++['!','X']).length=some (some 2) ∧
    evV generated (block 2++['!','X']) .callByValueSeq (tblV generated (block 2++['!','X']) .callByValueSeq 8) [] generatedRoot (block 2++['!','X']).length=some (some 2) := by decide +kernel

def reversedPattern : List Nat := [1,0,2,3,0,1]
def reversedSource := source bodies args.length d reversedPattern
def reversedTarget := target bodies args.length d reversedPattern

theorem reversed_checked : check reversedSource originalRoot bodies args alphabet d reversedPattern=true := by decide +kernel
/-- The first selected word need not be the longest parser on all inputs;
positive n then fails consistently, whereas all n=0 endpoints fit. -/
theorem reversed_endpoints :
    evV reversedSource (reversedPattern.flatMap (fun i => (words 0)[i]!++[d])) .callByValuePar
      (tblV reversedSource (reversedPattern.flatMap (fun i => (words 0)[i]!++[d])) .callByValuePar 8) [] originalRoot
      (reversedPattern.flatMap (fun i => (words 0)[i]!++[d])).length=some (some 0) ∧
    evV reversedTarget (reversedPattern.flatMap (fun i => (words 0)[i]!++[d])) .callByValueSeq
      (tblV reversedTarget (reversedPattern.flatMap (fun i => (words 0)[i]!++[d])) .callByValueSeq 8) [] generatedRoot
      (reversedPattern.flatMap (fun i => (words 0)[i]!++[d])).length=some (some 0) := by decide +kernel

def loopBodies : List MExp := [.call 0 []]
def loopArgs : List MExp := [.eps,.call 0 []]
def loopPattern : List Nat := [0,1]
def loopSource := source loopBodies 2 d loopPattern
def loopTarget := target loopBodies 2 d loopPattern

theorem loop_checked : check loopSource (root loopBodies loopArgs) loopBodies loopArgs alphabet d loopPattern=true := by decide +kernel

theorem loop_row (x : List Char) (k p : Nat) (hp : p≤x.length) :
    valAt (tblV loopSource x .callByValuePar k 0 []) p=none := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [valAt_tblV_succ (show ruleAtM loopSource.rules 0=some ⟨0,.call 0 []⟩ from rfl) [] hp]
    change evV loopSource x .callByValuePar (tblV loopSource x .callByValuePar k) [] (.call 0 []) p=none
    rw [evV_call_par (show ruleAtM loopSource.rules 0=some ⟨0,.call 0 []⟩ from rfl) rfl (by decide),evPar_nil]
    exact ih

theorem later_actual_undefined (x : List Char) (k : Nat) :
    evV loopSource x .callByValuePar (tblV loopSource x .callByValuePar k) [] (root loopBodies loopArgs) x.length=none := by
  have hr : ruleAtM loopSource.rules loopBodies.length=some ⟨2,DelimiterTemplate.compile d (DelimitedWordPattern.sourceParts d loopPattern)⟩ := rfl
  rw [root,evV_call_par hr rfl (by decide),loopArgs,
    evPar_cons_ok (show evV loopSource x .callByValuePar (tblV loopSource x .callByValuePar k) [] .eps x.length=some (some x.length) from rfl)]
  have hh : evV loopSource x .callByValuePar (tblV loopSource x .callByValuePar k) [] (.call 0 []) x.length=none := by
    rw [evV_call_par (show ruleAtM loopSource.rules 0=some ⟨0,.call 0 []⟩ from rfl) rfl (by decide),evPar_nil]
    exact loop_row x k x.length (Nat.le_refl _)
  rw [evPar_cons_none hh]

theorem generated_later_actual_undefined (x : List Char) (k : Nat) :
    evV loopTarget x .callByValueSeq (tblV loopTarget x .callByValueSeq k) [] (targetRoot loopBodies loopArgs) x.length=none := by
  exact (physical loopSource (root loopBodies loopArgs) loopBodies loopArgs alphabet d loopPattern loop_checked x k).symm.trans (later_actual_undefined x k)

/-- Without preflight the first projection fails before the looping actual. -/
theorem preflight_is_required :
    evV loopTarget ['a'] .callByValueSeq (tblV loopTarget ['a'] .callByValueSeq 3) []
      (DelimitedPatternEvaluation.passes loopBodies.length loopArgs (List.range loopArgs.length)) 1=some none := by decide +kernel

theorem out_of_scope_rejected : checkCore bodies args alphabet d [0,4]=false := by decide +kernel
theorem empty_arity_rejected : checkCore bodies [] alphabet d [0]=false := by decide +kernel
theorem empty_pattern_rejected : checkCore bodies args alphabet d []=false := by decide +kernel
theorem separator_capture_rejected : checkCore bodies [.lit [d]] alphabet d [0]=false := by decide +kernel
theorem wrong_declaration_rejected : check generated originalRoot bodies args alphabet d pattern=false := by decide +kernel

theorem same_physical_clock (x : List Char) (k : Nat) :
    evV original x .callByValuePar (tblV original x .callByValuePar k) [] originalRoot x.length=
      evV generated x .callByValueSeq (tblV generated x .callByValueSeq k) [] generatedRoot x.length :=
  physical original originalRoot bodies args alphabet d pattern checked x k

theorem all_original_strings :
    (fun x => SObs original .callByValuePar originalRoot x (some []))=
      (fun x => SObs generated .callByValueSeq generatedRoot x (some [])) :=
  language_translation original originalRoot bodies args alphabet d pattern checked

end Shallot.MacroPeg.CBV.DelimitedPatternExamples
