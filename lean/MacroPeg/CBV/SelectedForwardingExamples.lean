import MacroPeg.CBV.SelectedForwardingNormalization

namespace Shallot.MacroPeg.CBV.SelectedForwardingExamples
open MultiplyingPrefixCompiler (Spec sourceBody)
open SelectedForwardingContext (check)
open SelectedForwardingNormalization (normalized)
open RepeatedWordArguments (copies expression)
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def growing : Spec := ⟨0,3,
  .seq (.lit ['!']) (.seq (.call 2 [.lit ['X','?']]) (.lit ['?'])),.lit ['g']⟩
def forwarding : Spec := ⟨0,1,.eps,.lit ['f']⟩
def originBody : MExp := .alt (.lit ['X']) (.seq (.param 0) (.call 1 [.lit ['a','b']]))
def grammar : MGrammar := ⟨[
  ⟨1,sourceBody growing⟩,⟨1,sourceBody forwarding⟩,⟨1,originBody⟩]⟩
/-- Unselected metadata is deliberately unrelated to the origin rule. -/
def metadata : List Spec := [growing,forwarding,⟨99,2,.eps,.eps⟩]
def selected := [0,1]

theorem firstOrder : grammar.FirstOrder := by
  simp [grammar,growing,forwarding,originBody,sourceBody,MGrammar.FirstOrder,MExp.FirstOrder,MExp.FirstOrderArgs,expression]
theorem checked : check grammar metadata selected=true := by decide +kernel
theorem wrong_origin_shape_rejected : check grammar metadata [0,1,2]=false := by decide +kernel
theorem dropped_forward_successor_rejected : check grammar metadata [1]=false := by decide +kernel
theorem changed_body_rejected : check grammar [⟨0,3,.eps,.lit ['g']⟩,forwarding,⟨99,2,.eps,.eps⟩] selected=false := by decide +kernel

def entry : MExp := .call 1 [.lit ['a','b']]
def originalRun (e : MExp) (x : List Char) (k : Nat) := evV grammar x .callByValuePar
  (tblV grammar x .callByValuePar k) [] e x.length
def compiledRun (e : MExp) (x : List Char) (k : Nat) := evV (normalized grammar metadata selected) x .callByValuePar
  (tblV (normalized grammar metadata selected) x .callByValuePar k) [] e x.length

theorem original_parent_returns : originalRun entry (copies ['a','b'] 3++['g','!','X','?']) 12=some (some 0) := by decide +kernel
theorem compiled_parent_returns : compiledRun entry (copies ['a','b'] 3++['g','!','X','?']) 12=some (some 0) := by decide +kernel
theorem original_origin_callback : originalRun (.call 2 [.lit ['x']]) ['x','a','b','g'] 12=some (some 0) := by decide +kernel
theorem compiled_origin_callback : compiledRun (.call 2 [.lit ['x']]) ['x','a','b','g'] 12=some (some 0) := by decide +kernel
/-- The controller may finish before its argument's endpoint. Its body
must not be replaced by the unrelated metadata placeholder. -/
theorem origin_short_result : originalRun (.call 2 [.lit ['X','?']]) ['X','?'] 12=some (some 1) ∧
    compiledRun (.call 2 [.lit ['X','?']]) ['X','?'] 12=some (some 1) := by decide +kernel
theorem clock_gap : originalRun entry ['a','b','g'] 1=none ∧
    compiledRun entry ['a','b','g'] 1=some (some 0) := by decide +kernel
theorem all_observations (e : MExp) (he : e.FirstOrder) (x : List Char) (rest : Option (List Char)) :
    SObs grammar .callByValuePar e x rest ↔ SObs (normalized grammar metadata selected) .callByValuePar e x rest :=
  SelectedForwardingNormalization.checked_observations grammar firstOrder metadata selected checked e he x rest

def cyclicMeta : List Spec := [⟨1,1,.eps,.eps⟩,⟨0,1,.eps,.eps⟩,⟨99,2,.eps,.eps⟩]
def cyclicGrammar : MGrammar := ⟨[
  ⟨1,sourceBody ⟨1,1,.eps,.eps⟩⟩,⟨1,sourceBody ⟨0,1,.eps,.eps⟩⟩,⟨0,.lit ['X']⟩]⟩
theorem cyclic_checked : check cyclicGrammar cyclicMeta [0,1]=true := by decide +kernel
theorem other_arity_retained : evV (normalized cyclicGrammar cyclicMeta [0,1]) ['X'] .callByValuePar
    (tblV (normalized cyclicGrammar cyclicMeta [0,1]) ['X'] .callByValuePar 8) [] (.call 2 []) 1=some (some 0) := by decide +kernel

end Shallot.MacroPeg.CBV.SelectedForwardingExamples
