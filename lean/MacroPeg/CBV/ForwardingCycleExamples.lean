import MacroPeg.CBV.ForwardingCycleElimination

namespace Shallot.MacroPeg.CBV.ForwardingCycleExamples
open MultiplyingPrefixCompiler
open ForwardingPrefixTrace (Result classify)
open ForwardingCycleElimination (normalized)
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- 0 feeds the 1/2 cycle. Rule 3 grows its value before reaching that
component; rule 4 terminates at a missing head callee. -/
def specs : List Spec := [
  ⟨1,1,.lit ['!'],.lit ['x']⟩,
  ⟨2,1,.call 3 [.star (.chr 'c')],.eps⟩,
  ⟨1,1,.notP (.param 0),.param 0⟩,
  ⟨0,3,.param 0,.eps⟩,
  ⟨9,1,.eps,.lit ['!']⟩]

theorem source_firstOrder : (source specs).FirstOrder := by
  simp [source,specs,MGrammar.FirstOrder,sourceBody,MExp.FirstOrder,MExp.FirstOrderArgs,
    RepeatedWordArguments.expression]
theorem classifications : classify specs 0=.cycle [2,1,0] ∧ classify specs 1=.cycle [2,1] ∧
    classify specs 2=.cycle [1,2] ∧ classify specs 3=.terminal 3 [] ∧
    classify specs 4=.terminal 9 [4] := by decide +kernel
theorem checked_component : ForwardingPrefixCycles.check specs [2,1,0]=true := by decide +kernel
theorem open_component_rejected : ForwardingPrefixCycles.check specs [1]=false := by decide +kernel
theorem growing_component_rejected : ForwardingPrefixCycles.check specs [3,0,1,2]=false := by decide +kernel

theorem held_none (x w : List Char) (k p j : Nat) (h : GuardedReplayControl.Aligned x w p j) :
    valAt (sourceTable specs x k 0 [w]) p=none :=
  ForwardingPrefixCycles.rows_none specs [2,1,0]
    ((ForwardingPrefixCycles.checked_iff specs [2,1,0]).mp checked_component) x k 0 (by simp) w p j h

def sourceRun (e : MExp) (x : List Char) (k : Nat) :=
  evV (source specs) x .callByValuePar (sourceTable specs x k) [] e x.length
def normalizedRun (e : MExp) (x : List Char) (k : Nat) :=
  evV (normalized specs) x .callByValuePar (tblV (normalized specs) x .callByValuePar k) [] e x.length

theorem actual_cycles : ∀ k∈[0,1,2,4,8],
    sourceRun (.call 0 [.lit ['a','b']]) ['a','b','!','x'] k=none ∧
    normalizedRun (.call 0 [.lit ['a','b']]) ['a','b','!','x'] k=none := by decide +kernel
theorem empty_capture : ∀ k∈[0,1,2,4,8], sourceRun (.call 0 [.lit []]) ['x'] k=none ∧
    normalizedRun (.call 0 [.lit []]) ['x'] k=none := by decide +kernel
theorem failed_argument : sourceRun (.call 0 [.lit ['a','b']]) ['a','x'] 8=some none ∧
    normalizedRun (.call 0 [.lit ['a','b']]) ['a','x'] 8=some none := by decide +kernel
theorem missing_forward_callee : sourceRun (.call 4 [.lit ['a','b']]) ['a','b','!'] 8=some (some 0) ∧
    normalizedRun (.call 4 [.lit ['a','b']]) ['a','b','!'] 8=some (some 0) := by decide +kernel
theorem growing_branch : sourceRun (.call 3 [.lit ['a','b']]) ['a','b'] 8=some (some 0) ∧
    normalizedRun (.call 3 [.lit ['a','b']]) ['a','b'] 8=some (some 0) ∧
    sourceRun (.call 3 [.lit ['a','b']]) ['a','b','a','b','a','b'] 8=none ∧
    normalizedRun (.call 3 [.lit ['a','b']]) ['a','b','a','b','a','b'] 8=none := by decide +kernel

theorem actual_body_preflight : evV (source specs) ['x'] .callByValuePar (sourceTable specs ['x'] 8)
    [['a']] (sourceBody ⟨1,1,.lit ['!'],.lit ['x']⟩) 1=some none ∧
    evV (source specs) ['x'] .callByValuePar (sourceTable specs ['x'] 8) [['a']]
      ForwardingPrefixCycles.deadBody 1=some none ∧
    evV (source specs) ['x'] .callByValuePar (sourceTable specs ['x'] 8) [['a']]
      (.star (.lit [])) 1=none := by decide +kernel
theorem malformed_environment : evV (source specs) ['a'] .callByValuePar (sourceTable specs ['a'] 8) []
    (sourceBody ⟨1,1,.lit ['!'],.lit ['x']⟩) 1=some none ∧
    evV (source specs) ['a'] .callByValuePar (sourceTable specs ['a'] 8) []
      ForwardingPrefixCycles.deadBody 1=some none := by decide +kernel

def contextual : MExp := .alt (.notP (.call 0 [.star (.chr 'c')])) (.call 4 [.lit ['a','b']])
theorem contextual_preservation (x : List Char) (rest : Option (List Char)) :
    SObs (source specs) .callByValuePar contextual x rest ↔ SObs (normalized specs) .callByValuePar contextual x rest :=
  ForwardingCycleElimination.observations_iff specs source_firstOrder contextual (by trivial) x rest

/-- A finite forwarding path into growth is distinguished from a cycle.
Its inlining and connection to the Seq compiler are still outstanding. -/
def acyclic : List Spec := [⟨1,1,.eps,.eps⟩,⟨1,3,.eps,.eps⟩]
theorem acyclic_classified : classify acyclic 0=.terminal 1 [0] := by decide +kernel

end Shallot.MacroPeg.CBV.ForwardingCycleExamples
