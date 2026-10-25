import MacroPeg.CBV.ForwardingHeadNormalization
import MacroPeg.CBV.ForwardingCycleExamples

namespace Shallot.MacroPeg.CBV.ForwardingHeadExamples
open MultiplyingPrefixCompiler
open ForwardingHeadExpansion (expanded frame)
open ForwardingHeadNormalization (normalized)
open RepeatedWordArguments (copies expression)
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def chain : List Spec := [⟨1,1,.eps,.eps⟩,⟨1,3,.eps,.eps⟩]
def entry : MExp := .call 0 [.lit ['a','b']]
def sourceRun (rs : List Spec) (e : MExp) (x : List Char) (k : Nat) :=
  evV (source rs) x .callByValuePar (sourceTable rs x k) [] e x.length
def normalizedRun (rs : List Spec) (e : MExp) (x : List Char) (k : Nat) :=
  evV (normalized rs) x .callByValuePar (tblV (normalized rs) x .callByValuePar k) [] e x.length

theorem chain_firstOrder : (source chain).FirstOrder := by
  simp [source,chain,MGrammar.FirstOrder,sourceBody,MExp.FirstOrder,MExp.FirstOrderArgs,expression]
theorem chain_complete : ForwardingHeadExpansion.complete chain (chain.length+1) 0 []=true := by decide +kernel
theorem chain_source : ∀ n∈[1,3,9], sourceRun chain entry (copies ['a','b'] n) 8=some (some 0) := by decide +kernel
theorem chain_normalized : ∀ n∈[1,3,9], normalizedRun chain entry (copies ['a','b'] n) 8=some (some 0) := by decide +kernel
theorem clock_gap : sourceRun chain entry ['a','b'] 1=none ∧
    normalizedRun chain entry ['a','b'] 1=some (some 0) := by decide +kernel
theorem chain_language (x : List Char) : SObs (source chain) .callByValuePar entry x (some []) ↔
    SObs (normalized chain) .callByValuePar entry x (some []) :=
  ForwardingHeadNormalization.observations_iff chain chain_firstOrder entry (by trivial) x (some [])

def returning : List Spec := [⟨1,1,.lit ['?'],.eps⟩,⟨2,1,.lit ['!'],.eps⟩,⟨2,3,.eps,.eps⟩]
theorem returning_source : ∀ n∈[1,3,9], sourceRun returning entry (copies ['a','b'] n++['!','?']) 8=some (some 0) := by decide +kernel
theorem returning_normalized : ∀ n∈[1,3,9], normalizedRun returning entry (copies ['a','b'] n++['!','?']) 8=some (some 0) := by decide +kernel
theorem cyclic_component : ∀ k∈[0,1,2,4,8],
    sourceRun ForwardingCycleExamples.specs entry ['a','b'] k=none ∧
    normalizedRun ForwardingCycleExamples.specs entry ['a','b'] k=none := by decide +kernel

def scopedSpecs : List Spec := [⟨1,1,.eps,.eps⟩,⟨9,3,.eps,.param 1⟩]
theorem scoped_environment :
    evV (source scopedSpecs) ['a','b'] .callByValuePar (sourceTable scopedSpecs ['a','b'] 8) [['a'],['b']]
      (sourceBody ⟨1,1,.eps,.eps⟩) 2=some (some 1) ∧
    evV (source scopedSpecs) ['a','b'] .callByValuePar (sourceTable scopedSpecs ['a','b'] 8) [['a'],['b']]
      (expanded scopedSpecs 0) 2=some (some 1) ∧
    evV (source scopedSpecs) ['a','b'] .callByValuePar (sourceTable scopedSpecs ['a','b'] 8) [['a'],['b']]
      (ExpressionContext.plug (.seq (.andP (.param 0)) (sourceBody ⟨9,3,.eps,.param 1⟩)) (frame ⟨1,1,.eps,.eps⟩))
      2=some (some 0) := by decide +kernel

def committed : List Spec := [⟨1,1,.chr 'c',MExp.failAlways⟩,⟨2,3,.eps,.lit ['a','a','b']⟩,⟨9,2,.eps,.eps⟩]
def distributed : MExp := .alt
  (.seq (.call 2 [expression (.param 0) 3]) (.chr 'c'))
  (.seq (.seq (.param 0) (.lit ['a','a','b'])) (.chr 'c'))
theorem committed_choice : sourceRun committed (.call 0 [.lit ['a']]) ['a','a','a','b','c'] 8=some none ∧
    normalizedRun committed (.call 0 [.lit ['a']]) ['a','a','a','b','c'] 8=some none ∧
    evV (source committed) ['a','a','a','b','c'] .callByValuePar (sourceTable committed ['a','a','a','b','c'] 8)
      [['a']] distributed 5=some (some 0) := by decide +kernel

end Shallot.MacroPeg.CBV.ForwardingHeadExamples
