import MacroPeg.CBV.ForwardingSeqCorrespondence
import MacroPeg.CBV.ForwardingHeadExamples

namespace Shallot.MacroPeg.CBV.ForwardingSeqExamples
open ForwardingSeqCompiler
open MultiplyingPrefixCompiler (Spec arity view modes address render prefixCall origin_mode)
open RepeatedWordArguments (copies expression)
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def run (rs : List Spec) (e : MExp) (x : List Char) (k : Nat) :=
  evV (target rs) x .callByValueSeq (targetTable rs x k) [] (render rs.length e) x.length
abbrev entry := ForwardingHeadExamples.entry
abbrev chain := ForwardingHeadExamples.chain
abbrev returning := ForwardingHeadExamples.returning
abbrev committed := ForwardingHeadExamples.committed
abbrev cycles := ForwardingCycleExamples.specs

theorem chain_valid : Valid chain := by simp [Valid,chain,ForwardingHeadExamples.chain,MExp.FirstOrder]
theorem returning_valid : Valid returning := by simp [Valid,returning,ForwardingHeadExamples.returning,MExp.FirstOrder]
theorem cycles_valid : Valid cycles := by
  simp [Valid,cycles,ForwardingCycleExamples.specs,MExp.FirstOrder,MExp.FirstOrderArgs]
theorem committed_valid : Valid committed := by simp [Valid,committed,ForwardingHeadExamples.committed,MExp.FirstOrder,MExp.failAlways]

theorem chain_target : ∀ n∈[1,3,9,27], run chain entry (copies ['a','b'] n) 8=some (some 0) := by decide +kernel
theorem returning_target : ∀ n∈[1,3,9], run returning entry (copies ['a','b'] n++['!','?']) 8=some (some 0) := by decide +kernel
theorem closed_cycle : ∀ k∈[0,1,2,4,8], run cycles entry ['a','b'] k=none ∧
    run cycles (.call 0 [.lit []]) ['x'] k=none := by decide +kernel
theorem failed_argument : run cycles entry ['a','x'] 8=some none := by decide +kernel
theorem missing_callee : run cycles (.call 4 [.lit ['a','b']]) ['a','b','!'] 8=some (some 0) := by decide +kernel
theorem committed_target : run committed (.call 0 [.lit ['a']]) ['a','a','a','b','c'] 8=some none := by decide +kernel
theorem clock_difference : ForwardingHeadExamples.sourceRun chain entry ['a','b'] 1=none ∧
    run chain entry ['a','b'] 1=some (some 0) := by decide +kernel

theorem original_language (x : List Char) :
    SObs (MultiplyingPrefixCompiler.source returning) .callByValuePar entry x (some []) ↔
      SObs (target returning) .callByValueSeq (render returning.length entry) x (some []) :=
  ForwardingSeqCorrespondence.observations_iff returning returning_valid entry (by trivial) x (some [])

/-- An actual callback captures c* after returning from a tripled child;
the parent's ab remains available after that fresh argument call. -/
def fresh : List Spec := [
  ⟨1,1,.seq (.lit ['!']) (.seq (.call 2 [.star (.chr 'c')]) (.param 0)),.eps⟩,
  ⟨2,3,.param 0,.eps⟩,
  ⟨9,2,.eps,.eps⟩]
theorem fresh_valid : Valid fresh := by simp [Valid,fresh,MExp.FirstOrder,MExp.FirstOrderArgs]
theorem fresh_source : ∀ n∈[0,1,4], ForwardingHeadExamples.sourceRun fresh entry
    (copies ['a','b'] 4++['!']++List.replicate n 'c'++['a','b']) 8=some (some 0) := by decide +kernel
theorem fresh_target : ∀ n∈[0,1,4], run fresh entry
    (copies ['a','b'] 4++['!']++List.replicate n 'c'++['a','b']) 8=some (some 0) := by decide +kernel

def privateParameters : List Spec := [
  ⟨1,3,.param 0,.eps⟩,
  ⟨2,1,.notP (.param 1),.lit ['X']⟩,
  ⟨9,2,.eps,.eps⟩]
theorem private_parameters_valid : Valid privateParameters := by simp [Valid,privateParameters,MExp.FirstOrder]
theorem private_parameters : ForwardingHeadExamples.sourceRun privateParameters entry (copies ['a','b'] 4) 8=some (some 0) ∧
    run privateParameters entry (copies ['a','b'] 4) 8=some (some 0) ∧
    evV (target privateParameters) (copies ['a','b'] 4) .callByValueSeq (targetTable privateParameters (copies ['a','b'] 4) 8)
      [['a','b'],['a','b']] (.notP (.param 1)) 2=some none ∧
    evV (target privateParameters) (copies ['a','b'] 4) .callByValueSeq (targetTable privateParameters (copies ['a','b'] 4) 8)
      [['a','b'],['a','b']] (rebound privateParameters 3 (.notP (.param 1))) 2=some (some 2) := by decide +kernel

/-- A zero-factor child can consume from before the parent's capture.
The positive-factor compiler must not silently admit that different case. -/
def zeroFactor : List Spec := [⟨1,0,.chr '!',.eps⟩,⟨9,2,.eps,.chr 'a'⟩]
theorem zero_factor_rejected : ¬Valid zeroFactor := by
  intro h
  have hh : 1≤0 := (h ⟨1,0,.chr '!',.eps⟩ (by simp [zeroFactor])).1
  omega
theorem zero_factor_counterexample : ForwardingHeadExamples.sourceRun zeroFactor (.call 0 [.lit ['a']]) ['a','!'] 8=some (some 0) ∧
    run zeroFactor (.call 0 [.lit ['a']]) ['a','!'] 8=some (some 1) := by decide +kernel

end Shallot.MacroPeg.CBV.ForwardingSeqExamples
