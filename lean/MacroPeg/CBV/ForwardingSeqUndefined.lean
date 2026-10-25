import MacroPeg.CBV.ForwardingSeqExamples

namespace Shallot.MacroPeg.CBV.ForwardingSeqExamples
open ForwardingSeqCompiler
open MultiplyingPrefixCompiler (Spec render)

def unitCycle : List Spec := [⟨0,1,.eps,.eps⟩]
theorem unit_cycle_valid : Valid unitCycle := by simp [Valid,unitCycle,MExp.FirstOrder]
theorem unit_cycle_closed : ForwardingPrefixCycles.check unitCycle [0]=true := by decide +kernel

theorem empty_source (x : List Char) (k : Nat) :
    ForwardingHeadExamples.sourceRun unitCycle (.call 0 [.lit []]) x k=none := by
  have hr : ruleAtM (MultiplyingPrefixCompiler.source unitCycle).rules 0=
      some ⟨1,MultiplyingPrefixCompiler.sourceBody ⟨0,1,.eps,.eps⟩⟩ := rfl
  unfold ForwardingHeadExamples.sourceRun
  rw [evV_call_par hr rfl (by decide)]
  have hrow := ForwardingPrefixCycles.rows_none unitCycle [0]
    ((ForwardingPrefixCycles.checked_iff unitCycle [0]).mp unit_cycle_closed) x k 0 (by simp)
    [] x.length x.length ⟨Nat.le_refl _,Nat.le_refl _,rfl⟩
  simpa only [evParArgs,evV,Shallot.stripPrefix?,length_sfx x (Nat.le_refl _),pre,
    Nat.sub_self,List.take_zero] using hrow

theorem empty_target (x : List Char) (k : Nat) : run unitCycle (.call 0 [.lit []]) x k=none :=
  (ForwardingSeqCorrespondence.undefined_iff unitCycle unit_cycle_valid x [] (.call 0 [.lit []])
    (by trivial) x.length (Nat.le_refl _)).mp (empty_source x) k

end Shallot.MacroPeg.CBV.ForwardingSeqExamples
