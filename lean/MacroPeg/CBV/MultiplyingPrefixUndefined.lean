import MacroPeg.CBV.MultiplyingPrefixExamples

namespace Shallot.MacroPeg.CBV.MultiplyingPrefixExamples
open MultiplyingPrefixCompiler
open RepeatedWordArguments (copies expression)

def nullable (factor : Nat) : List Spec := [⟨0,factor,.eps,.eps⟩]
theorem nullable_valid (factor : Nat) (hf : 2≤factor) : Valid (nullable factor) := by
  simp [Valid,nullable,MExp.FirstOrder,hf]

theorem unit_factor_rejected : ¬Valid (nullable 1) := by
  intro h
  have hh : 2≤1 := (h ⟨0,1,.eps,.eps⟩ (by simp [nullable])).1
  omega
theorem unit_factor_counterexample : sourceRun (nullable 1) entry ['a','b'] 8=none ∧
    targetRun (nullable 1) entry ['a','b'] 8=some (some 0) := by decide +kernel

theorem empty_row (factor : Nat) (x : List Char) (k p : Nat) (hp : p≤x.length) :
    valAt (sourceTable (nullable factor) x k 0 [[]]) p=none := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hr : ruleAtM (source (nullable factor)).rules 0=some ⟨1,sourceBody ⟨0,factor,.eps,.eps⟩⟩ := rfl
    rw [valAt_tblV_succ hr [[]] hp]
    have ha : evV (source (nullable factor)) x .callByValuePar (sourceTable (nullable factor) x k) [[]]
        (expression (.param 0) factor) p=some (some p) := by
      rw [WordArguments.word_eval _ _ _ _ _ _ (RepeatedWordArguments.expression_word (.param 0) True.intro factor),
        RepeatedWordArguments.expression_value _ (.param 0) [] rfl]
      simp only [RepeatedWordArguments.copies_nil,WordArguments.literal,evV,Shallot.stripPrefix?,length_sfx x hp]
    have hc : evV (source (nullable factor)) x .callByValuePar (sourceTable (nullable factor) x k) [[]]
        (.call 0 [expression (.param 0) factor]) p=none := by
      rw [evV_call_par hr rfl (by decide)]
      simpa only [evParArgs,ha,pre,Nat.sub_self,List.take_zero] using ih
    exact evV_alt_none (evV_seq_none hc)

theorem empty_source (factor : Nat) (x : List Char) (k : Nat) :
    sourceRun (nullable factor) (.call 0 [.lit []]) x k=none := by
  have hr : ruleAtM (source (nullable factor)).rules 0=some ⟨1,sourceBody ⟨0,factor,.eps,.eps⟩⟩ := rfl
  unfold sourceRun
  rw [evV_call_par hr rfl (by decide)]
  simpa only [evParArgs,evV,Shallot.stripPrefix?,length_sfx x (Nat.le_refl _),
    pre,Nat.sub_self,List.take_zero] using empty_row factor x k x.length (Nat.le_refl _)

theorem empty_target (factor : Nat) (hf : 2≤factor) (x : List Char) (k : Nat) :
    targetRun (nullable factor) (.call 0 [.lit []]) x k=none := by
  unfold targetRun
  rw [← MultiplyingPrefixCorrespondence.evaluator_eq (nullable factor) (nullable_valid factor hf) x k []
    (.call 0 [.lit []]) (by trivial) x.length (Nat.le_refl _)]
  exact empty_source factor x k

end Shallot.MacroPeg.CBV.MultiplyingPrefixExamples
