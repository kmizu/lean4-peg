import MacroPeg.CBV.DoublingPrefixExamples

namespace Shallot.MacroPeg.CBV.DoublingPrefixExamples
open DoublingPrefixCompiler

/-- Empty doubled arguments recurse at the same position forever; the
fallback is never selected by a finite failure. -/
theorem empty_row (x : List Char) (k p : Nat) (hp : p≤x.length) :
    valAt (sourceTable specs x k 0 [[]]) p=none := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hr : ruleAtM (source specs).rules 0=some ⟨1,sourceBody ⟨0,.eps,.eps⟩⟩ := rfl
    rw [valAt_tblV_succ hr [[]] hp]
    have hc : evV (source specs) x .callByValuePar (sourceTable specs x k) [[]]
        (.call 0 [.seq (.param 0) (.param 0)]) p=none := by
      rw [evV_call_par hr rfl (by decide)]
      simpa only [evParArgs,evV,List.getElem?_cons_zero,Shallot.stripPrefix?,length_sfx x hp,
        pre,Nat.sub_self,List.take_zero] using ih
    exact evV_alt_none (evV_seq_none hc)

theorem empty_source (x : List Char) (k : Nat) : sourceRun specs (.call 0 [.lit []]) x k=none := by
  have hr : ruleAtM (source specs).rules 0=some ⟨1,sourceBody ⟨0,.eps,.eps⟩⟩ := rfl
  unfold sourceRun
  rw [evV_call_par hr rfl (by decide)]
  simpa only [evParArgs,evV,Shallot.stripPrefix?,length_sfx x (Nat.le_refl _),
    pre,Nat.sub_self,List.take_zero] using empty_row x k x.length (Nat.le_refl _)

theorem empty_target (x : List Char) (k : Nat) : targetRun specs (.call 0 [.lit []]) x k=none := by
  unfold targetRun
  rw [← DoublingPrefixCorrespondence.evaluator_eq specs valid x k [] (.call 0 [.lit []])
    (by trivial) x.length (Nat.le_refl _)]
  exact empty_source x k

end Shallot.MacroPeg.CBV.DoublingPrefixExamples
