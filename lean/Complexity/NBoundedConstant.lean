import Complexity.NBoundedTransfer

/-! Push a constant into a dedicated empty register without increasing the
space capacity used to annotate the surrounding numeric computation. -/
namespace Complexity.NBoundedConstant
open NBoundedTransfer
variable {K B : Nat}

theorem push_runs (i : Fin K) (S : Lists K) (hi : S i = []) (hS : NFits B S) :
    ∀ c : Nat, c+3 ≤ B → FitsRuns B (npushC i c) S (S.set i [c]) (c+1)
  | 0,hB => by
    have hF := replace hS i [0] (by simpa [encS,encN] using hB)
    have he : (NPrim.pushZ i).apply S = S.set i [0] := by simp [NPrim.apply,hi]
    refine ⟨1,by omega,?_⟩
    rw [← he]
    exact .prim hS (by rwa [he])
  | c+1,hB => by
    obtain ⟨t,ht,he⟩ := push_runs i S hi hS c (by omega)
    have hA := replace hS i [c] (by simp [encS,encN]; omega)
    have hF := replace hS i [c+1] (by simpa [encS,encN] using hB)
    have hinc : (NPrim.inc i).apply (S.set i [c]) = S.set i [c+1] := by
      simp [NPrim.apply,mapTop,Lists.set_set_u]
    have hh : NExec (NFits B) (.prim (.inc i)) (S.set i [c]) 1 (.cont (S.set i [c+1])) := by
      rw [← hinc]
      exact .prim hA (by rwa [hinc])
    exact ⟨t+1,by omega,.seqC he hh⟩

end Complexity.NBoundedConstant
