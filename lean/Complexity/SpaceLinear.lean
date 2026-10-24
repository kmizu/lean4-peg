import Complexity.SpaceNLogN

/-! Deterministic linear space with the standard binary input convention. -/
namespace Complexity

def SpaceLinear (L : Lang) : Prop :=
  ∃ (k : Nat) (M : TM k) (C : Nat), M.Decides L ∧ M.SpaceBounded (fun n => C*(n+1))

theorem SpaceLinear.to_nlog {L : Lang} (h : SpaceLinear L) : SpaceNLogN L := by
  obtain ⟨k,M,C,hdec,hspace⟩ := h
  refine ⟨k,M,C,hdec,hspace.mono (fun n => ?_)⟩
  exact Nat.le_mul_of_pos_right _ (by omega)

end Complexity
