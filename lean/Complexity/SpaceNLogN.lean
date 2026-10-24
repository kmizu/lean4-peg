import Complexity.TM

/-! Deterministic space O(n log(n+1)), with the standard binary input convention. -/
namespace Complexity

def SpaceNLogN (L : Lang) : Prop :=
  ∃ (k : Nat) (M : TM k) (C : Nat), M.Decides L ∧
    M.SpaceBounded (fun n => C*(n+1)*((n+1).log2+1))

theorem TM.SpaceBounded.mono {k : Nat} {M : TM k} {s t : Nat → Nat}
    (h : M.SpaceBounded s) (hst : ∀ n, s n ≤ t n) : M.SpaceBounded t := by
  intro w u i
  have hh := h w u i
  exact ⟨Nat.lt_of_lt_of_le hh.1 (hst w.length),fun j hj => hh.2 j (Nat.le_trans (hst w.length) hj)⟩

end Complexity
