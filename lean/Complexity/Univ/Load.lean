import Complexity.NMacros

/-!
# Pushing a constant list

`nloadP i l` pushes the numbers of `l` in order onto stack `i` (`nruns_load`), in `l.length + l.sum` steps.
-/

namespace Complexity

variable {K : Nat}

/-- Push the numbers of `l`, first to last. -/
def nloadP (i : Fin K) : List Nat → NProg K
  | [] => nskip i
  | c :: l => .seq (npushC i c) (nloadP i l)

theorem nruns_load (i : Fin K) : ∀ (l : List Nat) (S : Lists K),
    NRuns (nloadP i l) S (S.set i (S i ++ l)) (l.length + l.sum + 2)
  | [], S => by
    have := nruns_skip i S
    rw [List.append_nil, Lists.set_get_self]
    exact this.mono (by simp)
  | c :: l, S => by
    have h₁ := nruns_pushC i S c
    have h₂ := nruns_load i l (S.set i (S i ++ [c]))
    simp only [Lists.set_same, Lists.set_set_u, List.append_assoc, List.singleton_append] at h₂
    exact (h₁.seq h₂).mono (by simp; omega)

end Complexity
