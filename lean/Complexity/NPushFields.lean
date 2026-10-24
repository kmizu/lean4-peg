import Complexity.NMacros

/-! Emit a fixed field sequence as concrete pushes, with a size-dependent bound. -/
namespace Complexity.NPushFields
variable {K : Nat}

def program (i scratch : Fin K) : List Nat → NProg K
  | [] => nskip scratch
  | v :: vs => .seq (npushC i v) (program i scratch vs)

theorem runs (i scratch : Fin K) (vs : List Nat) (S : Lists K) (M : Nat)
    (hb : ∀ v ∈ vs, v ≤ M) :
    NRuns (program i scratch vs) S (S.set i (S i ++ vs)) (vs.length * (M+1) + 2) := by
  induction vs generalizing S with
  | nil => simpa only [program,List.length_nil,Nat.zero_mul,Nat.zero_add,List.append_nil,Lists.set_get_self]
      using nruns_skip scratch S
  | cons v vs ih =>
    have hp := nruns_pushC i S v
    have hr := ih (S.set i (S i ++ [v])) (fun w hw => hb w (by simp [hw]))
    have he : (S.set i (S i ++ [v])).set i ((S.set i (S i ++ [v])) i ++ vs) =
        S.set i (S i ++ v :: vs) := by simp [Lists.set_set_u,List.append_assoc]
    rw [he] at hr
    exact (hp.seq hr).mono (by have hv := hb v (by simp); simp only [List.length_cons,Nat.add_mul,Nat.one_mul]; omega)
end Complexity.NPushFields
