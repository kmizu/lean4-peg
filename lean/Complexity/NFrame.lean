import Complexity.NKit

/-!
# Stacks a program does not touch

`p.touches k`: the program mentions stack `k`. A program that does not touch stack `k` runs the same with any
contents there, and leaves them as they are (`nexec_frame`, `NRuns.frame`, `NHalts.frame`).
-/

namespace Complexity

variable {K : Nat}

def NPrim.touches : NPrim K → Fin K → Bool
  | .pushZ i, k | .inc i, k | .dec i, k | .pop i, k => i == k
  | .dup i j _, k => i == k || j == k

def NProg.touches : NProg K → Fin K → Bool
  | .prim a, k => a.touches k
  | .halt _, _ => false
  | .seq p q, k => p.touches k || q.touches k
  | .ite i _ p q, k => i == k || p.touches k || q.touches k
  | .loop i _ p, k => i == k || p.touches k

/-- Put `v` on stack `k` of the final stacks. -/
def LOutcome.setAt (k : Fin K) (v : List Nat) : LOutcome K → LOutcome K
  | .cont S => .cont (S.set k v)
  | .stop b S => .stop b (S.set k v)

theorem set_ne_get {S : Lists K} {k i : Fin K} (v : List Nat) (h : (i == k) = false) : (S.set k v) i = S i := by
  simp only [beq_eq_false_iff_ne, ne_eq] at h
  simp [Lists.set, h]

theorem NPrim.apply_set {a : NPrim K} {k : Fin K} (h : a.touches k = false) (S : Lists K) (v : List Nat) :
    a.apply (S.set k v) = (a.apply S).set k v := by
  funext x
  cases a with
  | pushZ i | inc i | dec i | pop i =>
    simp only [NPrim.touches, beq_eq_false_iff_ne, ne_eq] at h
    simp only [NPrim.apply, Lists.set]
    by_cases hx : x = i
    · subst hx; simp [Ne.symm h, h]
    · by_cases hk : x = k <;> simp [hx, hk, h, Ne.symm h]
  | dup i j hij =>
    simp only [NPrim.touches, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h
    simp only [NPrim.apply, Lists.set]
    by_cases hx : x = j
    · subst hx; simp [h.1, h.2, Ne.symm h.2]
    · by_cases hk : x = k <;> simp [hx, hk, h.1, h.2, Ne.symm h.1, Ne.symm h.2]

/-- **A program runs the same whatever an untouched stack holds.** -/
theorem nexec_frame {p : NProg K} {k : Fin K} (h : p.touches k = false) (v : List Nat) {S : Lists K} {t : Nat}
    {o : LOutcome K} (x : NExec NTrue p S t o) : NExec NTrue p (S.set k v) t (o.setAt k v) := by
  induction x with
  | prim _ _ =>
    rename_i a S _ _
    have e := NPrim.apply_set (a := a) h S v
    simp only [LOutcome.setAt]; rw [← e]; exact .prim trivial trivial
  | halt _ => exact .halt trivial
  | seqC _ _ ih₁ ih₂ =>
    simp only [NProg.touches, Bool.or_eq_false_iff] at h
    exact .seqC (ih₁ h.1) (ih₂ h.2)
  | seqS _ ih =>
    simp only [NProg.touches, Bool.or_eq_false_iff] at h
    exact .seqS (ih h.1)
  | iteT _ hc _ ih =>
    simp only [NProg.touches, Bool.or_eq_false_iff] at h
    exact .iteT trivial (by rw [set_ne_get v h.1.1]; exact hc) (ih h.1.2)
  | iteF _ hc _ ih =>
    simp only [NProg.touches, Bool.or_eq_false_iff] at h
    exact .iteF trivial (by rw [set_ne_get v h.1.1]; exact hc) (ih h.2)
  | loopF _ hc =>
    simp only [NProg.touches, Bool.or_eq_false_iff] at h
    exact .loopF trivial (by rw [set_ne_get v h.1]; exact hc)
  | loopC _ hc _ _ ih₁ ih₂ =>
    have h' := h
    simp only [NProg.touches, Bool.or_eq_false_iff] at h'
    exact .loopC trivial (by rw [set_ne_get v h'.1]; exact hc) (ih₁ h'.2) (ih₂ h)
  | loopS _ hc _ ih =>
    simp only [NProg.touches, Bool.or_eq_false_iff] at h
    exact .loopS trivial (by rw [set_ne_get v h.1]; exact hc) (ih h.2)

theorem NRuns.frame {p : NProg K} {k : Fin K} (h : p.touches k = false) (v : List Nat) {S S' : Lists K} {T : Nat}
    (x : NRuns p S S' T) : NRuns p (S.set k v) (S'.set k v) T :=
  let ⟨t, ht, e⟩ := x; ⟨t, ht, nexec_frame h v e⟩

theorem NHalts.frame {p : NProg K} {k : Fin K} (h : p.touches k = false) (v : List Nat) {S S' : Lists K} {b : Bool}
    {T : Nat} (x : NHalts p S b S' T) : NHalts p (S.set k v) b (S'.set k v) T :=
  let ⟨t, ht, e⟩ := x; ⟨t, ht, nexec_frame h v e⟩

end Complexity
