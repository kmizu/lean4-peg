import Complexity.NSpace

/-!
# Reasoning kit for stack machines over numbers

Programs are verified with time bounds only (the space bound follows, `nexec_space`), so the invariant is `True`.

* `NRuns p S S' T`: from `S` the program continues in state `S'` within `T` steps;
* `NHalts p S b S' T`: it stops with answer `b` in state `S'` within `T` steps;
* rules for the primitives, sequences, branches, and loops through a family of states (`nruns_family`).
-/

namespace Complexity

variable {K : Nat}

abbrev NTrue : Lists K → Prop := fun _ => True

def NRuns (p : NProg K) (S S' : Lists K) (T : Nat) : Prop := ∃ t, t ≤ T ∧ NExec NTrue p S t (.cont S')

def NHalts (p : NProg K) (S : Lists K) (b : Bool) (S' : Lists K) (T : Nat) : Prop :=
  ∃ t, t ≤ T ∧ NExec NTrue p S t (.stop b S')

theorem NRuns.mono {p : NProg K} {S S' : Lists K} {T T' : Nat} (h : NRuns p S S' T) (hT : T ≤ T') : NRuns p S S' T' :=
  let ⟨t, ht, hx⟩ := h; ⟨t, Nat.le_trans ht hT, hx⟩

theorem NHalts.mono {p : NProg K} {S S' : Lists K} {b : Bool} {T T' : Nat} (h : NHalts p S b S' T) (hT : T ≤ T') :
    NHalts p S b S' T' :=
  let ⟨t, ht, hx⟩ := h; ⟨t, Nat.le_trans ht hT, hx⟩

theorem NRuns.seq {p q : NProg K} {S S₁ S₂ : Lists K} {T₁ T₂ : Nat} (h₁ : NRuns p S S₁ T₁) (h₂ : NRuns q S₁ S₂ T₂) :
    NRuns (.seq p q) S S₂ (T₁ + T₂) :=
  let ⟨t₁, ht₁, x₁⟩ := h₁; let ⟨t₂, ht₂, x₂⟩ := h₂; ⟨t₁ + t₂, Nat.add_le_add ht₁ ht₂, .seqC x₁ x₂⟩

theorem NRuns.seqH {p q : NProg K} {S S₁ S₂ : Lists K} {b : Bool} {T₁ T₂ : Nat} (h₁ : NRuns p S S₁ T₁)
    (h₂ : NHalts q S₁ b S₂ T₂) : NHalts (.seq p q) S b S₂ (T₁ + T₂) :=
  let ⟨t₁, ht₁, x₁⟩ := h₁; let ⟨t₂, ht₂, x₂⟩ := h₂; ⟨t₁ + t₂, Nat.add_le_add ht₁ ht₂, .seqC x₁ x₂⟩

theorem NHalts.seq {p q : NProg K} {S S₁ : Lists K} {b : Bool} {T : Nat} (h : NHalts p S b S₁ T) :
    NHalts (.seq p q) S b S₁ T :=
  let ⟨t, ht, x⟩ := h; ⟨t, ht, .seqS x⟩

theorem nruns_prim (a : NPrim K) (S : Lists K) : NRuns (.prim a) S (a.apply S) 1 := ⟨1, Nat.le_refl _, .prim trivial trivial⟩

theorem nhalts_halt (b : Bool) (S : Lists K) : NHalts (.halt b) S b S 1 := ⟨1, Nat.le_refl _, .halt trivial⟩

theorem NRuns.iteT {i : Fin K} {c : NTest} {p q : NProg K} {S S' : Lists K} {T : Nat} (hc : c.eval (S i) = true)
    (h : NRuns p S S' T) : NRuns (.ite i c p q) S S' (T + 1) :=
  let ⟨t, ht, x⟩ := h; ⟨t + 1, by omega, .iteT trivial hc x⟩

theorem NRuns.iteF {i : Fin K} {c : NTest} {p q : NProg K} {S S' : Lists K} {T : Nat} (hc : c.eval (S i) = false)
    (h : NRuns q S S' T) : NRuns (.ite i c p q) S S' (T + 1) :=
  let ⟨t, ht, x⟩ := h; ⟨t + 1, by omega, .iteF trivial hc x⟩

theorem NHalts.iteT {i : Fin K} {c : NTest} {p q : NProg K} {S S' : Lists K} {b : Bool} {T : Nat}
    (hc : c.eval (S i) = true) (h : NHalts p S b S' T) : NHalts (.ite i c p q) S b S' (T + 1) :=
  let ⟨t, ht, x⟩ := h; ⟨t + 1, by omega, .iteT trivial hc x⟩

theorem NHalts.iteF {i : Fin K} {c : NTest} {p q : NProg K} {S S' : Lists K} {b : Bool} {T : Nat}
    (hc : c.eval (S i) = false) (h : NHalts q S b S' T) : NHalts (.ite i c p q) S b S' (T + 1) :=
  let ⟨t, ht, x⟩ := h; ⟨t + 1, by omega, .iteF trivial hc x⟩

/-- **A loop through a family of states**: the test holds at `F m` for `m < n` and fails at `F n`, and the body takes
`F m` to `F (m + 1)` within `T` steps. -/
theorem nruns_family {i : Fin K} {c : NTest} {p : NProg K} (F : Nat → Lists K) (n T : Nat)
    (htest : ∀ m, m < n → c.eval (F m i) = true) (hstop : c.eval (F n i) = false)
    (hbody : ∀ m, m < n → NRuns p (F m) (F (m + 1)) T) :
    ∀ r m, m + r = n → NRuns (.loop i c p) (F m) (F n) (r * (T + 1) + 1)
  | 0, m, h => by
    obtain rfl : m = n := by omega
    exact ⟨1, by simp, .loopF trivial hstop⟩
  | r + 1, m, h => by
    obtain ⟨t₁, ht₁, x₁⟩ := hbody m (by omega)
    obtain ⟨t₂, ht₂, x₂⟩ := nruns_family F n T htest hstop hbody r (m + 1) (by omega)
    refine ⟨t₁ + 1 + t₂, ?_, .loopC trivial (htest m (by omega)) x₁ x₂⟩
    rw [Nat.succ_mul]; omega

theorem nruns_family_const {i : Fin K} {c : NTest} {p : NProg K} (F : Nat → Lists K) (n T : Nat)
    (htest : ∀ m, m < n → c.eval (F m i) = true) (hstop : c.eval (F n i) = false)
    (hbody : ∀ m, m < n → NRuns p (F m) (F (m + 1)) T) :
    NRuns (.loop i c p) (F 0) (F n) (n * (T + 1) + 1) :=
  nruns_family F n T htest hstop hbody n 0 (by omega)

/-! ## Updating stacks -/

theorem Lists.set_comm {L : Lists K} {i j : Fin K} (h : i ≠ j) (a b : List Nat) :
    (L.set i a).set j b = (L.set j b).set i a := by
  funext x
  simp only [Lists.set]
  by_cases hi : x = i
  · subst hi; simp [h]
  · by_cases hj : x = j
    · subst hj; simp [hi]
    · simp [hi, hj]

theorem Lists.ext_at {L L' : Lists K} (h : ∀ x, L x = L' x) : L = L' := funext h

/-- Equalities between stacks updated at a few places: compare at every index. -/
macro "lists_eq" : tactic =>
  `(tactic| (funext x; simp only [Lists.set]; repeat' split
             all_goals (try subst_vars)
             all_goals (try simp_all)
             all_goals (try omega)))

/-- The value of stacks updated at a few places, at one index. -/
macro "lists_at" : tactic =>
  `(tactic| (simp only [Lists.set]; repeat' split
             all_goals (try subst_vars)
             all_goals (try simp_all)
             all_goals (try omega)))

end Complexity
