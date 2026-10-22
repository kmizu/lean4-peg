import Shallot.Peg.Dpda.Defs

/-!
# Runs of a DPDA on part of the stack

A move only looks at the top of the stack, so a run on a stack `ξ` is also a run on `ξ ++ β` until `ξ` is used up
(`run_append`). Conversely a run on `ξ ++ β` either stays above `β` or first empties `ξ` and then continues on `β`
(`run_split`).
-/

namespace Shallot.Dpda.DPDA

variable (M : DPDA)

theorem run_zero (c : Config) : M.run 0 c = some c := rfl

theorem run_succ_of_step {c c' : Config} (h : M.step c = some c') (n : Nat) : M.run (n + 1) c = M.run n c' := by
  simp [run, h]

theorem run_succ_of_step_none {c : Config} (h : M.step c = none) (n : Nat) : M.run (n + 1) c = none := by
  simp [run, h]

theorem run_add (m n : Nat) (c : Config) : M.run (m + n) c = (M.run m c).bind (M.run n) := by
  induction m generalizing c with
  | zero => simp [run]
  | succ m ih =>
    rw [Nat.succ_add]
    cases h : M.step c with
    | none => rw [run_succ_of_step_none M h, run_succ_of_step_none M h]; rfl
    | some c' => rw [run_succ_of_step M h, run_succ_of_step M h, ih]

theorem step_nil (q : Nat) (x : List Char) : M.step (q, x, []) = none := rfl

/-- Append `β` below the stack of a configuration. -/
def below (β : List Nat) : Config → Config := fun c => (c.1, c.2.1, c.2.2 ++ β)

theorem step_append {q : Nat} {x : List Char} {ξ : List Nat} (hξ : ξ ≠ []) (β : List Nat) :
    M.step (q, x, ξ ++ β) = (M.step (q, x, ξ)).map (below β) := by
  match ξ, hξ with
  | Z :: ξ', _ =>
    rcases h1 : M.δ q none Z with _ | ⟨p, γ⟩
    · cases x with
      | nil => simp [step, h1, below]
      | cons a x' =>
        rcases h2 : M.δ q (some a) Z with _ | ⟨p, γ⟩
        · simp [step, h1, h2, below]
        · simp [step, h1, h2, below, List.append_assoc]
    · simp [step, h1, below, List.append_assoc]

theorem run_append {n q q' : Nat} {x x' : List Char} {ξ ξ' : List Nat}
    (h : M.run n (q, x, ξ) = some (q', x', ξ')) (β : List Nat) :
    M.run n (q, x, ξ ++ β) = some (q', x', ξ' ++ β) := by
  induction n generalizing q x ξ with
  | zero => simp [run] at h ⊢; obtain ⟨rfl, rfl, rfl⟩ := h; exact ⟨rfl, rfl, rfl⟩
  | succ n ih =>
    cases hs : M.step (q, x, ξ) with
    | none => rw [run_succ_of_step_none M hs] at h; cases h
    | some c1 =>
      have hξ : ξ ≠ [] := by rintro rfl; cases hs
      rw [run_succ_of_step M hs] at h
      obtain ⟨p, x1, ξ1⟩ := c1
      have hs' : M.step (q, x, ξ ++ β) = some (p, x1, ξ1 ++ β) := by
        rw [step_append M hξ, hs]; rfl
      rw [run_succ_of_step M hs']
      exact ih h

/-- **Splitting a run on `ξ ++ β`**: either it is a run on `ξ` with `β` below, or `ξ` is emptied after `k` moves and
the remaining `n - k` moves run on `β`. -/
theorem run_split {n q : Nat} {x : List Char} {ξ β : List Nat} {c : Config} (hξ : ξ ≠ [])
    (h : M.run n (q, x, ξ ++ β) = some c) :
    (∃ c', M.run n (q, x, ξ) = some c' ∧ c = below β c' ∧ c'.2.2 ≠ []) ∨
      (∃ k, k ≤ n ∧ 0 < k ∧ ∃ s x', M.run k (q, x, ξ) = some (s, x', []) ∧ M.run (n - k) (s, x', β) = some c) := by
  induction n generalizing q x ξ with
  | zero =>
    simp [run] at h
    exact Or.inl ⟨(q, x, ξ), rfl, by rw [← h]; rfl, hξ⟩
  | succ n ih =>
    cases hs : M.step (q, x, ξ) with
    | none =>
      have : M.step (q, x, ξ ++ β) = none := by rw [step_append M hξ, hs]; rfl
      rw [run_succ_of_step_none M this] at h; cases h
    | some c1 =>
      obtain ⟨p, x1, ξ1⟩ := c1
      have hs' : M.step (q, x, ξ ++ β) = some (p, x1, ξ1 ++ β) := by rw [step_append M hξ, hs]; rfl
      rw [run_succ_of_step M hs'] at h
      by_cases h1 : ξ1 = []
      · subst h1
        refine Or.inr ⟨1, by omega, by omega, p, x1, ?_, ?_⟩
        · rw [run_succ_of_step M hs]; rfl
        · simpa using h
      · rcases ih h1 h with ⟨c', hc', hc, hne⟩ | ⟨k, hk, hk0, s, x', hr, hr'⟩
        · exact Or.inl ⟨c', by rw [run_succ_of_step M hs]; exact hc', hc, hne⟩
        · refine Or.inr ⟨k + 1, by omega, by omega, s, x', ?_, ?_⟩
          · rw [run_succ_of_step M hs]; exact hr
          · rw [show n + 1 - (k + 1) = n - k by omega]; exact hr'

/-- A configuration with a non-empty stack is stuck below `β` iff it is stuck. -/
theorem step_append_none {q : Nat} {x : List Char} {ξ : List Nat} (hξ : ξ ≠ []) (β : List Nat) :
    M.step (q, x, ξ ++ β) = none ↔ M.step (q, x, ξ) = none := by
  rw [step_append M hξ]; cases M.step (q, x, ξ) <;> simp

/-- Moves end in states below `nQ`. -/
theorem step_state_lt {c : Config} {p : Nat} {x : List Char} {γ : List Nat} (h : M.step c = some (p, x, γ)) :
    p < M.nQ := by
  obtain ⟨q, y, ξ⟩ := c
  match ξ, h with
  | Z :: β, h =>
    simp only [step] at h
    cases hε : M.δ q none Z with
    | some pγ =>
      rw [hε] at h; obtain ⟨p', γ'⟩ := pγ; simp at h; obtain ⟨rfl, -, -⟩ := h
      exact (M.cod _ _ _ _ _ hε).1
    | none =>
      rw [hε] at h
      cases y with
      | nil => cases h
      | cons a y' =>
        simp only at h
        cases ha : M.δ q (some a) Z with
        | none => rw [ha] at h; cases h
        | some pγ =>
          rw [ha] at h; obtain ⟨p', γ'⟩ := pγ; simp at h; obtain ⟨rfl, -, -⟩ := h
          exact (M.cod _ _ _ _ _ ha).1

theorem run_state_lt {k : Nat} (hk : 0 < k) {c : Config} {p : Nat} {x : List Char} {γ : List Nat}
    (h : M.run k c = some (p, x, γ)) : p < M.nQ := by
  induction k generalizing c with
  | zero => omega
  | succ k ih =>
    cases hs : M.step c with
    | none => rw [run_succ_of_step_none M hs] at h; cases h
    | some c1 =>
      rw [run_succ_of_step M hs] at h
      cases k with
      | zero => simp [run] at h; subst h; exact M.step_state_lt hs
      | succ k => exact ih (by omega) h

end Shallot.Dpda.DPDA
