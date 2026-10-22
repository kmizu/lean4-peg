import Shallot.Peg.Dpda.Moves

/-!
# Completeness for the pop nonterminals

If the automaton pops `Z` (in state `q`, on input `x`) after `n` moves, ending in state `p` with `x'` left, then
`P q Z p` succeeds on `x` leaving `x'`, and `P q Z r` fails for every other state `r`. By induction on `n`: the choice
over the states in which the first pushed symbol is popped has exactly one succeeding alternative (determinism).
-/

namespace Shallot.Dpda

open Shallot

namespace DPDA

variable (M : DPDA)

theorem run_nil_stack {m p r₁ : Nat} {x x' : List Char} (h : M.run m (p, x, []) = some (r₁, x', [])) :
    p = r₁ ∧ x = x' := by
  cases m with
  | zero => simp [run] at h; exact ⟨h.1, h.2⟩
  | succ m => rw [M.run_succ_of_step_none (M.step_nil p x)] at h; cases h

/-- A run that empties the stack `X :: γ` first empties `X`, then continues on `γ`. -/
theorem run_pop_split {n q X r₁ : Nat} {x x' : List Char} {γ : List Nat}
    (h : M.run n (q, x, X :: γ) = some (r₁, x', [])) :
    ∃ k s x'', 0 < k ∧ k ≤ n ∧ M.run k (q, x, [X]) = some (s, x'', []) ∧
      M.run (n - k) (s, x'', γ) = some (r₁, x', []) := by
  rcases M.run_split (ξ := [X]) (β := γ) (by simp) h with ⟨c', -, hc, hne⟩ | ⟨k, hk, hk0, s, x'', hr, hr'⟩
  · exfalso
    have : c'.2.2 ++ γ = [] := by simpa [below] using congrArg (fun c : Config => c.2.2) hc.symm
    exact hne (List.append_eq_nil_iff.mp this).1
  · exact ⟨k, s, x'', hk0, hk, hr, hr'⟩

/-- The statement for runs of length `n`. -/
def Pspec (n : Nat) : Prop :=
  ∀ q Z p x x', q < M.nQ → Z < M.nG → M.run n (q, x, [Z]) = some (p, x', []) →
    ∀ r, r < M.nQ →
      (r = p → ∃ t, Derives M.grammar (.nt (M.pidx q Z r)) x (.ok t x')) ∧
        (r ≠ p → Derives M.grammar (.nt (M.pidx q Z r)) x .fail)

theorem popS_spec (B : Nat) (hIH : ∀ n ≤ B, M.Pspec n) :
    ∀ (γ : List Nat) (p : Nat) (x x' : List Char) (r₁ m : Nat), m ≤ B → p < M.nQ → (∀ X ∈ γ, X < M.nG) →
      M.run m (p, x, γ) = some (r₁, x', []) → ∀ r, r < M.nQ →
        (r = r₁ → ∃ t, Derives M.grammar (M.popS r M.pidx p γ) x (.ok t x')) ∧
          (r ≠ r₁ → Derives M.grammar (M.popS r M.pidx p γ) x .fail)
  | [], p, x, x', r₁, m, _, _, _, h, r, _ => by
    obtain ⟨rfl, rfl⟩ := M.run_nil_stack h
    refine ⟨fun hr => ?_, fun hr => ?_⟩
    · subst hr; simp only [popS, if_true]; exact ⟨_, Derives.eps _⟩
    · simp only [popS, if_neg (Ne.symm hr)]; exact derives_failE _ _
  | X :: γ, p, x, x', r₁, m, hm, hp, hγ, h, r, hr => by
    obtain ⟨k, s, x'', hk0, hkm, hrk, hrest⟩ := M.run_pop_split h
    have hs : s < M.nQ := M.run_state_lt hk0 hrk
    have hP := hIH k (by omega) p X s x x'' hp (hγ X List.mem_cons_self) hrk
    have hγ' := popS_spec B hIH γ s x'' x' r₁ (m - k) (by omega) hs
      (fun Y hY => hγ Y (List.mem_cons_of_mem _ hY)) hrest r hr
    simp only [popS]
    constructor
    · intro hrr
      obtain ⟨t, ht⟩ := (hP s hs).1 rfl
      obtain ⟨t', ht'⟩ := hγ'.1 hrr
      apply altList_ok
      · intro e he
        obtain ⟨q₁, hq₁, rfl⟩ := List.mem_map.mp he
        by_cases hqs : q₁ = s
        · subst hqs
          exact Or.inr ⟨_, Derives.seqOk _ _ _ x'' x' _ _ ht ht'⟩
        · exact Or.inl (Derives.seqFail₁ _ _ _ ((hP q₁ (List.mem_range.mp hq₁)).2 hqs))
      · exact ⟨_, List.mem_map.mpr ⟨s, List.mem_range.mpr hs, rfl⟩, _,
          Derives.seqOk _ _ _ x'' x' _ _ ht ht'⟩
    · intro hrr
      apply altList_fail
      intro e he
      obtain ⟨q₁, hq₁, rfl⟩ := List.mem_map.mp he
      have hq₁' := List.mem_range.mp hq₁
      by_cases hqs : q₁ = s
      · subst hqs
        obtain ⟨t, ht⟩ := (hP q₁ hq₁').1 rfl
        exact Derives.seqFail₂ _ _ _ x'' _ ht (hγ'.2 hrr)
      · exact Derives.seqFail₁ _ _ _ ((hP q₁ hq₁').2 hqs)

theorem pop_spec_le : ∀ B n, n ≤ B → M.Pspec n
  | 0, n, hn => by
    have : n = 0 := by omega
    subst this
    intro q Z p x x' _ _ h
    simp [run] at h
  | B + 1, n, hn => by
    by_cases hle : n ≤ B
    · exact pop_spec_le B n hle
    · have hn' : n = B + 1 := by omega
      subst hn'
      intro q Z p x x' hq hZ hrun r hr
      cases hs : M.step (q, x, [Z]) with
      | none => rw [M.run_succ_of_step_none hs] at hrun; cases hrun
      | some c1 =>
        obtain ⟨p1, x₁, γ⟩ := c1
        rw [M.run_succ_of_step hs] at hrun
        have hlt := M.step_single_lt hs
        have hpS := M.popS_spec B (fun k hk => pop_spec_le B k hk) γ p1 x₁ x' p B (Nat.le_refl _) hlt.1 hlt.2 hrun r hr
        have hrule := M.ruleAt_pop hq hZ hr
        constructor
        · intro hrp
          obtain ⟨t, ht⟩ := hpS.1 hrp
          obtain ⟨t', ht'⟩ := M.moves_ok (cont := fun p γ => M.popS r M.pidx p γ) hs ht
          exact M.nt_ok hrule ht'
        · intro hrp
          exact M.nt_fail hrule (M.moves_fail (cont := fun p γ => M.popS r M.pidx p γ) hs (hpS.2 hrp))

theorem pop_spec (n : Nat) : M.Pspec n := M.pop_spec_le n n (Nat.le_refl _)

end DPDA

end Shallot.Dpda
