import Shallot.Peg.Dpda.Sound

/-!
# Derivations of `moves`

A move of the automaton on a single stack symbol, and how a derivation of the continuation lifts to a derivation of
`moves`. Because the automaton is deterministic, exactly one alternative of the choice can match.
-/

namespace Shallot.Dpda

open Shallot

namespace DPDA

variable (M : DPDA)

theorem step_single {q : Nat} {x : List Char} {Z p : Nat} {x₁ : List Char} {γ : List Nat}
    (hs : M.step (q, x, [Z]) = some (p, x₁, γ)) :
    (M.δ q none Z = some (p, γ) ∧ x₁ = x) ∨
      (M.δ q none Z = none ∧ ∃ a, x = a :: x₁ ∧ M.δ q (some a) Z = some (p, γ)) := by
  cases hε : M.δ q none Z with
  | some pγ =>
    obtain ⟨p', γ'⟩ := pγ
    simp [step, hε] at hs
    obtain ⟨rfl, rfl, rfl⟩ := hs
    exact Or.inl ⟨rfl, rfl⟩
  | none =>
    cases x with
    | nil => simp [step, hε] at hs
    | cons a x' =>
      cases ha : M.δ q (some a) Z with
      | none => simp [step, hε, ha] at hs
      | some pγ =>
        obtain ⟨p', γ'⟩ := pγ
        simp [step, hε, ha] at hs
        obtain ⟨rfl, rfl, rfl⟩ := hs
        exact Or.inr ⟨rfl, a, rfl, ha⟩

/-- The target state and pushed symbols of a move are in range. -/
theorem step_single_lt {q : Nat} {x : List Char} {Z p : Nat} {x₁ : List Char} {γ : List Nat}
    (hs : M.step (q, x, [Z]) = some (p, x₁, γ)) : p < M.nQ ∧ ∀ X ∈ γ, X < M.nG := by
  rcases M.step_single hs with ⟨hε, -⟩ | ⟨-, a, -, ha⟩
  · exact M.cod _ _ _ _ _ hε
  · exact M.cod _ _ _ _ _ ha

theorem moveAlt_ne {cont : Nat → List Nat → PExp} {q Z : Nat} {a a' : Char} {x₁ : List Char} (hpa : a' ≠ a) :
    Derives M.grammar (M.moveAlt cont q Z a') (a :: x₁) .fail := by
  unfold moveAlt
  cases hδ : M.δ q (some a') Z with
  | none => exact derives_failE _ _
  | some pγ =>
    obtain ⟨p'', γ''⟩ := pγ
    exact Derives.seqFail₁ _ _ _ (Derives.chrFail a' a x₁ (beqChar_false hpa))

theorem moveAlt_ok {cont : Nat → List Nat → PExp} {q Z : Nat} {a : Char} {x₁ r₀ : List Char} {p : Nat}
    {γ : List Nat} {t : PTree} (ha : M.δ q (some a) Z = some (p, γ))
    (h : Derives M.grammar (cont p γ) x₁ (.ok t r₀)) :
    Derives M.grammar (M.moveAlt cont q Z a) (a :: x₁) (.ok (.seq (.leaf [a]) t) r₀) := by
  simp only [moveAlt, ha]
  exact Derives.seqOk _ _ _ x₁ r₀ _ _ (Derives.chrOk a a x₁ (beqChar_iff.mpr rfl)) h

theorem moveAlt_fail {cont : Nat → List Nat → PExp} {q Z : Nat} {a : Char} {x₁ : List Char} {p : Nat}
    {γ : List Nat} (ha : M.δ q (some a) Z = some (p, γ))
    (h : Derives M.grammar (cont p γ) x₁ .fail) :
    Derives M.grammar (M.moveAlt cont q Z a) (a :: x₁) .fail := by
  simp only [moveAlt, ha]
  exact Derives.seqFail₂ _ _ _ x₁ _ (Derives.chrOk a a x₁ (beqChar_iff.mpr rfl)) h

theorem moves_ok {cont : Nat → List Nat → PExp} {q Z : Nat} {x x₁ r₀ : List Char} {p : Nat}
    {γ : List Nat} {t : PTree} (hs : M.step (q, x, [Z]) = some (p, x₁, γ))
    (h : Derives M.grammar (cont p γ) x₁ (.ok t r₀)) :
    ∃ t', Derives M.grammar (M.moves cont q Z) x (.ok t' r₀) := by
  rcases M.step_single hs with ⟨hε, rfl⟩ | ⟨hε, a, rfl, ha⟩
  · simp only [moves, hε]; exact ⟨_, h⟩
  · simp only [moves, hε]
    apply altList_ok
    · intro e he
      obtain ⟨a', -, rfl⟩ := List.mem_map.mp he
      by_cases hpa : a' = a
      · subst hpa; exact Or.inr ⟨_, M.moveAlt_ok ha h⟩
      · exact Or.inl (M.moveAlt_ne hpa)
    · exact ⟨_, List.mem_map.mpr ⟨a, M.read _ _ _ _ ha, rfl⟩, _, M.moveAlt_ok ha h⟩

theorem moves_fail {cont : Nat → List Nat → PExp} {q Z : Nat} {x x₁ : List Char} {p : Nat}
    {γ : List Nat} (hs : M.step (q, x, [Z]) = some (p, x₁, γ))
    (h : Derives M.grammar (cont p γ) x₁ .fail) :
    Derives M.grammar (M.moves cont q Z) x .fail := by
  rcases M.step_single hs with ⟨hε, rfl⟩ | ⟨hε, a, rfl, ha⟩
  · simp only [moves, hε]; exact h
  · simp only [moves, hε]
    apply altList_fail
    intro e he
    obtain ⟨a', -, rfl⟩ := List.mem_map.mp he
    by_cases hpa : a' = a
    · subst hpa; exact M.moveAlt_fail ha h
    · exact M.moveAlt_ne hpa

/-- A rule body that succeeds gives its nonterminal. -/
theorem nt_ok {i : Nat} {e : PExp} {x r : List Char} {t : PTree}
    (hr : ruleAt M.grammar.rules i = some e) (h : Derives M.grammar e x (.ok t r)) :
    ∃ t', Derives M.grammar (.nt i) x (.ok t' r) := ⟨_, Derives.ntOk i e x r t hr h⟩

theorem nt_fail {i : Nat} {e : PExp} {x : List Char}
    (hr : ruleAt M.grammar.rules i = some e) (h : Derives M.grammar e x .fail) :
    Derives M.grammar (.nt i) x .fail := Derives.ntFail i e x hr h

end DPDA

end Shallot.Dpda
