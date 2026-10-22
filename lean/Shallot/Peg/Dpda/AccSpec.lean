import Shallot.Peg.Dpda.PopSpec

/-!
# Completeness for the accept nonterminals

* `Afail`: if `Z` is popped after `n` moves without the automaton having accepted while processing `Z`, then
  `A q Z` fails on the input (so the following alternatives are tried).
* `Aok`: if the automaton accepts after `n` moves while processing `Z`, then `A q Z` succeeds, leaving nothing.

`Afail` is proved first, by induction on `n`, from the pop completeness; `Aok` then uses both.
-/

namespace Shallot.Dpda

open Shallot

namespace DPDA

variable (M : DPDA)

theorem run_nil_some {m p : Nat} {x : List Char} {c : Config} (h : M.run m (p, x, []) = some c) :
    m = 0 ∧ c = (p, x, []) := by
  cases m with
  | zero => simp [run] at h; exact ⟨rfl, h.symm⟩
  | succ m => rw [M.run_succ_of_step_none (M.step_nil p x)] at h; cases h

/-- A run that has emptied the stack cannot go on. -/
theorem run_le_of_pop {k n : Nat} {c : Config} {s : Nat} {x'' : List Char}
    (hk : M.run k c = some (s, x'', [])) {d : Config} (hn : M.run n c = some d) : n ≤ k := by
  rcases Nat.lt_or_ge k n with hlt | hge
  · exfalso
    obtain ⟨j, rfl⟩ : ∃ j, n = k + (j + 1) := ⟨n - k - 1, by omega⟩
    rw [M.run_add, hk] at hn
    simp [run, step_nil] at hn
  · exact hge

theorem accS_head {p X : Nat} {x : List Char} {γ : List Nat} (h : M.AccS p [X] x) : M.AccS p (X :: γ) x := by
  obtain ⟨n, f, β, h1, hf⟩ := h
  exact ⟨n, f, β ++ γ, M.run_append h1 γ, hf⟩

theorem accS_tail {k p s X : Nat} {x x'' : List Char} {γ : List Nat}
    (hk : M.run k (p, x, [X]) = some (s, x'', [])) (h : M.AccS s γ x'') : M.AccS p (X :: γ) x := by
  obtain ⟨n, f, β, h1, hf⟩ := h
  refine ⟨k + n, f, β, ?_, hf⟩
  have := M.run_append hk γ
  rw [M.run_add, show X :: γ = [X] ++ γ from rfl, this]
  simpa using h1

theorem accS_of_step {q Z p : Nat} {x x₁ : List Char} {γ : List Nat}
    (hs : M.step (q, x, [Z]) = some (p, x₁, γ)) (h : M.AccS p γ x₁) : M.AccS q [Z] x := by
  obtain ⟨n, f, β, h1, hf⟩ := h
  exact ⟨n + 1, f, β, by rw [M.run_succ_of_step hs]; exact h1, hf⟩

theorem cond_eof_ok (g : Grammar) (b : Bool) (hb : b = true) :
    ∃ t, Derives g (if b then eofE else failE) [] (.ok t []) := by
  rw [if_pos hb]; exact ⟨_, derives_eofE_nil g⟩

theorem cond_eof_fail (g : Grammar) (b : Bool) (x : List Char) (h : ¬ (b = true ∧ x = [])) :
    Derives g (if b then eofE else failE) x .fail := by
  by_cases hb : b = true
  · rw [if_pos hb]
    cases x with
    | nil => exact absurd ⟨hb, rfl⟩ h
    | cons c rest => exact derives_eofE_cons g c rest
  · rw [if_neg hb]; exact derives_failE g x

/-- `Z` is popped without the automaton accepting on the way. -/
def Afail (n : Nat) : Prop :=
  ∀ q Z x p x', q < M.nQ → Z < M.nG → M.run n (q, x, [Z]) = some (p, x', []) → ¬ M.AccS q [Z] x →
    Derives M.grammar (.nt (M.aidx q Z)) x .fail

theorem accS_fail (B : Nat) (hP : ∀ n ≤ B, M.Pspec n) (hAf : ∀ n ≤ B, M.Afail n) :
    ∀ (γ : List Nat) (p : Nat) (x x' : List Char) (r₁ m : Nat), m ≤ B → p < M.nQ → (∀ X ∈ γ, X < M.nG) →
      M.run m (p, x, γ) = some (r₁, x', []) → ¬ M.AccS p γ x →
        Derives M.grammar (M.accS M.pidx M.aidx p γ) x .fail
  | [], p, x, x', r₁, m, _, _, _, _, hacc => by
    simp only [accS]
    exact cond_eof_fail _ _ _ (fun ⟨hf, hx⟩ => hacc ⟨0, p, [], by simp [run, hx], hf⟩)
  | X :: γ, p, x, x', r₁, m, hm, hp, hγ, h, hacc => by
    obtain ⟨k, s, x'', hk0, hkm, hrk, hrest⟩ := M.run_pop_split h
    have hs : s < M.nQ := M.run_state_lt hk0 hrk
    have hX : X < M.nG := hγ X List.mem_cons_self
    have hPk := hP k (by omega) p X s x x'' hp hX hrk
    have hA := hAf k (by omega) p X x s x'' hp hX hrk (fun hh => hacc (M.accS_head hh))
    have hγ' := accS_fail B hP hAf γ s x'' x' r₁ (m - k) (by omega) hs
      (fun Y hY => hγ Y (List.mem_cons_of_mem _ hY)) hrest (fun hh => hacc (M.accS_tail hrk hh))
    simp only [accS]
    refine Derives.altFail _ _ _ hA ?_
    apply altList_fail
    intro e he
    obtain ⟨q₁, hq₁, rfl⟩ := List.mem_map.mp he
    by_cases hqs : q₁ = s
    · subst hqs
      obtain ⟨t, ht⟩ := (hPk q₁ hs).1 rfl
      exact Derives.seqFail₂ _ _ _ x'' _ ht hγ'
    · exact Derives.seqFail₁ _ _ _ ((hPk q₁ (List.mem_range.mp hq₁)).2 hqs)

theorem afail_le : ∀ B n, n ≤ B → M.Afail n
  | 0, n, hn => by
    have : n = 0 := by omega
    subst this
    intro q Z x p x' _ _ h
    simp [run] at h
  | B + 1, n, hn => by
    by_cases hle : n ≤ B
    · exact afail_le B n hle
    · have hn' : n = B + 1 := by omega
      subst hn'
      intro q Z x p x' hq hZ hrun hacc
      cases hs : M.step (q, x, [Z]) with
      | none => rw [M.run_succ_of_step_none hs] at hrun; cases hrun
      | some c1 =>
        obtain ⟨p1, x₁, γ⟩ := c1
        rw [M.run_succ_of_step hs] at hrun
        have hlt := M.step_single_lt hs
        have hbody : Derives M.grammar (M.accRule q Z) x .fail := by
          refine Derives.altFail _ _ _ ?_ ?_
          · exact cond_eof_fail _ _ _ (fun ⟨hf, hx⟩ => hacc ⟨0, q, [Z], by simp [run, hx], hf⟩)
          · exact M.moves_fail (cont := fun p γ => M.accS M.pidx M.aidx p γ) hs
              (M.accS_fail B (fun k _ => M.pop_spec k) (fun k hk => afail_le B k hk) γ p1 x₁ x' p B
                (Nat.le_refl _) hlt.1 hlt.2 hrun (fun hh => hacc (M.accS_of_step hs hh)))
        exact M.nt_fail (M.ruleAt_acc hq hZ) hbody

/-- Acceptance within `n` moves while processing `Z`. -/
def Aok (n : Nat) : Prop :=
  ∀ q Z x f β, q < M.nQ → Z < M.nG → M.run n (q, x, [Z]) = some (f, [], β) → M.final f = true →
    ∃ t, Derives M.grammar (.nt (M.aidx q Z)) x (.ok t [])

theorem accS_ok (B : Nat) (hP : ∀ n ≤ B, M.Pspec n) (hAo : ∀ n ≤ B, M.Aok n) :
    ∀ (γ : List Nat) (p : Nat) (x : List Char) (f : Nat) (β : List Nat) (m : Nat), m ≤ B → p < M.nQ →
      (∀ X ∈ γ, X < M.nG) → M.run m (p, x, γ) = some (f, [], β) → M.final f = true →
        ∃ t, Derives M.grammar (M.accS M.pidx M.aidx p γ) x (.ok t [])
  | [], p, x, f, β, m, _, _, _, h, hf => by
    obtain ⟨rfl, hc⟩ := M.run_nil_some h
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl, -⟩ := hc
    simp only [accS]
    exact cond_eof_ok _ _ hf
  | X :: γ, p, x, f, β, m, hm, hp, hγ, h, hf => by
    have hX : X < M.nG := hγ X List.mem_cons_self
    simp only [accS]
    rcases M.run_split (ξ := [X]) (β := γ) (by simp) h with
      ⟨c', hc', hc, -⟩ | ⟨k, hk, hk0, s, x'', hr, hr'⟩
    · obtain ⟨f', x', β'⟩ := c'
      simp only [below, Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl, -⟩ := hc
      obtain ⟨t, ht⟩ := hAo m hm p X x f β' hp hX hc' hf
      exact ⟨_, Derives.altL _ _ _ _ _ ht⟩
    · have hs : s < M.nQ := M.run_state_lt hk0 hr
      have hPk := hP k (by omega) p X s x x'' hp hX hr
      have hγ' := accS_ok B hP hAo γ s x'' f β (m - k) (by omega) hs
        (fun Y hY => hγ Y (List.mem_cons_of_mem _ hY)) hr' hf
      by_cases hacc : M.AccS p [X] x
      · obtain ⟨n₀, f₀, β₀, h₀, hf₀⟩ := hacc
        have hn₀ : n₀ ≤ k := M.run_le_of_pop hr h₀
        obtain ⟨t, ht⟩ := hAo n₀ (by omega) p X x f₀ β₀ hp hX h₀ hf₀
        exact ⟨_, Derives.altL _ _ _ _ _ ht⟩
      · have hA := M.afail_le k k (Nat.le_refl _) p X x s x'' hp hX hr hacc
        obtain ⟨t, ht⟩ := (hPk s hs).1 rfl
        obtain ⟨t', ht'⟩ := hγ'
        have hlist : ∃ t, Derives M.grammar
            (altList ((List.range M.nQ).map fun q₁ =>
              PExp.seq (.nt (M.pidx p X q₁)) (M.accS M.pidx M.aidx q₁ γ))) x (.ok t []) := by
          apply altList_ok
          · intro e he
            obtain ⟨q₁, hq₁, rfl⟩ := List.mem_map.mp he
            by_cases hqs : q₁ = s
            · subst hqs
              exact Or.inr ⟨_, Derives.seqOk _ _ _ x'' [] _ _ ht ht'⟩
            · exact Or.inl (Derives.seqFail₁ _ _ _ ((hPk q₁ (List.mem_range.mp hq₁)).2 hqs))
          · exact ⟨_, List.mem_map.mpr ⟨s, List.mem_range.mpr hs, rfl⟩, _,
              Derives.seqOk _ _ _ x'' [] _ _ ht ht'⟩
        obtain ⟨t'', ht''⟩ := hlist
        exact ⟨_, Derives.altR _ _ _ _ _ hA ht''⟩

theorem aok_le : ∀ B n, n ≤ B → M.Aok n
  | B, n, hn => by
    intro q Z x f β hq hZ hrun hf
    have hrule := M.ruleAt_acc hq hZ
    by_cases h0 : M.final q = true ∧ x = []
    · obtain ⟨hfq, rfl⟩ := h0
      obtain ⟨t, ht⟩ := cond_eof_ok M.grammar (M.final q) hfq
      exact M.nt_ok hrule (Derives.altL _ _ _ _ _ ht)
    · have hfail := cond_eof_fail M.grammar (M.final q) x h0
      cases n with
      | zero =>
        simp [run] at hrun
        obtain ⟨rfl, rfl, -⟩ := hrun
        exact absurd ⟨hf, rfl⟩ h0
      | succ m =>
        cases hs : M.step (q, x, [Z]) with
        | none => rw [M.run_succ_of_step_none hs] at hrun; cases hrun
        | some c1 =>
          obtain ⟨p1, x₁, γ⟩ := c1
          rw [M.run_succ_of_step hs] at hrun
          have hlt := M.step_single_lt hs
          obtain ⟨t, ht⟩ := M.accS_ok m (fun k _ => M.pop_spec k)
            (fun k hk => aok_le m k hk) γ p1 x₁ f β m (Nat.le_refl _) hlt.1 hlt.2 hrun hf
          obtain ⟨t', ht'⟩ := M.moves_ok (cont := fun p γ => M.accS M.pidx M.aidx p γ) hs ht
          exact M.nt_ok hrule (Derives.altR _ _ _ _ _ hfail ht')
termination_by B => B

/-- **Completeness**: an accepted word is accepted by the start rule, leaving nothing. -/
theorem complete {w : List Char} (h : M.language w) :
    ∃ t, Derives M.grammar (.nt M.grammar.start) w (.ok t []) := by
  obtain ⟨n, f, β, hrun, hf⟩ := h
  exact M.aok_le n n (Nat.le_refl _) M.q0 M.Z0 w f β M.q0_lt M.Z0_lt hrun hf

end DPDA

end Shallot.Dpda
