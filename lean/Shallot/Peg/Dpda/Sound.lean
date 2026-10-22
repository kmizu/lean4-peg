import Shallot.Peg.Dpda.Lemmas

/-!
# Soundness: a successful derivation gives a run of the automaton

`Rel C e x r` over-approximates "`e` succeeds on `x` leaving `r`" for the expression forms the grammar uses, with the
nonterminals interpreted by `C`. `sound_derives` shows that every successful derivation satisfies it, provided the
claims `C` follow from the rule bodies (`hnt`). For the DPDA grammar, `C` says:

* `P q Z p` succeeds on `x` leaving `r` only if the automaton, started on `[Z]` in state `q`, pops `Z` in state `p`
  having read `x` up to `r`;
* `A q Z` succeeds on `x` only if it leaves `[]` and the automaton accepts while processing `[Z]`.
-/

namespace Shallot.Dpda

open Shallot

/-- Over-approximate success relation (exact for `eps`, `chr`, `seq`, `alt` and end of input). -/
def Rel (C : Nat → List Char → List Char → Prop) : PExp → List Char → List Char → Prop
  | .eps, x, r => x = r
  | .chr c, x, r => x = c :: r
  | .seq e₁ e₂, x, r => ∃ m, Rel C e₁ x m ∧ Rel C e₂ m r
  | .alt e₁ e₂, x, r => Rel C e₁ x r ∨ Rel C e₂ x r
  | .notP .any, x, r => x = [] ∧ r = []
  | .notP _, x, r => x = r
  | .range lo hi, x, r => ∃ c, x = c :: r ∧ (leChar lo c && leChar c hi) = true
  | .nt i, x, r => C i x r
  | _, _, _ => True

theorem sound_derives {C : Nat → List Char → List Char → Prop} {g : Grammar}
    (hnt : ∀ i e, ruleAt g.rules i = some e → ∀ x r, Rel C e x r → C i x r)
    {e : PExp} {x : List Char} {o : Outcome} (h : Derives g e x o) :
    ∀ t r, o = .ok t r → Rel C e x r := by
  induction h with
  | eps input => intro t r ho; cases ho; rfl
  | chrOk c d rest hb =>
    intro t r ho; cases ho
    show d :: rest = c :: rest
    rw [beqChar_iff.mp hb]
  | rangeOk lo hi d rest hb => intro t r ho; cases ho; exact ⟨d, rfl, hb⟩
  | ntOk i e input rest t hr hd ih =>
    intro t' r ho; cases ho
    exact hnt i e hr _ _ (ih t rest rfl)
  | seqOk e₁ e₂ input rest₁ rest₂ t₁ t₂ h₁ h₂ ih₁ ih₂ =>
    intro t r ho; cases ho
    exact ⟨rest₁, ih₁ t₁ rest₁ rfl, ih₂ t₂ _ rfl⟩
  | altL e₁ e₂ input rest t h ih => intro t' r ho; cases ho; exact Or.inl (ih t _ rfl)
  | altR e₁ e₂ input rest t h₁ h₂ ih₁ ih₂ => intro t' r ho; cases ho; exact Or.inr (ih₂ t _ rfl)
  | notFail e input h ih =>
    intro t r ho; cases ho
    cases e with
    | any => cases h; exact ⟨rfl, rfl⟩
    | _ => rfl
  | _ => intro t r ho; first | (cases ho; done) | simp [Rel]

theorem rel_failE {C : Nat → List Char → List Char → Prop} {x r : List Char} : ¬ Rel C failE x r := by
  rintro ⟨c, -, h⟩
  have : ∀ n : Nat, (Nat.ble 1 n && Nat.ble n 0) = false := by
    intro n
    cases n with
    | zero => rfl
    | succ k => have h : Nat.ble (k + 1) 0 = false := rfl; simp [h]
  exact absurd h (by rw [show leChar '\u0001' c = Nat.ble 1 c.toNat from rfl,
    show leChar c '\u0000' = Nat.ble c.toNat 0 from rfl, this]; simp)

theorem rel_altList {C : Nat → List Char → List Char → Prop} {x r : List Char} :
    ∀ {l : List PExp}, Rel C (altList l) x r → ∃ e ∈ l, Rel C e x r
  | [], h => absurd h rel_failE
  | e :: es, h => by
    rcases h with h | h
    · exact ⟨e, List.mem_cons_self, h⟩
    · obtain ⟨e', he', h'⟩ := rel_altList h
      exact ⟨e', List.mem_cons_of_mem _ he', h'⟩

namespace DPDA

variable (M : DPDA)

/-- `Z` is popped in state `p`, reading `x` up to `r`. -/
def PopRun (q Z p : Nat) (x r : List Char) : Prop := ∃ n, M.run n (q, x, [Z]) = some (p, r, [])

/-- The stack `γ` is popped entirely, ending in state `r'`. -/
def PopS (p : Nat) (γ : List Nat) (r' : Nat) (x r : List Char) : Prop := ∃ n, M.run n (p, x, γ) = some (r', r, [])

/-- Acceptance is reached while processing the stack `γ`. -/
def AccS (p : Nat) (γ : List Nat) (x : List Char) : Prop :=
  ∃ n f β, M.run n (p, x, γ) = some (f, [], β) ∧ M.final f = true

/-- The claims about nonterminals. -/
def claim (i : Nat) (x r : List Char) : Prop :=
  (∀ q Z p, q < M.nQ → Z < M.nG → p < M.nQ → i = M.pidx q Z p → M.PopRun q Z p x r) ∧
    (∀ q Z, q < M.nQ → Z < M.nG → i = M.aidx q Z → r = [] ∧ M.AccS q [Z] x)

theorem rel_popS {x r : List Char} (r₀ : Nat) :
    ∀ (γ : List Nat) (p : Nat), p < M.nQ → (∀ X ∈ γ, X < M.nG) →
      Rel M.claim (M.popS r₀ M.pidx p γ) x r → M.PopS p γ r₀ x r
  | [], p, _, _, h => by
    unfold popS at h
    split at h
    · rename_i hp; subst hp; exact ⟨0, by simp [run]; exact h⟩
    · exact absurd h rel_failE
  | X :: γ, p, hp, hγ, h => by
    unfold popS at h
    obtain ⟨e, he, hrel⟩ := rel_altList h
    obtain ⟨q₁, hq₁, rfl⟩ := List.mem_map.mp he
    have hq₁' : q₁ < M.nQ := List.mem_range.mp hq₁
    obtain ⟨m, hnt, hrest⟩ := hrel
    obtain ⟨n₁, h₁⟩ := hnt.1 p X q₁ hp (hγ X List.mem_cons_self) hq₁' rfl
    obtain ⟨n₂, h₂⟩ := rel_popS r₀ γ q₁ hq₁' (fun Y hY => hγ Y (List.mem_cons_of_mem _ hY)) hrest
    refine ⟨n₁ + n₂, ?_⟩
    have := M.run_append h₁ γ
    rw [M.run_add, show X :: γ = [X] ++ γ from rfl, this]
    simpa using h₂

theorem rel_accS {x r : List Char} :
    ∀ (γ : List Nat) (p : Nat), p < M.nQ → (∀ X ∈ γ, X < M.nG) →
      Rel M.claim (M.accS M.pidx M.aidx p γ) x r → r = [] ∧ M.AccS p γ x
  | [], p, _, _, h => by
    unfold accS at h
    split at h
    · rename_i hf
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, 0, p, [], by simp [run], hf⟩
    · exact absurd h rel_failE
  | X :: γ, p, hp, hγ, h => by
    unfold accS at h
    rcases h with h | h
    · obtain ⟨hr, n, f, β, hrun, hf⟩ := h.2 p X hp (hγ X List.mem_cons_self) rfl
      refine ⟨hr, n, f, β ++ γ, ?_, hf⟩
      exact M.run_append hrun γ
    · obtain ⟨e, he, hrel⟩ := rel_altList h
      obtain ⟨q₁, hq₁, rfl⟩ := List.mem_map.mp he
      have hq₁' : q₁ < M.nQ := List.mem_range.mp hq₁
      obtain ⟨m, hnt, hrest⟩ := hrel
      obtain ⟨n₁, h₁⟩ := hnt.1 p X q₁ hp (hγ X List.mem_cons_self) hq₁' rfl
      obtain ⟨hr, n₂, f, β, h₂, hf⟩ :=
        rel_accS γ q₁ hq₁' (fun Y hY => hγ Y (List.mem_cons_of_mem _ hY)) hrest
      refine ⟨hr, n₁ + n₂, f, β, ?_, hf⟩
      have := M.run_append h₁ γ
      rw [M.run_add, show X :: γ = [X] ++ γ from rfl, this]
      simpa using h₂

/-- A successful `moves` expression comes from a move of the automaton on `[Z]`. -/
theorem rel_moves {cont : Nat → List Nat → PExp} {q Z : Nat} {x r : List Char}
    (h : Rel M.claim (M.moves cont q Z) x r) :
    ∃ p γ x₁, M.step (q, x, [Z]) = some (p, x₁, γ) ∧ p < M.nQ ∧ (∀ X ∈ γ, X < M.nG) ∧
      Rel M.claim (cont p γ) x₁ r := by
  unfold moves at h
  cases hε : M.δ q none Z with
  | some pγ =>
    obtain ⟨p, γ⟩ := pγ
    rw [hε] at h
    have hc := M.cod _ _ _ _ _ hε
    exact ⟨p, γ, x, by simp [step, hε], hc.1, hc.2, h⟩
  | none =>
    rw [hε] at h
    obtain ⟨e, he, hrel⟩ := rel_altList h
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp he
    cases ha : M.δ q (some a) Z with
    | none => simp only [moveAlt, ha] at hrel; exact absurd hrel rel_failE
    | some pγ =>
      obtain ⟨p, γ⟩ := pγ
      simp only [moveAlt, ha] at hrel
      obtain ⟨m, hx, hrest⟩ := hrel
      have hc := M.cod _ _ _ _ _ ha
      subst hx
      exact ⟨p, γ, m, by simp [step, hε, ha], hc.1, hc.2, hrest⟩

theorem sound_popRule {q Z p : Nat} {x r : List Char}
    (h : Rel M.claim (M.popRule q Z p) x r) : M.PopRun q Z p x r := by
  obtain ⟨p', γ, x₁, hs, hp', hγ, hrel⟩ := M.rel_moves h
  obtain ⟨n, hn⟩ := M.rel_popS p γ p' hp' hγ hrel
  exact ⟨n + 1, by rw [M.run_succ_of_step hs]; exact hn⟩

theorem sound_accRule {q Z : Nat} {x r : List Char}
    (h : Rel M.claim (M.accRule q Z) x r) : r = [] ∧ M.AccS q [Z] x := by
  unfold accRule at h
  rcases h with h | h
  · split at h
    · rename_i hf
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, 0, q, [Z], by simp [run], hf⟩
    · exact absurd h rel_failE
  · obtain ⟨p', γ, x₁, hs, hp', hγ, hrel⟩ := M.rel_moves h
    obtain ⟨hr, n, f, β, hn, hf⟩ := M.rel_accS γ p' hp' hγ hrel
    exact ⟨hr, n + 1, f, β, by rw [M.run_succ_of_step hs]; exact hn, hf⟩

theorem claim_of_rule {i : Nat} {e : PExp} (hr : ruleAt M.grammar.rules i = some e) (x r : List Char)
    (h : Rel M.claim e x r) : M.claim i x r := by
  constructor
  · intro q Z p hq hZ hp hi
    subst hi
    rw [M.ruleAt_pop hq hZ hp] at hr
    cases hr
    exact M.sound_popRule h
  · intro q Z hq hZ hi
    subst hi
    rw [M.ruleAt_acc hq hZ] at hr
    cases hr
    exact M.sound_accRule h

/-- **Soundness**: if `A q₀ Z₀` succeeds on `w` with nothing left, the automaton accepts `w`. -/
theorem sound {w : List Char} {t : PTree} (h : Derives M.grammar (.nt M.grammar.start) w (.ok t [])) :
    M.language w := by
  have := sound_derives (C := M.claim) (fun i e hr x r hrel => M.claim_of_rule hr x r hrel) h t [] rfl
  obtain ⟨-, n, f, β, hrun, hf⟩ := (this.2 M.q0 M.Z0 M.q0_lt M.Z0_lt rfl)
  exact ⟨n, f, β, hrun, hf⟩

end DPDA

end Shallot.Dpda
