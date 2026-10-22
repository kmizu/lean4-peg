import Shallot.Peg.Packrat.Spec
import Shallot.Peg.GrammarExtend

/-!
# The finite table domain

Only subexpressions of rules and the start call at positions through the
end of the input matter. Agreement on these cells propagates one round.
-/

namespace Shallot.Packrat

theorem mem_subterms_self (e : PExp) : e ∈ subterms e := by
  cases e <;> simp [subterms]

theorem subterms_trans {a b c : PExp} (hb : b ∈ subterms a)
    (hc : c ∈ subterms b) : c ∈ subterms a := by
  induction a with
  | seq a b iha ihb | alt a b iha ihb =>
    simp only [subterms, List.mem_cons, List.mem_append] at hb ⊢
    rcases hb with he | ha | hb
    · subst he; simpa only [subterms, List.mem_cons, List.mem_append] using hc
    · exact Or.inr (Or.inl (iha ha))
    · exact Or.inr (Or.inr (ihb hb))
  | star a ih | notP a ih =>
    simp only [subterms, List.mem_cons] at hb ⊢
    rcases hb with he | ha
    · subst he; simpa only [subterms, List.mem_cons, List.mem_append] using hc
    · exact Or.inr (ih ha)
  | eps | any | chr _ | range _ _ | lit _ | nt _ =>
    simp only [subterms, List.mem_singleton] at hb
    subst hb; exact hc

theorem dom_subterm {g : Grammar} {e a : PExp} (he : e ∈ dom g)
    (ha : a ∈ subterms e) : a ∈ dom g := by
  obtain ⟨b, hb, hbe⟩ := List.mem_flatMap.mp he
  exact List.mem_flatMap.mpr ⟨b, hb, subterms_trans hbe ha⟩

theorem dom_rule {g : Grammar} {j : Nat} {b : PExp}
    (h : ruleAt g.rules j = some b) : b ∈ dom g := by
  exact List.mem_flatMap.mpr ⟨b, List.mem_cons_of_mem _ (ruleAt_mem h), mem_subterms_self b⟩

theorem dom_start (g : Grammar) : .nt g.start ∈ dom g := by
  exact List.mem_flatMap.mpr ⟨_, List.mem_cons_self, mem_subterms_self _⟩

/-- Agreement at every relevant expression and input position. -/
def Agree (g : Grammar) (x : List Char) (n m : Nat) : Prop :=
  ∀ e ∈ dom g, ∀ i, i ≤ x.length → iter g x n e i = iter g x m e i

/-- A round depends only on relevant cells, provided consumption stays in bounds. -/
theorem round_congr {g : Grammar} {x : List Char} {T U : Tbl}
    (h : ∀ e ∈ dom g, ∀ i, i ≤ x.length → T e i = U e i)
    (consumption : ∀ e ∈ dom g, ∀ i, i ≤ x.length → ∀ k,
      T e i = some (some k) → k ≤ (x.drop i).length) :
    ∀ e ∈ dom g, ∀ i, i ≤ x.length → F g x T e i = F g x U e i := by
  intro e he i hi
  have hc : ∀ a ∈ subterms e, T a i = U a i :=
    fun a ha => h a (dom_subterm he ha) i hi
  cases e with
  | eps | any | chr _ | range _ _ | lit _ => rfl
  | nt j =>
    simp only [F]
    cases hr : ruleAt g.rules j with
    | none => rfl
    | some b => exact h b (dom_rule hr) i hi
  | seq a b =>
    have ha := hc a (by simp [subterms, mem_subterms_self])
    have hb : b ∈ dom g := dom_subterm he (by simp [subterms, mem_subterms_self])
    simp only [F]
    rw [← ha]
    cases hv : T a i with
    | none => rfl
    | some r =>
      cases r with
      | none => rfl
      | some k =>
        have hk := consumption a (dom_subterm he (by simp [subterms, mem_subterms_self])) i hi k hv
        have hik : i + k ≤ x.length := by simp only [List.length_drop] at hk; omega
        dsimp only
        rw [h b hb (i + k) hik]
  | alt a b =>
    have ha := hc a (by simp [subterms, mem_subterms_self])
    have hb := hc b (by simp [subterms, mem_subterms_self])
    simp only [F]
    rw [ha, hb]
  | star a =>
    have ha := hc a (by simp [subterms, mem_subterms_self])
    simp only [F]
    rw [← ha]
    cases hv : T a i with
    | none => rfl
    | some r =>
      cases r with
      | none => rfl
      | some k =>
        have hk := consumption a (dom_subterm he (by simp [subterms, mem_subterms_self])) i hi k hv
        have hik : i + k ≤ x.length := by simp only [List.length_drop] at hk; omega
        dsimp only
        rw [h (.star a) he (i + k) hik]
  | notP a =>
    have ha := hc a (by simp [subterms, mem_subterms_self])
    simp only [F]
    rw [ha]

/-- Equal consecutive tables stay equal after another round. -/
theorem agree_step {g : Grammar} {x : List Char} {n m : Nat}
    (h : Agree g x n m) : Agree g x (n + 1) (m + 1) :=
  round_congr h (fun _ _ _ _ _ hv => iter_consumption hv)

/-- Once two successive rounds agree, all later rounds agree with them. -/
theorem agree_later {g : Grammar} {x : List Char} {n : Nat}
    (h : Agree g x n (n + 1)) (k : Nat) : Agree g x n (n + k) := by
  induction k with
  | zero => intro _ _ _ _; rfl
  | succ k ih =>
    have hs : Agree g x (n + k) (n + k + 1) := by
      clear ih
      induction k with
      | zero => simpa using h
      | succ k ihk => simpa [Nat.add_assoc] using agree_step ihk
    intro e he i hi
    exact (ih e he i hi).trans (hs e he i hi)

end Shallot.Packrat
