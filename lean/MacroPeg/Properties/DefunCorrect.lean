import MacroPeg.Properties.Defun
import MacroPeg.Properties.Specialize
import MacroPeg.Properties.Decide

/-!
# Defunctionalization is correct

For a grammar `g` and a start expression `e` of the callable-value slice, `defun g e` is a first-order grammar and
expression with the same observations (`defun_obs`). Hence the decision procedure for first-order call-by-name Macro
PEG (`Decide.lean`) decides the slice too (`decideSlice_iff`).

The proof:

1. the translation never produces `lam`, `dbg`, `callParam` or `invoke`, so the result is first-order;
2. *every lambda a run meets is in `Λ`* (`Good`): substitution only moves lambdas around (`lams_subst`), and `Λ` holds
   the lambdas inside its own members' bodies (`LamsClosed`);
3. the first-order grammar has the rule `tr v body` for every spec (`ruleAt_defun`);
4. runs agree step by step (`run_forward`, `run_backward`): a call or an invocation is a call of the matching spec, and
   by `tr_subst` the callee bodies correspond again.
-/

namespace Shallot.MacroPeg

section

variable {g : MGrammar} {Λ : List (Nat × MExp)}

/-! ## The translation is first-order -/

theorem failAlways_firstOrder : MExp.failAlways.FirstOrder := trivial

theorem callUnit_firstOrder {v : List Nat} {u : Nat} {args targs : List MExp} (h : MExp.FirstOrderArgs targs) :
    (callUnit g Λ v u args targs).FirstOrder := by
  unfold callUnit; split
  · exact h
  · exact failAlways_firstOrder

mutual
  theorem tr_firstOrder (v : List Nat) : ∀ e : MExp, (tr g Λ v e).FirstOrder
    | .eps | .any | .chr _ | .range _ _ | .lit _ | .param _ | .lam _ _ | .dbg _ => trivial
    | .seq e₁ e₂ | .alt e₁ e₂ => ⟨tr_firstOrder v e₁, tr_firstOrder v e₂⟩
    | .star e | .notP e => tr_firstOrder v e
    | .call i args => by
      unfold tr; split
      · exact callUnit_firstOrder (trArgs_firstOrder v args)
      · exact failAlways_firstOrder
    | .callParam k args => by
      unfold tr; split
      · exact failAlways_firstOrder
      · exact callUnit_firstOrder (trArgs_firstOrder v args)
    | .invoke a b args => by
      unfold tr; split
      · exact callUnit_firstOrder (trArgs_firstOrder v args)
      · exact failAlways_firstOrder

  theorem trArgs_firstOrder (v : List Nat) : ∀ args : List MExp, MExp.FirstOrderArgs (trArgs g Λ v args)
    | [] => trivial
    | e :: es => ⟨tr_firstOrder v e, trArgs_firstOrder v es⟩
end

theorem defunGrammar_firstOrder : (defunGrammar g Λ).FirstOrder := by
  intro r hr
  simp only [defunGrammar, List.mem_map] at hr
  obtain ⟨⟨u, v⟩, _, rfl⟩ := hr
  exact tr_firstOrder v _

/-! ## Every lambda a run meets is in `Λ` -/

/-- All lambdas of `e` are in `Λ`. -/
def Good (Λ : List (Nat × MExp)) (e : MExp) : Prop := ∀ p ∈ e.lams, p ∈ Λ

/-- `Λ` contains the lambdas inside the bodies of its members. -/
def LamsClosed (Λ : List (Nat × MExp)) : Prop := ∀ a b, (a, b) ∈ Λ → Good Λ b

theorem lams_argAt : ∀ {A : List MExp} {k : Nat} {a : MExp}, argAt A k = some a → ∀ p ∈ a.lams, p ∈ MExp.lamsArgs A
  | _ :: _, 0, _, h, p, hp => by cases h; simp [MExp.lamsArgs, hp]
  | _ :: A, k + 1, _, h, p, hp => by simp [MExp.lamsArgs, lams_argAt (A := A) (k := k) h p hp]

mutual
  /-- Substitution brings in only the lambdas of the body and of the arguments. -/
  theorem lams_subst (A : List MExp) : ∀ (b : MExp), ∀ p ∈ (MExp.subst A b).lams, p ∈ b.lams ∨ p ∈ MExp.lamsArgs A
    | .param k, p, hp => by
      simp only [MExp.subst] at hp
      split at hp
      · exact .inr (lams_argAt (by assumption) p hp)
      · simp [MExp.failAlways, MExp.lams] at hp
    | .callParam k m, p, hp => by
      simp only [MExp.subst] at hp
      split at hp
      · rename_i a b h
        have hl := lams_argAt h
        simp only [MExp.lams, List.mem_cons, List.mem_append] at hp hl
        rcases hp with (rfl | hp) | hp
        · exact .inr (hl _ (.inl rfl))
        · exact .inr (hl _ (.inr hp))
        · rcases lamsArgs_subst A m p hp with h' | h'
          · exact .inl (by simpa [MExp.lams] using h')
          · exact .inr h'
      · simp only [MExp.lams] at hp
        rcases lamsArgs_subst A m p hp with h' | h'
        · exact .inl (by simpa [MExp.lams] using h')
        · exact .inr h'
      · simp [MExp.failAlways, MExp.lams] at hp
    | .call i m, p, hp => by
      simp only [MExp.subst, MExp.lams] at hp ⊢
      exact lamsArgs_subst A m p hp
    | .invoke a b m, p, hp => by
      simp only [MExp.subst, MExp.lams, List.mem_cons, List.mem_append] at hp ⊢
      rcases hp with (rfl | hp) | hp
      · exact .inl (.inl (.inl rfl))
      · exact .inl (.inl (.inr hp))
      · rcases lamsArgs_subst A m p hp with h' | h'
        · exact .inl (.inr h')
        · exact .inr h'
    | .seq e₁ e₂, p, hp | .alt e₁ e₂, p, hp => by
      simp only [MExp.subst, MExp.lams, List.mem_append] at hp ⊢
      rcases hp with hp | hp
      · exact (lams_subst A e₁ p hp).imp .inl id
      · exact (lams_subst A e₂ p hp).imp .inr id
    | .star e, p, hp | .notP e, p, hp | .dbg e, p, hp => by
      simp only [MExp.subst, MExp.lams] at hp ⊢
      exact lams_subst A e p hp
    | .lam a b, p, hp => by simp only [MExp.subst] at hp; exact .inl hp
    | .eps, p, hp | .any, p, hp | .chr _, p, hp | .range _ _, p, hp | .lit _, p, hp => by
      simp [MExp.subst, MExp.lams] at hp

  theorem lamsArgs_subst (A : List MExp) :
      ∀ (m : List MExp), ∀ p ∈ MExp.lamsArgs (MExp.substArgs A m), p ∈ MExp.lamsArgs m ∨ p ∈ MExp.lamsArgs A
    | [], p, hp => by simp [MExp.substArgs, MExp.lamsArgs] at hp
    | e :: es, p, hp => by
      simp only [MExp.substArgs, MExp.lamsArgs, List.mem_append] at hp ⊢
      rcases hp with hp | hp
      · exact (lams_subst A e p hp).imp .inl id
      · exact (lamsArgs_subst A es p hp).imp .inr id
end

theorem goodArgs_of_lamsArgs {A : List MExp} (h : ∀ p ∈ MExp.lamsArgs A, p ∈ Λ) :
    ∀ a ∈ A, Good Λ a := by
  induction A with
  | nil => simp
  | cons a A ih =>
    simp only [MExp.lamsArgs, List.mem_append] at h
    intro b hb
    rcases List.mem_cons.1 hb with rfl | hb
    · exact fun p hp => h p (.inl hp)
    · exact ih (fun p hp => h p (.inr hp)) b hb

theorem good_subst {A : List MExp} {b : MExp} (hA : ∀ p ∈ MExp.lamsArgs A, p ∈ Λ) (hb : Good Λ b) :
    Good Λ (MExp.subst A b) := fun p hp => (lams_subst A b p hp).elim (hb p) (hA p)

mutual
  /-- A lambda's body holds no lambda its enclosing expression does not. -/
  theorem lams_body : ∀ (e : MExp) {a : Nat} {b : MExp}, (a, b) ∈ e.lams → ∀ p ∈ b.lams, p ∈ e.lams
    | .lam a' b', a, b, h, p, hp => by
      simp only [MExp.lams, List.mem_cons] at h ⊢
      rcases h with h | h
      · cases h; exact .inr hp
      · exact .inr (lams_body b' h p hp)
    | .invoke a' b' m, a, b, h, p, hp => by
      simp only [MExp.lams, List.mem_cons, List.mem_append] at h ⊢
      rcases h with (h | h) | h
      · cases h; exact .inl (.inr hp)
      · exact .inl (.inr (lams_body b' h p hp))
      · exact .inr (lamsArgs_body m h p hp)
    | .call _ m, a, b, h, p, hp | .callParam _ m, a, b, h, p, hp => by
      simp only [MExp.lams] at h ⊢; exact lamsArgs_body m h p hp
    | .seq e₁ e₂, a, b, h, p, hp | .alt e₁ e₂, a, b, h, p, hp => by
      simp only [MExp.lams, List.mem_append] at h ⊢
      rcases h with h | h
      · exact .inl (lams_body e₁ h p hp)
      · exact .inr (lams_body e₂ h p hp)
    | .star e, a, b, h, p, hp | .notP e, a, b, h, p, hp | .dbg e, a, b, h, p, hp => by
      simp only [MExp.lams] at h ⊢; exact lams_body e h p hp
    | .eps, _, _, h, _, _ | .any, _, _, h, _, _ | .chr _, _, _, h, _, _ | .range _ _, _, _, h, _, _
    | .lit _, _, _, h, _, _ | .param _, _, _, h, _, _ => by simp [MExp.lams] at h

  theorem lamsArgs_body : ∀ (m : List MExp) {a : Nat} {b : MExp}, (a, b) ∈ MExp.lamsArgs m →
      ∀ p ∈ b.lams, p ∈ MExp.lamsArgs m
    | [], _, _, h, _, _ => by simp [MExp.lamsArgs] at h
    | e :: es, a, b, h, p, hp => by
      simp only [MExp.lamsArgs, List.mem_append] at h ⊢
      rcases h with h | h
      · exact .inl (lams_body e h p hp)
      · exact .inr (lamsArgs_body es h p hp)
end

/-- The lambdas of a grammar and a start expression are closed under taking bodies. -/
theorem lamsOf_closed (e : MExp) : LamsClosed (lamsOf g e) := by
  intro a b h p hp
  simp only [lamsOf, List.mem_append, List.mem_flatMap] at h ⊢
  rcases h with ⟨r, hr, h⟩ | h
  · exact .inl ⟨r, hr, lams_body _ h p hp⟩
  · exact .inr (lams_body _ h p hp)

theorem good_rule_lamsOf (e : MExp) {r : MRule} (hr : r ∈ g.rules) : Good (lamsOf g e) r.body := by
  intro p hp
  simp only [lamsOf, List.mem_append, List.mem_flatMap]
  exact .inl ⟨r, hr, hp⟩

theorem good_start_lamsOf (e : MExp) : Good (lamsOf g e) e := by
  intro p hp
  simp only [lamsOf, List.mem_append]
  exact .inr hp

/-- Every unit body is good. -/
theorem good_unitRule (hg : ∀ r ∈ g.rules, Good Λ r.body) (hΛ : LamsClosed Λ) (u : Nat) :
    Good Λ (unitRule g Λ u).body := by
  unfold unitRule
  split
  · rename_i hu
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hu, Option.getD_some]
    exact hg _ (List.getElem_mem hu)
  · split
    · rename_i a b h
      exact hΛ a b (List.mem_of_getElem? h)
    · intro p hp; simp [MExp.failAlways, MExp.lams] at hp

end

end Shallot.MacroPeg
