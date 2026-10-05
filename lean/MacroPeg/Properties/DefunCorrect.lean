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

/-! ## One step of a call-by-name run, seen through its observation

`runObs` forgets the parse tree. Each lemma below unfolds one step of `mpegRun` and says what the observation is in
terms of the observations of the sub-runs; they hold for every grammar. -/

/-- The observation of a run: `none` = out of fuel, `some none` = failure, `some (some r)` = success leaving `r`. -/
def runObs (o : Option MOutcome) : Option (Option (List Char)) := o.map MOutcome.restOf

section Steps

variable {G : MGrammar} {n : Nat} {x : List Char}

local notation "run" => mpegRun G Strategy.callByName

theorem obs_seq (a b : MExp) : runObs (run (n + 1) (.seq a b) x) =
    match runObs (run n a x) with
    | some (some r) => runObs (run n b r)
    | some none => some none
    | none => none := by
  rw [mpegRun.eq_def]; dsimp only
  cases run n a x with
  | none => rfl
  | some o => cases o with
    | fail => rfl
    | ok t r => dsimp only [runObs, Option.map, MOutcome.restOf]; cases run n b r with
      | none => rfl
      | some o => cases o <;> rfl

theorem obs_alt (a b : MExp) : runObs (run (n + 1) (.alt a b) x) =
    match runObs (run n a x) with
    | some (some r) => some (some r)
    | some none => runObs (run n b x)
    | none => none := by
  rw [mpegRun.eq_def]; dsimp only
  cases run n a x with
  | none => rfl
  | some o => cases o with
    | ok t r => rfl
    | fail => dsimp only [runObs, Option.map, MOutcome.restOf]; cases run n b x with
      | none => rfl
      | some o => cases o <;> rfl

theorem obs_star (a : MExp) : runObs (run (n + 1) (.star a) x) =
    match runObs (run n a x) with
    | some (some r) => runObs (run n (.star a) r)
    | some none => some (some x)
    | none => none := by
  rw [mpegRun.eq_def]; dsimp only
  cases run n a x with
  | none => rfl
  | some o => cases o with
    | fail => rfl
    | ok t r => dsimp only [runObs, Option.map, MOutcome.restOf]; cases run n (.star a) r with
      | none => rfl
      | some o => cases o <;> rfl

theorem obs_notP (a : MExp) : runObs (run (n + 1) (.notP a) x) =
    match runObs (run n a x) with
    | some (some _) => some none
    | some none => some (some x)
    | none => none := by
  rw [mpegRun.eq_def]; dsimp only
  cases run n a x with
  | none => rfl
  | some o => cases o <;> rfl

theorem obs_call {i : Nat} {args : List MExp} {r : MRule} (hr : ruleAtM G.rules i = some r)
    (ha : r.arity = args.length) :
    runObs (run (n + 1) (.call i args) x) = runObs (run n (MExp.subst args r.body) x) := by
  rw [mpegRun.eq_def]; dsimp only
  simp only [hr, ha, beq_self_eq_true, ↓reduceIte]
  cases run n (MExp.subst args r.body) x with
  | none => rfl
  | some o => cases o <;> rfl

theorem obs_call_missing {i : Nat} {args : List MExp} (hr : ruleAtM G.rules i = none) :
    runObs (run (n + 1) (.call i args) x) = some none := by
  rw [mpegRun.eq_def]; dsimp only; simp only [hr]; rfl

theorem obs_call_arity {i : Nat} {args : List MExp} {r : MRule} (hr : ruleAtM G.rules i = some r)
    (ha : r.arity ≠ args.length) : runObs (run (n + 1) (.call i args) x) = some none := by
  rw [mpegRun.eq_def]; dsimp only
  simp only [hr, beq_iff_eq, ha, ↓reduceIte]; rfl

theorem obs_invoke {a : Nat} {b : MExp} {args : List MExp} (ha : a = args.length) :
    runObs (run (n + 1) (.invoke a b args) x) = runObs (run n (MExp.subst args b) x) := by
  rw [mpegRun.eq_def]; dsimp only
  simp only [ha, beq_self_eq_true, ↓reduceIte]
  cases run n (MExp.subst args b) x with
  | none => rfl
  | some o => cases o <;> rfl

theorem obs_invoke_arity {a : Nat} {b : MExp} {args : List MExp} (ha : a ≠ args.length) :
    runObs (run (n + 1) (.invoke a b args) x) = some none := by
  rw [mpegRun.eq_def]; dsimp only
  simp only [beq_iff_eq, ha, ↓reduceIte]; rfl

theorem obs_failAlways : runObs (run (n + 2) MExp.failAlways x) = some none := by
  unfold MExp.failAlways
  rw [mpegRun.eq_def]; dsimp only; rw [mpegRun.eq_def]; rfl

theorem obs_eps : runObs (run (n + 1) .eps x) = some (some x) := by rw [mpegRun.eq_def]; rfl
theorem obs_lam (a : Nat) (b : MExp) : runObs (run (n + 1) (.lam a b) x) = some (some x) := by
  rw [mpegRun.eq_def]; rfl
theorem obs_dbg (b : MExp) : runObs (run (n + 1) (.dbg b) x) = some (some x) := by rw [mpegRun.eq_def]; rfl
theorem obs_param (k : Nat) : runObs (run (n + 1) (.param k) x) = some none := by rw [mpegRun.eq_def]; rfl
theorem obs_callParam (k : Nat) (m : List MExp) : runObs (run (n + 1) (.callParam k m) x) = some none := by
  rw [mpegRun.eq_def]; rfl

/-- Whatever `failAlways` returns is a failure. -/
theorem obs_failAlways_eq {r : Option (List Char)} (h : runObs (run (n + 1) MExp.failAlways x) = some r) :
    r = none := by
  cases n with
  | zero => unfold MExp.failAlways at h; rw [mpegRun.eq_def] at h; dsimp only at h; rw [mpegRun.eq_def] at h; cases h
  | succ n => rw [obs_failAlways] at h; cases h; rfl

end Steps

/-! ## The rules of the first-order grammar -/

section Rules

variable {g : MGrammar} {Λ : List (Nat × MExp)}

theorem indexIn_lt {α : Type} [DecidableEq α] {a : α} {l : List α} (h : a ∈ l) : indexIn a l < l.length :=
  (List.getElem?_eq_some_iff.1 (getElem?_indexIn a l h)).1

/-- A tag computed in a closed scope names a lambda of `Λ` or none. -/
theorem tagOf_nil_lt (a : MExp) : tagOf Λ [] a < Λ.length + 1 := by
  unfold tagOf; split
  · simp
  · split
    · have := indexIn_lt (by assumption); omega
    · omega
  · omega

theorem tagsOf_mem_vecs {args : List MExp} {m : Nat} (ha : m = args.length) :
    tagsOf Λ [] args ∈ vecs (Λ.length + 1) m := by
  refine (mem_vecs _ _ _).2 ⟨by simp [tagsOf, ha], fun k hk => ?_⟩
  simp only [tagsOf, List.mem_map] at hk
  obtain ⟨a, _, rfl⟩ := hk
  exact tagOf_nil_lt a

/-- The first-order grammar has the specialized body for every spec. -/
theorem ruleAt_defun {u : Nat} {v : List Nat} (hu : u < g.rules.length + Λ.length)
    (hv : v ∈ vecs (Λ.length + 1) (unitRule g Λ u).arity) :
    ruleAtM (defunGrammar g Λ).rules (specCode g Λ u v) =
      some ⟨(unitRule g Λ u).arity, tr g Λ v (unitRule g Λ u).body⟩ := by
  have hmem : (u, v) ∈ specsOf g Λ := by
    simp only [specsOf, List.mem_flatMap, List.mem_range, List.mem_map]
    exact ⟨u, hu, v, hv, rfl⟩
  rw [ruleAtM_eq_getElem?, defunGrammar, List.getElem?_map, specCode, getElem?_indexIn _ _ hmem]
  rfl

theorem unitRule_rule {i : Nat} {r : MRule} (hr : ruleAtM g.rules i = some r) :
    i < g.rules.length ∧ unitRule g Λ i = r := by
  rw [ruleAtM_eq_getElem?] at hr
  obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.1 hr
  refine ⟨hi, ?_⟩
  simp only [unitRule, hi, ↓reduceIte, List.getD_eq_getElem?_getD, hr, Option.getD_some]

theorem ruleAtM_none_iff {i : Nat} : ruleAtM g.rules i = none ↔ ¬ i < g.rules.length := by
  rw [ruleAtM_eq_getElem?, List.getElem?_eq_none_iff]; omega

theorem unitRule_lam {a : Nat} {b : MExp} (h : (a, b) ∈ Λ) :
    unitRule g Λ (g.rules.length + indexIn (a, b) Λ) = ⟨a, b⟩ := by
  simp only [unitRule, Nat.add_sub_cancel_left, getElem?_indexIn _ _ h]
  simp only [ite_eq_right_iff]
  intro hlt; omega

/-- One step of a translated unit call. -/
theorem obs_callUnit {n : Nat} {x : List Char} {u : Nat} {args : List MExp} (hu : u < g.rules.length + Λ.length) :
    runObs (mpegRun (defunGrammar g Λ) .callByName (n + 1) (callUnit g Λ [] u args (trArgs g Λ [] args)) x) =
      if (unitRule g Λ u).arity = args.length then
        runObs (mpegRun (defunGrammar g Λ) .callByName n (tr g Λ [] (MExp.subst args (unitRule g Λ u).body)) x)
      else runObs (mpegRun (defunGrammar g Λ) .callByName (n + 1) MExp.failAlways x) := by
  unfold callUnit
  split
  · rename_i ha
    rw [obs_call (ruleAt_defun hu (tagsOf_mem_vecs ha)) (by simp [trArgs_eq_map, ha]),
      tr_subst]
  · rfl

end Rules

end Shallot.MacroPeg
