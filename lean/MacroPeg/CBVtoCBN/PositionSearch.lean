import MacroPeg.CBVtoCBN.LengthSearch

namespace Shallot.MacroPeg.CBVtoCBN

/-- A fixed list of parameter references; these hold the enclosing activation's context. -/
def paramsFrom (start : Nat) : Nat → List MExp
  | 0 => []
  | n + 1 => .param start :: paramsFrom (start + 1) n

theorem paramsFrom_firstOrder (start n : Nat) : MExp.FirstOrderArgs (paramsFrom start n) := by
  induction n generalizing start with
  | zero => trivial
  | succ n ih => exact ⟨trivial, ih (start + 1)⟩

theorem subst_paramsFrom_cons (a : MExp) (args : List MExp) (start n : Nat) :
    MExp.substArgs (a :: args) (paramsFrom (start + 1) n) =
      MExp.substArgs args (paramsFrom start n) := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
    simp only [paramsFrom, MExp.substArgs, MExp.subst, argAt]
    rw [ih]

theorem subst_paramsFrom (args : List MExp) :
    MExp.substArgs args (paramsFrom 0 args.length) = args := by
  induction args with
  | nil => rfl
  | cons a args ih =>
    simp only [List.length_cons, paramsFrom, MExp.substArgs, MExp.subst, argAt]
    rw [subst_paramsFrom_cons, ih]

/-- Try each logical input position while retaining a fixed tuple of captured context arguments.
The candidate rule is static, so the construction stays first-order. -/
def anyPositionBody (self test ctxSize : Nat) : MExp :=
  .alt (.call test (.param 0 :: paramsFrom 1 ctxSize))
    (ifP (exactLengthP (.param 0)) MExp.failAlways
      (.call self (.seq (.param 0) .any :: paramsFrom 1 ctxSize)))

theorem anyPositionBody_firstOrder (self test ctxSize : Nat) :
    (anyPositionBody self test ctxSize).FirstOrder := by
  exact ⟨⟨trivial, paramsFrom_firstOrder 1 ctxSize⟩,
    ifP_firstOrder ⟨trivial, trivial⟩ trivial
      ⟨⟨trivial, trivial⟩, paramsFrom_firstOrder 1 ctxSize⟩⟩

theorem anyPositionBody_subst (self test : Nat) (counter : MExp) (ctx : List MExp) :
    MExp.subst (counter :: ctx) (anyPositionBody self test ctx.length) =
      .alt (.call test (counter :: ctx))
        (ifP (exactLengthP counter) MExp.failAlways
          (.call self (.seq counter .any :: ctx))) := by
  simp [anyPositionBody, ifP, exactLengthP, andP, MExp.subst, MExp.substArgs,
    MExp.failAlways, argAt, subst_paramsFrom_cons, subst_paramsFrom]

/-- One search step, including its finite failing endpoint. -/
theorem anyPosition_step {g : MGrammar} {self test : Nat} (ctx : List MExp)
    (hr : ruleAtM g.rules self = some ⟨ctx.length + 1, anyPositionBody self test ctx.length⟩)
    (x : List Char) (k : Nat) (r : Option (List Char)) :
    MacroObs g (.call self (skipN k :: ctx)) x r ↔
      MacroObs g (.alt (.call test (skipN k :: ctx))
        (if k = x.length then MExp.failAlways else .call self (skipN (k + 1) :: ctx))) x r := by
  rw [obs_call_iff hr (by simp), anyPositionBody_subst]
  have ht := exactLength_obs (skipN_rep g k) x
  by_cases he : k = x.length
  · rw [if_pos he] at ht ⊢
    have hf : MacroObs g MExp.failAlways x none := obs_not_some (obs_eps x)
    have hi : MacroObs g (ifP (exactLengthP (skipN k)) MExp.failAlways
        (.call self (.seq (skipN k) .any :: ctx))) x none := (ifP_true_iff ht none).mpr hf
    rw [alt_fail_right_iff hi, alt_fail_right_iff hf]
  · rw [if_neg he] at ht ⊢
    rw [obs_alt_iff, obs_alt_iff, ifP_false_iff ht r]
    rfl

open Classical in
/-- A total candidate predicate makes existential search total too. Candidates may depend on
all captured context arguments; they inspect the unchanged original input. -/
theorem anyPosition_obs {g : MGrammar} {self test : Nat} (ctx : List MExp)
    (hr : ruleAtM g.rules self = some ⟨ctx.length + 1, anyPositionBody self test ctx.length⟩)
    (x : List Char) (P : Nat → Prop) [DecidablePred P]
    (ht : ∀ k, k ≤ x.length → MacroObs g (.call test (skipN k :: ctx)) x
      (if P k then some x else none)) (k : Nat) (hk : k ≤ x.length) :
    MacroObs g (.call self (skipN k :: ctx)) x
      (if ∃ j, k ≤ j ∧ j ≤ x.length ∧ P j then some x else none) := by
  classical
  have aux : ∀ d k, k + d = x.length →
      MacroObs g (.call self (skipN k :: ctx)) x
        (if ∃ j, k ≤ j ∧ j ≤ x.length ∧ P j then some x else none) := by
    intro d
    induction d with
    | zero =>
      intro k he
      have hn : k = x.length := by omega
      have hex : (∃ j, k ≤ j ∧ j ≤ x.length ∧ P j) ↔ P k := by
        constructor
        · rintro ⟨j, hj, hjn, hp⟩
          have : j = k := by omega
          simpa [this] using hp
        · intro hp; exact ⟨k, Nat.le_refl _, by omega, hp⟩
      apply (anyPosition_step ctx hr x k _).mpr
      have hf : MacroObs g MExp.failAlways x none := obs_not_some (obs_eps x)
      rw [if_pos hn, alt_fail_right_iff hf]
      simpa only [hex] using ht k (by omega)
    | succ d ih =>
      intro k he
      have hn : k ≠ x.length := by omega
      apply (anyPosition_step ctx hr x k _).mpr
      rw [if_neg hn]
      by_cases hp : P k
      · have hex : ∃ j, k ≤ j ∧ j ≤ x.length ∧ P j := ⟨k, Nat.le_refl _, by omega, hp⟩
        rw [if_pos hex]
        exact obs_alt_some (by simpa only [if_pos hp] using ht k (by omega))
      · have hex : (∃ j, k ≤ j ∧ j ≤ x.length ∧ P j) ↔
            ∃ j, k + 1 ≤ j ∧ j ≤ x.length ∧ P j := by
          constructor
          · rintro ⟨j, hj, hjn, hpj⟩
            have hjne : j ≠ k := fun heq => hp (heq ▸ hpj)
            exact ⟨j, by omega, hjn, hpj⟩
          · rintro ⟨j, hj, hjn, hpj⟩; exact ⟨j, by omega, hjn, hpj⟩
        rw [alt_fail_left_iff (by simpa only [if_neg hp] using ht k (by omega)), hex]
        exact ih (k + 1) (by omega)
  exact aux (x.length - k) k (by omega)

end Shallot.MacroPeg.CBVtoCBN
