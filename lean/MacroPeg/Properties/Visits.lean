import MacroPeg.Properties.Observation
import MacroPeg.Determinism

/-!
# What a call-by-name evaluator evaluates

`Visits g e x e' x'`: evaluating `e` on `x` under call-by-name evaluates `e'` on `x'`. It follows the evaluation order
of the derivation rules: a sequence evaluates its second part only after the first succeeded (at the remaining input), a
choice evaluates its second alternative only after the first failed, `star` repeats after each success, a negative
lookahead evaluates its body, and a call evaluates the substituted rule body at the same position (call-by-name: the
actual arguments are not evaluated at the call). The earlier parts' results are given by finite derivations; the whole
evaluation is not required to terminate.

This is the set of judgments a memoizing (packrat) call-by-name evaluator would put in its table. `visits_suffix`: every
visited position is a suffix of the input. `visits_derivable`: if the whole evaluation has a finite derivation, every
visited judgment has one, so each table entry gets a finite result.
-/

namespace Shallot.MacroPeg

inductive Visits (g : MGrammar) : MExp → List Char → MExp → List Char → Prop
  | self (e : MExp) (x : List Char) : Visits g e x e x
  | seqL {a b : MExp} {x : List Char} {e' : MExp} {x' : List Char} :
      Visits g a x e' x' → Visits g (.seq a b) x e' x'
  | seqR {a b : MExp} {x : List Char} {t : MTree} {r : List Char} {e' : MExp} {x' : List Char} :
      MDerives g .callByName a x (.ok t r) → Visits g b r e' x' → Visits g (.seq a b) x e' x'
  | altL {a b : MExp} {x : List Char} {e' : MExp} {x' : List Char} :
      Visits g a x e' x' → Visits g (.alt a b) x e' x'
  | altR {a b : MExp} {x : List Char} {e' : MExp} {x' : List Char} :
      MDerives g .callByName a x .fail → Visits g b x e' x' → Visits g (.alt a b) x e' x'
  | star {a : MExp} {x : List Char} {e' : MExp} {x' : List Char} :
      Visits g a x e' x' → Visits g (.star a) x e' x'
  | starR {a : MExp} {x : List Char} {t : MTree} {r : List Char} {e' : MExp} {x' : List Char} :
      MDerives g .callByName a x (.ok t r) → Visits g (.star a) r e' x' → Visits g (.star a) x e' x'
  | notP {a : MExp} {x : List Char} {e' : MExp} {x' : List Char} :
      Visits g a x e' x' → Visits g (.notP a) x e' x'
  | call {i : Nat} {args : List MExp} {r : MRule} {x : List Char} {e' : MExp} {x' : List Char} :
      ruleAtM g.rules i = some r → r.arity = args.length →
      Visits g (MExp.subst args r.body) x e' x' → Visits g (.call i args) x e' x'

theorem Visits.trans {g : MGrammar} {e e₁ e₂ : MExp} {x x₁ x₂ : List Char} (h₁ : Visits g e x e₁ x₁)
    (h₂ : Visits g e₁ x₁ e₂ x₂) : Visits g e x e₂ x₂ := by
  induction h₁ with
  | self => exact h₂
  | seqL _ ih => exact .seqL (ih h₂)
  | seqR ha _ ih => exact .seqR ha (ih h₂)
  | altL _ ih => exact .altL (ih h₂)
  | altR ha _ ih => exact .altR ha (ih h₂)
  | star _ ih => exact .star (ih h₂)
  | starR ha _ ih => exact .starR ha (ih h₂)
  | notP _ ih => exact .notP (ih h₂)
  | call hr ha _ ih => exact .call hr ha (ih h₂)

/-- Every visited position is a suffix of the input. -/
theorem visits_suffix {g : MGrammar} {e e' : MExp} {x x' : List Char} (h : Visits g e x e' x') :
    ∃ p, x = p ++ x' := by
  induction h with
  | self => exact ⟨[], rfl⟩
  | seqL _ ih | altL _ ih | altR _ _ ih | star _ ih | notP _ ih | call _ _ _ ih => exact ih
  | seqR ha _ ih | starR ha _ ih =>
    obtain ⟨p, hp⟩ := mderives_suffix ha _ _ rfl
    obtain ⟨q, hq⟩ := ih
    exact ⟨p ++ q, by rw [hp, hq, List.append_assoc]⟩

/-- A call-by-name derivation of a call of an existing rule with matching arity contains one of the substituted body. -/
theorem cbn_call_body {g : MGrammar} {i : Nat} {args : List MExp} {r : MRule} {x : List Char} {o : MOutcome}
    (hd : MDerives g .callByName (.call i args) x o) (hr : ruleAtM g.rules i = some r)
    (ha : r.arity = args.length) : ∃ o', MDerives g .callByName (MExp.subst args r.body) x o' := by
  generalize he : MExp.call i args = E at hd
  cases hd with
  | callNameOk _ _ r' _ _ _ _ hr' _ hb =>
    cases he; rw [hr] at hr'; cases hr'; exact ⟨_, hb⟩
  | callNameFail _ _ r' _ _ hr' _ hb =>
    cases he; rw [hr] at hr'; cases hr'; exact ⟨_, hb⟩
  | callParOk _ _ _ _ _ _ _ hs => cases hs
  | callParFail _ _ _ _ _ hs => cases hs
  | callParArgFail _ _ _ _ _ _ _ hs => cases hs
  | callSeqOk _ _ _ _ _ _ _ _ hs => cases hs
  | callSeqFail _ _ _ _ _ _ hs => cases hs
  | callSeqArgFail _ _ _ _ _ _ _ _ hs => cases hs
  | callMissing _ _ _ hr' => cases he; rw [hr] at hr'; cases hr'
  | callArity _ _ r' _ hr' ha' => cases he; rw [hr] at hr'; cases hr'; exact absurd ha ha'
  | _ => cases he

/-- If the whole evaluation has a finite derivation, so does every judgment it visits. -/
theorem visits_derivable {g : MGrammar} {e e' : MExp} {x x' : List Char} (h : Visits g e x e' x') :
    (∃ o, MDerives g .callByName e x o) → ∃ o', MDerives g .callByName e' x' o' := by
  induction h with
  | self => exact id
  | seqL _ ih =>
    rintro ⟨o, hd⟩
    cases hd with
    | seqOk _ _ _ _ _ _ _ h₁ _ => exact ih ⟨_, h₁⟩
    | seqFail₁ _ _ _ h₁ => exact ih ⟨_, h₁⟩
    | seqFail₂ _ _ _ _ _ h₁ _ => exact ih ⟨_, h₁⟩
  | seqR ha _ ih =>
    rintro ⟨o, hd⟩
    cases hd with
    | seqOk _ _ _ _ _ _ _ h₁ h₂ =>
      have := mderives_det ha h₁; cases this; exact ih ⟨_, h₂⟩
    | seqFail₁ _ _ _ h₁ => have := mderives_det ha h₁; cases this
    | seqFail₂ _ _ _ _ _ h₁ h₂ =>
      have := mderives_det ha h₁; cases this; exact ih ⟨_, h₂⟩
  | altL _ ih =>
    rintro ⟨o, hd⟩
    cases hd with
    | altL _ _ _ _ _ h₁ => exact ih ⟨_, h₁⟩
    | altR _ _ _ _ _ h₁ _ => exact ih ⟨_, h₁⟩
    | altFail _ _ _ h₁ _ => exact ih ⟨_, h₁⟩
  | altR ha _ ih =>
    rintro ⟨o, hd⟩
    cases hd with
    | altL _ _ _ _ _ h₁ => have := mderives_det ha h₁; cases this
    | altR _ _ _ _ _ _ h₂ => exact ih ⟨_, h₂⟩
    | altFail _ _ _ _ h₂ => exact ih ⟨_, h₂⟩
  | star _ ih =>
    rintro ⟨o, hd⟩
    cases hd with
    | starNil _ _ h₁ => exact ih ⟨_, h₁⟩
    | starCons _ _ _ _ _ _ h₁ _ => exact ih ⟨_, h₁⟩
  | starR ha _ ih =>
    rintro ⟨o, hd⟩
    cases hd with
    | starNil _ _ h₁ => have := mderives_det ha h₁; cases this
    | starCons _ _ _ _ _ _ h₁ h₂ =>
      have := mderives_det ha h₁; cases this; exact ih ⟨_, h₂⟩
  | notP _ ih =>
    rintro ⟨o, hd⟩
    cases hd with
    | notOk _ _ _ _ h₁ => exact ih ⟨_, h₁⟩
    | notFail _ _ h₁ => exact ih ⟨_, h₁⟩
  | call hr ha _ ih =>
    rintro ⟨o, hd⟩
    exact ih (cbn_call_body hd hr ha)

end Shallot.MacroPeg
