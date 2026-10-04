import MacroPeg.Properties.Specialize
import MacroPeg.Determinism

/-!
# Argument equivalence and substitution (instructions.md §6)

## The counterexample (§6.1)

`F(x) ← x "a" !.` with the arguments `"a"` and `"a" !.`: as standalone expressions they have the same whole-consumption
language (`{"a"}`), but on `"aa"` the call `F("a")` succeeds and `F("a" !.)` fails. Whole-consumption equivalence is
therefore not enough for substitution; observational equivalence `≈` (failure and remaining input) is what is needed.

## The theorem (§6.2)

Fix a grammar `G` whose rule bodies are first-order and pure (no `lam`, `callParam`, `invoke`, `dbg`), and call-by-name.
For a first-order pure `body` and argument environments `ρ`, `ρ'` of the same length with `ρ[i] ≈ ρ'[i]` for every `i`,
`subst ρ body ≈ subst ρ' body` (`subst_obsEquiv_of_argEquiv`).

The proof has two separate parts:

* **syntactic** (`sim_subst`, induction on the body): substituting pointwise-related argument lists into a first-order
  body gives related expressions, where `Sim` is "the same syntax, except at some positions holding observationally
  equivalent expressions";
* **derivation induction** (`sim_preserve`): related expressions have the same observations. Syntax alone is not enough
  here: a recursive call `call i as` steps to `subst as r.body`, a new pair of expressions that is again related only
  because `sim_subst` applies to the rule body.

The arguments need not be closed and need not be first-order themselves: they only ever occur at `Sim.leaf` positions,
which are handled by their observational equivalence alone.
-/

namespace Shallot.MacroPeg

/-! ## First-order pure expressions -/

mutual
  def MExp.FirstOrder : MExp → Prop
    | .call _ args => MExp.FirstOrderArgs args
    | .seq e₁ e₂ => MExp.FirstOrder e₁ ∧ MExp.FirstOrder e₂
    | .alt e₁ e₂ => MExp.FirstOrder e₁ ∧ MExp.FirstOrder e₂
    | .star e => MExp.FirstOrder e
    | .notP e => MExp.FirstOrder e
    | .dbg _ => False
    | .lam _ _ => False
    | .callParam _ _ => False
    | .invoke _ _ _ => False
    | .eps => True
    | .any => True
    | .chr _ => True
    | .range _ _ => True
    | .lit _ => True
    | .param _ => True

  def MExp.FirstOrderArgs : List MExp → Prop
    | [] => True
    | e :: es => MExp.FirstOrder e ∧ MExp.FirstOrderArgs es
end

/-- All rule bodies of `g` are first-order and pure. -/
def MGrammar.FirstOrder (g : MGrammar) : Prop := ∀ r ∈ g.rules, r.body.FirstOrder

/-! ## The relation -/

mutual
  /-- `Sim g m m'`: `m` and `m'` have the same syntax except at `leaf` positions, which hold observationally equivalent
  expressions (fixed `g`, call-by-name). -/
  inductive Sim (g : MGrammar) : MExp → MExp → Prop
    | leaf {a a' : MExp} : ObsEquiv g a a' → Sim g a a'
    | node {a a' : MExp} : SimS g a a' → Sim g a a'

  /-- One constructor of matching shape at the top, with related children. -/
  inductive SimS (g : MGrammar) : MExp → MExp → Prop
    | eps : SimS g .eps .eps
    | any : SimS g .any .any
    | chr (c : Char) : SimS g (.chr c) (.chr c)
    | range (lo hi : Char) : SimS g (.range lo hi) (.range lo hi)
    | lit (s : List Char) : SimS g (.lit s) (.lit s)
    | param (k : Nat) : SimS g (.param k) (.param k)
    | seq {a b a' b' : MExp} : Sim g a a' → Sim g b b' → SimS g (.seq a b) (.seq a' b')
    | alt {a b a' b' : MExp} : Sim g a a' → Sim g b b' → SimS g (.alt a b) (.alt a' b')
    | star {a a' : MExp} : Sim g a a' → SimS g (.star a) (.star a')
    | notP {a a' : MExp} : Sim g a a' → SimS g (.notP a) (.notP a')
    | call (i : Nat) {as as' : List MExp} : SimArgs g as as' → SimS g (.call i as) (.call i as')

  inductive SimArgs (g : MGrammar) : List MExp → List MExp → Prop
    | nil : SimArgs g [] []
    | cons {a a' : MExp} {as as' : List MExp} : Sim g a a' → SimArgs g as as' → SimArgs g (a :: as) (a' :: as')
end

theorem SimArgs.length_eq {g : MGrammar} : ∀ {as as' : List MExp}, SimArgs g as as' → as.length = as'.length
  | _, _, .nil => rfl
  | _, _, .cons _ h => by simp [SimArgs.length_eq h]

theorem SimArgs.argAt {g : MGrammar} : ∀ {as as' : List MExp}, SimArgs g as as' → ∀ k,
    (argAt as k = none ∧ argAt as' k = none) ∨ ∃ a a', argAt as k = some a ∧ argAt as' k = some a' ∧ Sim g a a'
  | _, _, .nil, _ => Or.inl ⟨rfl, rfl⟩
  | _, _, .cons h _, 0 => Or.inr ⟨_, _, rfl, rfl, h⟩
  | _, _, .cons _ hs, k + 1 => SimArgs.argAt hs k

theorem sim_failAlways (g : MGrammar) : Sim g MExp.failAlways MExp.failAlways := .node (.notP (.node .eps))

/-! ## Syntactic part: substitution -/

mutual
  theorem sim_subst {g : MGrammar} {σ σ' : List MExp} (hσ : SimArgs g σ σ') :
      ∀ (c : MExp), c.FirstOrder → Sim g (MExp.subst σ c) (MExp.subst σ' c)
    | .eps, _ => .node .eps
    | .any, _ => .node .any
    | .chr c, _ => .node (.chr c)
    | .range lo hi, _ => .node (.range lo hi)
    | .lit s, _ => .node (.lit s)
    | .param k, _ => by
      simp only [MExp.subst]
      rcases hσ.argAt k with ⟨h, h'⟩ | ⟨a, a', h, h', hs⟩
      · rw [h, h']; exact sim_failAlways g
      · rw [h, h']; exact hs
    | .call i ms, hc => .node (.call i (simArgs_subst hσ ms hc))
    | .seq a b, hc => .node (.seq (sim_subst hσ a hc.1) (sim_subst hσ b hc.2))
    | .alt a b, hc => .node (.alt (sim_subst hσ a hc.1) (sim_subst hσ b hc.2))
    | .star a, hc => .node (.star (sim_subst hσ a hc))
    | .notP a, hc => .node (.notP (sim_subst hσ a hc))
    | .dbg _, hc => absurd hc id
    | .lam _ _, hc => absurd hc id
    | .callParam _ _, hc => absurd hc id
    | .invoke _ _ _, hc => absurd hc id

  theorem simArgs_subst {g : MGrammar} {σ σ' : List MExp} (hσ : SimArgs g σ σ') :
      ∀ (ms : List MExp), MExp.FirstOrderArgs ms → SimArgs g (MExp.substArgs σ ms) (MExp.substArgs σ' ms)
    | [], _ => .nil
    | m :: ms, hc => .cons (sim_subst hσ m hc.1) (simArgs_subst hσ ms hc.2)
end

/-! ## Derivation part: simulation -/

/-- One step of the simulation: a related pair is either equivalent outright or matches at the top. -/
theorem sim_step {g : MGrammar} {a a' : MExp} {x : List Char} {o : MOutcome} (hs : Sim g a a')
    (hd : MDerives g .callByName a x o)
    (ih : ∀ m', SimS g a m' → ∃ o', MDerives g .callByName m' x o' ∧ o'.restOf = o.restOf) :
    ∃ o', MDerives g .callByName a' x o' ∧ o'.restOf = o.restOf := by
  cases hs with
  | leaf he => exact (he x o.restOf).1 ⟨o, hd, rfl⟩
  | node hs => exact ih _ hs

/-- Related expressions (matching at the top) have the same observations: from any derivation of `m` a derivation of
`m'` with the same failure / remaining input. -/
theorem sim_preserve {g : MGrammar} (hg : g.FirstOrder) {m : MExp} {x : List Char} {o : MOutcome}
    (h : MDerives g .callByName m x o) :
    ∀ m', SimS g m m' → ∃ o', MDerives g .callByName m' x o' ∧ o'.restOf = o.restOf := by
  induction h using MDerives.rec
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ => True)
  case eps input => intro m' hs; cases hs; exact ⟨_, .eps input, rfl⟩
  case anyOk c rest => intro m' hs; cases hs; exact ⟨_, .anyOk c rest, rfl⟩
  case anyFail => intro m' hs; cases hs; exact ⟨_, .anyFail, rfl⟩
  case chrOk c d rest hb => intro m' hs; cases hs; exact ⟨_, .chrOk c d rest hb, rfl⟩
  case chrFail c d rest hb => intro m' hs; cases hs; exact ⟨_, .chrFail c d rest hb, rfl⟩
  case chrEmpty c => intro m' hs; cases hs; exact ⟨_, .chrEmpty c, rfl⟩
  case rangeOk lo hi d rest hb => intro m' hs; cases hs; exact ⟨_, .rangeOk lo hi d rest hb, rfl⟩
  case rangeFail lo hi d rest hb => intro m' hs; cases hs; exact ⟨_, .rangeFail lo hi d rest hb, rfl⟩
  case rangeEmpty lo hi => intro m' hs; cases hs; exact ⟨_, .rangeEmpty lo hi, rfl⟩
  case litOk s input rest hb => intro m' hs; cases hs; exact ⟨_, .litOk s input rest hb, rfl⟩
  case litFail s input hb => intro m' hs; cases hs; exact ⟨_, .litFail s input hb, rfl⟩
  case paramFail k input => intro m' hs; cases hs; exact ⟨_, .paramFail k input, rfl⟩
  case callNameOk i args r input rest t _ hr ha hd ih =>
    intro m' hs
    cases hs with
    | call _ hargs =>
      obtain ⟨o', hd', ho'⟩ := sim_step (sim_subst hargs r.body (hg r (ruleAtM_mem hr))) hd ih
      obtain ⟨t', rfl⟩ := restOf_eq_some ho'
      exact ⟨_, .callNameOk i _ r input rest t' rfl hr (ha.trans hargs.length_eq) hd', rfl⟩
  case callNameFail i args r input _ hr ha hd ih =>
    intro m' hs
    cases hs with
    | call _ hargs =>
      obtain ⟨o', hd', ho'⟩ := sim_step (sim_subst hargs r.body (hg r (ruleAtM_mem hr))) hd ih
      have := restOf_eq_none ho'
      subst this
      exact ⟨_, .callNameFail i _ r input rfl hr (ha.trans hargs.length_eq) hd', rfl⟩
  case callMissing i args input hr =>
    intro m' hs; cases hs; exact ⟨_, .callMissing i _ input hr, rfl⟩
  case callArity i args r input hr ha =>
    intro m' hs
    cases hs with
    | call _ hargs => exact ⟨_, .callArity i _ r input hr (hargs.length_eq ▸ ha), rfl⟩
  case seqOk e₁ e₂ input rest₁ rest₂ t₁ t₂ h₁ h₂ ih₁ ih₂ =>
    intro m' hs
    cases hs with
    | seq hs₁ hs₂ =>
      obtain ⟨o₁, d₁, c₁⟩ := sim_step hs₁ h₁ ih₁
      obtain ⟨t₁', rfl⟩ := restOf_eq_some c₁
      obtain ⟨o₂, d₂, c₂⟩ := sim_step hs₂ h₂ ih₂
      obtain ⟨t₂', rfl⟩ := restOf_eq_some c₂
      exact ⟨_, .seqOk _ _ _ _ _ _ _ d₁ d₂, rfl⟩
  case seqFail₁ e₁ e₂ input h₁ ih₁ =>
    intro m' hs
    cases hs with
    | seq hs₁ _ =>
      obtain ⟨o₁, d₁, c₁⟩ := sim_step hs₁ h₁ ih₁
      have := restOf_eq_none c₁; subst this
      exact ⟨_, .seqFail₁ _ _ _ d₁, rfl⟩
  case seqFail₂ e₁ e₂ input rest₁ t₁ h₁ h₂ ih₁ ih₂ =>
    intro m' hs
    cases hs with
    | seq hs₁ hs₂ =>
      obtain ⟨o₁, d₁, c₁⟩ := sim_step hs₁ h₁ ih₁
      obtain ⟨t₁', rfl⟩ := restOf_eq_some c₁
      obtain ⟨o₂, d₂, c₂⟩ := sim_step hs₂ h₂ ih₂
      have := restOf_eq_none c₂; subst this
      exact ⟨_, .seqFail₂ _ _ _ _ _ d₁ d₂, rfl⟩
  case altL e₁ e₂ input rest t h₁ ih₁ =>
    intro m' hs
    cases hs with
    | alt hs₁ _ =>
      obtain ⟨o₁, d₁, c₁⟩ := sim_step hs₁ h₁ ih₁
      obtain ⟨t₁', rfl⟩ := restOf_eq_some c₁
      exact ⟨_, .altL _ _ _ _ _ d₁, rfl⟩
  case altR e₁ e₂ input rest t h₁ h₂ ih₁ ih₂ =>
    intro m' hs
    cases hs with
    | alt hs₁ hs₂ =>
      obtain ⟨o₁, d₁, c₁⟩ := sim_step hs₁ h₁ ih₁
      have := restOf_eq_none c₁; subst this
      obtain ⟨o₂, d₂, c₂⟩ := sim_step hs₂ h₂ ih₂
      obtain ⟨t₂', rfl⟩ := restOf_eq_some c₂
      exact ⟨_, .altR _ _ _ _ _ d₁ d₂, rfl⟩
  case altFail e₁ e₂ input h₁ h₂ ih₁ ih₂ =>
    intro m' hs
    cases hs with
    | alt hs₁ hs₂ =>
      obtain ⟨o₁, d₁, c₁⟩ := sim_step hs₁ h₁ ih₁
      have := restOf_eq_none c₁; subst this
      obtain ⟨o₂, d₂, c₂⟩ := sim_step hs₂ h₂ ih₂
      have := restOf_eq_none c₂; subst this
      exact ⟨_, .altFail _ _ _ d₁ d₂, rfl⟩
  case starNil e input h₁ ih₁ =>
    intro m' hs
    cases hs with
    | star hs₁ =>
      obtain ⟨o₁, d₁, c₁⟩ := sim_step hs₁ h₁ ih₁
      have := restOf_eq_none c₁; subst this
      exact ⟨_, .starNil _ _ d₁, rfl⟩
  case starCons e input rest rest' t ts h₁ _ ih₁ ih₂ =>
    intro m' hs
    cases hs with
    | star hs₁ =>
      obtain ⟨o₁, d₁, c₁⟩ := sim_step hs₁ h₁ ih₁
      obtain ⟨t₁', rfl⟩ := restOf_eq_some c₁
      obtain ⟨o₂, d₂, c₂⟩ := ih₂ _ (.star hs₁)
      obtain ⟨t₂', rfl⟩ := restOf_eq_some c₂
      exact ⟨_, .starCons _ _ _ _ _ _ d₁ d₂, rfl⟩
  case notOk e input rest t h₁ ih₁ =>
    intro m' hs
    cases hs with
    | notP hs₁ =>
      obtain ⟨o₁, d₁, c₁⟩ := sim_step hs₁ h₁ ih₁
      obtain ⟨t₁', rfl⟩ := restOf_eq_some c₁
      exact ⟨_, .notOk _ _ _ _ d₁, rfl⟩
  case notFail e input h₁ ih₁ =>
    intro m' hs
    cases hs with
    | notP hs₁ =>
      obtain ⟨o₁, d₁, c₁⟩ := sim_step hs₁ h₁ ih₁
      have := restOf_eq_none c₁; subst this
      exact ⟨_, .notFail _ _ d₁, rfl⟩
  all_goals first
    | trivial
    | (intro m' hs; cases hs; done)
    | (intro m' hs; contradiction)

theorem sim_obs {g : MGrammar} (hg : g.FirstOrder) {m m' : MExp} (hs : Sim g m m') {x : List Char}
    {r : Option (List Char)} (h : MacroObs g m x r) : MacroObs g m' x r := by
  obtain ⟨o, hd, rfl⟩ := h
  obtain ⟨o', hd', ho'⟩ := sim_step hs hd (fun m' hs' => sim_preserve hg hd m' hs')
  exact ⟨o', hd', ho'⟩

/-- Pointwise equivalent argument lists of the same length are related. -/
theorem simArgs_of_pointwise {g : MGrammar} :
    ∀ {ρ ρ' : List MExp}, ρ.length = ρ'.length →
      (∀ (i : Nat) a a', ρ[i]? = some a → ρ'[i]? = some a' → ObsEquiv g a a') → SimArgs g ρ ρ'
  | [], [], _, _ => .nil
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl
  | a :: ρ, a' :: ρ', hl, h =>
    .cons (.leaf (h 0 a a' rfl rfl))
      (simArgs_of_pointwise (by simpa using hl) (fun i b b' hb hb' => h (i + 1) b b' hb hb'))

/-- **§6.2.** Fixed `g` (first-order, pure rule bodies), call-by-name: argument environments of the same length that are
pointwise observationally equivalent give observationally equivalent substituted bodies, for every first-order pure
`body`. -/
theorem subst_obsEquiv_general {g : MGrammar} (hg : g.FirstOrder) {body : MExp} (hb : body.FirstOrder)
    {ρ ρ' : List MExp} (hl : ρ.length = ρ'.length)
    (h : ∀ (i : Nat) a a', ρ[i]? = some a → ρ'[i]? = some a' → ObsEquiv g a a') :
    ObsEquiv g (MExp.subst ρ body) (MExp.subst ρ' body) := by
  intro x r
  constructor
  · exact sim_obs hg (sim_subst (simArgs_of_pointwise hl h) body hb)
  · exact sim_obs hg (sim_subst (simArgs_of_pointwise hl.symm (fun i a' a h' h'' => obsEquiv_symm (h i a a' h'' h')))
      body hb)

/- Every parameter index of an expression is below `n` (the scope condition of §6.2). -/
mutual
  def MExp.ParamsBelow (n : Nat) : MExp → Prop
    | .param k => k < n
    | .call _ args => MExp.ParamsBelowArgs n args
    | .seq e₁ e₂ => MExp.ParamsBelow n e₁ ∧ MExp.ParamsBelow n e₂
    | .alt e₁ e₂ => MExp.ParamsBelow n e₁ ∧ MExp.ParamsBelow n e₂
    | .star e => MExp.ParamsBelow n e
    | .notP e => MExp.ParamsBelow n e
    | .dbg e => MExp.ParamsBelow n e
    | .lam _ _ => True
    | .callParam k args => k < n ∧ MExp.ParamsBelowArgs n args
    | .invoke _ _ args => MExp.ParamsBelowArgs n args
    | .eps | .any | .chr _ | .range _ _ | .lit _ => True

  def MExp.ParamsBelowArgs (n : Nat) : List MExp → Prop
    | [] => True
    | e :: es => MExp.ParamsBelow n e ∧ MExp.ParamsBelowArgs n es
end

/-- §6.2 in the form of the brief, with the scope condition `body`'s parameters `< |ρ|`. The proof does not use the
scope condition (`subst_obsEquiv_general`): an out-of-range parameter becomes the same `failAlways` on both sides.
It is kept in this statement so that the result is read without relying on that fallback. -/
theorem subst_obsEquiv_of_argEquiv {g : MGrammar} (hg : g.FirstOrder) {body : MExp} (hb : body.FirstOrder)
    {ρ ρ' : List MExp} (_hscope : body.ParamsBelow ρ.length) (hl : ρ.length = ρ'.length)
    (h : ∀ (i : Nat) a a', ρ[i]? = some a → ρ'[i]? = some a' → ObsEquiv g a a') :
    ObsEquiv g (MExp.subst ρ body) (MExp.subst ρ' body) :=
  subst_obsEquiv_general hg hb hl h

/-! ## The counterexample of §6.1 -/

/-- `F(x) ← x "a" !.` -/
def ceG : MGrammar := ⟨[⟨1, .seq (.param 0) (.seq (.lit ['a']) (.notP .any))⟩]⟩

def argA : MExp := .lit ['a']
def argAEnd : MExp := .seq (.lit ['a']) (.notP .any)

theorem ceG_firstOrder : ceG.FirstOrder := by
  intro r hr
  simp only [ceG, List.mem_singleton] at hr
  subst hr
  exact ⟨trivial, trivial, trivial⟩

theorem stripPrefix_a {x : List Char} (h : Shallot.stripPrefix? ['a'] x = some []) : x = ['a'] := by
  match x, h with
  | c :: cs, h =>
    simp only [Shallot.stripPrefix?] at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h
      rw [h, ← Shallot.beqChar_eq hc]
    · cases h

/-- `"a"` consumes all of `x` iff `x = "a"`. -/
theorem argA_recognizesAll (x : List Char) : MRecognizesAll ceG argA x ↔ x = ['a'] := by
  constructor
  · rintro ⟨o, hd, ho⟩
    cases hd with
    | litOk _ _ rest hs =>
      simp only [MOutcome.restOf, Option.some.injEq] at ho
      subst ho
      exact stripPrefix_a hs
    | litFail _ _ _ => cases ho
  · rintro rfl
    exact ⟨_, .litOk ['a'] ['a'] [] (by decide), rfl⟩

/-- `"a" !.` consumes all of `x` iff `x = "a"`: the same whole-consumption language as `"a"`. -/
theorem argAEnd_recognizesAll (x : List Char) : MRecognizesAll ceG argAEnd x ↔ x = ['a'] := by
  constructor
  · rintro ⟨o, hd, ho⟩
    cases hd with
    | seqOk _ _ _ rest₁ rest₂ _ _ h₁ h₂ =>
      simp only [MOutcome.restOf, Option.some.injEq] at ho
      subst ho
      cases h₂ with
      | notFail _ _ _ =>
        cases h₁ with
        | litOk _ _ _ hs => exact stripPrefix_a hs
    | seqFail₁ _ _ _ _ => cases ho
    | seqFail₂ _ _ _ _ _ _ _ => cases ho
  · rintro rfl
    exact ⟨_, .seqOk _ _ _ [] [] _ _ (.litOk ['a'] ['a'] [] (by decide)) (.notFail _ _ .anyFail), rfl⟩

theorem same_recognizesAll (x : List Char) : MRecognizesAll ceG argA x ↔ MRecognizesAll ceG argAEnd x := by
  rw [argA_recognizesAll, argAEnd_recognizesAll]

/-- `F("a")` succeeds on `"aa"`, consuming everything. -/
theorem ce_call_argA : MDerives ceG .callByName (.call 0 [argA]) ['a', 'a']
    (.ok (.nodeCall 0 (.seq (.leaf ['a']) (.seq (.leaf ['a']) .notT))) []) :=
  .callNameOk 0 [argA] _ _ _ _ rfl rfl rfl
    (.seqOk _ _ _ ['a'] [] _ _ (.litOk ['a'] _ ['a'] (by decide))
      (.seqOk _ _ _ [] [] _ _ (.litOk ['a'] _ [] (by decide)) (.notFail _ _ .anyFail)))

/-- `F("a" !.)` fails on `"aa"`: the argument `"a" !.` already fails at the first `"a"`. -/
theorem ce_call_argAEnd : MDerives ceG .callByName (.call 0 [argAEnd]) ['a', 'a'] .fail :=
  .callNameFail 0 [argAEnd] _ _ rfl rfl rfl
    (.seqFail₁ _ _ _ (.seqFail₂ _ _ _ ['a'] _ (.litOk ['a'] _ ['a'] (by decide))
      (.notOk _ _ [] _ (.anyOk 'a' []))))

/-- Hence `F("a" !.)` has no success observation on `"aa"` (determinism), while `F("a")` does. -/
theorem ce_not_accepts : ¬ MAccepts ceG (.call 0 [argAEnd]) ['a', 'a'] := by
  rintro ⟨rest, o, hd, ho⟩
  have := mderives_det hd ce_call_argAEnd
  subst this
  cases ho

theorem ce_accepts : MRecognizesAll ceG (.call 0 [argA]) ['a', 'a'] := ⟨_, ce_call_argA, rfl⟩

/-- So the two arguments are not observationally equivalent (as the theorem would otherwise force equal call results):
on `"aa"`, `"a"` leaves `"a"` and `"a" !.` fails. -/
theorem argA_not_equiv_argAEnd : ¬ ObsEquiv ceG argA argAEnd := by
  intro h
  have hA : MacroObs ceG argA ['a', 'a'] (some ['a']) := ⟨_, .litOk ['a'] _ ['a'] (by decide), rfl⟩
  obtain ⟨o, hd, ho⟩ := (h _ _).1 hA
  have := mderives_det hd (.seqFail₂ _ _ _ ['a'] _ (.litOk ['a'] _ ['a'] (by decide))
    (.notOk _ _ [] _ (.anyOk 'a' [])))
  subst this
  cases ho

end Shallot.MacroPeg
