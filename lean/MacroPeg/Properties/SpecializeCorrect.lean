import MacroPeg.Properties.Specialize

/-!
# Correctness of finite specialization (instructions.md §5.3, §5.5, §5.6)

The proof relates Macro PEG expressions to plain PEG expressions by `Rel F`: the same PEG combinators on both sides, plus
two kinds of references,

* `envRef i`: the macro call `call i []` of an env rule and the plain `.nt i`;
* `specRef B w`: the macro call of fragment rule `B` with the constant arguments `D[w₀], D[w₁], …` and the plain
  reference to the specialized rule of `(B, w)`.

Two syntactic lemmas show that rule bodies stay related after the call-by-name substitution: `rel_embed` (an env body is
related to itself) and `rel_spec` (the substituted body of `B` under constants `w` is related to `B`'s specialized rule).
Then each direction is one induction on a derivation:

* `spec_preserve`: a call-by-name derivation of `m` gives a plain derivation of any `p` with `Rel F S m p`, with the same
  observation (failure ↦ failure, success with rest `r` ↦ success with rest `r`);
* `spec_reflect`: the converse, by induction on the plain derivation.

Neither direction uses fuel or determinism; an observation that has no derivation on one side has none on the other.
-/

namespace Shallot.MacroPeg

open Shallot (PExp PTree Grammar Derives Outcome pegRun)

/-! ## Substitution facts -/

/-- Substitution leaves an embedded plain PEG expression unchanged, for any actual arguments (it has no parameters and
all its calls have no arguments). Generalizes `subst_embedExp`. -/
theorem subst_embedExp_any (args : List MExp) : ∀ p : PExp, MExp.subst args (embedExp p) = embedExp p
  | .eps => rfl
  | .any => rfl
  | .chr _ => rfl
  | .range _ _ => rfl
  | .lit _ => rfl
  | .nt _ => rfl
  | .seq e₁ e₂ => by simp only [embedExp, MExp.subst]; rw [subst_embedExp_any args e₁, subst_embedExp_any args e₂]
  | .alt e₁ e₂ => by simp only [embedExp, MExp.subst]; rw [subst_embedExp_any args e₁, subst_embedExp_any args e₂]
  | .star e => by simp only [embedExp, MExp.subst]; rw [subst_embedExp_any args e]
  | .notP e => by simp only [embedExp, MExp.subst]; rw [subst_embedExp_any args e]

theorem substArgs_map {α : Type} (args : List MExp) (f : α → MExp) :
    ∀ l : List α, MExp.substArgs args (l.map f) = l.map (fun x => MExp.subst args (f x))
  | [] => rfl
  | x :: xs => by simp [MExp.substArgs, substArgs_map args f xs]

theorem argAt_eq_getElem? : ∀ (l : List MExp) (k : Nat), argAt l k = l[k]?
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: as, n + 1 => by simp [argAt, argAt_eq_getElem? as n]

/-! ## The correspondence -/

inductive Rel (F : FGrammar) (S : List (Nat × List Nat)) : MExp → PExp → Prop
  | eps : Rel F S .eps .eps
  | any : Rel F S .any .any
  | chr (c : Char) : Rel F S (.chr c) (.chr c)
  | range (lo hi : Char) : Rel F S (.range lo hi) (.range lo hi)
  | lit (s : List Char) : Rel F S (.lit s) (.lit s)
  | seq {m₁ m₂ : MExp} {p₁ p₂ : PExp} : Rel F S m₁ p₁ → Rel F S m₂ p₂ → Rel F S (.seq m₁ m₂) (.seq p₁ p₂)
  | alt {m₁ m₂ : MExp} {p₁ p₂ : PExp} : Rel F S m₁ p₁ → Rel F S m₂ p₂ → Rel F S (.alt m₁ m₂) (.alt p₁ p₂)
  | star {m : MExp} {p : PExp} : Rel F S m p → Rel F S (.star m) (.star p)
  | notP {m : MExp} {p : PExp} : Rel F S m p → Rel F S (.notP m) (.notP p)
  | envRef (i : Nat) (h : i < F.env.length) : Rel F S (.call i []) (.nt i)
  | specRef (B : Nat) (w : List Nat) (h : (B, w) ∈ S) :
      Rel F S (.call (F.env.length + B) (F.constArgs w)) (.nt (F.env.length + codeOn S B w))

theorem rel_embed (F : FGrammar) (S : List (Nat × List Nat)) : ∀ p : PExp, p.NtBounded F.env.length → Rel F S (embedExp p) p
  | .eps, _ => .eps
  | .any, _ => .any
  | .chr c, _ => .chr c
  | .range lo hi, _ => .range lo hi
  | .lit s, _ => .lit s
  | .nt i, h => .envRef i h
  | .seq a b, h => .seq (rel_embed F S a h.1) (rel_embed F S b h.2)
  | .alt a b, h => .alt (rel_embed F S a h.1) (rel_embed F S b h.2)
  | .star a, h => .star (rel_embed F S a h)
  | .notP a, h => .notP (rel_embed F S a h)

theorem FArg.subst_toM (F : FGrammar) {a : Nat} {w : List Nat} (hl : w.length = a) :
    ∀ x : FArg, x.WF F a → MExp.subst (F.constArgs w) (x.toM F) = embedExp (F.constP (x.resolve w))
  | .fwd j, h => by
    have hj : j < w.length := by simp only [FArg.WF] at h; omega
    simp [FArg.toM, MExp.subst, argAt_eq_getElem?, FGrammar.constArgs, FArg.resolve,
      List.getElem?_eq_getElem hj]
  | .const _, _ => subst_embedExp_any _ _

/-- The call-by-name substitution of the constants `w` into a well-formed body is related to the body specialized at `w`. -/
theorem rel_spec (F : FGrammar) (S : List (Nat × List Nat)) (hF : F.WF) {a : Nat} {w : List Nat}
    (hl : w.length = a) :
    ∀ e : FExp, e.WF F a → e.CallsIn S w → Rel F S (MExp.subst (F.constArgs w) (e.toM F)) (e.spec F (codeOn S) w)
  | .eps, _, _ => .eps
  | .any, _, _ => .any
  | .chr c, _, _ => .chr c
  | .range lo hi, _, _ => .range lo hi
  | .lit s, _, _ => .lit s
  | .param j, h, _ => by
    have hj : j < w.length := by simp only [FExp.WF] at h; omega
    simp only [FExp.toM, MExp.subst, FExp.spec, argAt_eq_getElem?, FGrammar.constArgs, List.getElem?_map,
      List.getElem?_eq_getElem hj, Option.map_some]
    exact rel_embed F S _ (F.constP_ntBounded hF _)
  | .env i, h, _ => .envRef i h
  | .call C as, h, hc => by
    simp only [FExp.toM, MExp.subst, FExp.spec]
    rw [substArgs_map]
    have : as.map (fun x => MExp.subst (F.constArgs w) (x.toM F)) = F.constArgs (as.map (FArg.resolve w)) := by
      simp only [FGrammar.constArgs, List.map_map]
      apply List.map_congr_left
      intro x hx
      exact FArg.subst_toM F hl x (h.2 x hx)
    rw [this]
    exact .specRef C _ hc
  | .seq a b, h, hc => .seq (rel_spec F S hF hl a h.1 hc.1) (rel_spec F S hF hl b h.2 hc.2)
  | .alt a b, h, hc => .alt (rel_spec F S hF hl a h.1 hc.1) (rel_spec F S hF hl b h.2 hc.2)
  | .star a, h, hc => .star (rel_spec F S hF hl a h hc)
  | .notP a, h, hc => .notP (rel_spec F S hF hl a h hc)

/-! ## Rule lookup in the embedding -/

theorem FGrammar.ruleAtM_toMacro_env (F : FGrammar) {i : Nat} {q : PExp} (h : F.env[i]? = some q) :
    ruleAtM F.toMacro.rules i = some ⟨0, embedExp q⟩ := by
  have hi : i < F.env.length := (List.getElem?_eq_some_iff.1 h).1
  rw [ruleAtM_eq_getElem?, FGrammar.toMacro, List.getElem?_append_left (by simpa using hi), List.getElem?_map, h]
  rfl

theorem FGrammar.ruleAtM_toMacro_frag (F : FGrammar) {B : Nat} {r : FRule} (h : F.rules[B]? = some r) :
    ruleAtM F.toMacro.rules (F.env.length + B) = some ⟨r.arity, r.body.toM F⟩ := by
  rw [ruleAtM_eq_getElem?, FGrammar.toMacro, List.getElem?_append_right (by simp), List.length_map,
    Nat.add_sub_cancel_left, List.getElem?_map, h]
  rfl

theorem FGrammar.ruleAtM_toMacro_none_env (F : FGrammar) {i : Nat} (hi : i < F.env.length) :
    ∃ q, F.env[i]? = some q ∧ ruleAtM F.toMacro.rules i = some ⟨0, embedExp q⟩ :=
  ⟨_, List.getElem?_eq_getElem hi, F.ruleAtM_toMacro_env (List.getElem?_eq_getElem hi)⟩

/-! ## Corresponding outcomes -/

/-- Outcomes with the same observation (trees are not compared). -/
inductive Corr : MOutcome → Outcome → Prop
  | fail : Corr .fail .fail
  | ok (t : MTree) (t' : PTree) (r : List Char) : Corr (.ok t r) (.ok t' r)

theorem Corr.restOf_eq {o : MOutcome} {o' : Outcome} (h : Corr o o') : o.restOf = pegRestOf o' := by
  cases h <;> rfl

theorem corr_of_restOf {o : MOutcome} {o' : Outcome} (h : o.restOf = pegRestOf o') : Corr o o' := by
  cases o <;> cases o' <;> simp_all [MOutcome.restOf, pegRestOf] <;> first | exact .fail | (subst_vars; exact .ok _ _ _)

/-! ## Preservation -/

theorem spec_preserve (F : FGrammar) (hF : F.WF) {S : List (Nat × List Nat)} (hS : F.SpecSet S) (A : Nat)
    (ks : List Nat) {m : MExp} {x : List Char}
    {o : MOutcome} (h : MDerives F.toMacro .callByName m x o) :
    ∀ p, Rel F S m p → ∃ o', Derives (F.specializeOn S A ks) p x o' ∧ Corr o o' := by
  induction h using MDerives.rec
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ => True)
  case eps input => intro p hp; cases hp; exact ⟨_, .eps input, .ok _ _ _⟩
  case anyOk c rest => intro p hp; cases hp; exact ⟨_, .anyOk c rest, .ok _ _ _⟩
  case anyFail => intro p hp; cases hp; exact ⟨_, .anyFail, .fail⟩
  case chrOk c d rest hb => intro p hp; cases hp; exact ⟨_, .chrOk c d rest hb, .ok _ _ _⟩
  case chrFail c d rest hb => intro p hp; cases hp; exact ⟨_, .chrFail c d rest hb, .fail⟩
  case chrEmpty c => intro p hp; cases hp; exact ⟨_, .chrEmpty c, .fail⟩
  case rangeOk lo hi d rest hb => intro p hp; cases hp; exact ⟨_, .rangeOk lo hi d rest hb, .ok _ _ _⟩
  case rangeFail lo hi d rest hb => intro p hp; cases hp; exact ⟨_, .rangeFail lo hi d rest hb, .fail⟩
  case rangeEmpty lo hi => intro p hp; cases hp; exact ⟨_, .rangeEmpty lo hi, .fail⟩
  case litOk s input rest hs => intro p hp; cases hp; exact ⟨_, .litOk s input rest hs, .ok _ _ _⟩
  case litFail s input hs => intro p hp; cases hp; exact ⟨_, .litFail s input hs, .fail⟩
  case callNameOk i args r input rest t _ hr ha _ ih =>
    intro p hp
    cases hp with
    | envRef _ hi =>
      obtain ⟨q, hq, hrq⟩ := F.ruleAtM_toMacro_none_env hi
      rw [hrq] at hr; cases hr
      have hrel : Rel F S (MExp.subst [] (embedExp q)) q := by
        rw [subst_embedExp_any]; exact rel_embed F S q (hF.1 q (List.mem_of_getElem? hq))
      obtain ⟨o', hd', hc⟩ := ih q hrel
      cases hc with
      | ok _ t' _ => exact ⟨_, .ntOk i q input rest t' (F.ruleAt_specializeOn_env S A ks hq) hd', .ok _ _ _⟩
    | specRef B w hm =>
      obtain ⟨rB, hrB, hl, hk⟩ := hS.1 _ hm
      rw [F.ruleAtM_toMacro_frag hrB] at hr; cases hr
      obtain ⟨o', hd', hc⟩ := ih _ (rel_spec F S hF hl rB.body (hF.2.2 rB (List.mem_of_getElem? hrB)) (hS.2 B w rB hm hrB))
      cases hc with
      | ok _ t' _ =>
        exact ⟨_, .ntOk _ _ input rest t' (F.ruleAt_specializeOn_spec S A ks hrB hm) hd', .ok _ _ _⟩
  case callNameFail i args r input _ hr ha _ ih =>
    intro p hp
    cases hp with
    | envRef _ hi =>
      obtain ⟨q, hq, hrq⟩ := F.ruleAtM_toMacro_none_env hi
      rw [hrq] at hr; cases hr
      have hrel : Rel F S (MExp.subst [] (embedExp q)) q := by
        rw [subst_embedExp_any]; exact rel_embed F S q (hF.1 q (List.mem_of_getElem? hq))
      obtain ⟨o', hd', hc⟩ := ih q hrel
      cases hc
      exact ⟨_, .ntFail i q input (F.ruleAt_specializeOn_env S A ks hq) hd', .fail⟩
    | specRef B w hm =>
      obtain ⟨rB, hrB, hl, hk⟩ := hS.1 _ hm
      rw [F.ruleAtM_toMacro_frag hrB] at hr; cases hr
      obtain ⟨o', hd', hc⟩ := ih _ (rel_spec F S hF hl rB.body (hF.2.2 rB (List.mem_of_getElem? hrB)) (hS.2 B w rB hm hrB))
      cases hc
      exact ⟨_, .ntFail _ _ input (F.ruleAt_specializeOn_spec S A ks hrB hm) hd', .fail⟩
  case callMissing i args input hr =>
    intro p hp
    cases hp with
    | envRef _ hi =>
      obtain ⟨q, _, hrq⟩ := F.ruleAtM_toMacro_none_env hi
      rw [hrq] at hr; cases hr
    | specRef B w hm =>
      obtain ⟨rB, hrB, _, _⟩ := hS.1 _ hm
      rw [F.ruleAtM_toMacro_frag hrB] at hr; cases hr
  case callArity i args r input hr ha =>
    intro p hp
    cases hp with
    | envRef _ hi =>
      obtain ⟨q, _, hrq⟩ := F.ruleAtM_toMacro_none_env hi
      rw [hrq] at hr; cases hr
      exact absurd rfl ha
    | specRef B w hm =>
      obtain ⟨rB, hrB, hl, _⟩ := hS.1 _ hm
      rw [F.ruleAtM_toMacro_frag hrB] at hr; cases hr
      simp [FGrammar.constArgs, hl] at ha
  case seqOk e₁ e₂ input rest₁ rest₂ t₁ t₂ _ _ ih₁ ih₂ =>
    intro p hp
    cases hp with
    | seq hp₁ hp₂ =>
      obtain ⟨_, d₁, c₁⟩ := ih₁ _ hp₁
      cases c₁
      obtain ⟨_, d₂, c₂⟩ := ih₂ _ hp₂
      cases c₂
      exact ⟨_, .seqOk _ _ _ _ _ _ _ d₁ d₂, .ok _ _ _⟩
  case seqFail₁ e₁ e₂ input _ ih₁ =>
    intro p hp
    cases hp with
    | seq hp₁ _ =>
      obtain ⟨_, d₁, c₁⟩ := ih₁ _ hp₁
      cases c₁
      exact ⟨_, .seqFail₁ _ _ _ d₁, .fail⟩
  case seqFail₂ e₁ e₂ input rest₁ t₁ _ _ ih₁ ih₂ =>
    intro p hp
    cases hp with
    | seq hp₁ hp₂ =>
      obtain ⟨_, d₁, c₁⟩ := ih₁ _ hp₁
      cases c₁
      obtain ⟨_, d₂, c₂⟩ := ih₂ _ hp₂
      cases c₂
      exact ⟨_, .seqFail₂ _ _ _ _ _ d₁ d₂, .fail⟩
  case altL e₁ e₂ input rest t _ ih =>
    intro p hp
    cases hp with
    | alt hp₁ _ =>
      obtain ⟨_, d, c⟩ := ih _ hp₁
      cases c
      exact ⟨_, .altL _ _ _ _ _ d, .ok _ _ _⟩
  case altR e₁ e₂ input rest t _ _ ih₁ ih₂ =>
    intro p hp
    cases hp with
    | alt hp₁ hp₂ =>
      obtain ⟨_, d₁, c₁⟩ := ih₁ _ hp₁
      cases c₁
      obtain ⟨_, d₂, c₂⟩ := ih₂ _ hp₂
      cases c₂
      exact ⟨_, .altR _ _ _ _ _ d₁ d₂, .ok _ _ _⟩
  case altFail e₁ e₂ input _ _ ih₁ ih₂ =>
    intro p hp
    cases hp with
    | alt hp₁ hp₂ =>
      obtain ⟨_, d₁, c₁⟩ := ih₁ _ hp₁
      cases c₁
      obtain ⟨_, d₂, c₂⟩ := ih₂ _ hp₂
      cases c₂
      exact ⟨_, .altFail _ _ _ d₁ d₂, .fail⟩
  case starNil e input _ ih =>
    intro p hp
    cases hp with
    | star hp₁ =>
      obtain ⟨_, d, c⟩ := ih _ hp₁
      cases c
      exact ⟨_, .starNil _ _ d, .ok _ _ _⟩
  case starCons e input rest rest' t ts _ _ ih₁ ih₂ =>
    intro p hp
    cases hp with
    | star hp₁ =>
      obtain ⟨_, d₁, c₁⟩ := ih₁ _ hp₁
      cases c₁
      obtain ⟨_, d₂, c₂⟩ := ih₂ _ (.star hp₁)
      cases c₂
      exact ⟨_, .starCons _ _ _ _ _ _ d₁ d₂, .ok _ _ _⟩
  case notOk e input rest t _ ih =>
    intro p hp
    cases hp with
    | notP hp₁ =>
      obtain ⟨_, d, c⟩ := ih _ hp₁
      cases c
      exact ⟨_, .notOk _ _ _ _ d, .fail⟩
  case notFail e input _ ih =>
    intro p hp
    cases hp with
    | notP hp₁ =>
      obtain ⟨_, d, c⟩ := ih _ hp₁
      cases c
      exact ⟨_, .notFail _ _ d, .ok _ _ _⟩
  all_goals first
    | trivial
    | (intro p hp; cases hp; done)
    | (intro p hp; contradiction)

/-! ## Reflection -/

theorem spec_reflect (F : FGrammar) (hF : F.WF) {S : List (Nat × List Nat)} (hS : F.SpecSet S) (A : Nat)
    (ks : List Nat) {p : PExp} {x : List Char}
    {o' : Outcome} (h : Derives (F.specializeOn S A ks) p x o') :
    ∀ m, Rel F S m p → ∃ o, MDerives F.toMacro .callByName m x o ∧ Corr o o' := by
  induction h with
  | eps input => intro m hm; cases hm; exact ⟨_, .eps input, .ok _ _ _⟩
  | anyOk c rest => intro m hm; cases hm; exact ⟨_, .anyOk c rest, .ok _ _ _⟩
  | anyFail => intro m hm; cases hm; exact ⟨_, .anyFail, .fail⟩
  | chrOk c d rest hb => intro m hm; cases hm; exact ⟨_, .chrOk c d rest hb, .ok _ _ _⟩
  | chrFail c d rest hb => intro m hm; cases hm; exact ⟨_, .chrFail c d rest hb, .fail⟩
  | chrEmpty c => intro m hm; cases hm; exact ⟨_, .chrEmpty c, .fail⟩
  | rangeOk lo hi d rest hb => intro m hm; cases hm; exact ⟨_, .rangeOk lo hi d rest hb, .ok _ _ _⟩
  | rangeFail lo hi d rest hb => intro m hm; cases hm; exact ⟨_, .rangeFail lo hi d rest hb, .fail⟩
  | rangeEmpty lo hi => intro m hm; cases hm; exact ⟨_, .rangeEmpty lo hi, .fail⟩
  | litOk s input rest hs => intro m hm; cases hm; exact ⟨_, .litOk s input rest hs, .ok _ _ _⟩
  | litFail s input hs => intro m hm; cases hm; exact ⟨_, .litFail s input hs, .fail⟩
  | ntOk i e input rest t hr _ ih =>
    intro m hm
    cases hm with
    | envRef _ hi =>
      obtain ⟨q, hq, hrq⟩ := F.ruleAtM_toMacro_none_env hi
      rw [F.ruleAt_specializeOn_env S A ks hq] at hr; simp only [Option.some.injEq] at hr; subst hr
      obtain ⟨o, d, c⟩ := ih _ (rel_embed F S q (hF.1 q (List.mem_of_getElem? hq)))
      cases c
      rw [← subst_embedExp_any [] q] at d
      exact ⟨_, .callNameOk i [] ⟨0, embedExp q⟩ input rest _ rfl hrq rfl d, .ok _ _ _⟩
    | specRef B w hm =>
      obtain ⟨rB, hrB, hl, hk⟩ := hS.1 _ hm
      rw [F.ruleAt_specializeOn_spec S A ks hrB hm] at hr; cases hr
      obtain ⟨o, d, c⟩ := ih _ (rel_spec F S hF hl rB.body (hF.2.2 rB (List.mem_of_getElem? hrB)) (hS.2 B w rB hm hrB))
      cases c
      exact ⟨_, .callNameOk _ _ ⟨rB.arity, rB.body.toM F⟩ input rest _ rfl (F.ruleAtM_toMacro_frag hrB)
        (by simp [FGrammar.constArgs, hl]) d, .ok _ _ _⟩
  | ntFail i e input hr _ ih =>
    intro m hm
    cases hm with
    | envRef _ hi =>
      obtain ⟨q, hq, hrq⟩ := F.ruleAtM_toMacro_none_env hi
      rw [F.ruleAt_specializeOn_env S A ks hq] at hr; simp only [Option.some.injEq] at hr; subst hr
      obtain ⟨o, d, c⟩ := ih _ (rel_embed F S q (hF.1 q (List.mem_of_getElem? hq)))
      cases c
      rw [← subst_embedExp_any [] q] at d
      exact ⟨_, .callNameFail i [] ⟨0, embedExp q⟩ input rfl hrq rfl d, .fail⟩
    | specRef B w hm =>
      obtain ⟨rB, hrB, hl, hk⟩ := hS.1 _ hm
      rw [F.ruleAt_specializeOn_spec S A ks hrB hm] at hr; cases hr
      obtain ⟨o, d, c⟩ := ih _ (rel_spec F S hF hl rB.body (hF.2.2 rB (List.mem_of_getElem? hrB)) (hS.2 B w rB hm hrB))
      cases c
      exact ⟨_, .callNameFail _ _ ⟨rB.arity, rB.body.toM F⟩ input rfl (F.ruleAtM_toMacro_frag hrB)
        (by simp [FGrammar.constArgs, hl]) d, .fail⟩
  | ntMissing i input hr =>
    intro m hm
    cases hm with
    | envRef _ hi =>
      obtain ⟨q, hq, _⟩ := F.ruleAtM_toMacro_none_env hi
      rw [F.ruleAt_specializeOn_env S A ks hq] at hr; cases hr
    | specRef B w hm =>
      obtain ⟨rB, hrB, hl, hk⟩ := hS.1 _ hm
      rw [F.ruleAt_specializeOn_spec S A ks hrB hm] at hr; cases hr
  | seqOk e₁ e₂ input rest₁ rest₂ t₁ t₂ _ _ ih₁ ih₂ =>
    intro m hm
    cases hm with
    | seq hm₁ hm₂ =>
      obtain ⟨_, d₁, c₁⟩ := ih₁ _ hm₁
      cases c₁
      obtain ⟨_, d₂, c₂⟩ := ih₂ _ hm₂
      cases c₂
      exact ⟨_, .seqOk _ _ _ _ _ _ _ d₁ d₂, .ok _ _ _⟩
  | seqFail₁ e₁ e₂ input _ ih₁ =>
    intro m hm
    cases hm with
    | seq hm₁ _ =>
      obtain ⟨_, d₁, c₁⟩ := ih₁ _ hm₁
      cases c₁
      exact ⟨_, .seqFail₁ _ _ _ d₁, .fail⟩
  | seqFail₂ e₁ e₂ input rest₁ t₁ _ _ ih₁ ih₂ =>
    intro m hm
    cases hm with
    | seq hm₁ hm₂ =>
      obtain ⟨_, d₁, c₁⟩ := ih₁ _ hm₁
      cases c₁
      obtain ⟨_, d₂, c₂⟩ := ih₂ _ hm₂
      cases c₂
      exact ⟨_, .seqFail₂ _ _ _ _ _ d₁ d₂, .fail⟩
  | altL e₁ e₂ input rest t _ ih =>
    intro m hm
    cases hm with
    | alt hm₁ _ =>
      obtain ⟨_, d, c⟩ := ih _ hm₁
      cases c
      exact ⟨_, .altL _ _ _ _ _ d, .ok _ _ _⟩
  | altR e₁ e₂ input rest t _ _ ih₁ ih₂ =>
    intro m hm
    cases hm with
    | alt hm₁ hm₂ =>
      obtain ⟨_, d₁, c₁⟩ := ih₁ _ hm₁
      cases c₁
      obtain ⟨_, d₂, c₂⟩ := ih₂ _ hm₂
      cases c₂
      exact ⟨_, .altR _ _ _ _ _ d₁ d₂, .ok _ _ _⟩
  | altFail e₁ e₂ input _ _ ih₁ ih₂ =>
    intro m hm
    cases hm with
    | alt hm₁ hm₂ =>
      obtain ⟨_, d₁, c₁⟩ := ih₁ _ hm₁
      cases c₁
      obtain ⟨_, d₂, c₂⟩ := ih₂ _ hm₂
      cases c₂
      exact ⟨_, .altFail _ _ _ d₁ d₂, .fail⟩
  | starNil e input _ ih =>
    intro m hm
    cases hm with
    | star hm₁ =>
      obtain ⟨_, d, c⟩ := ih _ hm₁
      cases c
      exact ⟨_, .starNil _ _ d, .ok _ _ _⟩
  | starCons e input rest rest' t ts _ _ ih₁ ih₂ =>
    intro m hm
    cases hm with
    | star hm₁ =>
      obtain ⟨_, d₁, c₁⟩ := ih₁ _ hm₁
      cases c₁
      obtain ⟨_, d₂, c₂⟩ := ih₂ _ (.star hm₁)
      cases c₂
      exact ⟨_, .starCons _ _ _ _ _ _ d₁ d₂, .ok _ _ _⟩
  | notOk e input rest t _ ih =>
    intro m hm
    cases hm with
    | notP hm₁ =>
      obtain ⟨_, d, c⟩ := ih _ hm₁
      cases c
      exact ⟨_, .notOk _ _ _ _ d, .fail⟩
  | notFail e input _ ih =>
    intro m hm
    cases hm with
    | notP hm₁ =>
      obtain ⟨_, d, c⟩ := ih _ hm₁
      cases c
      exact ⟨_, .notFail _ _ d, .ok _ _ _⟩

/-! ## Main theorem and corollaries -/

/-- Related expressions have the same observations, in both directions. -/
theorem rel_obs_iff (F : FGrammar) (hF : F.WF) {S : List (Nat × List Nat)} (hS : F.SpecSet S) (A : Nat)
    (ks : List Nat) {m : MExp} {p : PExp} (hr : Rel F S m p) (x : List Char) (r : Option (List Char)) :
    MacroObs F.toMacro m x r ↔ PegObs (F.specializeOn S A ks) p x r := by
  constructor
  · rintro ⟨o, hd, ho⟩
    obtain ⟨o', hd', hc⟩ := spec_preserve F hF hS A ks hd p hr
    exact ⟨o', hd', hc.restOf_eq ▸ ho⟩
  · rintro ⟨o', hd', ho⟩
    obtain ⟨o, hd, hc⟩ := spec_reflect F hF hS A ks hd' m hr
    exact ⟨o, hd, hc.restOf_eq.trans ho⟩

/-- Specialization over any `SpecSet` containing the entry pair. -/
theorem finite_specialization_on (F : FGrammar) (hF : F.WF) {S : List (Nat × List Nat)} (hS : F.SpecSet S)
    {A : Nat} {ks : List Nat} (hm : (A, ks) ∈ S) (x : List Char) (r : Option (List Char)) :
    MacroObs F.toMacro (F.entry A ks) x r ↔ PegObs (F.specializeOn S A ks) (.nt (F.specializeOn S A ks).start) x r :=
  rel_obs_iff F hF hS A ks (.specRef A ks hm) x r

/-- **Finite specialization (instructions.md §5.3).** For a well-formed fragment grammar and an admissible entry
`(A, ks)`, the call-by-name Macro PEG entry call `A(D[ks₀], …)` and the specialized ordinary PEG's start nonterminal have
exactly the same observations: for every input `x` and every observation `r` (`none` = failure, `some rest` = success
leaving `rest`), a finite derivation with that observation exists on one side iff it exists on the other. -/
theorem finite_specialization_cbn (F : FGrammar) (hF : F.WF) {A : Nat} {ks : List Nat} (hv : F.ValidVec A ks)
    (x : List Char) (r : Option (List Char)) :
    MacroObs F.toMacro (F.entry A ks) x r ↔
      PegObs (F.specialize A ks) (.nt (F.specialize A ks).start) x r :=
  finite_specialization_on F hF (F.specs_specSet hF) ((F.mem_specs A ks).2 hv) x r

/-- Success language (any remaining input). -/
theorem finite_specialization_accepts (F : FGrammar) (hF : F.WF) {A : Nat} {ks : List Nat} (hv : F.ValidVec A ks)
    (x : List Char) :
    MAccepts F.toMacro (F.entry A ks) x ↔ PAccepts (F.specialize A ks) (.nt (F.specialize A ks).start) x := by
  unfold MAccepts PAccepts
  exact exists_congr fun rest => finite_specialization_cbn F hF hv x (some rest)

/-- Whole-consumption language. -/
theorem finite_specialization_recognizesAll (F : FGrammar) (hF : F.WF) {A : Nat} {ks : List Nat}
    (hv : F.ValidVec A ks) (x : List Char) :
    MRecognizesAll F.toMacro (F.entry A ks) x ↔
      PRecognizesAll (F.specialize A ks) (.nt (F.specialize A ks).start) x :=
  finite_specialization_cbn F hF hv x (some [])

/-- Run-level form: some fuel makes the call-by-name interpreter return an outcome with observation `r` iff some fuel
makes the plain PEG interpreter on the specialized grammar do so (each side chooses its own fuel; a fuel-exhausted `none`
is never read as an observation). -/
theorem finite_specialization_run (F : FGrammar) (hF : F.WF) {A : Nat} {ks : List Nat} (hv : F.ValidVec A ks)
    (x : List Char) (r : Option (List Char)) :
    (∃ f o, mpegRun F.toMacro .callByName f (F.entry A ks) x = some o ∧ o.restOf = r) ↔
      (∃ f o, pegRun (F.specialize A ks) f (.nt (F.specialize A ks).start) x = some o ∧ pegRestOf o = r) := by
  rw [← macroObs_iff_run, ← pegObs_iff_run]
  exact finite_specialization_cbn F hF hv x r

/-! ## Expressiveness of the fragment (instructions.md §5.6)

The fragment and ordinary PEG define the same classes of languages, for both observations. This is a statement about
this fragment only (first-order, call-by-name, arguments forwarded or drawn from a finite `D`); it says nothing about
general Macro PEG. -/

theorem pegObs_nt_unfold {g : Grammar} {k : Nat} {e : PExp} (hk : Shallot.ruleAt g.rules k = some e)
    (x : List Char) (r : Option (List Char)) : PegObs g (.nt k) x r ↔ PegObs g e x r := by
  constructor
  · rintro ⟨o, hd, ho⟩
    cases hd with
    | ntOk _ e' _ rest t hr hd' => rw [hk] at hr; cases hr; exact ⟨_, hd', ho⟩
    | ntFail _ e' _ hr hd' => rw [hk] at hr; cases hr; exact ⟨_, hd', ho⟩
    | ntMissing _ _ hr => rw [hk] at hr; cases hr
  · rintro ⟨o, hd, ho⟩
    cases o with
    | fail => exact ⟨_, .ntFail k e x hk hd, ho⟩
    | ok t rest => exact ⟨_, .ntOk k e x rest t hk hd, ho⟩

/-- The fragment instance of a plain PEG `(g, s)`: env `g.rules`, no constants, one arity-0 rule `env s`. -/
def pegAsFragment (g : Grammar) (s : Nat) : FGrammar := ⟨g.rules, [], [⟨0, .env s⟩]⟩

theorem pegAsFragment_wf {g : Grammar} {s : Nat} (hself : g.SelfContained) (hs : s < g.rules.length) :
    (pegAsFragment g s).WF := by
  refine ⟨hself, by simp [pegAsFragment], ?_⟩
  intro r hr
  simp only [pegAsFragment, List.mem_singleton] at hr
  subst hr
  exact hs

theorem pegAsFragment_valid (g : Grammar) (s : Nat) : (pegAsFragment g s).ValidVec 0 [] :=
  ⟨_, rfl, rfl, by simp⟩

/-- Every plain PEG language (for each observation) is the language of a fragment entry. -/
theorem peg_obs_as_fragment (g : Grammar) (hself : g.SelfContained) {s : Nat} (hs : s < g.rules.length)
    (x : List Char) (r : Option (List Char)) :
    PegObs g (.nt s) x r ↔ MacroObs (pegAsFragment g s).toMacro ((pegAsFragment g s).entry 0 []) x r := by
  let F := pegAsFragment g s
  have hF := pegAsFragment_wf hself hs
  have hv := pegAsFragment_valid g s
  rw [finite_specialization_cbn F hF hv]
  have hstart : Shallot.ruleAt (F.specialize 0 []).rules (F.specialize 0 []).start = some (.nt s) := by
    have := F.ruleAt_specializeOn_spec F.specs 0 [] (B := 0) (w := []) (r := ⟨0, .env s⟩) rfl
      ((F.mem_specs 0 []).2 hv)
    exact this
  rw [pegObs_nt_unfold hstart]
  have he : (PExp.nt s).NtBounded g.rules.length := hs
  constructor
  · rintro ⟨o, hd, ho⟩
    exact ⟨o, Shallot.derives_append_preserved _ _ he hself hd, ho⟩
  · rintro ⟨o, hd, ho⟩
    exact ⟨o, Shallot.derives_append_reflect (F.specs.map (F.specRuleOn F.specs)) (F.specialize 0 []).start he hself hd, ho⟩

/-- **§5.6, as language classes.** (1) Every fragment entry's success language and whole-consumption language are those
of a self-contained ordinary PEG nonterminal; (2) conversely. -/
theorem fragment_lang_is_peg (F : FGrammar) (hF : F.WF) {A : Nat} {ks : List Nat} (hv : F.ValidVec A ks) :
    ∃ (g : Grammar) (s : Nat), g.SelfContained ∧ s < g.rules.length ∧
      ∀ x, (MAccepts F.toMacro (F.entry A ks) x ↔ PAccepts g (.nt s) x) ∧
        (MRecognizesAll F.toMacro (F.entry A ks) x ↔ PRecognizesAll g (.nt s) x) :=
  ⟨F.specialize A ks, (F.specialize A ks).start, F.specialize_selfContained hF A ks, F.entryNt_lt hv,
    fun x => ⟨finite_specialization_accepts F hF hv x, finite_specialization_recognizesAll F hF hv x⟩⟩

theorem peg_lang_is_fragment (g : Grammar) (hself : g.SelfContained) {s : Nat} (hs : s < g.rules.length) :
    ∃ (F : FGrammar) (A : Nat) (ks : List Nat), F.WF ∧ F.ValidVec A ks ∧
      ∀ x, (PAccepts g (.nt s) x ↔ MAccepts F.toMacro (F.entry A ks) x) ∧
        (PRecognizesAll g (.nt s) x ↔ MRecognizesAll F.toMacro (F.entry A ks) x) :=
  ⟨pegAsFragment g s, 0, [], pegAsFragment_wf hself hs, pegAsFragment_valid g s, fun x =>
    ⟨exists_congr fun rest => peg_obs_as_fragment g hself hs x (some rest), peg_obs_as_fragment g hself hs x (some [])⟩⟩

/-- §5.1(7): an expression over the ordinary environment means the same thing in the environment itself (as a plain
PEG), in the Macro PEG embedding (`env` rules as arity-0 macro rules), and — by `rel_obs_iff` — in the specialized
grammar. -/
theorem env_obs_iff (F : FGrammar) (hF : F.WF) (p : PExp) (hp : p.NtBounded F.env.length) (s : Nat)
    (x : List Char) (r : Option (List Char)) :
    PegObs ⟨F.env, s⟩ p x r ↔ MacroObs F.toMacro (embedExp p) x r := by
  rw [rel_obs_iff F hF (F.specs_specSet hF) 0 [] (rel_embed F F.specs p hp)]
  constructor
  · rintro ⟨o, hd, ho⟩
    exact ⟨o, Shallot.derives_append_preserved (g := ⟨F.env, s⟩) _ _ hp hF.1 hd, ho⟩
  · rintro ⟨o, hd, ho⟩
    exact ⟨o, Shallot.derives_append_reflect (g := ⟨F.env, s⟩) (F.specs.map (F.specRuleOn F.specs)) _ hp hF.1 hd,
      ho⟩

end Shallot.MacroPeg
