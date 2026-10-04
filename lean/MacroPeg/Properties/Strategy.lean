import MacroPeg.Properties.ArgEquiv

/-!
# Evaluation strategies (instructions.md §7)

`SObs g s e x r` is the observation relation for an arbitrary strategy `s` (`MacroObs` is the call-by-name instance).
Everything here is a statement about finite derivations; non-termination is stated as the non-existence of any
derivation, never through a fuel-bounded run.

* §7.1 — the four rows of the separation table, each as derivations under CBN, Par and Seq (`row1_*` … `row4_*`), plus
  the row the brief uses to rule out the weakened condition: an unused `&"a"` on input `"b"`.
* §7.2 — `Loop() ← Loop()`, `F(x, y) ← ε`: `Loop()` has no derivation under any strategy; under Par/Seq
  `F(!ε, Loop())` fails at the first argument and `F(Loop(), !ε)` has no derivation; under CBN both succeed.
* §7.3 — conditional agreement. If every actual argument in every rule body and in the start expression is a closed
  expression that, under every strategy and on every input, has a derivation succeeding without consuming input
  (`ZeroArg`), then the three strategies have the same observations (`strategy_agree`). The syntactic-`ε` fragment is the
  first instance (`strategy_agree_eps`). The condition is quantified over every syntactic argument, used or not, so an
  argument that only Par/Seq would evaluate is covered. It cannot be weakened to "may succeed on the empty string": the
  `&"a"` row is a counterexample.

No language-class statement is drawn from these examples: different results of one closed program under two strategies
say nothing yet about the classes of languages the strategies define.
-/

namespace Shallot.MacroPeg

/-- Observation under an arbitrary strategy. -/
def SObs (g : MGrammar) (s : Strategy) (e : MExp) (x : List Char) (r : Option (List Char)) : Prop :=
  ∃ o, MDerives g s e x o ∧ o.restOf = r

theorem macroObs_eq_sObs (g : MGrammar) (e : MExp) (x : List Char) (r : Option (List Char)) :
    MacroObs g e x r = SObs g .callByName e x r := rfl

/-- Each strategy is deterministic, so an expression has at most one observation per input. -/
theorem sObs_unique {g : MGrammar} {s : Strategy} {e : MExp} {x : List Char} {r r' : Option (List Char)}
    (h : SObs g s e x r) (h' : SObs g s e x r') : r = r' := by
  obtain ⟨o, hd, rfl⟩ := h
  obtain ⟨o', hd', rfl⟩ := h'
  rw [mderives_det hd hd']

/-- A call of an arity-0 rule, under any strategy, has the observation of its body. -/
theorem call0_obs {g : MGrammar} {s : Strategy} {i : Nat} {r : MRule} (hr : ruleAtM g.rules i = some r)
    (ha : r.arity = 0) {x : List Char} {o : MOutcome} (hd : MDerives g s (MExp.subst [] r.body) x o) :
    SObs g s (.call i []) x o.restOf := by
  cases s <;> cases o with
  | fail => first
    | exact ⟨_, .callNameFail i [] r x rfl hr ha hd, rfl⟩
    | exact ⟨_, .callParFail i [] r x [] rfl hr ha (.nil x) hd, rfl⟩
    | exact ⟨_, .callSeqFail i [] r x x [] rfl hr ha (.nil x) hd, rfl⟩
  | ok t rest => first
    | exact ⟨_, .callNameOk i [] r x rest t rfl hr ha hd, rfl⟩
    | exact ⟨_, .callParOk i [] r x rest [] t rfl hr ha (.nil x) hd, rfl⟩
    | exact ⟨_, .callSeqOk i [] r x x rest [] t rfl hr ha (.nil x) hd, rfl⟩

/-! ## §7.1 The separation table

`S` is rule `1` (arity 0, its body is the call of `F`), `F` is rule `0`; the observation of `S()` is compared. -/

/-- Row 1: `F(x) ← ε; S ← F(!ε)`. -/
def row1G : MGrammar := ⟨[⟨1, .eps⟩, ⟨0, .call 0 [.notP .eps]⟩]⟩

theorem row1_cbn (w : List Char) : SObs row1G .callByName (.call 1 []) w (some w) :=
  call0_obs (o := .ok _ w) rfl rfl (.callNameOk 0 _ _ w w _ rfl rfl rfl (.eps w))

theorem row1_par (w : List Char) : SObs row1G .callByValuePar (.call 1 []) w none :=
  call0_obs (o := .fail) rfl rfl
    (.callParArgFail 0 [] (.notP .eps) [] _ w [] rfl rfl rfl (.nil w) (.notOk _ _ _ _ (.eps w)))

theorem row1_seq (w : List Char) : SObs row1G .callByValueSeq (.call 1 []) w none :=
  call0_obs (o := .fail) rfl rfl
    (.callSeqArgFail 0 [] (.notP .eps) [] _ w w [] rfl rfl rfl (.nil w) (.notOk _ _ _ _ (.eps w)))

/-- Row 2: `F(x) ← x; S ← F("a")` on `"a"`. -/
def row2G : MGrammar := ⟨[⟨1, .param 0⟩, ⟨0, .call 0 [.lit ['a']]⟩]⟩

theorem row2_cbn : SObs row2G .callByName (.call 1 []) ['a'] (some []) :=
  call0_obs (o := .ok _ []) rfl rfl (.callNameOk 0 _ _ _ [] _ rfl rfl rfl (.litOk ['a'] ['a'] [] rfl))

theorem row2_par : SObs row2G .callByValuePar (.call 1 []) ['a'] (some []) :=
  call0_obs (o := .ok _ []) rfl rfl
    (.callParOk 0 _ _ _ [] [.lit ['a']] _ rfl rfl rfl
      (.cons _ _ ['a'] ['a'] [] _ [] (.litOk ['a'] ['a'] [] rfl) rfl (.nil _)) (.litOk ['a'] ['a'] [] rfl))

theorem row2_seq : SObs row2G .callByValueSeq (.call 1 []) ['a'] none :=
  call0_obs (o := .fail) rfl rfl
    (.callSeqFail 0 _ _ ['a'] [] [.lit ['a']] rfl rfl rfl
      (.cons _ _ ['a'] ['a'] [] [] _ [] (.litOk ['a'] ['a'] [] rfl) rfl (.nil _)) (.litFail ['a'] [] rfl))

/-- Rows 3 and 4: `F(x, y) ← ε`. -/
def row3G : MGrammar := ⟨[⟨2, .eps⟩, ⟨0, .call 0 [.lit ['a'], .lit ['a']]⟩]⟩
def row4G : MGrammar := ⟨[⟨2, .eps⟩, ⟨0, .call 0 [.lit ['a'], .lit ['b']]⟩]⟩

theorem row3_cbn : SObs row3G .callByName (.call 1 []) ['a'] (some ['a']) :=
  call0_obs (o := .ok _ ['a']) rfl rfl (.callNameOk 0 _ _ _ _ _ rfl rfl rfl (.eps _))

theorem row3_par : SObs row3G .callByValuePar (.call 1 []) ['a'] (some ['a']) :=
  call0_obs (o := .ok _ ['a']) rfl rfl
    (.callParOk 0 _ _ _ _ [.lit ['a'], .lit ['a']] _ rfl rfl rfl
      (.cons _ _ ['a'] ['a'] [] _ _ (.litOk ['a'] ['a'] [] rfl) rfl
        (.cons _ _ ['a'] ['a'] [] _ [] (.litOk ['a'] ['a'] [] rfl) rfl (.nil _)))
      (.eps _))

theorem row3_seq : SObs row3G .callByValueSeq (.call 1 []) ['a'] none :=
  call0_obs (o := .fail) rfl rfl
    (.callSeqArgFail 0 [.lit ['a']] (.lit ['a']) [] _ ['a'] [] [.lit ['a']] rfl rfl rfl
      (.cons _ _ ['a'] ['a'] [] [] _ [] (.litOk ['a'] ['a'] [] rfl) rfl (.nil _)) (.litFail ['a'] [] rfl))

theorem row4_cbn : SObs row4G .callByName (.call 1 []) ['a', 'b'] (some ['a', 'b']) :=
  call0_obs (o := .ok _ ['a', 'b']) rfl rfl (.callNameOk 0 _ _ _ _ _ rfl rfl rfl (.eps _))

theorem row4_par : SObs row4G .callByValuePar (.call 1 []) ['a', 'b'] none :=
  call0_obs (o := .fail) rfl rfl
    (.callParArgFail 0 [.lit ['a']] (.lit ['b']) [] _ ['a', 'b'] [.lit ['a']] rfl rfl rfl
      (.cons _ _ ['a', 'b'] ['a'] ['b'] _ [] (.litOk ['a'] ['a', 'b'] ['b'] rfl) rfl (.nil _))
      (.litFail ['b'] ['a', 'b'] rfl))

theorem row4_seq : SObs row4G .callByValueSeq (.call 1 []) ['a', 'b'] (some []) :=
  call0_obs (o := .ok _ []) rfl rfl
    (.callSeqOk 0 _ _ ['a', 'b'] [] [] [.lit ['a'], .lit ['b']] _ rfl rfl rfl
      (.cons _ _ ['a', 'b'] ['a'] ['b'] [] _ _ (.litOk ['a'] ['a', 'b'] ['b'] rfl) rfl
        (.cons _ _ ['b'] ['b'] [] [] _ [] (.litOk ['b'] ['b'] [] rfl) rfl (.nil _)))
      (.eps _))

/-- The extra row of §7.3: `F(x) ← ε; S ← F(&"a")` on `"b"`. The argument `&"a"` succeeds with zero consumption on
some inputs (those starting with `a`), but not on `"b"`; CBN never evaluates it, Par/Seq fail. So "may succeed on the
empty string" / "consumes nothing when it succeeds" is not a sufficient condition for strategy agreement. -/
def andA : MExp := .notP (.notP (.lit ['a']))
def rowAndG : MGrammar := ⟨[⟨1, .eps⟩, ⟨0, .call 0 [andA]⟩]⟩

theorem rowAnd_cbn : SObs rowAndG .callByName (.call 1 []) ['b'] (some ['b']) :=
  call0_obs (o := .ok _ ['b']) rfl rfl (.callNameOk 0 _ _ _ _ _ rfl rfl rfl (.eps _))

theorem andA_fails_b (s : Strategy) : MDerives rowAndG s andA ['b'] .fail :=
  .notOk _ _ _ _ (.notFail _ _ (.litFail ['a'] ['b'] rfl))

theorem rowAnd_par : SObs rowAndG .callByValuePar (.call 1 []) ['b'] none :=
  call0_obs (r := ⟨0, .call 0 [andA]⟩) (o := .fail) rfl rfl (.callParArgFail 0 [] andA [] _ _ [] rfl rfl rfl (.nil _) (andA_fails_b _))

theorem rowAnd_seq : SObs rowAndG .callByValueSeq (.call 1 []) ['b'] none :=
  call0_obs (r := ⟨0, .call 0 [andA]⟩) (o := .fail) rfl rfl (.callSeqArgFail 0 [] andA [] _ _ _ [] rfl rfl rfl (.nil _) (andA_fails_b _))

/-- `&"a"` does succeed with zero consumption on `"a"`, under every strategy. -/
theorem andA_zero_on_a (s : Strategy) : SObs rowAndG s andA ['a'] (some ['a']) :=
  ⟨_, .notFail _ _ (.notOk _ _ [] _ (.litOk ['a'] ['a'] [] rfl)), rfl⟩

/-! ## §7.2 Short-circuit and non-termination -/

def loopFG : MGrammar := ⟨[⟨0, .call 0 []⟩, ⟨2, .eps⟩]⟩

def loopCall : MExp := .call 0 []
def notEps : MExp := .notP .eps

/-- `Loop()` has no finite derivation under any strategy, for any input and outcome. -/
theorem loop_no_derivation (s : Strategy) {e : MExp} {x : List Char} {o : MOutcome}
    (h : MDerives loopFG s e x o) : e = loopCall → False := by
  induction h using MDerives.rec
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ => True)
  case callNameOk hr _ _ ih =>
    intro he; cases he; simp only [loopFG, ruleAtM, Option.some.injEq] at hr; subst hr; exact ih rfl
  case callNameFail hr _ _ ih =>
    intro he; cases he; simp only [loopFG, ruleAtM, Option.some.injEq] at hr; subst hr; exact ih rfl
  case callParOk hr _ _ _ _ ih =>
    intro he; cases he; simp only [loopFG, ruleAtM, Option.some.injEq] at hr; subst hr; exact ih rfl
  case callParFail hr _ _ _ _ ih =>
    intro he; cases he; simp only [loopFG, ruleAtM, Option.some.injEq] at hr; subst hr; exact ih rfl
  case callSeqOk hr _ _ _ _ ih =>
    intro he; cases he; simp only [loopFG, ruleAtM, Option.some.injEq] at hr; subst hr; exact ih rfl
  case callSeqFail hr _ _ _ _ ih =>
    intro he; cases he; simp only [loopFG, ruleAtM, Option.some.injEq] at hr; subst hr; exact ih rfl
  case callParArgFail pre bad post _ _ _ _ _ _ _ _ _ _ =>
    intro he; simp only [loopCall, MExp.call.injEq] at he; simp at he
  case callSeqArgFail pre bad post _ _ _ _ _ _ _ _ _ _ _ =>
    intro he; simp only [loopCall, MExp.call.injEq] at he; simp at he
  case callMissing hr =>
    intro he; cases he; simp [loopFG, ruleAtM] at hr
  case callArity hr ha =>
    intro he; cases he; simp only [loopFG, ruleAtM, Option.some.injEq] at hr; subst hr; exact ha rfl
  all_goals first
    | trivial
    | (intro he; cases he; done)

theorem loop_no_obs (s : Strategy) (x : List Char) (r : Option (List Char)) : ¬ SObs loopFG s loopCall x r := by
  rintro ⟨o, hd, _⟩; exact loop_no_derivation s hd rfl

/-- CBN: unused arguments do not block the body, whichever of them fails or diverges. -/
theorem cbn_unused_first_fails (x : List Char) : SObs loopFG .callByName (.call 1 [notEps, loopCall]) x (some x) :=
  ⟨_, .callNameOk 1 _ _ x x _ rfl rfl rfl (.eps x), rfl⟩

theorem cbn_unused_first_loops (x : List Char) : SObs loopFG .callByName (.call 1 [loopCall, notEps]) x (some x) :=
  ⟨_, .callNameOk 1 _ _ x x _ rfl rfl rfl (.eps x), rfl⟩

/-- Par/Seq: `F(!ε, Loop())` fails at its first argument; the second is never evaluated. -/
theorem par_shortCircuit (x : List Char) : SObs loopFG .callByValuePar (.call 1 [notEps, loopCall]) x none :=
  ⟨_, .callParArgFail 1 [] notEps [loopCall] _ x [] rfl rfl rfl (.nil x) (.notOk _ _ _ _ (.eps x)), rfl⟩

theorem seq_shortCircuit (x : List Char) : SObs loopFG .callByValueSeq (.call 1 [notEps, loopCall]) x none :=
  ⟨_, .callSeqArgFail 1 [] notEps [loopCall] _ x x [] rfl rfl rfl (.nil x) (.notOk _ _ _ _ (.eps x)), rfl⟩

/-- Par/Seq: `F(Loop(), !ε)` has no derivation at all (its first argument has none). -/
theorem byValue_first_loops (s : Strategy) (hs : s ≠ .callByName) {e : MExp} {x : List Char} {o : MOutcome}
    (h : MDerives loopFG s e x o) : e = .call 1 [loopCall, notEps] → False := by
  intro he
  cases h with
  | callNameOk _ _ _ _ _ _ hs' => exact hs hs'
  | callNameFail _ _ _ _ hs' => exact hs hs'
  | callParOk _ _ _ _ _ _ _ _ _ _ hargs _ =>
    cases he; cases hargs with
    | cons _ _ _ _ _ _ _ h1 _ _ => exact loop_no_derivation s h1 rfl
  | callParFail _ _ _ _ _ _ _ _ hargs _ =>
    cases he; cases hargs with
    | cons _ _ _ _ _ _ _ h1 _ _ => exact loop_no_derivation s h1 rfl
  | callSeqOk _ _ _ _ _ _ _ _ _ _ _ hargs _ =>
    cases he; cases hargs with
    | cons _ _ _ _ _ _ _ _ h1 _ _ => exact loop_no_derivation s h1 rfl
  | callSeqFail _ _ _ _ _ _ _ _ _ hargs _ =>
    cases he; cases hargs with
    | cons _ _ _ _ _ _ _ _ h1 _ _ => exact loop_no_derivation s h1 rfl
  | callParArgFail _ pre bad post _ _ _ _ _ _ hpre hfail =>
    simp only [MExp.call.injEq] at he
    obtain ⟨_, hl⟩ := he
    match pre, hl, hpre with
    | [], hl, _ =>
      simp only [List.nil_append, List.cons.injEq] at hl
      exact loop_no_derivation s hfail hl.1
    | [p], hl, hpre =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at hl
      obtain ⟨rfl, _⟩ := hl
      cases hpre with
      | cons _ _ _ _ _ _ _ h1 _ _ => exact loop_no_derivation s h1 rfl
    | _ :: _ :: _, hl, _ => simp at hl
  | callSeqArgFail _ pre bad post _ _ _ _ _ _ _ hpre hfail =>
    simp only [MExp.call.injEq] at he
    obtain ⟨_, hl⟩ := he
    match pre, hl, hpre with
    | [], hl, hpre =>
      simp only [List.nil_append, List.cons.injEq] at hl
      cases hpre
      exact loop_no_derivation s hfail hl.1
    | [p], hl, hpre =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at hl
      obtain ⟨rfl, _⟩ := hl
      cases hpre with
      | cons _ _ _ _ _ _ _ _ h1 _ _ => exact loop_no_derivation s h1 rfl
    | _ :: _ :: _, hl, _ => simp at hl
  | callMissing _ _ _ hr => cases he; simp [loopFG, ruleAtM] at hr
  | callArity _ _ _ _ hr ha => cases he; simp only [loopFG, ruleAtM, Option.some.injEq] at hr; subst hr; exact ha rfl
  | _ => cases he

theorem par_first_loops (x : List Char) (r : Option (List Char)) :
    ¬ SObs loopFG .callByValuePar (.call 1 [loopCall, notEps]) x r := by
  rintro ⟨o, hd, _⟩; exact byValue_first_loops _ (by decide) hd rfl

theorem seq_first_loops (x : List Char) (r : Option (List Char)) :
    ¬ SObs loopFG .callByValueSeq (.call 1 [loopCall, notEps]) x r := by
  rintro ⟨o, hd, _⟩; exact byValue_first_loops _ (by decide) hd rfl

/-! ## §7.3 Conditional strategy agreement -/

/-- An argument that, under every strategy and on every input, has a derivation succeeding without consuming input. -/
def ZeroArg (g : MGrammar) (a : MExp) : Prop := ∀ s x, ∃ t, MDerives g s a x (.ok t x)

/-- Closed: substitution leaves it unchanged. -/
def Closed (a : MExp) : Prop := ∀ σ, MExp.subst σ a = a

theorem zeroArg_lit_nil (g : MGrammar) : ZeroArg g (.lit []) := fun _ x => ⟨_, .litOk [] x x rfl⟩
theorem zeroArg_eps (g : MGrammar) : ZeroArg g .eps := fun _ x => ⟨_, .eps x⟩
theorem closed_eps : Closed .eps := fun _ => rfl

/-- The fragment: first-order and pure, and every actual argument of every call is a closed `ZeroArg` expression. -/
def ZArgs (g : MGrammar) : MExp → Prop
  | .call _ args => ∀ a ∈ args, Closed a ∧ ZeroArg g a
  | .seq e₁ e₂ => ZArgs g e₁ ∧ ZArgs g e₂
  | .alt e₁ e₂ => ZArgs g e₁ ∧ ZArgs g e₂
  | .star e => ZArgs g e
  | .notP e => ZArgs g e
  | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => False
  | .eps | .any | .chr _ | .range _ _ | .lit _ | .param _ => True

def MGrammar.ZArgs (g : MGrammar) : Prop := ∀ r ∈ g.rules, Shallot.MacroPeg.ZArgs g r.body

mutual
  /-- `Zr g m m'`: same syntax except at positions holding `ZeroArg` expressions (on both sides). -/
  inductive Zr (g : MGrammar) : MExp → MExp → Prop
    | leaf {a a' : MExp} : ZeroArg g a → ZeroArg g a' → Zr g a a'
    | node {a a' : MExp} : ZS g a a' → Zr g a a'

  inductive ZS (g : MGrammar) : MExp → MExp → Prop
    | eps : ZS g .eps .eps
    | any : ZS g .any .any
    | chr (c : Char) : ZS g (.chr c) (.chr c)
    | range (lo hi : Char) : ZS g (.range lo hi) (.range lo hi)
    | lit (s : List Char) : ZS g (.lit s) (.lit s)
    | param (k : Nat) : ZS g (.param k) (.param k)
    | seq {a b a' b' : MExp} : Zr g a a' → Zr g b b' → ZS g (.seq a b) (.seq a' b')
    | alt {a b a' b' : MExp} : Zr g a a' → Zr g b b' → ZS g (.alt a b) (.alt a' b')
    | star {a a' : MExp} : Zr g a a' → ZS g (.star a) (.star a')
    | notP {a a' : MExp} : Zr g a a' → ZS g (.notP a) (.notP a')
    | call (i : Nat) {as : List MExp} : (∀ a ∈ as, Closed a ∧ ZeroArg g a) → ZS g (.call i as) (.call i as)
end

theorem zr_refl {g : MGrammar} : ∀ (e : MExp), ZArgs g e → Zr g e e
  | .eps, _ => .node .eps
  | .any, _ => .node .any
  | .chr c, _ => .node (.chr c)
  | .range lo hi, _ => .node (.range lo hi)
  | .lit s, _ => .node (.lit s)
  | .param k, _ => .node (.param k)
  | .call i _, h => .node (.call i h)
  | .seq a b, h => .node (.seq (zr_refl a h.1) (zr_refl b h.2))
  | .alt a b, h => .node (.alt (zr_refl a h.1) (zr_refl b h.2))
  | .star a, h => .node (.star (zr_refl a h))
  | .notP a, h => .node (.notP (zr_refl a h))
  | .dbg _, h => absurd h id
  | .lam _ _, h => absurd h id
  | .callParam _ _, h => absurd h id
  | .invoke _ _ _, h => absurd h id

theorem argAt_mem : ∀ {σ : List MExp} {k : Nat} {a : MExp}, argAt σ k = some a → a ∈ σ
  | _ :: _, 0, _, h => by cases h; exact List.mem_cons_self
  | _ :: σ, k + 1, _, h => List.mem_cons_of_mem _ (argAt_mem (σ := σ) (k := k) h)

theorem argAt_none_iff : ∀ {σ : List MExp} {k : Nat}, argAt σ k = none ↔ σ.length ≤ k
  | [], _ => by simp [argAt]
  | _ :: _, 0 => by simp [argAt]
  | _ :: σ, k + 1 => by simp [argAt, argAt_none_iff (σ := σ) (k := k)]

theorem substArgs_closed {g : MGrammar} (σ : List MExp) : ∀ {ms : List MExp}, (∀ a ∈ ms, Closed a ∧ ZeroArg g a) →
    MExp.substArgs σ ms = ms
  | [], _ => rfl
  | m :: ms, h => by
    simp only [MExp.substArgs]
    rw [(h m List.mem_cons_self).1 σ, substArgs_closed σ (fun a ha => h a (List.mem_cons_of_mem _ ha))]

/-- Syntactic part: substituting two zero-argument lists of the same length into a fragment body gives related
expressions. -/
theorem zr_subst {g : MGrammar} {σ σ' : List MExp} (hl : σ.length = σ'.length) (hσ : ∀ a ∈ σ, ZeroArg g a)
    (hσ' : ∀ a ∈ σ', ZeroArg g a) : ∀ (c : MExp), ZArgs g c → Zr g (MExp.subst σ c) (MExp.subst σ' c)
  | .eps, _ => .node .eps
  | .any, _ => .node .any
  | .chr c, _ => .node (.chr c)
  | .range lo hi, _ => .node (.range lo hi)
  | .lit s, _ => .node (.lit s)
  | .param k, _ => by
    simp only [MExp.subst]
    cases h : argAt σ k with
    | none =>
      have h' : argAt σ' k = none := argAt_none_iff.2 (hl ▸ argAt_none_iff.1 h)
      rw [h']; exact .node (.notP (.node .eps))
    | some a =>
      cases h' : argAt σ' k with
      | none => exact absurd (argAt_none_iff.2 (hl.symm ▸ argAt_none_iff.1 h')) (by rw [h]; simp)
      | some a' => exact .leaf (hσ a (argAt_mem h)) (hσ' a' (argAt_mem h'))
  | .call i ms, hc => by
    simp only [MExp.subst]
    rw [substArgs_closed σ hc, substArgs_closed σ' hc]
    exact .node (.call i hc)
  | .seq a b, hc => .node (.seq (zr_subst hl hσ hσ' a hc.1) (zr_subst hl hσ hσ' b hc.2))
  | .alt a b, hc => .node (.alt (zr_subst hl hσ hσ' a hc.1) (zr_subst hl hσ hσ' b hc.2))
  | .star a, hc => .node (.star (zr_subst hl hσ hσ' a hc))
  | .notP a, hc => .node (.notP (zr_subst hl hσ hσ' a hc))
  | .dbg _, hc => absurd hc id
  | .lam _ _, hc => absurd hc id
  | .callParam _ _, hc => absurd hc id
  | .invoke _ _ _, hc => absurd hc id

/-- The values a by-value strategy passes for zero arguments: one `.lit []` per argument. -/
def zeroVals (as : List MExp) : List MExp := as.map (fun _ => .lit [])

/-- What the body is substituted with under each strategy, for zero arguments. -/
def stratArgs : Strategy → List MExp → List MExp
  | .callByName, as => as
  | _, as => zeroVals as

theorem zeroVals_zero (g : MGrammar) (as : List MExp) : ∀ a ∈ zeroVals as, ZeroArg g a := by
  intro a ha
  obtain ⟨_, _, rfl⟩ := List.mem_map.1 ha
  exact zeroArg_lit_nil g

theorem stratArgs_zero {g : MGrammar} (s : Strategy) {as : List MExp} (h : ∀ a ∈ as, Closed a ∧ ZeroArg g a) :
    ∀ a ∈ stratArgs s as, ZeroArg g a := by
  cases s
  · exact fun a ha => (h a ha).2
  all_goals exact zeroVals_zero g as

theorem length_stratArgs (s : Strategy) (as : List MExp) : (stratArgs s as).length = as.length := by
  cases s <;> simp [stratArgs, zeroVals]

/-- A zero argument's derivations all succeed without consuming input (determinism). -/
theorem zeroArg_outcome {g : MGrammar} {s : Strategy} {a : MExp} (ha : ZeroArg g a) {x : List Char}
    {o : MOutcome} (hd : MDerives g s a x o) : o.restOf = some x := by
  obtain ⟨t, ht⟩ := ha s x
  rw [mderives_det hd ht]; rfl

theorem argsPar_build {g : MGrammar} (s : Strategy) (x : List Char) :
    ∀ {as : List MExp}, (∀ a ∈ as, ZeroArg g a) → DerivesArgsPar g s x as (zeroVals as)
  | [], _ => .nil x
  | a :: as, h => by
    obtain ⟨t, ht⟩ := h a List.mem_cons_self s x
    exact .cons a as x [] x t _ ht rfl (argsPar_build s x (fun b hb => h b (List.mem_cons_of_mem _ hb)))

theorem argsSeq_build {g : MGrammar} (s : Strategy) (x : List Char) :
    ∀ {as : List MExp}, (∀ a ∈ as, ZeroArg g a) → DerivesArgsSeq g s x as (zeroVals as) x
  | [], _ => .nil x
  | a :: as, h => by
    obtain ⟨t, ht⟩ := h a List.mem_cons_self s x
    exact .cons a as x [] x x t _ ht rfl (argsSeq_build s x (fun b hb => h b (List.mem_cons_of_mem _ hb)))

theorem append_self_eq {p x : List Char} (h : x = p ++ x) : p = [] := by
  have := congrArg List.length h
  rw [List.length_append] at this
  exact List.eq_nil_of_length_eq_zero (by omega)

theorem argsPar_inv {g : MGrammar} {s : Strategy} {x : List Char} :
    ∀ {as vals : List MExp}, (∀ a ∈ as, ZeroArg g a) → DerivesArgsPar g s x as vals → vals = zeroVals as
  | [], _, _, h => by cases h; rfl
  | a :: as, _, hz, h => by
    cases h with
    | cons _ _ _ p rest _ vs h1 hp h2 =>
      have hr := zeroArg_outcome (hz a List.mem_cons_self) h1
      simp only [MOutcome.restOf, Option.some.injEq] at hr
      subst hr
      have := append_self_eq hp
      subst this
      rw [argsPar_inv (fun b hb => hz b (List.mem_cons_of_mem _ hb)) h2]
      rfl

theorem argsSeq_inv {g : MGrammar} {s : Strategy} :
    ∀ {x : List Char} {as vals : List MExp} {mid : List Char}, (∀ a ∈ as, ZeroArg g a) →
      DerivesArgsSeq g s x as vals mid → vals = zeroVals as ∧ mid = x
  | _, [], _, _, _, h => by cases h; exact ⟨rfl, rfl⟩
  | x, a :: as, _, _, hz, h => by
    cases h with
    | cons _ _ _ p rest _ _ vs h1 hp h2 =>
      have hr := zeroArg_outcome (hz a List.mem_cons_self) h1
      simp only [MOutcome.restOf, Option.some.injEq] at hr
      subst hr
      have := append_self_eq hp
      subst this
      obtain ⟨hv, hm⟩ := argsSeq_inv (fun b hb => hz b (List.mem_cons_of_mem _ hb)) h2
      exact ⟨by rw [hv]; rfl, hm⟩

/-- Building a call under any strategy from a derivation of the body substituted with `stratArgs`. -/
theorem call_build {g : MGrammar} (s : Strategy) {i : Nat} {as : List MExp} {r : MRule}
    (hr : ruleAtM g.rules i = some r) (ha : r.arity = as.length) (hz : ∀ a ∈ as, ZeroArg g a) {x : List Char}
    {o : MOutcome} (hd : MDerives g s (MExp.subst (stratArgs s as) r.body) x o) :
    ∃ o', MDerives g s (.call i as) x o' ∧ o'.restOf = o.restOf := by
  cases s <;> cases o with
  | fail => first
    | exact ⟨_, .callNameFail i as r x rfl hr ha hd, rfl⟩
    | exact ⟨_, .callParFail i as r x _ rfl hr ha (argsPar_build _ x hz) hd, rfl⟩
    | exact ⟨_, .callSeqFail i as r x x _ rfl hr ha (argsSeq_build _ x hz) hd, rfl⟩
  | ok t rest => first
    | exact ⟨_, .callNameOk i as r x rest t rfl hr ha hd, rfl⟩
    | exact ⟨_, .callParOk i as r x rest _ t rfl hr ha (argsPar_build _ x hz) hd, rfl⟩
    | exact ⟨_, .callSeqOk i as r x x rest _ t rfl hr ha (argsSeq_build _ x hz) hd, rfl⟩

theorem zr_step {g : MGrammar} {s : Strategy} {a a' : MExp} {x : List Char} {o : MOutcome} (hz : Zr g a a')
    (hd : MDerives g s a x o)
    (ih : ∀ s' m', ZS g a m' → ∃ o', MDerives g s' m' x o' ∧ o'.restOf = o.restOf) (s' : Strategy) :
    ∃ o', MDerives g s' a' x o' ∧ o'.restOf = o.restOf := by
  cases hz with
  | leaf ha ha' =>
    obtain ⟨t, ht⟩ := ha' s' x
    exact ⟨_, ht, (zeroArg_outcome ha hd).symm⟩
  | node hz => exact ih s' _ hz

/-- The call step shared by all three source strategies: the body was derived after substituting a list `σ` of zero
arguments of the right length. -/
theorem zr_call {g : MGrammar} (hg : g.ZArgs) {i : Nat} {as σ : List MExp} {r : MRule} {x : List Char}
    {o : MOutcome} {s₀ : Strategy}
    (hr : ruleAtM g.rules i = some r) (ha : r.arity = as.length) (has : ∀ a ∈ as, Closed a ∧ ZeroArg g a)
    (hσl : σ.length = as.length) (hσ : ∀ a ∈ σ, ZeroArg g a)
    (hd : MDerives g s₀ (MExp.subst σ r.body) x o)
    (ih : ∀ s' m', ZS g (MExp.subst σ r.body) m' → ∃ o', MDerives g s' m' x o' ∧ o'.restOf = o.restOf)
    (s' : Strategy) {wrap : MOutcome}
    (hwrap : wrap.restOf = o.restOf) :
    ∃ o', MDerives g s' (.call i as) x o' ∧ o'.restOf = wrap.restOf := by
  have hz := zr_subst (hσl.trans (length_stratArgs s' as).symm) hσ (stratArgs_zero s' has) r.body
    (hg r (ruleAtM_mem hr))
  obtain ⟨o', hd', ho'⟩ := zr_step hz hd ih s'
  obtain ⟨o'', hd'', ho''⟩ := call_build s' hr ha (fun a h => (has a h).2) hd'
  exact ⟨o'', hd'', ho''.trans (ho'.trans hwrap.symm)⟩

theorem eps_mem_zero {g : MGrammar} {as : List MExp} (has : ∀ a ∈ as, Closed a ∧ ZeroArg g a)
    {s : Strategy} {x : List Char} {a : MExp} (hmem : a ∈ as) (hfail : MDerives g s a x .fail) : False := by
  have := zeroArg_outcome (has a hmem).2 hfail
  cases this

/-- Derivation part: a derivation under one strategy gives one under any other strategy, for related expressions,
with the same observation. -/
theorem zr_preserve {g : MGrammar} (hg : g.ZArgs) {s : Strategy} {m : MExp} {x : List Char} {o : MOutcome}
    (h : MDerives g s m x o) :
    ∀ s' m', ZS g m m' → ∃ o', MDerives g s' m' x o' ∧ o'.restOf = o.restOf := by
  induction h using MDerives.rec
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ => True)
  case eps input => intro s' m' hz; cases hz; exact ⟨_, .eps input, rfl⟩
  case anyOk c rest => intro s' m' hz; cases hz; exact ⟨_, .anyOk c rest, rfl⟩
  case anyFail => intro s' m' hz; cases hz; exact ⟨_, .anyFail, rfl⟩
  case chrOk c d rest hb => intro s' m' hz; cases hz; exact ⟨_, .chrOk c d rest hb, rfl⟩
  case chrFail c d rest hb => intro s' m' hz; cases hz; exact ⟨_, .chrFail c d rest hb, rfl⟩
  case chrEmpty c => intro s' m' hz; cases hz; exact ⟨_, .chrEmpty c, rfl⟩
  case rangeOk lo hi d rest hb => intro s' m' hz; cases hz; exact ⟨_, .rangeOk lo hi d rest hb, rfl⟩
  case rangeFail lo hi d rest hb => intro s' m' hz; cases hz; exact ⟨_, .rangeFail lo hi d rest hb, rfl⟩
  case rangeEmpty lo hi => intro s' m' hz; cases hz; exact ⟨_, .rangeEmpty lo hi, rfl⟩
  case litOk str input rest hb => intro s' m' hz; cases hz; exact ⟨_, .litOk str input rest hb, rfl⟩
  case litFail str input hb => intro s' m' hz; cases hz; exact ⟨_, .litFail str input hb, rfl⟩
  case paramFail k input => intro s' m' hz; cases hz; exact ⟨_, .paramFail k input, rfl⟩
  case callNameOk i args r input rest t _ hr ha hd ih =>
    intro s' m' hz
    cases hz with
    | call _ has =>
      exact zr_call hg hr ha has rfl (fun a h => (has a h).2) hd ih s' rfl
  case callNameFail i args r input _ hr ha hd ih =>
    intro s' m' hz
    cases hz with
    | call _ has =>
      exact zr_call hg hr ha has rfl (fun a h => (has a h).2) hd ih s' rfl
  case callParOk i args r input rest vals t _ hr ha hargs hd _ ih =>
    intro s' m' hz
    cases hz with
    | call _ has =>
      have hv := argsPar_inv (fun a h => (has a h).2) hargs
      subst hv
      exact zr_call hg hr ha has (by simp [zeroVals]) (zeroVals_zero g args) hd ih s' rfl
  case callParFail i args r input vals _ hr ha hargs hd _ ih =>
    intro s' m' hz
    cases hz with
    | call _ has =>
      have hv := argsPar_inv (fun a h => (has a h).2) hargs
      subst hv
      exact zr_call hg hr ha has (by simp [zeroVals]) (zeroVals_zero g args) hd ih s' rfl
  case callSeqOk i args r input mid rest vals t _ hr ha hargs hd _ ih =>
    intro s' m' hz
    cases hz with
    | call _ has =>
      obtain ⟨hv, hm⟩ := argsSeq_inv (fun a h => (has a h).2) hargs
      subst hv; subst hm
      exact zr_call hg hr ha has (by simp [zeroVals]) (zeroVals_zero g args) hd ih s' rfl
  case callSeqFail i args r input mid vals _ hr ha hargs hd _ ih =>
    intro s' m' hz
    cases hz with
    | call _ has =>
      obtain ⟨hv, hm⟩ := argsSeq_inv (fun a h => (has a h).2) hargs
      subst hv; subst hm
      exact zr_call hg hr ha has (by simp [zeroVals]) (zeroVals_zero g args) hd ih s' rfl
  case callParArgFail i pre bad post r input preVals _ hr ha hpre hfail _ _ =>
    intro s' m' hz
    cases hz with
    | call _ has => exact (eps_mem_zero has (by simp) hfail).elim
  case callSeqArgFail i pre bad post r input mid preVals _ hr ha hpre hfail _ _ =>
    intro s' m' hz
    cases hz with
    | call _ has => exact (eps_mem_zero has (by simp) hfail).elim
  case callMissing i args input hr =>
    intro s' m' hz; cases hz; exact ⟨_, .callMissing i _ input hr, rfl⟩
  case callArity i args r input hr ha =>
    intro s' m' hz; cases hz; exact ⟨_, .callArity i _ r input hr ha, rfl⟩
  case seqOk e₁ e₂ input rest₁ rest₂ t₁ t₂ h₁ h₂ ih₁ ih₂ =>
    intro s' m' hz
    cases hz with
    | seq hz₁ hz₂ =>
      obtain ⟨o₁, d₁, c₁⟩ := zr_step hz₁ h₁ ih₁ s'
      obtain ⟨t₁', rfl⟩ := restOf_eq_some c₁
      obtain ⟨o₂, d₂, c₂⟩ := zr_step hz₂ h₂ ih₂ s'
      obtain ⟨t₂', rfl⟩ := restOf_eq_some c₂
      exact ⟨_, .seqOk _ _ _ _ _ _ _ d₁ d₂, rfl⟩
  case seqFail₁ e₁ e₂ input h₁ ih₁ =>
    intro s' m' hz
    cases hz with
    | seq hz₁ _ =>
      obtain ⟨o₁, d₁, c₁⟩ := zr_step hz₁ h₁ ih₁ s'
      have := restOf_eq_none c₁; subst this
      exact ⟨_, .seqFail₁ _ _ _ d₁, rfl⟩
  case seqFail₂ e₁ e₂ input rest₁ t₁ h₁ h₂ ih₁ ih₂ =>
    intro s' m' hz
    cases hz with
    | seq hz₁ hz₂ =>
      obtain ⟨o₁, d₁, c₁⟩ := zr_step hz₁ h₁ ih₁ s'
      obtain ⟨t₁', rfl⟩ := restOf_eq_some c₁
      obtain ⟨o₂, d₂, c₂⟩ := zr_step hz₂ h₂ ih₂ s'
      have := restOf_eq_none c₂; subst this
      exact ⟨_, .seqFail₂ _ _ _ _ _ d₁ d₂, rfl⟩
  case altL e₁ e₂ input rest t h₁ ih₁ =>
    intro s' m' hz
    cases hz with
    | alt hz₁ _ =>
      obtain ⟨o₁, d₁, c₁⟩ := zr_step hz₁ h₁ ih₁ s'
      obtain ⟨t₁', rfl⟩ := restOf_eq_some c₁
      exact ⟨_, .altL _ _ _ _ _ d₁, rfl⟩
  case altR e₁ e₂ input rest t h₁ h₂ ih₁ ih₂ =>
    intro s' m' hz
    cases hz with
    | alt hz₁ hz₂ =>
      obtain ⟨o₁, d₁, c₁⟩ := zr_step hz₁ h₁ ih₁ s'
      have := restOf_eq_none c₁; subst this
      obtain ⟨o₂, d₂, c₂⟩ := zr_step hz₂ h₂ ih₂ s'
      obtain ⟨t₂', rfl⟩ := restOf_eq_some c₂
      exact ⟨_, .altR _ _ _ _ _ d₁ d₂, rfl⟩
  case altFail e₁ e₂ input h₁ h₂ ih₁ ih₂ =>
    intro s' m' hz
    cases hz with
    | alt hz₁ hz₂ =>
      obtain ⟨o₁, d₁, c₁⟩ := zr_step hz₁ h₁ ih₁ s'
      have := restOf_eq_none c₁; subst this
      obtain ⟨o₂, d₂, c₂⟩ := zr_step hz₂ h₂ ih₂ s'
      have := restOf_eq_none c₂; subst this
      exact ⟨_, .altFail _ _ _ d₁ d₂, rfl⟩
  case starNil e input h₁ ih₁ =>
    intro s' m' hz
    cases hz with
    | star hz₁ =>
      obtain ⟨o₁, d₁, c₁⟩ := zr_step hz₁ h₁ ih₁ s'
      have := restOf_eq_none c₁; subst this
      exact ⟨_, .starNil _ _ d₁, rfl⟩
  case starCons e input rest rest' t ts h₁ _ ih₁ ih₂ =>
    intro s' m' hz
    cases hz with
    | star hz₁ =>
      obtain ⟨o₁, d₁, c₁⟩ := zr_step hz₁ h₁ ih₁ s'
      obtain ⟨t₁', rfl⟩ := restOf_eq_some c₁
      obtain ⟨o₂, d₂, c₂⟩ := ih₂ s' _ (.star hz₁)
      obtain ⟨t₂', rfl⟩ := restOf_eq_some c₂
      exact ⟨_, .starCons _ _ _ _ _ _ d₁ d₂, rfl⟩
  case notOk e input rest t h₁ ih₁ =>
    intro s' m' hz
    cases hz with
    | notP hz₁ =>
      obtain ⟨o₁, d₁, c₁⟩ := zr_step hz₁ h₁ ih₁ s'
      obtain ⟨t₁', rfl⟩ := restOf_eq_some c₁
      exact ⟨_, .notOk _ _ _ _ d₁, rfl⟩
  case notFail e input h₁ ih₁ =>
    intro s' m' hz
    cases hz with
    | notP hz₁ =>
      obtain ⟨o₁, d₁, c₁⟩ := zr_step hz₁ h₁ ih₁ s'
      have := restOf_eq_none c₁; subst this
      exact ⟨_, .notFail _ _ d₁, rfl⟩
  all_goals first
    | trivial
    | (intro s' m' hz; cases hz; done)

/-- **Conditional strategy agreement (§7.3).** If every rule body and the start expression `e` are first-order and pure,
and every actual argument occurring in them (used or not) is closed and, under every strategy and on every input,
succeeds without consuming input, then all three strategies have the same observations of `e` on every input. -/
theorem strategy_agree {g : MGrammar} (hg : g.ZArgs) {e : MExp} (he : ZArgs g e) (s s' : Strategy)
    (x : List Char) (r : Option (List Char)) : SObs g s e x r ↔ SObs g s' e x r := by
  have key : ∀ s₁ s₂, SObs g s₁ e x r → SObs g s₂ e x r := by
    rintro s₁ s₂ ⟨o, hd, rfl⟩
    obtain ⟨o', hd', ho'⟩ := zr_step (zr_refl e he) hd (fun s' m' hz => zr_preserve hg hd s' m' hz) s₂
    exact ⟨o', hd', ho'⟩
  exact ⟨key s s', key s' s⟩

/-! ### The syntactic-`ε` fragment (the first instance) -/

/-- Every actual argument is syntactically `ε`. -/
def EpsArgs : MExp → Prop
  | .call _ args => ∀ a ∈ args, a = .eps
  | .seq e₁ e₂ => EpsArgs e₁ ∧ EpsArgs e₂
  | .alt e₁ e₂ => EpsArgs e₁ ∧ EpsArgs e₂
  | .star e => EpsArgs e
  | .notP e => EpsArgs e
  | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => False
  | .eps | .any | .chr _ | .range _ _ | .lit _ | .param _ => True

theorem zArgs_of_epsArgs (g : MGrammar) : ∀ (e : MExp), EpsArgs e → ZArgs g e
  | .call _ _, h => fun a ha => by rw [h a ha]; exact ⟨closed_eps, zeroArg_eps g⟩
  | .seq a b, h => ⟨zArgs_of_epsArgs g a h.1, zArgs_of_epsArgs g b h.2⟩
  | .alt a b, h => ⟨zArgs_of_epsArgs g a h.1, zArgs_of_epsArgs g b h.2⟩
  | .star a, h => zArgs_of_epsArgs g a h
  | .notP a, h => zArgs_of_epsArgs g a h
  | .eps, _ | .any, _ | .chr _, _ | .range _ _, _ | .lit _, _ | .param _, _ => trivial
  | .dbg _, h | .lam _ _, h | .callParam _ _, h | .invoke _ _ _, h => absurd h id

/-- All actual arguments syntactically `ε` (start call included): the three strategies agree. -/
theorem strategy_agree_eps {g : MGrammar} (hg : ∀ r ∈ g.rules, EpsArgs r.body) {e : MExp} (he : EpsArgs e)
    (s s' : Strategy) (x : List Char) (r : Option (List Char)) : SObs g s e x r ↔ SObs g s' e x r :=
  strategy_agree (fun r hr => zArgs_of_epsArgs g r.body (hg r hr)) (zArgs_of_epsArgs g e he) s s' x r

end Shallot.MacroPeg
