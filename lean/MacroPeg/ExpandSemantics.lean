import MacroPeg.Expand
import MacroPeg.Determinism
import MacroPeg.Soundness
import MacroPeg.Completeness
import MacroPeg.Examples

/-!
# Macro expansion preserves call-by-name semantics (M-PEG-6)

M-PEG-5 proved that `MExp.expand` terminates on acyclic grammars and reaches the
"no calls remain" fixpoint (T-fix). This module proves what a user of the reference
`ParserGenerator.tryInlineHigherOrder` path actually relies on: **inlining does not
change what is accepted**. If the original grammar derives an outcome for `e` under
`CallByName`, the expanded grammar derives the same outcome (same failure, or success
with the same remaining input — parse trees necessarily differ, since `.nodeCall`
nodes disappear) for `MExp.expand e`.

Two well-formedness conditions turned out to be NECESSARY, each with a machine-checked
witness below (`ce004_*`, `ce005_*`):

- **Arity correctness** (`ArityOk`): every `.call` in the program refers to an existing
  rule with matching arity. The evaluator fails a mismatched call (`callArity`/
  `callMissing`), but `expand` never looks at the argument count — it simply
  substitutes — so `F(x) = "a"` called as `F("b", "c")` fails before expansion and
  matches `"a"` after. The reference `TypeChecker` rejects such programs, so this is
  the same assumption the Scala pipeline already makes.
- **No callable-valued rules** (`NoCallableRules`): no rule body expands to a lambda or
  to a bare parameter. Otherwise a `.call` whose value is a callable can be passed to
  a `.callParam` — the closure-return pattern `Baz(f) = f; Apply(f, s) = f(s);
  Apply(Baz(λx.x), "a")`, which the evaluator (reference and formal alike) fails but
  expansion accepts (`Examples.lean`'s `#guard`s already record the flip). This is a
  genuine semantic gap of the reference `MacroExpander`, not a formalization artifact.

A third issue was in the formalization itself and is fixed rather than assumed away:
`MExp.subst` used to collapse a `.callParam k` whose actual argument was a still-
unresolved `.param j` to `failAlways`, so the pass-through pattern `Baz(f, s) =
Apply(f, s); Apply(f, s) = f(s)` expanded to `failAlways` — diverging from the
reference `MacroExpander`, which handles it (verified this session: the reference
expands `S = Baz(λx.x, "a") !.` to `"a" !.`). `subst` now re-targets such a
`.callParam` to the outer parameter (`Syntax.lean`), which is unreachable in
derivations (their actual parameters are closed) but exactly what `expand`'s
"expand callee body first, substitute after" order needs. `ce004_passThrough` pins the
fixed behaviour.

Proof architecture: `subst_subst` (substitution composes), `expand_subst`
(`expand` commutes with `subst`, needing only `NoCallableRules`), then a single
induction over `MDerives` (`expand_preserves_cbn`), carrying `ArityOk` of the current
expression as part of the motive. Strategy is fixed to `.callByName` throughout —
under `CallByValuePar`/`CallByValueSeq`, inlining is NOT semantics-preserving even
for first-order grammars (CE-001's `F(x) = "b"` witness: the strategy-specific
argument evaluation is exactly what inlining erases), so no such theorem is possible.
-/

namespace Shallot.MacroPeg

/-! ## List helpers: `substArgs`/`expandArgs` are maps, and preserve length -/

theorem argAt_substArgs (args : List MExp) :
    ∀ (margs : List MExp) (k : Nat),
      argAt (MExp.substArgs args margs) k = (argAt margs k).map (MExp.subst args)
  | [], _ => by simp [MExp.substArgs, argAt]
  | _ :: _, 0 => by simp [MExp.substArgs, argAt]
  | _ :: ms, k + 1 => by simp [MExp.substArgs, argAt, argAt_substArgs args ms k]

theorem length_substArgs (args : List MExp) :
    ∀ margs : List MExp, (MExp.substArgs args margs).length = margs.length
  | [] => by simp [MExp.substArgs]
  | _ :: ms => by simp [MExp.substArgs, length_substArgs args ms]

theorem argAt_expandArgs (g : MGrammar) (h : acyclicB g = true) :
    ∀ (es : List MExp) (k : Nat),
      argAt (MExp.expandArgs g h es) k = (argAt es k).map (MExp.expand g h)
  | [], _ => by simp [MExp.expandArgs, argAt]
  | _ :: _, 0 => by simp [MExp.expandArgs, argAt]
  | _ :: es, k + 1 => by simp [MExp.expandArgs, argAt, argAt_expandArgs g h es k]

theorem length_expandArgs (g : MGrammar) (h : acyclicB g = true) :
    ∀ es : List MExp, (MExp.expandArgs g h es).length = es.length
  | [] => by simp [MExp.expandArgs]
  | _ :: es => by simp [MExp.expandArgs, length_expandArgs g h es]

theorem ruleAtM_map (f : MRule → MRule) :
    ∀ (rs : List MRule) (i : Nat), ruleAtM (rs.map f) i = (ruleAtM rs i).map f
  | [], _ => by simp [ruleAtM]
  | _ :: _, 0 => by simp [ruleAtM]
  | _ :: rs, i + 1 => by simp [ruleAtM, ruleAtM_map f rs i]

/-- Rule lookup in the expanded grammar: same index, same arity, expanded body. -/
theorem ruleAtM_expandGrammar (g : MGrammar) (h : acyclicB g = true) (i : Nat) :
    ruleAtM (MGrammar.expandGrammar g h).rules i =
      (ruleAtM g.rules i).map (fun r => { arity := r.arity, body := MExp.expand g h r.body }) := by
  simp [MGrammar.expandGrammar, ruleAtM_map]

theorem expandRule_eq_of_some (g : MGrammar) (h : acyclicB g = true) {i : Nat} {r : MRule}
    (hr : ruleAtM g.rules i = some r) : MExp.expandRule g h i = MExp.expand g h r.body := by
  unfold MExp.expandRule
  split
  · next heq => rw [heq] at hr; cases hr
  · next heq => rw [heq] at hr; cases hr; rfl

theorem expandRule_eq_of_none (g : MGrammar) (h : acyclicB g = true) {i : Nat}
    (hr : ruleAtM g.rules i = none) : MExp.expandRule g h i = MExp.failAlways := by
  unfold MExp.expandRule
  split
  · rfl
  · next heq => rw [heq] at hr; cases hr

/-! ## `failAlways` is a fixed point of both `subst` and `expand` -/

theorem subst_failAlways (args : List MExp) : MExp.subst args MExp.failAlways = MExp.failAlways := by
  simp [MExp.failAlways, MExp.subst]

theorem expand_failAlways (g : MGrammar) (h : acyclicB g = true) :
    MExp.expand g h MExp.failAlways = MExp.failAlways := by
  simp [MExp.failAlways, MExp.expand]

/-! ## Callable-valued expressions

`subst`'s `.callParam` case dispatches on whether the resolved argument is a `.lam`
(invoke), a `.param` (pass through), or anything else (fail). `expand`/`subst` can
turn one of the "anything else" shapes into a `.lam`/`.param` only through a rule whose
expanded body IS a `.lam`/`.param` — which `NoCallableRules` forbids. -/

/-- Is `e` syntactically a callable value or an unresolved parameter reference? -/
def MExp.isLamOrParam : MExp → Bool
  | .lam _ _ => true
  | .param _ => true
  | _ => false

/-- No rule of `g` expands to a lambda or to a bare parameter — i.e. no rule "returns a
callable". Stated on `expand`ed bodies (the shape `expand` actually splices), which is
what the commutation lemma needs; `noCallableRulesB` below is the decidable check. -/
def NoCallableRules (g : MGrammar) (h : acyclicB g = true) : Prop :=
  ∀ (i : Nat) (r : MRule), ruleAtM g.rules i = some r →
    (MExp.expand g h r.body).isLamOrParam = false

def noCallableRulesB (g : MGrammar) (h : acyclicB g = true) : Bool :=
  (MGrammar.expandGrammar g h).rules.all (fun r => !r.body.isLamOrParam)

theorem ruleAtM_mem : ∀ {rs : List MRule} {i : Nat} {r : MRule}, ruleAtM rs i = some r → r ∈ rs
  | _ :: _, 0, _, h => by simp [ruleAtM] at h; simp [h]
  | _ :: rs, i + 1, r, h => by
    simp only [ruleAtM] at h
    exact List.mem_cons_of_mem _ (ruleAtM_mem h)

theorem noCallableRules_of_B (g : MGrammar) (h : acyclicB g = true)
    (hb : noCallableRulesB g h = true) : NoCallableRules g h := by
  intro i r hr
  have hmem : ({ arity := r.arity, body := MExp.expand g h r.body } : MRule) ∈
      (MGrammar.expandGrammar g h).rules := by
    simp only [MGrammar.expandGrammar, List.mem_map]
    exact ⟨r, ruleAtM_mem hr, rfl⟩
  simp only [noCallableRulesB, List.all_eq_true] at hb
  have := hb _ hmem
  simpa using this

/-- `subst` never manufactures a callable/parameter out of a non-callable,
non-parameter expression. -/
theorem subst_isLamOrParam_false (args : List MExp) :
    ∀ e : MExp, e.isLamOrParam = false → (MExp.subst args e).isLamOrParam = false
  | .eps, _ => by simp [MExp.subst, MExp.isLamOrParam]
  | .any, _ => by simp [MExp.subst, MExp.isLamOrParam]
  | .chr _, _ => by simp [MExp.subst, MExp.isLamOrParam]
  | .range _ _, _ => by simp [MExp.subst, MExp.isLamOrParam]
  | .lit _, _ => by simp [MExp.subst, MExp.isLamOrParam]
  | .param _, h => by simp [MExp.isLamOrParam] at h
  | .lam _ _, h => by simp [MExp.isLamOrParam] at h
  | .call _ _, _ => by simp [MExp.subst, MExp.isLamOrParam]
  | .seq _ _, _ => by simp [MExp.subst, MExp.isLamOrParam]
  | .alt _ _, _ => by simp [MExp.subst, MExp.isLamOrParam]
  | .star _, _ => by simp [MExp.subst, MExp.isLamOrParam]
  | .notP _, _ => by simp [MExp.subst, MExp.isLamOrParam]
  | .dbg _, _ => by simp [MExp.subst, MExp.isLamOrParam]
  | .invoke _ _ _, _ => by simp [MExp.subst, MExp.isLamOrParam]
  | .callParam k _, _ => by
    simp only [MExp.subst]
    cases argAt args k with
    | none => simp [MExp.failAlways, MExp.isLamOrParam]
    | some a => cases a <;> simp [MExp.failAlways, MExp.isLamOrParam]

/-- Same for `expand`, given `NoCallableRules` (the only way `expand` could produce a
`.lam`/`.param` from a non-`.lam`/`.param` is by inlining a callable-valued rule). -/
theorem expand_isLamOrParam_false (g : MGrammar) (h : acyclicB g = true)
    (hnc : NoCallableRules g h) :
    ∀ e : MExp, e.isLamOrParam = false → (MExp.expand g h e).isLamOrParam = false
  | .eps, _ => by simp [MExp.expand, MExp.isLamOrParam]
  | .any, _ => by simp [MExp.expand, MExp.isLamOrParam]
  | .chr _, _ => by simp [MExp.expand, MExp.isLamOrParam]
  | .range _ _, _ => by simp [MExp.expand, MExp.isLamOrParam]
  | .lit _, _ => by simp [MExp.expand, MExp.isLamOrParam]
  | .param _, h => by simp [MExp.isLamOrParam] at h
  | .lam _ _, h => by simp [MExp.isLamOrParam] at h
  | .call _ [], _ => by simp [MExp.expand, MExp.isLamOrParam]
  | .call i (a :: as), _ => by
    simp only [MExp.expand]
    apply subst_isLamOrParam_false
    cases hr : ruleAtM g.rules i with
    | none => rw [expandRule_eq_of_none g h hr]; simp [MExp.failAlways, MExp.isLamOrParam]
    | some r => rw [expandRule_eq_of_some g h hr]; exact hnc i r hr
  | .seq _ _, _ => by simp [MExp.expand, MExp.isLamOrParam]
  | .alt _ _, _ => by simp [MExp.expand, MExp.isLamOrParam]
  | .star _, _ => by simp [MExp.expand, MExp.isLamOrParam]
  | .notP _, _ => by simp [MExp.expand, MExp.isLamOrParam]
  | .dbg _, _ => by simp [MExp.expand, MExp.isLamOrParam]
  | .invoke _ _ _, _ => by simp [MExp.expand, MExp.isLamOrParam]
  | .callParam _ _, _ => by simp [MExp.expand, MExp.isLamOrParam]

/-! ## Substitution composes

`subst A (subst M e) = subst (substArgs A M) e`, unconditionally — the pass-through
case of `subst` (`Syntax.lean`) is exactly what makes the `.callParam`/`.param j`
sub-case go through. -/

mutual
  theorem subst_subst (A M : List MExp) :
      ∀ e : MExp, MExp.subst A (MExp.subst M e) = MExp.subst (MExp.substArgs A M) e
    | .eps => by simp [MExp.subst]
    | .any => by simp [MExp.subst]
    | .chr _ => by simp [MExp.subst]
    | .range _ _ => by simp [MExp.subst]
    | .lit _ => by simp [MExp.subst]
    | .param k => by
      simp only [MExp.subst, argAt_substArgs]
      cases argAt M k with
      | none => simp [subst_failAlways]
      | some a => simp
    | .call i margs => by simp [MExp.subst, substArgs_subst A M margs]
    | .seq e₁ e₂ => by simp [MExp.subst, subst_subst A M e₁, subst_subst A M e₂]
    | .alt e₁ e₂ => by simp [MExp.subst, subst_subst A M e₁, subst_subst A M e₂]
    | .star e => by simp [MExp.subst, subst_subst A M e]
    | .notP e => by simp [MExp.subst, subst_subst A M e]
    | .dbg e => by simp [MExp.subst, subst_subst A M e]
    | .lam _ _ => by simp [MExp.subst]
    | .invoke _ _ margs => by simp [MExp.subst, substArgs_subst A M margs]
    | .callParam k margs => by
      simp only [MExp.subst, argAt_substArgs]
      cases hM : argAt M k with
      | none => simp [subst_failAlways]
      | some a =>
        cases a with
        | lam ar bod => simp [MExp.subst, substArgs_subst A M margs]
        | param j =>
          simp only [Option.map_some, MExp.subst]
          cases argAt A j with
          | none => simp [MExp.failAlways]
          | some b =>
            cases b <;> simp [MExp.subst, substArgs_subst A M margs, MExp.failAlways]
        | callParam k' margs' =>
          -- The argument is itself an unresolved `.callParam`: `subst A` turns it into
          -- an `.invoke`, a `.callParam`, or `failAlways` — never a `.lam`/`.param` —
          -- so both sides are `failAlways`.
          simp only [Option.map_some, MExp.subst, subst_failAlways]
          cases argAt A k' with
          | none => simp [MExp.failAlways]
          | some b => cases b <;> simp [MExp.failAlways]
        | _ =>
          -- Any other non-callable, non-parameter argument stays that way under
          -- `subst A`, so both sides are `failAlways`.
          simp [MExp.subst, subst_failAlways, MExp.failAlways]

  theorem substArgs_subst (A M : List MExp) :
      ∀ margs : List MExp,
        MExp.substArgs A (MExp.substArgs M margs) = MExp.substArgs (MExp.substArgs A M) margs
    | [] => by simp [MExp.substArgs]
    | e :: es => by simp [MExp.substArgs, subst_subst A M e, substArgs_subst A M es]
end

/-! ## How `subst` resolves a `.callParam`, case by case (no `match` left behind) -/

theorem subst_callParam_none {B : List MExp} {k : Nat} (margs : List MExp)
    (hB : argAt B k = none) : MExp.subst B (.callParam k margs) = MExp.failAlways := by
  simp [MExp.subst, hB]

theorem subst_callParam_lam {B : List MExp} {k ar : Nat} {bod : MExp} (margs : List MExp)
    (hB : argAt B k = some (.lam ar bod)) :
    MExp.subst B (.callParam k margs) = .invoke ar bod (MExp.substArgs B margs) := by
  simp [MExp.subst, hB]

theorem subst_callParam_param {B : List MExp} {k j : Nat} (margs : List MExp)
    (hB : argAt B k = some (.param j)) :
    MExp.subst B (.callParam k margs) = .callParam j (MExp.substArgs B margs) := by
  simp [MExp.subst, hB]

theorem subst_callParam_of_not {B : List MExp} {k : Nat} (margs : List MExp) {a : MExp}
    (hB : argAt B k = some a) (ha : a.isLamOrParam = false) :
    MExp.subst B (.callParam k margs) = MExp.failAlways := by
  simp only [MExp.subst, hB]
  cases a <;> simp_all [MExp.isLamOrParam]

/-! ## `expand` commutes with `subst`

`expand (subst B e) = subst (expandArgs B) (expand e)`, given `NoCallableRules`. This is
the key fact: `expand`'s "expand the callee body and the actual parameters
independently, then substitute" order (M-PEG-5's deliberate divergence from the
reference's "substitute, then re-expand") agrees with the evaluator's "substitute,
then derive" order up to expansion of the pieces. -/

mutual
  theorem expand_subst (g : MGrammar) (h : acyclicB g = true) (hnc : NoCallableRules g h)
      (B : List MExp) :
      ∀ e : MExp,
        MExp.expand g h (MExp.subst B e) = MExp.subst (MExp.expandArgs g h B) (MExp.expand g h e)
    | .eps => by simp [MExp.subst, MExp.expand]
    | .any => by simp [MExp.subst, MExp.expand]
    | .chr _ => by simp [MExp.subst, MExp.expand]
    | .range _ _ => by simp [MExp.subst, MExp.expand]
    | .lit _ => by simp [MExp.subst, MExp.expand]
    | .param k => by
      simp only [MExp.subst, MExp.expand, argAt_expandArgs]
      cases argAt B k with
      | none => simp [expand_failAlways]
      | some a => simp
    | .call _ [] => by simp [MExp.subst, MExp.substArgs, MExp.expand]
    | .call i (a :: as) => by
      have hl := expandArgs_subst g h hnc B (a :: as)
      simp only [MExp.subst, MExp.substArgs] at hl ⊢
      simp only [MExp.expand, MExp.expandArgs] at hl ⊢
      rw [subst_subst, hl]
    | .seq e₁ e₂ => by
      simp [MExp.subst, MExp.expand, expand_subst g h hnc B e₁, expand_subst g h hnc B e₂]
    | .alt e₁ e₂ => by
      simp [MExp.subst, MExp.expand, expand_subst g h hnc B e₁, expand_subst g h hnc B e₂]
    | .star e => by simp [MExp.subst, MExp.expand, expand_subst g h hnc B e]
    | .notP e => by simp [MExp.subst, MExp.expand, expand_subst g h hnc B e]
    | .dbg e => by simp [MExp.subst, MExp.expand, expand_subst g h hnc B e]
    | .lam _ _ => by simp [MExp.subst, MExp.expand]
    | .invoke _ _ margs => by
      simp [MExp.subst, MExp.expand, expandArgs_subst g h hnc B margs]
    | .callParam k margs => by
      have hl := expandArgs_subst g h hnc B margs
      have hrhs : MExp.expand g h (.callParam k margs) = .callParam k (MExp.expandArgs g h margs) := by
        simp [MExp.expand]
      rw [hrhs]
      cases hB : argAt B k with
      | none =>
        have hB' : argAt (MExp.expandArgs g h B) k = none := by rw [argAt_expandArgs, hB]; rfl
        rw [subst_callParam_none margs hB, expand_failAlways, subst_callParam_none _ hB']
      | some a =>
        have hB' : argAt (MExp.expandArgs g h B) k = some (MExp.expand g h a) := by
          rw [argAt_expandArgs, hB]; rfl
        cases a with
        | lam ar bod =>
          rw [subst_callParam_lam margs hB]
          simp only [MExp.expand] at hB' ⊢
          rw [subst_callParam_lam _ hB', hl]
        | param j =>
          rw [subst_callParam_param margs hB]
          simp only [MExp.expand] at hB' ⊢
          rw [subst_callParam_param _ hB', hl]
        | _ =>
          rw [subst_callParam_of_not margs hB (by simp [MExp.isLamOrParam]), expand_failAlways,
            subst_callParam_of_not _ hB'
              (expand_isLamOrParam_false g h hnc _ (by simp [MExp.isLamOrParam]))]

  theorem expandArgs_subst (g : MGrammar) (h : acyclicB g = true) (hnc : NoCallableRules g h)
      (B : List MExp) :
      ∀ margs : List MExp,
        MExp.expandArgs g h (MExp.substArgs B margs) =
          MExp.substArgs (MExp.expandArgs g h B) (MExp.expandArgs g h margs)
    | [] => by simp [MExp.substArgs, MExp.expandArgs]
    | e :: es => by
      simp [MExp.substArgs, MExp.expandArgs, expand_subst g h hnc B e, expandArgs_subst g h hnc B es]
end

/-! ## Arity correctness

Every `.call` refers to an existing rule of matching arity — the evaluator's
`callMissing`/`callArity` failures never fire. Checked structurally, into `.lam`/`.invoke`
bodies and actual-parameter lists alike, so that it is preserved by `subst` (the shape
the evaluator actually derives). -/

mutual
  def MExp.arityOk (g : MGrammar) : MExp → Bool
    | .call i args =>
      (match ruleAtM g.rules i with
        | some r => r.arity == args.length
        | none => false) && MExp.arityOkArgs g args
    | .seq e₁ e₂ => MExp.arityOk g e₁ && MExp.arityOk g e₂
    | .alt e₁ e₂ => MExp.arityOk g e₁ && MExp.arityOk g e₂
    | .star e => MExp.arityOk g e
    | .notP e => MExp.arityOk g e
    | .dbg e => MExp.arityOk g e
    | .lam _ bod => MExp.arityOk g bod
    | .callParam _ args => MExp.arityOkArgs g args
    | .invoke _ bod args => MExp.arityOk g bod && MExp.arityOkArgs g args
    | .eps => true
    | .any => true
    | .chr _ => true
    | .range _ _ => true
    | .lit _ => true
    | .param _ => true

  def MExp.arityOkArgs (g : MGrammar) : List MExp → Bool
    | [] => true
    | e :: es => MExp.arityOk g e && MExp.arityOkArgs g es
end

/-- Every rule body of `g` is arity-correct (the whole-program condition). -/
def MGrammar.arityOk (g : MGrammar) : Bool := g.rules.all (fun r => MExp.arityOk g r.body)

theorem arityOk_rule {g : MGrammar} (hg : g.arityOk = true) {i : Nat} {r : MRule}
    (hr : ruleAtM g.rules i = some r) : MExp.arityOk g r.body = true := by
  simp only [MGrammar.arityOk, List.all_eq_true] at hg
  exact hg r (ruleAtM_mem hr)

theorem arityOkArgs_mem {g : MGrammar} : ∀ {args : List MExp} {k : Nat} {a : MExp},
    MExp.arityOkArgs g args = true → argAt args k = some a → MExp.arityOk g a = true
  | _ :: _, 0, _, hargs, h => by
    simp only [argAt] at h
    cases h
    simp only [MExp.arityOkArgs, Bool.and_eq_true] at hargs
    exact hargs.1
  | _ :: _, _ + 1, _, hargs, h => by
    simp only [argAt] at h
    simp only [MExp.arityOkArgs, Bool.and_eq_true] at hargs
    exact arityOkArgs_mem hargs.2 h

theorem arityOk_failAlways (g : MGrammar) : MExp.arityOk g MExp.failAlways = true := by
  simp [MExp.failAlways, MExp.arityOk]

mutual
  theorem arityOk_subst {g : MGrammar} {args : List MExp} (hargs : MExp.arityOkArgs g args = true) :
      ∀ {e : MExp}, MExp.arityOk g e = true → MExp.arityOk g (MExp.subst args e) = true
    | .eps, _ => by simp [MExp.subst, MExp.arityOk]
    | .any, _ => by simp [MExp.subst, MExp.arityOk]
    | .chr _, _ => by simp [MExp.subst, MExp.arityOk]
    | .range _ _, _ => by simp [MExp.subst, MExp.arityOk]
    | .lit _, _ => by simp [MExp.subst, MExp.arityOk]
    | .param k, _ => by
      simp only [MExp.subst]
      cases h : argAt args k with
      | none => exact arityOk_failAlways g
      | some a => exact arityOkArgs_mem hargs h
    | .call i margs, he => by
      simp only [MExp.arityOk, Bool.and_eq_true] at he
      simp only [MExp.subst, MExp.arityOk, Bool.and_eq_true, length_substArgs]
      exact ⟨he.1, arityOkArgs_subst hargs he.2⟩
    | .seq e₁ e₂, he => by
      simp only [MExp.arityOk, Bool.and_eq_true] at he
      simp only [MExp.subst, MExp.arityOk, Bool.and_eq_true]
      exact ⟨arityOk_subst hargs he.1, arityOk_subst hargs he.2⟩
    | .alt e₁ e₂, he => by
      simp only [MExp.arityOk, Bool.and_eq_true] at he
      simp only [MExp.subst, MExp.arityOk, Bool.and_eq_true]
      exact ⟨arityOk_subst hargs he.1, arityOk_subst hargs he.2⟩
    | .star e, he => by
      simp only [MExp.arityOk] at he
      simp only [MExp.subst, MExp.arityOk]
      exact arityOk_subst hargs he
    | .notP e, he => by
      simp only [MExp.arityOk] at he
      simp only [MExp.subst, MExp.arityOk]
      exact arityOk_subst hargs he
    | .dbg e, he => by
      simp only [MExp.arityOk] at he
      simp only [MExp.subst, MExp.arityOk]
      exact arityOk_subst hargs he
    | .lam _ _, he => by simp only [MExp.subst]; exact he
    | .invoke _ bod margs, he => by
      simp only [MExp.arityOk, Bool.and_eq_true] at he
      simp only [MExp.subst, MExp.arityOk, Bool.and_eq_true]
      exact ⟨he.1, arityOkArgs_subst hargs he.2⟩
    | .callParam k margs, he => by
      simp only [MExp.arityOk] at he
      cases h : argAt args k with
      | none => rw [subst_callParam_none margs h]; exact arityOk_failAlways g
      | some a =>
        cases a with
        | lam ar bod =>
          rw [subst_callParam_lam margs h]
          have hbod : MExp.arityOk g bod = true := by
            have := arityOkArgs_mem hargs h
            simpa [MExp.arityOk] using this
          simp only [MExp.arityOk, Bool.and_eq_true]
          exact ⟨hbod, arityOkArgs_subst hargs he⟩
        | param j =>
          rw [subst_callParam_param margs h]
          simp only [MExp.arityOk]
          exact arityOkArgs_subst hargs he
        | _ =>
          rw [subst_callParam_of_not margs h (by simp [MExp.isLamOrParam])]
          exact arityOk_failAlways g

  theorem arityOkArgs_subst {g : MGrammar} {args : List MExp} (hargs : MExp.arityOkArgs g args = true) :
      ∀ {margs : List MExp}, MExp.arityOkArgs g margs = true →
        MExp.arityOkArgs g (MExp.substArgs args margs) = true
    | [], _ => by simp [MExp.substArgs, MExp.arityOkArgs]
    | e :: es, hm => by
      simp only [MExp.arityOkArgs, Bool.and_eq_true] at hm
      simp only [MExp.substArgs, MExp.arityOkArgs, Bool.and_eq_true]
      exact ⟨arityOk_subst hargs hm.1, arityOkArgs_subst hargs hm.2⟩
end

/-! ## The theorem -/

/-- What an outcome says about the input: `none` for failure, the remaining input on
success. Parse trees are deliberately forgotten — expansion removes `.nodeCall` nodes. -/
def MOutcome.restOf : MOutcome → Option (List Char)
  | .fail => none
  | .ok _ r => some r

theorem restOf_eq_some {o : MOutcome} {r : List Char} (h : o.restOf = some r) :
    ∃ t, o = .ok t r := by
  cases o with
  | fail => simp [MOutcome.restOf] at h
  | ok t r' => simp [MOutcome.restOf] at h; exact ⟨t, by rw [h]⟩

theorem restOf_eq_none {o : MOutcome} (h : o.restOf = none) : o = .fail := by
  cases o with
  | fail => rfl
  | ok t r' => simp [MOutcome.restOf] at h

/-- **T-exp (M-PEG-6).** Under `CallByName`, on an acyclic, arity-correct grammar with
no callable-valued rules, every derivation of the original program has a counterpart
in the expanded program with the same acceptance verdict and remaining input. -/
theorem expand_preserves_cbn {g : MGrammar} (h : acyclicB g = true) (hnc : NoCallableRules g h)
    (hga : g.arityOk = true) {e : MExp} {x : List Char} {o : MOutcome}
    (hd : MDerives g .callByName e x o) :
    MExp.arityOk g e = true →
      ∃ o', MDerives (MGrammar.expandGrammar g h) .callByName (MExp.expand g h e) x o' ∧
        o'.restOf = o.restOf := by
  induction hd using MDerives.rec
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ => True)
  case eps input => intro _; simp only [MExp.expand]; exact ⟨_, .eps input, rfl⟩
  case anyOk c rest => intro _; simp only [MExp.expand]; exact ⟨_, .anyOk c rest, rfl⟩
  case anyFail => intro _; simp only [MExp.expand]; exact ⟨_, .anyFail, rfl⟩
  case chrOk c d rest hcd => intro _; simp only [MExp.expand]; exact ⟨_, .chrOk c d rest hcd, rfl⟩
  case chrFail c d rest hcd => intro _; simp only [MExp.expand]; exact ⟨_, .chrFail c d rest hcd, rfl⟩
  case chrEmpty c => intro _; simp only [MExp.expand]; exact ⟨_, .chrEmpty c, rfl⟩
  case rangeOk lo hi d rest hr => intro _; simp only [MExp.expand]; exact ⟨_, .rangeOk lo hi d rest hr, rfl⟩
  case rangeFail lo hi d rest hr => intro _; simp only [MExp.expand]; exact ⟨_, .rangeFail lo hi d rest hr, rfl⟩
  case rangeEmpty lo hi => intro _; simp only [MExp.expand]; exact ⟨_, .rangeEmpty lo hi, rfl⟩
  case litOk str input rest hs => intro _; simp only [MExp.expand]; exact ⟨_, .litOk str input rest hs, rfl⟩
  case litFail str input hs => intro _; simp only [MExp.expand]; exact ⟨_, .litFail str input hs, rfl⟩
  case dbg e input => intro _; simp only [MExp.expand]; exact ⟨_, .dbg _ input, rfl⟩
  case paramFail k input => intro _; simp only [MExp.expand]; exact ⟨_, .paramFail k input, rfl⟩
  case lam ar bod input => intro _; simp only [MExp.expand]; exact ⟨_, .lam _ _ input, rfl⟩
  case callParamFail k args input => intro _; simp only [MExp.expand]; exact ⟨_, .callParamFail _ _ input, rfl⟩
  case invokeNameOk ar bod args input rest t hs ha hd ih =>
    intro hea
    simp only [MExp.arityOk, Bool.and_eq_true] at hea
    obtain ⟨o', hd', hrest⟩ := ih (arityOk_subst hea.2 hea.1)
    obtain ⟨t', rfl⟩ := restOf_eq_some hrest
    rw [expand_subst g h hnc] at hd'
    simp only [MExp.expand]
    exact ⟨_, .invokeNameOk _ _ _ input rest t' rfl (by rw [length_expandArgs]; exact ha) hd', rfl⟩
  case invokeNameFail ar bod args input hs ha hd ih =>
    intro hea
    simp only [MExp.arityOk, Bool.and_eq_true] at hea
    obtain ⟨o', hd', hrest⟩ := ih (arityOk_subst hea.2 hea.1)
    rw [restOf_eq_none hrest] at hd'
    rw [expand_subst g h hnc] at hd'
    simp only [MExp.expand]
    exact ⟨_, .invokeNameFail _ _ _ input rfl (by rw [length_expandArgs]; exact ha) hd', rfl⟩
  case invokeParOk ar bod args input rest vals t hs ha hargs hd ihargs ih => cases hs
  case invokeParFail ar bod args input vals hs ha hargs hd ihargs ih => cases hs
  case invokeParArgFail ar bod pre badArg post input preVals hs ha hpre hfail ihpre ihfail => cases hs
  case invokeSeqOk ar bod args input mid rest vals t hs ha hargs hd ihargs ih => cases hs
  case invokeSeqFail ar bod args input mid vals hs ha hargs hd ihargs ih => cases hs
  case invokeSeqArgFail ar bod pre badArg post input mid preVals hs ha hpre hfail ihpre ihfail => cases hs
  case invokeArity ar bod args input ha =>
    intro _
    simp only [MExp.expand]
    exact ⟨_, .invokeArity _ _ _ input (by rw [length_expandArgs]; exact ha), rfl⟩
  case callNameOk i args r input rest t hs hr ha hd ih =>
    intro hea
    simp only [MExp.arityOk, hr, Bool.and_eq_true] at hea
    obtain ⟨o', hd', hrest⟩ := ih (arityOk_subst hea.2 (arityOk_rule hga hr))
    obtain ⟨t', rfl⟩ := restOf_eq_some hrest
    rw [expand_subst g h hnc] at hd'
    cases args with
    | nil =>
      simp only [MExp.expand]
      simp only [MExp.expandArgs] at hd'
      refine ⟨_, .callNameOk i [] { arity := r.arity, body := MExp.expand g h r.body }
        input rest t' rfl ?_ ha hd', rfl⟩
      rw [ruleAtM_expandGrammar, hr]; rfl
    | cons a as =>
      simp only [MExp.expand]
      rw [expandRule_eq_of_some g h hr]
      exact ⟨_, hd', rfl⟩
  case callNameFail i args r input hs hr ha hd ih =>
    intro hea
    simp only [MExp.arityOk, hr, Bool.and_eq_true] at hea
    obtain ⟨o', hd', hrest⟩ := ih (arityOk_subst hea.2 (arityOk_rule hga hr))
    rw [restOf_eq_none hrest] at hd'
    rw [expand_subst g h hnc] at hd'
    cases args with
    | nil =>
      simp only [MExp.expand]
      simp only [MExp.expandArgs] at hd'
      refine ⟨_, .callNameFail i [] { arity := r.arity, body := MExp.expand g h r.body }
        input rfl ?_ ha hd', rfl⟩
      rw [ruleAtM_expandGrammar, hr]; rfl
    | cons a as =>
      simp only [MExp.expand]
      rw [expandRule_eq_of_some g h hr]
      exact ⟨_, hd', rfl⟩
  case callParOk i args r input rest vals t hs hr ha hargs hd ihargs ih => cases hs
  case callParFail i args r input vals hs hr ha hargs hd ihargs ih => cases hs
  case callParArgFail i pre badArg post r input preVals hs hr ha hpre hfail ihpre ihfail => cases hs
  case callSeqOk i args r input mid rest vals t hs hr ha hargs hd ihargs ih => cases hs
  case callSeqFail i args r input mid vals hs hr ha hargs hd ihargs ih => cases hs
  case callSeqArgFail i pre badArg post r input mid preVals hs hr ha hpre hfail ihpre ihfail => cases hs
  case callMissing i args input hr =>
    intro hea
    simp [MExp.arityOk, hr] at hea
  case callArity i args r input hr ha =>
    intro hea
    simp [MExp.arityOk, hr] at hea
    exact absurd hea.1 ha
  case seqOk e₁ e₂ input rest₁ rest₂ t₁ t₂ h₁ h₂ ih₁ ih₂ =>
    intro hea
    simp only [MExp.arityOk, Bool.and_eq_true] at hea
    obtain ⟨o₁, hd₁, hr₁⟩ := ih₁ hea.1
    obtain ⟨t₁', rfl⟩ := restOf_eq_some hr₁
    obtain ⟨o₂, hd₂, hr₂⟩ := ih₂ hea.2
    obtain ⟨t₂', rfl⟩ := restOf_eq_some hr₂
    simp only [MExp.expand]
    exact ⟨_, .seqOk _ _ _ _ _ _ _ hd₁ hd₂, rfl⟩
  case seqFail₁ e₁ e₂ input h₁ ih₁ =>
    intro hea
    simp only [MExp.arityOk, Bool.and_eq_true] at hea
    obtain ⟨o₁, hd₁, hr₁⟩ := ih₁ hea.1
    rw [restOf_eq_none hr₁] at hd₁
    simp only [MExp.expand]
    exact ⟨_, .seqFail₁ _ _ _ hd₁, rfl⟩
  case seqFail₂ e₁ e₂ input rest₁ t₁ h₁ h₂ ih₁ ih₂ =>
    intro hea
    simp only [MExp.arityOk, Bool.and_eq_true] at hea
    obtain ⟨o₁, hd₁, hr₁⟩ := ih₁ hea.1
    obtain ⟨t₁', rfl⟩ := restOf_eq_some hr₁
    obtain ⟨o₂, hd₂, hr₂⟩ := ih₂ hea.2
    rw [restOf_eq_none hr₂] at hd₂
    simp only [MExp.expand]
    exact ⟨_, .seqFail₂ _ _ _ _ _ hd₁ hd₂, rfl⟩
  case altL e₁ e₂ input rest t h ih =>
    intro hea
    simp only [MExp.arityOk, Bool.and_eq_true] at hea
    obtain ⟨o₁, hd₁, hr₁⟩ := ih hea.1
    obtain ⟨t', rfl⟩ := restOf_eq_some hr₁
    simp only [MExp.expand]
    exact ⟨_, .altL _ _ _ _ _ hd₁, rfl⟩
  case altR e₁ e₂ input rest t h₁ h₂ ih₁ ih₂ =>
    intro hea
    simp only [MExp.arityOk, Bool.and_eq_true] at hea
    obtain ⟨o₁, hd₁, hr₁⟩ := ih₁ hea.1
    rw [restOf_eq_none hr₁] at hd₁
    obtain ⟨o₂, hd₂, hr₂⟩ := ih₂ hea.2
    obtain ⟨t', rfl⟩ := restOf_eq_some hr₂
    simp only [MExp.expand]
    exact ⟨_, .altR _ _ _ _ _ hd₁ hd₂, rfl⟩
  case altFail e₁ e₂ input h₁ h₂ ih₁ ih₂ =>
    intro hea
    simp only [MExp.arityOk, Bool.and_eq_true] at hea
    obtain ⟨o₁, hd₁, hr₁⟩ := ih₁ hea.1
    rw [restOf_eq_none hr₁] at hd₁
    obtain ⟨o₂, hd₂, hr₂⟩ := ih₂ hea.2
    rw [restOf_eq_none hr₂] at hd₂
    simp only [MExp.expand]
    exact ⟨_, .altFail _ _ _ hd₁ hd₂, rfl⟩
  case starNil e input h ih =>
    intro hea
    simp only [MExp.arityOk] at hea
    obtain ⟨o₁, hd₁, hr₁⟩ := ih hea
    rw [restOf_eq_none hr₁] at hd₁
    simp only [MExp.expand]
    exact ⟨_, .starNil _ input hd₁, rfl⟩
  case starCons e input rest rest' t ts h₁ h₂ ih₁ ih₂ =>
    intro hea
    simp only [MExp.arityOk] at hea
    obtain ⟨o₁, hd₁, hr₁⟩ := ih₁ hea
    obtain ⟨t', rfl⟩ := restOf_eq_some hr₁
    obtain ⟨o₂, hd₂, hr₂⟩ := ih₂ (by simpa [MExp.arityOk] using hea)
    obtain ⟨ts', rfl⟩ := restOf_eq_some hr₂
    simp only [MExp.expand] at hd₂ ⊢
    exact ⟨_, .starCons _ _ _ _ _ _ hd₁ hd₂, rfl⟩
  case notOk e input rest t h ih =>
    intro hea
    simp only [MExp.arityOk] at hea
    obtain ⟨o₁, hd₁, hr₁⟩ := ih hea
    obtain ⟨t', rfl⟩ := restOf_eq_some hr₁
    simp only [MExp.expand]
    exact ⟨_, .notOk _ _ _ _ hd₁, rfl⟩
  case notFail e input h ih =>
    intro hea
    simp only [MExp.arityOk] at hea
    obtain ⟨o₁, hd₁, hr₁⟩ := ih hea
    rw [restOf_eq_none hr₁] at hd₁
    simp only [MExp.expand]
    exact ⟨_, .notFail _ _ hd₁, rfl⟩
  all_goals trivial

/-! ## Corollaries -/

/-- Whenever BOTH programs derive an outcome, the outcomes agree (via determinism of
the expanded program). Together with `expand_preserves_cbn` this says expansion can
only ever ADD termination, never change a verdict. -/
theorem expand_agrees_cbn {g : MGrammar} (h : acyclicB g = true) (hnc : NoCallableRules g h)
    (hga : g.arityOk = true) {e : MExp} (hea : MExp.arityOk g e = true) {x : List Char}
    {o o' : MOutcome}
    (hd : MDerives g .callByName e x o)
    (hd' : MDerives (MGrammar.expandGrammar g h) .callByName (MExp.expand g h e) x o') :
    o'.restOf = o.restOf := by
  obtain ⟨o'', hd'', hrest⟩ := expand_preserves_cbn h hnc hga hd hea
  rw [mderives_det hd' hd'']
  exact hrest

/-- The interpreter-level reading (what the Scala pipeline observes): a run of the
original program that finishes with some fuel has a run of the expanded program that
finishes with some fuel and the same verdict/remaining input. -/
theorem expand_preserves_cbn_run {g : MGrammar} (h : acyclicB g = true) (hnc : NoCallableRules g h)
    (hga : g.arityOk = true) {e : MExp} (hea : MExp.arityOk g e = true) {x : List Char}
    {f : Nat} {o : MOutcome}
    (hrun : mpegRun g .callByName f e x = some o) :
    ∃ f' o', mpegRun (MGrammar.expandGrammar g h) .callByName f' (MExp.expand g h e) x = some o' ∧
      o'.restOf = o.restOf := by
  obtain ⟨o', hd', hrest⟩ := expand_preserves_cbn h hnc hga (mpegRun_sound hrun) hea
  obtain ⟨f', hf'⟩ := mpegRun_complete hd'
  exact ⟨f', o', hf', hrest⟩

/-- Whole-grammar form: the start rule `.call i []` of the original program vs. the
same start rule of the expanded program. `MExp.expand (.call i []) = .call i []`, so
this is literally "run the expanded grammar from the same start symbol" — the shape
`ParserGenerator` emits. -/
theorem expandGrammar_preserves_start {g : MGrammar} (h : acyclicB g = true)
    (hnc : NoCallableRules g h) (hga : g.arityOk = true) {i : Nat} {r : MRule}
    (hr : ruleAtM g.rules i = some r) (h0 : r.arity = 0) {x : List Char} {o : MOutcome}
    (hd : MDerives g .callByName (.call i []) x o) :
    ∃ o', MDerives (MGrammar.expandGrammar g h) .callByName (.call i []) x o' ∧
      o'.restOf = o.restOf := by
  have hea : MExp.arityOk g (.call i []) = true := by
    simp [MExp.arityOk, MExp.arityOkArgs, hr, h0]
  obtain ⟨o', hd', hrest⟩ := expand_preserves_cbn h hnc hga hd hea
  simp only [MExp.expand] at hd'
  exact ⟨o', hd', hrest⟩

/-! ## Machine-checked witnesses for the two side conditions, and for the `subst` fix

Same `simp`-driven technique as `Counterexamples.lean` (CE-001): concrete, terminating
computations, evaluated by rewriting with the equation lemmas of the fuel interpreter
and of `expand` (whose well-founded recursion does not reduce under kernel `decide`). -/

/-- **CE-004 (pass-through, fixed).** `S = Baz(λx.x, "a") !.; Baz(f, s) = Apply(f, s);
Apply(f, s) = f(s)`. Rule 0 is `S`, 1 is `Baz`, 2 is `Apply`. -/
def passThroughGrammar : MGrammar :=
  { rules :=
      [ { arity := 0, body := .seq (.call 1 [.lam 1 (.param 0), .lit ['a']]) (.notP .any) }
      , { arity := 2, body := .call 2 [.param 0, .param 1] }
      , { arity := 2, body := .callParam 0 [.param 1] } ] }

theorem passThroughAcyclic : acyclicB passThroughGrammar = true := by
  simp [acyclicB, List.range, List.range.loop, List.all, rankGo, rankSuccs, natElem,
    MGrammar.calls, passThroughGrammar, ruleAtM, MExp.staticCalls, MExp.staticCallsArgs]

/-- Before expansion the evaluator accepts `"a"` (the reference `Interpreter` agrees:
`Success()`). -/
theorem ce004_passThrough_eval :
    mpegRun passThroughGrammar .callByName 10 (.call 0 []) ['a'] =
      some (.ok (.nodeCall 0 (.seq (.nodeCall 1 (.nodeCall 2 (.nodeInvoke (.leaf ['a'])))) .notT)) []) := by
  simp [mpegRun, passThroughGrammar, ruleAtM, MExp.subst, MExp.substArgs, argAt, stripPrefix?, beqChar]

/-- After expansion the SAME verdict — this is exactly what the pre-fix `subst`
got wrong (it produced `failAlways` for `Baz`'s body). The reference `MacroExpander`
expands `S` to `"a" !.`, and so does `expandGrammar` here. -/
theorem ce004_passThrough_expanded :
    (MGrammar.expandGrammar passThroughGrammar passThroughAcyclic).rules.map (·.body) =
      [ .seq (.invoke 1 (.param 0) [.lit ['a']]) (.notP .any)
      , .callParam 0 [.param 1]
      , .callParam 0 [.param 1] ] := by
  simp [MGrammar.expandGrammar, passThroughGrammar, MExp.expand, MExp.expandArgs, MExp.expandRule,
    ruleAtM, MExp.subst, MExp.substArgs, argAt]

theorem ce004_passThrough_expanded_eval :
    mpegRun (MGrammar.expandGrammar passThroughGrammar passThroughAcyclic) .callByName 10
      (.call 0 []) ['a'] =
      some (.ok (.nodeCall 0 (.seq (.nodeInvoke (.leaf ['a'])) .notT)) []) := by
  have hg := ce004_passThrough_expanded
  simp [MGrammar.expandGrammar, passThroughGrammar, MExp.expand, MExp.expandArgs, MExp.expandRule,
    ruleAtM, MExp.subst, MExp.substArgs, argAt] at hg ⊢
  simp [mpegRun, ruleAtM, MExp.subst, MExp.substArgs, argAt, stripPrefix?, beqChar]

/-- **CE-005 (arity correctness is necessary).** `S = F("b", "c"); F(x) = "a"` — an
arity-mismatched call. Rule 0 is `S`, 1 is `F`. -/
def arityMismatchGrammar : MGrammar :=
  { rules :=
      [ { arity := 0, body := .call 1 [.lit ['b'], .lit ['c']] }
      , { arity := 1, body := .lit ['a'] } ] }

theorem arityMismatchAcyclic : acyclicB arityMismatchGrammar = true := by
  simp [acyclicB, List.range, List.range.loop, List.all, rankGo, rankSuccs, natElem,
    MGrammar.calls, arityMismatchGrammar, ruleAtM, MExp.staticCalls, MExp.staticCallsArgs]

/-- The evaluator rejects the mismatched call outright (`callArity`)... -/
theorem ce005_arity_eval :
    mpegRun arityMismatchGrammar .callByName 10 (.call 0 []) ['a'] = some .fail := by
  simp [mpegRun, arityMismatchGrammar, ruleAtM, MExp.subst, MExp.substArgs, argAt]

/-- ...but expansion substitutes regardless of the argument count, and the expanded
program accepts `"a"`. Hence `arityOk` cannot be dropped from `expand_preserves_cbn`
(and, correspondingly, `arityMismatchGrammar.arityOk = false`). -/
theorem ce005_arity_expanded_eval :
    mpegRun (MGrammar.expandGrammar arityMismatchGrammar arityMismatchAcyclic) .callByName 10
      (.call 0 []) ['a'] = some (.ok (.nodeCall 0 (.leaf ['a'])) []) := by
  simp [MGrammar.expandGrammar, arityMismatchGrammar, MExp.expand, MExp.expandArgs, MExp.expandRule,
    ruleAtM, MExp.subst, MExp.substArgs, argAt]
  simp [mpegRun, ruleAtM, MExp.subst, MExp.substArgs, argAt, stripPrefix?, beqChar]

theorem ce005_arity_not_arityOk : arityMismatchGrammar.arityOk = false := by
  simp [MGrammar.arityOk, arityMismatchGrammar, MExp.arityOk, MExp.arityOkArgs, ruleAtM]

/-- **CE-006 (no callable-valued rules is necessary).** The closure-return grammar of
`Examples.lean` (`Baz(f) = f; Apply(f, s) = f(s)`): `Baz` expands to a bare `.param`,
so `noCallableRulesB` rejects it — and indeed `Examples.lean`'s `#guard`s show the
evaluator failing where the expanded program succeeds. -/
theorem ce006_closureReturn_not_noCallableRules :
    noCallableRulesB closureReturnGrammar closureReturnAcyclic = false := by
  simp [noCallableRulesB, MGrammar.expandGrammar, closureReturnGrammar, closureReturnBazBody,
    closureReturnApplyBody, MExp.expand, MExp.expandArgs, MExp.isLamOrParam]

end Shallot.MacroPeg
