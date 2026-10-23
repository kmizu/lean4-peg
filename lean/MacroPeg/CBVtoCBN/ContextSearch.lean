import MacroPeg.CBVtoCBN.PositionSearch

namespace Shallot.MacroPeg.CBVtoCBN

/-- Complement discovery with a fixed-size tuple of enclosing captured values. -/
def complementContextBody (self next ctxSize : Nat) : MExp :=
  ifP (exactLengthP (.seq (.param 0) (.param 1)))
    (.call next (.param 0 :: .param 1 :: paramsFrom 2 ctxSize))
    (.call self (.param 0 :: .seq (.param 1) .any :: paramsFrom 2 ctxSize))

theorem complementContextBody_firstOrder (self next ctxSize : Nat) :
    (complementContextBody self next ctxSize).FirstOrder := by
  exact ifP_firstOrder ⟨⟨trivial, trivial⟩, trivial⟩
    ⟨trivial, trivial, paramsFrom_firstOrder 2 ctxSize⟩
    ⟨trivial, ⟨trivial, trivial⟩, paramsFrom_firstOrder 2 ctxSize⟩

theorem complementContextBody_subst (self next : Nat) (a b : MExp) (ctx : List MExp) :
    MExp.subst (a :: b :: ctx) (complementContextBody self next ctx.length) =
      ifP (exactLengthP (.seq a b)) (.call next (a :: b :: ctx))
        (.call self (a :: .seq b .any :: ctx)) := by
  simp [complementContextBody, ifP, exactLengthP, andP, MExp.subst, MExp.substArgs,
    argAt, subst_paramsFrom_cons, subst_paramsFrom]

theorem complementContext_step {g : MGrammar} {self next : Nat} (ctx : List MExp)
    (hr : ruleAtM g.rules self = some ⟨ctx.length + 2, complementContextBody self next ctx.length⟩)
    (x : List Char) (p k : Nat) (r : Option (List Char)) :
    MacroObs g (.call self (skipN p :: skipN k :: ctx)) x r ↔
      if p + k = x.length then MacroObs g (.call next (skipN p :: skipN k :: ctx)) x r
      else MacroObs g (.call self (skipN p :: skipN (k + 1) :: ctx)) x r := by
  rw [obs_call_iff hr (by simp), complementContextBody_subst]
  have ht := exactLength_obs ((skipN_rep g p).seq (skipN_rep g k)) x
  by_cases he : p + k = x.length
  · rw [if_pos he] at ht ⊢
    exact ifP_true_iff ht r
  · rw [if_neg he] at ht ⊢
    exact ifP_false_iff ht r

/-- Every captured argument is retained unchanged through the entire finite search.
No totality assumption is imposed on the continuation: even its failure or divergence is preserved. -/
theorem complementContext_iff {g : MGrammar} {self next : Nat} (ctx : List MExp)
    (hr : ruleAtM g.rules self = some ⟨ctx.length + 2, complementContextBody self next ctx.length⟩)
    (x : List Char) (p k : Nat) (hk : p + k ≤ x.length) (r : Option (List Char)) :
    MacroObs g (.call self (skipN p :: skipN k :: ctx)) x r ↔
      MacroObs g (.call next (skipN p :: skipN (x.length - p) :: ctx)) x r := by
  have aux : ∀ d k, p + k + d = x.length →
      (MacroObs g (.call self (skipN p :: skipN k :: ctx)) x r ↔
        MacroObs g (.call next (skipN p :: skipN (x.length - p) :: ctx)) x r) := by
    intro d
    induction d with
    | zero =>
      intro k h
      have he : p + k = x.length := by omega
      have hk' : k = x.length - p := by omega
      rw [complementContext_step ctx hr, if_pos he, hk']
    | succ d ih =>
      intro k h
      have he : p + k ≠ x.length := by omega
      rw [complementContext_step ctx hr, if_neg he]
      exact ih (k + 1) (by omega)
  exact aux (x.length - (p + k)) k (by omega)

end Shallot.MacroPeg.CBVtoCBN
