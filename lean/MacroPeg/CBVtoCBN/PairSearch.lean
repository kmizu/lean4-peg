import MacroPeg.CBVtoCBN.Routing
import MacroPeg.CBVtoCBN.RootTests

namespace Shallot.MacroPeg.CBVtoCBN

/-- Seed complement discovery for a candidate, retaining the enclosing activation. -/
def pairSeedBody (helper ctxSize : Nat) : MExp :=
  .call helper (.param 0 :: .eps :: paramsFrom 1 ctxSize)

theorem pairSeedBody_firstOrder (helper ctxSize : Nat) : (pairSeedBody helper ctxSize).FirstOrder :=
  ⟨trivial, trivial, paramsFrom_firstOrder 1 ctxSize⟩

theorem pairSeedBody_subst (helper : Nat) (candidate : MExp) (ctx : List MExp) :
    MExp.subst (candidate :: ctx) (pairSeedBody helper ctx.length) = .call helper (candidate :: .eps :: ctx) := by
  simp [pairSeedBody, MExp.subst, MExp.substArgs, argAt, subst_paramsFrom_cons, subst_paramsFrom]

/-- Existential quantification over a pair `(k,n-k)`, with no change to the original input. -/
theorem anyPair_test {g : MGrammar} {entry seed helper test : Nat} (ctx : List MExp)
    (he : ruleAtM g.rules entry = some ⟨ctx.length + 1, anyPositionBody entry seed ctx.length⟩)
    (hs : ruleAtM g.rules seed = some ⟨ctx.length + 1, pairSeedBody helper ctx.length⟩)
    (hh : ruleAtM g.rules helper = some ⟨ctx.length + 2, complementContextBody helper test ctx.length⟩)
    (x : List Char) (P : Nat → Prop)
    (ht : ∀ k, k ≤ x.length → RootTest g (.call test (skipN k :: skipN (x.length - k) :: ctx)) x (P k)) :
    RootTest g (.call entry (.eps :: ctx)) x (∃ k, k ≤ x.length ∧ P k) := by
  classical
  have hc : ∀ k, k ≤ x.length → MacroObs g (.call seed (skipN k :: ctx)) x
      (if P k then some x else none) := by
    intro k hk
    rw [obs_call_iff hs (by simp), pairSeedBody_subst]
    change MacroObs g (.call helper (skipN k :: skipN 0 :: ctx)) x _
    exact (complementContext_iff ctx hh x k 0 (by omega) _).mpr (ht k hk).obs
  have h := anyPosition_obs ctx he x P hc 0 (by omega)
  apply RootTest.congr (RootTest.of_obs h)
  simp only [Nat.zero_le, true_and]

/-- Three fixed rules implement a bounded quantifier for any static candidate rule. -/
def pairSearchBlock (entry test ctxSize : Nat) : List MRule :=
  [⟨ctxSize + 1, anyPositionBody entry (entry + 1) ctxSize⟩,
   ⟨ctxSize + 1, pairSeedBody (entry + 2) ctxSize⟩,
   ⟨ctxSize + 2, complementContextBody (entry + 2) test ctxSize⟩]

theorem pairSearchBlock_firstOrder (entry test ctxSize : Nat) :
    ∀ rule ∈ pairSearchBlock entry test ctxSize, rule.body.FirstOrder := by
  intro rule hr
  simp only [pairSearchBlock, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact anyPositionBody_firstOrder _ _ _
  · exact pairSeedBody_firstOrder _ _
  · exact complementContextBody_firstOrder _ _ _

/-- The generated block supplies all rule lookups needed by the bounded-quantifier proof. -/
theorem pairSearchBlock_test (pre tail : List MRule) (test : Nat) (ctx : List MExp)
    (x : List Char) (P : Nat → Prop)
    (ht : ∀ k, k ≤ x.length → RootTest
      ⟨pre ++ (pairSearchBlock pre.length test ctx.length ++ tail)⟩
      (.call test (skipN k :: skipN (x.length - k) :: ctx)) x (P k)) :
    RootTest ⟨pre ++ (pairSearchBlock pre.length test ctx.length ++ tail)⟩
      (.call pre.length (.eps :: ctx)) x (∃ k, k ≤ x.length ∧ P k) := by
  apply anyPair_test ctx (entry := pre.length) (seed := pre.length + 1) (helper := pre.length + 2)
    _ _ _ x P ht
  · rw [show pre.length = pre.length + 0 by omega, ruleAtM_append_offset]; rfl
  · rw [ruleAtM_append_offset]; rfl
  · rw [ruleAtM_append_offset]; rfl

end Shallot.MacroPeg.CBVtoCBN
