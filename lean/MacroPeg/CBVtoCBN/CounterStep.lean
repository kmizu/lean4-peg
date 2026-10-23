import MacroPeg.CBVtoCBN.ContextSearch

namespace Shallot.MacroPeg.CBVtoCBN

theorem context_sim (g : MGrammar) : ∀ ctx : List MExp, SimArgs g ctx ctx
  | [] => .nil
  | _ :: ctx => .cons (.leaf (fun _ _ => Iff.rfl)) (context_sim g ctx)

/-- Two length representations can be replaced through a call while all captured context stays fixed. -/
theorem call_pair_len_equiv {g : MGrammar} (hg : g.FirstOrder) (i : Nat) (ctx : List MExp)
    {a b c d : MExp} {p q : Nat} (ha : LenRep g a p) (hb : LenRep g b q)
    (hc : LenRep g c p) (hd : LenRep g d q) :
    ObsEquiv g (.call i (a :: b :: ctx)) (.call i (c :: d :: ctx)) := by
  intro x r
  constructor
  · exact sim_obs hg (.node (.call i
      (.cons (.leaf (ha.equiv hc)) (.cons (.leaf (hb.equiv hd)) (context_sim g ctx)))))
  · exact sim_obs hg (.node (.call i
      (.cons (.leaf (hc.equiv ha)) (.cons (.leaf (hd.equiv hb)) (context_sim g ctx)))))

/-- Swap a newly found complementary pair back to the prefix/suffix convention. -/
def swapCounterBody (next ctxSize : Nat) : MExp :=
  .call next (.param 1 :: .param 0 :: paramsFrom 2 ctxSize)

theorem swapCounterBody_firstOrder (next ctxSize : Nat) :
    (swapCounterBody next ctxSize).FirstOrder :=
  ⟨trivial, trivial, paramsFrom_firstOrder 2 ctxSize⟩

theorem swapCounter_iff {g : MGrammar} {self next : Nat} (ctx : List MExp)
    (hr : ruleAtM g.rules self = some ⟨ctx.length + 2, swapCounterBody next ctx.length⟩)
    (a b : MExp) (x : List Char) (r : Option (List Char)) :
    MacroObs g (.call self (a :: b :: ctx)) x r ↔ MacroObs g (.call next (b :: a :: ctx)) x r := by
  rw [obs_call_iff hr (by simp)]
  simp [swapCounterBody, MExp.subst, MExp.substArgs, argAt,
    subst_paramsFrom_cons, subst_paramsFrom]

/-- Branch on a zero digit, otherwise discover its predecessor. All continuations are named rules. -/
def decrementBody (helper onZero ctxSize : Nat) : MExp :=
  ifP (exactLengthP (.param 1))
    (.call onZero (.param 0 :: .param 1 :: paramsFrom 2 ctxSize))
    (.call helper (.seq (.param 1) .any :: .eps :: paramsFrom 2 ctxSize))

theorem decrementBody_firstOrder (helper onZero ctxSize : Nat) :
    (decrementBody helper onZero ctxSize).FirstOrder :=
  ifP_firstOrder ⟨trivial, trivial⟩
    ⟨trivial, trivial, paramsFrom_firstOrder 2 ctxSize⟩
    ⟨⟨trivial, trivial⟩, trivial, paramsFrom_firstOrder 2 ctxSize⟩

theorem decrementBody_subst (helper onZero : Nat) (a b : MExp) (ctx : List MExp) :
    MExp.subst (a :: b :: ctx) (decrementBody helper onZero ctx.length) =
      ifP (exactLengthP b) (.call onZero (a :: b :: ctx))
        (.call helper (.seq b .any :: .eps :: ctx)) := by
  simp [decrementBody, ifP, exactLengthP, andP, MExp.subst, MExp.substArgs,
    argAt, subst_paramsFrom_cons, subst_paramsFrom]

/-- A bounded counter can be decremented inside a first-order CBN grammar.
The zero branch and the positive branch each preserve every observation of their continuation. -/
theorem decrement_iff {g : MGrammar} (hg : g.FirstOrder) {self helper swap onZero next : Nat}
    (ctx : List MExp)
    (hr : ruleAtM g.rules self = some ⟨ctx.length + 2, decrementBody helper onZero ctx.length⟩)
    (hh : ruleAtM g.rules helper = some ⟨ctx.length + 2, complementContextBody helper swap ctx.length⟩)
    (hs : ruleAtM g.rules swap = some ⟨ctx.length + 2, swapCounterBody next ctx.length⟩)
    (x : List Char) (k : Nat) (hk : k ≤ x.length) (r : Option (List Char)) :
    MacroObs g (.call self (skipN k :: skipN (x.length - k) :: ctx)) x r ↔
      if k = 0 then MacroObs g (.call onZero (skipN 0 :: skipN x.length :: ctx)) x r
      else MacroObs g (.call next (skipN (k - 1) :: skipN (x.length - (k - 1)) :: ctx)) x r := by
  rw [obs_call_iff hr (by simp), decrementBody_subst]
  change MacroObs g (ifP (exactLengthP (skipN (x.length - k)))
    (.call onZero (skipN k :: skipN (x.length - k) :: ctx))
    (.call helper (.seq (skipN (x.length - k)) .any :: .eps :: ctx))) x r ↔ _
  have ht := exactLength_obs (skipN_rep g (x.length - k)) x
  by_cases he : k = 0
  · subst k
    simp only [Nat.sub_zero] at ht ⊢
    exact ifP_true_iff ht r
  · have hne : x.length - k ≠ x.length := by omega
    rw [if_neg hne] at ht
    rw [if_neg he]
    rw [ifP_false_iff ht r]
    have hrep : LenRep g (.seq (skipN (x.length - k)) .any) (x.length - k + 1) :=
      (skipN_rep g (x.length - k)).seq (lenRep_any g)
    change MacroObs g (.call helper (.seq (skipN (x.length - k)) .any :: skipN 0 :: ctx)) x r ↔ _
    rw [call_pair_len_equiv hg helper ctx hrep (skipN_rep g 0)
      (skipN_rep g (x.length - k + 1)) (skipN_rep g 0) x r]
    rw [complementContext_iff ctx hh x (x.length - k + 1) 0 (by omega) r,
      swapCounter_iff ctx hs]
    have hpre : x.length - (x.length - k + 1) = k - 1 := by omega
    have hsuf : x.length - k + 1 = x.length - (k - 1) := by omega
    rw [hpre, hsuf]

end Shallot.MacroPeg.CBVtoCBN
