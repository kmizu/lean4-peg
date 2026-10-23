import MacroPeg.CBV.PrefixCounters
import MacroPeg.CBV.RootObservation
import MacroPeg.CBVtoCBN.PositionSearch

namespace Shallot.MacroPeg.CBV.PrefixCounters

open CBVtoCBN (paramsFrom paramsFrom_firstOrder subst_paramsFrom_cons subst_paramsFrom)

def prefixValues (x : List Char) : List Nat → List MExp
  | [] => []
  | k :: ks => .lit (x.take k) :: prefixValues x ks

@[simp] theorem prefixValues_length (x : List Char) (ks : List Nat) :
    (prefixValues x ks).length = ks.length := by
  induction ks with
  | nil => rfl
  | cons k ks ih => simp [prefixValues, ih]

/-- A tuple of root prefixes can be passed unchanged through any Par call. -/
theorem prefixValues_args (g : MGrammar) (x : List Char) (ks : List Nat) :
    DerivesArgsPar g .callByValuePar x (prefixValues x ks) (prefixValues x ks) := by
  induction ks with
  | nil => exact .nil x
  | cons k ks ih =>
    exact .cons _ _ _ _ _ _ _ (literal_take g .callByValuePar x k) (prefix_eq x k) ih

/-- Search upward from q until q+1 equals p. The remaining parameters are
enclosing root-valued counters, carried unchanged into the continuation. -/
def predecessorBody (self equal next ctxSize : Nat) : MExp :=
  RootObservation.branch
    (.call equal [.seq (.param 1) .any, .param 0])
    (.call next (.param 1 :: paramsFrom 2 ctxSize))
    (.call self (.param 0 :: .seq (.param 1) .any :: paramsFrom 2 ctxSize))

theorem predecessorBody_firstOrder (self equal next ctxSize : Nat) :
    (predecessorBody self equal next ctxSize).FirstOrder := by
  have hc := paramsFrom_firstOrder 2 ctxSize
  exact ⟨⟨⟨⟨trivial, trivial⟩, trivial, trivial⟩, trivial, hc⟩,
    ⟨⟨⟨trivial, trivial⟩, trivial, trivial⟩, trivial, ⟨trivial, trivial⟩, hc⟩⟩

theorem predecessorBody_subst (self equal next : Nat) (p q : MExp) (ctx : List MExp) :
    MExp.subst (p :: q :: ctx) (predecessorBody self equal next ctx.length) =
      RootObservation.branch (.call equal [.seq q .any, p])
        (.call next (q :: ctx)) (.call self (p :: .seq q .any :: ctx)) := by
  simp [predecessorBody, RootObservation.branch, MExp.subst, MExp.substArgs,
    argAt, subst_paramsFrom_cons, subst_paramsFrom]

/-- The search has exactly its continuation's observations. No termination
assumption is imposed on that continuation, and its failure cannot restart
the search. -/
theorem predecessor_body_iff {g : MGrammar} {self equal next : Nat}
    (ctx : List Nat)
    (hr : ruleAtM g.rules self =
      some ⟨ctx.length + 2, predecessorBody self equal next ctx.length⟩)
    (he : ruleAtM g.rules equal = some ⟨2, equalBody equal⟩)
    (x : List Char) (p q : Nat) (hp : p ≤ x.length) (hq : q < p)
    (r : Option (List Char)) :
    SObs g .callByValuePar
      (MExp.subst (.lit (x.take p) :: .lit (x.take q) :: prefixValues x ctx)
        (predecessorBody self equal next ctx.length)) x r ↔
    SObs g .callByValuePar (.call next (.lit (x.take (p - 1)) :: prefixValues x ctx)) x r := by
  have aux : ∀ d q, q + d + 1 = p → (
      SObs g .callByValuePar
        (MExp.subst (.lit (x.take p) :: .lit (x.take q) :: prefixValues x ctx)
          (predecessorBody self equal next ctx.length)) x r ↔
      SObs g .callByValuePar (.call next (.lit (x.take (p - 1)) :: prefixValues x ctx)) x r) := by
    intro d
    induction d with
    | zero =>
      intro q h
      have hq : q < x.length := by omega
      obtain ⟨t, ht⟩ := grow_obs g x q hq
      have hg := equal_arguments_obs he (a := q + 1) (b := p) (by omega) hp
        (ea := .seq (.lit (x.take q)) .any) (eb := .lit (x.take p))
        ⟨_, ht, rfl⟩ ⟨_, literal_take g .callByValuePar x p, rfl⟩
      have hEq : q + 1 = p := by omega
      simp only [if_pos hEq] at hg
      have hctx : ctx.length = (prefixValues x ctx).length := by simp
      rw [hctx, predecessorBody_subst, RootObservation.branch_true_iff hg]
      have hpred : q = p - 1 := by omega
      rw [hpred]
    | succ d ih =>
      intro q h
      have hq : q < x.length := by omega
      obtain ⟨t, ht⟩ := grow_obs g x q hq
      have hg := equal_arguments_obs he (a := q + 1) (b := p) (by omega) hp
        (ea := .seq (.lit (x.take q)) .any) (eb := .lit (x.take p))
        ⟨_, ht, rfl⟩ ⟨_, literal_take g .callByValuePar x p, rfl⟩
      have hNe : q + 1 ≠ p := by omega
      simp only [if_neg hNe] at hg
      have hctx : ctx.length = (prefixValues x ctx).length := by simp
      rw [hctx, predecessorBody_subst, RootObservation.branch_false_iff hg]
      have hv : DerivesArgsPar g .callByValuePar x
          (.lit (x.take p) :: .seq (.lit (x.take q)) .any :: prefixValues x ctx)
          (.lit (x.take p) :: .lit (x.take (q + 1)) :: prefixValues x ctx) :=
        .cons _ _ _ _ _ _ _ (literal_take g .callByValuePar x p) (prefix_eq x p)
          (.cons _ _ _ _ _ _ _ ht (prefix_eq x (q + 1)) (prefixValues_args g x ctx))
      rw [par_call_iff hr (by simp) hv]
      simpa only [prefixValues_length] using ih (q + 1) (by omega)
  exact aux (p - q - 1) q (by omega)

/-- A named first-order Par search computes the predecessor of a positive
counter and preserves every other counter, on the same original input. -/
theorem predecessor_iff {g : MGrammar} {self equal next : Nat}
    (ctx : List Nat)
    (hr : ruleAtM g.rules self =
      some ⟨ctx.length + 2, predecessorBody self equal next ctx.length⟩)
    (he : ruleAtM g.rules equal = some ⟨2, equalBody equal⟩)
    (x : List Char) (p q : Nat) (hp : p ≤ x.length) (hq : q < p)
    (r : Option (List Char)) :
    SObs g .callByValuePar
      (.call self (.lit (x.take p) :: .lit (x.take q) :: prefixValues x ctx)) x r ↔
    SObs g .callByValuePar (.call next (.lit (x.take (p - 1)) :: prefixValues x ctx)) x r := by
  have hv := prefixValues_args g x (p :: q :: ctx)
  simp only [prefixValues] at hv
  rw [par_call_iff hr (by simp) hv]
  exact predecessor_body_iff ctx hr he x p q hp hq r

end Shallot.MacroPeg.CBV.PrefixCounters
