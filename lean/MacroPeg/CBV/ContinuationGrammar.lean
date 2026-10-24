import MacroPeg.CBV.ContinuationPlan

/-! Lift continuation normalization through actual mutually recursive grammar
rounds. The source bodies contain consuming sequence outside control plans;
normalization is a fixed syntactic transformation, not a supplied row oracle. -/
namespace Shallot.MacroPeg.CBV.ContinuationGrammar
open ReplayControlFusion (Plan)
open ContinuationPlan

mutual
  theorem eval_headers (g h : MGrammar) (ha : ∀ i, (ruleAtM g.rules i).map MRule.arity=(ruleAtM h.rules i).map MRule.arity)
      (x : List Char) (s : Strategy) (T : ClockFreezing.Table) (E : List (List Char)) :
      ∀ e p, evV g x s T E e p=evV h x s T E e p
    | .call i args, p => by
      have hi := ha i
      cases hg : ruleAtM g.rules i with
      | none =>
        cases hh : ruleAtM h.rules i with
        | none => simp only [evV,hg,hh]
        | some r => simp [hg,hh] at hi
      | some r =>
        cases hh : ruleAtM h.rules i with
        | none => simp [hg,hh] at hi
        | some t =>
          have har : r.arity=t.arity := by simpa only [hg,hh,Option.map_some,Option.some.injEq] using hi
          simp only [evV,hg,hh,har]
          split
          · cases s <;> simp only [par_headers g h ha x _ T E args p,seq_headers g h ha x _ T E args p]
          · rfl
    | .seq a b, p => by
      simp only [evV,eval_headers g h ha x s T E a p]
      cases evV h x s T E a p with
      | none => rfl
      | some result => cases result with
        | none => rfl
        | some j => exact eval_headers g h ha x s T E b j
    | .alt a b, p => by
      simp only [evV,eval_headers g h ha x s T E a p]
      cases evV h x s T E a p with
      | none => rfl
      | some result => cases result with
        | none => exact eval_headers g h ha x s T E b p
        | some _ => rfl
    | .star a, p => evStar_congr p (fun q _ => eval_headers g h ha x s T E a q)
    | .notP a, p => by simp only [evV,eval_headers g h ha x s T E a p]
    | .eps, _ | .any, _ | .chr _, _ | .range _ _, _ | .lit _, _ | .param _, _ |
      .dbg _, _ | .lam _ _, _ | .callParam _ _, _ | .invoke _ _ _, _ => rfl

  theorem par_headers (g h : MGrammar) (ha : ∀ i, (ruleAtM g.rules i).map MRule.arity=(ruleAtM h.rules i).map MRule.arity)
      (x : List Char) (s : Strategy) (T : ClockFreezing.Table) (E : List (List Char)) :
      ∀ args p, evParArgs g x s T E args p=evParArgs h x s T E args p
    | [], _ => rfl
    | a::as, p => by simp only [evParArgs,eval_headers g h ha x s T E a p,par_headers g h ha x s T E as p]

  theorem seq_headers (g h : MGrammar) (ha : ∀ i, (ruleAtM g.rules i).map MRule.arity=(ruleAtM h.rules i).map MRule.arity)
      (x : List Char) (s : Strategy) (T : ClockFreezing.Table) (E : List (List Char)) :
      ∀ args p, evSeqArgs g x s T E args p=evSeqArgs h x s T E args p
    | [], _ => rfl
    | a::as, p => by
      simp only [evSeqArgs,eval_headers g h ha x s T E a p]
      cases evV h x s T E a p with
      | none => rfl
      | some result => cases result with
        | none => rfl
        | some j =>
          dsimp only []
          rw [seq_headers g h ha x s T E as j]
end

structure Rule where
  arity : Nat
  leaves : List MExp
  first : Plan
  next : Plan

def Rule.Valid (r : Rule) : Prop :=
  r.first.All (fun i => i<r.leaves.length) ∧ r.next.All (fun i => i<r.leaves.length)
def Rule.lookup (r : Rule) (i : Nat) : MExp := r.leaves[i]?.getD MExp.failAlways
def Rule.source (r : Rule) : MRule := ⟨r.arity,.seq (r.first.exp r.lookup) (r.next.exp r.lookup)⟩
def Rule.normalized (r : Rule) : MRule :=
  ⟨r.arity,(bind r.leaves.length r.first r.next).exp (expressions r.leaves.length r.lookup r.next)⟩
def source (rs : List Rule) : MGrammar := ⟨rs.map Rule.source⟩
def normalized (rs : List Rule) : MGrammar := ⟨rs.map Rule.normalized⟩

theorem headers (rs : List Rule) (i : Nat) :
    (ruleAtM (source rs).rules i).map MRule.arity=(ruleAtM (normalized rs).rules i).map MRule.arity := by
  simp only [source,normalized,ruleAtM_eq_getElem?,List.getElem?_map,Option.map_map]
  rfl

theorem tables_eq (rs : List Rule) (hv : ∀ r∈rs, r.Valid) (x : List Char) (s : Strategy) :
    ∀ k, tblV (source rs) x s k=tblV (normalized rs) x s k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    funext i E
    simp only [tblV,source,normalized,ruleAtM_eq_getElem?,List.getElem?_map]
    cases hr : rs[i]? with
    | none => rfl
    | some r =>
      dsimp only [Option.map_some]
      apply List.map_congr_left
      intro p _
      change evV (source rs) x s (tblV (source rs) x s k) E r.source.body p=
        evV (normalized rs) x s (tblV (normalized rs) x s k) E r.normalized.body p
      rw [ih]
      have he := expression_eq r.leaves.length r.lookup r.first r.next
        (hv r (List.mem_of_getElem? hr)).1 (hv r (List.mem_of_getElem? hr)).2
        (normalized rs) x s (tblV (normalized rs) x s k) E p
      exact (eval_headers (source rs) (normalized rs) (headers rs) x s _ E r.source.body p).trans he.symm

theorem evaluator_eq (rs : List Rule) (hv : ∀ r∈rs, r.Valid) (x : List Char) (s : Strategy)
    (k : Nat) (E : List (List Char)) (e : MExp) (p : Nat) :
    evV (source rs) x s (tblV (source rs) x s k) E e p=
    evV (normalized rs) x s (tblV (normalized rs) x s k) E e p := by
  rw [tables_eq rs hv x s k]
  exact eval_headers (source rs) (normalized rs) (headers rs) x s _ E e p


def FirstOrder (rs : List Rule) : Prop := ∀ r∈rs, ∀ e∈r.leaves, e.FirstOrder

theorem lookup_firstOrder (r : Rule) (hf : ∀ e∈r.leaves, e.FirstOrder) (i : Nat) :
    (r.lookup i).FirstOrder := by
  unfold Rule.lookup
  cases hr : r.leaves[i]? with
  | none => trivial
  | some e => exact hf e (List.mem_of_getElem? hr)

theorem source_firstOrder (rs : List Rule) (hf : FirstOrder rs) : (source rs).FirstOrder := by
  intro r hr
  obtain ⟨r,hm,rfl⟩ := List.mem_map.mp hr
  exact ⟨Plan.exp_firstOrder (lookup_firstOrder r (hf r hm)) r.first,
    Plan.exp_firstOrder (lookup_firstOrder r (hf r hm)) r.next⟩

theorem normalized_firstOrder (rs : List Rule) (hf : FirstOrder rs) : (normalized rs).FirstOrder := by
  intro r hr
  obtain ⟨r,hm,rfl⟩ := List.mem_map.mp hr
  exact Plan.exp_firstOrder (expressions_firstOrder r.leaves.length r.lookup (lookup_firstOrder r (hf r hm)) r.next) _

/-- Whole recursive grammars on unchanged strings, for either CBV strategy.
Every rule has its own leaves and continuation; no common continuation or
assumed recursive row correspondence appears in this theorem. -/
theorem observations_iff (rs : List Rule) (hv : ∀ r∈rs, r.Valid) (hf : FirstOrder rs)
    (s : Strategy) (hs : s≠.callByName) (e : MExp) (he : e.FirstOrder)
    (x : List Char) (rest : Option (List Char)) :
    SObs (source rs) s e x rest ↔ SObs (normalized rs) s e x rest := by
  have hd : decideObsV s (source rs) x e=decideObsV s (normalized rs) x e := by
    unfold decideObsV
    rw [ScannerPairFusion.stable_result_eq (source rs) (normalized rs) x s s e e
      (fun k => evaluator_eq rs hv x s k [] e x.length)]
  rw [←decideObsV_iff (source_firstOrder rs hf) hs he,
    ←decideObsV_iff (normalized_firstOrder rs hf) hs he,hd]

end Shallot.MacroPeg.CBV.ContinuationGrammar
