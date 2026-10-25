import MacroPeg.CBV.OriginHeadEvaluation

namespace Shallot.MacroPeg.CBV.OriginHeadInlining
open OriginHeadParts
open ReplayControlFusion (Part Plan sourceLeaf)
open MultiplyingPrefixCompiler (Spec sourceBody)
open MixedGrowthCompiler (Entry)

def entries (parts : List Part) (es : List Entry) (i : Nat) (r : Spec) (P : Plan) :=
  es.set i (.origin (plan parts r P))
def normalized (parts : List Part) (es : List Entry) (i : Nat) (r : Spec) (P : Plan) :=
  MixedGrowthCompiler.source (extended parts r) (entries parts es i r P)
def target (parts : List Part) (es : List Entry) (i : Nat) (r : Spec) (P : Plan) :=
  MixedForwardingCompiler.target (extended parts r) (entries parts es i r P)
abbrev render (parts : List Part) (es : List Entry) (i : Nat) (r : Spec) (P : Plan) :=
  MixedForwardingCompiler.render (extended parts r) (entries parts es i r P)

def plansCheck (parts : List Part) (es : List Entry) := es.all (fun e => match e with
  | .growth _ => true
  | .origin P => MixedGrowthChecks.planCheck parts P)
def check (parts : List Part) (es : List Entry) (i : Nat) : Bool := plansCheck parts es &&
  match es[i]? with
  | some (.growth r) => decide (1≤r.factor) && match es[r.callee]? with
    | some (.origin P) => MixedForwardingChecks.check (extended parts r) (entries parts es i r P)
    | _ => false
  | _ => false

theorem checked (parts : List Part) (es : List Entry) (i : Nat) (r : Spec) (P : Plan)
    (hi : es[i]?=some (.growth r)) (hj : es[r.callee]?=some (.origin P)) (hc : check parts es i=true) :
    1≤r.factor ∧ MixedForwardingCompiler.Valid (extended parts r) (entries parts es i r P) ∧
      ∀ (j : Nat) (Q : Plan), es[j]?=some (.origin Q) → ReplayControlFusion.ValidPlan parts Q := by
  obtain ⟨hp,h⟩ := Bool.and_eq_true_iff.mp hc
  simp only [hi,hj,Bool.and_eq_true_iff] at h
  refine ⟨of_decide_eq_true h.1,MixedForwardingChecks.checked _ _ h.2,?_⟩
  intro j Q hQ
  have hh := (List.all_eq_true.mp hp) (.origin Q) (List.mem_of_getElem? hQ)
  exact MixedGrowthChecks.plan_checked _ _ hh

theorem old_parts_valid (parts : List Part) (r : Spec) (es : List Entry)
    (hv : MixedForwardingCompiler.Valid (extended parts r) es) : ∀ a∈parts, ReplayControlFusion.ValidPart a := by
  intro a ha
  obtain ⟨j,hj⟩ := List.getElem?_of_mem ha
  exact hv.1 a (List.mem_of_getElem? (old_lookup parts r j a hj))

theorem body_bounds (parts : List Part) (es : List Entry) (i : Nat) (r : Spec) (P : Plan)
    (hi : es[i]?=some (.growth r)) (hj : es[r.callee]?=some (.origin P))
    (hg : (MixedGrowthCompiler.source parts es).FirstOrder) (hc : check parts es i=true)
    (x : List Char) (k : Nat) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    RLe (evV (MixedGrowthCompiler.source parts es) x .callByValuePar (tblV (MixedGrowthCompiler.source parts es) x .callByValuePar k) E (sourceBody r) p)
      (evV (MixedGrowthCompiler.source parts es) x .callByValuePar (tblV (MixedGrowthCompiler.source parts es) x .callByValuePar k) E
        ((plan parts r P).exp (sourceLeaf (extended parts r))) p) ∧
    RLe (evV (MixedGrowthCompiler.source parts es) x .callByValuePar (tblV (MixedGrowthCompiler.source parts es) x .callByValuePar k) E
        ((plan parts r P).exp (sourceLeaf (extended parts r))) p)
      (evV (MixedGrowthCompiler.source parts es) x .callByValuePar (tblV (MixedGrowthCompiler.source parts es) x .callByValuePar (k+1)) E (sourceBody r) p) := by
  have hv := checked parts es i r P hi hj hc
  have hparts := old_parts_valid parts r _ hv.2.1
  have hcallee : ruleAtM (MixedGrowthCompiler.source parts es).rules r.callee=some ⟨1,P.exp (sourceLeaf parts)⟩ := by
    rw [MixedGrowthCompiler.source_rule,hj]; rfl
  have hb := WordCallUnfolding.context_bounds (MixedGrowthCompiler.source parts es) r.callee (P.exp (sourceLeaf parts))
    hcallee (hg _ (ruleAtM_mem hcallee)) (power r.factor) (RepeatedWordArguments.expression_word (.param 0) True.intro _)
    (ForwardingHeadExpansion.frame r) x k E p hp
  have he := (OriginHeadEvaluation.plan_expression parts r P hparts (hv.2.2 r.callee P hj) hv.1
    (MixedGrowthCompiler.source parts es) x .callByValuePar (tblV (MixedGrowthCompiler.source parts es) x .callByValuePar k) E p).trans
    (OriginHeadEvaluation.unfolded_context parts r P (MixedGrowthCompiler.source parts es) x .callByValuePar
      (tblV (MixedGrowthCompiler.source parts es) x .callByValuePar k) E p)
  exact ⟨RLe.trans hb.1 (Or.inr he.symm),RLe.trans (Or.inr he) hb.2⟩

theorem related (parts : List Part) (es : List Entry) (i : Nat) (r : Spec) (P : Plan)
    (hi : es[i]?=some (.growth r)) (hj : es[r.callee]?=some (.origin P))
    (hg : (MixedGrowthCompiler.source parts es).FirstOrder) (hc : check parts es i=true) :
    FiniteBodyRewrite.Related (MixedGrowthCompiler.source parts es) (normalized parts es i r P) .callByValuePar 1 := by
  have hv := checked parts es i r P hi hj hc
  intro j
  by_cases hji : j=i
  · subst j
    simp only [normalized,MixedGrowthCompiler.source_rule,hi,entries,List.getElem?_set_self (List.getElem?_eq_some_iff.mp hi).1,Option.map_some]
    exact ⟨True.intro,fun x k E p hp => body_bounds parts es i r P hi hj hg hc x k E p hp⟩
  · simp only [normalized,MixedGrowthCompiler.source_rule,entries,List.getElem?_set_ne (Ne.symm hji)]
    cases he : es[j]? with
    | none => trivial
    | some e =>
      simp only [Option.map_some]
      refine ⟨True.intro,?_⟩
      intro x k E p hp
      have hbody : MixedGrowthCompiler.body (extended parts r) e=MixedGrowthCompiler.body parts e := by
        cases e with
        | growth s => rfl
        | origin Q => exact old_plan_eq parts r Q (hv.2.2 j Q he)
      rw [hbody]
      exact ⟨RLe.refl _,evV_mono (tblV_step _ _ _ k) _ _⟩

theorem observations_iff (parts : List Part) (es : List Entry) (i : Nat) (r : Spec) (P : Plan)
    (hi : es[i]?=some (.growth r)) (hj : es[r.callee]?=some (.origin P))
    (hg : (MixedGrowthCompiler.source parts es).FirstOrder) (hc : check parts es i=true)
    (e : MExp) (he : e.FirstOrder) (x : List Char) (rest : Option (List Char)) :
    SObs (MixedGrowthCompiler.source parts es) .callByValuePar e x rest ↔
      SObs (target parts es i r P) .callByValueSeq (render parts es i r P e) x rest :=
  (FiniteBodyRewrite.observations (related parts es i r P hi hj hg hc) hg
    (MixedForwardingCompiler.original_firstOrder _ _ (checked parts es i r P hi hj hc).2.1) (by decide) e he x rest).trans
    (MixedForwardingCorrespondence.observations_iff _ _ (checked parts es i r P hi hj hc).2.1 e he x rest)

theorem physical_bounds (parts : List Part) (es : List Entry) (i : Nat) (r : Spec) (P : Plan)
    (hi : es[i]?=some (.growth r)) (hj : es[r.callee]?=some (.origin P))
    (hg : (MixedGrowthCompiler.source parts es).FirstOrder) (hc : check parts es i=true)
    (e : MExp) (he : e.FirstOrder) (x : List Char) (k : Nat) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    RLe (evV (MixedGrowthCompiler.source parts es) x .callByValuePar (tblV (MixedGrowthCompiler.source parts es) x .callByValuePar k) E e p)
      (evV (target parts es i r P) x .callByValueSeq (tblV (target parts es i r P) x .callByValueSeq k) E (render parts es i r P e) p) ∧
    RLe (evV (target parts es i r P) x .callByValueSeq (tblV (target parts es i r P) x .callByValueSeq k) E (render parts es i r P e) p)
      (evV (MixedGrowthCompiler.source parts es) x .callByValuePar (tblV (MixedGrowthCompiler.source parts es) x .callByValuePar (2*((es.length+2)*k))) E e p) := by
  have hm := MixedForwardingCorrespondence.physical_bounds _ _ (checked parts es i r P hi hj hc).2.1 x k E e he p hp
  have hlen : (entries parts es i r P).length=es.length := by simp [entries]
  rw [hlen] at hm
  have ha := FiniteBodyRewrite.arities (related parts es i r P hi hj hg hc)
  have hf : RLe (evV (normalized parts es i r P) x .callByValuePar (tblV (normalized parts es i r P) x .callByValuePar k) E e p)
      (evV (target parts es i r P) x .callByValueSeq (tblV (target parts es i r P) x .callByValueSeq k) E (render parts es i r P e) p) := hm.1
  have hb : RLe (evV (target parts es i r P) x .callByValueSeq (tblV (target parts es i r P) x .callByValueSeq k) E (render parts es i r P e) p)
      (evV (normalized parts es i r P) x .callByValuePar (tblV (normalized parts es i r P) x .callByValuePar ((es.length+2)*k)) E e p) := hm.2
  rw [←SemanticBodyRewrite.evaluator (MixedGrowthCompiler.source parts es) (normalized parts es i r P) ha x .callByValuePar
    (tblV (normalized parts es i r P) x .callByValuePar k) E e p] at hf
  rw [←SemanticBodyRewrite.evaluator (MixedGrowthCompiler.source parts es) (normalized parts es i r P) ha x .callByValuePar
    (tblV (normalized parts es i r P) x .callByValuePar ((es.length+2)*k)) E e p] at hb
  exact ⟨RLe.trans (evV_mono (FiniteBodyRewrite.forward_tables (related parts es i r P hi hj hg hc) x k) e p) hf,
    RLe.trans hb (evV_mono (FiniteBodyRewrite.backward_tables (related parts es i r P hi hj hg hc) x ((es.length+2)*k)) e p)⟩

theorem undefined_iff (parts : List Part) (es : List Entry) (i : Nat) (r : Spec) (P : Plan)
    (hi : es[i]?=some (.growth r)) (hj : es[r.callee]?=some (.origin P))
    (hg : (MixedGrowthCompiler.source parts es).FirstOrder) (hc : check parts es i=true)
    (e : MExp) (he : e.FirstOrder) (x : List Char) :
    (∀ k, evV (MixedGrowthCompiler.source parts es) x .callByValuePar (tblV (MixedGrowthCompiler.source parts es) x .callByValuePar k) [] e x.length=none) ↔
      (∀ k, evV (target parts es i r P) x .callByValueSeq (tblV (target parts es i r P) x .callByValueSeq k) [] (render parts es i r P e) x.length=none) :=
  BoundedBodyRewrite.undefined_of_observations _ _ hg (MixedForwardingCompiler.target_firstOrder _ _)
    .callByValuePar .callByValueSeq (by decide) (by decide) e _ he (MixedForwardingCompiler.render_firstOrder _ _ e) x
    (fun rest => observations_iff parts es i r P hi hj hg hc e he x rest)

theorem checked_tail_closed (parts : List Part) (es : List Entry) (i : Nat) (r : Spec) (P : Plan)
    (hi : es[i]?=some (.growth r)) (hj : es[r.callee]?=some (.origin P)) (hc : check parts es i=true) :
    ReplayFallbackFusion.Closed r.tail :=
  ((checked parts es i r P hi hj hc).2.1.1 ⟨false,r.tail⟩ (List.mem_of_getElem? (tail_lookup parts r))).2 rfl

theorem rule_count (parts : List Part) (es : List Entry) (i : Nat) (r : Spec) (P : Plan) :
    (target parts es i r P).rules.length=es.length*(es.length+1)+3*parts.length+3 := by
  simp [target,MixedForwardingCompiler.rule_count,entries,extended,List.length_map,List.length_range,Nat.add_assoc]

theorem language_translation (parts : List Part) (es : List Entry) (i : Nat) (r : Spec) (P : Plan)
    (hi : es[i]?=some (.growth r)) (hj : es[r.callee]?=some (.origin P))
    (hg : (MixedGrowthCompiler.source parts es).FirstOrder) (hc : check parts es i=true) (e : MExp) (he : e.FirstOrder) :
    ∃ (g : MGrammar) (entry : MExp), g.FirstOrder ∧ entry.FirstOrder ∧
      ∀ x, SObs (MixedGrowthCompiler.source parts es) .callByValuePar e x (some []) ↔ SObs g .callByValueSeq entry x (some []) :=
  ⟨target parts es i r P,render parts es i r P e,MixedForwardingCompiler.target_firstOrder _ _,MixedForwardingCompiler.render_firstOrder _ _ e,
    fun x => observations_iff parts es i r P hi hj hg hc e he x (some [])⟩

end Shallot.MacroPeg.CBV.OriginHeadInlining
