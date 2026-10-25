import MacroPeg.CBV.CanonicalProducerEvaluation

namespace Shallot.MacroPeg.CBV.CanonicalProducerCorrespondence
open CanonicalProducerCompiler
open ReplayControlFusion (Part)
open RecursiveProducedCompiler (Entry)

def delay (ps : List Part) (es : List Entry) := (es.map (fun e => cost es (RecursiveProducedCompiler.body ps e))).sum

theorem mem_le_sum {α : Type} (f : α → Nat) (xs : List α) (a : α) (ha : a∈xs) : f a≤(xs.map f).sum := by
  induction xs with
  | nil => cases ha
  | cons b xs ih =>
    simp only [List.mem_cons] at ha
    simp only [List.map_cons,List.sum_cons]
    rcases ha with rfl|ha
    · omega
    · have hh := ih ha; omega

theorem prepared_rule (ps : List Part) (es : List Entry) (i : Nat) :
    ruleAtM (prepared ps es).rules i=(es[i]?).map (fun e => ⟨1,
      RecursiveProducedCompiler.body (outputParts ps es) (outputEntry es e)⟩) := by
  rw [prepared,RecursiveProducedCompiler.source_rule]
  simp only [outputEntries,List.getElem?_map,Option.map_map]
  cases es[i]? <;> rfl

theorem related (ps : List Part) (es : List Entry) (cores : List MExp) (hc : check ps es cores=true) :
    FiniteBodyRewrite.Related (source ps es) (prepared ps es) .callByValuePar (delay ps es) := by
  intro i
  rw [RecursiveProducedCompiler.source_rule,prepared_rule]
  cases hi : es[i]? with
  | none => trivial
  | some e =>
    refine ⟨rfl,?_⟩
    intro x k E p hp
    have hm := List.mem_of_getElem? hi
    have he := checked_body ps es cores hc e hm
    dsimp only
    rw [←checked_shape ps es cores hc e hm]
    have h := CanonicalProducerEvaluation.bounds ps es cores hc x E _ he.1 he.2 k p hp
    refine ⟨h.1,h.2.trans ?_⟩
    have hcost : cost es (RecursiveProducedCompiler.body ps e)≤delay ps es :=
      mem_le_sum (fun a => cost es (RecursiveProducedCompiler.body ps a)) es e hm
    exact evV_mono (tblV_le _ _ _ (Nat.add_le_add_left hcost k)) _ _

theorem render_firstOrder (ps : List Part) (es : List Entry) (cores : List MExp) (hc : check ps es cores=true) :
    ∀ e, e.FirstOrder → (render es e).FirstOrder
  | .call i [a],he => by
    have ih := render_firstOrder ps es cores hc a he.1
    cases hi : es[i]? with
    | none => simp only [render,hi]; exact ⟨ih,True.intro⟩
    | some e => cases e with
      | growth r | origin P => simp only [render,hi]; exact ⟨ih,True.intro⟩
      | produced d b =>
        simp only [render,hi]
        split
        · exact ⟨ih,True.intro⟩
        · exact ⟨ih,ReplayFallbackFusion.closed_firstOrder d (checked_producer ps es cores hc i d b hi).1,True.intro⟩
  | .seq a b,he | .alt a b,he => ⟨render_firstOrder ps es cores hc a he.1,render_firstOrder ps es cores hc b he.2⟩
  | .notP a,he | .star a,he => render_firstOrder ps es cores hc a he
  | .eps,he | .any,he | .chr _,he | .range _ _,he | .lit _,he | .param _,he | .dbg _,he | .lam _ _,he
  | .invoke _ _ _,he | .callParam _ _,he | .call _ [],he | .call _ (_::_::_),he => he

theorem preparation_bounds (ps : List Part) (es : List Entry) (cores : List MExp) (hc : check ps es cores=true)
    (x : List Char) (E : List (List Char)) (e : MExp) (he : e.FirstOrder) (hs : conforms ps es cores e=true)
    (k p : Nat) (hp : p≤x.length) :
    RLe (evV (source ps es) x .callByValuePar (tblV (source ps es) x .callByValuePar k) E e p)
      (evV (prepared ps es) x .callByValuePar (tblV (prepared ps es) x .callByValuePar k) E (render es e) p) ∧
    RLe (evV (prepared ps es) x .callByValuePar (tblV (prepared ps es) x .callByValuePar k) E (render es e) p)
      (evV (source ps es) x .callByValuePar
        (tblV (source ps es) x .callByValuePar ((delay ps es+1)*k+cost es e)) E e p) := by
  have hr := related ps es cores hc
  have ha := FiniteBodyRewrite.arities hr
  have hf := @evV_mono (source ps es) x .callByValuePar _ _ E (FiniteBodyRewrite.forward_tables hr x k) (render es e) p
  rw [SemanticBodyRewrite.evaluator _ _ ha x .callByValuePar (tblV (prepared ps es) x .callByValuePar k) E (render es e) p] at hf
  have hb := @evV_mono (prepared ps es) x .callByValuePar _ _ E (FiniteBodyRewrite.backward_tables hr x k) (render es e) p
  rw [←SemanticBodyRewrite.evaluator _ _ ha x .callByValuePar
    (tblV (source ps es) x .callByValuePar ((delay ps es+1)*k)) E (render es e) p] at hb
  exact ⟨(CanonicalProducerEvaluation.bounds ps es cores hc x E e he hs k p hp).1.trans hf,
    hb.trans (CanonicalProducerEvaluation.bounds ps es cores hc x E e he hs ((delay ps es+1)*k) p hp).2⟩

theorem stable_eq (ps : List Part) (es : List Entry) (cores : List MExp) (hc : check ps es cores=true)
    (x : List Char) (E : List (List Char)) (e : MExp) (he : e.FirstOrder) (hs : conforms ps es cores e=true)
    (p : Nat) (hp : p≤x.length) :
    evV (source ps es) x .callByValuePar (StablePar.table (source ps es) x) E e p=
      evV (source ps es) x .callByValuePar (StablePar.table (source ps es) x) E (render es e) p := by
  have hb := CanonicalProducerEvaluation.bounds ps es cores hc x E e he hs (iterBoundV (source ps es) x) p hp
  exact WordExpansionRefinement.antisymm hb.1 (hb.2.trans (StablePar.eval_le _ _ _ E e p hp))

theorem root_observations (ps : List Part) (es : List Entry) (cores : List MExp) (hc : check ps es cores=true)
    (e : MExp) (he : e.FirstOrder) (hs : conforms ps es cores e=true) (x : List Char) (rest : Option (List Char)) :
    SObs (source ps es) .callByValuePar e x rest ↔ SObs (source ps es) .callByValuePar (render es e) x rest := by
  have hg := source_firstOrder ps es cores hc
  rw [←decideObsV_iff hg (by decide) he,←decideObsV_iff hg (by decide) (render_firstOrder ps es cores hc e he)]
  unfold decideObsV
  rw [stable_eq ps es cores hc x [] e he hs x.length (Nat.le_refl _)]

theorem observations_iff (ps : List Part) (es : List Entry) (cores : List MExp) (hc : check ps es cores=true)
    (e : MExp) (he : e.FirstOrder) (hs : conforms ps es cores e=true)
    (ho : RecursiveProducedCompiler.conforms (outputEntries es) (render es e)=true)
    (x : List Char) (rest : Option (List Char)) :
    SObs (source ps es) .callByValuePar e x rest ↔ SObs (target ps es) .callByValueSeq (entry ps es e) x rest :=
  (root_observations ps es cores hc e he hs x rest).trans
    ((FiniteBodyRewrite.observations (related ps es cores hc) (source_firstOrder ps es cores hc)
      (RecursiveProducedCompiler.source_firstOrder _ _ (prepared_checked ps es cores hc)) (by decide)
      (render es e) (render_firstOrder ps es cores hc e he) x rest).trans
      (RecursiveProducedCorrespondence.observations_iff _ _ (prepared_checked ps es cores hc)
        (render es e) (render_firstOrder ps es cores hc e he) ho x rest))

theorem undefined_iff (ps : List Part) (es : List Entry) (cores : List MExp) (hc : check ps es cores=true)
    (e : MExp) (he : e.FirstOrder) (hs : conforms ps es cores e=true)
    (ho : RecursiveProducedCompiler.conforms (outputEntries es) (render es e)=true) (x : List Char) :
    (∀ k, evV (source ps es) x .callByValuePar (tblV (source ps es) x .callByValuePar k) [] e x.length=none) ↔
      (∀ k, evV (target ps es) x .callByValueSeq (tblV (target ps es) x .callByValueSeq k) [] (entry ps es e) x.length=none) :=
  BoundedBodyRewrite.undefined_of_observations _ _ (source_firstOrder ps es cores hc) (MixedForwardingCompiler.target_firstOrder _ _)
    .callByValuePar .callByValueSeq (by decide) (by decide) e _ he (MixedForwardingCompiler.render_firstOrder _ _ _)
    x (fun rest => observations_iff ps es cores hc e he hs ho x rest)

theorem language_translation (ps : List Part) (es : List Entry) (cores : List MExp) (hc : check ps es cores=true)
    (e : MExp) (he : e.FirstOrder) (hs : conforms ps es cores e=true)
    (ho : RecursiveProducedCompiler.conforms (outputEntries es) (render es e)=true) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧
      ∀ x, SObs (source ps es) .callByValuePar e x (some []) ↔ SObs g .callByValueSeq start x (some []) :=
  ⟨target ps es,entry ps es e,MixedForwardingCompiler.target_firstOrder _ _,MixedForwardingCompiler.render_firstOrder _ _ _,
    fun x => observations_iff ps es cores hc e he hs ho x (some [])⟩

theorem checked_observations (ps : List Part) (es : List Entry) (cores : List MExp) (hc : check ps es cores=true)
    (e : MExp) (hr : rootCheck ps es cores e=true) (x : List Char) (rest : Option (List Char)) :
    SObs (source ps es) .callByValuePar e x rest ↔ SObs (target ps es) .callByValueSeq (entry ps es e) x rest := by
  have h := root_checked ps es cores e hr
  exact observations_iff ps es cores hc e h.1 h.2.1 h.2.2 x rest

theorem checked_language (ps : List Part) (es : List Entry) (cores : List MExp) (hc : check ps es cores=true)
    (e : MExp) (hr : rootCheck ps es cores e=true) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧
      ∀ x, SObs (source ps es) .callByValuePar e x (some []) ↔ SObs g .callByValueSeq start x (some []) := by
  have h := root_checked ps es cores e hr
  exact language_translation ps es cores hc e h.1 h.2.1 h.2.2

end Shallot.MacroPeg.CBV.CanonicalProducerCorrespondence
