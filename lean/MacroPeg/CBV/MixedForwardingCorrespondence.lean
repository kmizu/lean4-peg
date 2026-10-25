import MacroPeg.CBV.MixedForwardingHead
import MacroPeg.CBV.ScannerPairFusion

namespace Shallot.MacroPeg.CBV.MixedForwardingCorrespondence
open MixedForwardingCompiler
open MultiplyingPrefixCompiler (Spec arity view)
open ReplayControlFusion (Part Plan)
open RepeatedWordArguments (copies expression)

/-- Growth variants and origin-control rows close together over the actual
recursive tables. No separately supplied row semantics remains. -/
theorem tables_rows (parts : List Part) (es : List Entry) (hv : Valid parts es)
    (x : List Char) (k : Nat) : Rows parts es x k := by
  induction k with
  | zero =>
    constructor
    · intro i r hi q m hmode v p j h; rfl
    · intro i P hr w p q h
      change none=P.eval (leafRows parts es (targetTable parts es x 0) w p q) p
      symm
      apply Plan.eval_none
      apply Plan.all_imp (t := P) _ (hv.2 (.origin P) (List.mem_of_getElem? hr))
      intro j hj
      obtain ⟨r,hr⟩ := hj
      simp only [leafRows,hr,targetTable,tblV,valAt_nil]
      cases r.replay <;> rfl
  | succ k ih =>
    constructor
    · intro i r hi q m hmode v p j h
      have hs : ruleAtM (source parts es).rules i=some ⟨1,ForwardingHeadExpansion.expanded (metadata es) i⟩ := by rw [source_rule,hi]; rfl
      have ht := target_rule parts es q m i r hmode hi
      rw [valAt_tblV_succ hs _ h.1,valAt_tblV_succ ht _ h.2.1]
      have hc : ForwardingHeadExpansion.complete (metadata es) (es.length+1) i []=true := by
        simpa only [metadata,List.length_map] using ForwardingHeadExpansion.expanded_complete (metadata es) i
      simpa only [ForwardingHeadExpansion.expanded,metadata,List.length_map,targetBody] using MixedForwardingHead.evaluator parts es hv x k ih (es.length+1) i []
        ((selected_iff es i).mpr ⟨r,hi⟩) hc m (mode_positive parts es hv q m hmode) v p j h
    · intro i P hr w p q h
      have hs : ruleAtM (source parts es).rules i=some ⟨1,P.exp (ReplayControlFusion.sourceLeaf parts)⟩ := by
        rw [source_rule,hr]; rfl
      rw [valAt_tblV_succ hs [w] h.1,Plan.exp_eval]
      apply Plan.eval_congr
      apply Plan.all_imp (t := P) _ (hv.2 (.origin P) (List.mem_of_getElem? hr))
      intro j hj
      obtain ⟨r,hr⟩ := hj
      have he := hv.1 r (List.mem_of_getElem? hr)
      have ht : ruleAtM (target parts es).rules (offset es+j)=some (helper parts es r) := by rw [helper_rule,hr]; rfl
      simp only [ReplayControlFusion.sourceLeaf,leafRows,hr]
      cases hb : r.replay
      · simp only [Bool.false_eq_true,if_false]
        rw [valAt_tblV_succ ht [] h.1]
        change evV (source parts es) x .callByValuePar (sourceTable parts es x k) [w] r.body p=
          evV (target parts es) x .callByValueSeq (targetTable parts es x k) [] (render parts es r.body) p
        rw [ReplayFallbackFusion.closed_env _ _ _ _ r.body (he.2 hb) [w] p]
        exact MixedForwardingEvaluation.evaluator parts es hv x k ih [] r.body he.1 p h.1
      · simp only [if_true]
        rw [valAt_tblV_succ ht [w] h.2.1]
        have hstrip := (CBVtoCBN.stripPrefix_exact w (sfx x p) (sfx x q)).mpr h.2.2
        simp only [evV,List.getElem?_cons_zero,hstrip,length_sfx x h.2.1]
        exact MixedForwardingEvaluation.evaluator parts es hv x k ih [w] r.body he.1 q h.2.1

theorem evaluator_eq (parts : List Part) (es : List Entry) (hv : Valid parts es) (x : List Char) (k : Nat)
    (E : List (List Char)) (e : MExp) (he : e.FirstOrder) (p : Nat) (hp : p≤x.length) :
    evV (source parts es) x .callByValuePar (sourceTable parts es x k) E e p =
      evV (target parts es) x .callByValueSeq (targetTable parts es x k) E (render parts es e) p :=
  MixedForwardingEvaluation.evaluator parts es hv x k (tables_rows parts es hv x k) E e he p hp

theorem undefined_iff (parts : List Part) (es : List Entry) (hv : Valid parts es) (x : List Char)
    (E : List (List Char)) (e : MExp) (he : e.FirstOrder) (p : Nat) (hp : p≤x.length) :
    (∀ k, evV (source parts es) x .callByValuePar (sourceTable parts es x k) E e p=none) ↔
      (∀ k, evV (target parts es) x .callByValueSeq (targetTable parts es x k) E (render parts es e) p=none) := by
  simp only [evaluator_eq parts es hv x _ E e he p hp]

theorem decide_eq (parts : List Part) (es : List Entry) (hv : Valid parts es) (e : MExp) (he : e.FirstOrder) (x : List Char) :
    decideObsV .callByValuePar (source parts es) x e =
      decideObsV .callByValueSeq (target parts es) x (render parts es e) := by
  unfold decideObsV
  rw [ScannerPairFusion.stable_result_eq (source parts es) (target parts es) x .callByValuePar .callByValueSeq
    e (render parts es e) (fun k => evaluator_eq parts es hv x k [] e he x.length (Nat.le_refl _))]

theorem normalized_observations_iff (parts : List Part) (es : List Entry) (hv : Valid parts es) (e : MExp) (he : e.FirstOrder)
    (x : List Char) (r : Option (List Char)) :
    SObs (source parts es) .callByValuePar e x r ↔ SObs (target parts es) .callByValueSeq (render parts es e) x r := by
  rw [← decideObsV_iff (source_firstOrder parts es hv) (by decide) he,
    ← decideObsV_iff (target_firstOrder parts es) (by decide) (render_firstOrder parts es e),decide_eq parts es hv e he x]

theorem physical_bounds (parts : List Part) (es : List Entry) (hv : Valid parts es)
    (x : List Char) (k : Nat) (E : List (List Char)) (e : MExp) (he : e.FirstOrder)
    (p : Nat) (hp : p≤x.length) :
    RLe (evV (original parts es) x .callByValuePar (tblV (original parts es) x .callByValuePar k) E e p)
      (evV (target parts es) x .callByValueSeq (targetTable parts es x k) E (render parts es e) p) ∧
    RLe (evV (target parts es) x .callByValueSeq (targetTable parts es x k) E (render parts es e) p)
      (evV (original parts es) x .callByValuePar (tblV (original parts es) x .callByValuePar ((es.length+2)*k)) E e p) := by
  have hb := SelectedForwardingNormalization.physical_bounds _ (original_firstOrder parts es hv) _ _ (selected_valid parts es hv) x k
  have hlen : (original parts es).rules.length=es.length := by simp [original,MixedGrowthCompiler.source]
  rw [hlen] at hb
  have ha := SelectedForwardingNormalization.arities (original parts es) (metadata es) (selected es)
  rw [←evaluator_eq parts es hv x k E e he p hp,
    ←SemanticBodyRewrite.evaluator (original parts es) (source parts es) ha x .callByValuePar
      (sourceTable parts es x k) E e p]
  exact ⟨evV_mono hb.1 e p,evV_mono hb.2 e p⟩

theorem observations_iff (parts : List Part) (es : List Entry) (hv : Valid parts es)
    (e : MExp) (he : e.FirstOrder) (x : List Char) (rest : Option (List Char)) :
    SObs (original parts es) .callByValuePar e x rest ↔
      SObs (target parts es) .callByValueSeq (render parts es e) x rest :=
  (FiniteBodyRewrite.observations
    (SelectedForwardingNormalization.related _ (original_firstOrder parts es hv) _ _ (selected_valid parts es hv))
      (original_firstOrder parts es hv) (source_firstOrder parts es hv) (by decide) e he x rest).trans
    (normalized_observations_iff parts es hv e he x rest)

theorem original_undefined_iff (parts : List Part) (es : List Entry) (hv : Valid parts es)
    (x : List Char) (E : List (List Char)) (e : MExp) (he : e.FirstOrder) (p : Nat) (hp : p≤x.length) :
    (∀ k, evV (original parts es) x .callByValuePar (tblV (original parts es) x .callByValuePar k) E e p=none) ↔
      (∀ k, evV (target parts es) x .callByValueSeq (targetTable parts es x k) E (render parts es e) p=none) :=
  (FiniteBodyRewrite.undefined_iff (SelectedForwardingNormalization.related _ (original_firstOrder parts es hv)
    _ _ (selected_valid parts es hv)) x E e p).trans (undefined_iff parts es hv x E e he p hp)

/-- A fixed grammar with n(n+1)+parts.length rules preserves the original input
language. No finite palette, alphabet restriction, or table oracle is supplied. -/
theorem language_translation (parts : List Part) (es : List Entry) (hv : Valid parts es) (e : MExp) (he : e.FirstOrder) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧
      ∀ x, SObs (original parts es) .callByValuePar e x (some []) ↔ SObs g .callByValueSeq start x (some []) :=
  ⟨target parts es,render parts es e,target_firstOrder parts es,render_firstOrder parts es e,
    fun x => observations_iff parts es hv e he x (some [])⟩


end Shallot.MacroPeg.CBV.MixedForwardingCorrespondence
