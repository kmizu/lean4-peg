import MacroPeg.CBV.ForwardingSeqHead

namespace Shallot.MacroPeg.CBV.ForwardingSeqCorrespondence
open ForwardingSeqCompiler
open MultiplyingPrefixCompiler (Spec arity view modes address render prefixCall origin_mode
  view_word view_value render_firstOrder)
open RepeatedWordArguments (copies expression)

/-- All generated views correspond in the actual recursive tables. There
is no semantic row oracle in the final translation. -/
theorem tables_rows (rs : List Spec) (hv : Valid rs) (x : List Char) (k : Nat) : Rows rs x k := by
  induction k with
  | zero => intro i r hi q m hmode v p j h; simp [sourceTable,targetTable,tblV,valAt_nil]
  | succ k ih =>
    intro i r hi q m hmode v p j h
    have hs : ruleAtM (source rs).rules i=some ⟨1,ForwardingHeadExpansion.expanded rs i⟩ := by rw [source_rule,hi]; rfl
    have ht := target_rule rs q m i r hmode hi
    rw [valAt_tblV_succ hs _ h.1,valAt_tblV_succ ht _ h.2.1]
    exact ForwardingSeqHead.evaluator rs hv x k ih (rs.length+1) i []
      (ForwardingHeadExpansion.expanded_complete rs i) m (mode_positive rs hv q m hmode) v p j h

theorem evaluator_eq (rs : List Spec) (hv : Valid rs) (x : List Char) (k : Nat)
    (E : List (List Char)) (e : MExp) (he : e.FirstOrder) (p : Nat) (hp : p≤x.length) :
    evV (source rs) x .callByValuePar (sourceTable rs x k) E e p=
      evV (target rs) x .callByValueSeq (targetTable rs x k) E (render rs.length e) p :=
  ForwardingSeqEvaluation.evaluator rs hv x k (tables_rows rs hv x k) E e he p hp

theorem physical_bounds (rs : List Spec) (hv : Valid rs) (x : List Char) (k : Nat)
    (E : List (List Char)) (e : MExp) (he : e.FirstOrder) (p : Nat) (hp : p≤x.length) :
    RLe (evV (MultiplyingPrefixCompiler.source rs) x .callByValuePar
      (tblV (MultiplyingPrefixCompiler.source rs) x .callByValuePar k) E e p)
      (evV (target rs) x .callByValueSeq (targetTable rs x k) E (render rs.length e) p) ∧
    RLe (evV (target rs) x .callByValueSeq (targetTable rs x k) E (render rs.length e) p)
      (evV (MultiplyingPrefixCompiler.source rs) x .callByValuePar
        (tblV (MultiplyingPrefixCompiler.source rs) x .callByValuePar ((rs.length+2)*k)) E e p) := by
  have hb := ForwardingHeadNormalization.physical_bounds rs (raw_firstOrder rs hv) x k
  have ha := FiniteBodyRewrite.arities (ForwardingHeadNormalization.related rs (raw_firstOrder rs hv))
  rw [←evaluator_eq rs hv x k E e he p hp,
    ←SemanticBodyRewrite.evaluator (MultiplyingPrefixCompiler.source rs) (source rs) ha x .callByValuePar
      (sourceTable rs x k) E e p]
  exact ⟨evV_mono hb.1 e p,evV_mono hb.2 e p⟩

theorem decide_eq (rs : List Spec) (hv : Valid rs) (e : MExp) (he : e.FirstOrder) (x : List Char) :
    decideObsV .callByValuePar (source rs) x e=decideObsV .callByValueSeq (target rs) x (render rs.length e) := by
  unfold decideObsV
  rw [ScannerPairFusion.stable_result_eq (source rs) (target rs) x .callByValuePar .callByValueSeq
    e (render rs.length e) (fun k => evaluator_eq rs hv x k [] e he x.length (Nat.le_refl _))]

theorem normalized_observations_iff (rs : List Spec) (hv : Valid rs) (e : MExp) (he : e.FirstOrder)
    (x : List Char) (rest : Option (List Char)) :
    SObs (source rs) .callByValuePar e x rest ↔ SObs (target rs) .callByValueSeq (render rs.length e) x rest := by
  rw [←decideObsV_iff (source_firstOrder rs hv) (by decide) he,
    ←decideObsV_iff (target_firstOrder rs) (by decide) (render_firstOrder rs.length e),decide_eq rs hv e he x]

/-- Transfer the actual original Par language through finite head
normalization into the fixed Seq grammar. Factor-1 cycles and finite paths
may coexist with arbitrary positive multiplication factors. -/
theorem observations_iff (rs : List Spec) (hv : Valid rs) (e : MExp) (he : e.FirstOrder)
    (x : List Char) (rest : Option (List Char)) :
    SObs (MultiplyingPrefixCompiler.source rs) .callByValuePar e x rest ↔
      SObs (target rs) .callByValueSeq (render rs.length e) x rest :=
  (ForwardingHeadNormalization.observations_iff rs (raw_firstOrder rs hv) e he x rest).trans
    (normalized_observations_iff rs hv e he x rest)

theorem undefined_iff (rs : List Spec) (hv : Valid rs) (x : List Char) (E : List (List Char))
    (e : MExp) (he : e.FirstOrder) (p : Nat) (hp : p≤x.length) :
    (∀ k, evV (MultiplyingPrefixCompiler.source rs) x .callByValuePar
      (tblV (MultiplyingPrefixCompiler.source rs) x .callByValuePar k) E e p=none) ↔
    (∀ k, evV (target rs) x .callByValueSeq (targetTable rs x k) E (render rs.length e) p=none) := by
  rw [ForwardingHeadNormalization.undefined_iff rs (raw_firstOrder rs hv) x E e p]
  simp only [evaluator_eq rs hv x _ E e he p hp]

theorem language_translation (rs : List Spec) (hv : Valid rs) (e : MExp) (he : e.FirstOrder) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧
      ∀ x, SObs (MultiplyingPrefixCompiler.source rs) .callByValuePar e x (some []) ↔
        SObs g .callByValueSeq start x (some []) :=
  ⟨target rs,render rs.length e,target_firstOrder rs,render_firstOrder rs.length e,
    fun x => observations_iff rs hv e he x (some [])⟩

end Shallot.MacroPeg.CBV.ForwardingSeqCorrespondence
