import MacroPeg.CBV.DoublingPrefixCalls
import MacroPeg.CBV.ScannerPairFusion

namespace Shallot.MacroPeg.CBV.DoublingPrefixCorrespondence
open DoublingPrefixCompiler

/-- The two representations of a captured value correspond in the actual
iterated tables, including recursive calls made before its first replay. -/
theorem tables_rows (rs : List Spec) (hv : Valid rs) (x : List Char) (k : Nat) : Rows rs x k := by
  induction k with
  | zero => intro i r hi half v p j h; simp [sourceTable,targetTable,tblV,valAt_nil]
  | succ k ih =>
    intro i r hi half v p j h
    have hs : ruleAtM (source rs).rules i=some ⟨1,sourceBody r⟩ := by rw [source_rule,hi]; rfl
    have ht := target_rule rs half i r hi
    have hr := hv r (List.mem_of_getElem? hi)
    rw [valAt_tblV_succ hs _ h.1,valAt_tblV_succ ht _ h.2.1]
    have hf : evV (source rs) x .callByValuePar (sourceTable rs x k) [word half v]
        (.seq (.param 0) r.fallback) p =
        evV (target rs) x .callByValueSeq (targetTable rs x k) [v]
          (MExp.subst [view half] (render rs r.fallback)) j := by
      rw [evV_seq_ok (GuardedReplayControl.aligned_replay (source rs) x (word half v)
        .callByValuePar (sourceTable rs x k) p j h)]
      exact DoublingPrefixEvaluation.view_evaluator rs hv x k ih half v r.fallback hr.2 j h.2.1
    have hc := DoublingPrefixCalls.prefix_eq rs x k ih r.callee half v p j h
    have hb : evV (source rs) x .callByValuePar (sourceTable rs x k) [word half v]
        (.seq (.call r.callee [.seq (.param 0) (.param 0)]) r.tail) p =
        evV (target rs) x .callByValueSeq (targetTable rs x k) [v]
          (.seq (.call (address rs true r.callee) [view half])
            (MExp.subst [view half] (render rs r.tail))) j := by
      cases ha : evV (source rs) x .callByValuePar (sourceTable rs x k) [word half v]
          (.call r.callee [.seq (.param 0) (.param 0)]) p with
      | none => rw [evV_seq_none ha,evV_seq_none (hc.symm.trans ha)]
      | some a => cases a with
        | none => rw [evV_seq_fail ha,evV_seq_fail (hc.symm.trans ha)]
        | some q =>
          rw [evV_seq_ok ha,evV_seq_ok (hc.symm.trans ha)]
          exact DoublingPrefixEvaluation.view_evaluator rs hv x k ih half v r.tail hr.1 q
            (evV_ok (tblV_ok (source rs) x .callByValuePar k) _ p h.1 q ha)
    change evV (source rs) x .callByValuePar (sourceTable rs x k) [word half v] (sourceBody r) p =
      evV (target rs) x .callByValueSeq (targetTable rs x k) [v] (targetBody rs half r) j
    cases ha : evV (source rs) x .callByValuePar (sourceTable rs x k) [word half v]
        (.seq (.call r.callee [.seq (.param 0) (.param 0)]) r.tail) p with
    | none => simp only [sourceBody,targetBody,evV_alt_none ha,evV_alt_none (hb.symm.trans ha)]
    | some a => cases a with
      | none =>
        simp only [sourceBody,targetBody,evV_alt_fail ha,evV_alt_fail (hb.symm.trans ha)]
        exact hf
      | some q => simp only [sourceBody,targetBody,evV_alt_ok ha,evV_alt_ok (hb.symm.trans ha)]

theorem evaluator_eq (rs : List Spec) (hv : Valid rs) (x : List Char) (k : Nat)
    (E : List (List Char)) (e : MExp) (he : e.FirstOrder) (p : Nat) (hp : p≤x.length) :
    evV (source rs) x .callByValuePar (sourceTable rs x k) E e p =
      evV (target rs) x .callByValueSeq (targetTable rs x k) E (render rs e) p :=
  DoublingPrefixEvaluation.evaluator rs hv x k (tables_rows rs hv x k) E e he p hp

theorem undefined_iff (rs : List Spec) (hv : Valid rs) (x : List Char)
    (E : List (List Char)) (e : MExp) (he : e.FirstOrder) (p : Nat) (hp : p≤x.length) :
    (∀ k, evV (source rs) x .callByValuePar (sourceTable rs x k) E e p=none) ↔
      (∀ k, evV (target rs) x .callByValueSeq (targetTable rs x k) E (render rs e) p=none) := by
  simp only [evaluator_eq rs hv x _ E e he p hp]

theorem decide_eq (rs : List Spec) (hv : Valid rs) (e : MExp) (he : e.FirstOrder) (x : List Char) :
    decideObsV .callByValuePar (source rs) x e =
      decideObsV .callByValueSeq (target rs) x (render rs e) := by
  unfold decideObsV
  rw [ScannerPairFusion.stable_result_eq (source rs) (target rs) x .callByValuePar .callByValueSeq
    e (render rs e) (fun k => evaluator_eq rs hv x k [] e he x.length (Nat.le_refl _))]

theorem observations_iff (rs : List Spec) (hv : Valid rs) (e : MExp) (he : e.FirstOrder)
    (x : List Char) (r : Option (List Char)) :
    SObs (source rs) .callByValuePar e x r ↔ SObs (target rs) .callByValueSeq (render rs e) x r := by
  rw [← decideObsV_iff (source_firstOrder rs hv) (by decide) he,
    ← decideObsV_iff (target_firstOrder rs) (by decide) (render_firstOrder rs e),decide_eq rs hv e he x]

/-- A fixed grammar with twice as many rules preserves the original input
language. No finite palette, alphabet restriction, or table oracle is supplied. -/
theorem language_translation (rs : List Spec) (hv : Valid rs) (e : MExp) (he : e.FirstOrder) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧
      ∀ x, SObs (source rs) .callByValuePar e x (some []) ↔ SObs g .callByValueSeq start x (some []) :=
  ⟨target rs,render rs e,target_firstOrder rs,render_firstOrder rs e,
    fun x => observations_iff rs hv e he x (some [])⟩

end Shallot.MacroPeg.CBV.DoublingPrefixCorrespondence
