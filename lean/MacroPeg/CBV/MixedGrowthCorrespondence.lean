import MacroPeg.CBV.MixedGrowthCalls
import MacroPeg.CBV.ScannerPairFusion

namespace Shallot.MacroPeg.CBV.MixedGrowthCorrespondence
open MixedGrowthCompiler
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
    ·
      intro i r hi q m hmode v p j h
      have hs : ruleAtM (source parts es).rules i=some ⟨1,MultiplyingPrefixCompiler.sourceBody r⟩ := by rw [source_rule,hi]; rfl
      have ht := target_rule parts es q m i r hmode hi
      have hm := mode_positive parts es hv q m hmode
      have hr := hv.2 (.growth r) (List.mem_of_getElem? hi)
      rw [valAt_tblV_succ hs _ h.1,valAt_tblV_succ ht _ h.2.1]
      have hf : evV (source parts es) x .callByValuePar (sourceTable parts es x k) [copies v m]
          (.seq (.param 0) r.fallback) p =
          evV (target parts es) x .callByValueSeq (targetTable parts es x k) (List.replicate (arity m) v)
            (MExp.subst [view m] (render parts es r.fallback)) j := by
        rw [evV_seq_ok (GuardedReplayControl.aligned_replay (source parts es) x (copies v m)
          .callByValuePar (sourceTable parts es x k) p j h)]
        exact MixedGrowthEvaluation.view_evaluator parts es hv x k ih m hm v r.fallback hr.2.2.1 j h.2.1
      have hc := MixedGrowthCalls.prefix_eq parts es hv x k ih i r hi m hm v p j h
      have hb : evV (source parts es) x .callByValuePar (sourceTable parts es x k) [copies v m]
          (.seq (.call r.callee [expression (.param 0) r.factor]) r.tail) p =
          evV (target parts es) x .callByValueSeq (targetTable parts es x k) (List.replicate (arity m) v)
            (.seq (prefixCall es i m r)
              (MExp.subst [view m] (render parts es r.tail))) j := by
        cases ha : evV (source parts es) x .callByValuePar (sourceTable parts es x k) [copies v m]
            (.call r.callee [expression (.param 0) r.factor]) p with
        | none => rw [evV_seq_none ha,evV_seq_none (hc.symm.trans ha)]
        | some a => cases a with
          | none => rw [evV_seq_fail ha,evV_seq_fail (hc.symm.trans ha)]
          | some q =>
            rw [evV_seq_ok ha,evV_seq_ok (hc.symm.trans ha)]
            exact MixedGrowthEvaluation.view_evaluator parts es hv x k ih m hm v r.tail hr.2.1 q
              (evV_ok (tblV_ok (source parts es) x .callByValuePar k) _ p h.1 q ha)
      change evV (source parts es) x .callByValuePar (sourceTable parts es x k) [copies v m] (MultiplyingPrefixCompiler.sourceBody r) p =
        evV (target parts es) x .callByValueSeq (targetTable parts es x k) (List.replicate (arity m) v) (growthBody parts es i m r) j
      cases ha : evV (source parts es) x .callByValuePar (sourceTable parts es x k) [copies v m]
          (.seq (.call r.callee [expression (.param 0) r.factor]) r.tail) p with
      | none => simp only [MultiplyingPrefixCompiler.sourceBody,growthBody,rebound,evV_alt_none ha,evV_alt_none (hb.symm.trans ha)]
      | some a => cases a with
        | none =>
          simp only [MultiplyingPrefixCompiler.sourceBody,growthBody,rebound,evV_alt_fail ha,evV_alt_fail (hb.symm.trans ha)]
          exact hf
        | some q => simp only [MultiplyingPrefixCompiler.sourceBody,growthBody,rebound,evV_alt_ok ha,evV_alt_ok (hb.symm.trans ha)]
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
        exact MixedGrowthEvaluation.evaluator parts es hv x k ih [] r.body he.1 p h.1
      · simp only [if_true]
        rw [valAt_tblV_succ ht [w] h.2.1]
        have hstrip := (CBVtoCBN.stripPrefix_exact w (sfx x p) (sfx x q)).mpr h.2.2
        simp only [evV,List.getElem?_cons_zero,hstrip,length_sfx x h.2.1]
        exact MixedGrowthEvaluation.evaluator parts es hv x k ih [w] r.body he.1 q h.2.1

theorem evaluator_eq (parts : List Part) (es : List Entry) (hv : Valid parts es) (x : List Char) (k : Nat)
    (E : List (List Char)) (e : MExp) (he : e.FirstOrder) (p : Nat) (hp : p≤x.length) :
    evV (source parts es) x .callByValuePar (sourceTable parts es x k) E e p =
      evV (target parts es) x .callByValueSeq (targetTable parts es x k) E (render parts es e) p :=
  MixedGrowthEvaluation.evaluator parts es hv x k (tables_rows parts es hv x k) E e he p hp

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

theorem observations_iff (parts : List Part) (es : List Entry) (hv : Valid parts es) (e : MExp) (he : e.FirstOrder)
    (x : List Char) (r : Option (List Char)) :
    SObs (source parts es) .callByValuePar e x r ↔ SObs (target parts es) .callByValueSeq (render parts es e) x r := by
  rw [← decideObsV_iff (source_firstOrder parts es hv) (by decide) he,
    ← decideObsV_iff (target_firstOrder parts es) (by decide) (render_firstOrder parts es e),decide_eq parts es hv e he x]

/-- A fixed grammar with n(n+1)+parts.length rules preserves the original input
language. No finite palette, alphabet restriction, or table oracle is supplied. -/
theorem language_translation (parts : List Part) (es : List Entry) (hv : Valid parts es) (e : MExp) (he : e.FirstOrder) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧
      ∀ x, SObs (source parts es) .callByValuePar e x (some []) ↔ SObs g .callByValueSeq start x (some []) :=
  ⟨target parts es,render parts es e,target_firstOrder parts es,render_firstOrder parts es e,
    fun x => observations_iff parts es hv e he x (some [])⟩


end Shallot.MacroPeg.CBV.MixedGrowthCorrespondence
