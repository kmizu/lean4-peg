import MacroPeg.CBV.DoublingPrefixEvaluation

namespace Shallot.MacroPeg.CBV.DoublingPrefixCalls
open DoublingPrefixCompiler
open GuardedReplayControl (Aligned)

/-- The original doubled argument starts before the retained capture;
the target consumes only its second copy. The child keeps that copy and
interprets it as half of the child's source value. -/
theorem prefix_eq (rs : List Spec) (x : List Char) (k : Nat) (hRows : Rows rs x k)
    (i : Nat) (half : Bool) (v : List Char) (p j : Nat) (h : Aligned x (word half v) p j) :
    evV (source rs) x .callByValuePar (sourceTable rs x k) [word half v]
      (.call i [.seq (.param 0) (.param 0)]) p=
    evV (target rs) x .callByValueSeq (targetTable rs x k) [v]
      (.call (address rs true i) [view half]) j := by
  cases hr : rs[i]? with
  | none =>
    have hs : ruleAtM (source rs).rules i=none := by rw [source_rule,hr]; rfl
    simp only [evV,hs,target_missing rs i hr]
  | some r =>
    have hs : ruleAtM (source rs).rules i=some ⟨1,sourceBody r⟩ := by rw [source_rule,hr]; rfl
    have ht := target_rule rs true i r hr
    have hp0 := GuardedReplayControl.aligned_replay (source rs) x (word half v) .callByValuePar
      (sourceTable rs x k) p j h
    have harg : evV (source rs) x .callByValuePar (sourceTable rs x k) [word half v]
        (.seq (.param 0) (.param 0)) p=
        evV (source rs) x .callByValuePar (sourceTable rs x k) [word half v] (.param 0) j := evV_seq_ok hp0
    have hview : evV (target rs) x .callByValueSeq (targetTable rs x k) [v] (view half) j=
        evV (source rs) x .callByValuePar (sourceTable rs x k) [word half v] (.param 0) j := by
      rw [WordArguments.word_eval (target rs) x .callByValueSeq (targetTable rs x k) [v] (view half) (view_word half) j,
        view_value half v]
      rfl
    cases hm : Shallot.stripPrefix? (word half v) (sfx x j) with
    | none =>
      have hd : evV (source rs) x .callByValuePar (sourceTable rs x k) [word half v] (.param 0) j=some none := by
        simp only [evV,List.getElem?_cons_zero,hm]
      rw [evV_call_par hs rfl (by decide),evV_call_seq ht rfl]
      simp only [evParArgs,evSeqArgs,harg,hview,hd]
    | some y =>
      have hdelta : sfx x j=word half v++y := (CBVtoCBN.stripPrefix_exact _ _ _).mp hm
      have hwhole : sfx x p=(word half v++word half v)++y := by
        rw [h.2.2,hdelta,List.append_assoc]
      have hys : ∃ u, x=u++y := by
        obtain ⟨u,hu⟩ := sfx_is_suffix x j
        refine ⟨u++word half v,?_⟩
        rw [hu,hdelta,List.append_assoc]
      have hy : sfx x y.length=y := sfx_suffix hys.choose_spec
      have hq : y.length≤x.length := by
        obtain ⟨u,hu⟩ := hys
        have hl := congrArg List.length hu
        simp only [List.length_append] at hl
        omega
      have hcs : pre x p y.length=word half v++word half v := by
        simpa only [length_sfx x h.1] using pre_eq (sfx_is_suffix x p) hwhole
      have hct : pre x j y.length=word half v := by
        simpa only [length_sfx x h.2.1] using pre_eq (sfx_is_suffix x j) hdelta
      have hd : evV (source rs) x .callByValuePar (sourceTable rs x k) [word half v] (.param 0) j=some (some y.length) := by
        simp only [evV,List.getElem?_cons_zero,hm]
      rw [evV_call_par hs rfl (by decide),evV_call_seq ht rfl]
      simp only [evParArgs,evSeqArgs,harg,hview,hd,hcs,hct]
      exact hRows i r hr true (word half v) p y.length ⟨h.1,hq,by simpa only [word,if_true,hy] using hwhole⟩

end Shallot.MacroPeg.CBV.DoublingPrefixCalls
