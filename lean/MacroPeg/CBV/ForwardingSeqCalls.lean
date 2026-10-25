import MacroPeg.CBV.ForwardingSeqEvaluation

namespace Shallot.MacroPeg.CBV.ForwardingSeqCalls
open ForwardingSeqCompiler
open MultiplyingPrefixCompiler (Spec arity view modes address render prefixCall origin_mode
  arity_positive view_word view_value render_firstOrder firstOrder_replicate)
open RepeatedWordArguments (copies expression)
open GuardedReplayControl (Aligned)

theorem prefix_eq (rs : List Spec) (x : List Char) (k : Nat) (hRows : Rows rs x k)
    (origin : Nat) (r : Spec) (hr : rs[origin]?=some r) (hfactor : 2≤r.factor) (m : Nat) (hm : 1≤m)
    (v : List Char) (p j : Nat) (h : Aligned x (copies v m) p j) :
    evV (source rs) x .callByValuePar (sourceTable rs x k) [copies v m]
      (.call r.callee [expression (.param 0) r.factor]) p=
    evV (target rs) x .callByValueSeq (targetTable rs x k) (List.replicate (arity m) v)
      (prefixCall rs origin m r) j := by
  have hf : r.factor=(r.factor-1)+1 := by omega
  have ha : arity r.factor=r.factor-1 := by unfold arity; rw [if_neg (by omega)]
  cases hc : rs[r.callee]? with
  | none =>
    have hn : ¬r.callee<rs.length := by have := List.getElem?_eq_none_iff.mp hc; omega
    simp [source_rule,prefixCall,hn,evV,MExp.failAlways]
  | some child =>
    have hci := (List.getElem?_eq_some_iff.mp hc).1
    have hs : ruleAtM (source rs).rules r.callee=some ⟨1,ForwardingHeadExpansion.expanded rs r.callee⟩ := by rw [source_rule,hc]; rfl
    have ht := target_rule rs (origin+1) r.factor r.callee child (origin_mode rs origin r hr) hc
    have hp0 := GuardedReplayControl.aligned_replay (source rs) x (copies v m) .callByValuePar
      (sourceTable rs x k) p j h
    have harg : evV (source rs) x .callByValuePar (sourceTable rs x k) [copies v m]
        (expression (.param 0) r.factor) p=
        evV (source rs) x .callByValuePar (sourceTable rs x k) [] (.lit (copies (copies v m) (r.factor-1))) j := by
      calc
        _ = evV (source rs) x .callByValuePar (sourceTable rs x k) [copies v m]
            (.seq (.param 0) (expression (.param 0) (r.factor-1))) p := by
          exact congrArg (fun n => evV (source rs) x .callByValuePar (sourceTable rs x k) [copies v m]
            (expression (.param 0) n) p) hf
        _ = _ := by
          rw [evV_seq_ok hp0,WordArguments.word_eval _ _ _ _ _ _
            (RepeatedWordArguments.expression_word (.param 0) True.intro _) j,
            RepeatedWordArguments.expression_value _ (.param 0) (copies v m) rfl]
          rfl
    have hargs := RepeatedWordArguments.sequential (target rs) x .callByValueSeq (targetTable rs x k)
      (List.replicate (arity m) v) (view m) (view_word m) (copies v m) (view_value m hm v) (r.factor-1) j h.2.1
    simp only [prefixCall,if_pos hci]
    rw [evV_call_par hs rfl (by decide),evV_call_seq ht (by simp only [List.length_replicate,ha])]
    simp only [evParArgs,harg,evV,hargs]
    cases hd : Shallot.stripPrefix? (copies (copies v m) (r.factor-1)) (sfx x j) with
    | none => rfl
    | some rest =>
      have hdelta := (CBVtoCBN.stripPrefix_exact _ _ _).mp hd
      have hwhole : sfx x p=copies (copies v m) r.factor++rest := by
        rw [h.2.2,hdelta]
        have hc : copies (copies v m) r.factor=copies v m++copies (copies v m) (r.factor-1) :=
          congrArg (copies (copies v m)) hf
        rw [hc,List.append_assoc]
      have hys := suffix_trans (sfx_is_suffix x j) ⟨copies (copies v m) (r.factor-1),hdelta⟩
      have hy : sfx x rest.length=rest := sfx_suffix hys.choose_spec
      have hq : rest.length≤x.length := by
        obtain ⟨u,hu⟩ := hys
        have hl := congrArg List.length hu
        simp only [List.length_append] at hl
        omega
      have hcap : pre x p rest.length=copies (copies v m) r.factor := by
        simpa only [length_sfx x h.1] using pre_eq (sfx_is_suffix x p) hwhole
      simp only [hcap]
      simpa only [ha] using hRows r.callee child hc (origin+1) r.factor (origin_mode rs origin r hr)
        (copies v m) p rest.length ⟨h.1,hq,by rw [hy]; exact hwhole⟩

end Shallot.MacroPeg.CBV.ForwardingSeqCalls
