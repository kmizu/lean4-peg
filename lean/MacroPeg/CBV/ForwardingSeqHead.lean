import MacroPeg.CBV.ForwardingSeqCalls

namespace Shallot.MacroPeg.CBV.ForwardingSeqHead
open ForwardingSeqCompiler
open MultiplyingPrefixCompiler (Spec arity view modes address render prefixCall origin_mode
  view_word view_value render_firstOrder)
open RepeatedWordArguments (copies expression)
open GuardedReplayControl (Aligned)

/-- Preserve a committed choice frame after its head has been translated.
The caller's fallback still starts at its original entry position. -/
theorem frame_eq (rs : List Spec) (hv : Valid rs) (x : List Char) (k : Nat) (hRows : Rows rs x k)
    (m : Nat) (hm : 1≤m) (v : List Char) (r : Spec) (htail : r.tail.FirstOrder) (hfall : r.fallback.FirstOrder)
    (A B : MExp) (p j : Nat) (h : Aligned x (copies v m) p j)
    (he : evV (source rs) x .callByValuePar (sourceTable rs x k) [copies v m] A p=
      evV (target rs) x .callByValueSeq (targetTable rs x k) (List.replicate (arity m) v) B j) :
    evV (source rs) x .callByValuePar (sourceTable rs x k) [copies v m]
      (ExpressionContext.plug A (ForwardingHeadExpansion.frame r)) p=
    evV (target rs) x .callByValueSeq (targetTable rs x k) (List.replicate (arity m) v)
      (.alt (.seq B (rebound rs m r.tail)) (rebound rs m r.fallback)) j := by
  have hf : evV (source rs) x .callByValuePar (sourceTable rs x k) [copies v m]
      (.seq (.param 0) r.fallback) p=
      evV (target rs) x .callByValueSeq (targetTable rs x k) (List.replicate (arity m) v) (rebound rs m r.fallback) j := by
    rw [evV_seq_ok (GuardedReplayControl.aligned_replay (source rs) x (copies v m) .callByValuePar
      (sourceTable rs x k) p j h)]
    exact ForwardingSeqEvaluation.view_evaluator rs hv x k hRows m hm v r.fallback hfall j h.2.1
  have hb : evV (source rs) x .callByValuePar (sourceTable rs x k) [copies v m] (.seq A r.tail) p=
      evV (target rs) x .callByValueSeq (targetTable rs x k) (List.replicate (arity m) v)
        (.seq B (rebound rs m r.tail)) j := by
    cases ha : evV (source rs) x .callByValuePar (sourceTable rs x k) [copies v m] A p with
    | none => rw [evV_seq_none ha,evV_seq_none (he.symm.trans ha)]
    | some a => cases a with
      | none => rw [evV_seq_fail ha,evV_seq_fail (he.symm.trans ha)]
      | some q =>
        rw [evV_seq_ok ha,evV_seq_ok (he.symm.trans ha)]
        exact ForwardingSeqEvaluation.view_evaluator rs hv x k hRows m hm v r.tail htail q
          (evV_ok (tblV_ok (source rs) x .callByValuePar k) _ p h.1 q ha)
  cases ha : evV (source rs) x .callByValuePar (sourceTable rs x k) [copies v m] (.seq A r.tail) p with
  | none => simp only [ForwardingHeadExpansion.frame,ExpressionContext.plug,evV_alt_none ha,evV_alt_none (hb.symm.trans ha)]
  | some a => cases a with
    | none =>
      simp only [ForwardingHeadExpansion.frame,ExpressionContext.plug,evV_alt_fail ha,evV_alt_fail (hb.symm.trans ha)]
      exact hf
    | some q => simp only [ForwardingHeadExpansion.frame,ExpressionContext.plug,evV_alt_ok ha,evV_alt_ok (hb.symm.trans ha)]

theorem evaluator (rs : List Spec) (hv : Valid rs) (x : List Char) (k : Nat) (hRows : Rows rs x k)
    (fuel i : Nat) (seen : List Nat) (hc : ForwardingHeadExpansion.complete rs fuel i seen=true)
    (m : Nat) (hm : 1≤m) (v : List Char) (p j : Nat) (h : Aligned x (copies v m) p j) :
    evV (source rs) x .callByValuePar (sourceTable rs x k) [copies v m]
      (ForwardingHeadExpansion.code rs fuel i seen) p=
    evV (target rs) x .callByValueSeq (targetTable rs x k) (List.replicate (arity m) v)
      (code rs fuel i seen m) j := by
  induction fuel generalizing i seen with
  | zero => cases hc
  | succ fuel ih =>
    have hp0 := GuardedReplayControl.aligned_replay (source rs) x (copies v m) .callByValuePar
      (sourceTable rs x k) p j h
    by_cases hi : i∈seen
    · simp only [ForwardingHeadExpansion.code,code,if_pos hi]
      have hg := CallLookahead.evV_peek (source rs) x .callByValuePar (sourceTable rs x k) [copies v m] (.param 0) p
      simp only [hp0,CallLookahead.peek] at hg
      rw [ForwardingPrefixCycles.deadBody,evV_seq_ok hg]
      have hs : evV (source rs) x .callByValuePar (sourceTable rs x k) [copies v m] (.star (.lit [])) p=none := by
        rw [evV_star]
        exact evStar_stuck (j := p) (by simp [evV,Shallot.stripPrefix?,length_sfx x h.1]) (by omega)
      have ht : evV (target rs) x .callByValueSeq (targetTable rs x k) (List.replicate (arity m) v) (.star (.lit [])) j=none := by
        rw [evV_star]
        exact evStar_stuck (j := j) (by simp [evV,Shallot.stripPrefix?,length_sfx x h.2.1]) (by omega)
      rw [hs,ht]
    · cases hr : rs[i]? with
      | none => simp [ForwardingHeadExpansion.code,code,hi,hr,MExp.failAlways,evV]
      | some r =>
        have hvalid := hv r (List.mem_of_getElem? hr)
        by_cases hf : r.factor=1
        · cases hn : rs[r.callee]? with
          | none =>
            simp only [ForwardingHeadExpansion.code,code,if_neg hi,hr,if_pos hf,hn]
            have hcall : evV (source rs) x .callByValuePar (sourceTable rs x k) [copies v m]
                (.call r.callee [expression (.param 0) r.factor]) p=some none := by
              simp only [evV,source_rule,hn,Option.map_none]
            rw [MultiplyingPrefixCompiler.sourceBody,evV_alt_fail (evV_seq_fail hcall),evV_seq_ok hp0]
            exact ForwardingSeqEvaluation.view_evaluator rs hv x k hRows m hm v r.fallback hvalid.2.2 j h.2.1
          | some child =>
            simp only [ForwardingHeadExpansion.complete,if_neg hi,hr,if_pos hf,hn] at hc
            have hchild := ih r.callee (i::seen) hc
            have hg := CallLookahead.evV_peek (source rs) x .callByValuePar (sourceTable rs x k) [copies v m] (.param 0) p
            simp only [hp0,CallLookahead.peek] at hg
            have he : evV (source rs) x .callByValuePar (sourceTable rs x k) [copies v m]
                (WordCallUnfolding.expanded (.param 0) (ForwardingHeadExpansion.code rs fuel r.callee (i::seen))) p=
                evV (target rs) x .callByValueSeq (targetTable rs x k) (List.replicate (arity m) v)
                  (code rs fuel r.callee (i::seen) m) j := by
              rw [WordCallUnfolding.expanded,evV_seq_ok hg,
                WordViewSubstitution.evaluator (source rs) x .callByValuePar (sourceTable rs x k) [copies v m]
                  (.param 0) True.intro (copies v m) rfl _
                  (ForwardingHeadExpansion.code_firstOrder rs (raw_firstOrder rs hv) fuel r.callee (i::seen)) p]
              exact hchild
            simp only [ForwardingHeadExpansion.code,code,if_neg hi,hr,if_pos hf,hn]
            exact frame_eq rs hv x k hRows m hm v r hvalid.2.1 hvalid.2.2 _ _ p j h he
        · have hfactor : 2≤r.factor := by have := hvalid.1; omega
          have he := ForwardingSeqCalls.prefix_eq rs x k hRows i r hr hfactor m hm v p j h
          simp only [ForwardingHeadExpansion.code,code,if_neg hi,hr,if_neg hf]
          exact frame_eq rs hv x k hRows m hm v r hvalid.2.1 hvalid.2.2 _ _ p j h he

end Shallot.MacroPeg.CBV.ForwardingSeqHead
