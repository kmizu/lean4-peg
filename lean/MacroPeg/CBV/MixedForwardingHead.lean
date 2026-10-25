import MacroPeg.CBV.MixedForwardingCalls

namespace Shallot.MacroPeg.CBV.MixedForwardingHead
open MixedForwardingCompiler
open ReplayControlFusion (Part Plan)
open MultiplyingPrefixCompiler (Spec arity view modes address render prefixCall origin_mode
  view_word view_value)
open RepeatedWordArguments (copies expression)
open GuardedReplayControl (Aligned)

/-- Preserve a committed choice frame after its head has been translated.
The caller's fallback still starts at its original entry position. -/
theorem frame_eq (parts : List Part) (es : List Entry) (hv : Valid parts es) (x : List Char) (k : Nat) (hRows : Rows parts es x k)
    (m : Nat) (hm : 1≤m) (v : List Char) (r : Spec) (htail : r.tail.FirstOrder) (hfall : r.fallback.FirstOrder)
    (A B : MExp) (p j : Nat) (h : Aligned x (copies v m) p j)
    (he : evV (source parts es) x .callByValuePar (sourceTable parts es x k) [copies v m] A p=
      evV (target parts es) x .callByValueSeq (targetTable parts es x k) (List.replicate (arity m) v) B j) :
    evV (source parts es) x .callByValuePar (sourceTable parts es x k) [copies v m]
      (ExpressionContext.plug A (ForwardingHeadExpansion.frame r)) p=
    evV (target parts es) x .callByValueSeq (targetTable parts es x k) (List.replicate (arity m) v)
      (.alt (.seq B (rebound parts es m r.tail)) (rebound parts es m r.fallback)) j := by
  have hf : evV (source parts es) x .callByValuePar (sourceTable parts es x k) [copies v m]
      (.seq (.param 0) r.fallback) p=
      evV (target parts es) x .callByValueSeq (targetTable parts es x k) (List.replicate (arity m) v) (rebound parts es m r.fallback) j := by
    rw [evV_seq_ok (GuardedReplayControl.aligned_replay (source parts es) x (copies v m) .callByValuePar
      (sourceTable parts es x k) p j h)]
    exact MixedForwardingEvaluation.view_evaluator parts es hv x k hRows m hm v r.fallback hfall j h.2.1
  have hb : evV (source parts es) x .callByValuePar (sourceTable parts es x k) [copies v m] (.seq A r.tail) p=
      evV (target parts es) x .callByValueSeq (targetTable parts es x k) (List.replicate (arity m) v)
        (.seq B (rebound parts es m r.tail)) j := by
    cases ha : evV (source parts es) x .callByValuePar (sourceTable parts es x k) [copies v m] A p with
    | none => rw [evV_seq_none ha,evV_seq_none (he.symm.trans ha)]
    | some a => cases a with
      | none => rw [evV_seq_fail ha,evV_seq_fail (he.symm.trans ha)]
      | some q =>
        rw [evV_seq_ok ha,evV_seq_ok (he.symm.trans ha)]
        exact MixedForwardingEvaluation.view_evaluator parts es hv x k hRows m hm v r.tail htail q
          (evV_ok (tblV_ok (source parts es) x .callByValuePar k) _ p h.1 q ha)
  cases ha : evV (source parts es) x .callByValuePar (sourceTable parts es x k) [copies v m] (.seq A r.tail) p with
  | none => simp only [ForwardingHeadExpansion.frame,ExpressionContext.plug,evV_alt_none ha,evV_alt_none (hb.symm.trans ha)]
  | some a => cases a with
    | none =>
      simp only [ForwardingHeadExpansion.frame,ExpressionContext.plug,evV_alt_fail ha,evV_alt_fail (hb.symm.trans ha)]
      exact hf
    | some q => simp only [ForwardingHeadExpansion.frame,ExpressionContext.plug,evV_alt_ok ha,evV_alt_ok (hb.symm.trans ha)]

theorem evaluator (parts : List Part) (es : List Entry) (hv : Valid parts es) (x : List Char) (k : Nat) (hRows : Rows parts es x k)
    (fuel i : Nat) (seen : List Nat) (hsel : i∈selected es) (hc : ForwardingHeadExpansion.complete (metadata es) fuel i seen=true)
    (m : Nat) (hm : 1≤m) (v : List Char) (p j : Nat) (h : Aligned x (copies v m) p j) :
    evV (source parts es) x .callByValuePar (sourceTable parts es x k) [copies v m]
      (ForwardingHeadExpansion.code (metadata es) fuel i seen) p=
    evV (target parts es) x .callByValueSeq (targetTable parts es x k) (List.replicate (arity m) v)
      (code parts es fuel i seen m) j := by
  induction fuel generalizing i seen with
  | zero => cases hc
  | succ fuel ih =>
    have hp0 := GuardedReplayControl.aligned_replay (source parts es) x (copies v m) .callByValuePar
      (sourceTable parts es x k) p j h
    by_cases hi : i∈seen
    · simp only [ForwardingHeadExpansion.code,code,if_pos hi]
      have hg := CallLookahead.evV_peek (source parts es) x .callByValuePar (sourceTable parts es x k) [copies v m] (.param 0) p
      simp only [hp0,CallLookahead.peek] at hg
      rw [ForwardingPrefixCycles.deadBody,evV_seq_ok hg]
      have hs : evV (source parts es) x .callByValuePar (sourceTable parts es x k) [copies v m] (.star (.lit [])) p=none := by
        rw [evV_star]
        exact evStar_stuck (j := p) (by simp [evV,Shallot.stripPrefix?,length_sfx x h.1]) (by omega)
      have ht : evV (target parts es) x .callByValueSeq (targetTable parts es x k) (List.replicate (arity m) v) (.star (.lit [])) j=none := by
        rw [evV_star]
        exact evStar_stuck (j := j) (by simp [evV,Shallot.stripPrefix?,length_sfx x h.2.1]) (by omega)
      rw [hs,ht]
    · cases hr : (metadata es)[i]? with
      | none => simp [ForwardingHeadExpansion.code,code,hi,hr,MExp.failAlways,evV]
      | some r =>
        obtain ⟨actual,ha⟩ := (selected_iff es i).mp hsel
        have har : actual=r := by simpa [metadata,ha] using hr
        subst actual
        have hvalid := hv.2 (.growth r) (List.mem_of_getElem? ha)
        by_cases hf : r.factor=1
        · cases hn : (metadata es)[r.callee]? with
          | none =>
            simp only [ForwardingHeadExpansion.code,code,if_neg hi,hr,if_pos hf,hn]
            have hcall : evV (source parts es) x .callByValuePar (sourceTable parts es x k) [copies v m]
                (.call r.callee [expression (.param 0) r.factor]) p=some none := by
              have hnone : es[r.callee]?=none := by
                cases he : es[r.callee]? <;> simp [metadata,he] at hn ⊢
              simp only [evV,source_rule,hnone,Option.map_none]
            rw [MultiplyingPrefixCompiler.sourceBody,evV_alt_fail (evV_seq_fail hcall),evV_seq_ok hp0]
            exact MixedForwardingEvaluation.view_evaluator parts es hv x k hRows m hm v r.fallback hvalid.2.2.1 j h.2.1
          | some child =>
            simp only [ForwardingHeadExpansion.complete,if_neg hi,hr,if_pos hf,hn] at hc
            have hchild := ih r.callee (i::seen) ((selected_valid parts es hv).edge i hsel r hr hf child hn) hc
            have hg := CallLookahead.evV_peek (source parts es) x .callByValuePar (sourceTable parts es x k) [copies v m] (.param 0) p
            simp only [hp0,CallLookahead.peek] at hg
            have he : evV (source parts es) x .callByValuePar (sourceTable parts es x k) [copies v m]
                (WordCallUnfolding.expanded (.param 0) (ForwardingHeadExpansion.code (metadata es) fuel r.callee (i::seen))) p=
                evV (target parts es) x .callByValueSeq (targetTable parts es x k) (List.replicate (arity m) v)
                  (code parts es fuel r.callee (i::seen) m) j := by
              rw [WordCallUnfolding.expanded,evV_seq_ok hg,
                WordViewSubstitution.evaluator (source parts es) x .callByValuePar (sourceTable parts es x k) [copies v m]
                  (.param 0) True.intro (copies v m) rfl _
                  (ForwardingHeadExpansion.code_firstOrder (metadata es) (metadata_firstOrder parts es hv) fuel r.callee (i::seen)) p]
              exact hchild
            simp only [ForwardingHeadExpansion.code,code,if_neg hi,hr,if_pos hf,hn]
            exact frame_eq parts es hv x k hRows m hm v r hvalid.2.1 hvalid.2.2.1 _ _ p j h he
        · have hfactor : 2≤r.factor := by have := hvalid.1; omega
          have he := MixedForwardingCalls.prefix_eq parts es hv x k hRows i r ha hfactor m hm v p j h
          simp only [ForwardingHeadExpansion.code,code,if_neg hi,hr,if_neg hf]
          exact frame_eq parts es hv x k hRows m hm v r hvalid.2.1 hvalid.2.2.1 _ _ p j h he

end Shallot.MacroPeg.CBV.MixedForwardingHead
