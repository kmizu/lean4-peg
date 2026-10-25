import MacroPeg.CBV.MixedForwardingCompiler

namespace Shallot.MacroPeg.CBV.MixedForwardingEvaluation
open MixedForwardingCompiler
open MultiplyingPrefixCompiler (arity view view_word view_value)
open ReplayControlFusion (Part Plan)
open RepeatedWordArguments (copies expression)
open GuardedReplayControl (Aligned)

theorem leaf_eval (parts : List Part) (es : List Entry) (x : List Char) (k : Nat)
    (E : List (List Char)) (a : MExp) (p q : Nat)
    (ha : evV (target parts es) x .callByValueSeq (targetTable parts es x k) E a p=some (some q)) (i : Nat) :
    evV (target parts es) x .callByValueSeq (targetTable parts es x k) E (leaf parts es a i) p=
      leafRows parts es (targetTable parts es x k) (pre x p q) p q i := by
  unfold leaf leafRows
  cases hr : parts[i]? with
  | none => simp [MExp.failAlways,evV]
  | some r =>
    have ht : ruleAtM (target parts es).rules (offset es+i)=some (helper parts es r) := by rw [helper_rule,hr]; rfl
    dsimp only []
    cases hb : r.replay
    · simp only [Bool.false_eq_true,if_false]
      rw [evV_call_seq ht (by simp [helper,hb])]
      rfl
    · simp only [if_true]
      rw [evV_call_seq ht (by simp [helper,hb]),evSeq_cons_ok ha]
      rfl

theorem evaluator (parts : List Part) (es : List Entry) (hv : Valid parts es) (x : List Char) (k : Nat) (hRows : Rows parts es x k)
    (E : List (List Char)) : ∀ e, e.FirstOrder → ∀ p, p≤x.length →
    evV (source parts es) x .callByValuePar (sourceTable parts es x k) E e p=
      evV (target parts es) x .callByValueSeq (targetTable parts es x k) E (render parts es e) p
  | .call i [a],h,p,hp => by
    cases hr : es[i]? with
    | none =>
      have hn : ¬i<es.length := by have := List.getElem?_eq_none_iff.mp hr; omega
      simp [render,hr,evV,source_rule,MExp.failAlways]
    | some e => cases e with
      | growth r =>
        have hi := (List.getElem?_eq_some_iff.mp hr).1
        have hs : ruleAtM (source parts es).rules i=some ⟨1,ForwardingHeadExpansion.expanded (metadata es) i⟩ := by rw [source_rule,hr]; rfl
        have ht : ruleAtM (target parts es).rules i=some ⟨1,targetBody parts es i 1 r⟩ := by simpa [address,arity] using target_rule parts es 0 1 i r rfl hr
        simp only [render,hr]
        rw [evV_call_par hs rfl (by decide),evV_call_seq ht rfl]
        have he := evaluator parts es hv x k hRows E a h.1 p hp
        simp only [evParArgs,evSeqArgs,←he]
        cases ha : evV (source parts es) x .callByValuePar (sourceTable parts es x k) E a p with
        | none => rfl
        | some result => cases result with
          | none => rfl
          | some j =>
            obtain ⟨hj,hcap⟩ := DependentCaptureFilter.success_prefix (by decide)
              (tblV_sound (source_firstOrder parts es hv) (by decide) k) E a h.1 p j hp ha
            have hc : Aligned x (copies (pre x p j) 1) p j := by
              exact ⟨hp,hj,by simpa only [copies,List.append_nil] using hcap⟩
            simpa [copies,arity,address] using hRows.1 i r hr 0 1 rfl (pre x p j) p j hc
      | origin P =>
        have hs : ruleAtM (source parts es).rules i=some ⟨1,P.exp (ReplayControlFusion.sourceLeaf parts)⟩ := by rw [source_rule,hr]; rfl
        simp only [render,hr]
        rw [evV_call_par hs rfl (by decide)]
        have heq := evaluator parts es hv x k hRows E a h.1 p hp
        have hguard : evV (target parts es) x .callByValueSeq (targetTable parts es x k) E (.andP (render parts es a)) p=
            CallLookahead.peek p (evV (source parts es) x .callByValuePar (sourceTable parts es x k) E a p) := by
          rw [CallLookahead.evV_peek,←heq]
        cases ha : evV (source parts es) x .callByValuePar (sourceTable parts es x k) E a p with
        | none => rw [evPar_cons_none ha,evV_seq_none (hguard.trans (by rw [ha]; rfl))]
        | some result => cases result with
          | none => rw [evPar_cons_fail ha,evV_seq_fail (hguard.trans (by rw [ha]; rfl))]
          | some q =>
            rw [evPar_cons_ok ha,evV_seq_ok (hguard.trans (by rw [ha]; rfl)),Plan.exp_eval]
            have hl : (fun j => evV (target parts es) x .callByValueSeq (targetTable parts es x k) E
                (leaf parts es (render parts es a) j) p)=leafRows parts es (targetTable parts es x k) (pre x p q) p q := by
              funext j
              exact leaf_eval parts es x k E _ p q (heq.symm.trans ha) j
            rw [hl]
            obtain ⟨hq,hs⟩ := ReplayFusion.success_prefix (tblV_sound (source_firstOrder parts es hv) (by decide) k) E a h.1 p q hp ha
            exact hRows.2 i P hr (pre x p q) p q ⟨hp,hq,hs⟩
  | .call i [],_,p,_ | .call i (_::_::_),_,p,_ => by
    cases hr : es[i]? with
    | none => simp [render,evV,source_rule,hr,MExp.failAlways]
    | some e => cases e <;> simp [render,evV,source_rule,hr,MExp.failAlways]
  | .seq a b,h,p,hp => by
    have he := evaluator parts es hv x k hRows E a h.1 p hp
    cases ha : evV (source parts es) x .callByValuePar (sourceTable parts es x k) E a p with
    | none => simp only [render,evV_seq_none ha,evV_seq_none (he.symm.trans ha)]
    | some v => cases v with
      | none => simp only [render,evV_seq_fail ha,evV_seq_fail (he.symm.trans ha)]
      | some j =>
        simp only [render,evV_seq_ok ha,evV_seq_ok (he.symm.trans ha)]
        exact evaluator parts es hv x k hRows E b h.2 j (evV_ok (tblV_ok (source parts es) x .callByValuePar k) a p hp j ha)
  | .alt a b,h,p,hp => by
    have he := evaluator parts es hv x k hRows E a h.1 p hp
    cases ha : evV (source parts es) x .callByValuePar (sourceTable parts es x k) E a p with
    | none => simp only [render,evV_alt_none ha,evV_alt_none (he.symm.trans ha)]
    | some v => cases v with
      | none =>
        simp only [render,evV_alt_fail ha,evV_alt_fail (he.symm.trans ha)]
        exact evaluator parts es hv x k hRows E b h.2 p hp
      | some j => simp only [render,evV_alt_ok ha,evV_alt_ok (he.symm.trans ha)]
  | .notP a,h,p,hp => by
    simp only [render,evV,evaluator parts es hv x k hRows E a h p hp]
  | .star a,h,p,hp => by
    simp only [render,evV_star]
    exact evStar_congr p (fun q hq => evaluator parts es hv x k hRows E a h q (Nat.le_trans hq hp))
  | .eps,_,_,_ | .any,_,_,_ | .chr _,_,_,_ | .range _ _,_,_,_ | .lit _,_,_,_ | .param _,_,_,_ => rfl
  | .dbg _,h,_,_ | .lam _ _,h,_,_ | .callParam _ _,h,_,_ | .invoke _ _ _,h,_,_ => False.elim h

theorem view_evaluator (parts : List Part) (es : List Entry) (hv : Valid parts es) (x : List Char) (k : Nat) (hRows : Rows parts es x k)
    (m : Nat) (hm : 1≤m) (v : List Char) (e : MExp) (he : e.FirstOrder) (p : Nat) (hp : p≤x.length) :
    evV (source parts es) x .callByValuePar (sourceTable parts es x k) [copies v m] e p=
      evV (target parts es) x .callByValueSeq (targetTable parts es x k) (List.replicate (arity m) v)
        (MExp.subst [view m] (render parts es e)) p := by
  rw [evaluator parts es hv x k hRows [copies v m] e he p hp]
  exact (WordViewSubstitution.evaluator (target parts es) x .callByValueSeq (targetTable parts es x k)
    (List.replicate (arity m) v) (view m) (view_word m) (copies v m) (view_value m hm v)
    (render parts es e) (render_firstOrder parts es e) p).symm


end Shallot.MacroPeg.CBV.MixedForwardingEvaluation
