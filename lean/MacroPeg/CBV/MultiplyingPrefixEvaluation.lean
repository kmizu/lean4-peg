import MacroPeg.CBV.MultiplyingPrefixCompiler
import MacroPeg.CBV.DependentCaptureFilter
import MacroPeg.CBV.WordViewSubstitution

namespace Shallot.MacroPeg.CBV.MultiplyingPrefixEvaluation
open MultiplyingPrefixCompiler
open RepeatedWordArguments (copies expression)
open GuardedReplayControl (Aligned)

/-- Normal calls capture their complete actual arguments. Internal half
views are introduced only by the distinguished doubling-prefix call. -/
theorem evaluator (rs : List Spec) (hv : Valid rs) (x : List Char) (k : Nat) (hRows : Rows rs x k)
    (E : List (List Char)) : ∀ e, e.FirstOrder → ∀ p, p≤x.length →
    evV (source rs) x .callByValuePar (sourceTable rs x k) E e p=
      evV (target rs) x .callByValueSeq (targetTable rs x k) E (render rs.length e) p
  | .call i [a],h,p,hp => by
    cases hr : rs[i]? with
    | none =>
      have hn : ¬i<rs.length := by have := List.getElem?_eq_none_iff.mp hr; omega
      simp [render,hn,evV,source_rule,MExp.failAlways]
    | some r =>
      have hi := (List.getElem?_eq_some_iff.mp hr).1
      have hs : ruleAtM (source rs).rules i=some ⟨1,sourceBody r⟩ := by rw [source_rule,hr]; rfl
      have ht : ruleAtM (target rs).rules i=some ⟨1,targetBody rs i 1 r⟩ := by simpa [address,arity] using target_rule rs 0 1 i r rfl hr
      simp only [render,if_pos hi]
      rw [evV_call_par hs rfl (by decide),evV_call_seq ht rfl]
      have he := evaluator rs hv x k hRows E a h.1 p hp
      simp only [evParArgs,evSeqArgs,←he]
      cases ha : evV (source rs) x .callByValuePar (sourceTable rs x k) E a p with
      | none => rfl
      | some result => cases result with
        | none => rfl
        | some j =>
          obtain ⟨hj,hcap⟩ := DependentCaptureFilter.success_prefix (by decide)
            (tblV_sound (source_firstOrder rs hv) (by decide) k) E a h.1 p j hp ha
          have hc : Aligned x (copies (pre x p j) 1) p j := by
            exact ⟨hp,hj,by simpa only [copies,List.append_nil] using hcap⟩
          simpa [copies,arity,address] using hRows i r hr 0 1 rfl (pre x p j) p j hc
  | .call i [],_,p,_ | .call i (_::_::_),_,p,_ => by
    cases hr : rs[i]? <;> simp [render,evV,source_rule,hr,MExp.failAlways]
  | .seq a b,h,p,hp => by
    have he := evaluator rs hv x k hRows E a h.1 p hp
    cases ha : evV (source rs) x .callByValuePar (sourceTable rs x k) E a p with
    | none => simp only [render,evV_seq_none ha,evV_seq_none (he.symm.trans ha)]
    | some v => cases v with
      | none => simp only [render,evV_seq_fail ha,evV_seq_fail (he.symm.trans ha)]
      | some j =>
        simp only [render,evV_seq_ok ha,evV_seq_ok (he.symm.trans ha)]
        exact evaluator rs hv x k hRows E b h.2 j (evV_ok (tblV_ok (source rs) x .callByValuePar k) a p hp j ha)
  | .alt a b,h,p,hp => by
    have he := evaluator rs hv x k hRows E a h.1 p hp
    cases ha : evV (source rs) x .callByValuePar (sourceTable rs x k) E a p with
    | none => simp only [render,evV_alt_none ha,evV_alt_none (he.symm.trans ha)]
    | some v => cases v with
      | none =>
        simp only [render,evV_alt_fail ha,evV_alt_fail (he.symm.trans ha)]
        exact evaluator rs hv x k hRows E b h.2 p hp
      | some j => simp only [render,evV_alt_ok ha,evV_alt_ok (he.symm.trans ha)]
  | .notP a,h,p,hp => by
    simp only [render,evV,evaluator rs hv x k hRows E a h p hp]
  | .star a,h,p,hp => by
    simp only [render,evV_star]
    exact evStar_congr p (fun q hq => evaluator rs hv x k hRows E a h q (Nat.le_trans hq hp))
  | .eps,_,_,_ | .any,_,_,_ | .chr _,_,_,_ | .range _ _,_,_,_ | .lit _,_,_,_ | .param _,_,_,_ => rfl
  | .dbg _,h,_,_ | .lam _ _,h,_,_ | .callParam _ _,h,_,_ | .invoke _ _ _,h,_,_ => False.elim h

/-- Every later test and fresh call sees the complete source value. -/
theorem view_evaluator (rs : List Spec) (hv : Valid rs) (x : List Char) (k : Nat) (hRows : Rows rs x k)
    (m : Nat) (hm : 1≤m) (v : List Char) (e : MExp) (he : e.FirstOrder) (p : Nat) (hp : p≤x.length) :
    evV (source rs) x .callByValuePar (sourceTable rs x k) [copies v m] e p=
      evV (target rs) x .callByValueSeq (targetTable rs x k) (List.replicate (arity m) v)
        (MExp.subst [view m] (render rs.length e)) p := by
  rw [evaluator rs hv x k hRows [copies v m] e he p hp]
  exact (WordViewSubstitution.evaluator (target rs) x .callByValueSeq (targetTable rs x k)
    (List.replicate (arity m) v) (view m) (view_word m) (copies v m) (view_value m hm v)
    (render rs.length e) (render_firstOrder rs.length e) p).symm

end Shallot.MacroPeg.CBV.MultiplyingPrefixEvaluation
