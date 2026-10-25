import MacroPeg.CBV.EmptyArgumentSpecialization

namespace Shallot.MacroPeg.CBV.EmptyArgumentEvaluation
open EmptyArgumentSpecialization

theorem sequential_bound (g : MGrammar) (x : List Char) (s : Strategy) (k : Nat) (E : List (List Char))
    (args : List MExp) (p : Nat) (hp : p≤x.length) (W : List (List Char)) (q : Nat)
    (h : evSeqArgs g x s (sourceTable g x s k) E args p=some (some (W,q))) : q≤x.length := by
  induction args generalizing p W q with
  | nil => simp only [evSeqArgs,Option.some.injEq,Prod.mk.injEq] at h; omega
  | cons a args ih =>
    cases ha : evV g x s (sourceTable g x s k) E a p with
    | none => simp only [evSeqArgs,ha] at h; cases h
    | some v => cases v with
      | none => simp only [evSeqArgs,ha] at h; cases h
      | some j =>
        have hj := evV_ok (tblV_ok g x s k) a p hp j ha
        cases ht : evSeqArgs g x s (sourceTable g x s k) E args j with
        | none => simp only [evSeqArgs,ha,ht] at h; cases h
        | some v => cases v with
          | none => simp only [evSeqArgs,ha,ht] at h; cases h
          | some v =>
            simp only [evSeqArgs,ha,ht,Option.some.injEq,Prod.mk.injEq] at h
            exact h.2 ▸ ih j hj v.1 v.2 ht

theorem ordinary_call (g : MGrammar) (x : List Char) (s : Strategy) (k : Nat) (hRows : Rows g x s k)
    (i : Nat) (r : MRule) (hr : ruleAtM g.rules i=some r) (args : List MExp) (E : List (List Char))
    (p : Nat) (hp : p≤x.length)
    (hpar : evParArgs g x s (sourceTable g x s k) E args p=
      evParArgs (target g) x s (targetTable g x s k) E (arguments g args) p)
    (hseq : evSeqArgs g x s (sourceTable g x s k) E args p=
      evSeqArgs (target g) x s (targetTable g x s k) E (arguments g args) p) :
    evV g x s (sourceTable g x s k) E (.call i args) p=
      evV (target g) x s (targetTable g x s k) E (.call i (arguments g args)) p := by
  have ht := original_rule g i r hr
  by_cases ha : r.arity=args.length
  · have hb : r.arity=(arguments g args).length := by rw [arguments_length]; exact ha
    by_cases hs : s=.callByValueSeq
    · subst s
      rw [evV_call_seq hr ha,evV_call_seq ht hb,←hseq]
      cases hv : evSeqArgs g x .callByValueSeq (sourceTable g x .callByValueSeq k) E args p with
      | none => rfl
      | some v => cases v with
        | none => rfl
        | some v => exact hRows.1 i r hr v.1 v.2 (sequential_bound g x .callByValueSeq k E args p hp v.1 v.2 hv)
    · rw [evV_call_par hr ha hs,evV_call_par ht hb hs,←hpar]
      cases evParArgs g x s (sourceTable g x s k) E args p with
      | none => rfl
      | some v => cases v with
        | none => rfl
        | some W => exact hRows.1 i r hr W p hp
  · simp only [evV,hr,ht,arguments_length,if_neg ha]

theorem zero_call (g : MGrammar) (x : List Char) (s : Strategy) (k : Nat) (hRows : Rows g x s k)
    (i : Nat) (r : MRule) (hr : ruleAtM g.rules i=some r) (ha : r.arity=1) (A : MExp) (he : zeroCheck A=true)
    (E : List (List Char)) (p : Nat) (hp : p≤x.length)
    (harg : evV g x s (sourceTable g x s k) E A p=
      evV (target g) x s (targetTable g x s k) E (render g A) p) :
    evV g x s (sourceTable g x s k) E (.call i [A]) p=
      evV (target g) x s (targetTable g x s k) E (.seq (render g A) (.call (g.rules.length+i) [])) p := by
  have ht := clone_rule g i r hr
  by_cases hs : s=.callByValueSeq
  · subst s
    rw [evV_call_seq hr (by simpa using ha)]
    cases hv : evV g x .callByValueSeq (sourceTable g x .callByValueSeq k) E A p with
    | none => simp only [evSeqArgs,hv,evV_seq_none (harg.symm.trans hv)]
    | some v => cases v with
      | none => simp only [evSeqArgs,hv,evV_seq_fail (harg.symm.trans hv)]
      | some q =>
        have hq := zero_success g x .callByValueSeq (sourceTable g x .callByValueSeq k) E A he p q hp hv
        subst q
        rw [evV_seq_ok (harg.symm.trans hv),evV_call_seq ht rfl]
        simp only [evSeqArgs,hv,pre,Nat.sub_self,List.take_zero]
        exact hRows.2 i r hr [] p hp
  · rw [evV_call_par hr (by simpa using ha) hs]
    cases hv : evV g x s (sourceTable g x s k) E A p with
    | none => simp only [evParArgs,hv,evV_seq_none (harg.symm.trans hv)]
    | some v => cases v with
      | none => simp only [evParArgs,hv,evV_seq_fail (harg.symm.trans hv)]
      | some q =>
        have hq := zero_success g x s (sourceTable g x s k) E A he p q hp hv
        subst q
        rw [evV_seq_ok (harg.symm.trans hv),evV_call_par ht rfl hs]
        simp only [evParArgs,hv,pre,Nat.sub_self,List.take_zero]
        exact hRows.2 i r hr [] p hp

mutual
  theorem evaluator (g : MGrammar) (x : List Char) (s : Strategy) (k : Nat) (hRows : Rows g x s k)
      (E : List (List Char)) : ∀ e, e.FirstOrder → ∀ p, p≤x.length →
      evV g x s (sourceTable g x s k) E e p=evV (target g) x s (targetTable g x s k) E (render g e) p
    | .call i [a],h,p,hp => by
      cases hr : ruleAtM g.rules i with
      | none => simp [render,evV,hr,MExp.failAlways]
      | some r =>
        by_cases he : r.arity=1 ∧ zeroCheck a=true
        · simp only [render,hr,if_pos he]
          exact zero_call g x s k hRows i r hr he.1 a he.2 E p hp (evaluator g x s k hRows E a h.1 p hp)
        · simpa only [render,hr,if_neg he,arguments] using ordinary_call g x s k hRows i r hr [a] E p hp
            (parallel g x s k hRows E [a] h p hp) (sequential g x s k hRows E [a] h p hp)
    | .call i [],h,p,hp => by
      cases hr : ruleAtM g.rules i with
      | none => simp [render,evV,hr,MExp.failAlways]
      | some r =>
        simpa only [render,hr] using (ordinary_call g x s k hRows i r hr [] E p hp
          (parallel g x s k hRows E [] h p hp) (sequential g x s k hRows E [] h p hp))
    | .call i (a::b::args),h,p,hp => by
      cases hr : ruleAtM g.rules i with
      | none => simp [render,evV,hr,MExp.failAlways]
      | some r =>
        simpa only [render,hr] using (ordinary_call g x s k hRows i r hr (a::b::args) E p hp
          (parallel g x s k hRows E (a::b::args) h p hp) (sequential g x s k hRows E (a::b::args) h p hp))
    | .seq a b,h,p,hp => by
      have he := evaluator g x s k hRows E a h.1 p hp
      cases ha : evV g x s (sourceTable g x s k) E a p with
      | none => simp only [render,evV_seq_none ha,evV_seq_none (he.symm.trans ha)]
      | some v => cases v with
        | none => simp only [render,evV_seq_fail ha,evV_seq_fail (he.symm.trans ha)]
        | some j =>
          simp only [render,evV_seq_ok ha,evV_seq_ok (he.symm.trans ha)]
          exact evaluator g x s k hRows E b h.2 j (evV_ok (tblV_ok g x s k) a p hp j ha)
    | .alt a b,h,p,hp => by
      have he := evaluator g x s k hRows E a h.1 p hp
      cases ha : evV g x s (sourceTable g x s k) E a p with
      | none => simp only [render,evV_alt_none ha,evV_alt_none (he.symm.trans ha)]
      | some v => cases v with
        | none =>
          simp only [render,evV_alt_fail ha,evV_alt_fail (he.symm.trans ha)]
          exact evaluator g x s k hRows E b h.2 p hp
        | some j => simp only [render,evV_alt_ok ha,evV_alt_ok (he.symm.trans ha)]
    | .notP a,h,p,hp => by simp only [render,evV,evaluator g x s k hRows E a h p hp]
    | .star a,h,p,hp => by
      simp only [render,evV_star]
      exact evStar_congr p (fun q hq => evaluator g x s k hRows E a h q (Nat.le_trans hq hp))
    | .eps,_,_,_ | .any,_,_,_ | .chr _,_,_,_ | .range _ _,_,_,_ | .lit _,_,_,_ | .param _,_,_,_ => rfl
    | .dbg _,h,_,_ | .lam _ _,h,_,_ | .callParam _ _,h,_,_ | .invoke _ _ _,h,_,_ => False.elim h
  termination_by e => sizeOf e
  decreasing_by all_goals simp_wf; all_goals omega

  theorem parallel (g : MGrammar) (x : List Char) (s : Strategy) (k : Nat) (hRows : Rows g x s k)
      (E : List (List Char)) : ∀ args, MExp.FirstOrderArgs args → ∀ p, p≤x.length →
      evParArgs g x s (sourceTable g x s k) E args p=
        evParArgs (target g) x s (targetTable g x s k) E (arguments g args) p
    | [],_,_,_ => rfl
    | a::args,h,p,hp => by
      simp only [arguments,evParArgs,evaluator g x s k hRows E a h.1 p hp,parallel g x s k hRows E args h.2 p hp]
  termination_by args => sizeOf args
  decreasing_by all_goals simp_wf; all_goals omega

  theorem sequential (g : MGrammar) (x : List Char) (s : Strategy) (k : Nat) (hRows : Rows g x s k)
      (E : List (List Char)) : ∀ args, MExp.FirstOrderArgs args → ∀ p, p≤x.length →
      evSeqArgs g x s (sourceTable g x s k) E args p=
        evSeqArgs (target g) x s (targetTable g x s k) E (arguments g args) p
    | [],_,_,_ => rfl
    | a::args,h,p,hp => by
      have he := evaluator g x s k hRows E a h.1 p hp
      cases ha : evV g x s (sourceTable g x s k) E a p with
      | none => simp only [arguments,evSeqArgs,←he,ha]
      | some v => cases v with
        | none => simp only [arguments,evSeqArgs,←he,ha]
        | some j =>
          simp only [arguments,evSeqArgs,←he,ha]
          exact congrArg (fun tail => match tail with
            | some (some (W,q)) => some (some (pre x p j::W,q)) | other => other)
            (sequential g x s k hRows E args h.2 j (evV_ok (tblV_ok g x s k) a p hp j ha))
  termination_by args => sizeOf args
  decreasing_by all_goals simp_wf; all_goals omega
end

end Shallot.MacroPeg.CBV.EmptyArgumentEvaluation
