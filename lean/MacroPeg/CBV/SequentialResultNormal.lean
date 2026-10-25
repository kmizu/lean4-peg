import MacroPeg.CBV.SequentialResultSyntax

namespace Shallot.MacroPeg.CBV.SequentialResultNormal
open SequentialResultSyntax
open EmptyResultObservation (project)
open ClockFreezing (Table)

structure Rows (g : MGrammar) (x : List Char) (T U : Table) : Prop where
  normal : ∀ i r, ruleAtM g.rules i=some r → ∀ W p, p≤x.length →
    valAt (U (2*i) W) p=valAt (T i W) p
  zero : ∀ i r, ruleAtM g.rules i=some r → ∀ p, p≤x.length →
    valAt (U (2*i+1) []) p=project p (valAt (T i (List.replicate r.arity [])) p)

mutual
  theorem normal_eval (g : MGrammar) (x : List Char) (T U : Table)
      (rows : Rows g x T U) (ht : OkTV x.length T) (hd : SequentialClock.Descending T) (E : List (List Char)) :
      ∀ e, e.FirstOrder → ∀ p, p≤x.length →
      evV (target g) x .callByValueSeq U E (normal e) p=evV g x .callByValueSeq T E e p
    | .call i args,he,p,hp => by
      have hr := target_rule g i false
      simp only [Bool.false_eq_true,if_false,Nat.add_zero] at hr
      simp only [normal]
      cases hs : ruleAtM g.rules i with
      | none => simp only [hs,Option.map_none] at hr; simp only [evV,hr,hs]
      | some r =>
        simp only [hs,Option.map_some] at hr
        by_cases ha : r.arity=args.length
        · rw [evV_call_seq hr (by simp only [normalArgs_length,ha]),evV_call_seq hs ha,
            arguments_eval g x T U rows ht hd E args he p hp]
          cases hv : evSeqArgs g x .callByValueSeq T E args p with
          | none => rfl
          | some v => cases v with
            | none => rfl
            | some pair =>
              obtain ⟨W,q⟩ := pair
              exact rows.normal i r hs W q (Nat.le_trans (SequentialClock.arguments_metadata hd E args p W q hv).1 hp)
        · have ha' : r.arity≠(normalArgs args).length := by simpa only [normalArgs_length] using ha
          simp only [evV,hr,hs,if_neg ha,if_neg ha']
    | .seq a b,he,p,hp => by
      have ha := normal_eval g x T U rows ht hd E a he.1 p hp
      simp only [normal]
      cases hv : evV g x .callByValueSeq T E a p with
      | none => rw [evV_seq_none hv,evV_seq_none (ha.trans hv)]
      | some v => cases v with
        | none => rw [evV_seq_fail hv,evV_seq_fail (ha.trans hv)]
        | some q =>
          rw [evV_seq_ok hv,evV_seq_ok (ha.trans hv)]
          exact normal_eval g x T U rows ht hd E b he.2 q (evV_ok ht a p hp q hv)
    | .alt a b,he,p,hp => by
      have ha := normal_eval g x T U rows ht hd E a he.1 p hp
      simp only [normal]
      cases hv : evV g x .callByValueSeq T E a p with
      | none => rw [evV_alt_none hv,evV_alt_none (ha.trans hv)]
      | some v => cases v with
        | none =>
          rw [evV_alt_fail hv,evV_alt_fail (ha.trans hv)]
          exact normal_eval g x T U rows ht hd E b he.2 p hp
        | some q => rw [evV_alt_ok hv,evV_alt_ok (ha.trans hv)]
    | .notP a,he,p,hp => by simp only [normal,evV,normal_eval g x T U rows ht hd E a he p hp]
    | .star a,he,p,hp => by
      rw [normal,evV_star,evV_star]
      exact evStar_congr p (fun q hq => normal_eval g x T U rows ht hd E a he q (by omega))
    | .eps,_,_,_ | .any,_,_,_ | .chr _,_,_,_ | .range _ _,_,_,_ | .lit _,_,_,_ | .param _,_,_,_ => rfl
    | .dbg _,he,_,_ | .lam _ _,he,_,_ | .callParam _ _,he,_,_ | .invoke _ _ _,he,_,_ => False.elim he

  theorem arguments_eval (g : MGrammar) (x : List Char) (T U : Table)
      (rows : Rows g x T U) (ht : OkTV x.length T) (hd : SequentialClock.Descending T) (E : List (List Char)) :
      ∀ args, MExp.FirstOrderArgs args → ∀ p, p≤x.length →
      evSeqArgs (target g) x .callByValueSeq U E (normalArgs args) p=evSeqArgs g x .callByValueSeq T E args p
    | [],_,_,_ => rfl
    | a::args,he,p,hp => by
      have ha := normal_eval g x T U rows ht hd E a he.1 p hp
      simp only [normalArgs]
      cases hv : evV g x .callByValueSeq T E a p with
      | none => rw [evSeq_cons_none hv,evSeq_cons_none (ha.trans hv)]
      | some v => cases v with
        | none => rw [evSeq_cons_fail hv,evSeq_cons_fail (ha.trans hv)]
        | some q => rw [evSeq_cons_ok hv,evSeq_cons_ok (ha.trans hv),
            arguments_eval g x T U rows ht hd E args he.2 q (evV_ok ht a p hp q hv)]
end

end Shallot.MacroPeg.CBV.SequentialResultNormal
