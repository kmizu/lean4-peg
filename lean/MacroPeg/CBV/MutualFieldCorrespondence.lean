import MacroPeg.CBV.MutualFieldLayout

namespace Shallot.MacroPeg.CBV.MutualFieldCorrespondence
open MutualFieldSyntax
open DelimitedValueSafety (Environment)

def EarlierBodies (bodies : List MExp) (headers : List Header) (d : Char) (x : List Char) (k : Nat) : Prop :=
  ∀ m, m<k → ∀ (i : Nat) (s : Header), headers[i]?=some s → ∀ W : List (List Char), W.length=s.arity →
    Environment d W → ∀ p, p≤x.length →
    evV (source bodies headers d) x .callByValuePar (tblV (source bodies headers d) x .callByValuePar m) W s.body p=
      evV (target bodies headers d) x .callByValueSeq (tblV (target bodies headers d) x .callByValueSeq m) W
        (emit bodies.length headers d s.body) p

mutual
  theorem expression_of_bodies (bodies : List MExp) (headers : List Header) (d : Char)
      (hv : Valid bodies headers d) (x : List Char) (k : Nat)
      (hbody : EarlierBodies bodies headers d x k) :
      ∀ scope e, exprCheck bodies.length headers scope d e=true → ∀ E, Environment d E → ∀ p, p≤x.length →
      evV (source bodies headers d) x .callByValuePar (tblV (source bodies headers d) x .callByValuePar k) E e p=
        evV (target bodies headers d) x .callByValueSeq (tblV (target bodies headers d) x .callByValueSeq k) E
          (emit bodies.length headers d e) p
    | _,.eps,_,_,_,_,_ | _,.any,_,_,_,_,_ | _,.chr _,_,_,_,_,_ | _,.range _ _,_,_,_,_,_
    | _,.lit _,_,_,_,_,_ | _,.param _,_,_,_,_,_ => rfl
    | scope,.call i args,he,E,hE,p,hp => by
      by_cases hi : i<bodies.length
      · have ha : args=[] := of_decide_eq_true (by simpa only [exprCheck,if_pos hi] using he)
        subst args
        have hr := List.getElem?_eq_getElem hi
        have hrs : ruleAtM (source bodies headers d).rules i=some ⟨0,bodies[i]⟩ :=
          source_installed bodies headers d i bodies[i] hr
        have hrt : ruleAtM (target bodies headers d).rules i=some ⟨0,bodies[i]⟩ :=
          target_installed bodies headers d i bodies[i] hr
        rw [emit,if_pos hi,emitArgs,evV_call_par hrs rfl (by decide),evPar_nil,
          evV_call_seq hrt rfl,evSeq_nil]
        exact congrArg (fun row => valAt row p) (RecursiveParserStability.helper_rows_eq hv.library
          (source_installed bodies headers d) (target_installed bodies headers d) x _ _ k i hi [] [])
      · cases hs : headers[i-bodies.length]? with
        | none => simp [exprCheck,hi,hs] at he
        | some s =>
          have hh := Bool.and_eq_true_iff.mp (show
            (decide (args.length=s.arity) && argsCheck bodies.length headers scope d args)=true by
              simpa only [exprCheck,if_neg hi,hs] using he)
          have ha : args.length=s.arity := of_decide_eq_true hh.1
          have hvalid := hv.headers s (List.mem_of_getElem? hs)
          cases hpat : s.pattern with
          | nil => exact False.elim (hvalid.nonempty hpat)
          | cons j js =>
            simp only [emit,if_neg hi,hs]
            rw [hpat]
            rw [show TupleFieldTransfer.head (address bodies.length headers (i-bodies.length)) s.arity d (j::js)
                (emitArgs bodies.length headers d args)=
              TupleFieldTransfer.head (address bodies.length headers (i-bodies.length)) args.length d (j::js)
                (emitArgs bodies.length headers d args) by rw [ha]]
            have hsource : ruleAtM (source bodies headers d).rules i=
                some ⟨args.length,TupleFieldTransfer.sourceBody d (j::js) s.body⟩ := by
              simpa only [show bodies.length+(i-bodies.length)=i by omega,ha,hpat] using
                source_row bodies headers d (i-bodies.length) s hs
            have htarget : TupleFieldTransfer.Installed (target bodies headers d)
                (address bodies.length headers (i-bodies.length)) args.length d (j::js)
                (emit bodies.length headers d s.body) := by
              simpa only [ha,hpat] using target_rows bodies headers d (i-bodies.length) s hs
            apply TupleFieldTransfer.physical_at (source bodies headers d) (target bodies headers d)
              i (address bodies.length headers (i-bodies.length)) d j js s.body
              (emit bodies.length headers d s.body) (emit_firstOrder _ _ _ _)
              args (emitArgs bodies.length headers d args) (emitArgs_length _ _ _ _)
              (by rw [ha]; exact hvalid.positive)
              (by intro n hn; rw [ha]; exact hvalid.scope n (by simpa [hpat] using hn))
              (by intro n hn; simpa only [hpat] using hvalid.cover n (by omega))
              hsource htarget (source_firstOrder_grammar bodies headers d hv)
              (args_firstOrder _ _ _ _ args hh.2) x E k p hp
            · intro m hm W hlen hfree q hq
              apply hbody m hm (i-bodies.length) s hs W (by omega)
              · intro w hw
                obtain ⟨n,hn,heq⟩ := List.mem_iff_getElem.mp hw
                rw [←heq]
                exact hfree n hn
              · exact hq
            · intro n hn
              rw [emitArgs_get]
              exact arguments_physical bodies headers d hv x k hbody scope args hh.2 n hn E hE p hp
            · intro n hn q hq
              exact DelimitedValueSafety.captured_free d _ x .callByValuePar _ E hE args[n]
                (args_checked _ _ _ _ args hh.2 n hn).2 p q hp hq
    | scope,.seq a b,he,E,hE,p,hp => by
      have ha := expression_of_bodies bodies headers d hv x k hbody scope a (Bool.and_eq_true_iff.mp he).1 E hE p hp
      simp only [emit]
      cases heval : evV (source bodies headers d) x .callByValuePar (tblV (source bodies headers d) x .callByValuePar k) E a p with
      | none => rw [evV_seq_none heval,evV_seq_none (ha.symm.trans heval)]
      | some v => cases v with
        | none => rw [evV_seq_fail heval,evV_seq_fail (ha.symm.trans heval)]
        | some q =>
          rw [evV_seq_ok heval,evV_seq_ok (ha.symm.trans heval)]
          exact expression_of_bodies bodies headers d hv x k hbody scope b (Bool.and_eq_true_iff.mp he).2 E hE q
            (evV_ok (tblV_ok _ _ _ k) _ p hp q heval)
    | scope,.alt a b,he,E,hE,p,hp => by
      have ha := expression_of_bodies bodies headers d hv x k hbody scope a (Bool.and_eq_true_iff.mp he).1 E hE p hp
      simp only [emit]
      cases heval : evV (source bodies headers d) x .callByValuePar (tblV (source bodies headers d) x .callByValuePar k) E a p with
      | none => rw [evV_alt_none heval,evV_alt_none (ha.symm.trans heval)]
      | some v => cases v with
        | some q => rw [evV_alt_ok heval,evV_alt_ok (ha.symm.trans heval)]
        | none =>
          rw [evV_alt_fail heval,evV_alt_fail (ha.symm.trans heval)]
          exact expression_of_bodies bodies headers d hv x k hbody scope b (Bool.and_eq_true_iff.mp he).2 E hE p hp
    | scope,.notP a,he,E,hE,p,hp => by
      simp only [emit,evV,expression_of_bodies bodies headers d hv x k hbody scope a he E hE p hp]
    | scope,.star a,he,E,hE,p,hp => by
      rw [emit,evV_star,evV_star]
      exact evStar_congr p (fun q hq => expression_of_bodies bodies headers d hv x k hbody scope a he E hE q (by omega))
    | _,.dbg _,he,_,_,_,_ | _,.lam _ _,he,_,_,_,_ | _,.callParam _ _,he,_,_,_,_ | _,.invoke _ _ _,he,_,_,_,_ => by cases he

  theorem arguments_physical (bodies : List MExp) (headers : List Header) (d : Char)
      (hv : Valid bodies headers d) (x : List Char) (k : Nat)
      (hbody : EarlierBodies bodies headers d x k) (scope : Nat) :
      ∀ args, argsCheck bodies.length headers scope d args=true → ∀ i, (hi : i<args.length) →
      ∀ E, Environment d E → ∀ p, p≤x.length →
      evV (source bodies headers d) x .callByValuePar (tblV (source bodies headers d) x .callByValuePar k) E args[i] p=
        evV (target bodies headers d) x .callByValueSeq (tblV (target bodies headers d) x .callByValueSeq k) E
          (emit bodies.length headers d args[i]) p
    | [],_,i,hi,_,_,_,_ => by simp at hi
    | a::as,he,0,_,E,hE,p,hp => expression_of_bodies bodies headers d hv x k hbody scope a
        (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp he).1).1 E hE p hp
    | a::as,he,i+1,hi,E,hE,p,hp => arguments_physical bodies headers d hv x k hbody scope as
        (Bool.and_eq_true_iff.mp he).2 i (by simpa using hi) E hE p hp
end

/-- A single physical-table induction handles every mutually recursive
header, including new tuples, differing arities, and return to the parent. -/
theorem physical (bodies : List MExp) (headers : List Header) (d : Char)
    (hv : Valid bodies headers d) (x : List Char) (k : Nat) :
    ∀ scope e, exprCheck bodies.length headers scope d e=true → ∀ E, Environment d E → ∀ p, p≤x.length →
    evV (source bodies headers d) x .callByValuePar (tblV (source bodies headers d) x .callByValuePar k) E e p=
      evV (target bodies headers d) x .callByValueSeq (tblV (target bodies headers d) x .callByValueSeq k) E
        (emit bodies.length headers d e) p := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    apply expression_of_bodies bodies headers d hv x k
    intro m hm i s hs W hlen hfree p hp
    exact ih m hm s.arity s.body (hv.headers s (List.mem_of_getElem? hs)).body W hfree p hp

end Shallot.MacroPeg.CBV.MutualFieldCorrespondence
