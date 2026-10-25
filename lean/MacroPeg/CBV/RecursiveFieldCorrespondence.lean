import MacroPeg.CBV.RecursiveFieldSyntax

namespace Shallot.MacroPeg.CBV.RecursiveFieldCorrespondence
open RecursiveFieldSyntax
open DelimitedValueSafety (Environment)

mutual
  theorem expression_of_body (bodies : List MExp) (arity : Nat) (d : Char) (j : Nat) (js : List Nat) (body : MExp)
      (hb : RecursiveParserStability.Valid bodies) (hn : 0<arity)
      (hs : ∀ i∈j::js, i<arity) (cover : ∀ i, i<arity → i∈j::js)
      (hc : exprCheck bodies.length arity arity d body=true)
      (x : List Char) (k : Nat)
      (hbody : ∀ m, m<k → ∀ W : List (List Char), W.length=arity → Environment d W → ∀ q, q≤x.length →
        evV (source bodies arity d (j::js) body) x .callByValuePar
          (tblV (source bodies arity d (j::js) body) x .callByValuePar m) W body q=
        evV (target bodies arity d (j::js) body) x .callByValueSeq
          (tblV (target bodies arity d (j::js) body) x .callByValueSeq m) W (emit bodies.length arity d (j::js) body) q) :
      ∀ scope e, exprCheck bodies.length arity scope d e=true → ∀ E, Environment d E → ∀ p, p≤x.length →
      evV (source bodies arity d (j::js) body) x .callByValuePar
        (tblV (source bodies arity d (j::js) body) x .callByValuePar k) E e p=
      evV (target bodies arity d (j::js) body) x .callByValueSeq
        (tblV (target bodies arity d (j::js) body) x .callByValueSeq k) E (emit bodies.length arity d (j::js) e) p
    | _,.eps,_,_,_,_,_ | _,.any,_,_,_,_,_ | _,.chr _,_,_,_,_,_ | _,.range _ _,_,_,_,_,_
    | _,.lit _,_,_,_,_,_ | _,.param _,_,_,_,_,_ => rfl
    | scope,.call i args,he,E,hE,p,hp => by
      by_cases hi : i<bodies.length
      · have ha : args=[] := of_decide_eq_true (by simpa only [exprCheck,if_pos hi] using he)
        subst args
        have hne : i≠bodies.length := by omega
        have hr := List.getElem?_eq_getElem hi
        have hrs : ruleAtM (source bodies arity d (j::js) body).rules i=some ⟨0,bodies[i]⟩ :=
          TupleFieldCompiler.source_installed bodies arity d (j::js) body i bodies[i] hr
        have hrt : ruleAtM (target bodies arity d (j::js) body).rules i=some ⟨0,bodies[i]⟩ :=
          TupleFieldCompiler.target_installed bodies arity d (j::js) _ i bodies[i] hr
        rw [emit,if_neg hne,emitArgs,evV_call_par hrs rfl (by decide),evPar_nil,
          evV_call_seq hrt rfl,evSeq_nil]
        exact congrArg (fun row => valAt row p) (RecursiveParserStability.helper_rows_eq hb
          (TupleFieldCompiler.source_installed bodies arity d (j::js) body)
          (TupleFieldCompiler.target_installed bodies arity d (j::js) _) x _ _ k i hi [] [])
      · have hh := Bool.and_eq_true_iff.mp (show
            ((decide (i=bodies.length) && decide (args.length=arity)) && argsCheck bodies.length arity scope d args)=true from
              by simpa only [exprCheck,if_neg hi] using he)
        have heq : i=bodies.length := of_decide_eq_true (Bool.and_eq_true_iff.mp hh.1).1
        have ha : args.length=arity := of_decide_eq_true (Bool.and_eq_true_iff.mp hh.1).2
        subst i
        rw [emit,if_pos rfl]
        rw [show TupleFieldTransfer.head bodies.length arity d (j::js) (emitArgs bodies.length arity d (j::js) args)=
          TupleFieldTransfer.head bodies.length args.length d (j::js) (emitArgs bodies.length arity d (j::js) args) by rw [ha]]
        have hsource := TupleFieldCompiler.source_row bodies arity d (j::js) body
        have htarget := TupleFieldCompiler.target_rows bodies arity d (j::js) (emit bodies.length arity d (j::js) body)
        have hfo := TupleFieldCompiler.source_firstOrder bodies arity d (j::js) body hb
          (RecursiveFieldSyntax.source_firstOrder _ _ _ _ body hc)
        apply TupleFieldTransfer.physical_of_body (source bodies arity d (j::js) body)
          (target bodies arity d (j::js) body) bodies.length d j js body
          (emit bodies.length arity d (j::js) body) (emit_firstOrder _ _ _ _ _)
          args (emitArgs bodies.length arity d (j::js) args) (emitArgs_length _ _ _ _ _) (by omega)
          (fun i hi => by rw [ha]; exact hs i hi) (fun i hi => cover i (by omega))
          (by simpa only [source,ha] using hsource) (by simpa only [target,ha] using htarget)
          hfo (args_firstOrder _ _ _ _ args hh.2) x E k p hp
        · intro m hm W hl hf q hq
          apply hbody m hm W (by omega)
          · intro w hw
            obtain ⟨i,hii,he⟩ := List.mem_iff_getElem.mp hw
            rw [←he]; exact hf i hii
          · exact hq
        · intro i hii
          rw [emitArgs_get]
          exact arguments_physical bodies arity d j js body hb hn hs cover hc x k hbody scope args hh.2 i hii E hE p hp
        · intro i hii q hv
          exact DelimitedValueSafety.captured_free d _ x .callByValuePar _ E hE args[i]
            (args_checked _ _ _ _ args hh.2 i hii).2 p q hp hv
    | scope,.seq a b,he,E,hE,p,hp => by
      have ha := expression_of_body bodies arity d j js body hb hn hs cover hc x k hbody scope a (Bool.and_eq_true_iff.mp he).1 E hE p hp
      simp only [emit]
      cases hv : evV (source bodies arity d (j::js) body) x .callByValuePar (tblV (source bodies arity d (j::js) body) x .callByValuePar k) E a p with
      | none => rw [evV_seq_none hv,evV_seq_none (ha.symm.trans hv)]
      | some v => cases v with
        | none => rw [evV_seq_fail hv,evV_seq_fail (ha.symm.trans hv)]
        | some q =>
          rw [evV_seq_ok hv,evV_seq_ok (ha.symm.trans hv)]
          exact expression_of_body bodies arity d j js body hb hn hs cover hc x k hbody scope b (Bool.and_eq_true_iff.mp he).2 E hE q
            (evV_ok (tblV_ok _ _ _ k) _ p hp q hv)
    | scope,.alt a b,he,E,hE,p,hp => by
      have ha := expression_of_body bodies arity d j js body hb hn hs cover hc x k hbody scope a (Bool.and_eq_true_iff.mp he).1 E hE p hp
      simp only [emit]
      cases hv : evV (source bodies arity d (j::js) body) x .callByValuePar (tblV (source bodies arity d (j::js) body) x .callByValuePar k) E a p with
      | none => rw [evV_alt_none hv,evV_alt_none (ha.symm.trans hv)]
      | some v => cases v with
        | some q => rw [evV_alt_ok hv,evV_alt_ok (ha.symm.trans hv)]
        | none =>
          rw [evV_alt_fail hv,evV_alt_fail (ha.symm.trans hv)]
          exact expression_of_body bodies arity d j js body hb hn hs cover hc x k hbody scope b (Bool.and_eq_true_iff.mp he).2 E hE p hp
    | scope,.notP a,he,E,hE,p,hp => by
      simp only [emit,evV,expression_of_body bodies arity d j js body hb hn hs cover hc x k hbody scope a he E hE p hp]
    | scope,.star a,he,E,hE,p,hp => by
      rw [emit,evV_star,evV_star]
      exact evStar_congr p (fun q hq => expression_of_body bodies arity d j js body hb hn hs cover hc x k hbody scope a he E hE q (by omega))
    | _,.dbg _,he,_,_,_,_ | _,.lam _ _,he,_,_,_,_ | _,.callParam _ _,he,_,_,_,_ | _,.invoke _ _ _,he,_,_,_,_ => by cases he

  theorem arguments_physical (bodies : List MExp) (arity : Nat) (d : Char) (j : Nat) (js : List Nat) (body : MExp)
      (hb : RecursiveParserStability.Valid bodies) (hn : 0<arity)
      (hs : ∀ i∈j::js, i<arity) (cover : ∀ i, i<arity → i∈j::js)
      (hc : exprCheck bodies.length arity arity d body=true)
      (x : List Char) (k : Nat)
      (hbody : ∀ m, m<k → ∀ W : List (List Char), W.length=arity → Environment d W → ∀ q, q≤x.length →
        evV (source bodies arity d (j::js) body) x .callByValuePar
          (tblV (source bodies arity d (j::js) body) x .callByValuePar m) W body q=
        evV (target bodies arity d (j::js) body) x .callByValueSeq
          (tblV (target bodies arity d (j::js) body) x .callByValueSeq m) W (emit bodies.length arity d (j::js) body) q)
      (scope : Nat) : ∀ args, argsCheck bodies.length arity scope d args=true → ∀ i, (hi : i<args.length) →
      ∀ E, Environment d E → ∀ p, p≤x.length →
      evV (source bodies arity d (j::js) body) x .callByValuePar
        (tblV (source bodies arity d (j::js) body) x .callByValuePar k) E args[i] p=
      evV (target bodies arity d (j::js) body) x .callByValueSeq
        (tblV (target bodies arity d (j::js) body) x .callByValueSeq k) E (emit bodies.length arity d (j::js) args[i]) p
    | [],_,i,hi,_,_,_,_ => by simp at hi
    | a::args,he,0,_,E,hE,p,hp => expression_of_body bodies arity d j js body hb hn hs cover hc x k hbody scope a
        (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp he).1).1 E hE p hp
    | a::args,he,i+1,hi,E,hE,p,hp => arguments_physical bodies arity d j js body hb hn hs cover hc x k hbody scope args
        (Bool.and_eq_true_iff.mp he).2 i (by simpa using hi) E hE p hp
end

/-- The recursive body assumption is discharged by induction on the actual
physical tables, for every newly captured tuple and observation position. -/
theorem physical (bodies : List MExp) (arity : Nat) (d : Char) (j : Nat) (js : List Nat) (body : MExp)
    (hb : RecursiveParserStability.Valid bodies) (hn : 0<arity)
    (hs : ∀ i∈j::js, i<arity) (cover : ∀ i, i<arity → i∈j::js)
    (hc : exprCheck bodies.length arity arity d body=true) (x : List Char) (k : Nat) :
    ∀ scope e, exprCheck bodies.length arity scope d e=true → ∀ E, Environment d E → ∀ p, p≤x.length →
    evV (source bodies arity d (j::js) body) x .callByValuePar
      (tblV (source bodies arity d (j::js) body) x .callByValuePar k) E e p=
    evV (target bodies arity d (j::js) body) x .callByValueSeq
      (tblV (target bodies arity d (j::js) body) x .callByValueSeq k) E (emit bodies.length arity d (j::js) e) p := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    apply expression_of_body bodies arity d j js body hb hn hs cover hc x k
    intro m hm W hl hf q hq
    exact ih m hm arity body hc W hf q hq

end Shallot.MacroPeg.CBV.RecursiveFieldCorrespondence
