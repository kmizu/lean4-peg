import MacroPeg.CBV.TypedFieldSyntax

namespace Shallot.MacroPeg.CBV.TypedFieldCorrespondence
open TypedFieldSyntax
open CaptureAlphabetEffects (Alphabet Environment)

def EarlierBodies (headers : List Header) (x : List Char) (k : Nat) : Prop :=
  ∀ m, m<k → ∀ (i : Nat) (s : Header), headers[i]?=some s → ∀ W, Environment s.parameters W → ∀ p, p≤x.length →
    evV (source headers) x .callByValuePar (tblV (source headers) x .callByValuePar m) W s.body p=
      evV (target headers) x .callByValueSeq (tblV (target headers) x .callByValueSeq m) W (emit headers s.body) p

mutual
  theorem expression_of_bodies (headers : List Header) (hv : Valid headers) (x : List Char) (k : Nat)
      (hbody : EarlierBodies headers x k) :
      ∀ Γ e, exprCheck headers Γ e=true → ∀ E, Environment Γ E → ∀ p, p≤x.length →
      evV (source headers) x .callByValuePar (tblV (source headers) x .callByValuePar k) E e p=
        evV (target headers) x .callByValueSeq (tblV (target headers) x .callByValueSeq k) E (emit headers e) p
    | _,.eps,_,_,_,_,_ | _,.any,_,_,_,_,_ | _,.chr _,_,_,_,_,_ | _,.range _ _,_,_,_,_,_
    | _,.lit _,_,_,_,_,_ | _,.param _,_,_,_,_,_ => rfl
    | Γ,.call i args,he,E,hE,p,hp => by
      cases hs : headers[i]? with
      | none => simp [exprCheck,hs] at he
      | some s =>
        have he : argsCheck headers Γ s.parameters args=true := by simpa only [exprCheck,hs] using he
        have ha : args.length=s.parameters.length := args_length headers Γ _ _ he
        have hvalid := hv.headers s (List.mem_of_getElem? hs)
        have hsource : ruleAtM (source headers).rules i=
            some ⟨args.length,TupleFieldTransfer.sourceBody s.delimiter s.pattern s.body⟩ := by
          simpa only [ha] using source_row headers i s hs
        have htarget : TupleFieldTransfer.Installed (target headers) (address headers i)
            args.length s.delimiter s.pattern (emit headers s.body) := by
          simpa only [ha] using target_rows headers i s hs
        have used : ParameterSupport.Supports (UsedFieldCapture.Allowed args.length s.pattern)
            (emit headers s.body) := by simpa only [ha] using hvalid.used
        have hb : ∀ m, m<k → ∀ W : List (List Char), W.length=args.length →
            (∀ n, (hn : n<W.length) → DelimitedCopyProjection.Free s.delimiter W[n]) →
            Environment s.parameters W → ∀ q, q≤x.length →
            evV (source headers) x .callByValuePar (tblV (source headers) x .callByValuePar m) W s.body q=
              evV (target headers) x .callByValueSeq (tblV (target headers) x .callByValueSeq m) W
                (emit headers s.body) q := by
          intro m hm W hlen hfree hW q hq
          exact hbody m hm i s hs W hW q hq
        have hrows := CaptureAlphabetEffects.physical_rows (source headers) (signatures headers) hv.effects x k
        have hQ : ∀ W, evParArgs (source headers) x .callByValuePar
            (tblV (source headers) x .callByValuePar k) E args p=some (some W) → Environment s.parameters W := by
          intro W hW
          exact CaptureAlphabetEffects.arguments (source headers) x _ (signatures headers) hrows Γ E hE
            s.parameters args (args_effect headers Γ _ _ he) p hp W hW
        have hemit : ∀ n, (hn : n<args.length) →
            evV (source headers) x .callByValuePar (tblV (source headers) x .callByValuePar k) E args[n] p=
              evV (target headers) x .callByValueSeq (tblV (target headers) x .callByValueSeq k) E
                ((emitArgs headers args)[n]'(by rw [emitArgs_length]; exact hn)) p := by
          intro n hn
          rw [emitArgs_get]
          exact arguments_physical headers hv x k hbody Γ s.parameters args he n hn E hE p hp
        have hfree : ∀ n, (hn : n<args.length) → ∀ q,
            evV (source headers) x .callByValuePar (tblV (source headers) x .callByValuePar k) E args[n] p=some (some q) →
              DelimitedCopyProjection.Free s.delimiter (pre x p q) := by
          intro n hn q hq
          obtain ⟨A,hA,hc,ht⟩ := args_checked headers Γ s.parameters args he n hn
          exact CaptureAlphabetEffects.captured_free (source headers) (signatures headers) hv.effects x k Γ E hE
            args[n] A ht s.delimiter (hvalid.free A (List.mem_of_getElem? hA)) p q hp hq
        simp only [emit,hs]
        rw [show TupleFieldTransfer.head (address headers i) s.parameters.length s.delimiter s.pattern (emitArgs headers args)=
            TupleFieldTransfer.head (address headers i) args.length s.delimiter s.pattern (emitArgs headers args) by rw [ha]]
        cases hpat : s.pattern with
        | nil =>
          simp only [hpat] at hsource htarget used
          exact TypedFieldTransfer.physical_empty_retaining (source headers) (target headers)
            i (address headers i) s.delimiter s.body (emit headers s.body) (Environment s.parameters)
            args (emitArgs headers args) (emitArgs_length headers args) used
            hsource htarget x E k p hp hb hemit hQ hfree
        | cons j js =>
          have hscope : ∀ n∈j::js, n<args.length := by
            intro n hn
            rw [ha]
            exact hvalid.scope n (by simpa only [hpat] using hn)
          have hn : 0<args.length := by have := hscope j (by simp); omega
          simp only [hpat] at hsource htarget used
          exact TypedFieldTransfer.physical_retaining (source headers) (target headers)
            i (address headers i) s.delimiter j js s.body (emit headers s.body) (Environment s.parameters)
            args (emitArgs headers args) (emitArgs_length headers args) hn hscope used
            hsource htarget (source_firstOrder_grammar headers hv) (args_firstOrder headers Γ _ _ he)
            x E k p hp hb hemit hQ hfree
    | Γ,.seq a b,he,E,hE,p,hp => by
      have ha := expression_of_bodies headers hv x k hbody Γ a (Bool.and_eq_true_iff.mp he).1 E hE p hp
      simp only [emit]
      cases heval : evV (source headers) x .callByValuePar (tblV (source headers) x .callByValuePar k) E a p with
      | none => rw [evV_seq_none heval,evV_seq_none (ha.symm.trans heval)]
      | some v => cases v with
        | none => rw [evV_seq_fail heval,evV_seq_fail (ha.symm.trans heval)]
        | some q =>
          rw [evV_seq_ok heval,evV_seq_ok (ha.symm.trans heval)]
          exact expression_of_bodies headers hv x k hbody Γ b (Bool.and_eq_true_iff.mp he).2 E hE q
            (evV_ok (tblV_ok _ _ _ k) _ p hp q heval)
    | Γ,.alt a b,he,E,hE,p,hp => by
      have ha := expression_of_bodies headers hv x k hbody Γ a (Bool.and_eq_true_iff.mp he).1 E hE p hp
      simp only [emit]
      cases heval : evV (source headers) x .callByValuePar (tblV (source headers) x .callByValuePar k) E a p with
      | none => rw [evV_alt_none heval,evV_alt_none (ha.symm.trans heval)]
      | some v => cases v with
        | some q => rw [evV_alt_ok heval,evV_alt_ok (ha.symm.trans heval)]
        | none =>
          rw [evV_alt_fail heval,evV_alt_fail (ha.symm.trans heval)]
          exact expression_of_bodies headers hv x k hbody Γ b (Bool.and_eq_true_iff.mp he).2 E hE p hp
    | Γ,.notP a,he,E,hE,p,hp => by
      simp only [emit,evV,expression_of_bodies headers hv x k hbody Γ a he E hE p hp]
    | Γ,.star a,he,E,hE,p,hp => by
      rw [emit,evV_star,evV_star]
      exact evStar_congr p (fun q hq => expression_of_bodies headers hv x k hbody Γ a he E hE q (by omega))
    | _,.dbg _,he,_,_,_,_ | _,.lam _ _,he,_,_,_,_ | _,.callParam _ _,he,_,_,_,_ | _,.invoke _ _ _,he,_,_,_,_ => by cases he

  theorem arguments_physical (headers : List Header) (hv : Valid headers) (x : List Char) (k : Nat)
      (hbody : EarlierBodies headers x k) (Γ : List Alphabet) :
      ∀ As args, argsCheck headers Γ As args=true → ∀ i, (hi : i<args.length) →
      ∀ E, Environment Γ E → ∀ p, p≤x.length →
      evV (source headers) x .callByValuePar (tblV (source headers) x .callByValuePar k) E args[i] p=
        evV (target headers) x .callByValueSeq (tblV (target headers) x .callByValueSeq k) E (emit headers args[i]) p
    | [],[],_,i,hi,_,_,_,_ => by simp at hi
    | A::As,a::args,he,0,_,E,hE,p,hp => expression_of_bodies headers hv x k hbody Γ a
        (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp he).1).1 E hE p hp
    | A::As,a::args,he,i+1,hi,E,hE,p,hp => arguments_physical headers hv x k hbody Γ As args
        (Bool.and_eq_true_iff.mp he).2 i (by simpa using hi) E hE p hp
    | [],_::_,h,_,_,_,_,_,_ | _::_,[],h,_,_,_,_,_,_ => by cases h
end

/-- The physical clock induction closes all recursive body hypotheses for
the whole finite family, including differently typed positive producers
inside actuals and return to each caller's retained environment. -/
theorem physical (headers : List Header) (hv : Valid headers) (x : List Char) (k : Nat) :
    ∀ Γ e, exprCheck headers Γ e=true → ∀ E, Environment Γ E → ∀ p, p≤x.length →
    evV (source headers) x .callByValuePar (tblV (source headers) x .callByValuePar k) E e p=
      evV (target headers) x .callByValueSeq (tblV (target headers) x .callByValueSeq k) E (emit headers e) p := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    apply expression_of_bodies headers hv x k
    intro m hm i s hs W hW p hp
    exact ih m hm s.parameters s.body (hv.headers s (List.mem_of_getElem? hs)).body W hW p hp

end Shallot.MacroPeg.CBV.TypedFieldCorrespondence
