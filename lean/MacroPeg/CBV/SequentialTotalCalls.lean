import MacroPeg.CBV.SequentialTotalRoutes

/-! The general call case of the staged Seq transformation, conditional on its
ordinary lower rows and current empty-call helpers. No restriction on
actual syntax, captures, arity or the source call graph is imposed. -/
namespace Shallot.MacroPeg.CBV.SequentialTotalCalls
open SequentialTotalSyntax SequentialTotalControl SequentialTotalArguments SequentialTotalRoutes

structure CallRows (g h : MGrammar) (x : List Char) (T U : SequentialClock.Table)
    (E : List (List Char)) (fuel p : Nat) : Prop where
  ordinary_rule : ∀ i r, ruleAtM g.rules i=some r → ∀ m,
    ∃ body, ruleAtM h.rules (ordinaryIndex g i m)=some ⟨r.arity,body⟩
  ordinary_value : ∀ i r, ruleAtM g.rules i=some r → ∀ m W q, W.length=r.arity → q<p →
    valAt (U (ordinaryIndex g i m) W) q=modeResult m q (valAt (T i W) q)
  empty_value : ∀ i r, ruleAtM g.rules i=some r → ∀ m,
    evV h x .callByValueSeq U E (emptyCall g i fuel m) p=
      modeResult m p (valAt (T i (List.replicate r.arity [])) p)

variable {g h : MGrammar} {x : List Char} {T U : SequentialClock.Table}
  {E : List (List Char)} {fuel p i : Nat} {args : List MExp} {as : List (Forms × Forms)}

theorem valid_call (hd : SequentialClock.Descending T)
    (entries : Entries g h x T U E p args as)
    (rows : CallRows g h x T U E fuel p) (r : MRule)
    (hr : ruleAtM g.rules i=some r) (ha : r.arity=args.length) :
    Realizes h x U E (callForms g fuel i as) p
      (evV g x .callByValueSeq T E (.call i args) p) := by
  have hlen := entries_length entries
  have ha' : r.arity=as.length := by omega
  have hz := zero_correct hd entries
  have hf := failure_correct hd entries
  obtain ⟨bs,hbs⟩ := rows.ordinary_rule i r hr .success
  obtain ⟨bf,hbf⟩ := rows.ordinary_rule i r hr .failure
  have har : ∀ ar∈positiveRoutes as, r.arity=ar.length := by
    intro ar har
    exact ha'.trans (positiveRoutes_arity as ar har).symm
  have hs := (calls_eval (positiveRoutes as) p (ordinaryIndex g i .success) ⟨r.arity,bs⟩ hbs har).trans
    (routes_correct hd entries (fun W q => valAt (U (ordinaryIndex g i .success) W) q))
  have hF := (lookahead_calls_eval (positiveRoutes as) p (ordinaryIndex g i .failure) ⟨r.arity,bf⟩ hbf har).trans
    (routes_correct hd entries (fun W q => CallLookahead.peek p (valAt (U (ordinaryIndex g i .failure) W) q)))
  rw [evV_call_seq hr ha]
  cases hv : evSeqArgs g x .callByValueSeq T E args p with
  | none =>
    simp only [hv,zeroArgsResult,failureArgsResult,positiveFeed] at hz hf hs hF
    simp [Realizes,callForms,hr,ha',evV,hz,hf,hs,hF,zeroResult,positiveResult,failureResult]
  | some v => cases v with
    | none =>
      simp only [hv,zeroArgsResult,failureArgsResult,positiveFeed] at hz hf hs hF
      simp [Realizes,callForms,hr,ha',evV,hz,hf,hs,zeroResult,positiveResult,failureResult]
    | some pair =>
      obtain ⟨W,q⟩ := pair
      have hm := SequentialClock.arguments_metadata hd E args p W q hv
      have hw : W.length=r.arity := by rw [evSeq_length args p W q hv,ha]
      by_cases hqp : q=p
      · subst q
        have hW : W=List.replicate r.arity [] := by simpa [ha] using hm.2 rfl
        subst W
        simp only [hv,zeroArgsResult,failureArgsResult,positiveFeed,↓reduceIte] at hz hf hs hF
        have ez := rows.empty_value i r hr .zero
        have ep := rows.empty_value i r hr .positive
        have ef := rows.empty_value i r hr .failure
        simp only [modeResult] at ez ep ef
        change Realizes h x U E (callForms g fuel i as) p (valAt (T i (List.replicate r.arity [])) p)
        unfold Realizes callForms
        simp only [hr,if_pos ha']
        constructor
        · exact (evV_seq_ok hz).trans ez
        constructor
        · rw [evV_alt_fail hs,evV_seq_ok hz,ep]
        · rw [evV_alt_fail hf,evV_alt_fail hF,evV_seq_ok hz,ef]
      · have hqp' : q<p := by omega
        have hS := rows.ordinary_value i r hr .success W q hw hqp'
        have hV := rows.ordinary_value i r hr .failure W q hw hqp'
        simp only [hv,zeroArgsResult,failureArgsResult,positiveFeed,if_neg hqp] at hz hf hs hF
        rw [hS] at hs
        rw [hV] at hF
        simp only [modeResult] at hs hF
        change Realizes h x U E (callForms g fuel i as) p (valAt (T i W) q)
        have hdq := hd i W q
        cases hc : valAt (T i W) q with
        | none =>
          simp only [hc,successResult,failureResult,CallLookahead.peek] at hs hF
          simp [Realizes,callForms,hr,ha',evV,hz,hf,hs,hF,zeroResult,positiveResult,failureResult]
        | some v => cases v with
          | none =>
            simp only [hc,successResult,failureResult,CallLookahead.peek] at hs hF
            simp [Realizes,callForms,hr,ha',evV,hz,hf,hs,hF,zeroResult,positiveResult,failureResult]
          | some j =>
            have hj : j≠p := by have := hdq j hc; omega
            simp only [hc,successResult,failureResult,CallLookahead.peek] at hs hF
            simp [Realizes,callForms,hr,ha',evV,hz,hf,hs,hF,zeroResult,positiveResult,failureResult,hj]

theorem call_correct (hd : SequentialClock.Descending T)
    (entries : Entries g h x T U E p args as)
    (rows : CallRows g h x T U E fuel p) :
    Realizes h x U E (callForms g fuel i as) p
      (evV g x .callByValueSeq T E (.call i args) p) := by
  cases hr : ruleAtM g.rules i with
  | none => simp [Realizes,callForms,hr,invalid,evV,MExp.failAlways,zeroResult,positiveResult,failureResult]
  | some r =>
    by_cases ha : r.arity=args.length
    · exact valid_call hd entries rows r hr ha
    · have hlen := entries_length entries
      have ha' : r.arity≠as.length := by omega
      simp [Realizes,callForms,hr,ha,ha',invalid,evV,MExp.failAlways,zeroResult,positiveResult,failureResult]

end Shallot.MacroPeg.CBV.SequentialTotalCalls
