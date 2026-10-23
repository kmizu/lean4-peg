import MacroPeg.CBV.CallQuery

namespace Shallot.MacroPeg.CBV

open Complexity Shallot.Packrat.Machine Shallot.MacroPeg.KExp

theorem argsState_callState {K : Nat} (r : EvalRegs K) (S : Lists K) (p rank q rank' : Nat) :
    argsState r (callState r S p rank) (S (r.get 15)) (S (r.get 21)) q rank' = callState r S q rank' := by
  simp only [argsState, callState]
  arg_states r

/-- Every fixed expression is executed by its actual stack program within a uniform polynomial budget. -/
theorem exprProgram_runs {K : Nat} (r : EvalRegs K) (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Nat → List (List Char) → Val) (E : List Nat) (hT : OkTV x.length T)
    (hE : ∀ i ∈ E, i < (spans x.length).length) :
    ∀ (e : MExp) (S : Lists K), EvalReady r S x (pack g x T) E → ∀ (p : Nat) (lp : List Nat),
      S (r.get 15) = lp ++ [p] → p ≤ x.length →
      NRuns (exprProgram r g s E.length e) S
        (S.set (r.get 16) (S (r.get 16) ++ [resultCode (eval g x s (pack g x T) E e p)]))
        (exprBudget g E.length e x.length)
  | .eps, S, ready, p, lp, hp, hpn => nruns_emptySuccess _ _ (r.ne (by decide)) S hp
  | .dbg _, S, ready, p, lp, hp, hpn => nruns_emptySuccess _ _ (r.ne (by decide)) S hp
  | .lam _ _, S, ready, p, lp, hp, hpn => nruns_emptySuccess _ _ (r.ne (by decide)) S hp
  | .any, S, ready, p, lp, hp, hpn => by
    have hx := remainingLex_runs r.param.literal anyTest S x ready.word ready.tmp hp hpn
    rw [remainingLex_any g x s (pack g x T) E p hpn] at hx
    exact hx
  | .chr c, S, ready, p, lp, hp, hpn => by
    have hx := remainingLex_runs r.param.literal (chrTest c) S x ready.word ready.tmp hp hpn
    rw [remainingLex_chr g x s (pack g x T) E c p hpn] at hx
    exact hx
  | .range lo hi, S, ready, p, lp, hp, hpn => by
    have hx := remainingLex_runs r.param.literal (rangeTest lo hi) S x ready.word ready.tmp hp hpn
    rw [remainingLex_range g x s (pack g x T) E lo hi p hpn] at hx
    exact hx
  | .lit w, S, ready, p, lp, hp, hpn => by
    have hx := fixedLiteral_runs r.param.literal w x S ready.word ready.tmp hp hpn
    rw [literalCode_eval g x s (pack g x T) E w p] at hx
    exact hx
  | .param k, S, ready, p, lp, hp, hpn =>
    paramEval_runs r S x (pack g x T) E g s ready hE k p hp hpn
  | .callParam _ _, S, ready, p, lp, hp, hpn => nruns_pushC _ S 1
  | .invoke _ _ _, S, ready, p, lp, hp, hpn => nruns_pushC _ S 0
  | .seq a b, S, ready, p, lp, hp, hpn => by
    have xa := exprProgram_runs r g x s T E hT hE a S ready p lp hp hpn
    let f := fun j => resultCode (eval g x s (pack g x T) E b j)
    have xb := seqAfter_runs r.param.literal (exprProgram r g s E.length b) S
      (eval g x s (pack g x T) E a p) f (exprBudget g E.length b x.length)
      (by
        intro j hj
        let V := S.set (r.get 15) (S (r.get 15) ++ [j])
        have hv := ready.frame 15 (by simp) (S (r.get 15) ++ [j])
        have xx := exprProgram_runs r g x s T E hT hE b V hv j (S (r.get 15)) (by simp [V])
          (eval_ok (pack_bound hT) a p hpn j hj)
        have hVout : V (r.get 16) = S (r.get 16) := by simp [V, Lists.set]
        rw [hVout] at xx
        exact xx)
    simp only [eval]
    cases heval : eval g x s (pack g x T) E a p with
    | none =>
      simp only [heval] at xa xb ⊢
      exact (xa.seq xb).mono (by simp only [exprBudget]; omega)
    | some u => cases u with
      | none =>
        simp only [heval] at xa xb ⊢
        exact (xa.seq xb).mono (by simp only [exprBudget]; omega)
      | some j =>
        simp only [heval] at xa xb ⊢
        exact (xa.seq xb).mono (by simp only [exprBudget]; omega)
  | .alt a b, S, ready, p, lp, hp, hpn => by
    have xa := exprProgram_runs r g x s T E hT hE a S ready p lp hp hpn
    have xb := exprProgram_runs r g x s T E hT hE b S ready p lp hp hpn
    have hx := altEval_runs (r.get 16) _ _ S _ _ _ _ xa xb
    have he : (if resultCode (eval g x s (pack g x T) E a p) = 1 then
        resultCode (eval g x s (pack g x T) E b p) else resultCode (eval g x s (pack g x T) E a p)) =
        resultCode (eval g x s (pack g x T) E (.alt a b) p) := by
      cases ha : eval g x s (pack g x T) E a p with
      | none => simp [eval, ha, resultCode]
      | some u => cases u with
        | none => simp [eval, ha, resultCode]
        | some j => simp [eval, ha, resultCode, show j + 2 ≠ 1 by omega]
    rw [he] at hx
    exact hx
  | .notP a, S, ready, p, lp, hp, hpn => by
    have xa := exprProgram_runs r g x s T E hT hE a S ready p lp hp hpn
    have xb := notAfter_runs r.param.literal S (resultCode (eval g x s (pack g x T) E a p)) p hp
    have he : (if resultCode (eval g x s (pack g x T) E a p) = 0 then 0 else
        if resultCode (eval g x s (pack g x T) E a p) = 1 then p + 2 else 1) =
        resultCode (eval g x s (pack g x T) E (.notP a) p) := by
      cases ha : eval g x s (pack g x T) E a p with
      | none => simp [eval, ha, resultCode]
      | some u => cases u with
        | none => simp [eval, ha, resultCode]
        | some j => simp [eval, ha, resultCode, show j + 2 ≠ 1 by omega]
    rw [he] at xb
    exact xa.seq xb
  | .star a, S, ready, p, lp, hp, hpn => by
    have hx := starEval_runs r.star (exprProgram r g s E.length a) S
      (fun q => eval g x s (pack g x T) E a q) x.length (exprBudget g E.length a x.length) p hp hpn
      (by
        intro q hq
        let V := starState r.star S q true
        have hVp : V (r.get 15) = S (r.get 15) ++ [q] := by
          change ((S.set (r.get 15) (S (r.get 15) ++ [q])).set (r.get 23) (S (r.get 23) ++ [1])) (r.get 15) = _
          simp [Lists.set]
        have hVout : V (r.get 16) = S (r.get 16) := by
          change ((S.set (r.get 15) (S (r.get 15) ++ [q])).set (r.get 23) (S (r.get 23) ++ [1])) (r.get 16) = _
          simp [Lists.set]
        have xx := exprProgram_runs r g x s T E hT hE a V (ready.star q true) q (S (r.get 15)) hVp hq
        rw [hVout] at xx
        exact xx)
      (fun q hq j hj => eval_ok (pack_bound hT) a q hq j hj)
    exact hx
  | .call i args, S, ready, p, lp, hp, hpn => by
    cases hrule : ruleAtM g.rules i with
    | none =>
      simp only [exprProgram, hrule, eval]
      exact (nruns_pushC (r.get 16) S 1).mono (by unfold exprBudget readCallCost; omega)
    | some rule =>
      by_cases ha : rule.arity = args.length
      · have xp := callPrepare_runs r S p hp
        let V := callState r S p 0
        let Q := rankLookup g x (pack g x T) i
        have hlimit := rankCap_bound (x := x) (grammarArity_bound (ruleAtM_mem hrule))
        have hc := argsProgram_runs r g s x (pack g x T) E (pack_bound hT) (ruleReadP r g i) Q
          ((subStrs x).length ^ rule.arity) (readCallCost g i x.length) hlimit
          (by
            intro W hw q rank lq lr hq hr hqn hRank
            exact ruleRead_bounded r g x T E i rule hrule W hw q rank lq lr hq hr hqn hRank)
          args
          (by
            intro a hm W hw q lq hq hqn
            exact exprProgram_runs r g x s T E hT hE a W hw q lq hq hqn)
          V (ready.call p 0) p 0 (S (r.get 15)) (S (r.get 21))
          (by simp [V, callState, Lists.set]) (by simp [V, callState, Lists.set]) hpn
          (by simp [ha])
        obtain ⟨q, rank, _, _, xt⟩ := hc
        have hframe := argsState_callState r S p 0 q rank
        have hVout : V (r.get 16) = S (r.get 16) := by simp [V, callState, Lists.set]
        rw [hVout, hframe] at xt
        have he : rankedAnswer Q (rankedArgs g x s (pack g x T) E args 0 p) =
            eval g x s (pack g x T) E (.call i args) p :=
          rankedCall_eval hT hrule ha hpn
        rw [he] at xt
        have xf := callCleanup_runs r S q rank (resultCode (eval g x s (pack g x T) E (.call i args) p))
        have hx := xp.seq (xt.seq xf)
        simp only [exprProgram, hrule, if_pos ha]
        exact hx.mono (by simp only [exprBudget]; omega)
      · simp only [exprProgram, hrule, if_neg ha, eval]
        exact (nruns_pushC (r.get 16) S 1).mono (by unfold exprBudget readCallCost; omega)
termination_by e _ _ _ _ _ _ => sizeOf e
decreasing_by all_goals decreasing_tactic

end Shallot.MacroPeg.CBV
