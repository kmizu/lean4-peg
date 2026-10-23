import MacroPeg.CBV.ArgStep

namespace Shallot.MacroPeg.CBV

open Complexity Shallot.MacroPeg.KExp

def argsState {K : Nat} (r : EvalRegs K) (S : Lists K) (lp lr : List Nat) (p rank : Nat) : Lists K :=
  (S.set (r.get 15) (lp ++ [p])).set (r.get 21) (lr ++ [rank])

theorem argsState_self {K : Nat} (r : EvalRegs K) (S : Lists K) (lp lr : List Nat) (p rank : Nat)
    (hp : S (r.get 15) = lp ++ [p]) (hr : S (r.get 21) = lr ++ [rank]) :
    argsState r S lp lr p rank = S := by
  unfold argsState
  rw [← hp, Lists.set_get_self, ← hr, Lists.set_get_self]

theorem argsState_argNext {K : Nat} (r : EvalRegs K) (s : Strategy) (S : Lists K)
    (lp lr : List Nat) (j rank p' rank' : Nat) :
    argsState r (argNextState r s S lp lr j rank) lp lr p' rank' = argsState r S lp lr p' rank' := by
  unfold argNextState
  split <;> simp only [argsState] <;> arg_states r

def rankedAnswer (Q : Nat → Nat → Res) : Option (Option (Nat × Nat)) → Res
  | none => none
  | some none => some none
  | some (some (rank, p)) => Q rank p

theorem rank_progress {D digit rank k limit : Nat} (hd : digit < D)
    (h : rank + D ^ (k + 1) ≤ limit) : rank + digit * D ^ k + D ^ k ≤ limit := by
  have hm := Nat.mul_le_mul_right (D ^ k) (show digit + 1 ≤ D by omega)
  have he : D ^ (k + 1) = D * D ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
  rw [he] at h
  rw [Nat.add_mul, Nat.one_mul] at hm
  omega

/-- The actual argument compiler realizes its streaming specification, including all early exits.
The continuation is itself required to be a verified stack program on each valid terminal rank. -/
theorem argsProgram_runs {K : Nat} (r : EvalRegs K) (g : MGrammar) (s : Strategy)
    (x : List Char) (row E : List Nat) (hrow : RowBound x.length row)
    (cont : NProg K) (Q : Nat → Nat → Res) (limit C : Nat)
    (hlimit : limit ≤ rankCap g x.length)
    (hcont : ∀ (V : Lists K), EvalReady r V x row E → ∀ (p rank : Nat) (lp lr : List Nat),
      V (r.get 15) = lp ++ [p] → V (r.get 21) = lr ++ [rank] → p ≤ x.length → rank < limit →
      NRuns cont V (V.set (r.get 16) (V (r.get 16) ++ [resultCode (Q rank p)])) C) :
    ∀ (args : List MExp),
    (∀ a ∈ args, ∀ (V : Lists K), EvalReady r V x row E → ∀ (q : Nat) (lp : List Nat),
      V (r.get 15) = lp ++ [q] → q ≤ x.length →
      NRuns (exprProgram r g s E.length a) V
        (V.set (r.get 16) (V (r.get 16) ++ [resultCode (eval g x s row E a q)]))
        (exprBudget g E.length a x.length)) →
    ∀ (S : Lists K), EvalReady r S x row E → ∀ (p rank : Nat) (lp lr : List Nat),
    S (r.get 15) = lp ++ [p] → S (r.get 21) = lr ++ [rank] → p ≤ x.length →
    rank + (subStrs x).length ^ args.length ≤ limit →
    ∃ q rank', q ≤ x.length ∧ rank' ≤ limit ∧
      NRuns (argsProgram r g s E.length args cont) S
        ((argsState r S lp lr q rank').set (r.get 16)
          (S (r.get 16) ++ [resultCode (rankedAnswer Q (rankedArgs g x s row E args rank p))]))
        (argsBudget g E.length args x.length + C) := by
  intro args
  induction args with
  | nil =>
    intro _ S ready p rank lp lr hp hr hpn hcap
    have hx := hcont S ready p rank lp lr hp hr hpn (by simp at hcap; omega)
    refine ⟨p, rank, hpn, by simp at hcap; omega, ?_⟩
    simpa only [argsProgram, argsBudget, Nat.zero_add, rankedArgs, rankedAnswer, argsState_self r S lp lr p rank hp hr] using hx
  | cons a args ih =>
    intro hbody S ready p rank lp lr hp hr hpn hcap
    have xa := hbody a List.mem_cons_self S ready p lp hp hpn
    have hRank : rank ≤ rankCap g x.length := by
      have := Nat.le_trans (show rank ≤ rank + (subStrs x).length ^ (a :: args).length by omega) hcap
      omega
    have hb : ∀ b ∈ args, ∀ (V : Lists K), EvalReady r V x row E → ∀ (q : Nat) (lp : List Nat),
        V (r.get 15) = lp ++ [q] → q ≤ x.length →
        NRuns (exprProgram r g s E.length b) V
          (V.set (r.get 16) (V (r.get 16) ++ [resultCode (eval g x s row E b q)]))
          (exprBudget g E.length b x.length) :=
      fun b hb => hbody b (List.mem_cons_of_mem a hb)
    cases he : eval g x s row E a p with
    | none =>
      have xb := argAfter_runs r g s S (fun _ => S) x row E ready p rank args.length C lp lr none
        hp hr hpn (by intro j hj; cases hj) hRank (argsProgram r g s E.length args cont)
        (by intro j hj; cases hj)
      rw [he] at xa
      have hx := xa.seq xb
      refine ⟨p, rank, hpn, Nat.le_trans (by omega) hcap, ?_⟩
      have hout := argsState_self r S lp lr p rank hp hr
      simp only [argsProgram, rankedArgs, he, rankedAnswer, resultCode, hout]
      exact hx.mono (by simp only [argsBudget]; omega)
    | some u => cases u with
      | none =>
        have xb := argAfter_runs r g s S (fun _ => S) x row E ready p rank args.length C lp lr (some none)
          hp hr hpn (by intro j hj; cases hj) hRank (argsProgram r g s E.length args cont)
          (by intro j hj; cases hj)
        rw [he] at xa
        have hx := xa.seq xb
        refine ⟨p, rank, hpn, Nat.le_trans (by omega) hcap, ?_⟩
        have hout := argsState_self r S lp lr p rank hp hr
        simp only [argsProgram, rankedArgs, he, rankedAnswer, resultCode, hout]
        exact hx.mono (by simp only [argsBudget]; omega)
      | some j =>
        let digit := spanId x.length p j
        let rank₁ := rank + digit * (subStrs x).length ^ args.length
        let p₁ := if s = .callByValueSeq then j else p
        let V := argNextState r s S lp lr j rank₁
        have hV : EvalReady r V x row E := ready.argNext s lp lr j rank₁
        have hjn := eval_ok hrow a p hpn j he
        have hp₁ : p₁ ≤ x.length := by dsimp [p₁]; split <;> assumption
        have hVp : V (r.get 15) = lp ++ [p₁] := by
          dsimp [V, argNextState, p₁]
          split <;> simp [Lists.set, hp]
        have hVr : V (r.get 21) = lr ++ [rank₁] := by
          dsimp [V, argNextState]
          split <;> simp [Lists.set]
        have hcap₁ : rank₁ + (subStrs x).length ^ args.length ≤ limit :=
          rank_progress (spanId_lt hpn) hcap
        obtain ⟨q, rank', hq, hr', xt⟩ := ih hb V hV p₁ rank₁ lp lr hVp hVr hp₁ hcap₁
        have hVout : V (r.get 16) = S (r.get 16) := by
          dsimp [V, argNextState]; split <;> simp [Lists.set]
        have hframe := argsState_argNext r s S lp lr j rank₁ q rank'
        rw [hVout, hframe] at xt
        let U := (argsState r S lp lr q rank').set (r.get 16)
          (S (r.get 16) ++ [resultCode (rankedAnswer Q (rankedArgs g x s row E args rank₁ p₁))])
        have xb := argAfter_runs r g s S (fun _ => U) x row E ready p rank args.length
          (argsBudget g E.length args x.length + C) lp lr (some (some j)) hp hr hpn
          (by intro z hz; cases Option.some.inj (Option.some.inj hz); exact hjn) hRank
          (argsProgram r g s E.length args cont)
          (by
            intro z hz
            have hz' : j = z := Option.some.inj (Option.some.inj hz)
            subst z
            exact xt)
        rw [he] at xa
        have hx := xa.seq xb
        refine ⟨q, rank', hq, hr', ?_⟩
        simp only [argsProgram, rankedArgs, he]
        exact hx.mono (by simp only [argsBudget]; omega)

end Shallot.MacroPeg.CBV
