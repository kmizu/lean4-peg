import MacroPeg.CBV.CallArithmetic

namespace Shallot.MacroPeg.CBV

open Complexity Shallot.MacroPeg.Mach Shallot.MacroPeg.KExp

/-- The immutable data and empty local workspaces required at each expression boundary.
Position, answer, call-rank and repetition frames may have arbitrary caller prefixes. -/
structure EvalReady {K : Nat} (r : EvalRegs K) (S : Lists K) (x : List Char) (row E : List Nat) : Prop where
  word : S (r.get 0) = mirrorRow x
  tmp : S (r.get 1) = []
  clean : ∀ i ∈ ([3, 4, 11, 12, 13, 14] : List (Fin 32)), S (r.get i) = []
  dict : S (r.get 17) = encPairs (spans x.length)
  count : S (r.get 19) = [(spans x.length).length]
  len : S (r.get 20) = [x.length]
  table : S (r.get 22) = row
  env : S (r.get 24) = E

/-- Changing any evaluator frame leaves all immutable inputs and local workspaces ready. -/
theorem EvalReady.frame {K : Nat} {r : EvalRegs K} {S : Lists K} {x : List Char} {row E : List Nat}
    (h : EvalReady r S x row E) (k : Fin 32) (hk : k ∈ ([15, 16, 21, 23] : List (Fin 32))) (v : List Nat) :
    EvalReady r (S.set (r.get k) v) x row E := by
  have h0 : (0 : Fin 32) ≠ k := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl | rfl | rfl <;> decide
  have h1 : (1 : Fin 32) ≠ k := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl | rfl | rfl <;> decide
  have h17 : (17 : Fin 32) ≠ k := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl | rfl | rfl <;> decide
  have h19 : (19 : Fin 32) ≠ k := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl | rfl | rfl <;> decide
  have h20 : (20 : Fin 32) ≠ k := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl | rfl | rfl <;> decide
  have h22 : (22 : Fin 32) ≠ k := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl | rfl | rfl <;> decide
  have h24 : (24 : Fin 32) ≠ k := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl | rfl | rfl <;> decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Lists.set, h0] using h.word
  · simpa [Lists.set, h1] using h.tmp
  · intro i hi
    have hik : i ≠ k := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi hk
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl <;> decide
    simpa [Lists.set, hik] using h.clean i hi
  · simpa [Lists.set, h17] using h.dict
  · simpa [Lists.set, h19] using h.count
  · simpa [Lists.set, h20] using h.len
  · simpa [Lists.set, h22] using h.table
  · simpa [Lists.set, h24] using h.env

/-- Repetition's private frames preserve the invariant expected by its recursively compiled body. -/
theorem EvalReady.star {K : Nat} {r : EvalRegs K} {S : Lists K} {x : List Char} {row E : List Nat}
    (h : EvalReady r S x row E) (p : Nat) (active : Bool) :
    EvalReady r (starState r.star S p active) x row E := by
  change EvalReady r ((S.set (r.get 15) (S (r.get 15) ++ [p])).set (r.get 23)
    (S (r.get 23) ++ [if active then 1 else 0])) x row E
  exact (h.frame 15 (by simp) _).frame 23 (by simp) _

/-- A variable leaf reads its identifier from the real environment row and matches the saved input interval. -/
theorem paramEval_runs {K : Nat} (r : EvalRegs K) (S : Lists K) (x : List Char) (row E : List Nat) (g : MGrammar) (s : Strategy)
    (ready : EvalReady r S x row E) (valid : ∀ i ∈ E, i < (spans x.length).length)
    (k q : Nat) {lp : List Nat} (hp : S (r.get 15) = lp ++ [q]) (hqn : q ≤ x.length) :
    NRuns (paramEvalP r E.length k) S
      (S.set (r.get 16) (S (r.get 16) ++ [resultCode (eval g x s row E (.param k) q)]))
      (12 * E.length + 10 + paramLiteralCost x.length) := by
  by_cases hk : k < E.length
  · simp only [paramEvalP, if_pos hk]
    have xread := tableRead_runs_used r.address (r.get 24) (r.get 7) (r.get 18)
      (r.ne (by decide)) (r.ne (by decide)) (r.ne (by decide))
      (by simp [EvalRegs.address, List.nodup_cons]) (fun _ => 0) (.num k) S E ready.env
      (by intro i hi; simp [AddrExpr.inputs] at hi) ready.tmp hk
    simp only [AddrExpr.value, AddrExpr.cost] at xread
    let X := S.set (r.get 18) (S (r.get 18) ++ [E[k]])
    have matchRun := paramLiteral_runs r.param X x E[k] q
      (li := S (r.get 18)) (lq := lp)
      (by change X (r.get 18) = _; simp [X])
      (by change X (r.get 15) = _; simp [X, Lists.set, hp])
      (by change X (r.get 0) = _; simp [X, Lists.set, ready.word])
      (by change X (r.get 17) = _; simp [X, Lists.set, ready.dict])
      (by change X (r.get 1) = _; simp [X, Lists.set, ready.tmp])
      (by change X (r.get 3) = _; simp [X, Lists.set, ready.clean 3 (by simp)])
      (by change X (r.get 4) = _; simp [X, Lists.set, ready.clean 4 (by simp)])
      (by change X (r.get 11) = _; simp [X, Lists.set, ready.clean 11 (by simp)])
      (by change X (r.get 12) = _; simp [X, Lists.set, ready.clean 12 (by simp)])
      (by change X (r.get 13) = _; simp [X, Lists.set, ready.clean 13 (by simp)])
      (by change X (r.get 14) = _; simp [X, Lists.set, ready.clean 14 (by simp)])
      (valid E[k] (List.getElem_mem hk)) hqn
    let v := literalCode (literalAt x E[k]) (sfx x q)
    change NRuns _ X (X.set (r.get 16) (X (r.get 16) ++ [v])) _ at matchRun
    have hx16 : X (r.get 16) = S (r.get 16) := by simp [X, Lists.set]
    rw [hx16] at matchRun
    let Y := X.set (r.get 16) (S (r.get 16) ++ [v])
    have xp := nruns_pop (r.get 18) Y (l := S (r.get 18)) (v := E[k]) (by simp [Y, X, Lists.set])
    have he : Y.set (r.get 18) (S (r.get 18)) = S.set (r.get 16) (S (r.get 16) ++ [v]) := by
      funext z
      by_cases h18 : z = r.get 18
      · subst z; simp [Y, X, Lists.set]
      by_cases h16 : z = r.get 16
      · subst z; simp [Y, X, Lists.set]
      simp [Y, X, Lists.set, h18, h16]
    rw [he] at xp
    have hv : v = resultCode (eval g x s row E (.param k) q) := by
      simp only [v, literalCode, eval, List.getElem?_eq_getElem hk]
      cases Shallot.stripPrefix? (literalAt x E[k]) (sfx x q) <;> rfl
    rw [hv] at xp
    exact (xread.seq (matchRun.seq xp)).mono (by omega)
  · simp only [paramEvalP, if_neg hk]
    have he : E[k]? = none := List.getElem?_eq_none (by omega)
    simpa only [eval, he, resultCode] using (nruns_pushC (r.get 16) S 1).mono (by omega)

end Shallot.MacroPeg.CBV
