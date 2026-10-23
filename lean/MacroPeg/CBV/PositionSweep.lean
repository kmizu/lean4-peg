import MacroPeg.CBV.ExprRuns

namespace Shallot.MacroPeg.CBV

open Complexity Shallot.MacroPeg.KExp

theorem EvalReady.reserved {K : Nat} {r : EvalRegs K} {S : Lists K} {x : List Char} {row E : List Nat}
    (h : EvalReady r S x row E) (k : Fin 32) (hk : 25 ≤ k.val) (v : List Nat) :
    EvalReady r (S.set (r.get k) v) x row E := by
  have hn : ∀ i : Fin 32, i.val < 25 → i ≠ k := by
    intro i hi he
    have := congrArg (fun j : Fin 32 => j.val) he
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Lists.set, hn 0 (by decide)] using h.word
  · simpa [Lists.set, hn 1 (by decide)] using h.tmp
  · intro i hi
    have hi' : i.val < 25 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa [Lists.set, hn i hi'] using h.clean i hi
  · simpa [Lists.set, hn 17 (by decide)] using h.dict
  · simpa [Lists.set, hn 19 (by decide)] using h.count
  · simpa [Lists.set, hn 20 (by decide)] using h.len
  · simpa [Lists.set, hn 22 (by decide)] using h.table
  · simpa [Lists.set, hn 24 (by decide)] using h.env

def posState {K : Nat} (r : EvalRegs K) (S : Lists K) (out : List Nat) (p remaining : Nat) : Lists K :=
  ((S.set (r.get 25) out).set (r.get 15) (S (r.get 15) ++ [p])).set (r.get 28) (S (r.get 28) ++ [remaining])

theorem EvalReady.positions {K : Nat} {r : EvalRegs K} {S : Lists K} {x : List Char} {row E : List Nat}
    (h : EvalReady r S x row E) (out : List Nat) (p remaining : Nat) :
    EvalReady r (posState r S out p remaining) x row E :=
  ((h.reserved 25 (by decide) out).frame 15 (by simp) _).reserved 28 (by decide) _

macro "pos_states " r:term : tactic => `(tactic| (
  funext z
  by_cases h15 : z = ($r).get 15
  · subst z; simp_all [Lists.set] <;> omega
  by_cases h16 : z = ($r).get 16
  · subst z; simp_all [Lists.set] <;> omega
  by_cases h25 : z = ($r).get 25
  · subst z; simp_all [Lists.set] <;> omega
  by_cases h28 : z = ($r).get 28
  · subst z; simp_all [Lists.set] <;> omega
  simp_all [Lists.set] <;> omega))

def positionBodyP {K : Nat} (r : EvalRegs K) (g : MGrammar) (s : Strategy) (m : Nat) (e : MExp) : NProg K :=
  .seq (exprProgram r g s m e) (.seq (nmv (r.get 16) (r.get 25) (r.ne (by decide)))
    (.seq (.prim (.inc (r.get 15))) (.prim (.dec (r.get 28)))))

theorem positionBody_runs {K : Nat} (r : EvalRegs K) (g : MGrammar) (s : Strategy) (x : List Char)
    (T : Nat → List (List Char) → Val) (E : List Nat) (hT : OkTV x.length T)
    (hE : ∀ i ∈ E, i < (spans x.length).length) (e : MExp) (S : Lists K)
    (ready : EvalReady r S x (pack g x T) E) (out : List Nat) (p remaining : Nat) (hp : p ≤ x.length) :
    NRuns (positionBodyP r g s E.length e) (posState r S out p remaining)
      (posState r S (out ++ [resultCode (eval g x s (pack g x T) E e p)]) (p + 1) (remaining - 1))
      (exprBudget g E.length e x.length + 4) := by
  let X := posState r S out p remaining
  let v := resultCode (eval g x s (pack g x T) E e p)
  have xe := exprProgram_runs r g x s T E hT hE e X (ready.positions out p remaining)
    p (S (r.get 15)) (by simp [X, posState, Lists.set]) hp
  have hx16 : X (r.get 16) = S (r.get 16) := by simp [X, posState, Lists.set]
  rw [hx16] at xe
  let Y := X.set (r.get 16) (S (r.get 16) ++ [v])
  have xm := nruns_mv (r.get 16) (r.get 25) (r.ne (by decide)) Y
    (l := S (r.get 16)) (v := v) (by simp [Y])
  let Z := (Y.set (r.get 25) (Y (r.get 25) ++ [v])).set (r.get 16) (S (r.get 16))
  have xi := nruns_inc (r.get 15) Z (l := S (r.get 15)) (v := p)
    (by simp [Z, Y, X, posState, Lists.set])
  let W := Z.set (r.get 15) (S (r.get 15) ++ [p + 1])
  have xd := nruns_dec (r.get 28) W (l := S (r.get 28)) (v := remaining)
    (by simp [W, Z, Y, X, posState, Lists.set])
  have he : W.set (r.get 28) (S (r.get 28) ++ [remaining - 1]) =
      posState r S (out ++ [v]) (p + 1) (remaining - 1) := by
    simp only [W, Z, Y, X, posState]
    pos_states r
  rw [he] at xd
  exact xe.seq (xm.seq (xi.seq xd))

def positionLoopP {K : Nat} (r : EvalRegs K) (g : MGrammar) (s : Strategy) (m : Nat) (e : MExp) : NProg K :=
  .loop (r.get 28) .pos (positionBodyP r g s m e)

def positionValues (g : MGrammar) (s : Strategy) (x : List Char) (row E : List Nat) (e : MExp) : List Nat :=
  (List.range (x.length + 1)).map (fun p => resultCode (eval g x s row E e p))

theorem positionLoop_runs {K : Nat} (r : EvalRegs K) (g : MGrammar) (s : Strategy) (x : List Char)
    (T : Nat → List (List Char) → Val) (E : List Nat) (hT : OkTV x.length T)
    (hE : ∀ i ∈ E, i < (spans x.length).length) (e : MExp) (S : Lists K)
    (ready : EvalReady r S x (pack g x T) E) :
    NRuns (positionLoopP r g s E.length e) (posState r S (S (r.get 25)) 0 (x.length + 1))
      (posState r S (S (r.get 25) ++ positionValues g s x (pack g x T) E e) (x.length + 1) 0)
      ((x.length + 1) * (exprBudget g E.length e x.length + 5) + 1) := by
  let F := fun k => posState r S (S (r.get 25) ++
    (List.range k).map (fun p => resultCode (eval g x s (pack g x T) E e p))) k (x.length + 1 - k)
  have hl := nruns_family_const (i := r.get 28) (c := .pos) (p := positionBodyP r g s E.length e)
    F (x.length + 1) (exprBudget g E.length e x.length + 4)
    (by
      intro k hk
      have he : x.length + 1 - k = (x.length - k) + 1 := by omega
      simp [F, posState, Lists.set, NTest.eval, he])
    (by simp [F, posState, Lists.set, NTest.eval])
    (by
      intro k hk
      have xb := positionBody_runs r g s x T E hT hE e S ready
        (S (r.get 25) ++ (List.range k).map (fun p => resultCode (eval g x s (pack g x T) E e p)))
        k (x.length + 1 - k) (by omega)
      have he : posState r S
          ((S (r.get 25) ++ (List.range k).map (fun p => resultCode (eval g x s (pack g x T) E e p))) ++
            [resultCode (eval g x s (pack g x T) E e k)]) (k + 1) (x.length + 1 - k - 1) = F (k + 1) := by
        simp [F, List.range_succ, List.map_append, List.append_assoc, Nat.sub_sub]
      rw [he] at xb
      exact xb)
  simpa [positionLoopP, positionValues, F, Nat.add_assoc] using hl

def positionPrepareP {K : Nat} (r : EvalRegs K) : NProg K :=
  .seq (.prim (.pushZ (r.get 15))) (.seq (.prim (.dup (r.get 20) (r.get 28) (r.ne (by decide))))
    (.prim (.inc (r.get 28))))

theorem positionPrepare_runs {K : Nat} (r : EvalRegs K) (S : Lists K) (n : Nat)
    (hn : S (r.get 20) = [n]) :
    NRuns (positionPrepareP r) S (posState r S (S (r.get 25)) 0 (n + 1)) 3 := by
  have xz := nruns_pushZ (r.get 15) S
  let X := S.set (r.get 15) (S (r.get 15) ++ [0])
  have xd := nruns_dup (r.get 20) (r.get 28) (r.ne (by decide)) X
    (l := []) (v := n) (by simp [X, Lists.set, hn])
  have hx28 : X (r.get 28) = S (r.get 28) := by simp [X, Lists.set]
  rw [hx28] at xd
  let Y := X.set (r.get 28) (S (r.get 28) ++ [n])
  have xi := nruns_inc (r.get 28) Y (l := S (r.get 28)) (v := n) (by simp [Y])
  have he : Y.set (r.get 28) (S (r.get 28) ++ [n + 1]) = posState r S (S (r.get 25)) 0 (n + 1) := by
    simp only [Y, X, posState]
    pos_states r
  rw [he] at xi
  exact xz.seq (xd.seq xi)

def positionCleanupP {K : Nat} (r : EvalRegs K) : NProg K :=
  .seq (.prim (.pop (r.get 28))) (.prim (.pop (r.get 15)))

theorem positionCleanup_runs {K : Nat} (r : EvalRegs K) (S : Lists K) (out : List Nat) (p remaining : Nat) :
    NRuns (positionCleanupP r) (posState r S out p remaining) (S.set (r.get 25) out) 2 := by
  let X := posState r S out p remaining
  have xc := nruns_pop (r.get 28) X (l := S (r.get 28)) (v := remaining) (by simp [X, posState])
  let Y := X.set (r.get 28) (S (r.get 28))
  have xp := nruns_pop (r.get 15) Y (l := S (r.get 15)) (v := p) (by simp [Y, X, posState, Lists.set])
  have he : Y.set (r.get 15) (S (r.get 15)) = S.set (r.get 25) out := by
    simp only [Y, X, posState]
    pos_states r
  rw [he] at xp
  exact xc.seq xp

def positionSweepP {K : Nat} (r : EvalRegs K) (g : MGrammar) (s : Strategy) (m : Nat) (e : MExp) : NProg K :=
  .seq (positionPrepareP r) (.seq (positionLoopP r g s m e) (positionCleanupP r))

def positionSweepCost (g : MGrammar) (m : Nat) (e : MExp) (n : Nat) : Nat :=
  (n + 1) * (exprBudget g m e n + 5) + 6

/-- Generate the complete row of a fixed expression over all valid input positions, in table order. -/
theorem positionSweep_runs {K : Nat} (r : EvalRegs K) (g : MGrammar) (s : Strategy) (x : List Char)
    (T : Nat → List (List Char) → Val) (E : List Nat) (hT : OkTV x.length T)
    (hE : ∀ i ∈ E, i < (spans x.length).length) (e : MExp) (S : Lists K)
    (ready : EvalReady r S x (pack g x T) E) :
    NRuns (positionSweepP r g s E.length e) S
      (S.set (r.get 25) (S (r.get 25) ++ positionValues g s x (pack g x T) E e))
      (positionSweepCost g E.length e x.length) := by
  exact ((positionPrepare_runs r S x.length ready.len).seq
    ((positionLoop_runs r g s x T E hT hE e S ready).seq (positionCleanup_runs r S _ _ _))).mono
      (by unfold positionSweepCost; omega)

theorem positionSweepCost_poly (g : MGrammar) (m : Nat) (e : MExp) : IsPoly (positionSweepCost g m e) :=
  isPoly_add (isPoly_mul (isPoly_add isPoly_id (isPoly_const 1))
    (isPoly_add (exprBudget_poly g m e) (isPoly_const 5))) (isPoly_const 6)

end Shallot.MacroPeg.CBV
