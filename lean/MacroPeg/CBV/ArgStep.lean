import MacroPeg.CBV.MachineBounds

namespace Shallot.MacroPeg.CBV

open Complexity Shallot.MacroPeg.Mach Shallot.MacroPeg.KExp

def evalValues (D n rank p id : Nat) (i : Fin 5) : Nat :=
  match i.val with
  | 0 => D
  | 1 => n
  | 2 => rank
  | 3 => p
  | _ => id

theorem fin5_cases (i : Fin 5) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
  by_cases h0 : i = 0
  · exact Or.inl h0
  by_cases h1 : i = 1
  · exact Or.inr (Or.inl h1)
  by_cases h2 : i = 2
  · exact Or.inr (Or.inr (Or.inl h2))
  by_cases h3 : i = 3
  · exact Or.inr (Or.inr (Or.inr (Or.inl h3)))
  right; right; right; right
  apply Fin.ext
  have hi := i.isLt
  have h0v : i.val ≠ 0 := fun h => h0 (Fin.ext h)
  have h1v : i.val ≠ 1 := fun h => h1 (Fin.ext h)
  have h2v : i.val ≠ 2 := fun h => h2 (Fin.ext h)
  have h3v : i.val ≠ 3 := fun h => h3 (Fin.ext h)
  omega

def argNextState {K : Nat} (r : EvalRegs K) (s : Strategy) (S : Lists K)
    (lp lr : List Nat) (j rank : Nat) : Lists K :=
  if s = .callByValueSeq then (S.set (r.get 21) (lr ++ [rank])).set (r.get 15) (lp ++ [j])
  else S.set (r.get 21) (lr ++ [rank])

theorem EvalReady.argNext {K : Nat} {r : EvalRegs K} {S : Lists K} {x : List Char} {row E : List Nat}
    (h : EvalReady r S x row E) (s : Strategy) (lp lr : List Nat) (j rank : Nat) :
    EvalReady r (argNextState r s S lp lr j rank) x row E := by
  unfold argNextState
  split
  · exact (h.frame 21 (by simp) _).frame 15 (by simp) _
  · exact h.frame 21 (by simp) _

macro "arg_states " r:term : tactic => `(tactic| (
  funext z
  by_cases h15 : z = ($r).get 15
  · subst z; simp_all [Lists.set]
  by_cases h16 : z = ($r).get 16
  · subst z; simp_all [Lists.set]
  by_cases h18 : z = ($r).get 18
  · subst z; simp_all [Lists.set]
  by_cases h21 : z = ($r).get 21
  · subst z; simp_all [Lists.set]
  simp_all [Lists.set]))

/-- A successful argument registers its substring, adds its weighted rank, and advances only in Seq. -/
theorem argSuccess_runs {K : Nat} (r : EvalRegs K) (g : MGrammar) (s : Strategy)
    (S U : Lists K) (x : List Char) (row E : List Nat) (ready : EvalReady r S x row E)
    (p j rank k C : Nat) (lp lr : List Nat)
    (hp : S (r.get 15) = lp ++ [p]) (hr : S (r.get 21) = lr ++ [rank])
    (hpn : p ≤ x.length) (hjn : j ≤ x.length) (hRank : rank ≤ rankCap g x.length)
    (cont : NProg K)
    (hc : NRuns cont (argNextState r s S lp lr j
      (rank + spanId x.length p j * (subStrs x).length ^ k)) U C) :
    NRuns (argSuccessP r s k cont) (S.set (r.get 16) (S (r.get 16) ++ [j + 1])) U
      (registerSpanCost x.length + AddrExpr.cost (fun _ => varsCap g x.length) (rankUpdateExpr k) + 10 + C) := by
  let digit := spanId x.length p j
  let rank' := rank + digit * (subStrs x).length ^ k
  let X := S.set (r.get 16) (S (r.get 16) ++ [j + 2])
  have xi := nruns_inc (r.get 16) (S.set (r.get 16) (S (r.get 16) ++ [j + 1]))
    (l := S (r.get 16)) (v := j + 1) (by simp)
  simp only [Lists.set_set_u] at xi
  have xs := registerSpan_runs r.register X p j x.length
    (lp := lp) (lr := S (r.get 16))
    (by change X (r.get 15) = _; simp [X, Lists.set, hp])
    (by change X (r.get 16) = _; simp [X]) hpn hjn
    (by change X (r.get 17) = _; simp [X, Lists.set, ready.dict])
    (by change X (r.get 1) = _; simp [X, Lists.set, ready.tmp])
    (by change X (r.get 19) = _; simp [X, Lists.set, ready.count])
  change NRuns _ X (X.set (r.get 18) (X (r.get 18) ++ [digit])) _ at xs
  have hx18 : X (r.get 18) = S (r.get 18) := by simp [X, Lists.set]
  rw [hx18] at xs
  let Y := X.set (r.get 18) (S (r.get 18) ++ [digit])
  let f := evalValues (subStrs x).length x.length rank p digit
  have hf : ∀ i, ∃ l, Y (r.address.vars i) = l ++ [f i] := by
    intro i
    rcases fin5_cases i with rfl | rfl | rfl | rfl | rfl
    · refine ⟨[], ?_⟩
      change Y (r.get 19) = [] ++ [(subStrs x).length]
      simp [Y, X, Lists.set, ready.count, spans_length]
    · refine ⟨[], ?_⟩
      change Y (r.get 20) = [] ++ [x.length]
      simp [Y, X, Lists.set, ready.len]
    · refine ⟨lr, ?_⟩
      change Y (r.get 21) = lr ++ [rank]
      simp [Y, X, Lists.set, hr]
    · refine ⟨lp, ?_⟩
      change Y (r.get 15) = lp ++ [p]
      simp [Y, X, Lists.set, hp]
    · refine ⟨S (r.get 18), ?_⟩
      change Y (r.get 18) = S (r.get 18) ++ [digit]
      simp [Y]
  have xr := rankUpdate_runs r Y f k (fun i _ => hf i)
    (by simp [Y, X, Lists.set, ready.tmp]) (lr := lr)
    (by change Y (r.get 21) = lr ++ [rank]; simp [Y, X, Lists.set, hr])
  change NRuns _ Y (Y.set (r.get 21) (lr ++ [rank'])) _ at xr
  let Z := Y.set (r.get 21) (lr ++ [rank'])
  have xd := nruns_pop (r.get 18) Z (l := S (r.get 18)) (v := digit)
    (by simp [Z, Y, Lists.set])
  let W := Z.set (r.get 18) (S (r.get 18))
  have xp := argPosition_runs r s W p j (lp := lp) (lr := S (r.get 16))
    (by simp [W, Z, Y, X, Lists.set, hp]) (by simp [W, Z, Y, X, Lists.set])
  have hout : (if s = .callByValueSeq then
      (W.set (r.get 16) (S (r.get 16))).set (r.get 15) (lp ++ [j])
      else W.set (r.get 16) (S (r.get 16))) = argNextState r s S lp lr j rank' := by
    unfold argNextState
    split <;> simp only [W, Z, Y, X] <;> arg_states r
  rw [hout] at xp
  have hD := length_subStrs_le x
  have hd := spanId_lt (x := x) (j := j) hpn
  have hvars : ∀ i, f i ≤ varsCap g x.length := by
    intro i
    rcases fin5_cases i with rfl | rfl | rfl | rfl | rfl
    · change (subStrs x).length ≤ varsCap g x.length
      unfold varsCap dictCap; omega
    · change x.length ≤ varsCap g x.length
      unfold varsCap; omega
    · change rank ≤ varsCap g x.length
      unfold varsCap; omega
    · change p ≤ varsCap g x.length
      unfold varsCap; omega
    · change digit ≤ varsCap g x.length
      dsimp [digit]
      unfold varsCap dictCap; omega
  have hcost := AddrExpr.cost_mono hvars (rankUpdateExpr k)
  exact (xi.seq (xs.seq (xr.seq (xd.seq (xp.seq hc))))).mono (by omega)

/-- The argument branch preserves both early exits, and continues only after a successfully registered value. -/
theorem argAfter_runs {K : Nat} (r : EvalRegs K) (g : MGrammar) (s : Strategy)
    (S : Lists K) (U : Nat → Lists K) (x : List Char) (row E : List Nat) (ready : EvalReady r S x row E)
    (p rank k C : Nat) (lp lr : List Nat) (u : Res)
    (hp : S (r.get 15) = lp ++ [p]) (hr : S (r.get 21) = lr ++ [rank])
    (hpn : p ≤ x.length) (hu : ∀ j, u = some (some j) → j ≤ x.length)
    (hRank : rank ≤ rankCap g x.length) (cont : NProg K)
    (hc : ∀ j, u = some (some j) → NRuns cont (argNextState r s S lp lr j
      (rank + spanId x.length p j * (subStrs x).length ^ k)) (U j) C) :
    NRuns (argAfterP r s k cont) (S.set (r.get 16) (S (r.get 16) ++ [resultCode u]))
      (match u with | some (some j) => U j | _ => S.set (r.get 16) (S (r.get 16) ++ [resultCode u]))
      (rankStepCost g k x.length + C) := by
  let o := r.get 16
  cases u with
  | none =>
    have hx := (nruns_skip o (S.set o (S o ++ [0]))).iteT (i := o) (c := .zero)
      (q := .seq (.prim (.dec o)) (.ite o .zero (.prim (.inc o)) (argSuccessP r s k cont)))
      (by simp [NTest.eval])
    simpa only [argAfterP, o, resultCode] using hx.mono (by unfold rankStepCost; omega)
  | some u => cases u with
    | none =>
      let X := S.set o (S o ++ [1])
      have xd := nruns_dec o X (l := S o) (v := 1) (by simp [X])
      simp only [X, Lists.set_set_u, Nat.reduceSub] at xd
      let Y := S.set o (S o ++ [0])
      have xi := nruns_inc o Y (l := S o) (v := 0) (by simp [Y])
      simp only [Y, Lists.set_set_u, Nat.reduceAdd] at xi
      have xb := xi.iteT (i := o) (c := .zero) (q := argSuccessP r s k cont) (by simp [Y, NTest.eval])
      have hx := (xd.seq xb).iteF (i := o) (c := .zero) (p := nskip o) (by simp [X, NTest.eval])
      simpa only [argAfterP, X, o, resultCode, Lists.set_set_u] using hx.mono (by unfold rankStepCost; omega)
    | some j =>
      let X := S.set o (S o ++ [j + 2])
      have xd := nruns_dec o X (l := S o) (v := j + 2) (by simp [X])
      simp only [X, Lists.set_set_u, show j + 2 - 1 = j + 1 by omega] at xd
      have xs := argSuccess_runs r g s S (U j) x row E ready p j rank k C lp lr hp hr hpn
        (hu j rfl) hRank cont (hc j rfl)
      have xb := xs.iteF (i := o) (c := .zero) (p := .prim (.inc o)) (by simp [o, NTest.eval])
      have hx := (xd.seq xb).iteF (i := o) (c := .zero) (p := nskip o) (by simp [X, NTest.eval])
      simpa only [argAfterP, X, o, resultCode] using hx.mono (by unfold rankStepCost; omega)

end Shallot.MacroPeg.CBV
