import MacroPeg.CBV.ExprState

namespace Shallot.MacroPeg.CBV

open Complexity Shallot.MacroPeg.KExp

/-- A call's private rank and position frames may nest above arbitrary caller prefixes. -/
def callState {K : Nat} (r : EvalRegs K) (S : Lists K) (p rank : Nat) : Lists K :=
  (S.set (r.get 21) (S (r.get 21) ++ [rank])).set (r.get 15) (S (r.get 15) ++ [p])

theorem EvalReady.call {K : Nat} {r : EvalRegs K} {S : Lists K} {x : List Char} {row E : List Nat}
    (h : EvalReady r S x row E) (p rank : Nat) : EvalReady r (callState r S p rank) x row E :=
  (h.frame 21 (by simp) _).frame 15 (by simp) _

theorem callPrepare_runs {K : Nat} (r : EvalRegs K) (S : Lists K) (p : Nat)
    {lp : List Nat} (hp : S (r.get 15) = lp ++ [p]) :
    NRuns (callPrepareP r) S (callState r S p 0) 4 := by
  have xz := nruns_pushZ (r.get 21) S
  let X := S.set (r.get 21) (S (r.get 21) ++ [0])
  have xd := nruns_dup (r.get 15) (r.get 3) (r.ne (by decide)) X (l := lp) (v := p)
    (by simp [X, Lists.set, hp])
  have hx3 : X (r.get 3) = S (r.get 3) := by simp [X, Lists.set]
  rw [hx3] at xd
  let Y := X.set (r.get 3) (S (r.get 3) ++ [p])
  have xm := nruns_mv (r.get 3) (r.get 15) (r.ne (by decide)) Y
    (l := S (r.get 3)) (v := p) (by simp [Y])
  have he : (Y.set (r.get 15) (Y (r.get 15) ++ [p])).set (r.get 3) (S (r.get 3)) = callState r S p 0 := by
    funext z
    by_cases h3 : z = r.get 3
    · subst z; simp [Y, X, callState, Lists.set]
    by_cases h15 : z = r.get 15
    · subst z; simp [Y, X, callState, Lists.set]
    by_cases h21 : z = r.get 21
    · subst z; simp [Y, X, callState, Lists.set]
    simp [Y, X, callState, Lists.set, h3, h15, h21]
  rw [he] at xm
  exact xz.seq (xd.seq xm)

theorem callCleanup_runs {K : Nat} (r : EvalRegs K) (S : Lists K) (p rank v : Nat) :
    NRuns (callCleanupP r) ((callState r S p rank).set (r.get 16) (S (r.get 16) ++ [v]))
      (S.set (r.get 16) (S (r.get 16) ++ [v])) 2 := by
  let X := (callState r S p rank).set (r.get 16) (S (r.get 16) ++ [v])
  have xp := nruns_pop (r.get 15) X (l := S (r.get 15)) (v := p)
    (by simp [X, callState, Lists.set])
  let Y := X.set (r.get 15) (S (r.get 15))
  have xr := nruns_pop (r.get 21) Y (l := S (r.get 21)) (v := rank)
    (by simp [Y, X, callState, Lists.set])
  have he : Y.set (r.get 21) (S (r.get 21)) = S.set (r.get 16) (S (r.get 16) ++ [v]) := by
    funext z
    by_cases h15 : z = r.get 15
    · subst z; simp [Y, X, callState, Lists.set]
    by_cases h16 : z = r.get 16
    · subst z; simp [Y, X, callState, Lists.set]
    by_cases h21 : z = r.get 21
    · subst z; simp [Y, X, callState, Lists.set]
    simp [Y, X, callState, Lists.set, h15, h16, h21]
  rw [he] at xr
  exact xp.seq xr

/-- Par removes only the argument result; Seq also replaces the current private cursor. -/
theorem argPosition_runs {K : Nat} (r : EvalRegs K) (s : Strategy) (S : Lists K) (p j : Nat)
    {lp lr : List Nat} (hp : S (r.get 15) = lp ++ [p]) (hr : S (r.get 16) = lr ++ [j + 2]) :
    NRuns (argPositionP r s) S
      (if s = .callByValueSeq then (S.set (r.get 16) lr).set (r.get 15) (lp ++ [j])
       else S.set (r.get 16) lr) 5 := by
  cases s with
  | callByName | callByValuePar =>
    simpa [argPositionP] using
      (nruns_pop (r.get 16) S hr).mono (by omega)
  | callByValueSeq =>
    simp only [argPositionP, if_true]
    have xd := nruns_dec (r.get 16) S hr
    simp only [show j + 2 - 1 = j + 1 by omega] at xd
    let X := S.set (r.get 16) (lr ++ [j + 1])
    have xe := nruns_dec (r.get 16) X (l := lr) (v := j + 1) (by simp [X])
    simp only [Nat.add_sub_cancel] at xe
    let Y := X.set (r.get 16) (lr ++ [j])
    have xp := nruns_pop (r.get 15) Y (l := lp) (v := p) (by simp [Y, X, Lists.set, hp])
    let Z := Y.set (r.get 15) lp
    have xm := nruns_mv (r.get 16) (r.get 15) (r.ne (by decide)) Z
      (l := lr) (v := j) (by simp [Z, Y, Lists.set])
    have he : (Z.set (r.get 15) (Z (r.get 15) ++ [j])).set (r.get 16) lr =
        (S.set (r.get 16) lr).set (r.get 15) (lp ++ [j]) := by
      funext z
      by_cases h15 : z = r.get 15
      · subst z; simp [Z, Y, X, Lists.set]
      by_cases h16 : z = r.get 16
      · subst z; simp [Z, Y, X, Lists.set]
      simp [Z, Y, X, Lists.set, h15, h16]
    rw [he] at xm
    exact xd.seq (xe.seq (xp.seq xm))

end Shallot.MacroPeg.CBV
