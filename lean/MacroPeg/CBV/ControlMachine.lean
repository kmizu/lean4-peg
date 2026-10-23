import MacroPeg.CBV.LexMachine

namespace Shallot.MacroPeg.CBV

open Complexity Shallot.Packrat.Machine Shallot.MacroPeg.KExp

/-- Retry only an explicit failure; the unknown result is preserved. -/
def altAfterP {K : Nat} (out : Fin K) (right : NProg K) : NProg K :=
  .ite out .zero (nskip out)
    (.seq (.prim (.dec out)) (.ite out .zero
      (.seq (.prim (.pop out)) right) (.prim (.inc out))))

theorem altAfter_runs {K : Nat} (out : Fin K) (right : NProg K) (S : Lists K) (v w T : Nat)
    (hr : NRuns right S (S.set out (S out ++ [w])) T) :
    NRuns (altAfterP out right) (S.set out (S out ++ [v]))
      (S.set out (S out ++ [if v = 1 then w else v])) (T + 5) := by
  let X := S.set out (S out ++ [v])
  cases v with
  | zero =>
    have hx := (nruns_skip out X).iteT (i := out) (c := .zero)
      (q := .seq (.prim (.dec out)) (.ite out .zero
        (.seq (.prim (.pop out)) right) (.prim (.inc out))))
      (by simp [X, NTest.eval])
    simpa only [altAfterP, X, Nat.zero_ne_one, if_false] using hx.mono (by omega)
  | succ v =>
    have xd := nruns_dec out X (l := S out) (v := v + 1) (by simp [X])
    simp only [X, Lists.set_set_u, Nat.add_sub_cancel] at xd
    let Y := S.set out (S out ++ [v])
    cases v with
    | zero =>
      have xp := nruns_pop out Y (l := S out) (v := 0) (by simp [Y])
      simp only [Y, Lists.set_set_u, Lists.set_get_self] at xp
      have xb := (xp.seq hr).iteT (i := out) (c := .zero) (q := .prim (.inc out))
        (by simp [Y, NTest.eval])
      have hx := (xd.seq xb).iteF (i := out) (c := .zero) (p := nskip out)
        (by simp [X, NTest.eval])
      simpa only [altAfterP, X, Nat.reduceAdd, if_true] using hx.mono (by omega)
    | succ v =>
      have xi := nruns_inc out Y (l := S out) (v := v + 1) (by simp [Y])
      simp only [Y, Lists.set_set_u] at xi
      have xb := xi.iteF (i := out) (c := .zero) (p := .seq (.prim (.pop out)) right)
        (by simp [Y, NTest.eval])
      have hx := (xd.seq xb).iteF (i := out) (c := .zero) (p := nskip out)
        (by simp [X, NTest.eval])
      simpa only [altAfterP, X, show v + 1 + 1 ≠ 1 by omega, if_false] using hx.mono (by omega)

def altEvalP {K : Nat} (out : Fin K) (left right : NProg K) : NProg K :=
  .seq left (altAfterP out right)

/-- Compositional choice rule, charging both possible evaluations and the actual branch overhead. -/
theorem altEval_runs {K : Nat} (out : Fin K) (left right : NProg K) (S : Lists K) (v w A B : Nat)
    (hl : NRuns left S (S.set out (S out ++ [v])) A)
    (hr : NRuns right S (S.set out (S out ++ [w])) B) :
    NRuns (altEvalP out left right) S (S.set out (S out ++ [if v = 1 then w else v])) (A + B + 5) := by
  exact (hl.seq (altAfter_runs out right S v w B hr)).mono (by omega)

/-- Map failure to empty success, success to failure, and preserve unknown. -/
def notAfterP {K : Nat} (r : LiteralRegs K) : NProg K :=
  .ite (r.get 16) .zero (nskip (r.get 16))
    (.seq (.prim (.dec (r.get 16))) (.ite (r.get 16) .zero
      (.seq (.prim (.pop (r.get 16))) (emptySuccess (r.get 15) (r.get 16) (r.ne (by decide))))
      (.seq (.prim (.pop (r.get 16))) (npushC (r.get 16) 1))))

theorem notAfter_runs {K : Nat} (r : LiteralRegs K) (S : Lists K) (v q : Nat)
    {lp : List Nat} (hp : S (r.get 15) = lp ++ [q]) :
    NRuns (notAfterP r) (S.set (r.get 16) (S (r.get 16) ++ [v]))
      (S.set (r.get 16) (S (r.get 16) ++ [if v = 0 then 0 else if v = 1 then q + 2 else 1])) 8 := by
  let o := r.get 16
  let X := S.set o (S o ++ [v])
  cases v with
  | zero =>
    have hx := (nruns_skip o X).iteT (i := o) (c := .zero)
      (q := .seq (.prim (.dec o)) (.ite o .zero
        (.seq (.prim (.pop o)) (emptySuccess (r.get 15) o (r.ne (by decide))))
        (.seq (.prim (.pop o)) (npushC o 1))))
      (by simp [X, NTest.eval])
    simpa only [notAfterP, o, X, if_true] using hx.mono (by omega)
  | succ v =>
    have xd := nruns_dec o X (l := S o) (v := v + 1) (by simp [X])
    simp only [X, Lists.set_set_u, Nat.add_sub_cancel] at xd
    let Y := S.set o (S o ++ [v])
    have xp := nruns_pop o Y (l := S o) (v := v) (by simp [Y])
    simp only [Y, Lists.set_set_u, Lists.set_get_self] at xp
    cases v with
    | zero =>
      have xe := nruns_emptySuccess (r.get 15) o (r.ne (by decide)) S hp
      have xb := (xp.seq xe).iteT (i := o) (c := .zero)
        (q := .seq (.prim (.pop o)) (npushC o 1))
        (by simp [Y, NTest.eval])
      have hx := (xd.seq xb).iteF (i := o) (c := .zero) (p := nskip o)
        (by simp [X, NTest.eval])
      simpa only [notAfterP, o, X, Nat.reduceAdd, Nat.one_ne_zero, if_false, if_true] using hx.mono (by omega)
    | succ v =>
      have xb := (xp.seq (nruns_pushC o S 1)).iteF (i := o) (c := .zero)
        (p := .seq (.prim (.pop o)) (emptySuccess (r.get 15) o (r.ne (by decide))))
        (by simp [Y, NTest.eval])
      have hx := (xd.seq xb).iteF (i := o) (c := .zero) (p := nskip o)
        (by simp [X, NTest.eval])
      simpa only [notAfterP, o, X, show v + 1 + 1 ≠ 0 by omega,
        show v + 1 + 1 ≠ 1 by omega, if_false] using hx.mono (by omega)

def seqSuccessP {K : Nat} (r : LiteralRegs K) (right : NProg K) : NProg K :=
  .seq (.prim (.dec (r.get 16)))
    (.seq (nmv (r.get 16) (r.get 15) (r.ne (by decide)))
      (.seq right (.prim (.pop (r.get 15)))))

/-- Decode a success, evaluate the right expression at its returned position, and restore the caller's position. -/
theorem seqSuccess_runs {K : Nat} (r : LiteralRegs K) (right : NProg K) (S : Lists K)
    (j w T : Nat)
    (hr : NRuns right (S.set (r.get 15) (S (r.get 15) ++ [j]))
      ((S.set (r.get 15) (S (r.get 15) ++ [j])).set (r.get 16) (S (r.get 16) ++ [w])) T) :
    NRuns (seqSuccessP r right) (S.set (r.get 16) (S (r.get 16) ++ [j + 1]))
      (S.set (r.get 16) (S (r.get 16) ++ [w])) (T + 4) := by
  let X := S.set (r.get 16) (S (r.get 16) ++ [j + 1])
  have xd := nruns_dec (r.get 16) X (l := S (r.get 16)) (v := j + 1) (by simp [X])
  simp only [X, Lists.set_set_u, Nat.add_sub_cancel] at xd
  let Y := S.set (r.get 16) (S (r.get 16) ++ [j])
  have xm := nruns_mv (r.get 16) (r.get 15) (r.ne (by decide)) Y
    (l := S (r.get 16)) (v := j) (by simp [Y])
  have he : (Y.set (r.get 15) (Y (r.get 15) ++ [j])).set (r.get 16) (S (r.get 16)) =
      S.set (r.get 15) (S (r.get 15) ++ [j]) := by
    funext z
    by_cases ho : z = r.get 16
    · subst z; simp [Y, Lists.set]
    by_cases hp : z = r.get 15
    · subst z; simp [Y, Lists.set]
    simp [Y, Lists.set, ho, hp]
  rw [he] at xm
  let Z := (S.set (r.get 15) (S (r.get 15) ++ [j])).set (r.get 16) (S (r.get 16) ++ [w])
  have xp := nruns_pop (r.get 15) Z (l := S (r.get 15)) (v := j) (by simp [Z, Lists.set])
  have hout : Z.set (r.get 15) (S (r.get 15)) = S.set (r.get 16) (S (r.get 16) ++ [w]) := by
    funext z
    by_cases ho : z = r.get 16
    · subst z; simp [Z, Lists.set]
    by_cases hp : z = r.get 15
    · subst z; simp [Z, Lists.set]
    simp [Z, Lists.set, ho, hp]
  rw [hout] at xp
  exact (xd.seq (xm.seq (hr.seq xp))).mono (by omega)

def seqAfterP {K : Nat} (r : LiteralRegs K) (right : NProg K) : NProg K :=
  .ite (r.get 16) .zero (nskip (r.get 16))
    (.seq (.prim (.dec (r.get 16))) (.ite (r.get 16) .zero
      (.prim (.inc (r.get 16))) (seqSuccessP r right)))

theorem seqAfter_runs {K : Nat} (r : LiteralRegs K) (right : NProg K) (S : Lists K)
    (u : Res) (f : Nat → Nat) (T : Nat)
    (hr : ∀ j, u = some (some j) → NRuns right (S.set (r.get 15) (S (r.get 15) ++ [j]))
      ((S.set (r.get 15) (S (r.get 15) ++ [j])).set (r.get 16) (S (r.get 16) ++ [f j])) T) :
    NRuns (seqAfterP r right) (S.set (r.get 16) (S (r.get 16) ++ [resultCode u]))
      (S.set (r.get 16) (S (r.get 16) ++ [match u with | some (some j) => f j | _ => resultCode u]))
      (T + 7) := by
  let o := r.get 16
  cases u with
  | none =>
    have hx := (nruns_skip o (S.set o (S o ++ [0]))).iteT (i := o) (c := .zero)
      (q := .seq (.prim (.dec o)) (.ite o .zero (.prim (.inc o)) (seqSuccessP r right)))
      (by simp [NTest.eval])
    simpa only [seqAfterP, o, resultCode] using hx.mono (by omega)
  | some u =>
    cases u with
    | none =>
      let X := S.set o (S o ++ [1])
      have xd := nruns_dec o X (l := S o) (v := 1) (by simp [X])
      simp only [X, Lists.set_set_u, Nat.reduceSub] at xd
      let Y := S.set o (S o ++ [0])
      have xi := nruns_inc o Y (l := S o) (v := 0) (by simp [Y])
      simp only [Y, Lists.set_set_u, Nat.reduceAdd] at xi
      have xb := xi.iteT (i := o) (c := .zero) (q := seqSuccessP r right) (by simp [Y, NTest.eval])
      have hx := (xd.seq xb).iteF (i := o) (c := .zero) (p := nskip o) (by simp [X, NTest.eval])
      simpa only [seqAfterP, X, o, resultCode] using hx.mono (by omega)
    | some j =>
      let X := S.set o (S o ++ [j + 2])
      have xd := nruns_dec o X (l := S o) (v := j + 2) (by simp [X])
      simp only [X, Lists.set_set_u, show j + 2 - 1 = j + 1 by omega] at xd
      have xs := seqSuccess_runs r right S j (f j) T (hr j rfl)
      have xb := xs.iteF (i := o) (c := .zero) (p := .prim (.inc o)) (by simp [o, NTest.eval])
      have hx := (xd.seq xb).iteF (i := o) (c := .zero) (p := nskip o) (by simp [X, NTest.eval])
      simpa only [seqAfterP, X, o, resultCode] using hx.mono (by omega)

end Shallot.MacroPeg.CBV
