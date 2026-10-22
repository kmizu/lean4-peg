import Shallot.Peg.Packrat.Machine.Read

/-!
# Negative lookahead on the stack machine

The predicate preserves unknown, turns failure into empty success, and
turns success into failure. In particular, divergence is never mistaken
for a failed match.
-/

namespace Shallot.Packrat.Machine

open Complexity

variable {K : Nat}

/-- Append success ending at the position currently on `p`. -/
def emptySuccess (p out : Fin K) (hpo : p ≠ out) : NProg K :=
  .seq (.prim (.dup p out hpo)) (.seq (.prim (.inc out)) (.prim (.inc out)))

theorem nruns_emptySuccess (p out : Fin K) (hpo : p ≠ out) (S : Lists K)
    {lp : List Nat} {i : Nat} (hp : S p = lp ++ [i]) :
    NRuns (emptySuccess p out hpo) S (S.set out (S out ++ [i + 2])) 3 := by
  have x₁ := nruns_dup p out hpo S hp
  have x₂ := nruns_inc out (S.set out (S out ++ [i])) (l := S out) (v := i) (by simp)
  have x₃ := nruns_inc out ((S.set out (S out ++ [i])).set out (S out ++ [i + 1]))
    (l := S out) (v := i + 1) (by simp)
  simp only [Lists.set_set_u] at x₂ x₃
  exact x₁.seq (x₂.seq x₃)

/-- Numeric result of negative lookahead at position `i`. -/
def notValue (i : Nat) : Nat → Nat
  | 0 => 0
  | 1 => i + 2
  | _ => 1

/-- Consume a result on `work` and append its negative predicate to `out`. -/
def negate (p work out : Fin K) (hpo : p ≠ out) (hwo : work ≠ out) : NProg K :=
  .ite work .zero (nmv work out hwo)
    (.seq (.prim (.dec work))
      (.ite work .zero (.seq (.prim (.pop work)) (emptySuccess p out hpo))
        (.seq (.prim (.pop work)) (npushC out 1))))

theorem nruns_negate (p work out : Fin K) (hpo : p ≠ out) (hwo : work ≠ out)
    (hpw : p ≠ work) (S : Lists K) {lp lw : List Nat} {i a : Nat}
    (hp : S p = lp ++ [i]) (hw : S work = lw ++ [a]) :
    NRuns (negate p work out hpo hwo) S
      ((S.set work lw).set out (S out ++ [notValue i a])) 7 := by
  cases a with
  | zero =>
    have mv := nruns_mv work out hwo S hw
    have he : (S.set out (S out ++ [0])).set work lw = (S.set work lw).set out (S out ++ [0]) := by
      lists_eq
    rw [he] at mv
    exact (mv.iteT (i := work) (c := .zero) (by rw [hw]; simp)).mono (by omega)
  | succ a =>
    have dc := nruns_dec work S hw
    simp only [Nat.add_one_sub_one] at dc
    let S₁ := S.set work (lw ++ [a])
    have hw₁ : S₁ work = lw ++ [a] := Lists.set_same _ _ _
    have pp := nruns_pop work S₁ hw₁
    have hp₁ : (S₁.set work lw) p = lp ++ [i] := by
      simp only [S₁, Lists.set_ne _ _ hpw]; exact hp
    cases a with
    | zero =>
      have es := nruns_emptySuccess p out hpo (S₁.set work lw) hp₁
      have he : (S₁.set work lw).set out ((S₁.set work lw) out ++ [i + 2]) =
          (S.set work lw).set out (S out ++ [i + 2]) := by
        simp only [S₁]; lists_eq
      rw [he] at es
      have br := (pp.seq es).iteT (i := work) (c := .zero)
        (q := .seq (.prim (.pop work)) (npushC out 1)) (by rw [hw₁]; simp)
      exact ((dc.seq br).iteF (p := nmv work out hwo) (i := work) (c := .zero)
        (by rw [hw]; simp)).mono (by omega)
    | succ a =>
      have pc := nruns_pushC out (S₁.set work lw) 1
      have he : (S₁.set work lw).set out ((S₁.set work lw) out ++ [1]) =
          (S.set work lw).set out (S out ++ [1]) := by
        simp only [S₁]; lists_eq
      rw [he] at pc
      have br := (pp.seq pc).iteF (i := work) (c := .zero)
        (p := .seq (.prim (.pop work)) (emptySuccess p out hpo)) (by rw [hw₁]; simp)
      exact ((dc.seq br).iteF (p := nmv work out hwo) (i := work) (c := .zero)
        (by rw [hw]; simp)).mono (by omega)

/-- Read one row and compute its negative predicate. -/
def notCell (r tmp idx p work out : Fin K) (hrT : r ≠ tmp) (hTw : tmp ≠ work)
    (hpi : p ≠ idx) (hpo : p ≠ out) (hwo : work ≠ out) : NProg K :=
  .seq (readRow r tmp idx p work hrT hTw hpi) (negate p work out hpo hwo)

/-- Lookahead changes only the output and uses a linear number of stack steps. -/
theorem nruns_notCell (r tmp idx p work out : Fin K) (hrT : r ≠ tmp) (hTw : tmp ≠ work)
    (hpi : p ≠ idx) (hpo : p ≠ out) (hwo : work ≠ out)
    (hd : [r, tmp, idx, p, work].Nodup) (S : Lists K) (hT : S tmp = [])
    {lp : List Nat} {i : Nat} (hp : S p = lp ++ [i]) (hi : i < (S r).length) :
    NRuns (notCell r tmp idx p work out hrT hTw hpi hpo hwo) S
      (S.set out (S out ++ [notValue i ((S r)[i])])) (6 * (S r).length + 4 * i + 14) := by
  have hpw : p ≠ work := by simp_all [List.nodup_cons]
  have how : out ≠ work := Ne.symm hwo
  have rd := nruns_readRow r tmp idx p work hrT hTw hpi hd S hT hp hi
  let S₁ := S.set work (S work ++ [(S r)[i]])
  have ng := nruns_negate p work out hpo hwo hpw S₁
    (lp := lp) (lw := S work) (i := i) (a := (S r)[i])
    (by simp only [S₁, Lists.set_ne _ _ hpw]; exact hp) (by simp [S₁])
  have he : (S₁.set work (S work)).set out (S₁ out ++ [notValue i ((S r)[i])]) =
      S.set out (S out ++ [notValue i ((S r)[i])]) := by
    simp only [S₁, Lists.set_ne _ _ how, Lists.set_set_u, Lists.set_get_self]
  rw [he] at ng
  exact (rd.seq ng).mono (by omega)

/-- Numeric negative lookahead commutes with the original table step. -/
theorem notValue_code (g : Grammar) (x : List Char) (T : Tbl) (e : PExp) (i : Nat) :
    notValue i (code i (T e i)) = code i (F g x T (.notP e) i) := by
  simp only [F]
  cases T e i with
  | none => rfl
  | some r => cases r <;> simp only [code, notValue, Nat.add_succ, Nat.add_zero]

/-- On verified rows, negative lookahead costs at most `10 |x| + 20` stack steps. -/
theorem nruns_notCell_round (g : Grammar) (x : List Char) (n : Nat) (e : PExp)
    (r tmp idx p work out : Fin K) (hrT : r ≠ tmp) (hTw : tmp ≠ work)
    (hpi : p ≠ idx) (hpo : p ≠ out) (hwo : work ≠ out)
    (hd : [r, tmp, idx, p, work].Nodup) (S : Lists K) (hT : S tmp = [])
    (hr : S r = row (iter g x n) e x.length) {lp : List Nat} {i : Nat}
    (hp : S p = lp ++ [i]) (hi : i ≤ x.length) :
    NRuns (notCell r tmp idx p work out hrT hTw hpi hpo hwo) S
      (S.set out (S out ++ [code i (iter g x (n + 1) (.notP e) i)]))
      (10 * x.length + 20) := by
  have hri : i < (S r).length := by simp only [hr, row_length]; omega
  have hv : (S r)[i] = code i (iter g x n e i) := by simp only [hr, row_get _ _ _ _ hi]
  have hx := nruns_notCell r tmp idx p work out hrT hTw hpi hpo hwo hd S hT hp hri
  have he : notValue i ((S r)[i]) = code i (iter g x (n + 1) (.notP e) i) := by
    rw [hv]
    exact notValue_code g x (iter g x n) e i
  rw [he] at hx
  apply hx.mono
  have hl : (S r).length = x.length + 1 := by simp [hr]
  omega

end Shallot.Packrat.Machine
