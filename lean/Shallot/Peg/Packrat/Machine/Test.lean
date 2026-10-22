import Shallot.Peg.Packrat.Machine.Not

/-!
# Finite tests compiled into stack programs

A fixed Boolean table becomes a concrete branch tree. Entries beyond the
finite table use a fixed default. No semantic predicate is called by the
machine at runtime. The tested number is consumed before either branch.
-/

namespace Shallot.Packrat.Machine

open Complexity

variable {K : Nat}

/-- Branch using a fixed finite Boolean table, consuming the top number. -/
def dispatch (work : Fin K) (flags : List Bool) (fallback : Bool) (yes no : NProg K) : NProg K :=
  caseTop work (flags.map fun b => if b then yes else no)
    (.seq (.prim (.pop work)) (if fallback then yes else no))

private theorem default_runs (work : Fin K) : ∀ (ps : List (NProg K)) (q : NProg K)
    (v : Nat) (S : Lists K) (lw : List Nat), S work = lw ++ [v + ps.length] →
    ∀ (S' : Lists K) (T : Nat), NRuns q (S.set work (lw ++ [v])) S' T →
      NRuns (caseTop work ps q) S S' (T + 2 * ps.length)
  | [], _, _, S, lw, hw, _, _, h => by
    simp only [List.length_nil, Nat.add_zero] at hw ⊢
    simpa only [← hw, Lists.set_get_self, caseTop, Nat.mul_zero, Nat.add_zero] using h
  | p :: ps, q, v, S, lw, hw, S', T, h => by
    have hw' : S work = lw ++ [(v + ps.length) + 1] := by simpa [Nat.add_assoc] using hw
    have dc := nruns_dec work S hw'
    simp only [Nat.add_one_sub_one] at dc
    have hh := default_runs work ps q v (S.set work (lw ++ [v + ps.length])) lw (by simp) S' T
      (by simpa only [Lists.set_set_u] using h)
    exact ((dc.seq hh).iteF (i := work) (c := .zero) (by rw [hw']; simp)).mono (by
      simp only [List.length_cons]; omega)

/-- Execute the selected branch after removing the tested value. -/
theorem nruns_dispatch (work : Fin K) (flags : List Bool) (fallback : Bool)
    (yes no : NProg K) (S S' : Lists K) {lw : List Nat} {v T : Nat}
    (hw : S work = lw ++ [v])
    (h : NRuns (if (flags[v]?).getD fallback then yes else no) (S.set work lw) S' T) :
    NRuns (dispatch work flags fallback yes no) S S' (T + 2 * flags.length + 3) := by
  by_cases hv : v < flags.length
  · have hp : v < (flags.map fun b => if b then yes else no).length := by simpa using hv
    have hh := caseTop_runs work (flags.map fun b => if b then yes else no)
      (.seq (.prim (.pop work)) (if fallback then yes else no)) v hp S lw hw S' T
      (by simpa only [List.getElem_map, List.getElem?_eq_getElem hv, Option.getD_some] using h)
    exact hh.mono (by omega)
  · have hh : (flags[v]?).getD fallback = fallback := by
      rw [List.getElem?_eq_none (by omega)]; rfl
    rw [hh] at h
    let S₁ := S.set work (lw ++ [v - flags.length])
    have pp := nruns_pop work S₁ (l := lw) (v := v - flags.length) (by simp [S₁])
    have hb : NRuns (if fallback then yes else no) (S₁.set work lw) S' T := by
      simpa only [S₁, Lists.set_set_u] using h
    have hd := default_runs work (flags.map fun b => if b then yes else no)
      (.seq (.prim (.pop work)) (if fallback then yes else no)) (v - flags.length) S lw
      (by simpa only [List.length_map, show v - flags.length + flags.length = v by omega] using hw) S' (1 + T) (pp.seq hb)
    exact hd.mono (by simp only [List.length_map]; omega)

/-- Read a symbol row and branch, restoring the work stack before the branch. -/
def readTest (r tmp idx p work : Fin K) (hrT : r ≠ tmp) (hTw : tmp ≠ work)
    (hpi : p ≠ idx) (flags : List Bool) (fallback : Bool) (yes no : NProg K) : NProg K :=
  .seq (readRow r tmp idx p work hrT hTw hpi) (dispatch work flags fallback yes no)

theorem nruns_readTest (r tmp idx p work : Fin K) (hrT : r ≠ tmp) (hTw : tmp ≠ work)
    (hpi : p ≠ idx) (hd : [r, tmp, idx, p, work].Nodup) (flags : List Bool) (fallback : Bool)
    (yes no : NProg K) (S S' : Lists K) (hT : S tmp = []) {lp : List Nat} {i T : Nat}
    (hp : S p = lp ++ [i]) (hi : i < (S r).length)
    (h : NRuns (if (flags[(S r)[i]]?).getD fallback then yes else no) S S' T) :
    NRuns (readTest r tmp idx p work hrT hTw hpi flags fallback yes no) S S'
      (6 * (S r).length + 4 * i + 2 * flags.length + T + 10) := by
  have rd := nruns_readRow r tmp idx p work hrT hTw hpi hd S hT hp hi
  let S₁ := S.set work (S work ++ [(S r)[i]])
  have br := nruns_dispatch work flags fallback yes no S₁ S'
    (lw := S work) (v := (S r)[i]) (by simp [S₁])
    (by simpa only [S₁, Lists.set_set_u, Lists.set_get_self] using h)
  exact (rd.seq br).mono (by omega)

end Shallot.Packrat.Machine
