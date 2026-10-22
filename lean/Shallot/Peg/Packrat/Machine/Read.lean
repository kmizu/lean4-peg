import Shallot.Peg.Packrat.Machine.Code
import Complexity.NTable

/-!
# Reading numeric rows on a concrete stack machine

Rows are stacks with entry zero at the bottom. The position is copied to
the existing verified `peekAt` program, so every lookup preserves the row
and the position, restores its scratch stacks, and appends one result.
-/

namespace Shallot.Packrat.Machine

open Complexity

variable {K : Nat}

/-- Read a row at the position on `p`, without consuming that position. -/
def readRow (r tmp idx p out : Fin K) (hrT : r ≠ tmp) (hTo : tmp ≠ out)
    (hpi : p ≠ idx) : NProg K :=
  .seq (.prim (.dup p idx hpi)) (peekAt r tmp idx out hrT hTo)

/-- A concrete row lookup preserves everything except its output stack. -/
theorem nruns_readRow (r tmp idx p out : Fin K) (hrT : r ≠ tmp) (hTo : tmp ≠ out)
    (hpi : p ≠ idx) (hd : [r, tmp, idx, p, out].Nodup) (S : Lists K)
    (hT : S tmp = []) {lp : List Nat} {i : Nat} (hp : S p = lp ++ [i])
    (hi : i < (S r).length) :
    NRuns (readRow r tmp idx p out hrT hTo hpi) S
      (S.set out (S out ++ [(S r)[i]])) (6 * (S r).length + 4 * i + 7) := by
  have hd' : [r, tmp, idx, out].Nodup := by
    simp_all [List.nodup_cons]
  have htr : tmp ≠ idx := by simp_all [List.nodup_cons]
  have hrr : r ≠ idx := by simp_all [List.nodup_cons]
  have hor : out ≠ idx := Ne.symm (by simp_all [List.nodup_cons])
  have x₁ := nruns_dup p idx hpi S hp
  let S₁ := S.set idx (S idx ++ [i])
  have hT₁ : S₁ tmp = [] := by simp [S₁, Lists.set_ne _ _ htr, hT]
  have hr₁ : S₁ r = S r := Lists.set_ne _ _ hrr
  have x₂ := nruns_peekAt r tmp idx out hrT hTo hd' S₁ hT₁
    (lc := S idx) (k := i) (by simp [S₁]) (by rw [hr₁]; exact hi)
  have ho₁ : S₁ out = S out := Lists.set_ne _ _ hor
  have he : (S₁.set idx (S idx)).set out (S₁ out ++ [(S₁ r)[i]'(by rw [hr₁]; exact hi)]) =
      S.set out (S out ++ [(S r)[i]]) := by
    simp only [ho₁, hr₁, S₁, Lists.set_set_u, Lists.set_get_self]
  rw [he] at x₂
  simp only [hr₁] at x₂
  exact (x₁.seq x₂).mono (by omega)

end Shallot.Packrat.Machine
