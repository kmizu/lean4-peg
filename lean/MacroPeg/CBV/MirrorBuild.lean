import MacroPeg.CBV.Mirror
import Shallot.Peg.Separation.Reduce
import Shallot.Peg.Packrat.Machine.Transfer

namespace Shallot.MacroPeg.CBV

open Complexity Shallot.Packrat.Machine Shallot.MacroPeg.KExp

/-- Reverse the loaded input row once, restoring both work stacks. -/
def mirrorBuildP {K : Nat} (row tmp work : Fin K) (hrt : row ≠ tmp)
    (htw : tmp ≠ work) (hwr : work ≠ row) : NProg K :=
  .seq (nmvAll row tmp hrt) (replaceRow tmp row work htw hwr)

theorem mirrorBuild_runs {K : Nat} (row tmp work : Fin K) (hrt : row ≠ tmp)
    (htw : tmp ≠ work) (hwr : work ≠ row) (S : Lists K) (x : List Char)
    (hr : S row = inputRow x) (ht : S tmp = []) (hw : S work = []) :
    NRuns (mirrorBuildP row tmp work hrt htw hwr) S (S.set row (mirrorRow x))
      (9 * (x.length + 1) + 4) := by
  have x₁ := nruns_mvAll row tmp hrt S
  rw [ht, List.nil_append, hr] at x₁
  let S₁ := (S.set tmp (inputRow x).reverse).set row []
  have hw₁ : S₁ work = [] := by simp [S₁, Lists.set, hwr, htw.symm, hw]
  have x₂ := nruns_replaceRow tmp row work htw hwr hrt.symm S₁ hw₁
  have hr₁ : S₁ row = [] := by simp [S₁]
  have ht₁ : S₁ tmp = (inputRow x).reverse := by simp [S₁, Lists.set, hrt.symm]
  rw [hr₁, ht₁] at x₂
  have he : (S₁.set row (inputRow x).reverse).set tmp [] = S.set row (mirrorRow x) := by
    funext k
    by_cases hkr : k = row
    · subst k; simp [S₁, Lists.set, hrt, mirrorRow]
    by_cases hkt : k = tmp
    · subst k; simp [S₁, Lists.set, ht, hrt.symm]
    simp [S₁, Lists.set, hkr, hkt]
  rw [he] at x₂
  exact (x₁.seq x₂).mono (by simp [inputRow_length]; omega)

theorem mirrorBuildCost_poly : IsPoly (fun n => 9 * (n + 1) + 4) :=
  isPoly_add (isPoly_mul (isPoly_const 9) (isPoly_add isPoly_id (isPoly_const 1))) (isPoly_const 4)

end Shallot.MacroPeg.CBV
