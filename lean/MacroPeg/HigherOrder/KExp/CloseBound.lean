import MacroPeg.HigherOrder.KExp.CloseSpec

/-!
# `closeBoundN` lies below a tower of a polynomial

Every stage bound of the composed machine is a polynomial in the input length, or a polynomial in
`cB2 j cN dN (cC1 … n)`, which is itself a tower of a polynomial. So `closeBoundN` is `TowerPoly j` for `j ≥ 1`.
-/

namespace Shallot.MacroPeg.KExp

open Complexity
open Complexity.Univ
open Shallot.MacroPeg.HO

/-- A tower of a polynomial is `TowerPoly`. -/
theorem towerPoly_tower {j : Nat} {g : Nat → Nat} (hg : IsPoly g) : TowerPoly j (fun n => tower j (g n)) :=
  let ⟨c, d, hc⟩ := hg; ⟨c, d, fun n => tower_mono j (hc n)⟩

/-- Powers of a `TowerPoly` bound are `TowerPoly` (`j ≥ 1`). -/
theorem towerPoly_pow {j : Nat} (hj : 1 ≤ j) {f : Nat → Nat} (hf : TowerPoly j f) :
    ∀ D : Nat, TowerPoly j (fun n => f n ^ D)
  | 0 => towerPoly_mono (towerPoly_const 1) (fun n => by simp)
  | D + 1 => towerPoly_mono (towerPoly_mul hj (towerPoly_pow hj hf D) hf) (fun n => by rw [Nat.pow_succ]; exact Nat.le_refl _)

/-- The reduction's steps are a polynomial in `n`. -/
theorem isPoly_cB1 (cR dR : Nat) : IsPoly (fun n => cB1 cR dR n) := by
  unfold cB1
  exact isPoly_mul (isPoly_const cR) (isPoly_pow (isPoly_add isPoly_id (isPoly_const 1)) dR)

/-- The output-length bound is a polynomial in `n`. -/
theorem isPoly_cC1 (tR : TTable) (cR dR : Nat) : IsPoly (fun n => cC1 tR cR dR n) := by
  unfold cC1
  exact isPoly_add (isPoly_add (isPoly_const _) (isPoly_mul (isPoly_const 4) isPoly_id))
    (isPoly_mul (isPoly_cB1 cR dR) (isPoly_const _))

/-- The decider's steps on the output, as a function of `n`, are `TowerPoly`. -/
theorem towerPoly_cB2 {j : Nat} (tR : TTable) (cR dR cN dN : Nat) :
    TowerPoly j (fun n => cB2 j cN dN (cC1 tR cR dR n)) := by
  unfold cB2
  exact towerPoly_tower (isPoly_mul (isPoly_const cN)
    (isPoly_pow (isPoly_add (isPoly_cC1 tR cR dR) (isPoly_const 1)) dN))

theorem closeBoundN_towerPoly {j : Nat} (hj : 1 ≤ j) (tR tN : TTable) (cR dR cN dN : Nat) :
    TowerPoly j (closeBoundN tR tN j cR dR cN dN) := by
  have h1 := isPoly_cB1 cR dR
  have hC := isPoly_cC1 tR cR dR
  have hB := towerPoly_cB2 (j := j) tR cR dR cN dN
  have k : ∀ a : Nat, TowerPoly j (fun _ => a) := fun a => towerPoly_const a
  have pP : IsPoly (fun n =>
      (1000 * (n + tsz tR + cR + dR + 2) ^ 4 + 1000 * (cB1 cR dR n + 2) ^ 2) +
      (10 + cB1 cR dR n * (1000 * (tsz tR + cC1 tR cR dR n + cB1 cR dR n * growth tR + 2) ^ 4)) +
      1000 * (tsz tR + 2 * cC1 tR cR dR n + 5) ^ 2 +
      1000 * (cC1 tR cR dR n + tsz tN + cN + dN + 2) ^ 4) := by
    refine isPoly_add (isPoly_add (isPoly_add (isPoly_add ?_ ?_) (isPoly_add (isPoly_const _)
      (isPoly_mul h1 (isPoly_mul (isPoly_const _) (isPoly_pow ?_ 4))))) ?_) ?_
    · exact isPoly_mul (isPoly_const _) (isPoly_pow (isPoly_add (isPoly_add (isPoly_add (isPoly_add isPoly_id
        (isPoly_const _)) (isPoly_const _)) (isPoly_const _)) (isPoly_const _)) 4)
    · exact isPoly_mul (isPoly_const _) (isPoly_pow (isPoly_add h1 (isPoly_const _)) 2)
    · exact isPoly_add (isPoly_add (isPoly_add (isPoly_const _) hC) (isPoly_mul h1 (isPoly_const _)))
        (isPoly_const _)
    · exact isPoly_mul (isPoly_const _) (isPoly_pow (isPoly_add (isPoly_add (isPoly_const _)
        (isPoly_mul (isPoly_const _) hC)) (isPoly_const _)) 2)
    · exact isPoly_mul (isPoly_const _) (isPoly_pow (isPoly_add (isPoly_add (isPoly_add (isPoly_add hC
        (isPoly_const _)) (isPoly_const _)) (isPoly_const _)) (isPoly_const _)) 4)
  have hT : TowerPoly j (fun n =>
      (1000 * (n + tsz tR + cR + dR + 2) ^ 4 + 1000 * (cB1 cR dR n + 2) ^ 2) +
      (10 + cB1 cR dR n * (1000 * (tsz tR + cC1 tR cR dR n + cB1 cR dR n * growth tR + 2) ^ 4)) +
      1000 * (tsz tR + 2 * cC1 tR cR dR n + 5) ^ 2 +
      1000 * (cC1 tR cR dR n + tsz tN + cN + dN + 2) ^ 4 +
      1000 * (cB2 j cN dN (cC1 tR cR dR n) + 2) ^ 2 +
      (10 + cB2 j cN dN (cC1 tR cR dR n) *
        (1000 * (tsz tN + (2 + 2 * tN.k + 4 * cC1 tR cR dR n) + cB2 j cN dN (cC1 tR cR dR n) * growth tN + 2) ^ 4)) +
      2) := by
    refine towerPoly_add (towerPoly_add (towerPoly_add (towerPoly_poly pP) ?_) ?_) (k 2)
    · exact towerPoly_mul hj (k _) (towerPoly_pow hj (towerPoly_add hB (k 2)) 2)
    · refine towerPoly_add (k 10) (towerPoly_mul hj hB (towerPoly_mul hj (k _) (towerPoly_pow hj ?_ 4)))
      refine towerPoly_add (towerPoly_add (towerPoly_poly ?_) (towerPoly_mul hj hB (k _))) (k 2)
      exact isPoly_add (isPoly_const _) (isPoly_add (isPoly_const _) (isPoly_mul (isPoly_const 4) hC))
  refine towerPoly_mono hT (fun n => ?_)
  unfold closeBoundN
  omega

end Shallot.MacroPeg.KExp
