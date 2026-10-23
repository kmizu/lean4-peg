import MacroPeg.CBV.ScanStep

namespace Shallot.MacroPeg.CBV

open Complexity Shallot.MacroPeg.Mach Shallot.MacroPeg.KExp

def scanLoopP {K : Nat} (r : ScanRegs K) : NProg K := .loop (r.get 11) .pos (scanStepP r)

/-- The physical scanning loop reaches precisely the final cursors and flag of `scanEnd`. -/
theorem scanLoop_runs {K : Nat} (r : ScanRegs K) (S : Lists K) (x : List Char) (k p q B : Nat)
    (hrow : S (r.get 0) = mirrorRow x) (htmp : S (r.get 1) = [])
    (hk : k ≤ p) (hp : p ≤ x.length) (hq : q ≤ x.length) (hB : ∀ v ∈ mirrorRow x, v ≤ B) :
    NRuns (scanLoopP r) (scanState r S p q k true)
      (scanState r S (scanEnd (mirrorRow x) k p q).src (scanEnd (mirrorRow x) k p q).dst 0
        (scanEnd (mirrorRow x) k p q).ok) (k * (scanStepCost x.length B + 1) + 1) := by
  induction k generalizing p q with
  | zero =>
    have hx := nruns_loop_exit (i := r.get 11) (c := .pos) (p := scanStepP r)
      (S := scanState r S p q 0 true) (by simp [scanState, Lists.set, NTest.eval])
    simpa [scanLoopP, scanEnd] using hx
  | succ k ih =>
    let a := (mirrorRow x).getD p 0
    let b := (mirrorRow x).getD q 0
    have hsrc : (a == 0) = false := by
      apply Bool.eq_false_iff.mpr
      intro hz
      have he : a = 0 := eq_of_beq hz
      have hpos := mirrorRow_positive hp (by omega)
      omega
    have xc := scanStep_runs r S x k p q B hrow htmp hk hp hq hB
    have htest : NTest.pos.eval (scanState r S p q (k + 1) true (r.get 11)) = true := by
      simp [scanState, Lists.set, NTest.eval]
    by_cases he : a = b
    · have hc : ((mirrorRow x).getD p 0 == (mirrorRow x).getD q 0 && !((mirrorRow x).getD p 0 == 0)) = true := by
        change (a == b && !(a == 0)) = true
        rw [hsrc]
        simp [he]
      have hend : scanEnd (mirrorRow x) (k + 1) p q = scanEnd (mirrorRow x) k (p - 1) (q - 1) := by
        rw [scanEnd, if_pos hc]
      rw [hend]
      have he' : (mirrorRow x).getD p 0 = (mirrorRow x).getD q 0 := he
      rw [if_pos he'] at xc
      have xl := ih (p - 1) (q - 1) (by omega) (by omega) (by omega)
      obtain ⟨tc, htc, hxc⟩ := xc
      obtain ⟨tl, htl, hxl⟩ := xl
      exact ⟨tc + 1 + tl, by rw [Nat.succ_mul]; omega, .loopC trivial htest hxc hxl⟩
    · have hc : ((mirrorRow x).getD p 0 == (mirrorRow x).getD q 0 && !((mirrorRow x).getD p 0 == 0)) = false := by
        change (a == b && !(a == 0)) = false
        have heq : (a == b) = false := Bool.eq_false_iff.mpr (fun h => he (eq_of_beq h))
        simp [heq]
      simp only [scanEnd, hc, Bool.false_eq_true, if_false]
      have he' : (mirrorRow x).getD p 0 ≠ (mirrorRow x).getD q 0 := he
      rw [if_neg he'] at xc
      have xl := nruns_loop_exit (i := r.get 11) (c := .pos) (p := scanStepP r)
        (S := scanState r S p q 0 false) (by simp [scanState, Lists.set, NTest.eval])
      obtain ⟨tc, htc, hxc⟩ := xc
      obtain ⟨tl, htl, hxl⟩ := xl
      refine ⟨tc + 1 + tl, ?_, .loopC trivial htest hxc hxl⟩
      have hm : scanStepCost x.length B + 1 ≤ (k + 1) * (scanStepCost x.length B + 1) :=
        Nat.le_mul_of_pos_left _ (by omega)
      omega

/-- A flag selects failure or success with the final remaining length. -/
def scanFinishP {K : Nat} (r : ScanRegs K) (ans : Fin K) (ha : ∀ i, ans ≠ r.get i) : NProg K :=
  .ite (r.get 12) .zero (npushC ans 1)
    (.seq (.prim (.dup (r.get 4) ans (ha 4).symm)) (.seq (.prim (.inc ans)) (.prim (.inc ans))))

theorem scanFinish_runs {K : Nat} (r : ScanRegs K) (ans : Fin K) (ha : ∀ i, ans ≠ r.get i)
    (S : Lists K) (p q k : Nat) (ok : Bool) :
    NRuns (scanFinishP r ans ha) (scanState r S p q k ok)
      ((scanState r S p q k ok).set ans (S ans ++ [if ok then q + 2 else 1])) 4 := by
  let X := scanState r S p q k ok
  have hxa : X ans = S ans := by simp [X, scanState, Lists.set, ha]
  cases ok with
  | false =>
    have hx := (nruns_pushC ans X 1).iteT (i := r.get 12) (c := .zero)
      (q := .seq (.prim (.dup (r.get 4) ans (ha 4).symm)) (.seq (.prim (.inc ans)) (.prim (.inc ans))))
      (by simp [X, scanState, Lists.set, NTest.eval])
    simpa [X, scanFinishP, hxa] using hx.mono (show 1 + 1 + 1 ≤ 4 by omega)
  | true =>
    have x₁ := nruns_dup (r.get 4) ans (ha 4).symm X (l := []) (v := q) (by simp [X, scanState, Lists.set])
    rw [hxa] at x₁
    let X₁ := X.set ans (S ans ++ [q])
    have x₂ := nruns_inc ans X₁ (l := S ans) (v := q) (by simp [X₁])
    simp only [X₁, Lists.set_set_u] at x₂
    let X₂ := X₁.set ans (S ans ++ [q + 1])
    have x₃ := nruns_inc ans X₂ (l := S ans) (v := q + 1) (by simp [X₂])
    simp only [X₂, X₁, Lists.set_set_u] at x₃
    have hx := (x₁.seq (x₂.seq x₃)).iteF (i := r.get 12) (c := .zero) (p := npushC ans 1)
      (by simp [X, scanState, Lists.set, NTest.eval])
    simpa [X, scanFinishP, Nat.add_assoc] using hx

/-- Pop only the four local scalar frames after scanning. -/
def scanCleanupP {K : Nat} (r : ScanRegs K) : NProg K :=
  .seq (.prim (.pop (r.get 12))) (.seq (.prim (.pop (r.get 11)))
    (.seq (.prim (.pop (r.get 4))) (.prim (.pop (r.get 3)))))

theorem scanCleanup_runs {K : Nat} (r : ScanRegs K) (S : Lists K) (p q k : Nat) (ok : Bool)
    (h3 : S (r.get 3) = []) (h4 : S (r.get 4) = []) (h11 : S (r.get 11) = []) (h12 : S (r.get 12) = []) :
    NRuns (scanCleanupP r) (scanState r S p q k ok) S 4 := by
  let X := scanState r S p q k ok
  have x₁ := nruns_pop (r.get 12) X (l := []) (v := if ok then 1 else 0) (by simp [X, scanState])
  let X₁ := X.set (r.get 12) []
  have x₂ := nruns_pop (r.get 11) X₁ (l := []) (v := k) (by simp [X₁, X, scanState, Lists.set])
  let X₂ := X₁.set (r.get 11) []
  have x₃ := nruns_pop (r.get 4) X₂ (l := []) (v := q) (by simp [X₂, X₁, X, scanState, Lists.set])
  let X₃ := X₂.set (r.get 4) []
  have x₄ := nruns_pop (r.get 3) X₃ (l := []) (v := p) (by simp [X₃, X₂, X₁, X, scanState, Lists.set])
  have he : X₃.set (r.get 3) [] = S := by
    simp only [X₃, X₂, X₁, X, scanState]
    scan_states r
  rw [he] at x₄
  exact x₁.seq (x₂.seq (x₃.seq x₄))

theorem scanState_frame {K : Nat} (r : ScanRegs K) (S : Lists K) (p q k : Nat) (ok : Bool)
    (ans : Fin K) (ha : ∀ i, ans ≠ r.get i) (v : List Nat) :
    (scanState r S p q k ok).set ans v = scanState r (S.set ans v) p q k ok := by
  have h3 := (ha 3).symm
  have h4 := (ha 4).symm
  have h11 := (ha 11).symm
  have h12 := (ha 12).symm
  unfold scanState
  scan_states r

def scanCoreP {K : Nat} (r : ScanRegs K) (ans : Fin K) (ha : ∀ i, ans ≠ r.get i) : NProg K :=
  .seq (scanLoopP r) (.seq (scanFinishP r ans ha) (scanCleanupP r))

def scanCoreCost (n B : Nat) : Nat := n * (scanStepCost n B + 1) + 9

/-- From prepared local cursors, the complete matcher returns its code and restores every local scalar. -/
theorem scanCore_runs {K : Nat} (r : ScanRegs K) (ans : Fin K) (ha : ∀ i, ans ≠ r.get i)
    (S : Lists K) (x : List Char) (k p q B : Nat)
    (hrow : S (r.get 0) = mirrorRow x) (htmp : S (r.get 1) = [])
    (h3 : S (r.get 3) = []) (h4 : S (r.get 4) = []) (h11 : S (r.get 11) = []) (h12 : S (r.get 12) = [])
    (hk : k ≤ p) (hp : p ≤ x.length) (hq : q ≤ x.length) (hB : ∀ v ∈ mirrorRow x, v ≤ B) :
    NRuns (scanCoreP r ans ha) (scanState r S p q k true)
      (S.set ans (S ans ++ [mirrorScan (mirrorRow x) k p q])) (scanCoreCost x.length B) := by
  let E := scanEnd (mirrorRow x) k p q
  let v := if E.ok then E.dst + 2 else 1
  let O := S.set ans (S ans ++ [v])
  have xl := scanLoop_runs r S x k p q B hrow htmp hk hp hq hB
  have xf := scanFinish_runs r ans ha S E.src E.dst 0 E.ok
  rw [scanState_frame r S E.src E.dst 0 E.ok ans ha] at xf
  have xc := scanCleanup_runs r O E.src E.dst 0 E.ok
    (by simp [O, Lists.set, (ha 3).symm, h3]) (by simp [O, Lists.set, (ha 4).symm, h4])
    (by simp [O, Lists.set, (ha 11).symm, h11]) (by simp [O, Lists.set, (ha 12).symm, h12])
  have hx := xl.seq (xf.seq xc)
  have hv : v = mirrorScan (mirrorRow x) k p q := scanEnd_value (mirrorRow x) k p q
  have hm := Nat.mul_le_mul_right (scanStepCost x.length B + 1) (Nat.le_trans hk hp)
  have hout : O = S.set ans (S ans ++ [mirrorScan (mirrorRow x) k p q]) := by simp only [O, hv]
  rw [hout] at hx
  exact hx.mono (by unfold scanCoreCost; omega)

/-- The complete scan budget is quadratic in input length for a fixed character-code bound. -/
theorem scanCoreCost_poly (B : Nat) : IsPoly (fun n => scanCoreCost n B) := by
  have hs : IsPoly (fun n => scanStepCost n B + 1) :=
    isPoly_add (isPoly_add (isPoly_add (isPoly_mul (isPoly_const 30) (isPoly_add isPoly_id (isPoly_const 1)))
      (isPoly_const _)) (isPoly_const 40)) (isPoly_const 1)
  exact isPoly_add (isPoly_mul isPoly_id hs) (isPoly_const 9)

end Shallot.MacroPeg.CBV
