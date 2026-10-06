import MacroPeg.HigherOrder.KExp.DiagFront
import Complexity.Univ.Load

/-!
# Laying out a constant table on the input

`layTP T j c d` puts the constant table `T` and the initial configuration of the input `w` on the stacks
(`SimSt`), and the number of steps `tower j (c * (|w|+1)^d)` on `CNT` (`layP_runs`).

The number of steps is computed as `c` multiplied `d` times by `|w|+1` (`count2P`), so every intermediate value
is at most `c * (|w|+1)^d`.
-/

namespace Shallot.MacroPeg.KExp

open Complexity
open Complexity.Univ
open Shallot.MacroPeg.HO

/-! ## `c * (n+1)^d` by repeated multiplication -/

def mulBody : NProg UK :=
  .seq (.prim (.dec DD)) (.seq (nmv VV AA (by decide)) (.seq (.prim (.pushZ VV)) (mulAcc AA N1 TT VV (by decide))))

def count2P (j : Nat) : NProg UK :=
  .seq (.prim (.dup NN N1 (by decide))) (.seq (.prim (.inc N1)) (.seq (nmv CC VV (by decide))
    (.seq (.loop DD .pos mulBody) (.seq (.prim (.pop DD)) (.seq (.prim (.pop N1)) (.seq (.prim (.pop NN))
    (.seq (towerP VV AA TT (by decide) (by decide) j) (nmv VV CNT (by decide)))))))))

/-- The stacks during the multiplications. -/
def mulF (n : Nat) (tp rest : List Nat) (k na c d : Nat) (m : Nat) : Lists UK :=
  ((((S4 n tp rest k na c d).set N1 [n + 1]).set CC []).set VV [c * (n + 1) ^ m]).set DD [d - m]

def mulCost (n c d : Nat) : Nat := c * (n + 1) ^ d * (3 * n + 8) + 6

theorem mul_body (n : Nat) (tp rest : List Nat) (k na c d : Nat) {m : Nat} (hm : m < d) :
    NRuns mulBody (mulF n tp rest k na c d m) (mulF n tp rest k na c d (m + 1)) (mulCost n c d) := by
  let A := mulF n tp rest k na c d m
  have d₁ := nruns_dec DD A (l := []) (v := d - m) (by simp only [A, mulF]; stk_simp)
  let A₁ := A.set DD ([] ++ [d - m - 1])
  have d₂ := nruns_mv VV AA (by decide) A₁ (l := []) (v := c * (n + 1) ^ m) (by simp only [A₁, A, mulF]; stk_simp)
  have ha : A₁ AA = [] := by simp only [A₁, A, mulF, S4]; stk_simp
  rw [ha] at d₂
  let A₂ := (A₁.set AA ([] ++ [c * (n + 1) ^ m])).set VV []
  have d₃ := nruns_pushZ VV A₂
  have hp : A₂ VV = [] := by simp only [A₂, Lists.set_same]
  rw [hp] at d₃
  let A₃ := A₂.set VV ([] ++ [0])
  have d₄ := nruns_mulAcc AA N1 TT VV (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) A₃
    (la := []) (lb := []) (lr := []) (x := c * (n + 1) ^ m) (y := n + 1) (z := 0)
    (by simp only [A₃, A₂]; stk_simp) (by simp only [A₃, A₂, A₁, A, mulF]; stk_simp)
    (by simp only [A₃, Lists.set_same])
  have e : (A₃.set AA []).set VV ([] ++ [0 + c * (n + 1) ^ m * (n + 1)]) = mulF n tp rest k na c d (m + 1) := by
    rw [Nat.zero_add, Nat.mul_assoc, ← Nat.pow_succ]
    simp only [A₃, A₂, A₁, A, mulF, S4, show d - m - 1 = d - (m + 1) by omega]
    lsimp
  rw [e] at d₄
  have hle : c * (n + 1) ^ m ≤ c * (n + 1) ^ d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
  have hle' : c * (n + 1) ^ m * (3 * (n + 1) + 5) ≤ c * (n + 1) ^ d * (3 * n + 8) :=
    Nat.mul_le_mul hle (by omega)
  refine (d₁.seq (d₂.seq (d₃.seq d₄))).mono ?_
  unfold mulCost; omega

def count2Cost (j n c d : Nat) : Nat := d * (mulCost n c d + 1) + towerCost (c * (n + 1) ^ d) j + 20

theorem nruns_count2 (j n : Nat) (tp rest : List Nat) (k na c d : Nat) :
    NRuns (count2P j) (S4 n tp rest k na c d) (SF j n tp rest k na c d) (count2Cost j n c d) := by
  let A := S4 n tp rest k na c d
  have d₁ := nruns_dup NN N1 (by decide) A (l := []) (v := n) (by simp only [A, S4]; stk_simp)
  have hn : A N1 = [] := by simp only [A, S4]; stk_simp
  rw [hn] at d₁
  have d₂ := nruns_inc N1 (A.set N1 ([] ++ [n])) (l := []) (v := n) (by simp only [Lists.set_same])
  rw [Lists.set_set_u] at d₂
  let A₁ := A.set N1 ([] ++ [n + 1])
  have d₃ := nruns_mv CC VV (by decide) A₁ (l := []) (v := c) (by simp only [A₁, A, S4]; stk_simp)
  have hv : A₁ VV = [] := by simp only [A₁, A, S4]; stk_simp
  rw [hv] at d₃
  have e₀ : (A₁.set VV ([] ++ [c])).set CC [] = mulF n tp rest k na c d 0 := by
    simp only [A₁, A, mulF, S4, Nat.pow_zero, Nat.mul_one, Nat.sub_zero]; lsimp
  rw [e₀] at d₃
  have hD : ∀ m, mulF n tp rest k na c d m DD = [] ++ [d - m] := fun m => by simp only [mulF]; stk_simp
  have hl := nruns_family_const (i := DD) (c := .pos) (p := mulBody) (mulF n tp rest k na c d) d (mulCost n c d)
    (fun m hm => by rw [hD, show d - m = (d - m - 1) + 1 by omega]; exact eval_pos_succ [] _)
    (by rw [hD, Nat.sub_self]; exact eval_pos_zero [])
    (fun m hm => mul_body n tp rest k na c d hm)
  let V := c * (n + 1) ^ d
  have d₅ := nruns_pop DD (mulF n tp rest k na c d d) (hD d)
  let B₁ := (mulF n tp rest k na c d d).set DD []
  have d₆ := nruns_pop N1 B₁ (l := []) (v := n + 1) (by simp only [B₁, mulF]; stk_simp)
  have d₇ := nruns_pop NN (B₁.set N1 []) (l := []) (v := n) (by simp only [B₁, mulF, S4]; stk_simp)
  let B₂ := (B₁.set N1 []).set NN []
  have d₁₁ := nruns_tower VV AA TT (by decide) (by decide) (by decide) B₂ (lv := []) (x := V)
    (by simp only [B₂, B₁, mulF, V]; stk_simp) j
  let B₃ := B₂.set VV ([] ++ [tower j V])
  have d₁₂ := nruns_mv VV CNT (by decide) B₃ (l := []) (v := tower j V) (by simp only [B₃, Lists.set_same])
  have hc : B₃ CNT = [] := by simp only [B₃, B₂, B₁, mulF, S4]; stk_simp
  rw [hc] at d₁₂
  have e : (B₃.set CNT ([] ++ [tower j V])).set VV [] = SF j n tp rest k na c d := by
    simp only [B₃, B₂, B₁, mulF, S4, SF, V, Nat.sub_self]; lsimp
  rw [e] at d₁₂
  refine (d₁.seq (d₂.seq (d₃.seq (hl.seq (d₅.seq (d₆.seq (d₇.seq (d₁₁.seq d₁₂)))))))).mono ?_
  unfold count2Cost
  have h2 : towerCost V j = towerCost (c * (n + 1) ^ d) j := rfl
  rw [h2]
  omega

/-! ## The layout -/

/-- Drop the numbers read, and push the table and the constants. -/
def layPreP (T : TTable) (c d : Nat) : NProg UK :=
  .seq (nclr LL) (.seq (nloadP TBL (encRows T.rows)) (.seq (npushC KS T.k)
    (.seq (npushC NA T.na) (.seq (npushC CC c) (npushC DD d)))))

/-- Lay out the constant table `T` and the initial configuration of the input, with the step count. -/
def layTP (T : TTable) (j c d : Nat) : NProg UK :=
  .seq parseP (.seq tapeP (.seq (layPreP T c d) (.seq layP (count2P j))))

def layCost (T : TTable) (j c d : Nat) (w : List Bool) : Nat :=
  1000 * (w.length + tsz T + c + d + 2) ^ 4 + 1000 * (tower j (c * (w.length + 1) ^ d) + 2) ^ 2

theorem lay_pre (T : TTable) (c d : Nat) (w : List Bool) :
    NRuns (layPreP T c d) (S2 w)
      (S3 w.length (w.length :: w.map bitSym) (encRows T.rows) T.k T.na c d)
      (2 * w.length + 1 + ((encRows T.rows).length + (encRows T.rows).sum + 2 + (T.k + 1 + (T.na + 1 +
        (c + 1 + (d + 1)))))) := by
  have d₁ := nruns_clr LL (S2 w)
  have hl : ((S2 w) LL).length ≤ w.length := by
    have : (S2 w) LL = deUnary w := by simp only [S2]; stk_simp
    rw [this]; have := deUnary_bound w; omega
  let A := (S2 w).set LL []
  have d₂ := Complexity.nruns_load TBL (encRows T.rows) A
  have h0 : A TBL = [] := by simp only [A, S2]; stk_simp
  rw [h0, List.nil_append] at d₂
  let A₁ := A.set TBL (encRows T.rows)
  have d₃ := nruns_pushC KS A₁ T.k
  have h1 : A₁ KS = [] := by simp only [A₁, A, S2]; stk_simp
  rw [h1] at d₃
  let A₂ := A₁.set KS ([] ++ [T.k])
  have d₄ := nruns_pushC NA A₂ T.na
  have h2 : A₂ NA = [] := by simp only [A₂, A₁, A, S2]; stk_simp
  rw [h2] at d₄
  let A₃ := A₂.set NA ([] ++ [T.na])
  have d₅ := nruns_pushC CC A₃ c
  have h3 : A₃ CC = [] := by simp only [A₃, A₂, A₁, A, S2]; stk_simp
  rw [h3] at d₅
  let A₄ := A₃.set CC ([] ++ [c])
  have d₆ := nruns_pushC DD A₄ d
  have h4 : A₄ DD = [] := by simp only [A₄, A₃, A₂, A₁, A, S2]; stk_simp
  rw [h4] at d₆
  have e : A₄.set DD ([] ++ [d]) = S3 w.length (w.length :: w.map bitSym) (encRows T.rows) T.k T.na c d := by
    simp only [A₄, A₃, A₂, A₁, A, S2, S3]; lsimp
  rw [e] at d₆
  exact (d₁.seq (d₂.seq (d₃.seq (d₄.seq (d₅.seq d₆))))).mono (by omega)

theorem lay_cost_bound (T : TTable) (j c d : Nat) (w : List Bool) :
    8 * w.length + 4 + (7 * w.length + 4 + ((2 * w.length + 1 + ((encRows T.rows).length + (encRows T.rows).sum + 2 +
      (T.k + 1 + (T.na + 1 + (c + 1 + (d + 1)))))) + (2 * (w.length + 1) + 6 * T.k + 20 +
      count2Cost j w.length c d))) ≤ layCost T j c d w := by
  unfold layCost count2Cost mulCost
  have htsz : (encRows T.rows).length + (encRows T.rows).sum + T.k + T.na = tsz T := rfl
  generalize tsz T = z at *
  generalize w.length = n at *
  generalize hP : n + z + c + d + 2 = P
  generalize hV : c * (n + 1) ^ d = V
  generalize hM : tower j V = M
  have hVM : V ≤ M := by rw [← hM]; exact le_tower j V
  have hjM : j ≤ M := by rw [← hM]; exact le_tower_height j V
  have h₃ : towerCost V j ≤ 2 + M * (8 * M + 6) := by
    have a := towerCost_le V j
    have e := Nat.mul_le_mul hjM (show 8 * tower j V + 6 ≤ 8 * M + 6 by omega)
    omega
  -- the multiplications
  have hA : d * (3 * n + 8) ≤ 8 * (P * P) := by
    have := Nat.mul_le_mul (show d ≤ P by omega) (show 3 * n + 8 ≤ 8 * P by omega)
    rw [Nat.mul_left_comm] at this; exact this
  generalize hAd : d * (3 * n + 8) = A at hA
  have hmul : d * (V * (3 * n + 8) + 6 + 1) = A * V + 7 * d := by
    rw [← hAd, Nat.mul_add, Nat.mul_add, Nat.mul_comm V, ← Nat.mul_assoc]; omega
  have hAV : A * V ≤ A * A + M * M := by
    have h1 : A * V ≤ A * M := Nat.mul_le_mul_left _ hVM
    rcases Nat.le_total A M with h | h
    · have := Nat.mul_le_mul_right M h; omega
    · have := Nat.mul_le_mul_left A h; omega
  have hAA : A * A ≤ 64 * (P * P * (P * P)) := by
    have := Nat.mul_le_mul hA hA
    have e : 8 * (P * P) * (8 * (P * P)) = 64 * (P * P * (P * P)) := by
      rw [Nat.mul_assoc, Nat.mul_left_comm (P * P) 8, ← Nat.mul_assoc]
    omega
  have hP4 : P ^ 4 = P * P * (P * P) := by
    rw [show 4 = 2 + 2 from rfl, Nat.pow_add, Nat.pow_two]
  have hPP : P ≤ P * P * (P * P) := by
    have := Nat.le_self_pow (by decide : 4 ≠ 0) P; omega
  have hsq : (M + 2) ^ 2 = M * M + 4 * M + 4 := by
    rw [Nat.pow_two, Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega
  have hmm : M * (8 * M + 6) = 8 * (M * M) + 6 * M := by
    rw [Nat.mul_add, Nat.mul_left_comm, Nat.mul_comm M 6]
  omega

/-- **The constant table laid out on the input.** -/
theorem layP_runs (T : TTable) (j c d : Nat) (w : List Bool) :
    ∃ S, NRuns (layTP T j c d) (nInit UK w) S (layCost T j c d w) ∧
      SimSt S T (finit T.k w) ∧ S CNT = [tower j (c * (w.length + 1) ^ d)] ∧ UScratch S := by
  have r₁ := nruns_parse w
  have r₂ := nruns_tape w
  have r₃ := lay_pre T c d w
  have r₄ := nruns_lay w.length (w.length :: w.map bitSym) (encRows T.rows) T.k T.na c d
  have r₅ := nruns_count2 j w.length (w.length :: w.map bitSym) (encRows T.rows) T.k T.na c d
  refine ⟨SF j w.length (w.length :: w.map bitSym) (encRows T.rows) T.k T.na c d,
    (r₁.seq (r₂.seq (r₃.seq (r₄.seq r₅)))).mono ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, sf_scratch _ _ _ _ _ _ _ _⟩
  · have := lay_cost_bound T j c d w
    simp only [List.length_cons, List.length_map]
    omega
  · simp only [SF]; stk_simp
  · simp only [SF]; stk_simp
  · simp only [SF]; stk_simp
  · simp only [SF]; stk_simp; rfl
  · simp only [SF]; stk_simp; rfl
  · rw [encTapes_finit]; simp only [SF]; stk_simp
  · simp only [SF]; stk_simp

end Shallot.MacroPeg.KExp
