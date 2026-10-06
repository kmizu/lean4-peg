import MacroPeg.HigherOrder.KExp.DiagLayout

/-!
# The front of the diagonal machine

`diagFrontP j` reads the input (`parseP`, `tapeP`), takes the constants and the rows (`loadP`, `takesP`,
`chunkPre`, `checkP`), lays out the configuration (`layP`), and computes the number of steps
`tower j (c * (|w|+1)^d)` on `CNT` (`countP`).

* `diagFront_ok`: on a well-shaped input, the stacks hold the table and the initial configuration (`SimSt`), the
  number of steps, and empty scratch;
* `diagFront_bad`: otherwise the program halts with `false`;

both within `frontCost j w` steps.
-/

namespace Shallot.MacroPeg.KExp

open Complexity
open Complexity.Univ
open Shallot.MacroPeg.HO

/-! ## The number of steps -/

def powBody : NProg UK :=
  .seq (.prim (.dec DD)) (.seq (nmv PP AA (by decide)) (.seq (.prim (.pushZ PP)) (mulAcc AA N1 TT PP (by decide))))

def countP (j : Nat) : NProg UK :=
  .seq (.prim (.pushZ PP)) (.seq (.prim (.inc PP)) (.seq (.prim (.dup NN N1 (by decide))) (.seq (.prim (.inc N1))
    (.seq (.loop DD .pos powBody) (.seq (.prim (.pop DD)) (.seq (.prim (.pop N1)) (.seq (.prim (.pop NN))
    (.seq (.prim (.pushZ VV)) (.seq (mulAcc CC PP TT VV (by decide)) (.seq (.prim (.pop PP))
    (.seq (towerP VV AA TT (by decide) (by decide) j) (nmv VV CNT (by decide)))))))))))))

/-- The stacks during the powers of `n + 1`. -/
def powF (n : Nat) (tp rest : List Nat) (k na c d : Nat) (m : Nat) : Lists UK :=
  (((S4 n tp rest k na c d).set N1 [n + 1]).set PP [(n + 1) ^ m]).set DD [d - m]

/-- The end of the front. -/
def SF (j n : Nat) (tp rest : List Nat) (k na c d : Nat) : Lists UK :=
  ((((((E0.set TP (tpOut tp k)).set TBL rest).set KS [k]).set NA [na]).set ST [2]).set POS
    (List.replicate k 0)).set CNT [tower j (c * (n + 1) ^ d)]

def powCost (n d : Nat) : Nat := (n + 1) ^ d * (3 * n + 8) + 6

theorem pow_body (n : Nat) (tp rest : List Nat) (k na c d : Nat) {m : Nat} (hm : m < d) :
    NRuns powBody (powF n tp rest k na c d m) (powF n tp rest k na c d (m + 1)) (powCost n d) := by
  let A := powF n tp rest k na c d m
  have d₁ := nruns_dec DD A (l := []) (v := d - m) (by simp only [A, powF]; stk_simp)
  let A₁ := A.set DD ([] ++ [d - m - 1])
  have d₂ := nruns_mv PP AA (by decide) A₁ (l := []) (v := (n + 1) ^ m) (by simp only [A₁, A, powF]; stk_simp)
  have ha : A₁ AA = [] := by simp only [A₁, A, powF, S4]; stk_simp
  rw [ha] at d₂
  let A₂ := (A₁.set AA ([] ++ [(n + 1) ^ m])).set PP []
  have d₃ := nruns_pushZ PP A₂
  have hp : A₂ PP = [] := by simp only [A₂, Lists.set_same]
  rw [hp] at d₃
  let A₃ := A₂.set PP ([] ++ [0])
  have d₄ := nruns_mulAcc AA N1 TT PP (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) A₃
    (la := []) (lb := []) (lr := []) (x := (n + 1) ^ m) (y := n + 1) (z := 0)
    (by simp only [A₃, A₂]; stk_simp) (by simp only [A₃, A₂, A₁, A, powF]; stk_simp)
    (by simp only [A₃, Lists.set_same])
  have e : (A₃.set AA []).set PP ([] ++ [0 + (n + 1) ^ m * (n + 1)]) = powF n tp rest k na c d (m + 1) := by
    rw [Nat.zero_add, ← Nat.pow_succ]
    simp only [A₃, A₂, A₁, A, powF, S4, show d - m - 1 = d - (m + 1) by omega]
    lsimp
  rw [e] at d₄
  have hle : (n + 1) ^ m ≤ (n + 1) ^ d := Nat.pow_le_pow_right (by omega) (by omega)
  have hle' : (n + 1) ^ m * (3 * (n + 1) + 5) ≤ (n + 1) ^ d * (3 * n + 8) :=
    Nat.mul_le_mul hle (by omega)
  refine (d₁.seq (d₂.seq (d₃.seq d₄))).mono ?_
  unfold powCost; omega

def countCost (j n c d : Nat) : Nat :=
  d * (powCost n d + 1) + c * (3 * (n + 1) ^ d + 5) + towerCost (c * (n + 1) ^ d) j + 20

theorem nruns_count (j n : Nat) (tp rest : List Nat) (k na c d : Nat) :
    NRuns (countP j) (S4 n tp rest k na c d) (SF j n tp rest k na c d) (countCost j n c d) := by
  let A := S4 n tp rest k na c d
  have d₁ := nruns_pushZ PP A
  have hp : A PP = [] := by simp only [A, S4]; stk_simp
  rw [hp] at d₁
  have d₂ := nruns_inc PP (A.set PP ([] ++ [0])) (l := []) (v := 0) (by simp only [Lists.set_same])
  rw [Lists.set_set_u] at d₂
  let A₁ := A.set PP ([] ++ [0 + 1])
  have d₃ := nruns_dup NN N1 (by decide) A₁ (l := []) (v := n) (by simp only [A₁, A, S4]; stk_simp)
  have hn : A₁ N1 = [] := by simp only [A₁, A, S4]; stk_simp
  rw [hn] at d₃
  have d₄ := nruns_inc N1 (A₁.set N1 ([] ++ [n])) (l := []) (v := n) (by simp only [Lists.set_same])
  rw [Lists.set_set_u] at d₄
  have e₀ : A₁.set N1 ([] ++ [n + 1]) = powF n tp rest k na c d 0 := by
    simp only [A₁, A, powF, S4, Nat.pow_zero, Nat.sub_zero]; lsimp
  rw [e₀] at d₄
  have hD : ∀ m, powF n tp rest k na c d m DD = [] ++ [d - m] := fun m => by simp only [powF]; stk_simp
  have hl := nruns_family_const (i := DD) (c := .pos) (p := powBody) (powF n tp rest k na c d) d (powCost n d)
    (fun m hm => by rw [hD, show d - m = (d - m - 1) + 1 by omega]; exact eval_pos_succ [] _)
    (by rw [hD, Nat.sub_self]; exact eval_pos_zero [])
    (fun m hm => pow_body n tp rest k na c d hm)
  let P := (n + 1) ^ d
  have d₅ := nruns_pop DD (powF n tp rest k na c d d) (hD d)
  let B₁ := (powF n tp rest k na c d d).set DD []
  have d₆ := nruns_pop N1 B₁ (l := []) (v := n + 1) (by simp only [B₁, powF]; stk_simp)
  have d₇ := nruns_pop NN (B₁.set N1 []) (l := []) (v := n) (by simp only [B₁, powF, S4]; stk_simp)
  let B₂ := (B₁.set N1 []).set NN []
  have d₈ := nruns_pushZ VV B₂
  have hv : B₂ VV = [] := by simp only [B₂, B₁, powF, S4]; stk_simp
  rw [hv] at d₈
  let B₃ := B₂.set VV ([] ++ [0])
  have d₉ := nruns_mulAcc CC PP TT VV (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) B₃
    (la := []) (lb := []) (lr := []) (x := c) (y := P) (z := 0)
    (by simp only [B₃, B₂, B₁, powF, S4]; stk_simp) (by simp only [B₃, B₂, B₁, powF, P]; stk_simp)
    (by simp only [B₃, Lists.set_same])
  rw [Nat.zero_add] at d₉
  let B₄ := (B₃.set CC []).set VV ([] ++ [c * P])
  have d₁₀ := nruns_pop PP B₄ (l := []) (v := P) (by simp only [B₄, B₃, B₂, B₁, powF, P]; stk_simp)
  let B₅ := B₄.set PP []
  have d₁₁ := nruns_tower VV AA TT (by decide) (by decide) (by decide) B₅ (lv := []) (x := c * P)
    (by simp only [B₅, B₄]; stk_simp) j
  let B₆ := B₅.set VV ([] ++ [tower j (c * P)])
  have d₁₂ := nruns_mv VV CNT (by decide) B₆ (l := []) (v := tower j (c * P)) (by simp only [B₆, Lists.set_same])
  have hc : B₆ CNT = [] := by simp only [B₆, B₅, B₄, B₃, B₂, B₁, powF, S4]; stk_simp
  rw [hc] at d₁₂
  have e : (B₆.set CNT ([] ++ [tower j (c * P)])).set VV [] = SF j n tp rest k na c d := by
    simp only [B₆, B₅, B₄, B₃, B₂, B₁, powF, S4, SF, P, Nat.sub_self]; lsimp
  rw [e] at d₁₂
  refine (d₁.seq (d₂.seq (d₃.seq (d₄.seq (hl.seq (d₅.seq (d₆.seq (d₇.seq (d₈.seq (d₉.seq (d₁₀.seq
    (d₁₁.seq d₁₂)))))))))))).mono ?_
  unfold countCost
  have : (3 * P + 5) = 3 * (n + 1) ^ d + 5 := rfl
  have h2 : towerCost (c * P) j = towerCost (c * (n + 1) ^ d) j := rfl
  rw [this, h2]
  omega

/-! ## The program -/

def restP (j : Nat) : NProg UK := .seq chunkPre (.seq checkP (.seq layP (countP j)))

def diagFrontP (j : Nat) : NProg UK :=
  .seq parseP (.seq tapeP (.seq loadP (takesP MM dsTakes dsTakes_ne (restP j))))

/-! ## Costs -/

theorem cost_bound (j : Nat) (w : List Bool) {c d L k : Nat} (hc : c ≤ w.length) (hd : d ≤ w.length)
    (hL : L ≤ w.length) (hk : k ≤ w.length) :
    8 * w.length + 4 + (7 * w.length + 4 + (3 * w.length + 1 + (15 + (6 * L + 3 * k + 8 + (4 +
      (2 * (w.length + 1) + 6 * k + 20 + countCost j w.length c d)))))) ≤ frontCost j w := by
  unfold frontCost countCost
  generalize w.length = n at *
  have hn1 : (n + 1) ^ (n + 1) = (n + 1) ^ n * (n + 1) := by rw [Nat.pow_succ]
  have hPn : (n + 1) ^ d ≤ (n + 1) ^ n := Nat.pow_le_pow_right (by omega) hd
  have hPn1 : (n + 1) ^ d ≤ (n + 1) ^ (n + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  generalize hX : (n + 1) * (n + 1) ^ (n + 1) = X
  -- the powers
  have h₁ : d * (powCost n d + 1) ≤ 8 * X + 7 * n := by
    unfold powCost
    have a : (n + 1) ^ d * (3 * n + 8) ≤ 8 * (n + 1) ^ (n + 1) := by
      rw [hn1, Nat.mul_comm 8, Nat.mul_assoc]
      exact Nat.mul_le_mul hPn (by omega)
    have b1 : d * (8 * (n + 1) ^ (n + 1)) ≤ (n + 1) * (8 * (n + 1) ^ (n + 1)) := Nat.mul_le_mul_right _ (by omega)
    have b2 : (n + 1) * (8 * (n + 1) ^ (n + 1)) = 8 * X := by rw [← hX, Nat.mul_left_comm]
    have f : d * ((n + 1) ^ d * (3 * n + 8) + 6 + 1) = d * ((n + 1) ^ d * (3 * n + 8)) + 7 * d := by
      rw [Nat.mul_add, Nat.mul_add, Nat.mul_comm d 6, Nat.mul_comm d 1]; omega
    have g := Nat.mul_le_mul_left d a
    rw [f]; omega
  -- the product
  have h₂ : c * (3 * (n + 1) ^ d + 5) ≤ 3 * X + 5 * n := by
    have a : c * (n + 1) ^ d ≤ X := by rw [← hX]; exact Nat.mul_le_mul (by omega) hPn1
    rw [Nat.mul_add, Nat.mul_left_comm]; omega
  -- the tower
  have hcX : c * (n + 1) ^ d ≤ X := by rw [← hX]; exact Nat.mul_le_mul (by omega) hPn1
  generalize hM : tower j X = M
  have hXM : X ≤ M := by rw [← hM]; exact le_tower j X
  have hjM : j ≤ M := by rw [← hM]; exact le_tower_height j X
  have h₃ : towerCost (c * (n + 1) ^ d) j ≤ 2 + M * (8 * M + 6) := by
    have a := towerCost_le (c * (n + 1) ^ d) j
    have b : tower j (c * (n + 1) ^ d) ≤ M := by rw [← hM]; exact tower_mono j hcX
    have e := Nat.mul_le_mul hjM (show 8 * tower j (c * (n + 1) ^ d) + 6 ≤ 8 * M + 6 by omega)
    omega
  have hsq : (M + 2) ^ 2 = M * M + 4 * M + 4 := by
    rw [Nat.pow_two, Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega
  have hmm : M * (8 * M + 6) = 8 * (M * M) + 6 * M := by
    rw [Nat.mul_add, Nat.mul_left_comm, Nat.mul_comm M 6]
  have h4 : n + 2 ≤ (n + 2) ^ 4 := Nat.le_self_pow (by decide) (n + 2)
  omega


/-! ## The front -/

theorem sf_scratch (j n : Nat) (tp rest : List Nat) (k na c d : Nat) : UScratch (SF j n tp rest k na c d) := by
  intro i hi
  simp only [SF, get_set, E0, v_TBL, v_KS, v_NA, v_ST, v_POS, v_TP, v_CNT]
  repeat' split
  all_goals first | rfl | omega

/-- **The front on a well-shaped input.** -/
theorem diagFront_ok (j : Nat) (w : List Bool) {k nq na c d : Nat} {rest : List Nat}
    (h : DiagShape w k nq na c d rest) :
    ∃ S, NRuns (diagFrontP j) (nInit UK w) S (frontCost j w) ∧
      SimSt S (tableOfNums k nq na rest) (finit k w) ∧ S CNT = [diagSteps j c d w] ∧ UScratch S := by
  obtain ⟨hd, hmod⟩ := h
  have hb := deUnary_bound w
  rw [hd] at hb
  simp only [List.sum_cons, List.length_cons] at hb
  have r₁ := nruns_parse w
  have r₂ := nruns_tape w
  have r₃ := nruns_load w
  have hS2L : S2L w = ((E0.set NN [w.length]).set TP (w.length :: w.map bitSym)).set MM
      (k :: nq :: na :: c :: d :: rest).reverse := by
    simp only [S2L, hd]
  rw [hS2L] at r₃
  have r₄ := nruns_chunkPre w.length (w.length :: w.map bitSym) rest k nq na c d
  have r₅ := nruns_check w.length (w.length :: w.map bitSym) rest k nq na c d hmod
  have r₆ := nruns_lay w.length (w.length :: w.map bitSym) rest k na c d
  have r₇ := nruns_count j w.length (w.length :: w.map bitSym) rest k na c d
  have rt := (takes_good w.length (w.length :: w.map bitSym) rest k nq na c d (restP j)).1
    (r₄.seq (r₅.seq (r₆.seq r₇)))
  refine ⟨SF j w.length (w.length :: w.map bitSym) rest k na c d, (r₁.seq (r₂.seq (r₃.seq rt))).mono ?_,
    ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, sf_scratch _ _ _ _ _ _ _ _⟩
  · have := cost_bound j w (c := c) (d := d) (L := rest.length) (k := k) (by omega) (by omega) (by omega)
      (by omega)
    simp only [List.length_cons, List.length_map]
    omega
  · show _ = encRows (decRows k rest)
    rw [encRows_decRows]; simp only [SF]; stk_simp
  · simp only [SF]; stk_simp; rfl
  · simp only [SF]; stk_simp; rfl
  · simp only [SF]; stk_simp; rfl
  · simp only [SF]; stk_simp; rfl
  · rw [encTapes_finit]; simp only [SF]; stk_simp
  · simp only [SF, diagSteps]; stk_simp

/-- **The front on any other input** halts with `false`. -/
theorem diagFront_bad (j : Nat) (w : List Bool) (h : ∀ k nq na c d rest, ¬ DiagShape w k nq na c d rest) :
    ∃ S', NHalts (diagFrontP j) (nInit UK w) false S' (frontCost j w) := by
  have hb := deUnary_bound w
  have r₁ := nruns_parse w
  have r₂ := nruns_tape w
  have r₃ := nruns_load w
  by_cases h5 : (deUnary w).length < 5
  · obtain ⟨S', hS'⟩ := nhalts_takes MM (restP j) dsTakes dsTakes_ne (S2L w) (by
      have : (S2L w) MM = (deUnary w).reverse := by simp only [S2L]; stk_simp
      rw [this, List.length_reverse]; simp only [dsTakes, List.length_cons, List.length_nil]; omega)
    refine ⟨S', (r₁.seqH (r₂.seqH (r₃.seqH hS'))).mono ?_⟩
    have := cost_bound j w (c := 0) (d := 0) (L := 0) (k := 0) (by omega) (by omega) (by omega) (by omega)
    simp only [dsTakes, List.length_cons, List.length_nil]
    omega
  · obtain ⟨k, nq, na, c, d, rest, hd⟩ : ∃ k nq na c d rest, deUnary w = k :: nq :: na :: c :: d :: rest := by
      match hL : deUnary w, h5 with
      | k :: nq :: na :: c :: d :: rest, _ => exact ⟨k, nq, na, c, d, rest, rfl⟩
      | [], h5 => simp at h5
      | [_], h5 => simp at h5
      | [_, _], h5 => simp at h5
      | [_, _, _], h5 => simp at h5
      | [_, _, _, _], h5 => simp at h5
    have hmod : rest.length % (2 * k + 1) ≠ 0 := fun hm => h k nq na c d rest ⟨hd, hm⟩
    rw [hd] at hb
    simp only [List.sum_cons, List.length_cons] at hb
    have hS2L : S2L w = ((E0.set NN [w.length]).set TP (w.length :: w.map bitSym)).set MM
        (k :: nq :: na :: c :: d :: rest).reverse := by
      simp only [S2L, hd]
    rw [hS2L] at r₃
    have r₄ := nruns_chunkPre w.length (w.length :: w.map bitSym) rest k nq na c d
    have r₅ := nhalts_check w.length (w.length :: w.map bitSym) rest k nq na c d hmod
    have hr : NHalts (restP j) _ false _ _ := r₄.seqH (NHalts.seq (q := .seq layP (countP j)) r₅)
    have ht := (takes_good w.length (w.length :: w.map bitSym) rest k nq na c d (restP j)).2 hr
    refine ⟨_, (r₁.seqH (r₂.seqH (r₃.seqH ht))).mono ?_⟩
    have := cost_bound j w (c := 0) (d := 0) (L := rest.length) (k := k) (by omega) (by omega) (by omega)
      (by omega)
    omega

end Shallot.MacroPeg.KExp
