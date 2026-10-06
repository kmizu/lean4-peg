import MacroPeg.HigherOrder.Mach.MainRun
import MacroPeg.HigherOrder.Mach.FinalSizes
import MacroPeg.HigherOrder.Mach.ReadSizes
import MacroPeg.HigherOrder.Mach.TBounds
import MacroPeg.HigherOrder.Mach.TowerArith

/-!
# The steps of the whole decision, first part: the tables

The tables of the final reading state are at most a tower of height `j` of `Pb F cap`, a polynomial in a bound `F`
on the sizes of the state (`tb_valSum`, `tb_cntSum`, `tb_envSum`, `tb_rowsFlat`, `tb_candSum`, `tb_zeroT`). On an
accepted reading whose orders pass, the evaluation costs at most `evBound` with the starting rule values `zeroT`
(`evalCost_final`).
-/

namespace Shallot.MacroPeg.Mach

open Complexity
open Shallot.MacroPeg.HO
open Shallot.MacroPeg.Flat

/-! ## Polynomials in `m` -/

section Poly

variable {m : Nat}

/-- Lift a monomial bound to a higher degree. -/
theorem pm_lift {x A a d : Nat} (hm : 1 ≤ m) (hx : x ≤ A * m ^ a) (h : a ≤ d) : x ≤ A * m ^ d :=
  Nat.le_trans hx (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hm h))

/-- Add two monomial bounds of the same degree. -/
theorem pm_add {x y A B d : Nat} (hx : x ≤ A * m ^ d) (hy : y ≤ B * m ^ d) : x + y ≤ (A + B) * m ^ d := by
  rw [Nat.add_mul]; omega

/-- Multiply two monomial bounds. -/
theorem pm_mul {x y A B a b : Nat} (hx : x ≤ A * m ^ a) (hy : y ≤ B * m ^ b) : x * y ≤ (A * B) * m ^ (a + b) := by
  refine Nat.le_trans (Nat.mul_le_mul hx hy) (Nat.le_of_eq ?_)
  rw [Nat.pow_add, Nat.mul_mul_mul_comm]

/-- A constant is a monomial of degree `0`. -/
theorem pm_const (c : Nat) : c ≤ c * m ^ 0 := by simp

/-- A linear bound `a * n + b ≤ (a + b) * (n + 1)`. -/
theorem pm_lin (a b n : Nat) : a * n + b ≤ (a + b) * (n + 1) ^ 1 := by
  rw [Nat.pow_one, Nat.mul_add, Nat.mul_one, Nat.add_mul]
  have : b * n + b ≥ b := Nat.le_add_left _ _
  omega

end Poly

/-! ## Towers of `k * M` -/

section TowM

variable {j : Nat}

theorem twL {a k M : Nat} (h : a ≤ k * M) : a ≤ tower j (k * M) := tw_of_le h

theorem twW {a ka kb M : Nat} (h : a ≤ tower j (ka * M)) (hk : ka ≤ kb) : a ≤ tower j (kb * M) :=
  tw_mono' h (Nat.mul_le_mul_right _ hk)

theorem twA {a b ka kb M : Nat} (hM : 1 ≤ M) (ha : a ≤ tower j (ka * M)) (hb : b ≤ tower j (kb * M)) :
    a + b ≤ tower j ((ka + kb + 2) * M) :=
  tw_mono' (tw_add ha hb) (by rw [Nat.add_mul, Nat.add_mul]; omega)

theorem twM (hj : 1 ≤ j) {a b ka kb M : Nat} (hM : 1 ≤ M) (ha : a ≤ tower j (ka * M))
    (hb : b ≤ tower j (kb * M)) : a * b ≤ tower j ((ka + kb + 2) * M) :=
  tw_mono' (tw_mul hj ha hb) (by rw [Nat.add_mul, Nat.add_mul]; omega)

theorem twC (hj : 1 ≤ j) {a ka M : Nat} (hM : 1 ≤ M) (c : Nat) (ha : a ≤ tower j (ka * M)) :
    c * a ≤ tower j ((ka + c) * M) :=
  tw_mono' (tw_cmul hj c ha) (by rw [Nat.add_mul]; have : c ≤ c * M := Nat.le_mul_of_pos_right _ hM; omega)

theorem twP5 (hj : 1 ≤ j) {a ka M : Nat} (hM : 1 ≤ M) (ha : a ≤ tower j (ka * M)) :
    a * a * a * a * a ≤ tower j ((5 * ka + 8) * M) :=
  tw_mono' (tw_pow5 hj ha) (by
    rw [Nat.add_mul, Nat.mul_assoc]; have : 8 ≤ 8 * M := Nat.le_mul_of_pos_right _ hM; omega)

end TowM

/-! ## Levels of towers -/

theorem tower_level_mono {k k' : Nat} (h : k ≤ k') (x : Nat) : tower k x ≤ tower k' x := by
  induction k' with
  | zero => rw [Nat.le_zero.1 h]; exact Nat.le_refl _
  | succ k' ih =>
    rcases Nat.lt_or_eq_of_le h with h | h
    · exact Nat.le_trans (ih (by omega)) (tower_le_succ _ _)
    · rw [h]; exact Nat.le_refl _

theorem two_pow_le_tower {j : Nat} (hj : 1 ≤ j) (x : Nat) : 2 ^ x ≤ tower j x :=
  tower_level_mono hj x

/-! ## The tables -/

theorem polyP_mono {a b : Nat} (h : a ≤ b) : polyP a ≤ polyP b := by
  unfold polyP; exact Nat.mul_le_mul (by omega) (by omega)

/-- The argument of the towers of the tables, for sizes at most `F`. -/
def Pb (F cap : Nat) : Nat := (F + 1) * (polyP F * cap + 2)

theorem pb_arg {F cap k N : Nat} (hk : k ≤ F) (hN : N ≤ F) : (k + 1) * (polyP N * cap + 2) ≤ Pb F cap :=
  Nat.mul_le_mul (by omega) (Nat.add_le_add_right (Nat.mul_le_mul_right _ (polyP_mono hN)) 2)

theorem pb_X {F cap N : Nat} (hN : N ≤ F) : polyP N * cap ≤ Pb F cap := by
  have h := pb_arg (cap := cap) (Nat.zero_le F) hN
  rw [Nat.zero_add, Nat.one_mul] at h
  omega

section Tables

variable {j cap F : Nat} {st : PSt}

theorem tb_valT (hj : 1 ≤ j) (hcap : 1 ≤ cap) (hi : MInv st) (hF : tsize st ≤ F) {k : Nat}
    (hk : k ≤ st.tt.length) : valT j cap st.x.length st.tt k ≤ tower j (Pb F cap) := by
  have hL : st.tt.length ≤ F := by unfold tsize at hF; omega
  have hN : st.x.length ≤ F := by unfold tsize at hF; omega
  exact tw_mono' (valT_le hj hcap hi.tt k) (pb_arg (by omega) hN)

theorem tb_rows (hj : 1 ≤ j) (hcap : 1 ≤ cap) (hi : MInv st) (hF : tsize st ≤ F) {k : Nat}
    (hk : k ≤ st.tt.length) : (rowsT j cap st.x.length st.tt k).length ≤ tower j (Pb F cap) := by
  have hN : st.x.length ≤ F := by unfold tsize at hF; omega
  exact tw_mono' (rowsT_length_le hj hcap hi.tt k hk) (pb_X hN)

theorem tb_envT (hj : 1 ≤ j) (hcap : 1 ≤ cap) (hi : MInv st) (hF : tsize st ≤ F) {c : Nat}
    (hc : c ≤ st.ct.length) : envT j cap st.x.length st.tt st.ct c ≤ tower j (Pb F cap) := by
  have hC : st.ct.length ≤ F := by unfold tsize at hF; omega
  have hN : st.x.length ≤ F := by unfold tsize at hF; omega
  exact tw_mono' (envT_le hj hcap hi.tt hi.ct c) (pb_arg (by omega) hN)

/-- The sum of a table over the type numbers, entrywise below `B`. -/
theorem typeTable_sum_le (tt : List (Nat × Nat)) (f : Nat → Nat) {B : Nat} (h : ∀ k ≤ tt.length, f k ≤ B) :
    (typeTable tt f).sum ≤ (tt.length + 1) * B := by
  have := sum_le_of_small (B := B) (l := typeTable tt f) (fun c hc => by
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hc
    exact h k (by have := List.mem_range.1 hk; omega))
  simpa [typeTable] using this

theorem tb_valSum (hj : 1 ≤ j) (hcap : 1 ≤ cap) (hi : MInv st) (hF : tsize st ≤ F) :
    (valTable j cap st.x.length st.tt).sum ≤ tower j (Pb F cap + (F + 1)) := by
  have hL : st.tt.length ≤ F := by unfold tsize at hF; omega
  have h := typeTable_sum_le st.tt _ (fun k hk => tb_valT (j := j) (cap := cap) hj hcap hi hF hk)
  exact Nat.le_trans h (Nat.le_trans (Nat.mul_le_mul_right _ (by omega)) (tw_cmul hj (F + 1) (Nat.le_refl _)))

theorem tb_cntSum (hj : 1 ≤ j) (hcap : 1 ≤ cap) (hi : MInv st) (hF : tsize st ≤ F) :
    (cntTable j cap st.x.length st.tt).sum ≤ tower j (Pb F cap + (F + 1)) := by
  have hL : st.tt.length ≤ F := by unfold tsize at hF; omega
  have h := typeTable_sum_le st.tt _ (fun k hk => tb_rows (j := j) (cap := cap) hj hcap hi hF hk)
  exact Nat.le_trans h (Nat.le_trans (Nat.mul_le_mul_right _ (by omega)) (tw_cmul hj (F + 1) (Nat.le_refl _)))

theorem tb_envSum (hj : 1 ≤ j) (hcap : 1 ≤ cap) (hi : MInv st) (hF : tsize st ≤ F) :
    (envTable j cap st.x.length st.tt st.ct).sum ≤ tower j (Pb F cap + (F + 1)) := by
  have hC : st.ct.length ≤ F := by unfold tsize at hF; omega
  have h := sum_le_of_small (B := tower j (Pb F cap)) (l := envTable j cap st.x.length st.tt st.ct)
    (fun c hc => by
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hc
      exact tb_envT hj hcap hi hF (by have := List.mem_range.1 hk; omega))
  have hl : (envTable j cap st.x.length st.tt st.ct).length = st.ct.length + 1 := by simp [envTable]
  rw [hl] at h
  exact Nat.le_trans h (Nat.le_trans (Nat.mul_le_mul_right _ (by omega)) (tw_cmul hj (F + 1) (Nat.le_refl _)))

theorem tb_rowsFlat (hj : 1 ≤ j) (hcap : 1 ≤ cap) (hi : MInv st) (hF : tsize st ≤ F) :
    (rowsFlat j cap st.x.length st.tt).length ≤ tower j (Pb F cap + Pb F cap + 2 + (F + 1)) := by
  have hL : st.tt.length ≤ F := by unfold tsize at hF; omega
  have hk : ∀ c ∈ (List.range (st.tt.length + 1)).map (fun k => (rowsT j cap st.x.length st.tt k).flatten),
      c.length ≤ tower j (Pb F cap + Pb F cap + 2) := by
    intro c hc
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hc
    have hkL : k ≤ st.tt.length := by have := List.mem_range.1 hk; omega
    have h₁ := length_flatten_le (L := rowsT j cap st.x.length st.tt k) (B := valT j cap st.x.length st.tt k)
      (fun r hr => Nat.le_of_eq (rowsT_row_length hi.tt hkL r hr))
    exact Nat.le_trans h₁ (tw_mul hj (tb_rows hj hcap hi hF hkL) (tb_valT hj hcap hi hF hkL))
  have h := length_flatten_le hk
  simp only [List.length_map, List.length_range] at h
  unfold rowsFlat
  exact Nat.le_trans h (Nat.le_trans (Nat.mul_le_mul_right _ (by omega)) (tw_cmul hj (F + 1) (Nat.le_refl _)))

/-- Every candidate count is at most a tower of `2 Pb + 2`. -/
theorem tb_cand (hj : 1 ≤ j) (hcap : 1 ≤ cap) (hi : MInv st) (hF : tsize st ≤ F) (k : Nat) :
    candNum j cap st.x.length st.tt k ≤ tower j (2 * Pb F cap + 2) := by
  have hN : st.x.length ≤ F := by unfold tsize at hF; omega
  cases k with
  | zero =>
    rw [candNum]
    refine Nat.le_trans (pow_le_two_pow _ _) (Nat.le_trans (two_pow_le_tower hj _) (tower_mono j ?_))
    have h₁ : (st.x.length + 3) * (st.x.length + 1) ≤ 2 * polyP st.x.length := by
      unfold polyP
      have e : 2 * ((st.x.length + 1) * (st.x.length + 2)) = (st.x.length + 1) * (2 * (st.x.length + 2)) := by
        rw [Nat.mul_left_comm]
      rw [Nat.mul_comm (st.x.length + 3) (st.x.length + 1), e]
      exact Nat.mul_le_mul_left _ (by omega)
    have h₂ : polyP st.x.length ≤ polyP st.x.length * cap := Nat.le_mul_of_pos_right _ hcap
    have h₃ := pb_X (cap := cap) hN
    omega
  | succ k =>
    rw [candNum]
    rcases hk : st.tt[k]? with _ | ⟨a, b⟩
    · exact Nat.zero_le _
    · simp only []
      split
      · rename_i hs
        have hkl : k < st.tt.length := (List.getElem?_eq_some_iff.1 hk).1
        have hab := hi.tt.2 k hkl
        rw [show st.tt[k] = (a, b) from (List.getElem?_eq_some_iff.1 hk).2] at hab
        refine tw_mono' (cand_le hcap hi.tt hk hab hs) ?_
        have := pb_X (cap := cap) hN
        omega
      · exact Nat.zero_le _

theorem tb_candSum (hj : 1 ≤ j) (hcap : 1 ≤ cap) (hi : MInv st) (hF : tsize st ≤ F) :
    ((List.range (st.tt.length + 1)).map (candNum j cap st.x.length st.tt)).sum ≤
      tower j (2 * Pb F cap + 2 + (F + 1)) := by
  have hL : st.tt.length ≤ F := by unfold tsize at hF; omega
  have h := sum_le_of_small (B := tower j (2 * Pb F cap + 2))
    (l := (List.range (st.tt.length + 1)).map (candNum j cap st.x.length st.tt))
    (fun c hc => by obtain ⟨k, _, rfl⟩ := List.mem_map.1 hc; exact tb_cand hj hcap hi hF k)
  simp only [List.length_map, List.length_range] at h
  exact Nat.le_trans h (Nat.le_trans (Nat.mul_le_mul_right _ (by omega)) (tw_cmul hj (F + 1) (Nat.le_refl _)))

/-- The starting rule values: zeros of the lengths of the rule types. -/
def zeroT (j cap : Nat) (st : PSt) : List (List Nat) :=
  st.rt.map (fun t => List.replicate (valT j cap st.x.length st.tt t) 0)

theorem tb_zeroT (hj : 1 ≤ j) (hcap : 1 ≤ cap) (hi : MInv st) (hF : tsize st ≤ F) :
    (zeroT j cap st).flatten.length ≤ tower j (Pb F cap + F) := by
  have hR : st.rt.length ≤ F := by unfold tsize at hF; omega
  have h := length_flatten_le (L := zeroT j cap st) (B := tower j (Pb F cap)) (fun c hc => by
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hc
    rw [List.length_replicate]; exact tb_valT hj hcap hi hF (hi.rt t ht))
  have hl : (zeroT j cap st).length = st.rt.length := by simp [zeroT]
  rw [hl] at h
  exact Nat.le_trans h (Nat.le_trans (Nat.mul_le_mul_right _ hR) (tw_cmul hj F (Nat.le_refl _)))

theorem tb_fuel (hj : 1 ≤ j) (hcap : 1 ≤ cap) (hi : MInv st) (hF : tsize st ≤ F) :
    (st.rt.map (valT j cap st.x.length st.tt)).sum ≤ tower j (Pb F cap + F) := by
  have hR : st.rt.length ≤ F := by unfold tsize at hF; omega
  have h := sum_le_of_small (B := tower j (Pb F cap)) (l := st.rt.map (valT j cap st.x.length st.tt))
    (fun c hc => by obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hc; exact tb_valT hj hcap hi hF (hi.rt t ht))
  rw [List.length_map] at h
  exact Nat.le_trans h (Nat.le_trans (Nat.mul_le_mul_right _ hR) (tw_cmul hj F (Nat.le_refl _)))

end Tables

/-! ## The evaluation on an accepted reading -/

/-- **On an accepted reading whose orders pass, the evaluation costs at most `evBound`.** -/
theorem evalCost_final {j : Nat} (hj : 1 ≤ j) (w : List Bool) (hok : (finalSt (ofBits w)).ok = true)
    (ho : ordOK j (finalSt (ofBits w)) = true) :
    evalCost j (capOf w) (finalSt (ofBits w)) ≤
      evBound j (capOf w) (finalSt (ofBits w)) (zeroT j (capOf w) (finalSt (ofBits w))) := by
  have hlt := finalSt_ltOK (ofBits w)
  rcases hd : deser (ofBits w) with _ | ⟨g, s, x⟩
  · have := final_of_fails (read_fail (fun _ _ _ _ _ h => by rw [hd] at h; cases h))
    rw [this] at hok; cases hok
  · rcases hcr : checkRules g with _ | bis
    · have := final_of_fails (read_fail (fun _ _ _ _ _ h₁ h₂ => by
        rw [hd] at h₁; cases h₁; rw [hcr] at h₂; cases h₂))
      rw [this] at hok; cases hok
    · rcases hinf : inferE g.types [] s with _ | ⟨_ | ⟨a, b⟩, is⟩
      · have := final_of_fails (read_fail (fun _ _ _ _ _ h₁ _ h₃ => by
          rw [hd] at h₁; cases h₁; rw [hinf] at h₃; cases h₃))
        rw [this] at hok; cases hok
      · obtain ⟨n, st, hreach, hr, hn⟩ := read_ok hd hcr hinf
        have hfin : finalSt (ofBits w) = st := final_of_reach hreach hr.ctl (by omega)
        rw [hfin] at ho hlt ⊢
        have hgo := (ordOK_iff j hr hcr hinf).1 ho
        obtain ⟨hrt, hit⟩ := itemsOK j hj hd hcr hinf hr hgo
        have hcap : 3 * (ofBits w).length + 2 ≤ capOf w := by
          have := ofBits_length_le w; unfold capOf; omega
        obtain ⟨G, _, hbis⟩ := checkRules_sound hcr
        have hx : st.x.map Char.ofNat = x := by rw [hr.x, codes_chars]
        have hr' : ReadOK st g.types bis is (st.x.map Char.ofNat) := by rw [hx]; exact hr
        have hrt' : ∀ t ∈ st.rt, need j (capOf w) st.tt t := fun t ht => need_cap_mono hcap (hrt t ht)
        have h := evalCost_le G hr' hbis (fun it hi => itemOK_cap_mono hcap (hit it hi)) hrt'
          (read_x_codes hr) hlt
        rw [← zero_iter G hr' hrt'] at h
        simpa only [zeroT, List.length_map] using h
      · have := final_of_fails (read_fail (fun _ _ _ _ _ h₁ _ h₃ => by
          rw [hd] at h₁; cases h₁; rw [hinf] at h₃; cases h₃))
        rw [this] at hok; cases hok

end Shallot.MacroPeg.Mach
