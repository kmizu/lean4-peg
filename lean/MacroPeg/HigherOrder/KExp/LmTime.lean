import MacroPeg.HigherOrder.KExp.Hard
import Complexity.ListTime
import Complexity.NStackIO
import Complexity.NSpace

/-!
# A list program with a tower-of-height-`j` budget puts a language in `KEXP j`

`kexp_of_lm`: if a list program decides `L` within `tower j (c (n+1)^d)` steps with lists of that length, then
`L ∈ KEXP j` (for `j ≥ 1`): the machine of `lm_time` halts within `lmTime`, a polynomial in the budget, and a
polynomial in `tower j (·)` of a polynomial is again below `tower j` of a polynomial (`TowerPoly` is closed under sums
and products, `tower_mul`, `tower_add`).
-/

namespace Shallot.MacroPeg.KExp

open Complexity
open Shallot.MacroPeg.HO

/-! ## Functions below a tower of a polynomial -/

/-- `f n ≤ tower j (c (n+1)^d)` for some `c`, `d`. -/
def TowerPoly (j : Nat) (f : Nat → Nat) : Prop := ∃ c d, ∀ n, f n ≤ tower j (c * (n + 1) ^ d)

theorem pow_le_pow_add (n d e : Nat) : (n + 1) ^ d ≤ (n + 1) ^ (d + e) := Nat.pow_le_pow_right (by omega) (by omega)

/-- Two bounds share one exponent and one constant. -/
theorem towerPoly_common {j : Nat} {f g : Nat → Nat} (hf : TowerPoly j f) (hg : TowerPoly j g) :
    ∃ c d, ∀ n, f n ≤ tower j (c * (n + 1) ^ d) ∧ g n ≤ tower j (c * (n + 1) ^ d) := by
  obtain ⟨c₁, d₁, h₁⟩ := hf
  obtain ⟨c₂, d₂, h₂⟩ := hg
  refine ⟨c₁ + c₂, d₁ + d₂, fun n => ⟨Nat.le_trans (h₁ n) (tower_mono _ ?_), Nat.le_trans (h₂ n) (tower_mono _ ?_)⟩⟩
  · exact Nat.mul_le_mul (by omega) (pow_le_pow_add n d₁ d₂)
  · exact Nat.mul_le_mul (by omega) (by rw [Nat.add_comm d₁]; exact pow_le_pow_add n d₂ d₁)

theorem towerPoly_mono {j : Nat} {f g : Nat → Nat} (hg : TowerPoly j g) (h : ∀ n, f n ≤ g n) : TowerPoly j f :=
  let ⟨c, d, hc⟩ := hg; ⟨c, d, fun n => Nat.le_trans (h n) (hc n)⟩

theorem towerPoly_poly {j : Nat} {f : Nat → Nat} (hf : IsPoly f) : TowerPoly j f :=
  let ⟨c, d, hc⟩ := hf; ⟨c, d, fun n => Nat.le_trans (hc n) (le_tower j _)⟩

/-- The constant `c (n+1)^d` doubled plus two is again of that form. -/
theorem double_plus_two (c d n : Nat) : 2 * (c * (n + 1) ^ d) + 2 ≤ (2 * c + 2) * (n + 1) ^ d := by
  have : 1 ≤ (n + 1) ^ d := Nat.pow_pos (by omega)
  rw [Nat.add_mul, Nat.mul_assoc]; omega

theorem towerPoly_add {j : Nat} {f g : Nat → Nat} (hf : TowerPoly j f) (hg : TowerPoly j g) :
    TowerPoly j (fun n => f n + g n) := by
  obtain ⟨c, d, h⟩ := towerPoly_common hf hg
  refine ⟨2 * c + 2, d, fun n => ?_⟩
  show f n + g n ≤ _
  have := tower_add j (c * (n + 1) ^ d) (c * (n + 1) ^ d)
  have := tower_mono j (show c * (n + 1) ^ d + c * (n + 1) ^ d + 2 ≤ (2 * c + 2) * (n + 1) ^ d by
    have := double_plus_two c d n; omega)
  have := (h n).1; have := (h n).2
  omega

theorem towerPoly_mul {j : Nat} (hj : 1 ≤ j) {f g : Nat → Nat} (hf : TowerPoly j f) (hg : TowerPoly j g) :
    TowerPoly j (fun n => f n * g n) := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  obtain ⟨c, d, h⟩ := towerPoly_common hf hg
  refine ⟨2 * c + 2, d, fun n => ?_⟩
  have hm := tower_mul j' (c * (n + 1) ^ d) (c * (n + 1) ^ d)
  have := tower_mono (j' + 1) (show c * (n + 1) ^ d + c * (n + 1) ^ d + 2 ≤ (2 * c + 2) * (n + 1) ^ d by
    have := double_plus_two c d n; omega)
  exact Nat.le_trans (Nat.mul_le_mul (h n).1 (h n).2) (Nat.le_trans hm this)

theorem towerPoly_const {j : Nat} (a : Nat) : TowerPoly j (fun _ => a) := towerPoly_poly (isPoly_const a)
theorem towerPoly_id {j : Nat} : TowerPoly j (fun n => n) := towerPoly_poly isPoly_id

/-! ## From list programs -/

/-- **List programs within a `tower j` budget decide `KEXP j` languages** (`j ≥ 1`). -/
theorem kexp_of_lm {j : Nat} (hj : 1 ≤ j) {k : Nat} (h1 : 1 < k) (lp : LProg k) (E : Nat) (hE : 2 ≤ E)
    (hc : lp.ConstOK E) (L : Lang) (s T : Nat → Nat) (hs : TowerPoly j s) (hT : TowerPoly j T)
    (h : ∀ w, ∃ t b L', t ≤ T w.length ∧ LExec (LenOK (s w.length)) lp (initLists k w) t (.stop b L') ∧
      (b = true ↔ L w)) :
    KEXP j L := by
  obtain ⟨M, hdec, hhalt⟩ := lm_time h1 lp E hE hc L s T h
  have hlm : TowerPoly j (lmTime s T) := by
    unfold lmTime
    refine towerPoly_add (towerPoly_poly ?_) (towerPoly_mul hj hT ?_)
    · exact isPoly_add (isPoly_mul (isPoly_const 4) isPoly_id) (isPoly_const 8)
    · exact towerPoly_add (towerPoly_mul hj (towerPoly_const 8) (towerPoly_add hs
        (towerPoly_add towerPoly_id (towerPoly_const 2)))) (towerPoly_const 20)
  obtain ⟨c, d, hcd⟩ := hlm
  exact ⟨k, M, lmTime s T, c, d, hcd, hdec, hhalt⟩

/-- **Stack machines over numbers within a `tower j` budget decide `KEXP j` languages** (`j ≥ 1`): on input `w`
(stack `0` holds the bits, `nInit`), the machine halts with the answer within `T |w|` steps, every state fitting in
`B |w|`. -/
theorem kexp_of_nprog {j : Nat} (hj : 1 ≤ j) {K : Nat} (hK : 1 < K) (p : NProg K) (L : Lang) (B T : Nat → Nat)
    (hB : TowerPoly j B) (hT : TowerPoly j T)
    (h : ∀ w, ∃ t b S', t ≤ T w.length ∧ NExec (NFits (B w.length)) p (nInit K w) t (.stop b S') ∧
      (b = true ↔ L w)) :
    KEXP j L := by
  let B' : Nat → Nat := fun n => B n + (2 * n + 2)
  have hB' : TowerPoly j B' := towerPoly_add hB (towerPoly_poly
    (isPoly_add (isPoly_mul (isPoly_const 2) isPoly_id) (isPoly_const 2)))
  let T' : Nat → Nat := fun n => (n + 1) * 5 + T n * ncost (B' n)
  have hT' : TowerPoly j T' := by
    refine towerPoly_add (towerPoly_poly (isPoly_mul (isPoly_add isPoly_id (isPoly_const 1)) (isPoly_const 5)))
      (towerPoly_mul hj hT ?_)
    unfold ncost
    exact towerPoly_add (towerPoly_mul hj (towerPoly_const 8) hB') (towerPoly_const 16)
  refine kexp_of_lm hj (k := K + 1) (by omega) (.seq (importP hK) p.compile) 3 (by decide) (nprog_constOK hK p) L
    B' T' hB' hT' (fun w => ?_)
  obtain ⟨t, b, S', ht, hx, hb⟩ := h w
  obtain ⟨t', ht', hx'⟩ := nprog_lexec hK p w (B := B' w.length) (by simp only [B']; omega)
    (hx.mono (fun _ hS => hS.mono (by simp only [B']; omega)))
  refine ⟨t', b, _, ?_, hx', hb⟩
  have : t * ncost (B' w.length) ≤ T w.length * ncost (B' w.length) := Nat.mul_le_mul_right _ ht
  simp only [T']; omega

/-- **Stack machines within a `tower j` time budget decide `KEXP j` languages** (`j ≥ 1`): only the time is
bounded; the space follows from it (`nexec_space`). -/
theorem kexp_of_nprog_time {j : Nat} (hj : 1 ≤ j) {K : Nat} (hK : 1 < K) (p : NProg K) (L : Lang) (T : Nat → Nat)
    (hT : TowerPoly j T)
    (h : ∀ w, ∃ t b S', t ≤ T w.length ∧ NExec (fun _ => True) p (nInit K w) t (.stop b S') ∧
      (b = true ↔ L w)) :
    KEXP j L := by
  let B : Nat → Nat := fun n => 2 * n + T n * (1 + T n + 1) + 2
  have hB : TowerPoly j B := by
    refine towerPoly_add (towerPoly_add (towerPoly_poly (isPoly_mul (isPoly_const 2) isPoly_id))
      (towerPoly_mul hj hT (towerPoly_add (towerPoly_add (towerPoly_const 1) hT) (towerPoly_const 1))))
      (towerPoly_const 2)
  refine kexp_of_nprog hj hK p L B T hB hT (fun w => ?_)
  obtain ⟨t, b, S', ht, hx, hb⟩ := h w
  refine ⟨t, b, S', ht, (nexec_space hx 1 (2 * w.length) (bnd_nInit w)).2 _ ?_, hb⟩
  have : grow 1 t ≤ T w.length * (1 + T w.length + 1) := Nat.mul_le_mul ht (by omega)
  simp only [B]; omega

end Shallot.MacroPeg.KExp
