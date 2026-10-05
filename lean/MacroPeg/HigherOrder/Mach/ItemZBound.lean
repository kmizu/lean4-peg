import MacroPeg.HigherOrder.Mach.RunBound
import MacroPeg.HigherOrder.Mach.ValueInv

/-!
# The size an item program sees

On a stack of at most `B` numbers with small codes, `itemZ` is at most `(N + 1114116) · (2 B + evalW)` (`itemZ_le`),
where `evalW` collects the sizes of the tables and of the rule values.
-/

namespace Shallot.MacroPeg.Mach

open Shallot.MacroPeg.HO
open Shallot.MacroPeg.Flat

theorem sum_le_of_small {B : Nat} {l : List Nat} (h : Small B l) : l.sum ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons c l ih =>
    simp only [List.sum_cons, List.length_cons, Nat.succ_mul]
    have := h c List.mem_cons_self
    have := ih (fun d hd => h d (List.mem_cons_of_mem _ hd))
    omega

theorem evFlat_small {B : Nat} {vs : List (List Nat)} (h : ∀ v ∈ vs, Small B v) : Small B (evFlat vs) := by
  intro c hc
  simp only [evFlat, List.mem_flatten, List.mem_reverse] at hc
  obtain ⟨v, hv, hcv⟩ := hc
  exact h v hv c hcv

theorem flatten_small {B : Nat} {L : List (List Nat)} (h : ∀ v ∈ L, Small B v) : Small B L.flatten :=
  small_flatten h

theorem mem_sum_le {l : List Nat} {a : Nat} (h : a ∈ l) : a ≤ l.sum := le_sum_of_mem h

/-- The sizes of the tables and of the rule values. -/
def evalW (j cap : Nat) (st : PSt) (Tf : List (List Nat)) : Nat :=
  2 + (rowsFlat j cap st.x.length st.tt).length + Tf.flatten.length + Tf.length + st.ct.length + st.lt.length +
    (encLits st.lt).length + (envTable j cap st.x.length st.tt st.ct).sum +
    (valTable j cap st.x.length st.tt).sum + (cntTable j cap st.x.length st.tt).sum +
    (encBodies st.bodies).sum + (encItems st.start).sum + st.x.length + st.tt.length +
    pushBound j cap (st.x.map Char.ofNat) st.tt st.ct Tf

theorem item_nums_le {st : PSt} {it : MItem} (h : it ∈ st.bodies.flatten ++ st.start) :
    it.a + it.b + it.ctx ≤ 3 * ((encBodies st.bodies).sum + (encItems st.start).sum) := by
  have hsub : ∀ c ∈ encItem it, c ≤ (encBodies st.bodies).sum + (encItems st.start).sum := by
    intro c hc
    rcases List.mem_append.1 h with h | h
    · obtain ⟨b, hb, hib⟩ := List.mem_flatten.1 h
      have : c ∈ encBodies st.bodies := by
        simp only [encBodies, List.mem_flatMap, List.mem_append]
        exact ⟨b, hb, .inl (by simp only [encItems, List.mem_flatMap]; exact ⟨it, hib, hc⟩)⟩
      have := mem_sum_le this; omega
    · have : c ∈ encItems st.start := by simp only [encItems, List.mem_flatMap]; exact ⟨it, h, hc⟩
      have := mem_sum_le this; omega
  have ha := hsub it.a (by simp [encItem])
  have hb := hsub it.b (by simp [encItem])
  have hc := hsub it.ctx (by simp [encItem])
  omega

theorem encLits_sum_le {lt : List (List Nat)} (h : ∀ l ∈ lt, ∀ c ∈ l, c < 1114112) :
    (encLits lt).sum ≤ (encLits lt).length * 1114113 := by
  refine sum_le_of_small (fun c hc => ?_)
  simp only [encLits, List.mem_flatMap, List.mem_append, List.mem_map, List.mem_singleton] at hc
  obtain ⟨l, hl, (⟨d, hd, rfl⟩ | rfl)⟩ := hc
  · have := h l hl d hd; omega
  · omega

/-- **The size an item program sees.** -/
theorem itemZ_le {j cap : Nat} {st : PSt} {Tf : List (List Nat)} {it : MItem} {vs : List (List Nat)} {B : Nat}
    (hw : TTWF st.tt) (hc : CTWF st.tt st.ct) (hcx : it.ctx ≤ st.ct.length)
    (hmem : it ∈ st.bodies.flatten ++ st.start) (hvs : ∀ v ∈ vs, Small (st.x.length + 2) v)
    (hB : (evFlat vs).length ≤ B) (hTf : ∀ f ∈ Tf, Small (st.x.length + 2) f) (hx : ∀ c ∈ st.x, c < 1114112)
    (hlt : LtOK st) :
    itemZ j cap st Tf it vs ≤ (st.x.length + 1114116) * (2 * B + evalW j cap st Tf) := by
  have hxl : (st.x.map Char.ofNat).length = st.x.length := by simp
  have hTf' : ∀ f ∈ Tf, Small ((st.x.map Char.ofNat).length + 2) f := by rw [hxl]; exact hTf
  have hvs' : ∀ v ∈ vs, Small ((st.x.map Char.ofNat).length + 2) v := by rw [hxl]; exact hvs
  -- the output
  have hout := stepT_size (j := j) (cap := cap) (x := st.x.map Char.ofNat) (lt := st.lt) (Tf := Tf) hw hc hcx vs
  have hcod := stepT_codes (j := j) (cap := cap) (lt := st.lt) hw hc hcx hvs' hTf'
  rw [hxl] at hcod
  -- sums of small numbers
  have s₁ := sum_le_of_small (evFlat_small hvs)
  have s₂ := sum_le_of_small (evFlat_small hcod)
  have s₃ := sum_le_of_small (flatten_small hTf)
  have hrows : Small (st.x.length + 2) (rowsFlat j cap st.x.length st.tt) := by
    refine small_flatten (fun r hr => ?_)
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hr
    exact small_flatten (rowsT_small hw (by have := List.mem_range.1 hk; omega))
  have s₄ := sum_le_of_small hrows
  have s₅ := sum_le_of_small (B := 1114112) (l := st.x) (fun c hc => by have := hx c hc; omega)
  have s₆ := encLits_sum_le hlt
  have hn := item_nums_le hmem
  -- every term, against its share of the bound
  obtain ⟨M, hM⟩ : ∃ M, M = st.x.length + 1114116 := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W, W = evalW j cap st Tf := ⟨_, rfl⟩
  obtain ⟨pB, hpB⟩ : ∃ pB, pB = pushBound j cap (st.x.map Char.ofNat) st.tt st.ct Tf := ⟨_, rfl⟩
  rw [← hpB] at hout
  rw [← hM, ← hW]
  have lin : ∀ a c b m : Nat, a ≤ b → c + 1 ≤ m → a * c + a ≤ b * m := fun a c b m hab hcm => by
    have := Nat.mul_le_mul hab hcm
    rw [Nat.mul_succ] at this; omega
  have m₁ := lin (evFlat vs).length (st.x.length + 2) B M hB (by omega)
  have m₂ := lin (evFlat (stepT j cap (st.x.map Char.ofNat) st.tt st.ct st.lt Tf it vs)).length (st.x.length + 2)
    (B + pB) M (by omega) (by omega)
  have m₃ := lin Tf.flatten.length (st.x.length + 2) Tf.flatten.length M (Nat.le_refl _) (by omega)
  have m₄ := lin (rowsFlat j cap st.x.length st.tt).length (st.x.length + 2) (rowsFlat j cap st.x.length st.tt).length
    M (Nat.le_refl _) (by omega)
  have m₅ := lin st.x.length 1114112 st.x.length M (Nat.le_refl _) (by omega)
  have m₆ := lin (encLits st.lt).length 1114113 (encLits st.lt).length M (Nat.le_refl _) (by omega)
  have hWsplit : M * W = M * 2 + M * (rowsFlat j cap st.x.length st.tt).length + M * Tf.flatten.length +
      M * Tf.length + M * st.ct.length + M * st.lt.length + M * (encLits st.lt).length +
      M * (envTable j cap st.x.length st.tt st.ct).sum + M * (valTable j cap st.x.length st.tt).sum +
      M * (cntTable j cap st.x.length st.tt).sum + M * (encBodies st.bodies).sum + M * (encItems st.start).sum +
      M * st.x.length + M * st.tt.length + M * pB := by
    rw [hW, hpB]; simp only [evalW, Nat.mul_add]
  have hBsplit : M * (2 * B + W) = 2 * (B * M) + M * W := by
    rw [Nat.mul_add, Nat.mul_comm M (2 * B), Nat.mul_assoc, Nat.mul_comm B M]
  have hBpB : (B + pB) * M = B * M + pB * M := Nat.add_mul _ _ _
  have c₁ : (rowsFlat j cap st.x.length st.tt).length * M = M * (rowsFlat j cap st.x.length st.tt).length :=
    Nat.mul_comm _ _
  have c₂ : Tf.flatten.length * M = M * Tf.flatten.length := Nat.mul_comm _ _
  have c₃ : st.x.length * M = M * st.x.length := Nat.mul_comm _ _
  have c₄ : (encLits st.lt).length * M = M * (encLits st.lt).length := Nat.mul_comm _ _
  have c₅ : pB * M = M * pB := Nat.mul_comm _ _
  have g₁ : ∀ a, a ≤ M * a := fun a => Nat.le_mul_of_pos_left a (by omega)
  have g₂ := g₁ (envTable j cap st.x.length st.tt st.ct).sum
  have g₃ := g₁ (valTable j cap st.x.length st.tt).sum
  have g₄ := g₁ (cntTable j cap st.x.length st.tt).sum
  have g₅ := g₁ Tf.length
  have g₆ := g₁ st.ct.length
  have g₇ := g₁ st.lt.length
  have g₈ := g₁ st.tt.length
  have g₉ : 3 * ((encBodies st.bodies).sum + (encItems st.start).sum) ≤
      M * (encBodies st.bodies).sum + M * (encItems st.start).sum := by
    have : 3 * ((encBodies st.bodies).sum + (encItems st.start).sum) ≤
        M * ((encBodies st.bodies).sum + (encItems st.start).sum) := Nat.mul_le_mul_right _ (by omega)
    rwa [Nat.mul_add M] at this
  have g₁₀ : 2 ≤ M * 2 := by omega
  unfold itemZ
  rw [hBsplit, hWsplit]
  omega

end Shallot.MacroPeg.Mach
