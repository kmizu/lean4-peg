import MacroPeg.HigherOrder.Mach.CodesBound

/-!
# Running items: the stack stays bounded

Running the items `l` adds at most `l.length · pushBound` numbers to the stack, and keeps all codes at most `N + 2`
(`runT_bounded`). So every item program along the run sees a stack of at most that size, and the steps of the run
are at most `l.length` times the largest item cost at that size (`runCost_le`).
-/

namespace Shallot.MacroPeg.Mach

open Shallot.MacroPeg.HO
open Shallot.MacroPeg.Flat

variable {j cap : Nat} {x : List Char} {tt ct : List (Nat × Nat)} {lt Tf : List (List Nat)}

/-- **The run keeps the stack bounded.** -/
theorem runT_bounded (hw : TTWF tt) (hc : CTWF tt ct) (hTf : ∀ f ∈ Tf, Small (x.length + 2) f) :
    ∀ (l : List MItem), (∀ it ∈ l, it.ctx ≤ ct.length) → ∀ vs, (∀ v ∈ vs, Small (x.length + 2) v) →
      (evFlat (runT j cap x tt ct lt Tf l vs)).length ≤ (evFlat vs).length + l.length * pushBound j cap x tt ct Tf ∧
        ∀ v ∈ runT j cap x tt ct lt Tf l vs, Small (x.length + 2) v
  | [], _, vs, hvs => ⟨by simp [runT], hvs⟩
  | it :: l, hl, vs, hvs => by
    have hcx := hl it List.mem_cons_self
    have h₁ := stepT_size (j := j) (cap := cap) (x := x) (lt := lt) (Tf := Tf) hw hc hcx vs
    have h₂ := stepT_codes (j := j) (cap := cap) (lt := lt) hw hc hcx hvs hTf
    have ih := runT_bounded hw hc hTf l (fun i hi => hl i (List.mem_cons_of_mem _ hi)) _ h₂
    simp only [runT, List.foldl_cons] at ih ⊢
    refine ⟨?_, ih.2⟩
    simp only [List.length_cons, Nat.succ_mul]
    have := ih.1
    omega

/-- **The steps of a run**, when every item costs at most `K` on the stacks of the run. -/
theorem runCost_le (st : PSt) (hw : TTWF st.tt) (hc : CTWF st.tt st.ct)
    (hTf : ∀ f ∈ Tf, Small (st.x.length + 2) f) (K : Nat) :
    ∀ (l : List MItem) (vs : List (List Nat)) (B : Nat), (∀ it ∈ l, it.ctx ≤ st.ct.length) →
      (∀ v ∈ vs, Small (st.x.length + 2) v) →
      (evFlat vs).length + l.length * pushBound j cap (st.x.map Char.ofNat) st.tt st.ct Tf ≤ B →
      (∀ it ∈ l, ∀ vs', (evFlat vs').length ≤ B → (∀ v ∈ vs', Small (st.x.length + 2) v) →
        itemCost j cap st Tf it vs' ≤ K) →
      runCost j cap st Tf l vs ≤ l.length * (K + 500)
  | [], _, _, _, _, _, _ => by simp [runCost]
  | it :: l, vs, B, hl, hvs, hB, hK => by
    have hcx := hl it List.mem_cons_self
    have hx : (st.x.map Char.ofNat).length = st.x.length := by simp
    have hTf' : ∀ f ∈ Tf, Small ((st.x.map Char.ofNat).length + 2) f := by rw [hx]; exact hTf
    have hvs' : ∀ v ∈ vs, Small ((st.x.map Char.ofNat).length + 2) v := by rw [hx]; exact hvs
    have h₁ := stepT_size (j := j) (cap := cap) (x := st.x.map Char.ofNat) (lt := st.lt) (Tf := Tf) hw hc hcx vs
    have h₂ := stepT_codes (j := j) (cap := cap) (lt := st.lt) hw hc hcx hvs' hTf'
    rw [hx] at h₂
    have hK₀ := hK it List.mem_cons_self vs (by simp only [List.length_cons, Nat.succ_mul] at hB; omega) hvs
    have ih := runCost_le st hw hc hTf K l _ B (fun i hi => hl i (List.mem_cons_of_mem _ hi)) h₂
      (by simp only [List.length_cons, Nat.succ_mul] at hB; omega) (fun i hi => hK i (List.mem_cons_of_mem _ hi))
    simp only [runCost, List.length_cons, Nat.succ_mul]
    omega

end Shallot.MacroPeg.Mach
