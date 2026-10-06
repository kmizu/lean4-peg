import MacroPeg.HigherOrder.Mach.Decide
import MacroPeg.HigherOrder.Mach.ItemsOK

/-!
# The decision with the tables

The machine evaluates with the tables of the small types, with the cap `3 · (number of bits) + 2`
(`numDecideT`). A larger cap keeps every type that was small small (`sizeNum_cap_mono`), so this is the decision
from the reading machine (`numDecideT_eq`) and decides the uniform problem (`numDecideT_iff`).
-/

namespace Shallot.MacroPeg.Mach

open Shallot.MacroPeg.HO
open Shallot.MacroPeg.Flat

/-! ## A larger cap -/

theorem sizeNum_cap_mono {cap cap' : Nat} (hc : cap ≤ cap') (tt : List (Nat × Nat)) :
    ∀ k, sizeNum cap tt k < cap → sizeNum cap' tt k = sizeNum cap tt k
  | 0, _ => by rw [sizeNum, sizeNum]
  | k + 1, h => by
    rw [sizeNum] at h ⊢
    rw [sizeNum]
    rcases hk : tt[k]? with _ | ⟨a, b⟩
    · rw [hk] at h; simp at h
    · rw [hk] at h; simp only [] at h ⊢
      split
      · rename_i hab
        rw [if_pos hab] at h
        have h₁ : sizeNum cap tt a + sizeNum cap tt b + 1 < cap := by
          rcases Nat.le_total cap (sizeNum cap tt a + sizeNum cap tt b + 1) with hc' | hc'
          · rw [Nat.min_eq_left hc'] at h; omega
          · rw [Nat.min_eq_right hc'] at h; exact h
        rw [sizeNum_cap_mono hc tt a (by omega), sizeNum_cap_mono hc tt b (by omega),
          Nat.min_eq_right (by omega), Nat.min_eq_right (by omega)]
      · rename_i hab
        rw [if_neg hab] at h; omega

variable {j cap cap' : Nat} {tt ct : List (Nat × Nat)}

theorem small_cap_mono (hc : cap ≤ cap') {k : Nat} (h : small j cap tt k) : small j cap' tt k :=
  ⟨h.1, by have := h.2; rw [sizeNum_cap_mono hc tt k h.2]; omega⟩

theorem need_cap_mono (hc : cap ≤ cap') {k : Nat} (h : need j cap tt k) : need j cap' tt k :=
  ⟨h.1, by have := h.2; rw [sizeNum_cap_mono hc tt k h.2]; omega⟩

theorem ctxSmall_cap_mono (hc : cap ≤ cap') : ∀ c, ctxSmall j cap tt ct c → ctxSmall j cap' tt ct c
  | 0, _ => by rw [ctxSmall]; trivial
  | k + 1, h => by
    rw [ctxSmall] at h ⊢
    rcases hk : ct[k]? with _ | ⟨par, t⟩
    · trivial
    · rw [hk] at h; simp only [] at h ⊢
      split
      · rename_i hp
        rw [if_pos hp] at h
        exact ⟨small_cap_mono hc h.1, ctxSmall_cap_mono hc par h.2⟩
      · rename_i hp
        rw [if_neg hp] at h; exact h

theorem itemOK_cap_mono (hc : cap ≤ cap') {it : MItem} (h : ItemOK j cap tt ct it) : ItemOK j cap' tt ct it :=
  ⟨ctxSmall_cap_mono hc _ h.1, fun h9 => small_cap_mono hc (h.2.1 h9),
    fun h12 => ⟨small_cap_mono hc (h.2.2 h12).1, need_cap_mono hc (h.2.2 h12).2⟩⟩

/-! ## The decision -/

/-- The cap for `bits`. -/
def capOf (bits : List Bool) : Nat := 3 * bits.length + 2

/-- The decision with the tables. -/
def numDecideT (j : Nat) (bits : List Bool) : Bool :=
  let st := finalSt (Complexity.ofBits bits)
  st.ok && ordOK j st &&
    (startCodeT j (capOf bits) (st.x.map Char.ofNat) st.tt st.ct st.lt st.rt st.bodies st.start == 2)

theorem ofBits_length_le : ∀ bits : List Bool, (Complexity.ofBits bits).length ≤ bits.length
  | b₃ :: b₂ :: b₁ :: b₀ :: bs => by
    have := ofBits_length_le bs; simp [Complexity.ofBits]; omega
  | [] => by simp [Complexity.ofBits]
  | [_] => by simp [Complexity.ofBits]
  | [_, _] => by simp [Complexity.ofBits]
  | [_, _, _] => by simp [Complexity.ofBits]

theorem numDecideT_eq (j : Nat) (hj : 1 ≤ j) (bits : List Bool) : numDecideT j bits = numDecide j bits := by
  unfold numDecideT numDecide
  simp only []
  rcases hd : deser (Complexity.ofBits bits) with _ | ⟨g, s, x⟩
  · have := final_of_fails (read_fail (fun _ _ _ _ _ h => by rw [hd] at h; cases h))
    simp [this]
  · rcases hcr : checkRules g with _ | bis
    · have := final_of_fails (read_fail (fun _ _ _ _ _ h₁ h₂ => by
        rw [hd] at h₁; cases h₁; rw [hcr] at h₂; cases h₂))
      simp [this]
    · rcases hinf : inferE g.types [] s with _ | ⟨_ | ⟨a, b⟩, is⟩
      · have := final_of_fails (read_fail (fun _ _ _ _ _ h₁ _ h₃ => by
          rw [hd] at h₁; cases h₁; rw [hinf] at h₃; cases h₃))
        simp [this]
      · obtain ⟨n, st, hreach, hr, hn⟩ := read_ok hd hcr hinf
        have hfin : finalSt (Complexity.ofBits bits) = st := final_of_reach hreach hr.ctl (by omega)
        rw [hfin]
        by_cases ho : ordOK j st = true
        · have hgo := (ordOK_iff j hr hcr hinf).1 ho
          obtain ⟨hrt, hit⟩ := itemsOK j hj hd hcr hinf hr hgo
          have hcap : 3 * (Complexity.ofBits bits).length + 2 ≤ capOf bits := by
            have := ofBits_length_le bits; unfold capOf; omega
          rw [startCodeT_eq (fun t ht => need_cap_mono hcap (hrt t ht))
            (fun it hi => itemOK_cap_mono hcap (hit it hi))]
        · simp [ho]
      · have := final_of_fails (read_fail (fun _ _ _ _ _ h₁ h₂ h₃ => by
          rw [hd] at h₁; cases h₁; rw [hinf] at h₃; cases h₃))
        simp [this]

/-- **The decision with the tables decides the uniform problem.** -/
theorem numDecideT_iff (j : Nat) (hj : 1 ≤ j) (bits : List Bool) :
    numDecideT j bits = true ↔ KExp.UMPEG j bits := by
  rw [numDecideT_eq j hj]; exact numDecide_iff j bits

end Shallot.MacroPeg.Mach
