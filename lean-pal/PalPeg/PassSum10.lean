import PalPeg.PassSum9

namespace PalPeg
namespace PassSum10
universe u
variable {α : Type u} [DecidableEq α]
set_option linter.unusedSectionVars false

/-- 反復 `s` の run の右端（絶対位置）。 -/
abbrev segEnd (x : List α) (k s p : ℕ) : ℕ :=
  s + extendReach (x.drop s) p (x.length + 1) (k * p)

/-- 右端が `L` を超えない間だけ周期を足す「区間和」。 -/
def segSum (x : List α) (k b L : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, s =>
      match firstOuter (x.drop s) k b (x.length + 1) 1 with
      | none => 0
      | some (p, _) =>
          if segEnd x k s p ≤ L then p + segSum x k b L fuel (nextPos x k s p) else 0

/-- 同じループの停止位置。 -/
def segExit (x : List α) (k b L : ℕ) : ℕ → ℕ → ℕ
  | 0, s => s
  | fuel + 1, s =>
      match firstOuter (x.drop s) k b (x.length + 1) 1 with
      | none => s
      | some (p, _) =>
          if segEnd x k s p ≤ L then segExit x k b L fuel (nextPos x k s p) else s

/-- 位置は真に進む。 -/
theorem nextPos_gt (x : List α) (k bound : ℕ) (hk : 3 ≤ k) {s p m : ℕ} (hs : s ≤ x.length)
    (hfo : firstOuter (x.drop s) k bound (x.length + 1) 1 = some (p, m)) :
    s < nextPos x k s p := by
  obtain ⟨hleast, -, hkr, -⟩ := stripLoop2_step_data x k bound hk hs hfo
  have hp : 0 < p := hleast.1.1
  have hkp : 0 < k * p := Nat.mul_pos (by omega) hp
  simp only [nextPos]
  omega

end PassSum10
end PalPeg

namespace PalPeg
namespace PassSum10
universe u
variable {α : Type u} [DecidableEq α]
set_option linter.unusedSectionVars false

theorem segSum_of_none (x : List α) (k b L : ℕ) {s : ℕ}
    (hfo : firstOuter (x.drop s) k b (x.length + 1) 1 = none) :
    ∀ fuel, segSum x k b L fuel s = 0 := by
  intro fuel; cases fuel with
  | zero => rfl
  | succ fuel => rw [segSum, hfo]

theorem segExit_of_none (x : List α) (k b L : ℕ) {s : ℕ}
    (hfo : firstOuter (x.drop s) k b (x.length + 1) 1 = none) :
    ∀ fuel, segExit x k b L fuel s = s := by
  intro fuel; cases fuel with
  | zero => rfl
  | succ fuel => rw [segExit, hfo]

theorem segExit_ge (x : List α) (k b L : ℕ) (hk : 3 ≤ k) :
    ∀ (fuel s : ℕ), s ≤ x.length → s ≤ segExit x k b L fuel s := by
  intro fuel
  induction fuel with
  | zero => intro s _; exact le_refl _
  | succ fuel ih =>
    intro s hs
    rw [segExit]
    rcases hfo : firstOuter (x.drop s) k b (x.length + 1) 1 with _ | ⟨p, m⟩
    · simp only []; exact le_refl _
    · simp only []
      split
      · exact le_trans (le_of_lt (nextPos_gt x k b hk hs hfo))
          (ih _ (nextPos_le x k b hk hs hfo))
      · exact le_refl _

theorem segExit_le (x : List α) (k b L : ℕ) (hk : 3 ≤ k) :
    ∀ (fuel s : ℕ), s ≤ x.length → segExit x k b L fuel s ≤ x.length := by
  intro fuel
  induction fuel with
  | zero => intro s hs; exact hs
  | succ fuel ih =>
    intro s hs
    rw [segExit]
    rcases hfo : firstOuter (x.drop s) k b (x.length + 1) 1 with _ | ⟨p, m⟩
    · simp only []; exact hs
    · simp only []
      split
      · exact ih _ (nextPos_le x k b hk hs hfo)
      · exact hs

/-- 燃料が十分なら結果は燃料に依らない（位置が真に進むため）。 -/
theorem segSum_stable (x : List α) (k b L : ℕ) (hk : 3 ≤ k) :
    ∀ (f₁ f₂ s : ℕ), s ≤ x.length → x.length + 1 - s ≤ f₁ → f₁ ≤ f₂ →
      segSum x k b L f₁ s = segSum x k b L f₂ s := by
  intro f₁
  induction f₁ with
  | zero => intro f₂ s hs h1 _; omega
  | succ f₁ ih =>
    intro f₂ s hs h1 h2
    obtain ⟨f₂', rfl⟩ : ∃ f₂', f₂ = f₂' + 1 := ⟨f₂ - 1, by omega⟩
    rw [segSum, segSum]
    rcases hfo : firstOuter (x.drop s) k b (x.length + 1) 1 with _ | ⟨p, m⟩
    · simp only []
    · simp only []
      have hgt := nextPos_gt x k b hk hs hfo
      have hle := nextPos_le x k b hk hs hfo
      split
      · rw [ih f₂' (nextPos x k s p) hle (by omega) (by omega)]
      · rfl

theorem segExit_stable (x : List α) (k b L : ℕ) (hk : 3 ≤ k) :
    ∀ (f₁ f₂ s : ℕ), s ≤ x.length → x.length + 1 - s ≤ f₁ → f₁ ≤ f₂ →
      segExit x k b L f₁ s = segExit x k b L f₂ s := by
  intro f₁
  induction f₁ with
  | zero => intro f₂ s hs h1 _; omega
  | succ f₁ ih =>
    intro f₂ s hs h1 h2
    obtain ⟨f₂', rfl⟩ : ∃ f₂', f₂ = f₂' + 1 := ⟨f₂ - 1, by omega⟩
    rw [segExit, segExit]
    rcases hfo : firstOuter (x.drop s) k b (x.length + 1) 1 with _ | ⟨p, m⟩
    · simp only []
    · simp only []
      have hgt := nextPos_gt x k b hk hs hfo
      have hle := nextPos_le x k b hk hs hfo
      split
      · rw [ih f₂' (nextPos x k s p) hle (by omega) (by omega)]
      · rfl


/-- **区間の分割**。内側の上限 `L' ≤ L` で走らせて止まった位置から続きを走らせると、
外側の上限 `L` で走らせたのと同じ和になる（同じ位置列をたどるため）。 -/
theorem segSum_split (x : List α) (k b : ℕ) (hk : 3 ≤ k) {L' L : ℕ} (hLL : L' ≤ L) :
    ∀ (fuel s : ℕ), s ≤ x.length → x.length + 1 - s ≤ fuel →
      segSum x k b L fuel s
        = segSum x k b L' fuel s + segSum x k b L fuel (segExit x k b L' fuel s) := by
  intro fuel
  induction fuel with
  | zero => intro s hs h1; omega
  | succ fuel ih =>
    intro s hs h1
    rw [segSum, segSum, segExit]
    rcases hfo : firstOuter (x.drop s) k b (x.length + 1) 1 with _ | ⟨p, m⟩
    · simp only []
      rw [segSum, hfo]
      simp
    · simp only []
      have hgt := nextPos_gt x k b hk hs hfo
      have hle := nextPos_le x k b hk hs hfo
      by_cases hcond : segEnd x k s p ≤ L'
      · rw [if_pos hcond, if_pos (le_trans hcond hLL), if_pos hcond]
        have hIH := ih (nextPos x k s p) hle (by omega)
        set e := segExit x k b L' fuel (nextPos x k s p) with he
        have hege : nextPos x k s p ≤ e := segExit_ge x k b L' hk fuel _ hle
        have hele : e ≤ x.length := segExit_le x k b L' hk fuel _ hle
        have hstab : segSum x k b L fuel e = segSum x k b L (fuel + 1) e :=
          segSum_stable x k b L hk fuel (fuel + 1) e hele (by omega) (by omega)
        rw [hIH, ← hstab]
        omega
      · rw [if_neg hcond, if_neg hcond]
        by_cases hcond2 : segEnd x k s p ≤ L
        · rw [if_pos hcond2, segSum, hfo]
          simp only []
          rw [if_pos hcond2, Nat.zero_add]
        · rw [if_neg hcond2, segSum, hfo]
          simp only []
          rw [if_neg hcond2]


/-- 上限を `x.length` にすると区間和は `stripLoop2Periods` そのもの
（run の右端は必ず `x.length` 以下）。 -/
theorem segSum_top (x : List α) (k b : ℕ) (hk : 3 ≤ k) :
    ∀ (fuel s : ℕ), s ≤ x.length →
      segSum x k b x.length fuel s = stripLoop2Periods x k b fuel s := by
  intro fuel
  induction fuel with
  | zero => intro s _; rfl
  | succ fuel ih =>
    intro s hs
    rw [segSum, stripLoop2Periods]
    rcases hfo : firstOuter (x.drop s) k b (x.length + 1) 1 with _ | ⟨p, m⟩
    · simp only []
    · simp only []
      obtain ⟨hleast, -, hkr, hR⟩ := stripLoop2_step_data x k b hk hs hfo
      have hvlen : (x.drop s).length = x.length - s := by simp
      have hcond : segEnd x k s p ≤ x.length := by
        have := hR.1; simp only [segEnd]; omega
      rw [if_pos hcond, ih _ (nextPos_le x k b hk hs hfo)]

end PassSum10
end PalPeg

section AxiomCheck
#print axioms PalPeg.PassSum10.nextPos_gt
#print axioms PalPeg.PassSum10.segExit_ge
#print axioms PalPeg.PassSum10.segExit_le
#print axioms PalPeg.PassSum10.segSum_stable
#print axioms PalPeg.PassSum10.segExit_stable
#print axioms PalPeg.PassSum10.segSum_split
#print axioms PalPeg.PassSum10.segSum_top
end AxiomCheck
