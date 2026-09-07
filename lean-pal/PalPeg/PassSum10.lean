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

namespace PalPeg
namespace PassSum10
universe u
variable {α : Type u} [DecidableEq α]
set_option linter.unusedSectionVars false

/-! ## 根（root）単位の再帰

区間 `[s, L]` の「根」＝その部分木がすべて `L` 以内に収まる節点の列。次の根は
「今の節点の部分木を抜けた位置」`segExit (segEnd s p) (nextPos s p)` にある。 -/

/-- 区間の根の周期の総和。 -/
def segRootSum (x : List α) (k b L : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, s =>
      match firstOuter (x.drop s) k b (x.length + 1) 1 with
      | none => 0
      | some (p, _) =>
          if segEnd x k s p ≤ L then
            p + segRootSum x k b L fuel
              (segExit x k b (segEnd x k s p) fuel (nextPos x k s p))
          else 0

/-- 区間の最初の根の周期（無ければ `0`）。 -/
def segFirstRoot (x : List α) (k b L : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | _ + 1, s =>
      match firstOuter (x.drop s) k b (x.length + 1) 1 with
      | none => 0
      | some (p, _) => if segEnd x k s p ≤ L then p else 0

/-- 区間の最後の根の周期（無ければ `0`）。 -/
def segLastRoot (x : List α) (k b L : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, s =>
      match firstOuter (x.drop s) k b (x.length + 1) 1 with
      | none => 0
      | some (p, _) =>
          if segEnd x k s p ≤ L then
            (match segLastRoot x k b L fuel
                (segExit x k b (segEnd x k s p) fuel (nextPos x k s p)) with
             | 0 => p
             | q + 1 => q + 1)
          else 0

theorem segRootSum_stable (x : List α) (k b L : ℕ) (hk : 3 ≤ k) :
    ∀ (f₁ f₂ s : ℕ), s ≤ x.length → x.length + 1 - s ≤ f₁ → f₁ ≤ f₂ →
      segRootSum x k b L f₁ s = segRootSum x k b L f₂ s := by
  intro f₁
  induction f₁ with
  | zero => intro f₂ s hs h1 _; omega
  | succ f₁ ih =>
    intro f₂ s hs h1 h2
    obtain ⟨f₂', rfl⟩ : ∃ f₂', f₂ = f₂' + 1 := ⟨f₂ - 1, by omega⟩
    rw [segRootSum, segRootSum]
    rcases hfo : firstOuter (x.drop s) k b (x.length + 1) 1 with _ | ⟨p, m⟩
    · simp only []
    · simp only []
      have hgt := nextPos_gt x k b hk hs hfo
      have hle := nextPos_le x k b hk hs hfo
      split
      · have hex : segExit x k b (segEnd x k s p) f₁ (nextPos x k s p)
            = segExit x k b (segEnd x k s p) f₂' (nextPos x k s p) :=
          segExit_stable x k b _ hk f₁ f₂' _ hle (by omega) (by omega)
        have hge := segExit_ge x k b (segEnd x k s p) hk f₁ _ hle
        have hlee := segExit_le x k b (segEnd x k s p) hk f₁ _ hle
        rw [← hex, ih f₂' _ hlee (by omega) (by omega)]
      · rfl

theorem segLastRoot_stable (x : List α) (k b L : ℕ) (hk : 3 ≤ k) :
    ∀ (f₁ f₂ s : ℕ), s ≤ x.length → x.length + 1 - s ≤ f₁ → f₁ ≤ f₂ →
      segLastRoot x k b L f₁ s = segLastRoot x k b L f₂ s := by
  intro f₁
  induction f₁ with
  | zero => intro f₂ s hs h1 _; omega
  | succ f₁ ih =>
    intro f₂ s hs h1 h2
    obtain ⟨f₂', rfl⟩ : ∃ f₂', f₂ = f₂' + 1 := ⟨f₂ - 1, by omega⟩
    rw [segLastRoot, segLastRoot]
    rcases hfo : firstOuter (x.drop s) k b (x.length + 1) 1 with _ | ⟨p, m⟩
    · simp only []
    · simp only []
      have hgt := nextPos_gt x k b hk hs hfo
      have hle := nextPos_le x k b hk hs hfo
      split
      · have hex : segExit x k b (segEnd x k s p) f₁ (nextPos x k s p)
            = segExit x k b (segEnd x k s p) f₂' (nextPos x k s p) :=
          segExit_stable x k b _ hk f₁ f₂' _ hle (by omega) (by omega)
        have hge := segExit_ge x k b (segEnd x k s p) hk f₁ _ hle
        have hlee := segExit_le x k b (segEnd x k s p) hk f₁ _ hle
        rw [← hex, ih f₂' _ hlee (by omega) (by omega)]
      · rfl

end PassSum10
end PalPeg

namespace PalPeg
namespace PassSum10
universe u
variable {α : Type u} [DecidableEq α]
set_option linter.unusedSectionVars false

/-- 燃料が十分なら標準燃料 `x.length + 1` の値と一致する。 -/
theorem segExit_canonical (x : List α) (k b L : ℕ) (hk : 3 ≤ k) (fuel s : ℕ)
    (hs : s ≤ x.length) (hf : x.length + 1 - s ≤ fuel) :
    segExit x k b L fuel s = segExit x k b L (x.length + 1) s := by
  have h1 := segExit_stable x k b L hk fuel (fuel + x.length + 1) s hs hf (by omega)
  have h2 := segExit_stable x k b L hk (x.length + 1) (fuel + x.length + 1) s hs
    (by omega) (by omega)
  rw [h1, h2]

theorem segSum_canonical (x : List α) (k b L : ℕ) (hk : 3 ≤ k) (fuel s : ℕ)
    (hs : s ≤ x.length) (hf : x.length + 1 - s ≤ fuel) :
    segSum x k b L fuel s = segSum x k b L (x.length + 1) s := by
  have h1 := segSum_stable x k b L hk fuel (fuel + x.length + 1) s hs hf (by omega)
  have h2 := segSum_stable x k b L hk (x.length + 1) (fuel + x.length + 1) s hs
    (by omega) (by omega)
  rw [h1, h2]

theorem segLastRoot_canonical (x : List α) (k b L : ℕ) (hk : 3 ≤ k) (fuel s : ℕ)
    (hs : s ≤ x.length) (hf : x.length + 1 - s ≤ fuel) :
    segLastRoot x k b L fuel s = segLastRoot x k b L (x.length + 1) s := by
  have h1 := segLastRoot_stable x k b L hk fuel (fuel + x.length + 1) s hs hf (by omega)
  have h2 := segLastRoot_stable x k b L hk (x.length + 1) (fuel + x.length + 1) s hs
    (by omega) (by omega)
  rw [h1, h2]

/-! ## 木の性質（`PassSum9` の (T2)(T3) を 1 パスの再帰の言葉で書いたもの） -/

/-- 部分木を抜けた位置（次の兄弟の位置）。 -/
abbrev subExit (x : List α) (k b s p : ℕ) : ℕ :=
  segExit x k b (segEnd x k s p) (x.length + 1) (nextPos x k s p)

/-- **(T3)**：連続する兄弟（＝ある節点とその部分木の直後の節点）の周期は 3 倍以上。
`PassSum9.sibling_growth_eight` は消費量補題のもとで `6 * p < p'` を与える。 -/
def RootGrowth (x : List α) (k b : ℕ) : Prop :=
  ∀ s p m p' m', s ≤ x.length →
    firstOuter (x.drop s) k b (x.length + 1) 1 = some (p, m) →
    firstOuter (x.drop (subExit x k b s p)) k b (x.length + 1) 1 = some (p', m') →
    3 * p ≤ p'

/-- **(T2)**：節点 `c` の子の列の末子 `q_m` は `7 * q_m < p_c`
（`PassSum9.last_child_bound`）。 -/
def LastChildBound (x : List α) (k b : ℕ) : Prop :=
  ∀ s p m, s ≤ x.length →
    firstOuter (x.drop s) k b (x.length + 1) 1 = some (p, m) →
    7 * segLastRoot x k b (segEnd x k s p) (x.length + 1) (nextPos x k s p) < p

/-- 木の性質のまとめ。 -/
def PassTreeFacts (x : List α) (k b : ℕ) : Prop :=
  RootGrowth x k b ∧ LastChildBound x k b

/-! ## R2：根の列の等比和 -/

theorem segLastRoot_pos (x : List α) (k b L : ℕ) (hk : 3 ≤ k) :
    ∀ (fuel s p m : ℕ), s ≤ x.length →
      firstOuter (x.drop s) k b (x.length + 1) 1 = some (p, m) →
      segEnd x k s p ≤ L → 0 < fuel → 0 < segLastRoot x k b L fuel s := by
  intro fuel
  cases fuel with
  | zero => intro s p m _ _ _ h; omega
  | succ fuel =>
    intro s p m hs hfo hcond _
    have hp : 0 < p := (stripLoop2_step_data x k b hk hs hfo).1.1.1
    rw [segLastRoot, hfo]
    simp only []
    rw [if_pos hcond]
    split
    · exact hp
    · omega

/-- **R2（等比和）**：`2 * Σ根 + 最初の根 ≤ 3 * 最後の根`。 -/
theorem segRoot_geom (x : List α) (k b L : ℕ) (hk : 3 ≤ k) (hgrow : RootGrowth x k b) :
    ∀ (fuel s : ℕ), s ≤ x.length → x.length + 1 - s ≤ fuel →
      2 * segRootSum x k b L fuel s + segFirstRoot x k b L fuel s
        ≤ 3 * segLastRoot x k b L fuel s := by
  intro fuel
  induction fuel with
  | zero => intro s hs h1; omega
  | succ fuel ih =>
    intro s hs h1
    rw [segRootSum, segFirstRoot, segLastRoot]
    rcases hfo : firstOuter (x.drop s) k b (x.length + 1) 1 with _ | ⟨p, m⟩
    · simp only []
      omega
    · simp only []
      have hgt := nextPos_gt x k b hk hs hfo
      have hle := nextPos_le x k b hk hs hfo
      have hp : 0 < p := (stripLoop2_step_data x k b hk hs hfo).1.1.1
      by_cases hcond : segEnd x k s p ≤ L
      · rw [if_pos hcond, if_pos hcond, if_pos hcond]
        have hege0 := segExit_ge x k b (segEnd x k s p) hk fuel _ hle
        have hele0 := segExit_le x k b (segEnd x k s p) hk fuel _ hle
        have hcan : segExit x k b (segEnd x k s p) fuel (nextPos x k s p)
            = subExit x k b s p := segExit_canonical x k b _ hk fuel _ hle (by omega)
        obtain ⟨e, hedef⟩ :
            ∃ e, segExit x k b (segEnd x k s p) fuel (nextPos x k s p) = e := ⟨_, rfl⟩
        rw [hedef] at hcan hege0 hele0
        rw [hedef]
        have hIH := ih e hele0 (by omega)
        rcases hfo' : firstOuter (x.drop e) k b (x.length + 1) 1 with _ | ⟨p', m'⟩
        · have hrs : segRootSum x k b L fuel e = 0 := by
            cases fuel with
            | zero => rfl
            | succ f => rw [segRootSum, hfo']
          have hlr0 : segLastRoot x k b L fuel e = 0 := by
            cases fuel with
            | zero => rfl
            | succ f => rw [segLastRoot, hfo']
          rw [hrs, hlr0]
          simp only []
          omega
        · by_cases hcond2 : segEnd x k e p' ≤ L
          · have hgrow' : 3 * p ≤ p' := hgrow s p m p' m' hs hfo (by rw [← hcan]; exact hfo')
            have hfuel : 0 < fuel := by omega
            obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
            have hlast : 0 < segLastRoot x k b L (f + 1) e :=
              segLastRoot_pos x k b L hk (f + 1) e p' m' hele0 hfo' hcond2 (by omega)
            have hfirst : segFirstRoot x k b L (f + 1) e = p' := by
              rw [segFirstRoot, hfo']; simp only []; rw [if_pos hcond2]
            rw [hfirst] at hIH
            have hrs : segRootSum x k b L (f + 1) e
                = p' + segRootSum x k b L f
                    (segExit x k b (segEnd x k e p') f (nextPos x k e p')) := by
              rw [segRootSum, hfo']; simp only []; rw [if_pos hcond2]
            have hlr : (match segLastRoot x k b L (f + 1) e with
                | 0 => p | q + 1 => q + 1) = segLastRoot x k b L (f + 1) e := by
              cases h : segLastRoot x k b L (f + 1) e with
              | zero => rw [h] at hlast; omega
              | succ q => simp
            rw [hlr]
            omega
          · have hrs : segRootSum x k b L fuel e = 0 := by
              cases fuel with
              | zero => rfl
              | succ f => rw [segRootSum, hfo']; simp only []; rw [if_neg hcond2]
            have hlr0 : segLastRoot x k b L fuel e = 0 := by
              cases fuel with
              | zero => rfl
              | succ f => rw [segLastRoot, hfo']; simp only []; rw [if_neg hcond2]
            rw [hrs, hlr0]
            simp only []
            omega
      · rw [if_neg hcond, if_neg hcond, if_neg hcond]

end PassSum10
end PalPeg

namespace PalPeg
namespace PassSum10
universe u
variable {α : Type u} [DecidableEq α]
set_option linter.unusedSectionVars false

/-! ## R1 と節点上界 (N)

`PassSum8` の `NodeOk_bound`（`11 * T ≤ 14 * p`）と `KidsOk_le_last'`
（`11 * ΣT ≤ 21 * ρ_max`）を、1 パスの再帰の上で直接証明する。 -/

/-- **R1**：区間の周期和は根の周期和の `14/11` 倍以下。

各根 `c` について「部分木の和 ≤ (14/11) * p_c」（＝ (N)）が成り立ち、
それを根の列に沿って足し上げる。(N) 自身は同じ帰納法の中で
「子の列に R1 と R2 を適用する」ことで得られる。 -/
theorem segSum_le_rootSum (x : List α) (k b : ℕ) (hk : 3 ≤ k)
    (hfacts : PassTreeFacts x k b) :
    ∀ (fuel s L : ℕ), s ≤ x.length → x.length + 1 - s ≤ fuel →
      11 * segSum x k b L fuel s ≤ 14 * segRootSum x k b L fuel s := by
  obtain ⟨hgrow, hlast⟩ := hfacts
  intro fuel
  induction fuel with
  | zero => intro s L hs h1; omega
  | succ fuel ih =>
    intro s L hs h1
    rw [segSum, segRootSum]
    rcases hfo : firstOuter (x.drop s) k b (x.length + 1) 1 with _ | ⟨p, m⟩
    · simp only []
      omega
    · simp only []
      have hgt := nextPos_gt x k b hk hs hfo
      have hle := nextPos_le x k b hk hs hfo
      have hp : 0 < p := (stripLoop2_step_data x k b hk hs hfo).1.1.1
      by_cases hcond : segEnd x k s p ≤ L
      · rw [if_pos hcond, if_pos hcond]
        -- 子の列（上限 `E_c`）への R1 と R2
        have hA := ih (nextPos x k s p) (segEnd x k s p) hle (by omega)
        have hR2 := segRoot_geom x k b (segEnd x k s p) hk hgrow fuel (nextPos x k s p)
          hle (by omega)
        have hT2 : 7 * segLastRoot x k b (segEnd x k s p) (x.length + 1) (nextPos x k s p) < p :=
          hlast s p m hs hfo
        have hcan : segLastRoot x k b (segEnd x k s p) fuel (nextPos x k s p)
            = segLastRoot x k b (segEnd x k s p) (x.length + 1) (nextPos x k s p) :=
          segLastRoot_canonical x k b _ hk fuel _ hle (by omega)
        rw [hcan] at hR2
        -- (N)：部分木の和は `3/11 * p` 以下
        have hN : 11 * segSum x k b (segEnd x k s p) fuel (nextPos x k s p) < 3 * p := by
          omega
        -- 区間の分割
        have hsplit := segSum_split x k b hk (L' := segEnd x k s p) (L := L) hcond
          fuel (nextPos x k s p) hle (by omega)
        have hege0 := segExit_ge x k b (segEnd x k s p) hk fuel _ hle
        have hele0 := segExit_le x k b (segEnd x k s p) hk fuel _ hle
        have hrest := ih (segExit x k b (segEnd x k s p) fuel (nextPos x k s p)) L
          hele0 (by omega)
        omega
      · rw [if_neg hcond, if_neg hcond]

/-- **(N) 節点上界**：節点 `c` の部分木の周期和は `(14/11) * p_c` 以下
（`11 * (p + 部分木) ≤ 14 * p`、すなわち `11 * 部分木 ≤ 3 * p`）。 -/
theorem node_subtree_bound (x : List α) (k b : ℕ) (hk : 3 ≤ k)
    (hfacts : PassTreeFacts x k b) (s p m : ℕ) (hs : s ≤ x.length)
    (hfo : firstOuter (x.drop s) k b (x.length + 1) 1 = some (p, m)) :
    11 * segSum x k b (segEnd x k s p) (x.length + 1) (nextPos x k s p) < 3 * p := by
  obtain ⟨hgrow, hlast⟩ := hfacts
  have hle := nextPos_le x k b hk hs hfo
  have hA := segSum_le_rootSum x k b hk ⟨hgrow, hlast⟩ (x.length + 1) (nextPos x k s p)
    (segEnd x k s p) hle (by omega)
  have hR2 := segRoot_geom x k b (segEnd x k s p) hk hgrow (x.length + 1) (nextPos x k s p)
    hle (by omega)
  have hT2 : 7 * segLastRoot x k b (segEnd x k s p) (x.length + 1) (nextPos x k s p) < p :=
    hlast s p m hs hfo
  omega

end PassSum10
end PalPeg

namespace PalPeg
namespace PassSum10
universe u
variable {α : Type u} [DecidableEq α]
set_option linter.unusedSectionVars false

/-! ## 最後の根 ≤ パスの最大周期 -/

theorem maxPeriod_stable (x : List α) (k b : ℕ) (hk : 3 ≤ k) :
    ∀ (f₁ f₂ s : ℕ), s ≤ x.length → x.length + 1 - s ≤ f₁ → f₁ ≤ f₂ →
      stripLoop2MaxPeriod x k b f₁ s = stripLoop2MaxPeriod x k b f₂ s := by
  intro f₁
  induction f₁ with
  | zero => intro f₂ s hs h1 _; omega
  | succ f₁ ih =>
    intro f₂ s hs h1 h2
    obtain ⟨f₂', rfl⟩ : ∃ f₂', f₂ = f₂' + 1 := ⟨f₂ - 1, by omega⟩
    rw [stripLoop2MaxPeriod, stripLoop2MaxPeriod]
    rcases hfo : firstOuter (x.drop s) k b (x.length + 1) 1 with _ | ⟨p, m⟩
    · simp only []
    · simp only []
      have hgt := nextPos_gt x k b hk hs hfo
      have hle := nextPos_le x k b hk hs hfo
      rw [ih f₂' (nextPos x k s p) hle (by omega) (by omega)]

/-- 部分木を抜けた位置での最大周期は、元の位置での最大周期以下。 -/
theorem maxPeriod_segExit_le (x : List α) (k b L : ℕ) (hk : 3 ≤ k) :
    ∀ (fuel s : ℕ), s ≤ x.length → x.length + 1 - s ≤ fuel →
      stripLoop2MaxPeriod x k b fuel (segExit x k b L fuel s)
        ≤ stripLoop2MaxPeriod x k b fuel s := by
  intro fuel
  induction fuel with
  | zero => intro s hs h1; omega
  | succ fuel ih =>
    intro s hs h1
    rw [segExit]
    rcases hfo : firstOuter (x.drop s) k b (x.length + 1) 1 with _ | ⟨p, m⟩
    · simp only []
      exact le_refl _
    · simp only []
      have hgt := nextPos_gt x k b hk hs hfo
      have hle := nextPos_le x k b hk hs hfo
      by_cases hcond : segEnd x k s p ≤ L
      · rw [if_pos hcond]
        have hIH := ih (nextPos x k s p) hle (by omega)
        have hege := segExit_ge x k b L hk fuel _ hle
        have hele := segExit_le x k b L hk fuel _ hle
        have hst : stripLoop2MaxPeriod x k b (fuel + 1)
              (segExit x k b L fuel (nextPos x k s p))
            = stripLoop2MaxPeriod x k b fuel (segExit x k b L fuel (nextPos x k s p)) :=
          (maxPeriod_stable x k b hk fuel (fuel + 1) _ hele (by omega) (by omega)).symm
        rw [hst]
        have hmax : stripLoop2MaxPeriod x k b (fuel + 1) s
            = max p (stripLoop2MaxPeriod x k b fuel (nextPos x k s p)) := by
          rw [stripLoop2MaxPeriod, hfo]
        rw [hmax]
        exact le_trans hIH (le_max_right _ _)
      · rw [if_neg hcond]

/-- 最後の根の周期はパスの最大周期以下。 -/
theorem segLastRoot_le_maxPeriod (x : List α) (k b : ℕ) (hk : 3 ≤ k) :
    ∀ (fuel s : ℕ), s ≤ x.length → x.length + 1 - s ≤ fuel →
      segLastRoot x k b x.length fuel s ≤ stripLoop2MaxPeriod x k b fuel s := by
  intro fuel
  induction fuel with
  | zero => intro s hs h1; omega
  | succ fuel ih =>
    intro s hs h1
    rw [segLastRoot, stripLoop2MaxPeriod]
    rcases hfo : firstOuter (x.drop s) k b (x.length + 1) 1 with _ | ⟨p, m⟩
    · simp only []
      omega
    · simp only []
      have hgt := nextPos_gt x k b hk hs hfo
      have hle := nextPos_le x k b hk hs hfo
      obtain ⟨hleast, -, hkr, hR⟩ := stripLoop2_step_data x k b hk hs hfo
      have hvlen : (x.drop s).length = x.length - s := by simp
      have hcond : segEnd x k s p ≤ x.length := by
        have := hR.1; simp only [segEnd]; omega
      rw [if_pos hcond]
      have hege := segExit_ge x k b (segEnd x k s p) hk fuel _ hle
      have hele := segExit_le x k b (segEnd x k s p) hk fuel _ hle
      have hIH := ih (segExit x k b (segEnd x k s p) fuel (nextPos x k s p)) hele (by omega)
      have hmono := maxPeriod_segExit_le x k b (segEnd x k s p) hk fuel _ hle (by omega)
      cases h : segLastRoot x k b x.length fuel
          (segExit x k b (segEnd x k s p) fuel (nextPos x k s p)) with
      | zero => simp only []; exact le_max_left _ _
      | succ q =>
        rw [h] at hIH
        simp only []
        exact le_trans (le_trans hIH hmono) (le_max_right _ _)

/-! ## 最終結果 -/

/-- **1 パスの周期和 ≤ 2 * 最大周期**（木の性質 `PassTreeFacts` のもとで）。 -/
theorem passSum_le_two_max_of_treeFacts (x : List α) (k b : ℕ) (hk : 3 ≤ k)
    (hfacts : PassTreeFacts x k b) (s : ℕ) (hs : s ≤ x.length) :
    stripLoop2Periods x k b (x.length + 1) s
      ≤ 2 * stripLoop2MaxPeriod x k b (x.length + 1) s := by
  obtain ⟨hgrow, hlast⟩ := hfacts
  have htop := segSum_top x k b hk (x.length + 1) s hs
  have hR1 := segSum_le_rootSum x k b hk ⟨hgrow, hlast⟩ (x.length + 1) s x.length hs (by omega)
  have hR2 := segRoot_geom x k b x.length hk hgrow (x.length + 1) s hs (by omega)
  have hlr := segLastRoot_le_maxPeriod x k b hk (x.length + 1) s hs (by omega)
  omega

/-- **`k = 8` の最終系**：木の性質から `EndToEnd2.PassPeriodSum 8 2`。 -/
theorem passPeriodSum_eight_of_treeFacts
    (h : ∀ (x : List (Fin 2)) (b : ℕ), PassTreeFacts x 8 b) :
    EndToEnd2.PassPeriodSum 8 2 := by
  refine passPeriodSum_eight_of_sum_le_max (fun x b s => ?_)
  by_cases hs : s ≤ x.length
  · exact passSum_le_two_max_of_treeFacts x 8 b (by omega) (h x b) s hs
  · have hdrop : x.drop s = [] := by
      apply List.drop_eq_nil_of_le; omega
    have hfo : firstOuter (x.drop s) 8 b (x.length + 1) 1 = none := by
      rw [hdrop, firstOuter]
      simp
    rw [stripLoop2Periods_of_none x 8 b hfo]
    exact Nat.zero_le _

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
#print axioms PalPeg.PassSum10.segRoot_geom
#print axioms PalPeg.PassSum10.segSum_le_rootSum
#print axioms PalPeg.PassSum10.node_subtree_bound
#print axioms PalPeg.PassSum10.segLastRoot_le_maxPeriod
#print axioms PalPeg.PassSum10.passSum_le_two_max_of_treeFacts
#print axioms PalPeg.PassSum10.passPeriodSum_eight_of_treeFacts
end AxiomCheck
