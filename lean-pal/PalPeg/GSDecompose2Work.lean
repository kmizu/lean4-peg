import PalPeg.GSDecompose2

/-!
# `decompose2` の仕事量：1 パスの分解と、周期和を仮定した線形上界

`PalPeg.GSDecompose2` の末尾のコメントで述べられている

```
1 パスの仕事 ≤ (2k+1) * Σⱼ pⱼ + O(T)
```

を**実際の定理として形式化**し、そのうえで残る唯一の未解決部分
`Σⱼ pⱼ ≤ C₁ * T`（run 開始位置の入れ子木に関する償却解析）を**仮定**として切り出し、
そこから `decompose2Work` の線形上界を導く。

* `stripLoop2Periods`：1 パスで `firstOuter` が返した最小周期 `pⱼ` の総和カウンタ。
* `stripLoop2Work_le`：`stripLoop2Work ≤ (2k+1) * Σ pⱼ + 3 * (前進量) + (k+2)*(2*bound+1)`
  （無条件・sorry なし）。
* `decomposeLoop2Work_le` / `decompose2Work_le`：`Σ pⱼ ≤ C₁ * bound` を仮定したときの
  大域線形上界。定数は `C = (4k+2)*C₁ + 17k + 50`, `D = 2k+5`。

`GSPreprocess.decomposeWork_le` と同じ幾何級数（`3*b ≤ p₂`）の議論を写しているが、
削除ループの前進量は `< p₂` なので、`(2k+3)*(|x| - s)` の telescoping 項は不要になる。
-/

namespace PalPeg

universe u
variable {α : Type u} [DecidableEq α]
set_option linter.unusedSectionVars false

/-! ## 補助：`extendReach` の単調性 -/

/-- `extendReach` は初期値以上（定義から直ちに従う）。 -/
theorem extendReach_ge_self (v : List α) (p : ℕ) :
    ∀ (fuel r : ℕ), r ≤ extendReach v p fuel r := by
  intro fuel
  induction fuel with
  | zero => intro r; exact le_refl _
  | succ fuel ih =>
    intro r
    by_cases hc : r < v.length ∧ v[r - p]? = v[r]?
    · rw [extendReach, if_pos hc]; have := ih (r + 1); omega
    · rw [extendReach, if_neg hc]

/-! ## 1 パスで見つかった最小周期の総和 -/

/-- `stripLoop2` の 1 パスで `firstOuter` が返した最小周期 `pⱼ` の総和。
`stripLoop2Work` と同じ再帰の形をしている。 -/
def stripLoop2Periods (x : List α) (k bound : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, s =>
      match firstOuter (x.drop s) k bound (x.length + 1) 1 with
      | none => 0
      | some (p, _) =>
          p + stripLoop2Periods x k bound fuel
            (s + (extendReach (x.drop s) p (x.length + 1) (k * p) - k * p + 1))

/-- **1 パスの仕事量の分解**（無条件）。

内訳は

* `firstOuter` の走査 `≤ (2k+1)*pⱼ + 2`（`firstOuterWork_le_some`）、
* `reach` 伸長 `≤ dⱼ = rⱼ - k*pⱼ + 1`（`extendReachWork_le'`、これは前進量そのもの）、
* 最後の失敗する走査 `≤ (k+2)*(2*bound+1)`（`firstOuterWork_le_min`）

であり、`dⱼ ≥ 1` なので定数項 `2` も前進量に償却できる。 -/
theorem stripLoop2Work_le (x : List α) (k bound : ℕ) (hk : 3 ≤ k) :
    ∀ (fuel s : ℕ),
      stripLoop2Work x k bound fuel s
        ≤ (2 * k + 1) * stripLoop2Periods x k bound fuel s
          + 3 * (stripLoop2 x k bound fuel s - s) + (k + 2) * (2 * bound + 1) := by
  intro fuel
  induction fuel with
  | zero => intro s; simp only [stripLoop2Work]; omega
  | succ fuel ih =>
    intro s
    rw [stripLoop2Work, stripLoop2Periods, stripLoop2]
    rcases hfo : firstOuter (x.drop s) k bound (x.length + 1) 1 with _ | ⟨p, m⟩
    · simp only []
      have hmin := firstOuterWork_le_min (x.drop s) k bound hk (x.length + 1) 1 (by omega)
        (by omega)
      have hmul : (k + 2) * (2 * min bound (x.drop s).length + 1)
          ≤ (k + 2) * (2 * bound + 1) :=
        Nat.mul_le_mul_left _ (by have := min_le_left bound (x.drop s).length; omega)
      omega
    · simp only []
      set r := extendReach (x.drop s) p (x.length + 1) (k * p) with hrdef
      set d := r - k * p + 1 with hddef
      have hw := firstOuterWork_le_some (x.drop s) k bound hk (x.length + 1) 1 p m
        (by omega) hfo
      have hex : extendReachWork (x.drop s) p (x.length + 1) (k * p) + k * p ≤ r + 1 :=
        extendReachWork_le' (x.drop s) p (x.length + 1) (k * p)
      have hrge : k * p ≤ r := by
        exact extendReach_ge_self (x.drop s) p (x.length + 1) (k * p)
      have hd1 : 1 ≤ d := by omega
      have hexd : extendReachWork (x.drop s) p (x.length + 1) (k * p) ≤ d := by omega
      have hrec := ih (s + d)
      have hmono := stripLoop2_ge x k bound fuel (s + d)
      have hsplit : (2 * k + 1) * (p + stripLoop2Periods x k bound fuel (s + d))
          = (2 * k + 1) * p + (2 * k + 1) * stripLoop2Periods x k bound fuel (s + d) := by
        ring
      have hd : 3 * (stripLoop2 x k bound fuel (s + d) - s)
          = 3 * (stripLoop2 x k bound fuel (s + d) - (s + d)) + 3 * d := by
        rw [← Nat.mul_add]; congr 1; omega
      omega

/-- 1 パス（`bound = p₂`）の仕事量：前進量は `stripLoop2_lt_second` より `< p₂`。 -/
theorem stripLoop2Work_le_pass (x : List α) (k : ℕ) (hk : 4 ≤ k) {s T m : ℕ}
    (hs : s ≤ x.length) (hT : 0 < T) (hprim : Primitive ((x.drop s).take T))
    (hkT : k * T ≤ m) (hm : m ≤ (x.drop s).length)
    (hperT : HasPeriod ((x.drop s).take m) T) (fuel : ℕ) :
    stripLoop2Work x k T fuel s
      ≤ (2 * k + 1) * stripLoop2Periods x k T fuel s + (3 * k + 9) * T := by
  have hmain := stripLoop2Work_le x k T (by omega) fuel s
  have hlt := stripLoop2_lt_second x k hk hs hT hprim hkT hm hperT fuel
  have hadv : stripLoop2 x k T fuel s - s ≤ T := by omega
  have h3 : 3 * (stripLoop2 x k T fuel s - s) ≤ 3 * T := by omega
  have hc : (k + 2) * (2 * T + 1) ≤ (3 * k + 6) * T := by
    have h1 : (k + 2) * (2 * T + 1) = (2 * k + 4) * T + (k + 2) := by ring
    have h2 : k + 2 ≤ (k + 2) * T := Nat.le_mul_of_pos_right _ hT
    have h3' : (2 * k + 4) * T + (k + 2) * T = (3 * k + 6) * T := by ring
    omega
  have hfin : 3 * T + (3 * k + 6) * T = (3 * k + 9) * T := by ring
  omega

/-! ## 周期和を仮定した大域線形上界

未解決部分は「1 パスの `Σⱼ pⱼ` が `bound` に比例する」ことだけである
（`GSDecompose2` の入れ子木の議論、(A) `child_period_bound` と
(B) `sibling_overlap_lt` から出るはずの構造帰納法）。ここではそれを仮説
`hsum` として取り出す。 -/

/-- **`decomposeLoop2` の大域的な線形仕事量**（周期和の仮説つき）。

`GSPreprocess.decomposeLoopWork_le` と同じ形の不変条件・幾何級数の議論。
`A = 2 * ((2k+1)*C₁ + 7k + 21)` がポテンシャル係数。 -/
theorem decomposeLoop2Work_le (x : List α) (k C₁ : ℕ) (hk : 4 ≤ k)
    (hsum : ∀ b s : ℕ, stripLoop2Periods x k b (x.length + 1) s ≤ C₁ * b) :
    ∀ (fuel s b : ℕ), s ≤ x.length → 0 < b → b ≤ x.length + 1 →
      (∀ p', p' < b → ¬ KRep (x.drop s) k p') →
      decomposeLoop2Work x k fuel s + (2 * ((2 * k + 1) * C₁ + 7 * k + 21)) * b
        ≤ (2 * ((2 * k + 1) * C₁ + 7 * k + 21)) * (x.length + 1)
          + ((3 * k + 8) * x.length + (2 * k + 5)) := by
  set E := (2 * k + 1) * C₁ + 7 * k + 21 with hEdef
  intro fuel
  induction fuel with
  | zero =>
    intro s b hs hb hbx _
    have hmulb : (2 * E) * b ≤ (2 * E) * (x.length + 1) := Nat.mul_le_mul_left _ hbx
    simp only [decomposeLoop2Work]
    omega
  | succ fuel ih =>
    intro s b hs hb hbx hbelow
    have hmulb : (2 * E) * b ≤ (2 * E) * (x.length + 1) := Nat.mul_le_mul_left _ hbx
    have hstep := decomposeStepWork_le x k s (by omega) hs
    have hvlen : (x.drop s).length = x.length - s := by simp
    rw [decomposeLoop2Work]
    rcases hfp : firstPeriod (x.drop s) k with _ | ⟨p₁, m⟩
    · simp only []
      omega
    · simp only []
      obtain ⟨hleast, rfl⟩ := firstPeriod_some (x.drop s) k (by omega) hfp
      have hp₁ : 0 < p₁ := hleast.1.1
      have hkp₁len : k * p₁ ≤ (x.drop s).length := hleast.1.2.1
      obtain ⟨hrge, hreach⟩ :=
        extendReach_spec (x.drop s) p₁ (x.length + 1) (k * p₁) (by omega)
          (Nat.le_mul_of_pos_left p₁ (by omega)) hkp₁len hleast.1.2.2
      rcases hsp : secondPeriod (x.drop s) k p₁
          (extendReach (x.drop s) p₁ (x.length + 1) (k * p₁)) with _ | p₂
      · simp only []
        omega
      · simp only []
        set r := extendReach (x.drop s) p₁ (x.length + 1) (k * p₁) with hrdef
        obtain ⟨hsecond, hsecmin⟩ :=
          secondPeriod_some (x.drop s) k p₁ r p₂ (by omega) hleast hreach.2.1 hreach.1 hsp
        have hprim : Primitive ((x.drop s).take p₂) :=
          second_primitive_of_least (by omega) hsecond hsecmin
        have hkrep₂ : KRep (x.drop s) k p₂ := kRep_of_second hsecond
        have hle₁₂ : p₁ ≤ p₂ := hleast.2 p₂ hkrep₂
        have hne₁₂ : p₁ ≠ p₂ := by
          rintro rfl
          exact not_second_reach hreach hsecond
        have hlt₁₂ : p₁ < p₂ := by omega
        have hgrow : (k - 1) * p₁ ≤ p₂ :=
          kRepetition_periods (by omega) hleast.1 hkrep₂ hprim hlt₁₂
        have hrlt : r < p₁ + p₂ :=
          reach_lt_add_of_second (by omega) hreach.2.1 hreach.1 hp₁ hkrep₂ hprim hlt₁₂
        have hbp₁ : b ≤ p₁ := by
          by_contra hcon
          exact hbelow p₁ (by omega) hleast.1
        have h3b : 3 * b ≤ p₂ := by
          have h1 : 3 * p₁ ≤ (k - 1) * p₁ := Nat.mul_le_mul_right p₁ (by omega)
          have h2 : 3 * b ≤ 3 * p₁ := by omega
          omega
        have hp₂pos : 0 < p₂ := hsecond.1
        have hkp₂ : k * p₂ ≤ (x.drop s).length := hkrep₂.2.1
        have hp₂x : p₂ ≤ x.length + 1 := by
          have : p₂ ≤ k * p₂ := Nat.le_mul_of_pos_left p₂ (by omega)
          omega
        -- 削除ループ
        have hs'ge := stripLoop2_ge x k p₂ (x.length + 1) s
        have hs'le := stripLoop2_le x k p₂ (by omega) (x.length + 1) s hs
        have hnext := stripLoop2_spec x k p₂ (by omega) (x.length + 1) s hs (by omega)
        have hrec := ih (stripLoop2 x k p₂ (x.length + 1) s) p₂ hs'le (by omega) hp₂x hnext
        -- 1 パスの削除ループの仕事量
        have hstrip : stripLoop2Work x k p₂ (x.length + 1) s
            ≤ (2 * k + 1) * (C₁ * p₂) + (3 * k + 9) * p₂ := by
          have h := stripLoop2Work_le_pass x k hk hs hp₂pos hprim
            (le_max_left (k * p₂) (r + 1)) hsecond.2.1 hsecond.2.2 (x.length + 1)
          have h2 : (2 * k + 1) * stripLoop2Periods x k p₂ (x.length + 1) s
              ≤ (2 * k + 1) * (C₁ * p₂) :=
            Nat.mul_le_mul_left _ (hsum p₂ s)
          omega
        -- 外側 1 反復の鋭い評価
        have hsharp := decomposeStepWork_le_sharp x k s (by omega) hfp hsp
        -- 1 パス全体 ≤ E * p₂
        have hpass : decomposeStepWork x k s + stripLoop2Work x k p₂ (x.length + 1) s
            ≤ E * p₂ := by
          have e1 : (2 * k + 1) * p₁ ≤ (2 * k + 1) * p₂ := Nat.mul_le_mul_left _ hle₁₂
          have e2 : 2 * r ≤ 4 * p₂ := by omega
          have e3 : 6 ≤ 6 * p₂ := Nat.le_mul_of_pos_right _ hp₂pos
          have e4 : (2 * k + 1) * (C₁ * p₂) = ((2 * k + 1) * C₁) * p₂ := by ring
          have e5 : (2 * k + 1) * p₂ + (2 * k + 1) * p₂ + 4 * p₂ + 6 * p₂
              + ((2 * k + 1) * C₁) * p₂ + (3 * k + 9) * p₂ = E * p₂ := by
            rw [hEdef]; ring
          omega
        -- 幾何級数：E * p₂ + (2E) * b ≤ (2E) * p₂
        have hgeo : E * p₂ + (2 * E) * b ≤ (2 * E) * p₂ := by
          have g1 : (2 * E) * (3 * b) ≤ (2 * E) * p₂ := Nat.mul_le_mul_left _ h3b
          have g2 : (2 * E) * (3 * b) = 3 * ((2 * E) * b) := by ring
          have g3 : 3 * (E * p₂) + (2 * E) * p₂ = (5 * E) * p₂ := by ring
          have g4 : 3 * ((2 * E) * p₂) = (6 * E) * p₂ := by ring
          have g5 : (5 * E) * p₂ ≤ (6 * E) * p₂ := Nat.mul_le_mul_right p₂ (by omega)
          omega
        omega

/-- **主定理（周期和の仮説つきの大域線形仕事量）**。

`C = (4k+2)*C₁ + 17k + 50`, `D = 2k+5`。 -/
theorem decompose2Work_le (x : List α) (k C₁ : ℕ) (hk : 4 ≤ k)
    (hsum : ∀ b s : ℕ, stripLoop2Periods x k b (x.length + 1) s ≤ C₁ * b) :
    decompose2Work x k ≤ ((4 * k + 2) * C₁ + 17 * k + 50) * x.length + (2 * k + 5) := by
  have h := decomposeLoop2Work_le x k C₁ hk hsum (x.length + 1) 0 1 (Nat.zero_le _)
    (by omega) (by omega) (by intro p' hp'; rintro ⟨h1, -, -⟩; omega)
  set E := (2 * k + 1) * C₁ + 7 * k + 21 with hEdef
  have e1 : (2 * E) * (x.length + 1) = (2 * E) * x.length + 2 * E := by ring
  have e2 : (2 * E) * 1 = 2 * E := by ring
  have e3 : (2 * E) * x.length + (3 * k + 8) * x.length
      = ((4 * k + 2) * C₁ + 17 * k + 50) * x.length := by
    rw [hEdef]; ring
  simp only [decompose2Work] at h ⊢
  omega

end PalPeg
