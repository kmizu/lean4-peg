import PalPeg.GSDecompL1
import PalPeg.GSPreprocess

/-!
# `decompose2`：run 単位で飛ばす削除ループと、無条件の L1 上界

`PalPeg.GSPreprocess` の `stripLoop` は最小周期を 1 つぶんずつ削るので、削除列が
「`T` 未満の `k`-繰り返し周期を持たない最初の位置」を跨ぎ越しうる。そこで
`gs_events.py` の `decomposition` と同じく **`start += reach - k*p + 1`**（周期 `p` の
`k`-繰り返しが初めて壊れる位置まで一気に進む）に変えたのが `stripLoop2` である。

この規則では、`[s, s')` の各位置に残存 run が `k*p` 以上あるので、
**通過した位置はすべて `T` 未満の `k`-繰り返し周期を持つ**（`stripLoop2_eligible`）。
したがって停止位置は「`T` 未満の周期を持たない最初の位置」そのものであり、
`GSDecompL1.pass_stops_before_second` からその位置は `s + T` 未満になる。
結果として `GSDecomp` の L1 上界が**仮定なしで**得られる。
-/

namespace PalPeg

universe u
variable {α : Type u} [DecidableEq α]
set_option linter.unusedSectionVars false

/-! ## `secondPeriod` が成功したときの仕様 -/

/-- `secondPeriod` が `some p₂` を返すときの仕様（`secondPeriod_none` の対）。 -/
theorem secondPeriod_some (v : List α) (k p₁ r p₂ : ℕ) (hk : 3 ≤ k)
    (hleast : IsLeastKRep v k p₁) (hreach : HasPeriod (v.take r) p₁) (hrle : r ≤ v.length)
    (h : secondPeriod v k p₁ r = some p₂) :
    Second v k r p₂ ∧ ∀ p', p' < p₂ → ¬ Second v k r p' := by
  refine secondOuter_some v k p₁ r hk hleast hreach hrle (v.length + 1) 1 0 p₂ (by omega) ?_ ?_ h
  · intro hlt
    refine ⟨by omega, ?_, ?_⟩
    · rw [hasPeriod_take_iff (by omega)]
      intro i hi; exact absurd hi (by omega)
    · rintro ⟨-, h2⟩
      rw [Nat.mul_one] at h2
      omega
  · intro p' hp'
    rintro ⟨h1, -, -⟩
    omega

/-! ## `firstOuter` の返す周期は `bound` 未満 -/

theorem firstOuter_lt_bound (v : List α) (k bound : ℕ) :
    ∀ (fuel p p₁ m : ℕ), firstOuter v k bound fuel p = some (p₁, m) → p₁ < bound := by
  intro fuel
  induction fuel with
  | zero => intro p p₁ m h; exact absurd h (by simp [firstOuter])
  | succ fuel ih =>
    intro p p₁ m h
    rw [firstOuter] at h
    split at h
    · next hg =>
      split at h
      · rw [Option.some.injEq, Prod.mk.injEq] at h
        exact h.1 ▸ hg.2
      · exact ih _ _ _ h
    · exact absurd h (by simp)

/-! ## 新しい削除ループ -/

/-- **run 単位の削除ループ**。周期 `p` の到達域 `r` に対し `r - k*p + 1` だけ進む
（`strip_kills_period` の削除量）。 -/
def stripLoop2 (x : List α) (k bound : ℕ) : ℕ → ℕ → ℕ
  | 0, s => s
  | fuel + 1, s =>
      match firstOuter (x.drop s) k bound (x.length + 1) 1 with
      | none => s
      | some (p, _) =>
          stripLoop2 x k bound fuel
            (s + (extendReach (x.drop s) p (x.length + 1) (k * p) - k * p + 1))

/-- 1 パスで得られるデータ（最小周期・到達域・削除量）をまとめて取り出す。 -/
private theorem strip_step_data (x : List α) (k bound : ℕ) (hk : 3 ≤ k) {s p m : ℕ}
    (hs : s ≤ x.length) (hfo : firstOuter (x.drop s) k bound (x.length + 1) 1 = some (p, m)) :
    IsLeastKRep (x.drop s) k p ∧ p < bound ∧
      k * p ≤ extendReach (x.drop s) p (x.length + 1) (k * p) ∧
      ReachOf (x.drop s) p (extendReach (x.drop s) p (x.length + 1) (k * p)) := by
  have hbelow : ∀ p', p' < 1 → ¬ KRep (x.drop s) k p' := by
    intro p' hp'; rintro ⟨h1, -, -⟩; omega
  obtain ⟨hleast, -⟩ :=
    firstOuter_some (x.drop s) k bound hk (x.length + 1) 1 p m (by omega) hbelow hfo
  refine ⟨hleast, firstOuter_lt_bound (x.drop s) k bound (x.length + 1) 1 p m hfo, ?_⟩
  have hvlen : (x.drop s).length = x.length - s := by simp
  exact extendReach_spec (x.drop s) p (x.length + 1) (k * p) (by omega)
    (Nat.le_mul_of_pos_left p (by omega)) hleast.1.2.1 hleast.1.2.2

theorem stripLoop2_ge (x : List α) (k bound : ℕ) :
    ∀ (fuel s : ℕ), s ≤ stripLoop2 x k bound fuel s := by
  intro fuel
  induction fuel with
  | zero => intro s; exact le_refl _
  | succ fuel ih =>
    intro s
    rw [stripLoop2]
    rcases hfo : firstOuter (x.drop s) k bound (x.length + 1) 1 with _ | ⟨p, m⟩
    · simp only []
      exact le_refl _
    · simp only []
      exact le_trans (Nat.le_add_right s _) (ih _)

theorem stripLoop2_le (x : List α) (k bound : ℕ) (hk : 3 ≤ k) :
    ∀ (fuel s : ℕ), s ≤ x.length → stripLoop2 x k bound fuel s ≤ x.length := by
  intro fuel
  induction fuel with
  | zero => intro s hs; exact hs
  | succ fuel ih =>
    intro s hs
    rw [stripLoop2]
    rcases hfo : firstOuter (x.drop s) k bound (x.length + 1) 1 with _ | ⟨p, m⟩
    · simp only []; exact hs
    · simp only []
      obtain ⟨hleast, -, hrge, hreach⟩ := strip_step_data x k bound hk hs hfo
      have hvlen : (x.drop s).length = x.length - s := by simp
      have h1 := hreach.1
      have hp : 0 < p := hleast.1.1
      have hkp : 0 < k * p := Nat.mul_pos (by omega) hp
      exact ih _ (by omega)

/-- **停止条件**：終了後の接尾辞には `bound` 未満の `k`-繰り返し周期がない。 -/
theorem stripLoop2_spec (x : List α) (k bound : ℕ) (hk : 3 ≤ k) :
    ∀ (fuel s : ℕ), s ≤ x.length → x.length ≤ fuel + s →
      ∀ p', p' < bound → ¬ KRep (x.drop (stripLoop2 x k bound fuel s)) k p' := by
  intro fuel
  induction fuel with
  | zero =>
    intro s hs hf p' hp'
    have hnil : x.drop (stripLoop2 x k bound 0 s) = ([] : List α) := by
      show x.drop s = []
      rw [show s = x.length from by omega]; simp
    rw [hnil]
    exact not_krep_nil (by omega)
  | succ fuel ih =>
    intro s hs hf p' hp'
    rw [stripLoop2]
    rcases hfo : firstOuter (x.drop s) k bound (x.length + 1) 1 with _ | ⟨p, m⟩
    · simp only []
      have hvlen : (x.drop s).length = x.length - s := by simp
      exact firstOuter_none_bnd (x.drop s) k bound hk (x.length + 1) 1 (by omega) (by omega)
        (by intro p'' h''; rintro ⟨h1, -, -⟩; omega) hfo p' hp'
    · simp only []
      obtain ⟨hleast, -, hrge, hreach⟩ := strip_step_data x k bound hk hs hfo
      have hvlen : (x.drop s).length = x.length - s := by simp
      have h1 := hreach.1
      have hp : 0 < p := hleast.1.1
      have hkp : 0 < k * p := Nat.mul_pos (by omega) hp
      exact ih _ (by omega) (by omega) p' hp'

/-- **通過した位置はすべて `bound` 未満の `k`-繰り返し周期を持つ**。
削除量が `r - k*p + 1` なので、途中の各位置には周期 `p` の run が `k*p` 以上残る。 -/
theorem stripLoop2_eligible (x : List α) (k bound : ℕ) (hk : 3 ≤ k) :
    ∀ (fuel s b : ℕ), s ≤ x.length → s ≤ b → b < stripLoop2 x k bound fuel s →
      ∃ p, p < bound ∧ KRep (x.drop b) k p := by
  intro fuel
  induction fuel with
  | zero => intro s b _ hsb hb; rw [stripLoop2] at hb; omega
  | succ fuel ih =>
    intro s b hs hsb hb
    rw [stripLoop2] at hb
    rcases hfo : firstOuter (x.drop s) k bound (x.length + 1) 1 with _ | ⟨p, m⟩
    · rw [hfo] at hb; simp only [] at hb; omega
    · rw [hfo] at hb; simp only [] at hb
      obtain ⟨hleast, hpb, hrge, hreach⟩ := strip_step_data x k bound hk hs hfo
      set r := extendReach (x.drop s) p (x.length + 1) (k * p) with hrdef
      have hvlen : (x.drop s).length = x.length - s := by simp
      have hrle : r ≤ x.length - s := by have := hreach.1; omega
      have hp : 0 < p := hleast.1.1
      have hkp : 0 < k * p := Nat.mul_pos (by omega) hp
      by_cases hlt : b < s + (r - k * p + 1)
      · -- `b` は run の内側：周期 `p` がまだ `k` 回残っている
        refine ⟨p, hpb, ?_, ?_, ?_⟩
        · exact hp
        · rw [List.length_drop]; omega
        · have hdt : HasPeriod (((x.drop s).drop (b - s)).take (r - (b - s))) p :=
            hasPeriod_drop_take hreach.2.1 (by omega) (by omega)
          have hEq : (x.drop s).drop (b - s) = x.drop b := by
            rw [List.drop_drop]
            exact congrArg (fun t => x.drop t) (by omega)
          rw [hEq] at hdt
          exact hasPeriod_take_of_le hdt (by omega)
      · exact ih _ b (by omega) (by omega) hb

/-- **1 パスの削除量は第 2 周期未満**（`pass_stops_before_second` の帰結）。 -/
theorem stripLoop2_lt_second (x : List α) (k : ℕ) (hk : 4 ≤ k) {s T m : ℕ}
    (hs : s ≤ x.length) (hT : 0 < T) (hprim : Primitive ((x.drop s).take T))
    (hkT : k * T ≤ m) (hm : m ≤ (x.drop s).length)
    (hperT : HasPeriod ((x.drop s).take m) T) :
    ∀ fuel, stripLoop2 x k T fuel s < s + T := by
  intro fuel
  obtain ⟨a, haT, hstop⟩ :=
    pass_stops_before_second (v := x.drop s) (T := T) (m := m) hk hT hprim hkT hm hperT
  have hvlen : (x.drop s).length = x.length - s := by simp
  by_contra hcon
  have hb : s + a < stripLoop2 x k T fuel s := by omega
  obtain ⟨q, hqT, hq⟩ := stripLoop2_eligible x k T (by omega) fuel s (s + a) hs (by omega) hb
  refine hstop q hqT ?_
  have hEq : (x.drop s).drop a = x.drop (s + a) := by rw [List.drop_drop]
  rw [hEq]
  exact hq

/-! ## 新しい前処理本体 -/

/-- `decomposeLoop` の `stripLoop` を `stripLoop2` に差し替えたもの。 -/
def decomposeLoop2 (x : List α) (k : ℕ) : ℕ → ℕ → ℕ × ℕ × ℕ
  | 0, _ => (x.length, 0, 0)
  | fuel + 1, s =>
      match firstPeriod (x.drop s) k with
      | none => (s, 0, 0)
      | some (p₁, m) =>
          match secondPeriod (x.drop s) k p₁ (extendReach (x.drop s) p₁ (x.length + 1) m) with
          | none => (s, p₁, extendReach (x.drop s) p₁ (x.length + 1) m)
          | some p₂ => decomposeLoop2 x k fuel (stripLoop2 x k p₂ (x.length + 1) s)

/-- **GS 前処理（run 単位削除版）**。 -/
def decompose2 (x : List α) (k : ℕ) : ℕ × ℕ × ℕ := decomposeLoop2 x k (x.length + 1) 0

theorem decomposeLoop2_spec (x : List α) (k : ℕ) (hk : 3 ≤ k) :
    ∀ (fuel s : ℕ), s ≤ x.length →
      GSCore x k (decomposeLoop2 x k fuel s).1 (decomposeLoop2 x k fuel s).2.1
        (decomposeLoop2 x k fuel s).2.2 := by
  intro fuel
  induction fuel with
  | zero => intro s _; exact gsCore_full x k (by omega)
  | succ fuel ih =>
    intro s hs
    have hvlen : (x.drop s).length = x.length - s := by simp
    rcases hfp : firstPeriod (x.drop s) k with _ | ⟨p₁, m⟩
    · have heq : decomposeLoop2 x k (fuel + 1) s = (s, 0, 0) := by
        rw [decomposeLoop2]; simp only [hfp]
      rw [heq]
      show GSCore x k s 0 0
      have hnone := firstPeriod_none (x.drop s) k hk hfp
      exact ⟨hs, fun _ => ⟨rfl, hnone⟩, fun h => absurd rfl h, fun h => absurd rfl h,
        fun h => absurd rfl h, fun h => absurd rfl h⟩
    · obtain ⟨hleast, rfl⟩ := firstPeriod_some (x.drop s) k hk hfp
      have hp₁ : 0 < p₁ := hleast.1.1
      obtain ⟨r, hrdef, hrge, hreach⟩ :
          ∃ r, extendReach (x.drop s) p₁ (x.length + 1) (k * p₁) = r ∧ k * p₁ ≤ r ∧
            ReachOf (x.drop s) p₁ r := by
        obtain ⟨h1, h2⟩ := extendReach_spec (x.drop s) p₁ (x.length + 1) (k * p₁) (by omega)
          (Nat.le_mul_of_pos_left p₁ (by omega)) hleast.1.2.1 hleast.1.2.2
        exact ⟨_, rfl, h1, h2⟩
      rcases hsp : secondPeriod (x.drop s) k p₁ r with _ | p₂
      · have heq : decomposeLoop2 x k (fuel + 1) s = (s, p₁, r) := by
          rw [decomposeLoop2]; simp only [hfp, hrdef, hsp]
        rw [heq]
        show GSCore x k s p₁ r
        refine ⟨hs, fun h => absurd h (by omega), fun _ => hleast, fun _ => hreach,
          fun _ => hrge, fun _ => ?_⟩
        exact secondPeriod_none (x.drop s) k p₁ r hk hleast hreach.2.1 hreach.1 hsp
      · have heq : decomposeLoop2 x k (fuel + 1) s
            = decomposeLoop2 x k fuel (stripLoop2 x k p₂ (x.length + 1) s) := by
          rw [decomposeLoop2]; simp only [hfp, hrdef, hsp]
        rw [heq]
        exact ih _ (stripLoop2_le x k p₂ hk (x.length + 1) s hs)

/-- `decompose2` も `GSCore` を計算する。 -/
theorem decompose2_spec (x : List α) (k : ℕ) (hk : 3 ≤ k) :
    GSCore x k (decompose2 x k).1 (decompose2 x k).2.1 (decompose2 x k).2.2 :=
  decomposeLoop2_spec x k hk (x.length + 1) 0 (Nat.zero_le _)

/-! ## 無条件の L1 上界 -/

/-- `decomposeLoop2` に沿った不変量（`GSDecompL1.gsDecomp_aux` と同型）。 -/
private theorem decomposeLoop2_bound (x : List α) (k : ℕ) (hk : 4 ≤ k) :
    ∀ (fuel s : ℕ), s ≤ x.length → x.length ≤ fuel + s →
      ∃ d, (decomposeLoop2 x k fuel s).1 = s + d ∧ s + d ≤ x.length ∧
        (d = 0 ∨ ∃ T₁ Tn q, IsLeastKRep (x.drop s) k q ∧ (k - 1) * q ≤ T₁ ∧
          (k - 2) * d + T₁ ≤ (k - 1) * Tn ∧ (k - 1) * Tn + d < x.length - s ∧
          ((decomposeLoop2 x k fuel s).2.1 ≠ 0 → Tn ≤ (decomposeLoop2 x k fuel s).2.1)) := by
  intro fuel
  induction fuel with
  | zero =>
    intro s hs hf
    refine ⟨0, ?_, by omega, Or.inl rfl⟩
    show x.length = s + 0
    omega
  | succ fuel ih =>
    intro s hs hf
    have hvlen : (x.drop s).length = x.length - s := by simp
    rcases hfp : firstPeriod (x.drop s) k with _ | ⟨p₁, m⟩
    · have heq : decomposeLoop2 x k (fuel + 1) s = (s, 0, 0) := by
        rw [decomposeLoop2]; simp only [hfp]
      rw [heq]
      exact ⟨0, by omega, by omega, Or.inl rfl⟩
    · obtain ⟨hleast, rfl⟩ := firstPeriod_some (x.drop s) k (by omega) hfp
      have hp₁ : 0 < p₁ := hleast.1.1
      obtain ⟨r, hrdef, hrge, hreach⟩ :
          ∃ r, extendReach (x.drop s) p₁ (x.length + 1) (k * p₁) = r ∧ k * p₁ ≤ r ∧
            ReachOf (x.drop s) p₁ r := by
        obtain ⟨h1, h2⟩ := extendReach_spec (x.drop s) p₁ (x.length + 1) (k * p₁) (by omega)
          (Nat.le_mul_of_pos_left p₁ (by omega)) hleast.1.2.1 hleast.1.2.2
        exact ⟨_, rfl, h1, h2⟩
      rcases hsp : secondPeriod (x.drop s) k p₁ r with _ | p₂
      · have heq : decomposeLoop2 x k (fuel + 1) s = (s, p₁, r) := by
          rw [decomposeLoop2]; simp only [hfp, hrdef, hsp]
        rw [heq]
        exact ⟨0, by omega, by omega, Or.inl rfl⟩
      · set s' := stripLoop2 x k p₂ (x.length + 1) s with hs'def
        have heq : decomposeLoop2 x k (fuel + 1) s = decomposeLoop2 x k fuel s' := by
          rw [decomposeLoop2]; simp only [hfp, hrdef, hsp, hs'def]
        rw [heq]
        obtain ⟨hsec, hsecmin⟩ :=
          secondPeriod_some (x.drop s) k p₁ r p₂ (by omega) hleast hreach.2.1 hreach.1 hsp
        have hkrep₂ : KRep (x.drop s) k p₂ := kRep_of_second hsec
        have hprim : Primitive ((x.drop s).take p₂) :=
          second_primitive_of_least (by omega) hsec hsecmin
        have hle12 : p₁ ≤ p₂ := hleast.2 _ hkrep₂
        have hne12 : p₁ ≠ p₂ := fun heq2 => not_second_reach hreach (heq2 ▸ hsec)
        have hlt12 : p₁ < p₂ := lt_of_le_of_ne hle12 hne12
        have hkp : (k - 1) * p₁ ≤ p₂ :=
          kRepetition_periods (by omega) hleast.1 hkrep₂ hprim hlt12
        have hkp₂len : k * p₂ ≤ x.length - s := by
          have h1 := hsec.2.1
          have h2 : k * p₂ ≤ max (k * p₂) (r + 1) := le_max_left _ _
          omega
        have hs'lt : s' < s + p₂ :=
          stripLoop2_lt_second x k hk hs hsec.1 hprim (le_max_left _ _) hsec.2.1 hsec.2.2 _
        have hs'ge : s ≤ s' := stripLoop2_ge x k p₂ (x.length + 1) s
        have hs'le : s' ≤ x.length := stripLoop2_le x k p₂ (by omega) (x.length + 1) s hs
        have hstop : ∀ p', p' < p₂ → ¬ KRep (x.drop s') k p' :=
          stripLoop2_spec x k p₂ (by omega) (x.length + 1) s hs (by omega)
        have hs'ne : s ≠ s' := fun heq2 => hstop p₁ hlt12 (heq2 ▸ hleast.1)
        obtain ⟨d', hd'eq, hd'le, hd'inv⟩ := ih s' hs'le (by omega)
        refine ⟨(s' - s) + d', by rw [hd'eq]; omega, by omega, Or.inr ?_⟩
        have hnew : ∀ q, IsLeastKRep (x.drop s') k q → p₂ ≤ q := by
          intro q hq
          by_contra hc
          exact hstop q (by omega) hq.1
        have hmul2 : (k - 2) * p₂ + p₂ = (k - 1) * p₂ := by
          rw [← Nat.succ_mul]; congr 1; omega
        have hmul1 : (k - 1) * p₂ + p₂ = k * p₂ := by
          rw [← Nat.succ_mul]; congr 1; omega
        have hma : (k - 2) * (s' - s) ≤ (k - 2) * p₂ :=
          Nat.mul_le_mul_left (k - 2) (by omega)
        rcases hd'inv with h0 | ⟨T₁', Tn', q', hq', hq'T, hsum', hlast', hTn'⟩
        · subst h0
          simp only [Nat.add_zero]
          refine ⟨p₂, p₂, p₁, hleast, hkp, by omega, by omega, ?_⟩
          intro hne
          refine hnew _ ?_
          have hL := (decomposeLoop2_spec x k (by omega) fuel s' hs'le).least hne
          rwa [hd'eq, Nat.add_zero] at hL
        · refine ⟨p₂, Tn', p₁, hleast, hkp, ?_, ?_, hTn'⟩
          · have h4 : (k - 1) * p₂ ≤ (k - 1) * q' := Nat.mul_le_mul_left (k - 1) (hnew q' hq')
            have h5 : (k - 2) * ((s' - s) + d') = (k - 2) * (s' - s) + (k - 2) * d' := by ring
            omega
          · omega

/-- **主定理（無条件）**：`decompose2 x k` の出力そのものが L1 上界つきの `GSDecomp` を
満たす。 -/
theorem decompose2_gsDecomp {k : ℕ} (hk : 4 ≤ k) (x : List α) :
    GSDecomp x k (decompose2 x k).1 (decompose2 x k).2.1 (decompose2 x k).2.2 := by
  have H : GSCore x k (decompose2 x k).1 (decompose2 x k).2.1 (decompose2 x k).2.2 :=
    decompose2_spec x k (by omega)
  have hdec : decompose2 x k = decomposeLoop2 x k (x.length + 1) 0 := rfl
  obtain ⟨d, hd, hdle, hinv⟩ := decomposeLoop2_bound x k hk (x.length + 1) 0
    (Nat.zero_le _) (by omega)
  rw [← hdec] at hd hinv
  have hs : (decompose2 x k).1 = d := by omega
  rcases hinv with h0 | ⟨T₁, Tn, q, hq, hqT, hsum, hlast, hTn⟩
  · subst h0
    rw [hs] at H ⊢
    exact gsDecomp_of_core_zero (by omega) H
  · have hqpos : 0 < q := hq.1.1
    have hT₁pos : 0 < T₁ := by
      have : k - 1 ≤ (k - 1) * q := Nat.le_mul_of_pos_right (k - 1) hqpos
      omega
    have hks : (k - 2) * d + d = (k - 1) * d := by
      rw [← Nat.succ_mul]; congr 1; omega
    refine ⟨H, ?_, ?_⟩
    · intro _; rw [hs]; omega
    · intro hne
      rw [hs]
      have hle := Nat.mul_le_mul_left (k - 1) (hTn hne)
      omega

/-- 切断は真に短い（`OnlineMachine.PrepImplSpecH` 向け）。 -/
theorem decompose2_cut_lt {k : ℕ} (hk : 4 ≤ k) {x : List α} (hx : x ≠ []) :
    (decompose2 x k).1 < x.length := by
  have h := (decompose2_gsDecomp hk x).cut_bound hx
  have : (decompose2 x k).1 ≤ (k - 1) * (decompose2 x k).1 :=
    Nat.le_mul_of_pos_left _ (by omega)
  omega

/-- 走査側が要求する `KSimple`。 -/
theorem decompose2_ksimple {k : ℕ} (hk : 4 ≤ k) (x : List α)
    (hp₁ : (decompose2 x k).2.1 ≠ 0) :
    KSimple (x.drop (decompose2 x k).1) k (decompose2 x k).2.1 (decompose2 x k).2.2 :=
  (decompose2_gsDecomp hk x).ksimple hp₁

/-! ## 仕事量カウンタ

`PalPeg.GSPreprocess` の `stripLoopWork` / `decomposeLoopWork` / `decomposeWork` を
`stripLoop2` 版に写したもの。`stripLoop2` は 1 反復ごとに `firstOuter` の走査に加えて
`extendReach` の伸長も行うので、その分もカウントする。 -/

def stripLoop2Work (x : List α) (k bound : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, s =>
      firstOuterWork (x.drop s) k bound (x.length + 1) 1 +
        (match firstOuter (x.drop s) k bound (x.length + 1) 1 with
         | none => 0
         | some (p, _) =>
             extendReachWork (x.drop s) p (x.length + 1) (k * p) +
               stripLoop2Work x k bound fuel
                 (s + (extendReach (x.drop s) p (x.length + 1) (k * p) - k * p + 1)))

def decomposeLoop2Work (x : List α) (k : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, s =>
      decomposeStepWork x k s +
        (match firstPeriod (x.drop s) k with
         | none => 0
         | some (p₁, m) =>
             match secondPeriod (x.drop s) k p₁ (extendReach (x.drop s) p₁ (x.length + 1) m) with
             | none => 0
             | some p₂ =>
                 stripLoop2Work x k p₂ (x.length + 1) s +
                   decomposeLoop2Work x k fuel (stripLoop2 x k p₂ (x.length + 1) s))

/-- **仕事量カウンタ**（`decompose2` 全体）。 -/
def decompose2Work (x : List α) (k : ℕ) : ℕ := decomposeLoop2Work x k (x.length + 1) 0

/-! ### 仕事量解析の現状

1 反復あたりの内訳は次の 2 つで、後者は前進量に telescoping する：

* `firstOuterWork (x.drop aⱼ) k T (|x|+1) 1 ≤ (2k+1)*pⱼ + 2`（`firstOuterWork_le_some`）、
* `extendReachWork (x.drop aⱼ) pⱼ (|x|+1) (k*pⱼ) ≤ dⱼ + 1`（`extendReachWork_le'`、
  `dⱼ = rⱼ - k*pⱼ + 1`）。

`Σⱼ dⱼ` は 1 パスの前進量なので `stripLoop2_lt_second` より `< T`、反復回数も
`dⱼ ≥ 1` より `< T`。したがって

`1 パスの仕事 ≤ (2k+1) * Σⱼ pⱼ + 4*T`

まで無条件に落ちる。残るのは **`Σⱼ pⱼ = O(T)`** のみで、これは未解決である
（下の反例を参照）。 -/

/-! ### 反例：連続する run の重なりは `pⱼ + pⱼ₊₁` 未満とは限らない

`w = (b a⁹)⁴`（`b = 1`, `a = 0`, `k = 4`, `|w| = 40`）では

* `p₀ = 10`（最小 4-繰り返し周期）、`r₀ = 40`、`d₀ = r₀ - k*p₀ + 1 = 1`、
* `p₁ = 1`（`w.drop 1` の最小 4-繰り返し周期）

なので重なり `k*p₀ - d₀ = 39` に対し `p₀ + p₁ = 11` であり `39 < 11` は成り立たない。
（重なりのうち両方の周期を担うのは `min (k*p₀ - d₀) (k*p₁) = 4` 文字だけで、
Fine–Wilf に要る `p₀ + p₁ - gcd = 10` に届かない。）
同時に `(k-1)*p₀ = 30 < d₀ + p₁ = 2` も偽なので、
`(k-2) * Σⱼ pⱼ < Σⱼ dⱼ + p_N` 型の総和評価はこの経路からは出ない。 -/

/-- 反例の語。 -/
def cexWordGS : List ℕ := (List.replicate 4 (1 :: List.replicate 9 0)).flatten

example : cexWordGS.length = 40 := by decide

example : firstPeriod cexWordGS 4 = some (10, 40) := by decide

example : extendReach cexWordGS 10 (cexWordGS.length + 1) 40 = 40 := by decide

example : firstPeriod (cexWordGS.drop 1) 4 = some (1, 4) := by decide

/-! ## 入れ子木（nesting tree）の 2 本の補題

1 パスの run 開始位置 `aⱼ`、最小周期 `pⱼ`、到達域 `rⱼ`、窓 `Wⱼ = [aⱼ, aⱼ + k*pⱼ)`、
周期領域 `Rⱼ = [aⱼ, aⱼ + rⱼ)` に対し

* **(A) 子**：`Wⱼ' ⊆ Rⱼ` かつ `pⱼ' ≠ pⱼ` なら `(k-1) * pⱼ' < pⱼ`；
* **(B) 兄弟**：`aⱼ' < aⱼ + rⱼ` かつ `Wⱼ' ⊄ Rⱼ` なら `(aⱼ + rⱼ) - aⱼ' < pⱼ + pⱼ'`。

反例 `(b a⁹)⁴` は (A) の側（`p=1` の窓が `p=10` の領域の内側）なので (B) の
重なり制約は掛からない、という区別がここで効く。 -/

/-- **内側ブロックの伝播**。周期 `p` の領域 `[0, r)` の内側に、長さ `p + g` 以上で
周期 `g`（`g ∣ p`）のブロックがあれば、領域全体が周期 `g` を持つ。

証明：`p`-周期性で添字を `p` で割った余りに落とし、ブロック `[t, t+L)` の中の
代表元へ移してからブロックの `g`-周期性を使う。 -/
theorem hasPeriod_of_inner_block {w : List α} {p g t L r : ℕ}
    (hp : 0 < p) (hgp : g ∣ p)
    (hper : HasPeriod (w.take r) p) (hr : r ≤ w.length)
    (htL : t + L ≤ r) (hL : p + g ≤ L)
    (hblock : HasPeriod ((w.drop t).take L) g) :
    HasPeriod (w.take r) g := by
  have hgp' : g ≤ p := Nat.le_of_dvd hp hgp
  have hulen : (w.take r).length = r := by simp only [List.length_take]; omega
  intro i hi
  rw [hulen] at hi
  -- ブロック内の代表元 `b`（`b ≡ i (mod p)`, `t ≤ b < t + p`）
  have hdm := Nat.div_add_mod t p
  have hmlt : t % p < p := Nat.mod_lt _ hp
  have hilt : i % p < p := Nat.mod_lt _ hp
  obtain ⟨b, hbt, hbp, hbmod⟩ : ∃ b, t ≤ b ∧ b < t + p ∧ b % p = i % p := by
    by_cases hc : i % p < t % p
    · refine ⟨p * (t / p) + i % p + p, by omega, by omega, ?_⟩
      have he : p * (t / p) + i % p + p = p * (t / p + 1) + i % p := by ring
      rw [he, Nat.mul_add_mod, Nat.mod_eq_of_lt hilt]
    · refine ⟨p * (t / p) + i % p, by omega, by omega, ?_⟩
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hilt]
  have hbr : b + g < r := by omega
  -- 各点を `w` の添字に直す
  have htake : ∀ j, j < r → (w.take r)[j]? = w[j]? := by
    intro j hj; exact List.getElem?_take_of_lt hj
  have hmod : ∀ j, j < r → w[j]? = w[j % p]? := by
    intro j hj
    have h := hasPeriod_getElem?_mod hper (by rw [hulen]; exact hj)
    have hjp : j % p < r := lt_of_lt_of_le (Nat.mod_lt _ hp) (by omega)
    rw [htake (j % p) hjp, htake j hj] at h
    exact h.symm
  -- ブロックの `g`-周期性
  have hbg : w[b]? = w[b + g]? := by
    have h := hblock (b - t) (by rw [List.length_take, List.length_drop]; omega)
    rw [List.getElem?_take_of_lt (show b - t < L by omega),
      List.getElem?_take_of_lt (show b - t + g < L by omega),
      List.getElem?_drop, List.getElem?_drop,
      show t + (b - t) = b from by omega,
      show t + (b - t + g) = b + g from by omega] at h
    exact h
  have hmodeq : (b + g) % p = (i + g) % p := by
    rw [Nat.add_mod b g p, Nat.add_mod i g p, hbmod]
  rw [htake _ (by omega), htake _ (by omega), hmod i (by omega), hmod (i + g) (by omega),
    ← hbmod, ← hmodeq, ← hmod b (by omega), ← hmod (b + g) (by omega)]
  exact hbg

/-- **核となる補題**。最小 `k`-繰り返し周期 `p`・到達域 `r` の領域 `[0, r)` の内側に、
長さ `p + q` 以上の周期 `q` の窓があれば `p ∣ q`。 -/
theorem dvd_of_inner_window {w : List α} {k p q t L r : ℕ} (_hk : 2 ≤ k)
    (hleast : IsLeastKRep w k p) (hR : ReachOf w p r) (hkr : k * p ≤ r)
    (hq : 0 < q) (htL : t + L ≤ r) (hpqL : p + q ≤ L)
    (hwin : HasPeriod ((w.drop t).take L) q) : p ∣ q := by
  have hp : 0 < p := hleast.1.1
  have hrle : r ≤ w.length := hR.1
  have hwlen : ((w.drop t).take L).length = L := by
    rw [List.length_take, List.length_drop]; omega
  have hwp : HasPeriod ((w.drop t).take L) p :=
    hasPeriod_take_of_le (hasPeriod_drop_take hR.2.1 hrle (by omega)) (by omega)
  have hgle : Nat.gcd p q ≤ p := Nat.gcd_le_left _ hp
  have hgq : Nat.gcd p q ≤ q := Nat.gcd_le_right _ hq
  have hgpos : 0 < Nat.gcd p q := Nat.gcd_pos_of_pos_left _ hp
  have hg := fineWilf hwp hwin hp hq (by rw [hwlen]; omega)
  have hall : HasPeriod (w.take r) (Nat.gcd p q) :=
    hasPeriod_of_inner_block hp (Nat.gcd_dvd_left p q) hR.2.1 hrle htL (by omega) hg
  have hgeq : Nat.gcd p q = p := by
    by_contra hne
    have hlt : Nat.gcd p q < p := by omega
    have hkg : k * Nat.gcd p q ≤ k * p := Nat.mul_le_mul_left k (by omega)
    have hkrep : KRep w k (Nat.gcd p q) :=
      ⟨hgpos, by omega, hasPeriod_take_of_le hall (by omega)⟩
    have := hleast.2 _ hkrep
    omega
  rw [← hgeq]; exact Nat.gcd_dvd_right p q

/-- **(A) 子の周期の上界**。子の窓 `[t, t + k*q)` が親の周期領域 `[0, r)` に収まり、
かつ `q ≠ p` なら `(k-1) * q < p`。 -/
theorem child_period_bound {w : List α} {k p q t r : ℕ} (hk : 4 ≤ k)
    (hleast : IsLeastKRep w k p) (hR : ReachOf w p r) (hkr : k * p ≤ r)
    (hq : IsLeastKRep (w.drop t) k q) (hfit : t + k * q ≤ r) (hne : q ≠ p) :
    (k - 1) * q < p := by
  by_contra hcon
  have hqpos : 0 < q := hq.1.1
  have hppos : 0 < p := hleast.1.1
  have hsub : (k - 1) * q + q = k * q := by
    have h1 := Nat.sub_one_mul k q
    have h2 : q ≤ k * q := Nat.le_mul_of_pos_left q (by omega)
    omega
  have hpq : p + q ≤ k * q := by omega
  have hdvd : p ∣ q :=
    dvd_of_inner_window (by omega) hleast hR hkr hqpos hfit hpq hq.1.2.2
  have hple : p ≤ q := Nat.le_of_dvd hqpos hdvd
  -- 子の窓は親の `p`-周期領域の内側なので `p`-周期的でもある
  have hkple : k * p ≤ k * q := Nat.mul_le_mul_left k hple
  have hpwin : HasPeriod ((w.drop t).take (k * q)) p :=
    hasPeriod_take_of_le (hasPeriod_drop_take hR.2.1 hR.1 (by omega)) (by omega)
  have hkrep : KRep (w.drop t) k p :=
    ⟨hppos, by rw [List.length_drop]; have := hR.1; omega,
      hasPeriod_take_of_le hpwin hkple⟩
  have := hq.2 _ hkrep
  omega

/-- **(B) 兄弟の重なりの上界**。`t` が親の周期領域の内側 (`t < r`) でありながら
子の窓がそこに収まらない (`r < t + k*q`) なら、重なり `r - t` は `p + q` 未満。 -/
theorem sibling_overlap_lt {w : List α} {k p q t r : ℕ} (hk : 4 ≤ k)
    (hleast : IsLeastKRep w k p) (hR : ReachOf w p r) (hkr : k * p ≤ r)
    (hq : IsLeastKRep (w.drop t) k q) (htr : t < r) (hnfit : r < t + k * q) :
    r - t < p + q := by
  by_contra hcon
  have hL : p + q ≤ r - t := by omega
  have hqpos : 0 < q := hq.1.1
  have hppos : 0 < p := hleast.1.1
  have hrle : r ≤ w.length := hR.1
  have hqwin : HasPeriod ((w.drop t).take (r - t)) q :=
    hasPeriod_take_of_le hq.1.2.2 (by omega)
  have hdvd : p ∣ q :=
    dvd_of_inner_window (by omega) hleast hR hkr hqpos (by omega) hL hqwin
  have hple : p ≤ q := Nat.le_of_dvd hqpos hdvd
  -- 窓 `[t, t + k*q)` の長さ `q` の接頭辞は `p`-周期的、`p ∣ q` なので窓全体が `p`-周期的
  have hpre : HasPeriod (((w.drop t).take (k * q)).take q) p := by
    have h1 : ((w.drop t).take (k * q)).take q = (w.drop t).take q := by
      rw [List.take_take]; congr 1
      have : q ≤ k * q := Nat.le_mul_of_pos_left q (by omega)
      omega
    rw [h1]
    exact hasPeriod_take_of_le (hasPeriod_drop_take hR.2.1 hrle (by omega)) (by omega)
  have hpall : HasPeriod ((w.drop t).take (k * q)) p :=
    hasPeriod_of_prefix_dvd hq.1.2.2 hqpos hdvd hpre
  have hkple : k * p ≤ k * q := Nat.mul_le_mul_left k hple
  have hkrep : KRep (w.drop t) k p :=
    ⟨hppos, le_trans hkple hq.1.2.1, hasPeriod_take_of_le hpall hkple⟩
  have hqp : q ≤ p := hq.2 _ hkrep
  have hqeq : q = p := by omega
  subst hqeq
  -- `p`-周期性が到達域 `r` を越えて伸びてしまう
  have hlenw : t + k * q ≤ w.length := by
    have := hq.1.2.1; rw [List.length_drop] at this; omega
  have hglue : HasPeriod (w.take (t + k * q)) q :=
    hasPeriod_glue hR.2.1 hq.1.2.2 (by omega) (by omega) hlenw
  have hr1 : HasPeriod (w.take (r + 1)) q := hasPeriod_take_of_le hglue (by omega)
  rcases hR.2.2 with h | h
  · omega
  · exact h hr1

/-! ### 残る構造帰納法

(A)(B) から、親（周期 `P`、領域長 `r < P + T'`）の直下にある run 開始位置は
「その領域内で連続する兄弟」であり、(B) より隣接する兄弟の間隔は
`> r' - P - p'` で下から抑えられ、(A) より各子の周期は `< P/(k-1)`。
よって `Σ(子の周期) ≤ (r + P/(k-1))/(k-2)` となり、周期についての強帰納法で
`total(P) ≤ C * P` が従う。パスの最上位では「親」を `T`-周期領域そのもの
（周期 `T`、根が原始的）とみなせばよい。

この構造帰納法（木の形式化と `Σⱼ pⱼ ≤ C₁ * T` の証明）は未着手であり、
`decompose2Work_le` はまだ述べていない。上の「1 パスの仕事 ≤ (2k+1) * Σⱼ pⱼ + 4*T」
と合わせれば、`decomposeWork_le` と同じ幾何級数の総和で線形性が出る。 -/

end PalPeg
