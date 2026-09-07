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

end PalPeg
