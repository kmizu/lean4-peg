import PalPeg.GSDecomp
import PalPeg.BorderJob

/-!
# Galil–Seiferas 前処理の L1 上界（GS Theorem 1）

`PalPeg.GSDecomp` は `GSCore`（分解の意味論）と、弱い上界つきの存在
`gsDecompW_exists` までを与えていた。本ファイルはその残りのギャップ、すなわち

* `s < |x| / (k-1)`（`(k-1) * s < |x|`）
* `s < (k-1)/(k-2) * p₁`（`(k-2) * s < (k-1) * p₁`）

を証明し、`gsDecomp_exists` を与える。
-/

namespace PalPeg

universe u
variable {α : Type u}

/-! ## 周期窓の貼り合わせ -/

/-- 周期 `p` の窓 `[0, A)` と `[d, d+B)` が `p` 以上重なっていれば貼り合わせられる。 -/
theorem hasPeriod_glue {w : List α} {p d A B : ℕ}
    (h1 : HasPeriod (w.take A) p) (h2 : HasPeriod ((w.drop d).take B) p)
    (hdp : d + p ≤ A) (hAB : A ≤ d + B) (hlen : d + B ≤ w.length) :
    HasPeriod (w.take (d + B)) p := by
  intro i hi
  rw [List.length_take] at hi
  rw [List.getElem?_take_of_lt (show i < d + B by omega),
    List.getElem?_take_of_lt (show i + p < d + B by omega)]
  by_cases hA : i + p < A
  · have h := h1 i (by rw [List.length_take]; omega)
    rwa [List.getElem?_take_of_lt (show i < A by omega),
      List.getElem?_take_of_lt hA] at h
  · have hid : d ≤ i := by omega
    have h := h2 (i - d) (by rw [List.length_take, List.length_drop]; omega)
    rw [List.getElem?_take_of_lt (show i - d < B by omega),
      List.getElem?_take_of_lt (show i - d + p < B by omega),
      List.getElem?_drop, List.getElem?_drop,
      show d + (i - d) = i from by omega,
      show d + (i - d + p) = i + p from by omega] at h
    exact h

/-! ## `T`-周期領域の中での平行移動 -/

/-- `v.take m` が周期 `T` を持つとき、`m` の内側では `T` だけずらしても同じものが見える。 -/
theorem drop_shift_take_eq {v : List α} {T m b L : ℕ}
    (hperT : HasPeriod (v.take m) T) (hm : m ≤ v.length) (h : b + T + L ≤ m) :
    (v.drop (b + T)).take L = (v.drop b).take L := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < L
  · rw [List.getElem?_take_of_lt hi, List.getElem?_take_of_lt hi,
      List.getElem?_drop, List.getElem?_drop]
    have hh := hperT (b + i) (by rw [List.length_take]; omega)
    rw [List.getElem?_take_of_lt (show b + i < m by omega),
      List.getElem?_take_of_lt (show b + i + T < m by omega)] at hh
    calc v[b + T + i]? = v[b + i + T]? := getElem?_congr (by omega)
      _ = v[b + i]? := hh.symm
  · rw [List.getElem?_eq_none (by rw [List.length_take, List.length_drop]; omega),
      List.getElem?_eq_none (by rw [List.length_take, List.length_drop]; omega)]

/-- `k`-繰り返し接頭辞は `T`-周期領域の内側で `T` だけ右へ移せる。 -/
theorem krep_shift {v : List α} {T m b k q : ℕ}
    (hperT : HasPeriod (v.take m) T) (hm : m ≤ v.length) (h : b + T + k * q ≤ m)
    (hq : KRep (v.drop b) k q) : KRep (v.drop (b + T)) k q := by
  refine ⟨hq.1, by rw [List.length_drop]; omega, ?_⟩
  rw [drop_shift_take_eq hperT hm h]
  exact hq.2.2

/-! ## 1 周期削っても最小周期は減らない（`k*p ≤ r` 版） -/

/-- `period_not_decreasing_of_strip` の到達域条件を `k*p ≤ r` に弱めた版。 -/
theorem strip_period_ge {w : List α} {k p q r : ℕ} (hk : 4 ≤ k)
    (hmin : ∀ q', KRep w k q' → p ≤ q') (hp : 0 < p)
    (hper : HasPeriod (w.take r) p) (hrle : r ≤ w.length) (hkr : k * p ≤ r)
    (hq : IsLeastKRep (w.drop p) k q) : p ≤ q := by
  by_contra hcon
  have hqp : q < p := Nat.lt_of_not_le hcon
  have hqpos : 0 < q := hq.1.1
  have h4p : 4 * p ≤ k * p := Nat.mul_le_mul_right p hk
  have hdrop : (k - 1) * p < k * q :=
    strip_period_drop (by omega) hmin hp hper hrle hkr hq.1 hqp
  have hsub1 : (k - 1) * p + p = k * p := by
    have h1 := Nat.sub_one_mul k p
    have h2 : p ≤ k * p := Nat.le_mul_of_pos_left p (by omega)
    omega
  have hsub2 : (k - 1) * q + q = k * q := by
    have h1 := Nat.sub_one_mul k q
    have h2 : q ≤ k * q := Nat.le_mul_of_pos_left q (by omega)
    omega
  have h3q : 3 * q ≤ (k - 1) * q := Nat.mul_le_mul_right q (by omega)
  -- `p ≤ (k-1) * q`
  have hpk1q : p ≤ (k - 1) * q := by
    by_contra hc
    have hc' : (k - 1) * q + 1 ≤ p := by omega
    have h1 : (k - 1) * ((k - 1) * q + 1) ≤ (k - 1) * p := Nat.mul_le_mul_left (k - 1) hc'
    have h2 : (k - 1) * ((k - 1) * q + 1) = (k - 1) * ((k - 1) * q) + (k - 1) := by ring
    have h3 : 3 * ((k - 1) * q) ≤ (k - 1) * ((k - 1) * q) :=
      Nat.mul_le_mul_right ((k - 1) * q) (by omega)
    omega
  have hge : p + q ≤ min (k * q) (r - p) := by omega
  have hres : HasPeriod ((w.drop p).take (r - p)) p := hasPeriod_drop_take hper hrle (by omega)
  have hrho : r - p ≤ (w.drop p).length := by rw [List.length_drop]; omega
  have hdvd : q ∣ p := dvd_of_residual_run hp hqpos hres hrho hq.1
    (IsLeastKRep.primitive (by omega) hq) hge
  have h2q : 2 * q ≤ p := two_mul_le_of_dvd hp hqpos hdvd (by omega)
  have h5 : (k - 1) * (2 * q) ≤ (k - 1) * p := Nat.mul_le_mul_left (k - 1) h2q
  have h6 : (k - 1) * (2 * q) = 2 * ((k - 1) * q) := by ring
  omega

/-! ## 鍵となる補題：1 フェーズの削除は第 2 周期 `T` に届く前に止まる -/

/-- **`pass_stops_before_second`**。`v.take m` が原始的な根 `v.take T` の周期 `T` を持ち
（`k*T ≤ m ≤ |v|`）、`4 ≤ k` なら、位置 `a < T` であって `v.drop a` が `T` 未満の
`k`-繰り返し周期を一切持たないものが存在する。

証明：そうでないとすると `[0, T)` のすべての位置に `T` 未満の最小 `k`-繰り返し周期があり、
その最大値 `p` を取る。`reach_lt_add_of_periodic_window` から `(k-1)*p < T`。`T`-周期性から
最小周期は位置について `T`-周期的なので `p` の最大性は `[0, 2T)` に持ち上がり、`p` を
達成する位置 `a✱` から `p` ずつ削り続けても（`strip_period_ge` と最大性から）最小周期は
`p` のまま。よって `v.drop a✱` は長さ `T + p` を超える周期 `p` の窓を持ち、
`reach_lt_add_of_periodic_window` に矛盾する。 -/
theorem pass_stops_before_second {v : List α} {k T m : ℕ} (hk : 4 ≤ k)
    (hT : 0 < T) (hprim : Primitive (v.take T))
    (hkT : k * T ≤ m) (hm : m ≤ v.length) (hperT : HasPeriod (v.take m) T) :
    ∃ a, a < T ∧ ∀ q, q < T → ¬ KRep (v.drop a) k q := by
  classical
  have h4T : 4 * T ≤ k * T := Nat.mul_le_mul_right T hk
  by_contra hcon
  push Not at hcon
  -- 各位置に最小 `k`-繰り返し周期がある
  have hleast : ∀ a, a < T → ∃ q, IsLeastKRep (v.drop a) k q := by
    intro a ha
    obtain ⟨q, _, hq⟩ := hcon a ha
    exact exists_least_kRep ⟨q, hq⟩
  -- 最小周期はすべて `T` 未満
  have hQlt : ∀ q, (∃ a, a < T ∧ IsLeastKRep (v.drop a) k q) → q < T := by
    rintro q ⟨a, ha, hq⟩
    obtain ⟨q', hq'T, hq'⟩ := hcon a ha
    exact lt_of_le_of_lt (hq.2 q' hq') hq'T
  obtain ⟨q0, hq0⟩ := hleast 0 hT
  set Q : ℕ → Prop := fun q => ∃ a, a < T ∧ IsLeastKRep (v.drop a) k q with hQdef
  have hQ0 : Q q0 := ⟨0, hT, hq0⟩
  set p := Nat.findGreatest Q T with hpdef
  have hQp : Q p := Nat.findGreatest_spec (P := Q) (le_of_lt (hQlt q0 hQ0)) hQ0
  have hmax : ∀ b, b < T → ∀ q, IsLeastKRep (v.drop b) k q → q ≤ p := by
    intro b hb q hq
    exact Nat.le_findGreatest (le_of_lt (hQlt q ⟨b, hb, hq⟩)) ⟨b, hb, hq⟩
  have hpT : p < T := hQlt p hQp
  obtain ⟨A, hA, hstar⟩ := hQp
  have hppos : 0 < p := hstar.1.1
  -- `(k-1) * p < T`
  have hkp : (k - 1) * p < T := by
    have hsub : (k - 1) * p + p = k * p := by
      have h1 := Nat.sub_one_mul k p
      have h2 : p ≤ k * p := Nat.le_mul_of_pos_left p (by omega)
      omega
    have hwin : HasPeriod ((v.drop A).take (min (k * p) (m - A))) p :=
      hasPeriod_take_of_le hstar.1.2.2 (min_le_left _ _)
    have hlt := reach_lt_add_of_periodic_window hT hprim hm (by omega) hperT hppos hpT
      (by omega) hwin
    omega
  have hkplt : k * p < 2 * T := by
    have hsub : (k - 1) * p + p = k * p := by
      have h1 := Nat.sub_one_mul k p
      have h2 : p ≤ k * p := Nat.le_mul_of_pos_left p (by omega)
      omega
    omega
  -- 最大性を `[0, 2T)` に持ち上げる
  have hexAll : ∀ b, b < 2 * T → ∃ q, IsLeastKRep (v.drop b) k q ∧ q ≤ p := by
    intro b hb
    rcases Nat.lt_or_ge b T with hbT | hbT
    · obtain ⟨q, hq⟩ := hleast b hbT
      exact ⟨q, hq, hmax b hbT q hq⟩
    · obtain ⟨q, hq⟩ := hleast (b - T) (by omega)
      have hqp : q ≤ p := hmax _ (by omega) q hq
      have hkq : k * q ≤ k * p := Nat.mul_le_mul_left k hqp
      have hshift : KRep (v.drop b) k q := by
        have hs := krep_shift (b := b - T) (q := q) hperT hm (by omega) hq.1
        rwa [show b - T + T = b from by omega] at hs
      obtain ⟨q', hq'⟩ := exists_least_kRep ⟨q, hshift⟩
      exact ⟨q', hq', le_trans (hq'.2 q hshift) hqp⟩
  -- `p` ずつ削っても最小周期は `p` のまま
  have hstep : ∀ j : ℕ, j * p ≤ T →
      IsLeastKRep (v.drop (A + j * p)) k p ∧
      HasPeriod ((v.drop A).take (j * p + k * p)) p := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨by simpa using hstar, ?_⟩
      simpa using hstar.1.2.2
    | succ j ih =>
      intro hjp
      have hjp' : j * p ≤ T := by
        have : j * p ≤ (j + 1) * p := Nat.mul_le_mul_right p (by omega)
        omega
      obtain ⟨hj, hwin⟩ := ih hjp'
      -- `v.drop (A + (j+1)*p) = (v.drop (A + j*p)).drop p`
      have hd1 : (v.drop (A + j * p)).drop p = v.drop (A + (j + 1) * p) := by
        rw [List.drop_drop]
        exact congrArg (fun t => v.drop t) (by ring)
      obtain ⟨q, hq, hqp⟩ := hexAll (A + (j + 1) * p) (by omega)
      have hge : p ≤ q := by
        refine strip_period_ge hk hj.2 hppos hj.1.2.2 hj.1.2.1 (le_refl _) ?_
        rw [hd1]; exact hq
      have hqeq : q = p := by omega
      subst hqeq
      refine ⟨hq, ?_⟩
      -- 貼り合わせ
      have hd2 : (v.drop A).drop ((j + 1) * p) = v.drop (A + (j + 1) * p) := by
        rw [List.drop_drop]
      have hB : HasPeriod (((v.drop A).drop ((j + 1) * p)).take (k * p)) p := by
        rw [hd2]; exact hq.1.2.2
      have hlen : (j + 1) * p + k * p ≤ (v.drop A).length := by
        have hcc : k * p ≤ v.length - (A + (j + 1) * p) := by
          have := hq.1.2.1; rwa [List.length_drop] at this
        have hcd : (v.drop A).length = v.length - A := List.length_drop
        omega
      have hdp : (j + 1) * p + p ≤ j * p + k * p := by
        have h1 : (j + 1) * p + p = (j + 2) * p := by ring
        have h2 : (j + 2) * p ≤ (j + k) * p := Nat.mul_le_mul_right p (by omega)
        have h3 : (j + k) * p = j * p + k * p := by ring
        omega
      have hAB : j * p + k * p ≤ (j + 1) * p + k * p := by
        have : j * p ≤ (j + 1) * p := Nat.mul_le_mul_right p (by omega)
        omega
      exact hasPeriod_glue hwin hB hdp hAB hlen
  -- 最後の窓
  obtain ⟨j0, hj0le, hj0gt⟩ : ∃ j0, j0 * p ≤ T ∧ T < j0 * p + p := by
    refine ⟨T / p, Nat.div_mul_le_self T p, ?_⟩
    have h1 := Nat.div_add_mod T p
    have h2 : T % p < p := Nat.mod_lt _ hppos
    have h3 : T / p * p = p * (T / p) := Nat.mul_comm _ _
    omega
  obtain ⟨-, hwin⟩ := hstep j0 hj0le
  have hLbig : T + p < j0 * p + k * p := by
    have h4p : 4 * p ≤ k * p := Nat.mul_le_mul_right p hk
    omega
  have hfit : A + (j0 * p + k * p) ≤ m := by omega
  have hlt := reach_lt_add_of_periodic_window hT hprim hm (by omega) hperT hppos hpT hfit hwin
  omega

/-! ## フェーズの合成 -/

/-- 削除ループ全体の再帰。不変量は
`(k-2)*s + T₁ ≤ (k-1)*Tn`（幾何級数）、`(k-1)*Tn + s < |v|`（最後のフェーズの
`k*Tn ≤ |v_n|`）、`Tn ≤ p₁`、そして `T₁` が `v` の最小周期の `(k-1)` 倍以上であること。 -/
private theorem gsDecomp_aux (k : ℕ) (hk : 4 ≤ k) :
    ∀ (n : ℕ) (v : List α), v.length ≤ n →
      ∃ s p₁ r, GSCore v k s p₁ r ∧
        (s = 0 ∨ ∃ T₁ Tn q, IsLeastKRep v k q ∧ (k - 1) * q ≤ T₁ ∧
          (k - 2) * s + T₁ ≤ (k - 1) * Tn ∧ (k - 1) * Tn + s < v.length ∧
          (p₁ ≠ 0 → Tn ≤ p₁)) := by
  intro n
  induction n with
  | zero =>
    intro v hv
    refine ⟨0, 0, 0, gsCore_zero_of_no_krep ?_, Or.inl rfl⟩
    rintro p ⟨hp0, hlen, -⟩
    have : 0 < k * p := Nat.mul_pos (by omega) hp0
    omega
  | succ n ih =>
    intro v hv
    by_cases hex : ∃ p, KRep v k p
    · obtain ⟨p₁, hleast⟩ := exists_least_kRep hex
      obtain ⟨r, hR, hkr⟩ := exists_reach hleast.1
      have hp₁pos : 0 < p₁ := hleast.1.1
      by_cases hns : NoSecond v k r
      · exact ⟨0, p₁, r, gsCore_zero_of_noSecond (by omega) hleast hR hkr hns, Or.inl rfl⟩
      · obtain ⟨p₂, hp₂, hmm, hper₂, hmin₂⟩ := exists_least_second hns
        have hkp₂n : k * p₂ ≤ v.length := le_trans (le_max_left _ _) hmm
        have hkrep₂ : KRep v k p₂ :=
          ⟨hp₂, hkp₂n, hasPeriod_take_of_le hper₂ (le_max_left _ _)⟩
        have hle12 : p₁ ≤ p₂ := hleast.2 _ hkrep₂
        have hne12 : p₁ ≠ p₂ := by
          intro heq
          have hmx : max (k * p₂) (r + 1) = r + 1 := by
            have : k * p₂ = k * p₁ := by rw [heq]
            omega
          rw [hmx] at hper₂
          rcases hR.2.2 with h | h
          · omega
          · exact h (heq ▸ hper₂)
        have hlt12 : p₁ < p₂ := lt_of_le_of_ne hle12 hne12
        have hprim : Primitive (v.take p₂) :=
          least_second_primitive (by omega) hp₂ hmm hper₂ hmin₂
        have hkp : (k - 1) * p₁ ≤ p₂ :=
          kRepetition_periods (by omega) hleast.1 hkrep₂ hprim hlt12
        obtain ⟨a, haT, hstop⟩ := pass_stops_before_second (v := v) (T := p₂)
          (m := max (k * p₂) (r + 1)) hk hp₂ hprim (le_max_left _ _) hmm hper₂
        have hapos : 0 < a := by
          rcases Nat.eq_zero_or_pos a with h0 | h
          · exfalso
            apply hstop p₁ hlt12
            rw [h0, List.drop_zero]
            exact hleast.1
          · exact h
        have hp₂le : p₂ ≤ k * p₂ := Nat.le_mul_of_pos_left p₂ (by omega)
        have hale : a ≤ v.length := by omega
        have hlen' : (v.drop a).length ≤ n := by rw [List.length_drop]; omega
        obtain ⟨s', p₁', r', H', hinv'⟩ := ih (v.drop a) hlen'
        have hnew : ∀ q, IsLeastKRep (v.drop a) k q → p₂ ≤ q := by
          intro q hq
          by_contra hc
          exact hstop q (by omega) hq.1
        have hdroplen : (v.drop a).length = v.length - a := List.length_drop
        have hmul2 : (k - 2) * p₂ + p₂ = (k - 1) * p₂ := by
          rw [← Nat.succ_mul]; congr 1; omega
        have hmul1 : (k - 1) * p₂ + p₂ = k * p₂ := by
          rw [← Nat.succ_mul]; congr 1; omega
        have hma : (k - 2) * a ≤ (k - 2) * p₂ := Nat.mul_le_mul_left (k - 2) (le_of_lt haT)
        refine ⟨a + s', p₁', r', H'.drop_comp hale, Or.inr ?_⟩
        rcases hinv' with h0 | ⟨T₁', Tn', q', hq', hq'T, hsum', hlast', hTn'⟩
        · subst h0
          simp only [Nat.add_zero]
          refine ⟨p₂, p₂, p₁, hleast, hkp, by omega, by omega, ?_⟩
          intro hne
          refine hnew p₁' ?_
          have := H'.least hne
          rwa [List.drop_zero] at this
        · refine ⟨p₂, Tn', p₁, hleast, hkp, ?_, ?_, hTn'⟩
          · have h4 : (k - 1) * p₂ ≤ (k - 1) * q' := Nat.mul_le_mul_left (k - 1) (hnew q' hq')
            have h5 : (k - 2) * (a + s') = (k - 2) * a + (k - 2) * s' := by ring
            omega
          · omega
    · refine ⟨0, 0, 0, gsCore_zero_of_no_krep ?_, Or.inl rfl⟩
      intro p hp
      exact hex ⟨p, hp⟩

/-! ## 主定理 -/

/-- **GS 前処理の存在定理（L1 上界つき、GS Theorem 1）**。任意の `x` と `4 ≤ k` に対し
`GSDecomp x k s p₁ r` を満たす分解が存在する。すなわち `x.drop s` は `k`-simple で、
切断長は `(k-1) * s < |x|` かつ `p₁ ≠ 0 → (k-2) * s < (k-1) * p₁` を満たす。 -/
theorem gsDecomp_exists {k : ℕ} (hk : 4 ≤ k) (x : List α) :
    ∃ s p₁ r, GSDecomp x k s p₁ r := by
  obtain ⟨s, p₁, r, H, hinv⟩ := gsDecomp_aux k hk x.length x (le_refl _)
  rcases hinv with h0 | ⟨T₁, Tn, q, hq, hqT, hsum, hlast, hTn⟩
  · subst h0
    exact ⟨0, p₁, r, gsDecomp_of_core_zero (by omega) H⟩
  · have hqpos : 0 < q := hq.1.1
    have hT₁pos : 0 < T₁ := by
      have : k - 1 ≤ (k - 1) * q := Nat.le_mul_of_pos_right (k - 1) hqpos
      omega
    have hks : (k - 2) * s + s = (k - 1) * s := by
      have h1 : (k - 2) * s + s = (k - 2 + 1) * s := (Nat.succ_mul _ _).symm
      have h2 : k - 2 + 1 = k - 1 := by omega
      rw [h1, h2]
    refine ⟨s, p₁, r, H, ?_, ?_⟩
    · intro _; omega
    · intro hne
      have : (k - 1) * Tn ≤ (k - 1) * p₁ := Nat.mul_le_mul_left (k - 1) (hTn hne)
      omega

/-- `GSDecomp` の 2 つの上界を明示した形（`BorderJob` / `GSVerifier` が消費する形）。 -/
theorem gsDecomp_exists' {k : ℕ} (hk : 4 ≤ k) (x : List α) :
    ∃ s p₁ r, GSCore x k s p₁ r ∧ (x ≠ [] → (k - 1) * s < x.length) ∧
      (p₁ ≠ 0 → (k - 2) * s < (k - 1) * p₁) := by
  obtain ⟨s, p₁, r, H⟩ := gsDecomp_exists hk x
  exact ⟨s, p₁, r, H.toGSCore, H.cut_bound, H.cut_period_bound⟩

/-! ## 消費側への橋渡し -/

/-- **`GSVerifier.vAnswer_correct` が要求する形**。`u = x.take s`, `v = x.drop s` として
`KSimple v k p₁ r` と L1 の 2 つの不等式をそのまま供給する。 -/
theorem gsDecomp_verifier_data {k : ℕ} (hk : 4 ≤ k) (x : List α) (hx : x ≠ []) :
    ∃ s p₁ r, 0 < p₁ ∧ KSimple (x.drop s) k p₁ r ∧
      (k - 1) * (x.take s).length < (x.take s).length + (x.drop s).length ∧
      (k - 2) * (x.take s).length < (k - 1) * p₁ := by
  obtain ⟨s, p₁, r, H⟩ := gsDecomp_exists hk x
  have hcut := H.cut_le
  have hts : (x.take s).length = s := by simp only [List.length_take]; omega
  have hds : (x.drop s).length = x.length - s := List.length_drop
  have hshort := H.cut_bound hx
  have hsle : s ≤ (k - 1) * s := Nat.le_mul_of_pos_left s (by omega)
  by_cases hp : p₁ = 0
  · refine ⟨s, (x.drop s).length + 1, 0, by omega, H.toGSCore.ksimple_none hp, ?_, ?_⟩
    · rw [hts, hds]; omega
    · rw [hts, hds]
      have h1 : x.length - s + 1 ≤ (k - 1) * (x.length - s + 1) :=
        Nat.le_mul_of_pos_left _ (by omega)
      have h2 : (k - 2) * s + s = (k - 1) * s := by
        rw [← Nat.succ_mul]; congr 1; omega
      omega
  · refine ⟨s, p₁, r, Nat.pos_of_ne_zero hp, H.ksimple hp, ?_, ?_⟩
    · rw [hts, hds]; omega
    · rw [hts]; exact H.cut_period_bound hp

/-- **`BorderJob.StageOK` が要求する形**。各段 `L` について `StageOK x k L s p₁ r` を満たす
分解が存在する。 -/
theorem stageOK_exists {k : ℕ} (hk : 4 ≤ k) (x : List α) {L : ℕ} (hL : 1 ≤ L)
    (hLx : L ≤ x.length) : ∃ s p₁ r, StageOK x k L s p₁ r := by
  obtain ⟨s, p₁, r, H⟩ := gsDecomp_exists hk (x.take L)
  have hxL : (x.take L).length = L := by simp only [List.length_take]; omega
  have hne : x.take L ≠ [] := by
    intro h
    rw [h] at hxL
    simp at hxL
    omega
  have hcut := H.cut_le
  rw [hxL] at hcut
  have hshort : (k - 1) * s < L := by
    have := H.cut_bound hne; omega
  have hds : ((x.take L).drop s).length = L - s := by rw [List.length_drop, hxL]
  by_cases hp : p₁ = 0
  · refine ⟨s, ((x.take L).drop s).length + 1, 0, hcut, H.toGSCore.ksimple_none hp, ?_, hshort⟩
    have h1 : 2 * s ≤ (k - 1) * s := Nat.mul_le_mul_right s (by omega)
    have h2 : 4 * (((x.take L).drop s).length + 1) ≤ k * (((x.take L).drop s).length + 1) :=
      Nat.mul_le_mul_right _ hk
    omega
  · exact ⟨s, p₁, r, hcut, H.ksimple hp, cut_charge_of_ratio hk (H.cut_period_bound hp), hshort⟩


end PalPeg
