import PalPeg.GalilShortPeriod
import PalPeg.GalilPeriodUnion

/-!
# 連鎖 1 巡分の「最小周期の引き継ぎ」

Galil 型実時間回文照合の chain round をまたぐ純粋な語の組合せ論。

* `periodOn_restrict` — 局所周期は部分区間へ制限できる。
* `periodOn_mul` — 局所周期 `P` は区間内で `m * P` へ反復できる。
* `periodOn_extend_prefix` / `periodOn_extend_suffix` — `P`-周期区間の
  左端（右端）にある長さ `P` の窓が周期 `d ∣ P` を持てば、区間全体が `d`-周期。
* `periodOn_extend_dvd` — 上記 2 本の合成。`P`-周期区間の内部に長さ `≥ P` の
  `d`-周期窓（`d ∣ P`）があれば、区間全体が `d`-周期。
* `periodOn_fineWilf` — Fine–Wilf の局所版。
* `noBelow_next` — 中心を `h` だけ動かした新しい区間でも「`2h` 未満の周期は無い」
  が保たれる（chain round の最小性の引き継ぎ）。
-/

set_option autoImplicit false
namespace PalPeg
open Manacher

variable {α : Type}

/-! ## 制限と反復 -/

/-- 局所周期は部分区間へ制限できる。 -/
theorem periodOn_restrict {x : List α} {p a b a' b' : ℕ} (h : PeriodOn x p a b) (ha : a ≤ a')
    (hb : b' ≤ b) : PeriodOn x p a' b' :=
  h.mono ha hb

/-- 区間上の周期 `P` は、区間内に収まる限り `m * P` ずらしても値が一致する。 -/
theorem periodOn_mul {x : List α} {P a b : ℕ} (h : PeriodOn x P a b) :
    ∀ m i, a ≤ i → i + m * P ≤ b → x[i]? = x[i + m * P]? := by
  intro m
  induction m with
  | zero => intro i _ _; simp
  | succ m ih =>
    intro i hi hib
    have hstep : i + P ≤ b := by
      have : P ≤ (m + 1) * P := by
        have := Nat.le_mul_of_pos_left P (show 0 < m + 1 by omega)
        omega
      omega
    have h1 : x[i]? = x[i + P]? := h i hi hstep
    have h2 : x[i + P]? = x[i + P + m * P]? := by
      refine ih (i + P) (by omega) ?_
      have e : i + P + m * P = i + (m + 1) * P := by ring
      omega
    have e : i + P + m * P = i + (m + 1) * P := by ring
    rw [h1, h2, e]

/-! ## 約数周期の伝播 -/

/-- 区間 `[a, b]` が周期 `P` を持ち、その左端の長さ `P` の窓 `[a, a+P-1]` が
周期 `d ∣ P` を持つなら、区間全体が周期 `d` を持つ。 -/
theorem periodOn_extend_prefix {x : List α} {P d a b : ℕ} (hP : PeriodOn x P a b)
    (hd : PeriodOn x d a (a + P - 1)) (hP0 : 0 < P) (hdP : d ∣ P)
    (hab : a + P ≤ b + 1) (hb : b < x.length) : PeriodOn x d a b := by
  have hab' : a ≤ b := by omega
  have hy : HasPeriod ((x.drop a).take (b + 1 - a)) P :=
    (hasPeriod_slice_iff hb hab').mpr hP
  have hpre : HasPeriod (((x.drop a).take (b + 1 - a)).take P) d := by
    rw [List.take_take, show min P (b + 1 - a) = P from Nat.min_eq_left (by omega)]
    have hwin : HasPeriod ((x.drop a).take (a + P - 1 + 1 - a)) d :=
      (hasPeriod_slice_iff (b := a + P - 1) (by omega) (by omega)).mpr hd
    rwa [show a + P - 1 + 1 - a = P from by omega] at hwin
  exact (hasPeriod_slice_iff hb hab').mp (hasPeriod_of_prefix_dvd hy hP0 hdP hpre)

/-- 区間 `[a, b]` が周期 `P` を持ち、その右端の長さ `P` の窓 `[b+1-P, b]` が
周期 `d ∣ P` を持つなら、区間全体が周期 `d` を持つ。 -/
theorem periodOn_extend_suffix {x : List α} {P d a b : ℕ} (hP : PeriodOn x P a b)
    (hd : PeriodOn x d (b + 1 - P) b) (hP0 : 0 < P) (hdP : d ∣ P)
    (hab : a + P ≤ b + 1) (hb : b < x.length) : PeriodOn x d a b := by
  have hab' : a ≤ b := by omega
  have hy : HasPeriod ((x.drop a).take (b + 1 - a)) P :=
    (hasPeriod_slice_iff hb hab').mpr hP
  have hylen : ((x.drop a).take (b + 1 - a)).length = b + 1 - a := by
    rw [List.length_take, List.length_drop]
    omega
  have hsuf : HasPeriod
      (((x.drop a).take (b + 1 - a)).drop
        (((x.drop a).take (b + 1 - a)).length - P)) d := by
    rw [hylen, drop_take_drop (show b + 1 - a - P ≤ b + 1 - a from by omega),
      show a + (b + 1 - a - P) = b + 1 - P from by omega,
      show b + 1 - a - (b + 1 - a - P) = P from by omega]
    have hwin : HasPeriod ((x.drop (b + 1 - P)).take (b + 1 - (b + 1 - P))) d :=
      (hasPeriod_slice_iff (a := b + 1 - P) hb (by omega)).mpr hd
    rwa [show b + 1 - (b + 1 - P) = P from by omega] at hwin
  have hpn : P ≤ ((x.drop a).take (b + 1 - a)).length := by rw [hylen]; omega
  exact (hasPeriod_slice_iff hb hab').mp
    (hasPeriod_of_suffix_gcd hy hP0 hdP hsuf hpn)

/-- **約数周期の伝播**。`P`-周期的な区間 `[a, b]` の内部に、長さ `≥ P` の窓
`[a', b']` があり、そこで周期 `d ∣ P` が成り立つなら、`[a, b]` 全体が周期 `d`
を持つ。

窓を右端まで伸ばし（`periodOn_extend_prefix`）、続いて左端まで伸ばす
（`periodOn_extend_suffix`）ことで得られる。 -/
theorem periodOn_extend_dvd {x : List α} {P d a b a' b' : ℕ} (hP : PeriodOn x P a b)
    (hd : PeriodOn x d a' b') (hdP : d ∣ P) (hd0 : 0 < d) (hP0 : 0 < P)
    (hb : b < x.length) (hsub : a ≤ a' ∧ b' ≤ b) (hwin : a' + P ≤ b' + 1) :
    PeriodOn x d a b := by
  have _hd0 := hd0
  obtain ⟨ha, hbb⟩ := hsub
  -- 窓を右端 `b` まで伸ばす。
  have hR : PeriodOn x d a' b :=
    periodOn_extend_prefix (hP.mono ha (le_refl b)) (hd.mono (le_refl a') (by omega)) hP0 hdP
      (by omega) hb
  -- 右端の長さ `P` の窓を取り直して、左端 `a` まで伸ばす。
  exact periodOn_extend_suffix hP (hR.mono (by omega) (le_refl b)) hP0 hdP (by omega) hb

/-! ## Fine–Wilf の局所版 -/

/-- **Fine–Wilf（局所版）**。区間 `[a, b]` が周期 `p` と `q` を共に持ち、区間長
`b + 1 - a` が `p + q - gcd p q` 以上なら、`gcd p q` も同区間の周期。 -/
theorem periodOn_fineWilf {x : List α} {p q a b : ℕ} (hp : PeriodOn x p a b)
    (hq : PeriodOn x q a b) (hp0 : 0 < p) (hq0 : 0 < q) (hb : b < x.length) (hab : a ≤ b)
    (hlen : p + q - Nat.gcd p q ≤ b + 1 - a) : PeriodOn x (Nat.gcd p q) a b := by
  have hyp : HasPeriod ((x.drop a).take (b + 1 - a)) p := (hasPeriod_slice_iff hb hab).mpr hp
  have hyq : HasPeriod ((x.drop a).take (b + 1 - a)) q := (hasPeriod_slice_iff hb hab).mpr hq
  have hylen : ((x.drop a).take (b + 1 - a)).length = b + 1 - a := by
    rw [List.length_take, List.length_drop]
    omega
  refine (hasPeriod_slice_iff hb hab).mp (fineWilf hyp hyq hp0 hq0 ?_)
  rw [hylen]
  exact hlen

/-! ## chain round をまたぐ最小性の引き継ぎ -/

/-- **最小性の引き継ぎ**。旧区間 `[C-k, C+k]`（半径 `k ≥ 2h`）が周期 `2h` を持ち
`2h` 未満の周期を持たず、新区間 `[C+h-k', C+h+k']`（中心が `h` 移動、半径
`k' ≥ 2h` かつ `k + 1 ≤ k' + h`）も周期 `2h` を持つなら、新区間も `2h` 未満の
周期を持たない。

証明：新区間に周期 `p < 2h` があると仮定する。新区間は長さ `2k' + 1 ≥ 4h + 1`
なので Fine–Wilf（局所版）が使え、`g = gcd p (2h) ≤ p < 2h` も新区間の周期に
なる。旧区間を `2h` ずらした窓 `W = [C-k+2h, C+k]` は新区間にも旧区間にも含まれ、
長さ `2k - 2h + 1 ≥ 2h` を持つ。よって `W` 上の周期 `g` は `periodOn_extend_dvd`
により旧区間全体へ伝播し、`hmin0` に矛盾する。 -/
theorem noBelow_next {x : List α} {C k k' h : ℕ} (hh : 0 < h) (hk : 2 * h ≤ k)
    (hk' : 2 * h ≤ k') (hkk : k + 1 ≤ k' + h) (hkC : k ≤ C) (hkC' : k' ≤ C + h)
    (hb : C + h + k' < x.length)
    (hper0 : PeriodOn x (2 * h) (C - k) (C + k))
    (hmin0 : ∀ p, 0 < p → p < 2 * h → ¬ PeriodOn x p (C - k) (C + k))
    (hper1 : PeriodOn x (2 * h) (C + h - k') (C + h + k')) :
    ∀ p, 0 < p → p < 2 * h → ¬ PeriodOn x p (C + h - k') (C + h + k') := by
  intro p hp0 hp2h hp1
  -- `g = gcd p (2h)` についての基本事実（`omega` には不透明な定数として渡す）。
  obtain ⟨g, hg⟩ : ∃ g, g = Nat.gcd p (2 * h) := ⟨Nat.gcd p (2 * h), rfl⟩
  have hg0 : 0 < g := by rw [hg]; exact Nat.gcd_pos_of_pos_left _ hp0
  have hgle : g ≤ p := by rw [hg]; exact Nat.gcd_le_left _ hp0
  have hgdvd : g ∣ 2 * h := by rw [hg]; exact Nat.gcd_dvd_right p (2 * h)
  -- 新区間の端点と長さ。
  have hab1 : C + h - k' ≤ C + h + k' := by omega
  have hlen1 : p + 2 * h - Nat.gcd p (2 * h) ≤ C + h + k' + 1 - (C + h - k') := by
    rw [← hg]; omega
  -- Fine–Wilf（局所版）で新区間に周期 `g` を出す。
  have hgS1 : PeriodOn x g (C + h - k') (C + h + k') := by
    rw [hg]
    exact periodOn_fineWilf hp1 hper1 hp0 (by omega) hb hab1 hlen1
  -- 窓 `W = [C-k+2h, C+k]` は新区間に含まれるので周期 `g` を持つ。
  have hgW : PeriodOn x g (C - k + 2 * h) (C + k) :=
    hgS1.mono (by omega) (by omega)
  -- `W` の長さは `≥ 2h` なので、旧区間全体へ `g` が伝播する。
  have hbOld : C + k < x.length := by omega
  have hgS0 : PeriodOn x g (C - k) (C + k) :=
    periodOn_extend_dvd hper0 hgW hgdvd hg0 (by omega) hbOld
      ⟨by omega, le_refl (C + k)⟩ (by omega)
  exact hmin0 g hg0 (by omega) hgS0

#print axioms periodOn_restrict
#print axioms periodOn_mul
#print axioms periodOn_extend_prefix
#print axioms periodOn_extend_suffix
#print axioms periodOn_extend_dvd
#print axioms periodOn_fineWilf
#print axioms noBelow_next

end PalPeg
