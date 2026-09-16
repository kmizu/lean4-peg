import PalPeg.Words
import PalPeg.GSScan

/-!
# Galil–Seiferas の前処理（分解側）

Galil and Seiferas, *Time-Space-Optimal String Matching*, JCSS 26 (1983), pp. 280–294
の前処理を形式化する。走査側は `PalPeg.GSScan`（`KSimple` を仮定して走る）にあり、
本ファイルはその仮定 `KSimple` を「分解の出力」から供給する側を扱う。

## `docs/palindromes-in-peg/gs_events.py` の `decomposition(size, k)` が返すもの

`decomposition` は `Decomposition(cut, period, reach)` を返す。`x` を長さ `size` の
パターン、`s = cut`、`v = x.drop s` とすると、その意味は次のとおり：

* `_first(start, size-start, k)` は「`v` の長さ `k*p` の接頭辞が周期 `p` を持つような
  最小の `p ≥ 1`」を探す（内側ループは `q < (k-1)*p` の間 `v[q] = v[p+q]` を比較し、
  `q = (k-1)*p` に達したら `(p, p+q) = (p, k*p)` を返す）。
  見つからなければ `Decomposition(s, None, 0)`：`v` は `k` 回繰り返される接頭辞を持たない。
* 見つかったら `reach` を最大まで伸ばす：`r` は `v.take r` が周期 `p₁` を持つ最大の値。
* `_second` は「`p₂ ≥ 1` と `q ≥ (k-1)*p₂` で `p₂ + q > r` かつ `v.take (p₂+q)` が
  周期 `p₂` を持つ」ものを探す。これは
  `m = max (k*p₂) (r+1)` に対し `m ≤ |v|` かつ `HasPeriod (v.take m) p₂` と同値
  （内側ループは `q` を 1 ずつ伸ばすので、条件が最初に成立する `q` で返る）。
  見つからなければ `Decomposition(s, p₁, r)`。
* 見つかったら `start` を進めて（`bound = second` 付きの `_first` が返す周期ぶんずつ）
  外側ループをやり直す。

したがって出力 `(s, p₁, r)` の意味は `GSCore` である（`p₁ = 0` を `None` の符号化とする）。
`GS_OVERLAP.md` の L1 の 2 つの上界

* `s < |x| / (k-1)`  すなわち `(k-1) * s < |x|`
* `s < (k-1)/(k-2) * p₁` すなわち `(k-2) * s < (k-1) * p₁`

を加えたものが `GSDecomp`。

## 本ファイルで証明したこと / していないこと

証明済み：
* 語の冪 `wpow` と原始性 `Primitive`、周期からの冪分解 `eq_wpow_of_hasPeriod`。
* GS の重なり補題 `kRepetition_periods`（Fine–Wilf 経由）と `reach_lt_add_of_second`。
* 最短 `k`-繰り返し周期は原始的（`IsLeastKRep.primitive`）。
* 走査側が必要とする周期の帰結（`GSCore.krep_bound` とその 3 系）、および
  `GSScan.KSimple` への橋渡し `GSCore.ksimple` / `GSCore.ksimple_none`。
* `GSCore` の存在（`gsCore_exists`）と最小の切断位置の存在（`gsCore_exists_least`）。

**未証明（意図的に述べていない）**：`GSDecomp` の存在、すなわち L1 の 2 つの上界つきの
GS Theorem 1。これは `_first`/`_second`/削除ループの償却解析（第 2 周期が反復ごとに
定数倍で増える、1 回の外側反復での削除量が第 2 周期未満、など）を要し、本ファイルの
範囲を超える。ここでは解析の中核部品（`kRepetition_periods`, `reach_lt_add_of_second`,
`strip_kills_period`）までを与える。
-/

namespace PalPeg

universe u
variable {α : Type u}

/-! ## 語の冪と原始性 -/

/-- 語の冪 `z^n`。 -/
def wpow (z : List α) : ℕ → List α
  | 0 => []
  | n + 1 => z ++ wpow z n

@[simp] theorem wpow_zero (z : List α) : wpow z 0 = [] := rfl

@[simp] theorem wpow_succ (z : List α) (n : ℕ) : wpow z (n + 1) = z ++ wpow z n := rfl

/-- `List.replicate`/`List.flatten` による定義との一致。 -/
theorem wpow_eq_flatten (z : List α) (n : ℕ) : wpow z n = (List.replicate n z).flatten := by
  induction n with
  | zero => simp
  | succ n ih => rw [wpow_succ, ih, List.replicate_succ, List.flatten_cons]

@[simp] theorem length_wpow (z : List α) (n : ℕ) : (wpow z n).length = n * z.length := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih, Nat.succ_mul, Nat.add_comm]

theorem getElem?_wpow {z : List α} {n i : ℕ} (_hz : 0 < z.length) (hi : i < n * z.length) :
    (wpow z n)[i]? = z[i % z.length]? := by
  induction n generalizing i with
  | zero => simp at hi
  | succ n ih =>
    rw [wpow_succ]
    by_cases h : i < z.length
    · rw [List.getElem?_append_left h, Nat.mod_eq_of_lt h]
    · have h : z.length ≤ i := Nat.le_of_not_lt h
      have hi' : i - z.length < n * z.length := by rw [Nat.succ_mul] at hi; omega
      rw [List.getElem?_append_right h, ih hi', ← Nat.mod_eq_sub_mod h]

theorem hasPeriod_wpow (z : List α) (n : ℕ) : HasPeriod (wpow z n) z.length := by
  rcases Nat.eq_zero_or_pos z.length with h | h
  · rw [h]; exact hasPeriod_zero _
  · intro i hi
    rw [length_wpow] at hi
    rw [getElem?_wpow h (by omega), getElem?_wpow h (by omega), Nat.add_mod_right]

/-- 原始語（GS の "basic word"）：真の冪でない。空語は原始的でない。 -/
def Primitive (y : List α) : Prop := ∀ (z : List α) (n : ℕ), y = wpow z n → n = 1

theorem primitive_iff_not_proper_power {y : List α} :
    Primitive y ↔ ∀ (z : List α) (n : ℕ), y = wpow z n → n = 1 := Iff.rfl

/-- 周期 `g`（`g ∣ |w|`）を持つ語は `(w.take g)^(|w|/g)` に分解される。 -/
theorem eq_wpow_of_hasPeriod {w : List α} {g : ℕ} (hg : 0 < g) (hgl : g ≤ w.length)
    (hdvd : g ∣ w.length) (hp : HasPeriod w g) :
    w = wpow (w.take g) (w.length / g) := by
  have hzlen : (w.take g).length = g := by simp only [List.length_take]; omega
  have hmul : w.length / g * g = w.length := Nat.div_mul_cancel hdvd
  apply List.ext_getElem?
  intro i
  by_cases hi : i < w.length
  · have h1 : w[i]? = w[i % g]? := (hasPeriod_getElem?_mod hp hi).symm
    have h2 : (wpow (w.take g) (w.length / g))[i]? = (w.take g)[i % (w.take g).length]? := by
      refine getElem?_wpow (by omega) ?_
      rw [hzlen, hmul]; exact hi
    rw [h1, h2, hzlen, List.getElem?_take_of_lt (Nat.mod_lt _ hg)]
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none]
    rw [length_wpow, hzlen, hmul]
    omega

/-- 真の周期（長さを割り、長さ未満）を持つ語は原始的でない。 -/
theorem not_primitive_of_period {w : List α} {g : ℕ} (hg : 0 < g) (hgl : g < w.length)
    (hdvd : g ∣ w.length) (hp : HasPeriod w g) : ¬ Primitive w := by
  intro hprim
  have hn := hprim _ _ (eq_wpow_of_hasPeriod hg (le_of_lt hgl) hdvd hp)
  have hmul : w.length / g * g = w.length := Nat.div_mul_cancel hdvd
  rw [hn, Nat.one_mul] at hmul
  omega

/-! ## `k`-繰り返し接頭辞 -/

/-- `v` の長さ `k*p` の接頭辞が周期 `p` を持つ（GS の "basic prefix repeated `k` times"
の候補：原始性はここでは要求しない）。 -/
def KRep (v : List α) (k p : ℕ) : Prop :=
  0 < p ∧ k * p ≤ v.length ∧ HasPeriod (v.take (k * p)) p

/-- `p` が `v` の最小の `k`-繰り返し周期（`_first` が返すもの）。 -/
def IsLeastKRep (v : List α) (k p : ℕ) : Prop :=
  KRep v k p ∧ ∀ q, KRep v k q → p ≤ q

/-- `r` は周期 `p` の到達域（`reach`）：`v.take r` は周期 `p` を持ち、それ以上伸びない。 -/
def ReachOf (v : List α) (p r : ℕ) : Prop :=
  r ≤ v.length ∧ HasPeriod (v.take r) p ∧ (r = v.length ∨ ¬ HasPeriod (v.take (r + 1)) p)

/-- `_second` が失敗すること：到達域 `r` を越える `k`-繰り返し接頭辞は存在しない。 -/
def NoSecond (v : List α) (k r : ℕ) : Prop :=
  ∀ p, 0 < p → max (k * p) (r + 1) ≤ v.length →
    ¬ HasPeriod (v.take (max (k * p) (r + 1))) p

/-- 周期は接頭辞に遺伝する（長さ指定版）。 -/
theorem hasPeriod_take_of_le {v : List α} {p q q' : ℕ} (h : HasPeriod (v.take q) p)
    (hq : q' ≤ q) : HasPeriod (v.take q') p := by
  intro i hi
  rw [List.length_take] at hi
  have hlen' : (v.take q).length = min q v.length := by simp
  have h2 := h i (by rw [hlen']; omega)
  rw [List.getElem?_take_of_lt (show i < q by omega),
    List.getElem?_take_of_lt (show i + p < q by omega)] at h2
  rw [List.getElem?_take_of_lt (show i < q' by omega),
    List.getElem?_take_of_lt (show i + p < q' by omega)]
  exact h2

/-! ## GS の重なり補題 -/

/-- **GS の重なり補題**。`v` が二つの `k`-繰り返し接頭辞 `p₁ < p₂` を持ち、
長い方の根 `v.take p₂` が原始的（basic）なら `(k-1) * p₁ ≤ p₂`。 -/
theorem kRepetition_periods {v : List α} {k p₁ p₂ : ℕ} (hk : 2 ≤ k)
    (h1 : KRep v k p₁) (h2 : KRep v k p₂) (hb : Primitive (v.take p₂))
    (hlt : p₁ < p₂) : (k - 1) * p₁ ≤ p₂ := by
  by_contra hcon0
  have hcon : p₂ < (k - 1) * p₁ := Nat.lt_of_not_le hcon0
  obtain ⟨hp₁, hlen₁, hper₁⟩ := h1
  obtain ⟨hp₂, hlen₂, hper₂⟩ := h2
  have hmul1 : (k - 1) * p₁ = k * p₁ - p₁ := Nat.sub_one_mul k p₁
  have hp₁le : p₁ ≤ k * p₁ := Nat.le_mul_of_pos_left p₁ (by omega)
  have hsub : k * p₁ ≤ k * p₂ := Nat.mul_le_mul_left k (le_of_lt hlt)
  have hboth : HasPeriod (v.take (k * p₁)) p₂ := hasPeriod_take_of_le hper₂ hsub
  have hwlen : (v.take (k * p₁)).length = k * p₁ := by
    simp only [List.length_take]; omega
  have hsum : p₁ + p₂ - Nat.gcd p₁ p₂ ≤ (v.take (k * p₁)).length := by
    rw [hwlen]; omega
  have hg := fineWilf hper₁ hboth hp₁ hp₂ hsum
  have hgle : Nat.gcd p₁ p₂ ≤ p₁ := Nat.gcd_le_left _ hp₁
  have hgpos : 0 < Nat.gcd p₁ p₂ := Nat.gcd_pos_of_pos_left _ hp₁
  have hp₂le : p₂ ≤ k * p₁ := by omega
  have hroot : HasPeriod (v.take p₂) (Nat.gcd p₁ p₂) := hasPeriod_take_of_le hg hp₂le
  have hrootlen : (v.take p₂).length = p₂ := by simp only [List.length_take]; omega
  have hdvd : Nat.gcd p₁ p₂ ∣ (v.take p₂).length := by
    rw [hrootlen]; exact Nat.gcd_dvd_right p₁ p₂
  exact not_primitive_of_period hgpos (by omega) hdvd hroot hb

/-- 第 2 周期が存在するとき、第 1 周期の到達域は `p₁ + p₂` 未満
（`GS_LOCAL_CLOCK.md` の `reach <= p2 + p1`）。 -/
theorem reach_lt_add_of_second {v : List α} {k p₁ p₂ r : ℕ} (hk : 2 ≤ k)
    (hper₁ : HasPeriod (v.take r) p₁) (hr : r ≤ v.length) (hp₁ : 0 < p₁)
    (h2 : KRep v k p₂) (hb : Primitive (v.take p₂)) (hlt : p₁ < p₂) :
    r < p₁ + p₂ := by
  by_contra hcon0
  have hcon : p₁ + p₂ ≤ r := Nat.le_of_not_lt hcon0
  obtain ⟨hp₂, hlen₂, hper₂⟩ := h2
  set m := min r (k * p₂) with hm
  have hkp₂ : p₁ + p₂ ≤ k * p₂ := by
    have h2p : 2 * p₂ ≤ k * p₂ := Nat.mul_le_mul_right p₂ (by omega)
    omega
  have hmge : p₁ + p₂ ≤ m := by omega
  have hmle : m ≤ v.length := by omega
  have ha : HasPeriod (v.take m) p₁ := hasPeriod_take_of_le hper₁ (by omega)
  have hbp : HasPeriod (v.take m) p₂ := hasPeriod_take_of_le hper₂ (by omega)
  have hwlen : (v.take m).length = m := by simp only [List.length_take]; omega
  have hg := fineWilf ha hbp hp₁ hp₂ (by rw [hwlen]; omega)
  have hgle : Nat.gcd p₁ p₂ ≤ p₁ := Nat.gcd_le_left _ hp₁
  have hgpos : 0 < Nat.gcd p₁ p₂ := Nat.gcd_pos_of_pos_left _ hp₁
  have hroot : HasPeriod (v.take p₂) (Nat.gcd p₁ p₂) := hasPeriod_take_of_le hg (by omega)
  have hrootlen : (v.take p₂).length = p₂ := by simp only [List.length_take]; omega
  have hdvd : Nat.gcd p₁ p₂ ∣ (v.take p₂).length := by
    rw [hrootlen]; exact Nat.gcd_dvd_right p₁ p₂
  exact not_primitive_of_period hgpos (by omega) hdvd hroot hb

/-- 最小の `k`-繰り返し周期の根は原始的（GS の "basic"）。 -/
theorem IsLeastKRep.primitive {v : List α} {k p : ℕ} (hk : 0 < k)
    (h : IsLeastKRep v k p) : Primitive (v.take p) := by
  obtain ⟨⟨hp, hlen, hper⟩, hmin⟩ := h
  have hple : p ≤ v.length := le_trans (Nat.le_mul_of_pos_left p hk) hlen
  have htlen : (v.take p).length = p := by simp only [List.length_take]; omega
  intro z n hzn
  by_contra hn
  have hzl : n * z.length = p := by
    have := congrArg List.length hzn
    rw [htlen, length_wpow] at this
    omega
  have hn0 : n ≠ 0 := by rintro rfl; rw [Nat.zero_mul] at hzl; omega
  have hn2 : 2 ≤ n := by omega
  have hzpos : 0 < z.length := by
    rcases Nat.eq_zero_or_pos z.length with h | h
    · rw [h, Nat.mul_zero] at hzl; omega
    · exact h
  have hzlt : z.length < p := by
    have : 2 * z.length ≤ n * z.length := Nat.mul_le_mul_right _ hn2
    omega
  -- `v.take p` は周期 `z.length` を持つ
  have hpre : HasPeriod (v.take p) z.length := by
    rw [hzn]; exact hasPeriod_wpow z n
  have hdvd : z.length ∣ p := ⟨n, by rw [← hzl]; exact Nat.mul_comm n z.length⟩
  have htt : (v.take (k * p)).take p = v.take p := by
    have : p ≤ k * p := Nat.le_mul_of_pos_left p hk
    rw [List.take_take]
    congr 1
    omega
  have hall : HasPeriod (v.take (k * p)) z.length :=
    hasPeriod_of_prefix_dvd hper hp hdvd (by rw [htt]; exact hpre)
  have hkz : k * z.length ≤ k * p := Nat.mul_le_mul_left k (le_of_lt hzlt)
  have hkrep : KRep v k z.length :=
    ⟨hzpos, by omega, hasPeriod_take_of_le hall hkz⟩
  have := hmin _ hkrep
  omega

/-! ## 分解の出力 -/

/-- **`gs_events.py` の `decomposition(|x|, k)` が返す `(s, p₁, r)` の意味**
（`p₁ = 0` が Python の `period = None` の符号化、そのとき `r = 0`）。 -/
structure GSCore (x : List α) (k s p₁ r : ℕ) : Prop where
  /-- `s` は `x` の接頭辞の長さ。 -/
  cut_le : s ≤ x.length
  /-- `period = None` の場合：`k`-繰り返し接頭辞が存在しない。 -/
  none_case : p₁ = 0 → r = 0 ∧ ∀ p, ¬ KRep (x.drop s) k p
  /-- `p₁` は `_first` の返す最小の `k`-繰り返し周期。 -/
  least : p₁ ≠ 0 → IsLeastKRep (x.drop s) k p₁
  /-- `r` は `p₁` の到達域（`reach`）。 -/
  reach : p₁ ≠ 0 → ReachOf (x.drop s) p₁ r
  /-- 到達域は少なくとも `k*p₁`（`_first` は `(p, k*p)` を返し、そこから伸ばす）。 -/
  reach_ge : p₁ ≠ 0 → k * p₁ ≤ r
  /-- `_second` の失敗：到達域を越える第 2 の `k`-繰り返し接頭辞はない。 -/
  simple : p₁ ≠ 0 → NoSecond (x.drop s) k r

/-- `GSCore` に `GS_OVERLAP.md` の L1 上界を加えたもの。 -/
structure GSDecomp (x : List α) (k s p₁ r : ℕ) : Prop extends GSCore x k s p₁ r where
  /-- `s < |x| / (k-1)`。 -/
  cut_bound : x ≠ [] → (k - 1) * s < x.length
  /-- `s < (k-1)/(k-2) * p₁`。 -/
  cut_period_bound : p₁ ≠ 0 → (k - 2) * s < (k - 1) * p₁

/-! ## 走査側が使う帰結 -/

/-- **主補題**。`v = x.drop s` の接頭辞 `v.take q` が `k` 回以上繰り返される周期 `p`
（`k * p ≤ q`）を持つなら、`p₁ ≠ 0` かつ `p₁ ≤ p` かつ `q ≤ r`。 -/
theorem GSCore.krep_bound {x : List α} {k s p₁ r : ℕ} (H : GSCore x k s p₁ r)
    {q p : ℕ} (hq : q ≤ (x.drop s).length) (hp : 0 < p) (hkp : k * p ≤ q)
    (hper : HasPeriod ((x.drop s).take q) p) :
    p₁ ≠ 0 ∧ p₁ ≤ p ∧ q ≤ r := by
  have hKrep : KRep (x.drop s) k p := ⟨hp, le_trans hkp hq, hasPeriod_take_of_le hper hkp⟩
  have hp₁ : p₁ ≠ 0 := fun h0 => (H.none_case h0).2 p hKrep
  refine ⟨hp₁, (H.least hp₁).2 p hKrep, ?_⟩
  by_contra hqr0
  have hqr : r < q := Nat.lt_of_not_le hqr0
  have hmax : max (k * p) (r + 1) ≤ q := by omega
  exact H.simple hp₁ p hp (le_trans hmax hq) (hasPeriod_take_of_le hper hmax)

/-- (i) `k * p₁ ≤ q` なら `v.take q` は `p₁` 未満の正の周期を持たない。 -/
theorem GSCore.no_shorter_period {x : List α} {k s p₁ r : ℕ} (H : GSCore x k s p₁ r)
    {q p : ℕ} (hq : q ≤ (x.drop s).length) (hkq : k * p₁ ≤ q) (hp : 0 < p)
    (hlt : p < p₁) : ¬ HasPeriod ((x.drop s).take q) p := by
  intro hper
  have hkp : k * p ≤ q := le_trans (Nat.mul_le_mul_left k (by omega)) hkq
  have := H.krep_bound hq hp hkp hper
  omega

/-- (ii) `q < k * p₁` なら `v.take q` は `q / k` 以下の正の周期を持たない
（`k * p ≤ q` なる `p` を持たない）。 -/
theorem GSCore.no_period_below {x : List α} {k s p₁ r : ℕ} (H : GSCore x k s p₁ r)
    {q p : ℕ} (hq : q ≤ (x.drop s).length) (hqk : q < k * p₁) (hp : 0 < p)
    (hkp : k * p ≤ q) : ¬ HasPeriod ((x.drop s).take q) p := by
  intro hper
  obtain ⟨-, hle, -⟩ := H.krep_bound hq hp hkp hper
  have : k * p₁ ≤ k * p := Nat.mul_le_mul_left k hle
  omega

/-- (iii) `r < q` なら `v.take q` のすべての正の周期 `p` は `q < k * p` を満たす
（「到達域を越えたら周期は `q/k` より大きい」）。 -/
theorem GSCore.period_gt_of_reach_lt {x : List α} {k s p₁ r : ℕ} (H : GSCore x k s p₁ r)
    {q p : ℕ} (hq : q ≤ (x.drop s).length) (hrq : r < q) (hp : 0 < p)
    (hper : HasPeriod ((x.drop s).take q) p) : q < k * p := by
  by_contra hcon0
  have hcon : k * p ≤ q := Nat.le_of_not_lt hcon0
  obtain ⟨-, -, h2⟩ := H.krep_bound hq hp hcon hper
  omega

/-- `k` 回繰り返される **基本**（原始的）接頭辞は高々ひとつ。 -/
theorem GSCore.basic_unique {x : List α} {k s p₁ r : ℕ} (H : GSCore x k s p₁ r)
    (hk : 2 ≤ k) {p : ℕ} (hkrep : KRep (x.drop s) k p)
    (hb : Primitive ((x.drop s).take p)) : p = p₁ := by
  obtain ⟨hp, hlen, hper⟩ := hkrep
  obtain ⟨hp₁, hle, hqr⟩ :=
    H.krep_bound (q := k * p) (p := p) hlen hp (le_refl _) hper
  rcases Nat.lt_or_ge p₁ p with hlt | hge
  · exfalso
    have hR := H.reach hp₁
    have hper₁ : HasPeriod ((x.drop s).take (k * p)) p₁ :=
      hasPeriod_take_of_le hR.2.1 hqr
    -- `p₁` と `p` の重なりから `p` が原始的でないことを導く
    have hp₁pos : 0 < p₁ := Nat.pos_of_ne_zero hp₁
    have hwlen : ((x.drop s).take (k * p)).length = k * p := by
      simp only [List.length_take]; omega
    have hsum : p₁ + p - Nat.gcd p₁ p ≤ ((x.drop s).take (k * p)).length := by
      rw [hwlen]
      have : 2 * p ≤ k * p := Nat.mul_le_mul_right p hk
      omega
    have hg := fineWilf hper₁ hper hp₁pos hp hsum
    have hgle : Nat.gcd p₁ p ≤ p₁ := Nat.gcd_le_left _ hp₁pos
    have hgpos : 0 < Nat.gcd p₁ p := Nat.gcd_pos_of_pos_left _ hp₁pos
    have hple : p ≤ k * p := Nat.le_mul_of_pos_left p (by omega)
    have hroot : HasPeriod ((x.drop s).take p) (Nat.gcd p₁ p) :=
      hasPeriod_take_of_le hg hple
    have hrootlen : ((x.drop s).take p).length = p := by
      simp only [List.length_take]; omega
    have hdvd : Nat.gcd p₁ p ∣ ((x.drop s).take p).length := by
      rw [hrootlen]; exact Nat.gcd_dvd_right p₁ p
    exact not_primitive_of_period hgpos (by omega) hdvd hroot hb
  · omega

/-! ## `PalPeg.GSScan.KSimple` への橋渡し -/

/-- 周期ありの分解は走査側の仮定 `KSimple` を与える。 -/
theorem GSCore.ksimple {x : List α} {k s p₁ r : ℕ} (H : GSCore x k s p₁ r) (hp₁ : p₁ ≠ 0) :
    KSimple (x.drop s) k p₁ r := by
  refine ⟨Nat.pos_of_ne_zero hp₁, (H.reach hp₁).2.1, ?_⟩
  intro q p' hq hp' hkp hper
  obtain ⟨-, h1, h2⟩ := H.krep_bound hq hp' hkp hper
  exact ⟨h1, h2⟩

/-- 周期なしの分解（`period = None`）でも走査側の仮定を与えられる。 -/
theorem GSCore.ksimple_none {x : List α} {k s p₁ r : ℕ} (H : GSCore x k s p₁ r)
    (hp₁ : p₁ = 0) : KSimple (x.drop s) k ((x.drop s).length + 1) 0 := by
  refine ksimple_of_no_repeat ?_
  intro q p' hq hp' hkp hper
  exact (H.none_case hp₁).2 p' ⟨hp', le_trans hkp hq, hasPeriod_take_of_le hper hkp⟩

/-! ## 存在 -/

/-- `v = []` は `k`-繰り返し接頭辞を持たない。 -/
theorem not_krep_nil {k p : ℕ} (hk : 0 < k) : ¬ KRep ([] : List α) k p := by
  rintro ⟨hp, hlen, -⟩
  simp only [List.length_nil, Nat.le_zero] at hlen
  rcases Nat.mul_eq_zero.mp hlen with h | h <;> omega

/-- `GSCore` の存在（`s = |x|` は常に許される）。 -/
theorem gsCore_exists (x : List α) (k : ℕ) (hk : 0 < k) : ∃ s p₁ r, GSCore x k s p₁ r := by
  refine ⟨x.length, 0, 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_refl _
  · intro _
    refine ⟨rfl, ?_⟩
    intro p hp
    rw [List.drop_length] at hp
    exact not_krep_nil hk hp
  · intro h; exact absurd rfl h
  · intro h; exact absurd rfl h
  · intro h; exact absurd rfl h
  · intro h; exact absurd rfl h

/-- 最小の切断位置 `s` での `GSCore` の存在。 -/
theorem gsCore_exists_least (x : List α) (k : ℕ) (hk : 0 < k) :
    ∃ s p₁ r, GSCore x k s p₁ r ∧ ∀ t, t < s → ¬ ∃ p₁' r', GSCore x k t p₁' r' := by
  classical
  have hne : ∃ s, ∃ p₁ r, GSCore x k s p₁ r := by
    obtain ⟨s, p₁, r, h⟩ := gsCore_exists x k hk
    exact ⟨s, p₁, r, h⟩
  obtain ⟨p₁, r, h⟩ := Nat.find_spec hne
  exact ⟨Nat.find hne, p₁, r, h, fun t ht => Nat.find_min hne ht⟩

/-! ## 償却解析の部品（GS Theorem 1 に向けて） -/

/-- 到達域の直後で `p₁` を殺す削除量 `d = r - k*p₁ + 1`：
`v.drop d` の長さ `k*p₁` の接頭辞はもはや周期 `p₁` を持たない。 -/
theorem strip_kills_period {v : List α} {k p r : ℕ} (hk : 2 ≤ k) (hp : 0 < p)
    (hkp : k * p ≤ r) (hR : ReachOf v p r) (hrlt : r < v.length) :
    ¬ HasPeriod ((v.drop (r - k * p + 1)).take (k * p)) p := by
  obtain ⟨hrle, hper, hmax⟩ := hR
  have h2p : 2 * p ≤ k * p := Nat.mul_le_mul_right p hk
  have hpr : p ≤ r := by omega
  have hne : ¬ HasPeriod (v.take (r + 1)) p := by
    rcases hmax with h | h
    · omega
    · exact h
  -- 反例の位置は必ず `i + p = r`
  have hmis : v[r - p]? ≠ v[r]? := by
    intro heq
    apply hne
    intro i hi
    rw [List.length_take] at hi
    rw [List.getElem?_take_of_lt (show i < r + 1 by omega),
      List.getElem?_take_of_lt (show i + p < r + 1 by omega)]
    rcases Nat.lt_or_ge (i + p) r with hlt | hge
    · have := hper i (by rw [List.length_take]; omega)
      rwa [List.getElem?_take_of_lt (show i < r by omega),
        List.getElem?_take_of_lt (show i + p < r by omega)] at this
    · have hir : i + p = r := by omega
      have hii : i = r - p := by omega
      rw [hii, show r - p + p = r from by omega]
      exact heq
  intro hcon
  apply hmis
  have hd : r - k * p + 1 + (k * p - 1 - p) = r - p := by omega
  have hd' : r - k * p + 1 + (k * p - 1) = r := by omega
  have h1 := hcon (k * p - 1 - p) (by rw [List.length_take, List.length_drop]; omega)
  rw [List.getElem?_take_of_lt (show k * p - 1 - p < k * p by omega),
    List.getElem?_take_of_lt (show k * p - 1 - p + p < k * p by omega),
    List.getElem?_drop, List.getElem?_drop, hd,
    show r - k * p + 1 + (k * p - 1 - p + p) = r from by omega] at h1
  exact h1

/-! ## `GSDecomp` の側から述べた帰結（走査が使う形） -/

/-- (i) `GSDecomp` 版：`k * p₁ ≤ q` なら `v.take q` は `p₁` 未満の正の周期を持たない。 -/
theorem GSDecomp.no_shorter_period {x : List α} {k s p₁ r : ℕ} (H : GSDecomp x k s p₁ r)
    {q p : ℕ} (hq : q ≤ (x.drop s).length) (hkq : k * p₁ ≤ q) (hp : 0 < p)
    (hlt : p < p₁) : ¬ HasPeriod ((x.drop s).take q) p :=
  H.toGSCore.no_shorter_period hq hkq hp hlt

/-- (ii) `GSDecomp` 版：`q < k * p₁` なら `k * p ≤ q` なる周期 `p` を持たない。 -/
theorem GSDecomp.no_period_below {x : List α} {k s p₁ r : ℕ} (H : GSDecomp x k s p₁ r)
    {q p : ℕ} (hq : q ≤ (x.drop s).length) (hqk : q < k * p₁) (hp : 0 < p)
    (hkp : k * p ≤ q) : ¬ HasPeriod ((x.drop s).take q) p :=
  H.toGSCore.no_period_below hq hqk hp hkp

/-- (iii) `GSDecomp` 版：到達域を越えた `q` では、すべての正の周期 `p` が `q < k * p`。 -/
theorem GSDecomp.period_gt_of_reach_lt {x : List α} {k s p₁ r : ℕ} (H : GSDecomp x k s p₁ r)
    {q p : ℕ} (hq : q ≤ (x.drop s).length) (hrq : r < q) (hp : 0 < p)
    (hper : HasPeriod ((x.drop s).take q) p) : q < k * p :=
  H.toGSCore.period_gt_of_reach_lt hq hrq hp hper

/-- `GSDecomp` 版：走査側の仮定 `KSimple`。 -/
theorem GSDecomp.ksimple {x : List α} {k s p₁ r : ℕ} (H : GSDecomp x k s p₁ r)
    (hp₁ : p₁ ≠ 0) : KSimple (x.drop s) k p₁ r :=
  H.toGSCore.ksimple hp₁

/-- `GSDecomp` 版：`k` 回繰り返される基本接頭辞は高々ひとつ。 -/
theorem GSDecomp.basic_unique {x : List α} {k s p₁ r : ℕ} (H : GSDecomp x k s p₁ r)
    (hk : 2 ≤ k) {p : ℕ} (hkrep : KRep (x.drop s) k p)
    (hb : Primitive ((x.drop s).take p)) : p = p₁ :=
  H.toGSCore.basic_unique hk hkrep hb

/-! ## `GSDecomp` が空でないこと -/

/-- 切断が不要な場合（`x` 自身が `k`-simple）は L1 上界は自明に成り立つ。 -/
theorem gsDecomp_of_core_zero {x : List α} {k p₁ r : ℕ} (hk : 2 ≤ k)
    (H : GSCore x k 0 p₁ r) : GSDecomp x k 0 p₁ r where
  toGSCore := H
  cut_bound := by
    intro hx
    have : 0 < x.length := List.length_pos_iff.mpr hx
    omega
  cut_period_bound := by
    intro hp₁
    have h1 : 0 < k - 1 := by omega
    have h2 : 0 < p₁ := Nat.pos_of_ne_zero hp₁
    have := Nat.mul_pos h1 h2
    omega

/-- `k`-繰り返し接頭辞をもたないパターンは `s = 0` で分解できる
（Python の `Decomposition(0, None, 0)`）。 -/
theorem gsDecomp_zero_of_no_krep {x : List α} {k : ℕ} (hk : 2 ≤ k)
    (h : ∀ p, ¬ KRep x k p) : GSDecomp x k 0 0 0 := by
  refine gsDecomp_of_core_zero hk ⟨Nat.zero_le _, ?_, ?_, ?_, ?_, ?_⟩
  · intro _; exact ⟨rfl, by simpa using h⟩
  · intro hne; exact absurd rfl hne
  · intro hne; exact absurd rfl hne
  · intro hne; exact absurd rfl hne
  · intro hne; exact absurd rfl hne

/-- **GS_LOCAL_CLOCK.md L6/L7 の第 2 周期の性質**（第 2 周期が存在する場合）。
`p₁` が最小の `k`-繰り返し周期、`r` がその到達域、`p₂` がより長い基本 `k`-繰り返し周期なら

* `(k-1) * p₁ ≤ p₂`（文書の `p2 >= (k-2)*p1` より強い）、
* `r < p₁ + p₂`（文書の `reach <= p2 + p1`）。 -/
theorem second_period_bounds {v : List α} {k p₁ p₂ r : ℕ} (hk : 2 ≤ k)
    (hleast : IsLeastKRep v k p₁) (hR : ReachOf v p₁ r)
    (h2 : KRep v k p₂) (hb : Primitive (v.take p₂)) (hlt : p₁ < p₂) :
    (k - 1) * p₁ ≤ p₂ ∧ r < p₁ + p₂ :=
  ⟨kRepetition_periods hk hleast.1 h2 hb hlt,
    reach_lt_add_of_second hk hR.2.1 hR.1 hleast.1.1 h2 hb hlt⟩

/-! ## 存在定理（証明可能な弱い上界つき）

`GSDecompW` は `GSCore` に「素朴な計算だけで証明できる」切断長の上界を付けたもの。
再帰は GS の削除ループを一段だけ真似る：

* `v` に `k`-繰り返し接頭辞がなければ `s = 0`。
* あって、第 2 周期がなければ（`NoSecond`）`s = 0`。
* 第 2 周期 `p₂`（最小のものを取る；最小性から `Primitive (v.take p₂)`）があれば
  `d₀ = r - k*p₁ + 1` だけ削って `v.drop d₀` に再帰する。`strip_kills_period` により
  この `d₀` は `p₁` を殺す量である（停止性そのものには `1 ≤ d₀` で十分）。

不変量（一段ぶん）：`kRepetition_periods` から `(k-1) * p₁ ≤ p₂`、
`reach_lt_add_of_second` から `r < p₁ + p₂`、`_second` の成功条件から `k * p₂ ≤ |v|`。
これらから

```
d₀ + (k-1) * p₁ ≤ p₂,     よって   k * d₀ + k*(k-1) ≤ k * d₀ + k*(k-1)*p₁ ≤ k * p₂ ≤ |v|.
```

再帰を合成すると `s = Σ dᵢ` は `s = 0 ∨ s + k*(k-1) ≤ |x|` を満たす。

**この計算からは定数割合の上界は出ない。** 一段の不等式は本質的に `k * dᵢ ≤ nᵢ`
（`nᵢ` は現在の接尾辞長）であり、`nᵢ₊₁ = nᵢ - dᵢ` と合わせると
`Σ dᵢ < n₀` しか従わない（`dᵢ = nᵢ/k` を毎回取る敵対列が反例）。定数割合
`s < |x|/(k-1)` を得るには「第 2 周期が反復ごとに定数倍で増える」ことが要り、
それには GS の削除ループ（`p₂` 未満の `k`-繰り返し周期を全部消すまで削る）の
run 構造の解析が必要で、ここでは行っていない。 -/

/-- `GSCore` に、証明可能な切断長上界 `s = 0 ∨ s + k*(k-1) ≤ |x|` を付けたもの。 -/
structure GSDecompW (x : List α) (k s p₁ r : ℕ) : Prop extends GSCore x k s p₁ r where
  cut_bound_w : s = 0 ∨ s + k * (k - 1) ≤ x.length

/-- 弱い版でも切断は真の接頭辞：`1 * s < 1 * |x|`（`x ≠ []`, `2 ≤ k`）。 -/
theorem GSDecompW.cut_lt {x : List α} {k s p₁ r : ℕ} (H : GSDecompW x k s p₁ r)
    (hk : 2 ≤ k) (hx : x ≠ []) : 1 * s < 1 * x.length := by
  have hpos : 0 < x.length := List.length_pos_iff.mpr hx
  have hkk : 0 < k * (k - 1) := Nat.mul_pos (by omega) (by omega)
  rcases H.cut_bound_w with h | h
  · omega
  · omega

/-- 弱い版からも走査側の仮定 `KSimple` が得られる。 -/
theorem GSDecompW.ksimple {x : List α} {k s p₁ r : ℕ} (H : GSDecompW x k s p₁ r)
    (hp₁ : p₁ ≠ 0) : KSimple (x.drop s) k p₁ r :=
  H.toGSCore.ksimple hp₁

/-! ### 補助：切断 0 の構成と切断の合成 -/

theorem gsCore_zero_of_no_krep {v : List α} {k : ℕ} (h : ∀ p, ¬ KRep v k p) :
    GSCore v k 0 0 0 := by
  refine ⟨Nat.zero_le _, ?_, ?_, ?_, ?_, ?_⟩
  · intro _; exact ⟨rfl, by simpa using h⟩
  · intro hne; exact absurd rfl hne
  · intro hne; exact absurd rfl hne
  · intro hne; exact absurd rfl hne
  · intro hne; exact absurd rfl hne

theorem gsCore_zero_of_noSecond {v : List α} {k p₁ r : ℕ} (hp₁ : p₁ ≠ 0)
    (hleast : IsLeastKRep v k p₁) (hR : ReachOf v p₁ r) (hkr : k * p₁ ≤ r)
    (hns : NoSecond v k r) : GSCore v k 0 p₁ r := by
  refine ⟨Nat.zero_le _, ?_, ?_, ?_, ?_, ?_⟩
  · intro h0; exact absurd h0 hp₁
  · intro _; rw [List.drop_zero]; exact hleast
  · intro _; rw [List.drop_zero]; exact hR
  · intro _; exact hkr
  · intro _; rw [List.drop_zero]; exact hns

/-- 切断の合成：`v.drop d₀` を `d₁` で切ることは `v` を `d₀ + d₁` で切ること。 -/
theorem GSCore.drop_comp {v : List α} {k d₀ d₁ p₁ r : ℕ}
    (H : GSCore (v.drop d₀) k d₁ p₁ r) (hd₀ : d₀ ≤ v.length) :
    GSCore v k (d₀ + d₁) p₁ r := by
  have hEq : v.drop (d₀ + d₁) = (v.drop d₀).drop d₁ := by
    rw [List.drop_drop]
  have hlen : (v.drop d₀).length = v.length - d₀ := List.length_drop
  have hcut := H.cut_le
  rw [hlen] at hcut
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hEq]; exact H.none_case
  · rw [hEq]; exact H.least
  · rw [hEq]; exact H.reach
  · exact H.reach_ge
  · rw [hEq]; exact H.simple

/-! ### 補助：最小の `k`-繰り返し周期、到達域、最小の第 2 周期 -/

theorem exists_least_kRep {v : List α} {k : ℕ} (h : ∃ p, KRep v k p) :
    ∃ p₁, IsLeastKRep v k p₁ := by
  classical
  exact ⟨Nat.find h, Nat.find_spec h, fun q hq => Nat.find_le hq⟩

theorem exists_reach {v : List α} {k p₁ : ℕ} (h : KRep v k p₁) :
    ∃ r, ReachOf v p₁ r ∧ k * p₁ ≤ r := by
  classical
  have hw : HasPeriod (v.take (k * p₁)) p₁ := h.2.2
  have hwle : k * p₁ ≤ v.length := h.2.1
  refine ⟨Nat.findGreatest (fun m => HasPeriod (v.take m) p₁) v.length,
    ⟨Nat.findGreatest_le _,
      Nat.findGreatest_spec (P := fun m => HasPeriod (v.take m) p₁) hwle hw, ?_⟩,
    Nat.le_findGreatest (P := fun m => HasPeriod (v.take m) p₁) hwle hw⟩
  rcases Nat.lt_or_ge (Nat.findGreatest (fun m => HasPeriod (v.take m) p₁) v.length)
      v.length with hlt | hge
  · exact Or.inr (Nat.findGreatest_is_greatest (P := fun m => HasPeriod (v.take m) p₁)
      (Nat.lt_succ_self _) (by omega))
  · have := Nat.findGreatest_le (P := fun m => HasPeriod (v.take m) p₁) v.length
    exact Or.inl (by omega)

theorem exists_least_second {v : List α} {k r : ℕ} (h : ¬ NoSecond v k r) :
    ∃ p₂, 0 < p₂ ∧ max (k * p₂) (r + 1) ≤ v.length ∧
      HasPeriod (v.take (max (k * p₂) (r + 1))) p₂ ∧
      ∀ q, 0 < q → max (k * q) (r + 1) ≤ v.length →
        HasPeriod (v.take (max (k * q) (r + 1))) q → p₂ ≤ q := by
  classical
  have hex : ∃ p, 0 < p ∧ max (k * p) (r + 1) ≤ v.length ∧
      HasPeriod (v.take (max (k * p) (r + 1))) p := by
    rcases Classical.em (∃ p, 0 < p ∧ max (k * p) (r + 1) ≤ v.length ∧
        HasPeriod (v.take (max (k * p) (r + 1))) p) with h' | h'
    · exact h'
    · exact absurd (fun p hp hm hper => h' ⟨p, hp, hm, hper⟩) h
  obtain ⟨h1, h2, h3⟩ := Nat.find_spec hex
  exact ⟨Nat.find hex, h1, h2, h3, fun q hq hm hper => Nat.find_le ⟨hq, hm, hper⟩⟩

/-- `_second` が返す最小の第 2 周期の根は原始的（basic）。 -/
theorem least_second_primitive {v : List α} {k r p₂ : ℕ} (hk : 1 ≤ k) (hp₂ : 0 < p₂)
    (hm : max (k * p₂) (r + 1) ≤ v.length)
    (hper : HasPeriod (v.take (max (k * p₂) (r + 1))) p₂)
    (hmin : ∀ q, 0 < q → max (k * q) (r + 1) ≤ v.length →
        HasPeriod (v.take (max (k * q) (r + 1))) q → p₂ ≤ q) :
    Primitive (v.take p₂) := by
  intro z n hzn
  by_contra hn
  have hkp₂ : k * p₂ ≤ v.length := le_trans (le_max_left _ _) hm
  have hp₂le : p₂ ≤ v.length := le_trans (Nat.le_mul_of_pos_left p₂ hk) hkp₂
  have htlen : (v.take p₂).length = p₂ := by simp only [List.length_take]; omega
  have hzl : n * z.length = p₂ := by
    have hc := congrArg List.length hzn
    rw [htlen, length_wpow] at hc; omega
  have hn0 : n ≠ 0 := by rintro rfl; rw [Nat.zero_mul] at hzl; omega
  have hn2 : 2 ≤ n := by omega
  have hzpos : 0 < z.length := by
    rcases Nat.eq_zero_or_pos z.length with h | h
    · rw [h, Nat.mul_zero] at hzl; omega
    · exact h
  have hzlt : z.length < p₂ := by
    have h2 : 2 * z.length ≤ n * z.length := Nat.mul_le_mul_right _ hn2
    omega
  have hdvd : z.length ∣ p₂ := ⟨n, by rw [← hzl]; exact Nat.mul_comm n z.length⟩
  have hpre : HasPeriod (v.take p₂) z.length := by rw [hzn]; exact hasPeriod_wpow z n
  have hp₂m : p₂ ≤ max (k * p₂) (r + 1) :=
    le_trans (Nat.le_mul_of_pos_left p₂ hk) (le_max_left _ _)
  have htt : (v.take (max (k * p₂) (r + 1))).take p₂ = v.take p₂ := by
    rw [List.take_take]; congr 1; omega
  have hall : HasPeriod (v.take (max (k * p₂) (r + 1))) z.length :=
    hasPeriod_of_prefix_dvd hper hp₂ hdvd (by rw [htt]; exact hpre)
  have hkz : max (k * z.length) (r + 1) ≤ max (k * p₂) (r + 1) := by
    have h3 : k * z.length ≤ k * p₂ := Nat.mul_le_mul_left k (le_of_lt hzlt)
    omega
  have := hmin z.length hzpos (le_trans hkz hm) (hasPeriod_take_of_le hall hkz)
  omega

/-! ### 主定理 -/

private theorem exists_gsCore_aux (k : ℕ) (hk : 4 ≤ k) :
    ∀ (n : ℕ) (v : List α), v.length ≤ n →
      ∃ d p₁ r, GSCore v k d p₁ r ∧ (d = 0 ∨ d + k * (k - 1) ≤ v.length) := by
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
      · obtain ⟨p₂, hp₂, hm, hper₂, hmin₂⟩ := exists_least_second hns
        have hkp₂n : k * p₂ ≤ v.length := le_trans (le_max_left _ _) hm
        have hrn : r + 1 ≤ v.length := le_trans (le_max_right _ _) hm
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
          least_second_primitive (by omega) hp₂ hm hper₂ hmin₂
        have hkp : (k - 1) * p₁ ≤ p₂ :=
          kRepetition_periods (by omega) hleast.1 hkrep₂ hprim hlt12
        have hrlt : r < p₁ + p₂ :=
          reach_lt_add_of_second (by omega) hR.2.1 hR.1 hp₁pos hkrep₂ hprim hlt12
        have hmul1 : (k - 1) * p₁ + p₁ = k * p₁ := by
          have := Nat.sub_one_mul k p₁
          have hle : p₁ ≤ k * p₁ := Nat.le_mul_of_pos_left p₁ (by omega)
          omega
        -- 削除量
        have hstep : (r - k * p₁ + 1) + (k - 1) * p₁ ≤ p₂ := by omega
        have hmulk := Nat.mul_le_mul_left k hstep
        rw [Nat.mul_add] at hmulk
        have hk1 : k - 1 ≤ (k - 1) * p₁ := Nat.le_mul_of_pos_right (k - 1) hp₁pos
        have hk2 : k * (k - 1) ≤ k * ((k - 1) * p₁) := Nat.mul_le_mul_left k hk1
        have hd0le : r - k * p₁ + 1 ≤ k * (r - k * p₁ + 1) :=
          Nat.le_mul_of_pos_left _ (by omega)
        have hbound : (r - k * p₁ + 1) + k * (k - 1) ≤ v.length := by omega
        have hlen' : (v.drop (r - k * p₁ + 1)).length ≤ n := by
          rw [List.length_drop]; omega
        obtain ⟨d₁, p₁', r', H', hb'⟩ := ih (v.drop (r - k * p₁ + 1)) hlen'
        refine ⟨(r - k * p₁ + 1) + d₁, p₁', r', H'.drop_comp (by omega), Or.inr ?_⟩
        rcases hb' with h | h
        · rw [h]; omega
        · rw [List.length_drop] at h; omega
    · refine ⟨0, 0, 0, gsCore_zero_of_no_krep ?_, Or.inl rfl⟩
      intro p hp
      exact hex ⟨p, hp⟩

/-- **GS 前処理の存在定理（弱い上界つき）**。任意の `x` と `4 ≤ k` に対し、
`k`-simple な接尾辞への分解 `(s, p₁, r)` が存在し、切断長は
`s = 0 ∨ s + k*(k-1) ≤ |x|` を満たす。 -/
theorem gsDecompW_exists {k : ℕ} (hk : 4 ≤ k) (x : List α) :
    ∃ s p₁ r, GSDecompW x k s p₁ r := by
  obtain ⟨s, p₁, r, H, hb⟩ := exists_gsCore_aux k hk x.length x (le_refl _)
  exact ⟨s, p₁, r, H, hb⟩

/-! ## GS の削除ループに向けた構造補題

外側ループ 1 回ぶん（1 フェーズ）を固定する：`v`、その最小 `k`-繰り返し周期 `p₁`、
到達域 `r`、最小の第 2 周期 `T = p₂`（原始的）、`m = max (k*T) (r+1) ≤ |v|`、
`HasPeriod (v.take m) T`。GS の削除ループは「現接尾辞に `T` 未満の `k`-繰り返し周期が
ある間、その最小周期 `p` のぶんだけ削る」を繰り返す。その解析に要る 2 本を証明する。 -/

/-- **削除で現れうる短い周期の下界**。`w` の最小 `k`-繰り返し周期が `p`（到達域 `r ≥ k*p`）
のとき、`w.drop p` の `k`-繰り返し周期 `q` が `q < p` を満たすなら `(k-1) * p < k * q`。

つまり 1 周期ぶん削っても、最小周期は `k/(k-1)` 倍より大きくしか減らない。
証明：`k*q ≤ (k-1)*p` なら `p + k*q ≤ k*p ≤ r` なので窓 `[p, p+k*q)` は `p`-周期領域の
内側にあり、`p` だけ左にずらすと `w.take (k*q)` 自身が周期 `q` を持つ。これは `p` の
最小性に反する。 -/
theorem strip_period_drop {w : List α} {k p q r : ℕ} (hk : 2 ≤ k)
    (hmin : ∀ q', KRep w k q' → p ≤ q') (hp : 0 < p)
    (hper : HasPeriod (w.take r) p) (hrle : r ≤ w.length) (hkr : k * p ≤ r)
    (hq : KRep (w.drop p) k q) (hqp : q < p) : (k - 1) * p < k * q := by
  by_contra hcon
  have hcon' : k * q ≤ (k - 1) * p := Nat.le_of_not_lt hcon
  have hmul1 : (k - 1) * p + p = k * p := by
    have h1 := Nat.sub_one_mul k p
    have h2 : p ≤ k * p := Nat.le_mul_of_pos_left p (by omega)
    omega
  have hfit : p + k * q ≤ r := by omega
  have hkqw : k * q ≤ w.length := by omega
  -- `w.take (k*q) = (w.drop p).take (k*q)`
  have hEq : w.take (k * q) = (w.drop p).take (k * q) := by
    apply List.ext_getElem?
    intro i
    by_cases hi : i < k * q
    · rw [List.getElem?_take_of_lt hi, List.getElem?_take_of_lt hi, List.getElem?_drop]
      have h := hper i (by rw [List.length_take]; omega)
      rw [List.getElem?_take_of_lt (show i < r by omega),
        List.getElem?_take_of_lt (show i + p < r by omega)] at h
      rw [h, Nat.add_comm p i]
    · rw [List.getElem?_eq_none (by rw [List.length_take]; omega),
        List.getElem?_eq_none (by rw [List.length_take, List.length_drop]; omega)]
  have hkrep : KRep w k q := ⟨hq.1, hkqw, by rw [hEq]; exact hq.2.2⟩
  have := hmin q hkrep
  omega

/-- **フェーズ不変量：削除中の到達域の上界**。`v.take m` が周期 `T`（`v.take T` は原始的、
`2*T ≤ m ≤ |v|`）を持つとき、接尾辞 `v.drop D` の周期 `p < T` の窓が
`T`-周期領域の内側（`D + rw ≤ m`）に収まるなら `rw < p + T`。

証明：`p + T ≤ rw` とすると窓 `[D, D+rw)` は周期 `p` と `T` を同時に持ち、長さが
`p + T` 以上なので Fine–Wilf から `g = gcd p T` も周期。窓を `T` の周期性で
オフセット `e = D % T` へ平行移動し（`getElem?` の `mod` 表示）、
`hasPeriod_of_suffix_gcd` を `v.take (e+T)` に適用して `v.take T` 自身が周期 `g` を
持つことを得る。`g ∣ T`、`g ≤ p < T` なので `v.take T` は原始的でない。矛盾。 -/
theorem reach_lt_add_of_periodic_window {v : List α} {T m D rw p : ℕ}
    (hT : 0 < T) (hprim : Primitive (v.take T)) (hm : m ≤ v.length) (h2T : 2 * T ≤ m)
    (hperT : HasPeriod (v.take m) T) (hp : 0 < p) (hpT : p < T)
    (hDrw : D + rw ≤ m) (hper : HasPeriod ((v.drop D).take rw) p) :
    rw < p + T := by
  by_contra hcon
  have hcon' : p + T ≤ rw := Nat.le_of_not_lt hcon
  set e := D % T with he
  have heT : e < T := Nat.mod_lt _ hT
  have hwlen : ((v.drop D).take rw).length = rw := by
    rw [List.length_take, List.length_drop]; omega
  -- 窓は周期 `T` も持つ
  have hperW : HasPeriod ((v.drop D).take rw) T := by
    intro i hi
    rw [hwlen] at hi
    rw [List.getElem?_take_of_lt (show i < rw by omega),
      List.getElem?_take_of_lt (show i + T < rw by omega),
      List.getElem?_drop, List.getElem?_drop]
    have h := hperT (D + i) (by rw [List.length_take]; omega)
    rw [List.getElem?_take_of_lt (show D + i < m by omega),
      List.getElem?_take_of_lt (show D + i + T < m by omega)] at h
    rw [h]
    exact getElem?_congr (by omega)
  have hg := fineWilf hper hperW hp hT (by rw [hwlen]; omega)
  have hgpos : 0 < Nat.gcd p T := Nat.gcd_pos_of_pos_left _ hp
  have hgle : Nat.gcd p T ≤ p := Nat.gcd_le_left _ hp
  have hgT : HasPeriod ((v.drop D).take T) (Nat.gcd p T) := hasPeriod_take_of_le hg (by omega)
  -- オフセット `D` の窓を `e = D % T` へ移す
  have hshift : (v.drop D).take T = (v.drop e).take T := by
    apply List.ext_getElem?
    intro i
    by_cases hi : i < T
    · rw [List.getElem?_take_of_lt hi, List.getElem?_take_of_lt hi,
        List.getElem?_drop, List.getElem?_drop]
      have e1 : (v.take m)[D + i]? = v[D + i]? := List.getElem?_take_of_lt (by omega)
      have e2 : (v.take m)[e + i]? = v[e + i]? := List.getElem?_take_of_lt (by omega)
      have h1 : (v.take m)[(D + i) % T]? = (v.take m)[D + i]? :=
        hasPeriod_getElem?_mod hperT (by rw [List.length_take]; omega)
      have h2 : (v.take m)[(e + i) % T]? = (v.take m)[e + i]? :=
        hasPeriod_getElem?_mod hperT (by rw [List.length_take]; omega)
      have h3 : (e + i) % T = (D + i) % T := Nat.mod_add_mod D T i
      rw [← e1, ← e2, ← h1, ← h2, h3]
    · rw [List.getElem?_eq_none (by rw [List.length_take, List.length_drop]; omega),
        List.getElem?_eq_none (by rw [List.length_take, List.length_drop]; omega)]
  rw [hshift] at hgT
  -- `v.take (e+T)` の末尾 `T` 文字が周期 `g` ⟹ 全体が周期 `g`
  have hxlen : (v.take (e + T)).length = e + T := by rw [List.length_take]; omega
  have hsuf : (v.take (e + T)).drop ((v.take (e + T)).length - T) = (v.drop e).take T := by
    rw [hxlen]
    apply List.ext_getElem?
    intro i
    by_cases hi : i < T
    · rw [List.getElem?_drop, List.getElem?_take_of_lt hi, List.getElem?_drop,
        List.getElem?_take_of_lt (show e + T - T + i < e + T by omega)]
      exact getElem?_congr (by omega)
    · rw [List.getElem?_eq_none (by rw [List.length_drop, hxlen]; omega),
        List.getElem?_eq_none (by rw [List.length_take, List.length_drop]; omega)]
  have hxT : HasPeriod (v.take (e + T)) T := hasPeriod_take_of_le hperT (by omega)
  have hall : HasPeriod (v.take (e + T)) (Nat.gcd p T) :=
    hasPeriod_of_suffix_gcd hxT hT (Nat.gcd_dvd_right p T) (by rw [hsuf]; exact hgT)
      (by rw [hxlen]; omega)
  have hroot : HasPeriod (v.take T) (Nat.gcd p T) := hasPeriod_take_of_le hall (by omega)
  have hrootlen : (v.take T).length = T := by rw [List.length_take]; omega
  have hdvd : Nat.gcd p T ∣ (v.take T).length := by
    rw [hrootlen]; exact Nat.gcd_dvd_right p T
  exact not_primitive_of_period hgpos (by omega) hdvd hroot hprim

/-- 周期の遺伝：`w.take r` が周期 `p` を持つなら `(w.drop d).take (r-d)` も。 -/
theorem hasPeriod_drop_take {w : List α} {p r d : ℕ} (h : HasPeriod (w.take r) p)
    (hrle : r ≤ w.length) (hd : d ≤ r) : HasPeriod ((w.drop d).take (r - d)) p := by
  intro i hi
  rw [List.length_take, List.length_drop] at hi
  rw [List.getElem?_take_of_lt (show i < r - d by omega),
    List.getElem?_take_of_lt (show i + p < r - d by omega),
    List.getElem?_drop, List.getElem?_drop]
  have h2 := h (d + i) (by rw [List.length_take]; omega)
  rw [List.getElem?_take_of_lt (show d + i < r by omega),
    List.getElem?_take_of_lt (show d + i + p < r by omega)] at h2
  rw [h2]
  exact getElem?_congr (by omega)

/-- **残存 run と新しい周期の関係**。`w.take ρ` が周期 `p` を持ち、`q` が `w` の
`k`-繰り返し周期で根 `w.take q` が原始的、かつ窓 `min (k*q) ρ` が `p + q` 以上なら
`q ∣ p`。（Fine–Wilf ＋ 原始性。）これが削除ループでの周期の動きを支配する。 -/
theorem dvd_of_residual_run {w : List α} {k p q ρ : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hres : HasPeriod (w.take ρ) p) (hρ : ρ ≤ w.length)
    (hkq : KRep w k q) (hprim : Primitive (w.take q))
    (hge : p + q ≤ min (k * q) ρ) : q ∣ p := by
  have hkqw : k * q ≤ w.length := hkq.2.1
  have hwlen : (w.take (min (k * q) ρ)).length = min (k * q) ρ := by
    rw [List.length_take]; omega
  have h1 : HasPeriod (w.take (min (k * q) ρ)) p := hasPeriod_take_of_le hres (by omega)
  have h2 : HasPeriod (w.take (min (k * q) ρ)) q := hasPeriod_take_of_le hkq.2.2 (by omega)
  have hgle : Nat.gcd p q ≤ p := Nat.gcd_le_left _ hp
  have hg := fineWilf h1 h2 hp hq (by rw [hwlen]; omega)
  have hgq : Nat.gcd p q ∣ q := Nat.gcd_dvd_right p q
  have hroot : HasPeriod (w.take q) (Nat.gcd p q) := hasPeriod_take_of_le hg (by omega)
  have hqlen : (w.take q).length = q := by rw [List.length_take]; omega
  have hgpos : 0 < Nat.gcd p q := Nat.gcd_pos_of_pos_left _ hp
  have hgeq : Nat.gcd p q = q := by
    by_contra hne
    have hlt : Nat.gcd p q < q := lt_of_le_of_ne (Nat.le_of_dvd hq hgq) hne
    exact not_primitive_of_period hgpos (by omega) (by rw [hqlen]; exact hgq) hroot hprim
  rw [← hgeq]; exact Nat.gcd_dvd_left p q

theorem two_mul_le_of_dvd {p q : ℕ} (hp : 0 < p) (_hq : 0 < q) (hd : q ∣ p) (hne : q ≠ p) :
    2 * q ≤ p := by
  obtain ⟨t, ht⟩ := hd
  have ht0 : t ≠ 0 := by rintro rfl; omega
  have ht1 : t ≠ 1 := by rintro rfl; omega
  calc 2 * q = q * 2 := Nat.mul_comm _ _
    _ ≤ q * t := Nat.mul_le_mul_left q (by omega)
    _ = p := ht.symm

/-- **削除ループで最小周期は減らない**。`w` の最小 `k`-繰り返し周期 `p` の run が
`(k+1)*p` 以上残っているとき、`p` を 1 周期ぶん削った `w.drop p` の最小 `k`-繰り返し
周期 `q` は `p ≤ q` を満たす（実際は `p = q`：`p` 自身がまだ `k`-繰り返し周期）。

証明：`q < p` なら `strip_period_drop` から `(k-1)*p < k*q`、一方
`dvd_of_residual_run`（残存 run `r - p ≥ k*p`）から `q ∣ p`、ゆえに `2*q ≤ p`。
両者は `k ≥ 4` で矛盾する。 -/
theorem period_not_decreasing_of_strip {w : List α} {k p q r : ℕ} (hk : 4 ≤ k)
    (hmin : ∀ q', KRep w k q' → p ≤ q') (hp : 0 < p)
    (hper : HasPeriod (w.take r) p) (hrle : r ≤ w.length) (hkr : (k + 1) * p ≤ r)
    (hq : IsLeastKRep (w.drop p) k q) : p ≤ q := by
  by_contra hcon
  have hqp : q < p := Nat.lt_of_not_le hcon
  have hqpos : 0 < q := hq.1.1
  have hmulk : k * p ≤ (k + 1) * p := Nat.mul_le_mul_right p (by omega)
  have h4p : 4 * p ≤ k * p := Nat.mul_le_mul_right p hk
  have hdrop : (k - 1) * p < k * q :=
    strip_period_drop (by omega) hmin hp hper hrle (by omega) hq.1 hqp
  have hsub1 : (k - 1) * p + p = k * p := by
    have h1 := Nat.sub_one_mul k p
    have h2 : p ≤ k * p := Nat.le_mul_of_pos_left p (by omega)
    omega
  have hsucc : k * p + p = (k + 1) * p := by rw [Nat.succ_mul]
  have hres : HasPeriod ((w.drop p).take (r - p)) p :=
    hasPeriod_drop_take hper hrle (by omega)
  have hrho : r - p ≤ (w.drop p).length := by rw [List.length_drop]; omega
  have hkqq : k * q ≤ k * p := Nat.mul_le_mul_left k (le_of_lt hqp)
  have hpq2 : p + q ≤ k * q := by omega
  have hpq3 : p + q ≤ r - p := by omega
  have hdvd : q ∣ p :=
    dvd_of_residual_run hp hqpos hres hrho hq.1
      (IsLeastKRep.primitive (by omega) hq) (by omega)
  have h2q : 2 * q ≤ p := two_mul_le_of_dvd hp hqpos hdvd (by omega)
  have : k * (2 * q) ≤ k * p := Nat.mul_le_mul_left k h2q
  have hkq2 : k * (2 * q) = 2 * (k * q) := by ring
  omega

/-- **run が尽きたときの周期の増加**。残存 run が `(k-1)*p` 以上あり、新しい
`k`-繰り返し周期 `q`（根は原始的）が `p < q` を満たすなら `(k-2)*p < q`。
すなわち周期は 1 回の run 交替ごとに `(k-2)` 倍より大きくなる。 -/
theorem period_grows_at_transition {w : List α} {k p q ρ : ℕ} (hk : 3 ≤ k) (hp : 0 < p)
    (hres : HasPeriod (w.take ρ) p) (hρ : ρ ≤ w.length) (hkρ : (k - 1) * p ≤ ρ)
    (hq : KRep w k q) (hprim : Primitive (w.take q)) (hpq : p < q) : (k - 2) * p < q := by
  by_contra hcon
  have hcon' : q ≤ (k - 2) * p := Nat.le_of_not_lt hcon
  have hsub : (k - 2) * p + p = (k - 1) * p := by
    have h1 : (k - 2) * p + p = (k - 2 + 1) * p := by rw [Nat.succ_mul]
    have h2 : k - 2 + 1 = k - 1 := by omega
    rw [h1, h2]
  have h2q : 2 * q ≤ k * q := Nat.mul_le_mul_right q (by omega)
  have hdvd : q ∣ p :=
    dvd_of_residual_run hp hq.1 hres hρ hq hprim (by omega)
  have := Nat.le_of_dvd hp hdvd
  omega

/-! ## 削除ループの解析：現状と残るギャップ

上の 4 本（`strip_period_drop`, `reach_lt_add_of_periodic_window`,
`period_not_decreasing_of_strip`, `period_grows_at_transition`）から、GS の削除ループ
（閾値 `T = p₂`、1 周期ぶんずつ削る）の構造は次のところまで確定する。
`aᵢ` を run `i` の開始位置（`v` 座標）、`pᵢ` をそのときの最小 `k`-繰り返し周期、
`rᵢ` をその到達域、`ρᵢ` を run を抜けた時点の残存到達域とすると：

* `k * pᵢ ≤ rᵢ < pᵢ + T`（`reach_lt_add_of_periodic_window`、`aᵢ + rᵢ ≤ m` のとき）。
  よって `(k-1) * pᵢ < T`。
* run の中では周期は変わらない（`period_not_decreasing_of_strip`：`pᵢ` の run が
  `(k+1)pᵢ` 以上残っていれば削っても最小周期は `pᵢ` のまま）。
* run を抜けるとき `ρᵢ ∈ [(k-1)pᵢ, k*pᵢ)` で、次の周期は
  `pᵢ₊₁ > (k-2) * pᵢ`（`period_grows_at_transition`）。**最小周期は run 交替ごとに
  `(k-2)` 倍より大きく増える。**
* 1 つの run の削除量は `ℓᵢ * pᵢ = rᵢ - ρᵢ < T - (k-2) * pᵢ`。

**残るギャップ。** 上から run の本数は `N < log_{k-2}(T/(k-2)) + 1` に抑えられるが、
各 run の削除量の上界は `T - (k-2)pᵢ` であって幾何級数にならない。総削除量は
`Σᵢ (T - (k-2)pᵢ) = O(T log T)` にしかならず、GS が主張する `Σ 削除量 < p₂ = T`
（`GS_LOCAL_CLOCK.md`）は出ない。`T` を `O(T)` に落とすには、2 本目以降の run の
到達域 `rᵢ` を `T` ではなく `pᵢ + pᵢ₊₁` 程度で抑える必要があり、そのための補題は
本ファイルにはない（`ρᵢ < pᵢ + pᵢ₊₁` は示せるが、`rᵢ` は `ρᵢ` より手前の情報を含まない）。

したがって `GSDecomp`（`(k-1)*s < |x|` と `(k-2)*s < (k-1)*p₁`）の存在は依然として
未証明であり、証明済みの存在定理は `gsDecompW_exists`（`s = 0 ∨ s + k*(k-1) ≤ |x|`、
すなわち `1 * s < 1 * |x|`）のみである。`B * s < p₁` 型の下界はこの構成からは
まったく出ない：最終接尾辞の最小周期 `p₁` と累積切断 `s` は無関係でありうる。 -/

end PalPeg

