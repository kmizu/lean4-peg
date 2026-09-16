import Mathlib.Data.List.Basic
import Mathlib.Data.List.PeriodicityLemma

/-!
# 語の組合せ論（回文と周期）

`List α` 上の回文 `IsPal` と周期 `HasPeriod` に関する基本補題群。
`PAL` の PEG 解析（鎖の環）で使う道具箱で、特に

* 回文の拡張規則 `isPal_cons_append_iff`
* 周期と境界（border）の同値 `hasPeriod_iff_drop_eq_take`
* Fine–Wilf の定理 `fineWilf`

を含む。添字はすべて `getElem?`（`Option α`）で扱い、依存型の証明項を避ける。
-/

namespace PalPeg

universe u
variable {α : Type u}

/-- `x` が回文であること。 -/
def IsPal (x : List α) : Prop := x.reverse = x

/-- `p` が `x` の周期であること（`p ≥ 1` は要求しない）。 -/
def HasPeriod (x : List α) (p : ℕ) : Prop := ∀ i, i + p < x.length → x[i]? = x[i + p]?

/-! ## 添字の補助補題 -/

theorem getElem?_take_drop {x : List α} {k m i : ℕ} (h : i < m) :
    ((x.drop k).take m)[i]? = x[k + i]? := by
  rw [List.getElem?_take_of_lt h, List.getElem?_drop]

/-- 回文性の添字による特徴づけ。 -/
theorem isPal_iff_getElem? {x : List α} :
    IsPal x ↔ ∀ i, i < x.length → x[i]? = x[x.length - 1 - i]? := by
  constructor
  · intro h i hi
    conv_lhs => rw [← h]
    rw [List.getElem?_reverse hi]
  · intro h
    apply List.ext_getElem?
    intro i
    by_cases hi : i < x.length
    · rw [List.getElem?_reverse hi]
      exact (h i hi).symm
    · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_lt hi),
        List.getElem?_eq_none (Nat.le_of_not_lt hi)]

/-! ## 回文の基本性質 -/

@[simp] theorem isPal_nil : IsPal ([] : List α) := rfl

@[simp] theorem isPal_singleton (a : α) : IsPal [a] := rfl

theorem isPal_reverse {x : List α} : IsPal x.reverse ↔ IsPal x := by
  unfold IsPal
  rw [List.reverse_reverse]
  exact eq_comm

/-- 回文の拡張規則：`a x b` が回文 ⟺ `a = b` かつ `x` が回文。 -/
theorem isPal_cons_append_iff {a b : α} {x : List α} :
    IsPal ([a] ++ x ++ [b]) ↔ a = b ∧ IsPal x := by
  unfold IsPal
  constructor
  · intro h
    have h' : ([b] ++ x.reverse) ++ [a] = ([a] ++ x) ++ [b] := by
      simpa using h
    obtain ⟨h1, h2⟩ := List.append_inj' h' (by simp)
    obtain ⟨h3, h4⟩ := List.append_inj h1 (by simp)
    have hab : b = a := by simpa using h3
    exact ⟨hab.symm, h4⟩
  · rintro ⟨rfl, h⟩
    simp [h]

/-- 回文の両端から `k` 文字ずつ削っても回文。 -/
theorem isPal_drop_take_center {w : List α} {k : ℕ} (hw : IsPal w)
    (hk : k ≤ w.length / 2) : IsPal ((w.drop k).take (w.length - 2 * k)) := by
  have h2k : 2 * k ≤ w.length := by omega
  have hlen : ((w.drop k).take (w.length - 2 * k)).length = w.length - 2 * k := by
    simp only [List.length_take, List.length_drop]
    omega
  rw [isPal_iff_getElem?] at hw ⊢
  intro i hi
  rw [hlen] at hi ⊢
  rw [getElem?_take_drop hi, getElem?_take_drop (by omega)]
  rw [hw (k + i) (by omega)]
  congr 1
  omega


/-! ## 周期の基本性質

Mathlib の `List.HasPeriod`（自己重なりによる定義）と橋渡ししておく。 -/

theorem getElem?_congr {x : List α} {i j : ℕ} (h : i = j) : x[i]? = x[j]? := by rw [h]

theorem hasPeriod_iff_list {x : List α} {p : ℕ} : HasPeriod x p ↔ List.HasPeriod x p := by
  rw [List.hasPeriod_iff_getElem?]
  constructor
  · intro h i hi; exact h i (by omega)
  · intro h i hi; exact h i (by omega)

/-- 周期 `p` の語では、添字は `p` を法として決まる。 -/
theorem hasPeriod_getElem?_mod {x : List α} {p : ℕ} (h : HasPeriod x p) {i : ℕ}
    (hi : i < x.length) : x[i % p]? = x[i]? :=
  (hasPeriod_iff_list.mp h).getElem?_mod p i x hi

theorem hasPeriod_of_forall_getElem?_mod {x : List α} {p : ℕ}
    (h : ∀ i, i < x.length → x[i]? = x[i % p]?) : HasPeriod x p :=
  hasPeriod_iff_list.mpr (List.hasPeriod_iff_forall_getElem?_mod.mpr h)

@[simp] theorem hasPeriod_zero (x : List α) : HasPeriod x 0 := by
  intro i hi; simp

/-- 語長以上の数はつねに周期。 -/
theorem hasPeriod_of_length_le {x : List α} {p : ℕ} (h : x.length ≤ p) : HasPeriod x p := by
  intro i hi; omega

/-- 周期は因子（infix）に遺伝する。 -/
theorem hasPeriod_infix {x y : List α} {p : ℕ} (h : HasPeriod x p) (hy : y <:+: x) :
    HasPeriod y p :=
  hasPeriod_iff_list.mpr ((hasPeriod_iff_list.mp h).infix hy)

/-- 周期は接頭辞に遺伝する。 -/
theorem hasPeriod_take {x : List α} {p k : ℕ} (h : HasPeriod x p) : HasPeriod (x.take k) p :=
  hasPeriod_infix h (List.take_prefix k x).isInfix

/-- 周期は接尾辞に遺伝する。 -/
theorem hasPeriod_drop {x : List α} {p k : ℕ} (h : HasPeriod x p) : HasPeriod (x.drop k) p :=
  hasPeriod_infix h (List.drop_suffix k x).isInfix

/-- 周期 `p` は周期 `k * p` を導く。 -/
theorem hasPeriod_mul {x : List α} {p : ℕ} (h : HasPeriod x p) (k : ℕ) :
    HasPeriod x (k * p) := by
  induction k with
  | zero => intro i hi; simp
  | succ k ih =>
    intro i hi
    rw [Nat.succ_mul] at hi ⊢
    set K := k * p with hK
    rw [ih i (by omega), ← Nat.add_assoc]
    exact h _ (by omega)

/-- 周期と境界（border）の同値：`p` が周期 ⟺ `x` の長さ `|x| - p` の接頭辞と接尾辞が一致。 -/
theorem hasPeriod_iff_drop_eq_take {x : List α} {p : ℕ} (hp : p ≤ x.length) :
    HasPeriod x p ↔ x.drop p = x.take (x.length - p) := by
  constructor
  · intro h
    apply List.ext_getElem?
    intro i
    rw [List.getElem?_drop, List.getElem?_take]
    split
    · next hlt => rw [Nat.add_comm p i]; exact (h i (by omega)).symm
    · next hge => exact List.getElem?_eq_none (by omega)
  · intro h i hi
    have h' := congrArg (fun l => l[i]?) h
    simp only [List.getElem?_drop, List.getElem?_take_of_lt (show i < x.length - p by omega)] at h'
    rw [Nat.add_comm i p]
    exact h'.symm

/-! ## 反転と周期 -/

theorem hasPeriod_reverse_of {x : List α} {p : ℕ} (h : HasPeriod x p) :
    HasPeriod x.reverse p := by
  intro i hi
  rw [List.length_reverse] at hi
  rw [List.getElem?_reverse (by omega), List.getElem?_reverse (by omega)]
  calc x[x.length - 1 - i]? = x[(x.length - 1 - (i + p)) + p]? := getElem?_congr (by omega)
    _ = x[x.length - 1 - (i + p)]? := (h _ (by omega)).symm

@[simp] theorem hasPeriod_reverse {x : List α} {p : ℕ} :
    HasPeriod x.reverse p ↔ HasPeriod x p := by
  constructor
  · intro h
    have := hasPeriod_reverse_of h
    rwa [List.reverse_reverse] at this
  · exact hasPeriod_reverse_of

/-! ## 周期の伝播 -/

/-- 先頭 `p` 文字が `g`-周期的（`g ∣ p`）なら、`p`-周期的な語全体が `g`-周期的。 -/
theorem hasPeriod_of_prefix_dvd {x : List α} {p g : ℕ} (hxp : HasPeriod x p) (hp : 0 < p)
    (hgp : g ∣ p) (hpre : HasPeriod (x.take p) g) : HasPeriod x g := by
  apply hasPeriod_of_forall_getElem?_mod
  intro i hi
  have hmod : i % p < p := Nat.mod_lt _ hp
  have hmod' : i % p < x.length := by
    rcases Nat.lt_or_ge x.length p with h | h
    · rw [Nat.mod_eq_of_lt (by omega)]; exact hi
    · omega
  have hmod2 : (i % p) % g ≤ i % p := Nat.mod_le _ _
  have h1 : x[i]? = x[i % p]? := (hasPeriod_getElem?_mod hxp hi).symm
  have h2 : (x.take p)[(i % p) % g]? = (x.take p)[i % p]? :=
    hasPeriod_getElem?_mod hpre
      (by simpa [List.length_take] using Nat.lt_min.mpr ⟨by omega, by omega⟩)
  rw [List.getElem?_take_of_lt hmod, List.getElem?_take_of_lt (by omega)] at h2
  rw [h1, ← h2, Nat.mod_mod_of_dvd _ hgp]

/-- 末尾 `p` 文字が `g`-周期的（`g ∣ p`）なら、`p`-周期的な語全体が `g`-周期的。 -/
theorem hasPeriod_of_suffix_gcd {x : List α} {p g : ℕ} (hxp : HasPeriod x p) (hp : 0 < p)
    (hgp : g ∣ p) (hsuf : HasPeriod (x.drop (x.length - p)) g) (hpn : p ≤ x.length) :
    HasPeriod x g := by
  have _hpn := hpn
  have hrev : HasPeriod x.reverse p := hasPeriod_reverse.mpr hxp
  have htake : x.reverse.take p = (x.drop (x.length - p)).reverse := List.take_reverse
  have hpre : HasPeriod (x.reverse.take p) g := by
    rw [htake]; exact hasPeriod_reverse_of hsuf
  exact hasPeriod_reverse.mp (hasPeriod_of_prefix_dvd hrev hp hgp hpre)

/-! ## Fine–Wilf（周期性補題） -/

/-- **Fine–Wilf の定理**。Mathlib の `List.HasPeriod.gcd` の言い換え。 -/
theorem fineWilf {x : List α} {p q : ℕ} (hp' : HasPeriod x p) (hq' : HasPeriod x q)
    (hp : 0 < p) (hq : 0 < q) (hlen : p + q - Nat.gcd p q ≤ x.length) :
    HasPeriod x (Nat.gcd p q) := by
  have _hp := hp
  have _hq := hq
  exact hasPeriod_iff_list.mpr
    ((hasPeriod_iff_list.mp hp').gcd (hasPeriod_iff_list.mp hq') hlen)


/-! ## 回文の境界（border） -/

/-- 長さ `k` の接頭辞と接尾辞が一致することの添字による特徴づけ。 -/
theorem take_eq_drop_iff {x : List α} {k : ℕ} (hk : k ≤ x.length) :
    x.take k = x.drop (x.length - k) ↔ ∀ i, i < k → x[i]? = x[x.length - k + i]? := by
  constructor
  · intro h i hi
    have h' := congrArg (fun l => l[i]?) h
    simpa only [List.getElem?_take_of_lt hi, List.getElem?_drop] using h'
  · intro h
    apply List.ext_getElem?
    intro i
    rw [List.getElem?_take, List.getElem?_drop]
    split
    · next hlt => exact h i hlt
    · next hge => exact (List.getElem?_eq_none (by omega)).symm

/-- 回文の接頭辞が回文であるのは、それが境界（border）であるとき、かつそのときに限る。 -/
theorem isPal_take_iff {x : List α} {k : ℕ} (hx : IsPal x) (hk : k ≤ x.length) :
    IsPal (x.take k) ↔ x.take k = x.drop (x.length - k) := by
  have hlen : (x.take k).length = k := by simp only [List.length_take]; omega
  rw [take_eq_drop_iff hk, isPal_iff_getElem?, hlen]
  rw [isPal_iff_getElem?] at hx
  constructor
  · intro h i hi
    have h1 := h i hi
    rw [List.getElem?_take_of_lt hi, List.getElem?_take_of_lt (show k - 1 - i < k by omega)] at h1
    rw [h1, hx (k - 1 - i) (by omega)]
    exact getElem?_congr (by omega)
  · intro h i hi
    rw [List.getElem?_take_of_lt hi, List.getElem?_take_of_lt (show k - 1 - i < k by omega),
      h i hi, hx (k - 1 - i) (by omega)]
    exact getElem?_congr (by omega)

/-- 回文の接尾辞が回文であるのも、それが境界（border）であるとき、かつそのときに限る。 -/
theorem isPal_drop_iff {x : List α} {k : ℕ} (hx : IsPal x) (hk : k ≤ x.length) :
    IsPal (x.drop (x.length - k)) ↔ x.take k = x.drop (x.length - k) := by
  have hlen : (x.drop (x.length - k)).length = k := by simp only [List.length_drop]; omega
  rw [take_eq_drop_iff hk, isPal_iff_getElem?, hlen]
  rw [isPal_iff_getElem?] at hx
  constructor
  · intro h i hi
    have h1 := h i hi
    rw [List.getElem?_drop, List.getElem?_drop] at h1
    rw [hx i (by omega)]
    rw [show x.length - 1 - i = x.length - k + (k - 1 - i) from by omega]
    exact h1.symm
  · intro h i hi
    rw [List.getElem?_drop, List.getElem?_drop, ← h i hi,
      show x.length - k + (k - 1 - i) = x.length - 1 - i from by omega]
    exact hx i (by omega)

/-! ## 最小周期の遺伝 -/

/-- 群補題（group lemma）。`x` の最小周期が `p` で、`x` の長さ `L ≥ 2p` の接尾辞 `y` を取ると、
`y` も `p` 未満の周期を持たない。 -/
theorem hasPeriod_minimal_of_suffix {x y : List α} {p L : ℕ}
    (hx : IsPal x) (hxp : HasPeriod x p) (hp : 0 < p) (hpn : p ≤ x.length)
    (hmin : ∀ q, 0 < q → q < p → ¬ HasPeriod x q)
    (hy : y = x.drop (x.length - L)) (hpL : 2 * p ≤ L) (hLn : L ≤ x.length)
    (hyPal : IsPal y) :
    ∀ q, 0 < q → q < p → ¬ HasPeriod y q := by
  have _hx := hx
  have _hyPal := hyPal
  subst hy
  intro q hq hqp hyq
  have hylen : (x.drop (x.length - L)).length = L := by
    simp only [List.length_drop]; omega
  have hgcd_le : Nat.gcd p q ≤ q := Nat.gcd_le_right _ hq
  have hyp' : HasPeriod (x.drop (x.length - L)) p := hasPeriod_drop hxp
  have hg : HasPeriod (x.drop (x.length - L)) (Nat.gcd p q) := by
    refine fineWilf hyp' hyq hp hq ?_
    rw [hylen]; omega
  have hdd : (x.drop (x.length - L)).drop (L - p) = x.drop (x.length - p) := by
    rw [List.drop_drop]
    exact congrArg (fun m => x.drop m) (by omega)
  have hsuf : HasPeriod (x.drop (x.length - p)) (Nat.gcd p q) := hdd ▸ hasPeriod_drop hg
  have hxg : HasPeriod x (Nat.gcd p q) :=
    hasPeriod_of_suffix_gcd hxp hp (Nat.gcd_dvd_left p q) hsuf hpn
  exact hmin _ (Nat.gcd_pos_of_pos_left q hp) (by omega) hxg

end PalPeg
