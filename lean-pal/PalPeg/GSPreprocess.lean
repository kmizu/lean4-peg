import PalPeg.GSDecomp

/-!
# Galil–Seiferas 前処理の**計算可能**な実装と正当性

`docs/palindromes-in-peg/gs_overlap.py` の `decompose`（= `gs_events.py` の
`decomposition`）を Lean の全域関数として書き下し、その出力が `PalPeg.GSCore` を
満たすことを証明する。`GSDecomp.lean` の `gsCore_exists` は**存在**しか言わないので、
TM に載せるにはこちらの「実際に計算する」版が要る。

## Python との対応

| Python (`gs_overlap.py`)        | Lean                                  |
| ------------------------------- | ------------------------------------- |
| `shift_without_period(q, k)`    | `shiftNoPeriod q k`                   |
| `_first_period` の内側 `while`  | `firstInner`                          |
| `_first_period` の外側 `while`  | `firstOuter`（`bound=None` は `bound = |v|`）|
| `decompose` の `reach` 伸長ループ | `extendReach`                        |
| `_second_period` の内側 `while` | `secondInner`                         |
| `_second_period` の外側 `while` | `secondOuter`                         |
| `decompose` の削除内側ループ    | `stripLoop`                           |
| `decompose` の外側 `while True` | `decomposeLoop`                       |

ループはすべて燃料（fuel）付き構造再帰で、`partial` を使わない。燃料は各ループにつき
`|x| + 1` を渡す（どのループも添字が毎回 1 以上増え、添字は `|x|` を越えない）。
`decomposeLoop` だけは燃料切れの分岐が残るが、そこでは常に正しい自明解
`(|x|, 0, 0)`（`GSDecomp.gsCore_exists` の証人）を返すので、正当性は燃料の十分性に
依存しない。

## 本ファイルの結果

1. **計算**：`decompose x k : ℕ × ℕ × ℕ`（`decide` で Python 参照実装と突き合わせ済み）。
2. **正当性**：`decompose_spec : 3 ≤ k → GSCore x k s p₁ r`（`s, p₁, r` は `decompose` の出力）。
   内側走査が本当に `IsLeastKRep` / `ReachOf` / `NoSecond` を計算することを、
   `GSDecomp.lean` の Fine–Wilf 系の道具（`fineWilf`, `hasPeriod_take_of_le`）で示す。
   走査側への橋渡しは `decompose_ksimple`。
3. **仕事量**：`decomposeWork` を instrumented counter として定義し、
   `decomposeWork_le : 4 ≤ k → decomposeWork x k ≤ (16k+38)*|x| + (2k+5)` を示す。
   ポテンシャル `Φ = (k+2)*p + q` による走査の局所評価と、削除ループの停止条件から
   得られる第 2 周期の幾何級数（`p₁' ≥ p₂ ≥ (k-1)*p₁`）による償却。詳細は末尾の節。
-/

namespace PalPeg

universe u
variable {α : Type u}

/-! ## ずらし幅 -/

/-- `gs_overlap.shift_without_period(matched, k) = max(1, ceil(matched/k))`。 -/
def shiftNoPeriod (q k : ℕ) : ℕ := max 1 (ceilDiv q k)

theorem shiftNoPeriod_pos (q k : ℕ) : 0 < shiftNoPeriod q k := by
  unfold shiftNoPeriod; omega

/-- ずらし幅の要：`1 ≤ d < shiftNoPeriod q k` なら `k * d < q`。
（`d + 1 ≤ ⌈q/k⌉` から `k*(d+1) ≤ q + k - 1`。） -/
theorem mul_lt_of_lt_shiftNoPeriod {q k d : ℕ} (hk : 0 < k) (hd : 0 < d)
    (hlt : d < shiftNoPeriod q k) : k * d < q := by
  have hb := (ceilDiv_bounds (q := q) (k := k) hk).2
  have h1 : d + 1 ≤ ceilDiv q k := by
    unfold shiftNoPeriod at hlt; omega
  have h2 : k * (d + 1) ≤ k * ceilDiv q k := Nat.mul_le_mul_left k h1
  have hq : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · subst h
      have : ceilDiv 0 k = 0 := by
        unfold ceilDiv
        exact Nat.div_eq_of_lt (by omega)
      omega
    · exact h
  have : k * d + k ≤ q + k - 1 := by
    rw [Nat.mul_succ] at h2; omega
  omega

section Dec

variable [DecidableEq α]

/-! ## `_first_period` -/

/-- `_first_period` の内側ループ：候補周期 `p` に対し一致長 `q` を伸ばす。
Python: `while p+q < size and q < (k-1)*p and word[q] == word[p+q]: q += 1`。 -/
def firstInner (v : List α) (k p : ℕ) : ℕ → ℕ → ℕ
  | 0, q => q
  | fuel + 1, q =>
      if p + q < v.length ∧ q < (k - 1) * p ∧ v[q]? = v[p + q]? then
        firstInner v k p fuel (q + 1)
      else q

/-- `_first_period` の外側ループ。`bound` は Python の `bound`（`None` は `|v|` で代用：
外側の番人 `p < size` と同じ効き）。返り値は `(p, p + q) = (p, k*p)`。 -/
def firstOuter (v : List α) (k bound : ℕ) : ℕ → ℕ → Option (ℕ × ℕ)
  | 0, _ => none
  | fuel + 1, p =>
      if p < v.length ∧ p < bound then
        if firstInner v k p (v.length + 1) 0 = (k - 1) * p then
          some (p, p + (k - 1) * p)
        else
          firstOuter v k bound fuel (p + shiftNoPeriod (firstInner v k p (v.length + 1) 0) k)
      else none

/-- `bound=None` 版（`decompose` 本体が使う方）。 -/
def firstPeriod (v : List α) (k : ℕ) : Option (ℕ × ℕ) :=
  firstOuter v k v.length (v.length + 1) 1

/-! ## `reach` の伸長 -/

/-- Python: `while reach < size and word[reach] == word[reach-first]: reach += 1`。 -/
def extendReach (v : List α) (p : ℕ) : ℕ → ℕ → ℕ
  | 0, r => r
  | fuel + 1, r =>
      if r < v.length ∧ v[r - p]? = v[r]? then extendReach v p fuel (r + 1) else r

/-! ## `_second_period` -/

/-- `_second_period` の内側ループ。`none` は「第 2 周期を発見（現在の `p`）」、
`some q` は通常終了で一致長 `q`。 -/
def secondInner (v : List α) (k p r : ℕ) : ℕ → ℕ → Option ℕ
  | 0, q => some q
  | fuel + 1, q =>
      if p + q < v.length ∧ v[q]? = v[p + q]? then
        (if r < p + (q + 1) ∧ (k - 1) * p ≤ q + 1 then none
         else secondInner v k p r fuel (q + 1))
      else some q

/-- `_second_period` の外側ループ。`k*first ≤ q ≤ reach` のときは周期ずらし
（`p += first; q -= first`）、そうでなければ `shiftNoPeriod` で `q := 0`。 -/
def secondOuter (v : List α) (k first r : ℕ) : ℕ → ℕ → ℕ → Option ℕ
  | 0, _, _ => none
  | fuel + 1, p, q =>
      if p < v.length then
        match secondInner v k p r (v.length + 1) q with
        | none => some p
        | some q' =>
            if k * first ≤ q' ∧ q' ≤ r then
              secondOuter v k first r fuel (p + first) (q' - first)
            else
              secondOuter v k first r fuel (p + shiftNoPeriod q' k) 0
      else none

/-- `_second_period` 本体。 -/
def secondPeriod (v : List α) (k first r : ℕ) : Option ℕ :=
  secondOuter v k first r (v.length + 1) 1 0

/-! ## 削除ループと本体 -/

/-- Python: `while True: found = _first_period(..., bound=second); if None: break; start += found[0]`。 -/
def stripLoop (x : List α) (k bound : ℕ) : ℕ → ℕ → ℕ
  | 0, s => s
  | fuel + 1, s =>
      match firstOuter (x.drop s) k bound (x.length + 1) 1 with
      | none => s
      | some (p, _) => stripLoop x k bound fuel (s + p)

/-- `decompose` の外側 `while True`。燃料切れでは自明に正しい `(|x|, 0, 0)` を返す。 -/
def decomposeLoop (x : List α) (k : ℕ) : ℕ → ℕ → ℕ × ℕ × ℕ
  | 0, _ => (x.length, 0, 0)
  | fuel + 1, s =>
      match firstPeriod (x.drop s) k with
      | none => (s, 0, 0)
      | some (p₁, m) =>
          match secondPeriod (x.drop s) k p₁ (extendReach (x.drop s) p₁ (x.length + 1) m) with
          | none => (s, p₁, extendReach (x.drop s) p₁ (x.length + 1) m)
          | some p₂ => decomposeLoop x k fuel (stripLoop x k p₂ (x.length + 1) s)

/-- **GS 前処理**。`gs_overlap.decompose(word, k)` の返す `(cut, period, reach)`
（`period = None` は `p₁ = 0` で符号化）。 -/
def decompose (x : List α) (k : ℕ) : ℕ × ℕ × ℕ := decomposeLoop x k (x.length + 1) 0

end Dec

/-! ## Python 参照実装との突き合わせ -/

section Examples

/-- `decompose("000000001", 8) = Decomposition(cut=0, period=1, reach=8)` -/
example : decompose ([0,0,0,0,0,0,0,0,1] : List ℕ) 8 = (0, 1, 8) := by decide

/-- `decompose("", 8) = Decomposition(0, None, 0)` -/
example : decompose ([] : List ℕ) 8 = (0, 0, 0) := by decide

/-- `decompose("01", 8) = Decomposition(0, None, 0)` -/
example : decompose ([0,1] : List ℕ) 8 = (0, 0, 0) := by decide

/-- `decompose("0101010101010101010101", 8) = Decomposition(0, 2, 22)` -/
example :
    decompose ([0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1] : List ℕ) 8 = (0, 2, 22) := by
  decide

/-- `decompose("0000000010000000", 8) = Decomposition(0, 1, 8)` -/
example : decompose ([0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0] : List ℕ) 8 = (0, 1, 8) := by decide

/-- `decompose("aabaabaabaabaabaabaabaabb", 8) = Decomposition(0, 3, 24)` -/
example :
    decompose ([0,0,1,0,0,1,0,0,1,0,0,1,0,0,1,0,0,1,0,0,1,0,0,1,1] : List ℕ) 8 = (0, 3, 24) := by
  decide

/-- 削除ループが動く例：`decompose("aaaabaaaabaaaabaaaab", 4) = Decomposition(1, None, 0)` -/
example :
    decompose ([0,0,0,0,1,0,0,0,0,1,0,0,0,0,1,0,0,0,0,1] : List ℕ) 4 = (1, 0, 0) := by
  decide

end Examples

/-! ## 正当性：補助補題 -/

/-- `v.take m` の周期を添字条件で書き直す（`m ≤ |v|` のとき）。 -/
theorem hasPeriod_take_iff {v : List α} {p m : ℕ} (hm : m ≤ v.length) :
    HasPeriod (v.take m) p ↔ ∀ i, i + p < m → v[i]? = v[i + p]? := by
  have hlen : (v.take m).length = m := by simp only [List.length_take]; omega
  constructor
  · intro h i hi
    have h2 := h i (by rw [hlen]; exact hi)
    rwa [List.getElem?_take_of_lt (show i < m by omega),
      List.getElem?_take_of_lt (show i + p < m by omega)] at h2
  · intro h i hi
    rw [hlen] at hi
    rw [List.getElem?_take_of_lt (show i < m by omega),
      List.getElem?_take_of_lt (show i + p < m by omega)]
    exact h i hi

/-- 一致がひとつ伸びれば周期もひとつ伸びる。 -/
theorem hasPeriod_take_succ {v : List α} {p q : ℕ}
    (hper : HasPeriod (v.take (p + q)) p) (hpq : p + q < v.length)
    (hm : v[q]? = v[p + q]?) : HasPeriod (v.take (p + (q + 1))) p := by
  rw [hasPeriod_take_iff (by omega)]
  intro i hi
  rcases Nat.lt_or_ge i q with hlt | hge
  · exact (hasPeriod_take_iff (show p + q ≤ v.length by omega)).mp hper i (by omega)
  · have hiq : i = q := by omega
    subst hiq
    rw [hm]
    exact getElem?_congr (by omega)

/-- 不一致があれば周期は伸びない。 -/
theorem not_hasPeriod_take_succ {v : List α} {p q : ℕ} (hpq : p + q < v.length)
    (hm : v[q]? ≠ v[p + q]?) : ¬ HasPeriod (v.take (p + q + 1)) p := by
  intro h
  exact hm (by
    have := (hasPeriod_take_iff (show p + q + 1 ≤ v.length by omega)).mp h q (by omega)
    rwa [Nat.add_comm q p] at this)

/-! ## ずらしの安全性（`_first_period`） -/

/-- **`_first_period` のずらしの正当性**。候補 `p` で一致長 `q` まで伸ばして失敗し、
`p` 以下の周期はすべて排除済みなら、`p` と `p + shiftNoPeriod q k` の間に
`k`-繰り返し周期はない。

* `k * p' ≤ p + q` のとき：`p` と `p'` の重なりに Fine–Wilf を使い、`gcd p p' ≤ p` が
  `k`-繰り返し周期になって矛盾。
* `p + q < k * p'` のとき：`d = p' - p` が `v.take q` の周期になり（`k * d < q`）、
  `d < p` の `k`-繰り返し周期になって矛盾。 -/
theorem no_krep_between {v : List α} {k p q : ℕ} (hk : 3 ≤ k) (hp : 0 < p)
    (hper : HasPeriod (v.take (p + q)) p) (hpq : p + q ≤ v.length)
    (hqk : q < (k - 1) * p)
    (hbelow : ∀ p'', p'' ≤ p → ¬ KRep v k p'') :
    ∀ p', p < p' → p' < p + shiftNoPeriod q k → ¬ KRep v k p' := by
  intro p' hlt hub hkrep
  obtain ⟨hp', hlen', hper'⟩ := hkrep
  have hdpos : 0 < p' - p := by omega
  have hkd : k * (p' - p) < q :=
    mul_lt_of_lt_shiftNoPeriod (by omega) hdpos (by omega)
  have hsub : (k - 1) * p = k * p - p := Nat.sub_one_mul k p
  have hple : p ≤ k * p := Nat.le_mul_of_pos_left p (by omega)
  have hdp : p' - p < p := by
    refine Nat.lt_of_mul_lt_mul_left (a := k) ?_
    omega
  rcases Nat.lt_or_ge (p + q) (k * p') with hcaseB | hcaseA
  · have hdper : HasPeriod (v.take q) (p' - p) := by
      rw [hasPeriod_take_iff (show q ≤ v.length by omega)]
      intro i hi
      have e1 : v[i]? = v[i + p']? :=
        (hasPeriod_take_iff hlen').mp hper' i (by omega)
      have e2 : v[i + (p' - p)]? = v[i + (p' - p) + p]? :=
        (hasPeriod_take_iff hpq).mp hper (i + (p' - p)) (by omega)
      rw [e1, e2]
      exact getElem?_congr (by omega)
    exact hbelow (p' - p) (by omega)
      ⟨hdpos, by omega, hasPeriod_take_of_le hdper (by omega)⟩
  · have hperA : HasPeriod (v.take (k * p')) p := hasPeriod_take_of_le hper hcaseA
    have hwlen : (v.take (k * p')).length = k * p' := by
      simp only [List.length_take]; omega
    have hgpos : 0 < Nat.gcd p p' := Nat.gcd_pos_of_pos_left _ hp
    have hgle : Nat.gcd p p' ≤ p := Nat.gcd_le_left _ hp
    have h3p : 3 * p' ≤ k * p' := Nat.mul_le_mul_right p' hk
    have hsum : p + p' - Nat.gcd p p' ≤ (v.take (k * p')).length := by
      rw [hwlen]; omega
    have hg := fineWilf hperA hper' hp hp' hsum
    have hkg : k * Nat.gcd p p' ≤ k * p' := Nat.mul_le_mul_left k (by omega)
    exact hbelow (Nat.gcd p p') hgle ⟨hgpos, by omega, hasPeriod_take_of_le hg hkg⟩


/-! ## `_first_period` の内側ループ -/

section Dec2

variable [DecidableEq α]

theorem firstInner_spec (v : List α) (k p : ℕ) :
    ∀ (fuel q : ℕ), v.length ≤ fuel + q → p + q ≤ v.length → q ≤ (k - 1) * p →
      HasPeriod (v.take (p + q)) p →
      q ≤ firstInner v k p fuel q ∧
      p + firstInner v k p fuel q ≤ v.length ∧
      firstInner v k p fuel q ≤ (k - 1) * p ∧
      HasPeriod (v.take (p + firstInner v k p fuel q)) p ∧
      ¬(p + firstInner v k p fuel q < v.length ∧
        firstInner v k p fuel q < (k - 1) * p ∧
        v[firstInner v k p fuel q]? = v[p + firstInner v k p fuel q]?) := by
  intro fuel
  induction fuel with
  | zero =>
    intro q hf hpq hqk hper
    refine ⟨le_refl _, hpq, hqk, hper, ?_⟩
    rintro ⟨h1, -, -⟩
    simp only [firstInner] at h1 ⊢
    omega
  | succ fuel ih =>
    intro q hf hpq hqk hper
    by_cases hcond : p + q < v.length ∧ q < (k - 1) * p ∧ v[q]? = v[p + q]?
    · obtain ⟨h1, h2, h3⟩ := hcond
      have hnext : HasPeriod (v.take (p + (q + 1))) p := hasPeriod_take_succ hper h1 h3
      have hrec := ih (q + 1) (by omega) (by omega) (by omega) hnext
      rw [firstInner, if_pos ⟨h1, h2, h3⟩]
      exact ⟨by omega, hrec.2.1, hrec.2.2.1, hrec.2.2.2.1, hrec.2.2.2.2⟩
    · rw [firstInner, if_neg hcond]
      exact ⟨le_refl _, hpq, hqk, hper, hcond⟩

end Dec2

/-! ## `_first_period` の外側ループ -/

/-- `|v|` 以上の候補周期は `k`-繰り返しになれない（`k ≥ 3`）。 -/
theorem not_krep_of_length_le {v : List α} {k p' : ℕ} (hk : 3 ≤ k) (h : v.length ≤ p') :
    ¬ KRep v k p' := by
  rintro ⟨hp, hlen, -⟩
  have h3 : 3 * p' ≤ k * p' := Nat.mul_le_mul_right p' hk
  omega

section Dec3

variable [DecidableEq α]

/-- `firstOuter` が返す周期は正で `|v|` 未満（削除ループの進行に使う）。 -/
theorem firstOuter_lt (v : List α) (k bound : ℕ) :
    ∀ (fuel p p₁ m : ℕ), 0 < p → firstOuter v k bound fuel p = some (p₁, m) →
      0 < p₁ ∧ p₁ < v.length := by
  intro fuel
  induction fuel with
  | zero => intro p p₁ m _ h; exact absurd h (by simp [firstOuter])
  | succ fuel ih =>
    intro p p₁ m hp h
    rw [firstOuter] at h
    split at h
    · next hg =>
      split at h
      · rw [Option.some.injEq, Prod.mk.injEq] at h
        exact ⟨h.1 ▸ hp, h.1 ▸ hg.1⟩
      · refine ih _ _ _ ?_ h
        have := shiftNoPeriod_pos (firstInner v k p (v.length + 1) 0) k
        omega
    · exact absurd h (by simp)

/-- `firstOuter` が `some (p₁, m)` を返すなら `p₁` は最小の `k`-繰り返し周期で `m = k*p₁`。
`bound` の値によらない（`bound` は候補を早く打ち切るだけ）。 -/
theorem firstOuter_some (v : List α) (k bound : ℕ) (hk : 3 ≤ k) :
    ∀ (fuel p p₁ m : ℕ), 0 < p → (∀ p', p' < p → ¬ KRep v k p') →
      firstOuter v k bound fuel p = some (p₁, m) →
      IsLeastKRep v k p₁ ∧ m = k * p₁ := by
  intro fuel
  induction fuel with
  | zero => intro p p₁ m _ _ h; exact absurd h (by simp [firstOuter])
  | succ fuel ih =>
    intro p p₁ m hp hbelow h
    rw [firstOuter] at h
    split at h
    · next hg =>
      obtain ⟨hg1, hg2⟩ := hg
      have hstart : HasPeriod (v.take (p + 0)) p := by
        rw [hasPeriod_take_iff (by omega)]
        intro i hi; exact absurd hi (by omega)
      have hspec := firstInner_spec v k p (v.length + 1) 0 (by omega) (by omega)
        (Nat.zero_le _) hstart
      obtain ⟨-, hq2, hq3, hq4, hq5⟩ := hspec
      have hkp : p + (k - 1) * p = k * p := by
        have h1 := Nat.sub_one_mul k p
        have h2 : p ≤ k * p := Nat.le_mul_of_pos_left p (by omega)
        omega
      split at h
      · next hqeq =>
        rw [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [hqeq] at hq2 hq4
        refine ⟨⟨⟨hp, by omega, by rw [← hkp]; exact hq4⟩, ?_⟩, hkp⟩
        intro q' hq'
        by_contra hcon
        exact hbelow q' (by omega) hq'
      · next hqne =>
        have hqlt : firstInner v k p (v.length + 1) 0 < (k - 1) * p := by omega
        have hnp : ¬ KRep v k p := by
          rintro ⟨-, hlen, hper⟩
          have hlt : p + firstInner v k p (v.length + 1) 0 < v.length := by omega
          have hmatch : v[firstInner v k p (v.length + 1) 0]?
              = v[p + firstInner v k p (v.length + 1) 0]? := by
            refine ((hasPeriod_take_iff hlen).mp hper _ (by omega)).trans ?_
            exact getElem?_congr (by omega)
          exact hq5 ⟨hlt, hqlt, hmatch⟩
        have hbelow' : ∀ p'', p'' ≤ p → ¬ KRep v k p'' := by
          intro p'' hp''
          rcases Nat.lt_or_ge p'' p with hlt | hge
          · exact hbelow p'' hlt
          · have : p'' = p := by omega
            exact this ▸ hnp
        refine ih _ p₁ m ?_ ?_ h
        · have := shiftNoPeriod_pos (firstInner v k p (v.length + 1) 0) k; omega
        · intro p' hp'
          rcases Nat.lt_or_ge p' p with hlt | hge
          · exact hbelow p' hlt
          · rcases Nat.eq_or_lt_of_le hge with heq | hgt
            · exact heq ▸ hnp
            · exact no_krep_between hk hp hq4 hq2 hqlt hbelow' p' hgt hp'
    · exact absurd h (by simp)

/-- `firstOuter`（`bound = |v|`）が `none` を返すなら `k`-繰り返し接頭辞は存在しない。 -/
theorem firstOuter_none (v : List α) (k : ℕ) (hk : 3 ≤ k) :
    ∀ (fuel p : ℕ), 0 < p → v.length ≤ fuel + p → (∀ p', p' < p → ¬ KRep v k p') →
      firstOuter v k v.length fuel p = none → ∀ p', ¬ KRep v k p' := by
  have hexit : ∀ (p : ℕ), v.length ≤ p → (∀ p', p' < p → ¬ KRep v k p') →
      ∀ p', ¬ KRep v k p' := by
    intro p hpl hbelow p'
    rcases Nat.lt_or_ge p' p with hlt | hge
    · exact hbelow p' hlt
    · exact not_krep_of_length_le hk (by omega)
  intro fuel
  induction fuel with
  | zero => intro p hp hf hbelow _; exact hexit p (by omega) hbelow
  | succ fuel ih =>
    intro p hp hf hbelow h
    rw [firstOuter] at h
    split at h
    · next hg =>
      obtain ⟨hg1, -⟩ := hg
      split at h
      · exact absurd h (by simp)
      · refine ih _ ?_ ?_ ?_ h
        · have := shiftNoPeriod_pos (firstInner v k p (v.length + 1) 0) k; omega
        · have := shiftNoPeriod_pos (firstInner v k p (v.length + 1) 0) k; omega
        · -- 直前の分岐と同じ論法
          have hstart : HasPeriod (v.take (p + 0)) p := by
            rw [hasPeriod_take_iff (by omega)]
            intro i hi; exact absurd hi (by omega)
          have hspec := firstInner_spec v k p (v.length + 1) 0 (by omega) (by omega)
            (Nat.zero_le _) hstart
          obtain ⟨-, hq2, hq3, hq4, hq5⟩ := hspec
          rename_i hqne
          have hqlt : firstInner v k p (v.length + 1) 0 < (k - 1) * p := by omega
          have hnp : ¬ KRep v k p := by
            rintro ⟨-, hlen, hper⟩
            have h1 := Nat.sub_one_mul k p
            have h2 : p ≤ k * p := Nat.le_mul_of_pos_left p (by omega)
            have hlt : p + firstInner v k p (v.length + 1) 0 < v.length := by omega
            have hmatch : v[firstInner v k p (v.length + 1) 0]?
                = v[p + firstInner v k p (v.length + 1) 0]? := by
              refine ((hasPeriod_take_iff hlen).mp hper _ (by omega)).trans ?_
              exact getElem?_congr (by omega)
            exact hq5 ⟨hlt, hqlt, hmatch⟩
          have hbelow' : ∀ p'', p'' ≤ p → ¬ KRep v k p'' := by
            intro p'' hp''
            rcases Nat.lt_or_ge p'' p with hlt | hge
            · exact hbelow p'' hlt
            · have : p'' = p := by omega
              exact this ▸ hnp
          intro p' hp'
          rcases Nat.lt_or_ge p' p with hlt | hge
          · exact hbelow p' hlt
          · rcases Nat.eq_or_lt_of_le hge with heq | hgt
            · exact heq ▸ hnp
            · exact no_krep_between hk hp hq4 hq2 hqlt hbelow' p' hgt hp'
    · next hg =>
      exact hexit p (by simp only [not_and] at hg; omega) hbelow

/-! ## `reach` の伸長 -/

theorem extendReach_spec (v : List α) (p : ℕ) :
    ∀ (fuel r : ℕ), v.length ≤ fuel + r → p ≤ r → r ≤ v.length → HasPeriod (v.take r) p →
      r ≤ extendReach v p fuel r ∧ ReachOf v p (extendReach v p fuel r) := by
  intro fuel
  induction fuel with
  | zero =>
    intro r hf hpr hrl hper
    have hz : extendReach v p 0 r = r := rfl
    rw [hz]
    exact ⟨le_refl _, hrl, hper, Or.inl (by omega)⟩
  | succ fuel ih =>
    intro r hf hpr hrl hper
    by_cases hc : r < v.length ∧ v[r - p]? = v[r]?
    · obtain ⟨h1, h2⟩ := hc
      have hnext : HasPeriod (v.take (r + 1)) p := by
        rw [hasPeriod_take_iff (by omega)]
        intro i hi
        rcases Nat.lt_or_ge (i + p) r with hlt | hge
        · exact (hasPeriod_take_iff hrl).mp hper i hlt
        · have hir : i = r - p := by omega
          subst hir
          rw [h2]
          exact getElem?_congr (by omega)
      have hrec := ih (r + 1) (by omega) (by omega) (by omega) hnext
      rw [extendReach, if_pos ⟨h1, h2⟩]
      exact ⟨by omega, hrec.2⟩
    · rw [extendReach, if_neg hc]
      refine ⟨le_refl _, hrl, hper, ?_⟩
      by_cases h1 : r < v.length
      · refine Or.inr ?_
        have hm : v[r - p]? ≠ v[r]? := by tauto
        intro hcon
        refine hm (((hasPeriod_take_iff (show r + 1 ≤ v.length by omega)).mp hcon (r - p)
          (by omega)).trans ?_)
        exact getElem?_congr (by omega)
      · exact Or.inl (by omega)

/-! ## `_second_period`：探索対象 -/

end Dec3

/-- `_second_period` が探すもの：到達域 `r` を越える `k`-繰り返し接頭辞。
`GSDecomp.NoSecond` はこれが存在しないこと。 -/
def Second (v : List α) (k r p : ℕ) : Prop :=
  0 < p ∧ max (k * p) (r + 1) ≤ v.length ∧ HasPeriod (v.take (max (k * p) (r + 1))) p

theorem noSecond_iff {v : List α} {k r : ℕ} : NoSecond v k r ↔ ∀ p, ¬ Second v k r p := by
  constructor
  · rintro h p ⟨h1, h2, h3⟩; exact h p h1 h2 h3
  · intro h p h1 h2 h3; exact h p ⟨h1, h2, h3⟩

theorem not_second_of_length_le {v : List α} {k r p : ℕ} (hk : 3 ≤ k) (h : v.length ≤ p) :
    ¬ Second v k r p := by
  rintro ⟨hp, hlen, -⟩
  have h3 : 3 * p ≤ k * p := Nat.mul_le_mul_right p hk
  have hkm : k * p ≤ max (k * p) (r + 1) := le_max_left _ _
  omega

/-- 重なりの場合（`max (k*p') (r+1) ≤ p + q`）：Fine–Wilf で `gcd p p'` も第 2 周期。 -/
theorem second_gcd {v : List α} {k p p' r q : ℕ} (hk : 3 ≤ k) (hp : 0 < p) (hlt : p < p')
    (hper : HasPeriod (v.take (p + q)) p) (_hpq : p + q ≤ v.length)
    (hs : Second v k r p') (hA : max (k * p') (r + 1) ≤ p + q) :
    Second v k r (Nat.gcd p p') := by
  obtain ⟨hp', hlen', hper'⟩ := hs
  have hperA : HasPeriod (v.take (max (k * p') (r + 1))) p := hasPeriod_take_of_le hper hA
  have hwlen : (v.take (max (k * p') (r + 1))).length = max (k * p') (r + 1) := by
    simp only [List.length_take]; omega
  have hgpos : 0 < Nat.gcd p p' := Nat.gcd_pos_of_pos_left _ hp
  have hgle : Nat.gcd p p' ≤ p := Nat.gcd_le_left _ hp
  have h3 : 3 * p' ≤ k * p' := Nat.mul_le_mul_right p' hk
  have hkm : k * p' ≤ max (k * p') (r + 1) := le_max_left _ _
  have hsum : p + p' - Nat.gcd p p' ≤ (v.take (max (k * p') (r + 1))).length := by
    rw [hwlen]; omega
  have hg := fineWilf hperA hper' hp hp' hsum
  have hgm : max (k * Nat.gcd p p') (r + 1) ≤ max (k * p') (r + 1) :=
    max_le (le_trans (Nat.mul_le_mul_left k (show Nat.gcd p p' ≤ p' by omega)) hkm)
      (le_max_right _ _)
  exact ⟨hgpos, le_trans hgm hlen', hasPeriod_take_of_le hg hgm⟩

/-- 重ならない場合（`p + q < m'`）：差 `p' - p` が `v.take q` の周期になる。 -/
theorem hasPeriod_diff {v : List α} {p p' q m' : ℕ} (hlt : p < p')
    (hper : HasPeriod (v.take (p + q)) p) (hpq : p + q ≤ v.length)
    (hper' : HasPeriod (v.take m') p') (hm' : m' ≤ v.length) (hB : p + q < m') :
    HasPeriod (v.take q) (p' - p) := by
  rw [hasPeriod_take_iff (show q ≤ v.length by omega)]
  intro i hi
  have e1 : v[i]? = v[i + p']? := (hasPeriod_take_iff hm').mp hper' i (by omega)
  have e2 : v[i + (p' - p)]? = v[i + (p' - p) + p]? :=
    (hasPeriod_take_iff hpq).mp hper (i + (p' - p)) (by omega)
  rw [e1, e2]
  exact getElem?_congr (by omega)

/-- 内側ループの脱出状態では、現在の候補 `p` 自身は第 2 周期でない。 -/
theorem not_second_of_exit {v : List α} {k p q r : ℕ} (hk : 3 ≤ k) (_hp : 0 < p)
    (_hper : HasPeriod (v.take (p + q)) p) (hpq : p + q ≤ v.length)
    (hexit1 : ¬(r < p + q ∧ (k - 1) * p ≤ q))
    (hexit2 : ¬(p + q < v.length ∧ v[q]? = v[p + q]?)) :
    ¬ Second v k r p := by
  rintro ⟨-, hlen, hper'⟩
  have hkm : k * p ≤ max (k * p) (r + 1) := le_max_left _ _
  have hrm : r + 1 ≤ max (k * p) (r + 1) := le_max_right _ _
  have hsub : (k - 1) * p = k * p - p := Nat.sub_one_mul k p
  have hple : p ≤ k * p := Nat.le_mul_of_pos_left p (by omega)
  rcases Nat.lt_or_ge q (max (k * p) (r + 1) - p) with hqlt | hqge
  · refine hexit2 ⟨by omega, ?_⟩
    refine ((hasPeriod_take_iff hlen).mp hper' q (by omega)).trans ?_
    exact getElem?_congr (by omega)
  · exact hexit1 ⟨by omega, by omega⟩

/-- `shiftNoPeriod` ずらしの正当性（`_second_period`）。 -/
theorem no_second_between_shift {v : List α} {k p q p₁ r : ℕ} (hk : 3 ≤ k) (hp : 0 < p)
    (hleast : IsLeastKRep v k p₁)
    (hper : HasPeriod (v.take (p + q)) p) (hpq : p + q ≤ v.length)
    (hexit : ¬(r < p + q ∧ (k - 1) * p ≤ q))
    (hnb : ¬(k * p₁ ≤ q ∧ q ≤ r))
    (hbelow : ∀ p'', p'' ≤ p → ¬ Second v k r p'') :
    ∀ p', p < p' → p' < p + shiftNoPeriod q k → ¬ Second v k r p' := by
  intro p' hlt hub hs
  obtain ⟨hp', hlen', hper'⟩ := hs
  have hdpos : 0 < p' - p := by omega
  have hkd : k * (p' - p) < q := mul_lt_of_lt_shiftNoPeriod (by omega) hdpos (by omega)
  rcases Nat.lt_or_ge (p + q) (max (k * p') (r + 1)) with hB | hA
  · have hdper := hasPeriod_diff hlt hper hpq hper' hlen' hB
    rcases Nat.lt_or_ge r q with hrq | hqr
    · have hqlt : q < (k - 1) * p := by
        by_contra hcon
        exact hexit ⟨by omega, by omega⟩
      have hsub : (k - 1) * p = k * p - p := Nat.sub_one_mul k p
      have hple : p ≤ k * p := Nat.le_mul_of_pos_left p (by omega)
      have hdp : p' - p < p := Nat.lt_of_mul_lt_mul_left (a := k) (by omega)
      have hmax : max (k * (p' - p)) (r + 1) ≤ q := max_le (by omega) (by omega)
      exact hbelow (p' - p) (by omega)
        ⟨hdpos, le_trans hmax (by omega), hasPeriod_take_of_le hdper hmax⟩
    · have hq1 : q < k * p₁ := by
        by_contra hcon
        exact hnb ⟨by omega, by omega⟩
      have hkrep : KRep v k (p' - p) :=
        ⟨hdpos, by omega, hasPeriod_take_of_le hdper (by omega)⟩
      have hge := hleast.2 _ hkrep
      have : k * p₁ ≤ k * (p' - p) := Nat.mul_le_mul_left k hge
      omega
  · exact hbelow _ (Nat.gcd_le_left _ hp)
      (second_gcd hk hp hlt hper hpq ⟨hp', hlen', hper'⟩ hA)

/-- 周期ずらし（`p += first`）の正当性（`_second_period`）。 -/
theorem no_second_between_period {v : List α} {k p q p₁ r : ℕ} (hk : 3 ≤ k) (hp : 0 < p)
    (hleast : IsLeastKRep v k p₁)
    (hper : HasPeriod (v.take (p + q)) p) (hpq : p + q ≤ v.length)
    (ha : k * p₁ ≤ q)
    (hbelow : ∀ p'', p'' ≤ p → ¬ Second v k r p'') :
    ∀ p', p < p' → p' < p + p₁ → ¬ Second v k r p' := by
  intro p' hlt hub hs
  obtain ⟨hp', hlen', hper'⟩ := hs
  have hdpos : 0 < p' - p := by omega
  rcases Nat.lt_or_ge (p + q) (max (k * p') (r + 1)) with hB | hA
  · have hdper := hasPeriod_diff hlt hper hpq hper' hlen' hB
    have hdlt : p' - p < p₁ := by omega
    have h1 : k * ((p' - p) + 1) ≤ k * p₁ := Nat.mul_le_mul_left k (by omega)
    rw [Nat.mul_succ] at h1
    have hkrep : KRep v k (p' - p) :=
      ⟨hdpos, by omega, hasPeriod_take_of_le hdper (by omega)⟩
    have hge := hleast.2 _ hkrep
    omega
  · exact hbelow _ (Nat.gcd_le_left _ hp)
      (second_gcd hk hp hlt hper hpq ⟨hp', hlen', hper'⟩ hA)


section Dec4

variable [DecidableEq α]

/-! ## `_second_period` のループ -/

theorem secondInner_spec (v : List α) (k p r : ℕ) :
    ∀ (fuel q : ℕ), v.length ≤ fuel + q → p + q ≤ v.length →
      HasPeriod (v.take (p + q)) p → ¬(r < p + q ∧ (k - 1) * p ≤ q) →
      ∀ q', secondInner v k p r fuel q = some q' →
        p + q' ≤ v.length ∧ HasPeriod (v.take (p + q')) p ∧
        ¬(r < p + q' ∧ (k - 1) * p ≤ q') ∧
        ¬(p + q' < v.length ∧ v[q']? = v[p + q']?) := by
  intro fuel
  induction fuel with
  | zero =>
    intro q hf hpq hper hne q' hq'
    have hqq : q' = q := by simpa [secondInner] using hq'.symm
    subst hqq
    exact ⟨hpq, hper, hne, by rintro ⟨h1, -⟩; omega⟩
  | succ fuel ih =>
    intro q hf hpq hper hne q' hq'
    rw [secondInner] at hq'
    split at hq'
    · next hc =>
      obtain ⟨h1, h2⟩ := hc
      split at hq'
      · exact absurd hq' (by simp)
      · next hcond =>
        exact ih (q + 1) (by omega) (by omega) (hasPeriod_take_succ hper h1 h2) hcond q' hq'
    · next hc =>
      have hqq : q' = q := by simpa using hq'.symm
      subst hqq
      exact ⟨hpq, hper, hne, hc⟩

theorem secondOuter_none (v : List α) (k p₁ r : ℕ) (hk : 3 ≤ k)
    (hleast : IsLeastKRep v k p₁) (hreach : HasPeriod (v.take r) p₁) (hrle : r ≤ v.length) :
    ∀ (fuel p q : ℕ), 0 < p → v.length ≤ fuel + p →
      (p < v.length → p + q ≤ v.length ∧ HasPeriod (v.take (p + q)) p ∧
        ¬(r < p + q ∧ (k - 1) * p ≤ q)) →
      (∀ p', p' < p → ¬ Second v k r p') →
      secondOuter v k p₁ r fuel p q = none → ∀ p', ¬ Second v k r p' := by
  have hp₁ : 0 < p₁ := hleast.1.1
  have hexit : ∀ (p : ℕ), v.length ≤ p → (∀ p', p' < p → ¬ Second v k r p') →
      ∀ p', ¬ Second v k r p' := by
    intro p hpl hbelow p'
    rcases Nat.lt_or_ge p' p with hlt | hge
    · exact hbelow p' hlt
    · exact not_second_of_length_le hk (by omega)
  intro fuel
  induction fuel with
  | zero => intro p q hp hf _ hbelow _; exact hexit p (by omega) hbelow
  | succ fuel ih =>
    intro p q hp hf hinv hbelow h
    rw [secondOuter] at h
    split at h
    · next hg =>
      obtain ⟨hpq, hper, hne⟩ := hinv hg
      rcases hsi : secondInner v k p r (v.length + 1) q with _ | q'
      · simp only [hsi] at h
        exact absurd h (by simp)
      · simp only [hsi] at h
        obtain ⟨hpq', hper', hne', hexit2⟩ :=
          secondInner_spec v k p r (v.length + 1) q (by omega) hpq hper hne q' hsi
        have hnp : ¬ Second v k r p := not_second_of_exit hk hp hper' hpq' hne' hexit2
        have hbelow' : ∀ p'', p'' ≤ p → ¬ Second v k r p'' := by
          intro p'' hp''
          rcases Nat.lt_or_ge p'' p with hlt | hge
          · exact hbelow p'' hlt
          · have hpp : p'' = p := by omega
            exact hpp ▸ hnp
        split at h
        · next hcase =>
          obtain ⟨hc1, hc2⟩ := hcase
          have hp₁q : p₁ ≤ q' := le_trans (Nat.le_mul_of_pos_left p₁ (by omega)) hc1
          refine ih (p + p₁) (q' - p₁) (by omega) (by omega) ?_ ?_ h
          · intro _
            have heq : p + p₁ + (q' - p₁) = p + q' := by omega
            refine ⟨by omega, ?_, ?_⟩
            · rw [heq, hasPeriod_take_iff hpq']
              intro i hi
              have e1 : v[i]? = v[i + p₁]? :=
                (hasPeriod_take_iff hrle).mp hreach i (by omega)
              have e2 : v[i + p₁]? = v[i + p₁ + p]? :=
                (hasPeriod_take_iff hpq').mp hper' (i + p₁) (by omega)
              rw [e1, e2]
              exact getElem?_congr (by omega)
            · rw [heq]
              rintro ⟨hr1, hr2⟩
              have hq'lt : q' < (k - 1) * p := by
                by_contra hcon
                exact hne' ⟨hr1, by omega⟩
              have : (k - 1) * p ≤ (k - 1) * (p + p₁) := Nat.mul_le_mul_left _ (by omega)
              omega
          · intro p' hp'
            rcases Nat.lt_or_ge p' p with hlt | hge
            · exact hbelow p' hlt
            · rcases Nat.eq_or_lt_of_le hge with heq | hgt
              · exact heq ▸ hnp
              · exact no_second_between_period hk hp hleast hper' hpq' hc1 hbelow' p' hgt hp'
        · next hcase =>
          have hsp := shiftNoPeriod_pos q' k
          refine ih (p + shiftNoPeriod q' k) 0 (by omega) (by omega) ?_ ?_ h
          · intro hlt
            refine ⟨by omega, ?_, ?_⟩
            · rw [hasPeriod_take_iff (by omega)]
              intro i hi; exact absurd hi (by omega)
            · have hpos : 0 < (k - 1) * (p + shiftNoPeriod q' k) :=
                Nat.mul_pos (by omega) (by omega)
              rintro ⟨-, h2⟩
              omega
          · intro p' hp'
            rcases Nat.lt_or_ge p' p with hlt | hge
            · exact hbelow p' hlt
            · rcases Nat.eq_or_lt_of_le hge with heq | hgt
              · exact heq ▸ hnp
              · exact no_second_between_shift hk hp hleast hper' hpq' hne' hcase hbelow'
                  p' hgt hp'
    · next hg => exact hexit p (by omega) hbelow

end Dec4

/-! ## 削除ループと本体 -/

/-- 燃料切れの逃げ道が返す自明な分解（`GSDecomp.gsCore_exists` の証人）。 -/
theorem gsCore_full (x : List α) (k : ℕ) (hk : 0 < k) : GSCore x k x.length 0 0 := by
  refine ⟨le_refl _, ?_, ?_, ?_, ?_, ?_⟩
  · intro _
    refine ⟨rfl, ?_⟩
    intro p hp
    rw [List.drop_length] at hp
    exact not_krep_nil hk hp
  · intro h; exact absurd rfl h
  · intro h; exact absurd rfl h
  · intro h; exact absurd rfl h
  · intro h; exact absurd rfl h

section Dec5

variable [DecidableEq α]

theorem firstPeriod_none (v : List α) (k : ℕ) (hk : 3 ≤ k)
    (h : firstPeriod v k = none) : ∀ p, ¬ KRep v k p := by
  refine firstOuter_none v k hk (v.length + 1) 1 (by omega) (by omega) ?_ h
  intro p' hp'
  rintro ⟨h1, -, -⟩
  omega

theorem firstPeriod_some (v : List α) (k : ℕ) (hk : 3 ≤ k) {p₁ m : ℕ}
    (h : firstPeriod v k = some (p₁, m)) : IsLeastKRep v k p₁ ∧ m = k * p₁ := by
  refine firstOuter_some v k v.length hk (v.length + 1) 1 p₁ m (by omega) ?_ h
  intro p' hp'
  rintro ⟨h1, -, -⟩
  omega

theorem secondPeriod_none (v : List α) (k p₁ r : ℕ) (hk : 3 ≤ k)
    (hleast : IsLeastKRep v k p₁) (hreach : HasPeriod (v.take r) p₁) (hrle : r ≤ v.length)
    (h : secondPeriod v k p₁ r = none) : NoSecond v k r := by
  rw [noSecond_iff]
  refine secondOuter_none v k p₁ r hk hleast hreach hrle (v.length + 1) 1 0
    (by omega) (by omega) ?_ ?_ h
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

/-- 削除ループは切断位置を `|x|` の内側に保つ。 -/
theorem stripLoop_le (x : List α) (k bound : ℕ) :
    ∀ (fuel s : ℕ), s ≤ x.length → stripLoop x k bound fuel s ≤ x.length := by
  intro fuel
  induction fuel with
  | zero => intro s hs; exact hs
  | succ fuel ih =>
    intro s hs
    rw [stripLoop]
    rcases hf : firstOuter (x.drop s) k bound (x.length + 1) 1 with _ | ⟨p, m⟩
    · simp only []; exact hs
    · simp only []
      refine ih (s + p) ?_
      have hlt := firstOuter_lt (x.drop s) k bound (x.length + 1) 1 p m (by omega) hf
      have hvlen : (x.drop s).length = x.length - s := by simp
      omega

/-- **`decomposeLoop` の正当性**。 -/
theorem decomposeLoop_spec (x : List α) (k : ℕ) (hk : 3 ≤ k) :
    ∀ (fuel s : ℕ), s ≤ x.length →
      GSCore x k (decomposeLoop x k fuel s).1 (decomposeLoop x k fuel s).2.1
        (decomposeLoop x k fuel s).2.2 := by
  intro fuel
  induction fuel with
  | zero => intro s _; exact gsCore_full x k (by omega)
  | succ fuel ih =>
    intro s hs
    rw [decomposeLoop]
    have hvlen : (x.drop s).length = x.length - s := by simp
    rcases hfp : firstPeriod (x.drop s) k with _ | ⟨p₁, m⟩
    · simp only []
      have hnone := firstPeriod_none (x.drop s) k hk hfp
      exact ⟨hs, fun _ => ⟨rfl, hnone⟩, fun h => absurd rfl h, fun h => absurd rfl h,
        fun h => absurd rfl h, fun h => absurd rfl h⟩
    · simp only []
      obtain ⟨hleast, rfl⟩ := firstPeriod_some (x.drop s) k hk hfp
      have hp₁ : 0 < p₁ := hleast.1.1
      have hkp₁len : k * p₁ ≤ (x.drop s).length := hleast.1.2.1
      have hkp₁per : HasPeriod ((x.drop s).take (k * p₁)) p₁ := hleast.1.2.2
      obtain ⟨hrge, hreach⟩ :=
        extendReach_spec (x.drop s) p₁ (x.length + 1) (k * p₁) (by omega)
          (Nat.le_mul_of_pos_left p₁ (by omega)) hkp₁len hkp₁per
      set r := extendReach (x.drop s) p₁ (x.length + 1) (k * p₁) with hrdef
      rcases hsp : secondPeriod (x.drop s) k p₁ r with _ | p₂
      · simp only []
        refine ⟨hs, fun h => absurd h (by omega), fun _ => hleast, fun _ => hreach,
          fun _ => hrge, fun _ => ?_⟩
        exact secondPeriod_none (x.drop s) k p₁ r hk hleast hreach.2.1 hreach.1 hsp
      · simp only []
        exact ih _ (stripLoop_le x k p₂ (x.length + 1) s hs)

/-- **主定理**：`decompose x k` は `GSCore` を満たす分解を*計算する*。 -/
theorem decompose_spec (x : List α) (k : ℕ) (hk : 3 ≤ k) :
    GSCore x k (decompose x k).1 (decompose x k).2.1 (decompose x k).2.2 :=
  decomposeLoop_spec x k hk (x.length + 1) 0 (Nat.zero_le _)

/-- 主定理の分解形。 -/
theorem decompose_spec' (x : List α) (k : ℕ) (hk : 3 ≤ k) {s p₁ r : ℕ}
    (h : decompose x k = (s, p₁, r)) : GSCore x k s p₁ r := by
  have := decompose_spec x k hk
  rw [h] at this
  exact this

/-- 走査側 (`PalPeg.GSScan`) が要求する `KSimple` を、計算された分解から直接得る。 -/
theorem decompose_ksimple (x : List α) (k : ℕ) (hk : 3 ≤ k)
    (hp₁ : (decompose x k).2.1 ≠ 0) :
    KSimple (x.drop (decompose x k).1) k (decompose x k).2.1 (decompose x k).2.2 :=
  (decompose_spec x k hk).ksimple hp₁

end Dec5

/-! ## ずらし幅の追加評価（仕事量解析用） -/

theorem le_mul_shiftNoPeriod (q k : ℕ) (hk : 0 < k) : q ≤ k * shiftNoPeriod q k := by
  have h := (ceilDiv_bounds (q := q) (k := k) hk).1
  have h2 : k * ceilDiv q k ≤ k * shiftNoPeriod q k :=
    Nat.mul_le_mul_left k (by unfold shiftNoPeriod; omega)
  omega

theorem shiftNoPeriod_le_max (q k : ℕ) (hk : 0 < k) : shiftNoPeriod q k ≤ max 1 q := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · have hz : ceilDiv 0 k = 0 := Nat.div_eq_of_lt (by omega)
    unfold shiftNoPeriod
    omega
  · have h := (ceilDiv_bounds (q := q) (k := k) hk).2
    have h3 : q ≤ k * q := Nat.le_mul_of_pos_left q hk
    have hc : ceilDiv q k ≤ q := by
      by_contra hcon
      have h1 : k * (q + 1) ≤ k * ceilDiv q k := Nat.mul_le_mul_left k (by omega)
      rw [Nat.mul_succ] at h1
      omega
    unfold shiftNoPeriod
    omega

section Dec6

variable [DecidableEq α]

/-! ## 仕事量カウンタ（instrumented step counter）

各ループの反復を 1 単位で数える。1 反復は「1 回の記号比較 + 定数個の添字更新」なので、
このカウンタは比較回数もずらし回数も同時に上から押さえる（`gs_overlap.Meter` の
`comparisons + events` に対応する粒度）。 -/

def firstInnerWork (v : List α) (k p : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, q =>
      1 + (if p + q < v.length ∧ q < (k - 1) * p ∧ v[q]? = v[p + q]? then
             firstInnerWork v k p fuel (q + 1)
           else 0)

def firstOuterWork (v : List α) (k bound : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, p =>
      if p < v.length ∧ p < bound then
        1 + firstInnerWork v k p (v.length + 1) 0 +
          (if firstInner v k p (v.length + 1) 0 = (k - 1) * p then 0
           else firstOuterWork v k bound fuel
             (p + shiftNoPeriod (firstInner v k p (v.length + 1) 0) k))
      else 0

def extendReachWork (v : List α) (p : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, r =>
      1 + (if r < v.length ∧ v[r - p]? = v[r]? then extendReachWork v p fuel (r + 1) else 0)

def secondInnerWork (v : List α) (k p r : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, q =>
      1 + (if p + q < v.length ∧ v[q]? = v[p + q]? then
             (if r < p + (q + 1) ∧ (k - 1) * p ≤ q + 1 then 0
              else secondInnerWork v k p r fuel (q + 1))
           else 0)

def secondOuterWork (v : List α) (k first r : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | fuel + 1, p, q =>
      if p < v.length then
        1 + secondInnerWork v k p r (v.length + 1) q +
          (match secondInner v k p r (v.length + 1) q with
           | none => 0
           | some q' =>
               if k * first ≤ q' ∧ q' ≤ r then
                 secondOuterWork v k first r fuel (p + first) (q' - first)
               else
                 secondOuterWork v k first r fuel (p + shiftNoPeriod q' k) 0)
      else 0

/-- `decompose` の外側 1 反復ぶんの仕事量（`_first` + `reach` 伸長 + `_second`）。 -/
def decomposeStepWork (x : List α) (k s : ℕ) : ℕ :=
  firstOuterWork (x.drop s) k (x.drop s).length ((x.drop s).length + 1) 1 +
    (match firstPeriod (x.drop s) k with
     | none => 0
     | some (p₁, m) =>
         extendReachWork (x.drop s) p₁ (x.length + 1) m +
           secondOuterWork (x.drop s) k p₁ (extendReach (x.drop s) p₁ (x.length + 1) m)
             ((x.drop s).length + 1) 1 0)

def stripLoopWork (x : List α) (k bound : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, s =>
      firstOuterWork (x.drop s) k bound (x.length + 1) 1 +
        (match firstOuter (x.drop s) k bound (x.length + 1) 1 with
         | none => 0
         | some (p, _) => stripLoopWork x k bound fuel (s + p))

/-- `decomposeLoop` 全体の仕事量。 -/
def decomposeLoopWork (x : List α) (k : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, s =>
      decomposeStepWork x k s +
        (match firstPeriod (x.drop s) k with
         | none => 0
         | some (p₁, m) =>
             match secondPeriod (x.drop s) k p₁ (extendReach (x.drop s) p₁ (x.length + 1) m) with
             | none => 0
             | some p₂ =>
                 stripLoopWork x k p₂ (x.length + 1) s +
                   decomposeLoopWork x k fuel (stripLoop x k p₂ (x.length + 1) s))

/-- **仕事量カウンタ**（`decompose` 全体）。 -/
def decomposeWork (x : List α) (k : ℕ) : ℕ := decomposeLoopWork x k (x.length + 1) 0

/-! ## 走査の純粋な範囲補題 -/

theorem firstInner_le (v : List α) (k p : ℕ) :
    ∀ (fuel q : ℕ), p + q ≤ v.length →
      q ≤ firstInner v k p fuel q ∧ p + firstInner v k p fuel q ≤ v.length := by
  intro fuel
  induction fuel with
  | zero => intro q h; exact ⟨le_refl _, h⟩
  | succ fuel ih =>
    intro q h
    by_cases hc : p + q < v.length ∧ q < (k - 1) * p ∧ v[q]? = v[p + q]?
    · rw [firstInner, if_pos hc]
      have := ih (q + 1) (by omega)
      exact ⟨by omega, this.2⟩
    · rw [firstInner, if_neg hc]
      exact ⟨le_refl _, h⟩

theorem secondInner_le (v : List α) (k p r : ℕ) :
    ∀ (fuel q q' : ℕ), p + q ≤ v.length → secondInner v k p r fuel q = some q' →
      q ≤ q' ∧ p + q' ≤ v.length := by
  intro fuel
  induction fuel with
  | zero =>
    intro q q' h hq
    have : q' = q := by simpa [secondInner] using hq.symm
    subst this
    exact ⟨le_refl _, h⟩
  | succ fuel ih =>
    intro q q' h hq
    rw [secondInner] at hq
    split at hq
    · next hc =>
      split at hq
      · exact absurd hq (by simp)
      · have := ih (q + 1) q' (by omega) hq
        exact ⟨by omega, this.2⟩
    · have : q' = q := by simpa using hq.symm
      subst this
      exact ⟨le_refl _, h⟩

/-! ## 線形仕事量：`_first_period` -/

theorem firstInnerWork_le (v : List α) (k p : ℕ) :
    ∀ (fuel q : ℕ), firstInnerWork v k p fuel q + q ≤ firstInner v k p fuel q + 1 := by
  intro fuel
  induction fuel with
  | zero => intro q; simp only [firstInnerWork, firstInner]; omega
  | succ fuel ih =>
    intro q
    by_cases hc : p + q < v.length ∧ q < (k - 1) * p ∧ v[q]? = v[p + q]?
    · rw [firstInnerWork, if_pos hc, firstInner, if_pos hc]
      have := ih (q + 1)
      omega
    · rw [firstInnerWork, if_neg hc, firstInner, if_neg hc]
      omega

/-- **`_first_period` の線形仕事量**：ポテンシャル `(k+2)*p + q` による。 -/
theorem firstOuterWork_le (v : List α) (k bound : ℕ) (hk : 3 ≤ k) :
    ∀ (fuel p : ℕ), 0 < p → firstOuterWork v k bound fuel p ≤ (k + 2) * (v.length + 1 - p) := by
  intro fuel
  induction fuel with
  | zero => intro p _; simp [firstOuterWork]
  | succ fuel ih =>
    intro p hp
    by_cases hg : p < v.length ∧ p < bound
    · rw [firstOuterWork, if_pos hg]
      obtain ⟨hg1, -⟩ := hg
      have hin := firstInnerWork_le v k p (v.length + 1) 0
      have hb := firstInner_le v k p (v.length + 1) 0 (by omega)
      have hsp : 1 ≤ shiftNoPeriod (firstInner v k p (v.length + 1) 0) k :=
        shiftNoPeriod_pos _ _
      have hsmax := shiftNoPeriod_le_max (firstInner v k p (v.length + 1) 0) k (by omega)
      have hkm := le_mul_shiftNoPeriod (firstInner v k p (v.length + 1) 0) k (by omega)
      have hsle : shiftNoPeriod (firstInner v k p (v.length + 1) 0) k ≤ v.length - p := by
        omega
      have hrec := ih (p + shiftNoPeriod (firstInner v k p (v.length + 1) 0) k) (by omega)
      have hd1 : (k + 2) * (v.length + 1 - p)
          = (k + 2) * (v.length + 1 - p - shiftNoPeriod (firstInner v k p (v.length + 1) 0) k)
            + (k + 2) * shiftNoPeriod (firstInner v k p (v.length + 1) 0) k := by
        rw [← Nat.mul_add]; congr 1; omega
      have hd2 : (k + 2) * shiftNoPeriod (firstInner v k p (v.length + 1) 0) k
          = k * shiftNoPeriod (firstInner v k p (v.length + 1) 0) k
            + 2 * shiftNoPeriod (firstInner v k p (v.length + 1) 0) k := by ring
      have hd3 : v.length + 1 - (p + shiftNoPeriod (firstInner v k p (v.length + 1) 0) k)
          = v.length + 1 - p - shiftNoPeriod (firstInner v k p (v.length + 1) 0) k := by omega
      rw [hd3] at hrec
      split <;> omega
    · rw [firstOuterWork, if_neg hg]
      omega

/-! ## 線形仕事量：`reach` 伸長 -/

theorem extendReachWork_le (v : List α) (p : ℕ) :
    ∀ (fuel r : ℕ), r ≤ v.length → extendReachWork v p fuel r ≤ v.length + 1 - r := by
  intro fuel
  induction fuel with
  | zero => intro r _; simp [extendReachWork]
  | succ fuel ih =>
    intro r hr
    by_cases hc : r < v.length ∧ v[r - p]? = v[r]?
    · rw [extendReachWork, if_pos hc]
      have := ih (r + 1) (by omega)
      omega
    · rw [extendReachWork, if_neg hc]
      omega

/-! ## 線形仕事量：`_second_period` -/

theorem secondInnerWork_le (v : List α) (k p r : ℕ) :
    ∀ (fuel q : ℕ), p + q ≤ v.length →
      secondInnerWork v k p r fuel q + q ≤ v.length - p + 1 := by
  intro fuel
  induction fuel with
  | zero => intro q h; simp only [secondInnerWork]; omega
  | succ fuel ih =>
    intro q h
    rw [secondInnerWork]
    split
    · next hc =>
      split
      · omega
      · have := ih (q + 1) (by omega)
        omega
    · omega

theorem secondInnerWork_le' (v : List α) (k p r : ℕ) :
    ∀ (fuel q q' : ℕ), secondInner v k p r fuel q = some q' →
      secondInnerWork v k p r fuel q + q ≤ q' + 1 := by
  intro fuel
  induction fuel with
  | zero =>
    intro q q' hq
    have : q' = q := by simpa [secondInner] using hq.symm
    subst this
    simp only [secondInnerWork]
    omega
  | succ fuel ih =>
    intro q q' hq
    rw [secondInner] at hq
    rw [secondInnerWork]
    split at hq
    · next hc =>
      rw [if_pos hc]
      split at hq
      · exact absurd hq (by simp)
      · next hd =>
        rw [if_neg hd]
        have := ih (q + 1) q' hq
        omega
    · next hc =>
      rw [if_neg hc]
      have : q' = q := by simpa using hq.symm
      subst this
      omega

/-- **`_second_period` の線形仕事量**：同じポテンシャル `(k+2)*p + q`。
周期ずらし（`p += first`, `q -= first`）でも `ΔΦ = (k+1)*first ≥ 2` が仕事を賄う。 -/
theorem secondOuterWork_le (v : List α) (k first r : ℕ) (hk : 3 ≤ k) (hf : 0 < first) :
    ∀ (fuel p q : ℕ), 0 < p → p ≤ 2 * v.length + 1 → q ≤ v.length →
      (p < v.length → p + q ≤ v.length) →
      secondOuterWork v k first r fuel p q + ((k + 2) * p + q)
        ≤ (k + 2) * (2 * v.length + 1) + v.length := by
  have hbase : ∀ p q : ℕ, p ≤ 2 * v.length + 1 → q ≤ v.length →
      (k + 2) * p + q ≤ (k + 2) * (2 * v.length + 1) + v.length := by
    intro p q hp hq
    have := Nat.mul_le_mul_left (k + 2) hp
    omega
  intro fuel
  induction fuel with
  | zero =>
    intro p q _ hp hq _
    simp only [secondOuterWork]
    have := hbase p q hp hq
    omega
  | succ fuel ih =>
    intro p q hp hple hq hinv
    rw [secondOuterWork]
    split
    · next hg =>
      have hpq : p + q ≤ v.length := hinv hg
      rcases hsi : secondInner v k p r (v.length + 1) q with _ | q'
      · simp only []
        have hw := secondInnerWork_le v k p r (v.length + 1) q hpq
        have := hbase p q hple hq
        have hmul : (k + 2) * p + q ≤ (k + 2) * (2 * v.length + 1) + v.length := this
        -- 発見して即終了：内側の仕事だけ
        have hb2 : (k + 2) * (p + 1) ≤ (k + 2) * (2 * v.length + 1) := by
          refine Nat.mul_le_mul_left (k + 2) ?_
          omega
        have hd : (k + 2) * (p + 1) = (k + 2) * p + (k + 2) := by ring
        omega
      · simp only []
        have hw := secondInnerWork_le' v k p r (v.length + 1) q q' hsi
        obtain ⟨hq'ge, hq'le⟩ := secondInner_le v k p r (v.length + 1) q q' hpq hsi
        split
        · next hcase =>
          obtain ⟨hc1, hc2⟩ := hcase
          have hfq : first ≤ q' := le_trans (Nat.le_mul_of_pos_left first (by omega)) hc1
          have hrec := ih (p + first) (q' - first) (by omega) (by omega) (by omega)
            (by intro _; omega)
          have hd : (k + 2) * (p + first) = (k + 2) * p + (k + 2) * first := by ring
          have hd2 : (k + 2) * first = k * first + 2 * first := by ring
          have hd3 : first ≤ k * first := Nat.le_mul_of_pos_left first (by omega)
          omega
        · next =>
          have hsp : 1 ≤ shiftNoPeriod q' k := shiftNoPeriod_pos _ _
          have hsmax := shiftNoPeriod_le_max q' k (by omega)
          have hkm := le_mul_shiftNoPeriod q' k (by omega)
          have hrec := ih (p + shiftNoPeriod q' k) 0 (by omega) (by omega) (by omega)
            (by intro _; omega)
          have hd : (k + 2) * (p + shiftNoPeriod q' k)
              = (k + 2) * p + (k * shiftNoPeriod q' k + 2 * shiftNoPeriod q' k) := by ring
          omega
    · next hg =>
      have := hbase p q hple hq
      omega

/-! ## 外側 1 反復の線形仕事量 -/

/-- **`decompose` の外側 1 反復（`_first` + `reach` + `_second`）は線形仕事量**。
定数は `C = 3k+8`, `D = 2k+5`。 -/
theorem decomposeStepWork_le (x : List α) (k s : ℕ) (hk : 3 ≤ k) (hs : s ≤ x.length) :
    decomposeStepWork x k s ≤ (3 * k + 8) * x.length + (2 * k + 5) := by
  have hvlen : (x.drop s).length = x.length - s := by simp
  have hLx : (x.drop s).length ≤ x.length := by omega
  have hA : (k + 2) * (x.drop s).length ≤ (k + 2) * x.length := Nat.mul_le_mul_left _ hLx
  have hB : (k + 2) * (2 * (x.drop s).length + 1)
      = 2 * ((k + 2) * (x.drop s).length) + (k + 2) := by ring
  have hC : (3 * k + 8) * x.length = 3 * ((k + 2) * x.length) + 2 * x.length := by ring
  have h1 : firstOuterWork (x.drop s) k (x.drop s).length ((x.drop s).length + 1) 1
      ≤ (k + 2) * (x.drop s).length := by
    have := firstOuterWork_le (x.drop s) k (x.drop s).length hk ((x.drop s).length + 1) 1
      (by omega)
    simpa using this
  unfold decomposeStepWork
  rcases hfp : firstPeriod (x.drop s) k with _ | ⟨p₁, m⟩
  · simp only []
    omega
  · simp only []
    obtain ⟨hleast, rfl⟩ := firstPeriod_some (x.drop s) k hk hfp
    have hp₁ : 0 < p₁ := hleast.1.1
    have hmle : k * p₁ ≤ (x.drop s).length := hleast.1.2.1
    have h2 := extendReachWork_le (x.drop s) p₁ (x.length + 1) (k * p₁) hmle
    have h3 := secondOuterWork_le (x.drop s) k p₁
      (extendReach (x.drop s) p₁ (x.length + 1) (k * p₁)) hk hp₁
      ((x.drop s).length + 1) 1 0 (by omega) (by omega) (by omega) (by intro _; omega)
    have h4 : (k + 2) * 1 + 0 = k + 2 := by ring
    omega

end Dec6

/-! ## 大域的な線形仕事量に向けた鋭い評価

`decomposeStepWork_le` は 1 パスを `O(|x|)` で押さえるが、GS の議論では 1 パスの仕事は
`O(k*p₂ + (r - k*p₁))` であり、パスごとに `p₂` が `(k-1)` 倍以上に増える（幾何級数）。
以下ではまずその鋭い評価を用意する。 -/

/-- `q ≤ k*p` なら `⌈q/k⌉ ≤ p`。 -/
theorem ceilDiv_le_of_le_mul {q k p : ℕ} (hk : 0 < k) (h : q ≤ k * p) : ceilDiv q k ≤ p := by
  have hb := (ceilDiv_bounds (q := q) (k := k) hk).2
  by_contra hcon
  have h1 : k * (p + 1) ≤ k * ceilDiv q k := Nat.mul_le_mul_left k (by omega)
  rw [Nat.mul_succ] at h1
  omega

/-- ずらし幅は候補周期を高々 2 倍にしかしない（`q ≤ k*p` のとき）。 -/
theorem shiftNoPeriod_le_of_le_mul {q k p : ℕ} (hk : 0 < k) (hp : 0 < p) (h : q ≤ k * p) :
    shiftNoPeriod q k ≤ p := by
  have := ceilDiv_le_of_le_mul hk h
  unfold shiftNoPeriod
  omega

section Dec7

variable [DecidableEq α]

/-- 内側走査は `(k-1)*p` を越えない（周期の仮定を使わない版）。 -/
theorem firstInner_le_bound (v : List α) (k p : ℕ) :
    ∀ (fuel q : ℕ), q ≤ (k - 1) * p → firstInner v k p fuel q ≤ (k - 1) * p := by
  intro fuel
  induction fuel with
  | zero => intro q h; exact h
  | succ fuel ih =>
    intro q h
    by_cases hc : p + q < v.length ∧ q < (k - 1) * p ∧ v[q]? = v[p + q]?
    · rw [firstInner, if_pos hc]
      exact ih (q + 1) (by omega)
    · rw [firstInner, if_neg hc]
      exact h

/-- **`_first_period` が成功したときの仕事量は `O(k * p₁)`**（`|v|` に依存しない）。
これが GS の「最小 `k`-繰り返し周期を見つけた時点で止まる」の定量版。 -/
theorem firstOuterWork_le_some (v : List α) (k bound : ℕ) (hk : 3 ≤ k) :
    ∀ (fuel p p₁ m : ℕ), 0 < p → firstOuter v k bound fuel p = some (p₁, m) →
      firstOuterWork v k bound fuel p + (k + 2) * p ≤ (2 * k + 1) * p₁ + 2 := by
  intro fuel
  induction fuel with
  | zero => intro p p₁ m _ h; exact absurd h (by simp [firstOuter])
  | succ fuel ih =>
    intro p p₁ m hp h
    rw [firstOuter] at h
    rw [firstOuterWork]
    split at h
    · next hg =>
      rw [if_pos hg]
      have hin := firstInnerWork_le v k p (v.length + 1) 0
      split at h
      · next hqeq =>
        rw [if_pos hqeq]
        rw [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        have h1 := Nat.sub_one_mul k p
        have h2 : p ≤ k * p := Nat.le_mul_of_pos_left p (by omega)
        have h3 : (2 * k + 1) * p = k * p + k * p + p := by ring
        have h4 : (k + 2) * p = k * p + 2 * p := by ring
        omega
      · next hqne =>
        rw [if_neg hqne]
        have hsp := shiftNoPeriod_pos (firstInner v k p (v.length + 1) 0) k
        have hkm := le_mul_shiftNoPeriod (firstInner v k p (v.length + 1) 0) k (by omega)
        have hrec := ih (p + shiftNoPeriod (firstInner v k p (v.length + 1) 0) k) p₁ m
          (by omega) h
        have hd : (k + 2) * (p + shiftNoPeriod (firstInner v k p (v.length + 1) 0) k)
            = (k + 2) * p + (k * shiftNoPeriod (firstInner v k p (v.length + 1) 0) k
              + 2 * shiftNoPeriod (firstInner v k p (v.length + 1) 0) k) := by ring
        omega
    · exact absurd h (by simp)

/-- **`bound` 付き `_first_period` の仕事量は `O(k * bound)`**。
候補周期は 1 反復で高々 2 倍にしかならないので、`bound` を越えた時点で止まる走査は
`bound` に比例した仕事しかしない。削除ループの最後の（失敗する）呼び出しに使う。 -/
theorem firstOuterWork_le_min (v : List α) (k bound : ℕ) (hk : 3 ≤ k) :
    ∀ (fuel p : ℕ), 0 < p → p ≤ 2 * min bound v.length + 1 →
      firstOuterWork v k bound fuel p + (k + 2) * p
        ≤ (k + 2) * (2 * min bound v.length + 1) := by
  intro fuel
  induction fuel with
  | zero =>
    intro p hp hple
    simp only [firstOuterWork]
    have h5 : (k + 2) * p ≤ (k + 2) * (2 * min bound v.length + 1) :=
      Nat.mul_le_mul_left _ hple
    omega
  | succ fuel ih =>
    intro p hp hple
    have h5 : (k + 2) * p ≤ (k + 2) * (2 * min bound v.length + 1) :=
      Nat.mul_le_mul_left _ hple
    rw [firstOuterWork]
    split
    · next hg =>
      obtain ⟨hg1, hg2⟩ := hg
      have hin := firstInnerWork_le v k p (v.length + 1) 0
      have hqb : firstInner v k p (v.length + 1) 0 ≤ (k - 1) * p :=
        firstInner_le_bound v k p (v.length + 1) 0 (Nat.zero_le _)
      have hkp : (k - 1) * p ≤ k * p := by
        have h1 := Nat.sub_one_mul k p
        have h2 : p ≤ k * p := Nat.le_mul_of_pos_left p (by omega)
        omega
      have hsle : shiftNoPeriod (firstInner v k p (v.length + 1) 0) k ≤ p :=
        shiftNoPeriod_le_of_le_mul (by omega) hp (by omega)
      have hsp := shiftNoPeriod_pos (firstInner v k p (v.length + 1) 0) k
      have hkm := le_mul_shiftNoPeriod (firstInner v k p (v.length + 1) 0) k (by omega)
      have hrec := ih (p + shiftNoPeriod (firstInner v k p (v.length + 1) 0) k)
        (by omega) (by omega)
      have hd : (k + 2) * (p + shiftNoPeriod (firstInner v k p (v.length + 1) 0) k)
          = (k + 2) * p + (k * shiftNoPeriod (firstInner v k p (v.length + 1) 0) k
            + 2 * shiftNoPeriod (firstInner v k p (v.length + 1) 0) k) := by ring
      have hmb : (k + 2) * (p + 1) ≤ (k + 2) * (2 * min bound v.length + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      have hd2 : (k + 2) * (p + 1) = (k + 2) * p + (k + 2) := by ring
      split <;> omega
    · omega

end Dec7

/-! ## `reach` 伸長と `_second_period` の鋭い評価 -/

section Dec8

variable [DecidableEq α]

/-- `reach` 伸長の仕事量はちょうど伸ばした量 + 1。 -/
theorem extendReachWork_le' (v : List α) (p : ℕ) :
    ∀ (fuel r : ℕ), extendReachWork v p fuel r + r ≤ extendReach v p fuel r + 1 := by
  intro fuel
  induction fuel with
  | zero => intro r; simp only [extendReachWork, extendReach]; omega
  | succ fuel ih =>
    intro r
    by_cases hc : r < v.length ∧ v[r - p]? = v[r]?
    · rw [extendReachWork, if_pos hc, extendReach, if_pos hc]
      have := ih (r + 1); omega
    · rw [extendReachWork, if_neg hc, extendReach, if_neg hc]; omega

/-- 内側走査が「発見」で終わったなら、現在の候補 `p` は本当に第 2 周期。 -/
theorem secondInner_second (v : List α) (k p r : ℕ) (hk : 3 ≤ k) (hp : 0 < p) :
    ∀ (fuel q : ℕ), p + q ≤ v.length → HasPeriod (v.take (p + q)) p →
      secondInner v k p r fuel q = none → Second v k r p := by
  intro fuel
  induction fuel with
  | zero => intro q _ _ h; exact absurd h (by simp [secondInner])
  | succ fuel ih =>
    intro q hpq hper h
    rw [secondInner] at h
    split at h
    · next hc =>
      obtain ⟨h1, h2⟩ := hc
      have hnext : HasPeriod (v.take (p + (q + 1))) p := hasPeriod_take_succ hper h1 h2
      split at h
      · next hfire =>
        obtain ⟨hf1, hf2⟩ := hfire
        have hkp : k * p ≤ p + (q + 1) := by
          have e := Nat.sub_one_mul k p
          have e2 : p ≤ k * p := Nat.le_mul_of_pos_left p (by omega)
          omega
        have hmax : max (k * p) (r + 1) ≤ p + (q + 1) := max_le hkp (by omega)
        exact ⟨hp, by omega, hasPeriod_take_of_le hnext hmax⟩
      · exact ih (q + 1) (by omega) hnext h
    · exact absurd h (by simp)

/-- 内側走査の脱出条件（周期の仮定なし版）。 -/
theorem secondInner_exit (v : List α) (k p r : ℕ) :
    ∀ (fuel q q' : ℕ), ¬(r < p + q ∧ (k - 1) * p ≤ q) →
      secondInner v k p r fuel q = some q' → ¬(r < p + q' ∧ (k - 1) * p ≤ q') := by
  intro fuel
  induction fuel with
  | zero =>
    intro q q' hne h
    have : q' = q := by simpa [secondInner] using h.symm
    subst this; exact hne
  | succ fuel ih =>
    intro q q' hne h
    rw [secondInner] at h
    split at h
    · split at h
      · exact absurd h (by simp)
      · next hd => exact ih (q + 1) q' hd h
    · have : q' = q := by simpa using h.symm
      subst this; exact hne

/-- **`_second_period` が成功したときは、返す `p₂` が最小の第 2 周期**。 -/
theorem secondOuter_some (v : List α) (k p₁ r : ℕ) (hk : 3 ≤ k)
    (hleast : IsLeastKRep v k p₁) (hreach : HasPeriod (v.take r) p₁) (hrle : r ≤ v.length) :
    ∀ (fuel p q p₂ : ℕ), 0 < p →
      (p < v.length → p + q ≤ v.length ∧ HasPeriod (v.take (p + q)) p ∧
        ¬(r < p + q ∧ (k - 1) * p ≤ q)) →
      (∀ p', p' < p → ¬ Second v k r p') →
      secondOuter v k p₁ r fuel p q = some p₂ →
      Second v k r p₂ ∧ ∀ p', p' < p₂ → ¬ Second v k r p' := by
  have hp₁ : 0 < p₁ := hleast.1.1
  intro fuel
  induction fuel with
  | zero => intro p q p₂ _ _ _ h; exact absurd h (by simp [secondOuter])
  | succ fuel ih =>
    intro p q p₂ hp hinv hbelow h
    rw [secondOuter] at h
    split at h
    · next hg =>
      obtain ⟨hpq, hper, hne⟩ := hinv hg
      rcases hsi : secondInner v k p r (v.length + 1) q with _ | q'
      · simp only [hsi] at h
        rw [Option.some.injEq] at h
        subst h
        exact ⟨secondInner_second v k p r hk hp (v.length + 1) q hpq hper hsi, hbelow⟩
      · simp only [hsi] at h
        obtain ⟨hpq', hper', hne', hexit2⟩ :=
          secondInner_spec v k p r (v.length + 1) q (by omega) hpq hper hne q' hsi
        have hnp : ¬ Second v k r p := not_second_of_exit hk hp hper' hpq' hne' hexit2
        have hbelow' : ∀ p'', p'' ≤ p → ¬ Second v k r p'' := by
          intro p'' hp''
          rcases Nat.lt_or_ge p'' p with hlt | hge
          · exact hbelow p'' hlt
          · have hpp : p'' = p := by omega
            exact hpp ▸ hnp
        split at h
        · next hcase =>
          obtain ⟨hc1, hc2⟩ := hcase
          have hp₁q : p₁ ≤ q' := le_trans (Nat.le_mul_of_pos_left p₁ (by omega)) hc1
          refine ih (p + p₁) (q' - p₁) p₂ (by omega) ?_ ?_ h
          · intro _
            have heq : p + p₁ + (q' - p₁) = p + q' := by omega
            refine ⟨by omega, ?_, ?_⟩
            · rw [heq, hasPeriod_take_iff hpq']
              intro i hi
              have e1 : v[i]? = v[i + p₁]? :=
                (hasPeriod_take_iff hrle).mp hreach i (by omega)
              have e2 : v[i + p₁]? = v[i + p₁ + p]? :=
                (hasPeriod_take_iff hpq').mp hper' (i + p₁) (by omega)
              rw [e1, e2]
              exact getElem?_congr (by omega)
            · rw [heq]
              rintro ⟨hr1, hr2⟩
              have hq'lt : q' < (k - 1) * p := by
                by_contra hcon
                exact hne' ⟨hr1, by omega⟩
              have : (k - 1) * p ≤ (k - 1) * (p + p₁) := Nat.mul_le_mul_left _ (by omega)
              omega
          · intro p' hp'
            rcases Nat.lt_or_ge p' p with hlt | hge
            · exact hbelow p' hlt
            · rcases Nat.eq_or_lt_of_le hge with heq | hgt
              · exact heq ▸ hnp
              · exact no_second_between_period hk hp hleast hper' hpq' hc1 hbelow' p' hgt hp'
        · next hcase =>
          have hsp := shiftNoPeriod_pos q' k
          refine ih (p + shiftNoPeriod q' k) 0 p₂ (by omega) ?_ ?_ h
          · intro hlt
            refine ⟨by omega, ?_, ?_⟩
            · rw [hasPeriod_take_iff (by omega)]
              intro i hi; exact absurd hi (by omega)
            · have hpos : 0 < (k - 1) * (p + shiftNoPeriod q' k) :=
                Nat.mul_pos (by omega) (by omega)
              rintro ⟨-, h2⟩
              omega
          · intro p' hp'
            rcases Nat.lt_or_ge p' p with hlt | hge
            · exact hbelow p' hlt
            · rcases Nat.eq_or_lt_of_le hge with heq | hgt
              · exact heq ▸ hnp
              · exact no_second_between_shift hk hp hleast hper' hpq' hne' hcase hbelow'
                  p' hgt hp'
    · exact absurd h (by simp)

/-- 発見で終わった内側走査の仕事量は `max (r+1-p) ((k-1)*p)` 止まり
（返す `q` は条件が最初に成立する値なので）。 -/
theorem secondInnerWork_le_none (v : List α) (k p r : ℕ) :
    ∀ (fuel q : ℕ), ¬(r < p + q ∧ (k - 1) * p ≤ q) →
      secondInner v k p r fuel q = none →
      secondInnerWork v k p r fuel q + q ≤ max (r + 1 - p) ((k - 1) * p) + 1 := by
  intro fuel
  induction fuel with
  | zero => intro q _ h; exact absurd h (by simp [secondInner])
  | succ fuel ih =>
    intro q hne h
    rw [secondInner] at h
    rw [secondInnerWork]
    split at h
    · next hc =>
      rw [if_pos hc]
      split at h
      · next hfire =>
        rw [if_pos hfire]
        omega
      · next hd =>
        rw [if_neg hd]
        have := ih (q + 1) hd h
        omega
    · next hc =>
      exact absurd h (by simp)

/-- **`_second_period` が成功したときの仕事量は `O(k*p₂ + r)`**。 -/
theorem secondOuterWork_le_some (v : List α) (k first r : ℕ) (hk : 3 ≤ k) (hf : 0 < first) :
    ∀ (fuel p q p₂ : ℕ), 0 < p →
      (p < v.length → p + q ≤ v.length ∧ ¬(r < p + q ∧ (k - 1) * p ≤ q)) →
      secondOuter v k first r fuel p q = some p₂ →
      secondOuterWork v k first r fuel p q + ((k + 2) * p + q)
        ≤ (2 * k + 1) * p₂ + r + 3 := by
  intro fuel
  induction fuel with
  | zero => intro p q p₂ _ _ h; exact absurd h (by simp [secondOuter])
  | succ fuel ih =>
    intro p q p₂ hp hinv h
    rw [secondOuter] at h
    rw [secondOuterWork]
    split at h
    · next hg =>
      rw [if_pos hg]
      obtain ⟨hpq, hne⟩ := hinv hg
      rcases hsi : secondInner v k p r (v.length + 1) q with _ | q'
      · simp only [hsi] at h ⊢
        rw [Option.some.injEq] at h
        subst h
        have hw := secondInnerWork_le_none v k p r (v.length + 1) q hne hsi
        have e1 : (k - 1) * p + (k + 2) * p = (2 * k + 1) * p := by
          have h1 := Nat.sub_one_mul k p
          have h2 : p ≤ k * p := Nat.le_mul_of_pos_left p (by omega)
          have h3 : (2 * k + 1) * p = k * p + k * p + p := by ring
          have h4 : (k + 2) * p = k * p + 2 * p := by ring
          omega
        omega
      · simp only [hsi] at h ⊢
        have hw := secondInnerWork_le' v k p r (v.length + 1) q q' hsi
        have hne' := secondInner_exit v k p r (v.length + 1) q q' hne hsi
        obtain ⟨hq'ge, hq'le⟩ := secondInner_le v k p r (v.length + 1) q q' hpq hsi
        split at h
        · next hcase =>
          obtain ⟨hc1, hc2⟩ := hcase
          rw [if_pos ⟨hc1, hc2⟩]
          have hfq : first ≤ q' := le_trans (Nat.le_mul_of_pos_left first (by omega)) hc1
          have hrec := ih (p + first) (q' - first) p₂ (by omega) ?_ h
          · have hd : (k + 2) * (p + first) = (k + 2) * p + (k + 2) * first := by ring
            have hd2 : (k + 2) * first = k * first + 2 * first := by ring
            have hd3 : first ≤ k * first := Nat.le_mul_of_pos_left first (by omega)
            omega
          · intro _
            refine ⟨by omega, ?_⟩
            rintro ⟨hr1, hr2⟩
            have hq'lt : q' < (k - 1) * p := by
              by_contra hcon
              exact hne' ⟨by omega, by omega⟩
            have : (k - 1) * p ≤ (k - 1) * (p + first) := Nat.mul_le_mul_left _ (by omega)
            omega
        · next hcase =>
          rw [if_neg hcase]
          have hsp := shiftNoPeriod_pos q' k
          have hkm := le_mul_shiftNoPeriod q' k (by omega)
          have hrec := ih (p + shiftNoPeriod q' k) 0 p₂ (by omega) ?_ h
          · have hd : (k + 2) * (p + shiftNoPeriod q' k)
                = (k + 2) * p + (k * shiftNoPeriod q' k + 2 * shiftNoPeriod q' k) := by ring
            omega
          · intro hlt
            refine ⟨by omega, ?_⟩
            have hpos : 0 < (k - 1) * (p + shiftNoPeriod q' k) :=
              Nat.mul_pos (by omega) (by omega)
            rintro ⟨-, h2⟩
            omega
    · exact absurd h (by simp)

end Dec8

/-! ## 削除ループの不変条件と仕事量 -/

section Dec9

variable [DecidableEq α]

/-- 外側 1 反復ぶんの「これ以下の周期はもうない」の更新（`firstOuter` の共通部分）。 -/
theorem firstOuter_step_below (v : List α) (k : ℕ) (hk : 3 ≤ k) {p : ℕ} (hp : 0 < p)
    (hg1 : p < v.length)
    (hqne : firstInner v k p (v.length + 1) 0 ≠ (k - 1) * p)
    (hbelow : ∀ p', p' < p → ¬ KRep v k p') :
    ∀ p', p' < p + shiftNoPeriod (firstInner v k p (v.length + 1) 0) k → ¬ KRep v k p' := by
  have hstart : HasPeriod (v.take (p + 0)) p := by
    rw [hasPeriod_take_iff (by omega)]
    intro i hi; exact absurd hi (by omega)
  obtain ⟨-, hq2, hq3, hq4, hq5⟩ :=
    firstInner_spec v k p (v.length + 1) 0 (by omega) (by omega) (Nat.zero_le _) hstart
  have hqlt : firstInner v k p (v.length + 1) 0 < (k - 1) * p := by omega
  have hnp : ¬ KRep v k p := by
    rintro ⟨-, hlen, hper⟩
    have h1 := Nat.sub_one_mul k p
    have h2 : p ≤ k * p := Nat.le_mul_of_pos_left p (by omega)
    have hlt : p + firstInner v k p (v.length + 1) 0 < v.length := by omega
    have hmatch : v[firstInner v k p (v.length + 1) 0]?
        = v[p + firstInner v k p (v.length + 1) 0]? := by
      refine ((hasPeriod_take_iff hlen).mp hper _ (by omega)).trans ?_
      exact getElem?_congr (by omega)
    exact hq5 ⟨hlt, hqlt, hmatch⟩
  have hbelow' : ∀ p'', p'' ≤ p → ¬ KRep v k p'' := by
    intro p'' hp''
    rcases Nat.lt_or_ge p'' p with hlt | hge
    · exact hbelow p'' hlt
    · have hpp : p'' = p := by omega
      exact hpp ▸ hnp
  intro p' hp'
  rcases Nat.lt_or_ge p' p with hlt | hge
  · exact hbelow p' hlt
  · rcases Nat.eq_or_lt_of_le hge with heq | hgt
    · exact heq ▸ hnp
    · exact no_krep_between hk hp hq4 hq2 hqlt hbelow' p' hgt hp'

/-- **`bound` 付き `_first_period` が `none` を返したら、`bound` 未満の
`k`-繰り返し周期は存在しない**。削除ループの停止条件がこれ。 -/
theorem firstOuter_none_bnd (v : List α) (k bound : ℕ) (hk : 3 ≤ k) :
    ∀ (fuel p : ℕ), 0 < p → v.length ≤ fuel + p → (∀ p', p' < p → ¬ KRep v k p') →
      firstOuter v k bound fuel p = none → ∀ p', p' < bound → ¬ KRep v k p' := by
  have hexit : ∀ (p : ℕ), (v.length ≤ p ∨ bound ≤ p) → (∀ p', p' < p → ¬ KRep v k p') →
      ∀ p', p' < bound → ¬ KRep v k p' := by
    intro p hpl hbelow p' hp'
    rcases Nat.lt_or_ge p' p with hlt | hge
    · exact hbelow p' hlt
    · exact not_krep_of_length_le hk (by omega)
  intro fuel
  induction fuel with
  | zero => intro p hp hf hbelow _; exact hexit p (Or.inl (by omega)) hbelow
  | succ fuel ih =>
    intro p hp hf hbelow h
    rw [firstOuter] at h
    split at h
    · next hg =>
      obtain ⟨hg1, -⟩ := hg
      split at h
      · exact absurd h (by simp)
      · next hqne =>
        refine ih _ ?_ ?_ ?_ h
        · have := shiftNoPeriod_pos (firstInner v k p (v.length + 1) 0) k; omega
        · have := shiftNoPeriod_pos (firstInner v k p (v.length + 1) 0) k; omega
        · exact firstOuter_step_below v k hk hp hg1 hqne hbelow
    · next hg =>
      simp only [not_and] at hg
      exact hexit p (by omega) hbelow

/-- 削除ループは切断位置を後退させない。 -/
theorem stripLoop_ge (x : List α) (k bound : ℕ) :
    ∀ (fuel s : ℕ), s ≤ stripLoop x k bound fuel s := by
  intro fuel
  induction fuel with
  | zero => intro s; exact le_refl _
  | succ fuel ih =>
    intro s
    rw [stripLoop]
    rcases hfo : firstOuter (x.drop s) k bound (x.length + 1) 1 with _ | ⟨p, m⟩
    · simp only []
      exact le_refl _
    · simp only []
      exact le_trans (Nat.le_add_right s p) (ih (s + p))

/-- **削除ループの停止不変条件**：終了後の接尾辞には `bound` 未満の
`k`-繰り返し周期がない。これが次のパスの最小周期 `p₁' ≥ p₂` を与える。 -/
theorem stripLoop_spec (x : List α) (k bound : ℕ) (hk : 3 ≤ k) :
    ∀ (fuel s : ℕ), s ≤ x.length → x.length ≤ fuel + s →
      ∀ p', p' < bound → ¬ KRep (x.drop (stripLoop x k bound fuel s)) k p' := by
  intro fuel
  induction fuel with
  | zero =>
    intro s hs hf p' hp'
    have hsx : s = x.length := by omega
    have hnil : x.drop (stripLoop x k bound 0 s) = ([] : List α) := by
      show x.drop s = []
      rw [hsx]; simp
    rw [hnil]
    exact not_krep_nil (by omega)
  | succ fuel ih =>
    intro s hs hf p' hp'
    have hvlen : (x.drop s).length = x.length - s := by simp
    rw [stripLoop]
    rcases hfo : firstOuter (x.drop s) k bound (x.length + 1) 1 with _ | ⟨p, m⟩
    · simp only []
      exact firstOuter_none_bnd (x.drop s) k bound hk (x.length + 1) 1 (by omega) (by omega)
        (by intro p'' h''; rintro ⟨h1, -, -⟩; omega) hfo p' hp'
    · simp only []
      have hlt := firstOuter_lt (x.drop s) k bound (x.length + 1) 1 p m (by omega) hfo
      exact ih (s + p) (by omega) (by omega) p' hp'

/-- **削除ループの仕事量**：進めた量に比例した分と、最後の失敗する走査 `O(k*bound)` のみ。 -/
theorem stripLoopWork_le (x : List α) (k bound : ℕ) (hk : 3 ≤ k) :
    ∀ (fuel s : ℕ),
      stripLoopWork x k bound fuel s
        ≤ (2 * k + 3) * (stripLoop x k bound fuel s - s) + (k + 2) * (2 * bound + 1) := by
  intro fuel
  induction fuel with
  | zero => intro s; simp only [stripLoopWork]; omega
  | succ fuel ih =>
    intro s
    rw [stripLoopWork, stripLoop]
    rcases hfo : firstOuter (x.drop s) k bound (x.length + 1) 1 with _ | ⟨p, m⟩
    · simp only []
      have hmin := firstOuterWork_le_min (x.drop s) k bound hk (x.length + 1) 1 (by omega)
        (by omega)
      have hmul : (k + 2) * (2 * min bound (x.drop s).length + 1)
          ≤ (k + 2) * (2 * bound + 1) :=
        Nat.mul_le_mul_left _ (by have := min_le_left bound (x.drop s).length; omega)
      omega
    · simp only []
      have hw := firstOuterWork_le_some (x.drop s) k bound hk (x.length + 1) 1 p m
        (by omega) hfo
      have hlt := firstOuter_lt (x.drop s) k bound (x.length + 1) 1 p m (by omega) hfo
      have hrec := ih (s + p)
      have hmono := stripLoop_ge x k bound fuel (s + p)
      have hd : (2 * k + 3) * (stripLoop x k bound fuel (s + p) - s)
          = (2 * k + 3) * (stripLoop x k bound fuel (s + p) - (s + p)) + (2 * k + 3) * p := by
        rw [← Nat.mul_add]; congr 1; omega
      have hd2 : (2 * k + 3) * p = (2 * k + 1) * p + 2 * p := by ring
      omega

end Dec9

/-! ## パス間の成長（幾何級数） -/

/-- 第 2 周期は `k`-繰り返し周期でもある。 -/
theorem kRep_of_second {v : List α} {k r p : ℕ} (hs : Second v k r p) : KRep v k p := by
  obtain ⟨hp, hlen, hper⟩ := hs
  exact ⟨hp, le_trans (le_max_left _ _) hlen, hasPeriod_take_of_le hper (le_max_left _ _)⟩

/-- 到達域 `r` を持つ最小周期 `p₁` 自身は第 2 周期になれない。 -/
theorem not_second_reach {v : List α} {k r p₁ : ℕ} (hR : ReachOf v p₁ r) :
    ¬ Second v k r p₁ := by
  rintro ⟨hp, hlen, hper⟩
  obtain ⟨hrle, hrper, hmax⟩ := hR
  have h1 : r + 1 ≤ max (k * p₁) (r + 1) := le_max_right _ _
  have hne : HasPeriod (v.take (r + 1)) p₁ := hasPeriod_take_of_le hper h1
  rcases hmax with heq | hno
  · omega
  · exact hno hne

/-- **最小の第 2 周期の根は原始的（basic）**。`IsLeastKRep.primitive` の第 2 周期版で、
GS の重なり補題 `kRepetition_periods` を適用するために必要。 -/
theorem second_primitive_of_least {v : List α} {k r p₂ : ℕ} (hk : 0 < k)
    (hs : Second v k r p₂) (hmin : ∀ p', p' < p₂ → ¬ Second v k r p') :
    Primitive (v.take p₂) := by
  obtain ⟨hp₂, hlen, hper⟩ := hs
  have hkm : k * p₂ ≤ max (k * p₂) (r + 1) := le_max_left _ _
  have hple : p₂ ≤ k * p₂ := Nat.le_mul_of_pos_left p₂ hk
  have htlen : (v.take p₂).length = p₂ := by simp only [List.length_take]; omega
  intro z n hzn
  by_contra hn
  have hzl : n * z.length = p₂ := by
    have hc := congrArg List.length hzn
    rw [htlen, length_wpow] at hc
    omega
  have hn0 : n ≠ 0 := by rintro rfl; rw [Nat.zero_mul] at hzl; omega
  have hn2 : 2 ≤ n := by omega
  have hzpos : 0 < z.length := by
    rcases Nat.eq_zero_or_pos z.length with h | h
    · rw [h, Nat.mul_zero] at hzl; omega
    · exact h
  have hzlt : z.length < p₂ := by
    have : 2 * z.length ≤ n * z.length := Nat.mul_le_mul_right _ hn2
    omega
  have hpre : HasPeriod (v.take p₂) z.length := by rw [hzn]; exact hasPeriod_wpow z n
  have hdvd : z.length ∣ p₂ := ⟨n, by rw [← hzl]; exact Nat.mul_comm n z.length⟩
  have htt : (v.take (max (k * p₂) (r + 1))).take p₂ = v.take p₂ := by
    rw [List.take_take]; congr 1; omega
  have hall : HasPeriod (v.take (max (k * p₂) (r + 1))) z.length :=
    hasPeriod_of_prefix_dvd hper hp₂ hdvd (by rw [htt]; exact hpre)
  have hgm : max (k * z.length) (r + 1) ≤ max (k * p₂) (r + 1) :=
    max_le (le_trans (Nat.mul_le_mul_left k (by omega)) hkm) (le_max_right _ _)
  exact hmin z.length hzlt ⟨hzpos, le_trans hgm hlen, hasPeriod_take_of_le hall hgm⟩

section Dec10

variable [DecidableEq α]

/-- **外側 1 反復の鋭い仕事量**（第 2 周期が見つかる＝最後のパスでない場合）：
`O(k*p₁ + k*p₂ + r)`。`|v|` には依存しない。 -/
theorem decomposeStepWork_le_sharp (x : List α) (k s : ℕ) (hk : 3 ≤ k) {p₁ p₂ : ℕ}
    (hfp : firstPeriod (x.drop s) k = some (p₁, k * p₁))
    (hsp : secondPeriod (x.drop s) k p₁ (extendReach (x.drop s) p₁ (x.length + 1) (k * p₁))
             = some p₂) :
    decomposeStepWork x k s
      ≤ (2 * k + 1) * p₁ + (2 * k + 1) * p₂
        + 2 * extendReach (x.drop s) p₁ (x.length + 1) (k * p₁) + 6 := by
  have hp₁ : 0 < p₁ :=
    (firstOuter_lt (x.drop s) k (x.drop s).length ((x.drop s).length + 1) 1 p₁ (k * p₁)
      (by omega) hfp).1
  have h1 := firstOuterWork_le_some (x.drop s) k (x.drop s).length hk
    ((x.drop s).length + 1) 1 p₁ (k * p₁) (by omega) hfp
  have h2 := extendReachWork_le' (x.drop s) p₁ (x.length + 1) (k * p₁)
  have h3 := secondOuterWork_le_some (x.drop s) k p₁
    (extendReach (x.drop s) p₁ (x.length + 1) (k * p₁)) hk hp₁
    ((x.drop s).length + 1) 1 0 p₂ (by omega) ?_ hsp
  · have key : decomposeStepWork x k s
        = firstOuterWork (x.drop s) k (x.drop s).length ((x.drop s).length + 1) 1
          + (extendReachWork (x.drop s) p₁ (x.length + 1) (k * p₁)
            + secondOuterWork (x.drop s) k p₁
                (extendReach (x.drop s) p₁ (x.length + 1) (k * p₁))
                ((x.drop s).length + 1) 1 0) := by
      unfold decomposeStepWork; rw [hfp]
    rw [key]
    omega
  · intro hlt
    refine ⟨by omega, ?_⟩
    rintro ⟨-, h4⟩
    rw [Nat.mul_one] at h4
    omega

/-- **`decomposeLoop` の大域的な線形仕事量**。

不変条件 `∀ p' < b, ¬ KRep (x.drop s) k p'`（削除ループが保証する）のもとで、
残りのパス全体の仕事は `A*b` を引いた分しかかからない（`A = 11k+27`）。
各パスは `O(k*p₂)` の仕事をし、次のパスの下界は `b' = p₂ ≥ (k-1)*p₁ ≥ 3*b` なので
`A*b` の項が幾何級数を吸収する。 -/
theorem decomposeLoopWork_le (x : List α) (k : ℕ) (hk : 4 ≤ k) :
    ∀ (fuel s b : ℕ), s ≤ x.length → 0 < b → b ≤ x.length + 1 →
      (∀ p', p' < b → ¬ KRep (x.drop s) k p') →
      decomposeLoopWork x k fuel s + (11 * k + 27) * b
        ≤ (11 * k + 27) * (x.length + 1) + (2 * k + 3) * (x.length - s)
          + ((3 * k + 8) * x.length + (2 * k + 5)) := by
  intro fuel
  induction fuel with
  | zero =>
    intro s b hs hb hbx _
    have hmulb : (11 * k + 27) * b ≤ (11 * k + 27) * (x.length + 1) :=
      Nat.mul_le_mul_left _ hbx
    simp only [decomposeLoopWork]
    omega
  | succ fuel ih =>
    intro s b hs hb hbx hbelow
    have hmulb : (11 * k + 27) * b ≤ (11 * k + 27) * (x.length + 1) :=
      Nat.mul_le_mul_left _ hbx
    have hstep := decomposeStepWork_le x k s (by omega) hs
    have hvlen : (x.drop s).length = x.length - s := by simp
    rw [decomposeLoopWork]
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
        -- 記号を固定
        set r := extendReach (x.drop s) p₁ (x.length + 1) (k * p₁) with hrdef
        -- `p₂` は最小の第 2 周期
        obtain ⟨hsecond, hsecmin⟩ :=
          secondOuter_some (x.drop s) k p₁ r (by omega) hleast hreach.2.1 hreach.1
            ((x.drop s).length + 1) 1 0 p₂ (by omega)
            (by
              intro hlt
              refine ⟨by omega, ?_, ?_⟩
              · rw [hasPeriod_take_iff (by omega)]
                intro i hi; exact absurd hi (by omega)
              · rintro ⟨-, h4⟩
                rw [Nat.mul_one] at h4
                omega)
            (by intro p' hp'; rintro ⟨h4, -, -⟩; omega) hsp
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
        have hkp₂ : k * p₂ ≤ (x.drop s).length := hkrep₂.2.1
        have hp₂x : p₂ ≤ x.length + 1 := by
          have : p₂ ≤ k * p₂ := Nat.le_mul_of_pos_left p₂ (by omega)
          omega
        -- 削除ループ
        have hs'ge := stripLoop_ge x k p₂ (x.length + 1) s
        have hs'le := stripLoop_le x k p₂ (x.length + 1) s hs
        have hstrip := stripLoopWork_le x k p₂ (by omega) (x.length + 1) s
        have hnext := stripLoop_spec x k p₂ (by omega) (x.length + 1) s hs (by omega)
        -- 帰納法の仮定
        have hrec := ih (stripLoop x k p₂ (x.length + 1) s) p₂ hs'le (by omega) hp₂x hnext
        -- 鋭いパス評価
        have hsharp := decomposeStepWork_le_sharp x k s (by omega) hfp hsp
        -- 算術
        have htel : (2 * k + 3) * (x.length - s)
            = (2 * k + 3) * (stripLoop x k p₂ (x.length + 1) s - s)
              + (2 * k + 3) * (x.length - stripLoop x k p₂ (x.length + 1) s) := by
          rw [← Nat.mul_add]; congr 1; omega
        have e0 : (k + 2) * (2 * p₂ + 1) = (2 * k + 4) * p₂ + (k + 2) := by ring
        have e1 : (2 * k + 1) * p₁ ≤ (2 * k + 1) * p₂ := Nat.mul_le_mul_left _ hle₁₂
        have e2 : p₁ ≤ p₂ := hle₁₂
        have e3 : (k + 2) ≤ (k + 2) * p₂ := Nat.le_mul_of_pos_right _ (by omega)
        have e4 : 6 ≤ 6 * p₂ := Nat.le_mul_of_pos_right _ (by omega)
        -- パス費用 ≤ (7k+16) * p₂
        have hpass : decomposeStepWork x k s + (k + 2) * (2 * p₂ + 1)
            ≤ (7 * k + 18) * p₂ := by
          have f1 : (2 * k + 1) * p₂ + (2 * k + 1) * p₂ + 2 * p₁ + 2 * p₂
              + (2 * k + 4) * p₂ + (k + 2) * p₂ + 6 * p₂ ≤ (7 * k + 18) * p₂ := by
            have g1 : 2 * p₁ ≤ 2 * p₂ := by omega
            have g2 : (2 * k + 1) * p₂ + (2 * k + 1) * p₂ + 2 * p₂ + 2 * p₂
                + (2 * k + 4) * p₂ + (k + 2) * p₂ + 6 * p₂ = (7 * k + 18) * p₂ := by ring
            omega
          omega
        -- 幾何級数：(7k+16)*p₂ + A*b ≤ A*p₂
        have hgeo : (7 * k + 18) * p₂ + (11 * k + 27) * b ≤ (11 * k + 27) * p₂ := by
          have g1 : (11 * k + 27) * (3 * b) ≤ (11 * k + 27) * p₂ :=
            Nat.mul_le_mul_left _ h3b
          have g2 : (11 * k + 27) * (3 * b) = 3 * ((11 * k + 27) * b) := by ring
          have g3 : 3 * ((7 * k + 18) * p₂) + (11 * k + 27) * p₂ = (32 * k + 81) * p₂ := by
            ring
          have g4 : 3 * ((11 * k + 27) * p₂) = (33 * k + 81) * p₂ := by ring
          have g5 : (32 * k + 81) * p₂ ≤ (33 * k + 81) * p₂ :=
            Nat.mul_le_mul_right p₂ (by omega)
          omega
        omega

/-- **主定理（大域的な線形仕事量）**：GS 前処理の総仕事量は入力長の線形。
`C = 16k+38`, `D = 2k+5`。 -/
theorem decomposeWork_le (x : List α) (k : ℕ) (hk : 4 ≤ k) :
    decomposeWork x k ≤ (16 * k + 38) * x.length + (2 * k + 5) := by
  have h := decomposeLoopWork_le x k hk (x.length + 1) 0 1 (Nat.zero_le _) (by omega)
    (by omega) (by intro p' hp'; rintro ⟨h1, -, -⟩; omega)
  have e1 : (11 * k + 27) * (x.length + 1) = (11 * k + 27) * x.length + (11 * k + 27) := by
    ring
  have e2 : (11 * k + 27) * x.length + (2 * k + 3) * x.length + (3 * k + 8) * x.length
      = (16 * k + 38) * x.length := by ring
  have e3 : (11 * k + 27) * 1 = 11 * k + 27 := by ring
  simp only [decomposeWork, Nat.sub_zero] at h ⊢
  omega

end Dec10

/-! ## 仕事量の小例と、大域的な線形性

`decomposeWork` は「どのループでも 1 反復 = 1 単位」で数える。1 反復は高々 1 回の記号比較と
定数個の添字更新なので、このカウンタは比較回数もずらし回数も同時に押さえる
（`gs_overlap.Meter` は `comparisons` と `events` を別々に数えるので値は一致しないが、
同じ定数倍の粒度）。

**主結果**（`decomposeWork_le`, `4 ≤ k`）：

```
decomposeWork x k ≤ (16k+38) * |x| + (2k+5)
```

証明は GS 1983 の償却解析をそのまま辿る。走査の局所評価はすべてポテンシャル
`Φ = (k+2)*p + q`（`GSScan.Phi` と同じ）による：

* `firstOuterWork_le_some`：`_first_period` は最小の `k`-繰り返し周期 `p₁` を見つけた
  時点で止まるので、仕事は `|v|` ではなく `(2k+1)*p₁ + 2` で押さえられる。
* `extendReachWork_le'`：`reach` 伸長の仕事はちょうど伸ばした量 + 1。
* `secondOuterWork_le_some`：`_second_period` は第 2 周期 `p₂` を見つけた時点で止まり、
  そのときの `q` は「条件が最初に成立する値」なので `max (r+1-p₂) ((k-1)*p₂)` 止まり。
  よって仕事は `(2k+1)*p₂ + r + 3`。
* `firstOuterWork_le_min`：`bound` 付き走査では候補周期が 1 反復で高々 2 倍にしか
  ならない（`shiftNoPeriod_le_of_le_mul`）ので、仕事は `(k+2)*(2*min bound |v| + 1)`。
* `stripLoopWork_le`：削除ループの各成功反復の仕事は見つけた周期 `p`（＝切断の前進量）に
  比例するので、`(2k+3)*Δs` に償却できる。最後の失敗する走査だけが `O(k*p₂)`。

パス間の成長（幾何級数）に必要だった構造的事実：

* `stripLoop_spec`：削除ループは `firstOuter (·, bound := p₂) = none` で止まるので、
  終了後の接尾辞には `p₂` 未満の `k`-繰り返し周期が**存在しない**
  （`firstOuter_none_bnd`）。したがって次のパスの最小周期は `p₁' ≥ p₂`。
  ——「次のパスの最小周期 ≥ p₂」を保証しているのは、まさにこの削除ループの停止条件である。
* `secondOuter_some`：`_second_period` の返す `p₂` は**最小の**第 2 周期。
* `second_primitive_of_least`：最小の第 2 周期の根 `v.take p₂` は原始的
  （`IsLeastKRep.primitive` の第 2 周期版）。これがないと重なり補題を使えない。
* `GSDecomp.kRepetition_periods`：ゆえに `(k-1)*p₁ ≤ p₂`。
* `GSDecomp.reach_lt_add_of_second`：ゆえに `r < p₁ + p₂`。

これらから 1 パスの仕事（削除の前進量に比例する分を除く）は `(7k+18)*p₂` で押さえられ、
不変条件の下界 `b` は `3*b ≤ (k-1)*p₁ ≤ p₂` を満たすので、ポテンシャル `(11k+27)*b` が
幾何級数を吸収する（`decomposeLoopWork_le`）。最後のパスだけは `O(k*|x|)` かかりうるが
（`decomposeStepWork_le`）、1 回しか起きないので線形性を壊さない。

なお `GSDecomp.GSDecomp`（L1 の切断上界 `(k-1)*s < |x|`, `(k-2)*s < (k-1)*p₁`）は
ここでも証明していない。上の議論はそれを経由せず、削除ループの停止条件と第 2 周期の
幾何級数だけで線形性を出している。 -/

section WorkExamples

/-- `decompose("000000001", 8)` は 1 反復で終わり、仕事量は 54。 -/
example : decomposeWork ([0,0,0,0,0,0,0,0,1] : List ℕ) 8 = 54 := by decide

example : decomposeStepWork ([0,0,0,0,0,0,0,0,1] : List ℕ) 8 0 = 54 := by decide

/-- 線形上界の実例（`k = 8`, `|x| = 9`：`(3k+8)|x| + (2k+5) = 309`）。 -/
example : decomposeStepWork ([0,0,0,0,0,0,0,0,1] : List ℕ) 8 0 ≤ (3 * 8 + 8) * 9 + (2 * 8 + 5) := by
  decide

/-- 削除ループが動く例（`k = 4`）：外側 1 反復ぶんは 36、全体は 123。 -/
example : decomposeStepWork ([0,0,0,0,1,0,0,0,0,1,0,0,0,0,1,0,0,0,0,1] : List ℕ) 4 0 = 36 := by
  decide

example : decomposeWork ([0,0,0,0,1,0,0,0,0,1,0,0,0,0,1,0,0,0,0,1] : List ℕ) 4 = 123 := by decide

/-- 大域的な線形上界の実例（`k = 8`, `|x| = 9`：`(16k+38)|x| + (2k+5) = 1515`）。 -/
example : decomposeWork ([0,0,0,0,0,0,0,0,1] : List ℕ) 8
    ≤ (16 * 8 + 38) * 9 + (2 * 8 + 5) := by decide

/-- 削除ループが動く例でも同様（`k = 4`, `|x| = 20`：`(16k+38)|x| + (2k+5) = 2053`）。 -/
example : decomposeWork ([0,0,0,0,1,0,0,0,0,1,0,0,0,0,1,0,0,0,0,1] : List ℕ) 4
    ≤ (16 * 4 + 38) * 20 + (2 * 4 + 5) := by decide

end WorkExamples


end PalPeg
