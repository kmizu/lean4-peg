import PalPeg.Manacher
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Manacher 走査のヘッド移動量（多テープ TM 上での線形時間実行）

`PalPeg.Manacher.run` の走査を、逐次アクセスのテープ上で実行することを想定して
3 本のヘッド位置を付随させ、その総移動量が入力長に対して線形であることを示す。

* `hR`（入力テープ右ヘッド）: 中心 `i` の展開で `x[i + r]` を読む。位置は
  `max` で単調増加し、総移動量は `≤ x.length`（かつ `≤ 2n`）。
* `hL`（入力テープ左ヘッド）: 中心 `i` の展開で `x[i - r₀ - 1], …, x[i - rad x i]`
  を読む。ステップ内の移動量は「再配置距離 + 走査距離」。
* `hM`（半径テープの鏡ヘッド）: `i < R` のとき `acc[2c - i]` を読む。同じ中心の
  支配下では 1 ステップ 1 マス左へ、中心が変わると `i - 1` へ跳ぶ。

主定理は `moveR_total`, `moveM_total`, `moveL_total` とその全走査版
`moveR_total_run`, `moveM_total_run`, `moveL_total_run`, `headMove_total_run`。
-/

namespace PalPeg
namespace Manacher

universe u
variable {α : Type u} [DecidableEq α]

/-! ## テープ上の距離 -/

/-- ヘッドの移動距離（`ℕ` 上の対称差）。 -/
def headDist (a b : ℕ) : ℕ := (a - b) + (b - a)

theorem headDist_self (a : ℕ) : headDist a a = 0 := by simp [headDist]

/-! ## 種半径 `seed`（`step` の `r₀`） -/

/-- 中心 `i` を処理する直前の状態から決まる種半径。`step` の局所束縛 `r₀` と一致する。 -/
def seed (x : List α) (i : ℕ) : ℕ :=
  if i < (run x i).R then
    min ((run x i).acc.getD (2 * (run x i).c - i) 0) ((run x i).R - i)
  else 0

theorem seed_eq_zero {x : List α} {i : ℕ} (h : (run x i).R ≤ i) : seed x i = 0 := by
  rw [seed, if_neg (by omega)]

theorem seed_le_frontier {x : List α} {i : ℕ} (h : i < (run x i).R) :
    seed x i ≤ (run x i).R - i := by
  rw [seed, if_pos h]; exact min_le_right _ _

/-- 種半径は本当に回文半径（`inv_run` の内部補題の再構成）。 -/
theorem palAt_seed {x : List α} {i : ℕ} (hi : i < x.length) : PalAt x i (seed x i) := by
  obtain ⟨-, hget, -, -, hcR⟩ := inv_run (x := x) i (le_of_lt hi)
  rw [seed]
  split
  · next hlt =>
    obtain ⟨hci, hRc, hcn⟩ := hcR hlt
    have hj : 2 * (run x i).c - i < i := by omega
    rw [hget _ hj, hRc]
    have hmin := rad_mirror_ge (x := x) (c := (run x i).c) (i := i) hcn (by omega) (by omega)
    exact (palAt_rad hi).mono hmin
  · exact palAt_zero hi

theorem seed_le_rad {x : List α} {i : ℕ} (hi : i < x.length) : seed x i ≤ rad x i :=
  le_rad (palAt_seed hi)

theorem expand_seed_eq {x : List α} {i : ℕ} (hi : i < x.length) :
    expand x i (seed x i) = rad x i := expand_eq (palAt_seed hi)

/-- 種が右端に届いているか、半径が種のまま（展開なし）か。 -/
theorem seed_key {x : List α} {i : ℕ} (hi : i < x.length) (hlt : i < (run x i).R) :
    seed x i = (run x i).R - i ∨ rad x i = seed x i := by
  obtain ⟨-, hget, -, -, hcR⟩ := inv_run (x := x) i (le_of_lt hi)
  obtain ⟨hci, hRc, hcn⟩ := hcR hlt
  have hj : 2 * (run x i).c - i < i := by omega
  have hs : seed x i = min (rad x (2 * (run x i).c - i)) ((run x i).R - i) := by
    rw [seed, if_pos hlt, hget _ hj]
  rcases Nat.lt_or_ge (rad x (2 * (run x i).c - i)) ((run x i).R - i) with h | h
  · right
    rw [hs, min_eq_left (le_of_lt h)]
    exact rad_mirror_eq hcn (by omega) (by omega) (by omega)
  · left; rw [hs, min_eq_right h]

/-! ## `run` の成分の漸化式 -/

theorem run_succ_c_raw (x : List α) (i : ℕ) :
    (run x (i + 1)).c = if (run x i).R < i + expand x i (seed x i) then i else (run x i).c := rfl

theorem run_succ_R_raw (x : List α) (i : ℕ) :
    (run x (i + 1)).R =
      if (run x i).R < i + expand x i (seed x i) then i + expand x i (seed x i)
      else (run x i).R := rfl

theorem run_succ_w_raw (x : List α) (i : ℕ) :
    (run x (i + 1)).w = (run x i).w + (expand x i (seed x i) - seed x i) := rfl

theorem cen_succ {x : List α} {i : ℕ} (hi : i < x.length) :
    (run x (i + 1)).c = if (run x i).R < i + rad x i then i else (run x i).c := by
  rw [run_succ_c_raw, expand_seed_eq hi]

theorem rht_succ {x : List α} {i : ℕ} (hi : i < x.length) :
    (run x (i + 1)).R = if (run x i).R < i + rad x i then i + rad x i else (run x i).R := by
  rw [run_succ_R_raw, expand_seed_eq hi]

theorem wrk_succ {x : List α} {i : ℕ} (hi : i < x.length) :
    (run x (i + 1)).w = (run x i).w + (rad x i - seed x i) := by
  rw [run_succ_w_raw, expand_seed_eq hi]

theorem run_zero_c (x : List α) : (run x 0).c = 0 := rfl
theorem run_zero_R (x : List α) : (run x 0).R = 0 := rfl
theorem run_zero_w (x : List α) : (run x 0).w = 0 := rfl

theorem rad_zero (x : List α) : rad x 0 = 0 := Nat.le_zero.mp rad_le_center

/-- 中心は添字を超えない。 -/
theorem cen_le {x : List α} : ∀ i, i ≤ x.length → (run x i).c ≤ i := by
  intro i
  induction i with
  | zero => intro _; simp [run_zero_c]
  | succ i ih =>
    intro hi
    have h := ih (by omega)
    rw [cen_succ (x := x) (i := i) (by omega)]
    split <;> omega

/-- 右端は常に「現在の中心の回文の右端」。 -/
theorem rht_eq_cen_add_rad {x : List α} :
    ∀ i, i ≤ x.length → (run x i).R = (run x i).c + rad x (run x i).c := by
  intro i
  induction i with
  | zero => intro _; simp [run_zero_c, run_zero_R, rad_zero]
  | succ i ih =>
    intro hi
    have h := ih (by omega)
    rw [cen_succ (x := x) (i := i) (by omega), rht_succ (x := x) (i := i) (by omega)]
    split
    · rfl
    · exact h

theorem rht_le_two_cen {x : List α} {i : ℕ} (hi : i ≤ x.length) :
    (run x i).R ≤ 2 * (run x i).c := by
  have h := rht_eq_cen_add_rad (x := x) i hi
  have h2 : rad x (run x i).c ≤ (run x i).c := rad_le_center
  omega

theorem cen_mono {x : List α} {i : ℕ} (hi : i < x.length) :
    (run x i).c ≤ (run x (i + 1)).c := by
  have h := cen_le (x := x) i (by omega)
  rw [cen_succ hi]; split <;> omega

/-! ## 展開が起きるステップ -/

/-- 展開（`seed < rad`）が起きたら、必ず中心が更新される。 -/
theorem change_of_expand {x : List α} {i : ℕ} (hi : i < x.length) (he : seed x i < rad x i) :
    (run x i).R < i + rad x i := by
  rcases Nat.lt_or_ge i (run x i).R with h | h
  · rcases seed_key hi h with hk | hk
    · omega
    · omega
  · have := seed_eq_zero (x := x) (i := i) h; omega

/-- 展開なしで中心が更新される場合は、半径 `0` の空回文で右端も `i` に落ちている。 -/
theorem no_expand_change {x : List α} {i : ℕ} (hi : i < x.length) (he : ¬ seed x i < rad x i)
    (hch : (run x i).R < i + rad x i) : rad x i = 0 ∧ (run x i).R ≤ i := by
  have hle := seed_le_rad hi
  have heq : seed x i = rad x i := by omega
  rcases Nat.lt_or_ge i (run x i).R with h | h
  · have := seed_le_frontier (x := x) (i := i) h; omega
  · have := seed_eq_zero (x := x) (i := i) h; omega

/-! ## 3 本のヘッド -/

/-- 右ヘッド（入力テープ）の位置：`max` で単調に前進する。 -/
def hR (x : List α) : ℕ → ℕ
  | 0 => 0
  | i + 1 => max (hR x i) (i + rad x i)

/-- 直近に展開が起きた中心（まだ無ければ `0`）。 -/
def lastExp (x : List α) : ℕ → ℕ
  | 0 => 0
  | i + 1 => if seed x i < rad x i then i else lastExp x i

/-- 左ヘッド（入力テープ）の位置：直近の展開が到達した左端。 -/
def hL (x : List α) (i : ℕ) : ℕ := lastExp x i - rad x (lastExp x i)

/-- 鏡ヘッド（半径テープ）が中心 `i` の処理時に参照する位置。 -/
def hM (x : List α) (i : ℕ) : ℕ := 2 * (run x i).c - i

/-- ステップ `i` における右ヘッドの移動量。 -/
def moveR (x : List α) (i : ℕ) : ℕ := hR x (i + 1) - hR x i

/-- ステップ `i` における鏡ヘッドの移動量（次の参照位置までの再配置）。 -/
def moveM (x : List α) (i : ℕ) : ℕ := headDist (hM x i) (hM x (i + 1))

/-- ステップ `i` における左ヘッドの移動量：
展開が起きるときのみ、「`i - r₀ - 1` への再配置」＋「`rad x i - r₀` の走査」。 -/
def moveL (x : List α) (i : ℕ) : ℕ :=
  if seed x i < rad x i then
    headDist (hL x i) (i - seed x i - 1) + (rad x i - seed x i)
  else 0

/-! ### 右ヘッド -/

theorem hR_le_succ (x : List α) (i : ℕ) : hR x i ≤ hR x (i + 1) := by
  simp only [hR]; omega

theorem hR_eq_rht {x : List α} : ∀ i, i ≤ x.length → hR x i = (run x i).R := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro hi
    have h := ih (by omega)
    rw [hR, h, rht_succ (x := x) (i := i) (by omega)]
    split <;> omega

theorem moveR_sum (x : List α) : ∀ n, ∑ i ∈ Finset.range n, moveR x i = hR x n := by
  intro n
  induction n with
  | zero => simp [hR]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have := hR_le_succ x n
    simp only [moveR]
    omega

/-! ### `lastExp` と左ヘッドの不変条件 -/

theorem lastExp_le (x : List α) : ∀ i, lastExp x i ≤ i := by
  intro i
  induction i with
  | zero => simp [lastExp]
  | succ i ih => rw [lastExp]; split <;> omega

theorem lastExp_lt (x : List α) {i : ℕ} (hi : 0 < i) : lastExp x i < i := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have := lastExp_le x k
  rw [lastExp]; split <;> omega

theorem lastExp_mono (x : List α) (i : ℕ) : lastExp x i ≤ lastExp x (i + 1) := by
  have := lastExp_le x i
  rw [lastExp]; split <;> omega

theorem hL_le_lastExp (x : List α) (i : ℕ) : hL x i ≤ lastExp x i := by
  simp only [hL]; omega

/-- 左ヘッドは現在の中心の回文の左端より右にはみ出さない。 -/
theorem hL_add_rht_le {x : List α} :
    ∀ i, i ≤ x.length → hL x i + (run x i).R ≤ 2 * (run x i).c := by
  intro i
  induction i with
  | zero => intro _; simp [hL, lastExp, run_zero_R, run_zero_c]
  | succ i ih =>
    intro hi
    have hix : i < x.length := by omega
    have hrad : rad x i ≤ i := rad_le_center
    by_cases he : seed x i < rad x i
    · have hch := change_of_expand hix he
      have hlast : lastExp x (i + 1) = i := by rw [lastExp, if_pos he]
      rw [cen_succ hix, rht_succ hix, if_pos hch, if_pos hch]
      simp only [hL, hlast]
      omega
    · have hlast : lastExp x (i + 1) = lastExp x i := by rw [lastExp, if_neg he]
      have hLi : hL x i ≤ i := le_trans (hL_le_lastExp x i) (lastExp_le x i)
      rw [cen_succ hix, rht_succ hix]
      simp only [hL, hlast]
      by_cases hch : (run x i).R < i + rad x i
      · obtain ⟨h0, hRi⟩ := no_expand_change hix he hch
        rw [if_pos hch, if_pos hch]
        simp only [hL] at hLi
        omega
      · rw [if_neg hch, if_neg hch]
        have := ih (by omega)
        simp only [hL] at this
        omega

/-- 左ヘッドは「直近の展開中心の回文の左端」であり、右端 `R` より左には行かない。 -/
theorem two_lastExp_le {x : List α} :
    ∀ i, i ≤ x.length → 2 * lastExp x i ≤ hL x i + (run x i).R := by
  intro i
  induction i with
  | zero => intro _; simp [hL, lastExp, run_zero_R]
  | succ i ih =>
    intro hi
    have hix : i < x.length := by omega
    have hrad : rad x i ≤ i := rad_le_center
    by_cases he : seed x i < rad x i
    · have hch := change_of_expand hix he
      have hlast : lastExp x (i + 1) = i := by rw [lastExp, if_pos he]
      rw [rht_succ hix, if_pos hch]
      simp only [hL, hlast]
      omega
    · have hlast : lastExp x (i + 1) = lastExp x i := by rw [lastExp, if_neg he]
      have h := ih (by omega)
      rw [rht_succ hix]
      simp only [hL, hlast]
      simp only [hL] at h
      by_cases hch : (run x i).R < i + rad x i
      · obtain ⟨h0, hRi⟩ := no_expand_change hix he hch
        rw [if_pos hch]
        omega
      · rw [if_neg hch]
        omega

theorem lastExp_le_cen {x : List α} : ∀ i, i ≤ x.length → lastExp x i ≤ (run x i).c := by
  intro i
  induction i with
  | zero => intro _; simp [lastExp, run_zero_c]
  | succ i ih =>
    intro hi
    have hix : i < x.length := by omega
    have h := ih (by omega)
    have hlast := lastExp_le x i
    rw [cen_succ hix]
    by_cases he : seed x i < rad x i
    · have hch := change_of_expand hix he
      rw [if_pos hch, lastExp, if_pos he]
    · rw [lastExp, if_neg he]
      split <;> omega

/-! ### 1 ステップあたりの移動量 -/

/-- 鏡ヘッドは 1 ステップで「1 マス」＋「中心の前進の 2 倍」しか動かない。 -/
theorem moveM_step {x : List α} {i : ℕ} (hi : i < x.length) :
    moveM x i ≤ 1 + 2 * ((run x (i + 1)).c - (run x i).c) := by
  have hc := cen_le (x := x) i (by omega)
  simp only [moveM, headDist, hM]
  rw [cen_succ hi]
  split <;> omega

/-- 左ヘッドは 1 ステップで「展開中心の前進の 2 倍」＋「走査量」しか動かない。 -/
theorem moveL_step {x : List α} {i : ℕ} (hi : i < x.length) :
    moveL x i ≤ 2 * (lastExp x (i + 1) - lastExp x i) + (rad x i - seed x i) := by
  simp only [moveL]
  split
  · next he =>
    have hlast : lastExp x (i + 1) = i := by rw [lastExp, if_pos he]
    have hrad : rad x i ≤ i := rad_le_center
    have hi0 : 0 < i := by omega
    have hjlt : lastExp x i < i := lastExp_lt x hi0
    have hA := hL_add_rht_le (x := x) i (by omega)
    have hB := two_lastExp_le (x := x) i (by omega)
    have hD := hL_le_lastExp x i
    have hE := cen_le (x := x) i (by omega)
    have hF := rht_le_two_cen (x := x) (i := i) (by omega)
    rw [hlast]
    rcases Nat.lt_or_ge i (run x i).R with h | h
    · have hs : seed x i = (run x i).R - i := by
        rcases seed_key hi h with hk | hk
        · exact hk
        · omega
      simp only [headDist]
      omega
    · have hs : seed x i = 0 := seed_eq_zero h
      simp only [headDist]
      omega
  · omega

/-! ## 総移動量 -/

theorem moveM_sum {x : List α} :
    ∀ n, n ≤ x.length → ∑ i ∈ Finset.range n, moveM x i ≤ n + 2 * (run x n).c := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    have hnx : n < x.length := by omega
    have h := ih (by omega)
    have hstep := moveM_step (x := x) (i := n) hnx
    have hmono := cen_mono (x := x) (i := n) hnx
    rw [Finset.sum_range_succ]
    omega

theorem moveL_sum {x : List α} :
    ∀ n, n ≤ x.length → ∑ i ∈ Finset.range n, moveL x i ≤ 2 * lastExp x n + (run x n).w := by
  intro n
  induction n with
  | zero => intro _; simp [lastExp, run_zero_w]
  | succ n ih =>
    intro hn
    have hnx : n < x.length := by omega
    have h := ih (by omega)
    have hstep := moveL_step (x := x) (i := n) hnx
    have hmono := lastExp_mono x n
    rw [Finset.sum_range_succ, wrk_succ hnx]
    omega

/-- **右ヘッドの総移動量**：入力長以下。 -/
theorem moveR_total (x : List α) {n : ℕ} (hn : n ≤ x.length) :
    ∑ i ∈ Finset.range n, moveR x i ≤ x.length := by
  rw [moveR_sum, hR_eq_rht n hn]
  exact (inv_run (x := x) n hn).2.2.1

/-- **右ヘッドの総移動量**：`2n` 以下（入力長に依らない形）。 -/
theorem moveR_total_two_mul (x : List α) {n : ℕ} (hn : n ≤ x.length) :
    ∑ i ∈ Finset.range n, moveR x i ≤ 2 * n := by
  rw [moveR_sum, hR_eq_rht n hn]
  have h1 := rht_le_two_cen (x := x) (i := n) hn
  have h2 := cen_le (x := x) n hn
  omega

/-- **鏡ヘッドの総移動量**：`3n` 以下。 -/
theorem moveM_total (x : List α) {n : ℕ} (hn : n ≤ x.length) :
    ∑ i ∈ Finset.range n, moveM x i ≤ 3 * n := by
  have h := moveM_sum (x := x) n hn
  have h2 := cen_le (x := x) n hn
  omega

/-- **左ヘッドの総移動量**：`2n + |x|` 以下。 -/
theorem moveL_total (x : List α) {n : ℕ} (hn : n ≤ x.length) :
    ∑ i ∈ Finset.range n, moveL x i ≤ 2 * n + x.length := by
  have h := moveL_sum (x := x) n hn
  have h2 := lastExp_le x n
  have h3 := (inv_run (x := x) n hn).2.2.2.1
  have h4 := (inv_run (x := x) n hn).2.2.1
  omega

/-! ### 全走査（`n = x.length`）の場合 -/

theorem moveR_total_run (x : List α) :
    ∑ i ∈ Finset.range x.length, moveR x i ≤ x.length := moveR_total x le_rfl

theorem moveM_total_run (x : List α) :
    ∑ i ∈ Finset.range x.length, moveM x i ≤ 3 * x.length := moveM_total x le_rfl

theorem moveL_total_run (x : List α) :
    ∑ i ∈ Finset.range x.length, moveL x i ≤ 3 * x.length := by
  have := moveL_total x (n := x.length) le_rfl
  omega

theorem moveL_total_run' (x : List α) :
    ∑ i ∈ Finset.range x.length, moveL x i ≤ 4 * x.length := by
  have := moveL_total_run x; omega

/-- **3 ヘッドの総移動量は入力長に線形**（`7|x|` 以下）。
したがって Manacher の走査は多テープ Turing 機械上で線形時間で実行できる。 -/
theorem headMove_total_run (x : List α) :
    ∑ i ∈ Finset.range x.length, (moveL x i + moveM x i + moveR x i) ≤ 7 * x.length := by
  have hL' := moveL_total_run x
  have hM' := moveM_total_run x
  have hR' := moveR_total_run x
  have hsplit : ∑ i ∈ Finset.range x.length, (moveL x i + moveM x i + moveR x i) =
      (∑ i ∈ Finset.range x.length, moveL x i) + (∑ i ∈ Finset.range x.length, moveM x i) +
        ∑ i ∈ Finset.range x.length, moveR x i := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [hsplit]
  omega

/-! ## 具体例 -/

section Examples

private def exh : List ℕ := [0, 1, 0, 0, 1, 0]

-- `moveL exh = [0, 1, 0, 0, 4, 0]`, `moveM exh = [0, 0, 0, 2, 1, 1]`,
-- `moveR exh = [0, 2, 0, 1, 2, 0]`（`#eval` で確認できる）。
example : ∑ i ∈ Finset.range exh.length, moveR exh i ≤ exh.length := moveR_total_run exh
example : ∑ i ∈ Finset.range exh.length, moveM exh i ≤ 3 * exh.length := moveM_total_run exh
example : ∑ i ∈ Finset.range exh.length, moveL exh i ≤ 3 * exh.length := moveL_total_run exh
example : ∑ i ∈ Finset.range exh.length, (moveL exh i + moveM exh i + moveR exh i)
    ≤ 7 * exh.length := headMove_total_run exh

end Examples

end Manacher
end PalPeg
