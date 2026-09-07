import PalPeg.Manacher
import PalPeg.ManacherHeads
import PalPeg.Schedule

/-!
# 中央回文ジョブ（dyadic stage の middle job）の実時間性

幅 `W` の dyadic stage で、中央窓 `x = (w.drop W).take (2*W)` の
接頭辞回文フラグ `IsPal (x.take L)`（`0 ≤ L ≤ 2W`）を、
`ALGORITHM_SPEC.md §3` のバッチ方式（`h = W/2`、`j = 0..3` の 4 サブジョブ）で
締切内に供給できることを示す。

主な内容：

* `stepCost` / `stepCost_cum`：Manacher 走査の 1 ステップあたりの費用
  （ステップ自身 + 展開比較 + 3 ヘッドの移動）の累積が `C * n`（`C = 12`）以下。
* `pad` / `padFlag`：区切り記号 `none` を挟んだ語 `pad x` の**奇数中心のみ**の
  Manacher 走査で、`x` の**両奇偶**の接頭辞回文フラグが読める
  （`padFlag_spec`）。これにより `radE` のアルゴリズムを別途用意する必要がない。
* `rad_take` / `radE_take` / `padFlag_take`：長さ `L` のフラグは
  凍結接頭辞 `x.take m`（`L ≤ m`）だけで決まる。
* `middleJob_cost` / `middleJob_deadline`：サブジョブ `k`（`1 ≤ k ≤ 4`）の総費用は
  `rate * h`（`rate = 128`）以下なので、`Schedule.finishTime` の意味で
  締切 `2*W + (k-1)*h` に間に合う。
* `middle_flag_spec`：時刻 `n ∈ [2W, 4W)` に届くフラグは
  `decide (IsPal ((w.drop W).take (n - 2*W)))` に一致し、かつ時刻 `n` までに準備完了。
-/

namespace PalPeg
namespace MiddleJob

open Manacher

universe u
variable {α : Type u}

/-! ## 補助：`take` の合成 -/

theorem take_take_of_le {x : List α} {L m : ℕ} (h : L ≤ m) :
    (x.take m).take L = x.take L := by
  rw [List.take_take]
  congr 1
  omega

/-! ## 1 ステップの費用と累積上界 -/

section Cost

variable [DecidableEq α]

/-- Manacher 走査のステップ `i` の費用：
ステップ自身に `1`、展開の比較に `rad x i - seed x i`、
入力テープ左右ヘッドと半径テープ鏡ヘッドの移動に `moveL + moveM + moveR`。 -/
def stepCost (x : List α) (i : ℕ) : ℕ :=
  1 + (rad x i - seed x i) + moveL x i + moveM x i + moveR x i

/-- 先頭 `n` 中心までの総費用。 -/
def totalCostUpto (x : List α) (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, stepCost x i

/-- 全走査の総費用。 -/
def totalCost (x : List α) : ℕ := totalCostUpto x x.length

/-- 1 文字あたりの費用定数。 -/
def C : ℕ := 12

/-- 展開の比較回数の累積は走査状態の `w` そのもの。 -/
theorem sum_expand_eq_w (x : List α) :
    ∀ n, n ≤ x.length → ∑ i ∈ Finset.range n, (rad x i - seed x i) = (run x n).w := by
  intro n
  induction n with
  | zero => intro _; simp [run_zero_w]
  | succ n ih =>
    intro hn
    rw [Finset.sum_range_succ, ih (by omega), wrk_succ (show n < x.length by omega)]

theorem w_le_two_mul (x : List α) {n : ℕ} (hn : n ≤ x.length) : (run x n).w ≤ 2 * n := by
  obtain ⟨-, -, -, hwR, -⟩ := inv_run (x := x) n hn
  have h1 := rht_le_two_cen (x := x) (i := n) hn
  have h2 := cen_le (x := x) n hn
  omega

theorem sum_expand_le (x : List α) {n : ℕ} (hn : n ≤ x.length) :
    ∑ i ∈ Finset.range n, (rad x i - seed x i) ≤ 2 * n := by
  rw [sum_expand_eq_w x n hn]; exact w_le_two_mul x hn

theorem moveL_total_four (x : List α) {n : ℕ} (hn : n ≤ x.length) :
    ∑ i ∈ Finset.range n, moveL x i ≤ 4 * n := by
  have h := moveL_sum (x := x) n hn
  have h2 := lastExp_le x n
  have h3 := w_le_two_mul x hn
  omega

/-- **累積費用の線形上界**：`∑_{i<n} stepCost x i ≤ C * n`（`C = 12`）。 -/
theorem stepCost_cum (x : List α) {n : ℕ} (hn : n ≤ x.length) :
    totalCostUpto x n ≤ C * n := by
  have hsplit : totalCostUpto x n =
      ((((∑ _i ∈ Finset.range n, 1) + ∑ i ∈ Finset.range n, (rad x i - seed x i))
        + ∑ i ∈ Finset.range n, moveL x i) + ∑ i ∈ Finset.range n, moveM x i)
        + ∑ i ∈ Finset.range n, moveR x i := by
    simp only [totalCostUpto, stepCost, Finset.sum_add_distrib]
  have hone : (∑ _i ∈ Finset.range n, 1) = n := by simp
  have h1 := sum_expand_le x hn
  have h2 := moveL_total_four x hn
  have h3 := moveM_total x hn
  have h4 := moveR_total_two_mul x hn
  rw [hsplit, hone]
  simp only [C]
  omega

theorem totalCost_le (x : List α) : totalCost x ≤ C * x.length :=
  stepCost_cum x le_rfl

end Cost

/-! ## 半径の凍結接頭辞依存性 -/

section Take

variable [DecidableEq α]

/-- **奇数中心の切り詰め補題**：中心 `r` で半径 `r` に達するかは `x[0..2r]` だけで決まる。 -/
theorem rad_take {x : List α} {r m : ℕ} (hm : 2 * r + 1 ≤ m) (hx : 2 * r + 1 ≤ x.length) :
    r ≤ rad (x.take m) r ↔ r ≤ rad x r := by
  have hlen : 2 * r + 1 ≤ (x.take m).length := by rw [List.length_take]; omega
  rw [← isPal_take_odd_iff hlen, ← isPal_take_odd_iff hx,
    take_take_of_le (show 2 * r + 1 ≤ m by omega)]

/-- **偶数中心の切り詰め補題**。 -/
theorem radE_take {x : List α} {r m : ℕ} (hm : 2 * r ≤ m) (hx : 2 * r ≤ x.length) :
    r ≤ radE (x.take m) r ↔ r ≤ radE x r := by
  have hlen : 2 * r ≤ (x.take m).length := by rw [List.length_take]; omega
  rw [← isPal_take_even_iff hlen, ← isPal_take_even_iff hx,
    take_take_of_le (show 2 * r ≤ m by omega)]

end Take

/-! ## 区切り記号による偶奇の統一（`radE` のアルゴリズムを不要にする） -/

/-- 各文字の後ろに区切り `none` を置いた本体。 -/
def body : List α → List (Option α)
  | [] => []
  | a :: t => some a :: none :: body t

/-- 先頭にも区切りを置いた語。`|pad x| = 2|x| + 1` で、
`x` の長さ `L` の接頭辞回文は `pad x` の中心 `L` の半径 `L` の回文に対応する。 -/
def pad (x : List α) : List (Option α) := none :: body x

@[simp] theorem body_nil : body ([] : List α) = [] := rfl

@[simp] theorem body_cons (a : α) (t : List α) :
    body (a :: t) = some a :: none :: body t := rfl

theorem body_append (x y : List α) : body (x ++ y) = body x ++ body y := by
  induction x with
  | nil => rfl
  | cons a t ih => simp [ih]

theorem body_length (x : List α) : (body x).length = 2 * x.length := by
  induction x with
  | nil => rfl
  | cons a t ih => simp only [body_cons, List.length_cons, ih]; omega

theorem pad_length (x : List α) : (pad x).length = 2 * x.length + 1 := by
  simp only [pad, List.length_cons, body_length]

theorem body_filterMap (x : List α) : (body x).filterMap (fun o => o) = x := by
  induction x with
  | nil => rfl
  | cons a t ih => simp [ih]

theorem body_inj {x y : List α} (h : body x = body y) : x = y := by
  have h2 := congrArg (List.filterMap (fun o : Option α => o)) h
  rwa [body_filterMap, body_filterMap] at h2

theorem body_reverse (x : List α) : (body x).reverse ++ [none] = none :: body x.reverse := by
  induction x with
  | nil => rfl
  | cons a t ih =>
    have h2 : (a :: t).reverse = t.reverse ++ [a] := by simp
    have h3 : body (t.reverse ++ [a]) = body t.reverse ++ [some a, none] := by
      rw [body_append]; rfl
    rw [h2, h3, body_cons, List.reverse_cons, List.reverse_cons, ih]
    simp

theorem pad_reverse (x : List α) : (pad x).reverse = pad x.reverse := by
  simp only [pad, List.reverse_cons]
  exact body_reverse x

/-- **区切り語は元の語と回文性が一致する。** -/
theorem pad_isPal (x : List α) : IsPal (pad x) ↔ IsPal x := by
  unfold IsPal
  rw [pad_reverse]
  constructor
  · intro h
    exact body_inj (by simpa [pad] using h)
  · intro h; rw [h]

theorem body_take (x : List α) : ∀ L, (body x).take (2 * L) = body (x.take L) := by
  induction x with
  | nil => intro L; simp
  | cons a t ih =>
    intro L
    cases L with
    | zero => simp
    | succ m =>
      have h2 : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
      rw [body_cons, h2, List.take_succ_cons, List.take_succ_cons, ih m,
        List.take_succ_cons, body_cons]

theorem pad_take (x : List α) (L : ℕ) : (pad x).take (2 * L + 1) = pad (x.take L) := by
  simp only [pad, List.take_succ_cons, body_take]

/-! ## `pad` 上の奇数走査から読むフラグ -/

section Flags

variable [DecidableEq α]

/-- 長さ `L` の接頭辞回文フラグ：区切り語 `pad x` の中心 `L` における半径が `L` 以上か。 -/
def padFlag (x : List α) (L : ℕ) : Bool := decide (L ≤ rad (pad x) L)

/-- **フラグの正当性**（奇数長・偶数長を統一的に扱う）。 -/
theorem padFlag_spec {x : List α} {L : ℕ} (hL : L ≤ x.length) :
    padFlag x L = decide (IsPal (x.take L)) := by
  have hlen : 2 * L + 1 ≤ (pad x).length := by rw [pad_length]; omega
  have h := isPal_take_odd_iff (x := pad x) (r := L) hlen
  rw [pad_take, pad_isPal] at h
  simp only [padFlag]
  exact decide_eq_decide.mpr h.symm

/-- **フラグは凍結接頭辞だけで決まる**：長さ `L` のフラグは `x.take m`（`L ≤ m`）から読める。 -/
theorem padFlag_take {x : List α} {L m : ℕ} (hLm : L ≤ m) (hLx : L ≤ x.length) :
    padFlag (x.take m) L = padFlag x L := by
  have h1 : L ≤ (x.take m).length := by rw [List.length_take]; omega
  rw [padFlag_spec h1, padFlag_spec hLx, take_take_of_le hLm]

/-- 半径表から読む参照フラグ（`Manacher.prefixPalFlagsFromRad` の本体）。 -/
def flagOf (x : List α) (L : ℕ) : Bool :=
  if L % 2 = 1 then decide (L / 2 ≤ rad x (L / 2)) else decide (L / 2 ≤ radE x (L / 2))

theorem prefixPalFlagsFromRad_eq_map (x : List α) :
    prefixPalFlagsFromRad x = (List.range (x.length + 1)).map (flagOf x) := rfl

/-- 半径表からのフラグと区切り語からのフラグは一致する。 -/
theorem flagOf_eq_padFlag {x : List α} {L : ℕ} (hL : L ≤ x.length) :
    flagOf x L = padFlag x L := by
  rw [padFlag_spec hL]
  simp only [flagOf]
  by_cases hp : L % 2 = 1
  · rw [if_pos hp]
    refine decide_eq_decide.mpr ?_
    have hL2 : L = 2 * (L / 2) + 1 := by omega
    rw [show x.take L = x.take (2 * (L / 2) + 1) by rw [← hL2]]
    exact (isPal_take_odd_iff (by omega)).symm
  · rw [if_neg hp]
    refine decide_eq_decide.mpr ?_
    have hL2 : L = 2 * (L / 2) := by omega
    rw [show x.take L = x.take (2 * (L / 2)) by rw [← hL2]]
    exact (isPal_take_even_iff (by omega)).symm

end Flags

/-! ## バッチ化されたサブジョブとその締切 -/

section Job

variable [DecidableEq α]

/-- サービスレート（1 到着あたりに処理できる費用単位）。 -/
def rate : ℕ := 128

/-- サブジョブ `k`（`1 ≤ k ≤ 4`）の費用：凍結接頭辞 `x.take (k*h)` の区切り語上での全走査。 -/
def jobWork (x : List α) (h : ℕ) (k : ℕ) : ℕ := totalCost (pad (x.take (k * h)))

/-- サブジョブ `k` の解放時刻：窓の先頭 `W` 文字が読まれた後、さらに `k*h` 文字が届いた時刻。 -/
def jobArr (W h : ℕ) (k : ℕ) : ℕ := W + k * h

/-- **サブジョブの費用上界**：`jobWork x h k ≤ rate * h`（`k ≤ 4`, `1 ≤ h`）。 -/
theorem middleJob_cost (x : List α) {h k : ℕ} (hh : 1 ≤ h) (hk : k ≤ 4) :
    jobWork x h k ≤ rate * h := by
  have hlen : (pad (x.take (k * h))).length ≤ 2 * (k * h) + 1 := by
    rw [pad_length, List.length_take]; omega
  have hcost := totalCost_le (pad (x.take (k * h)))
  have hkh : k * h ≤ 4 * h := Nat.mul_le_mul hk (le_refl h)
  have hmul : C * (pad (x.take (k * h))).length ≤ C * (2 * (k * h) + 1) :=
    Nat.mul_le_mul (le_refl C) hlen
  simp only [jobWork, rate, C] at *
  omega

/-- 奇数走査だけを見た場合の費用（仕様書の `4*C*h` 形）。 -/
theorem middleJob_cost_odd (x : List α) {h k : ℕ} (hk : k ≤ 4) :
    totalCost (x.take (k * h)) ≤ (4 * C) * h := by
  have hlen : (x.take (k * h)).length ≤ k * h := by rw [List.length_take]; omega
  have hcost := totalCost_le (x.take (k * h))
  have hkh : k * h ≤ 4 * h := Nat.mul_le_mul hk (le_refl h)
  have hmul : C * (x.take (k * h)).length ≤ C * (k * h) := Nat.mul_le_mul (le_refl C) hlen
  have h4 : C * (k * h) ≤ C * (4 * h) := Nat.mul_le_mul (le_refl C) hkh
  have h5 : C * (4 * h) = (4 * C) * h := by ring
  omega

end Job

/-! ### `Schedule` によるスケジューリング -/

section Sched

/-- 4 個のサブジョブが 1 個あたり `ρ * h` 以下の費用で、`h` 刻みの到着時刻を持つとき、
FIFO サーバの仕事時計は `ρ * (W + (k+1)*h)` を超えない。 -/
theorem cap_le_of_jobs {work arr : ℕ → ℕ} {ρ W h : ℕ}
    (harr : ∀ k, arr k = W + k * h)
    (hwork : ∀ k, k ≤ 4 → work k ≤ ρ * h) :
    ∀ k, k ≤ 4 → Schedule.cap work arr ρ k ≤ ρ * (W + (k + 1) * h) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have hIH := ih (by omega)
    have hw := hwork (k + 1) hk
    rw [Schedule.cap_succ, harr, max_eq_right hIH]
    have he : ρ * (W + (k + 1 + 1) * h) = ρ * (W + (k + 1) * h) + ρ * h := by ring
    rw [he]
    exact Nat.add_le_add_left hw _

/-- **サブジョブは締切に間に合う。**  `W = 2*h`、レート `ρ`、サブジョブ `k` の費用が
`ρ * h` 以下なら、`k` 番目のジョブは時刻 `2*W + (k-1)*h`（そのバッチの最初のフラグの
使用時刻）までに完了する。 -/
theorem finishTime_le_deadline {work arr : ℕ → ℕ} {ρ W h : ℕ} (hρ : 0 < ρ) (hWh : W = 2 * h)
    (harr : ∀ k, arr k = W + k * h)
    (hwork : ∀ k, k ≤ 4 → work k ≤ ρ * h) :
    ∀ k, 1 ≤ k → k ≤ 4 → Schedule.finishTime work arr ρ k ≤ 2 * W + (k - 1) * h := by
  intro k h1 h4
  have hcap := cap_le_of_jobs harr hwork k h4
  have heq : 2 * W + (k - 1) * h = W + (k + 1) * h := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    subst hWh
    simp only [Nat.add_sub_cancel]
    ring
  rw [Schedule.finishTime, Schedule.cdiv_le_iff hρ, heq]
  exact hcap

end Sched

section Deadline

variable [DecidableEq α]

/-- **中央ジョブの締切充足**：`W = 2h`、`h ≥ 1` のとき、サブジョブ `k`（`1 ≤ k ≤ 4`）は
時刻 `2*W + (k-1)*h` までに全フラグを出力し終える。 -/
theorem middleJob_deadline (x : List α) {W h : ℕ} (hh : 1 ≤ h) (hWh : W = 2 * h)
    {k : ℕ} (h1 : 1 ≤ k) (h4 : k ≤ 4) :
    Schedule.finishTime (jobWork x h) (jobArr W h) rate k ≤ 2 * W + (k - 1) * h :=
  finishTime_le_deadline (by simp [rate]) hWh (fun _ => rfl)
    (fun _ hk => middleJob_cost x hh hk) k h1 h4

/-- サブジョブ添字 `k = ⌊L/h⌋ + 1` は `L < 2*W = 4*h` のとき `4` 以下。 -/
theorem job_index_le {W h L : ℕ} (hh : 1 ≤ h) (hWh : W = 2 * h) (hL : L < 2 * W) :
    L / h + 1 ≤ 4 := by
  have hd : L / h < 4 := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    omega
  omega

/-- **フラグの正当性**：サブジョブ `k` は凍結接頭辞 `x.take (k*h)` だけから、
長さ `L < k*h` のフラグを正しく計算する。 -/
theorem flags_correct (x : List α) {h k L : ℕ} (hL : L < k * h) (hLx : L ≤ x.length) :
    padFlag (x.take (k * h)) L = decide (IsPal (x.take L)) := by
  rw [padFlag_take (by omega) hLx, padFlag_spec hLx]

/-- **中央フラグの総合仕様**：`3W ≤ |w|`、`W = 2h`、`h ≥ 1` のとき、
時刻 `n ∈ [2W, 4W)` に必要な中央フラグ（長さ `L = n - 2W`）は
サブジョブ `k = ⌊L/h⌋ + 1` が凍結接頭辞から計算し、
(1) 時刻 `n` までに準備完了し、(2) `decide (IsPal ((w.drop W).take L))` に一致する。 -/
theorem middle_flag_spec (w : List α) {W h n L k : ℕ} (hh : 1 ≤ h) (hWh : W = 2 * h)
    (hw : 3 * W ≤ w.length) (hn1 : 2 * W ≤ n) (hn2 : n < 4 * W)
    (hLdef : L = n - 2 * W) (hkdef : k = L / h + 1) :
    Schedule.finishTime (jobWork ((w.drop W).take (2 * W)) h) (jobArr W h) rate k ≤ n ∧
      padFlag (((w.drop W).take (2 * W)).take (k * h)) L
        = decide (IsPal ((w.drop W).take L)) := by
  set x := (w.drop W).take (2 * W) with hx
  have hxlen : x.length = 2 * W := by
    simp only [hx, List.length_take, List.length_drop]
    omega
  have hL2 : L < 2 * W := by omega
  have hLx : L ≤ x.length := by omega
  have hk4 : k ≤ 4 := by rw [hkdef]; exact job_index_le hh hWh hL2
  have hk1 : 1 ≤ k := by rw [hkdef]; exact Nat.le_add_left 1 _
  have hLkh : L < k * h := by
    rw [hkdef, ← Nat.div_lt_iff_lt_mul (show 0 < h by omega)]
    exact Nat.lt_succ_self _
  refine ⟨?_, ?_⟩
  · have hd := middleJob_deadline (x := x) (W := W) (h := h) hh hWh hk1 hk4
    have hkh : (k - 1) * h ≤ L := by
      rw [hkdef, Nat.add_sub_cancel]
      exact Nat.div_mul_le_self L h
    omega
  · rw [flags_correct x hLkh hLx]
    congr 1
    rw [hx, take_take_of_le (show L ≤ 2 * W by omega)]

end Deadline

/-! ## 具体例 -/

section Examples

private def exm : List ℕ := [0, 1, 0, 0, 1, 0]

-- `pad exm` は長さ `13`。長さ `L` のフラグは `padFlag exm L`。
example : (pad exm).length = 2 * exm.length + 1 := pad_length exm
example : List.map (padFlag exm) (List.range 7) = prefixPalFlags exm := by decide

example : padFlag exm 3 = decide (IsPal (exm.take 3)) := padFlag_spec (by decide)
example : padFlag (exm.take 4) 3 = padFlag exm 3 := padFlag_take (by omega) (by decide)

end Examples

end MiddleJob
end PalPeg
