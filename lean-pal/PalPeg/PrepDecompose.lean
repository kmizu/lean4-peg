import PalPeg.OnlineMachine
import PalPeg.GSPreprocess

/-!
# `PrepImpl` としての GS 前処理（半分割スケジュール）

`PalPeg.GSPreprocess` の全域関数 `decompose x k` を、`PalPeg.OnlineMachine` の
`PrepImpl` に載せる。半分割スケジュール（§7）では、段幅 `S` の段のパターンは
`x = (w.take (S / 2)).reverse`（長さ `S / 2`）であり、前処理はラウンド
`(S / 2, S]`（`S / 2` ラウンド以上）で終わらねばならない。

ここでの**モデル化は指標レベル**である。状態は

* 段幅 `S`、
* パターン `x`（最初のラウンド `S / 2 + 1` に `w.take (S / 2)` から確定）、
* 残り仕事量 `rem`（初期値 `decomposeWork x k`、毎ラウンド `Cp` ずつ減る）

を持ち、`rem = 0` になった時点で `decompose x k` を出力する（それ以前は決して
読まれないダミー `(|x|, 0, 0)`）。1 ラウンドあたりの単位操作数は定数 `Cp`。
実際に 1 ラウンドで `Cp` 単位ぶんの `decomposeLoop` を進めるテープ実現は別の層の
仕事であり、本ファイルはその**予算が足りること**（`Cp * (S / 2) ≥ decomposeWork x k`）
を保証する。
-/

namespace PalPeg

variable {α : Type}

/-! ## 状態と実装 -/

/-- `prepDecompose` の内部状態。 -/
structure PrepDecompState (α : Type) where
  /-- 段幅 `S`。 -/
  S : ℕ
  /-- 確定したパターン（未確定なら `[]`）。 -/
  x : List α
  /-- 残り仕事量。 -/
  rem : ℕ
  /-- パターンが確定済みか。 -/
  started : Bool
  deriving DecidableEq

variable [DecidableEq α]

/-- 1 ラウンドあたりの仕事量（`decomposeWork_le` の係数から取った定数）。 -/
def prepCp (k : ℕ) : ℕ := 2 * (16 * k + 38) + 2 * k + 6

/-- GS 前処理のラウンド実装（半分割スケジュール用）。 -/
def prepDecompose (k : ℕ) : PrepImpl α where
  State := PrepDecompState α
  init S := ⟨S, [], 0, false⟩
  step t _ st :=
    if st.started then
      { st with rem := st.rem - prepCp k }
    else
      let x := (t.take (st.S / 2)).reverse
      ⟨st.S, x, decomposeWork x k - prepCp k, true⟩
  result st := if st.started ∧ st.rem = 0 then decompose st.x k else (st.x.length, 0, 0)
  cost _ _ _ := prepCp k

@[simp] theorem prepDecompose_cost (k : ℕ) (t : List α) (n : ℕ)
    (st : (prepDecompose (α := α) k).State) :
    (prepDecompose (α := α) k).cost t n st = prepCp k := rfl

/-! ## 走らせた結果 -/

/-- ラウンド `S / 2 + j`（`1 ≤ j`）での状態。パターンは確定し、残りは `prepCp k * j`
だけ減っている。 -/
theorem prepDecompose_runToH (k : ℕ) (w : List α) (S : ℕ) (hS : 2 ≤ S) :
    ∀ j : ℕ, 1 ≤ j → S / 2 + j ≤ S →
      (prepDecompose (α := α) k).runToH w S (S / 2 + j) =
        ⟨S, (w.take (S / 2)).reverse,
          decomposeWork ((w.take (S / 2)).reverse) k - prepCp k * j, true⟩ := by
  have hhalf : 1 ≤ S / 2 := by omega
  intro j
  induction j with
  | zero => intro h; omega
  | succ j ih =>
    intro _ hle
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · -- 最初のラウンド：パターンを確定する
      have hzero : S / 2 + (0 + 1) = (S / 2) + 1 := by omega
      rw [hzero]
      simp only [PrepImpl.runToH]
      rw [if_neg (show ¬ (S / 2 + 1 ≤ S / 2) by omega), if_pos (show S / 2 + 1 ≤ S by omega),
        PrepImpl.runToH_init (P := prepDecompose (α := α) k) w S (le_refl _)]
      have htk : ((w.take (S / 2 + 1)).take (S / 2)) = w.take (S / 2) := by
        rw [List.take_take, Nat.min_eq_left (by omega)]
      simp [prepDecompose, htk]
    · -- 以後は残りを減らすだけ
      have := ih (by omega) (by omega)
      have harr : S / 2 + (j + 1) = (S / 2 + j) + 1 := by omega
      rw [harr]
      simp only [PrepImpl.runToH]
      rw [if_neg (show ¬ ((S / 2 + j) + 1 ≤ S / 2) by omega),
        if_pos (show (S / 2 + j) + 1 ≤ S by omega), this]
      have harith : decomposeWork ((w.take (S / 2)).reverse) k - prepCp k * j - prepCp k
          = decomposeWork ((w.take (S / 2)).reverse) k - prepCp k * (j + 1) := by
        rw [Nat.mul_succ]; omega
      simp [prepDecompose, harith]

/-- 予算が足りる：`|x| = S / 2 ≥ 1` なら `decomposeWork x k ≤ prepCp k * (S / 2)`。 -/
theorem decomposeWork_le_prepCp (k : ℕ) (hk : 4 ≤ k) (x : List α) (m : ℕ)
    (hlen : x.length = m) (hm : 1 ≤ m) : decomposeWork x k ≤ prepCp k * m := by
  have h := decomposeWork_le x k hk
  rw [hlen] at h
  have : (16 * k + 38) * m + (2 * k + 5) ≤ prepCp k * m := by
    have hstep : prepCp k * m = (16 * k + 38) * m + ((16 * k + 38) + 2 * k + 6) * m := by
      simp only [prepCp]; ring
    have : (2 * k + 5) ≤ ((16 * k + 38) + 2 * k + 6) * m :=
      le_trans (by omega) (Nat.le_mul_of_pos_right _ hm)
    omega
  omega

/-- ラウンド `S` では残り仕事量は `0`。 -/
theorem prepDecompose_runToH_done (k : ℕ) (hk : 4 ≤ k) (w : List α) (S : ℕ)
    (hS : 2 ≤ S) (hw : 2 * S ≤ w.length) :
    (prepDecompose (α := α) k).runToH w S S =
      ⟨S, (w.take (S / 2)).reverse, 0, true⟩ := by
  have hhalf : 1 ≤ S / 2 := by omega
  have hj : S / 2 + (S - S / 2) = S := by omega
  have hrun := prepDecompose_runToH (α := α) k w S hS (S - S / 2) (by omega) (by omega)
  rw [hj] at hrun
  rw [hrun]
  have hlen : ((w.take (S / 2)).reverse).length = S / 2 := by
    simp [List.length_take, Nat.min_eq_left (show S / 2 ≤ w.length by omega)]
  have hbudget := decomposeWork_le_prepCp (α := α) k hk ((w.take (S / 2)).reverse) (S / 2)
    hlen hhalf
  have : decomposeWork ((w.take (S / 2)).reverse) k - prepCp k * (S - S / 2) = 0 := by
    have : prepCp k * (S / 2) ≤ prepCp k * (S - S / 2) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  rw [this]

/-! ## 仕様 -/

/-- **主定理**：`decompose` の `GSDecomp` 正当性 `hdec` を仮定すれば、
`prepDecompose k` は半分割スケジュールの前処理仕様 `PrepImplSpecH` を満たす。 -/
theorem prepDecompose_spec (k : ℕ) (hk : 4 ≤ k)
    (hdec : ∀ x : List α, GSDecomp x k (decompose x k).1 (decompose x k).2.1
      (decompose x k).2.2) :
    PrepImplSpecH (prepDecompose (α := α) k) k (prepCp k) where
  correct := by
    intro w S hS hw
    have hhalf : 1 ≤ S / 2 := by omega
    have hrun := prepDecompose_runToH_done (α := α) k hk w S hS hw
    have hres : (prepDecompose (α := α) k).result
        ((prepDecompose (α := α) k).runToH w S S)
        = decompose ((w.take (S / 2)).reverse) k := by
      rw [hrun]
      simp [prepDecompose]
    have hlen : ((w.take (S / 2)).reverse).length = S / 2 := by
      simp [List.length_take, Nat.min_eq_left (show S / 2 ≤ w.length by omega)]
    have hne : (w.take (S / 2)).reverse ≠ [] := by
      intro h; rw [h] at hlen; simp at hlen; omega
    have H := hdec ((w.take (S / 2)).reverse)
    rw [hres]
    refine ⟨H, ?_⟩
    have hcut := H.cut_bound hne
    rw [hlen] at hcut
    have : (decompose ((w.take (S / 2)).reverse) k).1
        ≤ (k - 1) * (decompose ((w.take (S / 2)).reverse) k).1 :=
      Nat.le_mul_of_pos_left _ (by omega)
    omega
  cost_le := by intro t n st; exact le_refl _

end PalPeg
