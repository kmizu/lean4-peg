import PalPeg.Words
import PalPeg.Matching
import Mathlib.Data.Nat.Log

/-!
# 段（stage）による回文の分解

実時間回文認識器が使う「二進段（dyadic stage）」分解の組合せ論的な核。
アルゴリズムは一切扱わず、語の分解のみを述べる。

* `isPal_append_iff` — `IsPal (u ++ m ++ v)` の分解（`|u| = |v|` のとき）。
* `isPal_iff_split` — 幅 `W` での分解：両端 `W` 文字が反転一致 かつ 中央が回文。
* `pal_prefix_iff_stage` — 接頭辞 `w.take n` に対する段の形（`occursAt` を使う）。
* `stageOf` / `stageOf_spec` / `stageOf_pow` — 時刻 `n` を担当する段（2 冪）。
* `live_stages` — ある時刻に「生きている」段は高々 2 つ。
* `pal_take_lt_two` / `pal_take_two_three` — 小さい `n` の場合分け。
-/

namespace PalPeg

universe u
variable {α : Type u}

/-! ## 一般の三分割 -/

/-- 回文の三分割規則：`|u| = |v|` のとき、`u m v` が回文 ⟺ `v = u` の反転 かつ `m` が回文。
`isPal_cons_append_iff` の一般化（`u = [a]`, `v = [b]` の場合が元の補題）。 -/
theorem isPal_append_iff {u m v : List α} (h : u.length = v.length) :
    IsPal (u ++ m ++ v) ↔ (v = u.reverse ∧ IsPal m) := by
  unfold IsPal
  constructor
  · intro hx
    rw [List.reverse_append, List.reverse_append, List.append_assoc] at hx
    obtain ⟨h1, h2⟩ := List.append_inj hx (by simpa using h.symm)
    obtain ⟨h3, _⟩ := List.append_inj' h2 (by simpa using h)
    exact ⟨by rw [← h1, List.reverse_reverse], h3⟩
  · rintro ⟨rfl, hm⟩
    rw [List.reverse_append, List.reverse_append, hm, List.reverse_reverse, List.append_assoc]

/-- **幅 `W` の分割**：`2 * W ≤ |x|` のとき、`x` が回文 ⟺
末尾 `W` 文字が先頭 `W` 文字の反転 かつ 中央（両端 `W` 文字を除いた部分）が回文。 -/
theorem isPal_iff_split (x : List α) (W : ℕ) (hW : 2 * W ≤ x.length) :
    IsPal x ↔ x.drop (x.length - W) = (x.take W).reverse ∧
      IsPal ((x.drop W).take (x.length - 2 * W)) := by
  have hu : (x.take W).length = W := by simp only [List.length_take]; omega
  have hv : (x.drop (x.length - W)).length = W := by simp only [List.length_drop]; omega
  have hdd : (x.drop W).drop (x.length - 2 * W) = x.drop (x.length - W) := by
    rw [List.drop_drop]
    exact congrArg (fun m => x.drop m) (by omega)
  have hsplit :
      x.take W ++ (x.drop W).take (x.length - 2 * W) ++ x.drop (x.length - W) = x := by
    rw [List.append_assoc, ← hdd, List.take_append_drop, List.take_append_drop]
  have key := isPal_append_iff (u := x.take W)
      (m := (x.drop W).take (x.length - 2 * W)) (v := x.drop (x.length - W)) (by rw [hu, hv])
  rw [hsplit] at key
  exact key

/-! ## 段の形 -/

/-- **段の形**：接頭辞 `w.take n`（`2 * W ≤ n ≤ |w|`）が回文であるのは、
反転パターン `(w.take W).reverse` が `w.take n` の末尾に出現し、
かつ中央 `(w.drop W).take (n - 2 * W)` が回文であるとき、かつそのときに限る。 -/
theorem pal_prefix_iff_stage {w : List α} {n W : ℕ} (hW : 2 * W ≤ n) (hn : n ≤ w.length) :
    IsPal (w.take n) ↔
      occursAt (w.take W).reverse (w.take n) ∧ IsPal ((w.drop W).take (n - 2 * W)) := by
  have hxlen : (w.take n).length = n := by simp only [List.length_take]; omega
  have hsplit := isPal_iff_split (w.take n) W (by omega)
  rw [hxlen] at hsplit
  have hA : (w.take n).take W = w.take W := by
    rw [List.take_take]; congr 1; omega
  have hB : ((w.take n).drop W).take (n - 2 * W) = (w.drop W).take (n - 2 * W) := by
    rw [List.drop_take, List.take_take]; congr 1; omega
  rw [hA, hB] at hsplit
  have hPlen : ((w.take W).reverse).length = W := by
    simp only [List.length_reverse, List.length_take]; omega
  have hocc : occursAt (w.take W).reverse (w.take n) ↔
      (w.take n).drop (n - W) = (w.take W).reverse := by
    unfold occursAt
    rw [hPlen, hxlen]
    constructor
    · rintro ⟨_, h⟩; exact h.symm
    · intro h; exact ⟨by omega, h.symm⟩
  rw [hsplit, hocc]

/-! ## 段の割り当てと被覆 -/

/-- 時刻（接頭辞長）`n` を担当する段の幅：`2 * W ≤ n < 4 * W` を満たす 2 冪。 -/
def stageOf (n : ℕ) : ℕ := 2 ^ (Nat.log 2 n - 1)

theorem stageOf_pow (n : ℕ) : stageOf n = 2 ^ (Nat.log 2 n - 1) := rfl

/-- `stageOf n` は `2 * W ≤ n < 4 * W` を満たす（`n ≥ 2`）。 -/
theorem stageOf_spec {n : ℕ} (hn : 2 ≤ n) : 2 * stageOf n ≤ n ∧ n < 4 * stageOf n := by
  have hk : 0 < Nat.log 2 n := Nat.log_pos (by omega) hn
  have h1 : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
  have h2 : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by omega) n
  have he : 2 * stageOf n = 2 ^ Nat.log 2 n := by
    unfold stageOf
    rw [show 2 * 2 ^ (Nat.log 2 n - 1) = 2 ^ (Nat.log 2 n - 1 + 1) from by
      rw [Nat.pow_succ]; omega]
    congr 1
    omega
  have he2 : 4 * stageOf n = 2 ^ (Nat.log 2 n + 1) := by
    unfold stageOf
    rw [show 4 * 2 ^ (Nat.log 2 n - 1) = 2 ^ (Nat.log 2 n - 1 + 2) from by
      rw [Nat.pow_succ, Nat.pow_succ]; omega]
    congr 1
    omega
  exact ⟨by omega, by omega⟩

/-- `stageOf n` は 2 冪。 -/
theorem stageOf_isPow (n : ℕ) : ∃ k, stageOf n = 2 ^ k := ⟨Nat.log 2 n - 1, rfl⟩

/-- **生きている段は高々 2 つ**：時刻 `t` において `W ≤ t < 4 * W` を満たす 2 冪 `W = 2 ^ k`
の指数は、たかだか隣接する 2 つ（`|j - k| ≤ 1`）に限られる。 -/
theorem live_stages {t k j : ℕ} (hk1 : 2 ^ k ≤ t) (hk2 : t < 4 * 2 ^ k)
    (hj1 : 2 ^ j ≤ t) (hj2 : t < 4 * 2 ^ j) : j ≤ k + 1 ∧ k ≤ j + 1 := by
  have e4k : 4 * 2 ^ k = 2 ^ (k + 2) := by rw [Nat.pow_succ, Nat.pow_succ]; omega
  have e4j : 4 * 2 ^ j = 2 ^ (j + 2) := by rw [Nat.pow_succ, Nat.pow_succ]; omega
  constructor
  · by_contra hcon
    have hle : k + 2 ≤ j := by omega
    have := Nat.pow_le_pow_right (show 0 < 2 by omega) hle
    omega
  · by_contra hcon
    have hle : j + 2 ≤ k := by omega
    have := Nat.pow_le_pow_right (show 0 < 2 by omega) hle
    omega

/-! ## 小さい場合 -/

/-- 長さ 1 以下の語は回文。 -/
theorem isPal_of_length_le_one {x : List α} (h : x.length ≤ 1) : IsPal x := by
  rcases x with _ | ⟨a, l⟩
  · exact isPal_nil
  · rcases l with _ | ⟨b, t⟩
    · exact isPal_singleton a
    · simp at h

/-- `n < 2` の接頭辞は常に回文（長さ 0 と 1）。 -/
theorem pal_take_lt_two (w : List α) {n : ℕ} (hn : n < 2) : IsPal (w.take n) :=
  isPal_of_length_le_one (by simp only [List.length_take]; omega)

/-- `n ∈ {2, 3}` の場合：接頭辞が回文 ⟺ 両端の文字が一致。 -/
theorem pal_take_two_three {w : List α} {n : ℕ} (h2 : 2 ≤ n) (h3 : n ≤ 3)
    (hn : n ≤ w.length) : IsPal (w.take n) ↔ w[0]? = w[n - 1]? := by
  have hlen : (w.take n).length = n := by simp only [List.length_take]; omega
  rw [isPal_iff_getElem?, hlen]
  constructor
  · intro h
    have h0 := h 0 (by omega)
    rwa [List.getElem?_take_of_lt (show 0 < n by omega),
      List.getElem?_take_of_lt (show n - 1 - 0 < n by omega),
      show n - 1 - 0 = n - 1 from by omega] at h0
  · intro h i hi
    rw [List.getElem?_take_of_lt hi, List.getElem?_take_of_lt (show n - 1 - i < n by omega)]
    rcases (show i = 0 ∨ n - 1 - i = 0 ∨ i = n - 1 - i by omega) with h0 | h0 | h0
    · subst h0
      rw [show n - 1 - 0 = n - 1 from by omega]
      exact h
    · rw [h0, show i = n - 1 from by omega]
      exact h.symm
    · rw [← h0]

/-! ## 小例による健全性チェック -/

example : stageOf 2 = 1 := by decide
example : stageOf 4 = 2 := by decide
example : stageOf 7 = 2 := by decide
example : stageOf 8 = 4 := by decide
example : 2 * stageOf 7 ≤ 7 ∧ 7 < 4 * stageOf 7 := by decide
example : IsPal ([0, 1, 0] : List ℕ) := by unfold IsPal; decide
example : ¬ IsPal ([0, 1, 1] : List ℕ) := by unfold IsPal; decide
example : occursAt ([0, 1] : List ℕ).reverse ([0, 1, 2, 1, 0] : List ℕ) := by decide

end PalPeg
