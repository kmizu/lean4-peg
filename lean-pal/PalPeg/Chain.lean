import PalPeg.Basic
import PalPeg.Words

/-!
# 接尾辞回文の鎖 (chain of suffix palindromes)

語 `w` に対し、`w` の接尾辞のうち回文であるものの長さ全体を降順リストとして持つ。
これを 1 記号ずつのオンライン更新 (`chainStep`) で計算する参照アルゴリズムを与え、
その正当性 (`mem_chain_iff`)、狭義降順性 (`chain_sorted`)、
素朴な O(n^2) 参照定義との一致 (`chain_eq_suffixPalLengths`) を証明する。

将来の実時間機械 (real-time machine) に対する仕様層。
-/

namespace PalPeg

/-! ## 回文述語（`PalPeg.Words` の `IsPal` を使う） -/

/-- 鍵となる補題：`[a] ++ x ++ [b]` が回文 ⟺ `a = b` かつ `x` が回文。 -/
theorem isPal_cons_concat {α : Type _} (a b : α) (x : List α) :
    IsPal (a :: (x ++ [b])) ↔ a = b ∧ IsPal x := by
  unfold IsPal
  have hrev : (a :: (x ++ [b])).reverse = b :: (x.reverse ++ [a]) := by simp
  rw [hrev, List.cons_eq_cons]
  constructor
  · rintro ⟨rfl, h2⟩
    exact ⟨rfl, List.append_cancel_right h2⟩
  · rintro ⟨rfl, h⟩
    exact ⟨rfl, by rw [h]⟩

/-- `w ∈ PAL ↔ IsPal w`。 -/
theorem mem_PAL_iff_isPal (w : List (Fin 2)) : w ∈ PAL ↔ IsPal w := Iff.rfl

/-! ## 素朴な参照定義 (O(n^2)) -/

/-- `w` の接尾辞のうち回文であるものの長さ全体（降順・重複なし）を直接判定で求める。 -/
def suffixPalLengths (w : List (Fin 2)) : List ℕ :=
  ((List.range (w.length + 1)).filter
    (fun l => decide ((w.drop (w.length - l)).reverse = w.drop (w.length - l)))).reverse

theorem mem_suffixPalLengths_iff (w : List (Fin 2)) (l : ℕ) :
    l ∈ suffixPalLengths w ↔ l ≤ w.length ∧ IsPal (w.drop (w.length - l)) := by
  unfold suffixPalLengths IsPal
  simp only [List.mem_reverse, List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩

/-! ## オンライン更新 -/

/-- オンライン 1 ステップ。`wrev` はこれまで読んだ語の反転（最後に読んだ記号が先頭）、
`chain` はその接尾辞回文長の鎖、`a` は次の記号。
延長規則：`l + 2` が生き残るのは `l` が旧鎖にあり、かつ `wrev[l] = a` のとき。
そのあと必ず `1` と `0` を付ける。 -/
def chainStep (wrev : List (Fin 2)) (chain : List ℕ) (a : Fin 2) : List ℕ :=
  ((chain.filter (fun l => decide (wrev[l]? = some a))).map (· + 2)) ++ [1, 0]

/-- 反転語（到着順の記号列）に関する構造的再帰版。 -/
def chainRev : List (Fin 2) → List ℕ
  | [] => [0]
  | a :: v => chainStep v (chainRev v) a

/-- 語 `w` の接尾辞回文長の鎖。 -/
def chain (w : List (Fin 2)) : List ℕ := chainRev w.reverse

/-- `chain` を左からの `foldl` として実行する形。状態は（読んだ語の反転, 鎖）。 -/
def chainFold (st : List (Fin 2) × List ℕ) (a : Fin 2) : List (Fin 2) × List ℕ :=
  (a :: st.1, chainStep st.1 st.2 a)

theorem chain_eq_foldl (w : List (Fin 2)) :
    w.foldl chainFold ([], [0]) = (w.reverse, chain w) := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w a ih =>
      rw [List.foldl_append, ih]
      simp only [List.foldl_cons, List.foldl_nil, chainFold, chain,
        List.reverse_append, List.reverse_singleton, List.singleton_append, chainRev]

/-! ## 正当性 -/

theorem mem_chainRev_iff (v : List (Fin 2)) (l : ℕ) :
    l ∈ chainRev v ↔ l ≤ v.length ∧ IsPal (v.take l) := by
  induction v generalizing l with
  | nil =>
      simp only [chainRev, List.mem_singleton, List.length_nil, Nat.le_zero_eq,
        List.take_nil]
      constructor
      · rintro rfl; exact ⟨rfl, isPal_nil⟩
      · rintro ⟨rfl, _⟩; rfl
  | cons a v ih =>
      match l with
      | 0 => simp [chainRev, chainStep, IsPal]
      | 1 =>
          have h1 : (1 : ℕ) ∈ chainRev (a :: v) := by simp [chainRev, chainStep]
          have h2 : (1 : ℕ) ≤ (a :: v).length ∧ IsPal ((a :: v).take 1) :=
            ⟨by simp, rfl⟩
          exact iff_of_true h1 h2
      | (m + 2) =>
          have hmem : (m + 2) ∈ chainRev (a :: v) ↔ (m ∈ chainRev v ∧ v[m]? = some a) := by
            simp only [chainRev, chainStep, List.mem_append, List.mem_map, List.mem_filter,
              List.mem_cons, List.not_mem_nil, or_false, decide_eq_true_eq]
            constructor
            · rintro (⟨x, ⟨hx1, hx2⟩, hx3⟩ | h | h)
              · have : x = m := by omega
                subst this; exact ⟨hx1, hx2⟩
              · omega
              · omega
            · rintro ⟨h1, h2⟩; exact Or.inl ⟨m, ⟨h1, h2⟩, rfl⟩
          rw [hmem, ih]
          have htake : (a :: v).take (m + 2) = a :: (v.take m ++ v[m]?.toList) := by
            rw [List.take_succ_cons, List.take_add_one]
          rw [htake]
          by_cases hm : m < v.length
          · have hget : v[m]? = some v[m] := List.getElem?_eq_getElem hm
            rw [hget]
            simp only [Option.toList_some]
            rw [isPal_cons_concat]
            constructor
            · rintro ⟨⟨_, hp⟩, hb⟩
              refine ⟨by simp only [List.length_cons]; omega, ?_, hp⟩
              exact (Option.some.inj hb).symm
            · rintro ⟨_, hab, hp⟩
              exact ⟨⟨by omega, hp⟩, by rw [hab]⟩
          · have hget : v[m]? = none := List.getElem?_eq_none (by omega)
            rw [hget]
            simp only [Option.toList_none, List.append_nil, List.length_cons]
            constructor
            · rintro ⟨_, hb⟩; exact absurd hb (by simp)
            · rintro ⟨h, _⟩; omega

/-- 主定理：`l ∈ chain w` ⟺ `l ≤ |w|` かつ `w` の長さ `l` の接尾辞が回文。 -/
theorem mem_chain_iff (w : List (Fin 2)) (l : ℕ) :
    l ∈ chain w ↔ l ≤ w.length ∧ (w.drop (w.length - l)).reverse = w.drop (w.length - l) := by
  rw [chain, mem_chainRev_iff, List.length_reverse]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [List.take_reverse] at h2
    exact isPal_reverse.mp h2
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [List.take_reverse]
    exact isPal_reverse.mpr h2

/-- `w` が回文 ⟺ `|w|` が鎖に入っている。 -/
theorem mem_PAL_iff_length_mem_chain (w : List (Fin 2)) : w ∈ PAL ↔ w.length ∈ chain w := by
  rw [mem_PAL, mem_chain_iff]
  simp

/-! ## 狭義降順性 -/

theorem chainRev_pairwise_gt (v : List (Fin 2)) : (chainRev v).Pairwise (· > ·) := by
  induction v with
  | nil => simp [chainRev]
  | cons a v ih =>
      rw [chainRev, chainStep, List.pairwise_append]
      refine ⟨?_, ?_, ?_⟩
      · rw [List.pairwise_map]
        exact (ih.filter _).imp (by omega)
      · simp
      · intro x hx y hy
        simp only [List.mem_map, List.mem_filter] at hx
        obtain ⟨n, _, rfl⟩ := hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl <;> omega

/-- 鎖は狭義降順。 -/
theorem chain_sorted (w : List (Fin 2)) : (chain w).Pairwise (· > ·) :=
  chainRev_pairwise_gt w.reverse

theorem chain_nodup (w : List (Fin 2)) : (chain w).Nodup :=
  (chain_sorted w).imp (by omega)

/-! ## 素朴定義との一致 -/

theorem suffixPalLengths_pairwise_gt (w : List (Fin 2)) :
    (suffixPalLengths w).Pairwise (· > ·) := by
  unfold suffixPalLengths
  rw [List.pairwise_reverse]
  exact List.pairwise_lt_range.filter _

theorem chain_eq_suffixPalLengths (w : List (Fin 2)) : chain w = suffixPalLengths w := by
  refine List.Perm.eq_of_pairwise (le := (· > ·)) (fun a b _ _ h1 h2 => by omega)
    (chain_sorted w) (suffixPalLengths_pairwise_gt w) ?_
  rw [List.perm_ext_iff_of_nodup (chain_nodup w)
      ((suffixPalLengths_pairwise_gt w).imp (by omega))]
  intro l
  rw [mem_chain_iff, mem_suffixPalLengths_iff]
  rfl

/-! ## 先頭は最長接尾辞回文 -/

/-- 鎖の先頭は最長の接尾辞回文の長さ。 -/
theorem chain_head (w : List (Fin 2)) :
    ∃ l₀, (chain w).head? = some l₀ ∧ l₀ ∈ chain w ∧ ∀ l ∈ chain w, l ≤ l₀ := by
  have hne : chain w ≠ [] := by
    intro h
    have h0 : (0 : ℕ) ∈ chain w := by
      rw [mem_chain_iff]; simp
    rw [h] at h0; simp at h0
  obtain ⟨l₀, t, ht⟩ := List.exists_cons_of_ne_nil hne
  refine ⟨l₀, by rw [ht]; rfl, by rw [ht]; exact List.mem_cons_self, ?_⟩
  intro l hl
  have hp := chain_sorted w
  rw [ht, List.pairwise_cons] at hp
  rw [ht] at hl
  rcases List.mem_cons.mp hl with rfl | hl'
  · exact Nat.le_refl _
  · exact Nat.le_of_lt (hp.1 l hl')

/-! ## 健全性チェック -/

example : chain [] = [0] := by decide
example : chain [0, 1, 0, 0, 1, 0] = [6, 3, 1, 0] := by decide
example : chain [0, 1, 1, 0] = [4, 1, 0] := by decide
example : chain [0, 1] = [1, 0] := by decide
example : chain [1, 1, 1] = [3, 2, 1, 0] := by decide
example : suffixPalLengths [0, 1, 0, 0, 1, 0] = [6, 3, 1, 0] := by decide

end PalPeg
