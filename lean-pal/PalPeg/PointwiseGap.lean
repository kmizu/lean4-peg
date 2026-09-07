import PalPeg.GSVerifierTapes

/-!
# 一歩の費用を **点ごと**（`Metered` の `hcost` の形）で抑えられるか

`PalPeg.Metered` の実時間定理は、一歩の費用について

  `hcost : ∀ st, cst st ≤ (A + B') * ΔΦ`

という **点ごと** の評価を要求する。検証器つきの一歩の費用のうち、走査部と比較部は
`GSTapes.program_cost'`（`≤ (8k+13)·ΔΦ + 8`）で点ごとに抑えられるが、ずらしのときに
`U`（接頭辞テープ）のヘッドを添字 `checked + 1` から `1` へ戻す **巻き戻し**
（`GSVTapes.uxWalk` の `2·checked + 4` 動作）は点ごとに抑えられない。

本ファイルはその境界を正確に示す。

* **リセット枝**（`¬(k·p₁ ≤ q ∧ q ≤ r)`）では点ごとに抑えられる：
  `gsShift ≥ ⌈q/k⌉` なので `q ≤ k·gsShift ≤ k·ΔΦ`、したがって
  `2·checked ≤ 4q ≤ 4k·ΔΦ`（`rewind_pointwise_reset`）。
* **周期枝**（`k·p₁ ≤ q ≤ r`）では **どんな定数でも** 抑えられない：
  `ΔΦ = k·p₁` は小さいまま `q`（したがって `checked ≤ 2q`）をいくらでも大きくできる
  （`rewind_not_pointwise`）。

## この結果の意味（機械側の設計変更について）

「`U` を 2 枚持ち、ずらしのときに休んでいる方へ O(1) で切り替え、使い終わった方は
以後 1 歩あたり数セルずつ歩いて帰す」という設計でも、**周期枝のこの状態は救えない**。
切り替えが O(1) で済むのは「休んでいる方が既に家に着いている」ときだけであり、
そのためには前の走行の借金 `2·checked_prev` を歩き終えているだけの歩数が要る。
長い走行（`checked` 大）の直後のずらしでは、休んでいる方の借金も
（その前の走行に比例して）残りうるので、結局どちらかの巻き戻しに
`Θ(checked)` 動作が要る。一方この一歩の `ΔΦ` は `k·p₁`（`p₁ = 1` なら `k`）しかない。

したがって **`Metered` を素のまま使うための「点ごとの `hcost`」は、この検証器設計では
達成できない**。`Ψ = 2·checked` を含む償却形（`PalPeg.VerifierFeedX.fcostX_amortized`）と、
それを扱うスケジューラ（`PalPeg.MeteredX`）が必要である。
-/

set_option autoImplicit false

namespace PalPeg
namespace PointwiseGap

/-- ずらし後の走査状態。 -/
def shifted (k p₁ r : ℕ) (st : ScanState) : ScanState :=
  ⟨st.pos + gsShift k p₁ r st.q, gsNextQ k p₁ r st.q⟩

/-- **リセット枝では点ごとに抑えられる**：`2·checked ≤ 4k·ΔΦ`。 -/
theorem rewind_pointwise_reset {k p₁ r : ℕ} (hk : 0 < k) {z : VState}
    (hbranch : ¬ (k * p₁ ≤ z.1.q ∧ z.1.q ≤ r)) (hc : z.2 ≤ 2 * z.1.q) :
    2 * z.2 ≤ 4 * k * (Phi k (shifted k p₁ r z.1) - Phi k z.1) := by
  have hgs : gsShift k p₁ r z.1.q = max 1 (ceilDiv z.1.q k) := by
    unfold gsShift; rw [if_neg hbranch]
  have hcb : z.1.q ≤ k * ceilDiv z.1.q k := (ceilDiv_bounds hk).1
  have hmax : ceilDiv z.1.q k ≤ max 1 (ceilDiv z.1.q k) := le_max_right _ _
  have hsh : gsShift k p₁ r z.1.q ≤ Phi k (shifted k p₁ r z.1) - Phi k z.1 :=
    GSVTapes.gsShift_le_dPhi hk z.1
  have h1 : k * ceilDiv z.1.q k ≤ k * gsShift k p₁ r z.1.q := by
    rw [hgs]; exact Nat.mul_le_mul_left k hmax
  have h2 : k * gsShift k p₁ r z.1.q
      ≤ k * (Phi k (shifted k p₁ r z.1) - Phi k z.1) := Nat.mul_le_mul_left k hsh
  have h3 : 4 * k * (Phi k (shifted k p₁ r z.1) - Phi k z.1)
      = 4 * (k * (Phi k (shifted k p₁ r z.1) - Phi k z.1)) := by ring
  omega

/-- **周期枝では、どんな定数 `C` でも点ごとには抑えられない**。
`k = p₁ = 1`, `r = q = C + 1`, `checked = 2q` は
`VCheckedInv`（`checked ≤ 2q`）と周期枝の条件 `k·p₁ ≤ q ≤ r` を満たし、
`ΔΦ = 1` でありながら `checked = 2C + 2 > C·ΔΦ`。
（巻き戻し動作数は `2·checked` 以上なので、なおさら抑えられない。） -/
theorem rewind_not_pointwise (C : ℕ) :
    ∃ (k p₁ r : ℕ) (z : VState),
      0 < k ∧ 0 < p₁ ∧ z.2 ≤ 2 * z.1.q ∧ k * p₁ ≤ z.1.q ∧ z.1.q ≤ r ∧
      Phi k (shifted k p₁ r z.1) - Phi k z.1 = 1 ∧
      C * (Phi k (shifted k p₁ r z.1) - Phi k z.1) < z.2 := by
  refine ⟨1, 1, C + 1, ((⟨0, C + 1⟩ : ScanState), 2 * (C + 1)), by omega, by omega,
    by simp, by simp, by simp, ?_, ?_⟩
  · have hg : gsShift 1 1 (C + 1) (C + 1) = 1 := by
      unfold gsShift; rw [if_pos (by omega)]
    have hn : gsNextQ 1 1 (C + 1) (C + 1) = C := by
      unfold gsNextQ; rw [if_pos (by omega)]; omega
    show Phi 1 (shifted 1 1 (C + 1) (⟨0, C + 1⟩ : ScanState)) - Phi 1 (⟨0, C + 1⟩ : ScanState)
      = 1
    unfold shifted
    show Phi 1 (⟨0 + gsShift 1 1 (C + 1) (C + 1), gsNextQ 1 1 (C + 1) (C + 1)⟩ : ScanState)
        - Phi 1 (⟨0, C + 1⟩ : ScanState) = 1
    rw [hg, hn]
    show 2 * (0 + 1) + C - (2 * 0 + (C + 1)) = 1
    omega
  · have hg : gsShift 1 1 (C + 1) (C + 1) = 1 := by
      unfold gsShift; rw [if_pos (by omega)]
    have hn : gsNextQ 1 1 (C + 1) (C + 1) = C := by
      unfold gsNextQ; rw [if_pos (by omega)]; omega
    show C * (Phi 1 (shifted 1 1 (C + 1) (⟨0, C + 1⟩ : ScanState))
        - Phi 1 (⟨0, C + 1⟩ : ScanState)) < 2 * (C + 1)
    unfold shifted
    show C * (Phi 1 (⟨0 + gsShift 1 1 (C + 1) (C + 1), gsNextQ 1 1 (C + 1) (C + 1)⟩ :
        ScanState) - Phi 1 (⟨0, C + 1⟩ : ScanState)) < 2 * (C + 1)
    rw [hg, hn]
    show C * (2 * (0 + 1) + C - (2 * 0 + (C + 1))) < 2 * (C + 1)
    have e : 2 * (0 + 1) + C - (2 * 0 + (C + 1)) = 1 := by omega
    rw [e]
    omega

#print axioms rewind_pointwise_reset
#print axioms rewind_not_pointwise

end PointwiseGap
end PalPeg
