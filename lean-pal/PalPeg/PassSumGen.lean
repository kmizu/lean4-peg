import PalPeg.PassSum10
import PalPeg.PassSum7
import PalPeg.EndToEnd2

/-!
# 任意アルファベット版の周期和仮説 (`PassSumGen`)

`EndToEnd2.PassPeriodSum k C₁` は `x : List (Fin 2)` について述べられているが、
機械アルファベット `Fin sc`（入力 2 記号＋特殊記号）で段を動かすには、
`StageTapes.PrepOnTapes.len_le` が **`Fin sc` 上のすべての語** についての周期和の
上界を要求する（`len_le` は `w` について全称なので、`PassSumRelabel` の
2 記号 relabeling では埋まらない：`InputEmbed` の注記を参照）。

幸い `PassSum10` の鎖は**アルファベットについて完全に一般**である：

* `PassSum10.lastChildBound_holds : LastChildBound x 8 b`（無条件、`α` 一般）、
* `PassSum10.rootGrowth_of_consumption : Consumption x 8 b → RootGrowth x 8 b`（`α` 一般）、
* `PassSum10.passSum_le_two_max_of_treeFacts`（`α` 一般）、
* `PalPeg.passSumLinear_of_sum_le_max`（`α` 一般）。

`Fin 2` に固定されているのは最後のラッパー
（`PassSum7.passPeriodSum_eight_of_sum_le_max` /
`PassSum10.passPeriodSum_eight_of_treeFacts` / `_of_consumption`）だけなので、
本ファイルはその 3 つの `α` 一般版を与える。
-/

set_option autoImplicit false

namespace PalPeg
namespace PassSumGen

universe u

/-- **`EndToEnd2.PassPeriodSum` の任意アルファベット版**。 -/
def PassPeriodSumGen (α : Type u) [DecidableEq α] (k C₁ : ℕ) : Prop :=
  ∀ (x : List α) (b s : ℕ), stripLoop2Periods x k b (x.length + 1) s ≤ C₁ * b

/-- `α = Fin 2` では `EndToEnd2.PassPeriodSum` そのもの。 -/
theorem passPeriodSumGen_fin_two_iff (k C₁ : ℕ) :
    PassPeriodSumGen (Fin 2) k C₁ ↔ EndToEnd2.PassPeriodSum k C₁ := Iff.rfl

variable {α : Type u} [DecidableEq α]

/-- **`PassSum7.passPeriodSum_eight_of_sum_le_max` の `α` 一般版**：
`Σ ≤ 2 * max` なら `PassPeriodSumGen α 8 2`。 -/
theorem passPeriodSumGen_of_sum_le_max
    (h : ∀ (x : List α) (b s : ℕ),
      stripLoop2Periods x 8 b (x.length + 1) s
        ≤ 2 * stripLoop2MaxPeriod x 8 b (x.length + 1) s) :
    PassPeriodSumGen α 8 2 := by
  intro x b s
  exact passSumLinear_of_sum_le_max x 8 2 (fun b s => h x b s) b s

/-- **`PassSum10.passPeriodSum_eight_of_treeFacts` の `α` 一般版**：
木の性質 `PassTreeFacts` から `PassPeriodSumGen α 8 2`。 -/
theorem passPeriodSumGen_of_treeFacts
    (h : ∀ (x : List α) (b : ℕ), PassSum10.PassTreeFacts x 8 b) :
    PassPeriodSumGen α 8 2 := by
  refine passPeriodSumGen_of_sum_le_max (fun x b s => ?_)
  by_cases hs : s ≤ x.length
  · exact PassSum10.passSum_le_two_max_of_treeFacts x 8 b (by omega) (h x b) s hs
  · have hdrop : x.drop s = [] := by
      apply List.drop_eq_nil_of_le; omega
    have hfo : firstOuter (x.drop s) 8 b (x.length + 1) 1 = none := by
      rw [hdrop, firstOuter]
      simp
    rw [stripLoop2Periods_of_none x 8 b hfo]
    exact Nat.zero_le _

/-- **主結果**：消費量補題 `PassSum10.Consumption` の `α` 一般版から
`PassPeriodSumGen α 8 2`。`LastChildBound` は無条件
（`PassSum10.lastChildBound_holds`）、`RootGrowth` は
`PassSum10.rootGrowth_of_consumption` が与える。 -/
theorem passPeriodSumGen_of_consumption
    (h : ∀ (x : List α) (b : ℕ), PassSum10.Consumption x 8 b) :
    PassPeriodSumGen α 8 2 :=
  passPeriodSumGen_of_treeFacts
    (fun x b => ⟨PassSum10.rootGrowth_of_consumption x b (h x b),
      PassSum10.lastChildBound_holds x b⟩)

/-- **`stageIface` が要求する形**（`hsum` フィールドそのもの）を、
消費量補題から直接与える。 -/
theorem hsum_of_consumption {sc : ℕ}
    (h : ∀ (x : List (Fin sc)) (b : ℕ), PassSum10.Consumption x 8 b)
    (y : List (Fin sc)) (b s : ℕ) :
    stripLoop2Periods y 8 b (y.length + 1) s ≤ 2 * b :=
  passPeriodSumGen_of_consumption h y b s

/-- 系：`α = Fin 2` に落とせば従来の `EndToEnd2.PassPeriodSum 8 2`。 -/
theorem passPeriodSum_eight_of_consumption_gen
    (h : ∀ (x : List (Fin 2)) (b : ℕ), PassSum10.Consumption x 8 b) :
    EndToEnd2.PassPeriodSum 8 2 :=
  passPeriodSumGen_of_consumption h

section Audit

#print axioms passPeriodSumGen_of_sum_le_max
#print axioms passPeriodSumGen_of_treeFacts
#print axioms passPeriodSumGen_of_consumption
#print axioms hsum_of_consumption
#print axioms passPeriodSum_eight_of_consumption_gen

end Audit

end PassSumGen
end PalPeg
