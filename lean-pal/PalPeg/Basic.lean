import Mathlib.Computability.Language

/-!
# 二進回文言語 `PAL`

`Language α := Set (List α)`（Mathlib）。`PAL` は `{0,1}*` 上の回文全体。
鎖の環 (5)「`PALᴿ = PAL`」は `List.reverse_reverse` だけで閉じる。
-/

namespace PalPeg

/-- 二進アルファベット `Fin 2` 上の回文言語 `{ w | wᴿ = w }`。 -/
def PAL : Language (Fin 2) := { w | w.reverse = w }

theorem mem_PAL {w : List (Fin 2)} : w ∈ PAL ↔ w.reverse = w := Iff.rfl

/-- 反転不変性：`wᴿ ∈ PAL ↔ w ∈ PAL`。 -/
theorem PAL_reverse_mem (w : List (Fin 2)) : w.reverse ∈ PAL ↔ w ∈ PAL := by
  rw [mem_PAL, mem_PAL, List.reverse_reverse]
  exact eq_comm

/-- `PAL` は自分自身の反転言語である（`Language.reverse` の形）。 -/
theorem PAL_reverse : PAL.reverse = PAL := by
  ext w
  exact PAL_reverse_mem w

end PalPeg
