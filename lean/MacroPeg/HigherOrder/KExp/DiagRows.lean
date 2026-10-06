import MacroPeg.HigherOrder.KExp.Diag

/-!
# Whole chunks make well-formed rows

When the numbers come in whole chunks of `2k+1`, every chunk is whole (`chunks_whole`), so every row read back
writes and moves on `k` tapes (`tableOfNums_rowsOK`).
-/

namespace Shallot.MacroPeg.KExp

open Complexity
open Complexity.Univ

theorem chunks_whole (n : Nat) (hn : 0 < n) : ∀ (f : Nat) (l : List Nat), l.length % n = 0 →
    ∀ ch ∈ chunks n f l, ch.length = n
  | 0, _, _ => by simp [chunks]
  | f + 1, l, hm => by
    intro ch hch
    unfold chunks at hch
    split at hch
    · simp at hch
    · rename_i hl
      have hpos : 0 < l.length := List.length_pos_iff.2 hl
      have hle : n ≤ l.length := by
        rcases Nat.lt_or_ge l.length n with h | h
        · rw [Nat.mod_eq_of_lt h] at hm; omega
        · exact h
      rcases List.mem_cons.1 hch with rfl | hch
      · simp; omega
      · refine chunks_whole n hn f (l.drop n) ?_ ch hch
        rw [List.length_drop]
        have : l.length = (l.length - n) + n := by omega
        rw [this, Nat.add_mod_right] at hm
        exact hm

/-- **Rows read from whole chunks write and move on `k` tapes.** -/
theorem tableOfNums_rowsOK {k nq na : Nat} {rest : List Nat} (hm : rest.length % (2 * k + 1) = 0) :
    RowsOK (tableOfNums k nq na rest) := by
  intro r hr
  simp only [tableOfNums, decRows, List.mem_map] at hr
  obtain ⟨ch, hch, rfl⟩ := hr
  have hlen := chunks_whole (2 * k + 1) (by omega) _ rest hm ch hch
  cases ch with
  | nil => simp at hlen
  | cons q rest' =>
    simp only [List.length_cons] at hlen
    simp only [rowOfChunk, tableOfNums, List.length_take, List.length_drop]
    omega

end Shallot.MacroPeg.KExp
