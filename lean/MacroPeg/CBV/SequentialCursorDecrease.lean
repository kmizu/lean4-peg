import MacroPeg.CBV.SequentialCursorEntryMachine

/-! A successful input-character consumption moves one bit from the first
cursor difference into the next difference, if there is a next cursor. -/
namespace Shallot.MacroPeg.CBV.SequentialCursorDecrease
open SequentialCursorEdit SequentialCursorChain

def lowerRest (rest : List Nat) : List Nat := if rest = [] then [] else rest ++ [1]

theorem lowerRest_length (rest : List Nat) : (lowerRest rest).length ≤ rest.length+1 := by
  unfold lowerRest
  split <;> simp_all

theorem lowerRest_relative {p n : Nat} {ps : List Nat} (h : Chain (p+1) ps n) :
    lowerRest (blocks (deltas (p+1) ps)) = blocks (deltas p ps) := by
  cases h with
  | nil => rfl
  | @cons _ q _ qs hq ht =>
    have hn : blocks (deltas (p+1) (q :: qs)) ≠ [] := by simp [deltas,blocks_cons]
    have he : q-(p+1)+1 = q-p := by omega
    rw [lowerRest,if_neg hn]
    simp only [deltas,blocks_cons,List.append_assoc]
    rw [← List.replicate_succ',he]

theorem lower_current {p n : Nat} {ps : List Nat} (h : Chain (p+1) ps n) :
    lowerRest (blocks (deltas (p+1) ps)) ++ [0] ++ unary p = cursors (p :: ps) := by
  rw [lowerRest_relative h,cursors_cons]

end Shallot.MacroPeg.CBV.SequentialCursorDecrease
