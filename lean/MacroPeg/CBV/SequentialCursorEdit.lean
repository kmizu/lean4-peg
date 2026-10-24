import MacroPeg.CBV.SequentialSharedStateBound
import Complexity.ListAppend
import Complexity.ListIOSpec

/-! Algebra of local edits on the reversed binary cursor stream. The list
machine below uses symbols 1 for true and 0 for the block terminator. -/
namespace Shallot.MacroPeg.CBV.SequentialCursorEdit
open SequentialCursorChain

abbrev unary (n : Nat) : List Nat := List.replicate n 1

def bits (bs : List Bool) : List Nat := (bs.map Complexity.bitElem).reverse
def blocks (ds : List Nat) : List Nat := bits (encodeDeltas ds)
def cursors (ps : List Nat) : List Nat := bits (encode ps)

theorem bits_length (bs : List Bool) : (bits bs).length = bs.length := by simp [bits]

theorem blocks_cons (d : Nat) (ds : List Nat) :
    blocks (d :: ds) = blocks ds ++ [0] ++ unary d := by
  simp [blocks,bits,encodeDeltas,Complexity.bitElem,List.reverse_append,List.append_assoc]

theorem cursors_cons (p : Nat) (ps : List Nat) :
    cursors (p :: ps) = blocks (deltas p ps) ++ [0] ++ unary p := by
  simp only [cursors,encode,deltas,Nat.sub_zero]
  exact blocks_cons p (deltas p ps)

/-- Removing a cursor merges its difference into the next block. If there is
no following cursor, its data bits are discarded together with its delimiter. -/
def dropResult (d : Nat) (rest : List Nat) : List Nat :=
  if rest = [] then [] else rest ++ unary d

theorem dropResult_length (d : Nat) (rest : List Nat) :
    (dropResult d rest).length ≤ rest.length + d := by
  unfold dropResult
  split <;> simp_all

theorem drop_relative {p q n : Nat} {ps : List Nat} (hp : p ≤ q) (h : Chain q ps n) :
    dropResult (q-p) (blocks (deltas q ps)) = blocks (deltas p ps) := by
  cases h with
  | nil => rfl
  | @cons _ r _ rs hq ht =>
    have hn : blocks (deltas q (r :: rs)) ≠ [] := by simp [deltas,blocks_cons]
    have he : (r-q) + (q-p) = r-p := by omega
    rw [dropResult,if_neg hn]
    simp only [deltas,blocks_cons,List.append_assoc]
    rw [List.replicate_append_replicate,he]

theorem drop_current {p n : Nat} {ps : List Nat} (h : Chain p ps n) :
    dropResult p (blocks (deltas p ps)) = cursors ps := by
  change _ = blocks (deltas 0 ps)
  simpa only [Nat.sub_zero] using drop_relative (Nat.zero_le p) h

theorem duplicate_current (p : Nat) (ps : List Nat) :
    blocks (deltas p ps) ++ [0,0] ++ unary p = cursors (p :: p :: ps) := by
  rw [cursors_cons]
  simp only [deltas,Nat.sub_self,blocks_cons,List.replicate_zero,List.append_nil,List.append_assoc]
  rfl

theorem drop_saved {p q n : Nat} {ps : List Nat} (hp : p ≤ q) (h : Chain q ps n) :
    dropResult (q-p) (blocks (deltas q ps)) ++ [0] ++ unary p = cursors (p :: ps) := by
  rw [drop_relative hp h,cursors_cons]

end Shallot.MacroPeg.CBV.SequentialCursorEdit
