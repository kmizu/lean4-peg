import Complexity.Univ.SimSpec

/-!
# Lists of numbers as bits, and tables as numbers

A list of numbers is written in unary, each number as that many `true`s and a `false` (`unary`), and read back
by `deUnary` (`deUnary_unary`). The rows of a table with `k` tapes are read back from `encRows` in chunks of
`2k+1` numbers (`decRows_encRows`).
-/

namespace Complexity.Univ

def unary (l : List Nat) : List Bool := l.flatMap fun n => List.replicate n true ++ [false]

/-- Read unary numbers, `a` being the count of the number being read. -/
def deUnaryGo : Nat → List Bool → List Nat
  | _, [] => []
  | a, true :: bs => deUnaryGo (a + 1) bs
  | a, false :: bs => a :: deUnaryGo 0 bs

def deUnary (w : List Bool) : List Nat := deUnaryGo 0 w

theorem deUnaryGo_block (a n : Nat) (rest : List Bool) :
    deUnaryGo a (List.replicate n true ++ false :: rest) = (a + n) :: deUnaryGo 0 rest := by
  induction n generalizing a with
  | zero => simp [deUnaryGo]
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append, deUnaryGo, ih]; congr 1; omega

theorem deUnary_unary (l : List Nat) : deUnary (unary l) = l := by
  induction l with
  | nil => rfl
  | cons n l ih =>
    simp only [deUnary, unary, List.flatMap_cons, List.append_assoc, List.singleton_append] at ih ⊢
    rw [deUnaryGo_block, ih, Nat.zero_add]

theorem deUnary_append (l : List Nat) (w : List Bool) : deUnary (unary l ++ w) = l ++ deUnary w := by
  induction l with
  | nil => rfl
  | cons n l ih =>
    simp only [deUnary, unary, List.flatMap_cons, List.append_assoc, List.singleton_append, List.cons_append]
      at ih ⊢
    rw [deUnaryGo_block, List.nil_append, ih, Nat.zero_add]

/-- Cut a list into chunks of `n`, with fuel `f`. -/
def chunks (n : Nat) : Nat → List Nat → List (List Nat)
  | 0, _ => []
  | f + 1, l => if l = [] then [] else l.take n :: chunks n f (l.drop n)

/-- The row of a chunk `q :: ws ++ ms` with `k` tapes. -/
def rowOfChunk (k : Nat) : List Nat → Row
  | [] => (0, [], [])
  | q :: rest => (q, rest.take k, rest.drop k)

def decRows (k : Nat) (l : List Nat) : List Row := (chunks (2 * k + 1) l.length l).map (rowOfChunk k)

theorem chunks_enc (k : Nat) :
    ∀ (rows : List Row) (f : Nat), (∀ r ∈ rows, r.2.1.length = k ∧ r.2.2.length = k) → rows.length ≤ f →
      chunks (2 * k + 1) f (encRows rows) = rows.map fun r => r.1 :: r.2.1 ++ r.2.2
  | [], f, _, _ => by cases f <;> simp [chunks, encRows]
  | r :: rows, f, h, hf => by
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
    have hr := h r (by simp)
    have hlen : (r.1 :: r.2.1 ++ r.2.2).length = 2 * k + 1 := by simp [hr.1, hr.2]; omega
    have he : encRows (r :: rows) = (r.1 :: r.2.1 ++ r.2.2) ++ encRows rows := by simp [encRows]
    rw [chunks, he, if_neg (by simp), List.take_left' hlen, List.drop_left' hlen,
      chunks_enc k rows f (fun r' h' => h r' (by simp [h'])) (by simp at hf; omega)]
    simp

/-- **Rows read back.** -/
theorem decRows_encRows {k : Nat} {rows : List Row} (h : ∀ r ∈ rows, r.2.1.length = k ∧ r.2.2.length = k) :
    decRows k (encRows rows) = rows := by
  have hf : rows.length ≤ (encRows rows).length := by
    have : ∀ (rows : List Row), rows.length ≤ (encRows rows).length := by
      intro rows
      induction rows with
      | nil => simp [encRows]
      | cons r rows ih => simp [encRows] at ih ⊢; omega
    exact this rows
  rw [decRows, chunks_enc k rows _ h hf, List.map_map]
  conv => rhs; rw [← List.map_id rows]
  apply List.map_congr_left
  intro r hr
  obtain ⟨q, ws, ms⟩ := r
  have := h _ hr
  simp only at this
  simp [rowOfChunk, this.1]

/-- The rows of the table of a machine write and move on `k` tapes. -/
theorem tableOf_rowsOK {k : Nat} (M : TM k) : RowsOK (tableOf M) := by
  intro r hr
  simp only [tableOf, List.mem_map] at hr
  obtain ⟨m, _, rfl⟩ := hr
  simp [rowOf, tableOf]

end Complexity.Univ
