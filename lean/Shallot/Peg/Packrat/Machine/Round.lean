import Shallot.Peg.Packrat.Machine.Transfer

/-!
# A reusable table round

The invariant gives every old-row occurrence its specified values and
keeps every next row empty. A sweep followed by transfer advances this
invariant and preserves the input, length, scratch, and loop-control data.
-/

namespace Shallot.Packrat.Machine

open Complexity

private theorem get_idxOf (xs : List PExp) (e : PExp) (he : e ∈ xs) :
    xs[xs.idxOf e]'(List.idxOf_lt_length_iff.mpr he) = e := by
  induction xs with
  | nil => cases he
  | cons a xs ih =>
    by_cases ha : a = e
    · subst a; simp
    · have hm : e ∈ xs := by simpa [ha, Ne.symm ha] using he
      simpa only [List.idxOf_cons, show (a == e) = false by simp [ha], cond_false,
        List.getElem_cons_succ] using ih hm

theorem nodeExpr_idx (g : Grammar) (e : PExp) (he : e ∈ dom g) :
    nodeExpr g (nodeIdx g e he) = e := get_idxOf (dom g) e he

/-- A prepared table that can be advanced by another round. -/
structure Ready (g : Grammar) (x : List Char) (n : Nat) (S : Lists (NK g)) : Prop where
  old : ∀ j, S (oldR g j) = row (iter g x n) (nodeExpr g j) x.length
  next : ∀ j, S (nextR g j) = []
  input : S (inpR g) = inputRow x
  len : S (lenR g) = [x.length]
  tmp : S (tmpR g) = []

theorem Ready.rows {g : Grammar} {x : List Char} {n : Nat} {S : Lists (NK g)}
    (h : Ready g x n S) : Rows g x n S := by
  intro e he
  simpa only [nodeExpr_idx] using h.old (nodeIdx g e he)

/-- The private literal cursor may also carry an outer iteration counter. -/
theorem Ready.set_cur {g : Grammar} {x : List Char} {n : Nat} {S : Lists (NK g)}
    (h : Ready g x n S) (l : List Nat) : Ready g x n (S.set (curR g) l) := by
  constructor
  · intro j; rw [Lists.set_ne _ _ (show oldR g j ≠ curR g by packrat_regs)]; exact h.old j
  · intro j; rw [Lists.set_ne _ _ (show nextR g j ≠ curR g by packrat_regs)]; exact h.next j
  · rw [Lists.set_ne _ _ (show inpR g ≠ curR g by packrat_regs)]; exact h.input
  · rw [Lists.set_ne _ _ (show lenR g ≠ curR g by packrat_regs)]; exact h.len
  · rw [Lists.set_ne _ _ (show tmpR g ≠ curR g by packrat_regs)]; exact h.tmp

/-- One sweep followed by the transfer that prepares the next sweep. -/
def roundP (g : Grammar) : NProg (NK g) := .seq (sweep g) (transfer g)

def roundCost (g : Grammar) (N : Nat) : Nat :=
  sweepCost g (List.finRange (dom g).length) N + (dom g).length * (8 * N + 11) + 2

/-- A concrete round advances the prepared-table invariant by one. -/
theorem nruns_roundP (g : Grammar) (x : List Char) (n : Nat) (S : Lists (NK g))
    (h : Ready g x n S) :
    ∃ S', NRuns (roundP g) S S' (roundCost g x.length) ∧ Ready g x (n + 1) S' ∧
      (∀ r, (∀ j, r ≠ oldR g j ∧ r ≠ nextR g j) → S' r = S r) := by
  obtain ⟨S₁, sw, hn, hf⟩ := nruns_sweep g x n S h.rows h.input h.tmp (ll := []) h.len h.next
  obtain ⟨S₂, tr, ht, hfr⟩ := nruns_transferRows g (List.finRange (dom g).length) (finRange_nodup _)
    x.length (fun j => row (iter g x (n + 1)) (nodeExpr g j) x.length) S₁
    (by rw [hf _ (fun j => by packrat_regs)]; exact h.tmp)
    (fun j _ => by rw [hf _ (fun k => old_next_ne g j k), h.old j, row_length]; exact Nat.le_refl _)
    (fun j _ => hn j) (fun _ _ => row_length _ _ _)
  have frame : ∀ r, (∀ j, r ≠ oldR g j ∧ r ≠ nextR g j) → S₂ r = S r := by
    intro r hr
    rw [hfr r (fun j _ => hr j), hf r (fun j => (hr j).2)]
  refine ⟨S₂, (sw.seq tr).mono ?_, ?_, frame⟩
  · simp only [roundCost, List.length_finRange]; omega
  · constructor
    · intro j; exact (ht j (List.mem_finRange j)).1
    · intro j; exact (ht j (List.mem_finRange j)).2
    · rw [frame _ (fun j => by constructor <;> packrat_regs)]; exact h.input
    · rw [frame _ (fun j => by constructor <;> packrat_regs)]; exact h.len
    · rw [frame _ (fun j => by constructor <;> packrat_regs)]; exact h.tmp

def roundCoeff (g : Grammar) : Nat := sweepCoeff g (List.finRange (dom g).length) + 11 * (dom g).length + 2

theorem roundCost_le (g : Grammar) (N : Nat) : roundCost g N ≤ roundCoeff g * (N + 1) ^ 2 := by
  have hs := sweepCost_le g (List.finRange (dom g).length) N
  have hm : N + 1 ≤ (N + 1) ^ 2 := by
    simpa only [Nat.pow_two, Nat.mul_one] using Nat.mul_le_mul_left (N + 1) (show 1 ≤ N + 1 by omega)
  have hl : 8 * N + 11 ≤ 11 * (N + 1) ^ 2 := by omega
  have hh := Nat.mul_le_mul_left (dom g).length hl
  have he : (dom g).length * (11 * (N + 1) ^ 2) = (11 * (dom g).length) * (N + 1) ^ 2 := by
    rw [← Nat.mul_assoc, Nat.mul_comm (dom g).length 11]
  rw [he] at hh
  unfold roundCost roundCoeff
  rw [Nat.add_mul (sweepCoeff g (List.finRange (dom g).length) + 11 * (dom g).length) 2 ((N + 1) ^ 2),
    Nat.add_mul (sweepCoeff g (List.finRange (dom g).length)) (11 * (dom g).length) ((N + 1) ^ 2)]
  omega

end Shallot.Packrat.Machine
