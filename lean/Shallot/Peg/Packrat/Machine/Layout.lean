import Shallot.Peg.Packrat.Stored
import Shallot.Peg.Packrat.Machine.Literal
import Shallot.Peg.Packrat.Machine.Alt
import Shallot.Peg.Packrat.Machine.Star

/-!
# A concrete stack allocation for each grammar

Eight fixed stacks hold input, length, position, scratch data, and loop
counters. Every occurrence in `dom g` has an old row and a next row.
Expression lookup uses its first occurrence; repeated occurrences are safe
because every row for the same expression has the same specified value.
-/

namespace Shallot.Packrat.Machine

/-- Number of stacks in the compiled program. -/
def NK (g : Grammar) : Nat := 8 + 2 * (dom g).length

abbrev Node (g : Grammar) := Fin (dom g).length

def nodeIdx (g : Grammar) (e : PExp) (he : e ∈ dom g) : Node g :=
  ⟨(dom g).idxOf e, List.idxOf_lt_length_iff.mpr he⟩

def inpR (g : Grammar) : Fin (NK g) := ⟨0, by unfold NK; omega⟩
def lenR (g : Grammar) : Fin (NK g) := ⟨1, by unfold NK; omega⟩
def posR (g : Grammar) : Fin (NK g) := ⟨2, by unfold NK; omega⟩
def tmpR (g : Grammar) : Fin (NK g) := ⟨3, by unfold NK; omega⟩
def idxR (g : Grammar) : Fin (NK g) := ⟨4, by unfold NK; omega⟩
def workR (g : Grammar) : Fin (NK g) := ⟨5, by unfold NK; omega⟩
def curR (g : Grammar) : Fin (NK g) := ⟨6, by unfold NK; omega⟩
def countR (g : Grammar) : Fin (NK g) := ⟨7, by unfold NK; omega⟩
def oldR (g : Grammar) (j : Node g) : Fin (NK g) := ⟨8 + j.val, by have := j.isLt; unfold NK; omega⟩
def nextR (g : Grammar) (j : Node g) : Fin (NK g) :=
  ⟨8 + (dom g).length + j.val, by have := j.isLt; unfold NK; omega⟩

/-- Disjointness of the concrete allocated registers. -/
macro "packrat_regs" : tactic =>
  `(tactic| (simp [List.nodup_cons, inpR, lenR, posR, tmpR, idxR, workR, curR, countR, oldR, nextR]
    <;> omega))

theorem layout_disjoint (g : Grammar) (a b : Node g) :
    [inpR g, lenR g, posR g, tmpR g, idxR g, workR g, curR g, countR g, oldR g a, nextR g b].Nodup := by
  packrat_regs

/-- The old rows realize a round of the original table specification. -/
def Rows (g : Grammar) (x : List Char) (n : Nat) (S : Complexity.Lists (NK g)) : Prop :=
  ∀ e (he : e ∈ dom g), S (oldR g (nodeIdx g e he)) = row (iter g x n) e x.length

end Shallot.Packrat.Machine
