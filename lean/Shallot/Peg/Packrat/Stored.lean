import Shallot.Peg.Packrat.Main

/-!
# Materialized finite tables

Every round reads only the saved entries of the preceding round. Unlike
`iter`, the stored implementation does not recursively recompute table
entries when looking them up. Linear association-list lookup suffices here;
a machine-level complexity theorem is a separate step.
-/

namespace Shallot.Packrat

deriving instance DecidableEq for PExp

/-- A finite table with expression-position keys. -/
abbrev Saved := List ((PExp × Nat) × Option Res)

/-- Missing entries read as unknown. -/
def fetch : Saved → Tbl
  | [], _, _ => none
  | ((a, j), r) :: rest, e, i => if e = a ∧ i = j then r else fetch rest e i

/-- Evaluate a function table once at each relevant cell and save its values. -/
def save (g : Grammar) (x : List Char) (T : Tbl) : Saved :=
  (cells g x).map fun (e, i) => ((e, i), T e i)

private theorem fetch_map (cs : List (PExp × Nat)) (T : Tbl) (e : PExp) (i : Nat)
    (h : (e, i) ∈ cs) :
    fetch (cs.map fun (a, j) => ((a, j), T a j)) e i = T e i := by
  induction cs with
  | nil => cases h
  | cons c cs ih =>
    rcases c with ⟨a, j⟩
    simp only [List.map_cons, fetch]
    split
    · rename_i he
      obtain ⟨rfl, rfl⟩ := he
      rfl
    · rename_i he
      apply ih
      rcases List.mem_cons.mp h with heq | hin
      · cases heq; exact False.elim (he ⟨rfl, rfl⟩)
      · exact hin

theorem fetch_save {g : Grammar} {x : List Char} {T : Tbl} {e : PExp} {i : Nat}
    (he : e ∈ dom g) (hi : i ≤ x.length) : fetch (save g x T) e i = T e i :=
  fetch_map (cells g x) T e i (mem_cells.mpr ⟨he, hi⟩)

/-- Fill finite tables by rounds, retaining each previously computed value. -/
def stored (g : Grammar) (x : List Char) : Nat → Saved
  | 0 => save g x (fun _ _ => none)
  | n + 1 => save g x (F g x (fetch (stored g x n)))

/-- The finite implementation agrees with the function-table specification. -/
theorem stored_eq_iter (g : Grammar) (x : List Char) (n : Nat)
    (e : PExp) (he : e ∈ dom g) (i : Nat) (hi : i ≤ x.length) :
    fetch (stored g x n) e i = iter g x n e i := by
  induction n generalizing e i with
  | zero => exact fetch_save he hi
  | succ n ih =>
    rw [stored, fetch_save he hi, iter]
    exact (round_congr (fun a ha j hj => (ih a ha j hj).symm)
      (fun _ _ _ _ _ hv => iter_consumption hv) e he i hi).symm

/-- The stored recognizer at the proved bound. -/
def storedParse (g : Grammar) (x : List Char) : Option Res :=
  fetch (stored g x (bound g x)) (.nt g.start) 0

theorem storedParse_eq (g : Grammar) (x : List Char) : storedParse g x = parse g x :=
  stored_eq_iter g x (bound g x) _ (dom_start g) 0 (Nat.zero_le x.length)

/-- The executable finite table distinguishes exactly the semantic outcomes. -/
theorem storedParse_iff {g : Grammar} {x : List Char} {r : Res} :
    storedParse g x = some r ↔ ∃ o, Derives g (.nt g.start) x o ∧ erase x o = r := by
  rw [storedParse_eq, parse_iff]

theorem storedParse_none_iff {g : Grammar} {x : List Char} :
    storedParse g x = none ↔ ∀ o, ¬ Derives g (.nt g.start) x o := by
  rw [storedParse_eq, parse_none_iff]

end Shallot.Packrat
