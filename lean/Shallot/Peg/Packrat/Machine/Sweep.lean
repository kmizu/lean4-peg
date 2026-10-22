import Shallot.Peg.Packrat.Machine.Row

/-!
# A complete sweep over the next table

One concrete row program is generated for every occurrence in `dom g`.
A sweep fills every next row and preserves every old row. Repeated syntax
in the domain causes separate, equal rows rather than an aliasing issue.
-/

namespace Shallot.Packrat.Machine

open Complexity

def nodeExpr (g : Grammar) (j : Node g) : PExp := (dom g)[j.val]

theorem nodeExpr_mem (g : Grammar) (j : Node g) : nodeExpr g j ∈ dom g := List.getElem_mem j.isLt

@[simp] theorem nextR_inj (g : Grammar) (a b : Node g) : nextR g a = nextR g b ↔ a = b := by
  constructor
  · intro h
    apply Fin.ext
    have hh := congrArg Fin.val h
    simp only [nextR] at hh
    omega
  · intro h; cases h; rfl

/-- Generate a sequence of whole-row programs. -/
def sweepRows (g : Grammar) : List (Node g) → NProg (NK g)
  | [] => nskip (countR g)
  | j :: js => .seq (fillRow g (nodeExpr g j) (nodeExpr_mem g j) j) (sweepRows g js)

/-- The exact final contents of the next rows after a generated sequence. -/
def swept (g : Grammar) (x : List Char) (n : Nat) : Lists (NK g) → List (Node g) → Lists (NK g)
  | S, [] => S
  | S, j :: js => swept g x n (S.set (nextR g j)
      (S (nextR g j) ++ row (iter g x (n + 1)) (nodeExpr g j) x.length)) js

def sweepCost (g : Grammar) (js : List (Node g)) (N : Nat) : Nat :=
  (js.map fun j => rowCost (nodeExpr g j) N).sum + 2

/-- An untouched register has its original contents after the sweep. -/
theorem swept_frame (g : Grammar) (x : List Char) (n : Nat) (js : List (Node g))
    (S : Lists (NK g)) (r : Fin (NK g)) (h : ∀ j ∈ js, r ≠ nextR g j) :
    swept g x n S js r = S r := by
  induction js generalizing S with
  | nil => rfl
  | cons j js ih =>
    simp only [swept]
    rw [ih _ (fun k hk => h k (List.mem_cons_of_mem _ hk)), Lists.set_ne _ _ (h j List.mem_cons_self)]

/-- The generated sweep has exactly the specified final state and step budget. -/
theorem nruns_sweepRows (g : Grammar) (x : List Char) (n : Nat) (js : List (Node g))
    (S : Lists (NK g)) (hrows : Rows g x n S) (hinput : S (inpR g) = inputRow x)
    (htmp : S (tmpR g) = []) {ll : List Nat} (hlen : S (lenR g) = ll ++ [x.length]) :
    NRuns (sweepRows g js) S (swept g x n S js) (sweepCost g js x.length) := by
  induction js generalizing S with
  | nil => exact nruns_skip (countR g) S
  | cons j js ih =>
    have rx := nruns_fillRow g x n (nodeExpr g j) (nodeExpr_mem g j) j S hrows hinput htmp hlen
    let S₁ := S.set (nextR g j) (S (nextR g j) ++ row (iter g x (n + 1)) (nodeExpr g j) x.length)
    have tx := ih S₁ (hrows.set_next _ _)
      (by simp only [S₁, Lists.set_ne _ _ (show inpR g ≠ nextR g j by packrat_regs)]; exact hinput)
      (by simp only [S₁, Lists.set_ne _ _ (show tmpR g ≠ nextR g j by packrat_regs)]; exact htmp)
      (by simp only [S₁, Lists.set_ne _ _ (show lenR g ≠ nextR g j by packrat_regs)]; exact hlen)
    exact (rx.seq tx).mono (by simp [sweepCost]; omega)

/-- A row not in the sweep is unchanged. -/
theorem swept_next_not_mem (g : Grammar) (x : List Char) (n : Nat) (js : List (Node g))
    (S : Lists (NK g)) (j : Node g) (hj : j ∉ js) :
    swept g x n S js (nextR g j) = S (nextR g j) := by
  apply swept_frame
  intro k hk he
  exact hj ((nextR_inj g j k).mp he ▸ hk)

/-- Sweeping distinct empty next rows fills each with its specified values. -/
theorem swept_next_mem (g : Grammar) (x : List Char) (n : Nat) (js : List (Node g))
    (hn : js.Nodup) (S : Lists (NK g)) (hz : ∀ j ∈ js, S (nextR g j) = []) :
    ∀ j ∈ js, swept g x n S js (nextR g j) = row (iter g x (n + 1)) (nodeExpr g j) x.length := by
  induction js generalizing S with
  | nil => simp
  | cons k js ih =>
    obtain ⟨hk, hjs⟩ := List.nodup_cons.mp hn
    intro j hj
    simp only [swept]
    rcases List.mem_cons.mp hj with rfl | hj
    · rw [swept_next_not_mem g x n js _ j hk, Lists.set_same, hz j List.mem_cons_self, List.nil_append]
    · apply ih hjs _ _ j hj
      intro a ha
      have hne : nextR g a ≠ nextR g k := by
        intro he
        have := (nextR_inj g a k).mp he
        exact hk (this ▸ ha)
      rw [Lists.set_ne _ _ hne]
      exact hz a (List.mem_cons_of_mem _ ha)

private theorem finRange_nodup (N : Nat) : (List.finRange N).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_iff_getElem]
  intro i j hi hj hij he
  have hh := congrArg Fin.val he
  simp at hh
  omega

/-- A full sweep, containing every old-table expression occurrence once. -/
def sweep (g : Grammar) : NProg (NK g) := sweepRows g (List.finRange (dom g).length)

/-- Full-sweep correctness on all rows, with its concrete execution and frame property. -/
theorem nruns_sweep (g : Grammar) (x : List Char) (n : Nat) (S : Lists (NK g))
    (hrows : Rows g x n S) (hinput : S (inpR g) = inputRow x) (htmp : S (tmpR g) = [])
    {ll : List Nat} (hlen : S (lenR g) = ll ++ [x.length])
    (hz : ∀ j, S (nextR g j) = []) :
    ∃ S', NRuns (sweep g) S S' (sweepCost g (List.finRange (dom g).length) x.length) ∧
      (∀ j, S' (nextR g j) = row (iter g x (n + 1)) (nodeExpr g j) x.length) ∧
      (∀ r, (∀ j, r ≠ nextR g j) → S' r = S r) := by
  refine ⟨swept g x n S (List.finRange (dom g).length), nruns_sweepRows g x n _ S hrows hinput htmp hlen, ?_, ?_⟩
  · intro j
    exact swept_next_mem g x n _ (finRange_nodup _) S (fun k _ => hz k) j (List.mem_finRange j)
  · intro r hr
    exact swept_frame g x n _ S r (fun j _ => hr j)

/-- Each whole-row budget is bounded by a quadratic with a fixed coefficient. -/
theorem rowCost_le (e : PExp) (N : Nat) : rowCost e N ≤ (cellCoeff e + 9) * (N + 1) ^ 2 := by
  have hm : N + 1 ≤ (N + 1) * (N + 1) := by
    simpa using Nat.mul_le_mul_left (N + 1) (show 1 ≤ N + 1 by omega)
  have he : rowCost e N = cellCoeff e * ((N + 1) * (N + 1)) + 3 * (N + 1) + 6 := by
    unfold rowCost
    rw [Nat.mul_add, Nat.mul_left_comm (N + 1) (cellCoeff e) (N + 1), Nat.mul_comm (N + 1) 3]
  rw [he, Nat.pow_two, Nat.add_mul (cellCoeff e) 9 ((N + 1) * (N + 1))]
  omega

/-- A grammar-dependent coefficient for sweeping a fixed list of rows. -/
def sweepCoeff (g : Grammar) (js : List (Node g)) : Nat :=
  (js.map fun j => cellCoeff (nodeExpr g j) + 9).sum + 2

theorem sweepCost_le (g : Grammar) (js : List (Node g)) (N : Nat) :
    sweepCost g js N ≤ sweepCoeff g js * (N + 1) ^ 2 := by
  induction js with
  | nil =>
    simp only [sweepCost, sweepCoeff, List.map_nil, List.sum_nil, Nat.zero_add]
    have hh : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow 2 (N + 1) (by omega)
    omega
  | cons j js ih =>
    have hr := rowCost_le (nodeExpr g j) N
    have he : sweepCoeff g (j :: js) = (cellCoeff (nodeExpr g j) + 9) + sweepCoeff g js := by
      simp [sweepCoeff, Nat.add_assoc]
    rw [he, Nat.add_mul]
    simp only [sweepCost, List.map_cons, List.sum_cons] at ih ⊢
    omega

end Shallot.Packrat.Machine
