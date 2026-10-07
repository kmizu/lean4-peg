import Complexity.Comp.Basic
import Complexity.Univ.Code
import Complexity.Univ.CodeSize

/-!
# A one-tape machine accepting its own code

`K1 w` holds when `w` is the unary code `[1, nq, na] ++ rows` of a one-tape table (rows in whole chunks of 3) and that
table, run on `w` itself, reaches the accepting state 0. On the code of a machine it asks whether the machine
accepts its code (`k1_code`).
-/

namespace Complexity

open Complexity.Univ

/-- The table read from `nq :: na :: rest`, one tape. -/
def table1 (nq na : Nat) (rest : List Nat) : TTable := ⟨1, nq, na, decRows 1 rest⟩

/-- **A one-tape table accepting its own code.** -/
def K1 : Lang := fun w =>
  match deUnary w with
  | 1 :: nq :: na :: rest => rest.length % 3 = 0 ∧ ∃ t, (frun (table1 nq na rest) (finit 1 w) t).state = 0
  | _ => False

/-- The code of a one-tape machine. -/
def code1 (M : TM 1) : List Bool := unary ([1, M.nq, M.na] ++ encRows (tableOf M).rows)

theorem encRows_length1 (M : TM 1) : (encRows (tableOf M).rows).length % 3 = 0 := by
  have h := tableOf_rowsOK M
  have : ∀ rows : List Row, (∀ r ∈ rows, r.2.1.length = 1 ∧ r.2.2.length = 1) →
      (encRows rows).length = rows.length * 3 := by
    intro rows
    induction rows with
    | nil => intro _; simp [encRows]
    | cons r rows ih =>
      intro hr
      have h₁ := hr r (by simp)
      have h₂ := ih (fun r' h' => hr r' (by simp [h']))
      have e : encRows (r :: rows) = (r.1 :: r.2.1 ++ r.2.2) ++ encRows rows := by simp [encRows]
      rw [e, List.length_append, h₂]
      simp only [List.length_cons, List.length_append, h₁.1, h₁.2, Nat.succ_mul]; omega
  rw [this _ h]; exact Nat.mul_mod_left _ _

/-- On the code of a one-tape machine, `K1` asks whether the machine accepts its code. -/
theorem k1_code (M : TM 1) : K1 (code1 M) ↔ ∃ t, (M.run (initCfg 1 (code1 M)) t).state = 0 := by
  have hd : deUnary (code1 M) = 1 :: M.nq :: M.na :: encRows (tableOf M).rows := by
    rw [code1, deUnary_unary]; rfl
  have ht : table1 M.nq M.na (encRows (tableOf M).rows) = tableOf M := by
    have hr : decRows 1 (encRows (tableOf M).rows) = (tableOf M).rows := decRows_encRows (tableOf_rowsOK M)
    simp only [table1, hr]; rfl
  unfold K1
  rw [hd]
  simp only [encRows_length1 M, true_and]
  rw [ht]
  exact ⟨fun ⟨t, h⟩ => ⟨t, by rw [← frun_state]; exact h⟩, fun ⟨t, h⟩ => ⟨t, by rw [frun_state]; exact h⟩⟩

/-- A decider accepts exactly where its halted state is 0. -/
theorem accepts_iff {k : Nat} {M : TM k} {L : Lang} (h : M.Decides L) (w : List Bool) :
    (∃ t, (M.run (initCfg k w) t).state = 0) ↔ L w := by
  obtain ⟨t, ht, hL⟩ := h w
  constructor
  · rintro ⟨u, hu⟩
    have hu' : (M.run (initCfg k w) u).halted := .inl hu
    have e : (M.run (initCfg k w) t).state = (M.run (initCfg k w) u).state := by
      rcases Nat.le_total t u with hle | hle
      · rw [TM.run_stays M _ hle ht]
      · rw [TM.run_stays M _ hle hu']
    exact hL.1 (e.trans hu)
  · intro hw; exact ⟨t, hL.2 hw⟩

end Complexity
