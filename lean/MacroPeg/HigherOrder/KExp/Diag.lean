import Complexity.Univ.Code
import MacroPeg.HigherOrder.KExp.Hard

/-!
# The diagonal language of height `j`

The bits `w` are read as the unary list `[k, nq, na, c, d] ++ encRows rows`: a table and two constants. `w` is in
`Diag j` when that table, run on `w` itself for `tower j (c·(|w|+1)^d)` steps, is not in the accepting state 0.

No machine within such a tower decides `Diag j` (`diag_not_kexp`): on the code of its own table and constants it
would answer the opposite of what it answers.
-/

namespace Shallot.MacroPeg.KExp

open Complexity
open Complexity.Univ
open Shallot.MacroPeg.HO

/-- The table read from a list of numbers `k :: nq :: na :: rows`. -/
def tableOfNums (k nq na : Nat) (rest : List Nat) : TTable := ⟨k, nq, na, decRows k rest⟩

/-- The steps the diagonal machine allows. -/
def diagSteps (j c d : Nat) (w : List Bool) : Nat := tower j (c * (w.length + 1) ^ d)

/-- **The diagonal language of height `j`.** -/
def Diag (j : Nat) : Lang := fun w =>
  match deUnary w with
  | k :: nq :: na :: c :: d :: rest =>
    (frun (tableOfNums k nq na rest) (finit k w) (diagSteps j c d w)).state ≠ 0
  | _ => False

/-- The code of a machine with the constants `c`, `d`. -/
def diagCode {k : Nat} (M : TM k) (c d : Nat) : List Bool := unary ([k, M.nq, M.na, c, d] ++ encRows (tableOf M).rows)

theorem diag_code (j : Nat) {k : Nat} (M : TM k) (c d : Nat) :
    Diag j (diagCode M c d) ↔
      (M.run (initCfg k (diagCode M c d)) (diagSteps j c d (diagCode M c d))).state ≠ 0 := by
  have hd : deUnary (diagCode M c d) = k :: M.nq :: M.na :: c :: d :: encRows (tableOf M).rows := by
    rw [diagCode, deUnary_unary]; rfl
  have ht : tableOfNums k M.nq M.na (encRows (tableOf M).rows) = tableOf M := by
    have hr : decRows k (encRows (tableOf M).rows) = (tableOf M).rows := decRows_encRows (tableOf_rowsOK M)
    simp only [tableOfNums, hr]; rfl
  unfold Diag
  rw [hd]
  simp only
  rw [ht, frun_state]

/-- Two halted runs from the same configuration end in the same state. -/
theorem halted_state_eq {k : Nat} (M : TM k) (c : Complexity.Cfg k) {t u : Nat} (ht : (M.run c t).halted)
    (hu : (M.run c u).halted) : (M.run c t).state = (M.run c u).state := by
  rcases Nat.le_total t u with h | h
  · rw [TM.run_stays M c h ht]
  · rw [TM.run_stays M c h hu]

/-- **No machine within a tower of height `j` decides the diagonal language.** -/
theorem diag_not_kexp (j : Nat) : ¬ KEXP j (Diag j) := by
  rintro ⟨k, M, T, c, d, hT, hdec, htb⟩
  let w := diagCode M c d
  obtain ⟨t, ht, hL⟩ := hdec w
  have hB : (M.run (initCfg k w) (diagSteps j c d w)).halted := by
    rw [TM.run_stays M _ (by unfold diagSteps; exact hT w.length) (htb w)]; exact htb w
  have hs := halted_state_eq M (initCfg k w) ht hB
  have hD := diag_code j M c d
  rw [← hs] at hD
  by_cases h0 : (M.run (initCfg k w) t).state = 0
  · exact hD.1 (hL.1 h0) h0
  · exact h0 (hL.2 (hD.2 h0))

end Shallot.MacroPeg.KExp
