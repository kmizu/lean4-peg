import Complexity.Univ.Code
import MacroPeg.HigherOrder.KExp.Hard

/-!
# The diagonal language of height `j`

The bits `w` are read as the unary list `[k, nq, na, c, d] ++ encRows rows`: a table and two constants (the rows
must come in whole chunks of `2k+1` numbers). `w` is in `Diag j` when that table, run on `w` itself for `tower j (c·(|w|+1)^d)` steps, is not in the accepting state 0.

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
    rest.length % (2 * k + 1) = 0 ∧ (frun (tableOfNums k nq na rest) (finit k w) (diagSteps j c d w)).state ≠ 0
  | _ => False

theorem encRows_length {T : TTable} (h : RowsOK T) : (encRows T.rows).length = T.rows.length * (2 * T.k + 1) := by
  have : ∀ rows : List Row, (∀ r ∈ rows, r.2.1.length = T.k ∧ r.2.2.length = T.k) →
      (encRows rows).length = rows.length * (2 * T.k + 1) := by
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
  exact this T.rows h

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
  have hlen : (encRows (tableOf M).rows).length % (2 * k + 1) = 0 := by
    rw [encRows_length (tableOf_rowsOK M)]; exact Nat.mul_mod_left _ _
  unfold Diag
  rw [hd]
  simp only [hlen, true_and]
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
