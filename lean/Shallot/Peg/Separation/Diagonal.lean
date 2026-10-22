import Shallot.Peg.Packrat.Machine.TM
import MacroPeg.HigherOrder.KExp.DiagCost

/-!
# A diagonal language against a fixed polynomial degree

The simulation budget is `(input length + 1)^(p + 1)`. The unary header
contains the candidate coefficient as padding, which makes that budget
cover every candidate running within degree `p`. Header exponents are not
used by the diagonal machine.
-/

namespace Shallot.PegSeparation

open Complexity Complexity.Univ
open Shallot.MacroPeg.KExp
open Shallot.Packrat.Machine

/-- A fixed simulation budget, independent of all exponents in the input. -/
def polySteps (p : Nat) (w : List Bool) : Nat := (w.length + 1) ^ (p + 1)

/-- The polynomial diagonal language, with the header coefficients used only as padding. -/
def PolyDiag (p : Nat) (w : List Bool) : Prop :=
  match deUnary w with
  | k :: nq :: na :: _ :: _ :: rest =>
    rest.length % (2 * k + 1) = 0 ∧
      (frun (tableOfNums k nq na rest) (finit k w) (polySteps p w)).state ≠ 0
  | _ => False

/-- The machine's own code forces the opposite of its acceptance state. -/
theorem polyDiag_code (p : Nat) {k : Nat} (M : TM k) (c : Nat) :
    PolyDiag p (diagCode M c p) ↔
      (M.run (initCfg k (diagCode M c p)) (polySteps p (diagCode M c p))).state ≠ 0 := by
  have hd : deUnary (diagCode M c p) = k :: M.nq :: M.na :: c :: p :: encRows (tableOf M).rows := by
    rw [diagCode, deUnary_unary]; rfl
  have ht : tableOfNums k M.nq M.na (encRows (tableOf M).rows) = tableOf M := by
    have hr : decRows k (encRows (tableOf M).rows) = (tableOf M).rows := decRows_encRows (tableOf_rowsOK M)
    simp only [tableOfNums, hr]; rfl
  have hlen : (encRows (tableOf M).rows).length % (2 * k + 1) = 0 := by
    rw [encRows_length (tableOf_rowsOK M)]; exact Nat.mul_mod_left _ _
  unfold PolyDiag
  rw [hd]
  simp only [hlen, true_and]
  rw [ht, frun_state]

/-- The padding coefficient fits inside the length of its unary code. -/
theorem coeff_le_code {k : Nat} (M : TM k) (c p : Nat) : c ≤ (diagCode M c p).length := by
  have hh := deUnary_bound (diagCode M c p)
  have hd : deUnary (diagCode M c p) = k :: M.nq :: M.na :: c :: p :: encRows (tableOf M).rows := by
    rw [diagCode, deUnary_unary]; rfl
  rw [hd] at hh
  simp only [List.sum_cons, List.length_cons] at hh
  omega

/-- No multitape machine within degree `p` decides this language. -/
theorem polyDiag_not_time (p : Nat) :
    ¬ ∃ (k : Nat) (M : TM k) (c : Nat), M.Decides (PolyDiag p) ∧
      ∀ w, (M.run (initCfg k w) (c * (w.length + 1) ^ p)).halted := by
  rintro ⟨k, M, c, hdec, htime⟩
  let w := diagCode M c p
  have hB : c * (w.length + 1) ^ p ≤ polySteps p w := by
    have hc : c ≤ w.length := coeff_le_code M c p
    unfold polySteps
    rw [Nat.pow_succ, Nat.mul_comm ((w.length + 1) ^ p) (w.length + 1)]
    exact Nat.mul_le_mul_right _ (by omega)
  have hhalt : (M.run (initCfg k w) (polySteps p w)).halted := by
    rw [TM.run_stays M _ hB (htime w)]; exact htime w
  obtain ⟨t, ht, hL⟩ := hdec w
  have hs := halted_state_eq M (initCfg k w) ht hhalt
  have hd := polyDiag_code p M c
  rw [← hs] at hd
  by_cases h0 : (M.run (initCfg k w) t).state = 0
  · exact hd.mp (hL.mp h0) h0
  · exact h0 (hL.mpr (hd.mpr h0))

/-- The degree-15 polynomial diagonal language is outside every PEG on the fixed input characters. -/
theorem polyDiag_not_peg (f : Bool → Char) :
    ¬ ∃ g : Grammar, ∀ w, PolyDiag 15 w ↔ bitLanguage g f w := by
  rintro ⟨g, hg⟩
  obtain ⟨M, c, hdec, ht⟩ := bitLanguage_time15 g f
  apply polyDiag_not_time 15
  refine ⟨_, M, c, ?_, ht⟩
  intro w
  obtain ⟨t, hh, hL⟩ := hdec w
  exact ⟨t, hh, hL.trans (hg w).symm⟩

end Shallot.PegSeparation
