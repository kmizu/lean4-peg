import MacroPeg.HigherOrder.KExp.DiagCost
import MacroPeg.HigherOrder.KExp.DiagBound
import Complexity.Univ.SimRun

/-!
# The diagonal language is in (j+1)-EXPTIME, and the time hierarchy

The diagonal machine reads the code (`diagFrontP`), simulates the table for the allowed steps (`simP`) and answers
whether the state is not 0 (`ansP`). It decides `Diag j` within `diagBoundN j |w|` steps (`diagP_halts`), which is
below a tower of height `j+1` of a polynomial, so `Diag j` is in `KEXP (j+1)` (`diag_kexp`). With
`diag_not_kexp`, **`KEXP j` is strictly smaller than `KEXP (j+1)`** (`kexp_strict`).
-/

namespace Shallot.MacroPeg.KExp

open Complexity
open Complexity.Univ
open Shallot.MacroPeg.HO

/-- Accept when the state is not 0. -/
def ansP : NProg UK := .ite ST .zero (.halt false) (.halt true)

/-- The diagonal machine. -/
def diagP (j : Nat) : NProg UK := .seq (diagFrontP j) (.seq simP ansP)

/-- An input of the diagonal language has the shape of a code. -/
theorem diag_shape {j : Nat} {w : List Bool} (h : Diag j w) :
    ∃ k nq na c d rest, DiagShape w k nq na c d rest ∧
      (frun (tableOfNums k nq na rest) (finit k w) (diagSteps j c d w)).state ≠ 0 := by
  unfold Diag at h
  split at h
  · rename_i k nq na c d rest hd
    exact ⟨k, nq, na, c, d, rest, ⟨hd, h.1⟩, h.2⟩
  · exact h.elim

theorem diag_of_shape {j : Nat} {w : List Bool} {k nq na c d : Nat} {rest : List Nat}
    (h : DiagShape w k nq na c d rest) :
    Diag j w ↔ (frun (tableOfNums k nq na rest) (finit k w) (diagSteps j c d w)).state ≠ 0 := by
  unfold Diag
  rw [h.1]
  simp only [h.2, true_and]

/-- **The diagonal machine decides `Diag j` within `diagBoundN j |w|` steps.** -/
theorem diagP_halts (j : Nat) (w : List Bool) :
    ∃ b S', NHalts (diagP j) (nInit UK w) b S' (diagBoundN j w.length) ∧ (b = true ↔ Diag j w) := by
  by_cases hs : ∃ k nq na c d rest, DiagShape w k nq na c d rest
  · obtain ⟨k, nq, na, c, d, rest, h⟩ := hs
    obtain ⟨S, x₁, hS, hN, hsc⟩ := diagFront_ok j w h
    have hT := tableOfNums_rowsOK (nq := nq) (na := na) h.2
    have hc : CfgOK (tableOfNums k nq na rest) (finit k w) := finit_cfgOK (tableOfNums k nq na rest) w
    have x₂ := simP_runs _ hT _ hc _ S hS hN hsc
    have hcost := simCost_le hT hc (finit_nice k w) (diagSteps j c d w)
    have hle := diag_cost_le j h
    let st := (frun (tableOfNums k nq na rest) (finit k w) (diagSteps j c d w)).state
    let S₂ := (putCfg S (frun (tableOfNums k nq na rest) (finit k w) (diagSteps j c d w))).set CNT []
    have hST : S₂ ST = [st] := by
      simp only [S₂, putCfg, Lists.set]
      simp (config := { decide := true })
      rfl
    by_cases h0 : st = 0
    · have x₃ : NHalts ansP S₂ false S₂ 2 := NHalts.iteT (by rw [hST, h0]; rfl) (nhalts_halt false _)
      refine ⟨false, _, (x₁.seqH (x₂.seqH x₃)).mono (by omega), ?_⟩
      rw [diag_of_shape h]
      simp only [Bool.false_eq_true, false_iff]
      exact fun h' => h' h0
    · have x₃ : NHalts ansP S₂ true S₂ 2 := NHalts.iteF (by
        rw [hST]; simp only [NTest.eval, List.getLast?_singleton]; simpa using h0) (nhalts_halt true _)
      refine ⟨true, _, (x₁.seqH (x₂.seqH x₃)).mono (by omega), ?_⟩
      rw [diag_of_shape h]
      exact ⟨fun _ => h0, fun _ => rfl⟩
  · obtain ⟨S', x₁⟩ := diagFront_bad j w (fun k nq na c d rest h => hs ⟨k, nq, na, c, d, rest, h⟩)
    refine ⟨false, S', (NHalts.seq x₁).mono ?_, ?_⟩
    · unfold diagBoundN frontCost diagX; omega
    · simp only [Bool.false_eq_true, false_iff]
      intro hd
      obtain ⟨k, nq, na, c, d, rest, h, _⟩ := diag_shape hd
      exact hs ⟨k, nq, na, c, d, rest, h⟩

/-- **The diagonal language of height `j` is in (j+1)-EXPTIME.** -/
theorem diag_kexp (j : Nat) : KEXP (j + 1) (Diag j) := by
  obtain ⟨c, hc⟩ := diagBoundN_le j
  refine kexp_of_nprog_time (j := j + 1) (by omega) (K := UK) (by decide) (diagP j) (Diag j)
    (fun n => diagBoundN j n) ⟨c, 2, hc⟩ (fun w => ?_)
  obtain ⟨b, S', ⟨t, ht, hx⟩, hb⟩ := diagP_halts j w
  exact ⟨t, b, S', ht, hx, hb⟩

/-- **The time hierarchy**: some language is in (j+1)-EXPTIME but not in j-EXPTIME. -/
theorem kexp_strict (j : Nat) : ∃ L, KEXP (j + 1) L ∧ ¬ KEXP j L :=
  ⟨Diag j, diag_kexp j, diag_not_kexp j⟩

end Shallot.MacroPeg.KExp
