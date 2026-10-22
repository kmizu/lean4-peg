import Shallot.Peg.Separation.Front
import Complexity.Univ.SimRun
import Complexity.TmplBound

/-!
# A concrete polynomial-time decider for the diagonal language

The front uses a fixed exponent, then the existing universal simulator
executes the polynomial budget and answers opposite to state zero.
-/

namespace Shallot.PegSeparation

open Complexity Complexity.Univ Shallot.MacroPeg.KExp Shallot.MacroPeg.HO

/-- Worst-case stack steps of the complete polynomial diagonal program. -/
def polyDiagBound (p N : Nat) : Nat :=
  polyFrontCost p N + 10 + (N + 1) ^ (p + 1) *
    (1000 * (7 * N + 4 + (N + 1) ^ (p + 1) * ((N + 1) * (N + 3)) + 2) ^ 4) + 2

theorem polyDiag_cost (p : Nat) {w : List Bool} {k nq na c d : Nat} {rest : List Nat}
    (h : DiagShape w k nq na c d rest) :
    polyFrontCost p w.length + simBound (tableOfNums k nq na rest) (finit k w) (polySteps p w) + 2 ≤
      polyDiagBound p w.length := by
  obtain ⟨hk, _, _, ht⟩ := diag_sizes h
  have hcs := finit_csz k w
  have hg : growth (tableOfNums k nq na rest) ≤ (w.length + 1) * (w.length + 3) := by
    unfold growth
    exact Nat.mul_le_mul (by simp [tableOfNums]; omega) (by omega)
  have hs := simBound_le_of (T := tableOfNums k nq na rest) (cf := finit k w)
    (s := 7 * w.length + 4) (by omega) hg (Nat.le_refl (polySteps p w))
  unfold polyDiagBound polySteps at *
  omega

def polyDiagP (p : Nat) : NProg UK := .seq (polyFrontP p) (.seq simP (.ite ST .zero (.halt false) (.halt true)))

theorem polyDiag_shape {p : Nat} {w : List Bool} (h : PolyDiag p w) :
    ∃ k nq na c d rest, DiagShape w k nq na c d rest ∧
      (frun (tableOfNums k nq na rest) (finit k w) (polySteps p w)).state ≠ 0 := by
  unfold PolyDiag at h
  split at h
  · rename_i k nq na c d rest hd
    exact ⟨k, nq, na, c, d, rest, ⟨hd, h.1⟩, h.2⟩
  · exact h.elim

theorem polyDiag_of_shape {p : Nat} {w : List Bool} {k nq na c d : Nat} {rest : List Nat}
    (h : DiagShape w k nq na c d rest) :
    PolyDiag p w ↔ (frun (tableOfNums k nq na rest) (finit k w) (polySteps p w)).state ≠ 0 := by
  unfold PolyDiag
  rw [h.1]
  simp only [h.2, true_and]

/-- The concrete diagonal program halts with the specified answer on every input. -/
theorem polyDiagP_halts (p : Nat) (w : List Bool) :
    ∃ b S', NHalts (polyDiagP p) (nInit UK w) b S' (polyDiagBound p w.length) ∧ (b = true ↔ PolyDiag p w) := by
  by_cases hs : ∃ k nq na c d rest, DiagShape w k nq na c d rest
  · obtain ⟨k, nq, na, c, d, rest, h⟩ := hs
    obtain ⟨S, x₁, hS, hN, hsc⟩ := polyFront_ok p w h
    have hT := tableOfNums_rowsOK (nq := nq) (na := na) h.2
    have hc : CfgOK (tableOfNums k nq na rest) (finit k w) := finit_cfgOK (tableOfNums k nq na rest) w
    have x₂ := simP_runs _ hT _ hc _ S hS hN hsc
    have hcost := simCost_le hT hc (finit_nice k w) (polySteps p w)
    have hle := polyDiag_cost p h
    let st := (frun (tableOfNums k nq na rest) (finit k w) (polySteps p w)).state
    let S₂ := (putCfg S (frun (tableOfNums k nq na rest) (finit k w) (polySteps p w))).set CNT []
    have hST : S₂ ST = [st] := by
      simp only [S₂, putCfg, Lists.set]
      simp (config := { decide := true })
      rfl
    by_cases h0 : st = 0
    · have x₃ : NHalts (.ite ST .zero (.halt false) (.halt true)) S₂ false S₂ 2 :=
        NHalts.iteT (by rw [hST, h0]; rfl) (nhalts_halt false _)
      refine ⟨false, _, (x₁.seqH (x₂.seqH x₃)).mono (by omega), ?_⟩
      rw [polyDiag_of_shape h]
      simp only [Bool.false_eq_true, false_iff]
      exact fun h' => h' h0
    · have x₃ : NHalts (.ite ST .zero (.halt false) (.halt true)) S₂ true S₂ 2 :=
        NHalts.iteF (by rw [hST]; simp only [NTest.eval, List.getLast?_singleton]; simpa using h0) (nhalts_halt true _)
      refine ⟨true, _, (x₁.seqH (x₂.seqH x₃)).mono (by omega), ?_⟩
      rw [polyDiag_of_shape h]
      exact ⟨fun _ => h0, fun _ => rfl⟩
  · obtain ⟨S', x₁⟩ := polyFront_bad p w (fun k nq na c d rest h => hs ⟨k, nq, na, c, d, rest, h⟩)
    refine ⟨false, S', (NHalts.seq x₁).mono ?_, ?_⟩
    · unfold polyDiagBound; omega
    · simp only [Bool.false_eq_true, false_iff]
      intro hd
      obtain ⟨k, nq, na, c, d, rest, h, _⟩ := polyDiag_shape hd
      exact hs ⟨k, nq, na, c, d, rest, h⟩

/-- Fixed-exponent budget generation is polynomial in input length. -/
theorem polyFrontCost_poly (p : Nat) : IsPoly (polyFrontCost p) := by
  have hp : IsPoly (fun N => (N + 1) ^ (p + 1)) := isPoly_pow (isPoly_add isPoly_id (isPoly_const 1)) _
  have hpow : IsPoly (fun N => (N + 1) ^ (p + 1) * (3 * N + 8) + 6) :=
    isPoly_add (isPoly_mul hp (isPoly_add (isPoly_mul (isPoly_const 3) isPoly_id) (isPoly_const 8))) (isPoly_const 6)
  have hc : IsPoly (fun N => countCost 0 N 1 (p + 1)) := by
    simp only [countCost, towerCost, Nat.one_mul]
    exact isPoly_add (isPoly_add (isPoly_add
      (isPoly_mul (isPoly_const (p + 1)) (isPoly_add hpow (isPoly_const 1)))
      (isPoly_add (isPoly_mul (isPoly_const 3) hp) (isPoly_const 5))) (isPoly_const 2)) (isPoly_const 20)
  exact isPoly_add (isPoly_add (isPoly_add
    (isPoly_mul (isPoly_const 100) (isPoly_add isPoly_id (isPoly_const 1))) (isPoly_const p)) (isPoly_const 100)) hc

/-- The complete simulation budget is polynomial for each fixed `p`. -/
theorem polyDiagBound_poly (p : Nat) : IsPoly (polyDiagBound p) := by
  have h1 := isPoly_add isPoly_id (isPoly_const 1)
  have hp := isPoly_pow h1 (p + 1)
  have hg : IsPoly (fun N => (N + 1) * (N + 3)) := isPoly_mul h1 (isPoly_add isPoly_id (isPoly_const 3))
  have hi : IsPoly (fun N => 7 * N + 4 + (N + 1) ^ (p + 1) * ((N + 1) * (N + 3)) + 2) :=
    isPoly_add (isPoly_add (isPoly_add (isPoly_mul (isPoly_const 7) isPoly_id) (isPoly_const 4))
      (isPoly_mul hp hg)) (isPoly_const 2)
  exact isPoly_add (isPoly_add (isPoly_add (polyFrontCost_poly p) (isPoly_const 10))
    (isPoly_mul hp (isPoly_mul (isPoly_const 1000) (isPoly_pow hi 4)))) (isPoly_const 2)

end Shallot.PegSeparation
