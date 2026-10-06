import MacroPeg.HigherOrder.KExp.CloseBound
import MacroPeg.HigherOrder.KExp.DiagCost
import MacroPeg.HigherOrder.KExp.DiagUpper
import Complexity.Univ.Output

/-!
# j-EXPTIME is closed under polynomial-time reductions

A stage lays out a table on an input and simulates it (`stage_runs`). The composed machine runs the reduction's
table, reads its output back as an input, runs the decider's table on it and answers whether the state is 0
(`closeP_halts`). Its steps are within `closeBoundN`, which is below a tower of height `j` of a polynomial, so
`KEXP j` is closed under reductions (`kexp_reduces`).
-/

namespace Shallot.MacroPeg.KExp

open Complexity
open Complexity.Univ
open Shallot.MacroPeg.HO

/-- Lay out a table on the input and simulate it. -/
def stageP (T : TTable) (j c d : Nat) : NProg UK := .seq (layTP T j c d) simP

/-- The steps a stage simulates. -/
def stageSteps (j c d : Nat) (w : List Bool) : Nat := tower j (c * (w.length + 1) ^ d)

/-- What the stacks hold after a stage. -/
structure StageOut (S : Lists UK) (T : TTable) (cf : FCfg) : Prop where
  tbl : S TBL = encRows T.rows
  ks : S KS = [T.k]
  na : S NA = [T.na]
  st : S ST = [cf.state]
  pos : S POS = cf.pos
  tp : S TP = encTapes cf.tapes
  cnt : S CNT = []
  scratch : UScratch S

theorem putCfg_scratch {S : Lists UK} (hs : UScratch S) (cf : FCfg) : UScratch ((putCfg S cf).set CNT []) := by
  intro i hi
  have h₁ : i ≠ CNT := fun e => by subst e; simp at hi
  have h₂ : i ≠ TP := fun e => by subst e; simp at hi
  have h₃ : i ≠ POS := fun e => by subst e; simp at hi
  have h₄ : i ≠ Univ.ST := fun e => by subst e; simp at hi
  simp only [putCfg, Lists.set, h₁, h₂, h₃, h₄, if_false]
  exact hs i hi

/-- **A stage simulates the table for `stageSteps` steps.** -/
theorem stage_runs (T : TTable) (hT : RowsOK T) (j c d : Nat) (w : List Bool) :
    ∃ S, NRuns (stageP T j c d) (nInit UK w) S
        (layCost T j c d w + simBound T (finit T.k w) (stageSteps j c d w)) ∧
      StageOut S T (frun T (finit T.k w) (stageSteps j c d w)) := by
  obtain ⟨S, x₁, hS, hN, hs⟩ := layP_runs T j c d w
  have hc := finit_cfgOK T w
  have x₂ := simP_runs T hT _ hc _ S hS hN hs
  have hb := simCost_le hT hc (finit_nice T.k w) (stageSteps j c d w)
  unfold stageSteps at hb ⊢
  refine ⟨_, (x₁.seq x₂).mono (by omega), ?_⟩
  obtain ⟨h₁, h₂, h₃, _, _, _⟩ := hS
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, putCfg_scratch hs _⟩ <;>
    simp (config := { decide := true }) [putCfg, Lists.set, h₁, h₂, h₃]

/-- The output read back is no longer than the configuration. -/
theorem readOut_length_le (cf : FCfg) : (readOut (cf.tapes.getD 0 [])).length ≤ csz cf := by
  have h₁ : (readOut (cf.tapes.getD 0 [])).length ≤ (cf.tapes.getD 0 []).length := by
    unfold readOut; rw [List.length_map]; exact (List.takeWhile_prefix _).length_le
  have h₂ : (cf.tapes.getD 0 []).length ≤ (encTapes cf.tapes).length := by
    cases hts : cf.tapes with
    | nil => simp
    | cons t ts => simp [encTapes]; omega
  unfold csz; omega

/-- Accept when the state is 0. -/
def ansAccP : NProg UK := .ite Univ.ST .zero (.halt true) (.halt false)

/-- The composed machine: the reduction's table, its output as an input, the decider's table, the answer. -/
def closeP (tR tN : TTable) (j cR dR cN dN : Nat) : NProg UK :=
  .seq (stageP tR 0 cR dR) (.seq extractP (.seq (stageP tN j cN dN) ansAccP))

/-- The steps of `extractP` after a stage are within the bound of `closeBoundN`. -/
theorem extract_le {S : Lists UK} {T : TTable} {cf : FCfg} (h : StageOut S T cf) {C : Nat} (hC : csz cf ≤ C) :
    extractCost S ≤ 1000 * (tsz T + 2 * C + 5) ^ 2 := by
  unfold extractCost
  rw [h.tbl, h.ks, h.na, h.st, h.pos, h.tp]
  have : (encRows T.rows).length ≤ tsz T := by unfold tsz; omega
  have hc : cf.pos.length + (encTapes cf.tapes).length + (encTapes cf.tapes).sum ≤ csz cf := by unfold csz; omega
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by simp; omega) _)

/-- The layout cost grows with the length of the input. -/
theorem layCost_mono (T : TTable) (j c d : Nat) {w : List Bool} {m : Nat} (hm : w.length ≤ m) :
    layCost T j c d w ≤ 1000 * (m + tsz T + c + d + 2) ^ 4 + 1000 * (tower j (c * (m + 1) ^ d) + 2) ^ 2 := by
  unfold layCost
  have h₁ : (w.length + tsz T + c + d + 2) ^ 4 ≤ (m + tsz T + c + d + 2) ^ 4 := Nat.pow_le_pow_left (by omega) _
  have h₂ : tower j (c * (w.length + 1) ^ d) ≤ tower j (c * (m + 1) ^ d) :=
    tower_mono j (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
  have h₃ : (tower j (c * (w.length + 1) ^ d) + 2) ^ 2 ≤ (tower j (c * (m + 1) ^ d) + 2) ^ 2 :=
    Nat.pow_le_pow_left (by omega) _
  omega

/-- **`KEXP j` is closed under polynomial-time reductions** (`j ≥ 1`). -/
theorem kexp_reduces {j : Nat} (hj : 1 ≤ j) {L L' : Lang} (hL' : KEXP j L') (hr : Reduces L L') : KEXP j L := by
  obtain ⟨f, ⟨kR, hkR, R, TR, ⟨cR, dR, hTR⟩, hrun⟩, hf⟩ := hr
  obtain ⟨kN, N, TN, cN, dN, hTN, hdec, htb⟩ := hL'
  obtain ⟨c, d, hcd⟩ := closeBoundN_towerPoly hj (tableOf R) (tableOf N) cR dR cN dN
  refine kexp_of_nprog_time hj (K := UK) (by decide) (closeP (tableOf R) (tableOf N) j cR dR cN dN) L
    (closeBoundN (tableOf R) (tableOf N) j cR dR cN dN) ⟨c, d, hcd⟩ (fun w => ?_)
  -- the reduction
  obtain ⟨S₁, x₁, o₁⟩ := stage_runs (tableOf R) (tableOf_rowsOK R) 0 cR dR w
  obtain ⟨t, ht, hst, hout⟩ := hrun w
  have hB₁ : stageSteps 0 cR dR w = cB1 cR dR w.length := rfl
  have hfo : readOut ((frun (tableOf R) (finit (tableOf R).k w) (stageSteps 0 cR dR w)).tapes.getD 0 []) = f w :=
    frun_output hkR R w (Nat.le_trans ht (hTR _)) hst hout
  have x₂ := extractP_runs S₁ _ o₁.tp o₁.cnt o₁.scratch
  rw [hfo] at x₂
  -- the sizes of the reduction's run
  have hgr := frun_csz (tableOf_rowsOK R) (finit_cfgOK (tableOf R) w) (finit_nice (tableOf R).k w) (stageSteps 0 cR dR w)
  have hcsz : csz (frun (tableOf R) (finit (tableOf R).k w) (stageSteps 0 cR dR w)) ≤ cC1 (tableOf R) cR dR w.length := by
    have := finit_csz (tableOf R).k w
    have h₁ := hgr.1
    have e : stageSteps 0 cR dR w * growth (tableOf R) = cB1 cR dR w.length * growth (tableOf R) := by rw [hB₁]
    unfold cC1; omega
  have hm : (f w).length ≤ cC1 (tableOf R) cR dR w.length := by
    rw [← hfo]; exact Nat.le_trans (readOut_length_le _) hcsz
  -- the decider
  obtain ⟨S₃, x₃, o₃⟩ := stage_runs (tableOf N) (tableOf_rowsOK N) j cN dN (f w)
  let B₂ := stageSteps j cN dN (f w)
  have hhalt : (N.run (initCfg kN (f w)) B₂).halted := by
    have e := TM.run_stays N (initCfg kN (f w)) (t := TN (f w).length) (t' := B₂)
      (by simp only [B₂, stageSteps]; exact hTN _) (htb (f w))
    rw [e]; exact htb (f w)
  obtain ⟨t', ht', hL'⟩ := hdec (f w)
  have hs := halted_state_eq N (initCfg kN (f w)) ht' hhalt
  have hstate : (frun (tableOf N) (finit (tableOf N).k (f w)) B₂).state = (N.run (initCfg kN (f w)) t').state := by
    exact (frun_state N (f w) B₂).trans hs.symm
  -- the cost
  have hc₁ := simBound_le_of (T := tableOf R) (cf := finit (tableOf R).k w) (B := stageSteps 0 cR dR w)
    (s := tsz (tableOf R) + cC1 (tableOf R) cR dR w.length) (g := growth (tableOf R)) (X := cB1 cR dR w.length)
    (by have := finit_csz (tableOf R).k w; unfold cC1; omega) (Nat.le_refl _)
    (Nat.le_of_eq hB₁)
  have hX : B₂ ≤ cB2 j cN dN (cC1 (tableOf R) cR dR w.length) :=
    tower_mono j (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
  have hc₃ := simBound_le_of (T := tableOf N) (cf := finit (tableOf N).k (f w)) (B := B₂)
    (s := tsz (tableOf N) + (2 + 2 * (tableOf N).k + 4 * cC1 (tableOf R) cR dR w.length))
    (g := growth (tableOf N)) (X := cB2 j cN dN (cC1 (tableOf R) cR dR w.length))
    (by have := finit_csz (tableOf N).k (f w); omega) (Nat.le_refl _) hX
  have hl₁ : layCost (tableOf R) 0 cR dR w ≤
      1000 * (w.length + tsz (tableOf R) + cR + dR + 2) ^ 4 + 1000 * (cB1 cR dR w.length + 2) ^ 2 :=
    layCost_mono (tableOf R) 0 cR dR (w := w) (Nat.le_refl _)
  have hl₃ := layCost_mono (tableOf N) j cN dN hm
  have he := extract_le o₁ hcsz
  have hbound : layCost (tableOf R) 0 cR dR w + simBound (tableOf R) (finit (tableOf R).k w) (stageSteps 0 cR dR w) +
      (extractCost S₁ + (layCost (tableOf N) j cN dN (f w) + simBound (tableOf N) (finit (tableOf N).k (f w)) B₂ + 2)) ≤
      closeBoundN (tableOf R) (tableOf N) j cR dR cN dN w.length := by
    unfold closeBoundN cB2 at *
    omega
  -- the answer
  by_cases h0 : (N.run (initCfg kN (f w)) t').state = 0
  · have hST : S₃ Univ.ST = [0] := by rw [o₃.st, hstate, h0]
    have x₄ : NHalts ansAccP S₃ true S₃ 2 := NHalts.iteT (by rw [hST]; rfl) (nhalts_halt true _)
    obtain ⟨u, hu, hx⟩ := (x₁.seqH (x₂.seqH (x₃.seqH x₄))).mono hbound
    exact ⟨u, true, S₃, hu, hx, by simp only [true_iff]; exact (hf w).2 (hL'.1 h0)⟩
  · have hST : S₃ Univ.ST = [(N.run (initCfg kN (f w)) t').state] := by rw [o₃.st, hstate]
    have x₄ : NHalts ansAccP S₃ false S₃ 2 := NHalts.iteF (by
      rw [hST]; simp only [NTest.eval, List.getLast?_singleton]; simpa using h0) (nhalts_halt false _)
    obtain ⟨u, hu, hx⟩ := (x₁.seqH (x₂.seqH (x₃.seqH x₄))).mono hbound
    exact ⟨u, false, S₃, hu, hx, by
      simp only [Bool.false_eq_true, false_iff]
      exact fun hl => h0 (hL'.2 ((hf w).1 hl))⟩

end Shallot.MacroPeg.KExp
