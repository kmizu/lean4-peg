import Shallot.Peg.Separation.Upper
import MacroPeg.HigherOrder.KExp.Close

namespace Shallot.PegSeparation

open Complexity Complexity.Univ Shallot.MacroPeg.KExp Shallot.MacroPeg.HO

/-- The composed reduction and polynomial decider have a polynomial stack budget. -/
theorem closeBoundN_poly (tR tN : TTable) (cR dR cN dN : Nat) :
    IsPoly (closeBoundN tR tN 0 cR dR cN dN) := by
  have h1 := isPoly_cB1 cR dR
  have hC := isPoly_cC1 tR cR dR
  have hB : IsPoly (fun n => cB2 0 cN dN (cC1 tR cR dR n)) :=
    isPoly_mul (isPoly_const _) (isPoly_pow (isPoly_add hC (isPoly_const 1)) dN)
  have pP : IsPoly (fun n =>
      (1000 * (n + tsz tR + cR + dR + 2) ^ 4 + 1000 * (cB1 cR dR n + 2) ^ 2) +
      (10 + cB1 cR dR n * (1000 * (tsz tR + cC1 tR cR dR n + cB1 cR dR n * growth tR + 2) ^ 4)) +
      1000 * (tsz tR + 2 * cC1 tR cR dR n + 5) ^ 2 +
      1000 * (cC1 tR cR dR n + tsz tN + cN + dN + 2) ^ 4) := by
    refine isPoly_add (isPoly_add (isPoly_add (isPoly_add ?_ ?_) (isPoly_add (isPoly_const _)
      (isPoly_mul h1 (isPoly_mul (isPoly_const _) (isPoly_pow ?_ 4))))) ?_) ?_
    · exact isPoly_mul (isPoly_const _) (isPoly_pow (isPoly_add (isPoly_add (isPoly_add (isPoly_add isPoly_id
        (isPoly_const _)) (isPoly_const _)) (isPoly_const _)) (isPoly_const _)) 4)
    · exact isPoly_mul (isPoly_const _) (isPoly_pow (isPoly_add h1 (isPoly_const _)) 2)
    · exact isPoly_add (isPoly_add (isPoly_add (isPoly_const _) hC) (isPoly_mul h1 (isPoly_const _)))
        (isPoly_const _)
    · exact isPoly_mul (isPoly_const _) (isPoly_pow (isPoly_add (isPoly_add (isPoly_const _)
        (isPoly_mul (isPoly_const _) hC)) (isPoly_const _)) 2)
    · exact isPoly_mul (isPoly_const _) (isPoly_pow (isPoly_add (isPoly_add (isPoly_add (isPoly_add hC
        (isPoly_const _)) (isPoly_const _)) (isPoly_const _)) (isPoly_const _)) 4)
  have hT := isPoly_add (isPoly_add (isPoly_add pP
    (isPoly_mul (isPoly_const 1000) (isPoly_pow (isPoly_add hB (isPoly_const 2)) 2)))
    (isPoly_add (isPoly_const 10) (isPoly_mul hB (isPoly_mul (isPoly_const 1000)
      (isPoly_pow (isPoly_add (isPoly_add
        (isPoly_add (isPoly_const (tsz tN)) (isPoly_add (isPoly_const (2 + 2 * tN.k)) (isPoly_mul (isPoly_const 4) hC)))
        (isPoly_mul hB (isPoly_const (growth tN)))) (isPoly_const 2)) 4))))) (isPoly_const 2)
  obtain ⟨c, d, hc⟩ := hT
  refine ⟨c, d, fun n => ?_⟩
  have hn := hc n
  dsimp only at hn
  unfold closeBoundN
  omega

/-- Polynomial-time many-one reductions preserve P on the concrete TM model. -/
theorem p_reduces {L L' : Lang} (hL' : KEXP 0 L') (hr : Reduces L L') : KEXP 0 L := by
  obtain ⟨f, ⟨kR, hkR, R, TR, ⟨cR, dR, hTR⟩, hrun⟩, hf⟩ := hr
  obtain ⟨kN, N, TN, cN, dN, hTN, hdec, htb⟩ := hL'
  refine nprog_in_P (K := UK) (by decide) (closeP (tableOf R) (tableOf N) 0 cR dR cN dN) L
    (closeBoundN (tableOf R) (tableOf N) 0 cR dR cN dN)
    (closeBoundN_poly _ _ _ _ _ _) (fun w => ?_)
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
  obtain ⟨S₃, x₃, o₃⟩ := stage_runs (tableOf N) (tableOf_rowsOK N) 0 cN dN (f w)
  let B₂ := stageSteps 0 cN dN (f w)
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
  have hX : B₂ ≤ cB2 0 cN dN (cC1 (tableOf R) cR dR w.length) :=
    tower_mono 0 (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
  have hc₃ := simBound_le_of (T := tableOf N) (cf := finit (tableOf N).k (f w)) (B := B₂)
    (s := tsz (tableOf N) + (2 + 2 * (tableOf N).k + 4 * cC1 (tableOf R) cR dR w.length))
    (g := growth (tableOf N)) (X := cB2 0 cN dN (cC1 (tableOf R) cR dR w.length))
    (by have := finit_csz (tableOf N).k (f w); omega) (Nat.le_refl _) hX
  have hl₁ : layCost (tableOf R) 0 cR dR w ≤
      1000 * (w.length + tsz (tableOf R) + cR + dR + 2) ^ 4 + 1000 * (cB1 cR dR w.length + 2) ^ 2 :=
    layCost_mono (tableOf R) 0 cR dR (w := w) (Nat.le_refl _)
  have hl₃ := layCost_mono (tableOf N) 0 cN dN hm
  have he := extract_le o₁ hcsz
  have hbound : layCost (tableOf R) 0 cR dR w + simBound (tableOf R) (finit (tableOf R).k w) (stageSteps 0 cR dR w) +
      (extractCost S₁ + (layCost (tableOf N) 0 cN dN (f w) + simBound (tableOf N) (finit (tableOf N).k (f w)) B₂ + 2)) ≤
      closeBoundN (tableOf R) (tableOf N) 0 cR dR cN dN w.length := by
    unfold closeBoundN cB2 at *
    omega
  -- the answer
  by_cases h0 : (N.run (initCfg kN (f w)) t').state = 0
  · have hST : S₃ Univ.ST = [0] := by rw [o₃.st, hstate, h0]
    have x₄ : NHalts ansAccP S₃ true S₃ 2 := NHalts.iteT (by rw [hST]; rfl) (nhalts_halt true _)
    obtain ⟨u, hu, hx⟩ := (x₁.seqH (x₂.seqH (x₃.seqH x₄))).mono hbound
    exact ⟨true, S₃, ⟨u, hu, hx⟩, by simp only [true_iff]; exact (hf w).2 (hL'.1 h0)⟩
  · have hST : S₃ Univ.ST = [(N.run (initCfg kN (f w)) t').state] := by rw [o₃.st, hstate]
    have x₄ : NHalts ansAccP S₃ false S₃ 2 := NHalts.iteF (by
      rw [hST]; simp only [NTest.eval, List.getLast?_singleton]; simpa using h0) (nhalts_halt false _)
    obtain ⟨u, hu, hx⟩ := (x₁.seqH (x₂.seqH (x₃.seqH x₄))).mono hbound
    exact ⟨false, S₃, ⟨u, hu, hx⟩, by
      simp only [Bool.false_eq_true, false_iff]
      exact fun hl => h0 (hL'.2 ((hf w).1 hl))⟩

end Shallot.PegSeparation
