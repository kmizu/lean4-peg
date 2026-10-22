import Shallot.Peg.Packrat.Machine.Input

/-!
# Extract the answer and halt

Read the start row at position zero, compare its numeric entry with input
length plus two, and halt with true exactly for full-input success.
-/

namespace Shallot.Packrat.Machine

open Complexity

def answer (g : Grammar) : NProg (NK g) :=
  caseTop (curR g) [.halt false, .halt true] (.halt false)

theorem nhalts_answer (g : Grammar) (a b : Nat) (S : Lists (NK g)) {lc : List Nat}
    (hc : S (curR g) = lc ++ [cmpRes a b]) :
    ∃ S', NHalts (answer g) S (decide (a = b)) S' 7 := by
  by_cases hab : a < b
  · have hv : cmpRes a b = 0 := by simp [cmpRes, hab]
    rw [hv] at hc
    have hx := caseTop_halts (curR g) [.halt false, .halt true] (.halt false) 0 (by simp) S lc hc
      false (S.set (curR g) lc) 1 (nhalts_halt _ _)
    refine ⟨S.set (curR g) lc, ?_⟩
    simpa only [answer, show decide (a = b) = false by simp [show a ≠ b by omega]] using hx.mono (by simp)
  · by_cases he : a = b
    · have hv : cmpRes a b = 1 := by simp [cmpRes, he]
      rw [hv] at hc
      have hx := caseTop_halts (curR g) [.halt false, .halt true] (.halt false) 1 (by simp) S lc hc
        true (S.set (curR g) lc) 1 (nhalts_halt _ _)
      refine ⟨S.set (curR g) lc, ?_⟩
      simpa only [answer, show decide (a = b) = true by simp [he]] using hx.mono (by simp)
    · have hv : cmpRes a b = 2 := by simp [cmpRes, hab, he]
      rw [hv] at hc
      have hx := caseTop_default (curR g) [.halt false, .halt true] (.halt false) 0 S lc hc
        false (S.set (curR g) (lc ++ [0])) 1 (nhalts_halt _ _)
      refine ⟨S.set (curR g) (lc ++ [0]), ?_⟩
      simpa only [answer, show decide (a = b) = false by simp [he]] using hx.mono (by simp)

def startRow (g : Grammar) : Fin (NK g) := oldR g (nodeIdx g (.nt g.start) (dom_start g))

def finish (g : Grammar) : NProg (NK g) :=
  .seq (.prim (.pushZ (posR g)))
    (.seq (readRow (startRow g) (tmpR g) (idxR g) (posR g) (workR g)
      (by unfold startRow; packrat_regs) (by packrat_regs) (by packrat_regs))
      (.seq (.prim (.pop (posR g)))
        (.seq (emptySuccess (lenR g) (idxR g) (by packrat_regs))
          (.seq (cmpTop (workR g) (idxR g) (tmpR g) (posR g) (countR g) (curR g)
            (by packrat_regs) (by packrat_regs)) (answer g)))))

def finishCost (N : Nat) : Nat := 6 * N + (2 * N + 5) * (2 * N + 10) + 50

/-- The answer extractor halts with the endpoint comparison. -/
theorem nhalts_finish (g : Grammar) (x : List Char) (n : Nat) (S : Lists (NK g))
    (h : Ready g x n S) :
    ∃ S', NHalts (finish g) S (decide (code 0 (iter g x n (.nt g.start) 0) = x.length + 2)) S'
      (finishCost x.length) := by
  let v := code 0 (iter g x n (.nt g.start) 0)
  have hd : [posR g, workR g, lenR g, idxR g, tmpR g, curR g, countR g].Nodup := by packrat_regs
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hd
  have hlen := h.len
  have hrow : S (startRow g) = row (iter g x n) (.nt g.start) x.length := h.rows _ (dom_start g)
  have pz := nruns_pushZ (posR g) S
  let S₁ := S.set (posR g) (S (posR g) ++ [0])
  have hr₁ : S₁ (startRow g) = row (iter g x n) (.nt g.start) x.length := by
    simp only [S₁, startRow, Lists.set_ne _ _ (show oldR g (nodeIdx g (.nt g.start) (dom_start g)) ≠ posR g by packrat_regs)]
    exact hrow
  have rd := nruns_readRow (startRow g) (tmpR g) (idxR g) (posR g) (workR g)
    (by unfold startRow; packrat_regs) (by packrat_regs) (by packrat_regs)
    (by unfold startRow; packrat_regs) S₁
    (by simp only [S₁, Lists.set_ne _ _ (show tmpR g ≠ posR g by packrat_regs)]; exact h.tmp)
    (lp := S (posR g)) (i := 0) (by simp [S₁]) (by simp [hr₁])
  have hv : (S₁ (startRow g))[0]'(by simp [hr₁]) = v := by simp only [hr₁, row_get _ _ _ _ (Nat.zero_le x.length)]; rfl
  rw [hv] at rd
  let S₂ := S₁.set (workR g) (S₁ (workR g) ++ [v])
  have pp := nruns_pop (posR g) S₂ (l := S (posR g)) (v := 0) (by simp only [S₂, S₁, Lists.set_ne _ _ (show posR g ≠ workR g by packrat_regs), Lists.set_same])
  let S₃ := S₂.set (posR g) (S (posR g))
  have hl₃ : S₃ (lenR g) = [x.length] := by
    simp only [S₃, S₂, S₁, Lists.set_ne _ _ (show lenR g ≠ posR g by packrat_regs),
      Lists.set_ne _ _ (show lenR g ≠ workR g by packrat_regs)]
    exact h.len
  have el := nruns_emptySuccess (lenR g) (idxR g) (by packrat_regs) S₃ (lp := []) (i := x.length) hl₃
  let S₄ := S₃.set (idxR g) (S₃ (idxR g) ++ [x.length + 2])
  have cm := nruns_cmpTop (workR g) (idxR g) (tmpR g) (posR g) (countR g) (curR g)
    (by packrat_regs) (by packrat_regs) (by packrat_regs) S₄
    (li := S (workR g)) (lj := S₃ (idxR g)) (a := v) (b := x.length + 2)
    (by simp only [S₄, S₃, S₂, S₁, Lists.set_ne _ _ (show workR g ≠ idxR g by packrat_regs),
      Lists.set_ne _ _ (show workR g ≠ posR g by packrat_regs), Lists.set_same]) (by simp [S₄])
  let S₅ := S₄.set (curR g) (S₄ (curR g) ++ [cmpRes v (x.length + 2)])
  obtain ⟨S₆, ax⟩ := nhalts_answer g v (x.length + 2) S₅ (lc := S₄ (curR g)) (by simp [S₅])
  have hx := pz.seqH (rd.seqH (pp.seqH (el.seqH (cm.seqH ax))))
  refine ⟨S₆, hx.mono ?_⟩
  have hbound : v ≤ x.length + 2 := code_bound (Nat.zero_le x.length)
  have hc : (v + (x.length + 2) + 1) * (2 * v + 6) ≤ (2 * x.length + 5) * (2 * x.length + 10) :=
    Nat.mul_le_mul (by omega) (by omega)
  simp only [hr₁, row_length, finishCost]
  omega

theorem finishCost_le (N : Nat) : finishCost N ≤ 128 * (N + 1) ^ 2 := by
  have hm : N + 1 ≤ (N + 1) ^ 2 := by
    simpa only [Nat.pow_two, Nat.mul_one] using Nat.mul_le_mul_left (N + 1) (show 1 ≤ N + 1 by omega)
  have hp := Nat.mul_le_mul (show 2 * N + 5 ≤ 5 * (N + 1) by omega)
    (show 2 * N + 10 ≤ 10 * (N + 1) by omega)
  have he : (5 * (N + 1)) * (10 * (N + 1)) = 50 * (N + 1) ^ 2 := by
    simp only [Nat.pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  rw [he] at hp
  unfold finishCost
  omega

end Shallot.Packrat.Machine
