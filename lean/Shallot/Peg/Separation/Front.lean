import Shallot.Peg.Separation.Diagonal

/-!
# The polynomial diagonal machine's front

Reuse the verified input parser, row checker, and tape layout. Before
counting, overwrite the two header constants by `1` and the fixed `p + 1`.
Thus even malformed or huge input exponents cannot trigger a variable
exponent computation.
-/

namespace Shallot.PegSeparation

open Complexity Complexity.Univ Shallot.MacroPeg.KExp Shallot.MacroPeg.HO

/-- Discard both input constants and set a fixed simulation exponent. -/
def overwriteP (p : Nat) : NProg UK :=
  .seq (.prim (.pop CC)) (.seq (npushC CC 1) (.seq (.prim (.pop DD)) (npushC DD (p + 1))))

theorem nruns_overwrite (p n : Nat) (tp rest : List Nat) (k na c d : Nat) :
    NRuns (overwriteP p) (S4 n tp rest k na c d) (S4 n tp rest k na 1 (p + 1)) (p + 6) := by
  let S := S4 n tp rest k na c d
  have x₁ := nruns_pop CC S (l := []) (v := c) (by simp only [S, S4]; stk_simp)
  let S₁ := S.set CC []
  have x₂ := nruns_pushC CC S₁ 1
  have he₁ : S₁ CC = [] := Lists.set_same _ _ _
  rw [he₁, List.nil_append] at x₂
  let S₂ := S₁.set CC [1]
  have x₃ := nruns_pop DD S₂ (l := []) (v := d) (by simp only [S₂, S₁, S, S4]; stk_simp)
  let S₃ := S₂.set DD []
  have x₄ := nruns_pushC DD S₃ (p + 1)
  rw [show S₃ DD = [] from Lists.set_same _ _ _, List.nil_append] at x₄
  have he : S₃.set DD [p + 1] = S4 n tp rest k na 1 (p + 1) := by
    simp only [S₃, S₂, S₁, S, S4]; lsimp
  rw [he] at x₄
  exact (x₁.seq (x₂.seq (x₃.seq x₄))).mono (by omega)

def polyRestP (p : Nat) : NProg UK :=
  .seq chunkPre (.seq checkP (.seq layP (.seq (overwriteP p) (countP 0))))

def polyFrontP (p : Nat) : NProg UK :=
  .seq parseP (.seq tapeP (.seq loadP (takesP MM dsTakes dsTakes_ne (polyRestP p))))

/-- A polynomial front budget; the exponent `p + 1` is fixed by the program. -/
def polyFrontCost (p N : Nat) : Nat := 100 * (N + 1) + p + 100 + countCost 0 N 1 (p + 1)

/-- On a valid code the front lays out the simulator with the fixed budget. -/
theorem polyFront_ok (p : Nat) (w : List Bool) {k nq na c d : Nat} {rest : List Nat}
    (h : DiagShape w k nq na c d rest) :
    ∃ S, NRuns (polyFrontP p) (nInit UK w) S (polyFrontCost p w.length) ∧
      SimSt S (tableOfNums k nq na rest) (finit k w) ∧ S CNT = [polySteps p w] ∧ UScratch S := by
  obtain ⟨hd, hmod⟩ := h
  have hb := deUnary_bound w
  rw [hd] at hb
  simp only [List.sum_cons, List.length_cons] at hb
  have r₁ := nruns_parse w
  have r₂ := nruns_tape w
  have r₃ := nruns_load w
  have hS2L : S2L w = ((E0.set NN [w.length]).set TP (w.length :: w.map bitSym)).set MM
      (k :: nq :: na :: c :: d :: rest).reverse := by simp only [S2L, hd]
  rw [hS2L] at r₃
  have r₄ := nruns_chunkPre w.length (w.length :: w.map bitSym) rest k nq na c d
  have r₅ := nruns_check w.length (w.length :: w.map bitSym) rest k nq na c d hmod
  have r₆ := nruns_lay w.length (w.length :: w.map bitSym) rest k na c d
  have r₇ := nruns_overwrite p w.length (w.length :: w.map bitSym) rest k na c d
  have r₈ := nruns_count 0 w.length (w.length :: w.map bitSym) rest k na 1 (p + 1)
  have rt := (takes_good w.length (w.length :: w.map bitSym) rest k nq na c d (polyRestP p)).1
    (r₄.seq (r₅.seq (r₆.seq (r₇.seq r₈))))
  refine ⟨SF 0 w.length (w.length :: w.map bitSym) rest k na 1 (p + 1),
    (r₁.seq (r₂.seq (r₃.seq rt))).mono ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, sf_scratch _ _ _ _ _ _ _ _⟩
  · unfold polyFrontCost
    simp only [List.length_cons, List.length_map]
    omega
  · show _ = encRows (decRows k rest)
    rw [encRows_decRows]; simp only [SF]; stk_simp
  · simp only [SF]; stk_simp; rfl
  · simp only [SF]; stk_simp; rfl
  · simp only [SF]; stk_simp; rfl
  · simp only [SF]; stk_simp; rfl
  · rw [Shallot.MacroPeg.KExp.encTapes_finit]; simp only [SF]; stk_simp
  · simp only [SF, polySteps]; stk_simp

/-- An invalid code is rejected without computing any input-provided power. -/
theorem polyFront_bad (p : Nat) (w : List Bool)
    (h : ∀ k nq na c d rest, ¬ DiagShape w k nq na c d rest) :
    ∃ S', NHalts (polyFrontP p) (nInit UK w) false S' (polyFrontCost p w.length) := by
  have hb := deUnary_bound w
  have r₁ := nruns_parse w
  have r₂ := nruns_tape w
  have r₃ := nruns_load w
  by_cases h5 : (deUnary w).length < 5
  · obtain ⟨S', hS'⟩ := nhalts_takes MM (polyRestP p) dsTakes dsTakes_ne (S2L w) (by
      have : (S2L w) MM = (deUnary w).reverse := by simp only [S2L]; stk_simp
      rw [this, List.length_reverse]; simp only [dsTakes, List.length_cons, List.length_nil]; omega)
    refine ⟨S', (r₁.seqH (r₂.seqH (r₃.seqH hS'))).mono ?_⟩
    unfold polyFrontCost
    simp only [dsTakes, List.length_cons, List.length_nil]
    omega
  · obtain ⟨k, nq, na, c, d, rest, hd⟩ : ∃ k nq na c d rest, deUnary w = k :: nq :: na :: c :: d :: rest := by
      match hL : deUnary w, h5 with
      | k :: nq :: na :: c :: d :: rest, _ => exact ⟨k, nq, na, c, d, rest, rfl⟩
      | [], h5 => simp at h5
      | [_], h5 => simp at h5
      | [_, _], h5 => simp at h5
      | [_, _, _], h5 => simp at h5
      | [_, _, _, _], h5 => simp at h5
    have hmod : rest.length % (2 * k + 1) ≠ 0 := fun hm => h k nq na c d rest ⟨hd, hm⟩
    rw [hd] at hb
    simp only [List.sum_cons, List.length_cons] at hb
    have hS2L : S2L w = ((E0.set NN [w.length]).set TP (w.length :: w.map bitSym)).set MM
        (k :: nq :: na :: c :: d :: rest).reverse := by simp only [S2L, hd]
    rw [hS2L] at r₃
    have r₄ := nruns_chunkPre w.length (w.length :: w.map bitSym) rest k nq na c d
    have r₅ := nhalts_check w.length (w.length :: w.map bitSym) rest k nq na c d hmod
    have hr : NHalts (polyRestP p) _ false _ _ :=
      r₄.seqH (NHalts.seq (q := .seq layP (.seq (overwriteP p) (countP 0))) r₅)
    have rt := (takes_good w.length (w.length :: w.map bitSym) rest k nq na c d (polyRestP p)).2 hr
    refine ⟨_, (r₁.seqH (r₂.seqH (r₃.seqH rt))).mono ?_⟩
    unfold polyFrontCost
    omega

end Shallot.PegSeparation
