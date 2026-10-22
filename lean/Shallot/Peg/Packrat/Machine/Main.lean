import Shallot.Peg.Packrat.Machine.Finish

/-!
# The complete bounded stack-machine recognizer

From the actual initial bit stacks: load the two fixed input characters,
initialize every old row, iterate to the proved bound, read the start
entry, and halt. No prepared-table or execution assumption is required.
The full program has a cubic bound in the number of input bits.
-/

namespace Shallot.Packrat.Machine

open Complexity

def program (g : Grammar) (f : Bool → Char) : NProg (NK g) :=
  .seq (loadInput g f) (.seq (initTable g) (.seq (iterateBound g) (finish g)))

def programCost (g : Grammar) (f : Bool → Char) (N : Nat) : Nat :=
  inputCost f N + ((dom g).length * (3 * N + 7) + 2) + iterateCost g N + finishCost N

/-- Full-input language of the grammar on the two fixed input characters. -/
def bitLanguage (g : Grammar) (f : Bool → Char) : Lang := fun w =>
  ∃ t, Derives g (.nt g.start) (w.map f) (.ok t [])

/-- The concrete program halts from `nInit` with exactly the grammar's answer. -/
theorem program_halts (g : Grammar) (f : Bool → Char) (w : List Bool) :
    ∃ b S', NHalts (program g f) (nInit (NK g) w) b S' (programCost g f w.length) ∧
      (b = true ↔ bitLanguage g f w) := by
  have li := nruns_load_nInit g f w
  have hi : loaded g f w (inpR g) = inputRow (w.map f) := by simp [loaded]
  have hl : loaded g f w (lenR g) = [(w.map f).length] := by
    simp only [loaded, Lists.set_ne _ _ (show lenR g ≠ inpR g by packrat_regs), Lists.set_same, List.length_map]
  have ht : loaded g f w (tmpR g) = [] := by
    simp only [loaded, Lists.set_ne _ _ (show tmpR g ≠ inpR g by packrat_regs),
      Lists.set_ne _ _ (show tmpR g ≠ lenR g by packrat_regs)]
    simp [nInit, tmpR]
  have ho : ∀ j, loaded g f w (oldR g j) = [] := by
    intro j
    simp only [loaded, Lists.set_ne _ _ (show oldR g j ≠ inpR g by packrat_regs),
      Lists.set_ne _ _ (show oldR g j ≠ lenR g by packrat_regs)]
    simp [nInit, oldR]
  have hn : ∀ j, loaded g f w (nextR g j) = [] := by
    intro j
    simp only [loaded, Lists.set_ne _ _ (show nextR g j ≠ inpR g by packrat_regs),
      Lists.set_ne _ _ (show nextR g j ≠ lenR g by packrat_regs)]
    simp [nInit, nextR]
  obtain ⟨S₁, zi, h₁⟩ := nruns_initialize g (w.map f) (loaded g f w) hi hl ht ho hn
  obtain ⟨S₂, it, h₂, _⟩ := nruns_iterateBound g (w.map f) 0 S₁ h₁
  simp only [Nat.zero_add] at h₂
  obtain ⟨S₃, fi⟩ := nhalts_finish g (w.map f) (bound g (w.map f)) S₂ h₂
  refine ⟨_, S₃, (li.seqH (zi.seqH (it.seqH fi))).mono ?_, ?_⟩
  · simp only [List.length_map, programCost]
    omega
  · simpa only [decide_eq_true_eq, bitLanguage] using start_full_iff g (w.map f)

/-- The executable answer agrees with the previously verified bounded recognizer. -/
theorem program_halts_fullAccepts (g : Grammar) (f : Bool → Char) (w : List Bool) :
    ∃ S', NHalts (program g f) (nInit (NK g) w) (fullAccepts g (w.map f)) S' (programCost g f w.length) := by
  obtain ⟨b, S', hx, hb⟩ := program_halts g f w
  have he : b = fullAccepts g (w.map f) :=
    Bool.eq_iff_iff.mpr (hb.trans (fullAccepts_iff g (w.map f)).symm)
  exact ⟨S', he ▸ hx⟩

/-- The fixed-grammar coefficient of the cubic stack-step bound. -/
def programCoeff (g : Grammar) (f : Bool → Char) : Nat :=
  (inputMax f + 17) + (7 * (dom g).length + 2) + iterateCoeff g + 128

/-- The recognizer's bound has exponent three for every grammar. -/
theorem programCost_le (g : Grammar) (f : Bool → Char) (N : Nat) :
    programCost g f N ≤ programCoeff g f * (N + 1) ^ 3 := by
  have hone : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow 3 (N + 1) (by omega)
  have hnc : N + 1 ≤ (N + 1) ^ 3 := by
    have hh := Nat.pow_le_pow_right (show 1 ≤ N + 1 by omega) (show 1 ≤ 3 by omega)
    simpa only [Nat.pow_one] using hh
  have hi : inputCost f N ≤ (inputMax f + 17) * (N + 1) ^ 3 := by
    have hm := Nat.mul_le_mul_left (inputMax f + 11) (show N ≤ (N + 1) ^ 3 by omega)
    rw [Nat.mul_comm (inputMax f + 11) N] at hm
    have he : inputMax f + 17 = (inputMax f + 11) + 6 := by omega
    unfold inputCost
    rw [he, Nat.add_mul (inputMax f + 11) 6 ((N + 1) ^ 3)]
    omega
  have hz : (dom g).length * (3 * N + 7) + 2 ≤ (7 * (dom g).length + 2) * (N + 1) ^ 3 := by
    have hm := Nat.mul_le_mul_left (dom g).length (show 3 * N + 7 ≤ 7 * (N + 1) ^ 3 by omega)
    have he : (dom g).length * (7 * (N + 1) ^ 3) = 7 * (dom g).length * (N + 1) ^ 3 := by
      rw [← Nat.mul_assoc, Nat.mul_comm (dom g).length 7]
    rw [he] at hm
    rw [Nat.add_mul (7 * (dom g).length) 2 ((N + 1) ^ 3)]
    omega
  have hit := iterateCost_le g N
  have hf := Nat.le_trans (finishCost_le N)
    (Nat.mul_le_mul_left 128 (Nat.pow_le_pow_right (show 1 ≤ N + 1 by omega) (show 2 ≤ 3 by omega)))
  unfold programCost programCoeff
  simp only [Nat.add_mul] at hi hz ⊢
  omega

end Shallot.Packrat.Machine
