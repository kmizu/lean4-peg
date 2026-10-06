import Complexity.Univ.Sim

/-!
# Reading the output of a simulated machine

The output of a machine is the bits on tape 0 up to the first blank (`OutputIs`). On a finite tape it is read by
`readOut` (`readOut_of_cells`). When the machine has halted with an output within `B` steps, the table run for
`B` steps shows that output on tape 0 (`frun_output`).
-/

namespace Complexity

/-- The bits of a tape up to its first blank. -/
def readOut (t : List Nat) : List Bool := (t.takeWhile (· ≠ 0)).map (· == 2)

theorem readOut_of_cells : ∀ {out : List Bool} {t : List Nat},
    (∀ j (hj : j < out.length), t.getD j 0 = bitSym (out[j]'hj)) → t.getD out.length 0 = 0 → readOut t = out
  | [], t, _, h₀ => by
    cases t with
    | nil => rfl
    | cons a t => simp at h₀; simp [readOut, h₀]
  | b :: out, t, h₁, h₀ => by
    cases t with
    | nil => have := h₁ 0 (by simp); cases b <;> simp [bitSym] at this
    | cons a t =>
      have ha := h₁ 0 (by simp)
      simp only [List.getD_cons_zero, List.getElem_cons_zero] at ha
      have ih := readOut_of_cells (out := out) (t := t) (fun j hj => by
        have := h₁ (j + 1) (by simp; omega); simpa using this) (by simpa using h₀)
      have hne : a ≠ 0 := by rw [ha]; cases b <;> simp [bitSym]
      have e : (a :: t).takeWhile (· ≠ 0) = a :: t.takeWhile (· ≠ 0) := by simp [List.takeWhile_cons, hne]
      simp only [readOut] at ih ⊢
      rw [e, List.map_cons, ih, ha]
      cases b <;> rfl

/-- **The table shows the output of a halted machine.** -/
theorem frun_output {k : Nat} (hk : 0 < k) (M : TM k) (w : List Bool) {t B : Nat} (ht : t ≤ B)
    (hs : (M.run (initCfg k w) t).state = 0) {out : List Bool} (ho : OutputIs hk (M.run (initCfg k w) t) out) :
    readOut ((frun (tableOf M) (finit k w) B).tapes.getD 0 []) = out := by
  have hB : M.run (initCfg k w) B = M.run (initCfg k w) t := TM.run_stays M _ ht (.inl hs)
  have hr := frun_rep M w B
  rw [hB] at hr
  apply readOut_of_cells
  · intro j hj
    rw [show (0 : Nat) = (⟨0, hk⟩ : Fin k).val from rfl, hr.cells]
    exact ho.1 j hj
  · rw [show (0 : Nat) = (⟨0, hk⟩ : Fin k).val from rfl, hr.cells]
    exact ho.2

end Complexity
