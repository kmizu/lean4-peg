import PalPeg.GalilFppMarkTransform
import PalPeg.GalilFppMarked

set_option autoImplicit false
namespace PalPeg.GalilFppMarkSimulation
open GalilFppWide GalilFppMarkTransform

@[simp] theorem index_eq (a b : Fin 7) : tapeIndex a = tapeIndex b ↔ a = b := by
  simp [tapeIndex, Fin.ext_iff]
@[simp] theorem index_zero (a : Fin 7) : tapeIndex a = 0 ↔ a = 0 := by
  constructor
  · intro h; apply Fin.ext; exact congrArg (fun t : Fin 9 => t.val) h
  · intro h; subst a; rfl
@[simp] theorem index_zero_value : tapeIndex 0 = 0 := rfl
@[simp] theorem index_ne_marks (a : Fin 7) : tapeIndex a ≠ 8 := by
  intro h; have := congrArg Fin.val h; have := a.isLt; simp [tapeIndex] at *; omega

/-- At kernel instruction boundaries the first seven tapes agree exactly;
MARKS has A's head and represents the kernel's emitted-length list. -/
structure Related (base : ℕ → Fin 9) (x : GalilFppInstruction.Config) (z : Config 9) : Prop where
  pc : z.pc = x.pc
  pos : ∀ t, z.pos (tapeIndex t) = x.pos t
  tape : ∀ t, z.tape (tapeIndex t) = x.tape t
  head : z.pos 8 = x.pos 0
  marks : z.tape 8 = markTape base x.output

/-- Each successful kernel instruction is realized by one or two actual
instructions in the exported marked program. -/
theorem step (base : ℕ → Fin 9) (q : Fin 228)
    {x y : GalilFppInstruction.Config} {i : GalilFppInstruction.Instruction}
    (hi : GalilFppCode.code[q.val]? = some i) (hp : x.pc = q.val)
    (he : GalilFppInstruction.Execute i x y) (z : Config 9) (hr : Related base x z) :
    ∃ v qs, Steps GalilFppMarkedCode.code z qs v ∧ qs.length ≤ 2 ∧ Related base y v := by
  have hpc : z.pc = q.val := hr.pc.trans hp
  have h0 : z.pos 0 = x.pos 0 := hr.pos 0
  have halign : z.pos 8 = z.pos 0 := hr.head.trans h0.symm
  cases he with
  | emit x n =>
    obtain ⟨v, hs, hvpc, hvpos, hvmarks, hvtape⟩ := emit_write q n z hi hpc halign base x.output hr.marks
    refine ⟨v, [q.val], hs, by simp, ⟨hvpc, ?_, ?_, ?_, ?_⟩⟩
    · intro t; rw [hvpos]; exact hr.pos t
    · intro t; rw [hvtape _ (index_ne_marks t)]; exact hr.tape t
    · rw [hvpos]; exact hr.head
    · simpa [h0] using hvmarks
  | right x t n =>
    by_cases ht : t = 0
    · subst t
      obtain ⟨v, qs, hs, hl, hvpc, hv0, hv8, hvt, hvp⟩ := move_right q n z hi hpc halign
      refine ⟨v, qs, hs, by omega, ⟨hvpc, ?_, ?_, ?_, ?_⟩⟩
      · intro t
        by_cases ht : t = 0
        · subst t; simpa [h0] using hv0
        · simpa [ht] using (hvp (tapeIndex t) (by simpa using ht) (index_ne_marks t)).trans (hr.pos t)
      · intro t; rw [hvt]; exact hr.tape t
      · simpa [hv0, h0] using hv8
      · rw [hvt]; exact hr.marks
    · have hc : GalilFppMarkedCode.code[q.val]? = some (.move (tapeIndex t) true n) := by
        simpa [hi, translated, ht] using all_kernel_rows q
      let v : Config 9 := { z with pc := n, pos := Function.update z.pos (tapeIndex t) (z.pos (tapeIndex t)+1) }
      have hs : Steps GalilFppMarkedCode.code z [q.val] v := by
        simpa only [hpc] using (Steps.step z v v _ [] (by rw [hpc]; exact hc) (.right _ _ _) (.nil _))
      refine ⟨v, _, hs, by simp, ⟨rfl, ?_, hr.tape, ?_, hr.marks⟩⟩
      · intro k
        by_cases hk : k = t
        · subst k; simp [v, hr.pos]
        · simp [v, hk, hr.pos]
      · simpa [v, Ne.symm (index_ne_marks t), Ne.symm ht] using hr.head
  | left x t n hpos =>
    by_cases ht : t = 0
    · subst t
      obtain ⟨v, qs, hs, hl, hvpc, hv0, hv8, hvt, hvp⟩ := move_left q n z hi hpc halign (by omega)
      refine ⟨v, qs, hs, by omega, ⟨hvpc, ?_, ?_, ?_, ?_⟩⟩
      · intro t
        by_cases ht : t = 0
        · subst t; simpa [h0] using hv0
        · simpa [ht] using (hvp (tapeIndex t) (by simpa using ht) (index_ne_marks t)).trans (hr.pos t)
      · intro t; rw [hvt]; exact hr.tape t
      · simpa [hv0, h0] using hv8
      · rw [hvt]; exact hr.marks
    · have hc : GalilFppMarkedCode.code[q.val]? = some (.move (tapeIndex t) false n) := by
        simpa [hi, translated, ht] using all_kernel_rows q
      let v : Config 9 := { z with pc := n, pos := Function.update z.pos (tapeIndex t) (z.pos (tapeIndex t)-1) }
      have hzpos : 0 < z.pos (tapeIndex t) := by rw [hr.pos]; exact hpos
      have hs : Steps GalilFppMarkedCode.code z [q.val] v := by
        simpa only [hpc] using (Steps.step z v v _ [] (by rw [hpc]; exact hc) (.left _ _ _ hzpos) (.nil _))
      refine ⟨v, _, hs, by simp, ⟨rfl, ?_, hr.tape, ?_, hr.marks⟩⟩
      · intro k
        by_cases hk : k = t
        · subst k; simp [v, hr.pos]
        · simp [v, hk, hr.pos]
      · simpa [v, Ne.symm (index_ne_marks t), Ne.symm ht] using hr.head
  | write x t s n =>
    have hc : GalilFppMarkedCode.code[q.val]? = some (.write (tapeIndex t) s n) := by
      simpa [hi, translated] using all_kernel_rows q
    let v : Config 9 := { z with
      pc := n
      tape := Function.update z.tape (tapeIndex t) (Function.update (z.tape (tapeIndex t)) (z.pos (tapeIndex t)) s) }
    have hs : Steps GalilFppMarkedCode.code z [q.val] v := by
      simpa only [hpc] using (Steps.step z v v _ [] (by rw [hpc]; exact hc) (.write _ _ _ _) (.nil _))
    refine ⟨v, _, hs, by simp, ⟨rfl, hr.pos, ?_, hr.head, ?_⟩⟩
    · intro k
      by_cases hk : k = t
      · subst k; simp [v, hr.pos, hr.tape]
      · simp [v, hk, hr.tape]
    · simpa [v, Ne.symm (index_ne_marks t)] using hr.marks
  | read x t cs n hmem =>
    have hc : GalilFppMarkedCode.code[q.val]? = some (.read (tapeIndex t) cs) := by
      simpa [hi, translated] using all_kernel_rows q
    let v : Config 9 := { z with pc := n }
    have hm : (z.tape (tapeIndex t) (z.pos (tapeIndex t)), n) ∈ cs := by
      rw [hr.pos, hr.tape]; exact hmem
    have hs : Steps GalilFppMarkedCode.code z [q.val] v := by
      simpa only [hpc] using (Steps.step z v v _ [] (by rw [hpc]; exact hc) (.read _ _ _ _ hm) (.nil _))
    exact ⟨v, _, hs, by simp, ⟨rfl, hr.pos, hr.tape, hr.head, hr.marks⟩⟩

theorem pc_bound {q : ℕ} {i : GalilFppInstruction.Instruction}
    (hi : GalilFppCode.code[q]? = some i) : q < 228 := by
  obtain ⟨hq, _⟩ := List.getElem?_eq_some_iff.mp hi
  exact hq

/-- Arbitrary successful prefixes of the kernel lift to actual marked
execution prefixes with at most twice the instruction count. -/
theorem steps (base : ℕ → Fin 9) {x y : GalilFppInstruction.Config} {qs : List ℕ}
    (hs : GalilFppInstruction.Steps GalilFppCode.code x qs y)
    (u : Config 9) (hu : Related base x u) :
    ∃ v rs, Steps GalilFppMarkedCode.code u rs v ∧ rs.length ≤ 2*qs.length ∧ Related base y v := by
  induction hs generalizing u with
  | nil => exact ⟨u, [], .nil _, by simp, hu⟩
  | step x y z i qs hi he hs ih =>
    obtain ⟨v, rs, hr, hl, hv⟩ := step base ⟨x.pc, pc_bound hi⟩ hi rfl he u hu
    obtain ⟨w, ts, ht, htl, hw⟩ := ih v hv
    refine ⟨w, rs ++ ts, steps_append hr ht, ?_, hw⟩
    simp only [List.length_append, List.length_cons]; omega

theorem steps_completed {u v w : Config 9} {qs rs : List ℕ}
    (hs : Steps GalilFppMarkedCode.code u qs v)
    (hr : Completed GalilFppMarkedCode.code v rs w) :
    Completed GalilFppMarkedCode.code u (qs ++ rs) w := by
  induction hs with
  | nil => exact hr
  | step u v w i qs hi he hs ih => exact .step _ _ _ _ _ hi he (ih hr)

/-- Termination and the mark/output correspondence survive the complete
Scala instruction transformation, including its replacement of emit. -/
theorem completed (base : ℕ → Fin 9) {x y : GalilFppInstruction.Config} {qs : List ℕ}
    (hs : GalilFppInstruction.Completed GalilFppCode.code x qs y)
    (u : Config 9) (hu : Related base x u) :
    ∃ v rs, Completed GalilFppMarkedCode.code u rs v ∧
      rs.length ≤ 2*qs.length ∧ Related base y v := by
  induction hs generalizing u with
  | halt x hi =>
    have hc := all_kernel_rows ⟨x.pc, pc_bound hi⟩
    have hrow : GalilFppMarkedCode.code[u.pc]? = some .halt := by
      rw [hu.pc]
      simpa [hi, translated] using hc
    exact ⟨u, [u.pc], .halt _ hrow, by simp, hu⟩
  | step x y z i qs hi he hs ih =>
    obtain ⟨v, rs, hr, hl, hv⟩ := step base ⟨x.pc, pc_bound hi⟩ hi rfl he u hu
    obtain ⟨w, ts, ht, htl, hw⟩ := ih v hv
    refine ⟨w, rs ++ ts, steps_completed hr ht, ?_, hw⟩
    simp only [List.length_append, List.length_cons]; omega

/-- After preparation has established the kernel-entry relation, the
actual nine-tape program terminates with exactly the palindrome-prefix
marks. The preparation loop itself is not assumed to be proved here. -/
theorem prepared_marks (w : List (Fin 4)) (hsep : (3 : Fin 4) ∉ w)
    (base : ℕ → Fin 9) (hbase : ∀ i, base i ≠ 8) (u : Config 9)
    (hu : Related base (GalilFppGeneration.initial (GalilFppMarked.prepared w)) u) :
    ∃ v rs, Completed GalilFppMarkedCode.code u rs v ∧ v.pos 8 = 0 ∧ v.pc = 0 ∧
      ∀ b, v.tape 8 b = 8 ↔ 0 < b ∧ b ≤ w.length ∧ (w.take b).reverse = w.take b := by
  obtain ⟨y, qs, hs, hpos, hpc, hmarks⟩ := GalilFppMarked.prepared_kernel_exact w hsep
  obtain ⟨v, rs, hr, _, hv⟩ := completed base hs u hu
  refine ⟨v, rs, hr, hv.head.trans hpos, hv.pc.trans hpc, ?_⟩
  intro b
  rw [hv.marks]
  have hm : markTape base y.output b = 8 ↔ b ∈ y.output := by
    by_cases hb : b ∈ y.output <;> simp [markTape, hb, hbase b]
  exact hm.trans (hmarks b)

#print axioms prepared_marks
#print axioms completed
#print axioms steps
#print axioms step
end PalPeg.GalilFppMarkSimulation
