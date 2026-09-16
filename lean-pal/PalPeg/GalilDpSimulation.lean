import PalPeg.GalilDpTransform

set_option autoImplicit false
set_option maxRecDepth 100000
namespace PalPeg.GalilDpSimulation
open GalilFppWide GalilDpTransform

@[simp] theorem index_eq (a b : Fin 9) : tapeIndex a = tapeIndex b ↔ a = b := by
  simp [tapeIndex, Fin.ext_iff]
@[simp] theorem index_marks (a : Fin 9) : tapeIndex a = 8 ↔ a = 8 := by
  change tapeIndex a = tapeIndex 8 ↔ a = 8
  exact index_eq a 8
@[simp] theorem index_marks_value : tapeIndex 8 = 8 := rfl
@[simp] theorem index_ne_second (a : Fin 9) : tapeIndex a ≠ 9 := by
  intro h
  have hv := congrArg Fin.val h
  have := a.isLt
  simp [tapeIndex] at hv
  omega

/-- At original instruction boundaries DP retains the entire marked FPP
configuration and a synchronized physical copy of MARKS on SECOND. -/
structure Related (x : Config 9) (z : Config 12) : Prop where
  pc : z.pc = x.pc
  pos : ∀ t, z.pos (tapeIndex t) = x.pos t
  tape : ∀ t, z.tape (tapeIndex t) = x.tape t
  head : z.pos 8 = z.pos 9
  marks : z.tape 8 = z.tape 9

theorem step (q : Fin 321) {x y : Config 9} {i : Instruction 9}
    (hi : GalilFppMarkedCode.code[q.val]? = some i) (hp : x.pc = q.val)
    (he : Execute i x y) (z : Config 12) (hr : Related x z) :
    ∃ v qs, Steps GalilDpCode.code z qs v ∧ qs.length ≤ 2 ∧ Related y v := by
  have hpc : z.pc = q.val := hr.pc.trans hp
  have h8 : z.pos 8 = x.pos 8 := hr.pos 8
  have ht8 : z.tape 8 = x.tape 8 := hr.tape 8
  cases he with
  | right x t n =>
    by_cases ht : t = 8
    · subst t
      obtain ⟨v, qs, hs, hl, hvpc, hvt, hvh, hv8, hvp⟩ :=
        duplicate_move q true n z hi hpc hr.head (by simp)
      refine ⟨v, qs, hs, by omega, ⟨hvpc, ?_, ?_, hvh, ?_⟩⟩
      · intro t
        by_cases ht : t = 8
        · subst t; simpa [h8] using hv8
        · simpa [ht] using (hvp (tapeIndex t) (by simpa using ht)
            (index_ne_second t)).trans (hr.pos t)
      · intro t; rw [hvt]; exact hr.tape t
      · rw [hvt]; exact hr.marks
    · have hc := other_move_code q t true n ht hi
      let v : Config 12 := { z with
        pc := n
        pos := Function.update z.pos (tapeIndex t) (z.pos (tapeIndex t)+1) }
      have hs : Steps GalilDpCode.code z [q.val] v := by
        simpa only [hpc] using (Steps.step z v v _ [] (by rw [hpc]; exact hc)
          (.right _ _ _) (.nil _))
      refine ⟨v, _, hs, by simp, ⟨rfl, ?_, hr.tape, ?_, hr.marks⟩⟩
      · intro k
        by_cases hk : k = t
        · subst k; simp [v, hr.pos]
        · simp [v, hk, hr.pos]
      · simpa [v, Ne.symm (index_ne_second t), Ne.symm ((index_marks t).not.mpr ht)] using hr.head
  | left x t n hpos =>
    by_cases ht : t = 8
    · subst t
      obtain ⟨v, qs, hs, hl, hvpc, hvt, hvh, hv8, hvp⟩ :=
        duplicate_move q false n z hi hpc hr.head (by intro _; omega)
      refine ⟨v, qs, hs, by omega, ⟨hvpc, ?_, ?_, hvh, ?_⟩⟩
      · intro t
        by_cases ht : t = 8
        · subst t; simpa [h8] using hv8
        · simpa [ht] using (hvp (tapeIndex t) (by simpa using ht)
            (index_ne_second t)).trans (hr.pos t)
      · intro t; rw [hvt]; exact hr.tape t
      · rw [hvt]; exact hr.marks
    · have hc := other_move_code q t false n ht hi
      let v : Config 12 := { z with
        pc := n
        pos := Function.update z.pos (tapeIndex t) (z.pos (tapeIndex t)-1) }
      have hzpos : 0 < z.pos (tapeIndex t) := by rw [hr.pos]; exact hpos
      have hs : Steps GalilDpCode.code z [q.val] v := by
        simpa only [hpc] using (Steps.step z v v _ [] (by rw [hpc]; exact hc)
          (.left _ _ _ hzpos) (.nil _))
      refine ⟨v, _, hs, by simp, ⟨rfl, ?_, hr.tape, ?_, hr.marks⟩⟩
      · intro k
        by_cases hk : k = t
        · subst k; simp [v, hr.pos]
        · simp [v, hk, hr.pos]
      · simpa [v, Ne.symm (index_ne_second t), Ne.symm ((index_marks t).not.mpr ht)] using hr.head
  | write x t s n =>
    by_cases ht : t = 8
    · subst t
      obtain ⟨v, qs, hs, hl, hvpc, hvp, hvm, hv8, hvt⟩ :=
        duplicate_write q s n z hi hpc hr.head hr.marks
      refine ⟨v, qs, hs, by omega, ⟨hvpc, ?_, ?_, ?_, hvm⟩⟩
      · intro t; rw [hvp]; exact hr.pos t
      · intro t
        by_cases ht : t = 8
        · subst t; simpa [h8, ht8] using hv8
        · simpa [ht] using (hvt (tapeIndex t) (by simpa using ht)
            (index_ne_second t)).trans (hr.tape t)
      · rw [hvp]; exact hr.head
    · have hc := other_write_code q t s n ht hi
      let v : Config 12 := { z with
        pc := n
        tape := Function.update z.tape (tapeIndex t)
          (Function.update (z.tape (tapeIndex t)) (z.pos (tapeIndex t)) s) }
      have hs : Steps GalilDpCode.code z [q.val] v := by
        simpa only [hpc] using (Steps.step z v v _ [] (by rw [hpc]; exact hc)
          (.write _ _ _ _) (.nil _))
      refine ⟨v, _, hs, by simp, ⟨rfl, hr.pos, ?_, hr.head, ?_⟩⟩
      · intro k
        by_cases hk : k = t
        · subst k; simp [v, hr.pos, hr.tape]
        · simp [v, hk, hr.tape]
      · simpa [v, Ne.symm (index_ne_second t), Ne.symm ((index_marks t).not.mpr ht)] using hr.marks
  | read x t cs n hm =>
    have hc := read_code q t cs hi
    let v : Config 12 := { z with pc := n }
    have hz : (z.tape (tapeIndex t) (z.pos (tapeIndex t)), n) ∈ cs := by
      rw [hr.pos, hr.tape]; exact hm
    have hs : Steps GalilDpCode.code z [q.val] v := by
      simpa only [hpc] using (Steps.step z v v _ [] (by rw [hpc]; exact hc)
        (.read _ _ _ _ hz) (.nil _))
    exact ⟨v, _, hs, by simp, ⟨rfl, hr.pos, hr.tape, hr.head, hr.marks⟩⟩

theorem pc_bound {q : ℕ} {i : Instruction 9}
    (hi : GalilFppMarkedCode.code[q]? = some i) : q < 321 := by
  obtain ⟨hq, _⟩ := List.getElem?_eq_some_iff.mp hi
  exact hq

theorem steps {x y : Config 9} {qs : List ℕ}
    (hs : Steps GalilFppMarkedCode.code x qs y) (u : Config 12) (hu : Related x u) :
    ∃ v rs, Steps GalilDpCode.code u rs v ∧ rs.length ≤ 2*qs.length ∧ Related y v := by
  induction hs generalizing u with
  | nil => exact ⟨u, [], .nil _, by simp, hu⟩
  | step x y z i qs hi he hs ih =>
    obtain ⟨v, rs, hr, hl, hv⟩ := step ⟨x.pc, pc_bound hi⟩ hi rfl he u hu
    obtain ⟨w, ts, ht, htl, hw⟩ := ih v hv
    refine ⟨w, rs ++ ts, steps_append hr ht, ?_, hw⟩
    simp only [List.length_append, List.length_cons]; omega

/-- The complete FPP computation lifts up to its return point. DP does
not halt there: the caller can subsequently execute `dispatch`. -/
theorem completed {x y : Config 9} {qs : List ℕ}
    (hs : Completed GalilFppMarkedCode.code x qs y) (u : Config 12) (hu : Related x u) :
    ∃ v rs, Steps GalilDpCode.code u rs v ∧ rs.length ≤ 2*qs.length ∧ Related y v := by
  induction hs generalizing u with
  | halt x hi => exact ⟨u, [], .nil _, by simp, hu⟩
  | step x y z i qs hi he hs ih =>
    obtain ⟨v, rs, hr, hl, hv⟩ := step ⟨x.pc, pc_bound hi⟩ hi rfl he u hu
    obtain ⟨w, ts, ht, htl, hw⟩ := ih v hv
    refine ⟨w, rs ++ ts, steps_append hr ht, ?_, hw⟩
    simp only [List.length_append, List.length_cons]; omega

#print axioms completed
end PalPeg.GalilDpSimulation
