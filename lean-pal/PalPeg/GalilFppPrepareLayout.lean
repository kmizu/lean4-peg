import PalPeg.GalilFppPrepareInit
import PalPeg.GalilFppMarkedFrames

set_option autoImplicit false
namespace PalPeg.GalilFppPrepareLayout
open GalilFppWide GalilFppPreparation GalilFppPrepareCopy GalilFppPrepareCells
open GalilFppPrepareInit GalilFppMarkTransform GalilFppMarkSimulation

def leftBlank (i : ℕ) : Fin 9 := if i = 0 then 4 else 6

theorem fill_input (w : List (Fin 4)) :
    fill (w.map GalilFppRetry.letter ++ [5]) 1 leftBlank = GalilFppInputWord.inputTape w := by
  funext i
  by_cases hi : i = 0
  · subst i
    rw [fill_outside _ 1 _ 0 (Or.inl (by omega))]
    rfl
  · by_cases hb : i-1 < w.length
    · have hk : i-1 < (w.map GalilFppRetry.letter ++ [5]).length := by simp; omega
      have he : 1+(i-1) = i := by omega
      rw [← he, fill_inside _ 1 _ (i-1) hk, he,
        List.getElem_append_left (by simpa using hb), List.getElem_map]
      simp [GalilFppInputWord.inputTape, hi, List.getElem?_eq_getElem hb]
    · have hnone : w[i-1]? = none := by simp [List.getElem?_eq_none_iff, show w.length ≤ i-1 by omega]
      by_cases he : i = w.length+1
      · subst i
        have hk : w.length < (w.map GalilFppRetry.letter ++ [5]).length := by simp
        have hh := fill_inside (w.map GalilFppRetry.letter ++ [5]) 1 leftBlank w.length hk
        simpa [Nat.add_comm, List.getElem_append_right, GalilFppInputWord.inputTape] using hh
      · rw [fill_outside _ 1 _ i (Or.inr (by simp; omega))]
        simp [leftBlank, GalilFppInputWord.inputTape, hi, he, hnone]

def marksBase (n : ℕ) : ℕ → Fin 9 := fill (List.replicate n 7 ++ [5]) 1 leftBlank

theorem marksBase_ne_one (n i : ℕ) : marksBase n i ≠ 8 := by
  by_cases hi : i = 0
  · subst i
    rw [marksBase, fill_outside _ 1 _ 0 (Or.inl (by omega))]
    decide
  · by_cases hb : i ≤ n+1
    · have hk : i-1 < (List.replicate n (7 : Fin 9) ++ [5]).length := by simp; omega
      have he : 1+(i-1) = i := by omega
      rw [marksBase, ← he, fill_inside _ 1 _ (i-1) hk]
      have hm := List.getElem_mem hk
      simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at hm
      rcases hm with ⟨_, h⟩ | h <;> rw [h] <;> decide
    · rw [marksBase, fill_outside _ 1 _ i (Or.inr (by simp; omega))]
      simp [leftBlank, hi]

theorem copied_input (w : List (Fin 3)) (t : Fin 9) (ht : t = 0 ∨ t = 1) :
    (copied w (copyEntry w)).tape t =
      GalilFppInputWord.inputTape (GalilFppMarked.prepared (w.map embed)) := by
  rw [copied_ab w (copyEntry w) t ht]
  have hp : (copyEntry w).pos t = 1 := by rcases ht with rfl | rfl <;> rfl
  have hb : (copyEntry w).tape t = leftBlank := by rcases ht with rfl | rfl <;> rfl
  rw [hp, hb, ← fill_input]
  congr 2
  simp [GalilFppMarked.prepared, List.map_append, List.map_reverse, List.map_map,
    embed, GalilFppRetry.letter, Function.comp_def]
  rfl

/-- The concrete preparation result satisfies every field of the
previously conditional kernel-entry simulation relation. -/
theorem prepared_related (w : List (Fin 3)) (y : Config 9)
    (hpc : y.pc = 227) (ht : y.tape = (copied w (copyEntry w)).tape)
    (hp : y.pos = fun t => if t = 1 then 1 else 0) :
    Related (marksBase w.length)
      (GalilFppGeneration.initial (GalilFppMarked.prepared (w.map embed))) y := by
  refine ⟨hpc, ?_, ?_, ?_, ?_⟩
  · intro t
    fin_cases t <;> simp [hp, tapeIndex, GalilFppGeneration.initial]
  · intro t
    rw [ht]
    fin_cases t
    · exact copied_input w 0 (Or.inl rfl)
    · exact copied_input w 1 (Or.inr rfl)
    all_goals simp [copied, finish, written, backward_many_tape, turn, left, right,
      forward_many_tape, copyEntry, tapeIndex, GalilFppGeneration.initial]
  · simp [hp, GalilFppGeneration.initial]
  · rw [ht, copied_marks]
    rfl

/-- The complete exported marked-FPP program, from fresh scratch tapes,
terminates and marks exactly the positive palindromic source prefixes. -/
theorem marked_fpp (w : List (Fin 3)) :
    ∃ y qs, Completed GalilFppMarkedCode.code (GalilFppPrepareInit.initial w) qs y ∧
      y.pos 8 = 0 ∧ y.pc = 0 ∧ y.pos 7 = 0 ∧ y.tape 7 = source w ∧
      ∀ b, y.tape 8 b = 8 ↔ 0 < b ∧ b ≤ w.length ∧ (w.take b).reverse = w.take b := by
  obtain ⟨x, qs, hs, _, hpc, ht, hp⟩ := fresh_prepare w
  have hr := prepared_related w x hpc ht hp
  have hsep : (3 : Fin 4) ∉ w.map embed := by
    rintro h
    obtain ⟨a, _, ha⟩ := List.mem_map.mp h
    have hv := congrArg (fun t : Fin 4 => t.val) ha
    have := a.isLt
    simp [embed] at hv
    omega
  obtain ⟨y, rs, hrun, hpos, hyPC, hmarks⟩ := prepared_marks (w.map embed) hsep
    (marksBase w.length) (marksBase_ne_one w.length) x hr
  obtain ⟨hsourcePos, hsourceTape⟩ := GalilFppMarkedFrames.completed_source hrun (by omega)
  have hsource : x.tape 7 = source w := by
    rw [ht]
    simp [copied, finish, written, backward_many_tape, turn, left, right,
      forward_many_tape, copyEntry]
  refine ⟨y, qs ++ rs, GalilFppMarkSimulation.steps_completed hs hrun, hpos, hyPC,
    by simpa [hp] using hsourcePos, hsourceTape.trans hsource, ?_⟩
  intro b
  have hinj : Function.Injective embed := by
    intro a c h
    apply Fin.ext
    exact congrArg (fun t : Fin 4 => t.val) h
  have hpal : ((w.map embed).take b).reverse = (w.map embed).take b ↔
      (w.take b).reverse = w.take b := by
    rw [← List.map_take, ← List.map_reverse]
    exact List.map_inj_right (fun a c h => hinj h)
  simpa only [List.length_map, hpal] using hmarks b

#print axioms marked_fpp
#print axioms prepared_related
#print axioms fill_input
#print axioms marksBase_ne_one
end PalPeg.GalilFppPrepareLayout
