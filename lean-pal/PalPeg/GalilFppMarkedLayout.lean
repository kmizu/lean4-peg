import PalPeg.GalilFppPrepareLayout

set_option autoImplicit false
namespace PalPeg.GalilFppMarkedLayout
open GalilFppWide GalilFppPreparation GalilFppPrepareCopy GalilFppPrepareCells
open GalilFppPrepareInit GalilFppPrepareLayout GalilFppMarkTransform GalilFppMarkSimulation

theorem marksBase_cell (n i : ℕ) : marksBase n i =
    if i = 0 then 4 else if i ≤ n then 7 else if i = n+1 then 5 else 6 := by
  by_cases hi : i = 0
  · subst i
    rw [marksBase, fill_outside _ 1 _ 0 (Or.inl (by omega))]
    rfl
  · by_cases hn : i ≤ n
    · have hk : i-1 < (List.replicate n (7 : Fin 9) ++ [5]).length := by simp; omega
      have he : 1+(i-1) = i := by omega
      rw [marksBase, ← he, fill_inside _ 1 _ (i-1) hk, he,
        List.getElem_append_left (by simp; omega)]
      simp [hi, hn]
    · by_cases he : i = n+1
      · subst i
        have hk : n < (List.replicate n (7 : Fin 9) ++ [5]).length := by simp
        have hh := fill_inside (List.replicate n (7 : Fin 9) ++ [5]) 1 leftBlank n hk
        simpa [marksBase, List.getElem_append_right, Nat.add_comm] using hh
      · rw [marksBase, fill_outside _ 1 _ i (Or.inr (by simp; omega))]
        simp [leftBlank, hi, hn, he]

/-- Full physical layout consumed by DP: left marker, one boolean cell
per source prefix, right marker, then blank cells. -/
def marks (w : List (Fin 3)) (i : ℕ) : Fin 9 :=
  if i = 0 then 4
  else if i ≤ w.length then if (w.take i).reverse = w.take i then 8 else 7
  else if i = w.length+1 then 5 else 6

/-- No preparation premise remains. The complete nine-tape execution
returns the exact mark tape, including zeros, sentinels and blank suffix. -/
theorem marked_fpp_exact (w : List (Fin 3)) :
    ∃ y qs, Completed GalilFppMarkedCode.code (GalilFppPrepareInit.initial w) qs y ∧
      y.pc = 0 ∧ y.pos 8 = 0 ∧ y.pos 7 = 0 ∧ y.tape 7 = source w ∧ y.tape 8 = marks w := by
  obtain ⟨x, qs, hs, _, hpc, ht, hp⟩ := fresh_prepare w
  have hx := prepared_related w x hpc ht hp
  have hsep : (3 : Fin 4) ∉ w.map embed := by
    rintro h
    obtain ⟨a, _, ha⟩ := List.mem_map.mp h
    have hv := congrArg (fun t : Fin 4 => t.val) ha
    have := a.isLt
    simp [embed] at hv
    omega
  obtain ⟨v, ts, hv, hA, hvpc, hmem⟩ := GalilFppMarked.prepared_kernel_exact (w.map embed) hsep
  obtain ⟨y, rs, hr, _, hy⟩ := GalilFppMarkSimulation.completed (marksBase w.length) hv x hx
  obtain ⟨hsp, hst⟩ := GalilFppMarkedFrames.completed_source hr (by omega)
  have hsource : x.tape 7 = source w := by
    rw [ht]
    simp [copied, finish, written, backward_many_tape, turn, left, right, forward_many_tape, copyEntry]
  refine ⟨y, qs ++ rs, steps_completed hs hr, hy.pc.trans hvpc, hy.head.trans hA,
    by simpa [hp] using hsp, hst.trans hsource, ?_⟩
  rw [hy.marks]
  funext i
  have hinj : Function.Injective embed := by
    intro a b h; apply Fin.ext; exact congrArg (fun t : Fin 4 => t.val) h
  have hpal : ((w.map embed).take i).reverse = (w.map embed).take i ↔
      (w.take i).reverse = w.take i := by
    rw [← List.map_take, ← List.map_reverse]
    exact List.map_inj_right (fun a b h => hinj h)
  have hm : i ∈ v.output ↔ 0 < i ∧ i ≤ w.length ∧ (w.take i).reverse = w.take i := by
    simpa only [List.length_map, hpal] using hmem i
  simp only [markTape, hm, marksBase_cell, marks]
  by_cases hi : i = 0
  · subst i; simp
  · have hpos : 0 < i := by omega
    by_cases hn : i ≤ w.length <;> simp [hi, hpos, hn]

#print axioms marked_fpp_exact
end PalPeg.GalilFppMarkedLayout
