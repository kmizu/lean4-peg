import PalPeg.GalilFppGenerationCost
import PalPeg.GalilFppMarkedLayout

set_option autoImplicit false
namespace PalPeg.GalilFppMarkedCost
open GalilFppWide GalilFppPreparation GalilFppPrepareCopy GalilFppPrepareCells
open GalilFppPrepareInit GalilFppPrepareLayout GalilFppMarkTransform GalilFppMarkSimulation
open GalilFppMarkedLayout

/-- Full nine-tape preparation and marked kernel, with exact marks and a
conservative bound derived from the real seven-tape instruction trace. -/
theorem marked_fpp_exact_cost (w : List (Fin 3)) :
    ∃ y qs, Completed GalilFppMarkedCode.code (GalilFppPrepareInit.initial w) qs y ∧
      y.pc = 0 ∧ y.pos 8 = 0 ∧ y.pos 7 = 0 ∧ y.tape 7 = source w ∧
      y.tape 8 = marks w ∧ qs.length ≤ 1584*w.length+830 := by
  obtain ⟨x,qs,hs,hl,hpc,ht,hp⟩ := fresh_prepare w
  have hx := prepared_related w x hpc ht hp
  have hsep : (3 : Fin 4) ∉ w.map embed := by
    rintro h
    obtain ⟨a,_,ha⟩ := List.mem_map.mp h
    have hv := congrArg (fun t : Fin 4 => t.val) ha
    have := a.isLt
    simp [embed] at hv
    omega
  obtain ⟨v,ts,hv,hout,hA,hvpc,hcost⟩ :=
    GalilFppGenerationCost.initial_completed_cost (GalilFppMarked.prepared (w.map embed))
  have hmem : ∀ b, b ∈ v.output ↔
      0 < b ∧ b ≤ (w.map embed).length ∧
        ((w.map embed).take b).reverse = (w.map embed).take b := by
    intro b
    rw [hout,GalilFppChain.mem_initial_output]
    constructor
    · rintro ⟨hb,hbl,hborder⟩
      have hbound := GalilFppMarked.proper_border_bound _ hsep b hbl hborder
      exact ⟨hb,hbound,(GalilFppMarked.prepared_border _ b hbound).mp hborder⟩
    · rintro ⟨hb,hbound,hpal⟩
      refine ⟨hb,?_,(GalilFppMarked.prepared_border _ b hbound).mpr hpal⟩
      rw [GalilFppMarked.prepared_length]; omega
  obtain ⟨y,rs,hr,hrl,hy⟩ := GalilFppMarkSimulation.completed (marksBase w.length) hv x hx
  obtain ⟨hsp,hst⟩ := GalilFppMarkedFrames.completed_source hr (by omega)
  have hsource : x.tape 7 = source w := by
    rw [ht]
    simp [copied,finish,written,backward_many_tape,turn,left,right,forward_many_tape,copyEntry]
  refine ⟨y,qs ++ rs,steps_completed hs hr,hy.pc.trans hvpc,hy.head.trans hA,
    by simpa [hp] using hsp,hst.trans hsource,?_,?_⟩
  · rw [hy.marks]
    funext i
    have hinj : Function.Injective embed := by
      intro a b h; apply Fin.ext; exact congrArg (fun t : Fin 4 => t.val) h
    have hpal : ((w.map embed).take i).reverse = (w.map embed).take i ↔
        (w.take i).reverse = w.take i := by
      rw [← List.map_take,← List.map_reverse]
      exact List.map_inj_right (fun a b h => hinj h)
    have hm : i ∈ v.output ↔ 0 < i ∧ i ≤ w.length ∧ (w.take i).reverse = w.take i := by
      simpa only [List.length_map,hpal] using hmem i
    simp only [markTape,hm,marksBase_cell,marks]
    by_cases hi : i = 0
    · subst i; simp
    · have hpos : 0 < i := by omega
      by_cases hn : i ≤ w.length <;> simp [hi,hpos,hn]
  · rw [GalilFppMarked.prepared_length,List.length_map] at hcost
    simp only [List.length_append]
    omega

#print axioms marked_fpp_exact_cost
end PalPeg.GalilFppMarkedCost
