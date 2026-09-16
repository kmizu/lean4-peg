import PalPeg.GalilDpPrepared
import PalPeg.GalilFppMarkedCost

set_option autoImplicit false
namespace PalPeg.GalilDpPreparedCost
open GalilFppWide GalilDpTransform GalilDpSimulation GalilFppPrepareCopy GalilDpPrepared

/-- Preparation up to the actual DP search entry, including dispatch. -/
theorem prepared_cost (w : List (Fin 3)) (lower : ℕ) :
    ∃ y qs, Steps GalilDpCode.code (initial w lower) qs y ∧
      y.pc = 372 ∧ y.pos 8 = 0 ∧ y.pos 9 = 0 ∧ y.pos 7 = 0 ∧
      y.tape 7 = source w ∧ y.tape 8 = GalilFppMarkedLayout.marks w ∧
      y.tape 9 = GalilFppMarkedLayout.marks w ∧
      y.pos 10 = 0 ∧ y.pos 11 = 0 ∧ y.tape 10 = lowerTape lower ∧
      y.tape 11 = (fun _ => 6) ∧ qs.length ≤ 3168*w.length+1661 := by
  obtain ⟨x,qs,hs,hxpc,hx8,hx7,hxt,hxm,hcost⟩ :=
    GalilFppMarkedCost.marked_fpp_exact_cost w
  obtain ⟨v,rs,hr,hrl,hv⟩ := GalilDpSimulation.completed hs _ (initial_related w lower)
  have hvpc : v.pc = 0 := hv.pc.trans hxpc
  have hframe := (GalilDpFrames.before_search hr (by omega)).2
  obtain ⟨hlp,hlt⟩ := hframe 10 (by decide)
  obtain ⟨hop,hot⟩ := hframe 11 (by decide)
  have hv8 : v.pos 8 = 0 := (hv.pos 8).trans hx8
  have hv9 : v.pos 9 = 0 := hv.head.symm.trans hv8
  have hv7 : v.pos 7 = 0 := (hv.pos 7).trans hx7
  have hvt : v.tape 7 = source w := (hv.tape 7).trans hxt
  have hvm : v.tape 8 = GalilFppMarkedLayout.marks w := (hv.tape 8).trans hxm
  have hvs : v.tape 7 (v.pos 7) = 4 := by
    rw [hv7,hvt]
    simp [source,GalilFppInputWord.inputTape]
  have hd := dispatch ⟨0,by decide⟩ v (by rfl) hvpc hvs
  refine ⟨{v with pc := 372},rs ++ [0],steps_append hr hd,rfl,
    hv8,hv9,hv7,hvt,hvm,hv.marks.symm.trans hvm,
    hlp,hop,by simpa [initial] using hlt,by simpa [initial] using hot,?_⟩
  simp only [List.length_append,List.length_cons,List.length_nil]
  omega

#print axioms prepared_cost
end PalPeg.GalilDpPreparedCost
