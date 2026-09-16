import PalPeg.GalilDpSimulation
import PalPeg.GalilDpFrames
import PalPeg.GalilFppMarkedLayout

set_option autoImplicit false
namespace PalPeg.GalilDpPrepared
open GalilFppWide GalilDpTransform GalilDpSimulation GalilFppPrepareCopy

def lowerTape (lower : ℕ) (i : ℕ) : Fin 9 :=
  if i = 0 then 4 else if i ≤ lower then 8 else if i = lower+1 then 5 else 6

/-- Exactly the source and unary lower-bound preload used by Scala runDp. -/
def initial (w : List (Fin 3)) (lower : ℕ) : Config 12 where
  pc := 320
  tape := fun t => if t = 7 then source w else if t = 10 then lowerTape lower else fun _ => 6
  pos := fun _ => 0

theorem initial_related (w : List (Fin 3)) (lower : ℕ) :
    Related (GalilFppPrepareInit.initial w) (initial w lower) := by
  refine ⟨rfl, ?_, ?_, rfl, rfl⟩
  · intro t; rfl
  · intro t
    have ht : t.val ≠ 10 := by have := t.isLt; omega
    simp [initial, GalilFppPrepareInit.initial, tapeIndex, Fin.ext_iff, ht]

/-- Starting from the real twelve-tape preload, execution reaches the DP
search with two exact palindrome-prefix tapes, synchronized at the left
marker, and the original source preserved. This does not assert search
correctness or a linear bound for the complete computation. -/
theorem prepared (w : List (Fin 3)) (lower : ℕ) :
    ∃ y qs, Steps GalilDpCode.code (initial w lower) qs y ∧
      y.pc = 372 ∧ y.pos 8 = 0 ∧ y.pos 9 = 0 ∧ y.pos 7 = 0 ∧
      y.tape 7 = source w ∧ y.tape 8 = GalilFppMarkedLayout.marks w ∧
      y.tape 9 = GalilFppMarkedLayout.marks w ∧
      y.pos 10 = 0 ∧ y.pos 11 = 0 ∧ y.tape 10 = lowerTape lower ∧
      y.tape 11 = (fun _ => 6) := by
  obtain ⟨x, qs, hs, hxpc, hx8, hx7, hxt, hxm⟩ := GalilFppMarkedLayout.marked_fpp_exact w
  obtain ⟨v, rs, hr, _, hv⟩ := GalilDpSimulation.completed hs _ (initial_related w lower)
  have hvpc : v.pc = 0 := hv.pc.trans hxpc
  have hframe := (GalilDpFrames.before_search hr (by omega)).2
  obtain ⟨hlp, hlt⟩ := hframe 10 (by decide)
  obtain ⟨hop, hot⟩ := hframe 11 (by decide)
  have hv8 : v.pos 8 = 0 := (hv.pos 8).trans hx8
  have hv9 : v.pos 9 = 0 := hv.head.symm.trans hv8
  have hv7 : v.pos 7 = 0 := (hv.pos 7).trans hx7
  have hvt : v.tape 7 = source w := (hv.tape 7).trans hxt
  have hvm : v.tape 8 = GalilFppMarkedLayout.marks w := (hv.tape 8).trans hxm
  have hvs : v.tape 7 (v.pos 7) = 4 := by
    rw [hv7, hvt]
    simp [source, GalilFppInputWord.inputTape]
  have hd := dispatch ⟨0, by decide⟩ v (by rfl) hvpc hvs
  exact ⟨{ v with pc := 372 }, rs ++ [0], steps_append hr hd, rfl,
    hv8, hv9, hv7, hvt, hvm, hv.marks.symm.trans hvm,
    hlp, hop, by simpa [initial] using hlt, by simpa [initial] using hot⟩

#print axioms prepared
end PalPeg.GalilDpPrepared
