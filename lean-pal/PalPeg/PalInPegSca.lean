import PalPeg.Existence

/-!
# `PAL ∈ PEG` from a scaffold automaton

The emitted Scala construction (window-pal → `SymbolicSca2Peg`) builds a scaffold automaton and
renders it as a PEG; no Turing machine is involved. This is the same route in Lean: any Kim–Park
scaffold automaton recognizing `PAL` gives a total PEG through `SCAToPEG.loffBackward`, since `PAL`
is closed under reversal.
-/
set_option autoImplicit false
namespace PalPeg
open PegSeparation

/-- **A scaffold automaton for `PAL` gives a total PEG for `PAL`.** -/
theorem pal_recognizedByTotalPEG_of_sca (h : RecognizedBySCA PAL) : RecognizedByTotalPEG PAL := by
  obtain ⟨s, k, d, r, A, hA⟩ := h
  obtain ⟨n, G, hTotal, hG⟩ := SCAToPEG.loffBackward A
  refine ⟨n, G, hTotal, fun w => ?_⟩
  have hGrammar : G.Recognizes w ↔ A.Accepts w.reverse := by
    have h := (hG w.reverse).symm
    rwa [List.reverse_reverse] at h
  rw [hGrammar, hA, PAL_reverse_mem]

/-- info: 'PalPeg.pal_recognizedByTotalPEG_of_sca' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pal_recognizedByTotalPEG_of_sca

end PalPeg
