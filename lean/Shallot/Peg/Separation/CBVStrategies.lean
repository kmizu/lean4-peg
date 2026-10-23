import Shallot.Peg.Separation.CBVStrict
import MacroPeg.CBV.ParSimulation.Recognition

namespace Shallot.PegSeparation

open Shallot.MacroPeg

/-- Every first-order Seq language has one fixed first-order Par grammar
recognizing exactly the same original character strings. -/
theorem firstOrder_seq_subset_par {L : Shallot.Cfg.Language}
    (h : IsFirstOrderCBVPEL .callByValueSeq L) : IsFirstOrderCBVPEL .callByValuePar L := by
  obtain ⟨g, e, hg, he, hLang⟩ := h
  refine ⟨CBV.ParSimulation.translate g e, CBV.ParSimulation.candidateStart,
    CBV.ParSimulation.translate_firstOrder g e, CBV.ParSimulation.candidateStart_firstOrder, ?_⟩
  intro x
  exact (hLang x).trans (CBV.ParSimulation.translate_recognizes hg he x).symm

end Shallot.PegSeparation
