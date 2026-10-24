import Complexity.SpaceNLogN
import MacroPeg.CBV.SequentialBinaryInputMachine
import Shallot.Peg.Separation.CBVBinary
import Shallot.Peg.Separation.CBVStrategies

/-! The verified Seq machine gives a language-class upper bound. The following
implications identify a sufficient complexity separation, without assuming it. -/
namespace Shallot.PegSeparation
open Complexity Shallot.MacroPeg

theorem binary_seq_in_nlog_space {L : Lang}
    (h : IsFirstOrderBinaryCBVPEL .callByValueSeq L) : SpaceNLogN L := by
  obtain ⟨g,e,hg,he,hLang⟩ := h
  obtain ⟨M,hdec,hspace⟩ := CBV.SequentialBinaryInputMachine.machine hg he
  obtain ⟨C,hC⟩ := CBV.SequentialBinaryInputMachine.space_nlog_bound g e
  refine ⟨20,M,C,?_,hspace.mono hC⟩
  intro w
  obtain ⟨t,ht,hb⟩ := hdec w
  exact ⟨t,ht,hb.trans (hLang w).symm⟩

/-- Equality of the binary Par/Seq classes would place every P language in
this deterministic space bound. This is a necessary condition, not a converse. -/
theorem binary_reverse_requires_P_nlog_space
    (hReverse : ∀ L, IsFirstOrderBinaryCBVPEL .callByValuePar L →
      IsFirstOrderBinaryCBVPEL .callByValueSeq L) :
    ∀ L, KExp.KEXP 0 L → SpaceNLogN L := by
  intro L hp
  exact binary_seq_in_nlog_space (hReverse L ((binary_par_iff_P L).mpr hp))

/-- A reverse translation on the original character languages has the same
necessary consequence on their ordinary a/b restriction. -/
theorem original_reverse_requires_P_nlog_space
    (hReverse : ∀ L, IsFirstOrderCBVPEL .callByValuePar L → IsFirstOrderCBVPEL .callByValueSeq L) :
    ∀ L, KExp.KEXP 0 L → SpaceNLogN L := by
  intro L hp
  exact binary_seq_in_nlog_space (original_reverse_requires_seq_P hReverse L hp)

/-- A P language outside deterministic n log n space would yield a genuine
separating original character language. The space lower bound is an explicit
hypothesis here, not a theorem supplied by the Seq upper-bound construction. -/
theorem P_outside_nlog_space_separates_original {L : Lang}
    (hp : KExp.KEXP 0 L) (hspace : ¬ SpaceNLogN L) :
    (∀ C, IsFirstOrderCBVPEL .callByValueSeq C → IsFirstOrderCBVPEL .callByValuePar C) ∧
      ∃ C, IsFirstOrderCBVPEL .callByValuePar C ∧ ¬ IsFirstOrderCBVPEL .callByValueSeq C := by
  refine ⟨fun _ h => firstOrder_seq_subset_par h,?_⟩
  exact binary_P_witness_separates_original hp (fun hs => hspace (binary_seq_in_nlog_space hs))

end Shallot.PegSeparation
