import Complexity.SpaceLinear
import MacroPeg.CBV.SequentialPackedBinaryInputMachine
import Shallot.Peg.Separation.CBVSeqSpace

/-! The complete packed recognizer improves Seq's standard-input space bound.
The implications below retain their explicit unproved complexity hypotheses. -/
namespace Shallot.PegSeparation
open Complexity Shallot.MacroPeg

theorem binary_seq_in_linear_space {L : Lang}
    (h : IsFirstOrderBinaryCBVPEL .callByValueSeq L) : SpaceLinear L := by
  obtain ⟨g,e,hg,he,hLang⟩ := h
  obtain ⟨M,hdec,hspace⟩ := CBV.SequentialPackedBinaryInputMachine.machine hg he
  obtain ⟨C,hC⟩ := CBV.SequentialPackedBinaryInputMachine.space_linear_bound g e
  refine ⟨8,M,C,?_,hspace.mono hC⟩
  intro w
  obtain ⟨t,ht,hb⟩ := hdec w
  exact ⟨t,ht,hb.trans (hLang w).symm⟩


theorem binary_seq_in_P_and_linear_space {L : Lang}
    (h : IsFirstOrderBinaryCBVPEL .callByValueSeq L) : KExp.KEXP 0 L ∧ SpaceLinear L :=
  ⟨(binary_par_iff_P L).mp (binary_seq_subset_par h),binary_seq_in_linear_space h⟩

theorem binary_reverse_requires_P_linear_space
    (hReverse : ∀ L, IsFirstOrderBinaryCBVPEL .callByValuePar L → IsFirstOrderBinaryCBVPEL .callByValueSeq L) :
    ∀ L, KExp.KEXP 0 L → SpaceLinear L := by
  intro L hp
  exact binary_seq_in_linear_space (hReverse L ((binary_par_iff_P L).mpr hp))

theorem original_reverse_requires_P_linear_space
    (hReverse : ∀ L, IsFirstOrderCBVPEL .callByValuePar L → IsFirstOrderCBVPEL .callByValueSeq L) :
    ∀ L, KExp.KEXP 0 L → SpaceLinear L := by
  intro L hp
  exact binary_seq_in_linear_space (original_reverse_requires_seq_P hReverse L hp)

/-- A genuine separator follows if a P language outside deterministic linear
space is supplied. The lower-bound hypothesis is not proved by this module. -/
theorem P_outside_linear_space_separates_original {L : Lang}
    (hp : KExp.KEXP 0 L) (hspace : ¬SpaceLinear L) :
    (∀ C, IsFirstOrderCBVPEL .callByValueSeq C → IsFirstOrderCBVPEL .callByValuePar C) ∧
      ∃ C, IsFirstOrderCBVPEL .callByValuePar C ∧ ¬IsFirstOrderCBVPEL .callByValueSeq C := by
  refine ⟨fun _ h => firstOrder_seq_subset_par h,?_⟩
  exact binary_P_witness_separates_original hp (fun hs => hspace (binary_seq_in_linear_space hs))

end Shallot.PegSeparation
