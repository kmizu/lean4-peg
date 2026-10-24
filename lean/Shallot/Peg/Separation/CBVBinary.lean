import MacroPeg.CBV.BitWordMachine
import Shallot.Peg.Separation.CBVParLower

namespace Shallot.PegSeparation

open Shallot.MacroPeg

/-- Recognition on the usual a/b alphabet, with one original character per
bit. This is a language class; the grammar is fixed for the entire language. -/
def IsFirstOrderBinaryCBVPEL (s : Strategy) (L : Complexity.Lang) : Prop :=
  ∃ (g : MGrammar) (e : MExp), g.FirstOrder ∧ e.FirstOrder ∧
    ∀ w, L w ↔ SObs g s e (bitWord w) (some [])

theorem binary_cbv_in_P {s : Strategy} (hs : s ≠ .callByName) {L : Complexity.Lang}
    (h : IsFirstOrderBinaryCBVPEL s L) : KExp.KEXP 0 L := by
  obtain ⟨g, e, hg, he, hLang⟩ := h
  obtain ⟨k, M, T, c, d, hT, hdec, htime⟩ := CBV.bitWordLanguage_in_P g s e hg hs he
  refine ⟨k, M, T, c, d, hT, ?_, htime⟩
  intro w
  obtain ⟨t, ht, hb⟩ := hdec w
  exact ⟨t, ht, hb.trans (hLang w).symm⟩

/-- First-order Par recognizes exactly P on the ordinary binary alphabet.
The lower and upper bounds use the same original words, including empty. -/
theorem binary_par_iff_P (L : Complexity.Lang) :
    IsFirstOrderBinaryCBVPEL .callByValuePar L ↔ KExp.KEXP 0 L :=
  ⟨binary_cbv_in_P (by decide), firstOrder_par_contains_P⟩

theorem binary_seq_subset_par {L : Complexity.Lang}
    (h : IsFirstOrderBinaryCBVPEL .callByValueSeq L) : IsFirstOrderBinaryCBVPEL .callByValuePar L :=
  (binary_par_iff_P L).mpr (binary_cbv_in_P (by decide) h)

/-- On a/b words the open reverse inclusion is exactly the question whether
Seq recognizes every P language. This equivalence does not assert either. -/
theorem binary_reverse_iff_seq_covers_P :
    (∀ L, IsFirstOrderBinaryCBVPEL .callByValuePar L → IsFirstOrderBinaryCBVPEL .callByValueSeq L) ↔
      (∀ L, KExp.KEXP 0 L → IsFirstOrderBinaryCBVPEL .callByValueSeq L) := by
  constructor
  · intro h L hp; exact h L ((binary_par_iff_P L).mpr hp)
  · intro h L hp; exact h L ((binary_par_iff_P L).mp hp)

/-- A general reverse translation on original character languages would in
particular establish that Seq covers all P languages on ordinary a/b words. -/
theorem original_reverse_requires_seq_P
    (hReverse : ∀ L, IsFirstOrderCBVPEL .callByValuePar L → IsFirstOrderCBVPEL .callByValueSeq L) :
    ∀ L, KExp.KEXP 0 L → IsFirstOrderBinaryCBVPEL .callByValueSeq L := by
  intro L hp
  obtain ⟨g, e, hg, he, hLang⟩ := hReverse _ (firstOrder_par_contains_P_projection hp)
  refine ⟨g, e, hg, he, ?_⟩
  intro w
  simpa only [inputBits_bitWord] using hLang (bitWord w)

/-- Any P language outside the entire Seq class on a/b words yields a true
separation of the original character-language classes, without padding. -/
theorem binary_P_witness_separates_original
    {L : Complexity.Lang} (hp : KExp.KEXP 0 L)
    (hn : ¬ IsFirstOrderBinaryCBVPEL .callByValueSeq L) :
    ∃ C, IsFirstOrderCBVPEL .callByValuePar C ∧ ¬ IsFirstOrderCBVPEL .callByValueSeq C := by
  refine ⟨fun x => L (CBV.ParTableau.inputBits x), firstOrder_par_contains_P_projection hp, ?_⟩
  rintro ⟨g, e, hg, he, hLang⟩
  apply hn
  refine ⟨g, e, hg, he, ?_⟩
  intro w
  simpa only [inputBits_bitWord] using hLang (bitWord w)

end Shallot.PegSeparation
