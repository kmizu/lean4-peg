import MacroPeg.CBV.Upper
import Shallot.Peg.Separation.MacroStrict
import MacroPeg.CBVtoCBN.Recognition

namespace Shallot.PegSeparation

open Complexity Shallot.MacroPeg Shallot.MacroPeg.HO Shallot.MacroPeg.KExp

/-- First-order Macro PEG recognition under the given call-by-value strategy, on original character strings. -/
def IsFirstOrderCBVPEL (s : Strategy) (L : Shallot.Cfg.Language) : Prop :=
  ∃ (g : MGrammar) (e : MExp), g.FirstOrder ∧ e.FirstOrder ∧
    ∀ x, L x ↔ SObs g s e x (some [])

/-- One fixed CBN grammar recognizes a language that no first-order Par or Seq CBV grammar recognizes.
The common witness is the existing fixed CBN grammar outside machine-based polynomial time. -/
theorem firstOrder_cbn_not_cbv :
    ∃ L : Shallot.Cfg.Language, IsFirstOrderMPEL L ∧
      ¬ IsFirstOrderCBVPEL .callByValuePar L ∧ ¬ IsFirstOrderCBVPEL .callByValueSeq L := by
  obtain ⟨g, e, hg, he, _, _, hnot⟩ := firstOrder_witness
  let L : Shallot.Cfg.Language := fun x => MacroObs g e x (some [])
  have excludes : ∀ s, s ≠ .callByName → ¬ IsFirstOrderCBVPEL s L := by
    intro s hs
    rintro ⟨v, f, hv, hf, hLang⟩
    apply hnot
    have hP := CBV.language_in_P v s f hv hs hf
    obtain ⟨k, M, T, c, d, hT, hdec, htime⟩ := hP
    refine ⟨k, M, T, c, d, hT, ?_, htime⟩
    intro w
    obtain ⟨t, ht, hx⟩ := hdec w
    exact ⟨t, ht, hx.trans (hLang (tokenWord w)).symm⟩
  exact ⟨L, ⟨g, e, hg, he, fun _ => Iff.rfl⟩, excludes _ (by decide), excludes _ (by decide)⟩

/-- Every first-order CBV language is recognized by a fixed first-order CBN grammar
on exactly the same original character strings. -/
theorem firstOrder_cbv_subset_cbn {s : Strategy} (hs : s ≠ .callByName) {L : Shallot.Cfg.Language}
    (h : IsFirstOrderCBVPEL s L) : IsFirstOrderMPEL L := by
  obtain ⟨g, e, hg, he, hLang⟩ := h
  refine ⟨CBVtoCBN.translate g s e, CBVtoCBN.candidateStart,
    CBVtoCBN.translate_firstOrder g s e, CBVtoCBN.candidateStart_firstOrder, ?_⟩
  intro x
  exact (hLang x).trans (CBVtoCBN.translate_recognizes hg hs he x).symm

/-- First-order CBV-Par is strictly contained in first-order CBN. -/
theorem firstOrder_par_strict_cbn :
    (∀ L, IsFirstOrderCBVPEL .callByValuePar L → IsFirstOrderMPEL L) ∧
      ∃ L, IsFirstOrderMPEL L ∧ ¬ IsFirstOrderCBVPEL .callByValuePar L := by
  obtain ⟨L, hL, hp, _⟩ := firstOrder_cbn_not_cbv
  exact ⟨fun _ h => firstOrder_cbv_subset_cbn (by decide) h, L, hL, hp⟩

/-- First-order CBV-Seq is strictly contained in first-order CBN. -/
theorem firstOrder_seq_strict_cbn :
    (∀ L, IsFirstOrderCBVPEL .callByValueSeq L → IsFirstOrderMPEL L) ∧
      ∃ L, IsFirstOrderMPEL L ∧ ¬ IsFirstOrderCBVPEL .callByValueSeq L := by
  obtain ⟨L, hL, _, hs⟩ := firstOrder_cbn_not_cbv
  exact ⟨fun _ h => firstOrder_cbv_subset_cbn (by decide) h, L, hL, hs⟩

/-- Both strict inclusions share one CBN language outside the two CBV classes. -/
theorem firstOrder_cbv_par_seq_strict_cbn :
    (∀ L, IsFirstOrderCBVPEL .callByValuePar L → IsFirstOrderMPEL L) ∧
    (∀ L, IsFirstOrderCBVPEL .callByValueSeq L → IsFirstOrderMPEL L) ∧
      ∃ L, IsFirstOrderMPEL L ∧ ¬ IsFirstOrderCBVPEL .callByValuePar L ∧
        ¬ IsFirstOrderCBVPEL .callByValueSeq L :=
  ⟨firstOrder_par_strict_cbn.1, firstOrder_seq_strict_cbn.1, firstOrder_cbn_not_cbv⟩

end Shallot.PegSeparation
