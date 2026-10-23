import MacroPeg.CBV.Upper
import Shallot.Peg.Separation.MacroStrict

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

end Shallot.PegSeparation
