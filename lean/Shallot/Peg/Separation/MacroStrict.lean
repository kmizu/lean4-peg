import Shallot.Peg.Separation.TokenInput
import Shallot.Peg.Separation.Main
import MacroPeg.HigherOrder.FirstOrder

namespace Shallot.PegSeparation

open Complexity Shallot.MacroPeg Shallot.MacroPeg.HO Shallot.MacroPeg.KExp

/-- First-order CBN Macro PEG languages, with no bound on parser-parameter arities. -/
def IsFirstOrderMPEL (L : Shallot.Cfg.Language) : Prop :=
  ∃ (g : MGrammar) (e : MExp), g.FirstOrder ∧ e.FirstOrder ∧
    ∀ x, L x ↔ MacroObs g e x (some [])

theorem embedExp_firstOrder (e : PExp) : (embedExp e).FirstOrder := by
  induction e with
  | eps | any | chr | range | lit | nt => trivial
  | seq a b ha hb | alt a b ha hb => exact ⟨ha, hb⟩
  | star a ha | notP a ha => exact ha

theorem pegToMacroPeg_firstOrder (g : Grammar) : (pegToMacroPeg g).FirstOrder := by
  intro r hr
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp hr
  exact embedExp_firstOrder e

/-- Ordinary PEG observations agree with their zero-parameter Macro PEG embedding. -/
theorem peg_macro_accepts (g : Grammar) (x : List Char) :
    (∃ t, Derives g (.nt g.start) x (.ok t [])) ↔
      MacroObs (pegToMacroPeg g) (embedExp (.nt g.start)) x (some []) := by
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨_, peg_embed_complete ht, rfl⟩
  · rintro ⟨o, ho, hr⟩
    obtain ⟨o', he, hd⟩ := peg_embed_sound ho (.nt g.start) rfl
    rw [he] at hr
    cases o' with
    | fail => cases hr
    | ok t rest =>
      have hrest : rest = [] := Option.some.inj hr
      subst rest
      exact ⟨t, hd⟩

/-- Every ordinary PEG language is a first-order CBN Macro PEG language. -/
theorem pel_subset_firstOrder {L : Shallot.Cfg.Language} (h : Shallot.Cfg.IsPEL L) : IsFirstOrderMPEL L := by
  obtain ⟨g, hg⟩ := h
  exact ⟨pegToMacroPeg g, embedExp (.nt g.start), pegToMacroPeg_firstOrder g,
    embedExp_firstOrder _, fun x => (hg x).trans (peg_macro_accepts g x)⟩

/-- A fixed, arity-correct first-order grammar whose token-coded language is outside P. -/
theorem firstOrder_witness :
    ∃ (g : MGrammar) (e : MExp), g.FirstOrder ∧ e.FirstOrder ∧
      g.arityOk = true ∧ MExp.arityOk g e = true ∧ ¬ KEXP 0 (FirstLanguage g e) := by
  obtain ⟨L, hL, hnot⟩ := kexp_strict 0
  obtain ⟨g, e, hg, he, hga, hea, hred⟩ := first_order_hard hL
  exact ⟨g, e, hg, he, hga, hea, fun hP => hnot (p_reduces hP hred)⟩

/-- The fixed witness is not recognized by any ordinary PEG on character strings. -/
theorem firstOrder_non_PEL :
    ∃ L : Shallot.Cfg.Language, IsFirstOrderMPEL L ∧ ¬ Shallot.Cfg.IsPEL L := by
  obtain ⟨g, e, hg, he, _, _, hnot⟩ := firstOrder_witness
  let L : Shallot.Cfg.Language := fun x => MacroObs g e x (some [])
  refine ⟨L, ⟨g, e, hg, he, fun _ => Iff.rfl⟩, ?_⟩
  rintro ⟨p, hp⟩
  apply hnot
  have hP := tokenLanguage_in_P p
  obtain ⟨k, M, T, c, d, hT, hdec, htime⟩ := hP
  refine ⟨k, M, T, c, d, hT, ?_, htime⟩
  intro w
  obtain ⟨t, ht, hx⟩ := hdec w
  exact ⟨t, ht, hx.trans (hp (tokenWord w)).symm⟩

/-- **Ordinary PEG languages are strictly contained in first-order CBN Macro PEG languages.** -/
theorem pel_strict_in_firstOrder :
    (∀ L, Shallot.Cfg.IsPEL L → IsFirstOrderMPEL L) ∧
    ∃ L, IsFirstOrderMPEL L ∧ ¬ Shallot.Cfg.IsPEL L :=
  ⟨fun _ => pel_subset_firstOrder, firstOrder_non_PEL⟩

end Shallot.PegSeparation
