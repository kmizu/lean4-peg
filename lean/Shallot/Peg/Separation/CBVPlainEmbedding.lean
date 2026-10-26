import Shallot.Peg.Separation.CBVStrict
import MacroPeg.Properties.Strategy

namespace Shallot.PegSeparation

open Shallot.MacroPeg

theorem embedExp_epsArgs (e : PExp) : EpsArgs (embedExp e) := by
  induction e with
  | eps | any | chr | range | lit => trivial
  | nt => simp [embedExp, EpsArgs]
  | seq a b ha hb | alt a b ha hb => exact ⟨ha, hb⟩
  | star a ha | notP a ha => exact ha

/-- The same fixed zero-arity embedding preserves the whole-input language
under every strategy, including both CBV strategies and partial grammars. -/
theorem peg_cbv_accepts (g : Grammar) (s : Strategy) (x : List Char) :
    (∃ t, Derives g (.nt g.start) x (.ok t [])) ↔
      SObs (pegToMacroPeg g) s (embedExp (.nt g.start)) x (some []) := by
  have hr : ∀ r ∈ (pegToMacroPeg g).rules, EpsArgs r.body := by
    intro r hr
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp hr
    exact embedExp_epsArgs e
  exact (peg_macro_accepts g x).trans
    (strategy_agree_eps hr (embedExp_epsArgs _) .callByName s x (some []))

theorem pel_subset_firstOrder_cbv (s : Strategy) {L : Shallot.Cfg.Language}
    (h : Shallot.Cfg.IsPEL L) : IsFirstOrderCBVPEL s L := by
  obtain ⟨g, hg⟩ := h
  exact ⟨pegToMacroPeg g, embedExp (.nt g.start), pegToMacroPeg_firstOrder g,
    embedExp_firstOrder _, fun x => (hg x).trans (peg_cbv_accepts g s x)⟩

end Shallot.PegSeparation
