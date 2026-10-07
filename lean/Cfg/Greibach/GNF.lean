import Cfg.Greibach.GNFEps
import Cfg.Greibach.GNFComplete

/-!
# Every context-free grammar has an equivalent one in Greibach's standard form

`stdForm_exists`: for every grammar `g` there is a grammar in Greibach's standard form (`StdForm`: every right
side is a terminal followed by nonterminals, and the start is on no right side) with the same nonempty words.

The grammar is built in four stages:
1. `cleanG` (`Cfg/Greibach/GNFEps.lean`): drop the sides that mention missing nonterminals — same language;
2. `epsG` (`Cfg/Greibach/GNFEps.lean`): remove the empty word — the same nonempty words, `EpsFree`;
3. `unitG` (`Cfg/Greibach/GNFUnit.lean`): remove unit sides — same language, `UnitFree`;
4. `gnfG` (`Cfg/Greibach/GNFMain.lean`, `Cfg/Greibach/GNFComplete.lean`): the left-corner construction
   (old nonterminals, the nonterminals `⟨A/C⟩` of left-corner suffixes, one nonterminal per terminal, and a
   fresh start) — same language, `StdForm`.
-/

namespace Shallot.Cfg

/-- **The Greibach grammar** of `g`. -/
noncomputable def greibachG (g : CFGrammar) : CFGrammar := gnfG (unitG (epsG (cleanG g)))

/-- `greibachG g` is in Greibach's standard form. -/
theorem greibachG_stdForm (g : CFGrammar) : StdForm (greibachG g) :=
  gnfG_stdForm (unitG_refs (epsG_refs (cleanG_refs g)))

/-- `greibachG g` has the nonempty words of `g`. -/
theorem greibachG_language (g : CFGrammar) (w : List Char) (hw : w ≠ []) :
    g.language w ↔ (greibachG g).language w := by
  have hε : EpsFree (unitG (epsG (cleanG g))) := unitG_epsFree (epsG_epsFree _)
  have hR : RefsInRange (unitG (epsG (cleanG g))) := unitG_refs (epsG_refs (cleanG_refs g))
  rw [greibachG, gnfG_language hε (unitG_unitFree _) hR]
  show Gen g g.start w ↔ Gen (unitG (epsG (cleanG g))) g.start w
  rw [gen_unitG_iff, gen_epsG_iff, gen_cleanG_iff]
  exact ⟨fun h => ⟨h, hw⟩, fun h => h.1⟩

/-- **Greibach's standard form**: every context-free grammar has an equivalent grammar in standard form, up
to the empty word. -/
theorem stdForm_exists (g : CFGrammar) :
    ∃ g' : CFGrammar, StdForm g' ∧ ∀ w, w ≠ [] → (g.language w ↔ g'.language w) :=
  ⟨greibachG g, greibachG_stdForm g, greibachG_language g⟩

end Shallot.Cfg
