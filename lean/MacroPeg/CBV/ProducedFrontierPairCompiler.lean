import MacroPeg.CBV.FrontierArgumentCompiler
import MacroPeg.CBV.ScannedPairFusion
import MacroPeg.CBV.ProducedScannerCompiler

namespace Shallot.MacroPeg.CBV.ProducedFrontierPairCompiler
open FrontierArgumentCompiler (Selection)
open MixedScannerPairFusion (Entry)

def check (g : MGrammar) (ps : Selection) (es : List Entry) : Bool :=
  FrontierArgumentCompiler.check g ps && ProducedScannerCompiler.sameGrammar
    (FrontierArgumentCompiler.target g ps) (ScannedPairFusion.parGrammar es)

def rootCheck (ps : Selection) (es : List Entry) (e template : MExp) : Bool :=
  MixedGrowthChecks.firstOrderCheck e && MExp.beqE (FrontierArgumentCompiler.render ps e)
    (MixedScannerPairFusion.render es true template)

theorem observations_iff (g : MGrammar) (ps : Selection) (es : List Entry) (hc : check g ps es=true)
    (e template : MExp) (he : rootCheck ps es e template=true) (x : List Char) (rest : Option (List Char)) :
    SObs g .callByValuePar e x rest ↔ SObs (MixedScannerPairFusion.seqGrammar es) .callByValueSeq
      (MixedScannerPairFusion.render es false template) x rest := by
  obtain ⟨hg,hout⟩ := Bool.and_eq_true_iff.mp hc
  obtain ⟨hf,hr⟩ := Bool.and_eq_true_iff.mp he
  have hgram := ProducedScannerCompiler.sameGrammar_eq _ _ hout
  have hroot := (MExp.beqE_iff _ _).mp hr
  have h := FrontierArgumentCompiler.observations_iff g ps hg e (MixedGrowthChecks.firstOrder_checked e hf) x rest
  rw [hgram,hroot] at h
  exact h.trans (ScannedPairFusion.observations_iff es template x rest)

theorem undefined_iff (g : MGrammar) (ps : Selection) (es : List Entry) (hc : check g ps es=true)
    (e template : MExp) (he : rootCheck ps es e template=true) (x : List Char) :
    (∀ k, evV g x .callByValuePar (tblV g x .callByValuePar k) [] e x.length=none) ↔
      ∀ k, evV (MixedScannerPairFusion.seqGrammar es) x .callByValueSeq
        (tblV (MixedScannerPairFusion.seqGrammar es) x .callByValueSeq k) []
        (MixedScannerPairFusion.render es false template) x.length=none :=
  BoundedBodyRewrite.undefined_of_observations _ _
    (FrontierArgumentCompiler.source_firstOrder g ps (Bool.and_eq_true_iff.mp hc).1)
    (MixedScannerPairFusion.seq_firstOrder es) _ _ (by decide) (by decide) _ _
    (MixedGrowthChecks.firstOrder_checked e (Bool.and_eq_true_iff.mp he).1)
    (MixedScannerPairFusion.render_firstOrder es false template) x
    (fun rest => observations_iff g ps es hc e template he x rest)

theorem language_translation (g : MGrammar) (ps : Selection) (es : List Entry) (hc : check g ps es=true)
    (e template : MExp) (he : rootCheck ps es e template=true) :
    ∃ (out : MGrammar) (start : MExp), out.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
      SObs g .callByValuePar e x (some []) ↔ SObs out .callByValueSeq start x (some []) :=
  ⟨MixedScannerPairFusion.seqGrammar es,MixedScannerPairFusion.render es false template,
    MixedScannerPairFusion.seq_firstOrder es,MixedScannerPairFusion.render_firstOrder _ _ _,
    fun x => observations_iff g ps es hc e template he x (some [])⟩

end Shallot.MacroPeg.CBV.ProducedFrontierPairCompiler
