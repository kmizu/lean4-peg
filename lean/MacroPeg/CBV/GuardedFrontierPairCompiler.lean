import MacroPeg.CBV.GuardedPairCorrespondence
import MacroPeg.CBV.FrontierArgumentCompiler
import MacroPeg.CBV.ProducedScannerCompiler

namespace Shallot.MacroPeg.CBV.GuardedFrontierPairCompiler
open FrontierArgumentCompiler (Selection)
open MixedScannerPairFusion (Entry)

def check (g : MGrammar) (ps : Selection) (es : List Entry) (qs : List MExp) : Bool :=
  (FrontierArgumentCompiler.check g ps && GuardedPairSyntax.check es qs) && ProducedScannerCompiler.sameGrammar
    (FrontierArgumentCompiler.target g ps) (GuardedPairSyntax.parGrammar es qs)

def rootCheck (ps : Selection) (es : List Entry) (e template : MExp) : Bool :=
  MixedGrowthChecks.firstOrderCheck e && MExp.beqE (FrontierArgumentCompiler.render ps e) (GuardedPairSyntax.render es true template)

/-- Full original-grammar bounds, including ordered argument preflight:
source k refines to target 2k; target k refines to source k. -/
theorem bounds (g : MGrammar) (ps : Selection) (es : List Entry) (qs : List MExp) (hc : check g ps es qs=true)
    (e template : MExp) (he : rootCheck ps es e template=true) (x : List Char) (k : Nat) :
    RLe (evV g x .callByValuePar (tblV g x .callByValuePar k) [] e x.length)
      (evV (GuardedPairSyntax.seqGrammar es qs) x .callByValueSeq (tblV (GuardedPairSyntax.seqGrammar es qs) x .callByValueSeq (2*k)) []
        (GuardedPairSyntax.render es false template) x.length) ∧
    RLe (evV (GuardedPairSyntax.seqGrammar es qs) x .callByValueSeq (tblV (GuardedPairSyntax.seqGrammar es qs) x .callByValueSeq k) []
        (GuardedPairSyntax.render es false template) x.length)
      (evV g x .callByValuePar (tblV g x .callByValuePar k) [] e x.length) := by
  obtain ⟨hc,hg⟩ := Bool.and_eq_true_iff.mp hc
  obtain ⟨ha,hq⟩ := Bool.and_eq_true_iff.mp hc
  have hgram := ProducedScannerCompiler.sameGrammar_eq _ _ hg
  have hroot := (MExp.beqE_iff _ _).mp (Bool.and_eq_true_iff.mp he).2
  have hphys := FrontierArgumentCompiler.physical g ps ha x k [] e x.length (Nat.le_refl _)
  rw [hgram,hroot] at hphys
  rw [hphys]
  exact ⟨GuardedPairSimulation.forward_evaluator es qs x _ _ (tblV_ok _ _ _ k)
      (GuardedPairCorrespondence.forward_rows es qs hq x k) template [] x.length (Nat.le_refl _),
    GuardedPairSimulation.backward_evaluator es qs x _ _ (tblV_ok _ _ _ k)
      (GuardedPairCorrespondence.backward_rows es qs hq x k) template [] x.length (Nat.le_refl _)⟩

theorem observations_iff (g : MGrammar) (ps : Selection) (es : List Entry) (qs : List MExp) (hc : check g ps es qs=true)
    (e template : MExp) (he : rootCheck ps es e template=true) (x : List Char) (rest : Option (List Char)) :
    SObs g .callByValuePar e x rest ↔ SObs (GuardedPairSyntax.seqGrammar es qs) .callByValueSeq
      (GuardedPairSyntax.render es false template) x rest := by
  obtain ⟨hc,hg⟩ := Bool.and_eq_true_iff.mp hc
  obtain ⟨ha,hq⟩ := Bool.and_eq_true_iff.mp hc
  obtain ⟨hf,hr⟩ := Bool.and_eq_true_iff.mp he
  have hgram := ProducedScannerCompiler.sameGrammar_eq _ _ hg
  have hroot := (MExp.beqE_iff _ _).mp hr
  have h := FrontierArgumentCompiler.observations_iff g ps ha e (MixedGrowthChecks.firstOrder_checked e hf) x rest
  rw [hgram,hroot] at h
  exact h.trans (GuardedPairCorrespondence.observations_iff es qs hq template x rest)

theorem undefined_iff (g : MGrammar) (ps : Selection) (es : List Entry) (qs : List MExp) (hc : check g ps es qs=true)
    (e template : MExp) (he : rootCheck ps es e template=true) (x : List Char) :
    (∀ k, evV g x .callByValuePar (tblV g x .callByValuePar k) [] e x.length=none) ↔
      ∀ k, evV (GuardedPairSyntax.seqGrammar es qs) x .callByValueSeq
        (tblV (GuardedPairSyntax.seqGrammar es qs) x .callByValueSeq k) [] (GuardedPairSyntax.render es false template) x.length=none :=
  BoundedBodyRewrite.undefined_of_observations _ _
    (FrontierArgumentCompiler.source_firstOrder g ps (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hc).1).1)
    (GuardedPairSyntax.seq_firstOrder es qs) _ _ (by decide) (by decide) _ _
    (MixedGrowthChecks.firstOrder_checked e (Bool.and_eq_true_iff.mp he).1) (GuardedPairSyntax.render_firstOrder _ _ _) x
    (fun rest => observations_iff g ps es qs hc e template he x rest)

theorem language_translation (g : MGrammar) (ps : Selection) (es : List Entry) (qs : List MExp) (hc : check g ps es qs=true)
    (e template : MExp) (he : rootCheck ps es e template=true) :
    ∃ (out : MGrammar) (start : MExp), out.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
      SObs g .callByValuePar e x (some []) ↔ SObs out .callByValueSeq start x (some []) :=
  ⟨GuardedPairSyntax.seqGrammar es qs,GuardedPairSyntax.render es false template,GuardedPairSyntax.seq_firstOrder _ _,
    GuardedPairSyntax.render_firstOrder _ _ _,fun x => observations_iff g ps es qs hc e template he x (some [])⟩

end Shallot.MacroPeg.CBV.GuardedFrontierPairCompiler
