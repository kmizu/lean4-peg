import MacroPeg.CBV.CapturedOriginNormalization
import MacroPeg.CBV.FrontierArgumentCompiler
import MacroPeg.CBV.ProducedScannerCompiler

namespace Shallot.MacroPeg.CBV.CapturedOriginCompiler
open FrontierArgumentCompiler (Selection)
open MixedScannerPairFusion (Entry)
open CapturedOriginQuery (Plan)
open CapturedOriginNormalization (generatedQueries)

def check (g : MGrammar) (ps : Selection) (es : List Entry) (plans : List Plan) : Bool :=
  (FrontierArgumentCompiler.check g ps && CapturedOriginNormalization.check es plans) &&
    ProducedScannerCompiler.sameGrammar (FrontierArgumentCompiler.target g ps) (CapturedOriginNormalization.source es plans)
def rootCheck (ps : Selection) (es : List Entry) (e template : MExp) :=
  MixedGrowthChecks.firstOrderCheck e && MExp.beqE (FrontierArgumentCompiler.render ps e) (GuardedPairSyntax.render es true template)
abbrev target (es : List Entry) (plans : List Plan) := GuardedPairSyntax.seqGrammar es (generatedQueries es plans true)

theorem source_phase (g : MGrammar) (ps : Selection) (es : List Entry) (plans : List Plan) (hc : check g ps es plans=true)
    (e template : MExp) (he : rootCheck ps es e template=true) (x : List Char) (k : Nat) :
    evV g x .callByValuePar (tblV g x .callByValuePar k) [] e x.length=
      evV (CapturedOriginNormalization.prepared es plans) x .callByValuePar
        (tblV (CapturedOriginNormalization.prepared es plans) x .callByValuePar k) [] (GuardedPairSyntax.render es true template) x.length := by
  obtain ⟨hc,hg⟩ := Bool.and_eq_true_iff.mp hc
  obtain ⟨ha,hp⟩ := Bool.and_eq_true_iff.mp hc
  have hgram := ProducedScannerCompiler.sameGrammar_eq _ _ hg
  have hroot := (MExp.beqE_iff _ _).mp (Bool.and_eq_true_iff.mp he).2
  have hf := FrontierArgumentCompiler.physical g ps ha x k [] e x.length (Nat.le_refl _)
  rw [hgram,hroot] at hf
  exact hf.trans (CapturedOriginNormalization.physical es plans hp x k [] template x.length (Nat.le_refl _))

theorem bounds (g : MGrammar) (ps : Selection) (es : List Entry) (plans : List Plan) (hc : check g ps es plans=true)
    (e template : MExp) (he : rootCheck ps es e template=true) (x : List Char) (k : Nat) :
    RLe (evV g x .callByValuePar (tblV g x .callByValuePar k) [] e x.length)
      (evV (target es plans) x .callByValueSeq (tblV (target es plans) x .callByValueSeq (2*k)) [] (GuardedPairSyntax.render es false template) x.length) ∧
    RLe (evV (target es plans) x .callByValueSeq (tblV (target es plans) x .callByValueSeq k) [] (GuardedPairSyntax.render es false template) x.length)
      (evV g x .callByValuePar (tblV g x .callByValuePar k) [] e x.length) := by
  have hq := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hc).1).2).2
  rw [source_phase g ps es plans hc e template he x k]
  exact ⟨GuardedPairSimulation.forward_evaluator es (generatedQueries es plans true) x _ _ (tblV_ok _ _ _ k)
      (GuardedPairCorrespondence.forward_rows es _ hq x k) template [] x.length (Nat.le_refl _),
    GuardedPairSimulation.backward_evaluator es (generatedQueries es plans true) x _ _ (tblV_ok _ _ _ k)
      (GuardedPairCorrespondence.backward_rows es _ hq x k) template [] x.length (Nat.le_refl _)⟩

theorem observations_iff (g : MGrammar) (ps : Selection) (es : List Entry) (plans : List Plan) (hc : check g ps es plans=true)
    (e template : MExp) (he : rootCheck ps es e template=true) (x : List Char) (rest : Option (List Char)) :
    SObs g .callByValuePar e x rest ↔ SObs (target es plans) .callByValueSeq (GuardedPairSyntax.render es false template) x rest := by
  obtain ⟨hc,hg⟩ := Bool.and_eq_true_iff.mp hc
  obtain ⟨ha,hp⟩ := Bool.and_eq_true_iff.mp hc
  obtain ⟨hf,hr⟩ := Bool.and_eq_true_iff.mp he
  have hgram := ProducedScannerCompiler.sameGrammar_eq _ _ hg
  have hroot := (MExp.beqE_iff _ _).mp hr
  have h := FrontierArgumentCompiler.observations_iff g ps ha e (MixedGrowthChecks.firstOrder_checked e hf) x rest
  rw [hgram,hroot] at h
  exact h.trans ((CapturedOriginNormalization.observations_iff es plans hp template x rest).trans
    (GuardedPairCorrespondence.observations_iff es (generatedQueries es plans true) (Bool.and_eq_true_iff.mp hp).2 template x rest))

theorem undefined_iff (g : MGrammar) (ps : Selection) (es : List Entry) (plans : List Plan) (hc : check g ps es plans=true)
    (e template : MExp) (he : rootCheck ps es e template=true) (x : List Char) :
    (∀ k, evV g x .callByValuePar (tblV g x .callByValuePar k) [] e x.length=none) ↔
      ∀ k, evV (target es plans) x .callByValueSeq (tblV (target es plans) x .callByValueSeq k) []
        (GuardedPairSyntax.render es false template) x.length=none :=
  BoundedBodyRewrite.undefined_of_observations _ _
    (FrontierArgumentCompiler.source_firstOrder g ps (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hc).1).1)
    (GuardedPairSyntax.seq_firstOrder _ _) _ _ (by decide) (by decide) _ _
    (MixedGrowthChecks.firstOrder_checked e (Bool.and_eq_true_iff.mp he).1) (GuardedPairSyntax.render_firstOrder _ _ _) x
    (fun rest => observations_iff g ps es plans hc e template he x rest)

theorem language_translation (g : MGrammar) (ps : Selection) (es : List Entry) (plans : List Plan) (hc : check g ps es plans=true)
    (e template : MExp) (he : rootCheck ps es e template=true) :
    ∃ (out : MGrammar) (start : MExp), out.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
      SObs g .callByValuePar e x (some []) ↔ SObs out .callByValueSeq start x (some []) :=
  ⟨target es plans,GuardedPairSyntax.render es false template,GuardedPairSyntax.seq_firstOrder _ _,
    GuardedPairSyntax.render_firstOrder _ _ _,fun x => observations_iff g ps es plans hc e template he x (some [])⟩

end Shallot.MacroPeg.CBV.CapturedOriginCompiler
