import MacroPeg.CBV.ProducedScannerCompiler
import MacroPeg.CBV.PrefixFamilyFusion

namespace Shallot.MacroPeg.CBV.ProducedPrefixFamilyCompiler
open SelectedProducerNormalization (Selection)

/-- Selected producers preserve all source values, using the last actual
argument to recover the source prefix endpoint. The prefix-family backend
then captures consecutive chunks and reconstructs the original tuple. -/
def check (g : MGrammar) (ps : Selection) (rules : List MRule) : Bool :=
  SelectedProducerNormalization.check g ps && ProducedScannerCompiler.sameGrammar
    (SelectedProducerNormalization.target g ps) (PrefixFamilyFusion.parGrammar rules)

def rootCheck (ps : Selection) (e : MExp) : Bool :=
  SelectedProducerNormalization.conforms ps (PrefixFamilyFusion.render true 0 e)

theorem checked (g : MGrammar) (ps : Selection) (rules : List MRule) (hc : check g ps rules=true) :
    SelectedProducerNormalization.check g ps=true ∧
      SelectedProducerNormalization.target g ps=PrefixFamilyFusion.parGrammar rules :=
  ⟨(Bool.and_eq_true_iff.mp hc).1,ProducedScannerCompiler.sameGrammar_eq _ _ (Bool.and_eq_true_iff.mp hc).2⟩

theorem observations_iff (g : MGrammar) (ps : Selection) (rules : List MRule) (hc : check g ps rules=true)
    (e : MExp) (he : rootCheck ps e=true) (x : List Char) (rest : Option (List Char)) :
    SObs g .callByValuePar (PrefixFamilyFusion.render true 0 e) x rest ↔
      SObs (PrefixFamilyFusion.seqGrammar rules) .callByValueSeq (PrefixFamilyFusion.render false 0 e) x rest := by
  have h := checked g ps rules hc
  have hs := SelectedProducerCorrespondence.observations_iff g ps h.1 _
    (PrefixFamilyFusion.render_firstOrder true 0 e) he x rest
  rw [h.2] at hs
  exact hs.trans (PrefixFamilyFusion.observations_iff rules e x rest)

theorem defined_iff (g : MGrammar) (ps : Selection) (rules : List MRule) (hc : check g ps rules=true)
    (e : MExp) (he : rootCheck ps e=true) (x : List Char) (v : Option Nat) :
    (∃ k, evV g x .callByValuePar (tblV g x .callByValuePar k) [] (PrefixFamilyFusion.render true 0 e) x.length=some v) ↔
      ∃ k, evV (PrefixFamilyFusion.seqGrammar rules) x .callByValueSeq
        (tblV (PrefixFamilyFusion.seqGrammar rules) x .callByValueSeq k) [] (PrefixFamilyFusion.render false 0 e) x.length=some v := by
  have h := checked g ps rules hc
  have hs := SelectedProducerCorrespondence.defined_iff g ps h.1 x [] _
    (PrefixFamilyFusion.render_firstOrder true 0 e) he x.length (Nat.le_refl _) v
  dsimp only [SelectedProducerCorrespondence.sourceTable,SelectedProducerCorrespondence.targetTable] at hs
  rw [h.2] at hs
  refine hs.trans (exists_congr (fun k => ?_))
  have hk := PrefixFamilyFusion.evaluator_eq rules x k [] e x.length (Nat.le_refl _)
  simp only [PrefixFamilyFusion.words,List.length_nil] at hk
  rw [hk]

theorem undefined_iff (g : MGrammar) (ps : Selection) (rules : List MRule) (hc : check g ps rules=true)
    (e : MExp) (he : rootCheck ps e=true) (x : List Char) :
    (∀ k, evV g x .callByValuePar (tblV g x .callByValuePar k) [] (PrefixFamilyFusion.render true 0 e) x.length=none) ↔
      (∀ k, evV (PrefixFamilyFusion.seqGrammar rules) x .callByValueSeq
        (tblV (PrefixFamilyFusion.seqGrammar rules) x .callByValueSeq k) [] (PrefixFamilyFusion.render false 0 e) x.length=none) :=
  BoundedBodyRewrite.undefined_of_observations _ _ (SelectedProducerNormalization.source_firstOrder g ps (checked g ps rules hc).1)
    (PrefixFamilyFusion.seq_firstOrder rules) .callByValuePar .callByValueSeq (by decide) (by decide) _ _
    (PrefixFamilyFusion.render_firstOrder true 0 e) (PrefixFamilyFusion.render_firstOrder false 0 e) x
    (fun rest => observations_iff g ps rules hc e he x rest)

theorem language_translation (g : MGrammar) (ps : Selection) (rules : List MRule) (hc : check g ps rules=true)
    (e : MExp) (he : rootCheck ps e=true) :
    ∃ (out : MGrammar) (root : MExp), out.FirstOrder ∧ root.FirstOrder ∧
      ∀ x, SObs g .callByValuePar (PrefixFamilyFusion.render true 0 e) x (some []) ↔
        SObs out .callByValueSeq root x (some []) :=
  ⟨PrefixFamilyFusion.seqGrammar rules,PrefixFamilyFusion.render false 0 e,PrefixFamilyFusion.seq_firstOrder rules,
    PrefixFamilyFusion.render_firstOrder false 0 e,fun x => observations_iff g ps rules hc e he x (some [])⟩

end Shallot.MacroPeg.CBV.ProducedPrefixFamilyCompiler
