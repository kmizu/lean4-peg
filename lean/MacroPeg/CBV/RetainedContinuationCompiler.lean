import MacroPeg.CBV.RetainedContinuationAlgebra

namespace Shallot.MacroPeg.CBV.RetainedContinuationCompiler
open RetainedContinuationSyntax
open TypedFieldSyntax (Header)

def target (parts : List Header) (specs : List Spec) : MGrammar :=
  FieldPlanCompiler.target (normalizedParts parts specs) (normalizedSpecs parts specs)
def targetStart (parts : List Header) (specs : List Spec) (root : MExp) : MExp :=
  FieldPlanCompiler.targetStart (normalizedParts parts specs) (normalizedSpecs parts specs) root
def check (g : MGrammar) (start : MExp) (parts : List Header) (specs : List Spec) (root : MExp) : Bool :=
  RetainedContinuationSyntax.check parts specs && MixedGrowthChecks.firstOrderCheck root &&
    FieldPlanCompiler.check (normalized parts specs) root (normalizedParts parts specs) (normalizedSpecs parts specs) root &&
    FiniteSuffixCallCompiler.sameRules g.rules (source parts specs).rules && MExp.beqE start root

theorem checked (g : MGrammar) (start : MExp) (parts : List Header) (specs : List Spec) (root : MExp)
    (hc : check g start parts specs root=true) :
    RetainedContinuationSyntax.check parts specs=true ∧ root.FirstOrder ∧
      FieldPlanCompiler.check (normalized parts specs) root (normalizedParts parts specs) (normalizedSpecs parts specs) root=true ∧
      g=source parts specs ∧ start=root := by
  simp only [check,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨hp,he⟩,ht⟩,hg⟩,hr⟩ := hc
  have hg := FiniteSuffixCallCompiler.sameRules_checked _ _ hg
  refine ⟨hp,MixedGrowthChecks.firstOrder_checked root he,ht,?_,(MExp.beqE_iff _ _).mp hr⟩
  cases g; simp_all

theorem firstOrder (g : MGrammar) (start : MExp) (parts : List Header) (specs : List Spec) (root : MExp)
    (hc : check g start parts specs root=true) :
    g.FirstOrder ∧ start.FirstOrder ∧ (target parts specs).FirstOrder ∧ (targetStart parts specs root).FirstOrder := by
  obtain ⟨hp,he,ht,hg,hr⟩ := checked g start parts specs root hc
  obtain ⟨_,_,hT,hS⟩ := FieldPlanCompiler.firstOrder _ _ _ _ _ ht
  exact ⟨hg.symm ▸ source_firstOrder parts specs hp,hr ▸ he,hT,hS⟩

/-- A consuming suffix executes inside the selected retained environment.
Every generated copy, type/effect condition and source declaration is
checked; all recursive table assumptions have already been discharged. -/
theorem physical (g : MGrammar) (start : MExp) (parts : List Header) (specs : List Spec) (root : MExp)
    (hc : check g start parts specs root=true) (x : List Char) (k : Nat) :
    evV g x .callByValuePar (tblV g x .callByValuePar k) [] start x.length=
      evV (target parts specs) x .callByValueSeq (tblV (target parts specs) x .callByValueSeq k) []
        (targetStart parts specs root) x.length := by
  obtain ⟨hp,he,ht,hg,hr⟩ := checked g start parts specs root hc
  rw [hg,hr]
  exact (RetainedContinuationAlgebra.physical parts specs hp x k [] root x.length).trans
    (FieldPlanCompiler.physical _ _ _ _ _ ht x k)

theorem observations_iff (g : MGrammar) (start : MExp) (parts : List Header) (specs : List Spec) (root : MExp)
    (hc : check g start parts specs root=true) (x : List Char) (rest : Option (List Char)) :
    SObs g .callByValuePar start x rest ↔ SObs (target parts specs) .callByValueSeq (targetStart parts specs root) x rest := by
  obtain ⟨hg,hs,ht,he⟩ := firstOrder g start parts specs root hc
  rw [←decideObsV_iff hg (by decide) hs,←decideObsV_iff ht (by decide) he]
  unfold decideObsV
  rw [ScannerPairFusion.stable_result_eq _ _ x _ _ _ _ (fun k => physical g start parts specs root hc x k)]

theorem language_translation (g : MGrammar) (start : MExp) (parts : List Header) (specs : List Spec) (root : MExp)
    (hc : check g start parts specs root=true) :
    (fun x => SObs g .callByValuePar start x (some []))=
      (fun x => SObs (target parts specs) .callByValueSeq (targetStart parts specs root) x (some [])) := by
  funext x
  exact propext (observations_iff g start parts specs root hc x (some []))

theorem undefined_iff (g : MGrammar) (start : MExp) (parts : List Header) (specs : List Spec) (root : MExp)
    (hc : check g start parts specs root=true) (x : List Char) :
    (∀ k, evV g x .callByValuePar (tblV g x .callByValuePar k) [] start x.length=none) ↔
      (∀ k, evV (target parts specs) x .callByValueSeq (tblV (target parts specs) x .callByValueSeq k) []
        (targetStart parts specs root) x.length=none) := by
  constructor
  · intro h k; rw [←physical g start parts specs root hc x k]; exact h k
  · intro h k; rw [physical g start parts specs root hc x k]; exact h k

theorem rule_count (parts : List Header) (specs : List Spec) :
    (target parts specs).rules.length=((normalizedParts parts specs).map (fun r => r.parameters.length+1)).sum :=
  FieldPlanCompiler.rule_count _ _

end Shallot.MacroPeg.CBV.RetainedContinuationCompiler
