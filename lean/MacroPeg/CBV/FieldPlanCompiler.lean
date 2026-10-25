import MacroPeg.CBV.FieldPlanNormalization

namespace Shallot.MacroPeg.CBV.FieldPlanCompiler
open FieldPlanSyntax
open TypedFieldSyntax (Header)
open MixedGrowthChecks (firstOrderCheck firstOrder_checked)

def target (parts : List Header) (specs : List Spec) : MGrammar :=
  TypedFieldSyntax.target (expandedHeaders parts specs)
def targetStart (parts : List Header) (specs : List Spec) (root : MExp) : MExp :=
  TypedFieldSyntax.emit (expandedHeaders parts specs) (render parts specs root)
def check (g : MGrammar) (start : MExp) (parts : List Header) (specs : List Spec) (root : MExp) : Bool :=
  FieldPlanSyntax.check parts specs && firstOrderCheck root &&
    TypedFieldCompiler.check (expanded parts specs) (render parts specs root) (expandedHeaders parts specs) (render parts specs root) &&
    FiniteSuffixCallCompiler.sameRules g.rules (source parts specs).rules && MExp.beqE start root

theorem checked (g : MGrammar) (start : MExp) (parts : List Header) (specs : List Spec) (root : MExp)
    (hc : check g start parts specs root=true) :
    Valid parts specs ∧ root.FirstOrder ∧
      TypedFieldCompiler.check (expanded parts specs) (render parts specs root) (expandedHeaders parts specs) (render parts specs root)=true ∧
      g=source parts specs ∧ start=root := by
  simp only [check,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨hp,he⟩,ht⟩,hg⟩,hr⟩ := hc
  have hg := FiniteSuffixCallCompiler.sameRules_checked _ _ hg
  refine ⟨FieldPlanSyntax.checked parts specs hp,firstOrder_checked root he,ht,?_,(MExp.beqE_iff _ _).mp hr⟩
  cases g; simp_all

theorem firstOrder (g : MGrammar) (start : MExp) (parts : List Header) (specs : List Spec) (root : MExp)
    (hc : check g start parts specs root=true) :
    g.FirstOrder ∧ start.FirstOrder ∧ (target parts specs).FirstOrder ∧ (targetStart parts specs root).FirstOrder := by
  obtain ⟨hv,he,ht,hg,hr⟩ := checked g start parts specs root hc
  rw [hg,hr]
  exact ⟨source_firstOrder parts specs hv,he,TypedFieldSyntax.target_firstOrder_grammar _,TypedFieldSyntax.emit_firstOrder _ _⟩

/-- Caller-side distribution is composed with the typed field compiler.
No original header needs one common leading replay pattern. All premises
are finite checks of actual declarations, control plans and effects. -/
theorem physical (g : MGrammar) (start : MExp) (parts : List Header) (specs : List Spec) (root : MExp)
    (hc : check g start parts specs root=true) (x : List Char) (k : Nat) :
    evV g x .callByValuePar (tblV g x .callByValuePar k) [] start x.length=
      evV (target parts specs) x .callByValueSeq (tblV (target parts specs) x .callByValueSeq k) []
        (targetStart parts specs root) x.length := by
  obtain ⟨hv,he,ht,hg,hr⟩ := checked g start parts specs root hc
  rw [hg,hr]
  exact (FieldPlanNormalization.physical parts specs hv x k root he [] _ (Nat.le_refl _)).trans
    (TypedFieldCompiler.physical _ _ _ _ ht x k)

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
    (target parts specs).rules.length=(parts.map (fun r => r.parameters.length+1)).sum := by
  rw [target,TypedFieldSyntax.rule_count]
  simp only [expandedHeaders,List.map_map]
  rfl

end Shallot.MacroPeg.CBV.FieldPlanCompiler
