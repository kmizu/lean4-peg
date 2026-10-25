import MacroPeg.CBV.TypedFieldCorrespondence

namespace Shallot.MacroPeg.CBV.TypedFieldCompiler
open TypedFieldSyntax

def check (g : MGrammar) (start : MExp) (headers : List Header) (root : MExp) : Bool :=
  TypedFieldSyntax.check headers root &&
    FiniteSuffixCallCompiler.sameRules g.rules (source headers).rules && MExp.beqE start root

theorem checked (g : MGrammar) (start : MExp) (headers : List Header) (root : MExp)
    (hc : check g start headers root=true) :
    Valid headers ∧ exprCheck headers [] root=true ∧ g=source headers ∧ start=root := by
  obtain ⟨h,hr⟩ := Bool.and_eq_true_iff.mp hc
  obtain ⟨he,hg⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨hv,he⟩ := TypedFieldSyntax.checked headers root he
  have hg := FiniteSuffixCallCompiler.sameRules_checked _ _ hg
  refine ⟨hv,he,?_,(MExp.beqE_iff _ _).mp hr⟩
  cases g; simp_all

theorem firstOrder (g : MGrammar) (start : MExp) (headers : List Header) (root : MExp)
    (hc : check g start headers root=true) :
    g.FirstOrder ∧ start.FirstOrder ∧ (target headers).FirstOrder ∧ (emit headers root).FirstOrder := by
  obtain ⟨hv,he,hg,hr⟩ := checked g start headers root hc
  rw [hg,hr]
  exact ⟨source_firstOrder_grammar headers hv,source_firstOrder headers [] root he,
    target_firstOrder_grammar headers,emit_firstOrder headers root⟩

/-- Only finite syntax/effect checks of the real source declarations are
premises. Both generated grammar and start expression are input-independent. -/
theorem physical (g : MGrammar) (start : MExp) (headers : List Header) (root : MExp)
    (hc : check g start headers root=true) (x : List Char) (k : Nat) :
    evV g x .callByValuePar (tblV g x .callByValuePar k) [] start x.length=
      evV (target headers) x .callByValueSeq (tblV (target headers) x .callByValueSeq k) []
        (emit headers root) x.length := by
  obtain ⟨hv,he,hg,hr⟩ := checked g start headers root hc
  rw [hg,hr]
  exact TypedFieldCorrespondence.physical headers hv x k [] root he [] .nil _ (Nat.le_refl _)

theorem observations_iff (g : MGrammar) (start : MExp) (headers : List Header) (root : MExp)
    (hc : check g start headers root=true) (x : List Char) (rest : Option (List Char)) :
    SObs g .callByValuePar start x rest ↔ SObs (target headers) .callByValueSeq (emit headers root) x rest := by
  obtain ⟨hg,hs,ht,he⟩ := firstOrder g start headers root hc
  rw [←decideObsV_iff hg (by decide) hs,←decideObsV_iff ht (by decide) he]
  unfold decideObsV
  rw [ScannerPairFusion.stable_result_eq _ _ x _ _ _ _ (fun k => physical g start headers root hc x k)]

theorem language_translation (g : MGrammar) (start : MExp) (headers : List Header) (root : MExp)
    (hc : check g start headers root=true) :
    (fun x => SObs g .callByValuePar start x (some []))=
      (fun x => SObs (target headers) .callByValueSeq (emit headers root) x (some [])) := by
  funext x
  exact propext (observations_iff g start headers root hc x (some []))

theorem undefined_iff (g : MGrammar) (start : MExp) (headers : List Header) (root : MExp)
    (hc : check g start headers root=true) (x : List Char) :
    (∀ k, evV g x .callByValuePar (tblV g x .callByValuePar k) [] start x.length=none) ↔
      (∀ k, evV (target headers) x .callByValueSeq (tblV (target headers) x .callByValueSeq k) []
        (emit headers root) x.length=none) := by
  constructor
  · intro h k; rw [←physical g start headers root hc x k]; exact h k
  · intro h k; rw [physical g start headers root hc x k]; exact h k

end Shallot.MacroPeg.CBV.TypedFieldCompiler
