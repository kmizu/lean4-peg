import MacroPeg.CBV.MutualFieldCorrespondence

namespace Shallot.MacroPeg.CBV.MutualFieldCompiler
open MutualFieldSyntax

def check (g : MGrammar) (start : MExp) (bodies : List MExp) (headers : List Header)
    (d : Char) (root : MExp) : Bool :=
  MutualFieldSyntax.check bodies headers d root &&
    FiniteSuffixCallCompiler.sameRules g.rules (source bodies headers d).rules && MExp.beqE start root

theorem checked (g : MGrammar) (start : MExp) (bodies : List MExp) (headers : List Header)
    (d : Char) (root : MExp) (hc : check g start bodies headers d root=true) :
    Valid bodies headers d ∧ exprCheck bodies.length headers 0 d root=true ∧
      g=source bodies headers d ∧ start=root := by
  obtain ⟨h,hr⟩ := Bool.and_eq_true_iff.mp hc
  obtain ⟨he,hg⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨hv,he⟩ := MutualFieldSyntax.checked _ _ _ _ he
  have hg := FiniteSuffixCallCompiler.sameRules_checked _ _ hg
  refine ⟨hv,he,?_,(MExp.beqE_iff _ _).mp hr⟩
  cases g; simp_all

theorem firstOrder (g : MGrammar) (start : MExp) (bodies : List MExp) (headers : List Header)
    (d : Char) (root : MExp) (hc : check g start bodies headers d root=true) :
    g.FirstOrder ∧ start.FirstOrder ∧ (target bodies headers d).FirstOrder ∧
      (emit bodies.length headers d root).FirstOrder := by
  obtain ⟨hv,he,hg,hr⟩ := checked g start bodies headers d root hc
  rw [hg,hr]
  exact ⟨source_firstOrder_grammar bodies headers d hv,source_firstOrder _ _ _ _ _ he,
    target_firstOrder_grammar bodies headers d hv,emit_firstOrder _ _ _ _⟩

/-- Finite checks of the actual declarations/root yield one fixed Seq
grammar for any finite collection of mutually recursive covering headers. -/
theorem physical (g : MGrammar) (start : MExp) (bodies : List MExp) (headers : List Header)
    (d : Char) (root : MExp) (hc : check g start bodies headers d root=true)
    (x : List Char) (k : Nat) :
    evV g x .callByValuePar (tblV g x .callByValuePar k) [] start x.length=
      evV (target bodies headers d) x .callByValueSeq (tblV (target bodies headers d) x .callByValueSeq k) []
        (emit bodies.length headers d root) x.length := by
  obtain ⟨hv,he,hg,hr⟩ := checked g start bodies headers d root hc
  rw [hg,hr]
  exact MutualFieldCorrespondence.physical bodies headers d hv x k 0 root he []
    (by intro w hw; cases hw) _ (Nat.le_refl _)

theorem observations_iff (g : MGrammar) (start : MExp) (bodies : List MExp) (headers : List Header)
    (d : Char) (root : MExp) (hc : check g start bodies headers d root=true)
    (x : List Char) (rest : Option (List Char)) :
    SObs g .callByValuePar start x rest ↔
      SObs (target bodies headers d) .callByValueSeq (emit bodies.length headers d root) x rest := by
  obtain ⟨hg,hs,ht,he⟩ := firstOrder g start bodies headers d root hc
  rw [←decideObsV_iff hg (by decide) hs,←decideObsV_iff ht (by decide) he]
  unfold decideObsV
  rw [ScannerPairFusion.stable_result_eq _ _ x _ _ _ _ (fun k => physical g start bodies headers d root hc x k)]

theorem language_translation (g : MGrammar) (start : MExp) (bodies : List MExp) (headers : List Header)
    (d : Char) (root : MExp) (hc : check g start bodies headers d root=true) :
    (fun x => SObs g .callByValuePar start x (some []))=
      (fun x => SObs (target bodies headers d) .callByValueSeq (emit bodies.length headers d root) x (some [])) := by
  funext x
  exact propext (observations_iff g start bodies headers d root hc x (some []))

theorem undefined_iff (g : MGrammar) (start : MExp) (bodies : List MExp) (headers : List Header)
    (d : Char) (root : MExp) (hc : check g start bodies headers d root=true) (x : List Char) :
    (∀ k, evV g x .callByValuePar (tblV g x .callByValuePar k) [] start x.length=none) ↔
      (∀ k, evV (target bodies headers d) x .callByValueSeq (tblV (target bodies headers d) x .callByValueSeq k) []
        (emit bodies.length headers d root) x.length=none) := by
  constructor
  · intro h k; rw [←physical g start bodies headers d root hc x k]; exact h k
  · intro h k; rw [physical g start bodies headers d root hc x k]; exact h k

end Shallot.MacroPeg.CBV.MutualFieldCompiler
