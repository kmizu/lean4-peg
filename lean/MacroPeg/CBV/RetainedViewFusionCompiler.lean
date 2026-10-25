import MacroPeg.CBV.RetainedViewFusionCorrespondence

namespace Shallot.MacroPeg.CBV.RetainedViewFusionCompiler
open RetainedViewFusionSyntax
open SubstringCaptureView (region)

/-- Finite equality of all actual declarations and the complete root.
No helper semantics, output profiles or termination certificates are inputs. -/
def check (g : MGrammar) (root : MExp) (seeds : List (List Char)) (rs : List Spec) (e : Term) : Bool :=
  FiniteSuffixCallCompiler.sameRules g.rules (source (region seeds) rs).rules && MExp.beqE root (original (region seeds) e)

theorem checked (g : MGrammar) (root : MExp) (seeds : List (List Char)) (rs : List Spec) (e : Term)
    (hc : check g root seeds rs e=true) : g=source (region seeds) rs ∧ root=original (region seeds) e := by
  obtain ⟨hg,he⟩ := Bool.and_eq_true_iff.mp hc
  have hg := FiniteSuffixCallCompiler.sameRules_checked _ _ hg
  refine ⟨?_,(MExp.beqE_iff _ _).mp he⟩
  cases g
  simp_all

theorem physical (g : MGrammar) (root : MExp) (seeds : List (List Char)) (rs : List Spec) (e : Term)
    (hc : check g root seeds rs e=true) (x : List Char) (k : Nat) :
    evV g x .callByValuePar (tblV g x .callByValuePar k) [] root x.length=
      evV (target (region seeds) rs) x .callByValueSeq (tblV (target (region seeds) rs) x .callByValueSeq k) [] (RetainedViewFusionCorrespondence.root seeds rs e) x.length := by
  obtain ⟨hg,he⟩ := checked g root seeds rs e hc
  rw [hg,he]
  exact RetainedViewFusionCorrespondence.physical seeds rs e x k

theorem observations_iff (g : MGrammar) (root : MExp) (seeds : List (List Char)) (rs : List Spec) (e : Term)
    (hc : check g root seeds rs e=true) (x : List Char) (rest : Option (List Char)) :
    SObs g .callByValuePar root x rest ↔ SObs (target (region seeds) rs) .callByValueSeq (RetainedViewFusionCorrespondence.root seeds rs e) x rest := by
  obtain ⟨hg,he⟩ := checked g root seeds rs e hc
  rw [hg,he]
  exact RetainedViewFusionCorrespondence.observations_iff seeds rs e x rest

theorem language_translation (g : MGrammar) (root : MExp) (seeds : List (List Char)) (rs : List Spec) (e : Term)
    (hc : check g root seeds rs e=true) :
    (fun x => SObs g .callByValuePar root x (some []))=
      (fun x => SObs (target (region seeds) rs) .callByValueSeq (RetainedViewFusionCorrespondence.root seeds rs e) x (some [])) := by
  funext x
  exact propext (observations_iff g root seeds rs e hc x (some []))

theorem defined_iff (g : MGrammar) (root : MExp) (seeds : List (List Char)) (rs : List Spec) (e : Term)
    (hc : check g root seeds rs e=true) (x : List Char) (v : Option Nat) :
    (∃ k, evV g x .callByValuePar (tblV g x .callByValuePar k) [] root x.length=some v) ↔
      ∃ k, evV (target (region seeds) rs) x .callByValueSeq (tblV (target (region seeds) rs) x .callByValueSeq k) [] (RetainedViewFusionCorrespondence.root seeds rs e) x.length=some v := by
  constructor
  · rintro ⟨k,hk⟩; exact ⟨k,(physical g root seeds rs e hc x k).symm.trans hk⟩
  · rintro ⟨k,hk⟩; exact ⟨k,(physical g root seeds rs e hc x k).trans hk⟩

theorem undefined_iff (g : MGrammar) (root : MExp) (seeds : List (List Char)) (rs : List Spec) (e : Term)
    (hc : check g root seeds rs e=true) (x : List Char) :
    (∀ k, evV g x .callByValuePar (tblV g x .callByValuePar k) [] root x.length=none) ↔
      ∀ k, evV (target (region seeds) rs) x .callByValueSeq (tblV (target (region seeds) rs) x .callByValueSeq k) [] (RetainedViewFusionCorrespondence.root seeds rs e) x.length=none := by
  constructor
  · intro h k; exact (physical g root seeds rs e hc x k).symm.trans (h k)
  · intro h k; exact (physical g root seeds rs e hc x k).trans (h k)

end Shallot.MacroPeg.CBV.RetainedViewFusionCompiler
