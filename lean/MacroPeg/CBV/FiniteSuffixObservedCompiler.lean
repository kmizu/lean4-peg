import MacroPeg.CBV.FiniteSuffixObservedCorrespondence

namespace Shallot.MacroPeg.CBV.FiniteSuffixObservedCompiler
open FiniteSuffixObservedSyntax

/-- Finite equality of all actual declarations and the complete root.
No helper semantics, output profiles or termination certificates are inputs. -/
def check (g : MGrammar) (root : MExp) (R : List (List Char)) (rs : List Spec) (e : Term) : Bool :=
  FiniteSuffixCallCompiler.sameRules g.rules (source R rs).rules && MExp.beqE root (original R e)

theorem checked (g : MGrammar) (root : MExp) (R : List (List Char)) (rs : List Spec) (e : Term)
    (hc : check g root R rs e=true) : g=source R rs ∧ root=original R e := by
  obtain ⟨hg,he⟩ := Bool.and_eq_true_iff.mp hc
  have hg := FiniteSuffixCallCompiler.sameRules_checked _ _ hg
  refine ⟨?_,(MExp.beqE_iff _ _).mp he⟩
  cases g
  simp_all

theorem physical (g : MGrammar) (root : MExp) (R : List (List Char)) (rs : List Spec) (e : Term)
    (hc : check g root R rs e=true) (x : List Char) (k : Nat) :
    evV g x .callByValuePar (tblV g x .callByValuePar k) [] root x.length=
      evV (target R rs) x .callByValueSeq (tblV (target R rs) x .callByValueSeq k) [] (emit R rs [] none e) x.length := by
  obtain ⟨hg,he⟩ := checked g root R rs e hc
  rw [hg,he]
  exact (FiniteSuffixObservedCorrespondence.physical R rs x e [] x.length k (Nat.le_refl _)).1.symm

theorem observations_iff (g : MGrammar) (root : MExp) (R : List (List Char)) (rs : List Spec) (e : Term)
    (hc : check g root R rs e=true) (x : List Char) (rest : Option (List Char)) :
    SObs g .callByValuePar root x rest ↔ SObs (target R rs) .callByValueSeq (emit R rs [] none e) x rest := by
  obtain ⟨hg,he⟩ := checked g root R rs e hc
  rw [hg,he]
  exact FiniteSuffixObservedCorrespondence.observations_iff R rs e x rest

theorem language_translation (g : MGrammar) (root : MExp) (R : List (List Char)) (rs : List Spec) (e : Term)
    (hc : check g root R rs e=true) :
    (fun x => SObs g .callByValuePar root x (some []))=
      (fun x => SObs (target R rs) .callByValueSeq (emit R rs [] none e) x (some [])) := by
  funext x
  exact propext (observations_iff g root R rs e hc x (some []))

theorem defined_iff (g : MGrammar) (root : MExp) (R : List (List Char)) (rs : List Spec) (e : Term)
    (hc : check g root R rs e=true) (x : List Char) (v : Option Nat) :
    (∃ k, evV g x .callByValuePar (tblV g x .callByValuePar k) [] root x.length=some v) ↔
      ∃ k, evV (target R rs) x .callByValueSeq (tblV (target R rs) x .callByValueSeq k) [] (emit R rs [] none e) x.length=some v := by
  constructor
  · rintro ⟨k,hk⟩; exact ⟨k,(physical g root R rs e hc x k).symm.trans hk⟩
  · rintro ⟨k,hk⟩; exact ⟨k,(physical g root R rs e hc x k).trans hk⟩

theorem undefined_iff (g : MGrammar) (root : MExp) (R : List (List Char)) (rs : List Spec) (e : Term)
    (hc : check g root R rs e=true) (x : List Char) :
    (∀ k, evV g x .callByValuePar (tblV g x .callByValuePar k) [] root x.length=none) ↔
      ∀ k, evV (target R rs) x .callByValueSeq (tblV (target R rs) x .callByValueSeq k) [] (emit R rs [] none e) x.length=none := by
  constructor
  · intro h k; exact (physical g root R rs e hc x k).symm.trans (h k)
  · intro h k; exact (physical g root R rs e hc x k).trans (h k)

end Shallot.MacroPeg.CBV.FiniteSuffixObservedCompiler
