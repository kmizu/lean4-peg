import MacroPeg.CBV.RecursiveCopyCorrespondence

namespace Shallot.MacroPeg.CBV.RecursiveCopyCompiler
open RecursiveCopySyntax
abbrev Term := RecursiveCopySyntax.Expr

/-- Check the actual complete grammar and root as well as every nested
copy's source capture effects and the complete client dependency graph. -/
def check (g : MGrammar) (start : MExp) (clients : List Term) (alphabet : List Char) (d : Char) (root : Term) : Bool :=
  RecursiveCopySyntax.check clients alphabet d root && FiniteSuffixCallCompiler.sameRules g.rules (source clients d).rules &&
    MExp.beqE start (render clients.length true root)

theorem checked (g : MGrammar) (start : MExp) (clients : List Term) (alphabet : List Char) (d : Char) (root : Term)
    (hc : check g start clients alphabet d root=true) :
    RecursiveCopySyntax.check clients alphabet d root=true ∧ g=source clients d ∧ start=render clients.length true root := by
  obtain ⟨h,hs⟩ := Bool.and_eq_true_iff.mp hc
  obtain ⟨he,hg⟩ := Bool.and_eq_true_iff.mp h
  have hg := FiniteSuffixCallCompiler.sameRules_checked _ _ hg
  refine ⟨he,?_,(MExp.beqE_iff _ _).mp hs⟩
  cases g
  simp_all

theorem firstOrder (g : MGrammar) (start : MExp) (clients : List Term) (alphabet : List Char) (d : Char) (root : Term)
    (hc : check g start clients alphabet d root=true) :
    g.FirstOrder ∧ start.FirstOrder ∧ (target clients d).FirstOrder ∧ (render clients.length false root).FirstOrder := by
  obtain ⟨_,hg,hs⟩ := checked g start clients alphabet d root hc
  rw [hg,hs]
  exact ⟨source_firstOrder _ _,render_firstOrder _ _ _,target_firstOrder _ _,render_firstOrder _ _ _⟩

theorem physical (g : MGrammar) (start : MExp) (clients : List Term) (alphabet : List Char) (d : Char) (root : Term)
    (hc : check g start clients alphabet d root=true) (x : List Char) (k : Nat) :
    evV g x .callByValuePar (tblV g x .callByValuePar k) [] start x.length=
      evV (target clients d) x .callByValueSeq (tblV (target clients d) x .callByValueSeq k) [] (render clients.length false root) x.length := by
  obtain ⟨he,hg,hs⟩ := checked g start clients alphabet d root hc
  rw [hg,hs]
  exact RecursiveCopyCorrespondence.physical clients alphabet d root he x k _ (Nat.le_refl _)

theorem observations_iff (g : MGrammar) (start : MExp) (clients : List Term) (alphabet : List Char) (d : Char) (root : Term)
    (hc : check g start clients alphabet d root=true) (x : List Char) (rest : Option (List Char)) :
    SObs g .callByValuePar start x rest ↔ SObs (target clients d) .callByValueSeq (render clients.length false root) x rest := by
  obtain ⟨he,hg,hs⟩ := checked g start clients alphabet d root hc
  rw [hg,hs]
  exact RecursiveCopyCorrespondence.observations_iff clients alphabet d root he x rest

theorem language_translation (g : MGrammar) (start : MExp) (clients : List Term) (alphabet : List Char) (d : Char) (root : Term)
    (hc : check g start clients alphabet d root=true) :
    (fun x => SObs g .callByValuePar start x (some []))=
      (fun x => SObs (target clients d) .callByValueSeq (render clients.length false root) x (some [])) := by
  funext x
  exact propext (observations_iff g start clients alphabet d root hc x (some []))

theorem defined_iff (g : MGrammar) (start : MExp) (clients : List Term) (alphabet : List Char) (d : Char) (root : Term)
    (hc : check g start clients alphabet d root=true) (x : List Char) (v : Option Nat) :
    (∃ k, evV g x .callByValuePar (tblV g x .callByValuePar k) [] start x.length=some v) ↔
      ∃ k, evV (target clients d) x .callByValueSeq (tblV (target clients d) x .callByValueSeq k) [] (render clients.length false root) x.length=some v := by
  constructor
  · rintro ⟨k,hk⟩; exact ⟨k,(physical g start clients alphabet d root hc x k).symm.trans hk⟩
  · rintro ⟨k,hk⟩; exact ⟨k,(physical g start clients alphabet d root hc x k).trans hk⟩

theorem undefined_iff (g : MGrammar) (start : MExp) (clients : List Term) (alphabet : List Char) (d : Char) (root : Term)
    (hc : check g start clients alphabet d root=true) (x : List Char) :
    (∀ k, evV g x .callByValuePar (tblV g x .callByValuePar k) [] start x.length=none) ↔
      ∀ k, evV (target clients d) x .callByValueSeq (tblV (target clients d) x .callByValueSeq k) [] (render clients.length false root) x.length=none := by
  constructor
  · intro h k; rw [←physical g start clients alphabet d root hc x k]; exact h k
  · intro h k; rw [physical g start clients alphabet d root hc x k]; exact h k

end Shallot.MacroPeg.CBV.RecursiveCopyCompiler
