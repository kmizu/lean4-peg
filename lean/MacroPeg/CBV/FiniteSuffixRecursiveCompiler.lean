import MacroPeg.CBV.FiniteSuffixRecursiveCorrespondence

namespace Shallot.MacroPeg.CBV.FiniteSuffixRecursiveCompiler
open FiniteSuffixRecursiveSyntax
open RegularCaptureProduct (Node)
abbrev Spec := FiniteSuffixRecursiveSyntax.Rule
abbrev Term := FiniteSuffixRecursiveSyntax.Expr

/-- All actual declarations and the complete entry expression are compared
with the finite source syntax. No semantic helper condition is an input. -/
def check (g : MGrammar) (root : MExp) (nodes : List Node) (R : List (List Char)) (rs : List Spec) (e : Term) : Bool :=
  FiniteSuffixCallCompiler.nodesCheck nodes && FiniteSuffixCallCompiler.sameRules g.rules (source nodes R rs).rules &&
    MExp.beqE root (render nodes R rs none e)

theorem checked (g : MGrammar) (root : MExp) (nodes : List Node) (R : List (List Char)) (rs : List Spec) (e : Term)
    (hc : check g root nodes R rs e=true) :
    RegularCaptureProduct.Valid nodes ∧ g=source nodes R rs ∧ root=render nodes R rs none e := by
  obtain ⟨h,he⟩ := Bool.and_eq_true_iff.mp hc
  obtain ⟨hn,hg⟩ := Bool.and_eq_true_iff.mp h
  have hg := FiniteSuffixCallCompiler.sameRules_checked _ _ hg
  refine ⟨FiniteSuffixCallCompiler.nodes_checked nodes hn,?_,(MExp.beqE_iff _ _).mp he⟩
  cases g
  simp_all [source]

theorem observations_iff (g : MGrammar) (root : MExp) (nodes : List Node) (R : List (List Char)) (rs : List Spec) (e : Term)
    (hc : check g root nodes R rs e=true) (x : List Char) (rest : Option (List Char)) :
    SObs g .callByValuePar root x rest ↔ SObs (target nodes R rs) .callByValueSeq (render nodes R rs (some []) e) x rest := by
  obtain ⟨hn,hg,he⟩ := checked g root nodes R rs e hc
  rw [hg,he]
  exact FiniteSuffixRecursiveCorrespondence.observations_iff nodes hn R rs e x rest

theorem language_translation (g : MGrammar) (root : MExp) (nodes : List Node) (R : List (List Char)) (rs : List Spec) (e : Term)
    (hc : check g root nodes R rs e=true) :
    (fun x => SObs g .callByValuePar root x (some []))=
      (fun x => SObs (target nodes R rs) .callByValueSeq (render nodes R rs (some []) e) x (some [])) := by
  funext x
  exact propext (observations_iff g root nodes R rs e hc x (some []))

theorem defined_iff (g : MGrammar) (root : MExp) (nodes : List Node) (R : List (List Char)) (rs : List Spec) (e : Term)
    (hc : check g root nodes R rs e=true) (x : List Char) (v : Option Nat) :
    (∃ k, evV g x .callByValuePar (tblV g x .callByValuePar k) [] root x.length=some v) ↔
      ∃ k, evV (target nodes R rs) x .callByValueSeq (tblV (target nodes R rs) x .callByValueSeq k) [] (render nodes R rs (some []) e) x.length=some v := by
  obtain ⟨hn,hg,he⟩ := checked g root nodes R rs e hc
  rw [hg,he]
  exact FiniteSuffixRecursiveCorrespondence.defined_iff nodes hn R rs e x x.length (Nat.le_refl _) v

theorem undefined_iff (g : MGrammar) (root : MExp) (nodes : List Node) (R : List (List Char)) (rs : List Spec) (e : Term)
    (hc : check g root nodes R rs e=true) (x : List Char) :
    (∀ k, evV g x .callByValuePar (tblV g x .callByValuePar k) [] root x.length=none) ↔
      ∀ k, evV (target nodes R rs) x .callByValueSeq (tblV (target nodes R rs) x .callByValueSeq k) [] (render nodes R rs (some []) e) x.length=none := by
  obtain ⟨hn,hg,he⟩ := checked g root nodes R rs e hc
  rw [hg,he]
  exact FiniteSuffixRecursiveCorrespondence.undefined_iff nodes hn R rs e x

end Shallot.MacroPeg.CBV.FiniteSuffixRecursiveCompiler
