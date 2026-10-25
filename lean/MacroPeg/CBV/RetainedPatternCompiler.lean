import MacroPeg.CBV.RetainedPatternCorrespondence

namespace Shallot.MacroPeg.CBV.RetainedPatternCompiler
open RetainedPatternSyntax
abbrev Term := RetainedPatternSyntax.Expr

/-- Check the actual complete grammar and root as well as every nested
copy's source capture effects and the complete client dependency graph. -/
def check (g : MGrammar) (start : MExp) (bodies : List MExp) (clients : List Term) (arity : Nat) (alphabet : List Char) (d : Char) (pattern : List Nat) (root : Term) : Bool :=
  RetainedPatternSyntax.check bodies clients arity alphabet d pattern root && FiniteSuffixCallCompiler.sameRules g.rules (source bodies clients arity d pattern).rules &&
    MExp.beqE start (render bodies.length clients.length true root)

theorem checked (g : MGrammar) (start : MExp) (bodies : List MExp) (clients : List Term) (arity : Nat) (alphabet : List Char) (d : Char) (pattern : List Nat) (root : Term)
    (hc : check g start bodies clients arity alphabet d pattern root=true) :
    RetainedPatternSyntax.check bodies clients arity alphabet d pattern root=true ∧ g=source bodies clients arity d pattern ∧ start=render bodies.length clients.length true root := by
  obtain ⟨h,hs⟩ := Bool.and_eq_true_iff.mp hc
  obtain ⟨he,hg⟩ := Bool.and_eq_true_iff.mp h
  have hg := FiniteSuffixCallCompiler.sameRules_checked _ _ hg
  refine ⟨he,?_,(MExp.beqE_iff _ _).mp hs⟩
  cases g
  simp_all

theorem firstOrder (g : MGrammar) (start : MExp) (bodies : List MExp) (clients : List Term) (arity : Nat) (alphabet : List Char) (d : Char) (pattern : List Nat) (root : Term)
    (hc : check g start bodies clients arity alphabet d pattern root=true) :
    g.FirstOrder ∧ start.FirstOrder ∧ (target bodies clients arity d pattern).FirstOrder ∧ (render bodies.length clients.length false root).FirstOrder := by
  obtain ⟨he,hg,hs⟩ := checked g start bodies clients arity alphabet d pattern root hc
  rw [hg,hs]
  have hb := (RetainedPatternSyntax.checked bodies clients arity alphabet d pattern root he).library
  exact ⟨source_firstOrder _ _ _ _ _ hb,render_firstOrder _ _ _ _,target_firstOrder _ _ _ _ _ hb,render_firstOrder _ _ _ _⟩

theorem physical (g : MGrammar) (start : MExp) (bodies : List MExp) (clients : List Term) (arity : Nat) (alphabet : List Char) (d : Char) (pattern : List Nat) (root : Term)
    (hc : check g start bodies clients arity alphabet d pattern root=true) (x : List Char) (k : Nat) :
    evV g x .callByValuePar (tblV g x .callByValuePar k) [] start x.length=
      evV (target bodies clients arity d pattern) x .callByValueSeq (tblV (target bodies clients arity d pattern) x .callByValueSeq k) [] (render bodies.length clients.length false root) x.length := by
  obtain ⟨he,hg,hs⟩ := checked g start bodies clients arity alphabet d pattern root hc
  rw [hg,hs]
  exact RetainedPatternCorrespondence.physical bodies clients arity alphabet d pattern root he x k _ (Nat.le_refl _)

theorem observations_iff (g : MGrammar) (start : MExp) (bodies : List MExp) (clients : List Term) (arity : Nat) (alphabet : List Char) (d : Char) (pattern : List Nat) (root : Term)
    (hc : check g start bodies clients arity alphabet d pattern root=true) (x : List Char) (rest : Option (List Char)) :
    SObs g .callByValuePar start x rest ↔ SObs (target bodies clients arity d pattern) .callByValueSeq (render bodies.length clients.length false root) x rest := by
  obtain ⟨he,hg,hs⟩ := checked g start bodies clients arity alphabet d pattern root hc
  rw [hg,hs]
  exact RetainedPatternCorrespondence.observations_iff bodies clients arity alphabet d pattern root he x rest

theorem language_translation (g : MGrammar) (start : MExp) (bodies : List MExp) (clients : List Term) (arity : Nat) (alphabet : List Char) (d : Char) (pattern : List Nat) (root : Term)
    (hc : check g start bodies clients arity alphabet d pattern root=true) :
    (fun x => SObs g .callByValuePar start x (some []))=
      (fun x => SObs (target bodies clients arity d pattern) .callByValueSeq (render bodies.length clients.length false root) x (some [])) := by
  funext x
  exact propext (observations_iff g start bodies clients arity alphabet d pattern root hc x (some []))

theorem defined_iff (g : MGrammar) (start : MExp) (bodies : List MExp) (clients : List Term) (arity : Nat) (alphabet : List Char) (d : Char) (pattern : List Nat) (root : Term)
    (hc : check g start bodies clients arity alphabet d pattern root=true) (x : List Char) (v : Option Nat) :
    (∃ k, evV g x .callByValuePar (tblV g x .callByValuePar k) [] start x.length=some v) ↔
      ∃ k, evV (target bodies clients arity d pattern) x .callByValueSeq (tblV (target bodies clients arity d pattern) x .callByValueSeq k) [] (render bodies.length clients.length false root) x.length=some v := by
  constructor
  · rintro ⟨k,hk⟩; exact ⟨k,(physical g start bodies clients arity alphabet d pattern root hc x k).symm.trans hk⟩
  · rintro ⟨k,hk⟩; exact ⟨k,(physical g start bodies clients arity alphabet d pattern root hc x k).trans hk⟩

theorem undefined_iff (g : MGrammar) (start : MExp) (bodies : List MExp) (clients : List Term) (arity : Nat) (alphabet : List Char) (d : Char) (pattern : List Nat) (root : Term)
    (hc : check g start bodies clients arity alphabet d pattern root=true) (x : List Char) :
    (∀ k, evV g x .callByValuePar (tblV g x .callByValuePar k) [] start x.length=none) ↔
      ∀ k, evV (target bodies clients arity d pattern) x .callByValueSeq (tblV (target bodies clients arity d pattern) x .callByValueSeq k) [] (render bodies.length clients.length false root) x.length=none := by
  constructor
  · intro h k; rw [←physical g start bodies clients arity alphabet d pattern root hc x k]; exact h k
  · intro h k; rw [physical g start bodies clients arity alphabet d pattern root hc x k]; exact h k

end Shallot.MacroPeg.CBV.RetainedPatternCompiler
