import MacroPeg.CBV.ControlledPeriodCorrespondence

namespace Shallot.MacroPeg.CBV.ControlledPeriodCompiler
open RetainedPatternSyntax
open CopyPeriodControl (Tail)
open ControlledPeriodSyntax
abbrev Term := RetainedPatternSyntax.Expr

/-- Check the actual complete grammar and root as well as every nested
copy's ControlledPeriodSyntax.source capture effects and the complete client dependency graph. -/
def check (g : MGrammar) (start : MExp) (bodies : List MExp) (clients : List Term) (arity : Nat) (alphabet : List Char) (d : Char) (body : List Nat) (tail : Tail) (required : List Bool) (root : Term) : Bool :=
  ControlledPeriodSyntax.check bodies clients arity alphabet d body tail required root && FiniteSuffixCallCompiler.sameRules g.rules (ControlledPeriodSyntax.source bodies clients arity d body tail).rules &&
    MExp.beqE start (render bodies.length clients.length true root)

theorem checked (g : MGrammar) (start : MExp) (bodies : List MExp) (clients : List Term) (arity : Nat) (alphabet : List Char) (d : Char) (body : List Nat) (tail : Tail) (required : List Bool) (root : Term)
    (hc : check g start bodies clients arity alphabet d body tail required root=true) :
    ControlledPeriodSyntax.check bodies clients arity alphabet d body tail required root=true ∧ g=ControlledPeriodSyntax.source bodies clients arity d body tail ∧ start=render bodies.length clients.length true root := by
  obtain ⟨h,hs⟩ := Bool.and_eq_true_iff.mp hc
  obtain ⟨he,hg⟩ := Bool.and_eq_true_iff.mp h
  have hg := FiniteSuffixCallCompiler.sameRules_checked _ _ hg
  refine ⟨he,?_,(MExp.beqE_iff _ _).mp hs⟩
  cases g
  simp_all

theorem firstOrder (g : MGrammar) (start : MExp) (bodies : List MExp) (clients : List Term) (arity : Nat) (alphabet : List Char) (d : Char) (body : List Nat) (tail : Tail) (required : List Bool) (root : Term)
    (hc : check g start bodies clients arity alphabet d body tail required root=true) :
    g.FirstOrder ∧ start.FirstOrder ∧ (ControlledPeriodSyntax.target bodies clients arity d body tail).FirstOrder ∧ (emit bodies.length clients.length arity d body tail root).FirstOrder := by
  obtain ⟨he,hg,hs⟩ := checked g start bodies clients arity alphabet d body tail required root hc
  rw [hg,hs]
  have hb := (ControlledPeriodSyntax.checked bodies clients arity alphabet d body tail required root he).2.library
  exact ⟨ControlledPeriodSyntax.source_firstOrder _ _ _ _ _ _ hb,render_firstOrder _ _ _ _,ControlledPeriodSyntax.target_firstOrder _ _ _ _ _ _ hb,emit_firstOrder _ _ _ _ _ _ _⟩

theorem physical (g : MGrammar) (start : MExp) (bodies : List MExp) (clients : List Term) (arity : Nat) (alphabet : List Char) (d : Char) (body : List Nat) (tail : Tail) (required : List Bool) (root : Term)
    (hc : check g start bodies clients arity alphabet d body tail required root=true) (x : List Char) (k : Nat) :
    evV g x .callByValuePar (tblV g x .callByValuePar k) [] start x.length=
      evV (ControlledPeriodSyntax.target bodies clients arity d body tail) x .callByValueSeq (tblV (ControlledPeriodSyntax.target bodies clients arity d body tail) x .callByValueSeq k) [] (emit bodies.length clients.length arity d body tail root) x.length := by
  obtain ⟨he,hg,hs⟩ := checked g start bodies clients arity alphabet d body tail required root hc
  rw [hg,hs]
  exact ControlledPeriodCorrespondence.physical bodies clients arity alphabet d body tail required root he x k _ (Nat.le_refl _)

theorem observations_iff (g : MGrammar) (start : MExp) (bodies : List MExp) (clients : List Term) (arity : Nat) (alphabet : List Char) (d : Char) (body : List Nat) (tail : Tail) (required : List Bool) (root : Term)
    (hc : check g start bodies clients arity alphabet d body tail required root=true) (x : List Char) (rest : Option (List Char)) :
    SObs g .callByValuePar start x rest ↔ SObs (ControlledPeriodSyntax.target bodies clients arity d body tail) .callByValueSeq (emit bodies.length clients.length arity d body tail root) x rest := by
  obtain ⟨he,hg,hs⟩ := checked g start bodies clients arity alphabet d body tail required root hc
  rw [hg,hs]
  exact ControlledPeriodCorrespondence.observations_iff bodies clients arity alphabet d body tail required root he x rest

theorem language_translation (g : MGrammar) (start : MExp) (bodies : List MExp) (clients : List Term) (arity : Nat) (alphabet : List Char) (d : Char) (body : List Nat) (tail : Tail) (required : List Bool) (root : Term)
    (hc : check g start bodies clients arity alphabet d body tail required root=true) :
    (fun x => SObs g .callByValuePar start x (some []))=
      (fun x => SObs (ControlledPeriodSyntax.target bodies clients arity d body tail) .callByValueSeq (emit bodies.length clients.length arity d body tail root) x (some [])) := by
  funext x
  exact propext (observations_iff g start bodies clients arity alphabet d body tail required root hc x (some []))

theorem defined_iff (g : MGrammar) (start : MExp) (bodies : List MExp) (clients : List Term) (arity : Nat) (alphabet : List Char) (d : Char) (body : List Nat) (tail : Tail) (required : List Bool) (root : Term)
    (hc : check g start bodies clients arity alphabet d body tail required root=true) (x : List Char) (v : Option Nat) :
    (∃ k, evV g x .callByValuePar (tblV g x .callByValuePar k) [] start x.length=some v) ↔
      ∃ k, evV (ControlledPeriodSyntax.target bodies clients arity d body tail) x .callByValueSeq (tblV (ControlledPeriodSyntax.target bodies clients arity d body tail) x .callByValueSeq k) [] (emit bodies.length clients.length arity d body tail root) x.length=some v := by
  constructor
  · rintro ⟨k,hk⟩; exact ⟨k,(physical g start bodies clients arity alphabet d body tail required root hc x k).symm.trans hk⟩
  · rintro ⟨k,hk⟩; exact ⟨k,(physical g start bodies clients arity alphabet d body tail required root hc x k).trans hk⟩

theorem undefined_iff (g : MGrammar) (start : MExp) (bodies : List MExp) (clients : List Term) (arity : Nat) (alphabet : List Char) (d : Char) (body : List Nat) (tail : Tail) (required : List Bool) (root : Term)
    (hc : check g start bodies clients arity alphabet d body tail required root=true) (x : List Char) :
    (∀ k, evV g x .callByValuePar (tblV g x .callByValuePar k) [] start x.length=none) ↔
      ∀ k, evV (ControlledPeriodSyntax.target bodies clients arity d body tail) x .callByValueSeq (tblV (ControlledPeriodSyntax.target bodies clients arity d body tail) x .callByValueSeq k) [] (emit bodies.length clients.length arity d body tail root) x.length=none := by
  constructor
  · intro h k; rw [←physical g start bodies clients arity alphabet d body tail required root hc x k]; exact h k
  · intro h k; rw [physical g start bodies clients arity alphabet d body tail required root hc x k]; exact h k

end Shallot.MacroPeg.CBV.ControlledPeriodCompiler
