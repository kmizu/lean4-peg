import MacroPeg.CBV.RecursiveFieldCorrespondence

namespace Shallot.MacroPeg.CBV.RecursiveFieldCompiler
open RecursiveFieldSyntax

def check (g : MGrammar) (start : MExp) (bodies : List MExp) (arity : Nat) (d : Char)
    (js : List Nat) (body root : MExp) : Bool :=
  RecursiveFieldSyntax.check bodies arity d js body root &&
    FiniteSuffixCallCompiler.sameRules g.rules (source bodies arity d js body).rules && MExp.beqE start root

theorem checked (g : MGrammar) (start : MExp) (bodies : List MExp) (arity : Nat) (d : Char)
    (js : List Nat) (body root : MExp) (hc : check g start bodies arity d js body root=true) :
    RecursiveFieldSyntax.Checked bodies arity d js body root ∧ g=source bodies arity d js body ∧ start=root := by
  obtain ⟨h,hr⟩ := Bool.and_eq_true_iff.mp hc
  obtain ⟨he,hg⟩ := Bool.and_eq_true_iff.mp h
  have hg := FiniteSuffixCallCompiler.sameRules_checked _ _ hg
  refine ⟨RecursiveFieldSyntax.checked _ _ _ _ _ _ he,?_,(MExp.beqE_iff _ _).mp hr⟩
  cases g; simp_all

theorem firstOrder (g : MGrammar) (start : MExp) (bodies : List MExp) (arity : Nat) (d : Char)
    (js : List Nat) (body root : MExp) (hc : check g start bodies arity d js body root=true) :
    g.FirstOrder ∧ start.FirstOrder ∧ (target bodies arity d js body).FirstOrder ∧
      (emit bodies.length arity d js root).FirstOrder := by
  obtain ⟨h,hg,hr⟩ := checked g start bodies arity d js body root hc
  rw [hg,hr]
  exact ⟨TupleFieldCompiler.source_firstOrder _ _ _ _ _ h.library
      (RecursiveFieldSyntax.source_firstOrder _ _ _ _ _ h.body),
    RecursiveFieldSyntax.source_firstOrder _ _ _ _ _ h.root,
    TupleFieldCompiler.target_firstOrder _ _ _ _ _ h.library (emit_firstOrder _ _ _ _ _),
    emit_firstOrder _ _ _ _ _⟩

/-- Every recursive call is checked against the actual declaration and root.
Fresh actual captures and recursion are handled by the physical table induction. -/
theorem physical (g : MGrammar) (start : MExp) (bodies : List MExp) (arity : Nat) (d : Char)
    (js : List Nat) (body root : MExp) (hc : check g start bodies arity d js body root=true)
    (x : List Char) (k : Nat) :
    evV g x .callByValuePar (tblV g x .callByValuePar k) [] start x.length=
      evV (target bodies arity d js body) x .callByValueSeq
        (tblV (target bodies arity d js body) x .callByValueSeq k) [] (emit bodies.length arity d js root) x.length := by
  obtain ⟨h,hg,hr⟩ := checked g start bodies arity d js body root hc
  rw [hg,hr]
  cases js with
  | nil => exact False.elim (h.nonempty rfl)
  | cons j js =>
    exact RecursiveFieldCorrespondence.physical bodies arity d j js body h.library h.positive h.scope h.cover h.body x k
      0 root h.root [] (by intro w hw; cases hw) _ (Nat.le_refl _)

theorem observations_iff (g : MGrammar) (start : MExp) (bodies : List MExp) (arity : Nat) (d : Char)
    (js : List Nat) (body root : MExp) (hc : check g start bodies arity d js body root=true)
    (x : List Char) (rest : Option (List Char)) :
    SObs g .callByValuePar start x rest ↔ SObs (target bodies arity d js body) .callByValueSeq
      (emit bodies.length arity d js root) x rest := by
  obtain ⟨hg,hs,ht,he⟩ := firstOrder g start bodies arity d js body root hc
  rw [←decideObsV_iff hg (by decide) hs,←decideObsV_iff ht (by decide) he]
  unfold decideObsV
  rw [ScannerPairFusion.stable_result_eq _ _ x _ _ _ _ (fun k => physical g start bodies arity d js body root hc x k)]

theorem language_translation (g : MGrammar) (start : MExp) (bodies : List MExp) (arity : Nat) (d : Char)
    (js : List Nat) (body root : MExp) (hc : check g start bodies arity d js body root=true) :
    (fun x => SObs g .callByValuePar start x (some []))=
      (fun x => SObs (target bodies arity d js body) .callByValueSeq (emit bodies.length arity d js root) x (some [])) := by
  funext x
  exact propext (observations_iff g start bodies arity d js body root hc x (some []))

theorem undefined_iff (g : MGrammar) (start : MExp) (bodies : List MExp) (arity : Nat) (d : Char)
    (js : List Nat) (body root : MExp) (hc : check g start bodies arity d js body root=true) (x : List Char) :
    (∀ k, evV g x .callByValuePar (tblV g x .callByValuePar k) [] start x.length=none) ↔
      (∀ k, evV (target bodies arity d js body) x .callByValueSeq
        (tblV (target bodies arity d js body) x .callByValueSeq k) [] (emit bodies.length arity d js root) x.length=none) := by
  constructor
  · intro h k; rw [←physical g start bodies arity d js body root hc x k]; exact h k
  · intro h k; rw [physical g start bodies arity d js body root hc x k]; exact h k

end Shallot.MacroPeg.CBV.RecursiveFieldCompiler
