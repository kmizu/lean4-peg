import MacroPeg.CBV.FiniteSuffixObservedEvaluation
import MacroPeg.CBV.ScannerPairFusion

namespace Shallot.MacroPeg.CBV.FiniteSuffixObservedCorrespondence
open FiniteSuffixObservedSyntax FiniteSuffixObservedDeclarations FiniteSuffixObservedEvaluation FiniteSuffixObservedAtoms
open FiniteSuffixReplay (views)

/-- Both ordinary and every exact-word DFA channel close at the same physical
clock. No original parameterized table is retained in the generated grammar. -/
theorem tables_related (R : List (List Char)) (rs : List Spec) (x : List Char) (k : Nat) :
    Rows R rs x (tblV (source R rs) x .callByValuePar k) (tblV (target R rs) x .callByValueSeq k) := by
  induction k with
  | zero => intro i r hr E hE p hp m hm; cases m <;> rfl
  | succ k ih =>
    intro i r hr E hE p hp m hm
    have hs := FiniteSuffixDependentView.source_rule R rs i r hr
    have ht := target_rule R rs i r hr E hE m hm
    rw [valAt_tblV_succ hs E hp,valAt_tblV_succ ht [] hp]
    have hh := evaluation R rs x _ _ ih (tblV_ok _ _ _ k) (tblV_sound (target_firstOrder R rs) (by decide) k) r.body E p hp
    cases m with
    | none => exact hh.1
    | some v =>
      rcases v with ⟨u,q,r⟩
      obtain ⟨hu,hq,hr⟩ := (mode_mem R u q r).mp hm
      exact hh.2 u hu q r hq hr

theorem physical (R : List (List Char)) (rs : List Spec) (x : List Char) (e : Term) (E : List (List Char))
    (p k : Nat) (hp : p≤x.length) :
    FiniteSuffixObservedDispatch.ArgRel (source R rs) (target R rs) x
      (tblV (source R rs) x .callByValuePar k) (tblV (target R rs) x .callByValueSeq k) E R rs e p :=
  evaluation R rs x _ _ (tables_related R rs x k) (tblV_ok _ _ _ k) (tblV_sound (target_firstOrder R rs) (by decide) k) e E p hp

theorem observations_iff (R : List (List Char)) (rs : List Spec) (e : Term) (x : List Char) (rest : Option (List Char)) :
    SObs (source R rs) .callByValuePar (original R e) x rest ↔
      SObs (target R rs) .callByValueSeq (emit R rs [] none e) x rest := by
  rw [←decideObsV_iff (source_firstOrder R rs) (by decide) (render_firstOrder R e),
    ←decideObsV_iff (target_firstOrder R rs) (by decide) (emit_firstOrder R rs [] none e)]
  unfold decideObsV
  rw [ScannerPairFusion.stable_result_eq _ _ x _ _ _ _ (fun k => (physical R rs x e [] x.length k (Nat.le_refl _)).1.symm)]
  rfl

theorem language_translation (R : List (List Char)) (rs : List Spec) (e : Term) :
    (fun x => SObs (source R rs) .callByValuePar (original R e) x (some []))=
      (fun x => SObs (target R rs) .callByValueSeq (emit R rs [] none e) x (some [])) := by
  funext x
  exact propext (observations_iff R rs e x (some []))

theorem defined_iff (R : List (List Char)) (rs : List Spec) (e : Term) (x : List Char) (v : Option Nat) :
    (∃ k, evV (source R rs) x .callByValuePar (tblV (source R rs) x .callByValuePar k) [] (original R e) x.length=some v) ↔
      ∃ k, evV (target R rs) x .callByValueSeq (tblV (target R rs) x .callByValueSeq k) [] (emit R rs [] none e) x.length=some v := by
  constructor
  · rintro ⟨k,hk⟩; exact ⟨k,(physical R rs x e [] x.length k (Nat.le_refl _)).1.trans hk⟩
  · rintro ⟨k,hk⟩; exact ⟨k,(physical R rs x e [] x.length k (Nat.le_refl _)).1.symm.trans hk⟩

theorem undefined_iff (R : List (List Char)) (rs : List Spec) (e : Term) (x : List Char) :
    (∀ k, evV (source R rs) x .callByValuePar (tblV (source R rs) x .callByValuePar k) [] (original R e) x.length=none) ↔
      ∀ k, evV (target R rs) x .callByValueSeq (tblV (target R rs) x .callByValueSeq k) [] (emit R rs [] none e) x.length=none := by
  constructor
  · intro h k; exact (physical R rs x e [] x.length k (Nat.le_refl _)).1.trans (h k)
  · intro h k; exact (physical R rs x e [] x.length k (Nat.le_refl _)).1.symm.trans (h k)

end Shallot.MacroPeg.CBV.FiniteSuffixObservedCorrespondence
