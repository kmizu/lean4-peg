import MacroPeg.CBV.EmptyObservedEvaluation
import MacroPeg.CBV.EmptyObservedFirstOrder
import MacroPeg.CBV.ScannerPairFusion

namespace Shallot.MacroPeg.CBV.EmptyObservedCorrespondence
open EmptyObservedSyntax EmptyObservedEvaluation
open EmptyResultObservation (project)
abbrev Term := EmptyObservedSyntax.Expr
abbrev Spec := EmptyObservedSyntax.Rule

theorem physical_down (rs : List Spec) (x : List Char) (k : Nat) :
    Down rs x (tblV (source rs) x .callByValuePar k) := by
  intro e E p q hp he
  have hh := ReplayFusion.success_prefix (tblV_sound (source_firstOrder rs) (by decide) k)
    E (original e) (original_firstOrder e) p q hp he
  have hl := congrArg List.length hh.2
  rw [List.length_append,length_sfx x hp,length_sfx x hh.1] at hl
  omega

/-- Every retained environment, not just a preselected palette of captured
words, is represented by its actual empty-bit view. All rows close together. -/
theorem tables_related (rs : List Spec) (x : List Char) (k : Nat) :
    Rows rs x (tblV (source rs) x .callByValuePar k) (tblV (target rs) x .callByValueSeq k) := by
  induction k with
  | zero => intro i r hr E hE p hp zero; cases zero <;> rfl
  | succ k ih =>
    intro i r hr E hE p hp zero
    have hs : ruleAtM (source rs).rules i=some ⟨r.arity,original r.body⟩ := by rw [source_rule,hr]; rfl
    have ht := target_rule rs i r hr (view E) (by simpa [view] using hE) zero
    rw [valAt_tblV_succ hs E hp,valAt_tblV_succ ht [] hp]
    have hh := evaluation rs x _ _ ih (tblV_ok _ _ _ k) (physical_down rs x k) r.body E p hp
    cases zero
    · exact hh.1
    · exact hh.2

theorem physical (rs : List Spec) (x : List Char) (e : Term) (E : List (List Char))
    (p k : Nat) (hp : p≤x.length) :
    evV (target rs) x .callByValueSeq (tblV (target rs) x .callByValueSeq k) [] (emit rs (view E) false e) p=
      evV (source rs) x .callByValuePar (tblV (source rs) x .callByValuePar k) E (original e) p ∧
    evV (target rs) x .callByValueSeq (tblV (target rs) x .callByValueSeq k) [] (emit rs (view E) true e) p=
      project p (evV (source rs) x .callByValuePar (tblV (source rs) x .callByValuePar k) E (original e) p) :=
  evaluation rs x _ _ (tables_related rs x k) (tblV_ok _ _ _ k) (physical_down rs x k) e E p hp

theorem observations_iff (rs : List Spec) (e : Term) (x : List Char) (rest : Option (List Char)) :
    SObs (source rs) .callByValuePar (original e) x rest ↔
      SObs (target rs) .callByValueSeq (emit rs [] false e) x rest := by
  rw [←decideObsV_iff (source_firstOrder rs) (by decide) (original_firstOrder e),
    ←decideObsV_iff (EmptyObservedFirstOrder.target_firstOrder rs) (by decide) (EmptyObservedFirstOrder.emit_firstOrder rs [] false e)]
  unfold decideObsV
  rw [ScannerPairFusion.stable_result_eq _ _ x _ _ _ _ (fun k => (physical rs x e [] x.length k (Nat.le_refl _)).1.symm)]
  simp only [view,List.map_nil]

theorem language_translation (rs : List Spec) (e : Term) :
    (fun x => SObs (source rs) .callByValuePar (original e) x (some []))=
      (fun x => SObs (target rs) .callByValueSeq (emit rs [] false e) x (some [])) := by
  funext x
  exact propext (observations_iff rs e x (some []))

theorem defined_iff (rs : List Spec) (e : Term) (x : List Char) (v : Option Nat) :
    (∃ k, evV (source rs) x .callByValuePar (tblV (source rs) x .callByValuePar k) [] (original e) x.length=some v) ↔
      ∃ k, evV (target rs) x .callByValueSeq (tblV (target rs) x .callByValueSeq k) [] (emit rs [] false e) x.length=some v := by
  constructor
  · rintro ⟨k,hk⟩; exact ⟨k,(physical rs x e [] x.length k (Nat.le_refl _)).1.trans hk⟩
  · rintro ⟨k,hk⟩; exact ⟨k,(physical rs x e [] x.length k (Nat.le_refl _)).1.symm.trans hk⟩

theorem undefined_iff (rs : List Spec) (e : Term) (x : List Char) :
    (∀ k, evV (source rs) x .callByValuePar (tblV (source rs) x .callByValuePar k) [] (original e) x.length=none) ↔
      ∀ k, evV (target rs) x .callByValueSeq (tblV (target rs) x .callByValueSeq k) [] (emit rs [] false e) x.length=none := by
  constructor
  · intro h k; exact (physical rs x e [] x.length k (Nat.le_refl _)).1.trans (h k)
  · intro h k; exact (physical rs x e [] x.length k (Nat.le_refl _)).1.symm.trans (h k)

end Shallot.MacroPeg.CBV.EmptyObservedCorrespondence
