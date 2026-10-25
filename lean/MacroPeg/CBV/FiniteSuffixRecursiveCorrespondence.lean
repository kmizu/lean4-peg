import MacroPeg.CBV.FiniteSuffixRecursiveEvaluation

namespace Shallot.MacroPeg.CBV.FiniteSuffixRecursiveCorrespondence
open FiniteSuffixRecursiveSyntax FiniteSuffixRecursiveHelpers FiniteSuffixRecursiveEvaluation
open RegularCaptureProduct (Node)
abbrev Spec := FiniteSuffixRecursiveSyntax.Rule
abbrev Term := FiniteSuffixRecursiveSyntax.Expr

theorem source_stable (nodes : List Node) (hn : RegularCaptureProduct.Valid nodes) (R : List (List Char)) (rs : List Spec) (x : List Char) :
    ClockFreezing.StableRows (source nodes R rs) x .callByValuePar (RecursiveParserStability.pick (sourceBodies nodes))
      (RecursiveParserStability.floor (sourceBodies nodes) x) :=
  RecursiveParserStability.helpers_stable (RegularCaptureProduct.helper_valid hn) (source_installed nodes R rs) x _

theorem target_stable (nodes : List Node) (hn : RegularCaptureProduct.Valid nodes) (R : List (List Char)) (rs : List Spec) (x : List Char) :
    ClockFreezing.StableRows (target nodes R rs) x .callByValueSeq (RecursiveParserStability.pick (targetBodies nodes R))
      (RecursiveParserStability.floor (targetBodies nodes R) x) :=
  RecursiveParserStability.helpers_stable
    (RegularCaptureProduct.component_valid nodes hn _ (ExactWordCaptureMachine.observer_valid _).1) (target_installed nodes R rs) x _

/-- Frozen helper evaluation is cofinal with actual physical evaluation on
both sides; the emitted grammar contains only ordinary fixed rule calls. -/
theorem defined_iff (nodes : List Node) (hn : RegularCaptureProduct.Valid nodes) (R : List (List Char)) (rs : List Spec)
    (e : Term) (x : List Char) (p : Nat) (hp : p≤x.length) (v : Option Nat) :
    (∃ k, evV (source nodes R rs) x .callByValuePar (tblV (source nodes R rs) x .callByValuePar k) [] (render nodes R rs none e) p=some v) ↔
      ∃ k, evV (target nodes R rs) x .callByValueSeq (tblV (target nodes R rs) x .callByValueSeq k) [] (render nodes R rs (some []) e) p=some v := by
  have hs := ClockFreezing.defined_iff (source nodes R rs) x .callByValuePar _ _ (source_stable nodes hn R rs x) [] (render nodes R rs none e) p v
  have ht := ClockFreezing.defined_iff (target nodes R rs) x .callByValueSeq _ _ (target_stable nodes hn R rs x) [] (render nodes R rs (some []) e) p v
  constructor
  · intro h
    obtain ⟨k,hk⟩ := hs.mpr h
    exact ht.mp ⟨k,(frozen_equality nodes hn R rs x k e p hp).symm.trans hk⟩
  · intro h
    obtain ⟨k,hk⟩ := ht.mpr h
    exact hs.mp ⟨k,(frozen_equality nodes hn R rs x k e p hp).trans hk⟩

theorem canonical (nodes : List Node) (hn : RegularCaptureProduct.Valid nodes) (R : List (List Char)) (rs : List Spec)
    (e : Term) (x : List Char) (p : Nat) (hp : p≤x.length) :
    evV (source nodes R rs) x .callByValuePar (tblV (source nodes R rs) x .callByValuePar (iterBoundV (source nodes R rs) x)) [] (render nodes R rs none e) p=
      evV (target nodes R rs) x .callByValueSeq (tblV (target nodes R rs) x .callByValueSeq (iterBoundV (target nodes R rs) x)) [] (render nodes R rs (some []) e) p := by
  cases hs : evV (source nodes R rs) x .callByValuePar (tblV (source nodes R rs) x .callByValuePar (iterBoundV (source nodes R rs) x)) [] (render nodes R rs none e) p with
  | none =>
    cases ht : evV (target nodes R rs) x .callByValueSeq (tblV (target nodes R rs) x .callByValueSeq (iterBoundV (target nodes R rs) x)) [] (render nodes R rs (some []) e) p with
    | none => rfl
    | some v =>
      obtain ⟨k,hk⟩ := (defined_iff nodes hn R rs e x p hp v).mpr ⟨_,ht⟩
      have hh := (tblV_stable (source nodes R rs) x .callByValuePar hp).mp ⟨k,hk⟩
      rw [hs] at hh; cases hh
  | some v =>
    obtain ⟨k,hk⟩ := (defined_iff nodes hn R rs e x p hp v).mp ⟨_,hs⟩
    exact ((tblV_stable (target nodes R rs) x .callByValueSeq hp).mp ⟨k,hk⟩).symm

theorem observations_iff (nodes : List Node) (hn : RegularCaptureProduct.Valid nodes) (R : List (List Char)) (rs : List Spec)
    (e : Term) (x : List Char) (rest : Option (List Char)) :
    SObs (source nodes R rs) .callByValuePar (render nodes R rs none e) x rest ↔
      SObs (target nodes R rs) .callByValueSeq (render nodes R rs (some []) e) x rest := by
  rw [←decideObsV_iff (source_firstOrder nodes R rs) (by decide) (firstOrder nodes R rs none e),
    ←decideObsV_iff (target_firstOrder nodes R rs) (by decide) (firstOrder nodes R rs (some []) e)]
  unfold decideObsV
  rw [canonical nodes hn R rs e x x.length (Nat.le_refl _)]

theorem language_translation (nodes : List Node) (hn : RegularCaptureProduct.Valid nodes) (R : List (List Char)) (rs : List Spec) (e : Term) :
    (fun x => SObs (source nodes R rs) .callByValuePar (render nodes R rs none e) x (some []))=
      (fun x => SObs (target nodes R rs) .callByValueSeq (render nodes R rs (some []) e) x (some [])) := by
  funext x
  exact propext (observations_iff nodes hn R rs e x (some []))

theorem undefined_iff (nodes : List Node) (hn : RegularCaptureProduct.Valid nodes) (R : List (List Char)) (rs : List Spec)
    (e : Term) (x : List Char) :
    (∀ k, evV (source nodes R rs) x .callByValuePar (tblV (source nodes R rs) x .callByValuePar k) [] (render nodes R rs none e) x.length=none) ↔
      ∀ k, evV (target nodes R rs) x .callByValueSeq (tblV (target nodes R rs) x .callByValueSeq k) [] (render nodes R rs (some []) e) x.length=none := by
  constructor
  · intro h k
    cases he : evV (target nodes R rs) x .callByValueSeq (tblV (target nodes R rs) x .callByValueSeq k) [] (render nodes R rs (some []) e) x.length with
    | none => rfl
    | some v =>
      obtain ⟨j,hj⟩ := (defined_iff nodes hn R rs e x x.length (Nat.le_refl _) v).mpr ⟨k,he⟩
      rw [h j] at hj; cases hj
  · intro h k
    cases he : evV (source nodes R rs) x .callByValuePar (tblV (source nodes R rs) x .callByValuePar k) [] (render nodes R rs none e) x.length with
    | none => rfl
    | some v =>
      obtain ⟨j,hj⟩ := (defined_iff nodes hn R rs e x x.length (Nat.le_refl _) v).mp ⟨k,he⟩
      rw [h j] at hj; cases hj

end Shallot.MacroPeg.CBV.FiniteSuffixRecursiveCorrespondence
