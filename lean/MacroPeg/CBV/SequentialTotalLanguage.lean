import MacroPeg.CBV.SequentialTotalCompiler
import Shallot.Peg.Separation.CBVStrict

/-! Totalization gives a fixed Seq grammar for the complement of every
first-order Seq language on the same original character strings. This is
an internal Seq closure result, not the missing Par-to-Seq translation. -/
namespace Shallot.MacroPeg.CBV.SequentialTotalLanguage
open SequentialTotalSyntax SequentialTotalControl SequentialTotalCompiler
open SequentialLocalCorrectness (canonical)

def complementStart (g : MGrammar) (e : MExp) : MExp :=
  .seq (.notP (.seq (start g e) (.notP .any))) (.star .any)

theorem complement_firstOrder (g : MGrammar) (e : MExp) : (complementStart g e).FirstOrder :=
  ⟨⟨start_firstOrder g e,True.intro⟩,True.intro⟩

theorem eof_eval (g : MGrammar) (x : List Char) (T : SequentialClock.Table)
    (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV g x .callByValueSeq T E (.notP .any) p=
      if p=0 then some (some 0) else some none := by
  cases hs : sfx x p with
  | nil =>
    have hz : p=0 := by have hl := length_sfx x hp; rw [hs] at hl; simpa using hl.symm
    subst p
    simp [evV,hs]
  | cons c rest =>
    have hz : p≠0 := by have hl := length_sfx x hp; rw [hs,List.length_cons] at hl; omega
    simp [evV,hs,hz]

def complementResult (r : Res) : Res := if r=some (some 0) then some none else some (some 0)

theorem complement_eval (g : MGrammar) (hg : g.FirstOrder) (e : MExp) (he : e.FirstOrder)
    (x : List Char) :
    evV (target g) x .callByValueSeq (canonical (target g) x) [] (complementStart g e) x.length=
      complementResult (evV g x .callByValueSeq (canonical g x) [] e x.length) := by
  have hs := SequentialTotalCorrectness.start_correct g hg x [] e he x.length (Nat.le_refl _)
  have acceptRest (hf : evV (target g) x .callByValueSeq (canonical (target g) x) []
      (.seq (start g e) (.notP .any)) x.length=some none) :
      evV (target g) x .callByValueSeq (canonical (target g) x) [] (complementStart g e) x.length=some (some 0) := by
    rw [complementStart,evV_seq_ok (evV_not_fail hf)]
    exact SequentialResultZero.any_star_eval _ _ _ _ _ _ (Nat.le_refl _)
  cases hv : evV g x .callByValueSeq (canonical g x) [] e x.length with
  | none =>
    rw [hv] at hs
    exact acceptRest (evV_seq_fail hs)
  | some v => cases v with
    | none =>
      rw [hv] at hs
      exact acceptRest (evV_seq_fail hs)
    | some q =>
      rw [hv] at hs
      have hq := SequentialClock.expression_descending
        (SequentialClock.table_descending g x (SequentialLocalCorrectness.clock g x)) [] e x.length q hv
      have hf := eof_eval (target g) x (canonical (target g) x) [] q hq
      by_cases hq0 : q=0
      · subst q
        rw [complementStart,evV_seq_fail (evV_not_ok ((evV_seq_ok hs).trans hf))]
        rfl
      · simp only [if_neg hq0] at hf
        have ha := acceptRest ((evV_seq_ok hs).trans hf)
        simpa only [complementResult,show (some (some q) : Res)≠some (some 0) by simp [hq0],↓reduceIte] using ha

theorem complement_recognizes (g : MGrammar) (hg : g.FirstOrder) (e : MExp) (he : e.FirstOrder)
    (x : List Char) :
    SObs (target g) .callByValueSeq (complementStart g e) x (some []) ↔
      ¬ SObs g .callByValueSeq e x (some []) := by
  have hs := canonical_success_iff g hg e he x 0 (by omega)
  have ht := canonical_success_iff (target g) (target_firstOrder g)
    (complementStart g e) (complement_firstOrder g e) x 0 (by omega)
  simp only [sfx,Nat.sub_zero,List.drop_length] at hs ht
  rw [←hs,←ht,complement_eval g hg e he x]
  by_cases hv : evV g x .callByValueSeq (canonical g x) [] e x.length=some (some 0) <;>
    simp [complementResult,hv]

end Shallot.MacroPeg.CBV.SequentialTotalLanguage

namespace Shallot.PegSeparation
open Shallot.MacroPeg Shallot.MacroPeg.CBV

/-- First-order CBV-Seq languages are closed under complement on the
original character strings, including rejection caused by undefinedness. -/
theorem firstOrder_seq_complement {L : Shallot.Cfg.Language}
    (h : IsFirstOrderCBVPEL .callByValueSeq L) :
    IsFirstOrderCBVPEL .callByValueSeq (fun x => ¬ L x) := by
  obtain ⟨g,e,hg,he,hL⟩ := h
  refine ⟨SequentialTotalSyntax.target g,SequentialTotalLanguage.complementStart g e,
    SequentialTotalSyntax.target_firstOrder g,SequentialTotalLanguage.complement_firstOrder g e,?_⟩
  intro x
  exact (not_congr (hL x)).trans (SequentialTotalLanguage.complement_recognizes g hg e he x).symm

end Shallot.PegSeparation
