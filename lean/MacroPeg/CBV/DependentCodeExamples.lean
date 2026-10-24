import MacroPeg.CBV.RecursiveCodeExamples

/-! Retained parent values control actual argument selection, while a
recursive helper captures a different child's value and parent values
remain available after return. -/
namespace Shallot.MacroPeg.CBV.DependentCodeExamples
open RecursiveCodeGrammar
open RecursiveCodeExamples (header bodies head two)

def guarded : MExp := .seq (.notP (.param 0)) two

theorem guarded_captured (x : List Char) (E : List (List Char)) (p q : Nat) (hp : p≤x.length)
    (h : evV (RecursiveParserStability.grammar bodies) x .callByValuePar (canonical bodies x) E guarded p=some (some q)) :
    ∃ u v, header.code u ∧ header.code v ∧ pre x p q=u++v := by
  cases ht : evV (RecursiveParserStability.grammar bodies) x .callByValuePar (canonical bodies x) E (.param 0) p with
  | none =>
    have hn : evV (RecursiveParserStability.grammar bodies) x .callByValuePar (canonical bodies x) E (.notP (.param 0)) p=none := by
      change (match evV (RecursiveParserStability.grammar bodies) x .callByValuePar
          (canonical bodies x) E (.param 0) p with
        | some (some _) => some none
        | some none => some (some p)
        | none => none)=_
      rw [ht]
    rw [guarded,evV_seq_none hn] at h
    cases h
  | some result => cases result with
    | none =>
      have hn : evV (RecursiveParserStability.grammar bodies) x .callByValuePar (canonical bodies x) E (.notP (.param 0)) p=some (some p) := by
        change (match evV (RecursiveParserStability.grammar bodies) x .callByValuePar
          (canonical bodies x) E (.param 0) p with
        | some (some _) => some none
        | some none => some (some p)
        | none => none)=_
        rw [ht]
      rw [guarded,evV_seq_ok hn] at h
      exact (RecursiveCodeExamples.user '@' 1).captured x E p q hp h
    | some j =>
      have hn : evV (RecursiveParserStability.grammar bodies) x .callByValuePar (canonical bodies x) E (.notP (.param 0)) p=some none := by
        change (match evV (RecursiveParserStability.grammar bodies) x .callByValuePar
          (canonical bodies x) E (.param 0) p with
        | some (some _) => some none
        | some none => some (some p)
        | none => none)=_
        rw [ht]
      rw [guarded,evV_seq_fail hn] at h
      cases h

def user (mark : Char) (next : Nat) : User header where
  arg := guarded
  allowed := by simp [guarded,two,head,bodies,header,HelperArgument.Syntax]
  captured := guarded_captured
  body := (RecursiveCodeExamples.user mark next).body

def tails : List (User header) := [user '@' 1,user '%' 0]
def root : MExp := .call 0 []
def good : List Char := "aabb#aabb#aabb#@ab#ab#ab#!?aabb#aabb#".toList
def shortParent : List Char := "aabb#aabb#aabb#@ab#ab#ab#!?aabb#".toList
def sameChild : List Char := "aabb#aabb#aabb#@aabb#aabb#aabb#!?aabb#aabb#".toList

/-- Actual argument selection changes when only the retained parent value
changes; the recursive helper and input remain fixed. -/
theorem argument_depends_on_parent :
    evV (RecursiveParserStability.grammar bodies) "ab#ab#X".toList .callByValuePar
      (tblV (RecursiveParserStability.grammar bodies) "ab#ab#X".toList .callByValuePar 4)
      ["aabb#aabb#".toList] guarded 7=some (some 1) ∧
    evV (RecursiveParserStability.grammar bodies) "ab#ab#X".toList .callByValuePar
      (tblV (RecursiveParserStability.grammar bodies) "ab#ab#X".toList .callByValuePar 4)
      ["ab#ab#".toList] guarded 7=some none := by
  decide +kernel

/-- On a two-codeword capture with unequal parts, retaining only one word
without transforming the original argument would change its selection. -/
theorem duplicated_argument_view_required :
    evV (RecursiveParserStability.grammar bodies) "ab#aabb#X".toList .callByValueSeq
      (tblV (RecursiveParserStability.grammar bodies) "ab#aabb#X".toList .callByValueSeq 4)
      ["ab#".toList] (PrefixCodeCapture.view guarded) 9=some (some 1) ∧
    evV (RecursiveParserStability.grammar bodies) "ab#aabb#X".toList .callByValueSeq
      (tblV (RecursiveParserStability.grammar bodies) "ab#aabb#X".toList .callByValueSeq 4)
      ["ab#".toList] guarded 9=some none := by
  decide +kernel

theorem source_execution :
    evV (source header tails) good .callByValuePar
      (tblV (source header tails) good .callByValuePar 12) [] (render header tails true root) good.length=some (some 0) ∧
    evV (source header tails) shortParent .callByValuePar
      (tblV (source header tails) shortParent .callByValuePar 12) [] (render header tails true root) shortParent.length=some none ∧
    evV (source header tails) sameChild .callByValuePar
      (tblV (source header tails) sameChild .callByValuePar 12) [] (render header tails true root) sameChild.length=some none := by
  decide +kernel

theorem all_inputs (x : List Char) (r : Option (List Char)) :
    SObs (source header tails) .callByValuePar (render header tails true root) x r ↔
    SObs (target header tails) .callByValueSeq (render header tails false root) x r :=
  observations_iff header tails root x r

theorem translated_execution :
    SObs (target header tails) .callByValueSeq (render header tails false root) good (some []) ∧
    SObs (target header tails) .callByValueSeq (render header tails false root) shortParent none ∧
    SObs (target header tails) .callByValueSeq (render header tails false root) sameChild none := by
  have accept (x : List Char)
      (h : evV (source header tails) x .callByValuePar
        (tblV (source header tails) x .callByValuePar 12) [] (render header tails true root) x.length=some (some 0)) :
      SObs (target header tails) .callByValueSeq (render header tails false root) x (some []) := by
    apply (all_inputs x (some [])).mp
    obtain ⟨o,hd,ho⟩ := evV_derives (source_firstOrder header tails) (by decide)
      (render_firstOrder header tails true root) 12 (Nat.le_refl _) h
    rw [sfx_self] at hd
    obtain ⟨t,rest,rfl,hlen⟩ := obsR_ok ho
    have hr : rest=[] := List.length_eq_zero_iff.mp hlen
    subst rest
    exact ⟨_,hd,rfl⟩
  have reject (x : List Char)
      (h : evV (source header tails) x .callByValuePar
        (tblV (source header tails) x .callByValuePar 12) [] (render header tails true root) x.length=some none) :
      SObs (target header tails) .callByValueSeq (render header tails false root) x none := by
    apply (all_inputs x none).mp
    obtain ⟨o,hd,ho⟩ := evV_derives (source_firstOrder header tails) (by decide)
      (render_firstOrder header tails true root) 12 (Nat.le_refl _) h
    rw [sfx_self,obsR_fail ho] at hd
    exact ⟨_,hd,rfl⟩
  exact ⟨accept good source_execution.1,reject shortParent source_execution.2.1,reject sameChild source_execution.2.2⟩

end Shallot.MacroPeg.CBV.DependentCodeExamples
