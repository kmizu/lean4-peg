import MacroPeg.CBV.SequentialEncodedMachine
import Complexity.ListIOSpec
import Shallot.Peg.Separation.BitWord

/-! Read ordinary a/b input through the standard bit-input list interface.
No input repetition or extra input fields are supplied. -/
namespace Shallot.MacroPeg.CBV.SequentialBinaryLoader
open Complexity Complexity.BinaryWord
open Shallot.PegSeparation (bitWord)

def field (b : Bool) : List Nat :=
  (encN (SequentialInputRead.code (if b then 'b' else 'a'))).reverse

def reverseFields (w : List Bool) : List Nat := w.flatMap field

theorem field_length (b : Bool) : (field b).length ≤ 100 := by cases b <;> decide

theorem reverseFields_reverse (w : List Bool) :
    reverseFields w.reverse = (Complexity.encS (SequentialInputRead.codes (bitWord w))).reverse := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    simpa [reverseFields,List.flatMap_append,field,bitWord,SequentialInputRead.codes,
      Complexity.encS,List.reverse_append] using ih

def state (X R : List Nat) : Lists 20 := fun i => if i=1 then X else if i=0 then R else []

def body : LProg 20 :=
  .seq (.ite 1 (· == 5) (appendP 0 (field true)) (appendP 0 (field false))) (.pop 1)
def scan : LProg 20 := .loop 1 nonEmpty body

def program : LProg 20 := .seq scan (moveAll 0 11)

private theorem fits {X R : List Nat} {B : Nat} (hX : X.length+2 ≤ B) (hR : R.length+2 ≤ B) :
    LenOK B (state X R) := by
  intro i
  by_cases h1 : i=1 <;> by_cases h0 : i=0 <;> simp_all [state] <;> omega

theorem scan_runs (w : List Bool) (R : List Nat) {B : Nat}
    (hcap : R.length+100*w.length+2 ≤ B) :
    ∃ T, Complexity.Runs (LenOK B) scan (state (w.map bitElem).reverse R)
      (state [] (R++reverseFields w)) T := by
  induction w generalizing R with
  | nil =>
    have hh : LenOK B (state [] R) := fits (by simp only [List.length_nil]; simp at hcap; omega) (by simpa using hcap)
    exact ⟨1,by simpa [reverseFields] using (show Complexity.Runs (LenOK B) scan (state [] R) (state [] R) 1 from
      ⟨1,Nat.le_refl _,.loopF hh rfl⟩)⟩
  | cons b w ih =>
    let S := state ((w.map bitElem).reverse++[bitElem b]) R
    let M := S.set 0 (R++field b)
    have hf := field_length b
    have hS : LenOK B S := fits (by simp; simp at hcap; omega) (by simp at hcap; omega)
    have happ := append_runs (0 : Fin 20) (field b) hS (by simp [S,state]; simp at hcap; omega)
    have heM : S.set 0 (S 0++field b) = M := by simp [M,S,state]
    rw [heM] at happ
    have hM : LenOK B M := by obtain ⟨_,_,he⟩ := happ; exact he.q_end _ (Or.inl rfl)
    have hg : ∃ T, Complexity.Runs (LenOK B)
        (.ite 1 (· == 5) (appendP 0 (field true)) (appendP 0 (field false))) S M T := by
      cases b with
      | false => exact ⟨_,happ.iteF hS (by simp [S,state,lastSym,bitElem])⟩
      | true => exact ⟨_,happ.iteT hS (by simp [S,state,lastSym,bitElem])⟩
    have hp := runs_pop (i := (1 : Fin 20)) hM (by
      apply lenOK_set hM 1
      simp [M,S,state,Lists.set]; simp at hcap; omega)
    have heN : M.set 1 (M 1).dropLast = state (w.map bitElem).reverse (R++field b) := by
      funext i
      by_cases h1 : i=1 <;> by_cases h0 : i=0 <;> simp_all [M,S,state,Lists.set]
    rw [heN] at hp
    obtain ⟨Tg,hg⟩ := hg
    have hb := hg.seq hp
    obtain ⟨U,hu⟩ := ih (R++field b) (by simp; simp at hcap; omega)
    have he : state [] ((R++field b)++reverseFields w) = state [] (R++reverseFields (b::w)) := by
      simp [reverseFields,List.append_assoc]
    rw [he] at hu
    obtain ⟨t,_,hx⟩ := hb
    obtain ⟨u,_,hy⟩ := hu
    have ht : nonEmpty (lastSym (S 1)) = true := by simp [S,state,lastSym,nonEmpty]
    exact ⟨t+1+u,t+1+u,Nat.le_refl _,by simpa only [scan,body,S,List.map_cons,List.reverse_cons] using LExec.loopC hS ht hx hy⟩

def space (n : Nat) : Nat := 100*n+4

theorem runs (w : List Bool) :
    ∃ T, Complexity.Runs (LenOK (space w.length)) program (initLists 20 w)
      (SequentialEncodedMachine.input (bitWord w)) T := by
  obtain ⟨T,hr⟩ := scan_runs w.reverse [] (B := space w.length) (by simp [space])
  have heInput : state (List.map bitElem w.reverse).reverse [] = initLists 20 w := by
    funext i
    by_cases h1 : i=1
    · subst i; simp [state,initLists,List.map_reverse]
    · have hiv : i.val ≠ 1 := fun h => h1 (Fin.ext h)
      simp [state,initLists,h1,hiv]
  rw [heInput,reverseFields_reverse] at hr
  simp only [List.nil_append] at hr
  let X := Complexity.encS (SequentialInputRead.codes (bitWord w))
  have hS : LenOK (space w.length) (state [] X.reverse) := by
    obtain ⟨_,_,he⟩ := hr; exact he.q_end _ (Or.inl rfl)
  have hm := moveAll_runs_bounded (src := (0 : Fin 20)) (dst := 11) (by decide) hS (by
    have hh := hS 0
    simpa [state] using hh)
  have he : ((state [] X.reverse).set 11 (state [] X.reverse 11++(state [] X.reverse 0).reverse)).set 0 [] =
      SequentialEncodedMachine.input (bitWord w) := by
    funext i
    by_cases h11 : i=11 <;> by_cases h0 : i=0 <;> by_cases h1 : i=1 <;>
      simp_all [state,X,SequentialEncodedMachine.input,SequentialInputLength.state,Lists.set]
  rw [he] at hm
  exact ⟨_,hr.seq hm⟩

end Shallot.MacroPeg.CBV.SequentialBinaryLoader
