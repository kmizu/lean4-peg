import MacroPeg.CBV.SequentialPackedHaltMachine
import Shallot.Peg.Separation.BitWord

/-! Load an ordinary binary input as exactly its original a/b word. One
character is retained per input bit, without repetition or extra fields. -/
namespace Shallot.MacroPeg.CBV.SequentialPackedBinaryLoader
open Complexity SequentialCursorEditMachine
open SequentialCaptureCopyMachine (characters character)
open Shallot.PegSeparation (bitWord)

def state (X R : List Nat) : Lists 8 := fun i => if i=1 then X else if i=5 then R else []
def body : LProg 8 := .seq (.ite 1 (symIs 1) (.push 5 (character 'b')) (.push 5 (character 'a'))) (.pop 1)
def scan : LProg 8 := .loop 1 nonEmpty body
def program : LProg 8 := .seq scan (moveAll 5 6)

private theorem fits (X R : List Nat) {B : Nat} (hX : X.length+2 ≤ B) (hR : R.length+2 ≤ B) :
    LenOK B (state X R) := by
  intro i
  by_cases h1 : i=1 <;> by_cases h5 : i=5 <;> simp [state,h1,h5] <;> omega

theorem scan_runs (w : List Bool) (R : List Nat) {B : Nat} (hcap : R.length+w.length+2 ≤ B) :
    ∃ T, Runs (LenOK B) scan (state (w.map bitElem).reverse R)
      (state [] (R ++ characters (bitWord w))) T := by
  induction w generalizing R with
  | nil =>
    have hL := fits [] R (B := B) (by simp; simp at hcap; omega) (by simpa using hcap)
    exact ⟨1,by simpa [characters,bitWord] using (show Runs (LenOK B) scan (state [] R) (state [] R) 1 from
      ⟨1,Nat.le_refl _,.loopF hL rfl⟩)⟩
  | cons b w ih =>
    let S := state ((w.map bitElem).reverse ++ [bitElem b]) R
    let M := S.set 5 (R ++ [character (if b then 'b' else 'a')])
    have hS : LenOK B S := fits _ R (by simp; simp at hcap; omega) (by simp at hcap; omega)
    have hM : LenOK B M := lenOK_set hS 5 (by simp; simp at hcap; omega)
    have hp : ∃ T, Runs (LenOK B) (.ite 1 (symIs 1) (.push 5 (character 'b')) (.push 5 (character 'a'))) S M T := by
      cases b with
      | false => exact ⟨_,(runs_push (i := (5 : Fin 8)) (e := character 'a') hS hM).iteF hS (by
          simp [S,state,lastSym,bitElem,symIs])⟩
      | true => exact ⟨_,(runs_push (i := (5 : Fin 8)) (e := character 'b') hS hM).iteT hS (by
          simp [S,state,lastSym,bitElem,symIs])⟩
    obtain ⟨Tp,hp⟩ := hp
    have hpop := runs_pop (i := (1 : Fin 8)) hM (by
      apply lenOK_set hM 1
      simp [M,S,state,Lists.set]
      simp at hcap
      omega)
    have he : M.set 1 (M 1).dropLast = state (w.map bitElem).reverse (R ++ [character (if b then 'b' else 'a')]) := by
      funext i
      by_cases h1 : i=1 <;> by_cases h5 : i=5 <;> simp [M,S,state,Lists.set,h1,h5]
    rw [he] at hpop
    obtain ⟨Ti,hi⟩ := ih (R ++ [character (if b then 'b' else 'a')]) (by
      simp only [List.length_append,List.length_cons,List.length_nil] at hcap ⊢
      omega)
    have hout : state [] ((R ++ [character (if b then 'b' else 'a')]) ++ characters (bitWord w)) =
        state [] (R ++ characters (bitWord (b :: w))) := by simp [characters,bitWord,List.append_assoc]
    rw [hout] at hi
    obtain ⟨t1,ht1,hx1⟩ := hp.seq hpop
    obtain ⟨t2,ht2,hx2⟩ := hi
    exact ⟨t1+1+t2,t1+1+t2,by omega,by
      simpa only [scan,body,S,List.map_cons,List.reverse_cons] using
        LExec.loopC hS (by simp [S,state,lastSym,nonEmpty,bitElem]) hx1 hx2⟩

/-- The standard bit-input list interface loads to one a/b character per bit,
using at most input length plus two cells on each tape throughout. -/
theorem runs (w : List Bool) :
    ∃ T, Runs (LenOK (w.length+2)) program (initLists 8 w)
      (SequentialPackedInitMachine.input (characters (bitWord w))) T := by
  obtain ⟨Ts,hs⟩ := scan_runs w.reverse [] (B := w.length+2) (by simp)
  have hin : state (w.reverse.map bitElem).reverse []=initLists 8 w := by
    funext i
    by_cases h1 : i=1
    · subst i; simp [state,initLists,List.map_reverse]
    · have hv : i.val ≠ 1 := fun h => h1 (Fin.ext h)
      simp [state,initLists,h1,hv]
  have hrev : characters (bitWord w.reverse)=(characters (bitWord w)).reverse := by
    simp [characters,bitWord,List.map_reverse]
  rw [hin,hrev] at hs
  simp only [List.nil_append] at hs
  let M := state [] (characters (bitWord w)).reverse
  have hM : LenOK (w.length+2) M := end_fits hs
  have hr := moveAll_runs_bounded (src := (5 : Fin 8)) (dst := 6) (by decide) hM (by
    simp [M,state,characters,bitWord])
  have he : (M.set 6 (M 6 ++ (M 5).reverse)).set 5 [] = SequentialPackedInitMachine.input (characters (bitWord w)) := by
    funext i
    by_cases h1 : i=1 <;> by_cases h5 : i=5 <;> by_cases h6 : i=6 <;>
      simp [M,state,SequentialPackedInitMachine.input,Lists.set,h1,h5,h6]
  rw [he] at hr
  exact ⟨_,hs.seq hr⟩

end Shallot.MacroPeg.CBV.SequentialPackedBinaryLoader
