import MacroPeg.CBV.SequentialParamPackedMachine

/-! Source-fixed token tests over the actual original input. Constants stay
in program guards, while every input character and compressed position is
read from the tape. Input is restored on both success and failure. -/
namespace Shallot.MacroPeg.CBV.SequentialTokenMatchMachine
open Complexity SequentialCursorEdit SequentialCursorEditMachine SequentialCursorDecreaseMachine
open SequentialCaptureCopyMachine (characters character)

abbrev Test := Nat → Bool

def runTests : List Test → List Char → Option (List Char)
  | [], X => some X
  | _ :: _, [] => none
  | test :: tests, c :: X => if test (character c+4) then runTests tests X else none

def reject : LProg 8 := .seq (dropBlock 0 1) (moveAll 5 6)
def accept : LProg 8 := .seq SequentialWordRestoreMachine.success (moveAll 5 6)
def advance : LProg 8 := .seq (moveTop 5 6) (decrement 0 1)
def program : List Test → LProg 8
  | [] => accept
  | test :: tests => .ite 5 nonEmpty (.ite 5 test (.seq advance (program tests)) reject) reject

def result (L : Lists 8) (C A : List Nat) (ps : List Nat) (X : List Char)
    (r : Option (List Char)) : Lists 8 :=
  ((((L.set 2 (C ++ [if r.isSome then 1 else 0])).set 0
    (cursors ((r.map List.length).toList ++ ps))).set 5 []).set 6 (A ++ characters X))

theorem reject_runs (X : List Char) (ps : List Nat) (n : Nat)
    (hchain : SequentialCursorChain.Chain X.length ps n) (C A : List Nat) (L : Lists 8) {B : Nat}
    (hflag : L 2=C ++ [0]) (hcur : L 0=cursors (X.length :: ps))
    (hx : L 5=(characters X).reverse) (ha : L 6=A) (h1 : L 1=[])
    (hL : LenOK B L) (hcap : A.length+X.length+2 ≤ B) :
    ∃ T, Runs (LenOK B) reject L (result L C A ps X none) T := by
  obtain ⟨Td,hd⟩ := drop_current_runs (src := (0 : Fin 8)) (tmp := 1) (by decide) hchain L hcur h1 hL
  let M := L.set 0 (cursors ps)
  have hr := moveAll_runs_bounded (src := (5 : Fin 8)) (dst := 6) (by decide) (end_fits hd)
    (by simpa [M,Lists.set,hx,ha,characters] using hcap)
  have he : (M.set 6 (M 6 ++ (M 5).reverse)).set 5 [] = result L C A ps X none := by
    funext j
    by_cases h0 : j=0 <;> by_cases h2 : j=2 <;> by_cases h5 : j=5 <;> by_cases h6 : j=6 <;>
      simp_all [M,result,Lists.set]
  rw [he] at hr
  exact ⟨_,hd.seq hr⟩

theorem accept_runs (X : List Char) (ps : List Nat) (C A : List Nat) (L : Lists 8) {B : Nat}
    (hflag : L 2=C ++ [0]) (hcur : L 0=cursors (X.length :: ps))
    (hx : L 5=(characters X).reverse) (ha : L 6=A)
    (hL : LenOK B L) (hcap : A.length+X.length+2 ≤ B) :
    ∃ T, Runs (LenOK B) accept L (result L C A ps X (some X)) T := by
  have hs := SequentialWordRestoreMachine.success_runs C L hflag hL
  let M := L.set 2 (C ++ [1])
  have hr := moveAll_runs_bounded (src := (5 : Fin 8)) (dst := 6) (by decide) (end_fits hs)
    (by simpa [M,Lists.set,hx,ha,characters] using hcap)
  have he : (M.set 6 (M 6 ++ (M 5).reverse)).set 5 [] = result L C A ps X (some X) := by
    funext j
    by_cases h0 : j=0 <;> by_cases h2 : j=2 <;> by_cases h5 : j=5 <;> by_cases h6 : j=6 <;>
      simp_all [M,result,Lists.set]
  rw [he] at hr
  exact ⟨_,hs.seq hr⟩

theorem advance_runs (c : Char) (X : List Char) (ps : List Nat) (n : Nat)
    (hchain : SequentialCursorChain.Chain (X.length+1) ps n) (A : List Nat) (L : Lists 8) {B : Nat}
    (hcur : L 0=cursors ((X.length+1) :: ps)) (hx : L 5=(characters (c :: X)).reverse)
    (ha : L 6=A) (h1 : L 1=[]) (hL : LenOK B L) (hcap : A.length+X.length+3 ≤ B) :
    ∃ T, Runs (LenOK B) advance L
      (((L.set 5 (characters X).reverse).set 6 (A ++ [character c])).set 0 (cursors (X.length :: ps))) T := by
  have hs : L 5=(characters X).reverse ++ [character c] := by
    simpa only [characters,List.map_cons,List.reverse_cons] using hx
  have hm := SequentialCaptureSpliceMachine.moveLast_runs (by decide : (5 : Fin 8) ≠ 6) _ (character c) L hs hL
    (by rw [ha]; omega)
  let M := (L.set 5 (characters X).reverse).set 6 (A ++ [character c])
  have heM : (L.set 5 (characters X).reverse).set 6 (L 6 ++ [character c])=M := by rw [ha]
  rw [heM] at hm
  obtain ⟨Td,hd⟩ := decrement_current_runs (src := (0 : Fin 8)) (tmp := 1) (by decide) hchain M
    (by simpa [M,Lists.set] using hcur) (by simpa [M,Lists.set] using h1) (end_fits hm)
  exact ⟨_,hm.seq hd⟩

/-- Arbitrary source-fixed symbol predicates require no runtime word buffer. -/
theorem match_runs (tests : List Test) (X : List Char) (ps : List Nat) (n : Nat)
    (hchain : SequentialCursorChain.Chain X.length ps n) (C A : List Nat) (L : Lists 8) {B : Nat}
    (hflag : L 2=C ++ [0]) (hcur : L 0=cursors (X.length :: ps))
    (hx : L 5=(characters X).reverse) (ha : L 6=A) (h1 : L 1=[])
    (hL : LenOK B L) (hcap : A.length+X.length+2 ≤ B) :
    ∃ T, Runs (LenOK B) (program tests) L (result L C A ps X (runTests tests X)) T := by
  induction tests generalizing X A L with
  | nil => exact accept_runs X ps C A L hflag hcur hx ha hL hcap
  | cons test tests ih => cases X with
    | nil =>
      obtain ⟨Tr,hr⟩ := reject_runs [] ps n hchain C A L hflag hcur hx ha h1 hL hcap
      exact ⟨_,hr.iteF hL (by simp [hx,characters,lastSym,nonEmpty])⟩
    | cons c X =>
      have htop : lastSym (L 5)=character c+4 := by
        simp only [hx,characters,List.map_cons,List.reverse_cons,lastSym_append]
      have hnon : nonEmpty (lastSym (L 5))=true := by simp [htop,nonEmpty,character]
      cases ht : test (character c+4) with
      | false =>
        obtain ⟨Tr,hr⟩ := reject_runs (c :: X) ps n hchain C A L hflag hcur hx ha h1 hL hcap
        have hh : Runs (LenOK B) (program (test :: tests)) L (result L C A ps (c :: X) none) (Tr+1+1) := (hr.iteF (i := (5 : Fin 8)) (c := test) hL (by simpa only [htop] using ht)).iteT hL hnon
        simpa only [program,runTests,ht,Bool.false_eq_true,if_false] using (show ∃ T, Runs (LenOK B)
          (program (test :: tests)) L (result L C A ps (c :: X) none) T from ⟨_,hh⟩)
      | true =>
        obtain ⟨Ta,had⟩ := advance_runs c X ps n hchain A L hcur hx ha h1 hL
          (by simp only [List.length_cons] at hcap; omega)
        let M := (((L.set 5 (characters X).reverse).set 6 (A ++ [character c])).set 0 (cursors (X.length :: ps)))
        obtain ⟨Ti,hi⟩ := ih X (hchain.lower (Nat.le_succ X.length)) (A ++ [character c]) M
          (by simpa [M,Lists.set] using hflag) rfl rfl rfl
          (by simpa [M,Lists.set] using h1) (end_fits had)
          (by simp only [List.length_append,List.length_cons,List.length_nil] at hcap ⊢; omega)
        have he : result M C (A ++ [character c]) ps X (runTests tests X) =
            result L C A ps (c :: X) (runTests tests X) := by
          funext j
          by_cases h0 : j=0 <;> by_cases h2 : j=2 <;> by_cases h5 : j=5 <;> by_cases h6 : j=6 <;>
            simp [result,M,Lists.set,h0,h2,h5,h6,characters,List.append_assoc]
        rw [he] at hi
        have hh : Runs (LenOK B) (program (test :: tests)) L (result L C A ps (c :: X) (runTests tests X)) (Ta+Ti+1+1) := ((had.seq hi).iteT (i := (5 : Fin 8)) (c := test) hL (by simpa only [htop] using ht)).iteT hL hnon
        simpa only [program,runTests,ht,if_true] using (show ∃ T, Runs (LenOK B)
          (program (test :: tests)) L (result L C A ps (c :: X) (runTests tests X)) T from ⟨_,hh⟩)

theorem constOK (tests : List Test) (E : Nat) (hE : 2 ≤ E) : (program tests).ConstOK E := by
  have hd : reject.ConstOK E := by simp [reject,dropBlock,scan,moveTop,moveAll,clearP,LProg.ConstOK]
  have hs : accept.ConstOK E := ⟨by simp [SequentialWordRestoreMachine.success,LProg.ConstOK]; omega,
    by simp [moveAll,moveTop,LProg.ConstOK]⟩
  have ha : advance.ConstOK E := ⟨by simp [moveTop,LProg.ConstOK],decrement_constOK hE 0 1⟩
  induction tests with
  | nil => exact hs
  | cons test tests ih => exact ⟨⟨⟨ha,ih⟩,hd⟩,hd⟩

end Shallot.MacroPeg.CBV.SequentialTokenMatchMachine
