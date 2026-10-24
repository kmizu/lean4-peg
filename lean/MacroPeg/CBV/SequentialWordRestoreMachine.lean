import MacroPeg.CBV.SequentialWordMatchMachine

/-! Finish a selected captured-word comparison and restore the actual input
and word streams. Failure removes the partially advanced current cursor. -/
namespace Shallot.MacroPeg.CBV.SequentialWordRestoreMachine
open Complexity SequentialCursorEdit SequentialCursorEditMachine
open SequentialCaptureCopyMachine (characters character)
open SequentialWordMatchMachine (Trace)

def success : LProg 8 := .seq (.pop 2) (.push 2 1)
def record : LProg 8 := .ite 4 (symIs 0) success (dropBlock 0 1)
def restore : LProg 8 := .seq record (.seq (moveAll 7 4) (moveAll 5 6))
def program : LProg 8 := .seq SequentialWordMatchMachine.program restore

def result (L : Lists 8) (C tail A P : List Nat) (ps : List Nat) (w X wr xr : List Char) : Lists 8 :=
  ((((((L.set 2 (C ++ [if wr=[] then 1 else 0])).set 0
    (cursors (if wr=[] then xr.length :: ps else ps))).set 4
      (tail ++ [0] ++ (characters w).reverse ++ P.reverse)).set 7 []).set 5 []).set 6 (A ++ characters X))

theorem success_runs (C : List Nat) (L : Lists 8) {B : Nat}
    (hflag : L 2 = C ++ [0]) (hL : LenOK B L) :
    Runs (LenOK B) success L (L.set 2 (C ++ [1])) 2 := by
  have hh := hL 2
  rw [hflag] at hh
  simp only [List.length_append,List.length_singleton] at hh
  have hp := runs_pop (i := (2 : Fin 8)) hL (by
    apply lenOK_set hL 2
    rw [hflag,List.dropLast_concat]
    omega)
  have he : L.set 2 (L 2).dropLast = L.set 2 C := by rw [hflag,List.dropLast_concat]
  rw [he] at hp
  have hs := runs_push (i := (2 : Fin 8)) (e := 1) (end_fits hp) (by
    apply lenOK_set (end_fits hp) 2
    simp
    omega)
  simpa only [success,Lists.set_same,Lists.set_set_u] using hp.seq hs

theorem record_runs (wr xr : List Char) (ps : List Nat) (n : Nat)
    (hchain : SequentialCursorChain.Chain xr.length ps n) (C tail : List Nat) (L : Lists 8) {B : Nat}
    (hflag : L 2 = C ++ [0]) (hcur : L 0 = cursors (xr.length :: ps))
    (hw : L 4 = tail ++ [0] ++ (characters wr).reverse) (h1 : L 1 = []) (hL : LenOK B L) :
    ∃ T, Runs (LenOK B) record L
      ((L.set 2 (C ++ [if wr=[] then 1 else 0])).set 0
        (cursors (if wr=[] then xr.length :: ps else ps))) T := by
  cases wr with
  | nil =>
    have hs := success_runs C L hflag hL
    have hg : symIs 0 (lastSym (L 4))=true := by
      simp only [hw,characters,List.map_nil,List.reverse_nil,List.append_nil,lastSym_append]
      rfl
    have he : (L.set 2 (C ++ [1])).set 0 (cursors (xr.length :: ps)) = L.set 2 (C ++ [1]) := by
      funext j
      by_cases h0 : j=0 <;> by_cases h2 : j=2 <;> simp_all [Lists.set]
    simp only [ite_true]
    rw [he]
    exact ⟨_,hs.iteT hL hg⟩
  | cons c wr =>
    obtain ⟨Td,hd⟩ := drop_current_runs (src := (0 : Fin 8)) (tmp := 1) (by decide) hchain L hcur h1 hL
    have hg : symIs 0 (lastSym (L 4))=false := by
      rw [hw]
      simp only [characters,List.map_cons,List.reverse_cons,← List.append_assoc,lastSym_append]
      simp [symIs,character]
    have he : (L.set 2 (C ++ [0])).set 0 (cursors ps) = L.set 0 (cursors ps) := by
      rw [← hflag,Lists.set_get_self]
    simpa only [List.cons_ne_nil,if_false,he] using (show ∃ T, Runs (LenOK B) record L (L.set 0 (cursors ps)) T from ⟨_,hd.iteF hL hg⟩)

/-- Both streams are restored after success or mismatch, including empty
words. Every intermediate state obeys the given combined-stream capacities. -/
theorem restore_runs {w X U wr xr : List Char} (trace : Trace w X U wr xr)
    (ps : List Nat) (n : Nat) (hchain : SequentialCursorChain.Chain X.length ps n)
    (C tail A P : List Nat) (L : Lists 8) {B : Nat} (h1 : L 1 = [])
    (hL : LenOK B (SequentialWordMatchMachine.output L C tail A P ps U wr xr))
    (hword : tail.length+1+w.length+P.length+2 ≤ B)
    (hinput : A.length+X.length+2 ≤ B) :
    ∃ T, Runs (LenOK B) restore (SequentialWordMatchMachine.output L C tail A P ps U wr xr)
      (result L C tail A P ps w X wr xr) T := by
  obtain ⟨hw,hx⟩ := trace.split
  have hwl : w.length=U.length+wr.length := by rw [hw,List.length_append]
  have hxl : X.length=U.length+xr.length := by rw [hx,List.length_append]
  let M := SequentialWordMatchMachine.output L C tail A P ps U wr xr
  obtain ⟨Tr,hr⟩ := record_runs wr xr ps n (hchain.lower (by omega)) C tail M rfl rfl rfl
    (by simpa [M,SequentialWordMatchMachine.output,Lists.set] using h1) hL
  let N := (M.set 2 (C ++ [if wr=[] then 1 else 0])).set 0
    (cursors (if wr=[] then xr.length :: ps else ps))
  have hN : LenOK B N := end_fits hr
  have hm := moveAll_runs_bounded (src := (7 : Fin 8)) (dst := 4) (by decide) hN (by
    simp [N,M,SequentialWordMatchMachine.output,Lists.set,characters]
    omega)
  let R := (N.set 4 (N 4 ++ (N 7).reverse)).set 7 []
  have hi := moveAll_runs_bounded (src := (5 : Fin 8)) (dst := 6) (by decide) (end_fits hm) (by
    simp [N,M,SequentialWordMatchMachine.output,Lists.set,characters]
    omega)
  have he : (R.set 6 (R 6 ++ (R 5).reverse)).set 5 [] = result L C tail A P ps w X wr xr := by
    funext j
    by_cases h0 : j=0 <;> by_cases h2 : j=2 <;> by_cases h4 : j=4 <;>
      by_cases h5 : j=5 <;> by_cases h6 : j=6 <;> by_cases h7 : j=7 <;>
      simp [R,N,M,SequentialWordMatchMachine.output,result,Lists.set,h0,h2,h4,h5,h6,h7,
        hw,hx,characters,List.reverse_append,List.append_assoc]
  rw [he] at hi
  exact ⟨_,hr.seq (hm.seq hi)⟩

theorem match_runs {w X U wr xr : List Char} (trace : Trace w X U wr xr)
    (ps : List Nat) (n : Nat) (hchain : SequentialCursorChain.Chain X.length ps n)
    (C tail A P : List Nat) (L : Lists 8) {B : Nat}
    (hflag : L 2 = C ++ [1]) (hcur : L 0 = cursors (X.length :: ps))
    (hw : L 4 = tail ++ [0] ++ (characters w).reverse) (hx : L 5 = (characters X).reverse)
    (ha : L 6 = A) (hp : L 7 = P) (h1 : L 1 = []) (hL : LenOK B L)
    (hword : tail.length+1+w.length+P.length+2 ≤ B) (hinput : A.length+X.length+2 ≤ B) :
    ∃ T, Runs (LenOK B) program L (result L C tail A P ps w X wr xr) T := by
  obtain ⟨Tm,hm⟩ := SequentialWordMatchMachine.loop_runs trace ps n hchain C tail A P L
    hflag hcur hw hx ha hp h1 hL (by omega) hinput
  obtain ⟨Tr,hr⟩ := restore_runs trace ps n hchain C tail A P L h1 (end_fits hm) hword hinput
  exact ⟨_,hm.seq hr⟩


theorem constOK (E : Nat) (hE : 2 ≤ E) : program.ConstOK E := by
  have hs : success.ConstOK E := by simp [success,LProg.ConstOK]; omega
  have hd : (dropBlock (0 : Fin 8) 1).ConstOK E := by
    simp [dropBlock,scan,moveTop,moveAll,clearP,LProg.ConstOK]
  exact ⟨SequentialWordMatchMachine.constOK E hE,⟨hs,hd⟩,
    by simp [moveAll,moveTop,LProg.ConstOK],by simp [moveAll,moveTop,LProg.ConstOK]⟩

end Shallot.MacroPeg.CBV.SequentialWordRestoreMachine
