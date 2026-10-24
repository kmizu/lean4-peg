import MacroPeg.CBV.SequentialWordRestoreMachine

/-! A selected captured word is matched against the actual original input.
The current compressed cursor locates the suffix; no decoded position or
input substring is passed to the fixed executable program. -/
namespace Shallot.MacroPeg.CBV.SequentialWordInputMachine
open Complexity SequentialCursorEdit SequentialCursorEditMachine
open SequentialCaptureCopyMachine (characters)

def prepare : LProg 8 := .seq (SequentialCaptureCopyMachine.transfer false) (moveAll 1 0)
def program : LProg 8 := .seq prepare SequentialWordRestoreMachine.program

theorem prepare_runs (A Q : List Nat) (ps : List Nat) (L : Lists 8) {B : Nat}
    (hcur : L 0 = cursors (Q.length :: ps)) (hx : L 6 = A ++ Q)
    (h1 : L 1 = []) (h5 : L 5 = []) (hL : LenOK B L) :
    ∃ T, Runs (LenOK B) prepare L ((L.set 5 Q.reverse).set 6 A) T := by
  let C := blocks (SequentialCursorChain.deltas Q.length ps) ++ [0]
  have h0 : L 0 = C ++ unary Q.length := by simpa only [C,cursors_cons] using hcur
  have hc := hL 0
  rw [h0] at hc
  have hi := hL 6
  rw [hx] at hi
  simp only [List.length_append,List.length_replicate] at hc hi
  obtain ⟨Tt,ht⟩ := SequentialCaptureCopyMachine.transfer_runs false C A Q L h0
    (by rw [show C=blocks (SequentialCursorChain.deltas Q.length ps) ++ [0] from rfl,lastSym_append]; rfl)
    hx hL (by simp [h1]; omega) (by simp [h5]; omega) (by intro hh; contradiction)
  let M := (((((L.set 0 C).set 1 (unary Q.length)).set 6 A).set 5 Q.reverse).set 4 (L 4))
  have heM : (((((L.set 0 C).set 1 (L 1 ++ unary Q.length)).set 6 A).set 5
      (L 5 ++ Q.reverse)).set 4 (SequentialCaptureCopyMachine.destination false (L 4) Q)) = M := by
    simp [M,h1,h5,SequentialCaptureCopyMachine.destination]
  rw [heM] at ht
  have hr := moveAll_runs_bounded (src := (1 : Fin 8)) (dst := 0) (by decide) (end_fits ht)
    (by simpa [M,Lists.set] using hc)
  have he : (M.set 0 (M 0 ++ (M 1).reverse)).set 1 [] = (L.set 5 Q.reverse).set 6 A := by
    have hu : (unary Q.length).reverse=unary Q.length := by simp
    funext j
    by_cases h0j : j=0 <;> by_cases h1j : j=1 <;> by_cases h4j : j=4 <;>
      by_cases h5j : j=5 <;> by_cases h6j : j=6 <;>
      simp_all [M,Lists.set]
  rw [he] at hr
  exact ⟨_,ht.seq hr⟩

def result (L : Lists 8) (C tail P : List Nat) (ps : List Nat) (w x : List Char)
    (r : Option (List Char)) : Lists 8 :=
  ((((((L.set 2 (C ++ [if r.isSome then 1 else 0])).set 0
    (cursors ((r.map List.length).toList ++ ps))).set 4
      (tail ++ [0] ++ (characters w).reverse ++ P.reverse)).set 7 []).set 5 []).set 6 (characters x))

/-- An original-input prefix test with exact `stripPrefix?` semantics. The
capture and input are restored and all scratch tapes are empty afterwards. -/
theorem original_input_runs (x w : List Char) (p : Nat) (ps : List Nat)
    (hchain : SequentialCursorChain.Chain p ps x.length) (hp : p ≤ x.length)
    (C tail P : List Nat) (L : Lists 8) {B : Nat}
    (hflag : L 2 = C ++ [1]) (hcur : L 0 = cursors (p :: ps))
    (hw : L 4 = tail ++ [0] ++ (characters w).reverse) (hx : L 6 = characters x)
    (hP : L 7 = P) (h1 : L 1 = []) (h5 : L 5 = []) (hL : LenOK B L)
    (hword : tail.length+1+w.length+P.length+2 ≤ B) :
    ∃ T, Runs (LenOK B) program L
      (result L C tail P ps w x (Shallot.stripPrefix? w (sfx x p))) T := by
  let A := characters (x.take (x.length-p))
  let Q := sfx x p
  have hQ : Q.length=p := length_sfx x hp
  have hsplit : x=x.take (x.length-p) ++ Q := (List.take_append_drop _ x).symm
  have hin : L 6=A ++ characters Q := by
    rw [hx,hsplit]
    simp only [characters,List.map_append]
    rfl
  obtain ⟨Tp,hpRun⟩ := prepare_runs A (characters Q) ps L
    (by simpa only [characters,List.length_map,hQ] using hcur) hin h1 h5 hL
  let M := (L.set 5 (characters Q).reverse).set 6 A
  have hM : LenOK B M := end_fits hpRun
  obtain ⟨U,wr,xr,trace⟩ := SequentialWordMatchMachine.trace_exists w Q
  obtain ⟨Tm,hm⟩ := SequentialWordRestoreMachine.match_runs trace ps x.length
    (by simpa only [hQ] using hchain) C tail A P M
    (by simpa [M,Lists.set] using hflag) (by simpa [M,Lists.set,hQ] using hcur)
    (by simpa [M,Lists.set] using hw) rfl rfl (by simpa [M,Lists.set] using hP)
    (by simpa [M,Lists.set] using h1) hM hword (by
      have hh := hL 6
      rw [hin] at hh
      simpa only [List.length_append,characters,List.length_map] using hh)
  have he : SequentialWordRestoreMachine.result M C tail A P ps w Q wr xr =
      result L C tail P ps w x (Shallot.stripPrefix? w Q) := by
    rw [trace.stripPrefix]
    have hchars : A ++ characters Q = characters x := by
      rw [hsplit]
      simp only [characters,List.map_append]
      rfl
    funext j
    by_cases h0 : j=0 <;> by_cases h2 : j=2 <;> by_cases h4 : j=4 <;>
      by_cases h5j : j=5 <;> by_cases h6 : j=6 <;> by_cases h7 : j=7 <;>
      by_cases hs : wr=[] <;>
      simp [SequentialWordRestoreMachine.result,result,M,Lists.set,h0,h2,h4,h5j,h6,h7,hs,hchars]
  rw [he] at hm
  exact ⟨_,hpRun.seq hm⟩


theorem constOK (E : Nat) (hE : 2 ≤ E) : program.ConstOK E := by
  have hp : prepare.ConstOK E := by
    simp [prepare,SequentialCaptureCopyMachine.transfer,SequentialCaptureCopyMachine.transferBody,
      moveTop,moveAll,skipP,LProg.ConstOK]
  exact ⟨hp,SequentialWordRestoreMachine.constOK E hE⟩

end Shallot.MacroPeg.CBV.SequentialWordInputMachine
