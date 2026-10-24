import MacroPeg.CBV.SequentialTokenMatchMachine

namespace Shallot.MacroPeg.CBV.SequentialTokenInputMachine
open Complexity SequentialCursorEdit SequentialCursorEditMachine
open SequentialCaptureCopyMachine (characters)
open SequentialTokenMatchMachine (Test runTests)

def program (tests : List Test) : LProg 8 := .seq (.push 2 0)
  (.seq SequentialWordInputMachine.prepare (SequentialTokenMatchMachine.program tests))

def result (L : Lists 8) (ps : List Nat) (r : Option (List Char)) : Lists 8 :=
  SequentialParamMatchMachine.result L ps r

/-- Read only the original input and its compressed cursor. Source-fixed
predicates are executable guards, not tape buffers containing a literal. -/
theorem original_input_runs (tests : List Test) (x : List Char) (p : Nat) (ps : List Nat)
    (hchain : SequentialCursorChain.Chain p ps x.length) (hp : p ≤ x.length)
    (L : Lists 8) {B : Nat} (hcur : L 0=cursors (p :: ps)) (hx : L 6=characters x)
    (h1 : L 1=[]) (h5 : L 5=[]) (hL : LenOK B L) (hctrl : (L 2).length+3 ≤ B) :
    ∃ T, Runs (LenOK B) (program tests) L (result L ps (runTests tests (sfx x p))) T := by
  have hf := runs_push (i := (2 : Fin 8)) (e := 0) hL (by
    apply lenOK_set hL 2
    simpa using hctrl)
  let N := L.set 2 (L 2 ++ [0])
  let A := characters (x.take (x.length-p))
  let Q := sfx x p
  have hQ : Q.length=p := length_sfx x hp
  have hsplit : x=x.take (x.length-p) ++ Q := (List.take_append_drop _ x).symm
  have hin : N 6=A ++ characters Q := by
    change L 6= _
    rw [hx,hsplit]
    simp only [characters,List.map_append]
    rfl
  obtain ⟨Tp,hpRun⟩ := SequentialWordInputMachine.prepare_runs A (characters Q) ps N
    (by simpa [N,Lists.set,characters,hQ] using hcur) hin
    (by simpa [N,Lists.set] using h1) (by simpa [N,Lists.set] using h5) (end_fits hf)
  let M := (N.set 5 (characters Q).reverse).set 6 A
  obtain ⟨Tm,hm⟩ := SequentialTokenMatchMachine.match_runs tests Q ps x.length
    (by simpa only [hQ] using hchain) (L 2) A M rfl
    (by simpa [M,N,Lists.set,hQ] using hcur) rfl rfl
    (by simpa [M,N,Lists.set] using h1) (end_fits hpRun) (by
      have hh := hL 6
      rw [show L 6=A ++ characters Q from hin] at hh
      simpa only [List.length_append,characters,List.length_map] using hh)
  have he : SequentialTokenMatchMachine.result M (L 2) A ps Q (runTests tests Q)=
      result L ps (runTests tests Q) := by
    have hchars : A ++ characters Q=characters x := by
      rw [hsplit]
      simp only [characters,List.map_append]
      rfl
    funext j
    by_cases h0 : j=0 <;> by_cases h2 : j=2 <;> by_cases h5j : j=5 <;> by_cases h6 : j=6 <;>
      simp [SequentialTokenMatchMachine.result,result,SequentialParamMatchMachine.result,
        M,N,Lists.set,h0,h2,h5j,h6,h5,hx,hchars]
  rw [he] at hm
  exact ⟨_,hf.seq (hpRun.seq hm)⟩

theorem constOK (tests : List Test) (E : Nat) (hE : 2 ≤ E) : (program tests).ConstOK E := by
  have hp : SequentialWordInputMachine.prepare.ConstOK E := by
    simp [SequentialWordInputMachine.prepare,SequentialCaptureCopyMachine.transfer,
      SequentialCaptureCopyMachine.transferBody,moveAll,moveTop,skipP,LProg.ConstOK]
  exact ⟨by change 0 < E; omega,hp,SequentialTokenMatchMachine.constOK tests E hE⟩

end Shallot.MacroPeg.CBV.SequentialTokenInputMachine
