import MacroPeg.CBV.SequentialEightTapeMachine

/-! Inspect the actual difference between the first two retained cursors.
The complete cursor stream is restored before either continuation runs. -/
namespace Shallot.MacroPeg.CBV.SequentialCursorProgressMachine
open Complexity SequentialCursorEdit SequentialCursorEditMachine SequentialControlEditMachine

def program (progress equal : LProg 8) : LProg 8 := .seq (saveMany 0 1 1)
  (.ite 0 (symIs 1) (.seq (moveAll 1 0) progress) (.seq (moveAll 1 0) equal))

theorem gap_test (d : Nat) (ds : List Nat) :
    symIs 1 (lastSym (blocks (d :: ds)))=decide (0<d) := by
  cases d with
  | zero => simp [blocks_cons,lastSym_append,symIs]
  | succ d => simp [blocks_cons,List.replicate_succ',← List.append_assoc,lastSym_append,symIs]

/-- Positions are specification variables only. The executable discriminator
reads one bit of their difference block after saving the current cursor. -/
theorem dispatch_runs (progress equal : LProg 8) (q p : Nat) (ps : List Nat)
    (L M : Lists 8) {B T : Nat} (hcur : L 0=cursors (q :: p :: ps)) (h1 : L 1=[])
    (hL : LenOK B L) (hp : Runs (LenOK B) (if q<p then progress else equal) L M T) :
    ∃ U, Runs (LenOK B) (program progress equal) L M U := by
  let S := blocks (SequentialCursorChain.deltas q (p :: ps))
  have hsrc : L 0=S ++ blocks [q] := by
    rw [hcur,cursors_cons]
    simp only [blocks_cons q [],show blocks []=[] from rfl,List.nil_append]
    simp only [S,List.append_assoc]
  have hh := hL 0
  rw [hsrc] at hh
  simp only [List.length_append] at hh
  obtain ⟨Ts,hs⟩ := saveMany_runs (src := (0 : Fin 8)) (tmp := 1) (by decide) [q] S L hsrc hL
    (by simp only [h1,List.length_nil]; omega)
  let N := (L.set 0 S).set 1 (blocks [q]).reverse
  have heN : (L.set 0 S).set 1 (L 1 ++ (blocks [q]).reverse)=N := by simp [N,h1]
  rw [heN] at hs
  have hr := moveAll_runs_bounded (src := (1 : Fin 8)) (dst := 0) (by decide) (end_fits hs)
    (by simpa [N,Lists.set] using hh)
  have he : (N.set 0 (N 0 ++ (N 1).reverse)).set 1 []=L := by
    funext j
    by_cases h0 : j=0 <;> by_cases h1j : j=1 <;> simp_all [N,Lists.set]
  rw [he] at hr
  have hg : symIs 1 (lastSym (N 0))=decide (q<p) := by
    change symIs 1 (lastSym S)=_
    rw [show S=blocks ((p-q) :: SequentialCursorChain.deltas p ps) from rfl,gap_test]
    simp only [Nat.sub_pos_iff_lt]
  by_cases hlt : q<p
  · have ht : Runs (LenOK B) progress L M T := by simpa only [if_pos hlt] using hp
    exact ⟨_,hs.seq ((hr.seq ht).iteT (end_fits hs) (by simpa [hlt] using hg))⟩
  · have ht : Runs (LenOK B) equal L M T := by simpa only [if_neg hlt] using hp
    exact ⟨_,hs.seq ((hr.seq ht).iteF (end_fits hs) (by simpa [hlt] using hg))⟩

theorem constOK (progress equal : LProg 8) (E : Nat) (hp : progress.ConstOK E) (he : equal.ConstOK E) :
    (program progress equal).ConstOK E := by
  simp [program,saveMany,moveBlock,scan,moveTop,moveAll,skipP,LProg.ConstOK,hp,he]

end Shallot.MacroPeg.CBV.SequentialCursorProgressMachine
