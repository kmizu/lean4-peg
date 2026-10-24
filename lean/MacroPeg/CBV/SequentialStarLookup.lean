import Complexity.NTableLookup
import MacroPeg.CBV.SequentialStackCodecBound

/-! Resolve the source expression number of a repeated expression from the
number of its body using the fixed grammar's expression pool. -/
namespace Shallot.MacroPeg.CBV.SequentialStarLookup
open Complexity SequentialStackPool SequentialStackCodec CBVtoCBN

def table (ns : List CompileNode) : List Nat :=
  (exprPool ns).map (fun a => exprId ns (.star a))
def program {K : Nat} (i : Fin K) (ns : List CompileNode) : NProg K :=
  NTableLookup.program i (table ns)

theorem runs {K : Nat} (i : Fin K) (ns : List CompileNode) (a : MExp)
    (ha : ExprOK ns a) (S : Lists K) (l : List Nat) (hi : S i = l ++ [exprId ns a]) :
    NRuns (program i ns) S (S.set i (l ++ [exprId ns (.star a)])) (3 * (exprPool ns).length + 3) := by
  have hv : exprId ns a < (exprPool ns).length := List.idxOf_lt_length_iff.mpr ha.mem
  have htab : (table ns)[exprId ns a]'(by simpa [table] using hv) = exprId ns (.star a) := by
    simp only [table, List.getElem_map]
    have he : (exprPool ns)[exprId ns a]'hv = a := by
      apply Option.some.inj
      rw [← List.getElem?_eq_getElem hv]
      exact get_idxOf ha.mem
    rw [he]
  have hr := NTableLookup.runs i (table ns) (exprId ns a) (by simpa [table] using hv) S l hi
  rw [htab] at hr
  exact hr.mono (by have hstar : exprId ns (.star a) ≤ (exprPool ns).length := List.idxOf_le_length; omega)
end Shallot.MacroPeg.CBV.SequentialStarLookup
