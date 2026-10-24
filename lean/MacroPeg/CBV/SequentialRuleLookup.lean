import Complexity.NTableLookup
import MacroPeg.CBV.SequentialStackCodecBound
import MacroPeg.Properties.Specialize

/-! Resolve a rule number into its body expression number in the fixed grammar. -/
namespace Shallot.MacroPeg.CBV.SequentialRuleLookup
open Complexity SequentialStackCodec SequentialStackPool CBVtoCBN

def table (ns : List CompileNode) (g : MGrammar) : List Nat := g.rules.map (fun r => exprId ns r.body)
def program {K : Nat} (i : Fin K) (ns : List CompileNode) (g : MGrammar) : NProg K :=
  NTableLookup.program i (table ns g)

theorem exists_rule (g : MGrammar) (i : Nat) (hi : i < g.rules.length) :
    ∃ r, ruleAtM g.rules i = some r := by
  exact ⟨g.rules[i],by rw [ruleAtM_eq_getElem?,List.getElem?_eq_getElem hi]⟩

theorem runs {K : Nat} (j : Fin K) (ns : List CompileNode) (g : MGrammar) (i : Nat) (r : MRule)
    (hr : ruleAtM g.rules i = some r) (S : Lists K) (l : List Nat) (hj : S j = l ++ [i]) :
    NRuns (program j ns g) S (S.set j (l ++ [exprId ns r.body]))
      (2 * g.rules.length + (exprPool ns).length + 3) := by
  have hi := CBV.ruleAtM_lt hr
  have hget : g.rules[i]'hi = r := by
    apply Option.some.inj
    rw [← List.getElem?_eq_getElem hi,← ruleAtM_eq_getElem?]
    exact hr
  have ht : (table ns g)[i]'(by simpa [table] using hi) = exprId ns r.body := by
    simp [table,hget]
  have hrun := NTableLookup.runs j (table ns g) i (by simpa [table] using hi) S l hj
  rw [ht] at hrun
  exact hrun.mono (by have hh : exprId ns r.body ≤ (exprPool ns).length := List.idxOf_le_length; omega)
end Shallot.MacroPeg.CBV.SequentialRuleLookup
