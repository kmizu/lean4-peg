import MacroPeg.HigherOrder.KExp.Close
import MacroPeg.HigherOrder.KExp.FixedReduce
import MacroPeg.HigherOrder.KExp.Upper

/-!
# The orders of higher-order Macro PEG form a strict hierarchy

The language of a fixed well-typed grammar of order `≤ j` is in j-EXPTIME on Turing machines (`mpeg_kexp`): it
reduces to the uniform problem, which is in j-EXPTIME, and j-EXPTIME is closed under reductions. Some language of
(j+1)-EXPTIME is not in j-EXPTIME (`kexp_strict`), and it reduces to a grammar of order `j+1` (`kexp_hard`).
That grammar's language is therefore no grammar's of order `≤ j` (`order_strict`).
-/

namespace Shallot.MacroPeg.KExp

open Complexity
open Shallot.MacroPeg.HO

/-- **A fixed grammar of order `≤ j` has a language in j-EXPTIME**, on Turing machines (`j ≥ 1`). -/
theorem mpeg_kexp {j : Nat} (hj : 1 ≤ j) {g : HGrammar} {s : HExp} (hw : g.WellTyped) (ho : GOrd j g s)
    (ht : HasTy g.types [] s .p) : KEXP j (MPEG g s) :=
  kexp_reduces hj (umpeg_kexp hj) (mpeg_reduces hw ho ht)

/-- **The orders form a strict hierarchy** (`j ≥ 1`): some well-typed grammar of order `j+1` with a closed start
parser has a language that no well-typed grammar of order `≤ j` with a closed start parser has. -/
theorem order_strict {j : Nat} (hj : 1 ≤ j) :
    ∃ (g : HGrammar) (s : HExp), g.WellTyped ∧ g.order = j + 1 ∧ HasTy g.types [] s .p ∧
      ∀ (g' : HGrammar) (s' : HExp), g'.WellTyped → GOrd j g' s' → HasTy g'.types [] s' .p →
        MPEG g s ≠ MPEG g' s' := by
  obtain ⟨L, hL, hnot⟩ := kexp_strict j
  obtain ⟨g, s, hw, ho, ht, hred⟩ := kexp_hard (j := j + 1) (by omega) hL
  refine ⟨g, s, hw, ho, ht, fun g' s' hw' ho' ht' heq => hnot ?_⟩
  rw [heq] at hred
  exact kexp_reduces hj (mpeg_kexp hj hw' ho' ht') hred

end Shallot.MacroPeg.KExp
