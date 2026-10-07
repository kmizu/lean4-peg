import Shallot.Peg.Undecidable.FordCor
import Shallot.Peg.Undecidable.Bin
import Complexity.Undec.K1Defs
import Complexity.Undec.TMSR
import Complexity.Undec.SRMPCP
import Complexity.Undec.MPCP
import MacroPeg.HigherOrder.KExp.DiagRows

/-!
# From a one-tape table to Ford's grammar

For the code `w` of a one-tape table `T`, the chain of reductions gives Ford's grammar `k1Grammar w`:
`T`'s acceptance of `w` (`tm_sr`) → string rewriting (`sr_mpcp`) → the modified correspondence problem
(`mpcp_pcp`) → the correspondence problem over numbers (`pcpN_pcp`) → over bits → Ford's grammar (`ford_iff`).
Other inputs go to the grammar of the empty language. So `K1 w` holds iff the language of `k1Grammar w` is nonempty
(`k1_grammar`).
-/

namespace Shallot

open Complexity
open Complexity.Univ
open Complexity.Undec

/-- The correspondence instance over numbers of a one-tape table on an input. -/
def tablePCPN (T : TTable) (w : List Bool) : List Card :=
  mpcpToPCP (srFirst (tmStart T w) (tmSyms T)) (srCards (tmSRS T) (tmAcc T) (tmSyms T)) (tmSyms T + 2)

/-- **The grammar of an input**: Ford's grammar of its table's instance, or the empty language. -/
def k1Grammar (w : List Bool) : Grammar :=
  match deUnary w with
  | 1 :: nq :: na :: rest => if rest.length % 3 = 0 then fordG (toPCP (tablePCPN (table1 nq na rest) w)) else emptyG
  | _ => emptyG

/-- The table of whole chunks writes and moves on one tape. -/
theorem table1_rowsOK {nq na : Nat} {rest : List Nat} (h : rest.length % 3 = 0) : RowsOK (table1 nq na rest) :=
  Shallot.MacroPeg.KExp.tableOfNums_rowsOK (k := 1) h

/-- A one-tape table accepts `w` iff Ford's grammar of its instance has a nonempty language. -/
theorem table_ford (T : TTable) (hT : RowsOK T) (hk : T.k = 1) (w : List Bool) :
    (∃ t, (frun T (finit 1 w) t).state = 0) ↔ ∃ v, Accepts (fordG (toPCP (tablePCPN T w))) v := by
  have hb := srCards_below (tmSRS T) (tmStart T w) (tmAcc T) (tmSyms T) (tmSRS_below T) (tmStart_below T w)
    (tmAcc_below T)
  have hne := srCards_nonempty (tmSRS T) (tmStart T w) (tmAcc T) (tmSyms T) (tmSRS_nonempty T)
  rw [tm_sr T hT hk w,
    sr_mpcp _ _ _ _ (tmSRS_below T) (tmSRS_nonempty T) (tmStart_below T w) (tmAcc_below T),
    mpcp_pcp _ _ _ hb hne, pcpN_pcp]
  exact (ford_iff (toPCP_nonempty (mpcpToPCP_nonempty _ _ _ hne))).symm

/-- **`K1` holds iff the language of `k1Grammar` is nonempty.** -/
theorem k1_grammar (w : List Bool) : K1 w ↔ ∃ v, Accepts (k1Grammar w) v := by
  unfold K1 k1Grammar
  split
  next nq na rest heq =>
    rw [heq]
    by_cases hm : rest.length % 3 = 0
    · simp only [hm, true_and, if_true]
      exact table_ford _ (table1_rowsOK hm) rfl w
    · simp only [hm, false_and, if_false, false_iff]
      rintro ⟨v, hv⟩; exact emptyG_not v hv
  next h =>
    split
    next nq na rest heq => exact absurd heq (h nq na rest)
    next =>
      simp only [false_iff]
      rintro ⟨v, hv⟩; exact emptyG_not v hv

end Shallot
