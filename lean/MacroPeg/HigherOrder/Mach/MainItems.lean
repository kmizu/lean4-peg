import MacroPeg.HigherOrder.Mach.ItemDispatch
import MacroPeg.HigherOrder.Mach.ItemOps
import MacroPeg.HigherOrder.Mach.ItemLeaf
import MacroPeg.HigherOrder.Mach.ItemVRA
import MacroPeg.HigherOrder.Mach.Accepted

/-!
# One program for every item

`itemFullP` dispatches on the tag to the program of each kind of item. On an accepted reading, it does what
`stepT` says for every item of the bodies and the start (`itemFull_runs`), which is the hypothesis of the
evaluation stage.
-/

namespace Shallot.MacroPeg.Mach

open Complexity

/-- The program of one item, for every tag. -/
def itemFullP : NProg NK :=
  itemP itemLeafP itemSeqP itemAltP itemStarP itemNotP itemVarP itemRuleP itemLamP itemAppP

/-- Every item of an accepted reading runs as `stepT` says. -/
theorem itemFull_runs (j cap : Nat) {st : PSt} {R : List HO.Ty} {bis : List (List Flat.Item)}
    {is : List Flat.Item} {x : List Char} (hi : MInv st) (hr : ReadOK st R bis is x) :
    ∀ (Tf : List (List Nat)) (it : MItem), it ∈ st.bodies.flatten ++ st.start →
      ItemRunsC itemFullP j cap st Tf it 100 := by
  intro Tf it hit
  have hcur := read_ctx_le hr it hit
  have happ := read_app hr it hit
  exact itemP_runs
    (fun h => itemLeafP_runs j cap st Tf it h hcur)
    (fun h => itemSeqP_runs j cap st Tf it h hi.ct hcur)
    (fun h => itemAltP_runs j cap st Tf it h hi.ct hcur)
    (fun h => itemStarP_runs j cap st Tf it h hi.ct hcur)
    (fun h => itemNotP_runs j cap st Tf it h hi.ct hcur)
    (fun h => itemVarP_runs j cap st Tf it h hi.ct hcur)
    (fun h => itemRuleP_runs j cap st Tf it h hcur)
    (fun h => itemLamP_runs j cap st Tf it h hi.ct hcur)
    (fun h => itemAppP_runs j cap st Tf it h hcur (happ h).1 (happ h).2)

end Shallot.MacroPeg.Mach
