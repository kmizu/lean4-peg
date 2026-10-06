import MacroPeg.HigherOrder.KExp.FixedMap

/-!
# A fixed grammar reduces to the uniform problem

For a well-typed grammar of order `≤ j` with a closed start parser, putting its code before the input is a
polynomial-time reduction of its language to `UMPEG j` (`mpeg_reduces`).
-/

namespace Shallot.MacroPeg.KExp

open Complexity
open Shallot.MacroPeg.HO

theorem mpeg_reduces {j : Nat} {g : HGrammar} {s : HExp} (hw : g.WellTyped) (ho : GOrd j g s)
    (ht : HasTy g.types [] s .p) : Reduces (MPEG g s) (UMPEG j) :=
  ⟨fixedMap g s, fixedMap_polytime g s, fun w => by
    rw [fixedMap, umpeg_toBits]
    exact ⟨fun h => ⟨hw, ho, ht, h⟩, fun h => h.2.2.2⟩⟩

end Shallot.MacroPeg.KExp
