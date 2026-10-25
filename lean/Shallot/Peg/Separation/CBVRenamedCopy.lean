import MacroPeg.CBV.RenamedCopy
import Shallot.Peg.Separation.CBVStrict

namespace Shallot.PegSeparation

open Shallot.MacroPeg

/-- A concrete language over the original five symbols. Seq membership or
nonmembership is not asserted here. -/
theorem renamed_copy_isPar :
    IsFirstOrderCBVPEL .callByValuePar CBV.RenamedCopy.Language :=
  ⟨CBV.RenamedCopy.grammar, CBV.RenamedCopy.start,
    CBV.RenamedCopy.grammar_firstOrder, CBV.RenamedCopy.start_firstOrder,
    fun x => (CBV.RenamedCopy.recognizes x).symm⟩

end Shallot.PegSeparation
