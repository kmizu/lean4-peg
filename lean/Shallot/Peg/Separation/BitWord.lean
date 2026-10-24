import MacroPeg.Syntax

namespace Shallot.PegSeparation

/-- The ordinary binary alphabet: one a/b character per bit. -/
def bitWord (w : List Bool) : List Char := w.map (fun b => if b then 'b' else 'a')

end Shallot.PegSeparation
