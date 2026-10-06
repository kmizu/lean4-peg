import MacroPeg.HigherOrder.KExp.Lay
import MacroPeg.HigherOrder.KExp.Extract
import MacroPeg.HigherOrder.KExp.LmTime
import Complexity.Univ.SimBound

/-!
# The steps of composing a reduction with a decider, in the length of the input

The composed machine lays out the reduction's table `tR` on the input, runs it for `cB1 n = cR·(n+1)^dR` steps,
reads the output back as an input (of length at most `cC1 n`), lays out the decider's table `tN`, and runs it for
`cB2 = tower j (cN·(m+1)^dN)` steps on the output of length `m`. `closeBoundN` adds the bounds of all stages.
-/

namespace Shallot.MacroPeg.KExp

open Complexity
open Complexity.Univ
open Shallot.MacroPeg.HO

/-- The steps the reduction runs. -/
def cB1 (cR dR n : Nat) : Nat := cR * (n + 1) ^ dR

/-- A bound on the size of the reduction's configuration, hence on the output's length. -/
def cC1 (tR : TTable) (cR dR n : Nat) : Nat := 2 + 2 * tR.k + 4 * n + cB1 cR dR n * growth tR

/-- The steps the decider runs on an output of length `m`. -/
def cB2 (j cN dN m : Nat) : Nat := tower j (cN * (m + 1) ^ dN)

/-- The steps of the composed machine on an input of length `n`. -/
def closeBoundN (tR tN : TTable) (j cR dR cN dN n : Nat) : Nat :=
  -- laying out and running the reduction
  (1000 * (n + tsz tR + cR + dR + 2) ^ 4 + 1000 * (cB1 cR dR n + 2) ^ 2) +
  (10 + cB1 cR dR n * (1000 * (tsz tR + cC1 tR cR dR n + cB1 cR dR n * growth tR + 2) ^ 4)) +
  -- reading the output back
  1000 * (tsz tR + 2 * cC1 tR cR dR n + 5) ^ 2 +
  -- laying out and running the decider
  (1000 * (cC1 tR cR dR n + tsz tN + cN + dN + 2) ^ 4 + 1000 * (cB2 j cN dN (cC1 tR cR dR n) + 2) ^ 2) +
  (10 + cB2 j cN dN (cC1 tR cR dR n) *
    (1000 * (tsz tN + (2 + 2 * tN.k + 4 * cC1 tR cR dR n) + cB2 j cN dN (cC1 tR cR dR n) * growth tN + 2) ^ 4)) +
  2

end Shallot.MacroPeg.KExp
