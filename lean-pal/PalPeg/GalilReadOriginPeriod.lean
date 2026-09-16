import PalPeg.GalilScaffoldChainReadOrigin
import PalPeg.GalilPeriodUnion

/-!
# The input period read off at a terminal comparison

`ReadOrigin.reshift_palindrome` derives, halfway through its proof, that the
encoded word is `2*(interior.length+1)`-periodic on the whole stretch the
verifier has read since the origin — up to and including the mismatch place,
whose symbol still agrees with the chain prediction. That intermediate fact is
what the shift bookkeeping needs on its own, so it is extracted here.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open Manacher GalilScaffoldInputHead GalilScaffoldChainVerifier GalilScaffoldChainVerifyRun

namespace ReadOrigin

variable {raw : List (Fin 2)}

/-- At the terminal comparison of a round from origin `o`, the encoded word has
period `2*(o.interior.length+1)` on `(position o.start.verifier, position (right t.right)]`.
This is the periodicity half of `reshift_palindrome`, stated without the
palindrome conclusion. -/
theorem reshift_period (o : ReadOrigin raw)
    {s : OnlyCompareState} (extra : List (Fin 3))
    (hi : OnlyScan raw (o.center+(o.interior.length+1)) (o.radius+(o.interior.length+1))
      (2*(o.interior.length+1)) extra.length s.left s.right s.watch s.cycle)
    (ht : GalilScaffoldChainWatchTrace.Trace o.shifted.machine extra s.watch.machine)
    (hl : LeftMoves o.resumeLeft extra.length s.left)
    (hend : GalilScaffoldCounter.singlePositive s.cycle = true) (hc : canRight s.right)
    (hprediction : GalilScaffoldInputHead.read (right s.right) =
      GalilScaffoldChainConsume.symbol s.watch.machine.control.period.focus) :
    ∀ j, position o.start.machine.verifier < j →
      j+2*(o.interior.length+1) ≤ position (right s.right) →
      (encoded raw)[j]? = (encoded raw)[j+2*(o.interior.length+1)]? := by
  obtain ⟨_,hg,_,hb,a,_,htrace,_⟩ := o.reshift_compare extra hi ht hl hend hc hprediction
  have hperiod := o.joined_input_period (extra ++ [a]) htrace hb
  have hvpos := right_position s.watch.machine.verifier hg.1
    (represented_position _ raw hi.caught.verifierRep hi.caught.verifierPresent).1
  have hrpos := right_position s.right hc
    (represented_position _ raw hi.caught.scan.rightRep hi.caught.scan.rightPresent).1
  have hpos : position (consume s.watch.machine).verifier = position (right s.right) := by
    change position (right s.watch.machine.verifier) = _
    rw [hvpos,hrpos,hi.caught.aligned]
  intro j hj hj'
  refine hperiod j hj ?_
  rw [hpos]
  exact hj'

/-- `reshift_period` in `PeriodOn` form, ready for `periodOn_union`. -/
theorem reshift_periodOn (o : ReadOrigin raw)
    {s : OnlyCompareState} (extra : List (Fin 3))
    (hi : OnlyScan raw (o.center+(o.interior.length+1)) (o.radius+(o.interior.length+1))
      (2*(o.interior.length+1)) extra.length s.left s.right s.watch s.cycle)
    (ht : GalilScaffoldChainWatchTrace.Trace o.shifted.machine extra s.watch.machine)
    (hl : LeftMoves o.resumeLeft extra.length s.left)
    (hend : GalilScaffoldCounter.singlePositive s.cycle = true) (hc : canRight s.right)
    (hprediction : GalilScaffoldInputHead.read (right s.right) =
      GalilScaffoldChainConsume.symbol s.watch.machine.control.period.focus) :
    PeriodOn (encoded raw) (2*(o.interior.length+1))
      (position o.start.machine.verifier + 1) (position (right s.right)) := by
  intro i hia hib
  exact o.reshift_period extra hi ht hl hend hc hprediction i (by omega) hib

#print axioms reshift_period
#print axioms reshift_periodOn

end ReadOrigin
end PalPeg.GalilScaffoldChainInputSupply
