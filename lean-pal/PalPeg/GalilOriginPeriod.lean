import PalPeg.GalilReadOriginPeriod
import PalPeg.GalilPeriodSpan

/-!
# The input period already read at the origin, without any extension

`ReadOrigin.joined_input_period` states the periodicity of the encoded word
over everything the verifier has read since the origin, for an arbitrary
continuation `extra` of the watch run. Instantiating it at `extra = []` (the
empty trace) gives the periodicity of the stretch that the origin *already*
describes, namely `(position o.start.verifier, o.center + o.radius + 1]`, with
no extension at all. That degenerate instance is what the span lemmas
(`periodOn_span_of_next`) want as their `hright` hypothesis, so it is recorded
here in `PeriodOn` form, both on the full stretch and restricted to the right
half of the current span.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open Manacher GalilScaffoldInputHead GalilScaffoldChainVerifier GalilScaffoldChainVerifyRun

namespace ReadOrigin
variable {raw : List (Fin 2)}

/-- The shift run does not touch the verifier head, so the shifted machine sits
at the same input position as the watched one, i.e. at `o.center + o.radius + 1`. -/
theorem shifted_position (o : ReadOrigin raw) :
    position o.shifted.machine.verifier = o.center + o.radius + 1 := by
  rw [(chain_shift_values o.shiftRun).2.2.2.2.2.1]
  exact o.endPosition

/-- The shift run preserves the broken flag, so the shifted machine is unbroken. -/
theorem shifted_unbroken (o : ReadOrigin raw) :
    o.shifted.machine.control.broken = false :=
  (chain_shift_broken o.shiftRun).trans o.unbroken

/-- **The period already read at the origin.** Without extending the watch run
at all, the encoded word has period `2*(o.interior.length+1)` on the stretch
`(position o.start.verifier, position o.watched.verifier]`, whose right end is
`o.center + o.radius + 1` by `endPosition`. -/
theorem origin_period (o : ReadOrigin raw) :
    ∀ j, position o.start.machine.verifier < j →
      j + 2*(o.interior.length+1) ≤ o.center + o.radius + 1 →
      (encoded raw)[j]? = (encoded raw)[j+2*(o.interior.length+1)]? := by
  intro j hj hb
  refine o.joined_input_period [] (GalilScaffoldChainWatchTrace.empty _)
    o.shifted_unbroken j hj ?_
  rw [o.shifted_position]
  exact hb

/-- `origin_period` restated as a `PeriodOn` fact. -/
theorem origin_periodOn (o : ReadOrigin raw) :
    PeriodOn (encoded raw) (2*(o.interior.length+1))
      (position o.start.machine.verifier + 1) (o.center + o.radius + 1) := by
  intro i hi hb
  exact o.origin_period i (by omega) hb

/-- Restricted to the right half of the current span together with the new
place: this is exactly the `hright` hypothesis of `periodOn_span_of_next`.
(`PeriodOn.mono` is the same restriction lemma that `periodOn_restrict` wraps.) -/
theorem origin_periodOn_right (o : ReadOrigin raw) :
    PeriodOn (encoded raw) (2*(o.interior.length+1))
      (o.center + 1) (o.center + o.radius + 1) := by
  refine o.origin_periodOn.mono ?_ (le_refl _)
  have h := o.startBefore
  omega

#print axioms shifted_position
#print axioms shifted_unbroken
#print axioms origin_period
#print axioms origin_periodOn
#print axioms origin_periodOn_right

end ReadOrigin
end PalPeg.GalilScaffoldChainInputSupply
