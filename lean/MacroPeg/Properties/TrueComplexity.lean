import MacroPeg.Properties.QbfHard
import MacroPeg.Properties.Decide

/-!
# The complexity of first-order call-by-name Macro PEG recognition

* **Lower bound** (`QbfHard.lean`): the fixed first-order grammar `qbfG` decides TQBF under the polynomial-length
  encoding `enc` (`qbf_reduction`), so recognition is PSPACE-hard (TQBF is PSPACE-complete: an external fact).
* **Upper bound** (`Decide.lean`): recognition is decidable by `decideObs` (`decideObs_iff`), a fixpoint computation
  with at most `|rules| · (n+3)^((n+1)·K) · (n+1)` rounds (`iterBound_le`): exponential time.

This file joins the two: `qbfG` is first-order, so the decision procedure evaluates quantified Boolean formulas.
Whether first-order CBN Macro PEG recognition is EXPTIME-complete (or in PSPACE) is not settled here.
-/

namespace Shallot.MacroPeg

theorem qbfG_firstOrder : qbfG.FirstOrder := by
  intro r hr
  simp only [qbfG, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [qBody, mBody, clBody, tlBody, flBody, litBody, codeBody, andP, p0, p1, one, zero,
      MExp.FirstOrder, MExp.FirstOrderArgs]

theorem qbfStart_firstOrder : qbfStart.FirstOrder := by
  simp [qbfStart, qCall, cNum, asg, MExp.FirstOrder, MExp.FirstOrderArgs]

theorem qbfStart_closed : MExp.subst [] qbfStart = qbfStart := rfl

/-- The decision procedure, run on `qbfG`, evaluates quantified Boolean formulas. -/
theorem qbf_by_decision (q : List Bool) (m : QMatrix) :
    decideObs qbfG (enc q m) qbfStart = some (some []) ↔ qbfTrue q 0 [] m = true :=
  (decideObs_iff qbfG_firstOrder qbfStart_firstOrder qbfStart_closed _ _).trans (qbf_reduction q m)

end Shallot.MacroPeg
