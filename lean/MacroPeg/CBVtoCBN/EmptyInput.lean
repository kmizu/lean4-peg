import MacroPeg.CBVtoCBN.SpanValues

namespace Shallot.MacroPeg.CBVtoCBN

/-- A source-dependent constant branch decides acceptance of the empty input at translation time. -/
def emptyInputP (source : MGrammar) (s : Strategy) (e : MExp) : MExp :=
  if decideObsV s source [] e = some (some []) then .notP .any else MExp.failAlways

theorem emptyInputP_firstOrder (source : MGrammar) (s : Strategy) (e : MExp) :
    (emptyInputP source s e).FirstOrder := by
  unfold emptyInputP
  split <;> trivial

/-- The constant branch is total and rejects every nonempty original input. -/
theorem emptyInputP_obs (target source : MGrammar) (s : Strategy) (e : MExp) (x : List Char) :
    MacroObs target (emptyInputP source s e) x
      (if x = [] ∧ decideObsV s source [] e = some (some []) then some x else none) := by
  unfold emptyInputP
  by_cases he : decideObsV s source [] e = some (some [])
  · rw [if_pos he]
    cases x with
    | nil => simpa only [he, and_self, if_true] using obs_not_none (g := target) obs_any_nil
    | cons c cs =>
      simpa only [List.cons_ne_nil, false_and, if_false] using
        obs_not_some (g := target) (obs_any_some c cs)
  · rw [if_neg he]
    simpa only [he, and_false, if_false, MExp.failAlways] using obs_not_some (g := target) (obs_eps x)

/-- Empty-input recognition is translated for either first-order CBV strategy, with no padding or encoding.
Only acceptance is represented here; a source computation without a finite observation is rejected. -/
theorem emptyInputP_correct (target : MGrammar) {source : MGrammar} (hg : source.FirstOrder)
    {s : Strategy} (hs : s ≠ .callByName) {e : MExp} (he : e.FirstOrder) (x : List Char) :
    MacroObs target (emptyInputP source s e) x (some []) ↔
      x = [] ∧ SObs source s e [] (some []) := by
  have h := obs_unique_iff (emptyInputP_obs target source s e x) (some [])
  rw [h]
  by_cases hx : x = []
  · subst x
    simp only [true_and]
    rw [← decideObsV_iff hg hs he [] (some [])]
    split <;> simp_all
  · simp only [hx, false_and, if_false, Option.some_ne_none]

end Shallot.MacroPeg.CBVtoCBN
