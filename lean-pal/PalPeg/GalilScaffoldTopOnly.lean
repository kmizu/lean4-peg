import PalPeg.GalilScaffoldTopInvStep

/-!
# The controller's matched comparisons as the lower layer's only-compare run

In `periodOnly` watch mode with the lag exhausted, a matched comparison of
the controller is `onlyCompareNext` on the projection `⟨center, left,
right, watch, cycle, radius⟩`: heads outward, the chain's immediate consume,
`cycle--`, `radius++`. Counting ticks leave the projection unchanged (the
chain's disabled tick is idle at lag zero). A sequence of such ticks with
`n` matched comparisons is therefore an `OnlyMatchedRun` of `n` steps —
the round structure `CompareRounds` is built from.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier

/-- The only-compare projection of a VM with a watching chain. -/
def toOnly (s : GalilVM) (w : GalilScaffoldChainWatch.State) : OnlyCompareState :=
  ⟨s.center, s.left, s.right, w, s.cycle, s.radius⟩

/-- At lag zero the enabled chain tick into a watching state is the
immediate consume. -/
theorem chainTick_true_immediate {w w' : GalilScaffoldChainWatch.State} (hz : zero w.lag = true)
    (h : ChainTick true (.watch w) (.watch w')) : w' = GalilScaffoldChainWatch.immediate w := by
  obtain ⟨m, hs, hm⟩ := h
  cases hs with
  | watchStep _ m' hi =>
    cases hi with
    | idle _ =>
      simp at hm
      cases hm with
      | watch _ _ ho =>
        cases ho with
        | queued hz' => rw [hz] at hz'; cases hz'
        | immediate _ _ => rfl
    | take hp _ =>
      rw [positive_of_zero hz] at hp; cases hp
  | watchBreak _ hb => have hp := hb.1; rw [positive_of_zero hz] at hp; cases hp

/-- At lag zero the disabled chain tick is idle. -/
theorem chainTick_false_idle {w : GalilScaffoldChainWatch.State} {z : ChainVM} (hz : zero w.lag = true)
    (h : ChainTick false (.watch w) z) : z = .watch w := by
  obtain ⟨m, hs, hm⟩ := h
  simp at hm
  subst hm
  cases hs with
  | watchStep _ m' hi =>
    cases hi with
    | idle _ => rfl
    | take hp _ => rw [positive_of_zero hz] at hp; cases hp
  | watchBreak _ hb => have hp := hb.1; rw [positive_of_zero hz] at hp; cases hp

/-- The matched comparison in `periodOnly` at lag zero is `onlyCompareNext`
on the projection. -/
theorem afterCompare_only (s : GalilVM) (w w' : GalilScaffoldChainWatch.State) (vs : ScanVM) (vq : SearchVM)
    (hp : s.periodOnly = true) (hs : s.chain = .watch w) (hz : zero w.lag = true)
    (hl : vs.left = left s.left) (hr : vs.right = right s.right) (hc : vs.chain = .watch w')
    (ht : ChainTick true s.chain vs.chain) :
    toOnly (afterCompare s vs vq) w' = onlyCompareNext (toOnly s w) := by
  rw [hs, hc] at ht
  have := chainTick_true_immediate hz ht
  subst this
  simp only [toOnly, afterCompare, onlyCompareNext, cycleAfter, radiusAfter, hp, ite_true]
  simp [searchLens, scanLens, hl, hr]

#print axioms afterCompare_only

end PalPeg.GalilScaffoldChainInputSupply
