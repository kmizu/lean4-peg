import PalPeg.CloseoutWatchRound
import PalPeg.CloseoutWatchPhase2

/-!
# Round 16: the `BreakEndC` → fallback route is blocked, and why

Round 15's header listed, as the last missing piece of the three-way exit split
(`ExitSplit3C`: shift / matched chain break / **outer mismatch**), a `FoundExit`
route from a post-rounds `BreakEndC` landing back to
`CloseoutPrepInputs3.FallbackRouteG`, and named the obstruction as

> `FallbackRouteLP` asks for `PrepChain s1.chain`, and no lemma in the tree
> derives `PrepChain` from `s.chain = ChainVM.watch w`.

This round settles that item **negatively, and exactly**: no lemma derives it
because the implication is *false*, and the suggested repair (take one
`Tick.scan_fallback` step first, so that the chain becomes a `.copy`) does not
apply, because `FallbackRouteLP` demands `PrepChain` at the mismatch landing
`s1` itself — the state *before* the fallback tick — not at the state the
fallback tick lands in.

## What is proved here (unconditionally, no `sorry`)

`breakEnd_fallback_vacuous` — at every `BreakEndC` landing the hypothesis
`GalilPrepMatch.PrepChain s1.chain` of `CloseoutWatchPhase2.FallbackRouteLP`
is **false**: `BreakEndC` carries `LiveScanWatch c1 s1`, hence
`s1.chain = ChainVM.watch w`, while `PrepChain` is by definition a `.copy` or a
`.back` with positive lag.  So `FallbackRouteLP` applied at a `BreakEndC`
landing yields nothing: it is not merely unproved at that landing, it is
inapplicable there.

## Consequence for `ExitSplit3C` / `foundExit_compare_final9`

`foundExit_compare_final9` is therefore **not** constructed in this round.
**Missing fact (one sentence):** a fallback-route contract whose `PrepChain`
hypothesis is replaced by "`s1.chain` is a `.watch`, or `PrepChain s1.chain`"
— i.e. a `FallbackRouteLP`/`FallbackRouteG` variant admitting a *watching*
chain at the mismatch landing, which would have to be re-proved from
`GalilPrepMatch` upward (`prep_guard_false_afterMismatch` and the mismatch
route both consume `PrepChain` at that state), and which no file in the tree
states.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace PalPeg.CloseoutWatchRound16

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.CloseoutContracts
open PalPeg.GalilRunSkeleton
open PalPeg.CloseoutWatchRun (LiveScanWatch)
open PalPeg.CloseoutWatchRound (BreakEndC)

/-- **The blocked leaf, stated positively.**  At a `BreakEndC` landing the
chain is a `.watch`, so the `PrepChain` premise of
`CloseoutWatchPhase2.FallbackRouteLP` cannot hold there: routing an
outer-mismatch exit of the watch phase through the prep-time fallback is
impossible with the contracts as stated. -/
theorem breakEnd_fallback_vacuous {P : Shared} {q : ℕ} {first : Fin 9}
    {c : Control} {s : GalilVM} (hbe : BreakEndC P q first c s) :
    ∃ (c1 : Control) (s1 : GalilVM),
      WatchSeg P q first 2048 c s c1 s1 ∧ c1.clock = 1 ∧ LiveScanWatch c1 s1 ∧
        read (left s1.left) ≠ read (right s1.right) ∧
        ¬ GalilPrepMatch.PrepChain s1.chain := by
  obtain ⟨c1, s1, hseg, hclk, hlive, hne⟩ := hbe
  refine ⟨c1, s1, hseg, hclk, hlive, hne, ?_⟩
  obtain ⟨-, -, -, w, hw⟩ := hlive
  intro hpc
  rcases hpc with ⟨_, _, _, _, _, _, _, hx, -⟩ | ⟨_, _, _, _, _, hx, -⟩ <;>
    · rw [hw] at hx; exact ChainVM.noConfusion hx

end PalPeg.CloseoutWatchRound16

#print axioms PalPeg.CloseoutWatchRound16.breakEnd_fallback_vacuous
