import PalPeg.CloseoutMatchTickN

/-!
# The terminal match: what the machine actually does

The wiring question left open by `CloseoutMatchTickN` was *where does
`roundStepC_of_align`'s terminal-match case go*, since
`CloseoutWatchRound.TerminalC`'s four exits (fuel spent / shift guard / input
exhausted / `BreakEndC`) do not cover it — `BreakEndC` is the **mismatch** exit.

The spec answers it. `ScaffoldGalil.scala:254` `stepScan`:

```scala
chain.checkPair(left.read())
if (left.read() == right.read()) {
  matchedPlace()                                  // ← the outer symbols agree
} else if (!replaying && chain.canShift && chain.prediction() == right.read()) {
  beginChainShift()
} else {
  beginFallback()
}
```

and `matchedPlace()` (`:280`) only bumps `length` twice, calls `chain.matched()`
and pays the replay — **it does not end the scan**.  `ScaffoldChain.matched()`
(`ScaffoldChain.scala:156`) decrements `cycle` when `periodOnly` and, at zero
lag on a watching chain, calls `consume()` — which is exactly the consume that
fails at a terminal match.

So the terminal match does **not** stop the segment: it turns the watching chain
into a broken one and scanning continues; the machine restarts later, on the
broken chain (`Tick.restart`, whose source mode is `.scan`).  The Lean model
agrees: `GalilScaffoldTopChainVM.ChainMatched` has the constructor

```
| breaks (w w') (hb : BreakStep w w') : ChainMatched (.watch w) (.broken w')
```

`terminal_match_breaks` below is that step, machine-checked from the round.

**Consequences**

* `TerminalC` needs a fifth exit whose content is *the chain is no longer
  watching* — not a new obligation about the input, just the missing disjunct.
* For `hor`'s `InvSS` lift the path is already fine: after the break the machine
  restarts, and a restarted landing is `Restarted`, hence `Inv`, hence the
  `Inv` branch of `InvSS`.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutTerminalBreak

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRoundPeriod PalPeg.CloseoutPackRun31 PalPeg.CloseoutMatchTickN

/-- **The terminal match turns the watch into a broken chain.**  This is the
content of the fifth `TerminalC` exit: `ChainMatched.breaks` on the `BreakStep`
that `RoundScan.break_of_match` produces. -/
theorem terminal_match_breaks {raw : List (Fin 2)} {C R h used : ℕ} {s : GalilVM}
    {w0 : GalilScaffoldChainWatch.State}
    (hI : RoundScan raw C R h used s w0) (hav : canRight s.right)
    (hend : singlePositive s.cycle = true)
    (hmatch : read (GalilScaffoldInputHead.left s.left) = read (right s.right)) :
    ∃ w' : GalilScaffoldChainWatch.State,
      ChainMatched (ChainVM.watch w0) (ChainVM.broken w') := by
  obtain ⟨w', hb⟩ := break_at_terminal hI hav hend hmatch
  exact ⟨w', .breaks w0 w' hb⟩

/-- **So the chain at the target is not a watch.**  Which is why
`LiveScanWatch` fails there and the round structure has to stop. -/
theorem terminal_match_not_watch {raw : List (Fin 2)} {C R h used : ℕ} {s : GalilVM}
    {w0 : GalilScaffoldChainWatch.State} {z : ChainVM}
    (hI : RoundScan raw C R h used s w0) (hav : canRight s.right)
    (hend : singlePositive s.cycle = true)
    (hmatch : read (GalilScaffoldInputHead.left s.left) = read (right s.right))
    (hm : ChainMatched (ChainVM.watch w0) z) :
    ∀ w1 : GalilScaffoldChainWatch.State, z ≠ ChainVM.watch w1 := by
  intro w1 hz
  cases hm with
  | watch w w' ho =>
    exact PalPeg.CloseoutPackRun31.not_good_of_terminal_match hI hav hend hmatch
      (PalPeg.CloseoutPackRun31.outer_of_zero hI.caught.lagZero ho).1
  | breaks w w' hb => cases hz

#print axioms terminal_match_breaks
#print axioms terminal_match_not_watch

end PalPeg.CloseoutTerminalBreak
