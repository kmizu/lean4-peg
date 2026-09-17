import PalPeg.CloseoutWatchRound2
import PalPeg.CloseoutShiftRun
import PalPeg.CloseoutPackRun31

/-!
# `LandingReadyC` at a round state

`CloseoutWatchRound2.roundStepC_of_align` (and `CloseoutTerminalN`'s
`roundStepC_of_alignN`) take

```
hland : ∀ (c : Control) (s : GalilVM), LiveScanWatch c s → LandingReadyC s
```

which is quantified over **every** live scan-watch state, while
`LandingReadyC s = canRight s.right ∧ ChainReady s.chain ∧
(∀ w, s.chain = .watch w → 0 ≤ value w.machine.control.distance)` contains
`canRight s.right` — a property of the states a run reaches, not of all states.
That is the same shape as `hpack`'s defect, so the hypothesis is not usable as
written.  (Whether it is *false* is not checked here and is not claimed.)

This file derives `LandingReadyC` from **round data**, i.e. from facts that are
carried:

* `canRight s.right` — the caller's own (`Extra7.scanAvail` in the run pack);
* `ChainReady (.watch w)` — its three clauses at a round state:
  1. `positive w.lag = true → Good w` is **vacuous**, because
     `RoundScan.caught.lagZero` gives `zero w.lag = true` and hence
     `positive w.lag = false`;
  2. `WatchBlock w` **is** `BlockInv (.watch w)` (`GalilBranchInvariants:429`),
     which is `Coupled.block`, a field of `AuxPack.coupled`;
  3. `∀ m, Internal w m → canRight m.machine.verifier` collapses at zero lag —
     `CloseoutPackRun31.internal_of_zero` forces `m = w` — to
     `canRight w.machine.verifier`, which follows from `canRight s.right` plus
     `CaughtScan.aligned` (the verifier sits at the right head) and the
     verifier's representation, via `GalilEndOfInput.not_canRight_iff`.
* `0 ≤ value w.machine.control.distance` — taken as an input here; see the note
  at the end.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false

namespace PalPeg.CloseoutLandingRound

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton PalPeg.GalilBranchInvariants
open PalPeg.GalilTickFun (ChainReady)
open PalPeg.CloseoutPackRun31 PalPeg.CloseoutWatchRound2

/-- **The chain's verifier can move, at a round state.**  It sits exactly where
the scan's right head is (`CaughtScan.aligned`), and the right head can move. -/
theorem canRight_verifier_of_round {raw : List (Fin 2)} {C R h used : ℕ} {s : GalilVM}
    {w0 : GalilScaffoldChainWatch.State}
    (hI : PalPeg.GalilRoundPeriod.RoundScan raw C R h used s w0)
    (hav : canRight s.right) : canRight w0.machine.verifier := by
  by_contra hc
  have hend : position w0.machine.verifier = 2 * raw.length :=
    (PalPeg.GalilEndOfInput.not_canRight_iff _ raw hI.caught.verifierRep
      hI.caught.verifierPresent).1 hc
  have halign : position w0.machine.verifier = position s.right := hI.caught.aligned
  have hb : position s.right ≤ 2 * raw.length :=
    PalPeg.GalilEndOfInput.position_le _ raw hI.caught.scan.rightRep
  have hne : ¬ canRight s.right := by
    rw [PalPeg.GalilEndOfInput.not_canRight_iff _ raw hI.caught.scan.rightRep
      hI.caught.scan.rightPresent]
    omega
  exact hne hav

/-- **`ChainReady` at a round state.**  All three clauses come from the round
plus the block invariant. -/
theorem chainReady_of_round {raw : List (Fin 2)} {C R h used : ℕ} {s : GalilVM}
    {w0 : GalilScaffoldChainWatch.State}
    (hI : PalPeg.GalilRoundPeriod.RoundScan raw C R h used s w0)
    (hblk : BlockInv s.chain) (hav : canRight s.right) :
    ChainReady s.chain := by
  rw [hI.chain]
  refine ⟨fun hp => ?_, ?_, fun m hm => ?_⟩
  · rw [positive_eq_false_of_zero hI.caught.lagZero] at hp; cases hp
  · have hb : BlockInv (ChainVM.watch w0) := by rw [← hI.chain]; exact hblk
    exact hb
  · rw [internal_of_zero hI.caught.lagZero hm]
    exact canRight_verifier_of_round hI hav

/-- **`LandingReadyC` from the round.**  The `distance` floor is the one input
that the round itself does not carry. -/
theorem landingReadyC_of_round {raw : List (Fin 2)} {C R h used : ℕ} {s : GalilVM}
    {w0 : GalilScaffoldChainWatch.State}
    (hI : PalPeg.GalilRoundPeriod.RoundScan raw C R h used s w0)
    (hblk : BlockInv s.chain) (hav : canRight s.right)
    (hdist : 0 ≤ value w0.machine.control.distance) :
    LandingReadyC s := by
  refine ⟨hav, chainReady_of_round hI hblk hav, fun w hw => ?_⟩
  have : w = w0 := by rw [hI.chain] at hw; cases hw; rfl
  rw [this]; exact hdist

#print axioms canRight_verifier_of_round
#print axioms chainReady_of_round
#print axioms landingReadyC_of_round

end PalPeg.CloseoutLandingRound
