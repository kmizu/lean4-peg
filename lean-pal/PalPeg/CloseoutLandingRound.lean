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

/-! ## `0 ≤ value distance`: 参照 run については出る、実 chain については出ない

`GalilScaffoldChainRestart.Ordered s := value s.last ≤ value s.boundary ∧
value s.boundary ≤ value s.distance` で、`run_order` は `Ordered` の保存と
**`last` の単調性**（`value s.last ≤ value (run s xs).last`）を同時に返す。
`GalilScaffoldChainConsume.ready` は 3 counter すべて `reset`（値 `0`）なので、
参照 run では `0 ≤ value last ≤ value boundary ≤ value distance` が出る。 -/
theorem distance_nonneg_of_run (token boundary : Fin 3) (xs pre : List (Fin 3)) :
    0 ≤ value (GalilScaffoldChainSweep.run
      (GalilScaffoldChainConsume.ready token xs boundary) pre).distance := by
  have hinit : PalPeg.GalilScaffoldChainRestart.Ordered
      (GalilScaffoldChainConsume.ready token xs boundary) := by
    simp [PalPeg.GalilScaffoldChainRestart.Ordered,
      GalilScaffoldChainConsume.ready, GalilScaffoldCounter.reset, value]
  have hlast0 : value (GalilScaffoldChainConsume.ready token xs boundary).last = 0 := by
    simp [GalilScaffoldChainConsume.ready, GalilScaffoldCounter.reset, value]
  obtain ⟨hord, hmono⟩ :=
    PalPeg.GalilScaffoldChainRestart.run_order
      (GalilScaffoldChainConsume.ready token xs boundary) pre hinit
  rw [hlast0] at hmono
  exact le_trans hmono (le_trans hord.1 hord.2)

/-! **ここで止まる。**  `CloseoutSweptOff.SweptOff` が与えるのは
`Offset k w.machine.control d`（`d` は上の参照 run）であり、`Offset` は 3 counter が
定数 `k` だけずれることを言う。`ReadOrigin.offset` の `k` は
`(shifts * (interior.length+1) : ℕ)` で**非負**なので、
`value w.machine.control.distance = value d.distance - k` は**負になり得る**。
実 chain の `distance` 非負は shift guard（`4h ≤ distance` を shift 前に要求する）に
結びついた run の事実であり、**その供給元は本監査では特定できていない**。
「無い」とは書かない。 -/

/-! ## `0 ≤ value distance` は `SumRel` で半径の非負性に落ちる

`GalilChainCoupling.SumRel (.watch w) R := w.machine.control.broken = false →
value w.machine.control.distance + value w.lag = R`（`GalilChainCoupling:193`）で、
`AuxPack.coupled.sum` が `R := value s.radius` でそれを与える。ラウンドでは
`RoundScan.caught.lagZero` と `caught.unbroken` があるので

```
value w.machine.control.distance = value s.radius
```

となり、`distance` の非負性は**半径カウンタの非負性**と同値になる。 -/
theorem distance_eq_radius_of_round {raw : List (Fin 2)} {C R h used : ℕ} {s : GalilVM}
    {w0 : GalilScaffoldChainWatch.State}
    (hI : PalPeg.GalilRoundPeriod.RoundScan raw C R h used s w0)
    (hsum : PalPeg.GalilChainCoupling.SumRel s.chain (value s.radius)) :
    value w0.machine.control.distance = value s.radius := by
  have hs : PalPeg.GalilChainCoupling.SumRel (ChainVM.watch w0) (value s.radius) := by
    rw [← hI.chain]; exact hsum
  have he := hs hI.caught.unbroken
  have hz : value w0.lag = 0 := by
    have := hI.caught.lagZero
    simp only [GalilScaffoldCounter.zero, Bool.and_eq_true, List.isEmpty_iff] at this
    simp [value, this.1, this.2]
  omega

/-- **半径カウンタの非負性**は、中心台帳の等式と運ばれる走査不変量から出る。
`CentreLedger` の第 3 連言 `(position s.center : ℤ) + value s.radius = position s.right`
（`CloseoutPackRun47:153`）と `ScanInvariant.rightPos`
（`position r = center + radius`）を合わせると `value s.radius = rad ≥ 0`。 -/
theorem radius_nonneg_of_ledger {raw : List (Fin 2)} {s : GalilVM}
    (hledger : (position s.center : ℤ) + value s.radius = position s.right)
    (hcen : ∃ rad : ℕ, ScanInvariant raw (position s.center) rad s.left s.right) :
    0 ≤ value s.radius := by
  obtain ⟨rad, hsc⟩ := hcen
  have hr := hsc.rightPos
  omega

/-- **`LandingReadyC` from the round, with the `distance` floor derived.**
入力は全部運ばれるもの：ラウンド、`BlockInv`（`AuxPack.coupled.block`）、
`canRight s.right`（`Extra7.scanAvail`）、`SumRel`（`AuxPack.coupled.sum`）、
運ばれる走査不変量（`LPackM.scanGeom`）、そして中心台帳の等式。 -/
theorem landingReadyC_of_parts {raw : List (Fin 2)} {C R h used : ℕ} {s : GalilVM}
    {w0 : GalilScaffoldChainWatch.State}
    (hI : PalPeg.GalilRoundPeriod.RoundScan raw C R h used s w0)
    (hblk : BlockInv s.chain) (hav : canRight s.right)
    (hsum : PalPeg.GalilChainCoupling.SumRel s.chain (value s.radius))
    (hledger : (position s.center : ℤ) + value s.radius = position s.right)
    (hcen : ∃ rad : ℕ, ScanInvariant raw (position s.center) rad s.left s.right) :
    LandingReadyC s :=
  landingReadyC_of_round hI hblk hav
    (by rw [distance_eq_radius_of_round hI hsum]; exact radius_nonneg_of_ledger hledger hcen)

#print axioms canRight_verifier_of_round
#print axioms chainReady_of_round
#print axioms landingReadyC_of_round
#print axioms distance_nonneg_of_run
#print axioms distance_eq_radius_of_round
#print axioms radius_nonneg_of_ledger
#print axioms landingReadyC_of_parts

end PalPeg.CloseoutLandingRound
