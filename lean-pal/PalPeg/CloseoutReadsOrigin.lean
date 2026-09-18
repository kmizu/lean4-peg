import PalPeg.CloseoutOriginRounds
import PalPeg.CloseoutRoundUnique

/-!
# `H_readsShift` is free at a round start

`CloseoutRoundUnique.readsRound_tick` needs `H_readsShift` at exactly **one**
tick shape, `Tick.shift_done`, and nowhere else: every other shape either lands
an idle chain or lands in a mode other than `scan`.  Two turns of measurement
settle what that leaf is.

* `ReadsInv`'s witness is an **equality** `w.machine.control =
  run o.shifted.machine.control extra`, and `chainShiftOne` decrements
  `distance` / `boundary` / `last`, so the equality does not survive the shift
  phase — only `Offset` does (`CloseoutSweptOff`).  So the datum cannot simply
  be carried through the shift.
* `SweptOff` *does* survive, but its coordinates stay at the original origin
  while the round's advance by `h` per shift, and the bounce-to-`encoded`
  dictionary (`GalilGoodLag.origin_prediction_index`, via
  `reads_previous_window`) only looks back one period pair, so an accumulated
  continuation cannot be converted.  That conversion is the induction
  `rounds_origin` already performs.

So the leaf is the **round start's read origin**, and once it is present the
leaf is not merely implied, it is *immediate*: `CloseoutOriginAt.OriginAt`
yields a `RoundScan` at `used = 0` together with its `ReadsInv`
(`round_of_originAt`), and `CloseoutRoundUnique.roundScan_unique` says a state
determines the round's coordinates — so the `used` of **any** `RoundScan` at
that state is `0` and the witness is the one `OriginAt` already produced.

`h_readsShift_of_originAt` below is that, and `readsRound_of_originAt` gives
the bundle's whole `ReadsRound` field the same way.  `OriginAt` itself is
supplied at every round boundary by `CloseoutOriginRounds.originAt_of_rounds`
(from a controller `Rounds`, which `CloseoutWatchRound9` constructs), so what
is left of `hSP`'s round assembly is the `Rounds` segment and the *first* round
(`H_freshShift` / `H_fresh`) — not the reads witness.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutReadsOrigin

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton
open PalPeg.GalilRoundPeriod PalPeg.CloseoutPackRun31 PalPeg.CloseoutPackRun37
open PalPeg.CloseoutOriginAt PalPeg.CloseoutRoundReads PalPeg.CloseoutRoundUnique
open PalPeg.CloseoutPackRun41

/-- **The sweep witness at a state with a read origin.**  `round_of_originAt`
produces the pair at `used = 0`; `roundScan_unique` forces the `used` of any
other `RoundScan` at the same state to be `0` too. -/
theorem readsRun_of_originAt {w : List (Fin 2)} {s : GalilVM} (hO : OriginAt w s) :
    ReadsRun w s := by
  intro wch hch C R used hI
  obtain ⟨C0, R0, hI0, hRI0⟩ := round_of_originAt hO hch
  obtain ⟨hC, hR, hU⟩ := roundScan_unique hI0 hI
  subst hC; subst hR; subst hU
  exact hRI0

/-- **`ReadsRound` from the read origin.**  The premised form the bundle
carries. -/
theorem readsRound_of_originAt {w : List (Fin 2)} {c : Control} {s : GalilVM}
    (hO : OriginAt w s) : ReadsRound w c s :=
  readsRound_of_readsRun (readsRun_of_originAt hO)

/-- **`H_readsShift` from the read origin.**  The `shift_done` leaf of
`readsRound_tick`. -/
theorem h_readsShift_of_originAt {w : List (Fin 2)} {c : Control} {s : GalilVM}
    (hO : OriginAt w s) : H_readsShift w c s :=
  fun _ _ _ _ wch hch C R used hI => readsRun_of_originAt hO wch hch C R used hI

/-- **(NAMED, the reformulation) the read origin at a *completed* shift.**
`H_readsShift`'s sole consumer is the `shift_done` branch of
`readsRound_tick`, where `¬ remainingPos` — i.e. `positive s.remaining = false`
— is already in scope, so it belongs in the statement.  Mid-shift the chain is
a partially shifted watch and `Entry` does not hold of it; with the premise the
statement is about the post-shift watch only, which is exactly the one
`rounds_origin` lands on. -/
def OriginShift (w : List (Fin 2)) (c : Control) (s : GalilVM) : Prop :=
  c.mode = Mode.shift → c.replaying = false → s.periodOnly = true →
  positive s.remaining = false → OriginAt w s

/-- **`H_readsShift` from `OriginShift`.**  The premises line up one for one. -/
theorem h_readsShift_of_originShift {w : List (Fin 2)} {c : Control} {s : GalilVM}
    (hOS : OriginShift w c s) : H_readsShift w c s :=
  fun hm hr hpo hz => h_readsShift_of_originAt (hOS hm hr hpo hz) hm hr hpo hz

/-- **`H_readsBirth` from the read origin**, for the same reason (it is already
vacuous during replay by `CloseoutNoReplayWatch.h_readsBirth_vacuous`; this is
the non-vacuous route). -/
theorem h_readsBirth_of_originAt {w : List (Fin 2)} {c : Control} {t : GalilVM}
    (hO : OriginAt w t) : H_readsBirth w c t :=
  fun _ _ wch hch C R used hI => readsRun_of_originAt hO wch hch C R used hI

section
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **The bundle travels one tick with the reads leaf replaced by the origin.**
`CloseoutRoundBundle.roundBundle_tick`'s `H_readsShift` is now
`OriginShift`, so the bundle's two remaining leaves are both about the read
origin: `OriginShift` (the post-shift round start) and `H_freshShift` (the
first round). -/
theorem roundBundle_tick_O {w : List (Fin 2)} {delay : ℕ} {c c' : Control} {s t : GalilVM}
    (hB : PalPeg.CloseoutRoundBundle.RoundBundle w c s)
    (hinv : ChainPositionInvariantWithShiftPhase w c s) (hci : c.mode = Mode.shift → CopyIdle s)
    (hOS : OriginShift w c s)
    (hF : PalPeg.CloseoutPackRun37.H_freshShiftAtShiftEntry centre place entry q first w c s t)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) delay ⟨c, s⟩ ⟨c', t⟩) :
    PalPeg.CloseoutRoundBundle.RoundBundle w c' t :=
  PalPeg.CloseoutRoundBundle.roundBundle_tick centre place entry q first hB hinv hci
    (h_readsShift_of_originShift hOS) hF h

/-- **`H_readsShift` from a controller `Rounds` and the first round's origin.**
The whole supply chain in one statement: `originAt_of_rounds` carries the origin
along the rounds and `roundScan_unique` pins the landing's coordinates.  The
base `Entry` is what `GalilScaffoldTopFirstRound.first_round` — an
unconditional theorem — produces at a fresh chain's first shift, and the
`Rounds` is what `CloseoutWatchRound9.roundOne_of_segRun` builds (modulo
`ShiftAtMismatchC`). -/
theorem h_readsShift_of_rounds {w : List (Fin 2)} {P : Shared} {qq : ℕ} {fst : Fin 9}
    {delay hh m : ℕ} {c0 c1 : Control} {s0 s1 : GalilVM} {c : Control}
    {w0 : GalilScaffoldChainWatch.State} {o : ReadOrigin w}
    (hr : Rounds P qq fst delay hh m c0 s0 c1 s1)
    (hp : s0.periodOnly = true) (hs : s0.chain = ChainVM.watch w0)
    (hz : zero w0.lag = true)
    (he : Entry w o (toOnly s0 w0)) (hint : o.interior.length + 1 = hh)
    (hroom : o.radius + 2 ≤ o.center)
    (hpl : ∀ v : GalilScaffoldChainWatch.State, s1.chain = ChainVM.watch v →
      periodLength v = hh) :
    H_readsShift w c s1 :=
  h_readsShift_of_originAt
    (PalPeg.CloseoutOriginRounds.originAt_of_rounds hr hp hs hz he hint hroom hpl)

/-! ### `H_freshShift` is **not** reachable this way (measured, negative)

`shiftRound_tick`'s `scan_shift` branch splits on `s.periodOnly`; the `false`
side is `H_freshShift`.  One might hope `OriginAt` covers it too, since
`round_of_originAt` does not ask for `periodOnly`.  It does not: `OriginAt`
pins the round's `used` to `0`, so `RoundScan.count` gives
`value s.cycle = 2h`, and `RoundScan.terminal_iff` then makes
`singlePositive s.cycle = true` — which `shiftInv_entry` needs — equivalent to
`1 = 2h`.  A fresh chain's first shift happens at `used = 2h - 1`, after the
whole `WatchSeg` sweep, not at a round start.  So `H_freshShift` stays
`GalilScaffoldTopFirstRound.first_round`'s own obligation. -/

/-- **`OriginShift` from the previous round start and one round segment.**
`CloseoutRoundSeg.originAt_of_roundSeg`: the leaf is in the same currency as
the found-route family's `ShiftRoundC`, not a separate obligation. -/
theorem originShift_of_roundSeg {w : List (Fin 2)} {c : Control} {s0 s : GalilVM}
    (hO : OriginAt w s0)
    (hR : PalPeg.CloseoutRoundSeg.RoundSeg w s0 s)
    (hsome : ∀ wch' : GalilScaffoldChainWatch.State, s.chain = ChainVM.watch wch' →
      ∃ wch : GalilScaffoldChainWatch.State, s0.chain = ChainVM.watch wch) :
    OriginShift w c s :=
  fun _ _ _ _ => PalPeg.CloseoutRoundSeg.originAt_of_roundSeg hO hR hsome

end

#print axioms readsRun_of_originAt
#print axioms readsRound_of_originAt
#print axioms h_readsShift_of_originAt
#print axioms h_readsShift_of_originShift
#print axioms h_readsBirth_of_originAt
#print axioms roundBundle_tick_O
#print axioms h_readsShift_of_rounds
#print axioms originShift_of_roundSeg

end PalPeg.CloseoutReadsOrigin
