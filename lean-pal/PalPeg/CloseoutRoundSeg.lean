import PalPeg.CloseoutSweptOff

/-!
# The round boundary, stated exactly

Three turns of measurement settle where `hSP`'s remaining work is.

**Inside a round** everything is closed: the witness's `n` is the round's
`used`, `RoundScan.fresh` gives `used < 2h`, and
`CloseoutSweptOff.encoded_of_sweptOff` / `advance_of_sweptOff` produce the
prediction and its advance with no periodicity argument.

**Across the shift** the witness survives (`sweptOff_shift`,
`sweptOff_shiftOne`) because `Offset` only asks for the same period tape and
`broken`; the *coordinates* do not.  The next round is at `(C+h, R+h)`, and
re-anchoring the origin there is irreducible: `SweptOff` with the old origin
states the prediction at an index `2h` to the left, and `period_window` bridges
one such step — but round `m` would need `m` of them, which is precisely the
induction `GalilScaffoldChainReadOrigin.rounds_origin` already performs on
`CompareRounds`.

So the remaining obligation is the **round segment**: the projection of one
controller round to `CompareRounds h _ 1 _`, which
`GalilScaffoldTopRoundS.round_next` produces from a `ScanSeg` plus the terminal
comparison plus the shift.  `RoundSeg` names it, and
`originAt_next_of_roundSeg` shows it is enough: it delivers the next round's
`RoundScan` **and** its `ReadsInv`, both at the same coordinates.

With that, `hSP`'s residue is exactly two items, and they are the same kind of
work (assembling a controller-run segment into a `ReadOrigin`):

* `RoundSeg` — one round's projection (`round_next`);
* `H_freshShift` / `H_fresh` — the *first* round
  (`GalilScaffoldTopFirstRound.first_round`).

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutRoundSeg

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton
open PalPeg.GalilRoundPeriod PalPeg.CloseoutPackRun31 PalPeg.CloseoutPackRun37
open PalPeg.CloseoutOriginAt

/-- **(NAMED) one round's projection.**  `GalilScaffoldTopRoundS.round_next`
produces exactly this from a `ScanSeg`, the terminal mismatch comparison and
the shift; `GalilScaffoldTopRounds.rounds_lift` iterates it. -/
def RoundSeg (w : List (Fin 2)) (s s' : GalilVM) : Prop :=
  ∀ wch wch' : GalilScaffoldChainWatch.State,
    s.chain = ChainVM.watch wch → s'.chain = ChainVM.watch wch' →
      periodLength wch' = periodLength wch ∧
      CompareRounds (periodLength wch) (toOnly s wch) 1 (toOnly s' wch')

/-- **The next round, from the origin and one round segment.**  Both halves the
bundle needs come out together and at the same coordinates: the round datum
(`roundScan_entry`) and the sweep witness (`readsInv_of_entry`). -/
theorem originAt_next_of_roundSeg {w : List (Fin 2)} {s s' : GalilVM}
    {wch wch' : GalilScaffoldChainWatch.State}
    (hO : OriginAt w s) (hR : RoundSeg w s s')
    (hch : s.chain = ChainVM.watch wch) (hch' : s'.chain = ChainVM.watch wch') :
    ∃ C R : ℕ, RoundScan w C R (periodLength wch') 0 s' wch' ∧
      ReadsInv w C R (periodLength wch') 0 wch' := by
  obtain ⟨o, he, hint, hroom⟩ := hO wch hch
  obtain ⟨hh, hcr⟩ := hR wch wch' hch hch'
  obtain ⟨o', he', hint', hroom', -, -⟩ := originAt_next he hint hroom hh hcr
  exact ⟨o'.center, o'.radius,
    roundScan_entry o' (periodLength wch') hint' hch' he' hroom',
    readsInv_of_entry he' hint'⟩

/-- **`OriginAt` itself travels one round segment.**  The form the bundle
carries. -/
theorem originAt_of_roundSeg {w : List (Fin 2)} {s s' : GalilVM}
    (hO : OriginAt w s)
    (hR : RoundSeg w s s')
    (hsome : ∀ wch' : GalilScaffoldChainWatch.State, s'.chain = ChainVM.watch wch' →
      ∃ wch : GalilScaffoldChainWatch.State, s.chain = ChainVM.watch wch) :
    OriginAt w s' := by
  intro wch' hch'
  obtain ⟨wch, hch⟩ := hsome wch' hch'
  obtain ⟨o, he, hint, hroom⟩ := hO wch hch
  obtain ⟨hh, hcr⟩ := hR wch wch' hch hch'
  obtain ⟨o', he', hint', hroom', -, -⟩ := originAt_next he hint hroom hh hcr
  exact ⟨o', he', hint', hroom'⟩

#print axioms originAt_next_of_roundSeg
#print axioms originAt_of_roundSeg

end PalPeg.CloseoutRoundSeg
