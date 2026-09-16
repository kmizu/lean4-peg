import PalPeg.CloseoutPackRun5

/-!
# `CloseoutPackRun6`: the two boot-side `ShiftLocal` obligations are theorems

This wave attacks the thirteen residual hypotheses of
`CloseoutPackRun5.pal_in_peg_final11` — the seven fields of `BigResid5G`,
`H_extraEntry`, `H_extraTick`, `H_shiftLocalC`, `H_stageScan`, `H_bootShift`
and `H_landShift`.  **Two of them close here, unconditionally:**

* `h_bootShift : H_bootShift centreC placeC entry q first`
* `h_landShift : H_landShift centreC placeC entry q first`

The mechanism is a small chain fact that had not been isolated before
(§1): **a comparison out of an idle chain never produces a watching chain.**
`chainAt` from `.idle` has three disjuncts — the first is vacuous (it demands
`.idle ≠ .idle`), the second lands in `.idle`, and the third lands in
`chainStart … = .copy …` or, on a matched comparison, in `ChainMatched` of that
`.copy`, which by the constructor list of `ChainMatched` is again a `.copy`.
Since `beginShiftVM' s'' t''` *requires* `s''.chain = .watch w`
(`GalilScaffoldTopShiftCycle.beginShiftVM`), every one of the five fields of
`CloseoutLPack5.ShiftLocal` is vacuous at a state whose chain is idle
(§2, `shiftLocal_of_chainIdle`).

Both boot-side states are of exactly that shape: `GalilBootVM.initVM0` sets
`chain := .idle` by definition, and the `init` tick is the only tick available
out of `GalilScaffoldController.initial`, whose VM effect `initVM` again fixes
`t.chain = .idle` (§3).  The docstring of `CloseoutOracleI.H_bootShift` worried
that "`chainAt`'s third disjunct can still start the chain inside the very
comparison"; that is true, but the chain it starts is a `.copy`, not a `.watch`,
so the worry is unfounded.

## Verdicts on the other eleven

Each is still open, and for each the *single* missing machine fact is named.
None is an arithmetic gap that the material in the repository closes; several
are strictly stronger than what `CloseoutPackRun4`'s audit recorded, because the
`MInvG` re-cut moved the obligations rather than removing them.

* `rInitPackG` — *missing fact*: the `init` landing is `Leftmost w (position R) C`
  at the boot centre with the left head represented; `GalilTrailFront.inv_of_boot_tick`
  describes the **boot tick of the trail front**, not the centre invariant, and
  `CloseoutLPack.lpack_boot` only covers the `init` state itself, where every
  field is vacuous.  (`MInvG` does *not* help: the landing mode is `scan`.)
* `rScanInvR` — *missing fact* (replaying half only, cf.
  `CloseoutPackRun4.scanInvR_of_nonreplaying`): that a replayed scan re-reads the
  same letters, i.e. `GalilLiveCentreReplay.minv_matchR` bookkeeping lifted from
  `Leftmost` to `ScanInvariant` at the *current* `R`.
* `rShiftDoneScan` — *missing fact*: `GalilPeriodCentre` / `reshift_palindrome`
  need the shift **round**'s total displacement; a single exiting tick does not
  see how many `shiftOne` units ran, and `Extra.cand` gives a `Candidate` for the
  window, not for the consumed amount.
* `rShiftDoneMinv` — *missing fact*: `GalilLiveCentreShift.leftmost_shift` takes
  the shift amount `h` to be the period of the current span; `Extra.cand`'s
  `Candidate lower h` is not identified with the `remaining` the shift round
  consumed.  (This is the one obligation the re-cut **added**, and it is not
  cheaper than the two it replaced.)
* `rChoosePackL` — *missing fact*: `GalilScaffoldTopRewind.rewindFrame.choose`
  sets `y.left := x.right`, so the contract is exactly
  `Represents x.vm.right.head w ∧ focus ≠ none` **in `choose` mode**; the right
  head's representation is a field of `ScanInvariant` only, and no invariant in
  `BigPack2` carries it outside `scan`.
* `rReplayPackG` — *missing fact*: the frame-level `replayStart` relation has not
  been connected to `Restarted w t 0 reset`; `GalilLiveCentreCycle.cycle_fallback_minv`
  produces that shape only along a **fallback route** from a mismatch, and a
  `BigPack2` state in `replayStart` mode carries no such ancestry.
* `rShiftNext` / `H_shiftLocalC` — *missing fact*:
  `GalilCatchUpDistance.places_of_guard` gives `4h ≤ distance` only at a guard
  already entered, and `GalilChainCoupling.Coupled.sum` bounds `distance` by the
  radius only for the chain the coupling tracks; neither is available at an
  arbitrary `InvLPC` state whose chain happens to watch.
* `H_stageScan` — *missing fact*: `GalilReplaySegment.InvScan` has no restarted
  ancestor among its fields, and `GalilInvPlus3`'s landing lemmas produce
  `ReplayStage` only from `Inv`; the replay branch needs a genuinely new
  `InvScan → Restarted`-ancestor lemma.
* `H_extraEntry` — *missing fact*: `failed` / `cand` / `scanAvail` at an entry,
  which are vacuous only if the entry mode is never `scan` — the entry relation
  does not state that.
* `H_extraTick` — *missing fact*: `Extra.failed` is not tick-local; a matched
  comparison raises the radius, so `StageFailed` at the new radius is the DP's
  next verdict, which only `GalilLeafDp`'s round-level lemmas produce.

## Honest status

Standard axioms only.  Two of the thirteen residuals discharged; eleven remain,
each reduced to one named machine fact.  Unconditional `PAL ∈ PEG` remains open.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPackRun6

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton PalPeg.GalilCheckpoints
open PalPeg.GalilFinalAssembly PalPeg.GalilFinalAssembly4
open PalPeg.CloseoutLPack PalPeg.CloseoutLPack5 PalPeg.CloseoutLPack6
open PalPeg.CloseoutOracleI PalPeg.CloseoutOracleI2

/-! ## 1. An idle chain cannot become a watching chain inside one comparison -/

/-- **`ChainMatched` out of a `copy` chain stays a `copy` chain.** -/
theorem chainMatched_copy_ne_watch {ans : GalilScaffoldTape.Tape} {h : Counter}
    {wk : GalilScaffoldPlace.Place} {per : GalilScaffoldChainPeriod.Tape}
    {lag margin : Counter} {ver : PlaceHead} {z : ChainVM}
    (hm : ChainMatched (.copy ans h wk per lag margin ver) z) :
    ∀ wch : GalilScaffoldChainWatch.State, z ≠ .watch wch := by
  cases hm
  intro _ h'
  exact ChainVM.noConfusion h'

/-- **(KEY) `chainAt` out of an idle chain never lands in `watch`.** -/
theorem chainAt_idle_ne_watch {a f : Bool} {ans : GalilScaffoldTape.Tape} {c : Fin 3}
    {wk : GalilScaffoldPlace.Place} {ver : PlaceHead} {rad : Counter} {z : ChainVM}
    (h : chainAt a f ans c wk ver rad .idle z) :
    ∀ wch : GalilScaffoldChainWatch.State, z ≠ .watch wch := by
  rcases h with ⟨hne, -⟩ | ⟨-, -, hz⟩ | ⟨-, -, hz⟩
  · exact absurd rfl hne
  · intro _ h'; rw [hz] at h'; exact ChainVM.noConfusion h'
  · cases a with
    | false =>
      simp only [Bool.false_eq_true, if_false] at hz
      intro _ h'; rw [hz] at h'; exact ChainVM.noConfusion h'
    | true =>
      simp only [if_true] at hz
      exact chainMatched_copy_ne_watch hz

/-- **A comparison out of an idle chain lands with a non-watching chain.** -/
theorem compareFound_idle_ne_watch (P : Shared) (q : ℕ) (first : Fin 9) {s s'' : GalilVM}
    (hcmp : compareFound P q first s s'') (hi : s.chain = ChainVM.idle) :
    ∀ wch : GalilScaffoldChainWatch.State, s''.chain ≠ .watch wch := by
  obtain ⟨vs, vq, a, -, -, -, -, hch, ht⟩ := hcmp
  rw [hi] at hch
  have hz := chainAt_idle_ne_watch hch
  have hchain : s''.chain = vs.chain := by
    rw [ht]; cases a <;> simp [afterCompare, afterMismatch, searchLens, scanLens]
  rw [hchain]; exact hz

#print axioms chainMatched_copy_ne_watch
#print axioms chainAt_idle_ne_watch
#print axioms compareFound_idle_ne_watch

/-! ## 2. `ShiftLocal` is vacuous at an idle chain -/

section Vacuous
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **(KEY) every field of `CloseoutLPack5.ShiftLocal` is vacuous at a state
whose chain is idle**, because `beginShiftVM'` demands a watching chain at the
comparison target and §1 forbids one. -/
theorem shiftLocal_of_chainIdle {w : List (Fin 2)} {x : State GalilVM}
    (hi : x.vm.chain = ChainVM.idle) :
    ShiftLocal centre place entry q first w x := by
  have key : ∀ s'' t'' : GalilVM,
      (galilFrameS (PofC centre place entry w) q first).compare x.vm s'' →
      beginShiftVM' s'' t'' → False := by
    intro s'' t'' hcmp hb
    obtain ⟨wch, hw, -⟩ := hb
    exact compareFound_idle_ne_watch (PofC centre place entry w) q first hcmp hi wch hw
  exact
    { mode := fun s'' t'' h1 h2 => absurd (key s'' t'' h1 h2) (fun h => h)
      move := fun s'' t'' h1 h2 => absurd (key s'' t'' h1 h2) (fun h => h)
      guard := fun s'' t'' h1 h2 => absurd (key s'' t'' h1 h2) (fun h => h)
      coupled := fun s'' t'' h1 h2 => absurd (key s'' t'' h1 h2) (fun h => h)
      ver := fun s'' t'' h1 h2 => absurd (key s'' t'' h1 h2) (fun h => h) }

end Vacuous

#print axioms shiftLocal_of_chainIdle

/-! ## 3. `H_bootShift` and `H_landShift` -/

section Boot
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **`CloseoutOracleI.H_bootShift` is a theorem.**  `GalilBootVM.initVM0` sets
`chain := .idle`. -/
theorem h_bootShift : H_bootShift centre place entry q first :=
  fun _ _ => shiftLocal_of_chainIdle centre place entry q first rfl

/-- **`CloseoutOracleI.H_landShift` is a theorem.**  The only tick out of
`GalilScaffoldController.initial` is `Tick.init`, and `initVM` fixes
`t.chain = .idle`. -/
theorem h_landShift : H_landShift centre place entry q first := by
  intro a rest c1 t hst _
  refine shiftLocal_of_chainIdle centre place entry q first (x := ⟨c1, t⟩) ?_
  cases hst with
  | succ hx h hr =>
    cases hr with
    | zero _ _ =>
      exact (PalPeg.GalilTrailFront.init_tick_inv (P := PofC centre place entry (a :: rest))
        (q := q) (first := first) rfl h).2.2.2.2.2.2.2.2.2.2.1

end Boot

#print axioms h_bootShift
#print axioms h_landShift

end PalPeg.CloseoutPackRun6
