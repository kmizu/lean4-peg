import PalPeg.GalilOracleDischarge
import PalPeg.GalilCycleGlue
import PalPeg.GalilFoundLanding
import PalPeg.GalilCycleNoShift
import PalPeg.GalilCycleFoundBackground
import PalPeg.GalilPrepConstruct
import PalPeg.GalilSegmentConstruct2
import PalPeg.GalilRoundConstruct
import PalPeg.GalilMidRoundFallback
import PalPeg.GalilCycleProgress
import PalPeg.GalilWatchPhase
import PalPeg.GalilShiftPack
import PalPeg.GalilRoundPeriod
import PalPeg.GalilMismatchCaught
import PalPeg.GalilPreludeDone

/-!
# Discharging `hfound` of the cycle oracle

`PalPeg.GalilOracleDischarge.cycleOracle_of_pieces` reduces the cycle oracle to
seven exit hypotheses.  This module discharges the biggest of them, `hfound`:
the exit `SegEnd.found` of the chain-idle segment, i.e. one whole turn of the
main loop through a comparison at which the search reports `found`.

The body is a **complete case analysis**, in this order.

1.  The found comparison starts the chain (`hchm`/`hchne`), and the exit output
    of that comparison is total (`GalilCycleGlue.refresh_frame_exists`).
2.  `GalilPrepConstruct.prep_segment_construct` runs the chain's own
    `2h+2`-tick preparation as a background `WatchSegE` (`PrepData` carries its
    period data).
3.  `GalilSegmentConstruct2.prep_then_watch_construct` composes that with the
    watch phase and delivers a `WatchStop`.
4.  `hrealStop` removes the `outOfFuel` escape, leaving the five real exits of
    `RealStop`, and each is routed:

    * `lastLetter` — the report point inside the watch (`hreportWatch`);
    * `ended` — the input ran out inside the watch (`hreportEnded`);
    * `mismatchOther` — impossible: `GalilMismatchCaught.mismatchOther_impossible`
      is *run*, its scan/palindrome data coming from `hmisOtherData`, whose
      `hcaught` half is `GalilPreludeDone.prelude_done_before_extent`;
    * `broke` — the chain broke before any shift: `cycle_found_noshift_stepsAll`
      / `_minv` / `_restarted` are run for real, and `inv_of_residual` turns the
      landing into `Inv` (`FoundRoute.noShift`);
    * `mismatchWatch` — the first shift (`GalilShiftPack.shiftPack_concrete`
      plus `shift_run_chain`), then the re-shift rounds (`rounds_wide` driven by
      `GalilMidRoundFallback.roundEnd_midFallback`), and finally the five ends
      of a round: `BreakEnd` → `foundCycle_step_progress` + `inv_of_residual`
      (`FoundRoute.shift`), `InputEnd` / `LastLetterEnd` → report,
      `GuardFail` / `MidFallback` → `fallback_from_watch` and a landing.

Nothing is hidden: every leaf the local constructions cannot produce is a
**named hypothesis with a one-line meaning**, listed on the main theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.GalilOracleGlueC

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier
open GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton
open PalPeg.GalilOracleDischarge
open PalPeg.GalilSegmentConstruct2

/-! ## The five real exits of a watch phase -/

/-- `GalilSegmentConstruct2.WatchStop` without its `outOfFuel` escape. -/
inductive RealStop (P : Shared) (q : ℕ) (first : Fin 9) : Control → GalilVM → Prop
  /-- End of input. -/
  | ended (c : Control) (s : GalilVM) (hn : ¬ canRight s.right) : RealStop P q first c s
  /-- The terminal mismatch at a zero-lag watch: the found cycle continues. -/
  | mismatchWatch (c : Control) (s : GalilVM) (hm : c.mode = .scan) (hr : c.replaying = false)
      (hc : c.clock = 1) (ha : canRight s.right)
      (w : GalilScaffoldChainWatch.State) (hs : s.chain = .watch w) (hz : zero w.lag = true)
      (vs : ScanVM) (vq : SearchVM)
      (hcmp : (galilFrame P q first).compare s (scanLens.set s vs))
      (hmt : ¬ (galilFrame P q first).matched (scanLens.set s vs))
      (hq : searchEffect P false s vq) : RealStop P q first c s
  /-- A mismatch while the chain is not a zero-lag watch — the gap. -/
  | mismatchOther (c : Control) (s : GalilVM) (hm : c.mode = .scan) (hr : c.replaying = false)
      (hc : c.clock = 1) (ha : canRight s.right)
      (hno : ¬ ∃ w : GalilScaffoldChainWatch.State, s.chain = .watch w ∧ zero w.lag = true)
      (vs : ScanVM) (vq : SearchVM)
      (hcmp : (galilFrame P q first).compare s (scanLens.set s vs))
      (hmt : ¬ (galilFrame P q first).matched (scanLens.set s vs))
      (hq : searchEffect P false s vq) : RealStop P q first c s
  /-- The report point inside the watch phase. -/
  | lastLetter (c : Control) (s : GalilVM) (hm : c.mode = .scan) (hr : c.replaying = false)
      (hc : c.clock = 1) (ha : canRight s.right) (hpop : PopsIncoming s.right)
      (hinc : ∃ a : Fin 2, s.right.head.incoming = [a]) : RealStop P q first c s
  /-- The period break: a matched comparison whose chain effect breaks. -/
  | broke (c : Control) (s : GalilVM) (hm : c.mode = .scan) (hr : c.replaying = false)
      (hc : c.clock = 1) (ha : canRight s.right)
      (vs : ScanVM) (vq : SearchVM)
      (hcmp : (galilFrame P q first).compare s (scanLens.set s vs))
      (hmt : (galilFrame P q first).matched (scanLens.set s vs))
      (hq : searchEffect P true s vq)
      (w' : GalilScaffoldChainWatch.State) (hbroken : (afterCompare s vs vq).chain = .broken w') :
      RealStop P q first c s

/-! ## The period data of the preparation segment -/

/-- The argument list of `GalilPrepConstruct.prep_segment_construct`, bundled:
the DP answer tape, the centre the walker reads, the copy and back runs of the
chain's preparation, and the credited `chain.start()` at `sF`. -/
def PrepData (delay : ℕ) (sF : GalilVM) (h : ℕ) : Prop :=
  ∃ (answer : GalilScaffoldTape.Tape) (cen : Fin 3) (p q' : GalilScaffoldPlace.Place)
    (ver : PlaceHead) (radius : Counter) (u : GalilScaffoldTape.Tape)
    (ys : List (Fin 3)) (b : Fin 3),
    GalilScaffoldChainPeriod.Copy answer reset p (GalilScaffoldChainPeriod.start cen) h u
      (ofNat h) q'
      (GalilScaffoldChainPeriod.fill (GalilScaffoldChainPeriod.start cen) (ys ++ [b])) ∧
    u.focus = 4 ∧ positive (ofNat h) = true ∧
    (GalilScaffoldChainPeriod.fill (GalilScaffoldChainPeriod.start cen)
      (ys ++ [b])).focus = .plain b ∧
    GalilScaffoldChainPeriod.Back (GalilScaffoldChainPeriod.write
      (GalilScaffoldChainPeriod.fill (GalilScaffoldChainPeriod.start cen) (ys ++ [b])) (.last b))
      (h+1) (GalilScaffoldChainPeriod.moveRight ⟨[], .first cen,
        ys.map GalilScaffoldChainPeriod.Token.plain ++ [.last b]⟩) ∧
    ChainMatched (chainStart answer cen p ver radius) sF.chain ∧
    2*h+2 < delay

/-! ## The round iteration over a widened terminal -/

/-- `rounds_construct_of_measure` with an **arbitrary** terminal predicate `E`,
and with the loop invariant exported at the terminal.  This is what lets
`GalilMidRoundFallback.roundEnd_midFallback` — whose terminal is
`RoundEnd' ∨ MidFallback`, not `RoundEnd` — drive the iteration. -/
theorem rounds_wide (P : Shared) (q : ℕ) (first : Fin 9) (delay h : ℕ)
    (Inv E : Control → GalilVM → Prop) (mu : Control → GalilVM → ℕ)
    (hround : ∀ c s, Inv c s → E c s ∨
      ∃ (c' : Control) (s' : GalilVM),
        Rounds P q first delay h 1 c s c' s' ∧ Inv c' s' ∧ mu c' s' < mu c s) :
    ∀ (c : Control) (s : GalilVM), Inv c s →
      ∃ (m : ℕ) (c' : Control) (s' : GalilVM),
        Rounds P q first delay h m c s c' s' ∧ Inv c' s' ∧ E c' s' := by
  have key : ∀ (fuel : ℕ) (c : Control) (s : GalilVM), Inv c s → mu c s ≤ fuel →
      ∃ (m : ℕ) (c' : Control) (s' : GalilVM),
        Rounds P q first delay h m c s c' s' ∧ Inv c' s' ∧ E c' s' := by
    intro fuel
    induction fuel with
    | zero =>
      intro c s hI hmu
      rcases hround c s hI with hend | ⟨c1, s1, _, _, hlt⟩
      · exact ⟨0, c, s, .stop _ _, hI, hend⟩
      · omega
    | succ f ih =>
      intro c s hI hmu
      rcases hround c s hI with hend | ⟨c1, s1, hstep, hI1, hlt⟩
      · exact ⟨0, c, s, .stop _ _, hI, hend⟩
      · obtain ⟨m, c', s', hr, hI', hend⟩ := ih c1 s1 hI1 (by omega)
        exact ⟨1 + m, c', s', rounds_append P q first delay h hstep hr, hI', hend⟩
  intro c s hI
  exact key (mu c s) c s hI (le_refl _)

/-! ## `hfound`, discharged -/

/-- **The found exit of the chain-idle segment, routed.**

The hypotheses that no local construction can produce, with their meaning:

* `hrF` — the controller is not replaying at the found comparison.
* `hR0` / `hM0` / `hout0` — the entering state is a restart state with the
  centre invariant and a sound output (the `Inv` disjunct of `InvS`).
* `hsegE` — the idle segment in the `WatchSegE` form `watchSegE_construct`
  produces; `SegReached` keeps only its `StepsAll` shadow.
* `hchm` / `hchne` — the found comparison starts a real (non-idle) chain.
* `hprep` — the period data of the found DP answer, i.e. the argument list of
  `prep_segment_construct` at the state right after the found comparison.
* `hKinv2` — the state the preparation lands in satisfies the watch-phase
  invariant `K.Inv` (from `chainReady_of_vm` and the branch invariants).
* `hrealStop` — the watch phase does not exhaust the fuel: its exit is one of
  the five real ones.
* `hreportWatch` / `hreportEnded` — the report point inside the watch phase
  (the last-letter comparison), and the watch phase that runs out of input.
* `hmisOtherData` — the scan/palindrome data of `mismatchOther_impossible`,
  whose `hcaught` half is `prelude_done_before_extent`.
* `hwatchAtBreak` — the chain is still watching at the breaking comparison.
* `hterm` — the broken chain's counters at a no-shift terminal.
* `hresNoShift` / `hprogNoShift` — the residual facts and the centre progress
  at the no-shift landing.
* `hscanInv` / `hpos` / `hle` / `hper` / `hcopy` / `hpred` / `hlock` — the
  inputs of `shiftPack_concrete` at the terminal mismatch of the watch phase.
* `hguard` — the shift guard holds at that mismatch.
* `hRI` — the round invariant at the state the first shift lands in.
* `hsinv` / `hsearch` / `hwr` / `hwi` / `hmid'` / `hbreakStep` / `hpackRound` /
  `hmeasure` — the inputs of `roundEnd_midFallback`.
* `hfoundCycle` — the pieces assembled above form a `FoundCycle` (this is
  `GalilCycleGlue.foundCycle_of_constructions` at the `BreakEnd` branch).
* `hresFound` — the residual facts at a found-cycle landing.
* `hreportInput` / `hreportLast` — the two report exits of a round.
* `hfallbackFromWatch` — a mismatching comparison with the shift guard false
  falls back from the watch (`fallback_from_watch`) and lands in `Inv`. -/
theorem foundRoute_of_pieces
    (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ)
    (first : Fin 9) (raw : List (Fin 2))
    (K : Ctx (PofC centre place entry raw) q first) (fuel : ℕ)
    (W : GalilScaffoldChainWatch.State → Prop)
    (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM)
    (vq : SearchVM) (ch : ChainVM) (h radius : ℕ) (es0 : List Bool)
    (hsg : SegReached centre place entry q first raw c r c' t)
    (hclk : c'.clock = 1) (hrF : c'.replaying = false) (hav : canRight t.right)
    (hmt : read (left t.left) = read (right t.right))
    (hq : searchEffect (PofC centre place entry raw) true t vq)
    (hfnd : vq.search.mode = .found)
    -- the entering state
    (hR0 : ∃ (Rad : ℕ) (last : Counter), Restarted raw r Rad last)
    (hM0 : MInv raw c r) (hout0 : OutputRel raw c r)
    (hsegE : WatchSegE (PofC centre place entry raw) q first 2048 es0 c r c' t)
    -- the chain started at the found comparison
    (hchm : ChainMatched (chainStart (vq.dp.config.tapes 11)
      ((PofC centre place entry raw).centre t) ((PofC centre place entry raw).place t)
      t.center t.radius) ch)
    (hchne : ch ≠ ChainVM.idle)
    -- the preparation period
    (hprep : PrepData 2048 (afterCompare t ⟨left t.left, right t.right, ch⟩ vq) h)
    (hKinv2 : ∀ s2 : GalilVM, K.Inv s2)
    -- the watch phase reaches a real exit
    (hrealStop : ∀ (c1 : Control) (s1 : GalilVM),
      WatchStop (PofC centre place entry raw) q first c1 s1 →
      RealStop (PofC centre place entry raw) q first c1 s1)
    -- the two report exits of the watch phase
    (hreportWatch : ∀ (c1 : Control) (s1 : GalilVM), c1.clock = 1 → canRight s1.right →
      PopsIncoming s1.right → (∃ a : Fin 2, s1.right.head.incoming = [a]) →
      GlobalReport centre place entry q first raw)
    (hreportEnded : ∀ (_c1 : Control) (s1 : GalilVM), ¬ canRight s1.right →
      GlobalReport centre place entry q first raw)
    -- the gap exit is impossible
    (hmisOtherData : ∀ s1 : GalilVM, ∃ C k R : ℕ,
      ScanInvariant raw C k s1.left s1.right ∧ k + 1 < C ∧
      Manacher.PalAt (encoded raw) C R ∧
      (¬ (k + 1 ≤ R) → ∃ w : GalilScaffoldChainWatch.State,
        s1.chain = .watch w ∧ zero w.lag = true))
    -- the no-shift terminal
    (hterm : ∀ w3' : GalilScaffoldChainWatch.State,
      negative w3'.margin = false ∧ positive w3'.machine.control.last = true ∧
      zero w3'.lag = true ∧ Canonical w3'.machine.control.last)
    (hwatchAtBreak : ∀ s1 : GalilVM, ∃ w3 : GalilScaffoldChainWatch.State,
      s1.chain = ChainVM.watch w3)
    (hresNoShift : ∀ (cT : Control) (sT : GalilVM), FoundResidual raw cT sT)
    (hprogNoShift : ∀ sT : GalilVM, position r.center < position sT.center)
    -- the first shift
    (hscanInv : ∀ s1 : GalilVM, ScanInv raw s1 radius)
    (hpos : 0 < h) (hle : h ≤ radius)
    (hper : ∀ w : GalilScaffoldChainWatch.State, h = periodLength w)
    (hcopy : ∀ s1 : GalilVM, CopyIdle s1)
    (hpred : ∀ (s1 : GalilVM) (w : GalilScaffoldChainWatch.State),
      read (right s1.right) = GalilScaffoldChainConsume.symbol w.machine.control.period.focus)
    (hlock : ∀ (s1 : GalilVM) (w : GalilScaffoldChainWatch.State) (vs : ScanVM) (vqq : SearchVM),
      shiftGuardVM (afterMismatch s1 vs vqq) → vs.chain = ChainVM.watch w)
    (hguard : ∀ (s1 : GalilVM) (vs : ScanVM) (vqq : SearchVM),
      (PofC centre place entry raw).shiftGuard (afterMismatch s1 vs vqq))
    (hRI : ∀ (c1 : Control) (s1 : GalilVM), RoundInv h raw c1 s1)
    -- the round oracle
    (hsinv : ∀ c1 s1, RoundInv h raw c1 s1 → PalPeg.GalilRoundConstruct.SInv 2048 W c1 s1)
    (hsearch : ∀ (u : GalilVM) (a : Bool),
      ∃ v, searchEffect (PofC centre place entry raw) a u v)
    (hwr : ∀ w, W w → PalPeg.GalilBranchInvariants.WatchReady w)
    (hwi : ∀ w, W w → W (GalilScaffoldChainWatch.immediate w))
    (hmid' : ∀ (u : GalilVM) (w : GalilScaffoldChainWatch.State),
      u.chain = ChainVM.watch w → canRight u.right → singlePositive u.cycle = false →
      (read (left u.left) = read (right u.right) ∧ GalilScaffoldChainWatch.Good w) ∨
        read (left u.left) ≠ read (right u.right))
    (hbreakStep : ∀ (u : GalilVM) (w : GalilScaffoldChainWatch.State),
      u.chain = ChainVM.watch w → canRight u.right → singlePositive u.cycle = true →
      read (left u.left) = read (right u.right) → ∃ w', BreakStep w w')
    (hpackRound : ∀ (u : GalilVM) (w : GalilScaffoldChainWatch.State),
      u.chain = ChainVM.watch w → canRight u.right → singlePositive u.cycle = true →
      read (left u.left) ≠ read (right u.right) →
      PalPeg.GalilRoundConstruct.ShiftPack (PofC centre place entry raw) h u w)
    (hmeasure : ∀ c1 s1, RoundInv h raw c1 s1 → position s1.center + h ≤ 2 * raw.length)
    -- the four ends of a round
    (hfoundCycle : ∀ (ca : Control) (sa : GalilVM),
      BreakEnd (PofC centre place entry raw) q first 2048 ca sa →
      FoundCycle (PofC centre place entry raw) q first 2048 raw c r)
    (hresFound : ∀ (cT : Control) (sT : GalilVM), FoundResidual raw cT sT)
    (hreportInput : ∀ (ca : Control) (sa : GalilVM),
      InputEnd (PofC centre place entry raw) q first 2048 ca sa →
      GlobalReport centre place entry q first raw)
    (hreportLast : ∀ (ca : Control) (sa : GalilVM),
      (∃ (n : ℕ) (c1 : Control) (s1 : GalilVM),
        ScanSeg (PofC centre place entry raw) q first 2048 n ca sa c1 s1 ∧
        PalPeg.GalilRoundConstruct.LastLetterEnd c1 s1) →
      GlobalReport centre place entry q first raw)
    (hfallbackFromWatch : ∀ (ca : Control) (sa : GalilVM),
      GuardFail (PofC centre place entry raw) q first 2048 ca sa ∨
        PalPeg.GalilMidRoundFallback.MidFallback (PofC centre place entry raw) q first 2048 ca sa →
      FoundRoute centre place entry q first raw c r) :
    FoundRoute centre place entry q first raw c r := by
  classical
  -- (1) the found comparison: its period data and its exit output
  obtain ⟨answer, cen, p, q', ver, radius', u, ys, b, hcopyR, hu, hposH, hfocus, hback,
    hchS, hh⟩ := hprep
  obtain ⟨oF, hoF⟩ := PalPeg.GalilCycleGlue.refresh_frame_exists
    (PofC centre place entry raw) q first
    (afterCompare t ⟨left t.left, right t.right, ch⟩ vq) c'.output
  -- (2) the preparation segment
  obtain ⟨bs, cs, dm, c2, s2, hprepSeg, hbs, hcs, hdm, _hchain2, _hwatch2, hm2, hr2, _ho2,
    hlow2, _hhi2, _hl2, _hr2, _hc2, _hrad2, _hlen2, _hpo2, _hrep2, _hget2⟩ :=
    PalPeg.GalilPrepConstruct.prep_segment_construct (PofC centre place entry raw) q first 2048
      answer cen p q' ver radius' u h ys b hcopyR hu hposH hfocus hback
      (afterCompare t ⟨left t.left, right t.right, ch⟩ vq).chain hchS
      {c' with clock := 2048, output := oF, replaying := false}
      (afterCompare t ⟨left t.left, right t.right, ch⟩ vq) hsg.mode rfl rfl rfl hh
  -- (3) the watch phase
  obtain ⟨c1, s1, _hprepSeg', _hbs', _hcs', _hdm', hwseg, _hinv1, hm1, hr1, hc1, hstop⟩ :=
    prep_then_watch_construct (PofC centre place entry raw) q first 2048 K fuel h hprepSeg
      hbs hcs hdm hm2 hr2 hlow2 hh (hKinv2 s2)
  -- (4) the five real exits
  cases hrealStop c1 s1 hstop with
  | ended hn => exact .report (hreportEnded c1 s1 hn)
  | lastLetter _ _ hcc haa hpop hinc => exact .report (hreportWatch c1 s1 hcc haa hpop hinc)
  | mismatchOther _ _ _ haa hno vs vqq hcmp hmtn _hqq =>
      obtain ⟨C, k, R, hinv, hkC, hpal, hcaught⟩ := hmisOtherData s1
      exact absurd (PalPeg.GalilMismatchCaught.mismatchOther_impossible
        (PofC centre place entry raw) q first hinv hkC hpal hcaught haa hno hcmp hmtn)
        (fun hf => hf)
  | broke hmm hrr hcc haa vs3 vq3 hcmp3 hmt3 hq3 w3' hbroken =>
      obtain ⟨o3, ho3⟩ := PalPeg.GalilCycleGlue.refresh_frame_exists
        (PofC centre place entry raw) q first (afterCompare s1 vs3 vq3) c1.output
      obtain ⟨Rad0, last0, hR0'⟩ := hR0
      obtain ⟨hmargin, hlast, hlag, hcanon⟩ := hterm w3'
      obtain ⟨w3, hs3⟩ := hwatchAtBreak s1
      refine .noShift (foundLandingControl c1 2048 o3)
        (foundLandingVM (afterCompare s1 vs3 vq3) w3' entry) ?_ ?_ ?_
        (hresNoShift (foundLandingControl c1 2048 o3)
          (foundLandingVM (afterCompare s1 vs3 vq3) w3' entry))
        (hprogNoShift (foundLandingVM (afterCompare s1 vs3 vq3) w3' entry))
      · exact cycle_found_noshift_stepsAll raw (PofC centre place entry raw) rfl rfl q first 2048
          hR0' hout0 hsegE hsg.mode hrF hclk hav hsg.idle vq hq hfnd hmt ch hchm hchne oF hoF
          hprepSeg hwseg hmm hrr hcc w3 hs3 haa vs3 vq3 hcmp3 hmt3 hq3 o3 ho3 w3' hbroken
          hmargin hlast hlag entry (fun _ _ hx => hx)
      · exact cycle_found_noshift_minv raw (PofC centre place entry raw) (fun _ => rfl) q first
          2048 hR0' hM0 hsegE hsg.mode hrF hclk hav hsg.idle vq hq hfnd hmt ch hchm hchne oF hoF
          hprepSeg hwseg hmm hrr hcc w3 hs3 haa vs3 vq3 hcmp3 hmt3 hq3 o3 ho3 w3' hbroken entry
      · exact ⟨_, _, (cycle_found_noshift_restarted raw (PofC centre place entry raw) q first 2048
          hR0' hsegE hav hmt vq ch hchne oF hprepSeg hwseg haa vs3 vq3 hcmp3 hmt3 w3' hcanon
          hlast entry).choose_spec⟩
  | mismatchWatch hmm hrr hcc haa w hsw hz vs vqq hcmp hmtn hqq =>
      -- the first shift
      have hpack : PalPeg.GalilRoundConstruct.ShiftPack (PofC centre place entry raw) h s1 w :=
        PalPeg.GalilShiftPack.shiftPack_concrete (onLetterVM raw) leftFirstVM centre place entry
          raw radius h s1 w (hscanInv s1) hpos hle (hper w) (hcopy s1) (hpred s1 w) (hlock s1 w)
      obtain ⟨s2', t', hb, hs2', hi2, hrun⟩ := hpack.2.2 vs vqq (hguard s1 vs vqq)
      obtain ⟨v, cyc, hchainRun⟩ :=
        shift_run_chain hrun (GalilScaffoldChainWatch.immediate w) reset
      obtain ⟨o, ho⟩ := PalPeg.GalilTickFun3.refresh_exists (PofC centre place entry raw) q first
        (shiftLens.set s2' ⟨t', ChainVM.watch v, cyc⟩) c1.output
      -- the re-shift rounds
      obtain ⟨m, cR, sR, _hrounds, _hRI', hend⟩ :=
        rounds_wide (PofC centre place entry raw) q first 2048 h (RoundInv h raw)
          (fun ca sa =>
            PalPeg.GalilRoundConstruct.RoundEnd' (PofC centre place entry raw) q first 2048 ca sa ∨
            PalPeg.GalilMidRoundFallback.MidFallback
              (PofC centre place entry raw) q first 2048 ca sa)
          (fun _ sa => 2 * raw.length - position sa.center)
          (fun ca sa hIa => by
            rcases PalPeg.GalilMidRoundFallback.roundEnd_midFallback
              (PofC centre place entry raw) q first 2048 h raw W (by norm_num)
              (fun uu hper' hcyc => PalPeg.GalilMidRoundFallback.midFallback_guard_concrete
                (onLetterVM raw) leftFirstVM (restartVM entry) centre place entry uu hper' hcyc)
              hsinv hsearch hwr hwi hmid' hbreakStep hpackRound hmeasure ca sa hIa with
              he | he | ⟨cb, sb, hst, hIb, hlt⟩
            · exact Or.inl (Or.inl he)
            · exact Or.inl (Or.inr he)
            · exact Or.inr ⟨cb, sb, hst, hIb, hlt⟩)
          {c1 with mode := .scan, clock := 2048, output := o}
          (shiftLens.set s2' ⟨t', ChainVM.watch v, cyc⟩) (hRI _ _)
      -- the five ends of a round
      rcases hend with (hre | hlast) | hmidfb
      · rcases hre with hbreak | hinput | hgf
        · obtain ⟨Rad0, last0, hR0'⟩ := hR0
          obtain ⟨cT, sT, hst, hM, hRes, hprog⟩ :=
            PalPeg.GalilCycleProgress.foundCycle_step_progress (PofC centre place entry raw) q
              first 2048 raw c r (hfoundCycle cR sR hbreak) Rad0 last0 hR0' hM0
          exact .shift cT sT hst hM hRes (hresFound cT sT) hprog
        · exact .report (hreportInput cR sR hinput)
        · exact hfallbackFromWatch cR sR (Or.inl hgf)
      · exact .report (hreportLast cR sR hlast)
      · exact hfallbackFromWatch cR sR (Or.inr hmidfb)

#print axioms rounds_wide
#print axioms foundRoute_of_pieces

end PalPeg.GalilOracleGlueC
