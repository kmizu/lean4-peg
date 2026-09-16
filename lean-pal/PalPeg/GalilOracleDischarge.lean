import PalPeg.GalilRunSkeleton
import PalPeg.GalilReplaySegment
import PalPeg.GalilSegmentConstruct

/-!
# Discharging the cycle oracle, exit by exit

`PalPeg.GalilRunSkeleton` reduces `H_run` to the **cycle oracle**
`CycleOracleG`: at every state carrying the invariant pack `Inv`, either the
run can already be finished at a refreshed report point, or one sound run
reaches another `Inv` state with the tracked centre strictly further right.

This module assembles that oracle *top-down*.  Nothing here is hidden: every
piece that no local construction can produce travels as a **named hypothesis
with a one-line meaning**, and the body of `cycleOracleS_of_pieces` is nothing
but the explicit case analysis over the five exits of
`PalPeg.GalilSegmentConstruct.SegEnd`.

## The recursion state has to be widened

A fallback cycle whose FPP chooses a *positive* radius `R` does **not** land in
`Inv`: the landing controller has `replaying = true`, and after the `R` replay
rounds of `PalPeg.GalilReplaySegment.replay_after_fallback` the state carries
`InvScan 2048 raw c t R` — the scan pack at radius `R`, which has no
`Restarted` and no `StageEntry`.  So the oracle's recursion state is widened to

  `InvS raw c s := Inv raw c s ∨ ∃ k, InvScan 2048 raw c s k`,

`CycleOracleS` is the oracle over `InvS`, and `runS_fuel` /
`run_from_invS` re-prove `run_from_restarted` over it with **the same
measure** `2·|raw| − position s.center` (`invS_center_le`: an `InvScan`
state's centre is bounded by its own scan invariant exactly as an `Inv`
state's is).  `cycleOracle_of_pieces` then reads `CycleOracleG` off
`CycleOracleS`: an `InvScan` landing is turned into the oracle's *left*
disjunct by running the widened recursion to its report point.

## The five exits

* `lastLetter` — the comparison about to pop the final letter.  On a match the
  tick itself is the refreshed report point (`report_of_last_consume`); on a
  mismatch the controller first falls back and replays, and the report happens
  on the matched comparison that exhausts the replay counter
  (`report_after_replay_of_halted`).  Two hypotheses, `hlastMatch` /
  `hlastMismatch`.
* `mismatch` — a fallback cycle.  `FallbackRoute` splits it into the report,
  the radius-zero landing (`Inv`, via `fallbackCycle_step` / `inv_of_residual`)
  and the positive-radius landing (`ReplayLanding`), and the positive case is
  *not* assumed: `replay_after_fallback` is run for real, so the only thing
  left there is the output relation at the state the replay lands in
  (`houtReplay`) and the search-quiet invariant (`hquiet`).
* `found` / `foundBackground` — a found cycle.  `FoundRoute` splits it into the
  report inside the chain's life (the `lastLetter` exits of the watch and round
  constructions), the cycle with a first shift and re-shift rounds
  (`foundCycle_step'`) and the cycle that breaks before any shift
  (`cycle_found_noshift_*`).  Both landings are turned into `Inv` by the real
  `inv_of_residual`.
* `ended` — the right head has no further symbol.  From an `InvS` state this
  cannot happen *before* the last letter, because the `lastLetter` exit fires
  first; and once it has fired the report point is behind us.  Rather than
  assert the impossibility, `hended` asks for the finished run, which is the
  weaker and honest form.
-/

set_option autoImplicit false

namespace PalPeg.GalilOracleDischarge

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier
open GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton
open PalPeg.GalilEndOfInput (position_le)

/-! ## The widened recursion state -/

/-- The recursion state of the widened oracle: either the restart pack `Inv`,
or the post-replay scan pack `InvScan` at some radius. -/
def InvS (raw : List (Fin 2)) (c : Control) (s : GalilVM) : Prop :=
  Inv raw c s ∨ ∃ k : ℕ, PalPeg.GalilReplaySegment.InvScan 2048 raw c s k

theorem invS_of_inv {raw : List (Fin 2)} {c : Control} {s : GalilVM} (h : Inv raw c s) :
    InvS raw c s := Or.inl h

/-- The measure is a natural number on the widened state too: an `InvScan`
state's centre is bounded by its own scan invariant, exactly as `inv_center_le`
bounds an `Inv` state's. -/
theorem invS_center_le {raw : List (Fin 2)} {c : Control} {r : GalilVM} (h : InvS raw c r) :
    position r.center ≤ 2 * raw.length := by
  rcases h with h | ⟨k, h⟩
  · exact inv_center_le h
  · have hpos : position r.right = position r.center + k := h.scan.rightPos
    have hle : position r.right ≤ 2 * raw.length := position_le r.right raw h.input
    omega

/-! ## The oracle over the widened state -/

/-- A finished run, in the *global* form the published report lemmas produce. -/
def GlobalReport (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9) (raw : List (Fin 2)) : Prop :=
  ∃ y : State GalilVM,
    ScaffoldRun (PofC centre place entry) (fun _ => q) (fun _ => first) 2048 raw y ∧
    ReportPoint raw y ∧ Refreshed (PofC centre place entry raw) q first y

/-- What one turn of the main loop may deliver from `⟨c, r⟩`. -/
def CycleOut (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (c : Control) (r : GalilVM) : Prop :=
  GlobalReport centre place entry q first raw ∨
    ∃ (cT : Control) (sT : GalilVM) (k : ℕ),
      StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048 (SoundScanNR raw) k
        ⟨c, r⟩ ⟨cT, sT⟩ ∧
      InvS raw cT sT ∧ position r.center < position sT.center

/-- The cycle oracle over the widened recursion state. -/
def CycleOracleS (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9) (raw : List (Fin 2)) : Prop :=
  ∀ (c : Control) (r : GalilVM), InvS raw c r →
    CycleOut centre place entry q first raw c r

/-! ## The run lemma over the widened state -/

/-- **The recursion, fuelled form**, over `InvS`.  Same measure as
`PalPeg.GalilRunSkeleton.runG_fuel`. -/
theorem runS_fuel (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (hor : CycleOracleS centre place entry q first raw) :
    ∀ (n : ℕ) (c : Control) (r : GalilVM), 2 * raw.length - position r.center ≤ n →
      InvS raw c r → GlobalReport centre place entry q first raw := by
  intro n
  induction n with
  | zero =>
    intro c r hn hI
    rcases hor c r hI with hdone | ⟨cT, sT, k, _, hIT, hlt⟩
    · exact hdone
    · exact absurd (invS_center_le hIT) (by have := invS_center_le hI; omega)
  | succ n ih =>
    intro c r hn hI
    rcases hor c r hI with hdone | ⟨cT, sT, k, _, hIT, hlt⟩
    · exact hdone
    · exact ih cT sT (by have := invS_center_le hIT; omega) hIT

/-- **The recursion**, over `InvS`. -/
theorem run_from_invS (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (hor : CycleOracleS centre place entry q first raw) (c : Control) (r : GalilVM)
    (hI : InvS raw c r) : GlobalReport centre place entry q first raw :=
  runS_fuel centre place entry q first raw hor (2 * raw.length - position r.center) c r le_rfl hI

/-! ## What the idle segment leaves behind -/

/-- The facts the chain-idle segment construction carries to its exit.  Every
field is an output of `watchSegE_construct` together with the invariants the
entering state already had; the centre does not move along the segment. -/
structure SegReached (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM) : Prop where
  /-- the segment is a sound run of the scaffold -/
  run : ∃ k, StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048
    (SoundScanNR raw) k ⟨c, r⟩ ⟨c', t⟩
  /-- the segment does not move the centre -/
  center : t.center = r.center
  /-- still scanning, with at least one tick of the clock left -/
  mode : c'.mode = Mode.scan
  /-- the clock has not run out -/
  clock : 1 ≤ c'.clock
  /-- the chain is still idle at the exit -/
  idle : t.chain = ChainVM.idle
  /-- the centre invariant (completeness) -/
  minv : MInv raw c' t
  /-- the search co-run is still covered -/
  search : PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get t)
  /-- the right head still represents the input word -/
  input : GalilScaffoldInputTrace.Represents t.right.head raw
  /-- the replay counter never points past the arrived material -/
  frontier : Frontier t
  /-- no chain shift is in flight -/
  shiftIdle : ShiftIdle t
  /-- the scan invariant, at whatever radius the segment reached -/
  scan : ∃ R : ℕ, ScanInvariant raw (position t.center) R t.left t.right

/-! ## The landing states of the two cycles -/

/-- The landing state of a fallback cycle whose FPP chose a **positive** radius
`R`: a restart state with the replay flag up, exactly the input of
`PalPeg.GalilReplaySegment.replay_after_fallback`. -/
structure ReplayLanding (raw : List (Fin 2)) (c : Control) (s : GalilVM) (R : ℕ) : Prop where
  /-- the chosen radius is positive -/
  pos : 0 < R
  /-- the fallback restarted the machine at the new centre -/
  rest : Restarted raw s 0 reset
  /-- the controller is back in scan mode -/
  mode : c.mode = Mode.scan
  /-- with the full match delay -/
  clock : c.clock = 2048
  /-- and the replay flag up -/
  replaying : c.replaying = true
  /-- the replay counter holds the chosen radius -/
  replay : s.replay = ofNat R
  /-- the centre invariant (completeness) -/
  minv : MInv raw c s
  /-- the replay counter never points past the arrived material -/
  frontier : Frontier s
  /-- no chain shift is in flight -/
  shiftIdle : ShiftIdle s

/-- How a found comparison's cycle ends.  The three constructors are the three
routes of the module docstring; `shift` and `noShift` carry the same payload
(they differ only in which cycle lemma produces it). -/
inductive FoundRoute (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (c : Control) (r : GalilVM) : Prop
  /-- the report point falls inside the chain's life -/
  | report (h : GlobalReport centre place entry q first raw)
  /-- the cycle with a first shift and the re-shift rounds (`foundCycle_step'`) -/
  | shift (cT : Control) (sT : GalilVM)
      (hst : ∃ k, StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048
        (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩)
      (hM : MInv raw cT sT) (hR : ∃ (Rad : ℕ) (last : Counter), Restarted raw sT Rad last)
      (hres : FoundResidual raw cT sT) (hprog : position r.center < position sT.center)
  /-- the cycle that breaks before any shift (`cycle_found_noshift_*`) -/
  | noShift (cT : Control) (sT : GalilVM)
      (hst : ∃ k, StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048
        (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩)
      (hM : MInv raw cT sT) (hR : ∃ (Rad : ℕ) (last : Counter), Restarted raw sT Rad last)
      (hres : FoundResidual raw cT sT) (hprog : position r.center < position sT.center)

/-- How a mismatching comparison's fallback cycle ends. -/
inductive FallbackRoute (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (c : Control) (r : GalilVM) : Prop
  /-- the report point falls inside the fallback -/
  | report (h : GlobalReport centre place entry q first raw)
  /-- the FPP chose radius `0`: the landing carries the full pack -/
  | landed (cT : Control) (sT : GalilVM)
      (hst : ∃ k, StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048
        (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩)
      (hI : Inv raw cT sT) (hprog : position r.center < position sT.center)
  /-- the FPP chose a positive radius: the landing still owes `R` replay rounds -/
  | replaying (cT : Control) (sT : GalilVM) (R : ℕ)
      (hst : ∃ k, StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048
        (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩)
      (hL : ReplayLanding raw cT sT R) (hprog : position r.center < position sT.center)

/-! ## Running the replay of a positive-radius fallback landing -/

/-- **The positive-radius fallback landing re-enters the recursion.**  The `R`
replay rounds of `replay_after_fallback` are run for real; what is *not*
derived is the output relation at the state they land in (`hout`), which is
the obligation `PalPeg.GalilReplaySegment` hands back to its caller. -/
theorem cycleOut_of_replayLanding (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2))
    (hex : ∀ s, (PofC centre place entry raw).replayExhausted s = zero s.replay)
    (hsearch : ∀ s : GalilVM, PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get s) →
      ∀ a : Bool, ∃ v, searchEffect (PofC centre place entry raw) a s v)
    (hpres : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get s) →
      searchEffect (PofC centre place entry raw) a s v →
      PalPeg.GalilBranchInvariants2.SearchReady v)
    (hquiet : PalPeg.GalilReplaySegment.SearchQuiet (PofC centre place entry raw))
    (hout : ∀ (c' : Control) (t' : GalilVM) (k : ℕ),
      PalPeg.GalilReplaySegment.InvScan 2048 raw c' t' k → SoundScanNR raw ⟨c', t'⟩)
    (c : Control) (r : GalilVM) (cT : Control) (sT : GalilVM) (R : ℕ)
    (hst : ∃ k, StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048
      (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩)
    (hL : ReplayLanding raw cT sT R) (hprog : position r.center < position sT.center) :
    CycleOut centre place entry q first raw c r := by
  obtain ⟨es, c', t', _hseg, hrun, _hlen, _hcnt, _hrpos, hcen, hIS⟩ :=
    PalPeg.GalilReplaySegment.replay_after_fallback raw (PofC centre place entry raw) q first 2048
      hex (by norm_num) hsearch hpres hquiet R hL.pos cT sT hL.mode hL.clock hL.replaying
      hL.rest hL.replay hL.minv hL.frontier hL.shiftIdle
  obtain ⟨k, hst1⟩ := hst
  refine Or.inr ⟨c', t', k + es.length, stepsAll_trans hst1 (hrun (hout c' t' R hIS)), Or.inr ⟨R, hIS⟩, ?_⟩
  rw [hcen]
  exact hprog

/-! ## The oracle, exit by exit -/

/-- **The widened cycle oracle, assembled.**  The body is the explicit case
analysis over the five exits of `SegEnd`; every underivable piece is one of the
named hypotheses below.

* `hsegment` — the chain-idle segment construction reaches one of the five
  exits from any state of the recursion.
* `hended` — a segment that runs out of input has already passed the report
  point, so the run can be finished there.
* `hlastMatch` — the comparison that pops the last letter *matches*: that tick
  is the refreshed report point (`report_of_last_consume`).
* `hlastMismatch` — the comparison that pops the last letter *mismatches*: the
  controller falls back, replays, and reports on the matched comparison that
  exhausts the replay counter (`report_after_replay_of_halted`).
* `hmismatch` — a mismatching comparison starts a fallback cycle, which ends on
  one of the three routes of `FallbackRoute`.
* `hfound` — a found comparison starts a found cycle, which ends on one of the
  three routes of `FoundRoute`.
* `hfoundBg` — the same, for a chain started on a *background* tick
  (`cycle_found_stepsAll_bg` / `cycle_found_minv_bg`).
* `hex` — the concrete shared reports the replay exhausted exactly when the
  counter is empty.
* `hsearch` / `hpres` — the search co-run has an effect for every event at a
  covered state, and the effect is again covered.
* `hquiet` — the search never reports `found` while a replay is in flight.
* `houtReplay` — the state a replay lands in has a sound output. -/
theorem cycleOracleS_of_pieces (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2))
    (hex : ∀ s, (PofC centre place entry raw).replayExhausted s = zero s.replay)
    (hsearch : ∀ s : GalilVM, PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get s) →
      ∀ a : Bool, ∃ v, searchEffect (PofC centre place entry raw) a s v)
    (hpres : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get s) →
      searchEffect (PofC centre place entry raw) a s v →
      PalPeg.GalilBranchInvariants2.SearchReady v)
    (hquiet : PalPeg.GalilReplaySegment.SearchQuiet (PofC centre place entry raw))
    (houtReplay : ∀ (c' : Control) (t' : GalilVM) (k : ℕ),
      PalPeg.GalilReplaySegment.InvScan 2048 raw c' t' k → SoundScanNR raw ⟨c', t'⟩)
    (hsegment : ∀ (c : Control) (r : GalilVM), InvS raw c r →
      ∃ (c' : Control) (t : GalilVM),
        SegReached centre place entry q first raw c r c' t ∧
        PalPeg.GalilSegmentConstruct.SegEnd (PofC centre place entry raw) c' t)
    (hended : ∀ (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM), InvS raw c r →
      SegReached centre place entry q first raw c r c' t → ¬ canRight t.right →
      GlobalReport centre place entry q first raw)
    (hlastMatch : ∀ (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM), InvS raw c r →
      SegReached centre place entry q first raw c r c' t →
      c'.clock = 1 → canRight t.right → PopsIncoming t.right →
      (∃ a : Fin 2, t.right.head.incoming = [a]) →
      read (left t.left) = read (right t.right) →
      GlobalReport centre place entry q first raw)
    (hlastMismatch : ∀ (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM), InvS raw c r →
      SegReached centre place entry q first raw c r c' t →
      c'.clock = 1 → canRight t.right → PopsIncoming t.right →
      (∃ a : Fin 2, t.right.head.incoming = [a]) →
      read (left t.left) ≠ read (right t.right) →
      GlobalReport centre place entry q first raw)
    (hmismatch : ∀ (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM), InvS raw c r →
      SegReached centre place entry q first raw c r c' t →
      c'.replaying = false → c'.clock = 1 → canRight t.right →
      read (left t.left) ≠ read (right t.right) →
      FallbackRoute centre place entry q first raw c r)
    (hfound : ∀ (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM), InvS raw c r →
      SegReached centre place entry q first raw c r c' t →
      c'.clock = 1 → canRight t.right →
      read (left t.left) = read (right t.right) →
      (∃ vq, searchEffect (PofC centre place entry raw) true t vq ∧ vq.search.mode = .found) →
      FoundRoute centre place entry q first raw c r)
    (hfoundBg : ∀ (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM), InvS raw c r →
      SegReached centre place entry q first raw c r c' t → 1 ≤ c'.clock →
      (∃ vq, searchEffect (PofC centre place entry raw) false t vq ∧ vq.search.mode = .found) →
      FoundRoute centre place entry q first raw c r) :
    CycleOracleS centre place entry q first raw := by
  intro c r hI
  obtain ⟨c', t, hs, hend⟩ := hsegment c r hI
  cases hend with
  | ended hn =>
      exact Or.inl (hended c r c' t hI hs hn)
  | mismatch hr hc hav hne =>
      cases hmismatch c r c' t hI hs hr hc hav hne with
      | report h => exact Or.inl h
      | landed cT sT hst hIT hprog =>
          obtain ⟨k, hst⟩ := hst
          exact Or.inr ⟨cT, sT, k, hst, Or.inl hIT, hprog⟩
      | replaying cT sT R hst hL hprog =>
          exact cycleOut_of_replayLanding centre place entry q first raw hex hsearch hpres hquiet
            houtReplay c r cT sT R hst hL hprog
  | found hc hav hmt hq =>
      cases hfound c r c' t hI hs hc hav hmt hq with
      | report h => exact Or.inl h
      | shift cT sT hst hM hR hres hprog =>
          obtain ⟨k, hst⟩ := hst
          exact Or.inr ⟨cT, sT, k, hst, Or.inl (inv_of_residual hM hR hres), hprog⟩
      | noShift cT sT hst hM hR hres hprog =>
          obtain ⟨k, hst⟩ := hst
          exact Or.inr ⟨cT, sT, k, hst, Or.inl (inv_of_residual hM hR hres), hprog⟩
  | foundBackground hc hq =>
      cases hfoundBg c r c' t hI hs hc hq with
      | report h => exact Or.inl h
      | shift cT sT hst hM hR hres hprog =>
          obtain ⟨k, hst⟩ := hst
          exact Or.inr ⟨cT, sT, k, hst, Or.inl (inv_of_residual hM hR hres), hprog⟩
      | noShift cT sT hst hM hR hres hprog =>
          obtain ⟨k, hst⟩ := hst
          exact Or.inr ⟨cT, sT, k, hst, Or.inl (inv_of_residual hM hR hres), hprog⟩
  | lastLetter hc hav hpop hinc =>
      by_cases hmt : read (left t.left) = read (right t.right)
      · exact Or.inl (hlastMatch c r c' t hI hs hc hav hpop hinc hmt)
      · exact Or.inl (hlastMismatch c r c' t hI hs hc hav hpop hinc hmt)

/-! ## `CycleOracleG` from the widened oracle -/

/-- **The oracle of `PalPeg.GalilRunSkeleton`, discharged.**  An `Inv` state is
an `InvS` state; a landing that is again `Inv` is the oracle's right disjunct
verbatim, and a landing that is only `InvScan` is turned into the *left*
disjunct by running the widened recursion `run_from_invS` to its report
point. -/
theorem cycleOracleG_of_cycleOracleS (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (hor : CycleOracleS centre place entry q first raw) :
    CycleOracleG centre place entry q first raw := by
  intro c r hI
  rcases hor c r (invS_of_inv hI) with hdone | ⟨cT, sT, k, hst, hIT, hlt⟩
  · exact Or.inl hdone
  · rcases hIT with hInv | hScan
    · exact Or.inr ⟨cT, sT, k, hst, hInv, hlt⟩
    · exact Or.inl (run_from_invS centre place entry q first raw hor cT sT (Or.inr hScan))

/-- **`CycleOracleG` from the pieces.**  The hypothesis list is the one of
`cycleOracleS_of_pieces`; see its docstring for the one-line meaning of each. -/
theorem cycleOracle_of_pieces (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2))
    (hex : ∀ s, (PofC centre place entry raw).replayExhausted s = zero s.replay)
    (hsearch : ∀ s : GalilVM, PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get s) →
      ∀ a : Bool, ∃ v, searchEffect (PofC centre place entry raw) a s v)
    (hpres : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get s) →
      searchEffect (PofC centre place entry raw) a s v →
      PalPeg.GalilBranchInvariants2.SearchReady v)
    (hquiet : PalPeg.GalilReplaySegment.SearchQuiet (PofC centre place entry raw))
    (houtReplay : ∀ (c' : Control) (t' : GalilVM) (k : ℕ),
      PalPeg.GalilReplaySegment.InvScan 2048 raw c' t' k → SoundScanNR raw ⟨c', t'⟩)
    (hsegment : ∀ (c : Control) (r : GalilVM), InvS raw c r →
      ∃ (c' : Control) (t : GalilVM),
        SegReached centre place entry q first raw c r c' t ∧
        PalPeg.GalilSegmentConstruct.SegEnd (PofC centre place entry raw) c' t)
    (hended : ∀ (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM), InvS raw c r →
      SegReached centre place entry q first raw c r c' t → ¬ canRight t.right →
      GlobalReport centre place entry q first raw)
    (hlastMatch : ∀ (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM), InvS raw c r →
      SegReached centre place entry q first raw c r c' t →
      c'.clock = 1 → canRight t.right → PopsIncoming t.right →
      (∃ a : Fin 2, t.right.head.incoming = [a]) →
      read (left t.left) = read (right t.right) →
      GlobalReport centre place entry q first raw)
    (hlastMismatch : ∀ (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM), InvS raw c r →
      SegReached centre place entry q first raw c r c' t →
      c'.clock = 1 → canRight t.right → PopsIncoming t.right →
      (∃ a : Fin 2, t.right.head.incoming = [a]) →
      read (left t.left) ≠ read (right t.right) →
      GlobalReport centre place entry q first raw)
    (hmismatch : ∀ (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM), InvS raw c r →
      SegReached centre place entry q first raw c r c' t →
      c'.replaying = false → c'.clock = 1 → canRight t.right →
      read (left t.left) ≠ read (right t.right) →
      FallbackRoute centre place entry q first raw c r)
    (hfound : ∀ (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM), InvS raw c r →
      SegReached centre place entry q first raw c r c' t →
      c'.clock = 1 → canRight t.right →
      read (left t.left) = read (right t.right) →
      (∃ vq, searchEffect (PofC centre place entry raw) true t vq ∧ vq.search.mode = .found) →
      FoundRoute centre place entry q first raw c r)
    (hfoundBg : ∀ (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM), InvS raw c r →
      SegReached centre place entry q first raw c r c' t → 1 ≤ c'.clock →
      (∃ vq, searchEffect (PofC centre place entry raw) false t vq ∧ vq.search.mode = .found) →
      FoundRoute centre place entry q first raw c r) :
    CycleOracleG centre place entry q first raw :=
  cycleOracleG_of_cycleOracleS centre place entry q first raw
    (cycleOracleS_of_pieces centre place entry q first raw hex hsearch hpres hquiet houtReplay
      hsegment hended hlastMatch hlastMismatch hmismatch hfound hfoundBg)

#print axioms invS_of_inv
#print axioms invS_center_le
#print axioms runS_fuel
#print axioms run_from_invS
#print axioms cycleOut_of_replayLanding
#print axioms cycleOracleS_of_pieces
#print axioms cycleOracleG_of_cycleOracleS
#print axioms cycleOracle_of_pieces

end PalPeg.GalilOracleDischarge
