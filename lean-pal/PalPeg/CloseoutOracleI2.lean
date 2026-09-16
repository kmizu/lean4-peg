import PalPeg.CloseoutOracleI
import PalPeg.GalilLeafEnds

/-!
# `CloseoutOracleI2`: the packed oracle over the *unpacked* leaves

`CloseoutOracleI` states the packed cycle oracle
(`CloseoutOracleI.cycleOracleI_of_pieces`) with six route leaves at `ReachAtI` /
`CycleOutI`, plus `H_lrepC`, `hstage` and `hends`.  Those six leaves are *not*
the leaves that exist: the leaves that exist
(`CloseoutReportCase.reachAtC3_of_crossF`,
`CloseoutReadyStage.reachAtC3_of_target_matchS` / `reachAtC3_of_crossS`,
`GalilLeafReport.hlastMismatch_C`,
`GalilLeafMismatch.fallbackRouteMC2_of_mismatch`,
`CloseoutWatchRound3.foundExit_compare_final3`,
`CloseoutFoundBackground.foundExit_bg`) conclude `ReachAtC3` / `CycleOutMC3`,
whose `StepsAll` witnesses are **existentially hidden**.  So the pack cannot be
attached to them route by route from the outside: `ReachAtC3` does not expose the
run one would decorate.  Re-deriving each leaf with `IPack` threaded through
means re-running its proof (the `minv_watchSegE` / `matched_invariant'` /
`lrep_left` interval transport for the report leaves, `fallback_replayStart_All`
/ `minv_after_fallback` for the mismatch leaf, `leftmost_shift` /
`live_shift_of_palAt` / `places_of_guard` / `Coupled.sum` for the two found
leaves), which is an edit of those modules, not a new one.

This module therefore does the three things that *are* closable from outside,
and then supplies the one interface that makes all six leaves usable as they
stand.

## 1. `H_lrepC` is a theorem (§1)

`CloseoutOracleI.H_lrepC` is **discharged**: `CloseoutOracleI.parts_of_invLPC`
already produces `∃ R, ScanInvariant raw (position r.center) R r.left r.right`
at any `InvLPC` state, in both the `Inv` and the `InvScan` branch of `InvS`, and
`GalilScaffoldChainInputSupply.ScanInvariant` carries `leftRep` and
`leftPresent` — exactly the two conjuncts of `CloseoutLPack.LPack.lrep`.  So the
left-head representation never was a residual: `h_lrepC`, and with it
`lpack_of_invLPC'` (`LPack` at *every* `InvLPC` state, unconditionally) and
`ipack_of_invLPC'` (`IPack` there, modulo `ShiftLocal` only).

## 2. `hends` is a theorem, `hstage` splits (§2)

`hends_I` is `GalilLeafEnds.hends_C` composed with `InvLPS.1`, at `centreC` /
`placeC`.

`hstage` asks for `ReplayStage` at every `InvLPC` state.  `InvS` is
`Inv ∨ ∃ k, InvScan`, and on the `Inv` branch `GalilInvPlus3.replayStage_of_inv`
supplies it outright (`Inv.rest` + `Inv.stage` + `Inv.mode`).  `InvScan`
(`GalilReplaySegment.InvScan`) has **no** restarted ancestor among its eleven
fields, so that branch cannot produce the `Restarted … ∧ StageEntry … ∧
WatchSegE …` witness; it is named `H_stageScan` and `hstage_of_scanBranch`
assembles `hstage` from it.

## 3. The run-level bridge (§3)

`PackRun w` — "every `StepsAll` run out of a packed state is packed" — is the
minimal interface under which an *unpacked* conclusion becomes a packed one:
`reachAtI_of_reachAtC3`, `cycleOutI_of_cycleOutMC3` and
`cycleOracleI_of_cycleOracleMC3`.  The second run of a `ReachAtC3` starts at the
report point `y`, which is not an `InvLPC` state, so its pack is *not* available
from §1; it comes from the first run instead (`ipack_last_of_stepsI`), which is
why the bridge is stated on runs and not on states.

`packRun_of_packTick` derives it from `CloseoutOracleI.PackTick` via
`stepsI_of_stepsAll`, so `PackRun` is no stronger than the tick obligation; it
is weaker, and it is the form the leaves can actually be plugged into.

`cycleOracleI_of_leavesC3` is `CloseoutOracleI.cycleOracleI_of_pieces` with all
six route conclusions **unpacked** (`ReachAtC3` / `CycleOutMC3`), i.e. exactly
the shapes the existing leaf theorems have, plus `PackRun` and
`H_shiftLocalC`.  This is the intended consumer: the six leaves above go in
verbatim.

## Residual (NAMED), precisely

* `PackRun centre place entry q first w` (§3) — `∀ k x y,
  IPack … x → StepsAll (galilFrameS (PofC …) q first) 2048 (SoundScanNR w) k x y →
  StepsI … w k x y`.  Implied by `CloseoutOracleI.PackTick`.
* `H_shiftLocalC centre place entry q first w` (§1) — `∀ x, InvLPC w x.ctl x.vm →
  CloseoutLPack5.ShiftLocal centre place entry q first w x`.
* `H_stageScan centre place entry q first raw` (§2) — `∀ c r k,
  GalilReplaySegment.InvScan 2048 raw c r k →
  ReplayStage raw (PofC centre place entry raw) q first c r`.
* the six leaves themselves, now at their *existing* unpacked types, as the
  hypotheses of `cycleOracleI_of_leavesC3`:
  `hended`/`hlastMatch`/`hlastMismatch` at
  `ReachAtC3 (PofC centre place entry raw) q first raw m c r`,
  `hmismatch`/`hfound`/`hfoundBg` at `CycleOutMC3 … raw m c r`.
* `CloseoutOracleI.H_bootShift`, `H_landShift`, `CloseoutLPack5.H_realizeLI'` —
  untouched.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutOracleI2

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton PalPeg.GalilCheckpoints PalPeg.GalilTraceCost
open PalPeg.GalilOracleDischarge PalPeg.GalilOracleLocal PalPeg.GalilLexMeasure
open PalPeg.GalilInvPlus PalPeg.GalilInvPlus2 PalPeg.GalilInvPlus3
open PalPeg.GalilOracleMC PalPeg.GalilOracleMC2 PalPeg.GalilOracleM
open PalPeg.GalilSegmentConstruct PalPeg.GalilOracleLeaves2
open PalPeg.GalilFoundStage
open PalPeg.GalilFinalAssembly PalPeg.GalilFinalAssembly2 PalPeg.GalilFinalAssembly4
open PalPeg.CloseoutLPack PalPeg.CloseoutLPack5 PalPeg.CloseoutLPack6
open PalPeg.CloseoutOracleI

/-! ## 1. `H_lrepC` discharged -/

/-- **The left head is represented and present at every non-`init` `InvLPC`
state.**  `CloseoutOracleI.H_lrepC` is a theorem: the scan invariant
`parts_of_invLPC` extracts has `leftRep` and `leftPresent` as fields. -/
theorem h_lrepC (raw : List (Fin 2)) : H_lrepC raw := by
  intro c r hIC _
  obtain ⟨-, -, R, hi⟩ := parts_of_invLPC hIC
  exact ⟨hi.leftRep, hi.leftPresent⟩

#print axioms h_lrepC

/-- **`CloseoutLPack.LPack` at every `InvLPC` state, unconditionally.** -/
theorem lpack_of_invLPC' {raw : List (Fin 2)} {c : Control} {r : GalilVM}
    (hIC : InvLPC raw c r) : LPack raw c r :=
  lpack_of_invLPC (h_lrepC raw) hIC

section Pack
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **(NAMED) the shift-entry conditions at every `InvLPC` state.**  All that is
left of `IPack` at a landing once §1 removes the left-head half. -/
def H_shiftLocalC (raw : List (Fin 2)) : Prop :=
  ∀ x : State GalilVM, InvLPC raw x.ctl x.vm →
    ShiftLocal centre place entry q first raw x

/-- **`IPack` at every `InvLPC` state, modulo `H_shiftLocalC` alone.** -/
theorem ipack_of_invLPC' {raw : List (Fin 2)} (hsl : H_shiftLocalC centre place entry q first raw)
    {x : State GalilVM} (hIC : InvLPC raw x.ctl x.vm) :
    IPack centre place entry q first raw x :=
  ipack_of_invLPC centre place entry q first (h_lrepC raw) hIC (hsl x hIC)

end Pack

#print axioms lpack_of_invLPC'
#print axioms ipack_of_invLPC'

/-! ## 2. `hends` and `hstage` -/

/-- **The `hends` leaf of `CloseoutOracleI.cycleOracleI_of_pieces`.**
`GalilLeafEnds.hends_C` at `centreC` / `placeC`, entered through `InvLPS`. -/
theorem hends_I (entry q : ℕ) (first : Fin 9) (raw : List (Fin 2)) :
    ∀ (c : Control) (r : GalilVM),
      InvLPS (PofC centreC placeC entry raw) q first raw c r →
      ∃ n : ℕ, ∀ (es : List Bool) (c' : Control) (t : GalilVM),
        WatchSegE (PofC centreC placeC entry raw) q first 2048 es c r c' t →
        es.length = n → SegEnd (PofC centreC placeC entry raw) c' t :=
  fun c r hIS => PalPeg.GalilLeafEnds.hends_C entry q first raw c r hIS.1

#print axioms hends_I

section Stage
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **(NAMED) the stage data on the post-replay branch.**  `InvS` is
`Inv ∨ ∃ k, InvScan`; the `Inv` branch gives `ReplayStage` outright
(`GalilInvPlus3.replayStage_of_inv`), and `GalilReplaySegment.InvScan` has no
restarted ancestor among its fields, so the replay branch has to be named. -/
def H_stageScan (raw : List (Fin 2)) : Prop :=
  ∀ (c : Control) (r : GalilVM) (k : ℕ),
    PalPeg.GalilReplaySegment.InvScan 2048 raw c r k →
    ReplayStage raw (PofC centre place entry raw) q first c r

/-- **The `hstage` leaf, on the replay branch alone.** -/
theorem hstage_of_scanBranch {raw : List (Fin 2)}
    (hsc : H_stageScan centre place entry q first raw) :
    ∀ (c : Control) (r : GalilVM), InvLPC raw c r →
      InvLPS (PofC centre place entry raw) q first raw c r := by
  intro c r hIC
  refine ⟨hIC, ?_⟩
  rcases hIC.1.1.1.1 with h | ⟨k, h⟩
  · exact replayStage_of_inv h
  · exact hsc c r k h

end Stage

#print axioms hstage_of_scanBranch

/-! ## 3. The run-level bridge -/

section Bridge
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **(NAMED) the run-level pack obligation.**  Every `StepsAll` run out of a
packed state is a packed run.  Weaker than `CloseoutOracleI.PackTick` (see
`packRun_of_packTick`) and, unlike it, in the shape the existing unpacked leaves
can be fed into. -/
def PackRun (w : List (Fin 2)) : Prop :=
  ∀ (k : ℕ) (x y : State GalilVM), IPack centre place entry q first w x →
    StepsAll (galilFrameS (PofC centre place entry w) q first) 2048 (SoundScanNR w) k x y →
    StepsI centre place entry q first w k x y

/-- `PackRun` from the tick obligation. -/
theorem packRun_of_packTick {w : List (Fin 2)} (hpt : PackTick centre place entry q first w) :
    PackRun centre place entry q first w :=
  fun _ _ _ hx h => stepsI_of_stepsAll centre place entry q first hpt hx h

/-- **A packed run is packed at its endpoint.** -/
theorem ipack_last_of_stepsI {w : List (Fin 2)} {k : ℕ} {x y : State GalilVM}
    (h : StepsI centre place entry q first w k x y) :
    IPack centre place entry q first w y := by
  obtain ⟨g, -, hgk, -, hp⟩ := h
  rw [← hgk]; exact hp k le_rfl

/-- **`ReachAtC3` becomes `ReachAtI`** under `PackRun` and the pack at the entry
state.  The pack at the report point — where the continuation run starts — is
read off the first packed run, not off §1. -/
theorem reachAtI_of_reachAtC3 {w : List (Fin 2)} (hpr : PackRun centre place entry q first w)
    {m : ℕ} {c : Control} {r : GalilVM}
    (hx : IPack centre place entry q first w ⟨c, r⟩)
    (h : ReachAtC3 (PofC centre place entry w) q first w m c r) :
    ReachAtI centre place entry q first w m c r := by
  obtain ⟨y, k, L, hst, hcr, hrp, hfr, hcont⟩ := h
  have hstI : StepsI centre place entry q first w k ⟨c, r⟩ y := hpr k _ _ hx hst
  refine ⟨y, k, L, hstI, hcr, hrp, hfr, fun hlt => ?_⟩
  obtain ⟨c', r', k', L', hst', hcr', hIS, hp⟩ := hcont hlt
  exact ⟨c', r', k', L',
    hpr k' _ _ (ipack_last_of_stepsI centre place entry q first hstI) hst',
    hcr', hIS.1, hp⟩

/-- **`CycleOutMC3` becomes `CycleOutI`** under the same two inputs. -/
theorem cycleOutI_of_cycleOutMC3 {w : List (Fin 2)} (hpr : PackRun centre place entry q first w)
    {m : ℕ} {c : Control} {r : GalilVM}
    (hx : IPack centre place entry q first w ⟨c, r⟩)
    (h : CycleOutMC3 (PofC centre place entry w) q first w m c r) :
    CycleOutI centre place entry q first w m c r := by
  rcases h with hdone | ⟨cT, sT, k, L, hst, hcr, hIT, hlt, hpos⟩
  · exact Or.inl (reachAtI_of_reachAtC3 centre place entry q first hpr hx hdone)
  · exact Or.inr ⟨cT, sT, k, L, hpr k _ _ hx hst, hcr, hIT.1, hlt, hpos⟩

/-- **The packed cycle oracle from the unpacked one.**  This is the whole of
§3: `CloseoutLPack5.CycleOracleI` needs nothing from the routes that
`GalilInvPlus3.CycleOracleMC3` does not already give, once the pack travels with
the runs and `IPack` is available at the `InvLPC` entry (§1 plus
`H_shiftLocalC`). -/
theorem cycleOracleI_of_cycleOracleMC3 {w : List (Fin 2)}
    (hpr : PackRun centre place entry q first w)
    (hsl : H_shiftLocalC centre place entry q first w)
    (hsc : H_stageScan centre place entry q first w)
    (hor : CycleOracleMC3 (PofC centre place entry w) q first w) :
    CycleOracleI centre place entry q first w := by
  intro m c r hm1 hmle hIC hp
  exact cycleOutI_of_cycleOutMC3 centre place entry q first hpr
    (ipack_of_invLPC' centre place entry q first hsl (x := ⟨c, r⟩) hIC)
    (hor m c r hm1 hmle (hstage_of_scanBranch centre place entry q first hsc c r hIC) hp)

end Bridge

#print axioms packRun_of_packTick
#print axioms ipack_last_of_stepsI
#print axioms reachAtI_of_reachAtC3
#print axioms cycleOutI_of_cycleOutMC3
#print axioms cycleOracleI_of_cycleOracleMC3

/-! ## 4. The packed oracle over the six *unpacked* leaves -/

section Leaves
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **`CloseoutOracleI.cycleOracleI_of_pieces` with unpacked route
conclusions.**  Each of the six leaves is stated at `ReachAtC3` / `CycleOutMC3`,
i.e. at exactly the type the existing leaf theorems have
(`CloseoutReportCase.reachAtC3_of_crossF`,
`CloseoutReadyStage.reachAtC3_of_target_matchS`, `GalilLeafReport.hlastMismatch_C`,
`GalilLeafMismatch.fallbackRouteMC2_of_mismatch`,
`CloseoutWatchRound3.foundExit_compare_final3`,
`CloseoutFoundBackground.foundExit_bg`), and the pack is added afterwards by
`PackRun`.  The case analysis is `cycleOracleI_of_pieces`'s, verbatim: the
segment piece is `GalilOracleLeaves2.segment_of_invLPC`, so only the five
`SegEnd` constructors occur. -/
theorem cycleOracleI_of_leavesC3 (raw : List (Fin 2))
    (hpr : PackRun centre place entry q first raw)
    (hsl : H_shiftLocalC centre place entry q first raw)
    (hsc : H_stageScan centre place entry q first raw)
    (hex : ∀ s, (PofC centre place entry raw).replayExhausted s = zero s.replay)
    (hsearch : ∀ s : GalilVM, PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get s) →
      ∀ a : Bool, ∃ v, searchEffect (PofC centre place entry raw) a s v)
    (hpres : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get s) →
      searchEffect (PofC centre place entry raw) a s v →
      PalPeg.GalilBranchInvariants2.SearchReady v)
    (hends : ∀ (c : Control) (r : GalilVM),
      InvLPS (PofC centre place entry raw) q first raw c r →
      ∃ n : ℕ, ∀ (es : List Bool) (c' : Control) (t : GalilVM),
        WatchSegE (PofC centre place entry raw) q first 2048 es c r c' t →
        es.length = n → SegEnd (PofC centre place entry raw) c' t)
    (hended : ∀ (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ raw.length → InvLPS (PofC centre place entry raw) q first raw c r →
      position r.right ≤ 2 * m - 1 →
      SegReachedW centre place entry q first raw c r c' t → ¬ canRight t.right →
      ReachAtC3 (PofC centre place entry raw) q first raw m c r)
    (hlastMatch : ∀ (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ raw.length → InvLPS (PofC centre place entry raw) q first raw c r →
      position r.right ≤ 2 * m - 1 →
      SegReachedW centre place entry q first raw c r c' t →
      c'.clock = 1 → canRight t.right → PopsIncoming t.right →
      (∃ a : Fin 2, t.right.head.incoming = [a]) →
      read (left t.left) = read (right t.right) →
      ReachAtC3 (PofC centre place entry raw) q first raw m c r)
    (hlastMismatch : ∀ (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ raw.length → InvLPS (PofC centre place entry raw) q first raw c r →
      position r.right ≤ 2 * m - 1 →
      SegReachedW centre place entry q first raw c r c' t →
      c'.clock = 1 → canRight t.right → PopsIncoming t.right →
      (∃ a : Fin 2, t.right.head.incoming = [a]) →
      read (left t.left) ≠ read (right t.right) →
      ReachAtC3 (PofC centre place entry raw) q first raw m c r)
    (hmismatch : ∀ (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ raw.length → InvLPS (PofC centre place entry raw) q first raw c r →
      position r.right ≤ 2 * m - 1 →
      SegReachedW centre place entry q first raw c r c' t →
      c'.replaying = false → c'.clock = 1 → canRight t.right →
      read (left t.left) ≠ read (right t.right) →
      CycleOutMC3 (PofC centre place entry raw) q first raw m c r)
    (hfound : ∀ (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ raw.length → InvLPS (PofC centre place entry raw) q first raw c r →
      position r.right ≤ 2 * m - 1 →
      SegReachedW centre place entry q first raw c r c' t →
      c'.clock = 1 → canRight t.right →
      read (left t.left) = read (right t.right) →
      (∃ vq, searchEffect (PofC centre place entry raw) true t vq ∧ vq.search.mode = .found) →
      CycleOutMC3 (PofC centre place entry raw) q first raw m c r)
    (hfoundBg : ∀ (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ raw.length → InvLPS (PofC centre place entry raw) q first raw c r →
      position r.right ≤ 2 * m - 1 →
      SegReachedW centre place entry q first raw c r c' t → 1 ≤ c'.clock →
      (∃ vq, searchEffect (PofC centre place entry raw) false t vq ∧ vq.search.mode = .found) →
      CycleOutMC3 (PofC centre place entry raw) q first raw m c r) :
    CycleOracleI centre place entry q first raw := by
  intro m c r hm1 hmle hIC hp
  have hIS : InvLPS (PofC centre place entry raw) q first raw c r :=
    hstage_of_scanBranch centre place entry q first hsc c r hIC
  have hx : IPack centre place entry q first raw ⟨c, r⟩ :=
    ipack_of_invLPC' centre place entry q first hsl (x := ⟨c, r⟩) hIC
  obtain ⟨c', t, hsW, hEnd⟩ :=
    segment_of_invLPC centre place entry q first raw hex hsearch hpres c r hIC (hends c r hIS)
  cases hEnd with
  | ended hn =>
      exact Or.inl (reachAtI_of_reachAtC3 centre place entry q first hpr hx
        (hended m c r c' t hm1 hmle hIS hp hsW hn))
  | mismatch hr hc hav hne =>
      exact cycleOutI_of_cycleOutMC3 centre place entry q first hpr hx
        (hmismatch m c r c' t hm1 hmle hIS hp hsW hr hc hav hne)
  | found hc hav hmt hq =>
      exact cycleOutI_of_cycleOutMC3 centre place entry q first hpr hx
        (hfound m c r c' t hm1 hmle hIS hp hsW hc hav hmt hq)
  | foundBackground hc hq =>
      exact cycleOutI_of_cycleOutMC3 centre place entry q first hpr hx
        (hfoundBg m c r c' t hm1 hmle hIS hp hsW hc hq)
  | lastLetter hc hav hpop hinc =>
      by_cases hmt : read (left t.left) = read (right t.right)
      · exact Or.inl (reachAtI_of_reachAtC3 centre place entry q first hpr hx
          (hlastMatch m c r c' t hm1 hmle hIS hp hsW hc hav hpop hinc hmt))
      · exact Or.inl (reachAtI_of_reachAtC3 centre place entry q first hpr hx
          (hlastMismatch m c r c' t hm1 hmle hIS hp hsW hc hav hpop hinc hmt))

end Leaves

#print axioms cycleOracleI_of_leavesC3

/-! ## 5. `pal_in_peg_final6` over this module's residuals -/

/-- **`CloseoutOracleI.pal_in_peg_final6'` with `H_lrepC` discharged** and the
packed oracle replaced by the unpacked one plus the run-level bridge. -/
theorem pal_in_peg_final6'' (entry q : ℕ) (first : Fin 9)
    (hpr : ∀ w : List (Fin 2), PackRun centreC placeC entry q first w)
    (hsl : ∀ w : List (Fin 2), H_shiftLocalC centreC placeC entry q first w)
    (hsc : ∀ w : List (Fin 2), H_stageScan centreC placeC entry q first w)
    (hor : ∀ w : List (Fin 2), 0 < w.length →
      CycleOracleMC3 (PofC centreC placeC entry w) q first w)
    (hbs : H_bootShift centreC placeC entry q first)
    (hls : H_landShift centreC placeC entry q first)
    (hC : H_realizeLI' centreC placeC entry q first) :
    RecognizedByTotalPEG PAL :=
  pal_in_peg_final6' entry q first h_lrepC hbs hls
    (fun w hw => cycleOracleI_of_cycleOracleMC3 centreC placeC entry q first
      (hpr w) (hsl w) (hsc w) (hor w hw)) hC

#print axioms pal_in_peg_final6''

end PalPeg.CloseoutOracleI2
