import PalPeg.CloseoutPreload31

/-!
# `Canonical` along the `.run` / `.wait` legs, and the coupled round trip

`CloseoutPreload31.postRunF_round_trip` leaves four hypotheses outside the
`PostRunF` frame: `hcan1` / `hcan0` (`Canonical` debt at the `.wait` exit and
the `.double` entry), `hs2` (the `.wait` exit tick is `false`) and `hsc` (the
`ScanTrace` over the extended stream).

* §1 closes `hcan1` / `hcan0`: `Canonical` is preserved by every `.run` tick
  (`SafeQuanta` = calls that keep the debt, `safeCalls_debt`, then one unary
  `advance` = `dec`) and every `.wait` tick (`waitStep` keeps the debt, then
  `advance`), hence along `RunTrace` / `WaitTrace`.
* §2 states what `hs2` and `hsc` really are.  `ScanTrace F delay` is a run of
  `GalilScaffoldTop.Tick` on `State σ`; for a generic frame there is *no*
  projection from `State σ` to `SearchVM`, so nothing in the tree identifies the
  boolean a `searchStep` leg consumes with the boolean `ScanTrace` records
  (`CloseoutPreload21` §4 (i); on `galilFrameS` it is `CloseoutPreload22` §1).
  Both facts are therefore packaged as **one** hypothesis, `LegsCoupled`, and
  `wait_exit_false` / `scanTrace_extend_legs` are its two projections.
* §3 restates the round trip with `hcan1` / `hcan0` discharged and `hs2` /
  `hsc` replaced by `LegsCoupled`.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPreload32

open PalPeg PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController
open PalPeg.GalilScaffoldSearchFinish (Mode)
open PalPeg.GalilScaffoldCounter (Canonical value ofNat positive zero dec_canonical)
open PalPeg.GalilScaffoldSearchRun (SafeQuanta advance)
open PalPeg.GalilScaffoldDouble (waitStep enter)
open PalPeg.GalilLeafPres (safeCalls_debt)
open PalPeg.CloseoutReadyStage (DpSafeStage PacedL RunEntriesS)
open PalPeg.CloseoutPreload10 (PrepAt)
open PalPeg.CloseoutPreload13 (RunTrace run_step_quanta)
open PalPeg.CloseoutPreload14 (WaitTrace)
open PalPeg.CloseoutPreload17 (DoubleTrace)
open PalPeg.CloseoutPreload21 (ScanTrace)
open PalPeg.CloseoutPreload22 (ClockInv)
open PalPeg.CloseoutPreload23 (ScanSupplyInv)
open PalPeg.CloseoutPreload28 (StageInvD)
open PalPeg.CloseoutPreload31 (postRunF_round_trip)

/-! ## 1. `Canonical` is preserved along the legs -/

/-- The outer advance is a unary `dec` (or nothing): `Canonical` survives. -/
theorem canonical_advance {s : GalilScaffoldSearchFinish.State} (a : Bool)
    (hc : Canonical s.debt) : Canonical (advance a s).debt := by
  cases a
  · exact hc
  · exact dec_canonical _ hc

/-- Every quantum keeps the debt through its calls and pays by one `dec`. -/
theorem canonical_safeQuanta {s t : GalilScaffoldSearchFinish.State}
    {x y : GalilScaffoldControl.Machine 12} {as : List Bool}
    (h : SafeQuanta s x as t y) (hc : Canonical s.debt) : Canonical t.debt := by
  induction h with
  | nil => exact hc
  | cons s u t x y z a as hm hq hr ih =>
      apply ih
      apply canonical_advance
      rw [safeCalls_debt hq]
      exact hc

/-- A single `.run` tick preserves `Canonical`. -/
theorem canonical_run_step {c : GalilScaffoldPlace.Place} {a : Bool} {v v' : SearchVM}
    (hm : v.search.mode = Mode.run) (hs : searchStep c a v v')
    (hc : Canonical v.search.debt) : Canonical v'.search.debt := by
  obtain ⟨hq, -, -⟩ := run_step_quanta hm hs
  exact canonical_safeQuanta hq hc

/-- **NAMED — `Canonical` along a `.run` leg.** -/
theorem canonical_runTrace {as : List Bool} {v t : SearchVM}
    (hr : RunTrace as v t) (hc : Canonical v.search.debt) : Canonical t.search.debt := by
  induction hr with
  | nil => exact hc
  | cons c a as v v' t hm hs hr ih => exact ih (canonical_run_step hm hs hc)

#print axioms canonical_runTrace

/-- A single `.wait` tick preserves `Canonical`: `waitStep` never touches the
debt (`enter` only rewrites `mode`/`work`/`span`/`quarter`), then `advance`. -/
theorem canonical_wait_step {c : GalilScaffoldPlace.Place} {a : Bool} {v v' : SearchVM}
    (hm : v.search.mode = Mode.wait) (hs : searchStep c a v v')
    (hc : Canonical v.search.debt) : Canonical v'.search.debt := by
  unfold searchStep at hs
  rw [hm] at hs
  subst hs
  show Canonical (advance a (waitStep true v.search)).debt
  apply canonical_advance
  unfold waitStep
  split
  · exact hc
  · exact hc

/-- **NAMED — `Canonical` along a `.wait` leg.** -/
theorem canonical_waitTrace {as : List Bool} {v t : SearchVM}
    (hr : WaitTrace as v t) (hc : Canonical v.search.debt) : Canonical t.search.debt := by
  induction hr with
  | nil => exact hc
  | cons c a as v v' t hm hs hr ih => exact ih (canonical_wait_step hm hs hc)

#print axioms canonical_waitTrace

/-! ## 2. The event coupling — the one hypothesis -/

/-- **NAMED — the event coupling of the `.run` / `.wait` legs with the scan
leg.**  (a) the `.wait → .double` exit tick is the `false` event the stream
carries; (b) the scan leg from `p` extends over the two legs.  For a generic
`Frame σ` there is no map `State σ → SearchVM`, so neither half is provable
here; on `galilFrameS` (a) is `CloseoutPreload22.background_event_false` /
`compare_event_false_of_mismatch` and (b) is the `Tick` run itself. -/
def LegsCoupled {σ : Type} (F : Frame σ) (pre : List Bool) (p : State σ)
    (rs ws : List Bool) (a1 a2 : Bool) : Prop :=
  a2 = false ∧ ∃ (ts' : List Bool) (q' : State σ),
    ScanTrace F 2048 ts' (pre ++ (rs ++ a1 :: (ws ++ [false]))) p q'

/-- Projection (a): the `.wait` exit event is `false`. -/
theorem wait_exit_false {σ : Type} {F : Frame σ} {pre : List Bool} {p : State σ}
    {rs ws : List Bool} {a1 a2 : Bool} (h : LegsCoupled F pre p rs ws a1 a2) : a2 = false :=
  h.1

/-- Projection (b): the scan leg over the extended stream. -/
theorem scanTrace_extend_legs {σ : Type} {F : Frame σ} {pre : List Bool} {p : State σ}
    {rs ws : List Bool} {a1 a2 : Bool} (h : LegsCoupled F pre p rs ws a1 a2) :
    ∃ (ts' : List Bool) (q' : State σ),
      ScanTrace F 2048 ts' (pre ++ (rs ++ a1 :: (ws ++ [false]))) p q' :=
  h.2

/-! ## 3. The round trip with `hcan1` / `hcan0` discharged -/

/-- **NAMED — `postRunF_round_trip` with the `Canonical` premises derived from
the frame and `hs2` / `hsc` folded into `LegsCoupled`.**  Everything outside
the `PostRunF` frame and the leg traces is now the single hypothesis `hcoup`. -/
theorem postRunF_round_trip' {σ : Type} {F : Frame σ} {I : State σ → Prop}
    {k mw : ℕ} {pre rs ws bs : List Bool} {a1 a2 a3 : Bool}
    {cr cw : GalilScaffoldPlace.Place} {v t0 w0 w1 u0 : SearchVM} {p : State σ}
    (hsup : ScanSupplyInv F 2048 I)
    (hm : v.search.mode = Mode.run) (hsp : v.search.span = ofNat mw)
    (hlow : v.lower = ofNat k) (hcal : 8 * max k 1 ≤ mw)
    (hcan : Canonical v.search.debt)
    (hrun : RunTrace rs v t0) (ht0 : t0.search.mode = Mode.run)
    (hs1 : searchStep cr a1 t0 w0) (hw0 : w0.search.mode = Mode.wait)
    (hwait : WaitTrace ws w0 w1) (hw1 : w1.search.mode = Mode.wait)
    (hs2 : searchStep cw a2 w1 u0) (hne : u0.search.mode ≠ Mode.wait)
    (hcoup : LegsCoupled F pre p rs ws a1 a2)
    (hp : I p) (hclk : ClockInv 2048 p.ctl)
    (hblen : bs.length = mw)
    (hpaced : PacedL 2048 0 ((pre ++ (rs ++ a1 :: (ws ++ [false]))) ++ (bs ++ [a3]))) :
    ∃ t1 : SearchVM, DoubleTrace bs u0 t1 ∧ t1.search.mode = Mode.double ∧
      positive t1.search.work = false ∧ t1.search.span = ofNat (2 * mw) ∧
      t1.lower = ofNat k ∧
      ∀ (c' : GalilScaffoldPlace.Place) (t' : SearchVM), searchStep c' a3 t1 t' →
        PrepAt k (2 * mw) t' ∧ StageInvD k (2 * mw) t' ∧ t'.walker = c' ∧
          8 * max k 1 ≤ 2 * mw := by
  obtain ⟨ha2, ts', q', hsc⟩ := hcoup
  subst ha2
  have hct0 : Canonical t0.search.debt := canonical_runTrace hrun hcan
  have hcw0 : Canonical w0.search.debt := canonical_run_step ht0 hs1 hct0
  have hcan1 : Canonical w1.search.debt := canonical_waitTrace hwait hcw0
  have hcan0 : Canonical u0.search.debt := canonical_wait_step hw1 hs2 hcan1
  exact postRunF_round_trip hsup hm hsp hlow hcal hrun ht0 hs1 hw0 hwait hw1 hcan1
    hs2 hne hcan0 hsc hp hclk hblen hpaced

#print axioms postRunF_round_trip'

/-!
## 4. What is left

Closed: `canonical_runTrace`, `canonical_waitTrace` (§1) — `hcan1` / `hcan0`
of `CloseoutPreload31.postRunF_round_trip` are derived from the frame's
`Canonical v.search.debt`.

**NOT closed — `LegsCoupled` (§2).**  It is the event coupling of
`CloseoutPreload21` §4 (i) at the level of a generic `Frame σ`: `ScanTrace` has
no `SearchVM` in it, so the `false` at the `.wait` exit and the extension of the
scan leg over the two `searchStep` legs cannot be built from
`scanTrace_eq_runTrace` alone.  Discharging it needs the concrete frame
(`galilFrameS`, `searchLens`) and a lemma turning a `StepsAll` run whose search
projection is a `RunTrace` / `WaitTrace` into a `ScanTrace` with the same
booleans — `CloseoutPreload22` §1 gives the per-tick half of that.

**無条件 PAL ∈ PEG は未完.**
-/

end PalPeg.CloseoutPreload32
