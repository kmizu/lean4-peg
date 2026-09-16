import PalPeg.CloseoutReportCase
import PalPeg.CloseoutRadPack
import PalPeg.CloseoutCoreAudit
import PalPeg.CloseoutFairWitness
import PalPeg.GalilReplaySpan
import PalPeg.GalilFinalBaseNeed
import PalPeg.LocalSysConcrete
import PalPeg.LocalLedgerShift

/-!
# The shared contracts of the closeout (§5.1–5.3 of the proof plan)

This file is the **thin bundling layer** the parent owns.  It introduces no new
semantics: every field of every structure below is an existing type from the
development, and the only new inductive (`FairSteps`) is `StepsAll` with the
per-tick `GalilTickFair.Fair` datum carried alongside.

The point of the layer is negative as much as positive.  Each contract is
stated so that

* the **entry** is `GalilInvPlus3.InvLPS` (not a bare `InvL`, and not an
  `InvLPC` one hopes to strengthen again afterwards), so no全状態補強 of the
  form "any `InvL` state will do" is ever requested;
* the **search budget** is the `ReadyFuel … (headRank r.right * 2048 + c.clock)
  (headRank r.right)` shape that `CloseoutReportCase.reachAtC3_of_crossF`
  actually consumes, tied to the *same* event list that the segment produces —
  never an existential budget at the entry spent on a different event list;
* the **cost** is a `GalilTraceCost.CostedRun` over the *same* run as the
  `StepsAll`, so no semantics of run A is ever paired with a time bound of run
  B;
* no `hpres` / `StartShape` / unconditional `hpos` premise appears anywhere.

**無条件 PAL ∈ PEG は未完.**  The contracts are interfaces; the obligations they
name stay open in the ledger.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutContracts

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton PalPeg.GalilCheckpoints PalPeg.GalilTraceCost
open PalPeg.GalilIntervalCost PalPeg.GalilLedgerAssembly PalPeg.GalilLedgerQ64
open PalPeg.GalilLexMeasure
open PalPeg.GalilInvPlus PalPeg.GalilInvPlus2 PalPeg.GalilOracleM PalPeg.GalilOracleMC2
open PalPeg.GalilOracleMC3 PalPeg.GalilInvPlus3
open PalPeg.GalilFoundStage PalPeg.GalilFoundStageInv
open PalPeg.GalilSegmentConstructB PalPeg.GalilLeafEnds
open PalPeg.GalilTickFair (Fair)

/-! ## 1. `StageEntryC` — the reached stage entry -/

/-- **Contract 1: the stage entry.**  `InvLPS` (the landing invariant *with* the
stage data — the radius evaluation of a found tick and the preparation segment
both read it, and it cannot be recovered after dropping to `InvLPC`) together
with the entry search budget in the exact shape
`CloseoutReportCase.reachAtC3_of_crossF` consumes.

Note what is **not** here: no `hpres`, no `StartShape`, no `InvL`-for-every-state
reinforcement, and no unconditional position premise. -/
structure StageEntryC (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (c : Control) (r : GalilVM) : Prop where
  inv : InvLPS P q first raw c r
  fuel : ReadyFuel (searchLens.get r) (headRank r.right * 2048 + c.clock) (headRank r.right)

theorem StageEntryC.invLPC {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    {c : Control} {r : GalilVM} (h : StageEntryC P q first raw c r) : InvLPC raw c r :=
  invLPS_invLPC h.inv

theorem StageEntryC.stage {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    {c : Control} {r : GalilVM} (h : StageEntryC P q first raw c r) :
    ReplayStage raw P q first c r := invLPS_stage h.inv

/-- **Connected, consumer side.**  The crossing case of `MC4` over the contract:
this is `CloseoutReportCase.reachAtC3_of_crossF` with its two entry premises
replaced by the single bundle. -/
theorem reachAtC3_of_crossF_C (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m : ℕ) (hm1 : 1 ≤ m) (hmle : m ≤ raw.length)
    {c c' : Control} {r t : GalilVM}
    (hE : StageEntryC (PofC centre place entry raw) q first raw c r)
    (hsW : SegReachedW centre place entry q first raw c r c' t)
    (hlt : position r.right < 2 * m - 1) (hge : 2 * m - 1 ≤ position t.right) :
    ReachAtC3 (PofC centre place entry raw) q first raw m c r :=
  PalPeg.CloseoutReportCase.reachAtC3_of_crossF centre place entry q first raw m hm1 hmle
    hE.inv hE.fuel hsW hlt hge

/-! ## 2. `SegResult` — the result of one watched segment -/

/-- **Contract 2: the segment result.**  The *actual* event list `es`, the entry
and the exit of the `WatchSegE` it drives, its exact length and comparison
count, the head advance it causes, and the residual `ReadyFuel` at the exit —
all about the same `es`.  A budget quantified at the entry over some *other*
event list is exactly what this shape forbids. -/
def SegResult (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (c : Control) (r : GalilVM) (n K : ℕ) : Prop :=
  ∃ (es : List Bool) (cT : Control) (sT : GalilVM),
    WatchSegE P q first 2048 es c r cT sT ∧
    position sT.right = position r.right + es.count true ∧
    sT.center = r.center ∧
    ReadyFuel (searchLens.get sT) n K

/-! ## 3. `CostedRouteC` — semantics and time of **one** run -/

/-- `StepsAll` with the per-tick fairness datum.  Same shape, same `Q`, same
`delay`: forgetting `fair` returns the original run (`FairSteps.toStepsAll`). -/
inductive FairSteps (F : Frame GalilVM) (entry delay : ℕ) (Q : State GalilVM → Prop) :
    ℕ → State GalilVM → State GalilVM → Prop
  | zero (x : State GalilVM) (hx : Q x) : FairSteps F entry delay Q 0 x x
  | succ {n : ℕ} {x y z : State GalilVM} (hx : Q x) (h : Tick F delay x y)
      (hf : Fair entry delay x y) (hr : FairSteps F entry delay Q n y z) :
      FairSteps F entry delay Q (n+1) x z

theorem FairSteps.toStepsAll {F : Frame GalilVM} {entry delay : ℕ} {Q : State GalilVM → Prop}
    {n : ℕ} {x y : State GalilVM} (h : FairSteps F entry delay Q n x y) : StepsAll F delay Q n x y := by
  induction h with
  | zero x hx => exact .zero x hx
  | succ hx ht _ _ ih => exact .succ hx ht ih

theorem FairSteps.trans {F : Frame GalilVM} {entry delay : ℕ} {Q : State GalilVM → Prop}
    {m n : ℕ} {x y z : State GalilVM} (h1 : FairSteps F entry delay Q m x y)
    (h2 : FairSteps F entry delay Q n y z) : FairSteps F entry delay Q (m + n) x z := by
  induction h1 with
  | zero x hx => simpa using h2
  | succ hx ht hf _ ih =>
      exact Nat.succ_add _ _ ▸ FairSteps.succ hx ht hf (ih h2)

/-- **Contract 3: the costed route.**  One run: the `FairSteps` (hence the
`StepsAll`) and the `CostedRun` are indexed by the *same* `k` between the *same*
two states, and the landing carries `InvLPS` again. -/
def CostedRouteC (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (entry : ℕ)
    (c : Control) (r : GalilVM) (cT : Control) (sT : GalilVM) (k : ℕ) : Prop :=
  ∃ L : List Piece,
    FairSteps (galilFrameS P q first) entry 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩ ∧
    CostedRun r sT k L ∧
    InvLPS P q first raw cT sT

theorem CostedRouteC.stepsAll {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    {entry : ℕ} {c cT : Control} {r sT : GalilVM} {k : ℕ}
    (h : CostedRouteC P q first raw entry c r cT sT k) :
    StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩ := by
  obtain ⟨L, hrun, -, -⟩ := h
  exact hrun.toStepsAll

/-- **Connected, consumer side.**  A costed route that also makes progress and
respects the checkpoint position is a `CycleOutMC3` exit — the recursion of
`checkpoints_cost3` never leaves `InvLPS`. -/
theorem cycleOutMC3_of_costedRouteC {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    {entry m : ℕ} {c cT : Control} {r sT : GalilVM} {k : ℕ}
    (h : CostedRouteC P q first raw entry c r cT sT k)
    (hmu : mu raw sT < mu raw r) (hpos : position sT.right ≤ 2 * m - 1) :
    CycleOutMC3 P q first raw m c r := by
  obtain ⟨L, hrun, hcost, hland⟩ := h
  exact Or.inr ⟨cT, sT, k, L, hrun.toStepsAll, hcost, hland, hmu, hpos⟩

/-! ## 4. `FoundExit` — the common landing of the three found leaves -/

/-- **Contract 4: the found exit.**  The comparison-time leaf, the background
leaf and the in-replay leaf all return *this* type: the same run, the same cost
shape, the same position bound, and — in the `broke` branch — the stage datum
`ReplayStage` that `FoundRouteMC3.broke` and `FoundInReplayRouteMC3.broke`
require, since the break landing does not export its restart shape. -/
inductive FoundExit (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ)
    (c : Control) (r : GalilVM) : Prop
  | landed (cT : Control) (sT : GalilVM) (k : ℕ) (L : List Piece)
      (hst : StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩)
      (hcr : CostedRun r sT k L)
      (hM : MInv raw cT sT) (hR : ∃ (Rad : ℕ) (last : Counter), Restarted raw sT Rad last)
      (hres : FoundResidual raw cT sT) (hSpan : SpanRep sT)
      (hprog : position r.center < position sT.center)
      (hpos : position sT.right ≤ 2 * m - 1)
  | broke (cT : Control) (sT : GalilVM) (k : ℕ) (L : List Piece)
      (hst : StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩)
      (hcr : CostedRun r sT k L) (hIT : InvLP2 raw cT sT) (hcenT : CentreRep raw sT)
      (hstage : ReplayStage raw P q first cT sT)
      (hc : position sT.center = position r.center)
      (hlt : position r.right < position sT.right)
      (hpos : position sT.right ≤ 2 * m - 1)

/-- **Connected, consumer side.**  The found exit is exactly the non-`report`
part of `FoundInReplayRouteMC3`, so the in-replay leaf may return it verbatim. -/
theorem foundInReplayRouteMC3_of_foundExit {P : Shared} {q : ℕ} {first : Fin 9}
    {raw : List (Fin 2)} {m : ℕ} {c : Control} {r : GalilVM}
    (h : FoundExit P q first raw m c r) : FoundInReplayRouteMC3 P q first raw m c r := by
  cases h with
  | landed cT sT k L hst hcr hM hR hres hSpan hprog hpos =>
      exact .landed cT sT k L hst hcr hM hR hres hSpan hprog hpos
  | broke cT sT k L hst hcr hIT hcenT hstage hc hlt hpos =>
      exact .broke cT sT k L hst hcr hIT hcenT hstage hc hlt hpos

/-- **Connected, consumer side.**  The same value also feeds `FoundRouteMC3`,
whose `broke` field list is identical; the two `landed`-shaped constructors of
`FoundRouteMC3` are `FoundCost`-indexed, so a plain landing enters through
`FoundInReplayRouteMC3` and `cycleOutMC3_of_foundInReplay`. -/
theorem cycleOutMC3_of_foundExit (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m : ℕ) {c : Control} {r : GalilVM}
    (hIN : InvLPS (PofC centre place entry raw) q first raw c r)
    (h : FoundExit (PofC centre place entry raw) q first raw m c r) :
    CycleOutMC3 (PofC centre place entry raw) q first raw m c r :=
  cycleOutMC3_of_foundInReplay centre place entry q first raw m hIN
    (foundInReplayRouteMC3_of_foundExit h)

/-! ## 5. `CheckpointRunC` — the checkpoint run -/

/-- **Contract 5: the checkpoint run.**  The initial state, the checkpoint clock
`Tc`, the trace, the monotonicity, the report/`Refreshed` points, the interval
cost, and the finite bound `raw.length` — the conclusion of
`checkpoints_cost3`, verbatim, and nothing generalised to every run of the old
`PreTrace`. -/
def CheckpointRunC (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (x0 : State GalilVM) : Prop :=
  ∃ (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
    st 0 = x0 ∧ Tc 0 = 0 ∧
    Trace (galilFrameS P q first) 2048 (SoundScanNR raw) st (Tc raw.length) ∧
    (∀ m m', m ≤ m' → m' ≤ raw.length → Tc m ≤ Tc m') ∧
    (∀ m, 1 ≤ m → m ≤ raw.length → ReportPointAt P q first raw m (st (Tc m))) ∧
    (∀ m, 1 ≤ m → m < raw.length →
      Tc (m+1) - Tc m ≤ alpha' 2048 * (Cw raw (m+1) - Cw raw m) + beta' 2048)

/-- **Connected, producer side.**  `checkpoints_cost3` builds the contract from
an `InvLPS` entry alone: no `hstr`, no `StartShape`. -/
theorem checkpointRunC_of_cost3 (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (hor : CycleOracleMC3 P q first raw)
    {x0 : State GalilVM} {k0 : ℕ} {c : Control} {r : GalilVM}
    (hpre : StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k0 x0 ⟨c, r⟩)
    (hI : InvLPS P q first raw c r) (hpos : position r.right ≤ 1) :
    CheckpointRunC P q first raw x0 := by
  exact checkpoints_cost3 P q first raw hor hpre hI hpos

/-- The same, entered through `StageEntryC`. -/
theorem checkpointRunC_of_stageEntry (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (hor : CycleOracleMC3 P q first raw)
    {x0 : State GalilVM} {k0 : ℕ} {c : Control} {r : GalilVM}
    (hpre : StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k0 x0 ⟨c, r⟩)
    (hE : StageEntryC P q first raw c r) (hpos : position r.right ≤ 1) :
    CheckpointRunC P q first raw x0 :=
  checkpointRunC_of_cost3 P q first raw hor hpre hE.inv hpos

/-! ## 6. The local tracking contract -/

/-- **Contract 6: local tracking, option A.**  The tracking datum is
`LocalSysConcrete.Needy`: a **fixed** word `raw`, a real time `k`, an arrival
count `j ≤ raw.length`, the abstract index `stOf k` of the pre-loaded trace, and
the truncation correspondence `absState'' x = truncS (raw.length - j) (stOf k)`.

It is deliberately *not* "feeding an arbitrary letter preserves the run of the
same word": the arrival count is part of the datum and the truncation shrinks
with it (`LocalSysConcrete.needy_feedC`-shaped steps), so no `H_feed_track` over
arbitrary characters is assumed. -/
abbrev TrackC := @PalPeg.LocalSysConcrete.Needy

#check @PalPeg.LocalSysConcrete.Needy
#check @PalPeg.LocalSysConcrete.Tracked
#check @PalPeg.LocalTrackingLatch.micro
#check @PalPeg.LocalTrackingLatch.stAbs

/-! ## 7. The core contract, re-exported -/

/-- **Contract 7: the core.**  `CloseoutCoreAudit.CoreLocal` unchanged — one
`LocalStep`, one fixed encoding, the initial correspondence and the tick/feed
correspondences.  Re-exported here so that the closeout has a single name for
it. -/
abbrev CoreLocalC := @PalPeg.CloseoutCoreAudit.CoreLocal

#check @PalPeg.CloseoutCoreAudit.CoreLocal
#check @PalPeg.CloseoutCoreAudit.pal_in_peg_of_coreLocal

/-! ## 8. Producers and consumers this layer is meant to meet -/

#check @PalPeg.GalilInvPlus3.invLPS_of_boot
#check @PalPeg.GalilInvPlus3.invLPS_of_landed
#check @PalPeg.GalilInvPlus3.checkpoints_cost3
#check @PalPeg.GalilInvPlus3.FoundRouteMC3
#check @PalPeg.GalilInvPlus3.FoundInReplayRouteMC3
#check @PalPeg.GalilReplaySpan.ReadyFuelD
#check @PalPeg.GalilReplaySpan.RunEntriesPaced
#check @PalPeg.GalilReplaySpan.ReplayBudgetRD
#check @PalPeg.GalilReplaySpan.replay_after_fallback_general''_fuel'_of_decodes
#check @PalPeg.GalilSegmentConstructB.ReadyFuel
#check @PalPeg.CloseoutRadPack.RadLedger
#check @PalPeg.GalilFinalBaseNeed.PreTraceB
#check @PalPeg.GalilTickFair.Fair

end PalPeg.CloseoutContracts

#print axioms PalPeg.CloseoutContracts.reachAtC3_of_crossF_C
#print axioms PalPeg.CloseoutContracts.FairSteps.toStepsAll
#print axioms PalPeg.CloseoutContracts.FairSteps.trans
#print axioms PalPeg.CloseoutContracts.cycleOutMC3_of_costedRouteC
#print axioms PalPeg.CloseoutContracts.foundInReplayRouteMC3_of_foundExit
#print axioms PalPeg.CloseoutContracts.cycleOutMC3_of_foundExit
#print axioms PalPeg.CloseoutContracts.checkpointRunC_of_cost3
#print axioms PalPeg.CloseoutContracts.checkpointRunC_of_stageEntry
