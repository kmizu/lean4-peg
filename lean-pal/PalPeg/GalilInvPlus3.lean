import PalPeg.GalilOracleMC3
import PalPeg.GalilFoundStageInv

/-!
# The landing invariant with the stage data: `InvLPS`

`GalilOracleLeaves2.h_oracle_of_leaves'` still carries the two costed found
leaves `hfound` / `hfoundBg` open.  Their producers cannot be built from an
`InvLPC` entry, because the three lemmas that feed a found tick

* `GalilReplayBudgetProof.found_stage_data`,
* `GalilLaterRadius.found_radius_le_all_stages`,
* `GalilPrepConstruct.prep_segment_construct_of_found`

all read the *search history* of the tick: they need the found comparison to end
a segment out of a restarted state carrying the stage budget,
`Restarted raw r Rad last ∧ StageEntry Rad last` with a full clock, and
`InvLPC` records none of that.

That data is already packaged: `GalilFoundStage.ReplayStage raw P q first c s` is
exactly "`⟨c, s⟩` ends a `WatchSegE` out of a `Restarted`/`StageEntry` state with
`clock = 2048`", and it is closed under segments
(`GalilFoundStageInv.replayStage_trans`).  So

  `InvLPS P q first raw c r := InvLPC raw c r ∧ ReplayStage raw P q first c r`

and every landing of `GalilOracleMC3.cycleOracleMC2C_of_pieces'` (the pieces
theorem *without* the two refuted leaves `hquiet` / `houtReplay`, with
`StartShape` / `ReplayBudgetR` / `ReplayStageInv` / `RestartShape` and the
busy-replay leaf `hfoundReplay` in their place) establishes it:

* **boot** — `invLPC_of_boot` plus `init_restarted`'s `Restarted raw t 0 reset`;
  `StageEntry 0 reset` is free (`stageEntry_zero`) and the clock is inherited
  from `Control.initial 2048` (`init_clock_of_initial`).  `invLPS_of_boot`.
* **radius-`0` fallback landing** and **found landings, with and without a
  shift** — all three are `Inv` states (`invLPC_of_landed` /
  `inv_of_residual`), and `Inv` *already* carries `rest`, `stage` and
  `clock = 2048`, so the stage data is free there: `replayStage_of_inv`.
* **quiet replay landing** — `ReplayLanding`'s `rest : Restarted raw sT 0 reset`
  and `clock : cT.clock = 2048` start the segment, and the replay's own
  `WatchSegE` (branch (i) of `GalilOracleMC3.invScanO_of_replay_generalR`)
  carries it to the landing: `replayStage_after_replayLanding`.
* **busy replay landings** (`ChainEnd` / `BrokeAndRestarted`) — handed, as in
  `GalilOracleMC3`, to the single leaf `hfoundReplay`, at the strengthened value
  `FoundInReplayRouteMC3`: its `landed` exit is an `Inv` state (free), its
  `broke` exit takes the stage data as a field.
* **target-match continuation** — the report comparison at `2m-1` that does not
  start the chain is a `WatchSegE.matchIdle` step, so `replayStage_trans`
  carries the stage data across it: `reachAtC3_of_target_match`.
* **no-shift break landing** (`broke`) — `GalilInvPlus2.foundRouteMC_noshift''`
  does not export the fact that its landing is a restart (`GalilNoShiftStage`'s
  `fresh_break_stage` proves `StageEntry Rad w'.last` for the break, but the
  `Restarted` shape of the landing state is not carried through), so the
  `broke` constructor of `FoundRouteMC3` takes the stage data as a field.  It is
  an obligation of the (already named) leaves `hfound` / `hfoundBg`.

The recursion is then re-run over `InvLPS`: `ReachAtC3`, `CycleOutMC3`,
`CycleOracleMC3`, `checkpoints_cost3` (the trace proof of
`GalilOracleMC2.checkpoints_cost2` copied verbatim — it never inspects the
invariant) and `cycleOracleMC3_of_pieces`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.GalilInvPlus3

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton PalPeg.GalilOracleDischarge PalPeg.GalilOracleLocal
open PalPeg.GalilCheckpoints PalPeg.GalilTraceCost PalPeg.GalilLexMeasure
open PalPeg.GalilInvPlus PalPeg.GalilInvPlus2 PalPeg.GalilOracleMC
open PalPeg.GalilIntervalCost PalPeg.GalilLedgerQ64 PalPeg.GalilLedgerAssembly
open PalPeg.GalilGlueBLeaves PalPeg.GalilBranchInvariants2 PalPeg.GalilSegmentConstruct
open PalPeg.GalilNoShiftDischarge PalPeg.GalilOracleM PalPeg.GalilOracleMC2
open PalPeg.GalilFoundStage PalPeg.GalilFoundStageInv PalPeg.GalilChainCoupling
open PalPeg.GalilOracleLeaves2 PalPeg.GalilOracleMC3 PalPeg.GalilLeafOutReplay

/-! ## 1. The invariant -/

/-- **The landing invariant with the stage data.**  `InvLPC` (the local
recursion state, the entering counters, the copy pack and the centre head)
together with `ReplayStage`: the entry ends a `WatchSegE` out of a restarted
state whose radius meets the stage budget. -/
def InvLPS (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (c : Control) (r : GalilVM) : Prop :=
  InvLPC raw c r ∧ ReplayStage raw P q first c r

theorem invLPS_invLPC {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    {c : Control} {r : GalilVM} (h : InvLPS P q first raw c r) : InvLPC raw c r := h.1

theorem invLPS_stage {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    {c : Control} {r : GalilVM} (h : InvLPS P q first raw c r) :
    ReplayStage raw P q first c r := h.2

theorem invLPS_invL {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    {c : Control} {r : GalilVM} (h : InvLPS P q first raw c r) : InvL raw c r :=
  invLPC_invL h.1

/-! ## 2. The stage data at the landings -/

/-- **A restart landing carries the stage data outright.**  `Inv` has both
`rest : ∃ Rad last, Restarted raw r Rad last` and
`stage : ∀ Rad last, Restarted raw r Rad last → StageEntry Rad last`, and its
`mode` field pins `c.clock = 2048`, so the empty segment already witnesses
`ReplayStage`.  This is the radius-`0` fallback landing and both found
landings. -/
theorem replayStage_of_inv {raw : List (Fin 2)} {P : Shared} {q : ℕ} {first : Fin 9}
    {c : Control} {r : GalilVM} (h : Inv raw c r) : ReplayStage raw P q first c r := by
  obtain ⟨Rad, last, hR⟩ := h.rest
  exact replayStage_entry hR (h.stage Rad last hR) h.mode.2.2

/-- `InvLPS` at a restart landing. -/
theorem invLPS_of_inv {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    {c : Control} {r : GalilVM} (hIC : InvLPC raw c r) (h : Inv raw c r) :
    InvLPS P q first raw c r := ⟨hIC, replayStage_of_inv h⟩

/-- **The landed exit of a fallback, and every found landing.**
`GalilInvPlus2.invLPC_of_landed` with the stage data added: the landing is an
`Inv` state. -/
theorem invLPS_of_landed (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    {raw : List (Fin 2)} {k : ℕ} {x : State GalilVM} {cT : Control} {sT : GalilVM}
    (hx : CopyPack x.ctl x.vm)
    (hst : StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048 (SoundScanNR raw) k
      x ⟨cT, sT⟩)
    (hI : Inv raw cT sT) (hS : SpanRep sT) :
    InvLPS (PofC centre place entry raw) q first raw cT sT :=
  ⟨invLPC_of_landed centre place entry q first hx hst hI hS, replayStage_of_inv hI⟩

/-- **The boot landing.**  `GalilScaffoldTopInitRestart.init_restarted` leaves
`Restarted raw r 0 reset`, `GalilRestartStage.stageEntry_zero` gives
`StageEntry 0 reset`, and `init_clock_of_initial` keeps the clock at `2048`;
`GalilOracleMC2.invLPC_of_boot` supplies the copy pack. -/
theorem invLPS_of_boot (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9) (d : ℕ)
    {raw : List (Fin 2)} {n : ℕ} {c : Control} {r : GalilVM}
    (h : Steps (galilFrameS (PofC centre place entry raw) q first) 2048 n
      ⟨GalilScaffoldController.initial d, GalilBootVM.initVM0 raw⟩ ⟨c, r⟩)
    (hI : InvLP raw c r) (hR : Restarted raw r 0 reset) (hcl : c.clock = 2048) :
    InvLPS (PofC centre place entry raw) q first raw c r :=
  ⟨invLPC_of_boot centre place entry q first d h hI (centreRep_of_restarted hR),
    replayStage_entry hR (stageEntry_zero reset) hcl⟩

/-- **The `init` tick supplies exactly the three ingredients of
`invLPS_of_boot`.**  `init_restarted` at the concrete shared record. -/
theorem init_stage_data (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9) (delay : ℕ)
    (c : Control) (hm : c.mode = .init) (hcl : c.clock = 2048) (s0 : GalilVM)
    (a : Fin 2) (rest : List (Fin 2)) (h0 : s0.right = initialHead (a :: rest))
    (hrad : s0.radius = reset) (hlen : s0.length = reset) :
    ∃ t : GalilVM,
      Tick (galilFrameS (PofC centre place entry (a :: rest)) q first) delay ⟨c, s0⟩
        ⟨{c with mode := .scan, output := true}, t⟩ ∧
      Restarted (a :: rest) t 0 reset ∧ StageEntry 0 reset ∧
      ({c with mode := .scan, output := true} : Control).clock = 2048 := by
  obtain ⟨t, htick, hR, -⟩ :=
    init_restarted (onLetterVM (a :: rest)) leftFirstVM shiftGuardVM
      beginShiftVM' beginFallbackVM' (restartVM entry) centre place entry q first delay c hm s0
      a rest h0 hrad hlen
  exact ⟨t, htick, hR, stageEntry_zero reset, hcl⟩

/-- **The replay landing.**  `GalilOracleDischarge.ReplayLanding` starts the
segment (`rest : Restarted raw sT 0 reset`, `clock : cT.clock = 2048`,
`stageEntry_zero`), and the replay's own `WatchSegE` carries the stage data to
the landing. -/
theorem replayStage_after_replayLanding {raw : List (Fin 2)} {P : Shared} {q : ℕ} {first : Fin 9}
    {cT : Control} {sT : GalilVM} {R : ℕ} {es : List Bool} {c' : Control} {t' : GalilVM}
    (hL : ReplayLanding raw cT sT R)
    (hseg : WatchSegE P q first 2048 es cT sT c' t') :
    ReplayStage raw P q first c' t' :=
  replayStage_trans (replayStage_entry hL.rest (stageEntry_zero reset) hL.clock) hseg

#print axioms replayStage_of_inv
#print axioms invLPS_of_inv
#print axioms invLPS_of_landed
#print axioms invLPS_of_boot
#print axioms init_stage_data
#print axioms replayStage_after_replayLanding

/-! ## 3. The recursion over `InvLPS` -/

/-- `GalilOracleMC2.ReachAtC2` with the resume continuation carrying `InvLPS`. -/
def ReachAtC3 (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ)
    (c : Control) (r : GalilVM) : Prop :=
  ∃ (y : State GalilVM) (k : ℕ) (L : List Piece),
    StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ y ∧
    CostedRun r y.vm k L ∧
    PalPeg.GalilReportPrefix.ReportPointAt raw m y ∧ Refreshed P q first y ∧
    (m < raw.length → ∃ (c' : Control) (r' : GalilVM) (k' : ℕ) (L' : List Piece),
      StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k' y ⟨c', r'⟩ ∧
      CostedRun y.vm r' k' L' ∧
      InvLPS P q first raw c' r' ∧ position r'.right ≤ 2 * (m+1) - 1)

/-- Forgetting the stage data of the continuation. -/
theorem reachAtC2_of_3 {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)} {m : ℕ}
    {c : Control} {r : GalilVM} (h : ReachAtC3 P q first raw m c r) :
    ReachAtC2 P q first raw m c r := by
  obtain ⟨y, k, L, hst, hcr, hrp, hfr, hcont⟩ := h
  refine ⟨y, k, L, hst, hcr, hrp, hfr, fun hlt => ?_⟩
  obtain ⟨c', r', k', L', hst', hcr', hI, hp⟩ := hcont hlt
  exact ⟨c', r', k', L', hst', hcr', hI.1, hp⟩

/-- `GalilOracleMC2.CycleOutMC2C` over `InvLPS`. -/
def CycleOutMC3 (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ)
    (c : Control) (r : GalilVM) : Prop :=
  ReachAtC3 P q first raw m c r ∨
    ∃ (cT : Control) (sT : GalilVM) (k : ℕ) (L : List Piece),
      StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩ ∧
      CostedRun r sT k L ∧
      InvLPS P q first raw cT sT ∧ mu raw sT < mu raw r ∧
      position sT.right ≤ 2 * m - 1

/-- `GalilOracleMC2.CycleOracleMC2C` over `InvLPS`. -/
def CycleOracleMC3 (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) : Prop :=
  ∀ (m : ℕ) (c : Control) (r : GalilVM), 1 ≤ m → m ≤ raw.length → InvLPS P q first raw c r →
    position r.right ≤ 2 * m - 1 → CycleOutMC3 P q first raw m c r

/-- The centre-progress exit. -/
theorem cycleOutMC3_of_centre {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)} {m : ℕ}
    {c : Control} {r : GalilVM} {cT : Control} {sT : GalilVM} {k : ℕ} {L : List Piece}
    (hI : InvLPS P q first raw c r)
    (hst : StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩)
    (hcr : CostedRun r sT k L) (hIT : InvLPS P q first raw cT sT)
    (hlt : position r.center < position sT.center) (hp : position sT.right ≤ 2 * m - 1) :
    CycleOutMC3 P q first raw m c r :=
  Or.inr ⟨cT, sT, k, L, hst, hcr, hIT,
    mu_lt_of_centre (invS_center_le (invLPS_invL hI).1) (invLPS_invL hIT) hlt, hp⟩

/-- The no-shift exit (centre kept, right head strictly up). -/
theorem cycleOutMC3_of_noshift {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)} {m : ℕ}
    {c : Control} {r : GalilVM} {cT : Control} {sT : GalilVM} {k : ℕ} {L : List Piece}
    (hst : StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩)
    (hcr : CostedRun r sT k L) (hIT : InvLPS P q first raw cT sT)
    (hc : position sT.center = position r.center) (hlt : position r.right < position sT.right)
    (hp : position sT.right ≤ 2 * m - 1) : CycleOutMC3 P q first raw m c r :=
  Or.inr ⟨cT, sT, k, L, hst, hcr, hIT, mu_lt_of_right (invLPS_invL hIT) hc hlt, hp⟩

theorem reachC3_fuel (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (hor : CycleOracleMC3 P q first raw) (m : ℕ) (hm1 : 1 ≤ m) (hmle : m ≤ raw.length) :
    ∀ (n : ℕ) (c : Control) (r : GalilVM), mu raw r ≤ n → InvLPS P q first raw c r →
      position r.right ≤ 2 * m - 1 → ReachAtC3 P q first raw m c r := by
  intro n
  induction n with
  | zero =>
    intro c r hn hI hp
    rcases hor m c r hm1 hmle hI hp with hdone | ⟨cT, sT, k, L, _, _, _, hlt, _⟩
    · exact hdone
    · omega
  | succ n ih =>
    intro c r hn hI hp
    rcases hor m c r hm1 hmle hI hp with hdone | ⟨cT, sT, k, L, hst, hcr, hIT, hlt, hpT⟩
    · exact hdone
    · obtain ⟨y, k', L', hst', hcr', hrp, hfr, hcont⟩ := ih cT sT (by omega) hIT hpT
      exact ⟨y, k + k', L ++ L', stepsAll_trans hst hst', costedRun_trans hcr hcr', hrp, hfr, hcont⟩

theorem reachC3_from_invLPS (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (hor : CycleOracleMC3 P q first raw) {m : ℕ} (hm1 : 1 ≤ m) (hmle : m ≤ raw.length)
    {c : Control} {r : GalilVM} (hI : InvLPS P q first raw c r)
    (hp : position r.right ≤ 2 * m - 1) : ReachAtC3 P q first raw m c r :=
  reachC3_fuel P q first raw hor m hm1 hmle _ c r le_rfl hI hp

/-! ## 4. The checkpoint trace, over `InvLPS` -/

theorem checkpoints_cost3_upto (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (hor : CycleOracleMC3 P q first raw)
    {x0 : State GalilVM} {k0 : ℕ} {c : Control} {r : GalilVM}
    (hpre : StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k0 x0 ⟨c, r⟩)
    (hI : InvLPS P q first raw c r) (hpos : position r.right ≤ 1) :
    ∀ M, M ≤ raw.length →
    ∃ (st : ℕ → State GalilVM) (Tc : ℕ → ℕ) (e : ℕ),
      st 0 = x0 ∧ Tc 0 = 0 ∧ Trace (galilFrameS P q first) 2048 (SoundScanNR raw) st e ∧
      (∀ m, m < M → Tc m ≤ Tc (m+1)) ∧ Tc M ≤ e ∧
      (∀ m, 1 ≤ m → m ≤ M →
        PalPeg.GalilReportPrefix.ReportPointAt raw m (st (Tc m)) ∧
        Refreshed P q first (st (Tc m))) ∧
      (∀ m, 1 ≤ m → m < M →
        Tc (m+1) - Tc m ≤ alpha' 2048 * (Cw raw (m+1) - Cw raw m) + beta' 2048) ∧
      (M < raw.length → ∃ (c' : Control) (r' : GalilVM),
        st e = ⟨c', r'⟩ ∧ InvLPS P q first raw c' r' ∧ position r'.right ≤ 2 * (M+1) - 1 ∧
        (1 ≤ M → ∃ L : List Piece, CostedRun (st (Tc M)).vm r' (e - Tc M) L)) := by
  intro M
  induction M with
  | zero =>
    intro _
    obtain ⟨g, hg0, hgn, htr⟩ := stepsAll_fn hpre
    refine ⟨g, fun _ => 0, k0, hg0, rfl, htr, fun m hm => absurd hm (Nat.not_lt_zero _),
      Nat.zero_le _, fun m h1 h2 => absurd h1 (by omega), fun m h1 h2 => absurd h2 (by omega),
      fun _ => ⟨c, r, hgn, hI, by omega, fun h => absurd h (by omega)⟩⟩
  | succ M ih =>
    intro hM
    obtain ⟨st, Tc, e, hst0, hTc0, htr, hmono, hTcM, hchk, hcost, hres⟩ := ih (by omega)
    obtain ⟨c', r', hste, hI', hp', hpend⟩ := hres (by omega)
    obtain ⟨y, k, L2, hrun, hcr, hrp, hfr, hcont⟩ :=
      reachC3_from_invLPS P q first raw hor (m := M+1) (by omega) hM hI' hp'
    obtain ⟨g1, hg10, hg1k, htr1⟩ := stepsAll_fn hrun
    have hj1 : st e = g1 0 := by rw [hste, hg10]
    set st1 := concat st g1 e with hst1
    have htr1' : Trace (galilFrameS P q first) 2048 (SoundScanNR raw) st1 (e + k) :=
      trace_concat htr htr1 hj1
    have hst1y : st1 (e + k) = y := by rw [hst1, concat_end st g1 hj1, hg1k]
    obtain ⟨st2, e2, htr2, hagree, hle2, hres2⟩ :
        ∃ (st2 : ℕ → State GalilVM) (e2 : ℕ),
          Trace (galilFrameS P q first) 2048 (SoundScanNR raw) st2 e2 ∧
          (∀ i, i ≤ e + k → st2 i = st1 i) ∧ e + k ≤ e2 ∧
          (M + 1 < raw.length → ∃ (c'' : Control) (r'' : GalilVM),
            st2 e2 = ⟨c'', r''⟩ ∧ InvLPS P q first raw c'' r'' ∧
            position r''.right ≤ 2 * (M+1+1) - 1 ∧
            ∃ L : List Piece, CostedRun y.vm r'' (e2 - (e + k)) L) := by
      by_cases hlt : M + 1 < raw.length
      · obtain ⟨c'', r'', k', L', hrun2, hcr2, hI2, hp2⟩ := hcont hlt
        obtain ⟨g2, hg20, hg2k, htr2⟩ := stepsAll_fn hrun2
        have hj2 : st1 (e + k) = g2 0 := by rw [hst1y, hg20]
        refine ⟨concat st1 g2 (e + k), e + k + k', trace_concat htr1' htr2 hj2,
          fun i hi => concat_le st1 g2 hi, by omega, fun _ => ⟨c'', r'', ?_, hI2, hp2, L', ?_⟩⟩
        · rw [concat_end st1 g2 hj2, hg2k]
        · rw [show e + k + k' - (e + k) = k' by omega]; exact hcr2
      · exact ⟨st1, e + k, htr1', fun _ _ => rfl, le_rfl, fun h => absurd h hlt⟩
    have hTcle : ∀ m, m ≤ M → Tc m ≤ e := fun m hm =>
      le_trans (mono_of_step Tc M hmono m M hm le_rfl) hTcM
    have hst2old : ∀ m, m ≤ M → st2 (Tc m) = st (Tc m) := by
      intro m hm
      rw [hagree _ (by have := hTcle m hm; omega), hst1, concat_le st g1 (hTcle m hm)]
    have hst2y : st2 (e + k) = y := by rw [hagree _ le_rfl, hst1y]
    refine ⟨st2, fun m => if m ≤ M then Tc m else e + k, e2, ?_, ?_, htr2, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hagree 0 (by omega), hst1, concat_le st g1 (Nat.zero_le _), hst0]
    · simp [hTc0]
    · intro m hm
      by_cases hm' : m + 1 ≤ M
      · simp only [hm', show m ≤ M by omega, if_true]; exact hmono m (by omega)
      · have hmM : m = M := by omega
        subst hmM
        simp only [le_refl, if_true, hm', if_false]
        exact le_trans hTcM (Nat.le_add_right _ _)
    · simp only [show ¬ M + 1 ≤ M by omega, if_false]; exact hle2
    · intro m h1 h2
      by_cases hm' : m ≤ M
      · simp only [hm', if_true]
        rw [hst2old m hm']
        exact hchk m h1 hm'
      · have hmM : m = M + 1 := by omega
        subst hmM
        simp only [hm', if_false]
        rw [hst2y]
        exact ⟨hrp, hfr⟩
    · intro m h1 h2
      by_cases hm' : m + 1 ≤ M
      · simp only [hm', show m ≤ M by omega, if_true]
        exact hcost m h1 (by omega)
      · have hmM : m = M := by omega
        subst hmM
        simp only [le_refl, if_true, hm', if_false]
        obtain ⟨L1, hcr1⟩ := hpend h1
        have hall := costedRun_trans hcr1 hcr
        have hTm := hTcle m le_rfl
        obtain ⟨hrp0, hfr0⟩ := hchk m h1 le_rfl
        have hc' : CostedRun (st (Tc m)).vm y.vm (e + k - Tc m) (L1 ++ L2) := by
          rw [show e + k - Tc m = e - Tc m + k by omega]; exact hall
        exact interval_cost_of_costedRun h1 hrp0 hfr0 hrp hfr hc'
    · intro hlt
      obtain ⟨c'', r'', h1, h2, h3, L, h4⟩ := hres2 hlt
      refine ⟨c'', r'', h1, h2, h3, fun _ => ⟨L, ?_⟩⟩
      simp only [show ¬ M + 1 ≤ M by omega, if_false]
      rw [hst2y]
      exact h4

/-- **`checkpoints_cost3`.**  `GalilOracleMC2.checkpoints_cost2` over the oracle
carrying the stage data.  The entry state is only required to be `InvLPS`
(`invLPS_of_boot` at the boot); there is no `hstr` anywhere, because the
recursion never leaves `InvLPS`. -/
theorem checkpoints_cost3 (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (hor : CycleOracleMC3 P q first raw)
    {x0 : State GalilVM} {k0 : ℕ} {c : Control} {r : GalilVM}
    (hpre : StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k0 x0 ⟨c, r⟩)
    (hI : InvLPS P q first raw c r) (hpos : position r.right ≤ 1) :
    ∃ (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      st 0 = x0 ∧ Tc 0 = 0 ∧
      Trace (galilFrameS P q first) 2048 (SoundScanNR raw) st (Tc raw.length) ∧
      (∀ m m', m ≤ m' → m' ≤ raw.length → Tc m ≤ Tc m') ∧
      (∀ m, 1 ≤ m → m ≤ raw.length →
        PalPeg.GalilLedgerAssembly.ReportPointAt P q first raw m (st (Tc m))) ∧
      (∀ m, 1 ≤ m → m < raw.length →
        Tc (m+1) - Tc m ≤ alpha' 2048 * (Cw raw (m+1) - Cw raw m) + beta' 2048) := by
  obtain ⟨st, Tc, e, hst0, hTc0, htr, hmono, hTcM, hchk, hcost, -⟩ :=
    checkpoints_cost3_upto P q first raw hor hpre hI hpos raw.length le_rfl
  exact ⟨st, Tc, hst0, hTc0, trace_le htr hTcM, mono_of_step Tc raw.length hmono,
    fun m h1 h2 => ledgerAt_of_prefix (hchk m h1 h2).1 (hchk m h1 h2).2, hcost⟩

/-- The recursion over `InvLPS` also delivers the weaker `ReachAtC2`. -/
theorem reachC2_from_invLPS (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (hor : CycleOracleMC3 P q first raw) {m : ℕ} (hm1 : 1 ≤ m) (hmle : m ≤ raw.length)
    {c : Control} {r : GalilVM} (hI : InvLPS P q first raw c r)
    (hp : position r.right ≤ 2 * m - 1) : ReachAtC2 P q first raw m c r :=
  reachAtC2_of_3 (reachC3_from_invLPS P q first raw hor hm1 hmle hI hp)

#print axioms reachAtC2_of_3
#print axioms cycleOutMC3_of_centre
#print axioms cycleOutMC3_of_noshift
#print axioms reachC3_from_invLPS
#print axioms checkpoints_cost3
#print axioms reachC2_from_invLPS

/-! ## 5. The routes over `InvLPS` -/

/-- `GalilOracleMC2.FallbackRouteMC2` with the report exit strengthened to
`ReachAtC3`.  The two landings are unchanged: the radius-`0` landing is an `Inv`
state (`replayStage_of_inv`) and the replayed landing is reached from
`ReplayLanding`'s restart by the replay's own segment
(`replayStage_after_replayLanding`). -/
inductive FallbackRouteMC3 (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ)
    (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM) : Prop
  | report (h : ReachAtC3 P q first raw m c r)
  | landed (fb : ℕ) (cT : Control) (sT : GalilVM)
      (hst : StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) (1 + fb) ⟨c', t⟩ ⟨cT, sT⟩)
      (hD : FppData raw t fb 0)
      (hland : position sT.center = position (right t.right) - 0) (hCR : sT.center = sT.right)
      (hI : Inv raw cT sT) (hSpan : SpanRep sT) (hprog : position t.center < position sT.center)
      (hpos : position (right t.right) ≤ 2 * m - 1)
  | replaying (fb R : ℕ) (cT : Control) (sT : GalilVM)
      (hst : StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) (1 + fb) ⟨c', t⟩ ⟨cT, sT⟩)
      (hD : FppData raw t fb R) (hL : ReplayLanding raw cT sT R) (hSpan : SpanRep sT)
      (hland : position sT.center = position (right t.right) - R) (hCR : sT.center = sT.right)
      (hprog : position t.center < position sT.center)
      (hpos : position (right t.right) ≤ 2 * m - 1)

/-- **The found route whose preparation already happened inside the replay, over
`InvLPS`.**  `GalilOracleMC3.FoundInReplayRouteMC2` with the report exit at
`ReachAtC3`; `landed` is an `Inv` state (stage data free), `broke` carries it. -/
inductive FoundInReplayRouteMC3 (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ)
    (c : Control) (r : GalilVM) : Prop
  | report (h : ReachAtC3 P q first raw m c r)
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

theorem cycleOutMC3_of_foundInReplay (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m : ℕ) {c : Control} {r : GalilVM}
    (hIN : InvLPS (PofC centre place entry raw) q first raw c r)
    (h : FoundInReplayRouteMC3 (PofC centre place entry raw) q first raw m c r) :
    CycleOutMC3 (PofC centre place entry raw) q first raw m c r := by
  cases h with
  | report h => exact Or.inl h
  | landed cT sT k L hst hcr hM hR hres hSpan hprog hpos =>
      exact cycleOutMC3_of_centre hIN hst hcr
        (invLPS_of_landed centre place entry q first hIN.1.1.2 hst
          (inv_of_residual hM hR hres) hSpan) hprog hpos
  | broke cT sT k L hst hcr hIT hcenT hstage hc hlt hpos =>
      exact cycleOutMC3_of_noshift hst hcr ⟨⟨hIT, hcenT⟩, hstage⟩ hc hlt hpos

/-- **The mismatch exit over `InvLPS`, without `hquiet` and `houtReplay`.**
`GalilOracleMC3.cycleOutMC2C_of_fallback'` with the stage data carried to every
landing: the radius-`0` landing is an `Inv` state, the quiet replay landing is
reached from `ReplayLanding`'s restart by the replay's own segment
(`replayStage_after_replayLanding`), and the two busy branches are handed to
`hfoundReplay` at the strengthened value `FoundInReplayRouteMC3`. -/
theorem cycleOutMC3_of_fallback' (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m : ℕ) (hm1 : 1 ≤ m) (hmle : m ≤ raw.length)
    (hex : ∀ s, (PofC centre place entry raw).replayExhausted s = zero s.replay)
    (hsearch : ∀ s : GalilVM, SearchReady (searchLens.get s) →
      ∀ a : Bool, ∃ v, searchEffect (PofC centre place entry raw) a s v)
    (hpres : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s) →
      searchEffect (PofC centre place entry raw) a s v → SearchReady v)
    (hshape : PalPeg.GalilWatchOkInst.StartShape (PofC centre place entry raw))
    (hbudget : PalPeg.GalilFoundStage.ReplayBudgetR raw (PofC centre place entry raw) q first 2048)
    (hstageInv : PalPeg.GalilFoundStage.ReplayStageInv raw (PofC centre place entry raw) q first)
    (hrs : PalPeg.GalilReplaySpan.RestartShape (PofC centre place entry raw))
    (hfoundReplay : ∀ (c : Control) (r : GalilVM) (cT : Control) (sT : GalilVM) (R k : ℕ),
      1 ≤ m → m ≤ raw.length → InvLPS (PofC centre place entry raw) q first raw c r →
      StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048 (SoundScanNR raw) k
        ⟨c, r⟩ ⟨cT, sT⟩ →
      ReplayLanding raw cT sT R → SpanRep sT →
      position r.center < position sT.center → position sT.right ≤ 2 * m - 1 →
      (PalPeg.GalilReplaySpan.ChainEnd raw (PofC centre place entry raw) q first 2048
          (position sT.right + R) cT sT 0 R ∨
        PalPeg.GalilReplaySpan.BrokeAndRestarted raw (PofC centre place entry raw) q first 2048
          cT sT) →
      FoundInReplayRouteMC3 (PofC centre place entry raw) q first raw m c r)
    {c c' : Control} {r t : GalilVM} {es : List Bool}
    (hIN : InvLPS (PofC centre place entry raw) q first raw c r)
    (hw : WatchSegE (PofC centre place entry raw) q first 2048 es c r c' t)
    (hcen : t.center = r.center) (hc1 : c'.clock = 1) (hav : canRight t.right)
    (h : FallbackRouteMC3 (PofC centre place entry raw) q first raw m c r c' t) :
    CycleOutMC3 (PofC centre place entry raw) q first raw m c r := by
  have hIC : InvLPC raw c r := hIN.1
  have hI : InvL raw c r := invLPC_invL hIC
  obtain ⟨⟨R0, hi0⟩, hc0, -⟩ := invL_entry hI
  have hrun0 := seg_run centre place entry q first raw hI hw
  cases h with
  | report h => exact Or.inl h
  | landed fb cT sT hst hD hland hCR hIT hSpan hprog hpos =>
      obtain ⟨Rad, ℓ, a, xs, rs', q', a₀, ls₀, rs₀, q₀, gap₀, lower, span, y, hi, hRR, hSt, hv, hkC,
        hdec, hraw, hraw₀, hC₀, hspan, hres, hidle, hlow, hR, hfb⟩ := hD
      obtain ⟨L, w, hw', e, hcr, -, -, -, -, -, hr'⟩ :=
        GalilCostedFallback.costedRun_fallback_zero raw (PofC centre place entry raw) q first hw hi0
          hc0 hc1 (t := sT) hi hav hRR hSt ℓ hv hkC a xs rs' q' hdec hraw a₀ ls₀ rs₀ q₀ gap₀ hraw₀
          hC₀ hspan hres hidle hlow fb hR hfb hland hCR
      have hall := stepsAll_trans hrun0 hst
      rw [show es.length + (1 + fb) = es.length + 1 + fb by omega] at hall
      exact cycleOutMC3_of_centre hIN hall hcr
        (invLPS_of_landed centre place entry q first hIC.1.2 hall hIT hSpan)
        (by rw [← hcen]; exact hprog) (by rw [hr']; exact hpos)
  | replaying fb R cT sT hst hD hL hSpan hland hCR hprog hpos =>
      have hall0 := stepsAll_trans hrun0 hst
      rw [show es.length + (1 + fb) = es.length + 1 + fb by omega] at hall0
      have hprogR : position r.center < position sT.center := by rw [← hcen]; exact hprog
      have hposR : position sT.right ≤ 2 * m - 1 := by
        have h1 : position sT.right = position sT.center := by rw [hCR]
        have h2 : position sT.center = position (right t.right) - R := hland
        omega
      rcases invScanO_of_replay_generalR raw (PofC centre place entry raw) rfl rfl q first 2048
          hex (by norm_num) hsearch hpres hshape hbudget hstageInv hrs R hL.pos cT sT hL.mode
          hL.clock hL.replaying hL.rest hL.replay hL.minv hL.frontier hL.shiftIdle with
        ⟨esR, c'', t'', hseg, hstR, hlen, hcnt, hrr, hcc, hO⟩ | hEnd | ⟨hBr, -⟩
      · obtain ⟨Rad, ℓ, a, xs, rs', q', a₀, ls₀, rs₀, q₀, gap₀, lower, span, y, hi, hRR, hSt, hv,
          hkC, hdec, hraw, hraw₀, hC₀, hspan, hres, hidle, hlow, hR, hfb⟩ := hD
        obtain ⟨L, w, hw', e, hcr, -, -, -, -, -, hr'⟩ :=
          GalilCostedFallback.costedRun_fallback_replay raw (PofC centre place entry raw) q first hw
            hi0 hc0 hc1 (t := sT) (t' := t'') hi hav hRR hSt ℓ hv hkC a xs rs' q' hdec hraw a₀ ls₀
            rs₀ q₀ gap₀ hraw₀ hC₀ hspan hres hidle hlow fb esR R hR hfb hlen hland hCR hrr hcc
        have hall := stepsAll_trans hall0 hstR
        have hRRt : RadiusRep t''.radius R := by
          have h0 := radiusRep_watchSegE _ q first 2048 hseg hL.rest.2.2.2.2.1
          rw [hcnt, Nat.zero_add] at h0
          exact h0
        have hE : EntryCounters raw t'' :=
          entryCounters_of_invScan hO.1 hRRt (spanRep_watchSegE _ q first 2048 hseg hSpan)
            (canonical_length_watchSegE _ q first 2048 hseg hL.rest.2.2.2.2.2.1)
        have hIL : InvLP raw c'' t'' := ⟨invL_of_run hall (Or.inr ⟨R, hO.1⟩), hE⟩
        exact cycleOutMC3_of_centre hIN hall hcr
          ⟨⟨invLP2_of_stepsAll centre place entry q first hIC.1.2 hall hIL,
              (invScanC_of_restart hL.rest hcc hO.1).2⟩,
            replayStage_after_replayLanding hL hseg⟩
          (by rw [hcc]; exact hprogR) (by rw [hr']; exact hpos)
      · exact cycleOutMC3_of_foundInReplay centre place entry q first raw m hIN
          (hfoundReplay c r cT sT R _ hm1 hmle hIN hall0 hL hSpan hprogR hposR (Or.inl hEnd))
      · exact cycleOutMC3_of_foundInReplay centre place entry q first raw m hIN
          (hfoundReplay c r cT sT R _ hm1 hmle hIN hall0 hL hSpan hprogR hposR (Or.inr hBr))

/-- `GalilOracleMC2.FoundRouteMC2` with the report exit strengthened to
`ReachAtC3` and the `broke` landing carrying the stage data.  `shift` and
`noShift` land in `Inv` states, so their stage data is free
(`replayStage_of_inv`); `GalilInvPlus2.foundRouteMC_noshift''` does not export
the restart shape of the break landing, so `broke` takes `ReplayStage` as a
field. -/
inductive FoundRouteMC3 (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ)
    (c : Control) (r : GalilVM) (c0 : Control) (s0 : GalilVM) : Prop
  | report (h : ReachAtC3 P q first raw m c r)
  | shift (cT : Control) (sT : GalilVM) (hcost : FoundCost P q first raw c0 s0 cT sT)
      (hM : MInv raw cT sT) (hR : ∃ (Rad : ℕ) (last : Counter), Restarted raw sT Rad last)
      (hres : FoundResidual raw cT sT) (hSpan : SpanRep sT)
      (hprog : position s0.center < position sT.center)
      (hpos : position sT.right ≤ 2 * m - 1)
  | noShift (cT : Control) (sT : GalilVM) (hcost : FoundCost P q first raw c0 s0 cT sT)
      (hM : MInv raw cT sT) (hR : ∃ (Rad : ℕ) (last : Counter), Restarted raw sT Rad last)
      (hres : FoundResidual raw cT sT) (hSpan : SpanRep sT)
      (hprog : position s0.center < position sT.center)
      (hpos : position sT.right ≤ 2 * m - 1)
  | broke (cT : Control) (sT : GalilVM) (k : ℕ) (L : List Piece)
      (hst : StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩)
      (hcr : CostedRun r sT k L) (hIT : InvLP2 raw cT sT) (hcenT : CentreRep raw sT)
      (hstage : ReplayStage raw P q first cT sT)
      (hc : position sT.center = position r.center)
      (hlt : position r.right < position sT.right)
      (hpos : position sT.right ≤ 2 * m - 1)

/-- **The found exit over `InvLPS`**, the found route started at the segment end. -/
theorem cycleOutMC3_of_found (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m : ℕ) {c c' : Control} {r t : GalilVM} {es : List Bool}
    (hIN : InvLPS (PofC centre place entry raw) q first raw c r)
    (hw : WatchSegE (PofC centre place entry raw) q first 2048 es c r c' t)
    (hcen : t.center = r.center) (hav : canRight t.right)
    (h : FoundRouteMC3 (PofC centre place entry raw) q first raw m c r c' t) :
    CycleOutMC3 (PofC centre place entry raw) q first raw m c r := by
  have hIC : InvLPC raw c r := hIN.1
  have hI : InvL raw c r := invLPC_invL hIC
  obtain ⟨⟨R, hi⟩, hc0, -⟩ := invL_entry hI
  have hrun0 := seg_run centre place entry q first raw hI hw
  obtain ⟨Ls, k', w1, hcrS, he, hw1, -, -, -, -⟩ :=
    GalilCostedFallback.costedRun_watchSegE raw (PofC centre place entry raw) q first hw hi hc0 hav
  have fin : ∀ (cT : Control) (sT : GalilVM),
      FoundCost (PofC centre place entry raw) q first raw c' t cT sT →
      Inv raw cT sT → SpanRep sT → position t.center < position sT.center →
      position sT.right ≤ 2 * m - 1 →
      CycleOutMC3 (PofC centre place entry raw) q first raw m c r := by
    intro cT sT hcost hIT hSpan hprog hpos
    obtain ⟨k, L, hst, hcr⟩ := hcost w1 hw1
    have hall := stepsAll_trans hrun0 hst
    have hcr' := costedRun_trans hcrS hcr
    rw [show k' + (k + w1) = es.length + k by omega] at hcr'
    exact cycleOutMC3_of_centre hIN hall hcr'
      (invLPS_of_landed centre place entry q first hIC.1.2 hall hIT hSpan)
      (by rw [← hcen]; exact hprog) hpos
  cases h with
  | report h => exact Or.inl h
  | shift cT sT hcost hM hR hres hSpan hprog hpos =>
      exact fin cT sT hcost (inv_of_residual hM hR hres) hSpan hprog hpos
  | noShift cT sT hcost hM hR hres hSpan hprog hpos =>
      exact fin cT sT hcost (inv_of_residual hM hR hres) hSpan hprog hpos
  | broke cT sT k L hst hcr hIT hcenT hstage hc hlt hpos =>
      exact cycleOutMC3_of_noshift hst hcr ⟨⟨hIT, hcenT⟩, hstage⟩ hc hlt hpos

/-- **The background-found exit over `InvLPS`**, the found route started at the
cycle start. -/
theorem cycleOutMC3_of_foundBg (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m : ℕ) {c : Control} {r : GalilVM}
    (hIN : InvLPS (PofC centre place entry raw) q first raw c r)
    (h : FoundRouteMC3 (PofC centre place entry raw) q first raw m c r c r) :
    CycleOutMC3 (PofC centre place entry raw) q first raw m c r := by
  have hIC : InvLPC raw c r := hIN.1
  have hI : InvL raw c r := invLPC_invL hIC
  obtain ⟨-, hc0, -⟩ := invL_entry hI
  have fin : ∀ (cT : Control) (sT : GalilVM),
      FoundCost (PofC centre place entry raw) q first raw c r cT sT →
      Inv raw cT sT → SpanRep sT → position r.center < position sT.center →
      position sT.right ≤ 2 * m - 1 →
      CycleOutMC3 (PofC centre place entry raw) q first raw m c r := by
    intro cT sT hcost hIT hSpan hprog hpos
    obtain ⟨k, L, hst, hcr⟩ := hcost 0 (by omega)
    exact cycleOutMC3_of_centre hIN hst hcr
      (invLPS_of_landed centre place entry q first hIC.1.2 hst hIT hSpan) hprog hpos
  cases h with
  | report h => exact Or.inl h
  | shift cT sT hcost hM hR hres hSpan hprog hpos =>
      exact fin cT sT hcost (inv_of_residual hM hR hres) hSpan hprog hpos
  | noShift cT sT hcost hM hR hres hSpan hprog hpos =>
      exact fin cT sT hcost (inv_of_residual hM hR hres) hSpan hprog hpos
  | broke cT sT k L hst hcr hIT hcenT hstage hc hlt hpos =>
      exact cycleOutMC3_of_noshift hst hcr ⟨⟨hIT, hcenT⟩, hstage⟩ hc hlt hpos

#print axioms cycleOutMC3_of_foundInReplay
#print axioms cycleOutMC3_of_fallback'
#print axioms cycleOutMC3_of_found
#print axioms cycleOutMC3_of_foundBg

/-! ## 6. The matched, not-found comparison onto `2m-1`, over `InvLPS` -/

/-- **`GalilOracleMC2.reachAtC2_of_target_match` over `InvLPS`.**  Same proof,
with the stage data carried across the report comparison: the comparison at
`2m-1` matches, does not start the chain and leaves the replay flag down, so it
is literally a `WatchSegE.matchIdle` step, and `replayStage_trans` extends the
stage segment through the cycle's own segment and then through it. -/
theorem reachAtC3_of_target_match (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m : ℕ) (hm1 : 1 ≤ m) (hmle : m ≤ raw.length)
    (hpres : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s) →
      searchEffect (PofC centre place entry raw) a s v → SearchReady v)
    (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM)
    (hIN : InvLPS (PofC centre place entry raw) q first raw c r)
    (hsW : SegReachedW centre place entry q first raw c r c' t)
    (hT : AtTarget m c' t)
    (hmt : read (left t.left) = read (right t.right))
    (vq : SearchVM) (hq : searchEffect (PofC centre place entry raw) true t vq)
    (hnf : vq.search.mode ≠ .found) :
    ReachAtC3 (PofC centre place entry raw) q first raw m c r := by
  classical
  set P : Shared := PofC centre place entry raw with hP
  have hIC : InvLPC raw c r := hIN.1
  have hI : InvL raw c r := invLPC_invL hIC
  obtain ⟨hs, es, hw⟩ := hsW
  obtain ⟨hnr, hc1, hav, hpos, hrep⟩ := hT
  obtain ⟨⟨R0, hi0⟩, hc0, -⟩ := invL_entry hI
  have hrun0 := seg_run centre place entry q first raw hI hw
  obtain ⟨R, hi⟩ := hs.scan
  -- the entering counters, transported along the idle segment
  obtain ⟨RadE, hiE, hRRE, hSE, hLE⟩ := hIC.1.1.2
  have hiT : ScanInvariant raw (position r.center) (RadE + es.count true) t.left t.right :=
    scanInvariant_watchSegE P q first 2048 hw hiE
  have hRRT : RadiusRep t.radius (RadE + es.count true) :=
    radiusRep_watchSegE P q first 2048 hw hRRE
  have hST : SpanRep t := spanRep_watchSegE P q first 2048 hw hSE
  have hLT : Canonical t.length := canonical_length_watchSegE P q first 2048 hw hLE
  set vs : ScanVM := ⟨left t.left, right t.right, ChainVM.idle⟩ with hvs
  have hmt0 : (galilFrame P q first).matched (scanLens.set t vs) := hmt
  have hcmp : (galilFrameS P q first).compare t (afterCompare t vs vq) :=
    ⟨vs, vq, true, rfl, rfl, ⟨fun _ => hmt0, fun _ => rfl⟩, hq,
      Or.inr (Or.inl ⟨hs.idle, by simp [hnf], rfl⟩), rfl⟩
  have hmt1 : (galilFrameS P q first).matched (afterCompare t vs vq) := hmt
  set u : GalilVM := afterCompare t vs vq with hu
  set o : Bool := if P.onLetter u then decide (P.leftFirst u) else c'.output with ho'
  have ho : refresh (galilFrameS P q first) u c'.output o := by
    refine ⟨fun hl => ?_, fun hl => ?_⟩
    · have hl' : P.onLetter u := hl
      show (if P.onLetter u then decide (P.leftFirst u) else c'.output) = true ↔ P.leftFirst u
      rw [if_pos hl']; exact decide_eq_true_iff
    · have hl' : ¬ P.onLetter u := hl
      show (if P.onLetter u then decide (P.leftFirst u) else c'.output) = c'.output
      rw [if_neg hl']
  have hsrc : SoundScanNR raw ⟨c', t⟩ := stepsAll_last hrun0
  obtain ⟨⟨k1, hrun1⟩, hrp, hfr⟩ :=
    PalPeg.GalilReportPrefix.reportAt_of_match raw P rfl rfl q first 2048 hsrc hs.mode hc1 hnr
      hav hs.minv hi hpos hm1 hmle vs vq o rfl rfl hcmp hmt1 ho
  have hsound := stepsAll_last hrun1
  have hpl : (galilFrameS P q first).matchedPlace c'.replaying u u := by
    show u = (if c'.replaying then _ else u)
    rw [hnr]; simp
  have htick : Tick (galilFrameS P q first) 2048 ⟨c', t⟩
      ⟨{c' with clock := 2048, output := o, replaying := false}, u⟩ := by
    have h := Tick.scan_match (F := galilFrameS P q first) (delay := 2048) c' t u u o hs.mode
      (Or.inr hav) hc1 hcmp hmt1 hpl ho
    rw [hnr] at h
    simpa using h
  have hall := stepsAll_trans hrun0 (.succ hsrc htick (.zero _ hsound))
  obtain ⟨L, w, hw', hcr, -, -⟩ :=
    GalilCostedFallback.costedRun_target_match raw P q first hw hi0 hc0 hc1 hav m hm1 hpos vq
  -- the counters and the centre head at the landing of the comparison
  have hcu : u.center = r.center := by rw [hu, afterCompare_center, hs.center]
  have hEu : EntryCounters raw u := by
    refine ⟨RadE + es.count true + 1, ?_, ?_, ?_, ?_⟩
    · rw [hcu]; exact matched_invariant' raw vq (vs := vs) rfl rfl hmt hav hiT
    · rw [hu, afterCompare_radius]; exact radius_rep_inc hRRT
    · rw [hu]; exact spanRep_afterCompare hST
    · rw [hu, afterCompare_length]; exact inc_canonical _ (inc_canonical _ hLT)
  -- the stage data: the report comparison is a `matchIdle` step of the segment
  have hmid : WatchSegE P q first 2048 [true] c' t
      {c' with clock := 2048, output := o, replaying := false} u :=
    .matchIdle c' t vs vq o hs.mode hnr hav hc1 hs.idle rfl rfl rfl hmt0 hq hnf ho (.stop _ _)
  have hstage : ReplayStage raw P q first
      {c' with clock := 2048, output := o, replaying := false} u :=
    replayStage_trans (replayStage_trans hIN.2 hw) hmid
  refine ⟨_, es.length + (0 + 1), L ++ [GalilCostedFallback.cmpPiece (2 * m - 1) w hw'], hall,
    hcr, hrp, hfr, fun _ => ⟨_, u, 0, [], .zero _ (stepsAll_last hall), costedRun_nil u, ?_, ?_⟩⟩
  · have hIS : PalPeg.GalilReplaySegment.InvScan 2048 raw
        {c' with clock := 2048, output := o, replaying := false} u (R + 1) := by
      refine PalPeg.GalilReplaySegment.inv_after_replay 2048 raw _ u (R + 1) hs.mode rfl rfl
        (by rw [hu, afterCompare_chain]) ?_ hrp.centre ?_ ?_ ?_
      · exact matched_invariant' raw vq (vs := vs) rfl rfl hmt hav hi
      · exact hpres t true vq hs.search hq
      · rw [hu, afterCompare_replay]; exact hrep
      · exact PalPeg.GalilReplaySegment.shiftIdle_congr
          (PalPeg.GalilReplaySegment.afterCompare_remaining t vs vq) hs.shiftIdle
    have hIL : InvLP raw {c' with clock := 2048, output := o, replaying := false} u :=
      ⟨invL_of_run hall (Or.inr ⟨R + 1, hIS⟩), hEu⟩
    exact ⟨⟨invLP2_of_stepsAll centre place entry q first hIC.1.2 hall hIL,
      centreRep_congr hcu hIC.2⟩, hstage⟩
  · have h1 : position u.right = 2 * m - 1 := hrp.atPlace
    omega

#print axioms reachAtC3_of_target_match

/-! ## 7. The oracle over `InvLPS`, assembled -/

/-- **`GalilOracleMC3.cycleOracleMC2C_of_pieces'` over `InvLPS`.**  Same case
split and the same leaves — `hquiet` and `houtReplay` gone, `StartShape`,
`ReplayBudgetR`, `ReplayStageInv`, `RestartShape` and the busy-replay leaf
`hfoundReplay` in their place — with every entry state an `InvLPS` state and
every exit landing back in `InvLPS`.

The found leaves `hfound` / `hfoundBg` / `hfoundReplay` now *receive* the stage
data at the cycle entry, which is exactly what
`GalilReplayBudgetProof.found_stage_data`,
`GalilLaterRadius.found_radius_le_all_stages` and
`GalilPrepConstruct.prep_segment_construct_of_found` need at the found tick:
compose the entry's `ReplayStage` with the cycle's own segment through
`GalilFoundStageInv.replayStage_trans`, decompose the restart's centre with
`represents_decompose`, and the three lemmas apply.  In exchange they must
deliver the stage data again at their `broke` landing, which
`GalilInvPlus2.foundRouteMC_noshift''` does not export
(`GalilNoShiftStage.fresh_break_stage` proves the `StageEntry` half). -/
theorem cycleOracleMC3_of_pieces (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2))
    (hex : ∀ s, (PofC centre place entry raw).replayExhausted s = zero s.replay)
    (hsearch : ∀ s : GalilVM, SearchReady (searchLens.get s) →
      ∀ a : Bool, ∃ v, searchEffect (PofC centre place entry raw) a s v)
    (hpres : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s) →
      searchEffect (PofC centre place entry raw) a s v → SearchReady v)
    (hshape : PalPeg.GalilWatchOkInst.StartShape (PofC centre place entry raw))
    (hbudget : PalPeg.GalilFoundStage.ReplayBudgetR raw (PofC centre place entry raw) q first 2048)
    (hstageInv : PalPeg.GalilFoundStage.ReplayStageInv raw (PofC centre place entry raw) q first)
    (hrs : PalPeg.GalilReplaySpan.RestartShape (PofC centre place entry raw))
    (hsegmentM : ∀ (m : ℕ) (c : Control) (r : GalilVM), 1 ≤ m → m ≤ raw.length →
      InvLPS (PofC centre place entry raw) q first raw c r → position r.right ≤ 2 * m - 1 →
      ∃ (c' : Control) (t : GalilVM),
        SegReachedW centre place entry q first raw c r c' t ∧
        (AtTarget m c' t ∨ SegEnd (PofC centre place entry raw) c' t))
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
      FallbackRouteMC3 (PofC centre place entry raw) q first raw m c r c' t)
    (hfound : ∀ (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ raw.length → InvLPS (PofC centre place entry raw) q first raw c r →
      position r.right ≤ 2 * m - 1 →
      SegReachedW centre place entry q first raw c r c' t →
      c'.clock = 1 → canRight t.right →
      read (left t.left) = read (right t.right) →
      (∃ vq, searchEffect (PofC centre place entry raw) true t vq ∧ vq.search.mode = .found) →
      FoundRouteMC3 (PofC centre place entry raw) q first raw m c r c' t)
    (hfoundBg : ∀ (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ raw.length → InvLPS (PofC centre place entry raw) q first raw c r →
      position r.right ≤ 2 * m - 1 →
      SegReachedW centre place entry q first raw c r c' t → 1 ≤ c'.clock →
      (∃ vq, searchEffect (PofC centre place entry raw) false t vq ∧ vq.search.mode = .found) →
      FoundRouteMC3 (PofC centre place entry raw) q first raw m c r c r)
    (hfoundReplay : ∀ (m : ℕ) (c : Control) (r : GalilVM) (cT : Control) (sT : GalilVM) (R k : ℕ),
      1 ≤ m → m ≤ raw.length → InvLPS (PofC centre place entry raw) q first raw c r →
      StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048 (SoundScanNR raw) k
        ⟨c, r⟩ ⟨cT, sT⟩ →
      ReplayLanding raw cT sT R → SpanRep sT →
      position r.center < position sT.center → position sT.right ≤ 2 * m - 1 →
      (PalPeg.GalilReplaySpan.ChainEnd raw (PofC centre place entry raw) q first 2048
          (position sT.right + R) cT sT 0 R ∨
        PalPeg.GalilReplaySpan.BrokeAndRestarted raw (PofC centre place entry raw) q first 2048
          cT sT) →
      FoundInReplayRouteMC3 (PofC centre place entry raw) q first raw m c r) :
    CycleOracleMC3 (PofC centre place entry raw) q first raw := by
  intro m c r hm1 hmle hIN hp
  obtain ⟨c', t, hsW, hend⟩ := hsegmentM m c r hm1 hmle hIN hp
  obtain ⟨hs, es, hw⟩ := id hsW
  rcases hend with hT | hend
  · obtain ⟨hnr, hc1, hav, -, -⟩ := id hT
    by_cases hmt : read (left t.left) = read (right t.right)
    · obtain ⟨vq, hq⟩ := hsearch t hs.search true
      by_cases hf : vq.search.mode = .found
      · exact cycleOutMC3_of_found centre place entry q first raw m hIN hw hs.center hav
          (hfound m c r c' t hm1 hmle hIN hp hsW hc1 hav hmt ⟨vq, hq, hf⟩)
      · exact Or.inl (reachAtC3_of_target_match centre place entry q first raw m hm1 hmle hpres
          c r c' t hIN hsW hT hmt vq hq hf)
    · exact cycleOutMC3_of_fallback' centre place entry q first raw m hm1 hmle hex hsearch hpres
        hshape hbudget hstageInv hrs (hfoundReplay m) hIN hw hs.center hc1 hav
        (hmismatch m c r c' t hm1 hmle hIN hp hsW hnr hc1 hav hmt)
  · cases hend with
    | ended hn => exact Or.inl (hended m c r c' t hm1 hmle hIN hp hsW hn)
    | mismatch hr hc hav hne =>
        exact cycleOutMC3_of_fallback' centre place entry q first raw m hm1 hmle hex hsearch hpres
          hshape hbudget hstageInv hrs (hfoundReplay m) hIN hw hs.center hc hav
          (hmismatch m c r c' t hm1 hmle hIN hp hsW hr hc hav hne)
    | found hc hav hmt hq =>
        exact cycleOutMC3_of_found centre place entry q first raw m hIN hw hs.center hav
          (hfound m c r c' t hm1 hmle hIN hp hsW hc hav hmt hq)
    | foundBackground hc hq =>
        exact cycleOutMC3_of_foundBg centre place entry q first raw m hIN
          (hfoundBg m c r c' t hm1 hmle hIN hp hsW hc hq)
    | lastLetter hc hav hpop hinc =>
        by_cases hmt : read (left t.left) = read (right t.right)
        · exact Or.inl (hlastMatch m c r c' t hm1 hmle hIN hp hsW hc hav hpop hinc hmt)
        · exact Or.inl (hlastMismatch m c r c' t hm1 hmle hIN hp hsW hc hav hpop hinc hmt)

#print axioms cycleOracleMC3_of_pieces

/-- **`hsegmentM` at an `InvLPS` entry.**  `GalilOracleLeaves2.segment_of_invLPC`
only reads the `InvLPC` half, so the segment leaf of `cycleOracleMC3_of_pieces`
is discharged by the same fuel bound `hends`. -/
theorem segment_of_invLPS (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m : ℕ)
    (hex : ∀ s, (PofC centre place entry raw).replayExhausted s = zero s.replay)
    (hsearch : ∀ s : GalilVM, SearchReady (searchLens.get s) →
      ∀ a : Bool, ∃ v, searchEffect (PofC centre place entry raw) a s v)
    (hpres : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s) →
      searchEffect (PofC centre place entry raw) a s v → SearchReady v)
    (c : Control) (r : GalilVM)
    (hIN : InvLPS (PofC centre place entry raw) q first raw c r)
    (hends : ∃ n : ℕ, ∀ (es : List Bool) (c' : Control) (t : GalilVM),
      WatchSegE (PofC centre place entry raw) q first 2048 es c r c' t →
      es.length = n → SegEnd (PofC centre place entry raw) c' t) :
    ∃ (c' : Control) (t : GalilVM),
      SegReachedW centre place entry q first raw c r c' t ∧
      (AtTarget m c' t ∨ SegEnd (PofC centre place entry raw) c' t) := by
  obtain ⟨c', t, hsW, hEnd⟩ :=
    segment_of_invLPC centre place entry q first raw hex hsearch hpres c r hIN.1 hends
  exact ⟨c', t, hsW, Or.inr hEnd⟩

#print axioms segment_of_invLPS

end PalPeg.GalilInvPlus3
