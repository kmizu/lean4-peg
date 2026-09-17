import PalPeg.PackedRun
import PalPeg.CloseoutPackRun35

/-!
# `CloseoutPackRun36`: `LPackM2` carried inside the run pack, `pal_in_peg_final20`

`CloseoutPackRun35` §2 found `H_packOnRunG` circular: the pack states at which
`LPackM2` is needed come from `packRunR_MG` runs whose origins are arbitrary
`InvLPC` states quantified in `CycleOracleIMG`, and the trace is built from
those.  The non-circular fix is to carry `LPackM2` *inside* the run pack:

* §1 `IPackMG2 := IPackMG ∧ LPackM2`, `BigPack2MG2` / `BigPack2MG2''` over it.
  `lticksN_of_lpackM2_pt` produces `LTickLeavesN` *pointwise* from the
  `LPackM2` half (Run33's five readers specialised to one state), so the only
  leaf the tick needs is `ShiftPal` at scan/non-replaying states:
  `bigPack2MG2''_tick` = `bigPack2MG''_tick` ∧ `lpackM2_tick'`, with the
  `rewind`-on-`FIRST` branch's `LPackM2` half proved directly (every extra
  field is vacuous at the `replayStart` landing except `centreRep`, which is
  `centreRep_congr` over `fppReset`).
* §2 `StepsIMG2` / `ReachAtIMG2` / `CycleOutIMG2` / `CycleOracleIMG2` /
  `PreTraceIMG2` — Run30 §3 verbatim over `IPackMG2`.
* §3 `h_trailI_MG2`, `H_realizeLIMG2'`, `pal_in_peg_final5MG2` — Run30 §4–§5
  by projection `IPackMG2 → IPackMG`.
* §4 `lpackM2_of_invLPC` (origin: scan/non-replaying makes the five extra
  fields vacuous), `packRunR_MG2`, `cycleOracleIMG2_of_cycleOracleMC3R`,
  `h_bootIMG2_of_h_bootIMG`, and `pal_in_peg_final20` = `final19` with
  `hLv`/`hon` replaced by the pointwise guarded leaf
  `∀ w x, BigPack2MG2 … x → ScanNR x → ShiftPal … x.vm`.

Standard axioms only; unconditional `PAL ∈ PEG` remains open.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPackRun36

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open PalPeg.GalilThrottledRun PalPeg.GalilTrailProof PalPeg.GalilFinalAssembly
open PalPeg.CloseoutRadPack PalPeg.CloseoutRadPack2 PalPeg.CloseoutRadPack3
open PalPeg.CloseoutRadPack4 PalPeg.CloseoutLPack PalPeg.CloseoutLPack2
open PalPeg.CloseoutLPack3 PalPeg.CloseoutLPack4 PalPeg.CloseoutLPack5
open PalPeg.CloseoutLPack6
open PalPeg.GalilRunSkeleton PalPeg.GalilCheckpoints PalPeg.GalilTraceCost
open PalPeg.GalilOracleDischarge PalPeg.GalilOracleLocal PalPeg.GalilLexMeasure
open PalPeg.GalilInvPlus PalPeg.GalilInvPlus2 PalPeg.GalilOracleMC PalPeg.GalilOracleMC2
open PalPeg.GalilLookRefined PalPeg.GalilFinalBaseNeed PalPeg.GalilFinalAssembly2
open PalPeg.GalilLedgerQ64 PalPeg.GalilLedgerAssembly PalPeg.GalilIntervalCost
open PalPeg.GalilLatchTracking PalPeg.GalilArriveChain PalPeg.GalilTickArrive
open PalPeg.GalilTruncTick PalPeg.GalilFinalAssembly4
open PalPeg.GalilTrailScan PalPeg.GalilTrailBudget PalPeg.GalilTrailChain
open PalPeg.GalilTrailAssembly PalPeg.GalilTrailRad PalPeg.GalilFrontMono
open PalPeg.CloseoutOracleI PalPeg.CloseoutOracleI2 PalPeg.GalilInvPlus3
open PalPeg.CloseoutPackRun PalPeg.CloseoutPackRun2 PalPeg.CloseoutPackRun3
open PalPeg.CloseoutPackRun5 PalPeg.CloseoutPackRun7 PalPeg.CloseoutPackRun8
open PalPeg.CloseoutPackRun9 PalPeg.CloseoutPackRun10 PalPeg.CloseoutPackRun11
open PalPeg.CloseoutPackRun12 PalPeg.CloseoutPackRun16 PalPeg.CloseoutPackRun18
open PalPeg.CloseoutPackRun19 PalPeg.CloseoutPackRun20 PalPeg.CloseoutPackRun21
open PalPeg.CloseoutPackRun23 PalPeg.CloseoutPackRun24 PalPeg.CloseoutPackRun26
open PalPeg.CloseoutPackRun29 PalPeg.CloseoutPackRun30 PalPeg.CloseoutPackRun33
open PalPeg.CloseoutPackRun35
open GalilScaffoldInputHead GalilScaffoldCounter GalilScaffoldChainVerifier

/-! ## 1. `IPackMG2`, `BigPack2MG2`, `BigPack2MG2''`, the tick -/

section PackG2
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **`IPackMG` with `LPackM2` carried alongside.** -/
structure IPackMG2 (w : List (Fin 2)) (x : State GalilVM) : Prop where
  base : IPackMG centre place entry q first w x
  m2 : LPackM2 w x.ctl x.vm

/-- `CloseoutPackRun30.BigPack2MG` over `IPackMG2`. -/
structure BigPack2MG2 (w : List (Fin 2)) (x : State GalilVM) : Prop where
  ipackM : IPackMG2 centre place entry q first w x
  aux : AuxPack x.ctl x.vm
  live : CentreLive x.ctl x.vm
  extra : Extra' centre place entry w x

theorem bigPack2MG_of_bigPack2MG2 {w : List (Fin 2)} {x : State GalilVM}
    (h : BigPack2MG2 centre place entry q first w x) : BigPack2MG centre place entry q first w x :=
  ⟨h.ipackM.base, h.aux, h.live, h.extra⟩

/-- **`LTickLeavesN` pointwise from `LPackM2` at the state** (Run33's five
readers specialised to one state; `rewindLeft` from `Extra'.rewindMargin`). -/
theorem lticksN_of_lpackM2_pt {w : List (Fin 2)} {x : State GalilVM}
    (hx : BigPack2MG centre place entry q first w x) (hP : LPackM2 w x.ctl x.vm) :
    LTickLeavesN centre place entry q first w x.ctl x.vm where
  initPackN := rInitPackMG_of_pack centre place entry q first x hx
  scanInvR := fun hm => by
    cases hrep : x.ctl.replaying with
    | false => exact hx.ipackM.pack.scanGeom hm hrep
    | true => exact hP.scanGeomR hm hrep
  scanCanR := fun hm => canR_of_partsM centre place entry hx.aux.front hx.extra hm
  shiftDoneScan := fun hm hnp => by
    have hz : positive x.vm.remaining = false := by
      cases hpos : positive x.vm.remaining with
      | false => rfl
      | true => exact absurd (Or.inl hpos) hnp
    exact shiftGeom_exit (hP.shiftGeom hm) hz
  choosePackL := fun hm _ t ht => by
    rw [choose_left_eq_right (PofC centre place entry w) q first ht]
    exact hP.rrep (by rw [hm]; decide)
  rewindLeft := fun hm => left_pos_of_two (hx.extra.rewindMargin hm)
  replayPackN := fun hm _ _ h =>
    lpackM_replayStart_of_centreRep centre place entry q first (hP.centreRep (Or.inr hm)) h

/-- `CloseoutPackRun29.lTickLeaves2_of_shiftPal` with `ShiftPal` guarded by `ScanNR`. -/
theorem lTickLeaves2_of_shiftPalG {w : List (Fin 2)} {x : State GalilVM}
    (hP : LPackM2 w x.ctl x.vm) (hL : LTickLeavesN centre place entry q first w x.ctl x.vm)
    (hSP : ScanNR x → ShiftPal centre place entry q first w x.vm) :
    LTickLeaves2 centre place entry q first w x.ctl x.vm where
  shiftEntry := fun hm hr s' t hcmp hmt hg hb => by
    obtain ⟨r₀, hi⟩ := hP.packM.scanGeom hm hr
    exact shiftEntry_of_guard centre place entry q first hi (hL.scanCanR hm) (hSP ⟨hm, hr⟩)
      hcmp hmt hg hb

/-- **One tick of `IPackMG2`** from `BigPack2MG2` at the source, `WatchShiftG`,
and the guarded `ShiftPal` leaf: `lpackN_tick` ∧ `rShiftNextMG_of_watchShiftG`
∧ `lpackM2_tick'`. -/
theorem ipackMG2_tick_pt {w : List (Fin 2)}
    (hws : ∀ y : State GalilVM, WatchShiftG centre place entry q first w y)
    {x y : State GalilVM} (hx : BigPack2MG2 centre place entry q first w x)
    (hSP : ScanNR x → ShiftPal centre place entry q first w x.vm)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y)
    (hg : SoundScanNR w y) : IPackMG2 centre place entry q first w y := by
  have hxG := bigPack2MG_of_bigPack2MG2 centre place entry q first hx
  have hL := lticksN_of_lpackM2_pt centre place entry q first hxG hx.ipackM.m2
  refine ⟨⟨?_, rShiftNextMG_of_watchShiftG centre place entry q first hws x y hxG h hg⟩,
    lpackM2_tick' centre place entry q first hx.ipackM.m2 hL hx.aux
      (lTickLeaves2_of_shiftPalG centre place entry q first hx.ipackM.m2 hL hSP) h⟩
  obtain ⟨c, s⟩ := x
  obtain ⟨c', t⟩ := y
  exact lpackN_tick centre place entry q first hxG.ipackM.pack hL h

/-- `CloseoutPackRun30.BigPack2MG''` over `IPackMG2`. -/
structure BigPack2MG2'' (w : List (Fin 2)) (x : State GalilVM) : Prop where
  ipackM : IPackMG2 centre place entry q first w x
  aux : AuxPack x.ctl x.vm
  live : CentreLive x.ctl x.vm
  marks : MarksInv' first x.ctl x.vm
  extra : Extra3 centre place entry w x

theorem bigPack2MG2_of_bigPack2MG2'' {w : List (Fin 2)} {x : State GalilVM}
    (hx : BigPack2MG2'' centre place entry q first w x)
    (hnf : x.ctl.mode = Mode.rewind →
      ¬ (galilFrameS (PofC centre place entry w) q first).atFirst x.vm) :
    BigPack2MG2 centre place entry q first w x :=
  ⟨hx.ipackM, hx.aux, hx.live, extra'_of_extra3 centre place entry hx.extra
    (fun hm => two_le_left_of_marksInv' hx.marks hm (hnf hm))⟩

/-- **`CloseoutPackRun30.bigPack2MG''_tick` ∧ `lpackM2_tick'`**, with the only
leaf `ShiftPal` at scan/non-replaying states. -/
theorem bigPack2MG2''_tick {w : List (Fin 2)}
    (hws : ∀ y : State GalilVM, WatchShiftG centre place entry q first w y)
    (het : H_extraTick3 centre place entry q first w)
    (hme : H_marksEntry' (PofC centre place entry w) q first)
    {x y : State GalilVM} (hx : BigPack2MG2'' centre place entry q first w x)
    (hSP : ScanNR x → ShiftPal centre place entry q first w x.vm)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y)
    (hg : SoundScanNR w y) (hlv : CentreLive y.ctl y.vm) :
    BigPack2MG2'' centre place entry q first w y := by
  have haux : AuxPack y.ctl y.vm := auxPack_tick centre place entry q first hx.aux hx.live h
  have hmarks : MarksInv' first y.ctl y.vm := by
    obtain ⟨c, s⟩ := x
    obtain ⟨c', t⟩ := y
    exact marksInv'_tick _ q first 2048 hx.marks (fun hm ho hs => hme c s hm ho hs) h
  refine ⟨?_, haux, hlv, hmarks, het x y hx.extra h⟩
  by_cases hcase : x.ctl.mode = Mode.rewind ∧
      (galilFrameS (PofC centre place entry w) q first).atFirst x.vm
  · obtain ⟨hm, hf⟩ := hcase
    obtain ⟨c, s⟩ := x
    obtain ⟨c', t⟩ := y
    obtain ⟨hc', hfr⟩ := tick_rewind_atFirst hm hf h
    have hM : LPackM w c' t :=
      lpackM_rewind_done centre place entry q first hx.ipackM.base.pack hm hc' hfr
    have hG : ShiftLocalG centre place entry q first w ⟨c', t⟩ := by
      apply shiftLocalG_of_chainIdle
      apply haux.coupled.idleOut
      all_goals (show c'.mode ≠ _; rw [hc']; intro h; exact Mode.noConfusion h)
    refine ⟨⟨hM, hG⟩, ?_⟩
    obtain ⟨heq, hset⟩ := hfr
    have htc : t.center = s.center := by rw [hset, heq]; rfl
    have hCR : CentreRep w t := centreRep_congr htc (hx.ipackM.m2.centreRep (Or.inl hm))
    subst hc'
    refine ⟨hM, ?_, ?_, ?_, fun _ => hCR, ?_⟩
    all_goals vac rfl
  · have hnf : x.ctl.mode = Mode.rewind →
        ¬ (galilFrameS (PofC centre place entry w) q first).atFirst x.vm :=
      fun hm hf => hcase ⟨hm, hf⟩
    exact ipackMG2_tick_pt centre place entry q first hws
      (bigPack2MG2_of_bigPack2MG2'' centre place entry q first hx hnf) hSP h hg

end PackG2

#print axioms lticksN_of_lpackM2_pt
#print axioms ipackMG2_tick_pt
#print axioms bigPack2MG2''_tick

/-! ## 2. `StepsIMG2`, `ReachAtIMG2`, `CycleOracleIMG2`, `PreTraceIMG2` (Run30 §3) -/

section RunG2
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- `CloseoutPackRun30.StepsIMG` carrying `IPackMG2`. -/
def StepsIMG2 (w : List (Fin 2)) (k : ℕ) (x y : State GalilVM) : Prop :=
  PackedRun (galilFrameS (PofC centre place entry w) q first) 2048 (SoundScanNR w)
    (IPackMG2 centre place entry q first w) k x y

theorem stepsIMG2_trans {w : List (Fin 2)} {k1 k2 : ℕ} {x y z : State GalilVM}
    (h1 : StepsIMG2 centre place entry q first w k1 x y)
    (h2 : StepsIMG2 centre place entry q first w k2 y z) :
    StepsIMG2 centre place entry q first w (k1 + k2) x z :=
  PalPeg.PackedRun.trans h1 h2

theorem ipackMG2_last_of_stepsIMG2 {w : List (Fin 2)} {k : ℕ} {x y : State GalilVM}
    (h : StepsIMG2 centre place entry q first w k x y) :
    IPackMG2 centre place entry q first w y := by
  obtain ⟨g, -, hgk, -, hp⟩ := h
  rw [← hgk]; exact hp k le_rfl

/-- `CloseoutPackRun30.ReachAtIMG` over `StepsIMG2`. -/
def ReachAtIMG2 (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) : Prop :=
  ∃ (y : State GalilVM) (k : ℕ) (L : List Piece),
    StepsIMG2 centre place entry q first w k ⟨c, r⟩ y ∧
    CostedRun r y.vm k L ∧
    PalPeg.GalilReportPrefix.ReportPointAt w m y ∧
    Refreshed (PofC centre place entry w) q first y ∧
    (m < w.length → ∃ (c' : Control) (r' : GalilVM) (k' : ℕ) (L' : List Piece),
      StepsIMG2 centre place entry q first w k' y ⟨c', r'⟩ ∧
      CostedRun y.vm r' k' L' ∧
      InvLPC w c' r' ∧ position r'.right ≤ 2 * (m+1) - 1)

/-- `CloseoutPackRun30.CycleOutIMG` over `StepsIMG2`. -/
def CycleOutIMG2 (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) : Prop :=
  ReachAtIMG2 centre place entry q first w m c r ∨
    ∃ (cT : Control) (sT : GalilVM) (k : ℕ) (L : List Piece),
      StepsIMG2 centre place entry q first w k ⟨c, r⟩ ⟨cT, sT⟩ ∧
      CostedRun r sT k L ∧
      InvLPC w cT sT ∧ mu w sT < mu w r ∧
      position sT.right ≤ 2 * m - 1

/-- `CloseoutPackRun30.CycleOracleIMG` over `StepsIMG2`. -/
def CycleOracleIMG2 (w : List (Fin 2)) : Prop :=
  ∀ (m : ℕ) (c : Control) (r : GalilVM), 1 ≤ m → m ≤ w.length → InvLPC w c r →
    position r.right ≤ 2 * m - 1 → CycleOutIMG2 centre place entry q first w m c r

theorem reachIMG2_fuel (w : List (Fin 2)) (hor : CycleOracleIMG2 centre place entry q first w)
    (m : ℕ) (hm1 : 1 ≤ m) (hmle : m ≤ w.length) :
    ∀ (n : ℕ) (c : Control) (r : GalilVM), mu w r ≤ n → InvLPC w c r →
      position r.right ≤ 2 * m - 1 → ReachAtIMG2 centre place entry q first w m c r := by
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
      exact ⟨y, k + k', L ++ L',
        stepsIMG2_trans centre place entry q first hst hst',
        costedRun_trans hcr hcr', hrp, hfr, hcont⟩

theorem reachIMG2_from_invLPC (w : List (Fin 2))
    (hor : CycleOracleIMG2 centre place entry q first w)
    {m : ℕ} (hm1 : 1 ≤ m) (hmle : m ≤ w.length) {c : Control} {r : GalilVM}
    (hI : InvLPC w c r) (hp : position r.right ≤ 2 * m - 1) :
    ReachAtIMG2 centre place entry q first w m c r :=
  reachIMG2_fuel centre place entry q first w hor m hm1 hmle _ c r le_rfl hI hp

/-- `CloseoutPackRun30.checkpoints_costIMG_upto1` over `IPackMG2` (verbatim). -/
theorem checkpoints_costIMG2_upto1 (w : List (Fin 2))
    (hor : CycleOracleIMG2 centre place entry q first w)
    {x0 : State GalilVM} {k0 : ℕ} {c : Control} {r : GalilVM}
    (hpre : StepsIMG2 centre place entry q first w k0 x0 ⟨c, r⟩)
    (hI : InvLPC w c r) (hpos : position r.right = 1) :
    ∀ M, M ≤ w.length →
    ∃ (st : ℕ → State GalilVM) (Tc : ℕ → ℕ) (e : ℕ),
      st 0 = x0 ∧ Tc 0 = 0 ∧
      Trace (galilFrameS (PofC centre place entry w) q first) 2048 (SoundScanNR w) st e ∧
      (∀ m, m < M → Tc m ≤ Tc (m+1)) ∧ Tc M ≤ e ∧
      (∀ m, 1 ≤ m → m ≤ M →
        PalPeg.GalilReportPrefix.ReportPointAt w m (st (Tc m)) ∧
        Refreshed (PofC centre place entry w) q first (st (Tc m))) ∧
      (∀ m, 1 ≤ m → m < M →
        Tc (m+1) - Tc m ≤ alpha' 2048 * (Cw w (m+1) - Cw w m) + beta' 2048) ∧
      (M < w.length → ∃ (c' : Control) (r' : GalilVM),
        st e = ⟨c', r'⟩ ∧ InvLPC w c' r' ∧ position r'.right ≤ 2 * (M+1) - 1 ∧
        (1 ≤ M → ∃ L : List Piece, CostedRun (st (Tc M)).vm r' (e - Tc M) L)) ∧
      (M = 0 → e = k0 ∧ st e = ⟨c, r⟩) ∧
      (1 ≤ M → Tc 1 = k0) ∧
      (∀ i, i ≤ e → IPackMG2 centre place entry q first w (st i)) := by
  intro M
  induction M with
  | zero =>
    intro _
    obtain ⟨g, hg0, hgn, htr, hgp⟩ := hpre
    refine ⟨g, fun _ => 0, k0, hg0, rfl, htr, fun m hm => absurd hm (Nat.not_lt_zero _),
      Nat.zero_le _, fun m h1 h2 => absurd h1 (by omega), fun m h1 h2 => absurd h2 (by omega),
      fun _ => ⟨c, r, hgn, hI, by omega, fun h => absurd h (by omega)⟩,
      fun _ => ⟨rfl, hgn⟩, fun h => absurd h (by omega), hgp⟩
  | succ M ih =>
    intro hM
    obtain ⟨st, Tc, e, hst0, hTc0, htr, hmono, hTcM, hchk, hcost, hres, hzero, hone, hpk⟩ :=
      ih (by omega)
    obtain ⟨c', r', hste, hI', hp', hpend⟩ := hres (by omega)
    obtain ⟨y, k, L2, hrun, hcr, hrp, hfr, hcont⟩ :=
      reachIMG2_from_invLPC centre place entry q first w hor (m := M+1) (by omega) hM hI' hp'
    have hk0 : M = 0 → k = 0 ∧ e = k0 := by
      intro hM0
      subst hM0
      obtain ⟨he, hse⟩ := hzero rfl
      have hrr : r' = r := by
        have := hste.symm.trans hse
        exact (GalilScaffoldTop.State.mk.injEq _ _ _ _ ▸ this).2
      subst hrr
      have hyp := hrp.atPlace
      exact ⟨costedRun_zero hcr (by rw [hyp, hpos]), he⟩
    obtain ⟨g1, hg10, hg1k, htr1, hpg1⟩ := hrun
    have hj1 : st e = g1 0 := by rw [hste, hg10]
    set st1 := concat st g1 e with hst1
    have htr1' : Trace (galilFrameS (PofC centre place entry w) q first) 2048
        (SoundScanNR w) st1 (e + k) :=
      trace_concat htr htr1 hj1
    have hst1y : st1 (e + k) = y := by rw [hst1, concat_end st g1 hj1, hg1k]
    have hpk1 : ∀ i, i ≤ e + k → IPackMG2 centre place entry q first w (st1 i) :=
      pack_concat hj1 hpk hpg1
    obtain ⟨st2, e2, htr2, hagree, hle2, hres2, hpk2⟩ :
        ∃ (st2 : ℕ → State GalilVM) (e2 : ℕ),
          Trace (galilFrameS (PofC centre place entry w) q first) 2048 (SoundScanNR w) st2 e2 ∧
          (∀ i, i ≤ e + k → st2 i = st1 i) ∧ e + k ≤ e2 ∧
          (M + 1 < w.length → ∃ (c'' : Control) (r'' : GalilVM),
            st2 e2 = ⟨c'', r''⟩ ∧ InvLPC w c'' r'' ∧
            position r''.right ≤ 2 * (M+1+1) - 1 ∧
            ∃ L : List Piece, CostedRun y.vm r'' (e2 - (e + k)) L) ∧
          (∀ i, i ≤ e2 → IPackMG2 centre place entry q first w (st2 i)) := by
      by_cases hlt : M + 1 < w.length
      · obtain ⟨c'', r'', k', L', hrun2, hcr2, hI2, hp2⟩ := hcont hlt
        obtain ⟨g2, hg20, hg2k, htr2, hpg2⟩ := hrun2
        have hj2 : st1 (e + k) = g2 0 := by rw [hst1y, hg20]
        refine ⟨concat st1 g2 (e + k), e + k + k', trace_concat htr1' htr2 hj2,
          fun i hi => concat_le st1 g2 hi, by omega, fun _ => ⟨c'', r'', ?_, hI2, hp2, L', ?_⟩,
          pack_concat hj2 hpk1 hpg2⟩
        · rw [concat_end st1 g2 hj2, hg2k]
        · rw [show e + k + k' - (e + k) = k' by omega]; exact hcr2
      · exact ⟨st1, e + k, htr1', fun _ _ => rfl, le_rfl, fun h => absurd h hlt, hpk1⟩
    have hTcle : ∀ m, m ≤ M → Tc m ≤ e := fun m hm =>
      le_trans (mono_of_step Tc M hmono m M hm le_rfl) hTcM
    have hst2old : ∀ m, m ≤ M → st2 (Tc m) = st (Tc m) := by
      intro m hm
      rw [hagree _ (by have := hTcle m hm; omega), hst1, concat_le st g1 (hTcle m hm)]
    have hst2y : st2 (e + k) = y := by rw [hagree _ le_rfl, hst1y]
    refine ⟨st2, fun m => if m ≤ M then Tc m else e + k, e2, ?_, ?_, htr2, ?_, ?_, ?_, ?_, ?_,
      fun h => absurd h (by omega), ?_, hpk2⟩
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
    · intro _
      by_cases hM0 : M = 0
      · subst hM0
        obtain ⟨hk, he⟩ := hk0 rfl
        simp only [show ¬ (1 ≤ 0) by omega, if_false]
        omega
      · simp only [show 1 ≤ M by omega, if_true]
        exact hone (by omega)

/-- `CloseoutPackRun30.PreTraceIMG` over `IPackMG2`. -/
structure PreTraceIMG2 (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ) : Prop where
  base : PreTraceB centre place entry q first w st Tc
  packs : ∀ i, i ≤ Tc w.length → IPackMG2 centre place entry q first w (st i)

/-- `CloseoutPackRun30.H_bootIMG` over `StepsIMG2`. -/
def H_bootIMG2 : Prop :=
  ∀ (a : Fin 2) (rest : List (Fin 2)),
    ∃ (c1 : Control) (t : GalilVM),
      StepsIMG2 centre place entry q first (a :: rest) 1
        ⟨GalilScaffoldController.initial 2048, GalilBootVM.initVM0 (a :: rest)⟩ ⟨c1, t⟩ ∧
      InvLPC (a :: rest) c1 t ∧ position t.right = 1

/-- `CloseoutPackRun30.H_oracleIMG` over `StepsIMG2`. -/
def H_oracleIMG2 : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → CycleOracleIMG2 centre place entry q first w

theorem preTraceIMG2_exists (hboot : H_bootIMG2 centre place entry q first)
    (hor : H_oracleIMG2 centre place entry q first) (w : List (Fin 2)) (hw : 0 < w.length) :
    ∃ st Tc, PreTraceIMG2 centre place entry q first w st Tc := by
  rcases w with _ | ⟨a, rest⟩
  · simp at hw
  · obtain ⟨c1, t, hst, hI, hpos⟩ := hboot a rest
    obtain ⟨st, Tc, e, hst0, hTc0, htr, hmono, hTcM, hchk, hcost, -, -, hone, hpk⟩ :=
      checkpoints_costIMG2_upto1 centre place entry q first (a :: rest) (hor (a :: rest) hw)
        hst hI hpos (a :: rest).length le_rfl
    refine ⟨st, Tc, ⟨⟨⟨hst0, hTc0, trace_le htr hTcM, mono_of_step Tc _ hmono, ?_, hcost⟩,
      hone (by simp)⟩, fun i hi => hpk i (le_trans hi hTcM)⟩⟩
    intro m h1 h2
    exact ledgerAt_of_prefix (hchk m h1 h2).1 (hchk m h1 h2).2

end RunG2

#print axioms stepsIMG2_trans
#print axioms reachIMG2_from_invLPC
#print axioms checkpoints_costIMG2_upto1
#print axioms preTraceIMG2_exists

/-! ## 3. Trail bridge and `pal_in_peg_final5MG2` by projection -/

section TrailG2
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- `CloseoutPackRun30.H_trailI_MG` over `IPackMG2`. -/
def H_trailI_MG2 : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTrace centre place entry q first w st Tc →
    (∀ i, i ≤ Tc w.length → IPackMG2 centre place entry q first w (st i)) →
    ∀ m, m < w.length → ∀ i, i ≤ Tc (m+1) → TrailF w m (st i)

theorem h_trailI_MG2 : H_trailI_MG2 centre place entry q first :=
  fun w hw st Tc hP hIP m hm i hi =>
    h_trailI_MG centre place entry q first w hw st Tc hP (fun j hj => (hIP j hj).base) m hm i hi

theorem needIMG2'_le {w : List (Fin 2)}
    (hw : 0 < w.length) {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hP : PreTraceIMG2 centre place entry q first w st Tc) :
    ∀ m, m < w.length → ∀ i, i ≤ Tc (m+1) → needL' w st i ≤ m + 1 :=
  fun m hm i hi =>
    needL'_le_of_trailF w st m i
      (h_trailI_MG2 centre place entry q first w hw st Tc hP.base.pre hP.packs m hm i hi)

end TrailG2

#print axioms h_trailI_MG2
#print axioms needIMG2'_le

/-- `CloseoutPackRun30.H_realizeLIMG'` over `PreTraceIMG2`. -/
def H_realizeLIMG2' (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9) : Prop :=
  ∃ (Q' Γ' : Type) (_ : Fintype Q') (_ : DecidableEq Q') (_ : Fintype Γ') (_ : DecidableEq Γ')
    (t K : ℕ) (L : PalPeg.Local.LocalStep (Fin 2) Q' Γ' t K) (blank : Γ') (initQ : Q')
    (outQ : Q' → Bool) (n : ℕ) (htape : 0 < t) (hn : 0 < n),
    ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTraceIMG2 centre place entry q first w st Tc →
      ((L.realize blank initQ (GalilEmptyWord.accept' initQ outQ) n htape hn).SAccepts w ↔
        LatchTrue (PofC centre place entry w) q first w (stLG' τF w st (Tc w.length))
          ((w.length + 1) * τF))

/-- `PreTraceIMG2 ⊆ PreTraceIMG`, so `H_realizeLIMG'` is the stronger statement. -/
theorem h_realizeLIMG'_of_G2 {centre : GalilVM → Fin 3} {place : GalilVM → GalilScaffoldPlace.Place}
    {entry q : ℕ} {first : Fin 9} (h : H_realizeLIMG' centre place entry q first) :
    H_realizeLIMG2' centre place entry q first := by
  obtain ⟨Q', Γ', iQ, dQ, iΓ, dΓ, t, K, L, blank, initQ, outQ, n, htape, hn, hreal⟩ := h
  exact ⟨Q', Γ', iQ, dQ, iΓ, dΓ, t, K, L, blank, initQ, outQ, n, htape, hn,
    fun w hw st Tc hP => hreal w hw st Tc ⟨hP.base, fun i hi => (hP.packs i hi).base⟩⟩

/-- `CloseoutPackRun30.pal_in_peg_final5MG` over `PreTraceIMG2` (verbatim). -/
theorem pal_in_peg_final5MG2 (entry q : ℕ) (first : Fin 9)
    (hboot : H_bootIMG2 centreC placeC entry q first)
    (hA : H_oracleIMG2 centreC placeC entry q first)
    (hC : H_realizeLIMG2' centreC placeC entry q first) :
    RecognizedByTotalPEG PAL := by
  classical
  obtain ⟨Q', Γ', iQ, dQ, iΓ, dΓ, t, K, L, blank, initQ, outQ, n, htape, hn, hreal⟩ := hC
  have key : ∀ w : List (Fin 2), ∃ (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      0 < w.length → PreTraceIMG2 centreC placeC entry q first w st Tc := by
    intro w
    by_cases hw : 0 < w.length
    · obtain ⟨st, Tc, h⟩ := preTraceIMG2_exists centreC placeC entry q first hboot hA w hw
      exact ⟨st, Tc, fun _ => h⟩
    · exact ⟨fun _ => boot w, fun _ => 0, fun h => absurd h hw⟩
  choose stP TcP hP using key
  let M := L.realize blank initQ (GalilEmptyWord.accept' initQ outQ) n htape hn
  have hpre : ∀ w : List (Fin 2), 0 < w.length → PreloadL' w (stP w) (TcP w) := by
    intro w hw
    have h := hP w hw
    exact ⟨h.base.pre.tc0, fun m hm => h.base.pre.mono m (m+1) (by omega) hm,
      needL'_boot w (stP w) h.base.pre.start,
      needLe_of_pointwise' w (stP w) (TcP w) (needIMG2'_le centreC placeC entry q first hw h)⟩
  refine pal_in_peg_of_latch' (Nat.mul_pos hn (PalPeg.Local.cnt_pos K)) M
    (PofC centreC placeC entry) (fun _ => q) (fun _ => first) 2048
    (fun w => PofC_onLetter centreC placeC entry w)
    (fun w => PofC_leftFirst centreC placeC entry w)
    (fun w => stLG' τF w (stP w) (TcP w w.length))
    (fun w => arrLG' τF w (stP w) (TcP w w.length))
    (fun w => (w.length + 1) * τF) ?_ ?_ ?_ ?_
  · intro w hw
    have h := hP w hw
    exact abstractRun_throttledL'_2p18 w (stP w) (TcP w w.length)
      (PofC centreC placeC entry w) q first 2048
      (fun j => sharedC_trunc_vm w j centreC placeC entry (fun s => (centrePlaceC w j s).1)
        (fun s => (centrePlaceC w j s).2))
      (sharedC_suf w _ _ centreC placeC entry)
      (by rw [h.base.pre.start]; rfl) (needL'_boot w (stP w) h.base.pre.start)
      (by rw [h.base.pre.start]; exact sufVM_boot w) h.base.pre.trace.tick
  · intro w hw
    exact hreal w hw _ _ (hP w hw)
  · exact ledger_throttledL'_2p18 (PofC centreC placeC entry) (fun _ => q) (fun _ => first)
      stP TcP hpre (fun w hw => (hP w hw).base.pre.report w.length (by omega) le_rfl)
      (fun w hw => base_of_preTraceB (hP w hw).base)
      (fun w hw => (hP w hw).base.pre.cost)
  · exact GalilEmptyWord.realize_accept'_nil L blank initQ outQ n htape hn

#print axioms h_realizeLIMG'_of_G2
#print axioms pal_in_peg_final5MG2

/-! ## 4. Origin `LPackM2`, `packRunR_MG2`, the oracle bridge, `pal_in_peg_final20` -/

section BridgeG2
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **`LPackM2` at every `InvLPC` state**: the `LPackM` half is Run7/Run10's
chain from `ipack_of_invLPC'`; the origin is scan/non-replaying (`invS_mode`),
so the five extra fields are vacuous (as in `lpackM2_boot`). -/
theorem lpackM2_of_invLPC {w : List (Fin 2)} (hsl : H_shiftLocalG centre place entry q first w)
    {c : Control} {r : GalilVM} (hIC : InvLPC w c r) : LPackM2 w c r := by
  have hM : LPackM w c r :=
    (ipackM_of_ipackO centre place entry q first
      (ipackO_of_ipack centre place entry q first
        (ipack_of_invLPC' centre place entry q first
          (h_shiftLocalC_of_G centre place entry q first hsl) (x := ⟨c, r⟩) hIC))).pack
  obtain ⟨hm, hr⟩ := invS_mode hIC.1.1.1.1
  refine ⟨hM, fun _ hr' => absurd (hr.symm.trans hr') Bool.noConfusion, ?_, ?_, ?_, ?_⟩
  all_goals vac hm

/-- `IPackMG2` at an `InvLPC` origin. -/
theorem ipackMG2_of_invLPC {w : List (Fin 2)} (hsl : H_shiftLocalG centre place entry q first w)
    {c : Control} {r : GalilVM} (hIC : InvLPC w c r) :
    IPackMG2 centre place entry q first w ⟨c, r⟩ :=
  ⟨ipackMG_of_ipackM centre place entry q first
      (ipackM_of_ipackO centre place entry q first
        (ipackO_of_ipack centre place entry q first
          (ipack_of_invLPC' centre place entry q first
            (h_shiftLocalC_of_G centre place entry q first hsl) (x := ⟨c, r⟩) hIC))),
    lpackM2_of_invLPC centre place entry q first hsl hIC⟩

/-- `CloseoutPackRun30.PackRunRMG` over `StepsIMG2`. -/
def PackRunRMG2 (w : List (Fin 2)) : Prop :=
  ∀ (c : Control) (r : GalilVM), InvLPC w c r →
    ∀ (j : ℕ) (x : State GalilVM),
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 j ⟨c, r⟩ x →
      ∀ (k : ℕ) (y : State GalilVM), IPackMG2 centre place entry q first w x →
        StepsAll (galilFrameS (PofC centre place entry w) q first) 2048 (SoundScanNR w) k x y →
        StepsIMG2 centre place entry q first w k x y

/-- **(KEY) `CloseoutPackRun30.packRunR_MG` with `BigResid6G` replaced by
`WatchShiftG` and the pointwise guarded `ShiftPal` leaf.**  At a `ScanNR` run
state the `rewind` guard of `bigPack2MG2_of_bigPack2MG2''` is vacuous. -/
theorem packRunR_MG2 {w : List (Fin 2)}
    (hws : ∀ y : State GalilVM, WatchShiftG centre place entry q first w y)
    (hSP : ∀ x : State GalilVM, BigPack2MG2 centre place entry q first w x →
      ScanNR x → ShiftPal centre place entry q first w x.vm)
    (hee : H_extraEntry3 centre place entry w)
    (het : H_extraTick3 centre place entry q first w)
    (hme : H_marksEntry' (PofC centre place entry w) q first) :
    PackRunRMG2 centre place entry q first w := by
  intro c r hIC j x hjx k y hx h
  have hlv0 : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 m ⟨c, r⟩ z →
      CentreLive z.ctl z.vm :=
    PalPeg.GalilOracleLeaves2.hlive_of_invLPC centre place entry q first hIC
  have haux0 : AuxPack c r :=
    ⟨coupled_of_invLPC hIC, front_of_invLPC hIC, copyPack_of_invLPC hIC⟩
  have hauxx : AuxPack x.ctl x.vm :=
    auxPack_steps centre place entry q first (x := ⟨c, r⟩) hlv0 haux0 hjx
  have hexx : Extra3 centre place entry w x :=
    extra3_steps centre place entry q first het (x := ⟨c, r⟩) (hee c r hIC) hjx
  have hmx : MarksInv' first x.ctl x.vm :=
    marksInv'_of_run (PofC centre place entry w) q first 2048 hme (x := ⟨c, r⟩) hjx
      (m := Mode.scan) (by decide) (invS_mode hIC.1.1.1.1).1
  have hbx : BigPack2MG2'' centre place entry q first w x :=
    ⟨hx, hauxx, hlv0 j x hjx, hmx, hexx⟩
  obtain ⟨g, hg0, hgk, htr⟩ := stepsAll_fn h
  have hreach : ∀ i, i ≤ k →
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 (j + i) ⟨c, r⟩ (g i) := by
    intro i hi
    have := steps_of_trace htr i hi
    rw [hg0] at this
    exact steps_trans hjx this
  have hbig : ∀ i, i ≤ k → BigPack2MG2'' centre place entry q first w (g i) := by
    intro i
    induction i with
    | zero => intro _; rw [hg0]; exact hbx
    | succ n ih =>
      intro hi
      have hn := ih (by omega)
      exact bigPack2MG2''_tick centre place entry q first hws het hme hn
        (fun hs => hSP (g n) (bigPack2MG2_of_bigPack2MG2'' centre place entry q first hn
          (fun hm => absurd (hs.1.symm.trans hm) (by decide))) hs)
        (htr.tick n (by omega)) (htr.good (n+1) hi)
        (hlv0 (j + (n+1)) (g (n+1)) (hreach (n+1) hi))
  exact ⟨g, hg0, hgk, htr, fun i hi => (hbig i hi).ipackM⟩

theorem reachAtIMG2_of_reachAtC3R {w : List (Fin 2)}
    (hpr : PackRunRMG2 centre place entry q first w)
    {m : ℕ} {c : Control} {r : GalilVM} (hIC : InvLPC w c r)
    (hx : IPackMG2 centre place entry q first w ⟨c, r⟩)
    (h : ReachAtC3 (PofC centre place entry w) q first w m c r) :
    ReachAtIMG2 centre place entry q first w m c r := by
  obtain ⟨y, k, L, hst, hcr, hrp, hfr, hcont⟩ := h
  have hstI : StepsIMG2 centre place entry q first w k ⟨c, r⟩ y :=
    hpr c r hIC 0 ⟨c, r⟩ (.zero _) k y hx hst
  refine ⟨y, k, L, hstI, hcr, hrp, hfr, fun hlt => ?_⟩
  obtain ⟨c', r', k', L', hst', hcr', hIS, hp⟩ := hcont hlt
  exact ⟨c', r', k', L',
    hpr c r hIC k y (stepsAll_steps hst) k' ⟨c', r'⟩
      (ipackMG2_last_of_stepsIMG2 centre place entry q first hstI) hst',
    hcr', hIS.1, hp⟩

theorem cycleOutIMG2_of_cycleOutMC3R {w : List (Fin 2)}
    (hpr : PackRunRMG2 centre place entry q first w)
    {m : ℕ} {c : Control} {r : GalilVM} (hIC : InvLPC w c r)
    (hx : IPackMG2 centre place entry q first w ⟨c, r⟩)
    (h : CycleOutMC3 (PofC centre place entry w) q first w m c r) :
    CycleOutIMG2 centre place entry q first w m c r := by
  rcases h with hdone | ⟨cT, sT, k, L, hst, hcr, hIT, hlt, hpos⟩
  · exact Or.inl (reachAtIMG2_of_reachAtC3R centre place entry q first hpr hIC hx hdone)
  · exact Or.inr ⟨cT, sT, k, L, hpr c r hIC 0 ⟨c, r⟩ (.zero _) k ⟨cT, sT⟩ hx hst,
      hcr, hIT.1, hlt, hpos⟩

/-- `CloseoutPackRun30.cycleOracleIMG_of_cycleOracleMC3R` over `PackRunRMG2`,
origin pack `ipackMG2_of_invLPC`. -/
theorem cycleOracleIMG2_of_cycleOracleMC3R {w : List (Fin 2)}
    (hpr : PackRunRMG2 centre place entry q first w)
    (hsl : H_shiftLocalG centre place entry q first w)
    (hsc : H_stageScan centre place entry q first w)
    (hor : CycleOracleMC3 (PofC centre place entry w) q first w) :
    CycleOracleIMG2 centre place entry q first w := by
  intro m c r hm1 hmle hIC hp
  exact cycleOutIMG2_of_cycleOutMC3R centre place entry q first hpr hIC
    (ipackMG2_of_invLPC centre place entry q first hsl hIC)
    (hor m c r hm1 hmle (hstage_of_scanBranch centre place entry q first hsc c r hIC) hp)

/-- `H_bootIMG2` from `H_bootIMG`: the one-step boot run has `LPackM2` at the
boot state (`lpackM2_boot`) and at its `InvLPC` landing (`lpackM2_of_invLPC`). -/
theorem h_bootIMG2_of_h_bootIMG
    (hsl : ∀ w : List (Fin 2), H_shiftLocalG centre place entry q first w)
    (h : H_bootIMG centre place entry q first) : H_bootIMG2 centre place entry q first := by
  intro a rest
  obtain ⟨c1, t, ⟨g, hg0, hg1, htr, hp⟩, hI, hp1⟩ := h a rest
  refine ⟨c1, t, ⟨g, hg0, hg1, htr, fun i hi => ⟨hp i hi, ?_⟩⟩, hI, hp1⟩
  cases i with
  | zero => rw [hg0]; exact lpackM2_boot (a :: rest)
  | succ n =>
    cases n with
    | zero => rw [hg1]; exact lpackM2_of_invLPC centre place entry q first (hsl _) hI
    | succ n => omega

end BridgeG2

#print axioms lpackM2_of_invLPC
#print axioms packRunR_MG2
#print axioms cycleOracleIMG2_of_cycleOracleMC3R
#print axioms h_bootIMG2_of_h_bootIMG

/-- **`pal_in_peg_final19` with `hLv`/`hon` (trace leaves + `H_packOnRunG`)
replaced by the pointwise guarded leaf `hSP`**: `ShiftPal` at every
scan/non-replaying `BigPack2MG2` state.  `LTickLeavesN` is derived pointwise
from the `LPackM2` half (`lticksN_of_lpackM2_pt`), `AuxPack` is in the pack,
and the five non-shift `BigResid6G` contracts are never assembled: their
pointwise content enters the tick directly. -/
theorem pal_in_peg_final20 (entry q : ℕ) (first : Fin 9)
    (hSP : ∀ (w : List (Fin 2)) (x : State GalilVM),
      BigPack2MG2 centreC placeC entry q first w x →
      ScanNR x → ShiftPal centreC placeC entry q first w x.vm)
    (hws : ∀ w : List (Fin 2), ∀ y : State GalilVM, WatchShiftG centreC placeC entry q first w y)
    (hee : ∀ w : List (Fin 2), H_extraEntry3 centreC placeC entry w)
    (het : ∀ w : List (Fin 2), H_extraTick3 centreC placeC entry q first w)
    (hme : ∀ w : List (Fin 2), H_marksEntry' (PofC centreC placeC entry w) q first)
    (hsl : ∀ w : List (Fin 2), H_shiftLocalG centreC placeC entry q first w)
    (hsc : ∀ w : List (Fin 2), H_stageScan centreC placeC entry q first w)
    (hor : ∀ w : List (Fin 2), 0 < w.length →
      CycleOracleMC3 (PofC centreC placeC entry w) q first w)
    (hbs : H_bootShift centreC placeC entry q first)
    (hls : H_landShift centreC placeC entry q first)
    (hC : H_realizeLIMG2' centreC placeC entry q first) :
    RecognizedByTotalPEG PAL :=
  pal_in_peg_final5MG2 entry q first
    (h_bootIMG2_of_h_bootIMG centreC placeC entry q first hsl
      (h_bootIMG_of_h_bootIM centreC placeC entry q first
        (h_bootIM_of_h_bootIO centreC placeC entry q first
          (h_bootIO_of_h_bootI centreC placeC entry q first
            (h_bootI_of_bootIPack centreC placeC entry q first
              (bootIPack_of_parts centreC placeC entry q first h_lrepC hbs hls))))))
    (fun w hw => cycleOracleIMG2_of_cycleOracleMC3R centreC placeC entry q first
      (packRunR_MG2 centreC placeC entry q first (hws w) (hSP w) (hee w) (het w) (hme w))
      (hsl w) (hsc w) (hor w hw))
    hC

#print axioms pal_in_peg_final20

end PalPeg.CloseoutPackRun36
