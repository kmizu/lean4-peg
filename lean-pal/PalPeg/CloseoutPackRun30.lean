import PalPeg.PackedRun
import PalPeg.CloseoutPackRun26

/-!
# `CloseoutPackRun30`: the run/trace chain re-threaded over `ShiftLocalG`

`CloseoutPackRun26` refuted the unguarded `ShiftLocal` at every `scan → shift`
landing with mismatching heads, re-cut it as `ShiftLocalG` (all fields under
`ScanNR := mode = scan ∧ replaying = false`), and stated `pal_in_peg_final16`
still over the unguarded `BigResid6.rShiftNext`, because `IPackM.shift :
ShiftLocal` is hard-wired into `StepsIM` / `ReachAtIM` / `CycleOracleIM` /
`PreTraceIM` / `pal_in_peg_final5M`.

This file is that re-thread, as mirror definitions:

* §1 `IPackMG` (= `IPackM` with `shift : ShiftLocalG`), `BigPack2MG` (Run11's
  `BigPack2M` over it), `BigResid6G` (Run11's six contracts, quantified over
  `BigPack2MG`, with `rShiftNext` in the guarded form `RShiftNextMG`),
  `lticksN_of_big6G`, `bigPack2MG_tick`.
* §2 `BigPack2MG''` / `bigPack2MG''_tick` / `packRunR_MG` — Run18's `BigPack2M''`
  chain (marks + `Extra3`, no rewind corner) over `IPackMG`.
* §3 `StepsIMG`, `ReachAtIMG`, `CycleOutIMG`, `CycleOracleIMG`,
  `checkpoints_costIMG_upto1`, `PreTraceIMG`, `preTraceIMG_exists` — Run12 §0–§4.
* §4 the trail bridge: `halfBound_of_ipackMG` takes `ScanNR x` (the only place
  Run12 read `.shift.mode`), `shiftEntry_ptMG` / `shiftVerSane_ptMG` are the
  pointwise readers *guarded* by `ScanNR (st i)`, and `shiftOrd_ptG` /
  `verSane_ptG` are `CloseoutLPack6.shiftOrd_pt` / `verSane_pt` run through
  `CloseoutPackRun26.shiftOrd_tickG` / `saneTickG`.  **No trace state has to be
  shown scan/non-replaying**: the guard is discharged inside the `scan_shift`
  branch of the tick lemma by that branch's own `hm`/`hr`.  Hence `h_trailI_MG`.
* §5 `H_realizeLIMG'`, `pal_in_peg_final5MG` (Run12 §6 verbatim), the oracle
  bridge (Run12 §7), and `pal_in_peg_final17` = `final16` with `BigResid6`
  replaced by `BigResid6G`.

`BigResid6G` differs from `BigResid6` in two ways, both in the direction of the
refutation: `rShiftNext` concludes `ShiftLocalG` (discharged modulo `WatchShiftG`
by `rShiftNextMG_of_watchShiftG`, mirroring `rShiftNextG_of_pack`), and every
contract is handed the *weaker* pack `BigPack2MG` (whose `shift` half is only
guarded).  So `BigResid6G` is not derivable from `BigResid6`; the intended
producers of the five non-shift contracts read `LPackM`/`AuxPack`/`CentreLive`/
`Extra'` only, which are unchanged.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPackRun30

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
open PalPeg.CloseoutPackRun24 PalPeg.CloseoutPackRun26
open GalilScaffoldInputHead GalilScaffoldCounter GalilScaffoldChainVerifier

/-! ## 1. `IPackMG`, `BigPack2MG`, `BigResid6G` -/

section PackG
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **`CloseoutPackRun10.IPackM` with the shift half guarded.** -/
structure IPackMG (w : List (Fin 2)) (x : State GalilVM) : Prop where
  pack : LPackM w x.ctl x.vm
  shift : ShiftLocalG centre place entry q first w x

theorem ipackMG_of_ipackM {w : List (Fin 2)} {x : State GalilVM}
    (h : IPackM centre place entry q first w x) : IPackMG centre place entry q first w x :=
  ⟨h.pack, shiftLocalG_of_shiftLocal centre place entry q first h.shift⟩

theorem leftLive_ptMG {w : List (Fin 2)} {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hIP : ∀ i, i ≤ Tc w.length → IPackMG centre place entry q first w (st i)) :
    ∀ i, i ≤ Tc w.length → PalPeg.GalilTrailSane.LeftLive (st i).ctl (st i).vm :=
  fun i hi => leftLive_of_lpackM (hIP i hi).pack

/-- `CloseoutPackRun11.BigPack2M` over `IPackMG`. -/
structure BigPack2MG (w : List (Fin 2)) (x : State GalilVM) : Prop where
  ipackM : IPackMG centre place entry q first w x
  aux : AuxPack x.ctl x.vm
  live : CentreLive x.ctl x.vm
  extra : Extra' centre place entry w x

theorem bigPack2MG_of_bigPack2M {w : List (Fin 2)} {x : State GalilVM}
    (h : BigPack2M centre place entry q first w x) : BigPack2MG centre place entry q first w x :=
  ⟨ipackMG_of_ipackM centre place entry q first h.ipackM, h.aux, h.live, h.extra⟩

/-- `CloseoutPackRun26.RShiftNextG` with the source pack weakened to `BigPack2MG`. -/
def RShiftNextMG (w : List (Fin 2)) : Prop :=
  ∀ x y : State GalilVM, BigPack2MG centre place entry q first w x →
    Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y →
    SoundScanNR w y → ShiftLocalG centre place entry q first w y

/-- `CloseoutPackRun26.rShiftNextG_of_pack`: the pack is not consumed, so the
weaker source pack costs nothing. -/
theorem rShiftNextMG_of_watchShiftG {w : List (Fin 2)}
    (hws : ∀ y : State GalilVM, WatchShiftG centre place entry q first w y) :
    RShiftNextMG centre place entry q first w := by
  intro x y _ _ _
  by_cases hi : y.vm.chain = ChainVM.idle
  · exact shiftLocalG_of_chainIdle centre place entry q first hi
  · exact shiftLocalG_of_watchShiftG centre place entry q first hi (hws y)

/-- **`CloseoutPackRun11.BigResid6` over the guarded pack**: the five non-shift
contracts verbatim with hypothesis `BigPack2MG`, and `rShiftNext` in the guarded
form. -/
structure BigResid6G (w : List (Fin 2)) : Prop where
  rInitPackM : ∀ x : State GalilVM, BigPack2MG centre place entry q first w x →
    x.ctl.mode = Mode.init → ∀ t : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).init x.vm t →
    LPackM w {x.ctl with mode := Mode.scan, output := true} t
  rScanInvR : ∀ x : State GalilVM, BigPack2MG centre place entry q first w x →
    x.ctl.mode = Mode.scan →
    ∃ r, ScanInvariant w (position x.vm.center) r x.vm.left x.vm.right
  rShiftDoneScan : ∀ x : State GalilVM, BigPack2MG centre place entry q first w x →
    x.ctl.mode = Mode.shift →
    ¬ (galilFrameS (PofC centre place entry w) q first).remainingPos x.vm →
    ∃ r, ScanInvariant w (position x.vm.center) r x.vm.left x.vm.right
  rChoosePackL : ∀ x : State GalilVM, BigPack2MG centre place entry q first w x →
    x.ctl.mode = Mode.choose → x.ctl.odd = true → ∀ t : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).choose x.vm t →
    GalilScaffoldInputTrace.Represents t.left.head w ∧ t.left.head.focus ≠ none
  rReplayPackM : ∀ x : State GalilVM, BigPack2MG centre place entry q first w x →
    x.ctl.mode = Mode.replayStart → ∀ (t : GalilVM) (o : Bool),
    (galilFrameS (PofC centre place entry w) q first).replayStart x.vm t →
    LPackM w {x.ctl with mode := Mode.scan, clock := 2048, output := o, replaying := (galilFrameS (PofC centre place entry w) q first).replayPos t} t
  rShiftNext : RShiftNextMG centre place entry q first w

/-- `CloseoutPackRun11.lticksN_of_big6` over `BigResid6G`. -/
theorem lticksN_of_big6G {w : List (Fin 2)} (hr : BigResid6G centre place entry q first w)
    {x : State GalilVM} (hx : BigPack2MG centre place entry q first w x) :
    LTickLeavesN centre place entry q first w x.ctl x.vm where
  initPackN := hr.rInitPackM x hx
  scanInvR := hr.rScanInvR x hx
  scanCanR := fun hm => canR_of_partsM centre place entry hx.aux.front hx.extra hm
  shiftDoneScan := hr.rShiftDoneScan x hx
  choosePackL := hr.rChoosePackL x hx
  rewindLeft := fun hm _ => left_pos_of_two (hx.extra.rewindMargin hm)
  replayPackN := hr.rReplayPackM x hx

/-- **`lpackN_tick` plus the guarded shift step**: `CloseoutPackRun11.bigPack2M_tick`
over `BigResid6G`.  The non-shift half is `lpackN_tick` reused as is. -/
theorem lpackN_tickG {w : List (Fin 2)} (hr : BigResid6G centre place entry q first w)
    {x y : State GalilVM} (hx : BigPack2MG centre place entry q first w x)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y)
    (hg : SoundScanNR w y) : IPackMG centre place entry q first w y := by
  refine ⟨?_, hr.rShiftNext x y hx h hg⟩
  obtain ⟨c, s⟩ := x
  obtain ⟨c', t⟩ := y
  exact lpackN_tick centre place entry q first hx.ipackM.pack
    (lticksN_of_big6G centre place entry q first hr hx) h

theorem bigPack2MG_tick {w : List (Fin 2)} (hr : BigResid6G centre place entry q first w)
    (het : H_extraTick' centre place entry q first w)
    {x y : State GalilVM} (hx : BigPack2MG centre place entry q first w x)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y)
    (hg : SoundScanNR w y) (hlv : CentreLive y.ctl y.vm) :
    BigPack2MG centre place entry q first w y :=
  ⟨lpackN_tickG centre place entry q first hr hx h hg,
    auxPack_tick centre place entry q first hx.aux hx.live h, hlv, het x y hx.extra h⟩

end PackG

#print axioms ipackMG_of_ipackM
#print axioms rShiftNextMG_of_watchShiftG
#print axioms lticksN_of_big6G
#print axioms lpackN_tickG
#print axioms bigPack2MG_tick

/-! ## 2. `BigPack2MG''` and `packRunR_MG` (Run18 §2 over `IPackMG`) -/

section ResidTG
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- `CloseoutPackRun18.BigPack2M''` over `IPackMG`. -/
structure BigPack2MG'' (w : List (Fin 2)) (x : State GalilVM) : Prop where
  ipackM : IPackMG centre place entry q first w x
  aux : AuxPack x.ctl x.vm
  live : CentreLive x.ctl x.vm
  marks : MarksInv' first x.ctl x.vm
  extra : Extra3 centre place entry w x

theorem bigPack2MG_of_bigPack2MG'' {w : List (Fin 2)} {x : State GalilVM}
    (hx : BigPack2MG'' centre place entry q first w x)
    (hnf : x.ctl.mode = Mode.rewind →
      ¬ (galilFrameS (PofC centre place entry w) q first).atFirst x.vm) :
    BigPack2MG centre place entry q first w x :=
  ⟨hx.ipackM, hx.aux, hx.live, extra'_of_extra3 centre place entry hx.extra
    (fun hm => two_le_left_of_marksInv' hx.marks hm (hnf hm))⟩

/-- `CloseoutPackRun18.bigPack2M''_tick` over `BigResid6G`.  In the
`rewind`-on-`FIRST` branch the landing chain is idle, so the guarded shift half
is `shiftLocalG_of_chainIdle`. -/
theorem bigPack2MG''_tick {w : List (Fin 2)} (hr : BigResid6G centre place entry q first w)
    (het : H_extraTick3 centre place entry q first w)
    (hme : H_marksEntry' (PofC centre place entry w) q first)
    {x y : State GalilVM} (hx : BigPack2MG'' centre place entry q first w x)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y)
    (hg : SoundScanNR w y) (hlv : CentreLive y.ctl y.vm) :
    BigPack2MG'' centre place entry q first w y := by
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
    refine ⟨lpackM_rewind_done centre place entry q first hx.ipackM.pack hm hc' hfr, ?_⟩
    apply shiftLocalG_of_chainIdle
    apply haux.coupled.idleOut
    all_goals (show c'.mode ≠ _; rw [hc']; intro h; exact Mode.noConfusion h)
  · have hnf : x.ctl.mode = Mode.rewind →
        ¬ (galilFrameS (PofC centre place entry w) q first).atFirst x.vm :=
      fun hm hf => hcase ⟨hm, hf⟩
    exact lpackN_tickG centre place entry q first hr
      (bigPack2MG_of_bigPack2MG'' centre place entry q first hx hnf) h hg

end ResidTG

#print axioms bigPack2MG_of_bigPack2MG''
#print axioms bigPack2MG''_tick

/-! ## 3. `StepsIMG`, `ReachAtIMG`, `CycleOracleIMG`, `PreTraceIMG` (Run12 §0–§4) -/

section RunG
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- `CloseoutPackRun12.StepsIM` carrying `IPackMG`. -/
def StepsIMG (w : List (Fin 2)) (k : ℕ) (x y : State GalilVM) : Prop :=
  PackedRun (galilFrameS (PofC centre place entry w) q first) 2048 (SoundScanNR w)
    (IPackMG centre place entry q first w) k x y

theorem stepsIMG_of_stepsIM {w : List (Fin 2)} {k : ℕ} {x y : State GalilVM}
    (h : StepsIM centre place entry q first w k x y) :
    StepsIMG centre place entry q first w k x y :=
  PalPeg.PackedRun.mono
    (fun _ hs => ipackMG_of_ipackM centre place entry q first hs) h

theorem stepsIMG_trans {w : List (Fin 2)} {k1 k2 : ℕ} {x y z : State GalilVM}
    (h1 : StepsIMG centre place entry q first w k1 x y)
    (h2 : StepsIMG centre place entry q first w k2 y z) :
    StepsIMG centre place entry q first w (k1 + k2) x z :=
  PalPeg.PackedRun.trans h1 h2

theorem ipackMG_last_of_stepsIMG {w : List (Fin 2)} {k : ℕ} {x y : State GalilVM}
    (h : StepsIMG centre place entry q first w k x y) :
    IPackMG centre place entry q first w y := by
  obtain ⟨g, -, hgk, -, hp⟩ := h
  rw [← hgk]; exact hp k le_rfl

/-- `CloseoutPackRun12.ReachAtIM` over `StepsIMG`. -/
def ReachAtIMG (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) : Prop :=
  ∃ (y : State GalilVM) (k : ℕ) (L : List Piece),
    StepsIMG centre place entry q first w k ⟨c, r⟩ y ∧
    CostedRun r y.vm k L ∧
    PalPeg.GalilReportPrefix.ReportPointAt w m y ∧
    Refreshed (PofC centre place entry w) q first y ∧
    (m < w.length → ∃ (c' : Control) (r' : GalilVM) (k' : ℕ) (L' : List Piece),
      StepsIMG centre place entry q first w k' y ⟨c', r'⟩ ∧
      CostedRun y.vm r' k' L' ∧
      InvLPC w c' r' ∧ position r'.right ≤ 2 * (m+1) - 1)

/-- `CloseoutPackRun12.CycleOutIM` over `StepsIMG`. -/
def CycleOutIMG (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) : Prop :=
  ReachAtIMG centre place entry q first w m c r ∨
    ∃ (cT : Control) (sT : GalilVM) (k : ℕ) (L : List Piece),
      StepsIMG centre place entry q first w k ⟨c, r⟩ ⟨cT, sT⟩ ∧
      CostedRun r sT k L ∧
      InvLPC w cT sT ∧ mu w sT < mu w r ∧
      position sT.right ≤ 2 * m - 1

/-- `CloseoutPackRun12.CycleOracleIM` over `StepsIMG`. -/
def CycleOracleIMG (w : List (Fin 2)) : Prop :=
  ∀ (m : ℕ) (c : Control) (r : GalilVM), 1 ≤ m → m ≤ w.length → InvLPC w c r →
    position r.right ≤ 2 * m - 1 → CycleOutIMG centre place entry q first w m c r

theorem reachIMG_fuel (w : List (Fin 2)) (hor : CycleOracleIMG centre place entry q first w)
    (m : ℕ) (hm1 : 1 ≤ m) (hmle : m ≤ w.length) :
    ∀ (n : ℕ) (c : Control) (r : GalilVM), mu w r ≤ n → InvLPC w c r →
      position r.right ≤ 2 * m - 1 → ReachAtIMG centre place entry q first w m c r := by
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
        stepsIMG_trans centre place entry q first hst hst',
        costedRun_trans hcr hcr', hrp, hfr, hcont⟩

theorem reachIMG_from_invLPC (w : List (Fin 2))
    (hor : CycleOracleIMG centre place entry q first w)
    {m : ℕ} (hm1 : 1 ≤ m) (hmle : m ≤ w.length) {c : Control} {r : GalilVM}
    (hI : InvLPC w c r) (hp : position r.right ≤ 2 * m - 1) :
    ReachAtIMG centre place entry q first w m c r :=
  reachIMG_fuel centre place entry q first w hor m hm1 hmle _ c r le_rfl hI hp

/-- `CloseoutPackRun12.checkpoints_costIM_upto1` over `IPackMG` (verbatim). -/
theorem checkpoints_costIMG_upto1 (w : List (Fin 2))
    (hor : CycleOracleIMG centre place entry q first w)
    {x0 : State GalilVM} {k0 : ℕ} {c : Control} {r : GalilVM}
    (hpre : StepsIMG centre place entry q first w k0 x0 ⟨c, r⟩)
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
      (∀ i, i ≤ e → IPackMG centre place entry q first w (st i)) := by
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
      reachIMG_from_invLPC centre place entry q first w hor (m := M+1) (by omega) hM hI' hp'
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
    have hpk1 : ∀ i, i ≤ e + k → IPackMG centre place entry q first w (st1 i) :=
      pack_concat hj1 hpk hpg1
    obtain ⟨st2, e2, htr2, hagree, hle2, hres2, hpk2⟩ :
        ∃ (st2 : ℕ → State GalilVM) (e2 : ℕ),
          Trace (galilFrameS (PofC centre place entry w) q first) 2048 (SoundScanNR w) st2 e2 ∧
          (∀ i, i ≤ e + k → st2 i = st1 i) ∧ e + k ≤ e2 ∧
          (M + 1 < w.length → ∃ (c'' : Control) (r'' : GalilVM),
            st2 e2 = ⟨c'', r''⟩ ∧ InvLPC w c'' r'' ∧
            position r''.right ≤ 2 * (M+1+1) - 1 ∧
            ∃ L : List Piece, CostedRun y.vm r'' (e2 - (e + k)) L) ∧
          (∀ i, i ≤ e2 → IPackMG centre place entry q first w (st2 i)) := by
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

/-- `CloseoutPackRun12.PreTraceIM` over `IPackMG`. -/
structure PreTraceIMG (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ) : Prop where
  base : PreTraceB centre place entry q first w st Tc
  packs : ∀ i, i ≤ Tc w.length → IPackMG centre place entry q first w (st i)

theorem preTraceIMG_of_preTraceIM {w : List (Fin 2)} {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (h : PreTraceIM centre place entry q first w st Tc) :
    PreTraceIMG centre place entry q first w st Tc :=
  ⟨h.base, fun i hi => ipackMG_of_ipackM centre place entry q first (h.packs i hi)⟩

/-- `CloseoutPackRun12.H_bootIM` over `StepsIMG`. -/
def H_bootIMG : Prop :=
  ∀ (a : Fin 2) (rest : List (Fin 2)),
    ∃ (c1 : Control) (t : GalilVM),
      StepsIMG centre place entry q first (a :: rest) 1
        ⟨GalilScaffoldController.initial 2048, GalilBootVM.initVM0 (a :: rest)⟩ ⟨c1, t⟩ ∧
      InvLPC (a :: rest) c1 t ∧ position t.right = 1

theorem h_bootIMG_of_h_bootIM (h : H_bootIM centre place entry q first) :
    H_bootIMG centre place entry q first := by
  intro a rest
  obtain ⟨c1, t, hst, hI, hp⟩ := h a rest
  exact ⟨c1, t, stepsIMG_of_stepsIM centre place entry q first hst, hI, hp⟩

/-- `CloseoutPackRun12.H_oracleIM` over `StepsIMG`. -/
def H_oracleIMG : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → CycleOracleIMG centre place entry q first w

theorem preTraceIMG_exists (hboot : H_bootIMG centre place entry q first)
    (hor : H_oracleIMG centre place entry q first) (w : List (Fin 2)) (hw : 0 < w.length) :
    ∃ st Tc, PreTraceIMG centre place entry q first w st Tc := by
  rcases w with _ | ⟨a, rest⟩
  · simp at hw
  · obtain ⟨c1, t, hst, hI, hpos⟩ := hboot a rest
    obtain ⟨st, Tc, e, hst0, hTc0, htr, hmono, hTcM, hchk, hcost, -, -, hone, hpk⟩ :=
      checkpoints_costIMG_upto1 centre place entry q first (a :: rest) (hor (a :: rest) hw)
        hst hI hpos (a :: rest).length le_rfl
    refine ⟨st, Tc, ⟨⟨⟨hst0, hTc0, trace_le htr hTcM, mono_of_step Tc _ hmono, ?_, hcost⟩,
      hone (by simp)⟩, fun i hi => hpk i (le_trans hi hTcM)⟩⟩
    intro m h1 h2
    exact ledgerAt_of_prefix (hchk m h1 h2).1 (hchk m h1 h2).2

end RunG

#print axioms stepsIMG_trans
#print axioms reachIMG_from_invLPC
#print axioms checkpoints_costIMG_upto1
#print axioms preTraceIMG_exists

/-! ## 4. The trail bridge over `IPackMG` — guarded pointwise readers -/

section TrailG
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- `CloseoutPackRun12.halfBound_of_ipackM` with the mode read replaced by the
guard `ScanNR x`. -/
theorem halfBound_of_ipackMG {w : List (Fin 2)} {x : State GalilVM}
    (hx : IPackMG centre place entry q first w x) (hs : ScanNR x) {s'' t'' : GalilVM}
    (hcmp : (galilFrameS (PofC centre place entry w) q first).compare x.vm s'')
    (hb : beginShiftVM' s'' t'') :
    ∃ rad : ℕ,
      ScanInvariant w (position x.vm.center) rad x.vm.left x.vm.right ∧
      GalilScaffoldChainVerifier.canRight x.vm.right ∧
      ∀ wch : GalilScaffoldChainWatch.State, s''.chain = .watch wch →
        2 * periodLength wch ≤ rad := by
  obtain ⟨rad, hscan⟩ := hx.pack.scanGeom hs.1 hs.2
  refine ⟨rad, hscan, hx.shift.move hs s'' t'' hcmp hb, fun wch hch => ?_⟩
  have h4 : 4 * (periodLength wch : ℤ) ≤
      GalilScaffoldCounter.value wch.machine.control.distance :=
    hx.shift.guard hs s'' t'' hcmp hb wch hch
  have h2 : GalilScaffoldCounter.value wch.machine.control.distance ≤ 2 * (rad : ℤ) :=
    hx.shift.coupled hs s'' t'' hcmp hb wch hch rad hscan
  omega

/-- `CloseoutPackRun12.shiftEntry_ptM`, guarded by `ScanNR (st i)`. -/
theorem shiftEntry_ptMG {w : List (Fin 2)} {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hIP : ∀ i, i ≤ Tc w.length → IPackMG centre place entry q first w (st i)) :
    ∀ i, i ≤ Tc w.length → ScanNR (st i) → ∀ s'' t'' : GalilVM,
      (galilFrameS (PofC centre place entry w) q first).compare (st i).vm s'' →
      beginShiftVM' s'' t'' → ShiftBud t'' := by
  intro i hi hs s'' t'' hcmp hb
  obtain ⟨rad, hscan, hcan, hh⟩ :=
    halfBound_of_ipackMG centre place entry q first (hIP i hi) hs hcmp hb
  exact shiftBud_of_scanInv (onLetterVM w) leftFirstVM centre place entry q first
    hscan hcan hcmp hb hh

/-- `CloseoutPackRun12.shiftVerSane_ptM`, guarded by `ScanNR (st i)`. -/
theorem shiftVerSane_ptMG {w : List (Fin 2)} {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hIP : ∀ i, i ≤ Tc w.length → IPackMG centre place entry q first w (st i)) :
    ∀ i, i ≤ Tc w.length → ScanNR (st i) → ∀ s'' t'' : GalilVM,
      (galilFrameS (PofC centre place entry w) q first).compare (st i).vm s'' →
      beginShiftVM' s'' t'' → SaneVer t''.chain :=
  fun i hi hs s'' t'' hcmp hb =>
    saneVer_beginShift hb ((hIP i hi).shift.ver hs s'' t'' hcmp hb)

/-- **`CloseoutLPack6.shiftOrd_pt` with the entry hypothesis guarded**, through
`CloseoutPackRun26.shiftOrd_tickG`: the guard is discharged by the `scan_shift`
branch's own `hm`/`hr`, so no trace state has to be shown scan/non-replaying. -/
theorem shiftOrd_ptG {w : List (Fin 2)} (hw : 0 < w.length) {st : ℕ → State GalilVM}
    {Tc : ℕ → ℕ} (hP : PreTrace centre place entry q first w st Tc)
    (hll : ∀ i, i ≤ Tc w.length → PalPeg.GalilTrailSane.LeftLive (st i).ctl (st i).vm)
    (hen : ∀ i, i ≤ Tc w.length → ScanNR (st i) → ∀ s'' t'' : GalilVM,
      (galilFrameS (PofC centre place entry w) q first).compare (st i).vm s'' →
      beginShiftVM' s'' t'' → ShiftBud t'') :
    ∀ i, i ≤ Tc w.length → ShiftOrd (st i).ctl (st i).vm := by
  have hsane := sanePack_pt centre place entry q first hw hP hll
  have hL := radLedger_pt centre place entry q first hw hP hll
  intro i
  induction i with
  | zero => intro _; rw [hP.start]; exact shiftOrd_boot w
  | succ i ih =>
    intro hi
    have hlt : i < Tc w.length := by omega
    have hle : i ≤ Tc w.length := by omega
    exact shiftOrd_tickG (onLetterVM w) leftFirstVM centre place entry q first 2048
      (ih hle) (hL i hle).canonRem (hsane i hle).saneC
      (copyIdle_trace centre place entry q first hP i hle)
      (fun hm hr s'' t'' hcmp hb => hen i hle ⟨hm, hr⟩ s'' t'' hcmp hb)
      (hP.trace.tick i hlt)

/-- **`CloseoutLPack6.verSane_pt` with the entry hypothesis guarded**, through
`CloseoutPackRun26.saneTickG`. -/
theorem verSane_ptG {w : List (Fin 2)} (hw : 0 < w.length) {st : ℕ → State GalilVM}
    {Tc : ℕ → ℕ} (hP : PreTrace centre place entry q first w st Tc)
    (hll : ∀ i, i ≤ Tc w.length → PalPeg.GalilTrailSane.LeftLive (st i).ctl (st i).vm)
    (hsv : ∀ i, i ≤ Tc w.length → ScanNR (st i) → ∀ s'' t'' : GalilVM,
      (galilFrameS (PofC centre place entry w) q first).compare (st i).vm s'' →
      beginShiftVM' s'' t'' → SaneVer t''.chain) :
    ∀ i, i ≤ Tc w.length → ∀ p, verOf (st i).vm.chain = some p →
      GalilFrontMono.Sane p := by
  have hsane := sanePack_pt centre place entry q first hw hP hll
  intro i
  induction i with
  | zero => intro _; rw [hP.start]; exact saneVer_idle
  | succ i ih =>
    intro hi
    have hlt : i < Tc w.length := by omega
    have hle : i ≤ Tc w.length := by omega
    exact saneTickG (onLetterVM w) leftFirstVM centre place entry q first 2048
      (ih hle) (hsane i hle).saneC
      (fun hm hr s'' t'' hcmp hb => hsv i hle ⟨hm, hr⟩ s'' t'' hcmp hb)
      (hP.trace.tick i hlt)

/-- `CloseoutPackRun12.radPack_ptM` over `IPackMG`. -/
theorem radPack_ptMG {w : List (Fin 2)} (hw : 0 < w.length) {st : ℕ → State GalilVM}
    {Tc : ℕ → ℕ} (hP : PreTrace centre place entry q first w st Tc)
    (hIP : ∀ i, i ≤ Tc w.length → IPackMG centre place entry q first w (st i)) :
    ∀ i, i ≤ Tc w.length → RadPack (st i).ctl (st i).vm := by
  have hll := leftLive_ptMG centre place entry q first hIP
  have hen := shiftEntry_ptMG centre place entry q first hIP
  have hsv := shiftVerSane_ptMG centre place entry q first hIP
  have hL := radLedger_pt centre place entry q first hw hP hll
  have hS := shiftOrd_ptG centre place entry q first hw hP hll hen
  have hV := verSane_ptG centre place entry q first hw hP hll hsv
  exact fun i hi => radPack_of_parts (hL i hi) (hS i hi) (hll i hi) (hV i hi)

/-- `CloseoutPackRun12.trailF_ptM` over `IPackMG`. -/
theorem trailF_ptMG {w : List (Fin 2)} (hw : 0 < w.length) {st : ℕ → State GalilVM}
    {Tc : ℕ → ℕ} (hP : PreTrace centre place entry q first w st Tc)
    (hIP : ∀ i, i ≤ Tc w.length → IPackMG centre place entry q first w (st i))
    {m : ℕ} (hm : m < w.length) :
    ∀ i, i ≤ Tc (m+1) → TrailF w m (st i) := by
  have hll := leftLive_ptMG centre place entry q first hIP
  have hsane := sanePack_pt centre place entry q first hw hP hll
  have hrad := radPack_ptMG centre place entry q first hw hP hIP
  have hscan := scanT_pt centre place entry q first hw hP hrad hsane hm
  have hB := chainBudget_pt centre place entry q first hw hP hrad hsane hm
  have hV := verF_trace centre place entry q first hP hm hscan hB
  exact fun i hi => trailF_of_scanT (hscan i hi) (hV i hi).ver (hV i hi).lagPos

/-- `CloseoutPackRun12.H_trailI_M` over the guarded payload. -/
def H_trailI_MG : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTrace centre place entry q first w st Tc →
    (∀ i, i ≤ Tc w.length → IPackMG centre place entry q first w (st i)) →
    ∀ m, m < w.length → ∀ i, i ≤ Tc (m+1) → TrailF w m (st i)

/-- **(KEY) the trail bridge over the guarded payload is a theorem.** -/
theorem h_trailI_MG : H_trailI_MG centre place entry q first :=
  fun _ hw _ _ hP hIP _ hm i hi =>
    trailF_ptMG centre place entry q first hw hP hIP hm i hi

theorem needIMG'_le {w : List (Fin 2)}
    (hw : 0 < w.length) {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hP : PreTraceIMG centre place entry q first w st Tc) :
    ∀ m, m < w.length → ∀ i, i ≤ Tc (m+1) → needL' w st i ≤ m + 1 :=
  fun m hm i hi =>
    needL'_le_of_trailF w st m i
      (h_trailI_MG centre place entry q first w hw st Tc hP.base.pre hP.packs m hm i hi)

end TrailG

#print axioms halfBound_of_ipackMG
#print axioms shiftOrd_ptG
#print axioms verSane_ptG
#print axioms radPack_ptMG
#print axioms h_trailI_MG
#print axioms needIMG'_le

/-! ## 5. `pal_in_peg_final5MG`, the oracle bridge, `pal_in_peg_final17` -/

/-- `CloseoutPackRun12.H_realizeLIM'` over `PreTraceIMG`. -/
def H_realizeLIMG' (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9) : Prop :=
  ∃ (Q' Γ' : Type) (_ : Fintype Q') (_ : DecidableEq Q') (_ : Fintype Γ') (_ : DecidableEq Γ')
    (t K : ℕ) (L : PalPeg.Local.LocalStep (Fin 2) Q' Γ' t K) (blank : Γ') (initQ : Q')
    (outQ : Q' → Bool) (n : ℕ) (htape : 0 < t) (hn : 0 < n),
    ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTraceIMG centre place entry q first w st Tc →
      ((L.realize blank initQ (GalilEmptyWord.accept' initQ outQ) n htape hn).SAccepts w ↔
        LatchTrue (PofC centre place entry w) q first w (stLG' τF w st (Tc w.length))
          ((w.length + 1) * τF))

/-- `H_realizeLIM'` is the stronger statement (it must answer on the larger class
`PreTraceIMG ⊇ PreTraceIM`), so the weakening goes this way. -/
theorem h_realizeLIM'_of_G {centre : GalilVM → Fin 3} {place : GalilVM → GalilScaffoldPlace.Place}
    {entry q : ℕ} {first : Fin 9} (h : H_realizeLIMG' centre place entry q first) :
    H_realizeLIM' centre place entry q first := by
  obtain ⟨Q', Γ', iQ, dQ, iΓ, dΓ, t, K, L, blank, initQ, outQ, n, htape, hn, hreal⟩ := h
  exact ⟨Q', Γ', iQ, dQ, iΓ, dΓ, t, K, L, blank, initQ, outQ, n, htape, hn,
    fun w hw st Tc hP => hreal w hw st Tc (preTraceIMG_of_preTraceIM centre place entry q first hP)⟩

/-- `CloseoutPackRun12.pal_in_peg_final5M` over the guarded payload (verbatim). -/
theorem pal_in_peg_final5MG (entry q : ℕ) (first : Fin 9)
    (hboot : H_bootIMG centreC placeC entry q first)
    (hA : H_oracleIMG centreC placeC entry q first)
    (hC : H_realizeLIMG' centreC placeC entry q first) :
    RecognizedByTotalPEG PAL := by
  classical
  obtain ⟨Q', Γ', iQ, dQ, iΓ, dΓ, t, K, L, blank, initQ, outQ, n, htape, hn, hreal⟩ := hC
  have key : ∀ w : List (Fin 2), ∃ (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      0 < w.length → PreTraceIMG centreC placeC entry q first w st Tc := by
    intro w
    by_cases hw : 0 < w.length
    · obtain ⟨st, Tc, h⟩ := preTraceIMG_exists centreC placeC entry q first hboot hA w hw
      exact ⟨st, Tc, fun _ => h⟩
    · exact ⟨fun _ => boot w, fun _ => 0, fun h => absurd h hw⟩
  choose stP TcP hP using key
  let M := L.realize blank initQ (GalilEmptyWord.accept' initQ outQ) n htape hn
  have hpre : ∀ w : List (Fin 2), 0 < w.length → PreloadL' w (stP w) (TcP w) := by
    intro w hw
    have h := hP w hw
    exact ⟨h.base.pre.tc0, fun m hm => h.base.pre.mono m (m+1) (by omega) hm,
      needL'_boot w (stP w) h.base.pre.start,
      needLe_of_pointwise' w (stP w) (TcP w) (needIMG'_le centreC placeC entry q first hw h)⟩
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

#print axioms h_realizeLIM'_of_G
#print axioms pal_in_peg_final5MG

section BridgeG
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- `CloseoutPackRun12.PackRunRM` over `StepsIMG`. -/
def PackRunRMG (w : List (Fin 2)) : Prop :=
  ∀ (c : Control) (r : GalilVM), InvLPC w c r →
    ∀ (j : ℕ) (x : State GalilVM),
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 j ⟨c, r⟩ x →
      ∀ (k : ℕ) (y : State GalilVM), IPackMG centre place entry q first w x →
        StepsAll (galilFrameS (PofC centre place entry w) q first) 2048 (SoundScanNR w) k x y →
        StepsIMG centre place entry q first w k x y

/-- **(KEY) `CloseoutPackRun18.packRunR_M''` over `BigResid6G`.** -/
theorem packRunR_MG {w : List (Fin 2)}
    (hr : BigResid6G centre place entry q first w)
    (hee : H_extraEntry3 centre place entry w)
    (het : H_extraTick3 centre place entry q first w)
    (hme : H_marksEntry' (PofC centre place entry w) q first) :
    PackRunRMG centre place entry q first w := by
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
  have hbx : BigPack2MG'' centre place entry q first w x :=
    ⟨hx, hauxx, hlv0 j x hjx, hmx, hexx⟩
  obtain ⟨g, hg0, hgk, htr⟩ := stepsAll_fn h
  have hreach : ∀ i, i ≤ k →
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 (j + i) ⟨c, r⟩ (g i) := by
    intro i hi
    have := steps_of_trace htr i hi
    rw [hg0] at this
    exact steps_trans hjx this
  have hbig : ∀ i, i ≤ k → BigPack2MG'' centre place entry q first w (g i) := by
    intro i
    induction i with
    | zero => intro _; rw [hg0]; exact hbx
    | succ n ih =>
      intro hi
      exact bigPack2MG''_tick centre place entry q first hr het hme (ih (by omega))
        (htr.tick n (by omega)) (htr.good (n+1) hi)
        (hlv0 (j + (n+1)) (g (n+1)) (hreach (n+1) hi))
  exact ⟨g, hg0, hgk, htr, fun i hi => (hbig i hi).ipackM⟩

theorem reachAtIMG_of_reachAtC3R {w : List (Fin 2)}
    (hpr : PackRunRMG centre place entry q first w)
    {m : ℕ} {c : Control} {r : GalilVM} (hIC : InvLPC w c r)
    (hx : IPackMG centre place entry q first w ⟨c, r⟩)
    (h : ReachAtC3 (PofC centre place entry w) q first w m c r) :
    ReachAtIMG centre place entry q first w m c r := by
  obtain ⟨y, k, L, hst, hcr, hrp, hfr, hcont⟩ := h
  have hstI : StepsIMG centre place entry q first w k ⟨c, r⟩ y :=
    hpr c r hIC 0 ⟨c, r⟩ (.zero _) k y hx hst
  refine ⟨y, k, L, hstI, hcr, hrp, hfr, fun hlt => ?_⟩
  obtain ⟨c', r', k', L', hst', hcr', hIS, hp⟩ := hcont hlt
  exact ⟨c', r', k', L',
    hpr c r hIC k y (stepsAll_steps hst) k' ⟨c', r'⟩
      (ipackMG_last_of_stepsIMG centre place entry q first hstI) hst',
    hcr', hIS.1, hp⟩

theorem cycleOutIMG_of_cycleOutMC3R {w : List (Fin 2)}
    (hpr : PackRunRMG centre place entry q first w)
    {m : ℕ} {c : Control} {r : GalilVM} (hIC : InvLPC w c r)
    (hx : IPackMG centre place entry q first w ⟨c, r⟩)
    (h : CycleOutMC3 (PofC centre place entry w) q first w m c r) :
    CycleOutIMG centre place entry q first w m c r := by
  rcases h with hdone | ⟨cT, sT, k, L, hst, hcr, hIT, hlt, hpos⟩
  · exact Or.inl (reachAtIMG_of_reachAtC3R centre place entry q first hpr hIC hx hdone)
  · exact Or.inr ⟨cT, sT, k, L, hpr c r hIC 0 ⟨c, r⟩ (.zero _) k ⟨cT, sT⟩ hx hst,
      hcr, hIT.1, hlt, hpos⟩

/-- `CloseoutPackRun12.cycleOracleIM_of_cycleOracleMC3R` over `PackRunRMG`, with
the `InvLPC`-origin pack built from the guarded `H_shiftLocalG` through
`h_shiftLocalC_of_G` (the origin is scan/non-replaying). -/
theorem cycleOracleIMG_of_cycleOracleMC3R {w : List (Fin 2)}
    (hpr : PackRunRMG centre place entry q first w)
    (hsl : H_shiftLocalG centre place entry q first w)
    (hsc : H_stageScan centre place entry q first w)
    (hor : CycleOracleMC3 (PofC centre place entry w) q first w) :
    CycleOracleIMG centre place entry q first w := by
  intro m c r hm1 hmle hIC hp
  exact cycleOutIMG_of_cycleOutMC3R centre place entry q first hpr hIC
    (ipackMG_of_ipackM centre place entry q first
      (ipackM_of_ipackO centre place entry q first
        (ipackO_of_ipack centre place entry q first
          (ipack_of_invLPC' centre place entry q first
            (h_shiftLocalC_of_G centre place entry q first hsl) (x := ⟨c, r⟩) hIC))))
    (hor m c r hm1 hmle (hstage_of_scanBranch centre place entry q first hsc c r hIC) hp)

end BridgeG

#print axioms packRunR_MG
#print axioms cycleOracleIMG_of_cycleOracleMC3R

/-- **`CloseoutPackRun26.pal_in_peg_final16` with `BigResid6` replaced by
`BigResid6G`** — the unguarded, refuted `rShiftNext` is gone from the residual;
its guarded form `RShiftNextMG` is discharged modulo `WatchShiftG` by
`rShiftNextMG_of_watchShiftG`.  `H_realizeLIM'` becomes `H_realizeLIMG'` (the
same local-realization statement quantified over `PreTraceIMG`). -/
theorem pal_in_peg_final17 (entry q : ℕ) (first : Fin 9)
    (hr : ∀ w : List (Fin 2), BigResid6G centreC placeC entry q first w)
    (hee : ∀ w : List (Fin 2), H_extraEntry3 centreC placeC entry w)
    (het : ∀ w : List (Fin 2), H_extraTick3 centreC placeC entry q first w)
    (hme : ∀ w : List (Fin 2), H_marksEntry' (PofC centreC placeC entry w) q first)
    (hsl : ∀ w : List (Fin 2), H_shiftLocalG centreC placeC entry q first w)
    (hsc : ∀ w : List (Fin 2), H_stageScan centreC placeC entry q first w)
    (hor : ∀ w : List (Fin 2), 0 < w.length →
      CycleOracleMC3 (PofC centreC placeC entry w) q first w)
    (hbs : H_bootShift centreC placeC entry q first)
    (hls : H_landShift centreC placeC entry q first)
    (hC : H_realizeLIMG' centreC placeC entry q first) :
    RecognizedByTotalPEG PAL :=
  pal_in_peg_final5MG entry q first
    (h_bootIMG_of_h_bootIM centreC placeC entry q first
      (h_bootIM_of_h_bootIO centreC placeC entry q first
        (h_bootIO_of_h_bootI centreC placeC entry q first
          (h_bootI_of_bootIPack centreC placeC entry q first
            (bootIPack_of_parts centreC placeC entry q first h_lrepC hbs hls)))))
    (fun w hw => cycleOracleIMG_of_cycleOracleMC3R centreC placeC entry q first
      (packRunR_MG centreC placeC entry q first (hr w) (hee w) (het w) (hme w))
      (hsl w) (hsc w) (hor w hw))
    hC

#print axioms pal_in_peg_final17

end PalPeg.CloseoutPackRun30
