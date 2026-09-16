import PalPeg.CloseoutPackRun
import PalPeg.CloseoutLPack4

/-!
# `CloseoutPackRun2`: eliminating `rLiveNext` and `H_bigEntry` at the oracle's entries

`CloseoutPackRun.BigResid` has fourteen fields.  Two of them —

* `rLiveNext` (`CentreLive` at every tick's landing) and
* the `live` half of `H_bigEntry` (`CentreLive` at the entry)

— are *not* corners of one tick at all: `CentreLive` is `GalilRewindSafe`'s
isolated MARKS-tape assumption, and `GalilOracleLeaves2.hlive_of_invLPC` already
discharges it **for every state reachable from an `InvLPC` state**, because
`GalilCentreLive.centreLive_of_invLP_run` is a *run*-level theorem.  Stating the
pack obligation pointwise (`∀ x y, … → Tick x y → CentreLive y`) throws that
away.

This file therefore re-cuts the run-level bridge so that the reachability is
kept:

* §1 `steps_of_trace`, `AuxPack`, `auxPack_steps` — `Coupled`, `FrontPack` and
  `CopyPack` are tick-stable *on their own* (`coupled_tick`, `frontPack_tick`,
  `copyPack_tick`), so they travel along a bare `Steps` run as soon as
  `CentreLive` is available along it.  Nothing of `IPack` is needed.
* §2 `BigResid'` — `BigResid` **minus `rLiveNext`** (thirteen fields), with
  `bigPack_tick'` taking the landing's `CentreLive` as a hypothesis instead.
* §3 `PackRunR` — the run-level pack obligation *relative to an `InvLPC`
  origin*, and `packRunR_of_bigResid'`: `BigResid'` alone implies it.  Both
  `rLiveNext` and all four extra `H_bigEntry` fields are discharged here
  (`hlive_of_invLPC` for `live`, `CloseoutPackRun.§4` for the other three).
* §4 the oracle bridge (`reachAtI` / `cycleOutI` / `cycleOracleI`) rebuilt over
  `PackRunR`.  This is where the relativisation pays: in `ReachAtC3` the
  continuation run starts at the report point `y`, which is not `InvLPC` — but
  it *is* reachable from the `InvLPC` entry, which is exactly what `PackRunR`
  asks for.
* §5 `pal_in_peg_final8`: `pal_in_peg_final7` with `PackRun` + `H_bigEntry`
  replaced by `BigResid'`.
* §6 `BigResid4` — the `CloseoutLPack4` sharpening lifted to the enlarged pack:
  the two origin corners become arithmetic margins (`left_pos_iff`) and the two
  mismatch-entry corners merge into one entry-free `rMismatchMinv`
  (`minv_of_mismatch`), taking thirteen fields down to twelve.

## What is left (NAMED), route by route

`BigResid4 centre place entry q first w` — twelve fields, none of which this
file can close:

* `rInitPack` — the boot step (`initVM`) establishes `LPack`.
* `rScanMargin` / `rRewindMargin` — `rad + 2 ≤ C` resp. `2 ≤ position L`: the
  scan/rewind has not reached the origin.  `CloseoutLPack4.scanInv_pos` gives
  only `1 ≤ position L` from liveness, so this is a genuine leaf.
* `rScanInvR` — `ScanInvariant` in `scan` mode *during* a replay.
* `rScanCanR` — `canRight s.right` in `scan` mode.  `FrontPack.sane` is
  `p.gap = true ∨ 0 < p.head.left.length`, which does **not** imply
  `canRight p = (p.gap = false ∨ p.head.right ≠ [] ∨ p.head.incoming ≠ [])`, so
  the frontier does not close this.
* `rMismatchMinv` — `MInv` at the target of a comparison out of `scan`.
  `afterMismatch` moves `R` one place right (`afterMismatch_right`), so this is
  `Leftmost w (position R + 1) C`: the leftmost-live-centre obligation at a
  mismatch (`GalilLiveCentreFallback.leftmost_after_fallback` for the dead-centre
  branch, `GalilLiveCentre.leftmost_match` for the live one).
* `rShiftOneMinv` / `rShiftDoneScan` — `C` moving along a shift unit, and the
  new centre's palindrome radius at the shift exit
  (`GalilPeriodCentre`, `GalilScaffoldChainReadOrigin.reshift_palindrome`).
* `rChoosePack` / `rRewindPairMinv` / `rReplayPack` — the `choose` re-centring,
  the paired rewind unit (`GalilLiveCentreShift.live_shift_of_palAt`) and the
  `replayStart` reset (`minv_after_fallback`).
* `rShiftNext` — `CloseoutLPack5.ShiftLocal` at the tick's *landing*; a
  condition on the state one lands in, so no source-state data can produce it.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPackRun2

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton PalPeg.GalilCheckpoints
open PalPeg.GalilInvPlus PalPeg.GalilInvPlus2 PalPeg.GalilInvPlus3
open PalPeg.GalilFinalAssembly PalPeg.GalilFinalAssembly2 PalPeg.GalilFinalAssembly4
open PalPeg.CloseoutLPack PalPeg.CloseoutLPack3 PalPeg.CloseoutLPack4 PalPeg.CloseoutLPack5
open PalPeg.CloseoutOracleI PalPeg.CloseoutOracleI2
open PalPeg.GalilChainCoupling PalPeg.GalilFrontMono
open PalPeg.CloseoutPackRun

/-! ## 1. `Coupled` / `FrontPack` / `CopyPack` travel along a bare `Steps` run -/

/-- Every prefix of a `Trace` is a `Steps` run out of its start. -/
theorem steps_of_trace {σ : Type} {F : Frame σ} {delay : ℕ} {Q : State σ → Prop}
    {g : ℕ → State σ} {e : ℕ} (htr : Trace F delay Q g e) :
    ∀ i, i ≤ e → Steps F delay i (g 0) (g i) := by
  intro i
  induction i with
  | zero => intro _; exact .zero _
  | succ n ih =>
    intro hi
    exact steps_trans (ih (by omega)) (.succ (htr.tick n (by omega)) (.zero _))

/-- The three self-stable invariants of the enlarged pack, bundled. -/
structure AuxPack (c : Control) (s : GalilVM) : Prop where
  coupled : Coupled c s
  front : FrontPack c s
  copyP : CopyPack c s

section Aux
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- One tick of `AuxPack`.  `CentreLive` at the *source* is all `frontPack_tick`
wants; no part of `IPack` and no `SoundScanNR` enters. -/
theorem auxPack_tick {w : List (Fin 2)} {x y : State GalilVM}
    (ha : AuxPack x.ctl x.vm) (hlv : CentreLive x.ctl x.vm)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y) :
    AuxPack y.ctl y.vm := by
  obtain ⟨c, s⟩ := x
  obtain ⟨c', t⟩ := y
  exact
    { coupled := coupled_tick (onLetterVM w) leftFirstVM centre place entry q first 2048
        ha.coupled h
      front := frontPack_tick (onLetterVM w) leftFirstVM centre place entry q first 2048
        ha.front hlv h
      copyP := copyPack_tick (onLetterVM w) leftFirstVM centre place entry q first 2048
        ha.copyP h }

/-- `AuxPack` along a whole `Steps` run, given `CentreLive` at everything
reachable from its start. -/
theorem auxPack_steps {w : List (Fin 2)} {n : ℕ} {x y : State GalilVM}
    (hlv : ∀ (j : ℕ) (z : State GalilVM),
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 j x z →
      CentreLive z.ctl z.vm)
    (ha : AuxPack x.ctl x.vm)
    (h : Steps (galilFrameS (PofC centre place entry w) q first) 2048 n x y) :
    AuxPack y.ctl y.vm := by
  induction h with
  | zero z => exact ha
  | @succ m a b z h hr ih =>
    refine ih (fun j u hu => ?_) (auxPack_tick centre place entry q first ha
      (hlv 0 a (.zero a)) h)
    exact hlv (1 + j) u (steps_trans (.succ h (.zero b)) hu)

end Aux

/-! ## 2. `BigResid'`: `BigResid` without `rLiveNext` -/

section Resid
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **(NAMED) `CloseoutPackRun.BigResid` minus `rLiveNext`.**  Thirteen fields:
the twelve `LTickLeaves` corners over the enlarged pack, plus the landing's
`ShiftLocal`.  `CentreLive` at the landing is *not* a field: §3 gets it from the
run's `InvLPC` origin. -/
structure BigResid' (w : List (Fin 2)) : Prop where
  rInitPack : ∀ x : State GalilVM, BigPack centre place entry q first w x →
    x.ctl.mode = Mode.init → ∀ t : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).init x.vm t →
    LPack w {x.ctl with mode := Mode.scan, output := true} t
  rScanLeft : ∀ x : State GalilVM, BigPack centre place entry q first w x →
    x.ctl.mode = Mode.scan → 0 < position (GalilScaffoldInputHead.left x.vm.left)
  rScanInvR : ∀ x : State GalilVM, BigPack centre place entry q first w x →
    x.ctl.mode = Mode.scan →
    ∃ r, ScanInvariant w (position x.vm.center) r x.vm.left x.vm.right
  rScanCanR : ∀ x : State GalilVM, BigPack centre place entry q first w x →
    x.ctl.mode = Mode.scan → GalilScaffoldChainVerifier.canRight x.vm.right
  rShiftMinv : ∀ x : State GalilVM, BigPack centre place entry q first w x →
    x.ctl.mode = Mode.scan → ∀ s'' t'' : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).compare x.vm s'' →
    beginShiftVM' s'' t'' → MInv w {x.ctl with clock := 2048, mode := Mode.shift} t''
  rFallbackMinv : ∀ x : State GalilVM, BigPack centre place entry q first w x →
    x.ctl.mode = Mode.scan → ∀ s'' t'' : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).compare x.vm s'' →
    (galilFrameS (PofC centre place entry w) q first).beginFallback s'' t'' →
    MInv w {x.ctl with clock := 2048, mode := Mode.copy} t''
  rShiftOneMinv : ∀ x : State GalilVM, BigPack centre place entry q first w x →
    x.ctl.mode = Mode.shift → ∀ t : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).shiftOne x.vm t → MInv w x.ctl t
  rShiftDoneScan : ∀ x : State GalilVM, BigPack centre place entry q first w x →
    x.ctl.mode = Mode.shift →
    ¬ (galilFrameS (PofC centre place entry w) q first).remainingPos x.vm →
    ∃ r, ScanInvariant w (position x.vm.center) r x.vm.left x.vm.right
  rChoosePack : ∀ x : State GalilVM, BigPack centre place entry q first w x →
    x.ctl.mode = Mode.choose → x.ctl.odd = true → ∀ t : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).choose x.vm t →
    (GalilScaffoldInputTrace.Represents t.left.head w ∧ t.left.head.focus ≠ none) ∧
      MInv w {x.ctl with mode := Mode.rewind, pair := false} t
  rRewindLeft : ∀ x : State GalilVM, BigPack centre place entry q first w x →
    x.ctl.mode = Mode.rewind → 0 < position (GalilScaffoldInputHead.left x.vm.left)
  rRewindPairMinv : ∀ x : State GalilVM, BigPack centre place entry q first w x →
    x.ctl.mode = Mode.rewind → ∀ t : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).rewindPair x.vm t →
    MInv w {x.ctl with pair := false} t
  rReplayPack : ∀ x : State GalilVM, BigPack centre place entry q first w x →
    x.ctl.mode = Mode.replayStart → ∀ (t : GalilVM) (o : Bool),
    (galilFrameS (PofC centre place entry w) q first).replayStart x.vm t →
    LPack w {x.ctl with mode := Mode.scan, clock := 2048, output := o, replaying := (galilFrameS (PofC centre place entry w) q first).replayPos t} t
  rShiftNext : ∀ x y : State GalilVM, BigPack centre place entry q first w x →
    Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y →
    SoundScanNR w y → ShiftLocal centre place entry q first w y

/-- The twelve corners, repackaged as `CloseoutLPack3.LTickLeaves`. -/
theorem lticks_of_bigResid' {w : List (Fin 2)} (hr : BigResid' centre place entry q first w)
    {x : State GalilVM} (hx : BigPack centre place entry q first w x) :
    LTickLeaves centre place entry q first w x.ctl x.vm :=
  { initPack := hr.rInitPack x hx
    scanLeft := hr.rScanLeft x hx
    scanInvR := hr.rScanInvR x hx
    scanCanR := hr.rScanCanR x hx
    shiftMinv := hr.rShiftMinv x hx
    fallbackMinv := hr.rFallbackMinv x hx
    shiftOneMinv := hr.rShiftOneMinv x hx
    shiftDoneScan := hr.rShiftDoneScan x hx
    choosePack := hr.rChoosePack x hx
    rewindLeft := hr.rRewindLeft x hx
    rewindPairMinv := hr.rRewindPairMinv x hx
    replayPack := hr.rReplayPack x hx }

/-- `AuxPack` is the non-`IPack`, non-`CentreLive` part of `BigPack`. -/
theorem auxPack_of_bigPack {w : List (Fin 2)} {x : State GalilVM}
    (hx : BigPack centre place entry q first w x) : AuxPack x.ctl x.vm :=
  ⟨hx.coupled, hx.front, hx.copyP⟩

/-- `BigPack` out of its three parts. -/
theorem bigPack_mk {w : List (Fin 2)} {x : State GalilVM}
    (hI : IPack centre place entry q first w x) (ha : AuxPack x.ctl x.vm)
    (hlv : CentreLive x.ctl x.vm) : BigPack centre place entry q first w x :=
  ⟨hI, ha.coupled, ha.front, ha.copyP, hlv⟩

/-- **`BigPack` along one tick, with the landing's `CentreLive` supplied.**
`CloseoutPackRun.bigPack_tick` with `rLiveNext` replaced by a hypothesis. -/
theorem bigPack_tick' {w : List (Fin 2)} (hr : BigResid' centre place entry q first w)
    {x y : State GalilVM} (hx : BigPack centre place entry q first w x)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y)
    (hg : SoundScanNR w y) (hlv : CentreLive y.ctl y.vm) :
    BigPack centre place entry q first w y := by
  refine bigPack_mk centre place entry q first
    ⟨?_, hr.rShiftNext x y hx h hg⟩
    (auxPack_tick centre place entry q first (auxPack_of_bigPack centre place entry q first hx)
      hx.live h) hlv
  obtain ⟨c, s⟩ := x
  obtain ⟨c', t⟩ := y
  exact lpack_tick centre place entry q first hx.ipack.pack
    (lticks_of_bigResid' centre place entry q first hr hx) h

end Resid

/-! ## 3. `PackRunR`: the pack obligation relative to an `InvLPC` origin -/

section Run
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **The run-level pack obligation, relativised.**  Every `StepsAll` run out of
a packed state *reachable from an `InvLPC` state* is a packed run.  This is
`CloseoutOracleI2.PackRun` with the origin remembered — which is all §4 ever
needs, and what makes `CentreLive` free. -/
def PackRunR (w : List (Fin 2)) : Prop :=
  ∀ (c : Control) (r : GalilVM), InvLPC w c r →
    ∀ (j : ℕ) (x : State GalilVM),
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 j ⟨c, r⟩ x →
      ∀ (k : ℕ) (y : State GalilVM), IPack centre place entry q first w x →
        StepsAll (galilFrameS (PofC centre place entry w) q first) 2048 (SoundScanNR w) k x y →
        StepsI centre place entry q first w k x y

/-- **`BigPack` at an `InvLPC` state, with nothing left over.**
`CloseoutPackRun.bigEntry_of_invLPC` had `CentreLive` as an input;
`GalilOracleLeaves2.hlive_of_invLPC` at `m = 0` supplies it. -/
theorem bigPack_of_invLPC {w : List (Fin 2)} {c : Control} {r : GalilVM}
    (hIC : InvLPC w c r) (hI : IPack centre place entry q first w ⟨c, r⟩) :
    BigPack centre place entry q first w ⟨c, r⟩ :=
  bigEntry_of_invLPC centre place entry q first (x := ⟨c, r⟩) hIC
    (PalPeg.GalilOracleLeaves2.hlive_of_invLPC centre place entry q first hIC 0 ⟨c, r⟩
      (.zero _)) hI

/-- **`PackRunR` from `BigResid'` alone.**  Both `rLiveNext` and all four extra
fields of `CloseoutPackRun.H_bigEntry` are discharged: `CentreLive` everywhere
along the run by `hlive_of_invLPC`, the other three at the origin by
`CloseoutPackRun.§4` and then along the run by `auxPack_steps`. -/
theorem packRunR_of_bigResid' {w : List (Fin 2)}
    (hr : BigResid' centre place entry q first w) :
    PackRunR centre place entry q first w := by
  intro c r hIC j x hjx k y hx h
  -- `CentreLive` at everything reachable from the origin.
  have hlv0 : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 m ⟨c, r⟩ z →
      CentreLive z.ctl z.vm :=
    PalPeg.GalilOracleLeaves2.hlive_of_invLPC centre place entry q first hIC
  -- `AuxPack` at the origin needs no pack at all.
  have haux0 : AuxPack c r :=
    ⟨coupled_of_invLPC hIC, front_of_invLPC hIC, copyPack_of_invLPC hIC⟩
  have hauxx : AuxPack x.ctl x.vm :=
    auxPack_steps centre place entry q first (x := ⟨c, r⟩) hlv0 haux0 hjx
  have hbx : BigPack centre place entry q first w x :=
    bigPack_mk centre place entry q first hx hauxx (hlv0 j x hjx)
  obtain ⟨g, hg0, hgk, htr⟩ := stepsAll_fn h
  have hreach : ∀ i, i ≤ k →
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 (j + i) ⟨c, r⟩ (g i) := by
    intro i hi
    have := steps_of_trace htr i hi
    rw [hg0] at this
    exact steps_trans hjx this
  have hbig : ∀ i, i ≤ k → BigPack centre place entry q first w (g i) := by
    intro i
    induction i with
    | zero => intro _; rw [hg0]; exact hbx
    | succ n ih =>
      intro hi
      exact bigPack_tick' centre place entry q first hr (ih (by omega))
        (htr.tick n (by omega)) (htr.good (n+1) hi)
        (hlv0 (j + (n+1)) (g (n+1)) (hreach (n+1) hi))
  exact ⟨g, hg0, hgk, htr, fun i hi => (hbig i hi).ipack⟩

end Run

/-! ## 4. The oracle bridge over `PackRunR` -/

section Bridge
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **`ReachAtC3` becomes `ReachAtI`** under `PackRunR`.  The continuation run
starts at the report point `y`, which is *not* an `InvLPC` state — but it is
reachable from the `InvLPC` entry by the first run (`stepsAll_steps`), which is
exactly the shape `PackRunR` accepts. -/
theorem reachAtI_of_reachAtC3R {w : List (Fin 2)} (hpr : PackRunR centre place entry q first w)
    {m : ℕ} {c : Control} {r : GalilVM} (hIC : InvLPC w c r)
    (hx : IPack centre place entry q first w ⟨c, r⟩)
    (h : ReachAtC3 (PofC centre place entry w) q first w m c r) :
    ReachAtI centre place entry q first w m c r := by
  obtain ⟨y, k, L, hst, hcr, hrp, hfr, hcont⟩ := h
  have hstI : StepsI centre place entry q first w k ⟨c, r⟩ y :=
    hpr c r hIC 0 ⟨c, r⟩ (.zero _) k y hx hst
  refine ⟨y, k, L, hstI, hcr, hrp, hfr, fun hlt => ?_⟩
  obtain ⟨c', r', k', L', hst', hcr', hIS, hp⟩ := hcont hlt
  exact ⟨c', r', k', L',
    hpr c r hIC k y (stepsAll_steps hst) k' ⟨c', r'⟩
      (ipack_last_of_stepsI centre place entry q first hstI) hst',
    hcr', hIS.1, hp⟩

/-- **`CycleOutMC3` becomes `CycleOutI`** under `PackRunR`. -/
theorem cycleOutI_of_cycleOutMC3R {w : List (Fin 2)} (hpr : PackRunR centre place entry q first w)
    {m : ℕ} {c : Control} {r : GalilVM} (hIC : InvLPC w c r)
    (hx : IPack centre place entry q first w ⟨c, r⟩)
    (h : CycleOutMC3 (PofC centre place entry w) q first w m c r) :
    CycleOutI centre place entry q first w m c r := by
  rcases h with hdone | ⟨cT, sT, k, L, hst, hcr, hIT, hlt, hpos⟩
  · exact Or.inl (reachAtI_of_reachAtC3R centre place entry q first hpr hIC hx hdone)
  · exact Or.inr ⟨cT, sT, k, L, hpr c r hIC 0 ⟨c, r⟩ (.zero _) k ⟨cT, sT⟩ hx hst,
      hcr, hIT.1, hlt, hpos⟩

/-- **The packed cycle oracle from the unpacked one**, over `PackRunR`.
`CloseoutOracleI2.cycleOracleI_of_cycleOracleMC3` verbatim, except that the
`InvLPC` hypothesis of `CycleOracleI` is now *used* rather than only consumed by
`ipack_of_invLPC'`. -/
theorem cycleOracleI_of_cycleOracleMC3R {w : List (Fin 2)}
    (hpr : PackRunR centre place entry q first w)
    (hsl : H_shiftLocalC centre place entry q first w)
    (hsc : H_stageScan centre place entry q first w)
    (hor : CycleOracleMC3 (PofC centre place entry w) q first w) :
    CycleOracleI centre place entry q first w := by
  intro m c r hm1 hmle hIC hp
  exact cycleOutI_of_cycleOutMC3R centre place entry q first hpr hIC
    (ipack_of_invLPC' centre place entry q first hsl (x := ⟨c, r⟩) hIC)
    (hor m c r hm1 hmle (hstage_of_scanBranch centre place entry q first hsc c r hIC) hp)

end Bridge

/-! ## 5. `pal_in_peg_final7` over `BigResid'` -/

/-- **`CloseoutPackRun.pal_in_peg_final7` with `PackRun` and `H_bigEntry`
replaced by `BigResid'` alone.**  Compared with `pal_in_peg_final7`, the
`rLiveNext` field and the whole `H_bigEntry` obligation are gone. -/
theorem pal_in_peg_final8 (entry q : ℕ) (first : Fin 9)
    (hr : ∀ w : List (Fin 2), BigResid' centreC placeC entry q first w)
    (hsl : ∀ w : List (Fin 2), H_shiftLocalC centreC placeC entry q first w)
    (hsc : ∀ w : List (Fin 2), H_stageScan centreC placeC entry q first w)
    (hor : ∀ w : List (Fin 2), 0 < w.length →
      CycleOracleMC3 (PofC centreC placeC entry w) q first w)
    (hbs : H_bootShift centreC placeC entry q first)
    (hls : H_landShift centreC placeC entry q first)
    (hC : H_realizeLI' centreC placeC entry q first) :
    RecognizedByTotalPEG PAL :=
  pal_in_peg_final6' entry q first h_lrepC hbs hls
    (fun w hw => cycleOracleI_of_cycleOracleMC3R centreC placeC entry q first
      (packRunR_of_bigResid' centreC placeC entry q first (hr w)) (hsl w) (hsc w) (hor w hw))
    hC

/-! ## 6. `BigResid4`: the `CloseoutLPack4` sharpening over the enlarged pack -/

section Sharp
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **(NAMED) the sharpened residual, twelve fields.**  `CloseoutLPack4`'s two
moves, lifted to the enlarged pack:

* the two origin corners `rScanLeft` / `rRewindLeft` become the arithmetic
  margins `rScanMargin` / `rRewindMargin` (`left_pos_iff`), with no head shape
  left in them;
* the two mismatch-entry corners `rShiftMinv` / `rFallbackMinv` merge into the
  single entry-free `rMismatchMinv`, because `beginShiftVM'` and
  `beginFallbackVM'` both leave `L`, `C`, `R` and the replay counter alone
  (`minv_of_mismatch`). -/
structure BigResid4 (w : List (Fin 2)) : Prop where
  rInitPack : ∀ x : State GalilVM, BigPack centre place entry q first w x →
    x.ctl.mode = Mode.init → ∀ t : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).init x.vm t →
    LPack w {x.ctl with mode := Mode.scan, output := true} t
  rScanMargin : ∀ x : State GalilVM, BigPack centre place entry q first w x →
    x.ctl.mode = Mode.scan → ∀ r : ℕ,
    ScanInvariant w (position x.vm.center) r x.vm.left x.vm.right →
    r + 2 ≤ position x.vm.center
  rRewindMargin : ∀ x : State GalilVM, BigPack centre place entry q first w x →
    x.ctl.mode = Mode.rewind → 2 ≤ position x.vm.left
  rScanInvR : ∀ x : State GalilVM, BigPack centre place entry q first w x →
    x.ctl.mode = Mode.scan →
    ∃ r, ScanInvariant w (position x.vm.center) r x.vm.left x.vm.right
  rScanCanR : ∀ x : State GalilVM, BigPack centre place entry q first w x →
    x.ctl.mode = Mode.scan → GalilScaffoldChainVerifier.canRight x.vm.right
  rMismatchMinv : ∀ x : State GalilVM, BigPack centre place entry q first w x →
    x.ctl.mode = Mode.scan → ∀ s'' : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).compare x.vm s'' →
    MInv w {x.ctl with clock := 2048} s''
  rShiftOneMinv : ∀ x : State GalilVM, BigPack centre place entry q first w x →
    x.ctl.mode = Mode.shift → ∀ t : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).shiftOne x.vm t → MInv w x.ctl t
  rShiftDoneScan : ∀ x : State GalilVM, BigPack centre place entry q first w x →
    x.ctl.mode = Mode.shift →
    ¬ (galilFrameS (PofC centre place entry w) q first).remainingPos x.vm →
    ∃ r, ScanInvariant w (position x.vm.center) r x.vm.left x.vm.right
  rChoosePack : ∀ x : State GalilVM, BigPack centre place entry q first w x →
    x.ctl.mode = Mode.choose → x.ctl.odd = true → ∀ t : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).choose x.vm t →
    (GalilScaffoldInputTrace.Represents t.left.head w ∧ t.left.head.focus ≠ none) ∧
      MInv w {x.ctl with mode := Mode.rewind, pair := false} t
  rRewindPairMinv : ∀ x : State GalilVM, BigPack centre place entry q first w x →
    x.ctl.mode = Mode.rewind → ∀ t : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).rewindPair x.vm t →
    MInv w {x.ctl with pair := false} t
  rReplayPack : ∀ x : State GalilVM, BigPack centre place entry q first w x →
    x.ctl.mode = Mode.replayStart → ∀ (t : GalilVM) (o : Bool),
    (galilFrameS (PofC centre place entry w) q first).replayStart x.vm t →
    LPack w {x.ctl with mode := Mode.scan, clock := 2048, output := o, replaying := (galilFrameS (PofC centre place entry w) q first).replayPos t} t
  rShiftNext : ∀ x y : State GalilVM, BigPack centre place entry q first w x →
    Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y →
    SoundScanNR w y → ShiftLocal centre place entry q first w y

/-- **The sharpened residual implies `BigResid'`.** -/
theorem bigResid'_of_big4 {w : List (Fin 2)} (h : BigResid4 centre place entry q first w) :
    BigResid' centre place entry q first w where
  rInitPack := h.rInitPack
  rScanLeft := fun x hx hm => by
    obtain ⟨r, hi⟩ := h.rScanInvR x hx hm
    exact left_pos_of_two (margin_of_scanInv hi (h.rScanMargin x hx hm r hi))
  rScanInvR := h.rScanInvR
  rScanCanR := h.rScanCanR
  rShiftMinv := fun x hx hm s'' _ hcmp hb =>
    minv_of_mismatch (c := {x.ctl with clock := 2048}) rfl (beginShift_heads hb)
      (h.rMismatchMinv x hx hm s'' hcmp)
  rFallbackMinv := fun x hx hm s'' _ hcmp hb =>
    minv_of_mismatch (c := {x.ctl with clock := 2048}) rfl (beginFallback_heads hb)
      (h.rMismatchMinv x hx hm s'' hcmp)
  rShiftOneMinv := h.rShiftOneMinv
  rShiftDoneScan := h.rShiftDoneScan
  rChoosePack := h.rChoosePack
  rRewindLeft := fun x hx hm => left_pos_of_two (h.rRewindMargin x hx hm)
  rRewindPairMinv := h.rRewindPairMinv
  rReplayPack := h.rReplayPack
  rShiftNext := h.rShiftNext

/-- `PackRunR` from the sharpened residual. -/
theorem packRunR_of_big4 {w : List (Fin 2)} (h : BigResid4 centre place entry q first w) :
    PackRunR centre place entry q first w :=
  packRunR_of_bigResid' centre place entry q first (bigResid'_of_big4 centre place entry q first h)

end Sharp

/-- **`pal_in_peg_final8` over the sharpened residual.**  Twelve NAMED fields,
listed route by route in the module docstring. -/
theorem pal_in_peg_final9 (entry q : ℕ) (first : Fin 9)
    (hr : ∀ w : List (Fin 2), BigResid4 centreC placeC entry q first w)
    (hsl : ∀ w : List (Fin 2), H_shiftLocalC centreC placeC entry q first w)
    (hsc : ∀ w : List (Fin 2), H_stageScan centreC placeC entry q first w)
    (hor : ∀ w : List (Fin 2), 0 < w.length →
      CycleOracleMC3 (PofC centreC placeC entry w) q first w)
    (hbs : H_bootShift centreC placeC entry q first)
    (hls : H_landShift centreC placeC entry q first)
    (hC : H_realizeLI' centreC placeC entry q first) :
    RecognizedByTotalPEG PAL :=
  pal_in_peg_final8 entry q first
    (fun w => bigResid'_of_big4 centreC placeC entry q first (hr w)) hsl hsc hor hbs hls hC

#print axioms steps_of_trace
#print axioms auxPack_tick
#print axioms auxPack_steps
#print axioms lticks_of_bigResid'
#print axioms bigPack_tick'
#print axioms bigPack_of_invLPC
#print axioms packRunR_of_bigResid'
#print axioms reachAtI_of_reachAtC3R
#print axioms cycleOutI_of_cycleOutMC3R
#print axioms cycleOracleI_of_cycleOracleMC3R
#print axioms pal_in_peg_final8
#print axioms bigResid'_of_big4
#print axioms packRunR_of_big4
#print axioms pal_in_peg_final9

end PalPeg.CloseoutPackRun2
