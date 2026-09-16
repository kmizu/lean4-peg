import PalPeg.CloseoutOracleI2
import PalPeg.CloseoutLPack3
import PalPeg.GalilFrontMono
import PalPeg.GalilChainCoupling

/-!
# `CloseoutPackRun`: the enlarged pack and `CloseoutOracleI2.PackRun`

`CloseoutOracleI2.PackRun` is the run-level bridge every unpacked oracle leaf
has to cross:

    ∀ k x y, IPack … x → StepsAll (galilFrameS (PofC …) q first) 2048 (SoundScanNR w) k x y →
      StepsI … w k x y

It is implied by `CloseoutOracleI.PackTick`, i.e. by tick-locality of `IPack`,
and `CloseoutLPack3.lpack_tick` showed exactly *which* parts of one tick are not
`LPack`-local: the five `LTickLeaves` corners (the origin at a comparison and at
a rewind unit, the scan invariant / right mobility in `scan`, `MInv` at the two
entries and where `C` moves, the post-shift radius) plus the three landings.

**The move made here** is the one `CloseoutLPack4` pointed at: do not try to
make `IPack` tick-local, make the *pack larger* until the corners are local.
`BigPack` (§1) is `IPack` together with the four invariants that are already
known to be tick-stable on their own —

* `GalilChainCoupling.Coupled` (`coupled_tick`), the chain/scan coupling, which
  is what `ShiftLocal.coupled`'s `distance ≤ 2·rad` and `ShiftLocal.guard`'s
  place count are about;
* `GalilFrontMono.FrontPack` (`frontPack_tick`), whose `sane` / `frontier` /
  `replayPos` / `rewind` fields are the frontier data behind `scanCanR` during a
  replay and behind the `rewind` phase;
* `GalilChainCoupling.CopyPack` (`copyPack_tick`), the `hcopy` idleness;
* `CentreLive` (`GalilRewindSafe`), which `frontPack_tick` itself consumes.

§2 proves `bigPack_tick`: **`BigPack` along one tick**, with the `Coupled` /
`FrontPack` / `CopyPack` halves discharged outright by the three existing tick
lemmas, and the `IPack` half by `CloseoutLPack3.lpack_tick` fed from `BigResid`.

§3 is the payoff: `stepsI_of_bigPack` runs the induction over `StepsAll`
carrying `BigPack` and projecting `IPack`, and `packRun_of_bigResid` is
`CloseoutOracleI2.PackRun` — so `PackRun` no longer needs `PackTick`, only
`BigResid` plus `BigPack` at the entry (`H_bigEntry`), and §4 shows that at an `InvLPC` entry three
of the four extra fields are *not* residuals (`front_of_invLPC`,
`coupled_of_invLPC`, `copyPack_of_invLPC`), so `H_bigEntry` there is `CentreLive`
alone.

## Residual (NAMED), route by route

`BigResid centre place entry q first w` has one field per non-local route of
`CloseoutLPack3.LTickLeaves`, each now stated **over the enlarged pack**, i.e.
with `Coupled`, `FrontPack`, `CopyPack` and `CentreLive` available at the source
state (this is the whole point: e.g. `rScanInvR` may use `Coupled.sum`, `rScanCanR`
the frontier, `rShiftDoneScan` the candidate period `GalilCandidatePeriod.candidate_palAt`,
`rFallbackMinv` the DP maximality `GalilLiveCentreFallback.leftmost_after_fallback`,
`rScanLeft` / `rRewindLeft` the `Live`/`Leftmost` origin bound):

* `rInitPack`, `rScanLeft`, `rScanInvR`, `rScanCanR`, `rShiftMinv`,
  `rFallbackMinv`, `rShiftOneMinv`, `rShiftDoneScan`, `rChoosePack`,
  `rRewindLeft`, `rRewindPairMinv`, `rReplayPack` — the twelve
  `LTickLeaves` corners at `∀ x, BigPack … x → …`.
* `rShiftNext` — `ShiftLocal` at the tick's *landing* (`IPack`'s second half;
  `CloseoutLPack5.ShiftLocal` is a condition on the state one lands in, so no
  amount of source-state data can produce it).
* `rLiveNext` — `CentreLive` at the landing: the `rewind_pair` stopping rule
  lives on the MARKS tape and is invisible to `Tick`, so this is the same
  isolated assumption `GalilRewindSafe` names, now carried along the run.
* `H_bigEntry` (§3) — `BigPack` at a state where only `IPack` is known.  At an
  `InvLPC` entry §4 leaves only `CentreLive` of it
  (`GalilCentreLive.centreLive_of_invLP_run` supplies that from a run).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPackRun

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton PalPeg.GalilCheckpoints
open PalPeg.GalilInvPlus PalPeg.GalilInvPlus2 PalPeg.GalilInvPlus3
open PalPeg.GalilFinalAssembly PalPeg.GalilFinalAssembly2 PalPeg.GalilFinalAssembly4
open PalPeg.CloseoutLPack PalPeg.CloseoutLPack3 PalPeg.CloseoutLPack5
open PalPeg.CloseoutOracleI PalPeg.CloseoutOracleI2
open PalPeg.GalilChainCoupling PalPeg.GalilFrontMono

/-! ## 1. The enlarged pack -/

section Big
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **The enlarged pack.**  `IPack` plus the four invariants that are tick-stable
by themselves; they are exactly the data the `LTickLeaves` corners need. -/
structure BigPack (w : List (Fin 2)) (x : State GalilVM) : Prop where
  ipack : IPack centre place entry q first w x
  coupled : Coupled x.ctl x.vm
  front : FrontPack x.ctl x.vm
  copyP : CopyPack x.ctl x.vm
  live : CentreLive x.ctl x.vm

/-- **(NAMED) the corners of one tick, over the enlarged pack.**  One field per
non-local route of `CloseoutLPack3.LTickLeaves`, plus the two landing
conditions.  Each field now has `Coupled` / `FrontPack` / `CopyPack` /
`CentreLive` at the source state available. -/
structure BigResid (w : List (Fin 2)) : Prop where
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
  /-- The shift-entry conditions at the tick's **landing**. -/
  rShiftNext : ∀ x y : State GalilVM, BigPack centre place entry q first w x →
    Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y →
    SoundScanNR w y → ShiftLocal centre place entry q first w y
  /-- `CentreLive` at the landing (the MARKS-tape stopping rule). -/
  rLiveNext : ∀ x y : State GalilVM, BigPack centre place entry q first w x →
    Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y →
    CentreLive y.ctl y.vm

/-- The `BigResid` corners, repackaged as the `LTickLeaves` of the source
state. -/
theorem lticks_of_bigResid {w : List (Fin 2)} (hr : BigResid centre place entry q first w)
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

end Big

/-! ## 2. `BigPack` along one tick -/

section Tick
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **`BigPack` survives one tick.**  `Coupled`, `FrontPack` and `CopyPack` are
discharged by their own tick lemmas; `LPack` by `CloseoutLPack3.lpack_tick`
through `lticks_of_bigResid`; the two landing conditions are `BigResid`'s. -/
theorem bigPack_tick {w : List (Fin 2)} (hr : BigResid centre place entry q first w)
    {x y : State GalilVM} (hx : BigPack centre place entry q first w x)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y)
    (hg : SoundScanNR w y) :
    BigPack centre place entry q first w y := by
  obtain ⟨c, s⟩ := x
  obtain ⟨c', t⟩ := y
  refine
    { ipack := ⟨lpack_tick centre place entry q first hx.ipack.pack
          (lticks_of_bigResid centre place entry q first hr hx) h,
        hr.rShiftNext ⟨c, s⟩ ⟨c', t⟩ hx h hg⟩
      coupled := coupled_tick (onLetterVM w) leftFirstVM centre place entry q first 2048
        hx.coupled h
      front := frontPack_tick (onLetterVM w) leftFirstVM centre place entry q first 2048
        hx.front hx.live h
      copyP := copyPack_tick (onLetterVM w) leftFirstVM centre place entry q first 2048
        hx.copyP h
      live := hr.rLiveNext ⟨c, s⟩ ⟨c', t⟩ hx h }

end Tick

/-! ## 3. `PackRun` -/

section Run
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **(NAMED) the enlarged pack at an entry state.**  `PackRun` is stated with
`IPack` at the entry only, so the four extra invariants have to be produced
there; §4 discharges the `FrontPack` field at an `InvLPC` entry. -/
def H_bigEntry (w : List (Fin 2)) : Prop :=
  ∀ x : State GalilVM, IPack centre place entry q first w x →
    BigPack centre place entry q first w x

/-- **Every `StepsAll` run out of a `BigPack` state is a `StepsI` run.** -/
theorem stepsI_of_bigPack {w : List (Fin 2)} (hr : BigResid centre place entry q first w)
    {k : ℕ} {x y : State GalilVM} (hx : BigPack centre place entry q first w x)
    (h : StepsAll (galilFrameS (PofC centre place entry w) q first) 2048 (SoundScanNR w) k x y) :
    StepsI centre place entry q first w k x y := by
  obtain ⟨g, hg0, hgk, htr⟩ := stepsAll_fn h
  have hbig : ∀ i, i ≤ k → BigPack centre place entry q first w (g i) := by
    intro i
    induction i with
    | zero => intro _; rw [hg0]; exact hx
    | succ n ih =>
      intro hi
      exact bigPack_tick centre place entry q first hr (ih (by omega))
        (htr.tick n (by omega)) (htr.good (n+1) hi)
  exact ⟨g, hg0, hgk, htr, fun i hi => (hbig i hi).ipack⟩

/-- **`CloseoutOracleI2.PackRun` from the enlarged pack.**  This replaces
`CloseoutOracleI.PackTick` — which `CloseoutLPack4` showed is false as stated —
by `BigResid` plus `H_bigEntry`. -/
theorem packRun_of_bigResid {w : List (Fin 2)} (hr : BigResid centre place entry q first w)
    (he : H_bigEntry centre place entry q first w) :
    PackRun centre place entry q first w :=
  fun _ _ _ hx h => stepsI_of_bigPack centre place entry q first hr (he _ hx) h

end Run

/-! ## 4. The entry: `FrontPack` is free at an `InvLPC` state -/

section Entry
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- `GalilFrontMono.frontPack_of_invS` at an `InvLPC` entry: the `front` field of
`H_bigEntry` is not a residual where the oracle enters. -/
theorem front_of_invLPC {w : List (Fin 2)} {c : Control} {r : GalilVM}
    (hIC : InvLPC w c r) : FrontPack c r :=
  frontPack_of_invS hIC.1.1.1.1

/-- `GalilChainCoupling.coupled_of_invL` at an `InvLPC` entry: an `InvL` state is
chain-idle, hence coupled. -/
theorem coupled_of_invLPC {w : List (Fin 2)} {c : Control} {r : GalilVM}
    (hIC : InvLPC w c r) : Coupled c r :=
  coupled_of_invL hIC.1.1.1

/-- `CopyPack` is literally a field of `InvLP2`. -/
theorem copyPack_of_invLPC {w : List (Fin 2)} {c : Control} {r : GalilVM}
    (hIC : InvLPC w c r) : CopyPack c r := hIC.1.2

/-- **`H_bigEntry` at the oracle's entries, with three of its four extra fields
discharged.**  Only `CentreLive` — the MARKS-tape stopping rule of
`GalilRewindSafe`, obtainable from a run by
`GalilCentreLive.centreLive_of_invLP_run` — stays an input. -/
theorem bigEntry_of_invLPC {w : List (Fin 2)} {x : State GalilVM}
    (hIC : InvLPC w x.ctl x.vm) (hlv : CentreLive x.ctl x.vm)
    (hI : IPack centre place entry q first w x) :
    BigPack centre place entry q first w x :=
  { ipack := hI, coupled := coupled_of_invLPC hIC, front := front_of_invLPC hIC,
    copyP := copyPack_of_invLPC hIC, live := hlv }

end Entry

/-! ## 5. `pal_in_peg_final6''` over `BigResid` -/

/-- **`CloseoutOracleI2.pal_in_peg_final6''` with `PackRun` replaced by the
enlarged pack.** -/
theorem pal_in_peg_final7 (entry q : ℕ) (first : Fin 9)
    (hr : ∀ w : List (Fin 2), BigResid centreC placeC entry q first w)
    (he : ∀ w : List (Fin 2), H_bigEntry centreC placeC entry q first w)
    (hsl : ∀ w : List (Fin 2), H_shiftLocalC centreC placeC entry q first w)
    (hsc : ∀ w : List (Fin 2), H_stageScan centreC placeC entry q first w)
    (hor : ∀ w : List (Fin 2), 0 < w.length →
      CycleOracleMC3 (PofC centreC placeC entry w) q first w)
    (hbs : H_bootShift centreC placeC entry q first)
    (hls : H_landShift centreC placeC entry q first)
    (hC : H_realizeLI' centreC placeC entry q first) :
    RecognizedByTotalPEG PAL :=
  pal_in_peg_final6'' entry q first
    (fun w => packRun_of_bigResid centreC placeC entry q first (hr w) (he w))
    hsl hsc hor hbs hls hC

#print axioms lticks_of_bigResid
#print axioms bigPack_tick
#print axioms stepsI_of_bigPack
#print axioms packRun_of_bigResid
#print axioms front_of_invLPC
#print axioms coupled_of_invLPC
#print axioms copyPack_of_invLPC
#print axioms bigEntry_of_invLPC
#print axioms pal_in_peg_final7

end PalPeg.CloseoutPackRun
