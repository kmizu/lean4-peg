import PalPeg.CloseoutPackRun12
import PalPeg.CloseoutPackRun13

/-!
# `CloseoutPackRun14`: the leaf pack over `CentreMargin`

`CloseoutPackRun13` showed that the surviving rewind corner
`LTickLeavesN.rewindLeft` (`0 < position (left L)` at every `rewind` state)
follows from the coupling `RCouple` — a theorem on every run parked outside
`rewind` (`rcouple_of_run`) — together with the single named leaf
`CentreMargin` (`radius + pairOff + 2 ≤ position C` during `rewind`).  This
file re-cuts the leaf pack and the top-level statement over that leaf.  No
branch script is re-run: everything is composition.

* §1 `LTickLeavesN'` — `CloseoutPackRun11.LTickLeavesN` with `rewindLeft`
  replaced by `centreMargin : CentreMargin c s`; `LTickLeavesN'.toN` (under
  `RCouple`) via `rewindLeft_of_centreMargin`; `lpackN'_tick` / `lpackN'_tick'`.
* §2 `Extra''` — `CloseoutPackRun11.Extra'` with `rewindMargin` replaced by
  `centreMargin`; `H_extraEntry''` / `H_extraTick''`.
* §3 `BigPack2M'` — `BigPack2M` with `Extra''` and the (derived) coupling
  carried along; `BigResid6` is reused **unchanged** because `BigPack2M'`
  forgets down to `BigPack2M`; `bigPack2M'_tick`, `packRunR_M'`.
* §4 `pal_in_peg_final14` — `CloseoutPackRun12.pal_in_peg_final13` with
  `H_extraEntry'` / `H_extraTick'` replaced by `H_extraEntry''` / `H_extraTick''`.

## Honest status

Standard axioms only; unconditional `PAL ∈ PEG` remains open.  `CentreMargin`
itself is not proved here (it is a MARKS-tape fact invisible to `Tick`, see
`CloseoutPackRun13`); the other hypotheses of `pal_in_peg_final14` are exactly
those of `pal_in_peg_final13`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPackRun14

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
open PalPeg.CloseoutPackRun12 PalPeg.CloseoutPackRun13
open GalilScaffoldInputHead GalilScaffoldCounter GalilScaffoldChainVerifier

/-! ## 1. `LTickLeavesN'`: the leaves over the centre margin -/

section LeavesNP
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **(NAMED) the leaves of one tick, rewind corner replaced by the centre
margin.**  `CloseoutPackRun11.LTickLeavesN` with `rewindLeft` swapped for
`CloseoutPackRun13.CentreMargin`. -/
structure LTickLeavesN' (w : List (Fin 2)) (c : Control) (s : GalilVM) : Prop where
  initPackN : c.mode = Mode.init → ∀ t : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).init s t →
    LPackM w {c with mode := Mode.scan, output := true} t
  scanInvR : c.mode = Mode.scan →
    ∃ r, ScanInvariant w (position s.center) r s.left s.right
  scanCanR : c.mode = Mode.scan → GalilScaffoldChainVerifier.canRight s.right
  shiftDoneScan : c.mode = Mode.shift →
    ¬ (galilFrameS (PofC centre place entry w) q first).remainingPos s →
    ∃ r, ScanInvariant w (position s.center) r s.left s.right
  choosePackL : c.mode = Mode.choose → c.odd = true → ∀ t : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).choose s t →
    GalilScaffoldInputTrace.Represents t.left.head w ∧ t.left.head.focus ≠ none
  /-- **The one named leaf**: the centre keeps `radius + pairOff + 2` places
  to its left during `rewind`. -/
  centreMargin : CentreMargin c s
  replayPackN : c.mode = Mode.replayStart → ∀ (t : GalilVM) (o : Bool),
    (galilFrameS (PofC centre place entry w) q first).replayStart s t →
    LPackM w {c with mode := Mode.scan, clock := 2048, output := o, replaying := (galilFrameS (PofC centre place entry w) q first).replayPos t} t

/-- Under the coupling, `LTickLeavesN'` delivers `LTickLeavesN`. -/
theorem LTickLeavesN'.toN {w : List (Fin 2)} {c : Control} {s : GalilVM}
    (hco : RCouple c s) (h : LTickLeavesN' centre place entry q first w c s) :
    LTickLeavesN centre place entry q first w c s where
  initPackN := h.initPackN
  scanInvR := h.scanInvR
  scanCanR := h.scanCanR
  shiftDoneScan := h.shiftDoneScan
  choosePackL := h.choosePackL
  rewindLeft := fun hm => rewindLeft_of_centreMargin hco h.centreMargin hm
  replayPackN := h.replayPackN

/-- **(KEY) `LPackM` survives one tick over `LTickLeavesN'`.**  Composition of
`CloseoutPackRun11.lpackN_tick` with `LTickLeavesN'.toN`. -/
theorem lpackN'_tick {w : List (Fin 2)} {c c' : Control} {s t : GalilVM}
    (hco : RCouple c s) (hP : LPackM w c s)
    (hL : LTickLeavesN' centre place entry q first w c s)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 ⟨c, s⟩ ⟨c', t⟩) :
    LPackM w c' t :=
  lpackN_tick centre place entry q first hP (hL.toN centre place entry q first hco) h

/-- `lpackN'_tick` in state form. -/
theorem lpackN'_tick' {w : List (Fin 2)} {x y : State GalilVM}
    (hco : RCouple x.ctl x.vm) (hP : LPackM w x.ctl x.vm)
    (hL : LTickLeavesN' centre place entry q first w x.ctl x.vm)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y) :
    LPackM w y.ctl y.vm := by
  obtain ⟨c, s⟩ := x
  obtain ⟨c', t⟩ := y
  exact lpackN'_tick centre place entry q first hco hP hL h

end LeavesNP

#print axioms LTickLeavesN'.toN
#print axioms lpackN'_tick
#print axioms lpackN'_tick'

/-! ## 2. `Extra''`: the enlargement over the centre margin -/

section ExtraPP
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **(NAMED) `CloseoutPackRun11.Extra'` with `rewindMargin` replaced by
`CentreMargin`.** -/
structure Extra'' (w : List (Fin 2)) (x : State GalilVM) : Prop where
  ready : PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get x.vm)
  failed : x.ctl.mode = Mode.scan →
    PalPeg.GalilLeafDp.StageFailed (PofC centre place entry w) w x.vm
      (GalilScaffoldCounter.value x.vm.radius).toNat
  cand : x.ctl.mode = Mode.shift →
    ∃ lower h, PalPeg.GalilDpSuffix.Candidate
      (GalilScaffoldPlace.stream ((PofC centre place entry w).place x.vm)) lower h
  centreMargin : CentreMargin x.ctl x.vm
  scanAvail : x.ctl.mode = Mode.scan → x.ctl.replaying = false →
    GalilScaffoldChainVerifier.canRight x.vm.right

/-- Under the coupling, `Extra''` delivers `Extra'`. -/
theorem extra'_of_extra'' {w : List (Fin 2)} {x : State GalilVM}
    (hco : RCouple x.ctl x.vm) (h : Extra'' centre place entry w x) :
    Extra' centre place entry w x :=
  ⟨h.ready, h.failed, h.cand,
    fun hm => rewindMargin_of_centreMargin hco h.centreMargin hm, h.scanAvail⟩

/-- **(NAMED) `Extra''` at an `InvLPC` origin.** -/
def H_extraEntry'' (w : List (Fin 2)) : Prop :=
  ∀ (c : Control) (r : GalilVM), InvLPC w c r → Extra'' centre place entry w ⟨c, r⟩

/-- **(NAMED) `Extra''` travels along one tick.** -/
def H_extraTick'' (w : List (Fin 2)) : Prop :=
  ∀ x y : State GalilVM, Extra'' centre place entry w x →
    Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y →
    Extra'' centre place entry w y

/-- `CloseoutPackRun12.extra'_steps` over `Extra''`. -/
theorem extra''_steps {w : List (Fin 2)} (het : H_extraTick'' centre place entry q first w)
    {n : ℕ} {x y : State GalilVM} (he : Extra'' centre place entry w x)
    (h : Steps (galilFrameS (PofC centre place entry w) q first) 2048 n x y) :
    Extra'' centre place entry w y := by
  induction h with
  | zero z => exact he
  | @succ m a b z h hr ih => exact ih (het a b he h)

end ExtraPP

#print axioms extra'_of_extra''
#print axioms extra''_steps

/-! ## 3. `BigPack2M'` and `packRunR_M'` -/

section ResidMP
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **The enlarged pack over `Extra''`.**  The coupling `RCouple` is carried as
a field only so that the pack forgets down to `BigPack2M`; it is a theorem along
every run from an `InvLPC` origin (`rcouple_of_run`). -/
structure BigPack2M' (w : List (Fin 2)) (x : State GalilVM) : Prop where
  ipackM : IPackM centre place entry q first w x
  aux : AuxPack x.ctl x.vm
  live : CentreLive x.ctl x.vm
  rcouple : RCouple x.ctl x.vm
  extra : Extra'' centre place entry w x

/-- `BigPack2M'` forgets down to `BigPack2M`, so `BigResid6` is reusable as is. -/
theorem bigPack2M_of_bigPack2M' {w : List (Fin 2)} {x : State GalilVM}
    (h : BigPack2M' centre place entry q first w x) :
    BigPack2M centre place entry q first w x :=
  ⟨h.ipackM, h.aux, h.live, extra'_of_extra'' centre place entry h.rcouple h.extra⟩

/-- **The seven `LTickLeavesN'` leaves from the six `BigResid6` contracts plus
`Extra''`.**  `CloseoutPackRun11.lticksN_of_big6` with the rewind clause now
read straight off `Extra''.centreMargin`. -/
theorem lticksN'_of_big6 {w : List (Fin 2)} (hr : BigResid6 centre place entry q first w)
    {x : State GalilVM} (hx : BigPack2M' centre place entry q first w x) :
    LTickLeavesN' centre place entry q first w x.ctl x.vm where
  initPackN := hr.rInitPackM x (bigPack2M_of_bigPack2M' centre place entry q first hx)
  scanInvR := hr.rScanInvR x (bigPack2M_of_bigPack2M' centre place entry q first hx)
  scanCanR := fun hm => canR_of_partsM centre place entry hx.aux.front
    (extra'_of_extra'' centre place entry hx.rcouple hx.extra) hm
  shiftDoneScan := hr.rShiftDoneScan x (bigPack2M_of_bigPack2M' centre place entry q first hx)
  choosePackL := hr.rChoosePackL x (bigPack2M_of_bigPack2M' centre place entry q first hx)
  centreMargin := hx.extra.centreMargin
  replayPackN := hr.rReplayPackM x (bigPack2M_of_bigPack2M' centre place entry q first hx)

/-- **One tick of `BigPack2M'`.**  `CloseoutPackRun11.bigPack2M_tick` over
`Extra''`; the coupling is transported by `rcouple_tick` with no hypothesis. -/
theorem bigPack2M'_tick {w : List (Fin 2)} (hr : BigResid6 centre place entry q first w)
    (het : H_extraTick'' centre place entry q first w)
    {x y : State GalilVM} (hx : BigPack2M' centre place entry q first w x)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y)
    (hg : SoundScanNR w y) (hlv : CentreLive y.ctl y.vm) :
    BigPack2M' centre place entry q first w y := by
  have hbx := bigPack2M_of_bigPack2M' centre place entry q first hx
  refine ⟨⟨?_, hr.rShiftNext x y hbx h hg⟩,
    auxPack_tick centre place entry q first hx.aux hx.live h, hlv, ?_,
    het x y hx.extra h⟩
  · obtain ⟨c, s⟩ := x
    obtain ⟨c', t⟩ := y
    exact lpackN'_tick centre place entry q first hx.rcouple hx.ipackM.pack
      (lticksN'_of_big6 centre place entry q first hr hx) h
  · obtain ⟨c, s⟩ := x
    obtain ⟨c', t⟩ := y
    exact rcouple_tick _ q first 2048 hx.rcouple h

/-- The coupling at an `InvLPC` origin: such a state is in `scan` mode. -/
theorem rcouple_of_invLPC {w : List (Fin 2)} {c : Control} {r : GalilVM}
    (hIC : InvLPC w c r) : RCouple c r :=
  rcouple_of_mode (m := Mode.scan) (by decide) (invS_mode hIC.1.1.1.1).1

/-- **(KEY) `PackRunRM` from the six `BigResid6` contracts plus the two
`Extra''` obligations.**  `CloseoutPackRun12.packRunR_M` over `BigPack2M'`. -/
theorem packRunR_M' {w : List (Fin 2)}
    (hr : BigResid6 centre place entry q first w)
    (hee : H_extraEntry'' centre place entry w)
    (het : H_extraTick'' centre place entry q first w) :
    PackRunRM centre place entry q first w := by
  intro c r hIC j x hjx k y hx h
  have hlv0 : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 m ⟨c, r⟩ z →
      CentreLive z.ctl z.vm :=
    PalPeg.GalilOracleLeaves2.hlive_of_invLPC centre place entry q first hIC
  have haux0 : AuxPack c r :=
    ⟨coupled_of_invLPC hIC, front_of_invLPC hIC, copyPack_of_invLPC hIC⟩
  have hauxx : AuxPack x.ctl x.vm :=
    auxPack_steps centre place entry q first (x := ⟨c, r⟩) hlv0 haux0 hjx
  have hexx : Extra'' centre place entry w x :=
    extra''_steps centre place entry q first het (x := ⟨c, r⟩) (hee c r hIC) hjx
  have hcox : RCouple x.ctl x.vm :=
    rcouple_steps _ q first 2048 (x := ⟨c, r⟩) hjx (rcouple_of_invLPC hIC)
  have hbx : BigPack2M' centre place entry q first w x :=
    ⟨hx, hauxx, hlv0 j x hjx, hcox, hexx⟩
  obtain ⟨g, hg0, hgk, htr⟩ := stepsAll_fn h
  have hreach : ∀ i, i ≤ k →
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 (j + i) ⟨c, r⟩ (g i) := by
    intro i hi
    have := steps_of_trace htr i hi
    rw [hg0] at this
    exact steps_trans hjx this
  have hbig : ∀ i, i ≤ k → BigPack2M' centre place entry q first w (g i) := by
    intro i
    induction i with
    | zero => intro _; rw [hg0]; exact hbx
    | succ n ih =>
      intro hi
      exact bigPack2M'_tick centre place entry q first hr het (ih (by omega))
        (htr.tick n (by omega)) (htr.good (n+1) hi)
        (hlv0 (j + (n+1)) (g (n+1)) (hreach (n+1) hi))
  exact ⟨g, hg0, hgk, htr, fun i hi => (hbig i hi).ipackM⟩

end ResidMP

#print axioms bigPack2M_of_bigPack2M'
#print axioms lticksN'_of_big6
#print axioms bigPack2M'_tick
#print axioms rcouple_of_invLPC
#print axioms packRunR_M'

/-! ## 4. `pal_in_peg_final14` -/

/-- **`CloseoutPackRun12.pal_in_peg_final13` over the centre margin.**  Every
hypothesis is identical except that the two enlargement obligations are now
`H_extraEntry''` / `H_extraTick''`: the leaf pack demands `CentreMargin` at
`rewind` states instead of `rewindMargin` / `rewindLeft`. -/
theorem pal_in_peg_final14 (entry q : ℕ) (first : Fin 9)
    (hr : ∀ w : List (Fin 2), BigResid6 centreC placeC entry q first w)
    (hee : ∀ w : List (Fin 2), H_extraEntry'' centreC placeC entry w)
    (het : ∀ w : List (Fin 2), H_extraTick'' centreC placeC entry q first w)
    (hsl : ∀ w : List (Fin 2), H_shiftLocalC centreC placeC entry q first w)
    (hsc : ∀ w : List (Fin 2), H_stageScan centreC placeC entry q first w)
    (hor : ∀ w : List (Fin 2), 0 < w.length →
      CycleOracleMC3 (PofC centreC placeC entry w) q first w)
    (hbs : H_bootShift centreC placeC entry q first)
    (hls : H_landShift centreC placeC entry q first)
    (hC : H_realizeLIM' centreC placeC entry q first) :
    RecognizedByTotalPEG PAL :=
  pal_in_peg_final5M entry q first
    (h_bootIM_of_h_bootIO centreC placeC entry q first
      (h_bootIO_of_h_bootI centreC placeC entry q first
        (h_bootI_of_bootIPack centreC placeC entry q first
          (bootIPack_of_parts centreC placeC entry q first h_lrepC hbs hls))))
    (fun w hw => cycleOracleIM_of_cycleOracleMC3R centreC placeC entry q first
      (packRunR_M' centreC placeC entry q first (hr w) (hee w) (het w)) (hsl w) (hsc w)
      (hor w hw))
    hC

#print axioms pal_in_peg_final14

end PalPeg.CloseoutPackRun14
