import PalPeg.CloseoutPackRun16

/-!
# `CloseoutPackRun18`: the guarded marks corner threaded into the top-level

`CloseoutPackRun16` proved the guarded MARKS-tape invariant `MarksInv'` along
every run (`marksInv'_tick`, all twenty-four branches, under the single entry
fact `H_marksEntry'` at a selecting `choose`), and read off the rewind corner
`0 < position (left L)` at every `rewind` state **off the `FIRST` cell**
(`rewindLeft_of_marksInv'`, via `two_le_left_of_marksInv'`).  This file
threads that into `pal_in_peg_final13` with **no rewind corner left in the
enlargement**.

The one subtlety is the `FIRST` cell itself.  `MarksInv'` gives only
`1 ≤ position L` there, while `CloseoutPackRun11.Extra'.rewindMargin` asks for
`2 ≤ position L` at *every* `rewind` state, and `BigResid6.rShiftNext` is handed
`BigPack2M` (hence `Extra'`) at an arbitrary source.  So the tick is split:

* off the `FIRST` cell (or outside `rewind`) the pack forgets down to
  `BigPack2M` (`bigPack2M_of_bigPack2M''`) and `CloseoutPackRun11.lpackN_tick` /
  `BigResid6.rShiftNext` run as before;
* on the `FIRST` cell the only tick is `rewind_done` (`tick_rewind_atFirst`),
  which lands in `replayStart`: `LPackM` is `lpackN_tick`'s own `rewind_done`
  script (`lpackM_rewind_done`), and `ShiftLocal` at the landing is vacuous
  because the chain is idle outside `scan`/`shift`/`init`
  (`AuxPack.coupled.idleOut` + `CloseoutPackRun6.shiftLocal_of_chainIdle`).

* §1 `Extra3` — `CloseoutPackRun11.Extra'` with `rewindMargin` **deleted**
  (four fields); `H_extraEntry3` / `H_extraTick3` / `extra3_steps`.
* §2 `BigPack2M''` — `BigPack2M` over `Extra3` with `MarksInv' first` carried
  as a derived field; `bigPack2M''_tick`; `packRunR_M''`.  `BigResid6` is reused
  **unchanged**.
* §3 `pal_in_peg_final15` — `pal_in_peg_final13` with `H_extraEntry'` /
  `H_extraTick'` replaced by `H_extraEntry3` / `H_extraTick3` and one new
  hypothesis `H_marksEntry' (PofC centreC placeC entry w) q first`.

`MarksInv'` is parametric in `first`; the packs here are already parametric in
the same `first` (the one inside `galilFrameS`), so nothing new is threaded.

## Honest status

Standard axioms only; unconditional `PAL ∈ PEG` remains **open**.  Remaining:
the six `BigResid6` contracts, `H_extraEntry3` / `H_extraTick3` (no margin
field of any kind), `H_marksEntry'`, and — unchanged — `H_shiftLocalC`,
`H_stageScan`, `CycleOracleMC3`, `H_bootShift`, `H_landShift`, `H_realizeLIM'`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPackRun18

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
open PalPeg.CloseoutPackRun12 PalPeg.CloseoutPackRun16
open GalilScaffoldInputHead GalilScaffoldCounter GalilScaffoldChainVerifier

/-! ## 0. The `FIRST`-cell tick -/

/-- From a `rewind` state on the `FIRST` cell the only tick is `rewind_done`. -/
theorem tick_rewind_atFirst {P : Shared} {q : ℕ} {first : Fin 9} {delay : ℕ}
    {c c' : Control} {s t : GalilVM}
    (hm : c.mode = Mode.rewind) (hf : (galilFrameS P q first).atFirst s)
    (h : Tick (galilFrameS P q first) delay ⟨c, s⟩ ⟨c', t⟩) :
    c' = {c with mode := Mode.replayStart} ∧ (galilFrameS P q first).fppReset s t := by
  cases h
  all_goals first
    | exact ⟨rfl, by assumption⟩
    | (exfalso; simp_all)

#print axioms tick_rewind_atFirst

/-! ## 1. `Extra3`: the enlargement with no rewind corner -/

section ExtraT
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **(NAMED) `CloseoutPackRun11.Extra'` without `rewindMargin`.**  Four fields. -/
structure Extra3 (w : List (Fin 2)) (x : State GalilVM) : Prop where
  ready : PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get x.vm)
  failed : x.ctl.mode = Mode.scan →
    PalPeg.GalilLeafDp.StageFailed (PofC centre place entry w) w x.vm
      (GalilScaffoldCounter.value x.vm.radius).toNat
  cand : x.ctl.mode = Mode.shift →
    ∃ lower h, PalPeg.GalilDpSuffix.Candidate
      (GalilScaffoldPlace.stream ((PofC centre place entry w).place x.vm)) lower h
  scanAvail : x.ctl.mode = Mode.scan → x.ctl.replaying = false →
    GalilScaffoldChainVerifier.canRight x.vm.right

/-- `Extra'` forgets down to `Extra3`. -/
theorem extra3_of_extra' {w : List (Fin 2)} {x : State GalilVM}
    (h : Extra' centre place entry w x) : Extra3 centre place entry w x :=
  ⟨h.ready, h.failed, h.cand, h.scanAvail⟩

/-- `Extra3` plus the margin is `Extra'`. -/
theorem extra'_of_extra3 {w : List (Fin 2)} {x : State GalilVM}
    (h : Extra3 centre place entry w x)
    (hrm : x.ctl.mode = Mode.rewind → 2 ≤ position x.vm.left) :
    Extra' centre place entry w x :=
  ⟨h.ready, h.failed, h.cand, hrm, h.scanAvail⟩

/-- **(NAMED) `Extra3` at an `InvLPC` origin.** -/
def H_extraEntry3 (w : List (Fin 2)) : Prop :=
  ∀ (c : Control) (r : GalilVM), InvLPC w c r → Extra3 centre place entry w ⟨c, r⟩

/-- **(NAMED) `Extra3` travels along one tick.** -/
def H_extraTick3 (w : List (Fin 2)) : Prop :=
  ∀ x y : State GalilVM, Extra3 centre place entry w x →
    Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y →
    Extra3 centre place entry w y

theorem extra3_steps {w : List (Fin 2)} (het : H_extraTick3 centre place entry q first w)
    {n : ℕ} {x y : State GalilVM} (he : Extra3 centre place entry w x)
    (h : Steps (galilFrameS (PofC centre place entry w) q first) 2048 n x y) :
    Extra3 centre place entry w y := by
  induction h with
  | zero z => exact he
  | @succ m a b z h hr ih => exact ih (het a b he h)

end ExtraT

#print axioms extra3_of_extra'
#print axioms extra'_of_extra3
#print axioms extra3_steps

/-! ## 2. `BigPack2M''` and `packRunR_M''` -/

section ResidT
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **The enlarged pack over `Extra3`.**  `MarksInv' first` is carried as a
field only so that the pack forgets down to `BigPack2M` off the `FIRST` cell;
it is a theorem along every run from an `InvLPC` origin (`marksInv'_of_run`). -/
structure BigPack2M'' (w : List (Fin 2)) (x : State GalilVM) : Prop where
  ipackM : IPackM centre place entry q first w x
  aux : AuxPack x.ctl x.vm
  live : CentreLive x.ctl x.vm
  marks : MarksInv' first x.ctl x.vm
  extra : Extra3 centre place entry w x

/-- `BigPack2M''` forgets down to `BigPack2M` at every state that is not a
`rewind` state on the `FIRST` cell. -/
theorem bigPack2M_of_bigPack2M'' {w : List (Fin 2)} {x : State GalilVM}
    (hx : BigPack2M'' centre place entry q first w x)
    (hnf : x.ctl.mode = Mode.rewind →
      ¬ (galilFrameS (PofC centre place entry w) q first).atFirst x.vm) :
    BigPack2M centre place entry q first w x :=
  ⟨hx.ipackM, hx.aux, hx.live, extra'_of_extra3 centre place entry hx.extra
    (fun hm => two_le_left_of_marksInv' hx.marks hm (hnf hm))⟩

/-- `lpackN_tick`'s own `rewind_done` script, isolated. -/
theorem lpackM_rewind_done {w : List (Fin 2)} {c c' : Control} {s t : GalilVM}
    (hP : LPackM w c s) (hm : c.mode = Mode.rewind)
    (hc : c' = {c with mode := Mode.replayStart})
    (hi : (galilFrameS (PofC centre place entry w) q first).fppReset s t) :
    LPackM w c' t := by
  subst hc
  obtain ⟨heq, hset⟩ := hi
  exact lpackM_of_same hP (by rw [hm]; decide)
    (by rw [hset, heq]; rfl) (by rw [hset, heq]; rfl) (by rw [hset, heq]; rfl)
    (fun hs => by rcases hs with h | h <;> exact Mode.noConfusion h)
    (fun hm' _ => Mode.noConfusion hm')

/-- **One tick of `BigPack2M''`.**  Split on whether the source is a `rewind`
state on the `FIRST` cell (see the header). -/
theorem bigPack2M''_tick {w : List (Fin 2)} (hr : BigResid6 centre place entry q first w)
    (het : H_extraTick3 centre place entry q first w)
    (hme : H_marksEntry' (PofC centre place entry w) q first)
    {x y : State GalilVM} (hx : BigPack2M'' centre place entry q first w x)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y)
    (hg : SoundScanNR w y) (hlv : CentreLive y.ctl y.vm) :
    BigPack2M'' centre place entry q first w y := by
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
    apply PalPeg.CloseoutPackRun6.shiftLocal_of_chainIdle
    apply haux.coupled.idleOut
    all_goals (show c'.mode ≠ _; rw [hc']; intro h; exact Mode.noConfusion h)
  · have hnf : x.ctl.mode = Mode.rewind →
        ¬ (galilFrameS (PofC centre place entry w) q first).atFirst x.vm :=
      fun hm hf => hcase ⟨hm, hf⟩
    have hbx := bigPack2M_of_bigPack2M'' centre place entry q first hx hnf
    refine ⟨?_, hr.rShiftNext x y hbx h hg⟩
    obtain ⟨c, s⟩ := x
    obtain ⟨c', t⟩ := y
    exact lpackN_tick centre place entry q first hx.ipackM.pack
      (lticksN_of_big6 centre place entry q first hr hbx) h

/-- **(KEY) `PackRunRM` from the six `BigResid6` contracts, the two `Extra3`
obligations and the marks entry fact.**  `CloseoutPackRun14.packRunR_M'` over
`BigPack2M''`. -/
theorem packRunR_M'' {w : List (Fin 2)}
    (hr : BigResid6 centre place entry q first w)
    (hee : H_extraEntry3 centre place entry w)
    (het : H_extraTick3 centre place entry q first w)
    (hme : H_marksEntry' (PofC centre place entry w) q first) :
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
  have hexx : Extra3 centre place entry w x :=
    extra3_steps centre place entry q first het (x := ⟨c, r⟩) (hee c r hIC) hjx
  have hmx : MarksInv' first x.ctl x.vm :=
    marksInv'_of_run (PofC centre place entry w) q first 2048 hme (x := ⟨c, r⟩) hjx
      (m := Mode.scan) (by decide) (invS_mode hIC.1.1.1.1).1
  have hbx : BigPack2M'' centre place entry q first w x :=
    ⟨hx, hauxx, hlv0 j x hjx, hmx, hexx⟩
  obtain ⟨g, hg0, hgk, htr⟩ := stepsAll_fn h
  have hreach : ∀ i, i ≤ k →
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 (j + i) ⟨c, r⟩ (g i) := by
    intro i hi
    have := steps_of_trace htr i hi
    rw [hg0] at this
    exact steps_trans hjx this
  have hbig : ∀ i, i ≤ k → BigPack2M'' centre place entry q first w (g i) := by
    intro i
    induction i with
    | zero => intro _; rw [hg0]; exact hbx
    | succ n ih =>
      intro hi
      exact bigPack2M''_tick centre place entry q first hr het hme (ih (by omega))
        (htr.tick n (by omega)) (htr.good (n+1) hi)
        (hlv0 (j + (n+1)) (g (n+1)) (hreach (n+1) hi))
  exact ⟨g, hg0, hgk, htr, fun i hi => (hbig i hi).ipackM⟩

end ResidT

#print axioms bigPack2M_of_bigPack2M''
#print axioms lpackM_rewind_done
#print axioms bigPack2M''_tick
#print axioms packRunR_M''

/-! ## 3. `pal_in_peg_final15` -/

/-- **`CloseoutPackRun12.pal_in_peg_final13` with no rewind corner.**  The two
enlargement obligations are `H_extraEntry3` / `H_extraTick3` (four fields, no
margin), and the one new hypothesis is the marks entry fact `H_marksEntry'` at
a selecting `choose`.  Everything else is as in `pal_in_peg_final13`. -/
theorem pal_in_peg_final15 (entry q : ℕ) (first : Fin 9)
    (hr : ∀ w : List (Fin 2), BigResid6 centreC placeC entry q first w)
    (hee : ∀ w : List (Fin 2), H_extraEntry3 centreC placeC entry w)
    (het : ∀ w : List (Fin 2), H_extraTick3 centreC placeC entry q first w)
    (hme : ∀ w : List (Fin 2), H_marksEntry' (PofC centreC placeC entry w) q first)
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
      (packRunR_M'' centreC placeC entry q first (hr w) (hee w) (het w) (hme w))
      (hsl w) (hsc w) (hor w hw))
    hC

#print axioms pal_in_peg_final15

end PalPeg.CloseoutPackRun18
