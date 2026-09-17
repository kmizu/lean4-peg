import PalPeg.CloseoutPackRun43
import PalPeg.CloseoutPreload37

/-!
# `CloseoutPackRun45`: the `ready` field of `Extra5` relativised to `scan`/`shift`

`CloseoutPackRun43` deleted `Extra3.failed` and `Extra3.cand`, leaving
`Extra5` = `ready` (unconditional `SearchReady`) + `scanAvail`.  The caveat
recorded there is that `CloseoutPreload37.ReadyFieldP2` only offers
`ready : mode = scan → SearchReady` and `readyS : mode = shift → SearchReady`,
so `readyField2_tick` cannot supply the *unconditional* `Extra5.ready`, and the
`ready` half stays a named premise of `het` in `pal_in_peg_final22`.

**§0 audit.**  Every reader of `Extra5`/`Extra6` on the `final22` path was
checked: `lticksN_of_lpackM2_pt6` (Run43:154) reads `extra.scanAvail`
(`scanCanR`, the `canR_of_partsM` case split inlined) and `extra.rewindMargin`
(`rewindLeft`) only; `extra3_scanAvail_tick` (Run22:177), which is what
`H_extraTick5P`'s `scanAvail` half is discharged by, reads `extra.scanAvail`
only; `packRunR_MG26` (Run43:257) and `cycleOracleIMG2_of_cycleOracleMC3R`
consume the pack through `IPackMG2`.  **`ready` is read at no mode at all on
this path**, so relativising it to `mode = scan ∨ mode = shift` is safe and
every reader's proof script is unchanged.

* §1 `Extra5S` / `Extra6S` (the relativised `ready`), `extra6S_of_extra5S`.
* §2 the run pack over the relativised extras: `BigPack2MG6S` /
  `BigPack2MG6S''`, `lticksN_of_lpackM2_pt6S` (verbatim body),
  `ipackMG2_tick_pt6S`, `bigPack2MG6S''_tick`, `packRunR_MG26S`,
  `extra5S_steps`.
* §3 `extraTick5S_of_readyField2`: the `ready` half of the tick obligation from
  `CloseoutPreload37.readyField2_tick`, with `scanAvail` left as Run22's
  residue.  Note the **remaining gap**: `readyField2_tick` demands
  `CloseoutPackRun18.BigPack2M''`, whose `extra : Extra3` still carries the DP
  fields `failed`/`cand` that Run43 deleted, so this bridge is stated over
  `BigPack2M''` and is not yet feedable from `BigPack2MG6S''`.
* §4 `pal_in_peg_final23` — `pal_in_peg_final22` with `hee`/`het` in the
  `Extra5S` shape.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPackRun45

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open PalPeg.GalilThrottledRun PalPeg.GalilTrailProof PalPeg.GalilFinalAssembly
open PalPeg.GalilRunSkeleton PalPeg.GalilCheckpoints PalPeg.GalilTraceCost
open PalPeg.GalilOracleDischarge PalPeg.GalilOracleLocal
open PalPeg.GalilInvPlus PalPeg.GalilInvPlus2 PalPeg.GalilOracleMC PalPeg.GalilOracleMC2
open PalPeg.GalilFinalAssembly2 PalPeg.GalilFinalAssembly4
open PalPeg.CloseoutOracleI PalPeg.CloseoutOracleI2 PalPeg.GalilInvPlus3
open PalPeg.CloseoutPackRun PalPeg.CloseoutPackRun2 PalPeg.CloseoutPackRun3
open PalPeg.CloseoutPackRun5 PalPeg.CloseoutPackRun7 PalPeg.CloseoutPackRun8
open PalPeg.CloseoutPackRun9 PalPeg.CloseoutPackRun10 PalPeg.CloseoutPackRun11
open PalPeg.CloseoutPackRun12 PalPeg.CloseoutPackRun16 PalPeg.CloseoutPackRun18
open PalPeg.CloseoutPackRun19 PalPeg.CloseoutPackRun20 PalPeg.CloseoutPackRun21
open PalPeg.CloseoutPackRun23 PalPeg.CloseoutPackRun24 PalPeg.CloseoutPackRun26
open PalPeg.CloseoutPackRun29 PalPeg.CloseoutPackRun30 PalPeg.CloseoutPackRun33
open PalPeg.CloseoutPackRun35 PalPeg.CloseoutPackRun36 PalPeg.CloseoutPackRun43
open PalPeg.CloseoutPreload37 PalPeg.CloseoutPackRun22
open PalPeg.CloseoutLPack PalPeg.CloseoutLPack2 PalPeg.CloseoutLPack3
open PalPeg.CloseoutLPack4 PalPeg.CloseoutLPack5 PalPeg.CloseoutLPack6
open GalilScaffoldInputHead GalilScaffoldCounter GalilScaffoldChainVerifier

/-! ## 1. `Extra5S` and `Extra6S` -/

/-- **(NAMED) `CloseoutPackRun43.Extra5` with `ready` relativised.**  The
`SearchReady` datum is asked only at the two modes at which
`CloseoutPreload37.ReadyFieldP2` offers it (`ready` at `scan`, `readyS` at
`shift`). -/
structure Extra5S (x : State GalilVM) : Prop where
  ready : x.ctl.mode = Mode.scan ∨ x.ctl.mode = Mode.shift →
    PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get x.vm)
  scanAvail : x.ctl.mode = Mode.scan → x.ctl.replaying = false →
    GalilScaffoldChainVerifier.canRight x.vm.right

/-- **(NAMED) `CloseoutPackRun43.Extra6` with `ready` relativised.** -/
structure Extra6S (x : State GalilVM) : Prop where
  ready : x.ctl.mode = Mode.scan ∨ x.ctl.mode = Mode.shift →
    PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get x.vm)
  rewindMargin : x.ctl.mode = Mode.rewind → 2 ≤ position x.vm.left
  scanAvail : x.ctl.mode = Mode.scan → x.ctl.replaying = false →
    GalilScaffoldChainVerifier.canRight x.vm.right

theorem extra5S_of_extra5 {x : State GalilVM} (h : Extra5 x) : Extra5S x :=
  ⟨fun _ => h.ready, h.scanAvail⟩

theorem extra6S_of_extra6 {x : State GalilVM} (h : Extra6 x) : Extra6S x :=
  ⟨fun _ => h.ready, h.rewindMargin, h.scanAvail⟩

/-- **`extra6_of_extra5` over the relativised extras.** -/
theorem extra6S_of_extra5S {x : State GalilVM} (h : Extra5S x)
    (hrm : x.ctl.mode = Mode.rewind → 2 ≤ position x.vm.left) : Extra6S x :=
  ⟨h.ready, hrm, h.scanAvail⟩

#print axioms extra5S_of_extra5
#print axioms extra6S_of_extra6
#print axioms extra6S_of_extra5S

/-- **(NAMED) `Extra5S` at an `InvLPC` origin.** -/
def H_extraEntry5S (w : List (Fin 2)) : Prop :=
  ∀ (c : Control) (r : GalilVM), InvLPC w c r → Extra5S ⟨c, r⟩

/-! ## 2. The run pack over `Extra5S`/`Extra6S` -/

section PackG6S
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- `CloseoutPackRun43.BigPack2MG6` over `Extra6S`. -/
structure BigPack2MG6S (w : List (Fin 2)) (x : State GalilVM) : Prop where
  ipackM : IPackMG2 centre place entry q first w x
  aux : AuxPack x.ctl x.vm
  live : CentreLive x.ctl x.vm
  extra : Extra6S x

/-- `CloseoutPackRun43.BigPack2MG6''` over `Extra5S`. -/
structure BigPack2MG6S'' (w : List (Fin 2)) (x : State GalilVM) : Prop where
  ipackM : IPackMG2 centre place entry q first w x
  aux : AuxPack x.ctl x.vm
  live : CentreLive x.ctl x.vm
  marks : MarksInv' first x.ctl x.vm
  extra : Extra5S x

theorem bigPack2MG6S_of_bigPack2MG6S'' {w : List (Fin 2)} {x : State GalilVM}
    (hx : BigPack2MG6S'' centre place entry q first w x)
    (hnf : x.ctl.mode = Mode.rewind →
      ¬ (galilFrameS (PofC centre place entry w) q first).atFirst x.vm) :
    BigPack2MG6S centre place entry q first w x :=
  ⟨hx.ipackM, hx.aux, hx.live,
    extra6S_of_extra5S hx.extra (fun hm => two_le_left_of_marksInv' hx.marks hm (hnf hm))⟩

/-- **(NAMED) the pack-relative tick obligation over `Extra5S`.** -/
def H_extraTick5SP (w : List (Fin 2)) : Prop :=
  ∀ x y : State GalilVM, BigPack2MG6S'' centre place entry q first w x →
    Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y → Extra5S y

/-- **`CloseoutPackRun43.lticksN_of_lpackM2_pt6` over `BigPack2MG6S`.**  The
body is verbatim: no leaf reads `ready`. -/
theorem lticksN_of_lpackM2_pt6S {w : List (Fin 2)} {x : State GalilVM}
    (hx : BigPack2MG6S centre place entry q first w x) (hP : LPackM2 w x.ctl x.vm) :
    LTickLeavesN centre place entry q first w x.ctl x.vm where
  initPackN := fun hm _ _ => absurd hm hx.aux.front.notInit
  scanInvR := fun hm => by
    cases hrep : x.ctl.replaying with
    | false => exact hx.ipackM.base.pack.scanGeom hm hrep
    | true => exact hP.scanGeomR hm hrep
  scanCanR := fun hm => by
    cases hrep : x.ctl.replaying with
    | true => exact PalPeg.GalilTrailRad.replayCan_of_pack hx.aux.front hrep
    | false => exact hx.extra.scanAvail hm hrep
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

/-- `CloseoutPackRun43.ipackMG2_tick_pt6` over `BigPack2MG6S`. -/
theorem ipackMG2_tick_pt6S {w : List (Fin 2)}
    (hws : ∀ y : State GalilVM, WatchShiftG centre place entry q first w y)
    {x y : State GalilVM} (hx : BigPack2MG6S centre place entry q first w x)
    (hSP : ScanNR x → ShiftPal centre place entry q first w x.vm)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y)
    (hg : SoundScanNR w y) : IPackMG2 centre place entry q first w y := by
  have hL := lticksN_of_lpackM2_pt6S centre place entry q first hx hx.ipackM.m2
  have hsh : ShiftLocalG centre place entry q first w y := by
    by_cases hi : y.vm.chain = ChainVM.idle
    · exact shiftLocalG_of_chainIdle centre place entry q first hi
    · exact shiftLocalG_of_watchShiftG centre place entry q first hi (hws y)
  refine ⟨⟨?_, hsh⟩,
    lpackM2_tick' centre place entry q first hx.ipackM.m2 hL hx.aux
      (lTickLeaves2_of_shiftPalG centre place entry q first hx.ipackM.m2 hL hSP) h⟩
  obtain ⟨c, s⟩ := x
  obtain ⟨c', t⟩ := y
  exact lpackN_tick centre place entry q first hx.ipackM.base.pack hL h

/-- `CloseoutPackRun43.bigPack2MG6''_tick` over the relativised extras. -/
theorem bigPack2MG6S''_tick {w : List (Fin 2)}
    (hws : ∀ y : State GalilVM, WatchShiftG centre place entry q first w y)
    (het : H_extraTick5SP centre place entry q first w)
    (hme : H_marksEntry' (PofC centre place entry w) q first)
    {x y : State GalilVM} (hx : BigPack2MG6S'' centre place entry q first w x)
    (hSP : ScanNR x → ShiftPal centre place entry q first w x.vm)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y)
    (hg : SoundScanNR w y) (hlv : CentreLive y.ctl y.vm) :
    BigPack2MG6S'' centre place entry q first w y := by
  have haux : AuxPack y.ctl y.vm := auxPack_tick centre place entry q first hx.aux hx.live h
  have hmarks : MarksInv' first y.ctl y.vm := by
    obtain ⟨c, s⟩ := x
    obtain ⟨c', t⟩ := y
    exact marksInv'_tick _ q first 2048 hx.marks (fun hm ho hs => hme c s hm ho hs) h
  refine ⟨?_, haux, hlv, hmarks, het x y hx h⟩
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
    exact ipackMG2_tick_pt6S centre place entry q first hws
      (bigPack2MG6S_of_bigPack2MG6S'' centre place entry q first hx hnf) hSP h hg

end PackG6S

#print axioms lticksN_of_lpackM2_pt6S
#print axioms ipackMG2_tick_pt6S
#print axioms bigPack2MG6S''_tick

section RunG6S
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- `CloseoutPackRun43.packRunR_MG26` over the relativised extras. -/
theorem packRunR_MG26S {w : List (Fin 2)}
    (hws : ∀ y : State GalilVM, WatchShiftG centre place entry q first w y)
    (hSP : ∀ x : State GalilVM, BigPack2MG6S centre place entry q first w x →
      ScanNR x → ShiftPal centre place entry q first w x.vm)
    (het : H_extraTick5SP centre place entry q first w)
    (hme : H_marksEntry' (PofC centre place entry w) q first)
    (hprefix : ∀ (c : Control) (r : GalilVM), InvLPC w c r → ∀ (j : ℕ) (x : State GalilVM),
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 j ⟨c, r⟩ x →
      Extra5S x) :
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
  have hexx : Extra5S x := hprefix c r hIC j x hjx
  have hmx : MarksInv' first x.ctl x.vm :=
    marksInv'_of_run (PofC centre place entry w) q first 2048 hme (x := ⟨c, r⟩) hjx
      (m := Mode.scan) (by decide) (invS_mode hIC.1.1.1.1).1
  have hbx : BigPack2MG6S'' centre place entry q first w x :=
    ⟨hx, hauxx, hlv0 j x hjx, hmx, hexx⟩
  obtain ⟨g, hg0, hgk, htr⟩ := stepsAll_fn h
  have hreach : ∀ i, i ≤ k →
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 (j + i) ⟨c, r⟩ (g i) := by
    intro i hi
    have := steps_of_trace htr i hi
    rw [hg0] at this
    exact steps_trans hjx this
  have hbig : ∀ i, i ≤ k → BigPack2MG6S'' centre place entry q first w (g i) := by
    intro i
    induction i with
    | zero => intro _; rw [hg0]; exact hbx
    | succ n ih =>
      intro hi
      have hn := ih (by omega)
      exact bigPack2MG6S''_tick centre place entry q first hws het hme hn
        (fun hs => hSP (g n) (bigPack2MG6S_of_bigPack2MG6S'' centre place entry q first hn
          (fun hm => absurd (hs.1.symm.trans hm) (by decide))) hs)
        (htr.tick n (by omega)) (htr.good (n+1) hi)
        (hlv0 (j + (n+1)) (g (n+1)) (hreach (n+1) hi))
  exact ⟨g, hg0, hgk, htr, fun i hi => (hbig i hi).ipackM⟩

/-- `CloseoutPackRun43.extra5_steps` over `Extra5S`. -/
theorem extra5S_steps {w : List (Fin 2)}
    (het : ∀ x y : State GalilVM, Extra5S x →
      Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y → Extra5S y)
    {n : ℕ} {x y : State GalilVM} (he : Extra5S x)
    (h : Steps (galilFrameS (PofC centre place entry w) q first) 2048 n x y) : Extra5S y := by
  induction h with
  | zero z => exact he
  | @succ m a b z h hr ih => exact ih (het a b he h)

end RunG6S

#print axioms packRunR_MG26S
#print axioms extra5S_steps

/-! ## 3. The `ready` half from `CloseoutPreload37.readyField2_tick` -/

section Wire
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **`Extra5S` along one tick, `ready` from `ReadyFieldP2`.**  The `ready`
half is `CloseoutPreload37.readyField2_tick` (:96) — its `ready`/`readyS`
clauses are exactly the two modes `Extra5S.ready` asks about — and the
`scanAvail` half is `CloseoutPackRun22.extra3_scanAvail_tick` (:177) with its
residue `hres`.  The `ReadyFieldP2` datum is returned as well, so the field can
be carried along a run.

Residues, all inherited unchanged: `hentry`/`hentry'` (the `restart` /
`replayStart` landings, discharged by
`CloseoutPreload37.readyField2_entry_of_datum` :193 from the stage-entry data
`Restarted`/`StageEntry`/`CentreLongRun`/`NoReturn`/`EntryDepthG`), `hshift`
(the `scan_shift` tick, still open), and `hres` (Run22's `scanAvail` residue on
`scan_match` at clock `1`, `shift_done` and `replayStart`). -/
theorem extraTick5S_of_readyField2 {w : List (Fin 2)} {n n' : ℕ} {x y : State GalilVM}
    (hx : BigPack2M'' centre place entry q first w x)
    (hf : ReadyFieldP2 n x) (hn : n ≤ n')
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y)
    (hentry : x.ctl.mode = Mode.scan → restartVM entry x.vm y.vm → ReadyFieldP2 n' y)
    (hentry' : x.ctl.mode = Mode.replayStart → ReadyFieldP2 n' y)
    (hshift : x.ctl.mode = Mode.scan → y.ctl.mode = Mode.shift → ReadyFieldP2 n' y)
    (hres : (x.ctl.mode ≠ Mode.scan ∨ x.ctl.clock = 1) →
      y.ctl.mode = Mode.scan → y.ctl.replaying = false → canRight y.vm.right) :
    Extra5S y ∧ ReadyFieldP2 n' y := by
  have hR : ReadyFieldP2 n' y :=
    readyField2_tick centre place entry q first hx hf hn h hentry hentry' hshift
  refine ⟨⟨fun hm => ?_, extra3_scanAvail_tick centre place entry q first hx h hres⟩, hR⟩
  rcases hm with hm | hm
  · exact hR.ready hm
  · exact hR.readyS hm

end Wire

#print axioms extraTick5S_of_readyField2

/-! ## 4. `pal_in_peg_final23` -/

/-- **`CloseoutPackRun43.pal_in_peg_final22` with `Extra5` replaced by
`Extra5S`.**  Identical hypothesis list, except that `hSP` is over
`BigPack2MG6S`, `hee` is `H_extraEntry5S`, and `het` is the `Extra5S` tick: the
`SearchReady` datum is now demanded only at `scan` and `shift`, which is exactly
what `CloseoutPreload37.ReadyFieldP2` serves (`ready`/`readyS`), so `het`'s
`ready` half is discharged by `extraTick5S_of_readyField2` above modulo its
three residues (`hentry`/`hentry'` — the stage-entry data —, `hshift`, and
Run22's `scanAvail` residue).

**無条件 PAL ∈ PEG は未完.** -/
theorem pal_in_peg_final23 (entry q : ℕ) (first : Fin 9)
    (hSP : ∀ (w : List (Fin 2)) (x : State GalilVM),
      BigPack2MG6S centreC placeC entry q first w x →
      ScanNR x → ShiftPal centreC placeC entry q first w x.vm)
    (hws : ∀ w : List (Fin 2), ∀ y : State GalilVM, WatchShiftG centreC placeC entry q first w y)
    (hee : ∀ w : List (Fin 2), H_extraEntry5S w)
    (het : ∀ w : List (Fin 2), ∀ x y : State GalilVM, Extra5S x →
      Tick (galilFrameS (PofC centreC placeC entry w) q first) 2048 x y → Extra5S y)
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
      (packRunR_MG26S centreC placeC entry q first (hws w) (hSP w)
        (fun x y hx ht => het w x y hx.extra ht) (hme w)
        (fun c r hIC _ _ hjx =>
          extra5S_steps centreC placeC entry q first (het w) (hee w c r hIC) hjx))
      (hsl w) (hsc w) (hor w hw))
    hC

#print axioms pal_in_peg_final23

end PalPeg.CloseoutPackRun45
