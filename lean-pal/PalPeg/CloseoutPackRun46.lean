import PalPeg.CloseoutPackRun45

/-!
# `CloseoutPackRun46`: `ready` deleted from the pack extras

`CloseoutPackRun45`'s §0 audit showed that on the `final22`/`final23` path the
`ready` field of `Extra5`/`Extra5S` is read at **no mode at all**:
`lticksN_of_lpackM2_pt6` (Run43:154) reads only `extra.scanAvail` and
`extra.rewindMargin`, `extra3_scanAvail_tick` (Run22:177) reads `scanAvail`,
and every other consumer goes through `IPackMG2`.  So `ready` is dead weight,
exactly like `failed`/`cand` were in Run43.

* §1 `Extra7` (= `scanAvail` only) and `Extra8` (= `scanAvail` +
  `rewindMargin`), with `extra8_of_extra7`.
* §2 the run pack over them: `BigPack2MG7`/`BigPack2MG7''`,
  `lticksN_of_lpackM2_pt7`, `ipackMG2_tick_pt7`, `bigPack2MG7''_tick`,
  `packRunR_MG27`, `extra7_steps` (bodies verbatim from Run45 §2, with the
  `ready` clauses simply absent).
* §3 `H_extraEntry7` / `H_extraTick7P` discharged down to **two** residues:
  the entry one is `CloseoutPackRun22.extraEntry3_scanAvail`'s end-of-input
  fact `position r.right ≠ 2 * w.length`, and the tick one is Run22's
  `extra3_scanAvail_tick` residue (fires only on `scan_match` at clock `1`,
  `shift_done` and `replayStart`).  The whole `ReadyFieldP2`/`ReadyPacedS`
  readiness wiring disappears from the pack path.
* §4 `pal_in_peg_final24` — `pal_in_peg_final23` with `hee`/`het` in the
  `Extra7` shape.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPackRun46

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
open PalPeg.CloseoutPreload37 PalPeg.CloseoutPackRun22 PalPeg.CloseoutPackRun45
open PalPeg.CloseoutLPack PalPeg.CloseoutLPack2 PalPeg.CloseoutLPack3
open PalPeg.CloseoutLPack4 PalPeg.CloseoutLPack5 PalPeg.CloseoutLPack6
open GalilScaffoldInputHead GalilScaffoldCounter GalilScaffoldChainVerifier

/-! ## 1. `Extra7` and `Extra8` -/

/-- **(NAMED) `CloseoutPackRun45.Extra5S` minus the dead `ready` field.** -/
structure Extra7 (x : State GalilVM) : Prop where
  scanAvail : x.ctl.mode = Mode.scan → x.ctl.replaying = false →
    GalilScaffoldChainVerifier.canRight x.vm.right

/-- **(NAMED) `CloseoutPackRun45.Extra6S` minus the dead `ready` field.** -/
structure Extra8 (x : State GalilVM) : Prop where
  rewindMargin : x.ctl.mode = Mode.rewind → 2 ≤ position x.vm.left
  scanAvail : x.ctl.mode = Mode.scan → x.ctl.replaying = false →
    GalilScaffoldChainVerifier.canRight x.vm.right

theorem extra7_of_extra5S {x : State GalilVM} (h : Extra5S x) : Extra7 x := ⟨h.scanAvail⟩

theorem extra8_of_extra6S {x : State GalilVM} (h : Extra6S x) : Extra8 x :=
  ⟨h.rewindMargin, h.scanAvail⟩

/-- **`extra6S_of_extra5S` over the slim extras.** -/
theorem extra8_of_extra7 {x : State GalilVM} (h : Extra7 x)
    (hrm : x.ctl.mode = Mode.rewind → 2 ≤ position x.vm.left) : Extra8 x :=
  ⟨hrm, h.scanAvail⟩

#print axioms extra7_of_extra5S
#print axioms extra8_of_extra6S
#print axioms extra8_of_extra7

/-- **(NAMED) `Extra7` at an `InvLPC` origin.** -/
def H_extraEntry7 (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry : ℕ) (w : List (Fin 2)) : Prop :=
  ∀ (c : Control) (r : GalilVM), InvLPC w c r → Extra7 ⟨c, r⟩

/-! ## 2. The run pack over `Extra7`/`Extra8` -/

section PackG7
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- `CloseoutPackRun45.BigPack2MG6S` over `Extra8`. -/
structure BigPack2MG7 (w : List (Fin 2)) (x : State GalilVM) : Prop where
  ipackM : IPackMG2 centre place entry q first w x
  aux : AuxPack x.ctl x.vm
  live : CentreLive x.ctl x.vm
  extra : Extra8 x

/-- `CloseoutPackRun45.BigPack2MG6S''` over `Extra7`. -/
structure BigPack2MG7'' (w : List (Fin 2)) (x : State GalilVM) : Prop where
  ipackM : IPackMG2 centre place entry q first w x
  aux : AuxPack x.ctl x.vm
  live : CentreLive x.ctl x.vm
  marks : MarksInv' first x.ctl x.vm
  extra : Extra7 x

theorem bigPack2MG7_of_bigPack2MG7'' {w : List (Fin 2)} {x : State GalilVM}
    (hx : BigPack2MG7'' centre place entry q first w x)
    (hnf : x.ctl.mode = Mode.rewind →
      ¬ (galilFrameS (PofC centre place entry w) q first).atFirst x.vm) :
    BigPack2MG7 centre place entry q first w x :=
  ⟨hx.ipackM, hx.aux, hx.live,
    extra8_of_extra7 hx.extra (fun hm => two_le_left_of_marksInv' hx.marks hm (hnf hm))⟩

/-- **(NAMED) the pack-relative tick obligation over `Extra7`.** -/
def H_extraTick7P (w : List (Fin 2)) : Prop :=
  ∀ x y : State GalilVM, BigPack2MG7'' centre place entry q first w x →
    Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y → Extra7 y

/-- **`CloseoutPackRun45.lticksN_of_lpackM2_pt6S` over `BigPack2MG7`.**  The
body is verbatim: no leaf reads `ready`. -/
theorem lticksN_of_lpackM2_pt7 {w : List (Fin 2)} {x : State GalilVM}
    (hx : BigPack2MG7 centre place entry q first w x) (hP : LPackM2 w x.ctl x.vm) :
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
  rewindLeft := fun hm _ => left_pos_of_two (hx.extra.rewindMargin hm)
  replayPackN := fun hm _ _ h =>
    lpackM_replayStart_of_centreRep centre place entry q first (hP.centreRep (Or.inr hm)) h

/-- `CloseoutPackRun45.ipackMG2_tick_pt6S` over `BigPack2MG7`. -/
theorem ipackMG2_tick_pt7 {w : List (Fin 2)}
    (hws : ∀ y : State GalilVM, WatchShiftG centre place entry q first w y)
    {x y : State GalilVM} (hx : BigPack2MG7 centre place entry q first w x)
    (hSP : ScanNR x → ShiftPal centre place entry q first w x.vm)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y)
    (hg : SoundScanNR w y) : IPackMG2 centre place entry q first w y := by
  have hL := lticksN_of_lpackM2_pt7 centre place entry q first hx hx.ipackM.m2
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

/-- `CloseoutPackRun45.bigPack2MG6S''_tick` over the slim extras. -/
theorem bigPack2MG7''_tick {w : List (Fin 2)}
    (hws : ∀ y : State GalilVM, WatchShiftG centre place entry q first w y)
    (het : H_extraTick7P centre place entry q first w)
    (hme : H_marksEntry' (PofC centre place entry w) q first)
    {x y : State GalilVM} (hx : BigPack2MG7'' centre place entry q first w x)
    (hSP : ScanNR x → ShiftPal centre place entry q first w x.vm)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y)
    (hg : SoundScanNR w y) (hlv : CentreLive y.ctl y.vm) :
    BigPack2MG7'' centre place entry q first w y := by
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
    exact ipackMG2_tick_pt7 centre place entry q first hws
      (bigPack2MG7_of_bigPack2MG7'' centre place entry q first hx hnf) hSP h hg

end PackG7

#print axioms lticksN_of_lpackM2_pt7
#print axioms ipackMG2_tick_pt7
#print axioms bigPack2MG7''_tick

section RunG7
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- `CloseoutPackRun45.packRunR_MG26S` over the slim extras. -/
theorem packRunR_MG27 {w : List (Fin 2)}
    (hws : ∀ y : State GalilVM, WatchShiftG centre place entry q first w y)
    (hSP : ∀ x : State GalilVM, BigPack2MG7 centre place entry q first w x →
      ScanNR x → ShiftPal centre place entry q first w x.vm)
    (het : H_extraTick7P centre place entry q first w)
    (hme : H_marksEntry' (PofC centre place entry w) q first)
    (hprefix : ∀ (c : Control) (r : GalilVM), InvLPC w c r → ∀ (j : ℕ) (x : State GalilVM),
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 j ⟨c, r⟩ x →
      Extra7 x) :
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
  have hexx : Extra7 x := hprefix c r hIC j x hjx
  have hmx : MarksInv' first x.ctl x.vm :=
    marksInv'_of_run (PofC centre place entry w) q first 2048 hme (x := ⟨c, r⟩) hjx
      (m := Mode.scan) (by decide) (invS_mode hIC.1.1.1.1).1
  have hbx : BigPack2MG7'' centre place entry q first w x :=
    ⟨hx, hauxx, hlv0 j x hjx, hmx, hexx⟩
  obtain ⟨g, hg0, hgk, htr⟩ := stepsAll_fn h
  have hreach : ∀ i, i ≤ k →
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 (j + i) ⟨c, r⟩ (g i) := by
    intro i hi
    have := steps_of_trace htr i hi
    rw [hg0] at this
    exact steps_trans hjx this
  have hbig : ∀ i, i ≤ k → BigPack2MG7'' centre place entry q first w (g i) := by
    intro i
    induction i with
    | zero => intro _; rw [hg0]; exact hbx
    | succ n ih =>
      intro hi
      have hn := ih (by omega)
      exact bigPack2MG7''_tick centre place entry q first hws het hme hn
        (fun hs => hSP (g n) (bigPack2MG7_of_bigPack2MG7'' centre place entry q first hn
          (fun hm => absurd (hs.1.symm.trans hm) (by decide))) hs)
        (htr.tick n (by omega)) (htr.good (n+1) hi)
        (hlv0 (j + (n+1)) (g (n+1)) (hreach (n+1) hi))
  exact ⟨g, hg0, hgk, htr, fun i hi => (hbig i hi).ipackM⟩

/-- `CloseoutPackRun45.extra5S_steps` over `Extra7`. -/
theorem extra7_steps {w : List (Fin 2)}
    (het : ∀ x y : State GalilVM, Extra7 x →
      Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y → Extra7 y)
    {n : ℕ} {x y : State GalilVM} (he : Extra7 x)
    (h : Steps (galilFrameS (PofC centre place entry w) q first) 2048 n x y) : Extra7 y := by
  induction h with
  | zero z => exact he
  | @succ m a b z h hr ih => exact ih (het a b he h)

end RunG7

#print axioms packRunR_MG27
#print axioms extra7_steps

/-! ## 3. The two residues -/

section Wire
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **`H_extraEntry7` from a single residue.**  With `ready` gone, the entry
obligation is exactly `CloseoutPackRun22.extraEntry3_scanAvail` (:126), whose
only open input is the end-of-input fact on the right head. -/
theorem extraEntry7_of_end {w : List (Fin 2)}
    (hend : ∀ (c : Control) (r : GalilVM), InvLPC w c r → position r.right ≠ 2 * w.length) :
    H_extraEntry7 centre place entry w :=
  fun c r hIC => ⟨fun _ _ => extraEntry3_scanAvail hIC (hend c r hIC)⟩

/-- **`Extra7` along one tick from a single residue.**  With `ready` gone, the
tick obligation is exactly `CloseoutPackRun22.extra3_scanAvail_tick` (:177),
whose residue `hres` fires only on `scan_match` at clock `1`, `shift_done` and
`replayStart`.  No `ReadyFieldP2` / `ReadyPacedS` datum is involved. -/
theorem extraTick7_of_scanAvail {w : List (Fin 2)} {x y : State GalilVM}
    (hx : BigPack2M'' centre place entry q first w x)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y)
    (hres : (x.ctl.mode ≠ Mode.scan ∨ x.ctl.clock = 1) →
      y.ctl.mode = Mode.scan → y.ctl.replaying = false → canRight y.vm.right) :
    Extra7 y :=
  ⟨extra3_scanAvail_tick centre place entry q first hx h hres⟩

end Wire

#print axioms extraEntry7_of_end
#print axioms extraTick7_of_scanAvail

/-! ## 4. `pal_in_peg_final24` -/

/-- **`CloseoutPackRun45.pal_in_peg_final23` with `Extra5S` replaced by
`Extra7`.**  Identical hypothesis list, except that `hSP` is over
`BigPack2MG7`, `hee` is `H_extraEntry7` and `het` is the `Extra7` tick.  The
readiness wiring (`ReadyFieldP`/`ReadyPacedS`/`ReadyFieldP2`) has left the pack
path entirely: `hee` is discharged by `extraEntry7_of_end` and `het` by
`extraTick7_of_scanAvail`, each modulo one residue.

**無条件 PAL ∈ PEG は未完.** -/
theorem pal_in_peg_final24 (entry q : ℕ) (first : Fin 9)
    (hSP : ∀ (w : List (Fin 2)) (x : State GalilVM),
      BigPack2MG7 centreC placeC entry q first w x →
      ScanNR x → ShiftPal centreC placeC entry q first w x.vm)
    (hws : ∀ w : List (Fin 2), ∀ y : State GalilVM, WatchShiftG centreC placeC entry q first w y)
    (hee : ∀ w : List (Fin 2), H_extraEntry7 centreC placeC entry w)
    (het : ∀ w : List (Fin 2), ∀ x y : State GalilVM, Extra7 x →
      Tick (galilFrameS (PofC centreC placeC entry w) q first) 2048 x y → Extra7 y)
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
      (packRunR_MG27 centreC placeC entry q first (hws w) (hSP w)
        (fun x y hx ht => het w x y hx.extra ht) (hme w)
        (fun c r hIC _ _ hjx =>
          extra7_steps centreC placeC entry q first (het w) (hee w c r hIC) hjx))
      (hsl w) (hsc w) (hor w hw))
    hC

#print axioms pal_in_peg_final24

end PalPeg.CloseoutPackRun46
