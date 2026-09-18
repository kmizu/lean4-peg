import PalPeg.CloseoutPackRun42
import PalPeg.CloseoutPackRun36

/-!
# `CloseoutPackRun43`: `Extra3.failed` and `Extra3.cand` deleted

`CloseoutPackRun42` §2 audited `Extra3` and found two of its four fields dead on
the `pal_in_peg_final20` path: `Extra3` is consumed only through
`extra'_of_extra3` into `CloseoutPackRun11.Extra'`, and every reader of `Extra'`
(`canR_of_partsM`, `lticksN_of_big6`/`_big6G`/`_lpackM2_pt`,
`extra3_scanAvail_tick`) touches only `scanAvail` and `rewindMargin`.  The DP
consumers reach `StageFailed` by their own route (`MismatchDp`,
`GalilLeafDp.dpPack_of_stageFailed` → `GalilOracleMC3.hdp`), never via
`Extra3.failed`.

This file deletes both fields:

* §1 `Extra5` (= `Extra3` minus `failed`/`cand`: `ready` + `scanAvail`) and
  `Extra6` (= `Extra'` minus the same two: `ready` + `rewindMargin` +
  `scanAvail`), with `extra6_of_extra5` in place of `extra'_of_extra3`.
* §2 `BigPack2MG6` / `BigPack2MG6''` (Run36's `BigPack2MG2` / `BigPack2MG2''`
  over the slim extras), `lticksN_of_lpackM2_pt6` (the same seven leaves — the
  proofs do not change, since none read `failed`/`cand`), the tick, and
  `packRunR_MG26`.
* §3 `pal_in_peg_final22` — `pal_in_peg_final20` with `hee`/`het` in the
  `Extra5` forms.  The hypothesis list is `final20`'s, with the entry and tick
  obligations now free of every DP fact.

Note `Extra''` is taken (`CloseoutPackRun14`), hence `Extra6`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPackRun43

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
open PalPeg.CloseoutPackRun36
open GalilScaffoldInputHead GalilScaffoldCounter GalilScaffoldChainVerifier

/-! ## 1. `Extra5` and `Extra6` -/

/-- **(NAMED) `CloseoutPackRun18.Extra3` minus `failed` and `cand`.**  Two
fields.  Neither deleted field depends on `centre`/`place`/`entry`/`w` any more,
so the slim extras are parameterised by the state alone. -/
structure Extra5 (x : State GalilVM) : Prop where
  ready : PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get x.vm)
  scanAvail : x.ctl.mode = Mode.scan → x.ctl.replaying = false →
    GalilScaffoldChainVerifier.canRight x.vm.right

/-- **(NAMED) `CloseoutPackRun11.Extra'` minus `failed` and `cand`.**  Three
fields. -/
structure Extra6 (x : State GalilVM) : Prop where
  ready : PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get x.vm)
  rewindMargin : x.ctl.mode = Mode.rewind → 2 ≤ position x.vm.left
  scanAvail : x.ctl.mode = Mode.scan → x.ctl.replaying = false →
    GalilScaffoldChainVerifier.canRight x.vm.right

section Fwd
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry : ℕ)

theorem extra5_of_extra3 {w : List (Fin 2)} {x : State GalilVM}
    (h : Extra3 centre place entry w x) : Extra5 x := ⟨h.ready, h.scanAvail⟩

theorem extra6_of_extra' {w : List (Fin 2)} {x : State GalilVM}
    (h : Extra' centre place entry w x) : Extra6 x :=
  ⟨h.ready, h.rewindMargin, h.scanAvail⟩

end Fwd

/-- **`extra'_of_extra3` over the slim extras.**  The margin is still the one
thing `Extra5` does not carry. -/
theorem extra6_of_extra5 {x : State GalilVM} (h : Extra5 x)
    (hrm : x.ctl.mode = Mode.rewind → 2 ≤ position x.vm.left) : Extra6 x :=
  ⟨h.ready, hrm, h.scanAvail⟩

#print axioms extra5_of_extra3
#print axioms extra6_of_extra'
#print axioms extra6_of_extra5

/-! ## 2. The run pack over `Extra5`/`Extra6` -/

/-- **(NAMED) `Extra5` at an `InvLPC` origin.**  `H_extraEntry3` minus the two
dead fields. -/
def H_extraEntry5 (w : List (Fin 2)) : Prop :=
  ∀ (c : Control) (r : GalilVM), InvLPC w c r → Extra5 ⟨c, r⟩


section PackG6
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- `CloseoutPackRun36.BigPack2MG2` over `Extra6`. -/
structure BigPack2MG6 (w : List (Fin 2)) (x : State GalilVM) : Prop where
  ipackM : IPackMG2 centre place entry q first w x
  aux : AuxPack x.ctl x.vm
  live : CentreLive x.ctl x.vm
  extra : Extra6 x

/-- `CloseoutPackRun36.BigPack2MG2''` over `Extra5`. -/
structure BigPack2MG6'' (w : List (Fin 2)) (x : State GalilVM) : Prop where
  ipackM : IPackMG2 centre place entry q first w x
  aux : AuxPack x.ctl x.vm
  live : CentreLive x.ctl x.vm
  marks : MarksInv' first x.ctl x.vm
  extra : Extra5 x

theorem bigPack2MG6_of_bigPack2MG6'' {w : List (Fin 2)} {x : State GalilVM}
    (hx : BigPack2MG6'' centre place entry q first w x)
    (hnf : x.ctl.mode = Mode.rewind →
      ¬ (galilFrameS (PofC centre place entry w) q first).atFirst x.vm) :
    BigPack2MG6 centre place entry q first w x :=
  ⟨hx.ipackM, hx.aux, hx.live,
    extra6_of_extra5 hx.extra (fun hm => two_le_left_of_marksInv' hx.marks hm (hnf hm))⟩

/-- **(NAMED) the pack-relative tick obligation over `Extra5`.**
`CloseoutPackRun22.H_extraTick3P` with the source pack `BigPack2MG6''`. -/
def H_extraTick5P (w : List (Fin 2)) : Prop :=
  ∀ x y : State GalilVM, BigPack2MG6'' centre place entry q first w x →
    Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y → Extra5 y

/-- **`CloseoutPackRun36.lticksN_of_lpackM2_pt` over `BigPack2MG6`.**  Verbatim:
`initPackN` is `FrontPack.notInit` (`rInitPackMG_of_pack`'s whole content),
`scanCanR` is `canR_of_partsM`'s two-line case split, and `rewindLeft` reads
`Extra6.rewindMargin`.  Nothing reads `failed` or `cand`. -/
theorem lticksN_of_lpackM2_pt6 {w : List (Fin 2)} {x : State GalilVM}
    (hx : BigPack2MG6 centre place entry q first w x) (hP : LPackM2 w x.ctl x.vm) :
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

/-- `CloseoutPackRun36.ipackMG2_tick_pt` over `BigPack2MG6`.  The shift half is
`rShiftNextMG_of_watchShiftG`'s script inlined (it never consumes the pack). -/
theorem ipackMG2_tick_pt6 {w : List (Fin 2)}
    (hws : ∀ y : State GalilVM, WatchShiftG centre place entry q first w y)
    {x y : State GalilVM} (hx : BigPack2MG6 centre place entry q first w x)
    (hSP : ScanNR x → ShiftPal centre place entry q first w x.vm)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y)
    (hg : SoundScanNR w y) : IPackMG2 centre place entry q first w y := by
  have hL := lticksN_of_lpackM2_pt6 centre place entry q first hx hx.ipackM.m2
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

/-- `CloseoutPackRun36.bigPack2MG2''_tick` over the slim extras. -/
theorem bigPack2MG6''_tick {w : List (Fin 2)}
    (hws : ∀ y : State GalilVM, WatchShiftG centre place entry q first w y)
    (het : H_extraTick5P centre place entry q first w)
    (hme : H_marksEntry' (PofC centre place entry w) q first)
    {x y : State GalilVM} (hx : BigPack2MG6'' centre place entry q first w x)
    (hSP : ScanNR x → ShiftPal centre place entry q first w x.vm)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y)
    (hg : SoundScanNR w y) (hlv : CentreLive y.ctl y.vm) :
    BigPack2MG6'' centre place entry q first w y := by
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
    exact ipackMG2_tick_pt6 centre place entry q first hws
      (bigPack2MG6_of_bigPack2MG6'' centre place entry q first hx hnf) hSP h hg

end PackG6

#print axioms lticksN_of_lpackM2_pt6
#print axioms ipackMG2_tick_pt6
#print axioms bigPack2MG6''_tick

/-! ## 3. `packRunR_MG26` and `pal_in_peg_final22` -/

section RunG6
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- `CloseoutPackRun36.packRunR_MG2` over `H_extraEntry5` / `H_extraTick5P`.
The `Extra5` transport along the prefix run `⟨c, r⟩ ⟶* x` is no longer a
separate `extra3_steps`: the pack-relative tick obligation is discharged inside
the same induction that carries `BigPack2MG6''`, and the prefix `Steps` are
covered by `marksInv'_of_run` exactly as before. -/
theorem packRunR_MG26 {w : List (Fin 2)}
    (hws : ∀ y : State GalilVM, WatchShiftG centre place entry q first w y)
    (hSP : ∀ x : State GalilVM, BigPack2MG6 centre place entry q first w x →
      ScanNR x → ShiftPal centre place entry q first w x.vm)
    (het : H_extraTick5P centre place entry q first w)
    (hme : H_marksEntry' (PofC centre place entry w) q first)
    (hprefix : ∀ (c : Control) (r : GalilVM), InvLPC w c r → ∀ (j : ℕ) (x : State GalilVM),
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 j ⟨c, r⟩ x →
      Extra5 x) :
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
  have hexx : Extra5 x := hprefix c r hIC j x hjx
  have hmx : MarksInv' first x.ctl x.vm :=
    marksInv'_of_run (PofC centre place entry w) q first 2048 hme (x := ⟨c, r⟩) hjx
      (m := Mode.scan) (by decide) (invS_mode hIC.1.1.1.1).1
  have hbx : BigPack2MG6'' centre place entry q first w x :=
    ⟨hx, hauxx, hlv0 j x hjx, hmx, hexx⟩
  obtain ⟨g, hg0, hgk, htr⟩ := stepsAll_fn h
  have hreach : ∀ i, i ≤ k →
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 (j + i) ⟨c, r⟩ (g i) := by
    intro i hi
    have := steps_of_trace htr i hi
    rw [hg0] at this
    exact steps_trans hjx this
  have hbig : ∀ i, i ≤ k → BigPack2MG6'' centre place entry q first w (g i) := by
    intro i
    induction i with
    | zero => intro _; rw [hg0]; exact hbx
    | succ n ih =>
      intro hi
      have hn := ih (by omega)
      exact bigPack2MG6''_tick centre place entry q first hws het hme hn
        (fun hs => hSP (g n) (bigPack2MG6_of_bigPack2MG6'' centre place entry q first hn
          (fun hm => absurd (hs.1.symm.trans hm) (by decide))) hs)
        (htr.tick n (by omega)) (htr.good (n+1) hi)
        (hlv0 (j + (n+1)) (g (n+1)) (hreach (n+1) hi))
  exact ⟨g, hg0, hgk, htr, fun i hi => (hbig i hi).ipackM⟩

/-- The prefix transport from the bare `Extra5` entry and a bare `Extra5` tick. -/
theorem extra5_steps {w : List (Fin 2)}
    (het : ∀ x y : State GalilVM, Extra5 x →
      Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y → Extra5 y)
    {n : ℕ} {x y : State GalilVM} (he : Extra5 x)
    (h : Steps (galilFrameS (PofC centre place entry w) q first) 2048 n x y) : Extra5 y := by
  induction h with
  | zero z => exact he
  | @succ m a b z h hr ih => exact ih (het a b he h)

end RunG6

#print axioms packRunR_MG26
#print axioms extra5_steps

/-- **`pal_in_peg_final20` with `Extra3` replaced by `Extra5`.**  Same hypothesis
list as `CloseoutPackRun36.pal_in_peg_final20` (nothing added, nothing removed):
`hSP` is now stated over `BigPack2MG6`, and `hee`/`het` are the `Extra5` forms,
so neither entry nor tick obligation mentions `StageFailed` or `Candidate` any
more.  `DpFieldP` and `H_candOrient` are gone from this path entirely. -/
theorem pal_in_peg_final22 (entry q : ℕ) (first : Fin 9)
    (hSP : ∀ (w : List (Fin 2)) (x : State GalilVM),
      BigPack2MG6 centreC placeC entry q first w x →
      ScanNR x → ShiftPal centreC placeC entry q first w x.vm)
    (hws : ∀ w : List (Fin 2), ∀ y : State GalilVM, WatchShiftG centreC placeC entry q first w y)
    (hee : ∀ w : List (Fin 2), H_extraEntry5 w)
    (het : ∀ w : List (Fin 2), ∀ x y : State GalilVM, Extra5 x →
      Tick (galilFrameS (PofC centreC placeC entry w) q first) 2048 x y → Extra5 y)
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
      (packRunR_MG26 centreC placeC entry q first (hws w) (hSP w)
        (fun x y hx ht => het w x y hx.extra ht) (hme w)
        (fun c r hIC _ _ hjx =>
          extra5_steps centreC placeC entry q first (het w) (hee w c r hIC) hjx))
      (hsl w) (hsc w) (hor w hw))
    hC

#print axioms pal_in_peg_final22

end PalPeg.CloseoutPackRun43
