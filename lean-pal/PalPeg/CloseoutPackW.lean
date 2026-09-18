import PalPeg.CloseoutShiftWeak

/-!
# `IPackMW`: the run pack without the `ShiftLocalG` field

`CloseoutShiftWeak` weakened the pack's hypothesis from the false `WatchShiftG`
to `ShiftLocalG`, but `ShiftLocalG` is refuted by the same counterexample:
its fields are premised on `beginShiftVM' s'' t''`, and `beginShiftVM`
(`GalilScaffoldTopShiftCycle:23`) only asks `s''.chain = .watch w` — so a watch
just born at `ChainStep.backDone`, with `distance = reset`, satisfies the premise
while breaking `4 * periodLength ≤ distance`.

The field has to go, not be weakened.  It can: after `CloseoutShiftS` moved the
trail bridge onto `ChainPositionInvariant`, **nothing reads `IPackMG.shift`** — the only
readers were `halfBound_of_ipackMG` and `shiftVerSane_ptMG`, both replaced.

Dropping the field from `CloseoutPackRun30.IPackMG` directly breaks the older
`final17 → … → final25` chain (measured: `final18` becomes `sorryAx`), so this
file carries a *copy* of the pack without it, in the style of
`CloseoutStageCheck`.

`IPackMW w x := LPackM w x.ctl x.vm ∧ LPackM2 w x.ctl x.vm` — exactly
`IPackMG2` minus `shift`.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPackW

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
open PalPeg.CloseoutPackRun46 PalPeg.CloseoutFrontExtra
open PalPeg.CloseoutExtraFree
open PalPeg.CloseoutShiftWeak

section
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- `CloseoutPackRun36.IPackMG2` with the `shift` field dropped. -/
structure IPackMW (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9) (w : List (Fin 2)) (x : State GalilVM) : Prop where
  pack : PalPeg.CloseoutPackRun10.LPackM w x.ctl x.vm
  m2 : LPackM2 w x.ctl x.vm

/-- Forgetting the `shift` field. -/
theorem ipackMW_of_ipackMG2 {w : List (Fin 2)} {x : State GalilVM}
    (h : IPackMG2 centre place entry q first w x) : IPackMW centre place entry q first w x :=
  ⟨h.base.pack, h.m2⟩

/-- `CloseoutPackRun46.BigPack2MG7` over `IPackMW`. -/
structure BigPack2MG7W (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9) (w : List (Fin 2)) (x : State GalilVM) : Prop where
  ipackM : IPackMW centre place entry q first w x
  aux : AuxPack x.ctl x.vm
  live : CentreLive x.ctl x.vm
  extra : Extra8 x

/-- `CloseoutPackRun46.BigPack2MG7''` over `IPackMW`. -/
structure BigPack2MG7W'' (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9) (w : List (Fin 2)) (x : State GalilVM) : Prop where
  ipackM : IPackMW centre place entry q first w x
  aux : AuxPack x.ctl x.vm
  live : CentreLive x.ctl x.vm
  marks : MarksInv' first x.ctl x.vm
  extra : Extra7 x

theorem bigPack2MG7W_of_W'' {w : List (Fin 2)} {x : State GalilVM}
    (hx : BigPack2MG7W'' centre place entry q first w x)
    (hnf : x.ctl.mode = Mode.rewind →
      ¬ (galilFrameS (PofC centre place entry w) q first).atFirst x.vm) :
    BigPack2MG7W centre place entry q first w x :=
  ⟨hx.ipackM, hx.aux, hx.live,
    extra8_of_extra7 hx.extra (fun hm => two_le_left_of_marksInv' hx.marks hm (hnf hm))⟩

/-- Forgetting the `shift` field of the big pack. -/
theorem bigPack2MG7W_of_bigPack2MG7 {w : List (Fin 2)} {x : State GalilVM}
    (h : BigPack2MG7 centre place entry q first w x) :
    BigPack2MG7W centre place entry q first w x :=
  ⟨ipackMW_of_ipackMG2 centre place entry q first h.ipackM, h.aux, h.live, h.extra⟩

theorem lticksN_of_lpackM2_W {w : List (Fin 2)} {x : State GalilVM}
    (hx : BigPack2MG7W centre place entry q first w x) (hP : LPackM2 w x.ctl x.vm) :
    LTickLeavesN centre place entry q first w x.ctl x.vm where
  initPackN := fun hm _ _ => absurd hm hx.aux.front.notInit
  scanInvR := fun hm => by
    cases hrep : x.ctl.replaying with
    | false => exact hx.ipackM.pack.scanGeom hm hrep
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


/-- **The pack travels one tick with no `ShiftLocalG` anywhere.** -/
theorem ipackMW_tick {w : List (Fin 2)}
    {x y : State GalilVM} (hx : BigPack2MG7W centre place entry q first w x)
    (hSP : ScanNR x → ShiftPal centre place entry q first w x.vm)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y)
    (hg : SoundScanNR w y) : IPackMW centre place entry q first w y := by
  have hL := lticksN_of_lpackM2_W centre place entry q first hx hx.ipackM.m2
  refine ⟨?_, lpackM2_tick' centre place entry q first hx.ipackM.m2 hL hx.aux
    (lTickLeaves2_of_shiftPalG centre place entry q first hx.ipackM.m2 hL hSP) h⟩
  obtain ⟨c, s⟩ := x
  obtain ⟨c', t⟩ := y
  exact lpackN_tick centre place entry q first hx.ipackM.pack hL h

theorem bigPack2MG7W''_tick {w : List (Fin 2)}
    (hme : H_marksEntry' (PofC centre place entry w) q first)
    {x y : State GalilVM} (hx : BigPack2MG7W'' centre place entry q first w x)
    (hey : IPackMW centre place entry q first w y → Extra7 y)
    (hSP : ScanNR x → ShiftPal centre place entry q first w x.vm)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y)
    (hg : SoundScanNR w y) (hlv : CentreLive y.ctl y.vm) :
    BigPack2MG7W'' centre place entry q first w y := by
  have haux : AuxPack y.ctl y.vm := auxPack_tick centre place entry q first hx.aux hx.live h
  have hmarks : MarksInv' first y.ctl y.vm := by
    obtain ⟨c, s⟩ := x
    obtain ⟨c', t⟩ := y
    exact marksInv'_tick _ q first 2048 hx.marks (fun hm ho hs => hme c s hm ho hs) h
  suffices hip : IPackMW centre place entry q first w y by
    exact ⟨hip, haux, hlv, hmarks, hey hip⟩
  by_cases hcase : x.ctl.mode = Mode.rewind ∧
      (galilFrameS (PofC centre place entry w) q first).atFirst x.vm
  · obtain ⟨hm, hf⟩ := hcase
    obtain ⟨c, s⟩ := x
    obtain ⟨c', t⟩ := y
    obtain ⟨hc', hfr⟩ := tick_rewind_atFirst hm hf h
    have hM : LPackM w c' t :=
      lpackM_rewind_done centre place entry q first hx.ipackM.pack hm hc' hfr
    refine ⟨hM, ?_⟩
    obtain ⟨heq, hset⟩ := hfr
    have htc : t.center = s.center := by rw [hset, heq]; rfl
    have hCR : CentreRep w t := centreRep_congr htc (hx.ipackM.m2.centreRep (Or.inl hm))
    subst hc'
    refine ⟨hM, ?_, ?_, ?_, fun _ => hCR, ?_⟩
    all_goals vac rfl
  · have hnf : x.ctl.mode = Mode.rewind →
        ¬ (galilFrameS (PofC centre place entry w) q first).atFirst x.vm :=
      fun hm hf => hcase ⟨hm, hf⟩
    exact ipackMW_tick centre place entry q first
      (bigPack2MG7W_of_W'' centre place entry q first hx hnf) hSP h hg



#print axioms ipackMW_of_ipackMG2
#print axioms bigPack2MG7W_of_W''
#print axioms lticksN_of_lpackM2_W
#print axioms ipackMW_tick
#print axioms bigPack2MG7W''_tick

end

end PalPeg.CloseoutPackW
