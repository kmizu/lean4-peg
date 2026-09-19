import PalPeg.CloseoutPreload39
import PalPeg.BranchSupply
import PalPeg.GalilInvPlus3
import PalPeg.OracleRun
import PalPeg.ShapedRun
import PalPeg.CanonicalFallbackInput
import PalPeg.CanonicalReplay
import PalPeg.CanonicalChainReady
import PalPeg.CanonicalSearchHistory
import PalPeg.CanonicalSearchReady
import PalPeg.RestartLowerRun

set_option autoImplicit false

/-!
# `OracleReady`: the search readiness leaf of the run-shaped cycle oracle

`OracleRun.cycleOracleOn_of_fourLeaves` takes `hready`: the search co-process is ready at
every chain-idle scan state of a *shaped* run (`ShapedRun.ShapedSteps`: every `restart` lands
in a stage-entry restart, every `replayStart` in a fresh radius-`0` restart) out of an `InvLPS`
origin.  `CanonicalSearchReady.ready_of_invLPS_shaped` discharges it.

The canonical schedule restarts a broken chain first (`GalilTickFair.Canonical`,
`ScaffoldGalil.scala:230`).  The producer's leaves are:

* (`hrestartStage` — at a guard state of the packed run the restart lands in a stage-entry
  restart — is no longer a leaf: `RestartCertificate.restartStage` proves it);
* (`hshiftPeriodMinimal` — period minimality of the shifting chain — is no longer a leaf:
  `RestartLowerRun.scanMinimal_packed` carries the minimal period across broken restarts, using
  that the origin is reached from boot);
* `hmove` — the Galil move inequality that pays for a fallback, at a comparison state below
  the restart guard, **except** when the chain is idle and the search has parked in `missed`
  (`RestartLowerRun.move_of_idle_missed` proves that branch).

Fallback copy, fresh restart, and the entire replay segment are constructed here.
-/

namespace PalPeg.OracleReady

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilRunSkeleton PalPeg.CloseoutPreload39
  PalPeg.CloseoutReadyStage PalPeg.GalilInvPlus3 PalPeg.GalilFoundStage PalPeg.GalilOracleLocal
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
  PalPeg.GalilStructuredSkeleton PalPeg.GalilTraceCost PalPeg.ShapedRun

section
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **Search readiness at every scan state of a shaped run out of an `InvLPS` origin**, from
`hfresh` alone. -/
theorem searchReady_of_invLPS_shaped {w : List (Fin 2)}
    {c₀ : Control} {r₀ : GalilVM} (hI₀ : InvLPS (PofC centre place entry w) q first w c₀ r₀)
    {k : ℕ} {y : State GalilVM} (hsh : ShapedSteps centre place entry q first w k ⟨c₀, r₀⟩ y)
    (hm : y.ctl.mode = .scan) : PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get y.vm) := by
  exact PalPeg.CanonicalSearchReady.ready_of_invLPS_shaped centre place entry q first hI₀ hsh hm

/-- **The run-shaped cycle oracle from the atomic leaves**: `hready` of
`OracleRun.cycleOracleOn_of_fourLeaves` is `searchReady_of_invLPS_shaped`. -/
theorem cycleOracleOn_of_readyLeaves {w : List (Fin 2)} (hP : Decodes (PofC centre place entry w))
    (h4 : first ≠ 4) (hq : 0 < q) (h7 : first ≠ 7) (h8 : first ≠ 8)
    (hmove : ∀ (c₀ : Control) (r₀ : GalilVM) (k : ℕ) (c : Control) (s : GalilVM) (vq : SearchVM)
      (z : ChainVM) (m : ℕ), 1 ≤ m → m ≤ w.length →
      InvLPS (PofC centre place entry w) q first w c₀ r₀ →
      PalPeg.CloseoutCheckW.PackedFromBoot centre place entry q first w ⟨c₀, r₀⟩ →
      PalPeg.CloseoutCheckW.StepsIMWC centre place entry q first w k ⟨c₀, r₀⟩ ⟨c, s⟩ →
      ¬ restartGuardVM s →
      c.mode = .scan → c.replaying = false → c.clock = 1 → position s.right + 1 ≤ 2 * m - 1 →
      MInv w c s →
      GalilScaffoldInputHead.read (GalilScaffoldInputHead.left s.left) ≠
        GalilScaffoldInputHead.read (GalilScaffoldChainVerifier.right s.right) →
      searchEffect (PofC centre place entry w) false s vq →
      ¬ (s.chain = .idle ∧ vq.search.mode = .missed) →
      chainAt false (decide (vq.search.mode = .found)) (vq.dp.config.tapes 11)
        ((PofC centre place entry w).centre s) ((PofC centre place entry w).place s)
        s.center s.radius s.chain z →
      ¬ (PofC centre place entry w).shiftGuard
        (afterBirth (chainBorn (decide (vq.search.mode = .found)) s.chain)
          (afterMismatch s ⟨GalilScaffoldInputHead.left s.left,
            GalilScaffoldChainVerifier.right s.right, z⟩ vq)) →
      let s1 := afterBirth (chainBorn (decide (vq.search.mode = .found)) s.chain)
        (afterMismatch s ⟨GalilScaffoldInputHead.left s.left,right s.right,z⟩ vq)
      let ℓ := (value s.length).toNat
      let radius := chosenRadius
        ((GalilScaffoldPlace.stream (PalPeg.GalilTickFair.rightPlace s1)).take (ℓ+1))
      ℓ / 2 ≤ 4 * (ℓ / 2 + 1 - radius)) :
    PalPeg.CloseoutCheckW.CycleOracleOn centre place entry q first
      (PalPeg.CloseoutCheckW.ScanOnPackedRunFromInvLPS centre place entry q first)
      (PalPeg.ShapedRun.OracleTick entry) w := by
  have hrestartStage : ∀ (c₀ : Control) (r₀ : GalilVM) (k : ℕ) (y : State GalilVM),
      InvLPS (PofC centre place entry w) q first w c₀ r₀ →
      PalPeg.CloseoutCheckW.StepsIMWC centre place entry q first w k ⟨c₀, r₀⟩ y →
      y.ctl.mode = .scan → restartGuardVM y.vm → ∀ t : GalilVM, restartVM entry y.vm t →
      ∃ (Rad : ℕ) (last : Counter), Restarted w t Rad last ∧ StageEntry Rad last :=
    fun c₀ r₀ k y hI hrun hmode hguard t hrestart =>
      PalPeg.RestartCertificate.restartStage centre place entry q first hP hI hrun hmode hguard
        hrestart
  have hchain : ∀ (c₀ : Control) (r₀ : GalilVM) (k : ℕ) (y : State GalilVM),
      InvLPS (PofC centre place entry w) q first w c₀ r₀ →
      PalPeg.CloseoutCheckW.StepsIMWC centre place entry q first w k ⟨c₀,r₀⟩ y →
      y.ctl.mode = .scan → position y.vm.right+1 < (encoded w).length →
      PalPeg.GalilTickFun.ChainReady y.vm.chain := by
    intro c₀ r₀ k y hi hs hm hb
    have hp := PalPeg.CloseoutCheckW.ipackMW_last_of_stepsIMWC centre place entry q first hs
    exact PalPeg.CanonicalChainReady.of_window (hp.win hP) (PalPeg.CanonicalChainReady.copyReady_packed centre place entry q first hi
      (fun j z hz => PalPeg.CanonicalSearchHistory.birthCopy_packed centre place entry q first hP hi hz) hs) hb
  apply PalPeg.OracleRun.cycleOracleOn_of_fourLeaves centre place entry q first hP h4
    (fun c₀ r₀ k y hI₀ hsh hm _ =>
      searchReady_of_invLPS_shaped centre place entry q first hI₀ hsh hm)
    hchain hrestartStage
    (fun c₀ r₀ k c s vq z u m hm1 hmle hI₀ hBoot hrun hnoGuard hm => by
      cases w with
      | nil => exact absurd hmle (by simp; omega)
      | cons a rest =>
        exact PalPeg.CanonicalChainMinimal.shiftPeriodMinimal_packed centre place entry q first hP
          c₀ r₀ k c s vq z u m hm1 hmle hI₀ hrun
          (PalPeg.RestartLowerRun.scanMinimal_packed centre place entry q first hP hI₀ hBoot hrun
            hm) hnoGuard hm)
  intro c₀ r₀ k c s vq z m hm1 hmle hI hBoot hRun hNoGuardS hm hr hc hPos hM hMis hSearch hChain
    hGuard
  have hPack := PalPeg.CloseoutCheckW.ipackMW_last_of_stepsIMWC centre place entry q first hRun
  obtain ⟨_,_,rad,hScan,hLength⟩ :=
    PalPeg.CanonicalFallbackInput.counters centre place entry q first hI hRun hm hr
  have hCan : canRight s.right := canRight_of_bound _ w hScan.rightRep hScan.rightPresent
    (by simp only [encoded,pairs_length,List.length_append,List.length_singleton]; omega)
  obtain ⟨hEntry,hPin,fb,y,hLanding,hCentre,hPal,hMax,hMExit,hFExit⟩ :=
    PalPeg.CanonicalFallbackInput.begin_at_mismatch centre place entry q first hI hRun hm hr hCan hM hMis
      hq h7 h8 vq z
  let s1 := afterBirth (chainBorn (decide (vq.search.mode = .found)) s.chain)
    (afterMismatch s ⟨GalilScaffoldInputHead.left s.left,right s.right,z⟩ vq)
  let u := beginFallbackAt (PalPeg.GalilTickFair.rightPlace s1) s1
  let ℓ := (value s.length).toNat
  let radius := chosenRadius ((GalilScaffoldPlace.stream (PalPeg.GalilTickFair.rightPlace s1)).take (ℓ+1))
  have hLengthNat : ℓ = 2*rad+1 := by simp only [ℓ,hLength,Int.toNat_natCast]
  have hMove :
      let s1 := afterBirth (chainBorn (decide (vq.search.mode = .found)) s.chain)
        (afterMismatch s ⟨GalilScaffoldInputHead.left s.left,right s.right,z⟩ vq)
      let ℓ := (value s.length).toNat
      let radius := chosenRadius
        ((GalilScaffoldPlace.stream (PalPeg.GalilTickFair.rightPlace s1)).take (ℓ+1))
      ℓ / 2 ≤ 4 * (ℓ / 2 + 1 - radius) := by
    by_cases hmissed : s.chain = .idle ∧ vq.search.mode = .missed
    · exact PalPeg.RestartLowerRun.move_of_idle_missed centre place entry q first
        (by intro hnil; rw [hnil] at hmle; simp at hmle; omega) hP hI hBoot hRun hm hr hCan
        hmissed.1 hSearch hmissed.2
    · exact hmove c₀ r₀ k c s vq z m hm1 hmle hI hBoot hRun hNoGuardS hm hr hc hPos hM hMis hSearch
        hmissed hChain hGuard
  change ℓ / 2 ≤ 4*(ℓ / 2 + 1-radius) at hMove
  have hk : ℓ / 2 = rad := by rw [hLengthNat]; omega
  rw [hk] at hMove
  have hR1 : s1.right = right s.right := by simp only [s1,afterBirth_right,afterMismatch_right]
  have hRep1 : GalilScaffoldInputTrace.Represents s1.right.head w := by
    rw [hR1]; exact right_word _ w hScan.rightRep hCan
  have hRightPos := right_position s.right hCan (represented_position _ w hScan.rightRep hScan.rightPresent).1
  have hWinPos : 0 < ((GalilScaffoldPlace.stream (PalPeg.GalilTickFair.rightPlace s1)).take (ℓ+1)).length := by
    rw [List.length_take,PalPeg.GalilTickFair.rightPlace_length hRep1,hR1,hRightPos]
    omega
  have hChosen := (chosen_spec _ (List.ne_nil_of_length_pos hWinPos)).1
  have hRadius : radius ≤ rad := by
    have hCap : ((GalilScaffoldPlace.stream (PalPeg.GalilTickFair.rightPlace s1)).take (ℓ+1)).length ≤ ℓ+1 :=
      List.length_take_le _ _
    change 2*radius+1 ≤ _ at hChosen
    omega
  have hCentre' : position y.vm.center = position s.center+(rad+1-radius) := by
    have hCentreR : position y.vm.center = position (right s.right)-radius := hCentre
    have hScanPos : position s.right = position s.center+rad := hScan.rightPos
    rw [hRightPos,hScanPos] at hCentreR
    omega
  have hCost : 1588*(ℓ+1)+836 ≤ 12704*(rad+1-radius)+4012 := by omega
  have hReplayCost : radius ≤ 8*(rad+1-radius) := by omega
  have hCompare : (galilFrameS (PofC centre place entry w) q first).compare s s1 :=
    ⟨⟨GalilScaffoldInputHead.left s.left,right s.right,z⟩,vq,false,rfl,rfl,
      ⟨(fun h => by cases h),fun h => (hMis h).elim⟩,hSearch,hChain,rfl⟩
  have hNotMatched : ¬ (galilFrameS (PofC centre place entry w) q first).matched s1 := by
    change read s1.left ≠ read s1.right
    simpa only [s1,afterBirth_left,afterBirth_right,afterMismatch_left,afterMismatch_right] using hMis
  have hTick : Tick (galilFrameS (PofC centre place entry w) q first) 2048 ⟨c,s⟩
      ⟨{c with clock := 2048,mode := .copy},u⟩ :=
    Tick.scan_fallback c s s1 u hm (Or.inr hCan) hc hCompare hNotMatched (Or.inr hGuard) hr hEntry
  have hNR : ¬ restartVM entry s u := by
    apply not_restartVM_of_radius entry
    change value s1.radius ≠ value s.radius
    simp only [s1,afterBirth_radius,afterMismatch_radius,inc_value]
    omega
  have hCanonical : PalPeg.ShapedRun.OracleTick entry w ⟨c,s⟩
      ⟨{c with clock := 2048,mode := .copy},u⟩ :=
    PalPeg.ShapedRun.oracleTick_of_noGuard
      (PalPeg.GalilTickFair.canonical_of_scan_copy hm hNoGuardS hPin) hm hNoGuardS
  obtain ⟨g,h0,hk,hTrace,_,_⟩ := id hRun
  have hSourceSound : SoundScanNR w ⟨c,s⟩ := by rw [← hk]; exact hTrace.good k le_rfl
  have hSourceSteps : Steps (galilFrameS (PofC centre place entry w) q first) 2048 k ⟨c₀,r₀⟩ ⟨c,s⟩ := by
    have h := PalPeg.CloseoutPackRun2.steps_of_trace hTrace k le_rfl
    simpa only [h0,hk] using h
  have hPrefix := StepsAllR.succ hSourceSound hTick hCanonical hLanding.run
  have hFrontExit : PalPeg.GalilRunTrace.front y.vm = (position s.right+1 : ℕ) := by
    rw [PalPeg.GalilRunTrace.front_ofNat hLanding.replay,← hLanding.center,hCentre]
    have hRightPos := right_position s.right hCan (represented_position _ w hScan.rightRep hScan.rightPresent).1
    have hBound := hPal.1
    omega
  have hPacked := PalPeg.CloseoutMarksPack.packRunR_MWR_front centre place entry q first h4 hP
    (PalPeg.ShapedRun.OracleTick entry w) c₀ r₀ hI m hm1 hmle k ⟨c,s⟩ hSourceSteps
    (fb+1) y hPack hPrefix (by rw [hFrontExit]; exact_mod_cast hPos)
  have hRunY := PalPeg.CloseoutCheckW.stepsIMWC_trans centre place entry q first hRun hPacked
  have hStepsY := steps_trans hSourceSteps (stepsAllR_steps hPrefix)
  have hPackY := PalPeg.CloseoutCheckW.ipackMW_last_of_stepsIMWC centre place entry q first hRunY
  have hNoGuardY : ¬ restartGuardVM y.vm := by
    rintro ⟨w', hw', -⟩
    rw [hLanding.restarted.1] at hw'; cases hw'
  obtain ⟨N,yr,hN,hReplay,hShape,hNoGuardR,hMode,hClock,hReplaying,hRep,hScanR,hMinv,hC,hRight,hFront,
      hRem,hRefresh⟩ :=
    PalPeg.CanonicalReplay.segment centre place entry q first radius y.ctl y.vm 0
      hLanding.mode hLanding.clock hLanding.replaying hLanding.replay hLanding.restarted.2.2.2.1
      hMExit hFExit (stepsAll_last (stepsAllR_stepsAll hLanding.run)) hNoGuardY hLanding.refreshed
      (fun j t hs hmode _ => by
        have hstart := PalPeg.CanonicalSearchReady.field_restarted
          ((PofC centre place entry w).place y.vm) hLanding.restarted
          (stageEntry_zero _) hLanding.mode hLanding.clock
        exact (PalPeg.CanonicalSearchReady.field_alongShaped centre place entry q first hs
          (by rw [hLanding.mode]; decide) hstart).ready hmode)
      (fun j t hs hmode hFrontEq => by
        have hp := PalPeg.CloseoutMarksPack.packRunR_MWR_front centre place entry q first h4 hP
          (PalPeg.ShapedRun.OracleTick entry w) c₀ r₀ hI m hm1 hmle _ y hStepsY
          j t hPackY hs (by rw [hFrontEq,hFrontExit]; exact_mod_cast hPos)
        exact hchain c₀ r₀ _ t hI
          (PalPeg.CloseoutCheckW.stepsIMWC_trans centre place entry q first hRunY hp) hmode (by
            have htfront : PalPeg.GalilRunTrace.front t.vm = (position s.right+1 : ℕ) :=
              hFrontEq.trans hFrontExit
            have hrunT := PalPeg.CloseoutCheckW.stepsIMWC_trans centre place entry q first hRunY hp
            have hstepsT := steps_trans hStepsY (stepsAllR_steps hs)
            have hcp := PalPeg.GalilCentreLive.cpack_steps (onLetterVM w) leftFirstVM
              centre place entry q first 2048 hstepsT
              (PalPeg.GalilInvPlus2.hfloor_of_invLP2 centre place entry q first hI.1.1)
              (PalPeg.GalilCentreLive.cpack_of_entry q hI.1.1.1.1.1 hI.1.1.1.2)
            have hle : (position t.vm.right : ℤ) ≤ PalPeg.GalilRunTrace.front t.vm := by
              cases hr : t.ctl.replaying with
              | false => rw [PalPeg.CloseoutFrontExtra.front_eq_position hcp.front hr]
              | true =>
                obtain ⟨n,hn⟩ := hcp.front.replayPos hr
                rw [PalPeg.GalilRunTrace.front_ofNat hn]; omega
            have hlen : (encoded w).length = 2*w.length+1 := by simp [encoded,pairs_length]
            omega))
      (fun j t hs hmode hFrontEq hg t' ht' => by
        have hp := PalPeg.CloseoutMarksPack.packRunR_MWR_front centre place entry q first h4 hP
          (PalPeg.ShapedRun.OracleTick entry w) c₀ r₀ hI m hm1 hmle _ y hStepsY
          j t hPackY hs (by rw [hFrontEq,hFrontExit]; exact_mod_cast hPos)
        exact hrestartStage c₀ r₀ _ t hI
          (PalPeg.CloseoutCheckW.stepsIMWC_trans centre place entry q first hRunY hp) hmode hg t' ht')
  refine ⟨u,hEntry,hPin,yr.ctl,yr.vm,rad,radius,fb,N,
    stepsAllR_trans hLanding.run hReplay,
    shapedSteps_trans centre place entry q first hLanding.shaped hShape,
    hMode,hReplaying,hRefresh,hMinv,hNoGuardR,?_,hRadius,?_,hLanding.cost.trans hCost,?_⟩
  · have hRightR : position yr.vm.right = position y.vm.right+radius := hRight
    have h0 := hFrontExit
    rw [PalPeg.GalilRunTrace.front_ofNat hLanding.replay] at h0
    have hn : position y.vm.right+radius = position s.right+1 := by exact_mod_cast h0
    exact hRightR.trans hn
  · rw [hC]; exact hCentre'
  · omega

#print axioms cycleOracleOn_of_readyLeaves
#print axioms searchReady_of_invLPS_shaped


end

end PalPeg.OracleReady
