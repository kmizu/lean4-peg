import PalPeg.OracleRun
import PalPeg.ReadyTransport

/-! # Replay with the actual search and chain co-processes

Replay comparisons are forced by MInv. Search may finish and start a chain:
the construction uses the general matching tick, with no SearchQuiet premise.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace PalPeg.CanonicalReplay
open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
open PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilRunSkeleton
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilTickFair PalPeg.ShapedRun PalPeg.GalilStructuredSkeleton
open PalPeg.GalilRunTrace PalPeg.GalilFrontMono
open PalPeg.GalilReplaySegment PalPeg.GalilTickFun PalPeg.GalilTickFun2

variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- One forced replay comparison. The resulting chain is allowed to be active. -/
theorem comparison {raw : List (Fin 2)} (c : Control) (s : GalilVM) (rad rem : ℕ)
    (hm : c.mode = .scan) (hr : c.replaying = true) (hc : c.clock = 1)
    (hScan : ScanInvariant raw (position s.center) rad s.left s.right)
    (hMinv : MInv raw c s) (hRep : s.replay = ofNat (rem+1)) (hFront : Frontier s)
    (hSearch : ∃ v, searchEffect (PofC centre place entry raw) true s v)
    (hChain : ChainReady s.chain) :
    ∃ y : State GalilVM,
      StepsAllR (galilFrameS (PofC centre place entry raw) q first) 2048
        (SoundScanNR raw) (Canonical entry 2048) 1 ⟨c,s⟩ y ∧
      ShapedSteps centre place entry q first raw 1 ⟨c,s⟩ y ∧
      y.ctl.mode = .scan ∧ y.ctl.clock = 2048 ∧ y.ctl.replaying = decide (0 < rem) ∧
      y.vm.replay = ofNat rem ∧ y.vm.center = s.center ∧
      position y.vm.right = position s.right+1 ∧
      ScanInvariant raw (position y.vm.center) (rad+1) y.vm.left y.vm.right ∧
      MInv raw y.ctl y.vm ∧ Frontier y.vm ∧ y.vm.remaining = s.remaining ∧
      Refreshed (PofC centre place entry raw) q first y := by
  have hBound := hFront (rem+1) hRep
  have hav := PalPeg.GalilReplaySegment.canRight_of_frontier (Nat.succ_pos rem) hBound
  have hMatch := replay_match_of_minv hMinv hr hav hScan
  obtain ⟨vq,z,o,hq,hz,ho,ht⟩ :=
    PalPeg.OracleRun.matched_tick centre place entry q first c s hm hc hav hMatch hSearch hChain
  let b := chainBorn (decide (vq.search.mode = .found)) s.chain
  let vs : ScanVM := ⟨left s.left,right s.right,z⟩
  let t := replayDec true (afterBirth b (afterCompare s vs vq))
  let c' : Control := {c with clock := 2048,output := o, replaying := !(PofC centre place entry raw).replayExhausted t}
  have hTick : Tick (galilFrameS (PofC centre place entry raw) q first) 2048 ⟨c,s⟩ ⟨c',t⟩ := by
    simpa only [hr,Bool.true_and] using ht
  have hRefresh : refresh (galilFrameS (PofC centre place entry raw) q first) t c.output o := by
    simpa only [hr] using ho
  have hReplay : t.replay = ofNat rem := by
    simp only [t,replayDec_true_replay,afterBirth_replay,afterCompare_replay,hRep,dec_ofNat_succ]
  have hFlag : c'.replaying = decide (0 < rem) := by
    change (!zero t.replay) = decide (0 < rem)
    rw [hReplay]
    cases rem <;> simp [zero,ofNat]
  have hR : t.right = right s.right := by
    simp only [t,replayDec_right,afterBirth_right,afterCompare_right,vs]
  have hL : t.left = left s.left := by
    simp only [t,replayDec_left,afterBirth_left,afterCompare_left,vs]
  have hC : t.center = s.center := by
    simp only [t,replayDec_center,afterBirth_center,afterCompare_center]
  have hPos : position t.right = position s.right+1 := by
    rw [hR]
    exact right_position s.right hav (represented_position _ raw hScan.rightRep hScan.rightPresent).1
  have hScan' : ScanInvariant raw (position t.center) (rad+1) t.left t.right := by
    rw [hL,hR,hC]
    exact scanInvariant_matched hScan hav hMatch
  have hOut : OutputRel raw c' t :=
    outputRel_transfer raw rfl rfl
      (outputRel_of_refresh raw (PofC centre place entry raw) rfl rfl q first c t o hScan' hRefresh)
  have hQ : SoundScanNR raw ⟨c',t⟩ := fun _ _ => hOut
  have hNoRestart : ¬ restartVM entry s t :=
    not_restartVM_of_chainAt_target entry hz
      (by simp only [t,replayDec_chain,afterBirth_chain,afterCompare_chain,vs])
  have hCan : Canonical entry 2048 ⟨c,s⟩ ⟨c',t⟩ :=
    canonical_of_scan_nonCopy hm (by change c.mode ≠ .copy; rw [hm]; decide) hNoRestart
  refine ⟨⟨c',t⟩,.succ (soundScanNR_replaying raw hr) hTick hCan (.zero _ hQ),
    .succ hTick (fun _ => hNoRestart)
      (fun h => (by have : c.mode = .replayStart := h; rw [hm] at this; cases this)) (.zero _),
    hm,rfl,hFlag,hReplay,hC,hPos,hScan',?_,?_,?_,⟨c.output,hRefresh⟩⟩
  · have hBase := minv_matchR (PofC centre place entry raw) (fun _ => rfl)
      (vs := vs) (vq := vq) o 2048 hr rfl hav hScan hMinv
    apply minv_same (s := replayDec true (afterCompare s vs vq)) (c :=
      {c with clock := 2048,output := o, replaying := !(PofC centre place entry raw).replayExhausted (replayDec true (afterCompare s vs vq))})
      ?_ ?_ ?_ ?_ hBase
    · change (!zero t.replay) = (!zero (replayDec true (afterCompare s vs vq)).replay)
      simp only [t,replayDec_true_replay,afterBirth_replay]
    · simp only [t,replayDec_right,afterBirth_right]
    · simp only [t,replayDec_center,afterBirth_center]
    · simp only [t,replayDec_true_replay,afterBirth_replay]
  · intro m hm
    have he : m = rem := (ofNat_inj (hReplay.symm.trans hm)).symm
    subst m
    rw [hR]
    exact right_frontier_step s.right rem hBound
  · simp only [t,PalPeg.GalilReplaySegment.replayDec_remaining,afterBirth_remaining,PalPeg.GalilReplaySegment.afterCompare_remaining]

/-- Complete a replay using readiness only at states on the constructed run.
The chain may start or advance during replay. -/
theorem segment {raw : List (Fin 2)} (rem : ℕ) :
    ∀ (c : Control) (s : GalilVM) (rad : ℕ),
    c.mode = .scan → c.clock = 2048 → c.replaying = decide (0 < rem) →
    s.replay = ofNat rem → ScanInvariant raw (position s.center) rad s.left s.right →
    MInv raw c s → Frontier s → SoundScanNR raw ⟨c,s⟩ →
    (rem = 0 → Refreshed (PofC centre place entry raw) q first ⟨c,s⟩) →
    (∀ k y, ShapedSteps centre place entry q first raw k ⟨c,s⟩ y →
      y.ctl.mode = .scan → y.vm.chain = .idle →
      PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get y.vm)) →
    (∀ k y, StepsAllR (galilFrameS (PofC centre place entry raw) q first) 2048
      (SoundScanNR raw) (Canonical entry 2048) k ⟨c,s⟩ y →
      y.ctl.mode = .scan → front y.vm = front s → ChainReady y.vm.chain) →
    ∃ y, StepsAllR (galilFrameS (PofC centre place entry raw) q first) 2048
      (SoundScanNR raw) (Canonical entry 2048) (rem*2048) ⟨c,s⟩ y ∧
      ShapedSteps centre place entry q first raw (rem*2048) ⟨c,s⟩ y ∧
      y.ctl.mode = .scan ∧ y.ctl.clock = 2048 ∧ y.ctl.replaying = false ∧
      y.vm.replay = reset ∧
      ScanInvariant raw (position y.vm.center) (rad+rem) y.vm.left y.vm.right ∧
      MInv raw y.ctl y.vm ∧ y.vm.center = s.center ∧
      position y.vm.right = position s.right+rem ∧ Frontier y.vm ∧
      y.vm.remaining = s.remaining ∧ Refreshed (PofC centre place entry raw) q first y := by
  induction rem with
  | zero =>
    intro c s rad hm hc hr hRep hScan hMinv hFront hQ hRefresh hReady hChain
    exact ⟨⟨c,s⟩,.zero _ hQ,.zero _,hm,hc,by simpa using hr,hRep,
      by simpa using hScan,hMinv,rfl,by simp,hFront,rfl,hRefresh rfl⟩
  | succ rem ih =>
    intro c s rad hm hc hFlag hRep hScan hMinv hFront hQ hRefresh hReady hChain
    have hr : c.replaying = true := by simpa using hFlag
    have hav := PalPeg.GalilReplaySegment.canRight_of_frontier (Nat.succ_pos rem)
      (hFront (rem+1) hRep)
    obtain ⟨t,hBg,hL,hR,hC,hReplay,hRemaining,hRadius,hLength,hFpp,hBgShape⟩ :=
      PalPeg.OracleRun.scanBackground_run_all centre place entry q first 2047 c s hm hc hav hQ
        hReady (fun k y h hy _ hyr hyrep => hChain k y h hy (front_congr hyr hyrep))
    have hScanT : ScanInvariant raw (position t.center) rad t.left t.right := by
      rw [hL,hR,hC]; exact hScan
    have hMinvT : MInv raw {c with clock := 1} t := minv_same rfl hR hC hReplay hMinv
    have hFrontT : Frontier t := by intro m he; rw [hReplay] at he; rw [hR]; exact hFront m he
    have hSearch : ∃ v, searchEffect (PofC centre place entry raw) true t v := by
      by_cases hi : t.chain = .idle
      · exact PalPeg.GalilBranchInvariants2.searchEffect_exists _ true t
          (hReady 2047 ⟨{c with clock := 1},t⟩ hBgShape hm hi)
      · exact ⟨searchLens.get t,Or.inr ⟨hi,rfl⟩⟩
    obtain ⟨y1,hStep,hStepShape,hm1,hc1,hr1,hRep1,hC1,hPos1,hScan1,hMinv1,hFront1,hRem1,hRef1⟩ :=
      comparison centre place entry q first {c with clock := 1} t rad rem hm hr rfl
        hScanT hMinvT (hReplay.trans hRep) hFrontT hSearch
        (hChain 2047 ⟨{c with clock := 1},t⟩ hBg hm (front_congr hR hReplay))
    have hRound : StepsAllR (galilFrameS (PofC centre place entry raw) q first) 2048
        (SoundScanNR raw) (Canonical entry 2048) 2048 ⟨c,s⟩ y1 :=
      stepsAllR_trans hBg hStep
    have hRoundShape : ShapedSteps centre place entry q first raw 2048 ⟨c,s⟩ y1 :=
      shapedSteps_trans centre place entry q first hBgShape hStepShape
    have hFrontRound : front y1.vm = front s := by
      rw [front_ofNat hRep1,front_ofNat hRep,hPos1,hR]
      push_cast
      ring
    obtain ⟨y,hRest,hRestShape,hm2,hc2,hr2,hRep2,hScan2,hMinv2,hC2,hPos2,hFront2,hRem2,hRef2⟩ :=
      ih y1.ctl y1.vm (rad+1) hm1 hc1 hr1 hRep1 hScan1 hMinv1 hFront1
        (stepsAll_last (stepsAllR_stepsAll hStep)) (fun _ => hRef1)
        (fun k y hs hmode hidle => hReady (2048+k) y
          (shapedSteps_trans centre place entry q first hRoundShape hs) hmode hidle)
        (fun k y hs hmode hf => hChain (2048+k) y (stepsAllR_trans hRound hs) hmode (hf.trans hFrontRound))
    have hTicks : (rem+1)*2048 = 2048+rem*2048 := by omega
    refine ⟨y,?_,?_,hm2,hc2,hr2,hRep2,?_,hMinv2,hC2.trans (hC1.trans hC),?_,hFront2,
      hRem2.trans (hRem1.trans hRemaining),hRef2⟩
    · rw [hTicks]; exact stepsAllR_trans hRound hRest
    · rw [hTicks]; exact shapedSteps_trans centre place entry q first hRoundShape hRestShape
    · convert hScan2 using 1 <;> omega
    · rw [hPos2,hPos1,hR]; omega

#print axioms comparison
#print axioms segment
end PalPeg.CanonicalReplay
