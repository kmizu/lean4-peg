import PalPeg.CloseoutStageCheck
import PalPeg.CloseoutOracleI2

/-!
# The boot lands in the `Inv` branch, so its stage is free

`GalilFinalAssembly4.invLPC_init` (:71) builds the boot landing's invariant from
`hI : Inv (a :: rest) … t` (:94) and then forgets which disjunct of
`InvS = Inv ∨ ∃ k, InvScan` it used.  `CloseoutOracleI2.hstage_of_scanBranch`
closes the `Inv` disjunct for free with `replayStage_of_inv`; only the `InvScan`
disjunct ever needed `H_stageScan`.

So the boot supplies `InvLPS` outright.  This file is `invLPC_init` verbatim with
that one extra field in the conclusion — the last piece the stage-free checkpoint
layer needs.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false

namespace PalPeg.CloseoutStageBoot

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilTickArrive PalPeg.GalilLatchTracking PalPeg.GalilArriveChain
open PalPeg.GalilThrottledRun PalPeg.GalilThrottledRunGen PalPeg.GalilLedgerQ64
open PalPeg.GalilRunSkeleton PalPeg.GalilCheckpoints PalPeg.GalilTraceCost
open PalPeg.GalilOracleDischarge PalPeg.GalilOracleLocal PalPeg.GalilLexMeasure
open PalPeg.GalilInvPlus PalPeg.GalilInvPlus2 PalPeg.GalilOracleMC PalPeg.GalilOracleMC2
open PalPeg.GalilGlueBLeaves PalPeg.GalilBranchInvariants2 PalPeg.GalilSegmentConstruct
open PalPeg.GalilTruncTick PalPeg.GalilFinalAssembly PalPeg.GalilFinalAssembly2
open PalPeg.GalilFinalBaseNeed PalPeg.GalilFinalAssembly3 PalPeg.GalilOracleLeaves2
open PalPeg.GalilFinalAssembly4 PalPeg.GalilInvPlus3 PalPeg.CloseoutOracleI2

theorem invLPS_init (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9) (a : Fin 2) (rest : List (Fin 2)) :
    ∃ (c1 : Control) (t : GalilVM),
      StepsAll (galilFrameS (PofC centre place entry (a :: rest)) q first) 2048
        (SoundScanNR (a :: rest)) 1
        ⟨initial 2048, GalilBootVM.initVM0 (a :: rest)⟩ ⟨c1, t⟩ ∧
      InvLPS (PofC centre place entry (a :: rest)) q first (a :: rest) c1 t ∧
      position t.right = 1 := by
  obtain ⟨t, ht, hR, hpos, hRt, hrem, hrp, hS⟩ :=
    init_restarted_span (onLetterVM (a :: rest)) leftFirstVM shiftGuardVM beginShiftVM'
      beginFallbackVM' (restartVM entry) centre place entry q first 2048 (initial 2048) rfl
      (GalilBootVM.initVM0 (a :: rest)) a rest (GalilBootVM.initVM0_right _)
      (GalilBootVM.initVM0_radius _) (GalilBootVM.initVM0_length _)
  have hst : StepsAll (galilFrameS (PofC centre place entry (a :: rest)) q first) 2048
      (SoundScanNR (a :: rest)) 1 ⟨initial 2048, GalilBootVM.initVM0 (a :: rest)⟩
      ⟨{(initial 2048) with mode := .scan, output := true}, t⟩ :=
    .succ (fun hsc => by cases hsc) ht
      (.zero _ (fun _ _ => outputRel_position_one a rest _ t (by rw [hRt, hpos])))
  have hMt : MInv (a :: rest) {(initial 2048) with mode := .scan, output := true} t := by
    refine minv_of_leftmost ?_ rfl
    rw [hRt, hpos]
    exact leftmost_one a rest
  have htrp : t.replay = reset := by
    rw [hrp]; exact GalilBootVM.initVM0_replay _
  have hI : Inv (a :: rest) {(initial 2048) with mode := .scan, output := true} t :=
    inv_of_parts hR hMt ⟨rfl, rfl, rfl⟩ (frontier_of_reset htrp) (replayRest_of_reset htrp)
      (by
        rw [shiftIdle_iff, hrem]
        exact (shiftIdle_iff (GalilBootVM.initVM0 (a :: rest))).1
          (GalilBootVM.initVM0_shiftIdle _))
  have hIP : InvLP (a :: rest) {(initial 2048) with mode := .scan, output := true} t :=
    ⟨invL_of_run hst (invS_of_inv hI), entryCounters_of_restarted hR hS⟩
  exact ⟨_, t, hst,
    ⟨invLPC_of_boot centre place entry q first 2048 (stepsAll_steps hst) hIP
      (centreRep_of_restarted hR),
     replayStage_of_inv hI⟩,
    by rw [hRt, hpos]⟩

#print axioms invLPS_init

end PalPeg.CloseoutStageBoot
