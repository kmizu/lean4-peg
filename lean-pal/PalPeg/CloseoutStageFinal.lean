import PalPeg.CloseoutStageOracle
import PalPeg.CloseoutPackRun51

/-!
# `pal_in_peg_final26` — `H_stageScan` gone: **seven** hypotheses

`pal_in_peg_final25` (`CloseoutPackRun51`) has eight.  `hsc` is one of them, and
it was already **refuted** as stated (`CloseoutStageScan1`): `InvScan`'s eleven
fields never mention `s.radius`, while `ReplayStage`'s `Restarted` demands a
canonical one.

It is also unnecessary.  Its single consumer on the main path is
`cycleOracleIMG2_of_cycleOracleMC3R` (`CloseoutPackRun36:673`), which calls
`hstage_of_scanBranch` to lift `InvLPC` to the `InvLPS` that `CycleOracleMC3`
demands — and that lift is only needed because Run36 §2 carries `InvLPC` through
the checkpoint recursion.  But `CycleOutMC3` hands the stage *back* at both exits
(`GalilInvPlus3:193, :212`), and the boot lands in the `Inv` branch, whose stage
`replayStage_of_inv` gives for free (`CloseoutStageBoot.invLPS_init`).

`CloseoutStageCheck` therefore re-runs the checkpoint layer over `InvLPS` —
`PreTraceIMG2` is unchanged, so it is a drop-in — and this file re-runs
`pal_in_peg_final5MG2` over it.

Seven hypotheses remain: `hSP`, `hws`, `hee`, `het`, `hme`, `hor`, `hC`.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutStageFinal

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
open PalPeg.CloseoutPackRun36 PalPeg.CloseoutStageCheck PalPeg.CloseoutStageBoot
open PalPeg.CloseoutPackRun PalPeg.CloseoutPackRun2 PalPeg.CloseoutPackRun3
open PalPeg.CloseoutPackRun5 PalPeg.CloseoutPackRun7 PalPeg.CloseoutPackRun8
open PalPeg.CloseoutPackRun9 PalPeg.CloseoutPackRun10 PalPeg.CloseoutPackRun11
open PalPeg.CloseoutPackRun12 PalPeg.CloseoutPackRun16 PalPeg.CloseoutPackRun18
open PalPeg.CloseoutPackRun19 PalPeg.CloseoutPackRun20 PalPeg.CloseoutPackRun21
open PalPeg.CloseoutPackRun23 PalPeg.CloseoutPackRun24 PalPeg.CloseoutPackRun29
open PalPeg.CloseoutPackRun30 PalPeg.CloseoutPackRun33 PalPeg.CloseoutPackRun35
open PalPeg.CloseoutPackRun26 PalPeg.CloseoutStageSupply
open PalPeg.CloseoutLPack PalPeg.CloseoutLPack2 PalPeg.CloseoutLPack3
open PalPeg.CloseoutLPack4 PalPeg.CloseoutLPack5 PalPeg.CloseoutLPack6
open PalPeg.GalilLookRefined PalPeg.CloseoutOracleI PalPeg.CloseoutLPack5
open PalPeg.CloseoutStageOracle PalPeg.CloseoutPackRun43 PalPeg.CloseoutPackRun45
open PalPeg.CloseoutPackRun46 PalPeg.CloseoutPreload37 PalPeg.CloseoutPackRun22
open PalPeg.CloseoutShiftLocalFree

theorem pal_in_peg_final5MG2S (entry q : ℕ) (first : Fin 9)
    (hboot : H_bootIMG2S centreC placeC entry q first)
    (hA : H_oracleIMG2S centreC placeC entry q first)
    (hC : H_realizeLIMG2' centreC placeC entry q first) :
    RecognizedByTotalPEG PAL := by
  classical
  obtain ⟨Q', Γ', iQ, dQ, iΓ, dΓ, t, K, L, blank, initQ, outQ, n, htape, hn, hreal⟩ := hC
  have key : ∀ w : List (Fin 2), ∃ (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      0 < w.length → PreTraceIMG2 centreC placeC entry q first w st Tc := by
    intro w
    by_cases hw : 0 < w.length
    · obtain ⟨st, Tc, h⟩ := preTraceIMG2S_exists centreC placeC entry q first hboot hA w hw
      exact ⟨st, Tc, fun _ => h⟩
    · exact ⟨fun _ => boot w, fun _ => 0, fun h => absurd h hw⟩
  choose stP TcP hP using key
  let M := L.realize blank initQ (GalilEmptyWord.accept' initQ outQ) n htape hn
  have hpre : ∀ w : List (Fin 2), 0 < w.length → PreloadL' w (stP w) (TcP w) := by
    intro w hw
    have h := hP w hw
    exact ⟨h.base.pre.tc0, fun m hm => h.base.pre.mono m (m+1) (by omega) hm,
      needL'_boot w (stP w) h.base.pre.start,
      needLe_of_pointwise' w (stP w) (TcP w) (needIMG2'_le centreC placeC entry q first hw h)⟩
  refine pal_in_peg_of_latch' (Nat.mul_pos hn (PalPeg.Local.cnt_pos K)) M
    (PofC centreC placeC entry) (fun _ => q) (fun _ => first) 2048
    (fun w => PofC_onLetter centreC placeC entry w)
    (fun w => PofC_leftFirst centreC placeC entry w)
    (fun w => stLG' τF w (stP w) (TcP w w.length))
    (fun w => arrLG' τF w (stP w) (TcP w w.length))
    (fun w => (w.length + 1) * τF) ?_ ?_ ?_ ?_
  · intro w hw
    have h := hP w hw
    exact abstractRun_throttledL'_2p18 w (stP w) (TcP w w.length)
      (PofC centreC placeC entry w) q first 2048
      (fun j => sharedC_trunc_vm w j centreC placeC entry (fun s => (centrePlaceC w j s).1)
        (fun s => (centrePlaceC w j s).2))
      (sharedC_suf w _ _ centreC placeC entry)
      (by rw [h.base.pre.start]; rfl) (needL'_boot w (stP w) h.base.pre.start)
      (by rw [h.base.pre.start]; exact sufVM_boot w) h.base.pre.trace.tick
  · intro w hw
    exact hreal w hw _ _ (hP w hw)
  · exact ledger_throttledL'_2p18 (PofC centreC placeC entry) (fun _ => q) (fun _ => first)
      stP TcP hpre (fun w hw => (hP w hw).base.pre.report w.length (by omega) le_rfl)
      (fun w hw => base_of_preTraceB (hP w hw).base)
      (fun w hw => (hP w hw).base.pre.cost)
  · exact GalilEmptyWord.realize_accept'_nil L blank initQ outQ n htape hn

/-- **`pal_in_peg_final25` with `hsc` gone: seven hypotheses.** -/
theorem pal_in_peg_final26 (entry q : ℕ) (first : Fin 9)
    (hSP : ∀ (w : List (Fin 2)) (x : GalilScaffoldTop.State GalilVM),
      BigPack2MG7 centreC placeC entry q first w x →
      ScanNR x → ShiftPal centreC placeC entry q first w x.vm)
    (hws : ∀ w : List (Fin 2), ∀ y : GalilScaffoldTop.State GalilVM,
      WatchShiftG centreC placeC entry q first w y)
    (hee : ∀ w : List (Fin 2), H_extraEntry7 centreC placeC entry w)
    (het : ∀ w : List (Fin 2), ∀ x y : GalilScaffoldTop.State GalilVM, Extra7 x →
      Tick (galilFrameS (PofC centreC placeC entry w) q first) 2048 x y → Extra7 y)
    (hme : ∀ w : List (Fin 2), H_marksEntry' (PofC centreC placeC entry w) q first)
    (hor : ∀ w : List (Fin 2), 0 < w.length →
      CycleOracleMC3 (PofC centreC placeC entry w) q first w)
    (hC : H_realizeLIMG2' centreC placeC entry q first) :
    RecognizedByTotalPEG PAL :=
  pal_in_peg_final5MG2S entry q first
    (h_bootIMG2S_of_bootIPack centreC placeC entry q first
      (fun w => h_shiftLocalG centreC placeC entry q first (raw := w))
      (bootIPack_of_parts centreC placeC entry q first h_lrepC
        (CloseoutPackRun6.h_bootShift centreC placeC entry q first)
        (CloseoutPackRun6.h_landShift centreC placeC entry q first)))
    (h_oracleIMG2S_of_MC3 centreC placeC entry q first
      (fun w => packRunR_MG27 centreC placeC entry q first (hws w) (hSP w)
        (fun x y hx ht => het w x y hx.extra ht) (hme w)
        (fun c r hIC _ _ hjx =>
          extra7_steps centreC placeC entry q first (het w) (hee w c r hIC) hjx))
      (fun w => h_shiftLocalG centreC placeC entry q first (raw := w))
      hor)
    hC

#print axioms pal_in_peg_final5MG2S
#print axioms pal_in_peg_final26

end PalPeg.CloseoutStageFinal
