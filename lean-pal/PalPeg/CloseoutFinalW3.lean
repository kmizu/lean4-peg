import PalPeg.CloseoutWatchSupply
import PalPeg.CloseoutFinalPack

/-!
# `pal_in_peg_final34` — `ConsumeAvail` gone

`CloseoutPackRun41.watchShiftS_of_chainPosInv2` uses `ConsumeAvail` at exactly
one place, `chainPos_step P.chainPos hav hstep`, and
`CloseoutPackRun48.chainPos_step_of_supply` is that step with the `ConsumeAvail`
replaced by four local facts — all `ChainPack` fields.  So `hav` was never an
independent obligation: it is the same data as `hpack`.

`hav` is therefore replaced by nothing new; only `hsc` (the trace's states are
`scan`, a property of `PreTraceB`, not an oracle) appears in its place.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutFinalW3

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
open PalPeg.CloseoutPackRun36 PalPeg.CloseoutPackW PalPeg.CloseoutStageCheck
open PalPeg.CloseoutCheckW PalPeg.CloseoutExtraOracle PalPeg.CloseoutExtraFree
open PalPeg.CloseoutFrontExtra PalPeg.CloseoutStageOracle PalPeg.CloseoutStageBoot
open PalPeg.CloseoutShiftS PalPeg.CloseoutPackRun34 PalPeg.GalilLookRefined
open PalPeg.CloseoutOracleW PalPeg.CloseoutCheckW PalPeg.CloseoutPackW
open PalPeg.CloseoutShiftFinal PalPeg.CloseoutShiftLocalFree
open PalPeg.CloseoutOracleW PalPeg.CloseoutCheckW PalPeg.CloseoutPackW
open PalPeg.CloseoutFinalW PalPeg.CloseoutShiftLocalFree
open PalPeg.CloseoutPackRun41 PalPeg.CloseoutPackRun44 PalPeg.CloseoutPackRun47
open PalPeg.CloseoutPackRun48 PalPeg.CloseoutShiftS2 PalPeg.CloseoutTrailS2
open PalPeg.CloseoutOracleW PalPeg.CloseoutCheckW PalPeg.CloseoutPackW
open PalPeg.CloseoutFinalW PalPeg.CloseoutShiftLocalFree
open PalPeg.CloseoutPackRun41 PalPeg.CloseoutPackRun44 PalPeg.CloseoutPackRun47
open PalPeg.CloseoutPackRun48 PalPeg.CloseoutShiftS2 PalPeg.CloseoutTrailS2
open PalPeg.CloseoutChainPack PalPeg.CloseoutWatchSupply PalPeg.CloseoutFinalS2
open PalPeg.CloseoutFinalPack

theorem pal_in_peg_final5MW3 (entry q : ℕ) (first : Fin 9)
    (hboot : H_bootIMW centreC placeC entry q first)
    (hA : H_oracleIMW centreC placeC entry q first)
    (hC : H_realizeLIMW' centreC placeC entry q first)
    (hbgP : ∀ w : List (Fin 2), H_bgP2 centreC placeC entry q first w)
    (hmatchP : ∀ w : List (Fin 2), H_matchP2 centreC placeC entry q first w)
    (hentry : ∀ w : List (Fin 2), H_shiftEntry2 centreC placeC entry q first w)
    (hsdP : ∀ w : List (Fin 2), H_shiftDoneRad2 centreC placeC entry q first w)
    (hpos2 : ∀ (w : List (Fin 2)) (st : ℕ → GalilScaffoldTop.State GalilVM),
      st 0 = boot w → ChainPosInv2 w (st 0).ctl (st 0).vm)
    (hpk : ∀ (w : List (Fin 2)) (c : Control) (s : GalilVM),
      ChainPosInv2 w c s → ChainPack q first w c s)
    :
    RecognizedByTotalPEG PAL := by
  classical
  obtain ⟨Q', Γ', iQ, dQ, iΓ, dΓ, t, K, L, blank, initQ, outQ, n, htape, hn, hreal⟩ := hC
  have key : ∀ w : List (Fin 2), ∃ (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      0 < w.length → PreTraceIMW centreC placeC entry q first w st Tc := by
    intro w
    by_cases hw : 0 < w.length
    · obtain ⟨st, Tc, h⟩ := preTraceIMW_exists centreC placeC entry q first hboot hA w hw
      exact ⟨st, Tc, fun _ => h⟩
    · exact ⟨fun _ => boot w, fun _ => 0, fun h => absurd h hw⟩
  choose stP TcP hP using key
  let M := L.realize blank initQ (GalilEmptyWord.accept' initQ outQ) n htape hn
  have hpre : ∀ w : List (Fin 2), 0 < w.length → PreloadL' w (stP w) (TcP w) := by
    intro w hw
    have h := hP w hw
    exact ⟨h.base.pre.tc0, fun m hm => h.base.pre.mono m (m+1) (by omega) hm,
      needL'_boot w (stP w) h.base.pre.start,
      needLe_of_pointwise' w (stP w) (TcP w)
        (PalPeg.CloseoutWatchSupply.needIMW'_le_W3 centreC placeC entry q first hw h
          (hbgP w) (hmatchP w) (hentry w) (hsdP w)
          (hpos2 w (stP w) h.base.pre.start) (hpk w))⟩
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
    exact hreal w hw _ _ (hP w hw).base
  · exact ledger_throttledL'_2p18 (PofC centreC placeC entry) (fun _ => q) (fun _ => first)
      stP TcP hpre (fun w hw => (hP w hw).base.pre.report w.length (by omega) le_rfl)
      (fun w hw => base_of_preTraceB (hP w hw).base)
      (fun w hw => (hP w hw).base.pre.cost)
  · exact GalilEmptyWord.realize_accept'_nil L blank initQ outQ n htape hn



#print axioms pal_in_peg_final5MW2

#print axioms pal_in_peg_final5MW3

/-- **`pal_in_peg_final33` with `hav`, `hstart` and `hbudget` gone: five
hypotheses.**

`hbudget` is a `ChainPack` field too (`scanBound`): the position bound is a
property of the state, and `ChainPack` is what travels along the run, so it
belongs in the bundle rather than beside it.

`hstart` is not an independent obligation either:
`CloseoutPackRun47.bgStartP2_of_centre` already produces `BgStartP2` from three
facts about a `scan` state — `canRight s.right`, the radius ledger and
`CentreLedger` — and all three are `ChainPack` fields (the first via the
position bound).

`hav` was not an independent obligation.  `watchShiftS_of_chainPosInv2` uses
`ConsumeAvail` at exactly one place, and `chainPos_step_of_supply` is that step
over the four local facts that are already `ChainPack` fields.  Nothing replaces
it: `shiftLocalS_of_chainPack` needs no mode hypothesis either, because every
field of `ShiftLocalS` is premised on `ScanNR x`, so the mode is available from
inside the field. -/
theorem pal_in_peg_final36 (entry q : ℕ) (first : Fin 9)
    (hSP : ∀ (w : List (Fin 2)) (x : GalilScaffoldTop.State GalilVM),
      BigPack2MG7W centreC placeC entry q first w x →
      ScanNR x → ShiftPal centreC placeC entry q first w x.vm)
    (hme : ∀ w : List (Fin 2), H_marksEntry' (PofC centreC placeC entry w) q first)
    (hor : ∀ w : List (Fin 2), 0 < w.length →
      CycleOracleMC3 (PofC centreC placeC entry w) q first w)
    (hC : H_realizeLIMW' centreC placeC entry q first)
    (hpack : ∀ (w : List (Fin 2)) (c : Control) (s : GalilVM),
      ChainPosInv2 w c s → ChainPack q first w c s)
    :
    RecognizedByTotalPEG PAL :=
  pal_in_peg_final5MW3 entry q first
    (h_bootIMW_of_bootIPack centreC placeC entry q first
      (fun w => h_shiftLocalG centreC placeC entry q first (raw := w))
      (bootIPack_of_parts centreC placeC entry q first h_lrepC
        (CloseoutPackRun6.h_bootShift centreC placeC entry q first)
        (CloseoutPackRun6.h_landShift centreC placeC entry q first)))
    (h_oracleIMW_of_MC3_W centreC placeC entry q first
      (fun w => packRunR_MW centreC placeC entry q first (hSP w) (hme w))
      (fun w => h_shiftLocalG centreC placeC entry q first (raw := w))
      hor)
    hC
    (fun w => h_bgP2_of_chainPack centreC placeC entry q first (hpack w)
      (bgStartP2_of_chainPack centreC placeC entry q first (hpack w)
        (scanBudget_of_chainPack centreC placeC entry q first (hpack w))))
    (fun w => h_matchP2_of_target centreC placeC entry q first
      (h_matchRes2_of_chainPack centreC placeC entry q first (hpack w) (scanBudget_of_chainPack centreC placeC entry q first (hpack w))))
    (fun w => h_shiftEntry2_of_target centreC placeC entry q first
      (h_shiftRes2_of_chainPack centreC placeC entry q first (hpack w) (scanBudget_of_chainPack centreC placeC entry q first (hpack w))))
    (fun w => h_shiftDoneRad2_of_chainPack centreC placeC entry q first (hpack w))
    (fun w st hst => by rw [hst]; exact chainPosInv2_of_idle (boot_chain_idle w))
    (fun w => hpack w)

#print axioms pal_in_peg_final36


end PalPeg.CloseoutFinalW3
