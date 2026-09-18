import PalPeg.CloseoutFinalW4
import PalPeg.CloseoutVerSide

/-!
# `given_globalRun41Landings_and_verifierRun` — the refuted `hpack` replaced by the run-level `VerRun`

`CloseoutPackRefute` showed `hpack : ∀ w c s, ChainPosInv2 w c s → ChainPack …`
is **false**.  `CloseoutVerSide` then measured what the top theorem actually
uses it for: `given_bootOracleRealize_and_chainPackAtAnyState` calls it in exactly one place, and the
lemma at the bottom of that call (`shiftLocalS_of_chainPack`) reads four fields,
three of which (`inv`, `repR`) the caller already has — `ChainPosInv2` is a
hypothesis and `LPackM`/`LPackM2` come off the pre-trace's own packs.

So the whole contribution of `hpack` is `repV` and `lagCan` at the run's `scan`
states, and `CloseoutVerSide.VerRun` states exactly those **along the run**.
That is not free at an arbitrary idle-chain state, so `chainPosInv2_of_idle`
gives no counterexample — the refutation does not apply to it.

`given_bootOracleRealize_and_verifierRun` is `final5MW3` with `needIMW'_le_W4` in place of
`needIMW'_le_W3`, and `given_globalRun41Landings_and_verifierRun` is `final37` with `hpack` replaced by
`hver`.  Four hypotheses still, but **none of them refuted**:

* `hSP` — the `ShiftPal` move lemma (guard premised, geometric conclusion);
* `hor` — `CycleOracleMC3`;
* `hC` — local realization;
* `hver` — `VerRun` at the boot state of every run.

`verRun_of_hpack` shows nothing is lost: the old (false) hypothesis implies the
new one.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutFinalW5

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

open PalPeg.CloseoutVerSide
open PalPeg.CloseoutFinalW3
open PalPeg.CloseoutFinalW4

theorem given_bootOracleRealize_and_verifierRun (entry q : ℕ) (first : Fin 9)
    (hboot : H_bootIMW centreC placeC entry q first)
    (hA : H_oracleIMW centreC placeC entry q first)
    (hC : H_realizeLIMW' centreC placeC entry q first)
    (hbgP : ∀ w : List (Fin 2), H_bgP2 centreC placeC entry q first w)
    (hmatchP : ∀ w : List (Fin 2), H_matchP2 centreC placeC entry q first w)
    (hentry : ∀ w : List (Fin 2), H_shiftEntry2 centreC placeC entry q first w)
    (hsdP : ∀ w : List (Fin 2), H_shiftDoneRad2 centreC placeC entry q first w)
    (hpos2 : ∀ (w : List (Fin 2)) (st : ℕ → GalilScaffoldTop.State GalilVM),
      st 0 = boot w → ChainPosInv2 w (st 0).ctl (st 0).vm)
    (hver : ∀ (w : List (Fin 2)) (st : ℕ → GalilScaffoldTop.State GalilVM),
      st 0 = boot w → VerRun centreC placeC entry q first w (st 0))
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
        (PalPeg.CloseoutVerSide.needIMW'_le_W4 centreC placeC entry q first hw h
          (hbgP w) (hmatchP w) (hentry w) (hsdP w)
          (hpos2 w (stP w) h.base.pre.start)
          (hver w (stP w) h.base.pre.start))⟩
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

#print axioms given_bootOracleRealize_and_verifierRun

end PalPeg.CloseoutFinalW5
