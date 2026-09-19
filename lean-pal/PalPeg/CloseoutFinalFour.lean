import PalPeg.ShiftLocalRun
import PalPeg.CloseoutFinalW

/-!
# `given_globalScanLandings` — `H_FourSemiperiodsLeDistance` が消えた最上位（7 前提・反証済みゼロ）

## 何が変わったか

`given_globalScanLandings_and_fourOther`（`CloseoutFinalW`）の 8 前提のうち
`hfour : ∀ w, H_FourSemiperiodsLeDistance …` を落とした。**何も代わりに取らない。**

`CloseoutPackRun40.ChainPositionInvariantExactCoupling` は `CloseoutPackRun34.ChainPositionInvariant` の `coupled` 場を
`Coupled`（`Other`、2h）から `Coupled'`（`Other'`、5h ＋ 正半周期）に強めただけの構造で、

* `watchShiftS_of_chainPosInv'`（`Run40:407`）は `H_FourSemiperiodsLeDistance` を**取らない**
  （`four_of_other'` が `Coupled'.watch` の場から直接効く）、
* `chainPosInv'_tick`（`Run40:435`）が要求する分岐前提は `H_BackgroundLandingPayload` / `H_MatchLandingPayload` /
  `H_ShiftExitPayload` の **3 本だけで `final30` と同一**、
* boot は `coupled'_of_idle`（`Run40:87`）で無条件。

`ShiftLocalRun` がこれを run に載せて `needBound_without_fourOther` を作る。

## 組み立ての括り出し

`given_bootOracleRealize_and_globalScanLandings` / `5MW2` / `5MW3` / `5MW4` は、`needL'` の上界を作る 1 行を除いて
**同一の 45 行**である。本ファイルの `given_needBound` がその 45 行で、
上界そのものを `hneed` として取る。以後の版は 4 行の instantiation で済む
（既存 4 版の載せ替えは別コミット）。

## 偽の前提で `hfour` を落とした既存版との違い

| 定理 | 前提数 | 偽の前提 | 機械検査 |
|---|---|---|---|
| `final31`（`CloseoutFinalS2`） | 9 | `hav`（`ConsumeAvail` を全状態に量化） | `ConsumeAvailRefute.hav_false` |
| `final36`（`CloseoutFinalW3`） | 5 | `hpack`（`ChainPositionInvariantWithShiftPhase → ChainPack`） | `CloseoutPackRefute.hpack_false` |
| `final37`（`CloseoutFinalW4`） | 4 | 同上 | 同上 |
| **`final39`（本ファイル）** | **7** | **なし** | — |

**全体 build 成功・標準公理のみ・無条件 PAL は未完。計画書 §10.5（前提ゼロ）は未達。**
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutFinalFour

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
open PalPeg.CloseoutRadPack PalPeg.CloseoutRadPack2 PalPeg.CloseoutRadPack3
open PalPeg.CloseoutRadPack4 PalPeg.CloseoutLPack PalPeg.CloseoutLPack2
open PalPeg.CloseoutLPack3 PalPeg.CloseoutLPack4 PalPeg.CloseoutLPack5
open PalPeg.CloseoutLPack6
open PalPeg.GalilOracleDischarge PalPeg.GalilOracleLocal PalPeg.GalilLexMeasure
open PalPeg.GalilLookRefined PalPeg.GalilFinalBaseNeed PalPeg.GalilFinalAssembly2
open PalPeg.GalilLedgerQ64 PalPeg.GalilLedgerAssembly PalPeg.GalilIntervalCost
open PalPeg.GalilLatchTracking PalPeg.GalilArriveChain PalPeg.GalilTickArrive
open PalPeg.GalilTruncTick PalPeg.GalilFinalAssembly4
open PalPeg.GalilTrailScan PalPeg.GalilTrailBudget PalPeg.GalilTrailChain
open PalPeg.GalilTrailAssembly PalPeg.GalilTrailRad PalPeg.GalilFrontMono
open PalPeg.CloseoutPackRun35
open PalPeg.CloseoutPackRun36 PalPeg.CloseoutPackW PalPeg.CloseoutStageCheck
open PalPeg.CloseoutCheckW PalPeg.CloseoutExtraOracle PalPeg.CloseoutExtraFree
open PalPeg.CloseoutFrontExtra PalPeg.CloseoutStageOracle PalPeg.CloseoutStageBoot
open PalPeg.CloseoutShiftS PalPeg.CloseoutPackRun34 PalPeg.GalilLookRefined
open PalPeg.CloseoutOracleW PalPeg.CloseoutCheckW PalPeg.CloseoutPackW
open PalPeg.CloseoutShiftFinal PalPeg.CloseoutShiftLocalFree
open PalPeg.CloseoutFinalW PalPeg.ShiftLocalRun

/-- The consumer observes only the latch.  Once the deadline and lookahead
bounds hold, every such trace gives the same language, without any canonical
schedule or equality between its internal states and a concrete machine. -/
theorem latch_iff_pal_of_preTrace (entry q : ℕ) (first : Fin 9)
    {w : List (Fin 2)} {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hNonempty : 0 < w.length)
    (hPreTrace : PreTraceB centreC placeC entry q first w st Tc)
    (hNeed : ∀ m, m < w.length → ∀ i, i ≤ Tc (m+1) → needL' w st i ≤ m + 1) :
    LatchTrue (PofC centreC placeC entry w) q first w
      (stLG' τF w st (Tc w.length)) ((w.length + 1) * τF) ↔ w ∈ PAL := by
  have hPreload : PreloadL' w st Tc :=
    ⟨hPreTrace.pre.tc0, fun m hm => hPreTrace.pre.mono m (m+1) (by omega) hm,
      needL'_boot w st hPreTrace.pre.start, needLe_of_pointwise' w st Tc hNeed⟩
  apply latch_iff_pal w _ (PofC_onLetter centreC placeC entry w)
    (PofC_leftFirst centreC placeC entry w) q first
  have hRate : 2 * (2 * alpha' 2048 + (2 * beta' 2048 + 1)) ≤ τF := by
    have h := GalilLedgerThrottled.two_c2_le_τ'
    unfold GalilLedgerThrottled.c2 at h
    exact h.trans_eq' (by ring)
  exact reported_throttledLG' τF PalPeg.GalilThrottledRunGen.two_le_ticksPerSymbol _ _ hRate w hNonempty _ q first st Tc
    hPreload (hPreTrace.pre.report w.length (by omega) le_rfl)
    (fun m hm => GalilLedgerThrottled.dwT_cost w Tc hPreload.tc0
      (base_of_preTraceB hPreTrace) (hPreTrace.pre.cost) m hm)

/-- **The final theorem from a pre-loaded trace for every non-empty word.**  The trace
producer is abstracted away so that oracles of different shapes can feed it. -/
theorem given_preTraceIMW_on (entry q : ℕ) (first : Fin 9)
    (P : List (Fin 2) → (ℕ → State GalilVM) → (ℕ → ℕ) → Prop)
    (hpre : ∀ w : List (Fin 2), 0 < w.length →
      ∃ (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
        PreTraceIMW centreC placeC entry q first w st Tc ∧ P w st Tc)
    (hC : ∃ (Q' Γ' : Type) (_ : Fintype Q') (_ : DecidableEq Q') (_ : Fintype Γ')
      (_ : DecidableEq Γ') (t K : ℕ) (L : PalPeg.Local.LocalStep (Fin 2) Q' Γ' t K) (blank : Γ')
      (initQ : Q') (outQ : Q' → Bool) (n : ℕ) (htape : 0 < t) (hn : 0 < n),
      ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc,
        PreTraceIMW centreC placeC entry q first w st Tc → P w st Tc →
        ((L.realize blank initQ (GalilEmptyWord.accept' initQ outQ) n htape hn).SAccepts w ↔
          LatchTrue (PofC centreC placeC entry w) q first w (stLG' τF w st (Tc w.length))
            ((w.length + 1) * τF)))
    (hneed : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ), 0 < w.length →
      PalPeg.CloseoutCheckW.PreTraceIMW centreC placeC entry q first w st Tc →
      ∀ m, m < w.length → ∀ i, i ≤ Tc (m+1) →
        PalPeg.GalilLookRefined.needL' w st i ≤ m + 1) :
    RecognizedByTotalPEG PAL := by
  classical
  obtain ⟨Q', Γ', iQ, dQ, iΓ, dΓ, t, K, L, blank, initQ, outQ, n, htape, hn, hreal⟩ := hC
  let M := L.realize blank initQ (GalilEmptyWord.accept' initQ outQ) n htape hn
  apply pal_in_peg_of_structured (Nat.mul_pos hn (PalPeg.Local.cnt_pos K)) M
  intro w
  cases w with
  | nil =>
    exact iff_of_true (GalilEmptyWord.realize_accept'_nil L blank initQ outQ n htape hn) rfl
  | cons a rest =>
    have hNonempty : 0 < (a :: rest).length := by simp
    obtain ⟨st, Tc, hPreTrace, hPredicate⟩ := hpre (a :: rest) hNonempty
    exact (hreal _ hNonempty st Tc hPreTrace hPredicate).trans
      (latch_iff_pal_of_preTrace entry q first hNonempty hPreTrace.base
        (hneed _ st Tc hNonempty hPreTrace))

/-- The original consumer: any trace, the realization over every `PreTraceB` trace. -/
theorem given_preTraceIMW (entry q : ℕ) (first : Fin 9)
    (hpre : ∀ w : List (Fin 2), 0 < w.length →
      ∃ (st : ℕ → State GalilVM) (Tc : ℕ → ℕ), PreTraceIMW centreC placeC entry q first w st Tc)
    (hC : H_realizeLIMW' centreC placeC entry q first)
    (hneed : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ), 0 < w.length →
      PalPeg.CloseoutCheckW.PreTraceIMW centreC placeC entry q first w st Tc →
      ∀ m, m < w.length → ∀ i, i ≤ Tc (m+1) →
        PalPeg.GalilLookRefined.needL' w st i ≤ m + 1) :
    RecognizedByTotalPEG PAL :=
  given_preTraceIMW_on entry q first (fun _ _ _ => True)
    (fun w hw => by obtain ⟨st, Tc, h⟩ := hpre w hw; exact ⟨st, Tc, h, trivial⟩)
    (by
      obtain ⟨Q', Γ', iQ, dQ, iΓ, dΓ, t, K, L, blank, initQ, outQ, n, htape, hn, hreal⟩ := hC
      exact ⟨Q', Γ', iQ, dQ, iΓ, dΓ, t, K, L, blank, initQ, outQ, n, htape, hn,
        fun w hw st Tc h _ => hreal w hw st Tc h.base⟩)
    hneed

/-- **最上位の組み立て（`final5MW*` 4 版の共通部分）。**  `needL'` の上界を
`hneed` として外から取る。 -/
theorem given_needBound (entry q : ℕ) (first : Fin 9)
    (hboot : H_bootIMW centreC placeC entry q first)
    (hA : H_oracleIMW centreC placeC entry q first)
    (hC : H_realizeLIMW' centreC placeC entry q first)
    (hneed : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ), 0 < w.length →
      PalPeg.CloseoutCheckW.PreTraceIMW centreC placeC entry q first w st Tc →
      ∀ m, m < w.length → ∀ i, i ≤ Tc (m+1) →
        PalPeg.GalilLookRefined.needL' w st i ≤ m + 1) :
    RecognizedByTotalPEG PAL :=
  given_preTraceIMW entry q first
    (fun w hw => preTraceIMW_exists centreC placeC entry q first hboot hA w hw) hC hneed

/-- **`given_bootOracleRealize_and_globalScanLandings` から `hfour` が消えた版。** -/
theorem given_bootOracleRealize_sansFourOther (entry q : ℕ) (first : Fin 9)
    (hboot : H_bootIMW centreC placeC entry q first)
    (hA : H_oracleIMW centreC placeC entry q first)
    (hC : H_realizeLIMW' centreC placeC entry q first)
    (hbgP : ∀ w : List (Fin 2), H_BackgroundLandingPayload centreC placeC entry q first w)
    (hmatchP : ∀ w : List (Fin 2), H_MatchLandingPayload centreC placeC entry q first w)
    (hsdP : ∀ w : List (Fin 2), H_ShiftExitPayload centreC placeC entry q first w) :
    RecognizedByTotalPEG PAL :=
  given_needBound entry q first hboot hA hC
    (fun w st _ hw h => needBound_without_fourOther centreC placeC entry q first hw h
      (hbgP w) (hmatchP w) (hsdP w)
      (by rw [h.base.pre.start]; exact chainPosInvCoupled'_at_idle (boot_chain_idle w)))

/-- **`given_globalScanLandings_and_fourOther` から `H_FourSemiperiodsLeDistance` が消えた最上位。7 前提・反証済みゼロ。** -/
theorem given_globalScanLandings (entry q : ℕ) (first : Fin 9)
    (hSP : ∀ (w : List (Fin 2)) (x : GalilScaffoldTop.State GalilVM),
      BigPack2MG7W centreC placeC entry q first w x →
      ScanNR x → ShiftPal centreC placeC entry q first w x.vm)
    (hme : ∀ w : List (Fin 2), H_marksEntry' (PofC centreC placeC entry w) q first)
    (hor : ∀ w : List (Fin 2), 0 < w.length →
      CycleOracleMC3 (PofC centreC placeC entry w) q first w)
    (hC : H_realizeLIMW' centreC placeC entry q first)
    (hbgP : ∀ w : List (Fin 2), H_BackgroundLandingPayload centreC placeC entry q first w)
    (hmatchP : ∀ w : List (Fin 2), H_MatchLandingPayload centreC placeC entry q first w)
    (hsdP : ∀ w : List (Fin 2), H_ShiftExitPayload centreC placeC entry q first w) :
    RecognizedByTotalPEG PAL :=
  given_bootOracleRealize_sansFourOther entry q first
    (h_bootIMW_of_bootIPack centreC placeC entry q first
      (fun w => h_shiftLocalG centreC placeC entry q first (raw := w))
      (bootIPack_of_parts centreC placeC entry q first h_lrepC
        (CloseoutPackRun6.h_bootShift centreC placeC entry q first)
        (CloseoutPackRun6.h_landShift centreC placeC entry q first)))
    (h_oracleIMW_of_MC3_W centreC placeC entry q first
      (fun w => packRunR_MW centreC placeC entry q first (hSP w) (hme w))
      (fun w => h_shiftLocalG centreC placeC entry q first (raw := w))
      hor)
    hC hbgP hmatchP hsdP

#print axioms given_preTraceIMW
#print axioms given_needBound
#print axioms given_bootOracleRealize_sansFourOther
#print axioms given_globalScanLandings

end PalPeg.CloseoutFinalFour
