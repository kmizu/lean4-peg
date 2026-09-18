import PalPeg.LiveSegmentConstruct
import PalPeg.FoundPackCorrected
import PalPeg.ChainReachesWatchFromFound

/-!
# `ReachesWatchPhase` を run から出す（clock の余裕なし）

`FoundPackCorrected.reachesWatchPhase_of_backgroundRun` は `n < cP.clock` を要求して
いたので `2h+2 < 2048` の準備しか載らなかった。`LiveSegmentConstruct.
watchSegE_constructLive` が clock を構成の中で処理するようになったので、その制約が消える。

結論は選言 2 択:

* **`ReachesWatchPhase`** — 準備の `2h+2` 手が走り切って chain が watch 相に着いた
  （`chainReachesWatch_of_found` が chain の trace を、`chainTicks_unique` が区間の終端を決める）
* **`SegEnd` で早く終わった** — 準備の途中で比較が不一致になった。そこでは chain は
  まだ copy/back なので `shiftGuard` は立たず、機械は `scan_fallback` に行く
  （`FoundPackCorrected.no_shift_from_copyChain`）

**この 2 択が正しい目標。** n125 で「無条件形は成り立たない」と書いたのは、
idle 版の構成が既に同じ 2 択で書かれていること（`es.length = n ∨ SegEnd P c' t`）を
見落としていたため。新しい概念は要らなかった。

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.ReachesWatchFromRun

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilScaffoldController
open GalilScaffoldCounter GalilScaffoldChainVerifier GalilScaffoldInputHead
open PalPeg.CopyPhaseTick PalPeg.CopyPhaseTickMatched PalPeg.GalilSegmentConstruct
open PalPeg.FoundPackCorrected PalPeg.LiveSegmentConstruct

/-- **`ReachesWatchPhase` を run から、clock の余裕なしで。** -/
theorem reachesWatchPhase_or_segEnd (P : Shared) (q : ℕ) (first : Fin 9) (h : ℕ)
    {cP : Control} {sP : GalilVM}
    (hScan : cP.mode = Mode.scan) (hNotReplaying : cP.replaying = false)
    (hClock : 1 ≤ cP.clock)
    (hPhase : CopyOrBack sP.chain) (hLag : LagPos sP.chain)
    (hChainReachesWatch : ∀ es : List Bool, es.length = 2 * h + 2 →
      ∃ w : GalilScaffoldChainWatch.State, ChainTicks es sP.chain (ChainVM.watch w)) :
    ReachesWatchPhase P q first cP sP ∨
      ∃ (es : List Bool) (c' : Control) (s' : GalilVM),
        WatchSegE P q first 2048 es cP sP c' s' ∧ SegEnd P c' s' ∧
        c'.mode = Mode.scan ∧ c'.replaying = false ∧ CopyOrBack s'.chain := by
  obtain ⟨es, c', s', hSeg, hMode', hRep', hClock', hEnd⟩ :=
    watchSegE_constructLive P q first 2048 (by norm_num) (2 * h + 2) cP sP hScan hNotReplaying
      hClock hPhase hLag
  rcases hEnd with hWatch | ⟨hPhase', hLag', hLenOrEnd⟩
  · exact Or.inl ⟨es, c', s', hSeg, hWatch⟩
  · rcases hLenOrEnd with hLen | hSegEnd
    · obtain ⟨w, hTicks⟩ := hChainReachesWatch es hLen
      obtain ⟨hSegTicks, -⟩ :=
        watchSegE_events P q first 2048 hSeg (copyOrBack_not_idle hPhase)
      exact Or.inl ⟨es, c', s', hSeg, w, chainTicks_unique hSegTicks hTicks⟩
    · exact Or.inr ⟨es, c', s', hSeg, hSegEnd, hMode', hRep', hPhase'⟩

/-- **節 4 の正しい形まで**（到達した側）。 -/
theorem prepLandingWatchC_or_segEnd (P : Shared) (q : ℕ) (first : Fin 9) (h : ℕ)
    {cP : Control} {sP : GalilVM}
    (hScan : cP.mode = Mode.scan) (hNotReplaying : cP.replaying = false)
    (hClock : 1 ≤ cP.clock)
    (hPhase : CopyOrBack sP.chain) (hLag : LagPos sP.chain)
    (hChainReachesWatch : ∀ es : List Bool, es.length = 2 * h + 2 →
      ∃ w : GalilScaffoldChainWatch.State, ChainTicks es sP.chain (ChainVM.watch w))
    (hShort : ∀ (c2 : Control) (s2 : GalilVM),
      (∃ es : List Bool, WatchSegE P q first 2048 es cP sP c2 s2) →
      ∀ (es' : List Bool) (c3 : Control) (s3 : GalilVM),
        WatchSegE P q first 2048 es' c2 s2 c3 s3 → es'.length < c2.clock) :
    (∃ (es : List Bool) (c2 : Control) (s2 : GalilVM),
        WatchSegE P q first 2048 es cP sP c2 s2 ∧
        PalPeg.CloseoutWatchRound7.PrepLandingWatchC P q first c2 s2) ∨
      ∃ (es : List Bool) (c' : Control) (s' : GalilVM),
        WatchSegE P q first 2048 es cP sP c' s' ∧ SegEnd P c' s' ∧
        c'.mode = Mode.scan ∧ c'.replaying = false ∧ CopyOrBack s'.chain := by
  rcases reachesWatchPhase_or_segEnd P q first h hScan hNotReplaying hClock hPhase hLag
    hChainReachesWatch with hReach | hEnd
  · exact Or.inl (prepLandingWatchC_at_reachedWatch P q first hReach hShort)
  · exact Or.inr hEnd

#print axioms reachesWatchPhase_or_segEnd
#print axioms prepLandingWatchC_or_segEnd

end PalPeg.ReachesWatchFromRun
