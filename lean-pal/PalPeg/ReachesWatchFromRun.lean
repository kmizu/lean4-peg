import PalPeg.LiveSegmentConstruct
import PalPeg.FoundPackCorrected
import PalPeg.ChainReachesWatchFromFound
import PalPeg.CloseoutPreload5

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


/-! ## found 誕生点での組み立て

`FoundCompareCtxC`（`CloseoutWatchRound2:270`）は誕生を

    ChainMatched (chainStart (vq.dp.config.tapes 11) (P.centre sF) (P.place sF)
      sF.center sF.radius) ch  ∧  sP = afterBirth true (afterCompare sF ⟨…, ch⟩ vq)

の形で持っている。そこから `reachesWatchPhase_or_segEnd` の 3 入力が全部出る:

| 入力 | 出どころ |
|---|---|
| `CopyOrBack sP.chain` | `CopyPhaseTick.copyOrBack_of_chainMatched_chainStart` ＋ `AnswerAheadDecode.copyInv_of_found` |
| `LagPos sP.chain` | `CopyPhaseTickMatched.lagPos_of_chainMatched_chainStart` |
| `hChainReachesWatch` | `ChainReachesWatchFromFound.chainReachesWatch_of_found` |

`cP.mode` / `cP.replaying` / `1 ≤ cP.clock` も `FoundCompareCtxC` が持っている
（`cP = {cF with clock := 2048, output := oF, replaying := false}`）。

**残る側条件は誕生時の半径が `ofNat (r0+1)` 形であること**——`found_to_watchStart_least` が
その形を要求し、`LagPos` も lag の正値を要求する。`CloseoutWatchRound7.FoundRadiusCanonC`
（`Canonical sF.radius`）＋ 「found 時の半径は正」（`ASSEMBLY_PLAN` が既存の仮定として
挙げているもの）＋ `CloseoutPreload5.canonical_eq_ofNat` で出るはず。 -/

/-- **found 誕生点で `ReachesWatchPhase ∨ SegEnd`。**  chain 側の入力はすべて
誕生の `ChainMatched` と `CopyInv` から出る。 -/
theorem reachesWatchPhase_or_segEnd_at_foundBirth (P : Shared) (q : ℕ) (first : Fin 9)
    {cP : Control} {sP : GalilVM}
    {answer : GalilScaffoldTape.Tape} {cen : Fin 3}
    {walker : GalilScaffoldPlace.Place} {ver : GalilScaffoldInputHead.PlaceHead}
    {r0 h : ℕ}
    (hScan : cP.mode = Mode.scan) (hNotReplaying : cP.replaying = false)
    (hClock : 1 ≤ cP.clock)
    (hBirth : ChainMatched (chainStart answer cen walker ver (ofNat (r0 + 1))) sP.chain)
    (hCopyInv : PalPeg.GalilBranchInvariants.CopyInv answer reset walker
      (GalilScaffoldChainPeriod.start cen) h)
    (hChainReachesWatch : ∀ es : List Bool, es.length = 2 * h + 2 →
      ∃ w : GalilScaffoldChainWatch.State, ChainTicks es sP.chain (ChainVM.watch w)) :
    ReachesWatchPhase P q first cP sP ∨
      ∃ (es : List Bool) (c' : Control) (s' : GalilVM),
        WatchSegE P q first 2048 es cP sP c' s' ∧ SegEnd P c' s' ∧
        c'.mode = Mode.scan ∧ c'.replaying = false ∧ CopyOrBack s'.chain :=
  reachesWatchPhase_or_segEnd P q first h hScan hNotReplaying hClock
    (copyOrBack_of_chainMatched_chainStart hBirth hCopyInv)
    (lagPos_of_chainMatched_chainStart hBirth)
    hChainReachesWatch

#print axioms reachesWatchPhase_or_segEnd_at_foundBirth


/-! ## 半径の側条件を標準形に

コードベースの他所（`GalilScaffoldChainCredits:63`、`GalilScaffoldChainReady:39`）は
誕生時の半径の側条件を `Canonical radius ∧ 0 < value radius` の対で書いている。
`CloseoutPreload5.canonical_eq_ofNat` でそれが `ofNat (r0+1)` 形に落ちるので、
`reachesWatchPhase_or_segEnd_at_foundBirth` も同じ対で取れるようにする。 -/

/-- `Canonical` ＋ 正値なら `ofNat (r0+1)` 形。 -/
theorem eq_ofNat_succ_of_canonical_pos {c : Counter}
    (hCanonical : Canonical c) (hPos : 0 < value c) : ∃ r0 : ℕ, c = ofNat (r0 + 1) := by
  have hEq := PalPeg.CloseoutPreload5.canonical_eq_ofNat hCanonical (le_of_lt hPos)
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (value c).toNat = n := ⟨_, rfl⟩
  rw [hn] at hEq
  have hSucc : n - 1 + 1 = n := by omega
  exact ⟨n - 1, by rw [hSucc]; exact hEq⟩

/-- **`reachesWatchPhase_or_segEnd_at_foundBirth` の標準側条件版。**  半径は
`Canonical` ＋ 正値で取る（コードベースの他所と同じ形）。 -/
theorem reachesWatchPhase_or_segEnd_at_foundBirth_canonical (P : Shared) (q : ℕ) (first : Fin 9)
    {cP : Control} {sP : GalilVM}
    {answer : GalilScaffoldTape.Tape} {cen : Fin 3}
    {walker : GalilScaffoldPlace.Place} {ver : GalilScaffoldInputHead.PlaceHead}
    {radius : Counter} {h : ℕ}
    (hScan : cP.mode = Mode.scan) (hNotReplaying : cP.replaying = false)
    (hClock : 1 ≤ cP.clock)
    (hRadiusCanonical : Canonical radius) (hRadiusPos : 0 < value radius)
    (hBirth : ChainMatched (chainStart answer cen walker ver radius) sP.chain)
    (hCopyInv : PalPeg.GalilBranchInvariants.CopyInv answer reset walker
      (GalilScaffoldChainPeriod.start cen) h)
    (hChainReachesWatch : ∀ es : List Bool, es.length = 2 * h + 2 →
      ∃ w : GalilScaffoldChainWatch.State, ChainTicks es sP.chain (ChainVM.watch w)) :
    ReachesWatchPhase P q first cP sP ∨
      ∃ (es : List Bool) (c' : Control) (s' : GalilVM),
        WatchSegE P q first 2048 es cP sP c' s' ∧ SegEnd P c' s' ∧
        c'.mode = Mode.scan ∧ c'.replaying = false ∧ CopyOrBack s'.chain := by
  obtain ⟨r0, hRadius⟩ := eq_ofNat_succ_of_canonical_pos hRadiusCanonical hRadiusPos
  subst hRadius
  exact reachesWatchPhase_or_segEnd_at_foundBirth P q first hScan hNotReplaying hClock
    hBirth hCopyInv hChainReachesWatch

#print axioms eq_ofNat_succ_of_canonical_pos
#print axioms reachesWatchPhase_or_segEnd_at_foundBirth_canonical

end PalPeg.ReachesWatchFromRun
