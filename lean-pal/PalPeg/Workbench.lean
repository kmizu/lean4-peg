-- 1. 正本の残り壁に直接効きそうな部品（最優先で配線を試す）
import PalPeg.CloseoutBirthFrame
import PalPeg.CloseoutBranchRes
import PalPeg.CloseoutCandOrient
import PalPeg.CloseoutClockFront
import PalPeg.CloseoutLagAll
import PalPeg.CloseoutLaterEntry
import PalPeg.CloseoutRestartShape
import PalPeg.CloseoutRightBounds
import PalPeg.CloseoutSegCheckpoint
import PalPeg.CloseoutSegment
import PalPeg.CloseoutStageFree
import PalPeg.CloseoutStageLanding
import PalPeg.CloseoutWalkerSupply
import PalPeg.CloseoutWalkerTick
import PalPeg.CloseoutWatchRound26
import PalPeg.CloseoutWatchRound53

-- 2. 最上位の別系列（前提の数え直しに使う）
import PalPeg.CloseoutCoreEnc24
import PalPeg.CloseoutFinalW5
import PalPeg.CloseoutWatchRound51
import PalPeg.CloseoutWeakFinal

-- 3. 記録（回帰テストと反証の記録）
import PalPeg.CloseoutPeriodOnlyRegression
import PalPeg.CloseoutPresRefute

-- 4. `hC`（局所実現）の供給元として書かれた層 — 未配線
import PalPeg.ClockRecycleTrace
import PalPeg.DecompUniform
import PalPeg.DualQueueMachine
import PalPeg.FiniteMatcherBank
import PalPeg.FinitePrepBank
import PalPeg.HistoryArrival
import PalPeg.HistoryReadyInput
import PalPeg.InputEmbed
import PalPeg.LocalAlloc
import PalPeg.LocalArrivalTiming
import PalPeg.MeteredX
import PalPeg.PassSum4
import PalPeg.PatternPairProg
import PalPeg.PointwiseGap
import PalPeg.RTQueueCalls
import PalPeg.ReplayCyclePadded
import PalPeg.ReplayDrain
import PalPeg.StageTapesX
import PalPeg.StageTapesZ
import PalPeg.TextFeedInput
import PalPeg.TextFeedPipelineBacklog
import PalPeg.TextFeedPipelineBirthInput
import PalPeg.TextFeedPipelineFeedBody
import PalPeg.TextFeedPipelineInputObservations
import PalPeg.TextFeedPipelinePrefixFedSetup
import PalPeg.TextFeedPipelineRecycle
import PalPeg.TextFeedPipelineReplay
import PalPeg.TextFeedPipelineSlots
import PalPeg.TextFeedScan
import PalPeg.TextFeedStageDeadline
import PalPeg.VerifierFeedCompare
import PalPeg.VerifierFeedMachine
import PalPeg.VerifierFeedZ

-- 5. `Galil*` の未配線部品
import PalPeg.GalilBreakNoBelow
import PalPeg.GalilFppPrefix
import PalPeg.GalilFppRunSupply
import PalPeg.GalilFppWriteOnce
import PalPeg.GalilLeafFb
import PalPeg.GalilLeafStartShape
import PalPeg.GalilScaffoldPrepareClock
import PalPeg.GalilScaffoldStructured
import PalPeg.GalilSourceCost
import PalPeg.CloseoutFinalVer
import PalPeg.CloseoutFinalBranch
import PalPeg.MatchedRunSnoc
import PalPeg.ShiftPhaseDeterminism
import PalPeg.RoundSegFromRun
import PalPeg.ShiftPalAlongTrace
import PalPeg.FoundPackRefute
import PalPeg.FoundPackCorrected
import PalPeg.CopyPhaseTick
import PalPeg.CopyPhaseTickMatched
import PalPeg.AnswerAheadDecode
import PalPeg.ChainReachesWatchFromFound
import PalPeg.LiveSegmentConstruct
import PalPeg.ReachesWatchFromRun
import PalPeg.CopyPhaseNoShift

/-!
# `Workbench` — 作ったが正本の鎖に配線されていない部品

## このファイルの役割

`PalPeg/` は 1143 モジュール・331,884 行・定理 12,613 本ある。そのうち**正本
`PalPeg.Canonical`（→ `given_globalScanLandings_and_fourOther`）の推移 import 閉包は 526 本**で、
残り 617 本は正本に効いていない。しかし**「効いていない」と「無関係」は違う**。
実際、未登録・未参照のまま健全だった部品を回収した（`CloseoutPackRun49` の
`LPackM3`、`CloseoutWatchRound53`、`CloseoutRealize1`）。

そこで根を 2 本に分ける。

* `PalPeg.Canonical` — 正本の鎖。意味のある別名つき。`lake build PalPeg.Canonical`
  で正本だけを速くビルドできる。
* `PalPeg.Workbench`（このファイル）— 作ったが未配線の部品。**主定理
  `RecognizedByTotalPEG PAL` との関係を層ごとに明記する。**

上の 64 本の import で、再編前の `PalPeg.lean` が持っていた 1101 本を 1 本も落とさず
覆う（機械照合済み：新根の閉包 1135 ⊇ 旧登録 1101、欠落 0）。

**デッドコードかどうかは主定理との関係でしか判定できない。** 誰も import して
いないこと・名前が参照されていないことは、削除の根拠にならない。削除したのは
`Probe1`（`attribute [ext]` と `#check` と自明な `example` だけ、定理 0、未登録）1 本。

## 1. 正本の残り壁に直接効きそうな部品

`final30` の 8 前提は 4 壁（`hSP` `hme` `hor` `hC`）＋ 4 供給
（`hfour` `hbgP` `hmatchP` `hsdP`）。以下はその壁に触れている：

* `CloseoutClockFront` — front ポテンシャル `pot` と `front_le_of_run`、
  **`canRight_of_run`** / **`extra7_of_run`**。`hee`/`het` を消したのと同じ機構で、
  `LandingReadyC` が要求する `canRight s.right` の供給元になり得る。
* `CloseoutWatchRound53` — `wrel_run`、`watchTailC_of_coreX`、`good_of_pos`。
  `good_of_pos` は `ChainW`（窓つきの束）から `Good` を出す。**`WatchOk` 自体は
  2026-09-19 に無条件で反証された**（`PalPeg.WatchOkRefute.watchOk_false`）ので、
  `WatchOk` のインスタンスを作る道ではなく、`ChainOk` を lag/margin を縛る形に
  再設計するときの `Good` 供給元として使う。
* `CloseoutLagAll` — `LagAll`（step/matched/idle/broken で閉じる）と `lagAll_lagCan`。
  `LagCan` は `LPackM3` の場なので、無条件化の候補。
* `CloseoutSegment` — `ScanToScan`（run の区間分解）。`hSP` のラウンド境界と
  `hor` の found 葉がここに帰着する、と台帳が指している壁。
* `CloseoutBranchRes` — `chainPosInv_steps_res` / `shiftLocalS_of_run_res`。
  `H_FourSemiperiodsLeDistance` の消費者 `watchShiftS_of_chainPosInv` が要求する `ChainPositionInvariant` の run 搬送。
* `CloseoutRightBounds` — 右ヘッドの上界（`rightInBounds`）。`canRight` 系の義務。
* `CloseoutWalkerSupply` / `CloseoutWalkerTick` — `hme` の `walkerInOrigin_of_run` の
  側義務 `hcan` と walker 不変量の tick 保存。
* `CloseoutSegCheckpoint` / `CloseoutStageFree` / `CloseoutStageLanding` /
  `CloseoutLaterEntry` / `CloseoutRestartShape` / `CloseoutWatchRound26` /
  `CloseoutCandOrient` — `hor`（oracle）の葉と区間構成。
* `CloseoutBirthFrame` — `hbirth_PofC`（`M-periodOnly` 修正の側条件を具体 `PofC` で放電）。

## 2. 最上位の別系列

`pal_in_peg_final*` は 48 本あり、番号は「いつ書いたか」でしかない。反証済みの前提を
含まない中で前提が最少なのがどれかは、**型を実際に見て**判断する
（Prop 引数の本数＝前提の本数ではない）。ここはその比較対象。

型を確認済みの比較表（2026-09-19）:

| 定理 | 前提数 | 偽の前提 | 機械検査 |
|---|---|---|---|
| **`CloseoutFinalFour.given_globalScanLandings`** | **7** | **なし**（正本、`Canonical` 参照） | — |
| `CloseoutFinalBranch.given_landingObligationsAlongRun` | 6（Prop 引数） | なし。ただし `hB` は**4 義務の束**なので義務の実数は 9。前進は「global → run 形」の弱化であって本数の削減ではない | — |
| `CloseoutFinalBranch.given_landingObligationsSansRadiusLedger` | 6（Prop 引数） | なし。`final41` の `hB` から**半径台帳を放電**した版（`RadLedger` は `radLedger_pt` で trace 全点にタダ）。残る `shiftCan` は `canRight s.right` のみ | — |
| `CloseoutFinalBranch.given_scanLandingObligations` | 6（Prop 引数、うち `h4 : first ≠ 4` は `by decide`） | なし。**`shiftDone` 義務を完全に放電**（半径台帳 ＋ `canRight` の両方が新規入力ゼロ）。2026-09-19 に **`hme` も放電**（`CloseoutMarksPack.packRunR_MW_marksFree`）。残差は `ScanLandingObligationsAt` の 3 場（`bg`/`matchLand`/`entryLand`）＋ `hver` | — |
| `CloseoutFinalW.given_globalScanLandings_and_fourOther` | 8 | なし（一代前、`hfour` を含む） | — |
| `CloseoutFinalVer.given_globalRun41Landings_and_verifierRun` | 9 | なし | — |
| `CloseoutFinalS2.given_consumeAvailEverywhere_FALSE_HYP` | 9 | `hav` | `ConsumeAvailRefute.hav_false` |
| `CloseoutFinalW3.given_chainPackAtAnyState_andMore_FALSE_HYP` | 5 | `hpack` | `CloseoutPackRefute.hpack_false` |
| `CloseoutFinalW4.given_chainPackAtAnyState_FALSE_HYP` | 4 | `hpack` | 同上 |

## `MatchedRunSnoc` — run を tick ごとに積むための部品（未配線）

| 定理 | 内容 |
|---|---|
| `onlyMatchedRun_snoc` | `OnlyMatchedRun` に一致比較 1 手を**末尾**から足す |
| `onlyMatchedRun_head` | 先頭 1 手を剥がす |
| `onlyMatchedRun_trans` | 2 本を連結 |
| `matchedSeq_snoc_background` | `MatchedSeq` に background 量子を末尾から足す（カウント不変） |
| `matchedSeq_snoc_compare` | `MatchedSeq` に一致比較を末尾から足す（カウント +1） |
| `scanSeg_snoc_wait` / `_count` / `_match` | `ScanSeg`（制御つき）を末尾から伸ばす 3 本 |
| `compare_matched_parts` | `compareFound` ＋ `matched` ＋ watch から `galilFrame` 側の比較と `afterCompare` を取り出す |
| **`scanSeg_snoc_tick`** | **run の 1 tick を `ScanSeg` に吸収する。出口は 3 つだけ: 伸びる / mode が scan を離れる / chain が watch でなくなる** |
| `restartNeedsBroken_of_restartVM` | `scanSeg_snoc_tick` の側条件を具体枠で放電 |

**主定理との関係**: `obligation_shiftPalAtScanStates` の残差は
`CloseoutRoundSeg` によれば `RoundSeg`（＝`CompareRounds h _ 1 _`）と `H_fresh` の
2 つで、どちらも `GalilScaffoldTopRoundS.round_next` /
`GalilScaffoldTopFirstRound.first_round` が要求する **`ScanSeg`（run の区間）** を
作れるかに帰着する。区間を run から抽出するのが CLAUDE.md §1 の壁 (1)（`ScanToScan`）。

`MatchedSeq` は `count`（background）と `compare`（一致比較）から成る run 上の
inductive で、**`Tick` の `scan_wait` / `scan_count` / `scan_match` と 1 対 1 に対応する**。
ただし前からしか積めないので、run を歩きながら積むには末尾伸長が要る。それがこの 5 本。
これがあれば `CompareRounds.next` の `OnlyMatchedRun` 引数は区間抽出なしで手に入る。

| `scanSeg_of_steps` | scan ＋ watch の区間に沿って `ScanSeg` が伸びる |
| `onlyMatchedRun_of_steps` | その末尾で下層の `OnlyMatchedRun`（`CompareRounds.next` の第 1 引数） |
| `compare_mismatched_parts` | 不一致比較 tick の分解（ラウンド境界用） |

## `ShiftPhaseDeterminism` — shift 相は `Fair` なしで決定的（未配線）

| 定理 | 内容 |
|---|---|
| `refresh_det` | 出力の更新は一意 |
| `shiftOne_det` | 1 単位の shift は行き先を一意に決める |
| `tick_shift_det` | shift 相の tick は一意（`Tick` の 24 構成子を両側で潰した） |
| `steps_shift_det` | 中間が全部 shift 相なら同じ長さの 2 本の run は同じ状態に着く |
| **`steps_shift_exit_unique`** | **shift 相の出口は状態も長さも一意（長さを仮定しなくてよい）** |
| `tick_shift_keeps_ctl` | 残り歩数が正な shift tick は制御を変えない（`shift_done` が使えないから） |
| `steps_shift_mode_of_remaining` | 残り歩数が正な限り mode は shift のまま（guard の出どころ） |
| **`shift_landing_eq`** | **構成した着地と run の実際の着地は一致（仮定は `remainingPos` だけ、`Fair` 不要）** |

**主定理との関係**: `round_next` はラウンド 1 周を**構成**して `Steps` と
`CompareRounds h (toOnly s w0) 1 (toOnly (構成した着地) v)` を返す。`RoundSeg`
（したがって `OriginAt` の搬送）に使うには構成した着地と run の実際の着地を
同一視する必要があり、その差は **shift 相だけ**（scan 側は
`onlyMatchedRun_of_steps` が実際の状態で直接出す）。shift 相は無条件に決定的なので、
`Fair` を持ち出さずに同一視できる。

## `RoundSegFromRun` — `RoundSeg` / `OriginAt` を run の実際の状態で（未配線）

| 定理 | 内容 |
|---|---|
| `roundSeg_of_compareRounds` | `RoundSeg` は `CompareRounds` の包み（周期長の一致だけが中身） |
| `compareRounds_at_actual` | 構成した着地での `CompareRounds` を run の実際の着地へ移す |
| `roundSeg_at_actual` | 上の合成 |
| **`originAt_at_actual`** | **`OriginAt` がラウンドを 1 つ越える（run の実際の状態で）** |
| **`readsShift_at_actual`** | **`H_readsShift` を run の実際の状態で（新しい名前付きの葉ゼロ）** |

**主定理との関係**: `H_readsShift` の唯一の供給元は
`CloseoutReadsOrigin.h_readsShift_of_originAt`（`OriginAt w s → H_readsShift w c s`）で、
`H_readsShift` は `CloseoutBundleRun.shiftPal_of_run_B` の 2 つの残差のうちの 1 つ
（もう 1 つは `H_freshShift`）。`shiftPal_of_run_B` は `hSP`
（＝ `obligation_shiftPalAtScanStates`）そのもの。

段差は shift 相だけで（scan 側は `onlyMatchedRun_of_steps` が最初から実際の状態で出す）、
`ShiftPhaseDeterminism.shift_landing_eq` が `Fair` なしで埋める。

`readsShift_at_actual` の鎖（新しい名前付きの葉はゼロ）:

    OriginAt（前ラウンド起点）
      → roundSeg_at_actual（shift 相の決定性で実状態へ）
      → CloseoutReadsOrigin.originShift_of_roundSeg
      → CloseoutReadsOrigin.h_readsShift_of_originShift
      → H_readsShift

**残り**: (a) `OriginAt` を「いまのラウンド起点で」持つ run 不変量に仕立てる
（ラウンド境界で `originAt_at_actual` を使う）、(b) `round_next` の入力の配線、
(c) `H_freshShiftAtShiftEntry`（新鮮な chain の第 1 ラウンド、`first_round`）。

## `FoundPackRefute` — `foundExit_compare_final20` の `hpack` は **REFUTED（条件付き）**

| 定理 | 内容 |
|---|---|
| `chainMatched_copy_stays_copy` | `ChainMatched` は `.copy` から `.copy` にしか行かない |
| `chainStart_is_copy` | `chainStart` は `.copy`（`rfl`、公理ゼロ） |
| `chainTick_copy_not_watch` | **誕生直後の chain は 1 tick でも watch にならない**（`ChainStep` に `.copy → .watch` が無い） |
| `prepLandingLiveC_watch_start` | `PrepLandingLiveC` も watch 始点を強制する |
| `prepLandingLiveC_false_of_foundCompareCtx` | `PrepLandingLiveC` も found 比較直後で偽 |
| **`hpack_false_of_foundCompareCtx`** | **`FoundCompareCtxC` の証人 ＋ `PrepLandingWatchC` から `False`** |
| **`hpack_false_of_foundReachable`** | **`InvLPC` ＋ `SegReachedW` ＋ found 比較から `False`（証人は `foundCompareCtxC_of_found` が作る）** |

`hpack` の 4 番目の節 `PrepLandingWatchC` は `WatchSegE.stop` の `es = []` 実例で
`∃ w, sP.chain = .watch w` を強制する（`CloseoutWatchRound8.prepLandingWatchC_watch_start`）。
一方 guard の `FoundCompareCtxC` は `sP.chain = ch` で `ChainMatched (chainStart …) ch`。
`chainStart` は `.copy` で、`ChainMatched` の構成子は形を保つ 1 歩の関係
（`.copy → .copy` / `.back → .back` / `.watch → .watch` / `.watch → .broken`）なので
`ch` は必ず `.copy`。**両立しない。**

**`REFUTED（条件付き）`**——未構成の証人は `FoundCompareCtxC`
（`WatchSegE` / `searchEffect` / `refresh` の証人が要る）。

`PrepLandingWatchC` 自身は偽ではない（chain が watch になった後の landing では真、
producer は `CloseoutWatchRound10.prepLandingWatchC_of_short`）。**束ねる場所が間違っている。**
`hpack` という名前は `CloseoutPackRefute.hpack_false` で既に一度偽になっており、
`LandingFreshC` も Round 44 で反証されて `LandingFreshC'` に割られている——
**同じ場所で同じ種類の誤りが 3 回**。

`CloseoutFoundRoute1` は**壊れていたので直した**（2026-09-19）。`:238` の `StepsAll.zero`
型不整合は、モデル修正 `M-periodOnly` で比較の行き先が `afterBirth true (…)` になったのに
着地状態が `afterCompare …` のままだったため。`afterBirth` はヘッドを触らないので
`OutputRel` / `ScanInvariant` / `chain` はすべて congruence で移る。
これで `foundCompareCtxC_of_found`（`FoundCompareCtxC` の producer）が使えるようになり、
上の到達可能性込みの反証が書けた。

## `FoundPackCorrected` — `PrepLanding*` の正しい形（`∀` → `∃`、未配線）

| 定理 | 内容 |
|---|---|
| `ReachesWatchPhase`（def） | **誕生から watch 相に到達する区間が「ある」**（存在形） |
| **`prepLandingWatchC_at_reachedWatch`** | **到達先では `PrepLandingWatchC` が正しく成り立つ**（`prepLandingWatchC_of_short` を当てる） |
| `watchSegE_match_needs_only_nonIdle` | `WatchSegE` の `match` は `chain ≠ .idle` しか要求しない（copy/back 相も区間に載る） |
| `BreakLandingAtReachedWatch`（def） | 節 7（`BreakLandingC`）の `∃` 版 |
| **`reachesWatchPhase_of_breakLandingAtReachedWatch`** | **節 7 の正しい形は節 4 の正しい形を含意する**（供給は 1 本で足りる） |
| `not_shiftGuardVM_of_not_watch` | watch でなければ shift guard は立たない |
| `guardNeedsWatch_PofC` | 具体枠では `shiftGuard = shiftGuardVM` で watch を要求 |
| **`no_shift_from_copyChain`** | **誕生直後（`.copy` 相）の scan 状態からは shift に行けない**（不一致が来ても `scan_fallback`） |
| **`reachesWatchPhase_of_chainTicks`** | **橋: 区間の chain trace が watch に着くなら `ReachesWatchPhase`**（`watchSegE_events` ＋ `chainTicks_unique`） |

**`ReachesWatchPhase` に残るのは区間の長さだけ。** `found_to_watchStart_least` が
任意の長さ `h` / `h+1` のイベント列について `ChainTicks (bs ++ dm :: cs) x1 (.watch …)` を
与えるので、run が誕生からその長さの `WatchSegE` を走れば終端は watch。
**chain の中身はもう一切残っていない**——純粋な予算・スケジュールの問題になった。

**訂正（n125）: `reachesWatchPhase_of_backgroundRun` の `hClock : n < cP.clock` は強すぎた。**
`watchSegE_backgroundRun_live` が `.count` / `.wait` だけで区間を作るので、
`delay = 2048` の下では background だけで走れるのは 2047 手、つまり `2h+2 < 2048`
（`h ≤ 1022`）の準備に限られる（`GalilScaffoldTopWatchSegE.lean:26,33`）。

**ただし「無条件形は成り立たない」まで言ったのは考えすぎだった。**
idle chain 版 `GalilSegmentConstructB.watchSegE_constructB` は `n < c.clock` を
**要求していない**——clock を構成の中で処理し、結論は既に `es.length = n ∨ SegEnd P c' t`
という 2 択になっている。live 版も同じ形でよく、唯一足りなかった部品が
「一致事象で chain が 1 手進める」＝ `CopyPhaseTickMatched.copyOrBack_tick_true_exists`。
できたのが `LiveSegmentConstruct.watchSegE_constructLive` と
`ReachesWatchFromRun.reachesWatchPhase_or_segEnd`（下）。

**壊れていたのは結論の量化子だった。** `PrepLandingWatchC` は

    ∀ es c2 s2, WatchSegE … cP sP c2 s2 → （c2 s2 で watch）

で、`WatchSegE.stop cP sP` が無条件に存在するため `sP` 自身が watch であることを
強制する。誕生直後の chain は `.copy` なのでこれは偽（`FoundPackRefute`）。
`WatchSegE` の側は壊れておらず copy/back も素通しできるので、正しいのは

    ∃ es c2 s2, WatchSegE … cP sP c2 s2 ∧ （c2 s2 で watch）

**`∀ → ∃` の付け替えは要求を空虚に弱めたのではなく、量化子の位置を直したもの。**
到達先では既存の producer がそのまま効く。

## `CopyPhaseTickMatched` — 一致事象でも copy/back の `ChainTick` はある（未配線）

| 定理 | 内容 |
|---|---|
| `zero_false_of_positive` / `positive_inc` | 正値カウンタの基本（**`zero` の否定では `inc` で保たれない**: `⟨[], [()]⟩` の `inc` は `reset`） |
| `LagPos`（def） | chain の lag が正（`.copy` / `.back` 相でだけ内容がある） |
| **`lagPos_tick`** | **`LagPos` は 1 tick で保たれる**（事象によらず） |
| `lagPos_chainStart` / `lagPos_of_chainMatched_chainStart` | 誕生時の lag は `radius = ofNat (r0+1)` で正 |
| `chainStep_back_shape'` | `.back` の 1 手は lag を保った `.back` か lag を受け継いだ `.watch` |
| **`backChain_tick_true_exists`** | **`.back` 相でも一致事象の `ChainTick` は存在する**（lag 正のとき） |
| **`copyOrBack_tick_true_exists`** | **`CopyOrBack` ＋ lag 正なら一致事象でも 1 手ある** |
| **`copyOrBack_tick_true`** | **一致事象でも相は copy/back か watch に閉じる**（`breaks` は lag 正で排除） |

**以前 `sorry` を書きかけた場所の本当の障害はここだった。** `.back` から `backDone` で
生まれた watch に `ChainMatched` を当てるには `Outer w true w'` が要り、その 2 枝は
`queued`（`zero w.lag = false`）と `immediate`（`zero w.lag = true` ∧ `Good w`）。
`Good` は誕生時には出ない（`WatchOkRefute.watchOk_false`）。しかし
**誕生した chain の lag は正**（`chainStart … radius` が `lag = margin = radius`、
copy/back の `ChainStep` は lag を触らず `ChainMatched` は `inc` するだけ）なので
`Outer.queued` が無条件に使え、`Good` は要らない。同じ正値が `ChainMatched.breaks`
（`BreakStep` は `zero w.lag = true` を要求、`GalilScaffoldTopChainVM:27`）も排除する。

**不変量は `positive` で書くこと。** `zero lag = false` では `inc` で保たれない。

## `ChainReachesWatchFromFound` — `hChainReachesWatch` の供給（未配線）

| 定理 | 内容 |
|---|---|
| **`chainReachesWatch_of_found`** | **found 文脈から「長さ `2h+2` の任意のイベント列で watch に着く」** |

`found_to_watchStart_least` の `dm` は**引数**なので、`list_split_mid` が出す実際の
中央要素ごとに定理を当て直す。そのとき `h` が揺れないことを保証するのが
`hCursor : (denote y.config).pos 11 = h`（DP 出力カーソル）。**これが無いと `h` の
一意性が言えず、「長さ `2h+2`」という主張そのものが `dm` 依存になって壊れる。**
誕生した chain と `chainStart` の同一視は `chainMatched_unique`。

## `LiveSegmentConstruct` / `ReachesWatchFromRun` — clock の余裕なしの区間構成（未配線）

| 定理 | 内容 |
|---|---|
| `LiveSegmentConstruct.match_step_live` | 一致比較 1 手分の証人（`WatchSegE.match` の側条件をすべて作る） |
| **`LiveSegmentConstruct.watchSegE_constructLive`** | **live chain 版の区間構成。`n` 手走破 ∨ `SegEnd`。clock の余裕は不要** |
| **`ReachesWatchFromRun.reachesWatchPhase_or_segEnd`** | **`ReachesWatchPhase` ∨ `SegEnd` で早期終了** |
| `ReachesWatchFromRun.prepLandingWatchC_or_segEnd` | 節 4 の正しい形まで（到達した側） |

探索側の帳簿（`ReadyFuel` / `hsearch`）は live chain では**丸ごと不要**——
`searchEffect P a s v` は `s.chain ≠ .idle` の枝で `v = searchLens.get s` に潰れ、
`chainBorn` も `false` になるので誕生も起きない。`SegEnd` の 5 枝のうち live で
実際に出るのは `.mismatch` だけ。

**残る配線**: found 文脈から 3 入力を作る（`CopyOrBack` ← `copyOrBack_of_chainMatched_chainStart`
＋ `copyInv_of_found`、`LagPos` ← `lagPos_of_chainMatched_chainStart`、
`hChainReachesWatch` ← `chainReachesWatch_of_found`）。`FoundCompareCtxC`
（`CloseoutWatchRound2:270`）が材料を持っている。**残る側条件は `sF.radius = ofNat (r0+1)`**
（`found_to_watchStart_least` が `ofNat (r0+1)` 形を、`LagPos` が `positive sF.radius` を要求）。

## `ShiftPalAlongTrace` — `hSP` の正しい形（trace 形、未配線）

| 定理 | 内容 |
|---|---|
| `chainIdle_after_init` | `init` の行き先は chain が idle（`initVM` が置く） |
| `roundBundle_alongTrace` | `RoundBundle` を trace に沿って（`st 1` から） |
| **`shiftPal_alongTrace`** | **`ShiftPal` を trace の scan 点で** |

**主定理との関係**: 公理 `obligation_shiftPalAtScanStates` は一状態述語
`BigPack2MG7W` の下で `ShiftPal` を要求していたが、その guard は chain の周期テープと
入力語 `w` を一切結びつけていない（n112、**偽の疑いが濃い**）。`shiftPal_alongTrace` が
正しい形で、残差は 3 つだけ:

| 残差 | 形 | 出どころ |
|---|---|---|
| `H_readsShift` | trace 形 | `RoundSegFromRun.readsShift_at_actual`（実状態で出る） |
| `H_freshShiftAtShiftEntry` | tick 形 | 狭めた版、`GalilScaffoldTopFirstRound.first_round` |
| `hFreshBranch`（`periodOnly = false`） | 状態ごと | 同上 |

`AuxPack`（`auxPack_alongTrace_afterFirstStep`）と `canRight`
（`canRightAtScanOrShift_alongTrace`）は中で放電済み。起点が `st 1` なのは
`AuxPack` が boot では偽だから（`AuxPackNotAtBoot`）で、`st 1` の chain が idle なのは
`initVM` が `t.chain = .idle` を置くから。

## `H_freshShift` を消費者の scope に狭めた（2026-09-19）

`CloseoutPackRun37.H_freshShift` は「`periodOnly = false` の状態からの**任意の** tick」に
`ShiftInv` を課していたが、唯一の消費者 `shiftRound_tick` はそれを `scan_shift` 分岐の
`periodOnly = false` 側でしか使わない。広い版は fresh chain が `.watch` になった直後
（`chainStart` が `cycle` を reset した点）で `ShiftInv.count : value cycle = 2k` を
満たせないので**偽の疑いが濃い**（機械検査した反証はまだ無いので `REFUTED` とは書かない）。
**過剰量化の 12 例目。**

`CloseoutPackRun37.H_freshShiftAtShiftEntry` が狭めた版で、shift 入口——比較が不一致で
shift guard が立ち `beginShift` が着く——でだけ主張する。これは
`CloseoutReadsOrigin:140` の既存の測定（「fresh chain の第 1 shift は `used = 2h-1`、
`WatchSeg` の掃引の後で起きる」）と一致し、`GalilScaffoldTopFirstRound.first_round` の
結論が出る場所とも一致する。

差し替えたのは `shiftRound_tick`（`CloseoutPackRun37`）と `shiftRound_tick_A`
（`CloseoutAdvanceT`）、および供給側の `CloseoutBundleRun` / `CloseoutRoundBundle` /
`CloseoutReadsOrigin`。全体 build 成功。

**`scanSeg_snoc_tick` で tick 補題は済んだ**（標準 3 公理）。残るのは、これを run 不変量
（「いまの状態はあるラウンド起点から `n` 手の一致比較で到達した」）に仕立てて、
ラウンド境界（`scan_shift`）で `CompareRounds.next` を組む部分。

**`CloseoutSegment.ScanToScan` は要らないかもしれない。** あのファイルは
「`SpanRep` は `ScanToScan` の下流」と書いていたが、`SpanRep` は 2026-09-19 に
`BranchSupply.spanRepOnScanAndShift_alongTrace` で **tick ごとに**証明できた。
`RoundSeg` も同じで、区間を抽出せずに tick ごとに積めば足りる公算が大きい。
なお `ScanToScan` は「任意の scan→scan 健全 run が `ScanSeg` ＋ `Rounds` に分解する」
と全称量化しており、`ScanSeg.match` が `hwatch`（chain が watch）を要求する一方で
idle chain の一致比較も合法な tick である以上、**偽の疑いが強い**
（機械検査した反証はまだ無いので `REFUTED` とは書かない）。

`CloseoutFinalVer.given_globalRun41Landings_and_verifierRun` は前提数では `final39` に劣るが、**残す**:
分岐前提が Run41 系（`H_BackgroundLandingChainLedger` / `H_MatchLandingChainLedger` / `H_ShiftEntryChainLedger` / `H_ShiftExitRadiusLedger`）で、
`CloseoutPackRun48` の 4 放電器（`h_bgP2_of_supply` / `h_matchP2_of_target` /
`h_shiftEntry2_of_target` / `h_shiftDoneRad2_of_supply`）が効く**唯一の**経路。
`final39` の 3 本を落とすにはこちらを詰めることになる。ただし Run48 の放電器の入力は
まだ「任意の scan 状態 ＋ `ChainPositionInvariantWithShiftPhase`」形なので、run 形（`VerRun` と同じ形）に
直す必要がある。

## 3. 記録

`CloseoutPeriodOnlyRegression` は `M-periodOnly` 修正の回帰テスト、
`CloseoutPresRefute` は `hpres` が debt 0 で破れることの機械検査済み記録。
どちらも誰も import しないが、**消すと監査の根拠が消える**。

## 4. `hC`（`H_realizeLIMW'`＝局所実現）の供給元として書かれた層 — 未配線

層ごとに主定理の閉包との関係を実測した結果：

| 層 | 閉包内 | 閉包外 |
|---|---|---|
| `TextFeed*` | **0** | **153** |
| `Prog*` | 6（`Galil*Program*` 系で別物） | **119** |
| `GS*` | **0** | 13 |
| `*Tapes` | 1 | 15 |
| `Middle*` / `*Bank` | 0 | 5 |

**`TextFeed*` 153 モジュールは 1 本も正本に届いていない。** これは「無関係」ではなく
「未配線」。`hC` は未解決の壁であり、この層はまさにその供給元として書かれている。
一方 `CloseoutRealize1.h_realizeSMG2'_of_LIMG2'` は「`LocalStep` の証人は付随的で、
任意の厳密実時間 `StructuredMachine` で足りる」ことを示しており、**この層が本当に
必要かどうかは未判定**。判定せずに消さない。

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/
