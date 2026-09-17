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

/-!
# `Workbench` — 作ったが正本の鎖に配線されていない部品

## このファイルの役割

`PalPeg/` は 1143 モジュール・331,884 行・定理 12,613 本ある。そのうち**正本
`PalPeg.Canonical`（→ `pal_in_peg_final30`）の推移 import 閉包は 526 本**で、
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
* `CloseoutWatchRound53` — `wrel_run`、`watchTailC_of_coreX`、**`good_of_pos`**。
  `good_of_pos` は `WatchOk.good`（正の lag で `Good`）の内容そのもの。
  `WatchOk` インスタンス不在が `ChainTickable` の壁なので、ここは直接効く。
* `CloseoutLagAll` — `LagAll`（step/matched/idle/broken で閉じる）と `lagAll_lagCan`。
  `LagCan` は `LPackM3` の場なので、無条件化の候補。
* `CloseoutSegment` — `ScanToScan`（run の区間分解）。`hSP` のラウンド境界と
  `hor` の found 葉がここに帰着する、と台帳が指している壁。
* `CloseoutBranchRes` — `chainPosInv_steps_res` / `shiftLocalS_of_run_res`。
  `H_fourOther` の消費者 `watchShiftS_of_chainPosInv` が要求する `ChainPosInv` の run 搬送。
* `CloseoutRightBounds` — 右ヘッドの上界（`rightInBounds`）。`canRight` 系の義務。
* `CloseoutWalkerSupply` / `CloseoutWalkerTick` — `hme` の `walkerInOrigin_of_run` の
  側義務 `hcan` と walker 不変量の tick 保存。
* `CloseoutSegCheckpoint` / `CloseoutStageFree` / `CloseoutStageLanding` /
  `CloseoutLaterEntry` / `CloseoutRestartShape` / `CloseoutWatchRound26` /
  `CloseoutCandOrient` — `hor`（oracle）の葉と区間構成。
* `CloseoutBirthFrame` — `hbirth_PofC`（`M-periodOnly` 修正の側条件を具体 `PofC` で放電）。

## 2. 最上位の別系列

`pal_in_peg_final*` は 47 本あり、番号は「いつ書いたか」でしかない。反証済みの前提を
含まない中で前提が最少なのがどれかは、**型を実際に見て**判断する
（Prop 引数の本数＝前提の本数ではない）。ここはその比較対象。

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
