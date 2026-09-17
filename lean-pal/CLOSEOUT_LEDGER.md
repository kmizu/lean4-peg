# CLOSEOUT_LEDGER — lean-pal 残差台帳

**目的**: 無条件 `PAL ∈ PEG`（`PegSeparation.RecognizedByTotalPEG PalPeg.PAL`）へ向けて、
主経路に残る**意味的義務**だけを一元管理する。ファイル追加・新しい `finalN`・build 成功は、
それ単独では前進として数えない。

**状態区分**

| 区分 | 意味 |
|---|---|
| `OPEN` | 未証明の意味的義務が残っている |
| `REFUTED` | 現在の命題に反例がある。証明対象でなく修正対象 |
| `REFORMULATED` | 命題を適切に変更したが、成立または利用側との接続が未完 |
| `PROVED` | 新命題自体は証明した。最終経路への供給は未確認 |
| `INTEGRATED` | 成立済みの前提から供給でき、主経路で利用され、対応する旧義務が消えた |

**未解消の前提を `H_x → H_y`、構造体フィールド、instance、別 oracle へ移しただけなら `OPEN` のまま。**

基点: HEAD `b70b395`（PR #61）。検証コマンド: `cd lean-pal && lake build --quiet PalPeg`。
`#print axioms` は推移的公理依存の検査であって、引数として置いた前提の成立を検証しない。
最上位定理の**完全な型**を `#check` で確認し、各前提の供給元まで追うこと。

---

## 0. 最上位

`pal_in_peg_final25` — `PalPeg/CloseoutPackRun51.lean`（`final24` + `hbs`/`hls`/`hsl` 供給）。状態 `OPEN`（下記 **8** 前提が未供給）。

前提: `hSP`, `hws`, `hee`, `het`, `hme`, `hsc`, `hor`, `hC`。
`hbs`/`hls`/`hsl` は §2 の通り、木の中の定理で供給済み（`final24` の 11 前提 → 8）。

> 注意: `final13 → final24` の番号の増加は、**義務の減少を意味しない**。多くは
> 同じ義務の再定式化であり、実際に主経路から消えた義務は §2 に列挙したものだけ。

### 8 前提の素性（2026-09-19 の調査で全部割れた）

| 前提 | 種類 | 残り |
|---|---|---|
| `hee` / `het` | **道具あり・検証済み** | `CloseoutClockFront.extra7_of_run` が `CloseoutPackRun46.extra7_steps` を置換して同時に消える |
| `hsc` | **道具あり・検証済み** | `CloseoutInvScanS.replayStage_of_invSS`。`InvS` の replay 枝強化で消費側 1 行が消える |
| `hme` | **道具あり・検証済み** | `hcan`・`hplace` は定理化済み。残りは走行の各 tick が `Fair` を満たすことの監査のみ（`tick_fair_unique` は `GalilTickFair:437` で証明済み） |
| `hSP` | 残差絞り込み済み | `ChainRound` 経由 |
| `hws` | 残差絞り込み済み | `MatchRes2` の未証明成分 4 個 |
| `hor` | **別種** | 葉 15 個。閉 9、進行中 3、未着手 3（`hfound`/`hfoundBg`/`hfoundReplay` の found 経路構成） |
| `hC` | **別種** | `H_realizeLIMG2'` は局所機械の**存在証明**（`∃ Q' Γ' … L, ∀ w, SAccepts ↔ LatchTrue`）。仮定を減らす対象でなく機械を作る対象 |

---

## 1. OPEN（主経路に残る意味的義務）

| ID | 意味 | 現在の宣言 | 供給元 | 利用側 |
|---|---|---|---|---|
| `hSP` | scan 状態での `ShiftPal`（shift 入口の回文性） | `CloseoutPackRun36:712` の引数 | `ChainRound`（`CloseoutPackRun31:183`）→ 残 `H_shiftDone`(閉)/`H_advance`/`H_birth`/`H_fresh`/`H_matched` | `lTickLeaves2_of_shiftPalG` |
| `hws` | `WatchShiftG`（chain–scan 結合） | 同上 | `ChainPosInv2`（`CloseoutPackRun41:215`）+ `Coupled'`（`PackRun40:77`） → 残 `MatchRes2` の `repVmid`/`replayPay`、新規場 `CentreLedger`、`LagCan` | `rShiftNextMG_of_watchShiftG` |
| `hee` | `Extra7` 入口（`mode = scan ∧ ¬replaying → canRight right`） | `CloseoutPackRun46:284` | 残差は **1 つ**: `∀ c r, InvLPC w c r → position r.right ≠ 2*w.length`（`extraEntry7_of_end`）。**真偽が未確定で、偽の疑いが強い**: `Inv`（`GalilRunInv:29-49`）の 10 場のうち右ヘッドに触れるのは `input : Represents r.right.head raw` だけで、これは内容を縛るが**位置を縛らない**。入力を食い切った状態（`Tick.scan_wait` が回る状態）でも全場が成立しうる。攻め口は (a) `w = []` で `2*w.length = 0` と初期位置 `0` が一致する反例、(b) `InvLPC` への右ヘッド余裕場の追加（`hsc` と同じ再切り出し）。 | `bigPack2MG7''_tick` |
| `het` | `Extra7` tick | `CloseoutPackRun46:296` | 残差は **1 つ**: `(mode ≠ scan ∨ clock = 1) → y.mode = scan → ¬y.replaying → canRight y.vm.right` | 同上 |
| `hme` | `H_marksEntry'`（rewind 角） | `CloseoutPackRun16:165` | `h_marksEntry'_of_layout` → `marksEntry'_of_run`（`PackRun17:387`）。4 入力のうち **`hcan` は定理化済み**（`CloseoutReplayCanRight.hcan_of_cpack`）、**`hplace` も制限版が出た**（`CloseoutPlaceBound.hplace_of_order`、`GalilTrailOrder.Order.cr` から）。残るのは量化のずれ 1 点: `hwin` の産出元 `wpack_of_fair`（`PackRun25:121`）は `FairSteps` 上だが `marksEntry'_of_run` は `Steps` 上。原因は `windowInOrigin_tick`（`PackRun25:80`）が `Fair` を取ること。**`Fair` の一意性 `tick_fair_unique` は `GalilTickFair:437` で証明済み（sorry なし）**なので、残りは最上位走行の各 tick が `Fair` を満たすことの監査のみ。 | `pal_in_peg_final25` |
| `hsc` | `H_stageScan`（`CloseoutOracleI2:173`） | 最上位引数 | **REFUTED**（§4）。再切り出しの配線図: 消費側は `hstage_of_scanBranch`（`CloseoutOracleI2:179`）**ただ 1 つ**で、`InvS`（`GalilOracleDischarge:79`）の replay 枝から `InvScan` を取り出して `hsc` を当てている。よって `InvS` の replay 枝を `InvScan ∧ ReplayStage` に差し替えれば `hsc` は消える。産出側の第 1 段は証明済み（`CloseoutStageScan1.replayStage_of_replay_after_fallback`）。`InvS` の出現は 45 箇所で、そのうち replay 枝を作る産出点だけが `ReplayStage` の供給を要する。 | `pal_in_peg_final25` |
| `hor` | `CycleOracleMC3` | 最上位引数 | §3 の葉一覧 | 同上 |
| `hbirth` | `M-periodOnly` の副産物。`afterBirth` が `S.onLetter`/`S.leftFirst`/`S.replayExhausted` を変えないこと。`Shared` の 3 場は抽象関数なので一般には偽 | `LocalTick1.tickL1_abs` / `LocalReplayParked.tickL1_abs''_nonreplay` の引数 | 具体 `PofC` で放電可能（`afterBirth` は `periodOnly` と `cycle` しか触らず、`replayExhausted = zero ∘ replay`）。未供給 |
| `hC` | `H_realizeLIMG2'`（局所実現） | `CloseoutPackRun36:488` | 局所側（`LocalSysConcrete`/`LocalRealizes*`）、`Fair` 依存 | `pal_in_peg_final5MG2` |

---

## 2. INTEGRATED（主経路から実際に消えた義務）

| ID | 何が起きたか | 根拠 |
|---|---|---|
| `Extra.failed` | **削除**。監査の結果どの消費側も読んでいなかった（`Extra'` の読み手は `scanAvail`/`rewindMargin` のみ；DP の実消費は `MismatchDp` が自前経路で `StageFailed` に到達） | `CloseoutPackRun42` §2 監査、`CloseoutPackRun43` |
| `Extra.cand` | **削除**（同上）。裸の向き変換 `H_candOrient` は反例あり（§4） | `CloseoutPackRun43`、`CloseoutCandOrient` |
| `Extra.ready` | **削除**。どのモードでも読まれていなかった | `CloseoutPackRun45` §0 監査、`CloseoutPackRun46` |
| `hsl` (`H_shiftLocalG`) | **定理化**。`InvLPC` のどの状態も chain は idle（`Inv.rest` → `Restarted` 第 1 連言、または `InvScan.chainIdle`）なので `ShiftLocalG` は空虚（`shiftLocalG_of_chainIdle`） | `CloseoutShiftLocalFree.chainIdle_of_invS` / `h_shiftLocalG`、`CloseoutPackRun51` で供給 |
| `rInitPackM` | 無条件で証明（pack は `AuxPack.front.notInit` により `init` に居ない） | `CloseoutPackRun21:88` |
| `WatchPrefixC` | 無条件の定理（`WatchSeg` の構成子族は排他、段は関数的） | `CloseoutWatchRound20:172` |
| `ShiftPeriodC` | 葉ですらなかった（`ShiftRoundDataL` の 2 場から導出）→ 削除 | `CloseoutWatchRound45:81` |
| `WindowEndC` | 仮定ゼロで閉（`LandingData.ScanInvariant` の `Represents` から） | `CloseoutWatchRound50:86` |
| `H_fourOther` | `Coupled'`（sharp `5h`）の下で定理に | `CloseoutPackRun40:306`、`coupled'_tick` は無仮定 |
| `hshift`（readiness） | 放電（`scan_shift` は比較量子を 1 つ消費し clock を 2048 に） | `CloseoutPreload38:51` |
| `hact`（readiness） | 形を slack 0 の節に直して消滅 | `CloseoutPreload39:57` |
| `hrot`（core） | `RTQueue.Inv` から導出、仮定でなくなった | `CloseoutCoreEnc22:180` |
| `near ≠ []`（core） | 消滅 | `CloseoutCoreEnc22` |
| `hbs`（`H_bootShift`） | **既に木の中の定理**。`initVM0` が `chain := .idle` にし、`shiftLocal_of_chainIdle` が `ShiftLocal` の全 5 場を潰す（`beginShiftVM'` は `chain = .watch` を要るが `chainAt_idle_ne_watch` が禁じる） | `CloseoutPackRun6:184`、供給は `CloseoutPackRun51.pal_in_peg_final25` |
| `hls`（`H_landShift`） | 同上。`initial` からの唯一の tick は `Tick.init` で chain は idle のまま（`GalilTrailFront.init_tick_inv`） | `CloseoutPackRun6:190`、同上 |
| `hsc` の再切り出し第 1 段 | `ReplayStage` は fallback replay の着地で**実際に構成できる**（`Restarted raw t 0 reset` と `c.clock = 2048` は呼び出し側に既にある）。`replay_after_fallback` が捨てていた `stage` フィールドを拾い直した。`H_stageScan` 自体は §4 の通り偽のままで、`InvScanS` への差し替えが残り | `CloseoutStageScan1.replayStage_of_seg` / `replayStage_of_replay_after_fallback` |
| `hpresT`（oracle） | `SegReachedW` が `HpresRepAt` の入力 2 つ（`StepsAll … SoundScanNR` と `mode = scan`）をそのまま持っていた | `CloseoutOracle7.hpresT_of_hpresRepAt`、oracle の前提が 15→14 |

---

## 3. `CycleOracleMC3` の葉（`hor` の内訳）

閉: `hex`, `hsearch`, `hends`, `hbudget`, `hrs`, `hended`, `hlastMatch`, `hstr`, `hfb`。

| 葉 | 状態 | 備考 |
|---|---|---|
| `hpres` | `REFORMULATED` | 普遍形は `GalilLeafPres.hpres_false_at` が反証。scan 側は `HpresAt` で放電（`CloseoutOracle5:64`）。replay 側 `hpresRep` は `GalilReplaySpan` に制限形を受ける版を追加する編集が必要（進行中） |
| `hstage` | `OPEN` | `ReplayStageInv`、mid-replay restart の `3·radius ≤ 5·last` |
| `hshape` | `REFORMULATED` | `StartShape` は偽 → `StartShape'`（`GalilReplaySpan.startShape'_of_decodes`） |
| `hlastMismatch` | `OPEN` | 最終文字分岐 + `EntryRefreshed` |
| `hmismatch` | `OPEN` | `hdp` → `MismatchDp`+`StageBudgetAt`、`hpos` → 区間予算 |
| `hfound`/`hfoundBg` | `OPEN` | 着地不変量に `Restarted`/`StageEntry` + found tick からの経路構成。**最大の未着手** |
| `hfoundReplay` | `OPEN` | 未着手 |
| `hreadyB` | `OPEN` | 着地での `RunEntriesAll` |

---

## 4. REFUTED（反例があり、修正対象）

| ID | 反例／理由 | 現在の扱い |
|---|---|---|
| `H_candOrient` | `W = [0,0,0,0,0,1]`, `n=5`, `lower=0`, `h=1`。接頭辞 3/5 は回文、`W.drop 3 = [0,0,1]` は非回文。Lean で確認（`CloseoutCandOrient.unrestricted_transport_false`、標準公理のみ） | 主経路から削除済み。正しい橋は `GalilDpSuffix.candidate_iff`（同一窓＋反転） |
| `Extra.scanMargin` | 1 文字語で反証（`ScanMargin2.margin_false_witness`） | 削除済み |
| `ShiftLocal`（無ガード） | 全 `scan→shift` 着地で偽（`shiftLocal_false_at_landing`、`Internal.idle` が有効） | `ShiftLocalG`（scan ガード付き）へ |
| `ReplayNoBusyC` | replay 中も found 量子で chain は始まる（Scala も同じ） | `ReplayRunW`（3 分岐）へ |
| `LandingFreshC` | `h` が普遍量化で `periodLength w' = 0` と `= 1` を同時要求 | `LandingFreshC'` + `ShiftPeriodC` へ分割 |
| `MismatchLandingLagZeroC` | lag 1 の `take` が guard を通る（`budget_counterexample`） | 着地限定 `MismatchLandingLagZeroL` へ |
| `WatchFreshC` | 全 watch 区間量化、`WatchSegE.stop` は任意 clock で成立 | 着地限定へ。ただし下記の通り着地版は空虚 |
| `WatchFreshAtC`（着地版） | **前提が充足不能 = 空虚**。着地の chain は `copy`（`chainStart` は `ChainVM.copy`、`ChainMatched` は構成子を保つ）であり `watch` ではない（`CloseoutWatchRound52.landing_chain_copy:120`、`landing_not_watch:135`、`watchFreshAtC_vacuous:148`）。**n72 の「文脈だけで閉じた」は誤り**で、`watchFreshAtC_of_ctx` は内容を持たない | 誕生時刻版 `WatchBirthFreshC`（watch 誕生は着地の `2h+3` prep tick 後、そこでの clock は `MatchClock.run 2048 2048 avPrep` で fresh でない）へ。`OPEN` |
| `ChainWatchPhaseC`（`n ≤ 2047`） | chain 周期は非有界なので copy/back 相は 1 クロック窓に収まらない | 相跨ぎ `ChainWatchReachM` へ |
| `LagPos`（`0 < lag`） | `Outer.immediate` は `zero lag` がガード | `LagCan`（`0 ≤ value lag`、自己保存）へ |
| `ScanRealized` | `ScanSupplyInv` と矛盾（`scanRealized_absurd`） | `PostRunPh`/`PostRunF`（到達可能接頭辞）へ |
| `hplace`（∀ 全状態の place 境界） | `placeC u = ⟨lettersOf u.center.head, u.center.gap⟩` は中心ヘッドしか読まず、`position u.right` は右ヘッドしか読まない。両者を結ぶ場が型に無いので、中心を 1 文字進めて右ヘッドを原点に置けば破れる | `CloseoutPlaceBound.hplace_false`。到達可能状態（`position center ≤ position right`）へ制限が必要 |
| `hpres`/`hpresRep`（普遍形） | `hpres_false_at` | `HpresAt`/`HpresRepAt` へ |
| `Extra3.failed`（全 scan 状態） | restart が DP を入口に reset | 削除（§2） |
| `hsc`（`H_stageScan`） | `InvScan`（`GalilReplaySegment:317-341`）の 11 場は**どれも `s.radius` に言及せん**が、結論の `ReplayStage` は `Restarted` 経由で `RadiusRep r.radius Rad`＝`Canonical r.radius` を要求する。`Counter = ⟨pos neg : List Unit⟩` で `⟨[()],[()]⟩` は値 0 の非 canonical な合法値なので、任意の `InvScan` 住人の `radius` だけをこれに差し替えれば 11 場は全部生き残り `ReplayStage` だけが壊れる（`s.length`/`s.cycle`/`s.periodOnly` でも同じ）。紙の議論であり Lean 項ではない | 再切り出し `InvScanS := InvScan ∧ ReplayStage`（`InvScan→InvScanO`、`SearchReady→SearchReadyB` と同じ型）。最初の一歩は `replayStage_of_replay_after_fallback` |

---

## 5. モデルの欠陥（修正単位）

| ID | 内容 | 状態 |
|---|---|---|
| `M-periodOnly` | Scala `ScaffoldChain.start()` は `periodOnly = false` **かつ** `cycle.reset()` を行うが、Lean のモデルはどちらも落としていた。修正: `chainBorn (found) (x : ChainVM) := x.isIdle && found`（誕生条件は「その遷移で新しい chain が実際に始まること」であって `found = true` ではない）と `afterBirth born s`（`GalilScaffoldTopSearch:70,77`）。`compareFound`/`backgroundS` の遷移先をこれで包んだ。 | **修正済み・検証中**。抽象側の破損は 2 モジュールのみ（`GalilScaffoldTopSegmentHeads.watchSegE_heads` は単調形 `t.periodOnly = true → s.periodOnly = true` に弱めた）。局所側は `LocalTick1` に `birthL`/`abs_birthL`/`inv_birthL`/`stepLocal_birthL` を入れ、`bgState` に誕生元 chain を渡し、局所歩数 `c₁` を 66 → 67 に上げて `tickL1_local`/`tickL1_inv`/`tickL1_abs` を再証明（sorry なし）。`tickL1_abs` は新たに側条件 `hbirth`（`onLetter`/`leftFirst`/`replayExhausted` が `afterBirth` 不変）を取る。`Shared` の 3 場は抽象関数なので一般には示せず、具体 `PofC` での放電が **OPEN**。回帰テスト `CloseoutPeriodOnlyRegression.birth_resets` が修正前は失敗し修正後は通る。 |

---

## 5b. 合成の方針: `canRight` 一本化

`hee`・`het`・`MatchRes2.canR`/`canRNext`・`walkerInOrigin_of_run` の `hcan` は**すべて同じ義務**
「その状態で右ヘッドがまだ動ける（入力が尽きていない）」に帰着する。個別に潰すのではなく 1 本の
走行補題で倒す。

1. 右ヘッドが進むのは比較のときだけで、1 回につき `position` はちょうど +1
   （`GalilScaffoldChainInputSupply.right_position`:500）。
2. 比較は `clock = 1` でのみ起き、その tick で clock は `delay` に戻る。よって比較は `delay` tick に
   1 回以下。
3. したがって `n` tick の走行で `position y.right ≤ position x.right + (n / delay + 1)`。
4. 入力枯渇は `position = 2 * w.length`（`GalilEndOfInput.not_canRight_iff`）。最上位の走行は
   `delay * w.length` tick なので `position ≤ w.length + 1 < 2 * w.length`（`1 < w.length`）。

**材料はすべて既存。**
* `front s := position s.right + value s.replay`（`GalilRunTrace:39`）は `front_tick_mono`
  （`GalilFrontMono:175`）で 23 構成子すべてについて単調が証明済み。増えるのは比較のときだけ。
* `Tick` の 23 構成子のうち clock を触るのは 5 つだけ（`GalilScaffoldTop:110-173` を実読）。
  `scan_count` が `clock - 1`、`scan_match`/`scan_shift`/`scan_fallback`/`replayStart`/`restart` が
  `clock := delay`、残り 17 は不変。よって**どの tick も clock を 1 より多く減らさない**。
* ポテンシャル `Ψ (c, s) := delay * front s - c.clock` は tick 毎に高々 +1。比較は
  `front` +1（`delay` 増）と clock `1 → delay`（`delay - 1` 減）で差し引き +1、非比較は
  `front` 不変で clock 減 ≤ 1。

**`PalPeg/CloseoutClockFront.lean` に一式を書き、`lean` で検証した（標準 3 公理のみ）。**

| 定理 | 内容 |
|---|---|
| `clock_drop_one` | どの tick も clock を 1 より多く減らさない（23 構成子） |
| `clock_le_delay` / `_steps` | clock は `delay` を超えない |
| `front_clock_tick` | **核心**。front 不変、または比較（front +1 かつ `clock = 1`、`clock' = delay`）。23 構成子のうち `Or.inr` は 3 つ（`scan_match` の非 replay、`scan_shift`、`scan_fallback`）だけ |
| `pot_tick` | `Ψ := delay·front − clock` は tick 毎に高々 +1 |
| `pot_steps` | `n` tick で `Ψ ≤ Ψ₀ + n` |
| `front_le_of_run` | 初期状態（`front = 0`, `clock = delay`）から `delay·front ≤ n` |
| `canRight_of_run` | `n < delay·(2·w.length)` なら右ヘッドは動ける |
| `extra7_of_run` | `Extra7` を走行から直接供給 |

**検証結果（2026-09-19）**: `clock_drop_one`, `clock_le_delay`, `clock_le_delay_steps`,
`front_clock_tick`, `pot_tick`, `pot_steps`, `front_le_of_run`, `canRight_of_run`,
`extra7_of_run` の 9 本すべてが `[propext, Classical.choice, Quot.sound]` のみで通った。
`front_clock_tick` の 23 構成子のうち比較枝（`Or.inr`）は 3 つだけであることも確認。

**接続点**: `CloseoutPackRun46.extra7_steps`（:270）が「原点の `Extra7` ＋ tick 保存」から
走行先の `Extra7` を出している。`extra7_of_run` はそれを丸ごと置き換えるので、
**`hee` と `het` が同時に消える**（8 前提 → 6 前提）。`replayStart` が第 1 枝に入るのは
`RewindEq` の等式 `position center + r = position right`（`GalilFrontMono:90`）による。

---

## 6. 運用規則

- 再定式化・改名でも同じ義務 ID を引き継ぐ。
- 「一つの仮定」に問題を詰め直して数を減らさない。
- 進捗率は報告しない。今回何が `INTEGRATED` になったかを報告する。
- 同じ義務が名前を変えて再登場したら、別名へ分解する前に、初期状態・遷移・量化範囲・供給元へ戻って監査する。
