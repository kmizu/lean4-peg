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

## 2026-09-19 wave 7 後の偵察 — 残り 5 前提の構造

**全体 build 成功・標準公理のみ・無条件 PAL は未完。**
`pal_in_peg_final27`（5 前提）は main にマージ済み（PR #66）。

wave 7 完了後、残り 5 つ（`hSP`, `hws`, `hme`, `hor`, `hC`）の到達可能性を調べた。
**新しい定理は作っていない。以下は次 wave のための設計情報。**

### `hme`（`H_marksEntry'`）— 経路は存在するが `Fair` が必要

`CloseoutPackRun17` に **`H_marksEntry'` を一切使わない** run 版が既にある:

- `marksEntry'_of_layout`（`Run16:176`）は `ChooseLayout → MarksEntry'` を**副条件なし**で出す。
- `chooseLayout_of_wpack`（`Run17:118`）は `WPack` から `ChooseLayout` を出す。
- `marks_steps`（`Run17:406`）は `CPack`/`WPack`/`MarksInv'` を run に沿って同時に運ぶ。
- `marksInv'_of_run'`（`Run17:430`）が結論。

残る入力は 3 つ:
1. `h4 : first ≠ 4` — `first` の選択に関する側条件（`Fin 9` の 9 通り中 8 通りで成立）。
2. `hfl : ∀ m z, Steps … → z.ctl.mode = scan → 0 ≤ value z.vm.length`。
   **`CPack.canon : Canonical s.length` では出ない**（`Canonical` と `0 ≤ value` は
   リポジトリ内でも常に別々の条件として並記される、例 `CloseoutPackRun49:85`）。
3. `hwin : ∀ m z, … → z.ctl.mode = copy → WindowInOrigin z.vm`。
   `WindowInOrigin s := (stream s.fpp.walker).length ≤ position s.right`（FPP walker、
   `WalkerInOrigin` の**主 walker とは別**）。producer は `CloseoutPackRun25:124` だが
   **`FairSteps` を要求する**（`windowInOrigin_of_fair` が `Fair` の `fallbackPlace` を使う）。

**したがって `hme` の除去は `PackRunRMG2P` の run を `Steps` から `FairSteps` へ
上げる作業とセットになる。** `Fair` 自体は `GalilTickFair` で完成しており
（`Tick ∧ Fair` は全状態で一意）、構成側の witness が `Fair` を満たすことの確認が
別途必要。これが次 wave の主題。

### `hws`（`WatchShiftG`）— 5 連言のうち 1 つは wave 7 で無料に

`WatchShiftG`（`CloseoutPackRun26`）は `ScanNR x → x.vm.chain ≠ idle → compare x.vm s'' →
s''.chain = .watch wch →` の下で 5 つを主張する:

1. `canRight x.vm.right` — **wave 7 の `extra7_of_front_steps_pack` で出る**（`ScanNR` は
   `Extra7` の発火条件と同一）。
2. `4 * periodLength wch ≤ value wch.machine.control.distance`
3. `∀ rad, ScanInvariant … → value wch.machine.control.distance ≤ 2 * rad`
   — 素材は `Coupled'.sum : SumRel s.chain (value s.radius)`、
   `SumRel (.watch w) R = (broken = false → distance + lag = R)`（`GalilChainCoupling`）。
   `lag` の非負性と radius の一致（`RadiusRep`）が要る。
4. `canRight wch.machine.verifier`
5. `Sane wch.machine.verifier`

`Coupled'.block : BlockInv s.chain` は `.watch w` で `WatchBlock w = OnBlock w.machine.control.period`
のみ。**4 と 5（chain の verifier ヘッドの健全性）は既存の不変量に無い。** 新規に要る。

### `hSP`（`ShiftPal`）— 空虚ではない

`ShiftPalAt w s s'`（`CloseoutPackRun31`）は `s'.chain = .watch wch → shiftGuardVM s' →
∀ r₀, ScanInvariant … → 1 ≤ periodLength wch ∧ periodLength wch ≤ r₀ + 1 ∧
PalAt (encoded w) (center + periodLength wch) (r₀ + 1 - periodLength wch)`。
`ShiftLocalG` を空虚にした「`InvLPC` の chain は idle」の手は使えない
（run 途中では chain は動いている）。実質的な周期・回文の主張で、
Galil の move 補題（`GalilMoveLemma`）圏の内容。

### `hor` / `hC`

`hor`（`CycleOracleMC3`）: producer はゼロのまま（6 consume, 0 produce）。最大の残り。
`hC`（`H_realizeLIMG2'`）: `h_realizeLIMG'_of_G2`（`Run36:499`）で `H_realizeLIMG'` に
還元される。局所機械の実現。

## 2026-09-19 wave 7 — `hee`/`het` を **無条件化**: 最上位は **5 前提**

**`pal_in_peg_final27`（`CloseoutExtraFinal`）— 標準公理のみ・5 前提。**
残り: `hSP`, `hws`, `hme`, `hor`, `hC`。

`hee`（`H_extraEntry7`）と `het`（`Extra7` の tick 保存）は、どちらも
`packRunR_MG27` の `hprefix`（`CloseoutPackRun46:229`）を作るためだけに存在した。
`hprefix` は「`InvLPC` 起点の run の各点で `Extra7`」、すなわち scan かつ
非 replaying な各状態で `canRight`。

wave 5 の `CloseoutCanRightBound.extra7_of_bound` は位置上界からこれを出すが、
`PackRunRMG2` に位置上界が無かった。**上界は front ポテンシャルに乗って伝わる。**

- `GalilRunTrace.front s = position s.right + value s.replay`（`:39`）は
  `CentreLive` run 上で単調（`GalilFrontMono.front_stepsAll_mono`、**既存**）。
- `FrontPack.rest` は `ReplayRest`、すなわち `c.replaying = false → s.replay = reset`。
  よって**非 replaying 状態では `front s = position s.right`**（`front_eq_position`）。
- ゆえに run の出口 `y` が非 replaying かつ cycle の上界を持てば、
  `position x.right = front x ≤ front y = position y.right ≤ 2m-1`。

右ヘッド自身の単調性（34 ケースの `Tick` 解析）は**一切不要**。

`extra7_of_bound` の残り 2 入力（`Represents … w`, `focus ≠ none`）は
`LPackM.scanGeom`（`CloseoutPackRun10:139`）の `ScanInvariant` から出る。
`scanGeom` の発火条件は `mode = scan ∧ replaying = false` で、
**`Extra7` が語る条件と完全に一致**する（`rrep_of_lpackM`）。

帰納の循環（`Extra7 (g (n+1))` が構築中の pack を要求）は
`bigPack2MG7''_tickE` が `Extra7` を**その pack の関数として**受け取ることで解消。

呼び出し側は全て上界を持っている:
- 進行分岐: `CycleOutMC3` の定義に `position sT.right ≤ 2m-1`（`GalilInvPlus3:213`）、
  非 replaying は `InvLPS` から `invS_mode`。
- checkpoint 分岐: `ReportPointAt`（`GalilReportPrefix`）の場が
  `notReplaying`, `atPlace : position = 2m-1`, `pos : 1 ≤ m`, `le : m ≤ w.length`。

| 新規ファイル | 内容 | 公理 |
|---|---|---|
| `CloseoutFrontExtra` | `front_eq_position`, `position_le_of_front_steps`, `rrep_of_lpackM`, `extra7_of_front_steps_pack` | 標準 |
| `CloseoutExtraFree` | `steps_to_end_of_trace`, `bigPack2MG7''_tickE`, **`packRunR_MG27P`**（`Extra7` 入力ゼロ） | 標準 |
| `CloseoutExtraOracle` | `reachAtIMG2S_of_reachAtC3R_P`, `cycleOutIMG2S_of_cycleOutMC3R_P`, `h_oracleIMG2S_of_MC3_P` | 標準 |
| `CloseoutExtraFinal` | **`pal_in_peg_final27`（5 前提）** | 標準 |

**台帳判定**: `hee` → **PROVED**、`het` → **PROVED**。
wave 5 の「`hee`/`het` の残差は偽の疑いが強い」という記録は**誤り**だった。
偽なのは「任意の状態で `canRight`」であって、run 文脈では真。訂正する。

**全体 build 成功・標準公理のみ・無条件 PAL は未完。**

## 2026-09-19 wave 6 — `hsc`（`H_stageScan`）を **完全除去**: 最上位は **7 前提**

**`pal_in_peg_final26`（`CloseoutStageFinal`）— 標準公理のみ・7 前提。**
残り: `hSP`, `hws`, `hee`, `het`, `hme`, `hor`, `hC`。

`hsc` は wave 5 で **REFUTED**（`InvScan` の 11 場は `s.radius` に触れないのに
`ReplayStage` は `Canonical radius` を要求）。今回の結論は、**再切り出しすら要らず
そのまま消える**というもの。

根拠の連鎖:

1. `hsc` の主経路上の消費者は `cycleOracleIMG2_of_cycleOracleMC3R`
   （`CloseoutPackRun36:673`）ただ 1 つ。そこで `hstage_of_scanBranch` を呼び、
   `InvLPC` を `CycleOracleMC3` の要求する `InvLPS` に持ち上げている。
2. その `hstage_of_scanBranch`（`CloseoutOracleI2:179`）は
   `rcases hIC.1.1.1.1 with h | ⟨k, h⟩` で分岐し、**`Inv` 側は
   `replayStage_of_inv h` で無条件に閉じている**。`hsc` が要るのは `InvScan` 側だけ。
3. ところが `CycleOutMC3` は **両方の出口で `InvLPS` を返している**
   （`ReachAtC3` の継続 `GalilInvPlus3:193`、進行分岐 `:212`）。
   `reachAtC2_of_3` と `cycleOutIMG2_of_cycleOutMC3R` が `hIS.1` で捨てていただけ。
4. boot も `Inv` 分岐に着地する: `GalilFinalAssembly4.invLPC_init:94` が
   `hI : Inv (a :: rest) … t` を作ってから、どちらの選言だったかを忘れている。

すなわち **stage は、必要とされるすべての地点ですでに産出されている**。
Run36 §2 のチェックポイント再帰を `InvLPC` ではなく `InvLPS` の上で走らせれば、
`hstage_of_scanBranch` は一度も呼ばれない。

| 新規ファイル | 内容 | 公理 |
|---|---|---|
| `CloseoutStageRecur` | `reachIMG2_fuel_stageFree`（`InvLPS` を運ぶ再帰）, `cycleOracleIMG2_stageFree` | 標準 |
| `CloseoutStageCheck` | Run36 §2 を `InvLPS` 上で再走: `ReachAtIMG2S`/`CycleOutIMG2S`/`CycleOracleIMG2S`/`checkpoints_costIMG2S_upto1`/`preTraceIMG2S_exists` | 標準 |
| `CloseoutStageBoot` | `invLPS_init` — `invLPC_init` に `replayStage_of_inv hI` を足しただけ | 標準 |
| `CloseoutStageOracle` | `h_bootIMG2S_of_bootIPack`, `h_oracleIMG2S_of_MC3`（**`hsc` 引数なし**） | 標準 |
| `CloseoutStageFinal` | `pal_in_peg_final5MG2S`, **`pal_in_peg_final26`（7 前提）** | 標準 |

**ドロップイン性の要点**: `preTraceIMG2S_exists` の結論 `PreTraceIMG2` は
Run36 の同名 structure **そのもの**（StageCheck 側の複製定義は削除済み）。
よって下流（`h_trailI_MG2` / `needIMG2'_le` / `pal_in_peg_of_latch'`）は無改造。

**台帳判定**: `hsc` → **REMOVED**（REFUTED のまま、置換も不要）。
wave 5 で書いた `InvScanS` / `InvLPCS` 再切り出し（`CloseoutStageSupply`,
`CloseoutStageFree`, `CloseoutStageLanding`, `CloseoutStageScan1`）は
**この経路では不要**になった。`CycleOracleMC3` を無条件に作る段（`hor`）で
replay 着地の stage を供給するときに再利用できるので残す。

**全体 build 成功・標準公理のみ・無条件 PAL は未完。**

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
| `hsc` | `H_stageScan`（`CloseoutOracleI2:173`） | 最上位引数 | **REFUTED**（§4）。**2026-09-19: 連鎖が全段つながった（標準公理のみ、`final25` への配線は未了）**。突破口は `ReplayStage`（`GalilFoundStage:98`）が着地状態に `Restarted` を要求せず、**`Restarted` な祖先から `WatchSegE` で到達したこと**だけを言う点。着地でこれは真。(a) 消費側 `CloseoutStageSupply.invLPS_of_invLPCS` が `hstage_of_scanBranch` の `hsc` 無し版。(b) 橋 `CloseoutStageFree.cycleOracleIMG2_stageFree` で `hsc` が `hup : InvLPC → InvLPCS` に置換。(c) 産出側 restart 枝は `invLPCS_of_inv`、replay 枝は `CloseoutStageLanding.invLPCS_of_replayLanding`（`ReplayLanding` の `rest : Restarted raw s 0 reset` と `clock : c.clock = 2048`、`replay_after_fallback` が返す `hseg` の 3 つがそのまま `invLPCS_of_seg` の入力）。残るのは `invLPC_after_replayLanding` の結論に `InvLPCS` を通す編集と、`final25` の引数列からの除去。 | `pal_in_peg_final25` |
| `hme` | **道具あり・検証済み** | `hcan`・`hplace` は定理化済み。残りは走行の各 tick が `Fair` を満たすことの監査のみ（`tick_fair_unique` は `GalilTickFair:437` で証明済み） |
| `hSP` | 残差絞り込み済み | `ChainRound` 経由 |
| `hws` | `WatchShiftG`（chain–scan 結合） | 最上位引数 | `ChainPosInv2`（`CloseoutPackRun41:215`）+ `Coupled'`（`PackRun40:77`） → `MatchRes2`（`PackRun48:208`）。**`matchRes2_of_lpackM3`（`PackRun49:420`）は完成済み**で、残差は `MatchRest`（`PackRun49:405`）の 4 場 `repV`/`repVmid`/`replayPay`/`canRNext`。**そのうち `canRNext` は位置上界から出る**（`CloseoutCanRightBound.canRight_next_of_bound`、2026-09-19 証明）。 | `pal_in_peg_final25` |
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
| `hor` | `CycleOracleMC3`（`GalilInvPlus3:216`） | 最上位引数 | **重要な訂正（2026-09-19）**: `h_oracle_of_leaves5`（`CloseoutOracle6:323`）の 15 葉は**旧系統 `H_oracle` 向け**で、`final25` が要求する `CycleOracleMC3` への橋は**存在しない**（`MC3` を産出する定理が repo に無く、消費する定理だけがある）。つまり `hor` は葉を潰す前に「`MC3` を出す定理を書く」段階がある。その日に向けて閉じた材料: **`hrs`（`RestartShape`）と `hbudget`（`ReplayBudgetR`）は無条件で証明済み**（`CloseoutRestartShape.restartShape_PofC` / `replayBudgetR_PofC`、後者は `decodesC` だけ）。`hended` も `GalilLeafReport.hended_C` で閉（残差 `EntryRefreshed` 1 つ）。`hshape`（`StartShape`）は `canRight s.center` を要求し `GalilWatchOkInst:61` が「導出不能」と明記。`EntryRefreshed` は出力の**完全性**（`IsPal → output = true`）を要するが `OutputRel` は健全性のみ。 | `pal_in_peg_final25` |
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

**接続点と残る障害（2026-09-19 の調査）**: `Extra7` は `BigPack2MG7''` の第 5 場で、
`packRunR_MG27`（`CloseoutPackRun46:223`）が走行の各点 `g i` で要求する。`hreach` が
`Steps … (j+i) ⟨c,r⟩ (g i)` を与えるので `extra7_of_run` の形には合う。

**ただし `extra7_of_run` は走行長の上界 `n < delay * (2 * w.length)` を要求し、
`PackRunRMG2`（`CloseoutPackRun36:588`）の `∀ (j : ℕ)` にはその上界がない。** これは
当初の見立ての誤りで、配線は 1 行では済まない。

**正しい route を実装した（`PalPeg/CloseoutCanRightBound.lean`、標準 3 公理のみで検証済み）**:
`CycleOracleIMG2`（`CloseoutPackRun36:256`）と `CycleOutIMG2`（:247）は**始点と終点の両方で
`position r.right ≤ 2 * m - 1` を保つ**設計で、`1 ≤ m ≤ w.length` なので
`position right ≤ 2*w.length - 1 < 2*w.length`。入力枯渇は `position = 2*w.length`
（`GalilEndOfInput.not_canRight_iff`）なので、これがそのまま `canRight` を与える
（`canRight_of_position_bound`）。

さらに `CostedRun.right_mono`（`GalilTraceCost:80`、右ヘッドは単調非減少）により、
出口の上界が走行の各中間点にも及ぶ（`canRight_of_costedRun`）。走行長の議論は不要。

残る作業は `packRunR_MG27` の `hprefix` をこの経路に差し替えること。

**この位置上界は 3 箇所に効く**（教訓: 同じ義務が名前を変えて複数箇所に出る）:
`hee`/`het`（`extra7_of_bound`）、`MatchRest.canRNext`（`canRight_next_of_bound`）、
`hor` の `hended`（既に `GalilLeafReport.hended_C` が同じ上界を使って閉じている）。

---

## 6. 運用規則

- 再定式化・改名でも同じ義務 ID を引き継ぐ。
- 「一つの仮定」に問題を詰め直して数を減らさない。
- 進捗率は報告しない。今回何が `INTEGRATED` になったかを報告する。
- 同じ義務が名前を変えて再登場したら、別名へ分解する前に、初期状態・遷移・量化範囲・供給元へ戻って監査する。
