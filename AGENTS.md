# AGENTS.md

このファイルは、このリポジトリで作業するコーディングエージェント向けの正本である。
`CLAUDE.md` の複製に、**引き継ぎ時点の現状**（下の §0）を先頭に足したもの。
`CLAUDE.md` と食い違ったときは §0 が新しい。

---

## §0 現状 — 2026-09-22 引き継ぎ（Codex 向け）

### 0.1 一言で

`lean-pal/` の無条件 `PAL ∈ PEG` は、**残り義務 1 本**。
それが `PalPeg.PalInPeg.obligation_localRealization`（局所実現）で、
いまその具体構成を `lean-pal/PalPeg/PhysicalEncoding.lean` に書いている途中。
**無条件 PAL は未完。最終定理は局所実現の追加公理に依存する。**

**2026-09-22 最新の作業順序:** ユーザー指定の [`proof-strategy.md`](proof-strategy.md) に従う。
M0（接続面）→ M1（boot/feed/境界）→ M2（非飢餓scan count）→ M3–M5。
下のmatched部品記録は再利用資料であり、直近の実装順ではない。

### 0.2 完成判定と残件 KPI（2026-09-22 先輩の指示で更新）

```sh
cd lean-pal && . ~/.elan/env && lake env lean PalPeg/Axioms.lean
```

`PalPeg/Axioms.lean:392` の guard が固定している一覧が計器:

```
'PalPeg.PalInPeg.unconditional' depends on axioms:
  [propext, Classical.choice, Quot.sound, PalPeg.PalInPeg.obligation_localRealization]
```

**この 4 本目が消えて標準 3 公理だけになったとき、§10.5（前提ゼロ）達成。**
義務を 1 本証明したら guard が壊れる → その更新が最終義務の放電記録。

**作業中の KPI は [`lean-pal/PHYSICAL_KPI.md`](lean-pal/PHYSICAL_KPI.md)、
チェック台帳は [`lean-pal/PHYSICAL_CONNECTIONS.md`](lean-pal/PHYSICAL_CONNECTIONS.md)。**
先輩の最新指示は「公理が一本いうても、それは巨大な塊だから指標にしないでもいいよ。分解してこ」。
方針書の **39作業項目（M0–M5）** を証拠付きで消し込む。これは補題数でも同じ重さの単位でもない。
現状 **21完了・18未完**（M0 6/6、M1 7/7、M2 6/6、M3 1/6、M4 0/6、M5 1/8）。
M3-02のconsume各ケースは、watch count全体を同じ最終TickCasesへ接続して完了。
Workbench BUILD=0、最終公理監査 AUDIT=0。最新ログは `/tmp/physical-dp-retirement-{workbench,axioms}.log`。
公理数は日々の指標にせず、上の監査を最後の完成判定に使う。
最終接続8項目はまだ具体機械での充足が未完。旧23出口表は局所部品の在庫（15あり、8未）。T06 beginShiftを源条件供給・実dispatcherまで接続し完了。
boot/feed/全starved/idle-chain静止count/watch count全体/正規watch入口/shift入口・進行・終了は、
同じ役割・符号交換を行う共通 `PhysicalShiftDispatch.machine rest` へ接続済み。
`cases_of_remaining` が既存CountAtRest/CountWatch/CountBackReady/shiftと、新しいEntryを最終TickCasesへ渡す。
正規period配置とcopy/backのhは `PhysicalChainShape.period_onRun` で供給済み。
CountWatchはlag・token・方向・成否で制限しない。他のchain/searchのactiveはhotherに残り、count全体の完成ではない。
`rest` は未実装命令行。全modeの証明・最終機械の確定は未完。
**共通接続の基礎（2026-09-23）:** `PhysicalLoanDispatch.machine rest` と
`PhysicalLoanInvariant.Enc` を下記の最新Cleanup機械/Encが包む。scan・chain idle・searchActiveのとき実mirror2に部分鏡と
radius/debtのbalanceを要求し、他は従来のコピー付きSnapshot Encを使う。
`PhysicalDebtFeed`が実feedの12段と証明用補完の可換性を証明し、入力到来・全starvedを新契約へ接続。
blank・idle静止count・watch count全体・watch入口・shift入口/進行/終了も同じ最終TickCasesへ保持。
118本・半径1536・有限役割は維持。旧コピー付き入口の32+32/64融合もそのまま再利用する。
**正のworkのgrow countも接続済み。** `PhysicalGrowStorage`がspan+=8・work--・span鏡と背景消去を保存し、
`PhysicalGrowCount`がdebt++の2回と部分鏡再準備を32+32+32で融合、同じmacro sweepでclockを減算する。
実窓のgrow選択と`forward_grow`を最終TickCasesへ接続し、hotherからCountGrowを除いた。
**grow比較の非ヘッド行も証明済み。** `PhysicalMatchCounters`がradius++/length+=2/debt--と
条件付きcycle/replay減算、実部分鏡の保存を証明。`PhysicalGrowMatch.body`がgrow 96と比較32を
半径128の実sweepへ融合し、カーソル以外のVM更新を実compareFun/matchedPlaceと同定した。
`PhysicalLoanAssembly`は部分鏡を保った12段ヘッド実行・実macro sweepを組み立てる。
名前のないidle verifierはstayで処理。
**grow比較の個別接続も完了。** `PhysicalGrowMatchTick`が半径128の非ヘッド行と12段で左右ヘッドと
clock/output/replayingを更新し、実macro1536 sweepを証明。`PhysicalGrowMatchCase`が窓のguardと
実tickFunを同定し、`PhysicalLoanDispatch.forward_match/cases_of_remaining`へ接続した。
到来prefixは既存ArrivedOnRun、右head可用性は非飢餓条件から供給。hotherからMatchGrowを除いた。
MatchGrowはscan/clock≤1/chain idle/search grow/work正/比較一致で、matched全体の完成ではない。
prepare（work=0）・他の探索行・search出口補完・DP reset・restart全行も残る。
今回の新4guardと更新したcases guardは標準3公理以内。全体BUILD=0・最終AUDIT=0。
KPI21完了18未完、T02/M3-01未完。詳細は§0.6と台帳末尾。
**退役DP消去を共通dispatcherと同じsweepへ接続済み（既存7activeケースの移行も完了）。** `PhysicalProgramErase`は同じ118本の
退役DP12本に有限phaseと半径1の行動列を使う。Denseな非空白接頭辞を源条件に、
線形回数の実sweepでresetへのTEqGを供給し、`bank_sweep_enc`が既存全Encと余白を保持する。
旧eraseActが非空白rootで停止する例を`left_only_stuck`で確認した。
**Denseのprogram実行からの供給は完了。** `GalilDpDensity.onRun/fpp_onRun`が任意入力・lowerの
実初期配置から任意prefixのDP12/FPP9本の形を証明した。MARKSのemit位置は既存prepared完成形と
実行一意性から供給し、全373命令の保存は有限表のカーネル検査＋実命令の意味で閉じる。
`PhysicalDpDensity.bank_reset_onRun`が待機/halt後を含む実Control.RunからDenseとサイズ上限を供給し、
3*(max(w.length+1,lower+1)+bs.count true)+5回の消去でresetへのTEqGを返す。
**有限phaseと単一sweepへの統合はboot/feed/starvedと既存7activeケースまで接続済み。**
`PhysicalDpCleanup.machine rest`は旧LoanDispatchを包み、同じ源窓から通常処理の次のlive/役割を
読み、次に退役側となるDPだけを並行消去する。半径1536・118本のままで追加tickはない。
`PhysicalEraseBatch.stored`が1536段（各テープ最大1536行動）を1sweepへ融合。
`PhysicalRetiredDpFrame.loan`が旧snapshot/部分鏡を含む全Encへの置換保存を証明し、
新Encは存在量化した消去履歴GoodとViewを持つ。`ready`がdoneからresetのTEqGを供給。
`forward_kept/forward_retired`が通常継続/新退役の一般接続を用意し、
`PhysicalDpCleanupBoot.forward_feed/forward_starved`が実blank bootを含め源条件を供給済み。
**2026-09-23 15:05 引き継ぎ最新版は `CLAUDE.md` 冒頭。**
`PhysicalDpBank.machine`が現在の全dispatcherのdpLive/両bankアドレス保存を源窓から証明。
`PhysicalLoanDispatch.active_of_remaining`へ既存ケース本体を抽出し、
`PhysicalDpCleanupDispatch.cases_of_remaining`がCountAtRest/CountWatch/CountBackReady/
shift/Entry/CountGrow/MatchGrowを新機械/Encの最終TickCasesへ移行済み。
残差hotherの7除外条件は同じで、未実装ケースは減らしていない。
`PhysicalDpPreload.dense_onRun`がlower/copy等の任意ロード途中の12本Dense、
`prepare_run_size`が長さ≤1+実enabled回数を証明。完成済みpreloadを仮定しない。
`PhysicalDpRetirement.live`がsnapshot/部分鏡を含む源Loan Encからlive DPのTEqGを供給し、
`forward_preparing/program`が実Run由来のDenseを同じwrapの退役開始へ渡す。
**再liveまでの消去期限、PAL全体から準備/program Runを供給する接続、
DP live切替え・prepare/restartの実行行は未完。** Retirement補題の旧後状態Enc/実step等式は
各reset行が証明して渡す必要がある。現在のdispatcherはDP bitを保持するため、flip行を
追加するときは別扱いする。FPP旧消去の置換も残る。
今回の新10guardは標準3公理以内、Workbench BUILD=0（9810 jobs）・AUDIT=0。
KPI21/18・T15/8を維持。ユーザーのClaude Code引き継ぎ依頼で追加証明作業を区切った。
具体的な12段結果の射影を直接比較せず、`held_bank/held_roles`・`boot_nonhead`などの一般補題と
融合規則全体のgeneralizeを先に使う。今回の最終Boot buildは約5秒。
新しい `axiom` を足して置き換えてはならない。

### 0.3 残っている義務の型

`lean-pal/PalPeg/PalInPegUnconditional.lean:144`:

```lean
axiom obligation_localRealization (entry q : ℕ) (first : Fin 9) :
    H_realizeCanonical centreC placeC entry q first
```

最終消費者は `ShadowedLocalFinal.given_physicalMachine_indexed`。
機械本体を語の量化の外で固定し、証明用の `Enc w` だけを添字付けした。
元の `given_physicalMachine` は語に依存しない特殊化として維持している。
固定証人 entry=0 / q=1 / first=0 で8つの物理義務を
`PhysicalContract.Obligations` に記録し、`PhysicalConnection.given_obligations` が
既存の抽象側3契約を供給して最終型まで接続する。**仮定付きの型検査であり、8義務の放電ではない。**

`PhysicalContract.forwardTick_of_cases` は OnRun / PreTraceIMW / CanonTrace を保持する。
旧 `forwardTick_of_rule.hideal` の全状態量化へ無理に合わせない。
quiet scan は `PhysicalGuardProbe.frame_quiet_scan_starves` によりstarved側。
その生のtick補題を、非飢餓側が接続できた証拠に数えない。

### 0.4 いま書いている構成（`PalPeg/PhysicalEncoding.lean`）

16,642 行（2026-09-22 Codex 継続編集後）。`PalPeg/Workbench.lean:84` に登録済み。
**単体 build EXIT=0・`PalPeg.Workbench` BUILD=0・sorry 0**。matched共通カウンタ・鏡と制御の12ステップ接続まで、Workbench build と9定理の公理guardで検証。最終公理監査AUDIT=0、追加公理1は残る。

| 決めたこと | 実体 |
|---|---|
| アルファベット | `Γm`（`blankM` / `bottomM` / `encCell` / `encProg` / `encToken` / `encSeg`） |
| 物理状態 | `QPhys fppBound dpBound × (Fin tapeCountM → STape Γm)`、`tapeCountM = 118` |
| テープの割り当て | `abbrev Slot`（`(Fin 4 × Fin 12) ⊕ Fin 9 ⊕ Fin 12 ⊕ Unit ⊕ Unit ⊕ Fin 3 ⊕ Fin 16 ⊕ Fin 7 ⊕ Fin 9 ⊕ Fin 12`）、`slotIndex : Slot ≃ Fin tapeCountM` |
| 符号化述語 | `Enc w margin x p := EncControl w x p.1 ∧ EncTapes margin x … p.2` |
| 規則 | `physRule entryQ first hbound hK : ActRule …`、分岐表は `ruleNext` / `ruleActs`、命令表は `modeCommands` |
| 1 ティックの分業 | `tickPhysRule` の `idealRun … 12` で検証。step 0 は `ruleNext` / `ruleActs` でヘッド以外を処理して4命令を書き、step 1–11がヘッドを動かす。単独の `physRule` はstep 0の表であり、最終融合はC05 |

**設計上の固定点（動かさないこと）**

1. **シミュレーションは `Rep` / `TEqG` で行う。** 物理テープと抽象テープの
   *リテラルな等号*を要求しない。`MachineStep.sweepClosure` の定義が
   `∃ ideal, Enc x (p.1, ideal) ∧ ∀ tape, TEqG blank (ideal tape) (p.2 tape)` で、
   `TEqG` は「ヘッド位置が同じ・全位置の読みが同じ」。
2. **`ActRule.acts` は 1 ティックあたり最大 `K` 個のアクション*リスト*を返す。**
   ただし**左へ 1 歩は 1 アクションで書けるが、右へ 1 歩は書けない**（右移動は
   ビュー層が 11 スロット使ってやること）。§0.6 を読むこと。
3. **ゴミをその場で消さない。** プログラム機械の全消去は
   `fppLive` / `dpLive` のビット反転で、退役した半分は
   `withErase` が毎ティック 1 セルずつ背景消去する。
4. **番号を状態に持ち込まない。** `QPhys` は有限。長さはテープが持つ。
   ただし**配役（どのテープがどの役か）は有限なので制御に入れてよい**（§0.5 の鏡）。
5. **「別レイアウトで部品を作って後で統合」には戻らない。**

**窓シミュレータ**（`fpp` 分岐のために作ったもの）

`winTape` / `winMachine` が半径 `K` の窓から機械を再構成し、
`MachineAgree` + `machineAgree_tick` + `progRunActs_of_agree` が
「半径 `n` まで一致する 2 機械は `n` 回の call で区別できない」を与える。
出口は `fppActs_eq` と `fpp_slot_after`。

**ビュー層の窓**（ヘッドを読む行のために）

`viewWindows v ws` が機械の窓（`Γm`）を `decCell` でビューの窓（`Γc`）に翻訳し、
`viewWindows_of_encoded` が「符号化テープの上ではそれがビュー自身の窓」と言う。
`ConcreteLocalMachine.viewTopsOfWindows` がそこから 3 記号（focus / near / front）を読む。

### 0.5 分岐の実装状況

`Mode` は 10 個（`GalilScaffoldController.lean:21`）:
`init | scan | shift | copy | home | fpp | markEnd | choose | rewind | replayStart`。

**旧部品台帳は `tickFun` の23出口のうち局所分岐定理あり15、未接続8**（正本は `PHYSICAL_KPI.md`）。下表は既存証明の索引で、ラッパー・部分ケースを含むため行数や定理数を KPI にしない:

| 分岐 | 定理 |
|---|---|
| `markEnd` | `markEnd_of_tick` |
| `home` | `home_of_tick` |
| `choose`（back 側） | `choose_back_of_tick` |
| `fpp` | `fpp_of_tick` |
| `copy` | `copy_one_of_tick` / `copy_end_of_tick` |
| `rewind` | `rewind_one_of_tick` / `rewind_reset_of_tick` / `rewind_one_of_tick_branch` / `rewind_pair_of_tick_branch` |
| `shift`（出口） | `shift_exit_of_tick` |
| `scan`（静止腕） | `background_still_of_tick` |
| `scan`（消費腕） | `scan_consume_of_tick` —— **カーソルが右へ動く最初の枝**（平文字に限る） |

**残っている処理の概略**（分岐と共有処理が混在。正確な残数は KPI 台帳）: `scan` の restart・matched・beginFallback、
`scan` の idle 腕の DP 走者（12 テープ、中身は一番大きい）、`init`、`replayStart`、
`choose` の select 側、chain の誕生。shiftモード全体は最終接続済み。
watch countの境界事象は有限役割交換で接続済み。比較内で二度消費するときの合成はM4に残る。

**別名（`alias`）の機構** — 正本 `scala/pal/src/main/scala/pal/` の `alias` は 13 箇所あり、
ポインタの付け替え（`ScavmStructs.scala:139` の `StackView.copyFrom` は `top = other.top`）。
テープにポインタは無いので、符号化は二通りで払う:

* **鏡** — `mirrorSource : Fin 7 → Fin 16` が `0,1,2 ↦ 2`(radius) / `3 ↦ 5`(lower) /
  `4 ↦ 6`(span) / `5 ↦ 10`(chain.h) / `6 ↦ 3`(length)。鏡は源と**常に同じ値**を持つ
  第二のテープで、源を動かす枝は同じティックで鏡も動かす。
  **鏡を 1 本足す費用 = その源を動かす全ての枝に 1 行動と 1 仮説。**
  源を動かす枝がまだ無いうちに足すのが一番安い。
* **境界カウンタ** — counter 13 distance / 14 boundary / 15 last。入れ子の1本の段で
  持つ初期案は未実装だった。現在は既存の段付き単項カウンタを使い、watch中に未使用の
  counter 10を予備として準備し、14/15/10の有限役割を回す構成を接続中（§0.6）。
  成功countのFIRST/LAST境界は同じ役割交換付きdispatcherの最終TickCasesへ接続済み。
  比較の二度消費とshift入口の合成は実dispatcherまで完了。restartは未完。

### 0.6 次の一手 —— M3 共有する段表現・alias・DP

`PhysicalContract.Enc` は blank boot / running の二相。runningは `CoreEnc` のsweepClosureで、
`CoreEnc` は既存の Enc と `slot=0 ∧ 全ビューowed=0` を持つ。
半径は micro=128、macro=1536、margin=1536。有限PC範囲は FPP=max 321 (code.length+1)、DP=code.length+1。
行動長・PC到達範囲・消去条件は各ケースで供給する必要がある。

* **M1は7/7完了。** `enc_initial` が全空白を受け入れ、`PhysicalBootFeed.boot_sweep` が
  最初の実sweepで番兵・カウンタ・有限制御を整えて同じ入力を4ビューへ届ける。
* `PhysicalBootFeed.forwardFeed` は `machineStep noneStep` の初回を含む全some遷移を証明。
  残りの通常noneステップの実装はデータ引数であり、feedの定理に未証明仮定はない。
* `boot_none` / `initial_starved` / `first_letter_unstarves` が空白開始と最初の飢餓解除を確認。
  空語・1文字の全実行の認識証明とは区別する。
* `LocalBlankSweep.compStep_apply_blankEdge` は任意アルファベットへ一般化済み。
  旧 `LocalQueueInit` のAPIは特殊化として残した。
* `EncTapes.places` の未使用な内側の `margin ≤ junk.length` を削除した。
  外側の `padLeft` が余白を供給する。既存の物理符号化証明は単体EXIT=0。
* `PhysicalBoundary.macroBoundary_tickRule` が12ステップ後のslot=0/owed=0を証明。
  `running_fused_step` が同じ実行の融合・実sweepへ輸送する。単体EXIT=0。
* **M2-01/02完了。** `PhysicalTickDispatch.forward_starved` が全starvedを保存。
  `PhysicalScanCount.forward_count_atRest` が非飢餓scan/clock>1/chain idle/search idle-or-missedを
  clock減算・背景消去・12ステップ境界・融合・実sweepまで証明。
  `cases_of_remaining` で最終TickCasesへ接続。他の静止ケースやcount全体は未完。
* **M2は6/6完了。** `PhysicalCountConsume.forward_count_plain` がplain・順方向・一致を
  clock減算、符号更新、period/verifier移動と共に同じ実sweepへ接続。
  `cases_of_remaining` が最終TickCasesへ渡す。後続M3-02で逆方向・不一致・境界も接続済み。
  `workStep` と `countedStep` は同じ物理ステップ内でVM更新とclock減算を行う。
* **M3は1/6完了、残りを統合中。** `ChainBoundaryCache.Inv` が周期テープの形と
  予備カウンタの準備を結ぶ。成功消費ごとにphaseに応じ1/2/3増分し、境界で新distanceに一致。
  `inv_consume` は両方向・FIRST/LAST反転、`inv_shift` は実際のshiftと予備減算を保存。
* `PhysicalCounterCache.boundary_rotate` は同じΓm/padLeftの有限窓から最大3アクションを出し、
  boundary/last/spareの独立テープの役割交換と次回用Invまで証明する。
  成功countの境界は `PhysicalBoundaryCount` で全体機械へ接続済み。比較内の合成は残る。
  詳細はPHYSICAL_CONNECTIONS.md。
* `PhysicalRoles.Control` は Roles × (Unit ⊕ QPhys)。118本・Γm・半径1536を保ち、
  `LocalRoleRouting.decode_route` が役割で振り分けた実sweepと論理ステップの対応を証明。
  `forward_feed` / `cases_of_remaining` へ既存のboot/feed/starved/countケースを輸送済み。
  `boundaryRoles` は14/15/10を回し、`compose_boundary` が既存の3役交換と結ぶ。
  `PhysicalBoundaryCount.machine rest` がこの同じ役割表で境界の選択・交換を実装済み。
  下層の `PhysicalRoles.machine` / `PhysicalCacheMachine.routedMachine` は保持版として残る。
* `PhysicalFreeCounter.running_free_counter` は未使用counterの更新を全Encへ運ぶ。
  `PhysicalSpare.overlay` は同じ源窓・半径でslot 10とその符号だけを差し替える。
  `PhysicalCountSpare.forward_plain` はVM/clock/予備の同時更新と次回用Inv/Repまで実sweepで証明。
  `PhysicalWatchEntry.forward_count` がback→watch入口を有限窓の選択と実tickFunへ接続。
  slot 10/13/14/15をreset、periodを右へ動かし、clock減算とFPP背景消去を同時実行する。
  `cache_at_entry` は正規period配置からInv/Repを作る。入口の後状態Encは仮定しない。
  `PhysicalCacheInvariant.CoreInv` は休止counterの形式とwatch/brokenのInv/Repを同じEncへ載せる。
  実boot・初回を含むfeed・全starved・静止count・plain一致count・正規watch入口で保持を証明。
  `PhysicalCacheMachine.cases_of_remaining` が同じ機械・Encでこれらを最終TickCasesへ接続し、
  plain消費の源Inv/RepはEncから供給する。`routed_cases` で既存の有限役割へも輸送済み。
  `PhysicalConsumeStage.running_staged` は両方向・FIRST/LASTを含む実12ステップ後の状態を同定。
  `PhysicalBoundaryRotate.running_rotate` が境界/last/予備の役割・符号交換を全Encへ運ぶ。
  `PhysicalBoundaryCount.forward_match` / `cases_of_remaining` は成功countの全token・両方向を
  同じ役割交換付き機械・CoreInv・最終TickCasesへ接続する。源の左移動条件もCacheから供給。
  `PhysicalCountMismatch.forward_count` が不一致のwatch→brokenを予備ごと保持する。
  `PhysicalWatchIdle.forward_count` が非消費を保持し、`PhysicalBoundaryCount.forward_watch` が
  watch count全体を同じ機械・CoreInv・最終TickCasesへ渡す。token/方向/lag符号/成否の追加仮定なし。
  **M3-02完了。shift入口の比較二度消費・CoreInv保存も共通dispatcherへ接続済み。
  restart用コピー、他の比較腕は未完。総数21完了・18未完。**
* `ChainStoredPeriod.vmTick` がcopy/backのhとperiod長を全VM tickで保存。
  `PhysicalChainShape.period_onRun` がこれとBlockInvを到着待ちtruncation・報告後plateauへ運ぶ。
  最終 `CountBackReady` の源条件はback/FIRSTだけになり、正規配置はOnRunから供給済み。
  `PhysicalPeriodMirror.entry` → `PhysicalCacheMachine.periodMirror_entry` と最終
  `PhysicalBoundaryCount.forward_entry` が、slot 10を予備にresetした後も鏡5に正符号のhが
  残ることを実sweepで証明する。鏡5は同じCache/CoreInvへ組み込み済みで、boot/feed/
  starvedとwatch count全体（境界の役割交換・不一致→brokenを含む）で保持する。
  `ChainBoundaryCache.cursor_length` と `PhysicalCacheInvariant.running_mirror` が、
  存在量化されたhをbeginShiftVM'が使うperiodLengthへ結ぶ。鏡の符号はtrueで、予備の符号と独立。
  **shiftの入口・進行・終了は同じ最終TickCasesへ接続済み。restart用コピーは未完。**
  `PhysicalShift.ideal_tapes` / `ideal_shaped` / `running_shaped` は更新しないテープと退役FPPの
  背景消去を含む全Enc・全counter形・マクロ境界を、実sweepまで保存する。
  `PhysicalShift.running` は予備減算・h鏡再建も同時に共通CoreInvへ格納する。
  `remainingBound_onRun` は既存Coupledと周期長保存からremaining.toNat≤hを供給する。
  **Cacheへの上限条件追加は不要だった。** `copyIdle_onRun` も既存traceから供給し、
  `PhysicalShift.running_mode` は元のremainingPosのcopy側をCopyIdleで排除し、
  進行を `running`、終了を `running_exit` へ渡す。終了では残量の自然数値がゼロなので
  再建鏡はhそのものになる。`forward_shift` と最終残差hotherはshiftモード全体を処理済み。
  `PhysicalShiftEntry.running_lend` はcounter1/鏡5の有限交換を全CoreInv・TEqGで証明。
  その源はmode=shiftかつremaining=resetの中間状態であり、実tickを追加するものではない。
  `PhysicalCompareGuard.scanShiftRead_running` がwatch起点の比較後guardを実sweepの源窓から読む。
  内部消費の成功/失敗/静止、FIRST/LAST、両方向を含み、可用性は既存の合法Tickから供給する。
  `PhysicalEncoding.scanCommands` は不一致時にこのguardを使って入口の追加移動を選択する。
  `modeCommands_shift_verifier` が同じ実命令表のmoveRight/stepRight選択を証明。
  `PhysicalWatchActions` の二段非ヘッド行動列は32+32=64へ縮小した。全体のmicroRadius=128、
  macroRadius=1536、118本は変更なし。`LocalRoleFusion.compiled_seq` が途中の役割交換を含む
  二段を単一sweepへまとめる。lag/margin・distance・period・spareと境界snapshotを含む。
  `PhysicalWatchStep.running_pair_good_ideal` / `running_pair_good` が共通CoreInvを保存する。
  `PhysicalShiftStart` がradius++、length+=2、cycle/remaining resetと鏡・背景消去を加え、
  `running_entry` で `PhysicalShiftEntry.running_lend` のremaining/鏡5交換へ接続した。
  `plan` は二度消費64＋共通入口64を既存半径128へまとめる。
  `running_nonhead` はこの全非ヘッド処理の単一実sweep後のCoreInvを証明する。
  `source_of_guard` は既存 `WindowPack.source_watch_of_guard` から源watchと内部Goodを供給。
  `immediate_good_of_window` / `running_from_window` は源のChainWindowRunと右ヘッドの
  入力表現から即時Goodも供給する（到来済みprefixを取れる）。
  `PhysicalTickAssembly.running_tick` は同じ非ヘッドCoreInvの証人と12段ヘッド実行をTEqGで合成。
  `running_fused_route` は同じ半径1536の実sweepと最終役割交換へ運ぶ。
  `PhysicalShiftTick.running` は左・右・検証の3カーソル移動まで同じCoreInvを保存する。
  `PhysicalShiftLanding.running_tick` は源の比較/guard・窓・period形から両Goodを供給し、
  到達状態をbeginShift/tickFun全体と同定済み。periodLength_consumeで残量の同一性を閉じた。
  `PhysicalShiftSource.running_onRun` が実行由来の源条件を供給済み。`Heads` は右ヘッドと
  verifierの同じ到来prefix表現・存在・LagAtだけを取り、窓全体のprefix輸送を不要にした。
  `represents_trunc` / `heads_onRun` が追跡中の切詰めと報告後plateauをともに処理する。
  **接続面の修正:** `OnRun` は `TrackedAt.used` を忘れていた。`ArrivedOnRun` がその既存の
  消費上限を保持し、実行の帰納法から `given_physicalMachine_indexed.hforwardTick` と
  `TickCases.active` まで渡す。追加の未証明仮定ではない。旧 `OnRun` へ忘却可能。
  **T06完了:** `PhysicalShiftDispatch.forward_entry` → `cases_of_remaining` が全源条件供給と
  実際の有限窓選択を閉じた。`entryRead_iff` と `entry_of_compare` が入口全体の被覆を保証する。
  同じ機械は既存のboot/feed/starved/count/shiftも保持し、追加の物理tickはない。
  M3-01第4小項目も完了し内訳は4/5。残りはrestart用lastの複数コピーと再準備。
  M4-02にはbeginFallbackが残る。39項目は21完了・18未完、旧T表は15あり・8未。
  番兵から最初の文字へ進む場合も`shiftLeftFirst`/`leftFirst_eq`が扱う。
* **restartの現在地（2026-09-23）:** `PhysicalRestartStorage` が旧lower/span/work/debtの
  非参照性をbackground/compare/restartで証明し、到来・飢餓・有限制御も扱う。
  有効なrestartは4値を上書きするので、差し替え前後でtickFunの後状態は同一。
  実窓のrestart優先選択、4ビューのstay、DP live切替えを含む有限制御は証明済み。
  `Related` / `related_tick` は全10モードの休止探索storage同値を証明し、`Stored` が
  同値な代表状態のRunningを保持する。最終dispatcherのEncはまだ従来のまま。
  `PhysicalSearchRecycle.running_watch_entry` はcounter5/6/7/8とmirror3/4を同じ入口sweepでreset。
  `PhysicalSearchSnapshots` がその6本に2組のboundary/last/spareを載せる。
  組は(5,6,7)と(mirror3,mirror4,8)。`entry_saved` で実入口から準備、`watch_consume` で
  源のphase・period窓による最大3増分/境界交換と次のInv、`shift_running` で全6本の減算を証明。
  `saved_last_copies` はcounter6/mirror4の独立したlastを取り出す。118本・半径1536は維持。
  **consume側base/hbaseは`PhysicalSnapshotCount.forward_match`で放電済み。**
  `rotate_mix` / `jointRoles` が既存14/15/10と追加2組の交換を同じ実sweepへ合成する。
  `PhysicalSnapshotInvariant.Enc` はcanonicalと同値なstorage代表とwatch/brokenのコピーInvを保持。
  `PhysicalSnapshotMachine.machine rest` がこの同じEncでblank boot/全feed/全starved/
  idle静止count/watch count全体/watch入口を実dispatcher・最終TickCasesへ接続した。
  源Inv/コピーはEnc、入口のperiod形とhはOnRun、verifier可用性は元の合法Tickから供給する。
  **新Encのshift進行・終了も接続済み。** `PhysicalSnapshotShift.saved_tick` が元の合法Tickから
  保存代表の合法shiftを再構成。`running` が`overlayWith decrement (workStep rest)`のbaseを放電し、
  `exit_enc` が終了時の全コピー保持を証明する。`PhysicalSnapshotShiftDispatch.machine rest` は
  源窓のmode/starved/remaining判定で同じ行へ分岐し、`cases_of_remaining` がshift全体を外す。
  残量上限とCopyIdleは消費者のOnRunから供給。既存のboot/feed/starved/count/watch入口も保持する。
  **コピー付きshift入口も最終接続済み。** `PhysicalSearchSnapshots.boundedRule` と
  `running_increment_ideal` で小半径へ一般化し、`PhysicalSnapshotWatch` が既存watch行と
  snapshot行を同じ32窓でoverlay、既存14/15/10と追加2組の役割・符号交換を合成する。
  `running_pair` はoptional内部＋即時の32+32計画を1sweepで証明。`goodAge/goodSpare` は
  コピー更新量をcanonical watchから定め、`running_good_ideal` が実際のcaught/immediateへ結ぶ。
  `PhysicalSnapshotEntry` が共通入口64と鏡の引き渡しを合成し、`PhysicalSnapshotEntryTick`
  が3カーソルの12段移動を合成。`PhysicalSnapshotEntryDispatch.forward_entry` は元の
  ArrivedOnRun/合法Tickから両Good・到来prefix・period形を供給し、実窓選択とtickFun同定を閉じる。
  `cases_of_remaining` がshift入口を新Encのhotherから外し、既存全ケースも同じmachineへ保持する。
  追加sweep・半径増加・保存代表への偽のOnRun仮定はない。`scanShiftRead_running_ready` は
  Tick由来のverifier可用性を直接受け取る形へ分解し、既存のTick付きAPIも維持した。
  **他の比較腕（matched/beginFallback等）・restartは新Encのhotherに残る。**
  **lastの3コピー引き渡しも実装済み。** `PhysicalRestartCopies` がcounter6→lower、
  counter15→work、mirror4→mirror3を有限交換し、旧lower/鏡3をresetしてspan/鏡4へ渡す。
  `core_prepared` は全EncTapes・counter形・マクロ境界を保存し、`running` は半径32の
  実sweepを証明。`from_copies` は源条件を現在のコピー付きEncから供給する。
  これは同じrestartへ融合する中間行で、この段階のdebt/DPは旧値のまま。
  **debt初期化と鏡再準備の実行部品も追加済み。** `PhysicalDebtMirror` はmirror2をcounter8へ
  貸し、符号反転でinitialDebt(radius)を得る。旧counter8はresetして再準備用mirror2へ渡す。
  `RebuildingCore` は実mirror2に `ofNat (radius.value + min debt.value 0).toNat` を要求し、
  他のテープには従来CoreInvを保つ。`repair`は証明用にmirror0を参照するだけで物理コピーではない。
  `ready`が半径/debt非負時に従来Runningへ戻す。`restart_from_copies`はlast引き渡し32と
  debt貸出し32を1sweepへ融合し、既存のコピー付きEncから源条件を供給。
  `only_dp_left`は残る抽象更新がDP resetのみと同定する（DP実行行は未実装）。
  `PhysicalDebtRebuild.running`は有限窓でdebt負を読み、debt++と負の場合だけmirror2++を
  同時実行。`running_double`は途中の-1→0を含む2回を32+32の単一sweepで証明する。
  balanceは借用開始時に0、payで保存。比較時radius++/debt--も下記の実行行で保存済み。
  **Rebuilding契約を共通Enc/dispatcherへ接続済み。** `PhysicalLoanInvariant.Enc`はscan中の
  idle-chain active searchだけをRebuilding＋balanceにし、他はSnapshot Encを要求する。
  `PhysicalDebtFeed.run_complete/core_feed/running_feed`はproof補完と実12段/実sweepの可換性を使い、
  部分鏡の実値を保存する。飢餓判定も実窓から復元。`PhysicalLoanDispatch.machine rest`が
  初回を含むfeedと全starvedを処理し、`cases_of_remaining`は既接続のcount/watch入口/shift全体を保持。
  shift終了の非idle源条件は`shift_nonidle_tick/onRun`が実traceとplateauから供給する。
  **正のworkのgrow countを最終TickCasesへ追加済み。** `PhysicalGrowStorage`はspan/mirror4の
  独立テープへ8増分、workを1減算、FPPの背景消去を同時実行し、repairとの可換性からRebuildingを保存。
  `PhysicalGrowCount.body`はこの32とdebt返済32+32を半径96へ融合する。clock減算込みのruleを
  半径1536の1sweepとして実行し、源のEncからbalance・実work正判定を供給する。
  `successor_eq`で実tickFunと一致し、`PhysicalLoanDispatch.forward_grow/cases_of_remaining`へ接続。
  countの全ヘッドは抽象的に静止するため、実ヘッドテープ・制御とマクロ境界もそのまま保持する。
  12回の追加実行や未計上の準備tickは挿入しない。初回feed/全starved/既存count/watch/shiftは保持済み。
  全growではなく、work=0のprepareは未完。
  **比較の非ヘッド処理:** `PhysicalMatchCounters.actual/currentRule`は半径32でradius++、length+=2、
  debt--、有限制御が選ぶcycle/replay減算を実行する。部分鏡mirror2のpushは源debtが正の場合だけ。
  `rebuilding_core/running/running_current`が全Rebuildingとbalanceを保持し、負→0や0→負も扱う。
  `PhysicalGrowStorage`の行動長を再確認して半径64から32へ縮め、grow全体96と比較32を
  `PhysicalGrowMatch.body`の128へ融合した。`running`は実sweep、`matched_grow`は同じVMの
  compareFun＋matchedPlace更新と、残るleft/right移動を厳密に同定する。制御/outputはまだ含まない。
  `PhysicalTickAssembly.running_tick_optional`はheadOfがnoneのビューをstayで扱い、旧APIは維持。
  `PhysicalLoanAssembly.running_tick/running_fused_route`は実部分鏡を残したまま12段ヘッド実行と
  半径1536の実sweepへ運ぶ。proof補完だけを使い、実テープの瞬間コピーを行わない。
  **grow比較への個別適用も最終TickCasesまで完了。** `PhysicalGrowMatchTick.next_control`が
  源窓のscanMatchedCtl/rightOnLetter/leftFirst/replayZeroを実出力・再生制御へ結ぶ。
  `running_ideal/running`は左moveLeft・右moveRight・残りstayと実部分鏡を同じ実sweepで保存する。
  `PhysicalGrowMatchCase.successor_eq/guard_running/forward`は実tickFun一致と実窓の分岐選択、
  源Encからbalance・Rebuilding、後状態のNeedsLoanを供給する。
  `PhysicalLoanDispatch.forward_match/cases_of_remaining`でhotherからMatchGrowを除いた。
  最終call siteでheads_onRunが到来prefixを供給し、非飢餓scanからright.canRightを供給する。
  後状態Enc・head readiness・入力表現を未供給の引数として残していない。
  同じ機械は既存CountGrow・boot/feed/starved/count/watch/shift全体も維持。全matchedではない。
  次はwork=0のprepare/DP reset・bank再利用の契約、他の探索行、search出口補完、
  DPリセット用バッファ、restart全行。doubleはspan+=2・work--・quarter=(quarter+1)%4で、
  debt++は源quarter=3だけなのでgrowの2返済を流用しない。
  SafeCallsのdebt非負条件は最後のadvanceより前なので、search終了時debt=-1も考慮する。
  `credit_one_short`はその不足が高々1であることだけを証明。終了時の補完行と源条件供給は未完。
  DPの退役半分の空白も後状態の仮定で済ませない。
  現EncTapesのidleShapeはFPP9本だけで、DP12本の退役側shape/空白はまだ契約にない。
  prepareはDP reset(pc320)、tape10のLEFT/right初期化、work=lower、walker=centerを同時に要求する。
  lower→work/後のspan→workのaliasを既存の鏡と有限役割で扱い、追加tickや後状態仮定で隠さない。
  T02/M3-01は未完、KPIは21完了18未完、T15あり8未のまま。詳細はPHYSICAL_CONNECTIONS.md末尾。
* **Tickの合法性を捨てない。** `TickCases.active` は最終消費者が渡す実際のTickも受け取る。
  `PhysicalCountReady.verifier_canRight_of_countTick` がpositive lag watchのcanRightを供給し、
  `moveRight_ready` が任意の表現ビューのhreadyへ運ぶ。plain消費の呼び出しで供給済み。
  そのために可用性をtraceから改めて再構成する必要はない。
* 巨大な融合規則は定義展開せず、記号的な規則に対する等式を先に適用する。
  boot_sweepの左端輸送は `sweep_from_blank`、外側Encの輸送は `enc_running` で行う。
  12段のレコードを `change` / `simpa [bootStep]` で直接展開すると型検査が膨張する。
  射影した実行結果の輸送でも、`generalize hr : idealRun … = result at hbase hcounter ⊢`
  のように関連する仮説と目標を一緒に記号化してから射影する。目標だけ記号化して
  巨大な項へ `rw` / `congrArg` を適用する方法は `core_still` で時間超過した。
  具体的な `workStep` のテープ保存も同様。`rewrite [workStep]` でrflを走らせずに開き、
  `generalize hR : workRule rest = R at hkept ⊢` の後に記号的な `fused_kept R` を使う。
  具体12段のまま `change` / `simpa only [workStep]` を使うと200万heartbeatsでも時間超過した。
  `PhysicalShiftTick.running_ideal` でも末尾の `simpa only [rule]` / rule等号の `rw` が
  100万heartbeatsで時間超過した。目標と補題の**各idealRun関数全体**を別々にgeneralizeし、
  その2関数の等号をつないでから書き換えると、具体12段を展開せず型が合う。

#### 旧次手の資料 —— `scan` の `matched` 腕（M4で再開）

**分岐補題未接続は10/23**（§0.2、KPI 台帳）。`scan` の消費腕
（`scan_consume_of_tick`）は部分ケースとして通っており、**カーソルが右へ動く最初の枝**。そのために組み立て器を
二状態化してある（`encTapes_replaceHeadsOfState` → `enc_afterTickOfState`）。

#### 枝を書くときの型（消費腕の部品表）

| 層 | 定理 |
|---|---|
| 命令 | `scanCommands` / `headOp_scanCommands` / `modeCommands_scan` |
| 制御 | `scanConsumeNext` / `_of_match` / `_of_mismatch` / `scanConsumeNext_untouched` / `encControl_scanConsume` |
| 行動 | `scanConsumeActs` ＋ 射影 4 本（`_lag` / `_distance` / `_period` / `_off`） |
| テープ | `scanConsume_lagTape` / `_distanceTape` / `_periodTape` → `encTapes_chainConsume` → `physRule_scan_consume` |
| ヘッド | `headOf_tickFun_scan_consume` |
| 二状態 | `stepState` ＋ 一致補題 5 本 / `backgroundFun_of_active` |
| 組み立て | `scan_consume_of_tick` |

#### `matched` 腕について測ったこと

`compareFun`（`FrameFunction.lean:525`）は

```lean
let headLeft := left s.left          -- 左カーソルが左へ
let headRight := right s.right       -- 右カーソルが右へ
let agree := decide (read headLeft = read headRight)   -- 動いた後の文字同士
let searched := searchEffectFun P agree s              -- 探索も 1 量子
... chainAtFun agree born ...                          -- chain も一歩
```

**二本のカーソルが同時に動き、比較は動いた後の文字同士。そのうえ探索と chain も動く。**
一番重い腕である。ただし:

* **二本同時に動くことは組み立て器が既に運べる。** `rewindCommands` の pair 行
  （`PhysicalEncoding:8531`）が `v = 0 ∨ v = 1` に `.moveLeft` を出し、
  `rewind_pair_of_tick_branch` が通っている。命令は `Fin 4 → ViewCommand` で
  カーソルごとに独立。
* **読み取りは 3 つとも窓の中で閉じた**（ここまでが今日の到達点）:

| 読むもの | 定理 |
|---|---|
| 右カーソルの着地先 | `landingLetter` / `landingLetter_eq` / `read_right_absHead'`（側条件 `hready` 要） |
| 左カーソルの着地先 | `leavingLetter` / `leavingLetter_eq` / `read_left_absHead'`（**側条件不要**——左一歩は 1 アクション） |
| 比較のビット | `agreeTest` / `agreeTest_eq` |
| `matched` の番人 | `compareFun_cursors` / `matchedTest_compareFun` —— **番人は `agree` そのもの** |

左の着地先は `belowRead`（back テープのヘッド直下）で読む。`backStack v = v.focus :: v.back`
（`LocalViewDecision.lean:111`）で、`StackTape.belowSym_eq`（`LocalQueueMachine.lean:397`）が
既にある。**2026-09-22 Codex 継続で左端の側条件を除去**: `leavingLetter` が focus=none を
先に判定し、その場合は none を返す。`back_nil_iff_focus_none` により back 非空の追加仮定は
不要になった。左端の未封印 junk を誤読しない。

#### 2026-09-22 Codex 継続: 一ティックの二度消費を既存ビュー命令へ接続

`chainTickFun true` は `chainStepFun` の後に `chainMatchedFun` を行う。
watch の lag が最初の消費でゼロになれば、そのティックで **もう一度消費する**
（`GalilScaffoldChainWatch.Outer` のコメントにも明記）。検証カーソルは右へ二歩必要。
`scanCommands` に単純に一歩だけ追加しても、この枝を表現できない。

* 既存の `.stepRight` は一文字ぶんの移動なので、抽象ヘッドの `right ∘ right` に一致。
  `moveRight_twice` / `absHead'_stepRight` で証明し、`headOp .stepRight` を実装した。
* `HeadReady command view` を導入し、`enc_afterTickOfState` まで既存APIをその場で一般化。
  `.moveRight` は gap=true のときだけ、`.stepRight` は gap によらず次セルが必要。
  `headReady_stepRight_of_canRight` が抽象側の二つの `canRight` からその条件を出す。
* `chainTickFun_watch_double` → `compareFun_watch_double` →
  `headOp_compareFun_watch_double` で実際の比較の二度消費をこの命令へ接続した。
  **12スロット・118テープ・既存レイアウトのまま**。既存の分岐証明も build 済み。
* 探索は `searchEffectFun` が **chain=idle の場合だけ**動かす。
  active chain の比較は探索を恒等写像にしてよい。idle の探索・chain誕生と分けて組み立てる。

**`scanCommands` の比較腕は実装・二度消費の実行まで検証済み。**
`ruleNext` / `ruleActs` の比較腕も共通カウンタと制御まで接続済み（下記）。`scan_watch_double_head` が実際の
12ステップで検証カーソルの二歩右移動を与える。一般化した組み立て器に接続した。
局所実現義務も既証明分岐の数も変わっていない。
検証: `PalPeg.Workbench` BUILD=0、`PalPeg/Axioms.lean` AUDIT=0。
`absHead'_stepRight` / `headReady_stepRight_of_canRight` / `enc_afterTickOfState` /
`headOp_compareFun_watch_double` の個別公理監査も標準3公理以内。

#### 同日続き: scan の窓による分岐判定を抽象 tick へ接続

* `availableTest_eq`: gap・near・front の読みが `canRightTest` と一致。`EncTapes` から導出。
* `counterZeroTest_eq` / `counterPositiveTest_eq` / `counterNegativeTest_eq`: 符号と直下セルから
  カウンタの判定を復元。
* `restartTest_eq`: broken に加え **margin 非負・last 正・lag ゼロ** を読む。
  引き継ぎ時の「chainTag=broken」という略記だけでは restart の条件にならない。
* `scanPhase_eq`: restart / quiet / count / compare の優先順が抽象制御と一致。
* `agreeTest_of_encoded`: 個別の読み取り一致を仮定せず、符号化と右の `canRight` から比較を復元。
* `tickFun_scan_matched_vm_of_window`: `scanPhase=.compare` と `agreeTest=true` で、実際の
  `tickFun` が matched 腕のVMを返すことを証明。

**物理の matched 腕全体の証明は未完。** 判定とヘッドに加え、下記の共通部分を
`scanNext` / `scanActs` として `ruleNext` / `ruleActs` の比較腕へ接続した。
`scanAfterConsumeWindows` は `windowAfter` で一度目の消費後の窓を復元し、
`chainMatchConsumesTest_of_watchConsume` が二度目の判定を証明する。
`incTwiceActs` / `counter_incTwice_at` / `encTapes_scanLength` は、途中で符号が変わる
場合も含め `length += 2` と鏡の符号化保存まで接続済み。
**これらは分岐全体の証明ではなく、T05 の残数は減らさない。**
最終検証: 単体 EXIT=0、Workbench BUILD=0、個別 SCAN_AUDIT=0（標準3公理のみ）。
`unconditional` は `obligation_localRealization` を依然として使用。

#### 同日続き: matched の共通部分を実際の12ステップへ接続

* `scan_matched_counters_of_tick`: active chain で共通4カウンタと鏡の物理値が
  抽象 `tickFun` と一致。lengthの二回加算、cycle/replayの条件付き減算を含む。
* `scan_matched_control_of_tick`: chainの種類によらず制御・出力・再生継続・
  onLetter/leftFirstが抽象 `tickFun` と一致。到来済み入力の表現・長さは源状態の条件。
* 内部消費専用の `scanConsume_tapes` に切り出し、二度目の窓を求める補題が
  比較用 `ruleActs` の拡張に依存しないようにした。
* **残数は分岐10・共有5・最終接続8・追加公理1のまま。** chain全体と探索・誕生との
  合成はまだ閉じていない。

#### `matched` 腕に残っていること

1. **`scanCommands` の比較行と全ケースの抽象ヘッド対応を閉じる。** 二度消費の plain/forward ケースは接続済み。
   `tickFun` の scan は 6 腕（restart / background×2 / matched / beginShift / beginFallback）で、
   判別子は順に: `restartGuard`（`restartTest_eq` で窓と接続済み）、
   `!replaying && !available`（`available = canRightTest s.right`、カーソル 2 の窓）、
   `1 < clock`（制御）、`matched`（＝ `agreeTest`、上で閉じた）、`shiftGuard`。
2. 共通カウンタ・鏡と制御の接続は済み。chain 全ケースと同時に `EncTapes` / `EncControl` を組み立てる。
3. idle chain では探索と誕生、active chain では chain の内部ステップ＋match 処理を、
   比較のカウンタ更新と合成する。watch の二度消費には上記 `.stepRight` を使う。

#### そのあと

残りの枝（§0.5）→ `hideal` を放電 → `unconditional` の経路を
`given_physicalMachine`（`ShadowedLocalFinal.lean:1395`）へ張り替え →
`PalPeg/Axioms.lean:392` の guard 更新。
`given_physicalMachine` は標準 3 公理のみに依存し、`unconditional` が既に供給している
3 つの側条件と、8 つの証明義務（`hencInit` / `hforwardTick` / `hforwardFeed` /
`PhysFrozen`＋3 / `hencRep` / `hencOut`）を取る。**いま作っているのは `hforwardTick` の中身だけ。**

### 0.7 検証の作法（必ず守る）

```sh
cd /home/mizushima/repo/lean4-peg/lean-pal && . ~/.elan/env
lake env lean PalPeg/PhysicalEncoding.lean > /tmp/pe.log 2>&1; echo EXIT=$?   # 単一ファイル（速い）
lake build --quiet PalPeg.Workbench > /tmp/b.log 2>&1; echo BUILD=$?          # モジュール
```

* **`BUILD=` / `EXIT=` の行を読む。** タスクの終了コードを信じない。
* build は 1 本ずつ。lean プロセスは最大 2。全体 build を毎回起動しない。
* 大きい編集は python パッチで（`assert s.count(old) == n` を必ず入れる）。
  失敗した改造はスクラッチパッドに退避してから `git checkout -- <file>` で戻す。
* **`git reset --hard` / `git clean` は禁止。**

### 0.8 このリポジトリで繰り返し踏んだ罠

* 複数行のレコードリテラル `{x with a := …⏎ b := …}` は `unexpected token`。1 行で書く。
* `have h := …` は定義を忘れる。使用箇所に項を展開して書く。
* `match hslot : e with` の依存 match は簡約を止める。`hslot :` を外す。
* `rw` が `match` をイオタ簡約しないときは末尾に `rfl`。
* `Function expected at f … h` を見たら、宣言の arity ではなく**呼び出し側の余った引数**を疑う。
* `slotIndex` は `Fintype.equivFin` 由来で noncomputable。それを使う `def` は全部 `noncomputable def`。
* 名前に番号を付けない。`_'` / `_2` の変種を作らず**その場で一般化**する。
* 仮定名は意味で付ける（`hpack` / `hav` という名前だったせいで過剰量化を見逃した）。
* **新しい宣言を挿し込むときは docstring の境界を見る。** anchor を「定理の行」に取ると
  その定理の docstring と本体の間に入り `unexpected token '/--'`。4 回踏んだ。
  anchor は docstring の先頭に取る。
* **`cases h : e` はゴールを置換するが、`f y` の中の `y.vm.chain` までは届かない。**
  `counterOf y c` のような射影越しの場合は `simp [counterOf, …, h]` で先に展開する。
* `unfold f` は外側の `match` を簡約しないことがある。`simp only [f]`（等式補題）を使う。
* `let x := …` を含む定義（`GalilScaffoldChainConsume.consume`）は `unfold` 後も
  `have` が残って `rw [if_pos …]` が刺さらない。先に `cases` で `match` を潰す。
* 表に `if` の枝を 1 本足すと、その表の射影補題が**全部**動く。
  `rewindOneActs` の枝を 1 本足したときは 9 宣言・error 16 だった。
* 構造インスタンスの仮説を 1 つ増やすと、その**全フィールド**の呼び出しが動く。
  足す前に、使用箇所を名前付きの `have` に切り出しておくと影響が 1 箇所で済む。
* **暗黙引数は最初に解けた制約で潰れる。** `enc_afterTickOfState` の `{z}` は
  `(fun i => rfl)` で `y` に潰れたので `(z := …)` で明示した。
* **「この API は知らないから止める」と判断する前に 1 回 grep する。** 今日は既存部品を
  4 回見落としかけた: `resetSeg`（可動原点）/ `mirrorSource`（鏡）/ `counter_inc_at` の
  テープ版 / `StackTape.belowSym_eq`。**この建物は思っているより建っている。**
* **接続を試みないと定義の穴は出ない。** `scanConsumeNext` が使う lag と数える distance の
  新しい符号を書いていなかったことは、表を書いた時点では分からず、一歩の後の符号化が
  「新しい polarity の下でのカウンタの値」を求めたときに出た。

### 0.9 下の §（`CLAUDE.md` 由来）の鮮度について

`## lean-pal 無条件 PAL ∈ PEG の進捗（2026-09-19 時点）` 以下の §1〜§5 は
**義務が 1 本になる前の地層**で、`pal_in_peg_final*` の前提の数え方など
既に当たらない記述を含む。方法論（過剰量化・偽の葉・命名規律・一次情報の扱い）は
いまも有効なので残してある。**到達点として読むのは §0 だけ。**

---

## リポジトリの全体像

3 つの独立したサブプロジェクトが同居している。互いに toolchain が違うので混ぜないこと。

| ディレクトリ | 内容 | toolchain |
|---|---|---|
| `lean/` | **Shallot**（PEG フレームワーク + 第一階関数型言語の仕様・実装・証明）と **Lens**（Lean 4 → Scala 3 抽出器） | Lean v4.32.0、外部依存ゼロ（Mathlib 不使用） |
| `scala/` | Lens の抽出結果（`generated/`、コミット済み）、手書きランタイム、CLI、差分ハーネス、`pal/`（Python 版 PAL 生成器の Scala 3 移植） | Scala 3.7.4 / sbt 1.x |
| `lean-pal/` | `PAL ∈ PEG` の Lean 証明（Kim–Park 成果物 `PegSeparation` 経由、**条件付き**） | Lean v4.31.0 + Mathlib v4.31.0（pinned） |

`docs/palindromes-in-peg/` は素の PEG で回文言語を書く構成のアーティファクト（Python が参照実装、Rust runner、検証ログ）。入口は `STATUS.md`。

## よく使うコマンド

`lake` は `~/.elan/env` を source しないと見つからないことがある（Makefile は自動で source する）。

### 全体検証（`lean/` + `scala/`）

```sh
make verify        # audit → lean build → lake test → drift → sbt test → 差分ハーネス群
make verify-fast   # 証明中の反復用: audit + lake build のみ
make audit         # scripts/audit-source.sh: sorry/admit/native_decide/axiom を lean/ から排除
make lean          # cd lean && lake build（= 全証明 + Audit.lean の公理監査）
make lake-test     # Lens の golden テスト（lean/tests/golden/Shallot.scala と diff）
make regen         # Lens で scala/generated を再生成（コミット対象）
make check-drift   # コミット済み generated が fresh extraction と一致するか
make scala         # cd scala && sbt -batch test
make diff / json-suite / macro-peg-diff / counterexample-diff   # 差分ハーネス各種
make corpus-golden # golden 再生成（意図的な操作。git diff でレビューする）
```

Lens golden の更新: `cd lean && LENS_UPDATE_GOLDEN=1 lake test`（その後 git diff を確認）。

### lean/ 単体

```sh
cd lean && lake build              # defaultTargets = Shallot + Lens
cd lean && lake build Shallot.Peg.Soundness   # 単一モジュール
cd lean && lake exe extract --out <dir> --pkg shallot.gen
```

### scala/

```sh
cd scala && sbt -batch test                       # 全サブプロジェクト
cd scala && sbt -batch "pal/test"                 # PAL 移植のみ（直列実行、-Xmx8g）
cd scala && sbt -batch "shallotCli/run run ../examples/fact.shl"
cd scala && sbt -batch "shallotCli/run eval \"1 + 2 * 3\""
cd scala && sbt -batch "pal/testOnly pal.SomeSuite"   # 単一スイート
```

この WSL2 環境では sbt が `/run/user/1000` の AccessDenied で起動しないことがある。回避: `mkdir -p /tmp/xdg-1000; XDG_RUNTIME_DIR=/tmp/xdg-1000 sbt -batch ...`。

### lean-pal/

```sh
make lean-pal                                   # 初回: Mathlib cache 取得 + build
cd lean-pal && lake build --quiet PalPeg        # 通常の反復
cd lean-pal && lake build PalPeg.GSScan         # 単一モジュール
```

`make verify` には**含まれない**（Mathlib cache のダウンロードが必要なため）。全体ビルドは 9,000 job 超で長い。

## アーキテクチャ上の要点

### lean/ — Shallot と Lens

- `Shallot.lean` がルート import。新モジュールはここに追加しないとビルドも監査も通らない。
- 具体構文パーサは「検証済み汎用 PEG インタプリタを文法値に適用したもの」であり、PEG の soundness/completeness/determinism がそのまま Shallot パーサに効く。JSON（`lean/Json/`）と Macro PEG（`lean/MacroPeg/`）も同じ枠組み上に載っている。
- `lean/Audit.lean` の `#guard_msgs in #print axioms` ブロックが公理監査の本体。ビルド成功 = 標準 3 公理（`propext`/`Classical.choice`/`Quot.sound`）以外を使っていない証明。旗艦定理を足したらここにも guard を追加する。
- ポリシー: `sorry`/`admit`/`native_decide`/追加 `axiom` は禁止（`scripts/audit-source.sh` がソースレベルで、`Audit.lean` が意味レベルで弾く）。
- **Lens の抽出可能サブセット**は `docs/extractable-subset.md` に凍結されている。抽出対象コードでは `partial def`/`unsafe`/`opaque`、添字付き inductive、Prop を運ぶコンストラクタ、`do` 記法（明示 `match` で書く）、whitelist 外の typeclass は使えない（fail-loud）。
- `scala/generated` は**コミット済み**の生成物。Lean 側を変えたら `make regen` → 差分をレビュー → コミット。`check-drift` が CI 相当の門番。
- 差分ハーネス（`corpus/`）のケーステーブルは Lean で一度だけ定義され、抽出される。Lean-native 実行と抽出 Scala 実行が `corpus/golden/*.jsonl` と三者一致することで、抽出器・ランタイム・評価器のドリフトを検出する。
- TCB: Lean カーネル、Lens、手書きランタイム `scala/runtime`（`shallot.rt`）、Scala コンパイラ、JVM。

### scala/ の sbt 構成

`runtime`（strict lint）→ `generated`（lint 免除）→ `shallotCli`（strict）。`macroPegRef` は vendored 参照実装（lint 免除、`UPSTREAM.md` 参照）、`macroPegDiff` はその独立差分ドライバ、`pal` は Python 生成器の移植でテストは Python 出力とバイト一致を比較する。手書きコードは `-Werror -Wunused:all`。

Scala 3 は**ブレース構文で書く**（indentation syntax / `then` / `end` は使わない）。サブエージェントに書かせるときも指示に含める。

### lean-pal/ — PAL ∈ PEG

- 唯一の仮定は `PegSeparation.RealTimeTM.RecognizedBy PalPeg.PAL`（厳密実時間多テープ TM が PAL を認識すること）。Galil 機械をこのモデルに書き下す作業が進行中で、無条件の `PAL ∈ PEG` は**未完**。対外的な言い回しは「条件付き」を崩さない。
- `PalPeg.lean` がルート import。`PalPeg/` には未 import・未追跡のモジュールが大量にある（追跡 110 / 実在 500 超）ので、`lake build --quiet PalPeg` が通ったことと「そのファイルがビルドされた」ことは別。新モジュールは必ずルートに追加する。
- 公理監査は `PalPeg/Axioms.lean` の guard。`lean/` の `audit-source.sh` は `lean-pal/` を**見ない**ので、こちらでは `sorry` 排除を自分で確認する。
- 層構成（下から）: 語の組合せ論（`Words`/`Groups*`）→ 仕様（`Chain`/`Stages`/`Assembly`/`OnlineMachine`）→ GS 分解・前処理（`GSScan`/`GSDecomp*`/`GSPreprocess*`）→ 実時間照合（`GSRealTime`/`GSVerifier*`/`StageMatcher`）→ 中央フラグ（`Manacher*`/`MiddleJob`/`BorderJob`）→ スケジューリング（`RTQueue`/`Schedule`）→ テープ化（`TapeLib`/`*Tapes`）→ 有限制御 `ProgLang` 移植（`*Prog*`）。詳細は `lean-pal/README.md` の「ファイル構成」。
- 設計・現状の正本は `lean-pal/ASSEMBLY_PLAN.md`（組み立て方針、新しい順に追記）と `lean-pal/DESIGN_SCA_PAL.md`、`ALGORITHM_SPEC.md`。
- 旧制御層は `lean-pal/archive/single-prog/` に退避済みでビルド対象外。

## lean-pal 無条件 PAL ∈ PEG の進捗（2026-09-19 時点）

**進捗の計器は `PalPeg.PalInPeg.unconditional : RecognizedByTotalPEG PAL` の公理リスト。**
目標は閉じた項として存在し、足りない義務は `axiom` で明示されている。
`PalPeg/Axioms.lean` の `#guard_msgs in #print axioms` がラチェットで、
1 個外すと guard が壊れて更新を強制される。**標準 3 公理だけになったら §10.5 達成。**
いまは **1 個**の義務が残っている（2026-09-19, n175 で 4 → 3、n246 で 3 → 2:
`obligation_shiftPalResiduesAlongRun` は `WindowPack.shiftPal_of_windowRunPack` で証明。
2026-09-20, n282 で 2 → 1: `obligation_cycleOracleOnPackedRun` は定理
`PalInPeg.cycleOracleOnPackedRun`＝`OracleReady.cycleOracleOn_of_readyLeaves` になった）:
`obligation_localRealization`。経路は `PalPeg/PalInPegUnconditional.lean` の
docstring に表で記録。

**trace 形は run 形から導けた（n175）。** trace は `st 0 = boot w` から始まるので
`st 1` で `InvLPC` が立ち（`GalilTrailFront.inv_of_boot_tick` ＋
`GalilOracleMC2.invLPC_of_boot`、`BranchSupply.cpack_alongTrace` と同じ recipe）、
`GalilTrailFront.steps_between` で `st j`（`1 ≤ j ≤ Tc`）に届く。
**新しい定理は 1 本も書いていない。既存部品を繋いだだけ。**

**2026-09-19（n112→n113）: 旧 `obligation_shiftPalAtScanStates` は偽の疑いが濃かったので
run 形／trace 形の 2 つに割った（3 → 4）。**
`ShiftPal` の結論は「chain の周期が入力語 `w` の本物の周期である」という履歴の事実だが、
guard の `BigPack2MG7W` の場を一次情報で全部展開したところ、chain の周期テープの中身と
`w` を結びつける場が 1 つも無かった（`w` に触れる場はヘッド、chain に触れる場はカウンタ）。
`hpack` が偽だったのと同じ欠陥で、CLAUDE.md 自身が `ShiftPal` を過剰量化の 5 例の
1 番目に挙げていた。機械検査した反証はまだ無いので `REFUTED` とは書いていない。

**差し替え済み**（n113）: `obligation_shiftPalAlongRun`（`InvLPC` 起点から到達する
scan 状態）と `obligation_shiftPalAlongTrace`（`PreTraceIMW` の trace の scan 点）。
どちらも履歴が run で固定されるのでこの欠陥は無く、放電器も用意してある
（`ShiftPalAlongTrace.shiftPal_alongTrace` / `CloseoutBundleRun.shiftPal_of_run_B`、
残差はどちらも `H_readsShift` ＋ `H_freshShiftAtShiftEntry` ＋ `periodOnly = false` 分岐）。
**偽の疑いが濃い前提 1 個より、真であろう前提 2 個を採った。** 詳細は `CLAUDE_RESUME.md` n112/n113。
`marksEntry` は 2026-09-19 に放電（`CloseoutMarksPack.packRunR_MW_marksFree`、n110）:
唯一の消費者だった `packRunR_MW` の 2 箇所は `MarksInv'` を作るためだけにあり、
`CloseoutPackRun17.marksInv'_of_run'` が `H_marksEntry'` なしで run 全点に
それを与えていた。4 入力（`first ≠ 4` / `hfloor_of_invLP2` /
`windowInOrigin_alongRun` / `cpack_of_entry`）は `InvLPC` の origin で全部無償。
`WindowInOrigin` の障害だった `Fair` は、モデル欠陥 `M-fallbackPlace` を直した
時点（n107）で消えていた。
**「`hme` の producer は `hpack` だけ」という過去の自分の記述を一次情報として
扱っていたせいで 1 日以上見落とした。**

**guard を狭く切ると義務が増える。** 2026-09-19 に `ChainPositionInvariantWithShiftPhase.payload`
の guard が `ScanNR`（`mode = scan ∧ replaying = false`）だったせいで replay 中の
台帳が抜け、その穴埋め用に `MatchRest.replayPay` という義務が立っていた。
guard を `mode = scan` に広げたら**義務ごと消えた**。同型の例が 8 件
（`LagCan` は `.watch` だけ / `CentreRep` は `rewind ∨ replayStart` だけ /
`VerRep` は `.watch` だけ …）。**新しい場を足す前に、既存の guard が必要以上に
狭くないかを見る。**

**run 形（`∀ z, Steps j x z → …`）と trace 形（`∀ i ≤ Tc, … (st i) …`）は別物。**
`Tick` は決定的でないので trace 形から run 形は出ない。run に沿う事実は trace 形で書く
（`obligation_verifierRunAlongRun` が落ちたのはこの切り直しだけが理由）。

**自分が書いた義務も過剰量化しうる。** 2026-09-19 に `obligation_matchRest_alongTrace` の
場 `canRNext`（`canRight (right s.right)` を trace 全域で、mode guard なし）が
**偽**だと機械検査で確定した（`MatchRestRefute.matchRest_alongTrace_false`）。
報告点は `position right = 2|w| − 1` ちょうどなので 2 歩分の余裕は原理的に無い。
**「着地状態の性質」を「源状態の性質」として書くと 1 歩ぶん強くなる。**
義務を書く前に、消費者がその分岐で何を要求しているかを読む。

* 公理は**1 場ずつの原子**に分解する（束ねると「1 個外す」が測れない）
* 義務は**trace 形**で書く。global 形（`∀ c s`）は放電の材料が run に沿ってしか
  存在しないので**原理的に落ちない**（`hpack` / `hav` が偽だったのと同じ病）
* `pal_in_peg` という名前は無条件の最終定理のために予約。部分結果は
  `PalInPeg.given_<残差>`

### 旧記述（前提を数えていた時期のもの。上の計器に置き換わった）

**状態: 全体 build 成功・標準公理のみ・無条件 PAL は未完。正本の最上位は `pal_in_peg_final39`（`CloseoutFinalFour`、**7 前提・反証済みゼロ**: `hSP` `hme` `hor` `hC` `hbgP` `hmatchP` `hsdP`。2026-09-19 に `hfour` を**何も足さずに**放電——`CloseoutPackRun40.ChainPosInv'`＝`Coupled` を `Coupled'` に強めた構造が `four_of_other'` を直接使えるため、`ShiftLocalRun` が run に載せた。索引の別名は `Canonical.pal_in_peg_of_seven_leaves`）。一代前は `pal_in_peg_final30`（`CloseoutFinalW`、8 前提、`hfour` を含む）。`hfour` を落とした既存 3 版はどれも代わりに**偽の前提**を取っていた: `final31` は `hav`（`ConsumeAvailRefute.hav_false`、過剰量化の 8 例目）、`final36`/`final37` は `hpack`（`CloseoutPackRefute.hpack_false`）。`pal_in_peg_final37`（`CloseoutFinalW4`）は 4 前提だが `hpack` が**偽**（`CloseoutPackRefute`、2026-09-19 反証）——`ChainPack` は run 沿いの束を一状態述語として書いており `ChainPosInv2` からは出ない。よって 8 → 4 の削減は偽の前提を通っており、前進として数えない。計画書 §10.5（前提ゼロ）は未達。** 全モジュール sorry なし。新モジュールは `PalPeg.lean` の `import PalPeg.GalilSegmentConstruct` の直後に登録。

### 1. 最上位の定理と残りの仮定

| 定理 | ファイル | 仮定 |
|---|---|---|
| **`pal_in_peg_final37`** | **`CloseoutFinalW4`** | **4 前提**: `hSP`（scan 状態の `ShiftPal`）, `hor`（`CycleOracleMC3`）, `hC`（`H_realizeLIMW'`）, `hpack`（`ChainPosInv2 → ChainPack`）。`final25` の 8 前提のうち `hsc`/`hws`/`hsl`/`hni` は**反証**、`hee`/`het` は `front` ポテンシャルで証明、`hme` は `hpack` の `marks` 場に包含。残差の正本は `lean-pal/CLOSEOUT_LEDGER.md` |
**残差は 3 つの壁に統合（n77）**: (1) `ScanToScan`（run の区間分解、`CloseoutSegment`）— `hSP` のラウンド境界・最初のラウンドと `hor` の found 葉（`ShiftRoundC`）がここに帰着、(2) `hC`（`H_realizeLIMW'`）、(3) `hpack` のモデル欠陥 (e) 部分（`marks`/`hwin`）。`hor` の橋は `CloseoutOracleBridge.hor_of_H_oracle`、`H_oracle` の葉は `CloseoutOracle8.h_oracle_of_leaves7` で 11。
| **`pal_in_peg_final30`** | **`CloseoutFinalW`** | **8 前提・反証済みゼロ**: `hSP`, `hme`, `hor`, `hC`, `hfour`, `hbgP`, `hmatchP`, `hsdP`。`final29` の `hsl`（`ShiftLocalG`）も偽だったため（`beginShiftVM'` は `shiftGuardVM` を含まない）、弱化ではなく**場ごと削除**。wave 8 で trail 橋を `ChainPosInv` に載せ替えた結果 `IPackMG.shift` を読む者が消えたので可能になった。非破壊複製: `CloseoutPackW`（`IPackMW`）/ `CheckW` / `OracleW`（`packRunR_MW` は shift 仮説ゼロ）/ `FinalW`。`hC` は `PreTraceB` を取る `H_realizeLIMW'` へ |
| **`pal_in_peg_final29`** | **`CloseoutWeakFinal`** | **9 前提・偽の前提ゼロ**: `hSP`, `hsl`（`ShiftLocalG`）, `hme`, `hor`, `hC`, `hfour`, `hbgP`, `hmatchP`, `hsdP`。`final27` の 5 前提のうち `hws`（`∀ w y, WatchShiftG`）は **偽**（`CloseoutPackRun32`: `ChainStep.backDone` 生まれの watch は `distance = reset`）。2 つの弱化で除去: trail 橋を `ChainPosInv` に載せ替え（`CloseoutShiftS`/`ShiftFinal`）、pack 側は必要な `ShiftLocalG` を直接取る（`CloseoutShiftWeak`）。後ろ 4 前提は Run34 の guarded 分岐仮説 |
| **`pal_in_peg_final27`** | **`CloseoutExtraFinal`** | **5 前提**: `hSP`, `hws`, `hme`, `hor`, `hC`。`final26` の 7 前提から `hee`/`het` が消えた。理由: 両者は `packRunR_MG27` の `hprefix`（run 各点の `Extra7`＝`canRight`）を作るためだけに存在し、その上界は front ポテンシャル（`front = position + replay value`、`front_stepsAll_mono` で単調、非 replaying では `front = position`）に乗って run の出口から遡る。出口の上界は `CycleOutMC3` の定義と `ReportPointAt.atPlace` が持つ（`CloseoutFrontExtra`/`ExtraFree`/`ExtraOracle`） |
| **`pal_in_peg_final26`** | **`CloseoutStageFinal`** | **7 前提**: `hSP`, `hws`, `hee`, `het`, `hme`, `hor`, `hC`。`final25` の 8 前提から `hsc`（`H_stageScan`、反証済み）が消えた。理由: `CycleOutMC3` は両出口で `InvLPS` を返しており（`GalilInvPlus3:193, :212`）、boot も `Inv` 分岐に着地する（`invLPC_init:94`）。チェックポイント層を `InvLPS` 上で再走させれば `hstage_of_scanBranch` は呼ばれない（`CloseoutStageCheck`/`StageBoot`/`StageOracle`）。残差の正本は `lean-pal/CLOSEOUT_LEDGER.md` |
| `pal_in_peg_final25` | `CloseoutPackRun51` | 8 前提: `hSP`（scan 状態の `ShiftPal`）, `hws`（`WatchShiftG`）, `hee`（`Extra7` 入口）, `het`（`Extra7` tick）, `hme`（`H_marksEntry'`）, `hsc`（`H_stageScan`、**反証済み**・再切り出し待ち）, `hor`（`CycleOracleMC3`）, `hC`（`H_realizeLIMG2'`）。`final24` の 11 前提のうち `hbs`/`hls`/`hsl` は木の中の定理で供給済み（`InvLPC` の chain は常に idle → `ShiftLocal*` は空虚）。残差の正本は `lean-pal/CLOSEOUT_LEDGER.md` |
| `pal_in_peg_final24` | `CloseoutPackRun46` | `hSP`（scan 状態の `ShiftPal`）, `WatchShiftG`, `Extra7`（`scanAvail` のみ）入口/tick, `H_extraEntry3/Tick3`, `H_marksEntry'`, `H_shiftLocalG`, `H_realizeLIMG'`, `H_shiftLocalC`, `H_stageScan`, `CycleOracleMC3`, `H_bootShift`, `H_landShift`, `H_realizeLIM'`（最上位。found 葉は `foundExit_compare_final9`、readiness は `PostRunC`、核は `chooseVm_tapeActK`；詳細 `CLAUDE_RESUME.md` n74；残差の正本は `lean-pal/CLOSEOUT_LEDGER.md`；**モデル欠陥: chain 誕生で `periodOnly` 未リセット（修正保留）**；readiness 帰納段 `postRunF_step` 成立；found 葉は `foundExit_compare_final14`（`FoundExitLPS`）、readiness 往復は `galilFrameS` 上で閉、core `shiftVm_tapeActKQ` K=28）；`BigResid6` は `bigResid6_of_lpackM2`（残 `ShiftPal`・`WatchShift`）；readiness は `PostRunF` 往復（Preload31）；readiness は `ScanRealized` 矛盾（n49）で `PostRunPh/F` へ再基底化中；rewind 角は `MarksEntry` 1 点；found 葉は `foundExit_compare_final19`；`ShiftLocal` は反証→`ShiftLocalG`（final16、`IPackMG` 再配線中）；`rewindMargin` は `CentreMargin` 1 葉に集約、`.double` 出口義務は Scala に合わせ再定式化要） |
| `pal_in_peg_final4` | `GalilFinalAssembly4` | `H_oracle2`（boot 側 oracle、`CycleOracleMC2C`）, `H_needLB'`, `H_realizeLB'` |
| `pal_in_peg_final2'_trailF` | `GalilTrailProof` | `H_oracle`, `H_trailF`, `H_base`, `H_realizeL'` |
| `pal_in_peg_of_local_core` | `LocalLatchRealize` | 局所 oracle（`LocalSysConcrete.localSys_oracles` の残差）+ `H_ledger`（`LocalLedgerShift` で放電済み、`habs`/飢餓同値が残り） |

- `H_oracle2` ← `GalilFinalAssembly4.h_oracle2_of_leaves` ← `GalilOracleMC3.h_oracle_of_leaves''`（`hquiet`/`houtReplay` 除去、`hfoundReplay` 追加）。葉の現状は §3。
- **重要（2026-09-19 訂正）**: `h_oracle_of_leaves*` は**全部** `GalilFinalAssembly.H_oracle`（= `CycleOracleMC`、origin/着地とも `InvL`）を結論とする。最上位の `hor` は `CycleOracleMC3`（origin/着地とも `InvLPS`）で**別物**。橋は `CloseoutOracleBridge.hor_of_H_oracle`（`H_oracle` ＋ `InvLPS` 着地 lift）。差は 2 つ（不変量と、中心進行 vs `mu` 進行）。**型名の一致で producer を判断せず、定義を展開して origin と結論の不変量を照合すること。**
- **重要（2026-09-19 追加、同じ欠陥の 5 例目）**: 名前付き葉が偽になる典型は「唯一の消費者が到達しない状態まで量化している」こと。`ShiftPal` / `H_advanceT` / `MatchTickC` / `hpos` / `ShiftAtMismatchC` が全部これ。**新しい葉を測るときは、まず消費者のその分岐で何が scope に入っているかを読み、それを文に入れる。** `ShiftAtMismatchC` の場合は `SegEndS` の出口が「cycle 終端 ∨ 不一致」の選言で、不一致側では cycle 終端が未知なのに葉が主張していた（Scala `ScaffoldGalil.scala:254` の `canShift` は `periodOnly` のとき `singlePositive cycle` を要求し、周期中の不一致では `beginFallback()`）。反証は `CloseoutShiftMismatch.shiftAtMismatchC_false_at_nonterminal`、再定式化は `ShiftAtMismatchN` / `roundOne_of_segRun_N`。
- `H_needLB'` ← `H_trailF`（`GalilTrailProof`）← scan 側 `GalilTrailScan/Budget/Front/Sane/Order` + verifier 側 `GalilTrailChain/Assembly`。残りは scan 不変量 pack `RadPack`（`GalilTrailRad`、進行中）1 つに集約。
- `H_realizeLB'`: 局所実現。`LocalSysConcrete`（tick/到着/stutter/出力 oracle は無仮定）、`LocalRealizesScan`（rewind/choose 閉）、`LocalRealizesPhase`（shift/copy/home/markEnd 閉、fpp は局所 1 量子のみ残）。**scan/init/replayStart は抽象 tick の非決定性で閉じない**（§2）。

### 2. 設計上の重要事実（2026-09-17 深夜〜朝に判明）

- **訂正（2026-09-19）**: 下の「`radiusAfter`（search 活性∧chain idle なら不変）」は
  **古い**。一次情報 `PalPeg/GalilScaffoldTopSearch.lean:37` は
  `def radiusAfter (s : GalilVM) : Counter := GalilScaffoldCounter.inc s.radius` で
  **無条件の `inc`**。`backgroundS` は右ヘッドも radius も変えないので
  `position center + value radius = position right` は background で保存され、
  matched compare では両方 +1。**過去の自分の記述を一次情報として使わない。**
- **`Fair` 完成（`GalilTickFair`）: `Tick ∧ Fair` は全状態で一意、残差なし。** 抽象 `Tick` 単体は一意でない（`GalilTickDet`）: (a) broken chain で `restart` と `scan_wait` stutter が競合（Scala は restart 優先）、(b) 探索量子は `ReadFun GalilDpCode.code` + `PrepareControl.Tick` 決定性を仮定すれば関数的、(c) chain は関数的、(e) `beginFallbackVM'`（着地場所）が非関数的。
  **訂正（2026-09-19, n171）: `initVM`/`replayStartVM` は `periodOnly`/`walker` を自由に
  していない。** 定義（`GalilScaffoldTopReplay:20,33`）の 15 連言の最後 2 つが
  `t.periodOnly = s.periodOnly ∧ t.walker = s.walker` で、既に固定されている。
  よって `Fair.keepsSearchCursor` は `Tick` からタダ（`tick_init_cases` /
  `tick_replayStart_cases` で `initVM`/`replayStartVM` を取り出すだけ）。
  `Fair` の実質は 2 場: `restartFirst`（broken chain のときの restart 優先。
  `restartGuardVM` が `chain = .broken w` を要求するので broken chain のない区間では空虚）と
  `fallbackPlace`（`beginFallbackVM'` が place `p` を長さ上界だけで縛っているのが原因。
  実機は search の walker から一意に計算するので、これは**形式化のミス**——
  `beginFallbackVM'` に `t.fpp.walker = t.walker` を足せば消える）。`tickFun`（`GalilTickFun`）は choice で 1 つ選ぶだけ。**方針**: モデルは編集せず（使用箇所 300 超）、Scala の優先順位と固定値を表す `Fair` を定義して `Tick ∧ Fair` の一意性を証明（`GalilTickFair`、進行中）。構成側の witness と局所 step が `Fair` を満たすことを別途確認。
- **偽だった葉（同じ型: 任意状態への量化）**: `hquiet`（`SearchQuiet` は「found に到達しない」と同値、`GalilLeafQuiet`）、`houtReplay`（`InvScan` に出力なし → `InvScanO := InvScan ∧ OutputRel`、`GalilLeafOutReplay`）、`hpres`（`SearchReady` は負債 1 単位分保存されない → `SearchReadyB := ReadyRem ∧ RunEntriesAll`、`GalilLeafPres`；`watchSegE_construct` は再証明要、`GalilSegmentConstructB` 進行中）、`hpos`（区間終端の右ヘッド位置、`GalilLeafPos`: 区間予算 `position r.right + count true ≤ 2m−2` から出す）。
- **過剰量化の 8 例目（2026-09-19）**: `pal_in_peg_final31` の
  `(hav : ∀ w (st : ℕ → State GalilVM) (i : ℕ), ConsumeAvail (st i).vm.chain)`。
  `st` が無制約関数なので `∀ z : ChainVM, ConsumeAvail z` と同値で、
  `gap = false` かつ右も incoming も空な verifier を持つ watch で破れる
  （`ConsumeAvailRefute.hav_false`）。正しい形は run 形の `CloseoutVerSide.VerRun`。
  **run に沿う事実を `∀ st` で書くと、常に状態全体への全称に潰れる。**
- **過剰量化の 7 例目（2026-09-19、自分で撒いた）**: `M-watchBreak` 修正の下流で
  `(hnobg : ∀ w' v, ¬ BreakStepPos w' v)` と書いたが、`BreakStepPos` は「正 lag ＋ 不一致」
  なのでそういう `w'` は存在し、**この前提は偽**。義務は必ず**状態局所**に書く
  （`NoBgBreak x := ∀ w v, x = .watch w → ¬ BreakStepPos w v` を run の各点や不変量の場として
  持たせる）。`∀ w' v, ¬ BreakStepPos w' v` と書いてはならない。
- **モデル欠陥 `M-watchBreak`（2026-09-19、機械検査済み）**: Scala 正本
  `ScaffoldChain.step()` は `Mode.Watch` かつ `lag.sign > 0` で `consume()` を呼び、
  不一致なら `Mode.Broken` に落とす（`ScaffoldChain.scala:136,178`）。Lean の `ChainStep`
  には `.watch → .broken` の構成子が無く、break は `ChainMatched.breaks` にしか無い上に
  その `BreakStep` は `zero w.lag = true` を要求するので **lag ゼロ経路のみ**。結果、
  正 lag ＋ 不一致の watch に**後続状態が存在しない**（`PalPeg.ChainStepGap.
  no_chainStep_at_positive_lag_mismatch`）。**これが `WatchOk` が偽である根本原因。**
  直すには `ChainStep` に正 lag 版 break を足す（影響 202 箇所、`M-periodOnly` と同規模）。
- **`WatchOk` は 2026-09-19 に無条件で反証された（機械検査済み）**: `PalPeg.WatchOkRefute.watchOk_false`
  （引数は `WatchOk Ok` のみ、公理は `propext`/`Quot.sound`、`sorryAx` なし）。`born` が
  **任意の lag/margin** で `Ok` を与え、`good` がその正 lag で `Good`（period テープの焦点記号と
  入力右ヘッドの記号の一致）を強制するが、`born` の仮説（`canRight ver` と `OnBlock v`）は
  両者を関係づけない。証人は `bornVer`/`bornBlock`（`symbol (moveRight bornBlock).focus = some 0`
  と `read (right bornVer) = some 2` をカーネルで計算）と `lag = ⟨[0],[]⟩`。
  `born` の過剰量化は `ChainOk` の設計が強制している（`| .back v _ _ _ ver => OnBlock v ∧ canRight ver`
  が lag/margin を無視し、`ChainStep.backDone` はそれを watch へ継承する）。
  **帰結**: `hready : ChainTickable` を `ChainOk`＋`WatchOk` 上に載せ替える道は閉じた。
  消すには `ChainOk` を `.copy`/`.back` で lag/margin を縛り、誕生義務を `.back` の場として
  持たせる再設計が必要。これは `hSP` の唯一の残り障害。
- **偽だった仮定（前夜まで）**: `periodLength` +1、`hbg`、`hfast`、`lookChain` 常時 2 手、`ReplaySpan`（反例 `aaaaabaaaab`）、`Trail`（fallback 後は右スタック非空 → `TrailF`）、`ReplayStageInv`/`FoundStage` の普遍形（到達可能 found に限定 → `ReplayBudgetR`）。
- found 時の半径 k ≤ 2n（`found_radius_le_two_period`）が replay 予算の鍵。`OffCompareFoundStage` は `GalilFoundStageInv` で閉じた。

### 3. `H_oracle2` の葉（`GalilOracleMC3.h_oracle_of_leaves''` 基準）

閉: `hex`, `hsearch`, `hsegmentM`（`segment_of_invLPC`+`hends_C`）, `hends`, **`hbudget`（`replayBudgetR_of_decodes'` を `decodesC` で — `CloseoutOracle8.hbudget_C`）**, **`hrs`（`restartShape_sharedC` — `CloseoutOracle8.hrs_C`）**, `hstr`（`Final4` で不要）。
**訂正（2026-09-19）**: `hended`/`hlastMatch` は**閉じていない**。producer（`GalilLeafReport.hended_C`/`hlastMatch_C`、`GalilOracleMC4.hlastMatch_C'`）は側入力 `hpres`（bare `SearchReady` が search quantum で保存される）を取るが、それは**偽**。`GalilLeafPres.searchReady_run_true_iff` が `SearchReady v' ↔ 1 ≤ value v.search.debt` を証明済みで、debt 0 で破れる（機械検査: `CloseoutPresRefute.hpres_fails_at_zero_debt`）。閉じるには `GalilLeafPres` が指定する `SearchReadyB := ReadyRem ∧ RunEntriesAll` への再切り出しが必要。
**`Decodes` はタダ**: `GalilFinalAssembly2.decodesC` が証明済み（`Decodes` は `P.centre`/`P.place` だけを縛り、`centreC`/`placeC` は `s.center` の具体関数）。`Closeout*` 全域の `hP : Decodes (PofC …)` 素通し仮説は全部不要。
**訂正（2026-09-19, n114）: 探索（DP）側は無条件で証明済み。**
`GalilDpCorrect.initial_correct`（fresh プリロードから `Result`）、
`GalilScaffoldSearchRun.dp_quanta_safe` / `calibrated_quanta_safe`
（run 相の探索状態から `SafeQuanta` ＋ `Result`）、
`GalilTickFair.readFun_code`（`decide` で証明、`safeQuanta_unique` の前提）、
`GalilMinimalPeriod.result_least`（`Result` → `Candidate` ＋ 最小性）は
すべて標準 3 公理のみで、既に `GalilScaffoldStagePrepare` / `GalilBranchInvariants2` /
`GalilScaffoldChainFallback` で消費されている。
`CloseoutPrepInputs3.PrepInputsG3` が `Result` を仮説として束ねているのは
**ステージ層とそこの間が繋がっていないだけ**で、found 経路の残りは新しい数学ではなく層の配線。

**訂正（2026-09-19, n181/n182）: `hpres` の後継 `ReadyFuel` は反証済み**
（`PalPeg/ReadyFuelRefute.not_readyFuel_v0`）。`.run` 入口の債務（= 2）が
`K = headRank`（入力長に比例）回のマッチを払えと要求していた。
**正しい乗り物は `GalilReplaySpan.ReadyClosure`**（`ready`/`seg`/`restart` の 3 場）で、
`CloseoutPreload11.readyClosure_S2` が `PostRun` ＋ `RestartS2` から出す。
消費者（`CloseoutReportCase`）が `ReadyFuel` から取り出しているのは `SearchReady` だけなので
置換は 1:1。`CloseoutContracts.StageEntryC` も `fuel` 場が偽なので切り直しが要る。

残: `hpres`→`ReadyClosure` 版への切り直し（上）; `hstage`（`ReplayStage` を `GalilReplaySpan` 内で持ち回り、進行中、mid-replay restart の `3·radius ≤ 5·last` が新義務）; `hshape`（`StartShape`）; `hlastMismatch` の最終文字分岐（`LastMismatchReport`）と `EntryRefreshed`; `hmismatch` ← `GalilLeafMismatch` の残差 `hdp`（DP pack、進行中）/`hfb`（fallback tick 数、進行中）/`hpos`（区間予算前提を pieces に追加、進行中）; `hfound`/`hfoundBg` ← 着地不変量に `Restarted`/`StageEntry` を追加（`GalilInvPlus3`、進行中）+ found tick からの経路構成（未着手、最大の残り）; `hfoundReplay`（replay 中 found の経路、未着手）。

### 3c. 2026-09-19 の追加（`M-periodOnly` とモデルの忠実性）

- **モデル欠陥 `M-periodOnly` を実装**: Scala `ScaffoldChain.start()` の `periodOnly = false` と `cycle.reset()` が Lean に無かった。`chainBorn (found) (x : ChainVM) := x.isIdle && found`（誕生条件は「その遷移で新しい chain が実際に始まること」）と `afterBirth born s`（`GalilScaffoldTopSearch:70,77`）を入れ、`compareFound`/`backgroundS`/`background_found_step` の遷移先を包んだ。全体 build 緑。回帰テスト `CloseoutPeriodOnlyRegression.birth_resets`。
- 伝播を止めた補題: `not_shiftGuard_afterMismatchB`（誕生時の chain は `chainStart`＝`.copy`、`shiftGuardVM` は `.watch` を要求 → guard は立たない）と `refresh_afterBirth_iff`（`P.onLetter = onLetterVM raw`・`P.leftFirst = leftFirstVM` の下で `refresh` は `afterBirth` 不変）。
- 局所側: `LocalTick1` に `birthL`/`abs_birthL`/`inv_birthL`/`stepLocal_birthL`/`matchCtl_congr` と射影群、`bgState` に誕生元 chain を追加、`c₁` を 66 → 67。`tickL1_abs` は側条件 `hbirth` を取り、具体 `PofC` では定理（`CloseoutBirthFrame.hbirth_PofC`）。
- **`hsc`（`H_stageScan`）は反証**: `InvScan` の 11 場は `s.radius` に触れないのに `ReplayStage` は `Canonical radius` を要求。再切り出し `InvScanS := InvScan ∧ ReplayStage`、産出側の第 1 段は `CloseoutStageScan1`。
- **`hme` への合成**: `walkerInOrigin_of_run` の義務 `hcan` は `CPack.front : FrontPack` の `replayPos` + `frontier` と `consume_not_replaying_false` から出る（`CloseoutReplayCanRight`）。新規入力なし。
- `hee`/`het` の残差（scan 状態で `canRight`）は**偽の疑いが強い**。`Inv.input` は右ヘッドの内容を縛るが位置を縛らない。

### 3b. 2026-09-17 朝の追加
- `StartShape` は偽 → `StartShape'`（`GalilReplaySpan.startShape'_of_decodes`）。`hpres` は `ReadyFuel`（`GalilSegmentConstructB`/`GalilReadyFuelUses`）と `RunEntriesAtBegin`（replay、`''_fuel`）に置換。`hfb` 閉（`GalilLeafFb`）。`hdp` → `MismatchDp`+`StageBudgetAt`（`GalilLeafDp`）。`hpos` → 区間予算（`GalilOracleMC4`）。`TrailF` は `RadPack` の tick 保存 1 つ（`GalilTrailRad`）。局所 7/10 モード閉（`LocalWF`）。
- 次: `RadPack` tick 保存、`Fair` を使った scan/init/replayStart の `Realizes`、found 経路 3 葉、各版の集約（MC2/MC3/MC4/InvPlus3/ReadyFuel）。

### 4. 残りの課題（優先順）
1. `Fair` 一意性（`GalilTickFair`）→ 構成 witness/局所 step の `Fair` 監査 → `Realizes` の scan/init/replayStart。
2. found 経路の葉（`hfound`/`hfoundBg`/`hfoundReplay`）: `InvLPS` 上で `prep_segment_construct_of_found` → rounds/break 分岐 → `foundRouteMC_shift`/`foundRouteMC_noshift_dC`。
3. §3 の進行中項目の登録と `h_oracle_of_leaves'''` への集約。
4. `RadPack` で `H_trailF` を閉じる。局所側: `LocalWF`（fpp 量子、側条件）。
5. 局所台帳の `habs`/飢餓同値（`LocalSysConcrete.H_ready`, `H_feed_track`）。

### 5. 再開手順
```sh
cd lean-pal && . ~/.elan/env && lake build --quiet PalPeg > /tmp/b.log 2>&1; echo $?   # 全体（20 分）
cd lean-pal && lake env lean PalPeg/X.lean                                          # 単一ファイル
sed -i "/^import PalPeg.CloseoutFinalBranch$/a import PalPeg.X" PalPeg/Workbench.lean  # 未配線の新モジュール
# 正本の鎖に入るなら PalPeg/Canonical.lean に別名を置く。ルート PalPeg.lean は 4 本だけ
# （PalInPeg / Canonical / Workbench / Axioms）で、直接は足さない。
```
- サブエージェント規約: 定理 1 つ・ファイル:行番号・使う補題名を指定、新規ファイル 1 本、既存編集禁止（例外は明示）、sorry 禁止、`lake build` 禁止、`#print axioms`。中心部の設計は自分で書く。
- 詳細は `CLAUDE_RESUME.md` / `lean-pal/ASSEMBLY_PLAN.md` 先頭。

## 証明はコードである — lean-pal 編集の規律

2026-09-19 に `lean-pal/` は **1143 モジュール・331,884 行・定理 12,593 本**に達し、
「名前を思い出して grep する」運用が破綻した。同じ日に既存部品を 3 回取り落とし
（`CloseoutTerminalN.roundStepC_of_alignN` を「配線が必要」、`CloseoutMarksFree.marks_steps_free`
を「無い」、`CloseoutPackRun49`（`LPackM3`）を「中心台帳は `ChainPack` にしか無い」と書いた）、
そのうえ未検証の断定を重ねた。**証明が進まない直接の原因は難易度ではなく、
「どのモジュールにどの証明があるか」の地図が無いことだった。**

証明はコードである。プログラムを関数・モジュールに整理するのと全く同じ規律を適用する。

### 1. 断定の前に地図を作る

- **コードベース全体を俯瞰していない状態で「○○は無い」「○○が壁だ」と書かない。**
  部品の不在は grep 1 回では示せない。俯瞰は機械で取る（import グラフ、宣言の逆引き、
  主定理からの推移閉包）。
- 「前提が N 本」のような数は、**その定理の型を実際に見てから**書く。
  `#print axioms` は公理の推移依存だけを見るもので、前提の本数は見ない。
- Prop 引数の本数＝前提の本数ではない。`∀ w, H_x w` は 1 本に見えて族であり、
  instance や decidability は自動放電される。**数えるべきは「producer が無い前提」**。

### 2. 1 モジュール 1 責務・名前が中身を表す

- **定理名・ファイル名に番号を入れない。**「いつ書いたか」ではなく「何であるか」を書く。
  `final37` / `PackRun49` / `Oracle8` / `Preload41` のような名前は、番号を覚えていない限り
  意味から引けない。意味のある別名は `PalPeg/Canonical.lean` に置く（**カーネルが検査する
  索引**：名前が動けば build が壊れる。markdown の索引は黙って腐る）。
- 反証済みのものは `refuted_` を前置して、使ってはいけないことを名前で示す。
- **仮定名・変数名は「何を言っているか」を表す。位置で付けない。**
  コウタの指摘（2026-09-19）:「変数名とか仮定につける名前も大事。あとでみたときに
  直感的になんか変なことしてるなってわかるから」。**名前は臭い検出器である。**
  実例: 偽だった前提が `hav` / `hpack` という名前だったので過剰量化が見えなかった。
  `hconsumeAvailEverywhere` / `hchainPackAtAnyState` なら一目で分かった。
  - ✗ `hP` `hR` `hL` `h1` `hz` `hE` `hi` `key` `hm2`（位置・登場順で付けた名前）
  - ✓ `hpre`（`PreTrace`）`hradLedger` `hlagCan` `hipos`（`1 ≤ i`）`hradZero`
    `hentryCounters` `hile`（`i ≤ Tc`）`hpackM2` `hverRun` `hfront` `hshiftLocal`
  - 同じ名前を別の意味で使い回さない（`hpre` を `PreTrace` と `PreloadL'` の両方に
    使うと衝突する。`hpreTrace` / `hpreload` に分ける）。
  - **過剰量化した仮定には、その過剰量化が名前に出る名前を付ける**
    （`…Everywhere` / `…AtAnyState`）。そうすれば書いた瞬間に気づける。
  - **略すのは `h`（hypothesis）だけ。** 人間には長い識別子のコストがあるが AI には
    ほぼ無いので、多少長くても意味が分かる名前を選ぶ。略す場合は規則性を持たせる
    （コウタ 2026-09-19）。
  - **記号だけの接尾辞を新しく作らない。** 既存の `IPackM` / `IPackMG` / `IPackMG2` /
    `IPackMW` 系がその失敗例で、docstring から辿れるのは 2 つだけ:
    | 記号 | 意味 | 出典 |
    |---|---|---|
    | `G` | **G**uarded（shift 半分を mode guard で守った） | `CloseoutPackRun30:81` |
    | `2` | `LPackM2` を併せて運ぶ世代 | `CloseoutPackRun36:73` |
    | `W` | `shift` 場を**落とした**系統（偽の `WatchShiftG` を運んでいた場） | `CloseoutPackW:63` |
    | `I` / `M` | **出典なし**（誰も書いていない） | — |

    `PreTraceIMW` の実体は「各点で `LPackM` と `LPackM2` を持つ pre-trace」。
    `IMW` は「いつ書いたか」の痕跡であって「何であるか」を表していない。
    **新しく書くものは `LandingObligationsAlongTrace` のように、読んで分かる名前にする。**

### 3. コピペ証明を残さない

- 同じ証明を書き足して `_A` `_B` `_2` `_'` の変種を増やすのをやめる。
  変種が必要なら、共通部分を補題に切り出してから分岐させる。
- 既に 88 個の suffix 変種と 233 個の `*_tick` があり、47 本の `pal_in_peg_final*` がある。
  **これ以上増やす前に、既にあるものを探す。**

### 4. デッドコードの判定は主定理との関係でのみ行う

- **「誰も import していない」「名前が参照されていない」はデッドの証明にならない。**
  未登録・未参照のまま健全で有用な部品が実在した（`CloseoutPackRun49` は未登録のまま
  5 定理が健全、修理して 7 定理全部が通った）。
- 判定基準は **主定理 `RecognizedByTotalPEG PAL` との関係**。その義務・前提・残差に
  触れているなら、参照ゼロでも残す。関係が無いものだけを削除する。
- 削除は不可逆なので、削除前に「何がそこにあったか」を索引に記録する。

### 5. 反証を書くのは、証明を試して反証の形の障害に当たったときだけ

- まず証明を書こうとする。`REFUTED` と書けるのは **`False` を導く機械検査済みの定理が
  あるとき**だけ。定理が前提を取るなら `REFUTED（条件付き）` と書き、未構成の証人を名指す。
- 散文の論証・他ファイルのヘッダ・類推・**過去の自分の記述**は一次情報として扱わない。
- **ファイル自身の docstring も一次情報ではない**（2026-09-19, n116）。
  `CloseoutRealize1.lean` は冒頭で §1〜§6 を完了したかのように列挙していたが、
  実際の宣言は 2 つだけで §3〜§6 は存在しなかった（§6 は「latch を迂回する直接経路」と
  読める記述で、信じると `hC` の壁を回避できると誤解する）。
  **宣言の存在は `grep "^theorem"` で確認する。docstring の節番号を数えない。**

## 進捗ノートの扱い

- `CLAUDE_RESUME.md`（ルート）が Claude Code 向けの再開情報の最新。`PROGRESS.md` は古い記録を含む。どちらも新しいエントリが上に来る追記形式で、各エントリは「何を証明したか / build 結果 / 公理 / 未完の部分」を 1 段落で書く。
- lean-pal の節目を記録するときは `ASSEMBLY_PLAN.md` と `CLAUDE_RESUME.md` の両方の先頭に追記する。「全体 build 成功・標準公理のみ・無条件 PAL は未完」の 3 点を必ず明記する。
- `docs/palindromes-in-peg/HANDOFF.md` は Codex の構成ログ（新しい順）。

## その他

- ディスクが逼迫しがち（`make disksize` で確認）。`lean/.lake`、`lean-pal/.lake`、`scala/*/target` が大きい。
- `.claude/worktrees/` はサブエージェント用の worktree 置き場で git ignore 済み。
