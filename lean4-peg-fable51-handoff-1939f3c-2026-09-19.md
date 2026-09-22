# lean4-peg：Fable 5.1への引き継ぎと、残る2公理を閉じる構成方針

対象コミット：[`1939f3c5ee67a4dda8f621cf56332d0cc1f1203a`](https://github.com/kmizu/lean4-peg/commit/1939f3c5ee67a4dda8f621cf56332d0cc1f1203a)（main、PR #74マージ後）。対象は `lean-pal/`、Lean v4.31.0。

この文書は現行ソースを読んだレビューと実装計画である。提案する新しい宣言は未実装・未コンパイル。今回、Pythonのno-restart診断を実行して再現したが、Leanの再ビルドは実施していない。既存定理についての「実装済み」は当該SHAの証明本体を確認した意味であり、今回のカーネル再検査済みという意味ではない。

調査中の更新も反映済み。PR #73の `793e64e` からPR #74の対象SHAへの差分は、`Workbench.lean` のimport位置修正と検証記録の確定。数学的な定義・証明本体は変更なし。リポジトリには全体build成功（9705 jobs）、最終定理の標準3公理＋独自2公理、`shiftPeriodMinimal_packed` の標準公理のみ・`sorryAx`なしが記録された。これは記録の確認であり、本レビューでのLean再実行ではない。

## 1. 私の判断と着手順

**2公理という数から「あと少し」とは判断しない。ただし、局所実現について「producerがない」で止まるのも不十分。既存の局所命令・有限制御・機械化の部品から、具体的な構成へ進める。**

優先する順序は次のとおり。

1. **cycle側のno-restart方針と `hmove` の整合性を決着させる。** 既知の診断が示すbroken分岐を先に調べる。既存の周期補題をさらに積む前に、証明しようとしている不等式がその実行方針で正しいかを確認する。
2. **局所実現は「物理状態を持続させる有限局所機械」を直接構成する。** `ActRule → compStep → LocalStep.realize` を主経路にし、抽象状態から毎回物理配置を作り直す経路を避ける。最初の成果は、queueの有限観測から命令列を選ぶ具体的関数と、その既存抽象操作との対応。
3. **既存の最終定理が使う `entry = 0, q = 1, first = 0` に固定して閉じる。** 任意のentry・q・firstについて公理と同じ一般性を証明することは最終目標に不要。一般化は完成後でよい。
4. **証明した項を最終経路へ実際に接続し、公理監査で依存を消す。** 補題数・ファイル数・文書の版数を進捗にしない。

Fable 5.1は単独で進める。最新のリポジトリ引き継ぎにある「サブエージェントなし・不要な探索や補題追加なし」を引き継ぐ。9/17の旧計画にある親＋5担当方式は今回採用しない。

## 2. 現状：古い引き継ぎ本文より実際の型と証明本体を優先

| 対象 | 現行ソースの状態 | 次の仕事 |
|---|---|---|
| `PalPeg.PalInPeg.unconditional` | 閉じた `RecognizedByTotalPEG PAL`。独自公理2本に依存 | 最終の型を維持して依存を消す |
| `obligation_cycleOracleOnPackedRun` | 公理のまま | `hmove`の成立性・実行方針を解決し、oracleを構成 |
| 探索準備 | `CanonicalSearchReady.ready_of_invLPS_shaped` を `OracleReady` が使用 | 同じ方針を維持する限り再証明しない |
| chain準備 | `CanonicalChainReady.of_window` / `copyReady_packed` と `CanonicalSearchHistory.birthCopy_packed` をproducer内で使用 | 既存の接続を保つ |
| fallback・replay実行 | `CanonicalFallbackInput.begin_at_mismatch` と `CanonicalReplay.segment` をproducer内で使用 | 実行構成と時間上界の未証明部分を区別 |
| shift周期最小性 | `CanonicalChainMinimal.shiftPeriodMinimal_packed` に証明本体あり | oracleの該当引数へ接続 |
| 移動量 | `OracleReady.cycleOracleOn_of_readyLeaves` の `hmove` が残る | 下記§3 |
| `obligation_localRealization` | `H_realizeCanonical` の公理 | 下記§4の具体機械構成 |
| canonical一意性・切り詰め | `tick_canonical_unique` / `canonical_trunc` / `realizes_canonical` に証明本体あり | boundedな実走行のsimulationで再利用 |

`HANDOFF_CODEX_2026-09-19.md` の後半にある「oracleの4葉」は以前の状態。現行producerの明示的な数学的残差は `hshiftPeriodMinimal` と `hmove` であり、前者には既存producerがある。一方、`PROOF_STACK.md` のn267にある「次は境界補題を接続」は、先頭のno-restart診断によって前提から再点検が必要になった。

現行の `Axioms.lean` は、標準公理3本に加え、次の2本が出ることを期待している。

```text
PalPeg.PalInPeg.obligation_cycleOracleOnPackedRun
PalPeg.PalInPeg.obligation_localRealization
```

「build成功・標準公理のみ」という過去ログは部分定理の話と最終定理の話を混在させている。最終結果は必ず `#print axioms PalPeg.PalInPeg.unconditional` で確認する。

## 3. cycle oracle：まずbroken分岐を決着させる

### 3.1 本当に必要な不等式

`OracleReady.lean` の `hmove` は、不一致・shift guard不成立の比較状態について、概略次を要求する。

```text
ℓ = (value s.length).toNat
R = ℓ / 2
r = chosenRadius (rightPlaceから読むfallback窓)
d = R + 1 - r

要求：R ≤ 4*d
```

これはfallback・replayの費用を中心移動量に対して評価するための条件。`begin_at_mismatch` で走行を作れることだけでは埋まらない。

### 3.2 今回実行して確認した診断

```bash
python3 docs/palindromes-in-peg/diagnose_no_restart_fallback.py
```

当該SHAのPythonソースと依存ファイルで実行し、終了コード0で次を再現した。

```text
prefix = abaaaaababaaabaaaaabaaaaabaaaaabaaaa
centre = 45
radius = 25
move = 6
chain = broken

25 > 4*6 = 24
```

このスクリプトはPythonのbroken-restart分岐をメモリ上で除去して実行する。元ファイルを書き換えない。**Leanのpacked-run到達可能性、`hmove`の全前提、cycle公理全体の反証までは示していない。** また、Pythonの実行パラメータと最終Lean witnessの `q = 1` 等の対応も確認対象である。

それでも、no-restart方針を維持したまま当該不等式を当然視する理由はない。最初の作業は次の3点に限定する。

1. 比較直前の `s`、`searchEffect` 後の `vq`、`chainAt` 後の `z`、`afterMismatch` 後の `s1` を区別し、Pythonの `R,d` とLeanの式を対応させる。比較によるrightの+1を二重に数えない。
2. 診断状態がLeanの `InvLPS` 起点、`StepsIMWC`、`MInv`、報告点上界等を満たすか、どの条件で排除されるかを調べる。単に「Pythonだから違う」で終わらせない。
3. **該当する／具体的な条件で排除される／まだ対応未確定**のどれかを、条件名と証拠で記録する。形式反証がない段階で `REFUTED` と書かない。

### 3.3 実行方針の選択

**私の第一候補は、診断がLeanにも対応するなら、Scala正本のbroken restartを復帰させること。** readinessの葉を減らすためにrestartを削った結果、時間評価の根拠を失っている可能性がある。葉の数が一時的に増えても、実際のアルゴリズムと証明の前提を揃える方を選ぶ。

| 選択 | やること | 成立を確認する点 |
|---|---|---|
| restartを復帰（第一候補） | brokenかつ実際のguard成立時にrestartする方針を固定し、readinessの新しい起点を作る | restartの費用・guard・fair性・探索下限を運ぶ |
| no-restartを維持 | `R ≤ 4d` を必要としない費用契約を実際に証明する、または診断を排除する具体的到達条件を証明 | 定数変更だけで済むかは未確認。全入力共通の線形費用が必要 |

restart復帰時は `Fair` を名前だけでそのまま採らない。旧 `Fair.fallbackPlace` はsearch cursorをpinしており、現行の右ヘッドpinと異なる。**restart優先＋右ヘッド由来のfallbackコピー元**という実際に使う方針を固定する。

影響を受ける箇所は限定して追う。

- `GalilTickFair.Canonical` と一意性・切り詰め保存。
- `ShapedRun` / `ReadyTransport` / `CanonicalSearchReady` のno-restart依存。
- `CanonicalPeriod` の `lower = reset`。restart後も下限ゼロとは限らないので、確認済み下限とそれ以下の候補排除を履歴として運ぶ。ゼロという等式を保存しようとしない。
- `CloseoutCheckW` のrun述語とoracleの費用台帳。restartが追加された分を実費用へ入れる。

方針を変えるだけでは公理を証明したことにならない。最終のPALの意味は保持し、bootから新しい方針の走行を構成できるところまで同じ変更で繋ぐ。

### 3.4 no-restart経路が成立すると確認できた場合のhmove構成

既存の証明部品を次の順で使う。

1. `CanonicalFallbackInput.counters` から `ScanInvariant` と `length = 2R+1` を得る。
2. idle・探索失敗ケースは `CanonicalChainMinimal.move_of_idle_missed_packed` を照合する。
3. 生存chainの短半径ケースは、**実際に保持された周期の証人** `h` と `MoveMinimal … h`、`R ≤ 4h` を揃え、`move_of_activeBound` へ渡す。
4. 長半径ケースは `move_of_activePeriodBreak` を候補にする。必要なものは `0 < h`、`2h ≤ R`、現在のspanの周期 `2h`、全てのより短い正周期の排除、そして不一致文字を追加した窓でその周期が破れること。
5. 純粋組合せ論側には `GalilMoveLemma.galil_move_of_minimal_period_break` が既にある。**次に足すべきなのはFine–Wilfの再証明ではなく、実際の比較・予測・境界文字と `hbreak` の対応。** broken状態でもその前提が残ると勝手に仮定しない。

特に `move_of_live_sem_packed` / `move_of_preShift_packed` の現在の

```text
∀ h, MoveMinimal raw C h → R ≤ 4*h
```

を埋めに行かない。`MoveMinimal raw C 0` は `0 < g ∧ g < 0` を要求するため空虚に成立し、この全称前提は `R = 0` を強制する。必要なのは、chainが保持する正の周期証人に結びついた境界条件。**全称前提を証人付きの契約に書き換える。**

また現行producerの `hmove` は任意の `InvLPS` 起点を取るが、最終oracleの運ぶ述語は `PackedFromBoot` を持つ。boot履歴が必要なら、それを葉へ渡す方向へconsumerを修正する。完成済み `PreTrace` の存在を使ってoracleを証明すると循環するので、使うのは既に構成済みの有限prefixまで。

## 4. 局所実現：具体機械を作るためのアプローチ

### 4.1 目標の読み直し

`CloseoutFinalW.H_realizeCanonical` は概略、次の量化順序を持つ。

```text
∃ 有限Q, 有限Γ, 固定t,K, LocalStep L, blank, initQ, outQ, 固定n>0,
  ∀ 非空入力w, ∀ st,Tc,
    PreTraceIMW w st Tc → CanonTrace w st Tc →
      M.SAccepts w ↔ LatchTrue (... stLG' ...) ((|w|+1)*τF)
```

機械は入力より外側で一つ選ぶ。受理同値を要求しているので、任意のtraceと物理テープの全状態を逐一同一にする必要はない。

**提案する主経路は「具体機械の実走行に対するbounded simulation＋期限内report」を証明し、最後に受理同値へ落とす。** その途中で既存canonical一意性を使うのはよいが、無限traceの完全一致を新たな目標にしない。

### 4.2 構成上の転換：物理状態を一次データにする

旧構成には、抽象 `Mirrored1 P` から毎回 `rep : ChainVM → ChainL`、queueのrole配置、不要領域を再選択し、全状態で厳密な `enc_tick` 等式を要求する方向がある。これでは実行履歴に依存する配置を抽象状態だけから回復する仕事が増える。

**物理機械自身を `QPhys × (Fin t → STape Γ)` として作り、role tag・chain配置・buffer bankを実行の間ずっと保持する。** 抽象状態との関係は、物理状態からの抽象化または `Rep` というsimulation関係で証明する。

この変更により次を不要にできる。

- 任意の抽象chainについての全域section `absChain (rep c) = c`。
- 抽象状態から不要領域の履歴を一意に再構成すること。
- 末尾のblankの保持量まで含む `STape` の構文上の等式。
- 「符号化が単射なら局所制御を作れる」という回り道。必要なのは有限窓だけから次の命令を選べること。

物理 `LocalSys` を `L0.apply` の `none` / `some a` から定義すれば、その物理状態の符号化は恒等写像にできる。**消えるのは符号化の往復義務であり、物理実行がGalilの動作を再現する証明ではない。** 後者に作業を集中する。

### 4.3 そのまま使える部品と、使う際の条件

| 部品 | 使い道 | 注意 |
|---|---|---|
| `CloseoutCoreStep.QL` | 有限制御の土台。clock、PC、mode、role、polarity等 | clampした値が到達状態で元の値と等しいことを証明 |
| `CloseoutCoreEnc12.ActRule` | 有限制御・入力・有限窓から次制御と各テープの命令列を返す | `acts` が完全な抽象状態や入力全体を参照してはいけない |
| `CloseoutCoreEnc12.compStep` | `ActRule` を `LocalStep` に変換 | `compStep_apply` はmargin付き・`TEqG`による対応 |
| `CloseoutCoreEnc22` | 9本のcursor配置、queue tailの分解、shiftの≤28局所命令 | 28はshiftの評価。全モードの上界ではない |
| `CloseoutCoreEnc25.RTag` / `roleOf` / `sApply` / `laysS_sApply` | queue配置を有限tagで持ち回る | `deltaOf` はまだ抽象queueを受け取る。有限観測から同じ分岐を選ぶ関数が必要 |
| `LocalChain.ChainL` と各 `local_*` / `absChain_*` | chainの物理状態と抽象動作の対応 | verifier・walkerのqueueも物理配置と入力供給の対象 |
| `CloseoutCoreEnc24.chainTapes_shift` | chain shift時の局所テープ操作 | 元の表現・不要領域・不変量の前提を満たす必要あり |
| `LocalSysConcrete.feedC` / `physWF_feedC` | 入力到着の意味と保存則の参照 | 固定語の追跡保存は「その語の次の文字」に対して示す |
| `CanonicalLocalRealizes.canonical_trunc` / `tick_canonical_unique` | 切り詰めた局所状態の次状態と抽象prefixの同定 | 実際に選ぶpolicyと一致させる |
| `LocalLatchRealize.latchL` | report時の受理bitの保持 | report判定と出力が有限制御から読めること |
| `Local.LocalStep.realize` / `realize_SAccepts` | 局所機械から固定速度の多テープ機械へ | 1入力あたり `n * (7*K+2)` micro-step。n,K,tは全入力共通 |
| `LocalLedgerShift` / `LocalTrackingLatch` | 入力時刻付き進行・期限・report | 物理走行の期限は `|w|*n` 側。古いtraceの `(|w|+1)*τF` と時刻を直結しない |

### 4.4 作るものと接続順

以下の `QPhys` / `ConcreteRule` / `Rep` / `TrackAt` は**提案名**。既存宣言ではない。新ファイルを使うなら、実際の機械を定義する1本（例：`ConcreteLocalMachine.lean`）を中心にし、`NAMED_*` の包装を増やさない。

**L1：固定の物理レイアウトと有限制御を決める。**

- `QPhys` は `QL` を土台に、各queueのphaseと `RTag : Fin 4 × Bool`、chainの有限tag、bufferのactive bit、report/answer/started、必要な有限初期化phaseを持つ。
- 任意長の数値・リストをQへ押し込まない。queueの `lenf,lenr,ok`、job番号、移動量等はテープに置く。比較に必要な符号・ゼロ判定・残高は、更新とともに保つカウンタ表現で局所的に読めるようにする。
- queueは旧 `tView = 4` を無条件採用しない。現行修正版の `tViewQ = 9`（back/focus、near、7 role stacks）を出発点とし、カウンタ等の追加分を明示する。chain内のviewも数える。有限本であれば、少ない本数への最適化は不要。
- 不要領域をその場で全消去しない。`CloseoutCoreEnc18`以降と同じく、不要領域を残してrole/bankを切り替える。新たに必要なゼロ状態は、空の予備bankと漸進的な再充填で供給する。

**L2：有限窓から命令を選ぶ関数を一つ作る。これを最初の実装成果にする。**

最初はqueueの1 sub-stepを対象にする。

1. 有限なqueue観測型を定義する。phase、RTag、必要なcounterの符号・ゼロ判定、各role stack先頭の記号・空印を含む。
2. `sApply` / `deltaOf` の各分岐を、その観測だけから選べる関数へ書き下す。例えば `.reversing` の空／非空／単一要素判定は、局所sentinelと隣接セルから得る。任意長リストの末尾を直接読まない。
3. 実際の `nq` / `acts` を返し、`laysS_sApply` と対応させる。role回転をtag更新として保持する。
4. `ActRule.len_le` を証明し、`compStep` で**具体的な局所機械の項**を作る。この項を本体のfeed/dequeue分岐から呼ぶ。

これは「queueの局所性を仮定したら機械がある」という新wrapperではなく、その局所性のproducerを埋める作業である。

**L3：全モードを同じ命令選択器へ統合する。**

`LocalSysConcrete.Steps` は10モードを持つ。次の単位で、抽象後継・物理更新・各テープの命令数を一緒に確定する。

| 分岐群 | 構成の要点 |
|---|---|
| arrival | 入力bitを有限制御へ受け、全view/verifierへ固定本数のqueue操作で配る。元の入力全体は参照しない |
| init | blank状態から実際の初期化を行う。最初の入力を保持したまま固定長prologueを実行可能にする |
| scan background/compare | DP命令、chain step、比較、出力更新を固定回数で実行。broken時の方針は§3で決めたものに揃える |
| shift | `CloseoutCoreEnc22`のqueue込み≤28の構成と `CoreEnc24`のchain操作を接続 |
| copy/home/fpp | コピーと移動は小ステップ。FPPは固定 `q=1` を起点に実命令を実行し、choiceで選んだ抽象後継との等式を目標にしない |
| markEnd/choose/rewind | sentinel・markの局所読取り、既存の駐車済みheadやbank切替を使う。無制限長のcounterを1tickで消去しない |
| replayStart | 停車済みmirror、role/bank切替、必要なcounter初期化を局所更新として実装 |

**重要：`CloseoutCoreAgree.SL` の `init = scan = replayStart = id` は仮実装。** `CloseoutCoreEnc6.modeWin_SL_*` が通っていても、この3モードの意味論的実装はできていない。旧「7モードがある」という記録を全機械に数え直さない。

既存の `microCount_le` は手書き数表についての定理で、全分岐の実命令数の証明ではない。途中の分岐で更新後の記号を読む場合も、固定窓内の仮想実行として計算する。各 `acts` の長さからBを得て `K ≥ B` とする。最初からK=1やK=64を固定して実装を曲げない。固定定数を増やすこと自体は許されるが、物理締切も再計算する。

**L4：初期化と物理不変量を同時に閉じる。**

- 物理テープは `realize` のblank初期状態から始まる。必要なsentinel・padding・予備bankを魔法の初期配置として与えない。
- 例えば論理左端を物理位置Kに置き、固定長prologueで左端印と初期headを準備する。論理headが左端を越えないよう局所印でclampすれば、`compStep_apply` の `K ≤ pos` を実行全体で保てる。prologueの間は最初の入力を有限制御に保持する。margin確立前の初期化は別に直接検証し、`compStep_apply`のmargin前提を先取りしない。
- 初期化費用は固定定数。最初の1文字を含む受理期限に収まるよう、全入力共通のslot幅nに計上する。
- `Rep` はchain対応、queueの `LaysS`、counterの値と役割、bank清掃・予備領域、有限PC/clock境界、読取可能性を保持する。追加する各fieldに対し、初期化と変更する分岐の保存を同じ作業で提出する。
- `TEqG`（同じhead位置・同じ読取り）でsimulationを運ぶ。末尾blankの表現差を消すために全体の厳密等式を証明しない。

**L5：実入力に沿った有限prefixのsimulationを証明する。**

`TrackAt(w,s,j,k,phys)` は提案する追跡関係で、時刻s、到着済み文字数j、抽象tick数k、物理状態の `Rep` を結ぶ。w,s,j,kは証明上の添字で、有限制御に格納する値ではない。

- 到着時は `inp w s = some a` から正しい次文字aを得て、jを進める。
- 非到着時、実際に必要なセルが揃えばabstract tickを1つ進める。不足ならstutterする。
- starvation判定はmodeごとの必要読取りに一致させる。既存 `Starved` は4 head条件の一括要求なので、余計に止まって期限を破らないかを確認する。各分岐について安全性と進行性の両方を出す。
- canonicalを使うなら、実際の局所tickがそのpolicyを満たすことを先に示し、一意性でprefixの後継と同定する。
- 対象は最終reportまでの有限prefix。`realizes_canonical` の現在の `∀ k` のtrace前提を、必要な `k < Tc |w|` のbounded版へ切り直す。未構成の無限延長を新たな義務にしない。

**L6：期限・ラッチ・最終受理へ繋ぐ。**

1. 同じ実走行について、oracleの費用、到着時刻、simulationの進行数を繋ぐ。`LocalLedgerShift.sched_of_starved` / `H_ledger_of_local_oracles` の必要条件を実際に埋める。
2. `latchL` 相当の有限bitで、当該入力slotの正しいreportを記憶する。reportのsoundness/completenessと、追加の入力がない最終slot内での完了を証明する。
3. `LocalStep.realize` / `realize_SAccepts` で具体機械Mの受理へ移す。nは初期化・入力配布・計算の全費用を含む固定定数とする。
4. 抽象側の `latch_iff_pal_of_preTrace` には `hNeed` が必要。現行の最終組み立てが作っているlookahead証明を再利用し、全ての対象 `PreTraceIMW` について供給する。無いままiffを適用しない。
5. `M.SAccepts w ↔ w ∈ PAL` と抽象側の `LatchTrue … ↔ w ∈ PAL` を合成して `H_realizeCanonical centreC placeC 0 1 0` を得る。Mの正しさの証明でoracleを使うならその依存を明記し、先にcycle公理を閉じる。循環は禁止。

ここで物理走行と旧抽象traceの終端時刻が違っていても、**双方が同じ入力について期限内に正しい受理結果を返す**なら、受理同値は合成できる。これは時刻の違いを無視するという意味ではなく、各側の期限を各側で証明するという意味である。

### 4.5 局所実現で最初に提出させる具体的成果

新しい残差一覧ではなく、次のいずれかを要求する。

- **第一成果**：queueの有限観測から `nq/acts` を選ぶ実関数、`laysS_sApply` への対応、`len_le`、`compStep` の具体項。本体から使う場所を明記。
- **第二成果**：blank初期状態から動くinit＋入力到着＋1回のscan比較を同じ物理表現で通す。固定入力への実行例と一般のsimulation命題を区別して提出。
- その後に10モードの未処理分岐を順に埋める。別々の物理配置で作った部品を後で統合する進め方には戻らない。

## 5. 停滞を起こした判断規則の書き換え

| 旧規則・起こりやすい行動 | 書き換える規則 |
|---|---|
| 公理が2なのであと少し | 公理の中身を実際の証明課題で測る。残り時間・完成率は数から推定しない |
| producerがないので未完と報告 | 要求型から具体構成、既存部品、最初の実装、検証方法まで示す |
| 既存補題が使えないたびに新wrapper | 消費者の量化範囲・物理表現・実行方針を点検し、必要ならその契約自体を書き換える |
| 原子的な葉を減らすため動作を省略 | アルゴリズムと費用の根拠を保存する。省略には新しい正当性・時間証明が必要 |
| conditional theoremがbuildしたので前進 | どの未証明条件を何で置換し、最終消費者がそれを使ったかを示す |
| 固定窓で書ける更新が存在すれば機械ができる | 次制御と更新が有限観測だけの関数であることまで証明する |
| 全状態・全パラメータで証明する | 最終witnessと実際に到達するprefixの必要範囲へ限定する |
| 詰まると全体build・巨大な履歴を再読 | 最小の失敗goalと必要なproducer/consumerに絞り、対象モジュールだけ検証 |

証明未完成のまま取り除かれたinline draftは復活させない。現行チェックポイントから、上記の成立性判断と具体構成を行う。

## 6. Fable 5.1へ最初に渡す指示

```text
対象: kmizu/lean4-peg、lean-pal、Lean v4.31.0。
基準SHA: 1939f3c5ee67a4dda8f621cf56332d0cc1f1203a。
目的: PalPeg.PalInPeg.unconditional の独自公理を0にする。
最終witnessは entry=0, q=1, first=0。不要な一般化をしない。

単独で実装する。サブエージェントなし。未コミット変更を保存し、
reset --hard / cleanを使わない。既存の2公理以外を追加しない。

この引き継ぎの§3、§4を作業方針とする。
最初に最新HEADとの差分、PalInPegUnconditional、OracleReadyの実際の型を読む。
巨大なCLAUDE_RESUME/ASSEMBLY_PLAN全体は読み直さない。

第一作業はno-restartとhmoveの整合性。
既存Python診断のbroken分岐をLeanの前提へ対応させ、
同じ不等式が成立すると期待してよいか決める。
既知診断を無視してFine–Wilf補題を足し続けない。
対応するならrestart復帰を第一候補にし、guard、readiness、lower、費用まで扱う。
MoveMinimalの全称hquarterはh=0で破綻するので使わない。

局所実現は「producerなし」で止めない。
CoreEnc12.ActRule/compStep、CoreEnc22の9本queue配置、
CoreEnc25のRTag/sApply、LocalChainの対応補題を使い、
持続する物理状態と有限観測による命令選択器を作る。
最初の実装成果はqueue sub-stepの具体ActRuleとsimulation。
init/scan/replayStart=idを完成した実装として使わない。
抽象状態からの全域sectionや厳密なテープ項等式を目標にしない。
TEqG/Repで実走行を追跡し、deadlineと受理同値まで接続する。

1作業単位につき、現在のgoal、使う補題、変更範囲、成功条件を固定する。
進捗報告は完全な定理名・残前提・消費者・検証結果で示す。
新wrapper、仮定の移動、文書更新だけを証明進捗としない。
各葉は単体/module build。公理1本を実際に置換した段階で全体buildと公理監査。
難しいから停止せず、具体的な失敗条件に応じて方針を修正して続ける。
```

## 7. /loopで注意を戻すための短い指示

以下を、利用環境で有効な `/loop` の本文に使う。コマンドの引数形式・間隔・寿命はこのレビューでは検証していない。タイマーごとに別のbuildや別実装を並走させない。

```text
現在の作業を点検して、同じ証明を続けて。

1. 今消そうとしている公理と、直下の具体goalを1つだけ示す。
2. 前回から「証明して消費者へ接続した条件」を示す。
   まだ無ければ、未接続/仮説/調査をそのまま区別して書く。
3. 新wrapper・文書・補題一覧だけ増えていないか確認する。
4. 同じgoalで2回進展がなければ、直近の失敗goal、量化範囲、
   物理表現、no-restartの整合性を確認し、次の一手を具体的に変える。
5. localRealizationなら、ActRuleのどの分岐を実装し、
   有限窓から何を読むか、どのRep保存を閉じるかを示す。
6. 「あと少し」「接続だけ」という見込みを報告に使わない。
7. 必要な単体検証を行い、その結果に基づいて自律的に続ける。

報告は短く。全体buildを毎回起動しない。動いているbuildを重ねない。
公理1本の証明・接続まで進んだら、最終公理リストを更新して示す。
```

## 8. 検証手順と完了条件

最初に現在地を確認する。別の作業木を基準SHAへ強制的に戻さない。

```bash
git status --short
git rev-parse HEAD
git diff --stat 1939f3c5ee67a4dda8f621cf56332d0cc1f1203a -- lean-pal
cat lean-pal/lean-toolchain
```

対象moduleの検証例。以下はリポジトリルートから実行する。

```bash
cd lean-pal
if [ -f "$HOME/.elan/env" ]; then . "$HOME/.elan/env"; fi
lake build PalPeg.OracleReady
# 新規または編集中のファイルは実際のモジュール名で検証する。
# lake env lean PalPeg/対象.lean は、依存oleanが最新であるときに限る。
```

新モジュールの登録先は現行運用の `PalPeg/Workbench.lean`。importはファイル先頭のimport群に置く。PR #74で末尾importの配置エラーが修正されたので、末尾に追記しない。古い指示の「rootへ追加」を機械的に実行せず、現行のimport経路を確認する。

公理置換後に、対象ソースのbuildを終えてから監査する。

```bash
# lean-pal/内で実行
lake build PalPeg.PalInPegUnconditional
cat > /tmp/lean-pal-final-audit.lean <<'EOF'
import PalPeg.PalInPegUnconditional

set_option autoImplicit false

example : PegSeparation.RecognizedByTotalPEG PalPeg.PAL :=
  PalPeg.PalInPeg.unconditional

#check PalPeg.PalInPeg.unconditional
#print axioms PalPeg.PalInPeg.unconditional
EOF
lake env lean /tmp/lean-pal-final-audit.lean
```

`Axioms.lean` の期待値は実際の監査出力に合わせて更新する。減っていない依存を期待値から消してはいけない。最後に1本だけ全体buildを行い、終了コードと対象SHAを残す。

```bash
# lean-pal/内で、bashで実行
set -o pipefail
lake build PalPeg 2>&1 | tee /tmp/lean-pal-final-build.log
build_status=${PIPESTATUS[0]}
printf 'BUILD=%s\n' "$build_status" | tee -a /tmp/lean-pal-final-build.log
test "$build_status" -eq 0
```

完了条件：

- 閉じた型 `RecognizedByTotalPEG PAL` を維持。
- 最終依存公理が標準公理の範囲内。`sorryAx`・残り2独自公理・別名の独自公理がない。
- `PAL`、PEG全域性、機械の実時間性の定義を弱めていない。
- 同じ固定有限機械が全入力を処理する。語や入力長ごとの機械を選んでいない。
- 初期化、入力到着、空語、最初の1文字、最終slotの費用と受理を処理。
- `make verify` だけで代用せず、`lean-pal`の対象moduleと全体buildを確認。

進捗記録は次の短い形式でよい。

```text
SHA:
対象公理:
今回のgoal:
証明した宣言:
消えた前提 / まだ残る前提:
実際の消費者:
検証コマンド・終了コード:
最終公理リスト（置換時）:
次の一手:
```

## 9. 根拠ソース（基準SHA固定）

- [最終定理と2公理](https://github.com/kmizu/lean4-peg/blob/1939f3c5ee67a4dda8f621cf56332d0cc1f1203a/lean-pal/PalPeg/PalInPegUnconditional.lean)
- [現在のoracle producerとhmove](https://github.com/kmizu/lean4-peg/blob/1939f3c5ee67a4dda8f621cf56332d0cc1f1203a/lean-pal/PalPeg/OracleReady.lean)
- [周期最小性とhquarterの現行型](https://github.com/kmizu/lean4-peg/blob/1939f3c5ee67a4dda8f621cf56332d0cc1f1203a/lean-pal/PalPeg/CanonicalChainMinimal.lean)
- [fallback移動量のconsumer](https://github.com/kmizu/lean4-peg/blob/1939f3c5ee67a4dda8f621cf56332d0cc1f1203a/lean-pal/PalPeg/CanonicalFallbackInput.lean)
- [Fine–Wilf・境界文字の既存補題](https://github.com/kmizu/lean4-peg/blob/1939f3c5ee67a4dda8f621cf56332d0cc1f1203a/lean-pal/PalPeg/GalilMoveLemma.lean)
- [no-restart診断](https://github.com/kmizu/lean4-peg/blob/1939f3c5ee67a4dda8f621cf56332d0cc1f1203a/docs/palindromes-in-peg/diagnose_no_restart_fallback.py)
- [Scalaのbroken restartとfallbackコピー元](https://github.com/kmizu/lean4-peg/blob/1939f3c5ee67a4dda8f621cf56332d0cc1f1203a/scala/pal/src/main/scala/pal/ScaffoldGalil.scala)
- [Canonical / Fair / rightPlace](https://github.com/kmizu/lean4-peg/blob/1939f3c5ee67a4dda8f621cf56332d0cc1f1203a/lean-pal/PalPeg/GalilTickFair.lean)
- [局所実現が要求する型](https://github.com/kmizu/lean4-peg/blob/1939f3c5ee67a4dda8f621cf56332d0cc1f1203a/lean-pal/PalPeg/CloseoutFinalW.lean)
- [ActRuleとcompStep](https://github.com/kmizu/lean4-peg/blob/1939f3c5ee67a4dda8f621cf56332d0cc1f1203a/lean-pal/PalPeg/CloseoutCoreEnc12.lean)
- [queueを含むshift局所操作と9本配置](https://github.com/kmizu/lean4-peg/blob/1939f3c5ee67a4dda8f621cf56332d0cc1f1203a/lean-pal/PalPeg/CloseoutCoreEnc22.lean)
- [queueの有限role tagと具体操作](https://github.com/kmizu/lean4-peg/blob/1939f3c5ee67a4dda8f621cf56332d0cc1f1203a/lean-pal/PalPeg/CloseoutCoreEnc25.lean)
- [init/scan/replayStartがidである旧仮実装](https://github.com/kmizu/lean4-peg/blob/1939f3c5ee67a4dda8f621cf56332d0cc1f1203a/lean-pal/PalPeg/CloseoutCoreEnc6.lean)
- [chainの物理状態と抽象化](https://github.com/kmizu/lean4-peg/blob/1939f3c5ee67a4dda8f621cf56332d0cc1f1203a/lean-pal/PalPeg/LocalChain.lean)
- [局所機械から多テープ機械への変換](https://github.com/kmizu/lean4-peg/blob/1939f3c5ee67a4dda8f621cf56332d0cc1f1203a/lean-pal/PalPeg/LocalStepRealize.lean)
- [bounded版への切り直し候補](https://github.com/kmizu/lean4-peg/blob/1939f3c5ee67a4dda8f621cf56332d0cc1f1203a/lean-pal/PalPeg/CanonicalLocalRealizes.lean)
- [ラッチとPALの受理同値](https://github.com/kmizu/lean4-peg/blob/1939f3c5ee67a4dda8f621cf56332d0cc1f1203a/lean-pal/PalPeg/CloseoutFinalFour.lean)
- [局所走行の期限証明](https://github.com/kmizu/lean4-peg/blob/1939f3c5ee67a4dda8f621cf56332d0cc1f1203a/lean-pal/PalPeg/LocalLedgerShift.lean)
- [最終公理監査](https://github.com/kmizu/lean4-peg/blob/1939f3c5ee67a4dda8f621cf56332d0cc1f1203a/lean-pal/PalPeg/Axioms.lean)
- [最新の引き継ぎと訂正](https://github.com/kmizu/lean4-peg/blob/1939f3c5ee67a4dda8f621cf56332d0cc1f1203a/lean-pal/HANDOFF_CODEX_2026-09-19.md)

9/17版の大規模並列計画は履歴としてのみ扱う。この文書では、残差の名前を増やす方針から、実行方針の整合性と具体的な有限命令選択器を作る方針へ更新した。
