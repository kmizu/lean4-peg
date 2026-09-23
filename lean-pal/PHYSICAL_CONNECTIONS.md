# 物理機械の接続作業台帳

正本: [proof-strategy.md](../proof-strategy.md)。作業項目をそのまま分解して追う。
`[ ]` は未完、検証中は未完のまま。段階ごとの個数は 6 / 7 / 6 / 6 / 6 / 8 = 39。
**完了21、未完18。** M0=6/6、M1=7/7、M2=6/6、M3=1/6、M4=0/6、M5=1/8。
これは補題本数や重み付き進捗率ではない。最終ケースの閉鎖には、同じ機械・入力条件・
源状態の側条件・マクロ境界・融合・dispatcher の接続まで必要。

## M0：接続面とガードを確定する

- [x] M0-01: 付録Aの quiet ⇒ starved を Lean で確認する。
- [x] M0-02: 固定パラメータ 0 / 1 / 0 で、最終消費者の引数を一覧化する。
- [x] M0-03: Enc の w 依存、初期状態、OnRun の保持方法を決める。
- [x] M0-04: microRadius / macroRadius / margin、各プログラムの有限PC範囲を固定する。
- [x] M0-05: 未完成部分は名前付きの明示仮定として、接続の型を検査する。新規 axiom や sorry は導入しない。
- [x] M0-06: 仮定付き接続は「型が合うことの確認」と記録し、残存義務の解消とは数えない。

## M1：初期化・入力到着・マクロ境界を先に通す

- [x] M1-01: 初期化前と通常動作中の外側の符号化を定義する。
- [x] M1-02: 全空白の初期状態を証明する。
- [x] M1-03: 初回入力を保持し、初期化と最初の到着を正しく接続する。
- [x] M1-04: 通常の some letter が `arriveState'` に対応することを証明する。
- [x] M1-05: 初期化・feed・12ステップ tick のそれぞれについて、マクロ境界の不変量を供給する。
- [x] M1-06: 融合後の余白を使って sweepClosure へ輸送する。
- [x] M1-07: 空入力、最初の1文字、入力到着直後の飢餓解除を検査する。

## M2：非飢餓の scan count を、最初の接続例として完成させる

- [x] M2-01: 外側の飢餓停止と、内側の restart 優先を表にする。
- [x] M2-02: 非飢餓の count 側で静止するケースを閉じる。
- [x] M2-03: 既存の `scanConsume_*` と `stepState` を使い、plain token の消費ケースを閉じる。
- [x] M2-04: clock の減算、polarity、period の移動、verifier の右移動を一緒に確認する。
- [x] M2-05: hready と各読み取りの一致を、Enc と実行不変量から供給する。
- [x] M2-06: その結果を hforwardTick の実際のケースへ接続する。

## M3：残りの分岐が共有する、表現上の難所を解く

- [ ] M3-01: distance / boundary / last の読み出しを、段構造の不変量として確定する。
- [x] M3-02: 境界記号の first / last、方向反転を含む consume の各ケースを閉じる。成功・失敗・非消費を含むwatch count全体を、同じ最終TickCasesへ接続。比較内の二度消費の合成はM4に残る。
- [ ] M3-03: init / replayStart / choose-select に必要なカーソル複製・役割交換を実装し、後の独立更新も保存する。
- [ ] M3-04: chain 誕生時の idle → active に対して、verifier の表現を供給する。
- [ ] M3-05: DP の12テープに、既存の有限窓による実行証明を接続する。
- [ ] M3-06: DP・FPP の退役側を、再度 live にする条件を確認する。
  実preloadからの任意program RunのDenseはDP12/FPP9本とも供給済み（GalilDpDensity/PhysicalDpDensity）。
  共通dispatcherに有限phaseと並行消去を載せ、blank boot/全feed/全starvedと既存7activeケースを新Encの最終TickCasesへ接続。
  実prepareの任意途中RunもDense（PhysicalDpPreload）、源Encのlive DP表現から退役開始へ接続（PhysicalDpRetirement）。
  消去期限、PAL全体から準備/program Runを供給する接続、再live/prepare/restartの実行行、FPP旧消去置換は未完。

## M4：matched と残りのケースを、同じ dispatcher に載せる

- [ ] M4-01: matched の side conditions を呼び出し側で供給する。
- [ ] M4-02: beginShift / beginFallback が、比較後の状態を使うことをそろえる。**beginShiftは完了**（`PhysicalShiftDispatch.forward_entry` → `cases_of_remaining`）。beginFallbackは未完。
- [ ] M4-03: restart が最優先の scan 分岐であることを保持する。
- [ ] M4-04: init、replayStart、choose-select、shiftOne、chain 誕生を接続する。**shiftOneとshift出口は完了**（`running_mode` → `forward_shift` → `cases_of_remaining`）。他は未完。
- [ ] M4-05: 分岐表の残りパラメータ `rest` を具体化する。
- [ ] M4-06: 各モードを場合分けし、未処理のケースが残らないことを Lean のゴールで確認する。

## M5：停止・出力を閉じ、最終定理を切り替える

- [ ] M5-01: PhysFrozen と enter / keep / quiet を、同じ機械の none ステップについて証明する。
- [ ] M5-02: hencRep と hencOut を証明する。
- [x] M5-03: 既存の抽象側3契約を固定証人 0 / 1 / 0 で渡す。
- [ ] M5-04: `unconditional` を具体機械からの経路へ切り替える。
- [ ] M5-05: `obligation_localRealization` への依存を取り除き、未使用の追加公理宣言も整理する。
- [ ] M5-06: 最終公理監査が標準公理だけになることを確認し、guard を更新する。
- [ ] M5-07: ルート全体をビルドする。
- [ ] M5-08: 「unconditional は存在しない」等の古い説明を、実際の結果に合わせて更新する。

## 証拠と残差

- M0: `PhysicalGuardProbe.quiet_scan_starves` / `tickFun_nonstarved_count`、
  `ShadowedLocalFinal.given_physicalMachine_indexed`、`PhysicalContract.Obligations` /
  `forwardTick_of_cases`、`PhysicalConnection` の `given_obligations`。
  語ごとの証明述語だけを添字付けし、有限機械は全入力で共通。
- 固定値: entry=0、q=1、first=0、microRadius=128、macroRadius=1536、margin=1536。
  FPPのPC範囲は max 321 (code.length+1)、DPはcode.length+1。
  個別行動表の長さ、到達PCの範囲、FPPの hcomp / hfloorRun / hin は未供給。
- M1: 外側の blank / running 符号化、`enc_initial`、`running_margin` /
  `running_boundary` は型を検査済み。boot遷移は `PhysicalBootFeed.boot_sweep` で構成済み。
- M1: `LocalBlankSweep.compStep_apply_blankEdge` を任意アルファベットへ一般化。
  `LocalQueueInit` の既存APIはその特殊化として残す。追加の準備tickは導入しない。
- M1: コピー用カーソルの余白は既に padLeft が保証する。
  `EncTapes.places` の未使用な内側の junk.length ≥ margin を除去し、
  初期状態に二重の余白を強制しない。単体Lean EXIT=0。
- M1-03/04: `PhysicalBootFeed.machineStep noneStep` は同じ有限機械のboot・feedを定義し、
  `forwardFeed` が初回を含む任意の到来文字を実際の物理ステップで模倣する。
  通常noneステップは明示データ引数 `noneStep` のまま。feedの証明はその実装に仮定を置かない。
  未計上の準備tickを挿入せず、最初のsweepで番兵・ゼロカウンタと4ビューの到着を処理する。
- M1-05: `PhysicalBoundary.macroBoundary_of_heads` / `macroBoundary_tickRule` が
  12ステップ後のslot=0・全ビューowed=0を供給。boot / feed はそれぞれ
  `boot_core` / `PhysicalFeed.core_feed` のCoreEncに境界を含める。
- M1-07: `boot_none` は空白からのnoneステップで同じ抽象状態を保ち、
  `initial_starved` / `first_letter_unstarves` は初期の飢餓と1文字到着後の解除を確認。
  これは入力境界の検査であり、空語・1文字の全実行の最終認識証明ではない。
- M1-06: `PhysicalBoundary.running_fused_step` が同じ12ステップ規則の理想実行を、
  融合した実ステップのsweepClosureへ運ぶ。具体分岐の保存そのものはhstepに残す。
  この項目完了は個別分岐の完了を意味しない。
- M2-01: `PhysicalTickDispatch.starvedRead_running` が全モードの飢餓判定を有限窓から読み、
  `guardedStep` が内側のrestart/count/comparisonに先立って飢餓を停止させる。
  `forward_starved` はbootも含む外側Encを保存する。restartの優先順は既存の
  `scanPhase_eq` を再利用し、`countRead` はcountにだけclock減算を選ぶ。
- M2-02: `PhysicalScanCount.forward_count_atRest` が、非飢餓scan・clock>1・chain idle・
  search idle/missedのケースを同じ `scanMachine rest` の実noneステップで証明。
  背景消去、clock減算、12ステップの境界、融合、sweepClosureまで含む。
  watchのlag=0等の別の静止ケースはまだ残り側。count全体の完成とは数えない。
- M2-03/04: `PhysicalCountConsume.forward_count_plain` がplain token・順方向・一致の
  countを同じ `scanMachine rest` の実noneステップで証明。clock減算、lag・distanceの
  符号更新、period移動、verifier右移動を同じ12ステップと融合後のsweepに含める。
  M2の出口は方針書どおり「非飢餓の一ケース」。逆方向・成功境界は後続M3の
  PhysicalBoundaryCountで接続済み。不一致もM3-02で接続済み。
- M2-06: `PhysicalCountConsume.cases_of_remaining` が全starved、CountAtRest、
  CountPlainMatchを最終 `TickCases` へ渡す。残差 `hother` は非飢餓かつ
  `¬CountAtRest ∧ ¬CountPlainMatch` のケース。`rest` の未実装命令行も残っている。
- M2-05: `PhysicalContract.TickCases.active` が、最終消費者から来た実際の
  `Tick` の証拠を引き継ぐように修正。`forwardTick_of_cases` で具体的に供給済み。
  `PhysicalCountReady.verifier_canRight_of_countTick` はその証拠から正のlagを持つwatchの
  verifier可用性を取り出し、`moveRight_ready` は任意の表現ビューの準備条件へ運ぶ。
  `core_consume` はこのhreadyとEncからのtoken/verdict/forward符号を供給する。
  局所読取や準備条件の未証明仮定は最終ケースの外へ出さない。
- M5-03: `PhysicalConnection.given_obligations` で抽象側3契約を0/1/0に供給済み。
- 上記チェックは Workbench BUILD=0 で確認。新しい接続・境界定理の公理guardも通過。
- 最終定理の追加公理を別の公理へ置き換えない。公理監査は最終完成時の確認。

## M3 境界カウンタ：検証済み部品と統合残差

段を区切るだけでは、独立に使われるboundary/lastとrestartのlower/workへの受け渡しを
実現できない。既存の `LocalCounter` の段付き符号化を使ったまま、予備カウンタを
周期の移動中に準備し、境界で有限の役割交換を行う部品を作った。物理テープ118本は増やしていない。

`ChainBoundaryCache.Inv h age s spare` は実際のperiodテープをFIRST/plain/LASTに分解し、
次の境界までの移動と3つの論理値、予備値を結びつける。hとageは証明の添字だけ。
Bをboundaryの値、pを `min phase.val 2` とすると、次を保つ。

- distance = B + age
- last = B（phase=0）、B − h（それ以外）
- spare = B − p*h + (p+1)*age

`cursor_boundary` は境界記号を読むこととage+1=hの同値を証明する。
`inv_consume` は実際のconsumeの左右両方向・FIRST/LAST反転で保存し、
`inv_shift` は実際の `chainShiftOne` と予備の同時減算で保存する。負の値も許す。
増分率は初回境界まで1、次まで2、その後3。`spare_eq_at_boundary` は境界直前に
その回数を加えると新しいdistanceと**論理Counterとして等しい**ことを証明する。

`PhysicalCounterCache.increments_encode` は同じΓm・padLeft・action-list上で、
有限の源窓から増分列と最終polarityを生成する。源と鏡は同じ値でよく、捨てた段の
リテラルな一致を要求しない。ゼロをまたぐ複数増分にも対応する。
`boundary_actions_length` は1テープ最大3アクション、`boundary_rotate` は実際のconsumeに
対する boundary := inc distance / last := old boundary と予備の再利用、次回用Invを証明する。
役割はboundary/last/spareの3つで、`rotate_injective` が独立なテープの所有を保つ。

`LocalRoleRouting.route` は役割の置換を有限制御へ持たせ、源の役割で読み書きし、
出力で役割を変更する。`decode_route` は実際のLocalStep.apply（sweep込み）と交換する。
`PhysicalRoles.Control` は Roles × (Unit ⊕ QPhys)、`Enc` は役割で並べ替えて既存Encを読む。
`machine rest` / `forward_feed` / `cases_of_remaining` へ既存のboot/feed/starvedと2つのcountを
輸送済み。ここでのmachineは役割を保持する下層版。
現在のPhysicalBoundaryCount.machineはこの同じ表で成功countの境界交換を行う。

境界用の役割は**既存slot 14/15/10 = boundary/last/spare**に固定した。
10はcopy/backではchain.hを持つが、watch/brokenではcounterOfがnoneなので予備に使える。
`boundaryRoles` / `compose_boundary` が同じ118本上の有限置換と既存3役の回転を結ぶ。
restart用の複数コピーについては別途割り当てが必要。

`PhysicalFreeCounter.running_free_counter` は論理的に未使用のカウンタの符号とテープを
交換しても、他の全成分のEnc・余白・sweepClosureを保つ。
`PhysicalSpare.Rep` は予備の符号付きカウンタ表現をTEqGで保持する。単なる「未使用テープ」
では減算後の余白を保証できないため、この表現はwatch状態の不変量に必要。
`PhysicalSpare.overlay` は元のLocalStepのslot 10とその符号だけを、同じ源窓からの
予備の出力へ差し替える。半径1536・1物理ステップのまま、別の準備tickを追加しない。
`PhysicalCountSpare.forward_plain` は既存のcount/VM/clockの実sweepと予備更新を合成し、
次回用のRepとInvも返す。
`PhysicalWatchEntry.running_entry` はbackからwatchへ入る実sweepでslot 10/13/14/15を
各1アクションでresetし、periodを右へ動かす。hの鏡を含む他の論理成分は保持し、
FPP退役半分には既存のwithEraseを同時適用する。
`cache_at_entry` が正規のFIRST/plain/LAST配置からInv/Repを新たに供給する。
`forward_count` は有限窓の `entryRead` で選ぶ `withWatchEntry work` の実ステップを、
時計の減算を含む本物のtickFunへ接続する。追加の準備tickは無い。

ここで `ShapedCoreEnc` は既存CoreEncに `CounterShapes`（休止中も含む全counterの
padLeft/mapTape encSeg形式）を加える。`prepared_shapes` はbootの準備配置、
`core_rule` / `shaped_clockDown` はこの入口と時計更新での保持を証明する。
`PhysicalCacheInvariant.CoreInv` はこの形状とwatch/brokenのInv/Repを同じ符号化に載せる。
`boot_core` / `boot_sweep` / `forward_feed` / `forward_starved` は実boot・初回を含むfeed・
全starvedでこの強い符号化を保つ。`running_plain` は源Inv/RepをEncから取り出し、
実際のplain一致消費と予備準備を同時に行って同じCoreInvへ戻す。
`PhysicalCacheMachine` は窓でwatch入口と成功消費の予備準備を選択し、元の静止countも保持する。
`cases_of_remaining` はCountAtRest / CountPlainMatch / CountWatchEntryを同じ機械・Encで
最終TickCasesへ接続する。`routed_cases` は同じ結果を既存の有限役割付き機械へ輸送する。
118本・Γm・半径1536は不変で、追加の準備tickは無い。

**残る分岐での保存は未完。正規period配置のOnRun供給は接続済み。**
下層CountWatchEntryの正規配置条件を、最終層では `PhysicalChainShape.period_onRun` と
`first_shape` が供給する。残差の除外はback/FIRSTという実ガードの `CountBackReady`。
`PhysicalBoundaryCount.machine rest` はその下層機械に境界の役割・符号交換を組み込み、
同じCoreInvでwatch countの全ケースを保持する。全分岐の保存はまだ必要なので、
Inv/Repを全到達watch状態へ供給したとは数えない。

**M3-02は完了、M3-01は未完。** 残っている統合は以下。

1. 残る分岐でCoreInvを保存する。正規period配置とcopy/backのhはOnRunから供給済み。
   boot/feed・全starved・静止count・watch count全体・back/FIRST入口は接続済み。
   semiperiod hの鏡5はwatch入口の実sweep後、watch全体、shiftの進行・終了まで共通Encで保持済み。
   beginShiftの実tickでremainingに渡す接続もPhysicalShiftDispatchで完了。
2. 比較の二度消費・shift入口でのCoreInv保存は実dispatcherまで完了。他の比較腕は未完。
   watch countは一致・不一致・非消費、全token両方向・境界Roles/polarity更新まで接続済み。
3. restartでlastをlower/workへ渡すための複数コピーと、使用後の再準備を接続する。
4. 強めた同じEnc・実sweep・最終TickCasesで残るケースを閉じる。

これらは未完18項目の内訳であり、補題数だけではKPIを減らさない。

## 最終ケースの台帳

| 群 | ガード | 側条件の供給元 | 定理 / 最終での使用状況 |
|---|---|---|---|
| boot | 初期制御、none / some | Encのblank相 | boot_sweep / boot_none / forwardFeed。共通machineStepへ接続済み、通常none実装は残る |
| feed | some letter | Encから全条件供給 | forwardFeed。初回を含み、通常noneの実装に仮定なし |
| starvation | starved=true | Encの窓読取、boot相 | forward_starved、cases_of_remainingへ接続済み |
| restart | 非飢餓、restart=true | OnRun / CanonTrace | 未 |
| count | 非飢餓、restart=false、clock>1 | Enc、源状態のchain/search場合分け | idle静止・watch全体・正規watch入口をPhysicalBoundaryCount.cases_of_remainingへ接続。他のchain/searchケースは残る |
| matched | 比較一致 | 比較窓、探索・chain不変量 | 共通カウンタ・制御のみ。最終未 |
| shift/fallback入口 | 比較不一致 | 比較後状態、shiftGuard | shift入口は全更新・源条件供給・有限窓選択・最終TickCasesまで接続。fallback入口は未 |
| chain consume | plain / FIRST / LAST、方向、成功/失敗 | EncのCache、合法Tick | countの全token・両方向・成功/失敗・非消費まで最終接続。比較内の二度消費の合成はM4に残る |
| chain lifecycle | idle/copy/back/watch/broken | OnRunのperiod形状・h、鏡・DP・誕生時のhead | back/FIRST入口のcountは源の正規配置供給まで接続。hの鏡は入口後まで。他のlifecycleと鏡の継続保持は未 |
| fallback各mode | copy/home/fpp/markEnd/choose/rewind | 読み取り、PC、消去の到達不変量 | 旧T表に部品。最終未 |
| shift/replay | shiftOne/exit/replayStart | alias、counter、head readiness | beginShift入口/shiftOne/exitは共通CoreInv・実sweep・最終TickCasesへ接続済み。replayStartは未 |
| frozen/report/output | report後のplateau | OnRun、PhysFrozen | 未 |

quiet scan は `frame_quiet_scan_starves` により非飢餓側から除外できる。
starvationの保存は、この除外とは別に `forward_starved` で証明済み。

## 直近の実装順

M1とM2を完了。次はM3の段境界・alias・DP。別レイアウトを作らない。

1. watch count全体、back/FIRST入口、shiftの進行・終了は接続済み。period形状・h・残量上限・
   CopyIdleはOnRunから供給済み。boot/feed・全starved・idle静止countも同じ機械へ接続済み。
2. beginShiftの比較/immediate、remaining reset、h/remaining交換と全ヘッド実行は
   共通dispatcherまで完了。次はrestart時のlastの複数コピーと再準備。
3. カーソルの複製・役割交換、DP窓、退役バッファの再利用へ進む。

M2で通った接続順は `core_consume` → `running_consume` → `forward_count_plain`
→ `cases_of_remaining`。合法なTickを保持して可用性を供給し、Encから読み取りを供給する。

既存 `PhysicalEncoding.EncTapes.places` の内側の高さ条件を外したのは、
全空白の最初のsweepから二重余白を定数ステップ内に作る必要をなくすため。
外側のpadLeftとsealed junkを保持し、既存の読取・更新定理はすべて再ビルド済み。

M2検証: `/tmp/physical-count-consume.log` **EXIT=0**、
`/tmp/physical-consume-workbench.log` **BUILD=0**、
`/tmp/physical-consume-axioms.log` **AUDIT=0**。
M3部品検証: `/tmp/physical-counter-cache.log` **EXIT=0**、
`/tmp/physical-cache-workbench.log` **BUILD=0**、
`/tmp/physical-cache-axioms.log` **AUDIT=0**。
`ChainBoundaryCache` / `PhysicalCounterCache` の追加guardも標準公理のみ。
役割・予備合成の検証: `/tmp/physical-count-spare.log` **EXIT=0**、
`/tmp/physical-roles-workbench.log` **BUILD=0**、
`/tmp/physical-roles-axioms.log` **AUDIT=0**。新モジュール5本をWorkbenchへ登録し、公理guard通過。
最終定理のguardは未変更で、無条件PALの証明はまだ未完。

watch入口の検証: `/tmp/physical-watch-entry.log` **EXIT=0**、
`/tmp/physical-watch-workbench.log` **BUILD=0**、
`/tmp/physical-watch-axioms.log` **AUDIT=0**。
`cache_at_entry` / `selected_entry` / `forward_count` の3guardは標準3公理のみ。
最終unconditionalの追加公理は未変更。完了20・未完19。

共通cache符号化の検証: `PhysicalCacheInvariant.lean` / `PhysicalCacheMachine.lean` **EXIT=0**、
`/tmp/physical-cache-machine-workbench.log` **BUILD=0**、
`/tmp/physical-cache-machine-axioms.log` **AUDIT=0**。
新モジュール2本をWorkbenchへ登録し、追加した公理guardは標準3公理のみ。
`sorry` / `admit` / `native_decide` / 新規 `axiom` なし。最終定理の追加公理は未変更。

## 成功countの境界を最終契約へ接続（2026-09-22）

`PhysicalConsumeStage.running_staged` は既存workRuleの実12ステップ後を、境界/lastだけが
旧値を保持する中間状態として同定する。periodの左右両方向・FIRST/LASTを扱う。
これは同じ一歩の途中結果の証明であり、準備用の物理tickを追加していない。
`cursor_left` は逆方向とLASTで必要な左側の存在をCache.Cursorから供給する。

`PhysicalBoundaryRotate.running_rotate` は準備済み予備→boundary、旧boundary→last、
旧last→予備の役割と符号を交換し、全Encを回復する。TEqGの実テープにも適用する。
`PhysicalBoundaryCount.running_match` は源CoreInvから予備Inv/Rep・canonical性・左移動条件を
取り出し、VM更新・clock・予備準備・境界交換の結果へ同じCoreInvを返す。

`PhysicalBoundaryCount.machine rest` は源の有限窓から境界を選び、有限制御内の符号と
役割表を同時更新する。`decode_machine` がこの実sweepを上の証明へ結ぶ。
`forward_match` / `cases_of_remaining` は成功countのplain両方向・FIRST/LASTを最終TickCasesへ
接続する。boot/feed・全starved・静止count・正規watch入口も同じ機械で成立する。
118本・Γm・半径1536を保持し、準備tickは増やしていない。

consumeの不一致・比較との合成、他分岐のCoreInv保存、正規入口のOnRun供給、shift/restartは残る。
**M3-01/02は未完。総数20完了・19未完を維持する。**

成功count境界の検証: `/tmp/physical-boundary-count.log` **EXIT=0**、
`/tmp/physical-boundary-count-workbench.log` **BUILD=0**、
`/tmp/physical-boundary-count-axioms.log` **AUDIT=0**。
新モジュール3本をWorkbenchへ登録。running_staged / running_rotate / running_match /
forward_match / cases_of_remainingのguardは標準3公理のみ。
新規axiom・sorry・admit・native_decideなし。最終unconditionalのguardは未変更。

## M3-02完了：watch count全体（2026-09-22）

`PhysicalCountMismatch.core_mismatch` はwatch→brokenの実12ステップで、verifierだけを右へ
動かし、counter・period・予備・符号を保持する。FPP退役側の背景消去とmacro境界も含む。
`forward_count` はclock減算と源窓の選択まで接続する。境界記号で不一致になっても、
予備準備と役割交換は発動しないことを窓読取から証明する。

`PhysicalCacheMachine.core_still` をidle専用から一般化し、実行後の符号と全counterの保持から
Cacheをそのまま運ぶ。`PhysicalWatchIdle.forward_count` は正でないlagのwatchを保持する。
`PhysicalBoundaryCount.cursor_symbol` はCache.Cursorから実tokenを供給するので、呼び出し側に
plain/FIRST/LASTや方向の仮定を要求しない。

`forward_watch` の源条件はEnc、scan、非飢餓、clock>1、watchタグ、既存の合法Tickだけ。
lagの符号で静止/消費を分け、消費時は比較結果で成功/失敗を分ける。成功時のplain両方向と
FIRST/LASTは既存の役割交換へ、失敗時はbrokenへ接続する。
`cases_of_remaining` の残差から **CountWatch全体** が消えた。これをM3-02の完了証拠とする。
**この時点で21完了・18未完。** 比較の同一tick内の二度消費との合成（M4）、shift/restart、DP、
停止/出力は残る。正規watch入口のOnRun供給と入口後のhの鏡は、次節で接続した。
count全体・PAL全体の完成とは数えない。

watch count全体の検証: `/tmp/physical-watch-count.log` **EXIT=0**、
`/tmp/physical-watch-count-workbench.log` **BUILD=0**、
`/tmp/physical-watch-count-axioms.log` **AUDIT=0**。
新モジュールPhysicalCountMismatch/PhysicalWatchIdleをWorkbenchへ登録。
forward_count（両モジュール）、forward_consume、forward_watch、cases_of_remainingのguardは
標準3公理のみ。新規axiom/sorry/admit/native_decideなし。git diff --check通過。
最終unconditionalの追加公理は未変更で、無条件PALは未完。

## M3-01の分解：watch入口の源条件とhの鏡（2026-09-22）

| 小項目 | 状態 | 証拠・残差 |
|---|---|---|
| periodの正規配置を実行中の源状態から供給 | 完了 | `PhysicalChainShape.period_onRun` は到着待ちのtruncationと報告後のplateauを扱う。`first_shape` を `cases_of_remaining` で使用 |
| copy/backのhとperiod長の一致 | 完了 | `ChainStoredPeriod.vmTick` → 同じ `period_onRun`。誕生・コピー・巻き戻し・全VM tickを通して供給 |
| hの独立コピーをwatch入口の実sweep後に保持 | 完了 | `PhysicalPeriodMirror.entry` → `PhysicalCacheMachine.periodMirror_entry` → `PhysicalBoundaryCount.forward_entry` の追加結論。鏡5は正符号の `ofNat (xs.length+1)` をTEqGで表現 |
| そのコピーのwatch/shift中の保持とremainingへの引き渡し | 完了 | watch count・shift入口/進行/終了を共通CoreInv・実sweep・最終TickCasesへ接続。`PhysicalShiftDispatch.forward_entry` が源の中間状態生成、全ヘッド実行、有限窓での選択を閉じる。残量上限と入力表現は実行から供給 |
| shiftの予備減算・restart用lastの複数コピー | 未完 | shiftの予備減算は最終接続済み。`PhysicalRestartStorage` がrestartのガード・静止命令・有限制御更新と、旧探索4カウンタの非参照性を証明。lastの複製準備、貸出し後の鏡の再準備、DPリセット用バッファ、実行行との接続は未完 |

これはM3-01の内訳で、39項目へ追加計上しない。**21完了・18未完を維持。**
最終ケースの除外は `CountWatchEntry` の正規配置ではなく、`CountBackReady`
（scan/count、backでFIRST）へ一般化した。源の配置とhは既存OnRunから取り出す。
新しいaxiom・物理テープ・準備tickは追加していない。

入口の源条件・hの鏡の検証:
- `/tmp/physical-period-mirror.log` **EXIT=0**（鏡の単体証明）
- `/tmp/physical-period-mirror-connection.log` **EXIT=0**（最終ケースへの接続）
- `/tmp/physical-period-mirror-workbench.log` **BUILD=0**
- `/tmp/physical-period-mirror-axioms.log` **AUDIT=0**
新規3モジュールをWorkbenchに登録。新しい定理は標準公理のみ、禁止構文なし、
`git diff --check`通過。最終unconditionalの追加公理は未変更で、無条件PALは未完。


## hの鏡を共通の符号化で運ぶ（2026-09-22）

`PhysicalCacheInvariant.Cache` に鏡5の `Rep true (ofNat …)` を追加した。
元の予備カウンタの符号には結びつけず、境界で予備の役割・符号が変わってもhの意味を保つ。
`ChainBoundaryCache.cursor_length` から、Cacheのhは実際の `periodLength wm` と一致する。
`running_mirror` は、この長さを実物の鏡テープから取り出す。

保存を同じ `PhysicalBoundaryCount.machine rest` と最終 `cases_of_remaining` へ接続した範囲:
- watch入口: 既存OnRunからStoredを供給し、実sweepのh保存を後状態のCacheへ格納。
- boot・初回を含むfeed・starved・静止count。
- watch count全体: plain、FIRST/LAST、両方向、非消費、不一致→broken。
  12スロットの実sweepはTEqGで輸送し、境界の役割交換も鏡5を保持する。

**shiftの引き渡しは未完。** 現在の `mirrorMagnitude` はshift中を
`h - remaining.toNat` と定義している。counter1と鏡5を交換し、旧remainingをゼロにして、
remainingの減算と同時に鏡を1ずつ再建する設計に対応する契約である。
この実行とremainingの上限保存、shift終了時のh復元、restart用の複数コピーはまだ接続していない。
M3-01の第4小項目はwatch count側だけ閉じたため未完のまま。**総数21完了・18未完を維持。**

検証:
- `/tmp/physical-mirror-lifetime-cache-check.log` **EXIT=0**
- `/tmp/physical-mirror-lifetime-boundary-check.log` **EXIT=0**
- `/tmp/physical-mirror-lifetime-workbench.log` **BUILD=0**
- `/tmp/physical-mirror-lifetime-axioms.log` **AUDIT=0**
対象ソースの禁止構文なし、`git diff --check`通過。最終unconditionalの追加公理は未変更。


## shiftOneの更新行を同じ機械へ実装（2026-09-22）

`PhysicalEncoding` の既存 `modeCommands` / `ruleNext` / `ruleActs` にshiftの動く側を入れた。
左カーソルは `stepRight`（半セル二歩）、中央は `moveRight`（一歩）、他の二本は静止。
cycleは二増、lengthは二減、remaining/radius/margin/distance/boundary/lastと予備は一減。
hの鏡5は予備10から独立した正符号の一増。カウンタの行動リストは各テープ最大2で、
118本・12スロット・半径1536・準備tickなしという構成を保持する。

| 接続した部分 | 証拠 | 残差 |
|---|---|---|
| 二回減算と符号反転 | `counter_decTwice_at` / `shiftCounter_tape` | 源と鏡は同値でよく、テープの等号は要求しない |
| 全論理カウンタの実sweep後の値 | `PhysicalShift.running_counter` | 共通EncTapesへの束ねが未完 |
| 名前の無い予備の一減算 | `PhysicalShift.running_spare` | Cache.Invと共通Encの同時保存が未完 |
| hの鏡の一増 | `PhysicalShift.running_mirror` | `h−remaining.toNat`との一致には残量上限が必要。入口の役割交換も未完 |
| 全カーソルの12スロット後の表現 | `PhysicalShift.ideal_head` | `ready_of_tick`で合法Tickから移動先を供給済み。Enc全体への束ねと融合が未完 |
| 有限制御の12スロット後の対応 | `PhysicalShift.ideal_control` | 窓からの最初の文字判定も証明済み。最終TickCasesへ未接続 |

**共通Enc保存・最終ケースへの接続はまだ閉じていない。** T08とM3-01は未完のまま、
**21完了・18未完を維持する。** 更新しないテープ、マクロ境界、Cacheの寿命を上の結果と
同時にまとめてから、shiftの分岐を `cases_of_remaining` の残差から外す。
`remainingPos` はshiftとcopyの残量テストのORなので、正のremainingを使う証明への供給も確認する。

検証: `/tmp/physical-shift.log` **EXIT=0**、
`/tmp/physical-shift-workbench.log` **BUILD=0**、
`/tmp/physical-shift-axioms.log` **AUDIT=0**。
`PhysicalShift`をWorkbenchへ登録。変更した旧shift出口を含めてbuild成功。
各新定理のguardは標準3公理のみ。禁止構文なし、`git diff --check`通過。
最終unconditionalの追加公理は未変更で、無条件PALは未完。


## shiftOneを最終ケースから放電（2026-09-22）

直前節の「Enc全体へ未接続」を解消した。`PhysicalShift.ideal_tapes` が動く全ヘッド、
カウンタと鏡に加え、静止テープ・全slotの余白・FPP背景消去を束ねる。
`ideal_shaped` / `running_shaped` が有限制御・マクロ境界・全16counterの形を実sweepまで保つ。
`running` は境界予備の減算とh鏡の再建を同じCoreInvへ格納する。

残量上限は物理Cacheの新フィールドにせず、`RemainingBound` を既存Coupledと一緒にtraceで運ぶ。
入口のimmediateで周期長が変わらないことは、既存`periodLength_consume`とBlockInvで供給。
`remainingBound_onRun` は入力待ちのtruncationと報告後のpacked runを扱う。
`copyIdle_onRun` はtrace上のCopyIdleを供給し、報告後はPlateauInv.scanでshiftを排除する。
元のremainingPosはshift/copyのORであることを`shiftMoving_iff`で固定し、コピー側の排除を
最終呼び出しで行う。後状態のEncを仮定せず、可用性は合法Tickから供給する。

`PhysicalBoundaryCount.forward_shift` → `cases_of_remaining` により、同じ118本・12スロット・
半径1536の役割付き機械と共通EncでShiftMovingを処理し、`hother`から除外した。
T08の局所分岐証明は完了し、さらに最終接続まで到達。**旧T表は14あり・9未**。
M4-04はshiftOne小項目だけを消し込み、**39項目は21完了・18未完を維持**。

次の残差はbeginShiftの比較後状態からのremaining/鏡5の役割交換、旧remainingのreset、
shift出口での鏡hの復元接続、restart用コピー。他の未処理activeは引き続きhother、
未実装命令行はrestに明示する。追加公理の放電・無条件PALは未完。

検証: `/tmp/physical-shift.log` **EXIT=0**、
`/tmp/physical-shift-connection.log` **EXIT=0**、
`/tmp/physical-shift-workbench.log` **BUILD=0**、
`/tmp/physical-shift-axioms.log` **AUDIT=0**。
`ideal_shaped` / `running_shaped` / `remainingBound_onRun` / `copyIdle_onRun` / `running` /
`forward_shift` / `cases_of_remaining`の公理guard通過（標準3公理のみ）。
新規axiom・sorry・admit・native_decideなし、git diff --check通過。
39項目と旧23出口の件数も台帳の実行列から確認。最終unconditionalの追加公理は残る。


## shiftモード全体を放電し、入口の受け渡しを分離（2026-09-22）

`PhysicalShift.running_exit` が残量ゼロでの鏡hの回復、全counter形、制御、背景消去と
共通Cacheを同じ実sweepへ接続した。`running_mode` はOnRunから来るCopyIdleと残量上限を使い、
元のremainingPosガードの進行・終了を場合分けする。`PhysicalBoundaryCount.forward_shift` /
`cases_of_remaining` の残差は、ShiftMovingだけでなく **mode ≠ shift** まで縮小した。

入口の残件は次の境界で分ける。小項目は39項目へ重複計上しない。

| 義務 | 状態 | 証拠 / 残差 |
|---|---|---|
| shift進行の全Enc・Cache・最終接続 | 完了 | `PhysicalShift.running` → `forward_shift` |
| shift終了の全Enc・Cache・最終接続 | 完了 | `PhysicalShift.running_exit` / `running_mode` → `forward_shift` |
| 入口のh/remaining受け渡し | 部品検証済み・最終未接続 | `PhysicalShiftEntry.running_lend`。源は同じCoreInv、watch、mode=shift、remaining=reset。counter1/鏡5を有限交換し、remaining=ofNat(periodLength)と再建鏡0を同じCoreInvへ格納。全118テープを保持し、実テープはTEqGで扱う |
| 交換前の中間状態を実tick内で生成 | 未完 | 比較後状態、chainの内部消費とimmediate、remainingのreset、length/cycle/control更新を合成 |
| 入口の有限窓による選択と最終接続 | 未完 | watch起点の比較後guardとverifier命令は実表へ接続済み。役割交換の選択、他の更新、全CoreInv、最終beginShiftのhother除外は未 |

`running_lend` は交換先のEncを仮定しない。ただし、その源の中間状態は現在の入口行では
まだ作られていない。中間状態は同じtick内の証明点であり、新たな物理tickではない。
**beginShift全体・M3-01・M4-04は未完。39項目は21完了・18未完、旧T表は14あり・9未を維持。**
restart用コピー、DP、他モード、停止/出力と最終公理の除去も残る。

検証:
- shift終了のモジュール: `/tmp/physical-shift-exit-module.log` **BUILD=0**
- 最終分岐への接続: `/tmp/physical-shift-exit-connection.log` **EXIT=0**
- 入口の役割交換: `/tmp/physical-shift-entry.log` **EXIT=0**
- 登録済みWorkbench: `/tmp/physical-shift-entry-workbench.log` **BUILD=0**
- 最終公理監査: `/tmp/physical-shift-entry-axioms.log` **AUDIT=0**
新定理のguardは標準3公理のみ。変更した証明の禁止構文なし、`git diff --check`通過。
最終unconditionalは局所実現の追加公理に依存したまま。追加公理宣言は増やしていない。


## 比較後のshift guardを実命令表へ接続（2026-09-23）

`PhysicalEncoding.scanShiftRead` は、源窓から内部消費後の半径2の窓を再構成し、
lag=0・phase=4・broken・margin/cycle・period記号を読む。右の比較文字は源ビューから
着地先を読む。`singlePositiveRead` は減算後のゼロを有限窓で判定してcycle=1を識別する。

`PhysicalCompareGuard.scanShiftRead_running` は、watch起点の比較不一致で、この読みが
本物の `shiftGuardTest (compareFun ... x.vm)` と一致することを証明する。
内部消費の成功・不一致・静止を含み、成功時のFIRST/LASTと方向反転も扱う。
Cache.Cursorがperiod記号と左移動条件を供給し、合法なTickが消費時のverifier可用性を供給する。
源のTEqGから実sweepの窓へ輸送済みで、後状態のEncや窓の一致を追加前提にしない。

`scanCommands` の比較行は、一致なら従来のmatchイベント、不一致ならこのshift guardで
第二のverifier移動を選ぶようになった。`modeCommands_shift_verifier` が実際の命令表で
moveRight/stepRightの選択を証明する。既存のmatched/count/shift分岐もWorkbenchで再検査した。

**まだ入口全体は未完。** 残る仕事は以下。

1. beginShift分岐からwatch源を供給する（現在のreader定理はwatchを前提にする）。
2. 内部消費＋immediateのカウンタ・周期・予備更新と境界役割交換を同じtickで合成する。
3. 共通カウンタ・制御・remaining resetを実装し、`PhysicalShiftEntry.running_lend` の源を作る。
4. 役割交換を有限窓から選び、全ヘッドの12ステップ後の表現・共通CoreInv・最終TickCasesへつなぐ。

M3-01/M4-02/M4-04は未完のまま。**39項目は21完了・18未完、旧T表は14あり・9未**。
新しい公理、物理テープ、追加の準備tickは導入していない。

検証: `/tmp/physical-compare-guard.log` **EXIT=0**、
`/tmp/physical-compare-guard-workbench.log` **BUILD=0**、
`/tmp/physical-compare-guard-axioms.log` **AUDIT=0**。
新定理の公理guardは標準3公理のみ。禁止構文なし、`git diff --check`通過。
無条件PALの最終追加公理は未変更。


## 比較内の二回消費：途中の役割交換を含む行動列（2026-09-23）

`LocalRoleFusion` は既存の `seqRule` と `LocalRoleRouting.route` を結ぶ。
第一段の有限役割交換を第二段の読み書きへ反映し、最終役割だけを外側の制御へ返す。
一時的な役割レジスタは `flatten` で取り除き、出力制御は既存の `QPhys` のまま。
`compiled_seq` は任意の源の役割配置について、単一sweepの結果と二段の理想実行の
制御一致・全テープの `TEqG` を証明する。

`PhysicalWatchActions` は同じΓm・118本・microRadius=128上の補助ルールを構成した。
**最終機械のdispatcherにはまだ組み込んでいない。**

- `rule true` はlagを減算、`rule false` はmarginを加算し、双方がdistance・period・spareを更新。
  `internal_actions_eq` で第一段を既存成功consume行＋spare準備と同定した。
- `balance_tape` / `distance_tape` は符号のゼロ越えを含めて検証。
  `period_tape` は両方向を扱い、左側の実セル条件は既存Cursorから供給する形。
- `logical_boundary` は準備済みspare→boundary、旧boundary→lastを、符号とテープ双方で証明。
  `logical_cache` は旧last→spareと同じCache.Invの保存を証明。
  局所前提は源のphase/event読み出し、Inv、spare/last/boundaryのRepで、後状態Encを要求しない。
- `plan` は内部消費が無い場合も含め、64+64の窓で第一段とimmediateを合成。
  `fused_actions_length` は途中の境界交換があっても各物理テープ最大6操作を保証。
  `plan_ideal` / `fused_apply` が途中の役割交換を含めた二段実行との一致を証明。
- `fusedRoles_other` / `fused_other` は他の役割・テープを保存し、既存ビュー層の4ヘッド、
  プログラム、鏡、入口の共通カウンタとの合成に必要な境界を明示する。

次は、この行動列の全EncTapes/EncControl・CounterShapesを組み立て、
入口のradius/length/cycle/remaining更新と既存12ステップのヘッド実行へ合成する。
その後 `running_lend` と同じ実tickで接続し、`cases_of_remaining` の入口ケースを放電する。
beginShift源がwatchであること、immediateのヘッド可用性、最終dispatcher選択も未完。
**39項目は21完了・18未完、旧T表は14あり・9未のまま。補題数をKPIへ加算しない。**

検証: `/tmp/local-role-fusion-build.log` **BUILD=0**、
`/tmp/physical-watch-actions.log` **EXIT=0**、
`/tmp/physical-watch-actions-workbench.log` **BUILD=0**、
`/tmp/physical-watch-actions-axioms.log` **AUDIT=0**。
新規2モジュールをWorkbenchに登録。新規公理guardは標準3公理のみ。
禁止構文なし・diff check成功。最終定理の追加公理依存は未解消。


## 二度消費の全符号化と単一sweepへの接続（2026-09-23）

前段の `PhysicalWatchActions` を、`PhysicalWatchStep` で共通の `CoreInv` に接続した。
`stateAfter` はchainの制御・カウンタだけを進め、verifierは既存ビュー層の実行を待つ中間状態。

- `result_counters` は全15本の名前付きカウンタを、途中の境界交換後の値・符号・
  padded tapeまで同時に同定。余分な物理テープや段の別表現は導入しない。
- `result_tapes` / `encControl_after` / `core_after` は、全118本のEncTapes、有限制御、
  マクロ境界を保存する。周期の左移動条件は既存Cursorから `cursor_left` で供給。
- `running` は源の共通Runningからspare/last/h鏡を取り出す。slot10を正規化するのは
  理想テープの存在証人だけで、`logical_congr` が実テープへのTEqG輸送を保証する。
  `of_watching_cache` が全CounterShapesも組み立てる。後状態Encを仮定するラッパーではない。
- `running_pair` は内部消費なし/ありの双方で、二段のRunningを `fused_apply` へ渡し、
  単一の実sweep後まで運ぶ。二つの量子の間で役割が変わる境界も含む。
- `pair_state` / `running_pair_good` は明示的な成功入力Goodから、結果を既存の
  `caught`→`immediate` と同定する。結論は `stepState` でverifierを源の場所へ戻した
  状態の共通Runningであり、独自のカウンタ状態だけを結論にしていない。

**未完:** この補助行を最終機械へ選択・融合すること。beginShiftがwatchから来ること、
内部/即時のGoodを実際の入口条件から供給すること、既存12ステップのヘッド実行、
radius/length/cycle/remaining更新、`running_lend` の交換、全入口を最終TickCasesへ接続すること。
非ヘッド側の全CoreInv保存が閉じたことと、入口全体が閉じたことは区別する。
**39項目は21完了・18未完、Tは14あり・9未を維持。**

検証: `/tmp/physical-watch-step.log` **EXIT=0**、
`/tmp/physical-watch-step-workbench.log` **BUILD=0**、
`/tmp/physical-watch-step-axioms.log` **AUDIT=0**。
Workbenchからルートへ登録済み。running / running_pair / running_pair_good のguardは
標準3公理のみ。禁止構文なし・diff check成功。最終公理依存は変更なし。


## shift入口の非ヘッド統合（2026-09-23）

`PhysicalShiftStart` の `running_nonhead` が、共通入口更新と二度消費を同じ実sweepへまとめた。

- `prepared` はradius++、length+=2、cycle/remaining reset、mode=shift、clock=2048、
  periodOnly=true。radiusの3鏡とlengthの鏡、退役FPPの背景消去も同時に行う。
- `tapes_prepared` / `core_prepared` / `invariant_prepared` が全118テープとCoreInvを保持。
  `running_prepared` は実テープをTEqGで運び、`running_entry` が旧remainingのreset直後に
  既存の `running_lend` を使う。鏡の内容をhとして貸し、ゼロになった旧remainingを再建鏡にする。
- 二度消費の各窓を64から32へ縮小し、その二段64と共通入口64を `plan` で融合した。
  全体のmicroRadius=128、macroRadius=1536、Γm、118テープ、共通CoreInvは変更なし。
  `PhysicalWatchStep.running_pair_ideal` / `running_pair_good_ideal` は融合前の理想行にも
  同じ保存を与え、追加の実ティックを導入せず合成できる。
- `source_of_guard` は既存 `WindowPack.source_watch_of_guard` を消費し、比較とshift guardから
  源watch・内部Good・内部処理後のwatch同定を供給する。
  `immediate_good_of_window` / `running_from_window` は既存ChainWindowRunと右ヘッドの
  入力表現・存在・可用性から即時Goodも導く。入力表現は到来済みprefixを引数に取れる。

**未完:** OnRunからその源の窓/入力表現を供給すること、既存12ステップのヘッド実行との合成、
全体をbeginShift/tickFunと同定し実dispatcher・最終TickCasesへ渡すこと。
`entryState` は源のヘッドを保持した中間状態。KPIは**21完了・18未完**、旧T表は**14あり・9未**。

検証: `/tmp/physical-shift-start.log` **EXIT=0**、
`/tmp/physical-shift-start-workbench.log` **BUILD=0**、
`/tmp/physical-shift-start-axioms.log` **AUDIT=0**。
Workbenchからルートへ登録済み。新しい4つの公理guardは標準3公理のみ。
禁止構文なし、diff check通過。最終定理の追加公理依存は未変更。


## shift入口のヘッド合成とtickFun同定（2026-09-23）

`PhysicalShiftLanding.running_tick` が、源の比較/shift guard・窓・右ヘッド表現・period形から、
抽象tickFunのshift入口を一回の物理sweepで模倣する。追加公理なし。

- `PhysicalTickAssembly.running_tick` は非ヘッドRunningのcanonical証人と既存12段の
  ヘッド実行を合成する。4本のヘッドがすべて存在する入口で、非ヘッドだけの役割交換を許す。
  literalなテープ等号にせずTEqGで共通CoreInv/CounterShapes/Cacheを保存する。
- `running_fused_route` は12段を既存macroRadius=1536へ融合し、実sweepと源の役割交換へ輸送。
  テープ118本、microRadius=128、有限制御と既存CoreInvは変更しない。
- `PhysicalShiftTick.running` は左カーソルをleft、右カーソルをright、検証カーソルを
  Internalの消費有無に応じてrightまたはright×2へ動かす。onLetter/leftFirstも更新する。
- `PhysicalShiftLanding.moved_eq_entry` はperiodLength_consumeで貸出し残量を同定し、
  比較後のbeginShiftと全状態が等しいと証明。`running_from_window` は源の比較/窓から
  両Goodを供給、`running_tick` はその到達状態を抽象tickFunのshift分岐へ接続する。

**残り:** OnRunから源のChainWindowRun・到来済み入力の右ヘッド表現/存在/長さを供給すること。
追跡中の入力切詰めと報告後plateauの両方を扱う。共通PhysicalBoundaryCount.machineへ
stepの選択を入れ、cases_of_remainingのshift入口を放電すること。
従って39項目は**21完了・18未完**、旧T表は**14あり・9未**を維持する。

検証: `/tmp/physical-shift-tick.log` **EXIT=0**、
`/tmp/physical-shift-landing.log` **EXIT=0**、
`/tmp/physical-shift-tick-workbench.log` **BUILD=0**、
`/tmp/physical-shift-tick-axioms.log` **AUDIT=0**。
新規3モジュールはWorkbenchへ登録。running_tick/running_fused_route/各runningのguardは
標準3公理のみ。禁止構文なし、diff check通過。最終公理依存は未変更。


## shift入口の源条件供給と到来上限の保持（2026-09-23）

`PhysicalShiftSource.running_onRun` が、最終消費者のrunからshift入口の全読取条件を供給する。
`Heads` は右ヘッドとwatch verifierの同じ入力表現・存在・非負lag台帳だけを持つ。
`heads_of_pack` は既存IPackMW.winとrightHead_of_packsからそれを取り出す。
`represents_trunc` / `heads_trunc` が到来済みprefixへ移し、`heads_onRun` は追跡中と
報告後plateauの両方を処理する。`watch_internal` と `good_at_right` が内部消費後の
lagゼロで同じ次文字を読むことと可用性を証明し、窓全体のprefixへの輸送を不要にした。

源の調査で、旧OnRunが実行のTrackedAt.usedを忘れていることが判明した。
`LocalShadowConcrete.ArrivedOnRun` は同じNeedyの証人k/jとusedVM≤jを保持する。
実行帰納法の `harrivedOnRun` が既存TrackedAt.needy/usedから供給するため、新しい仮定はない。
`pal_in_peg_of_shadowed_sysC` → `given_shadowedLocalSystem` →
`given_physicalMachine_indexed.hforwardTick` → `PhysicalContract.Obligations` /
`TickCases.active` と各active remainderまで運ぶ。旧OnRunへの忘却を用意し、
starved/feed/frozen/report/outの既存契約と旧非添字consumerは維持した。

**残り:** 共通dispatcherでこの有限な行を選び、最終TickCasesのshift入口を閉じること。
その時点までは39項目**21完了・18未完**、旧T表**14あり・9未**を維持する。

検証: `/tmp/physical-arrived-contract-build.log` **BUILD=0**、
`/tmp/physical-arrived-landing-build.log` **BUILD=0**、
`/tmp/physical-shift-source.log` **EXIT=0**、
`/tmp/physical-shift-source-workbench.log` **BUILD=0**、
`/tmp/physical-shift-source-axioms.log` **AUDIT=0**。
新規moduleはWorkbench登録済み。heads_onRun/running_onRunのguardは標準3公理のみ。
最終consumerの標準3公理guardも通過。禁止構文なし、diff check通過、最終追加公理は未変更。


## shift入口の共通dispatcher接続（2026-09-23）

`PhysicalShiftDispatch.machine rest` はPhysicalBoundaryCountの同じ有限制御・Γm・118本・
半径1536・Enc上に、shift入口の有限分岐を追加する。追加の物理tickは無い。

- `microWindows_read` は現在の役割表で論理順に読んだ実窓を128の窓へ制限する。
- `entryRead_iff` はscan/clock=1/watchers/非飢餓/不一致/比較後shift guardの読取と
  抽象の源条件 `Entry` の同値。`entry_of_compare` が抽象scan-shift腕の全体を覆う。
- `consumeTest_running` はlagカウンタ11を読み、Internalの消費有無を選ぶ。
  `apply_entry` がその有限選択を、証明済みの `PhysicalShiftTick.step` の実sweepに同定する。
- `comparison_of_entry` は合法TickからcompareFoundを取り出す。`forward_entry` は
  ArrivedOnRun/PreTraceIMWからPhysicalShiftSourceを使い、後状態の全Encを構成する。
- `forward_feed` / `forward_starved` と `cases_of_remaining` が既存の全接続を保持する。
  activeの残差は従来の4除外に `¬ Entry` を追加した。入口の未供給条件は残らない。

**T06完了。旧T表は15あり・8未（14あり・9未から1件減）。**
M3-01の鏡の保持・remainingへの引き渡しも完了し、内訳は4/5。残りはrestart用lastコピー。
39項目は**21完了・18未完**。M4-02はbeginFallbackが残るため未完、最終追加公理も残る。

検証: `/tmp/physical-shift-dispatch.log` **EXIT=0**、
`/tmp/physical-shift-dispatch-workbench.log` **BUILD=0**、
`/tmp/physical-shift-dispatch-axioms.log` **AUDIT=0**。
新モジュールはWorkbench登録済み。forward_entry/cases_of_remainingのguardは標準3公理のみ。
禁止構文なし、diff check通過。具体12段の二者択一は記号的な `select_lift_apply` で証明し、
巨大なstepを分岐ごとにsimpで展開する時間超過を避けた。


## restartの保存対象と源条件（2026-09-23）

`restartVM` を実際の消費者として読み直した。必要な出力はlower=last、work=last、
span=0、debt=-radius、DPリセット、chain=idle、clock=2048。
現行Encのmirrorsも含めると、lower/counter5、work/counter7、lowerのmirror3に
独立したlastの表現が必要になる。単にcounter15を一か所へ移すだけでは満たせない。

`PhysicalRestartStorage` の到達点:

- `replace` はlower/span/work/debtだけを差し替える。
- `background_replace` / `compare_replace` はchain非idleのもとで差し替えと実関数が可換。
  任意のSharedに対して成立し、探索が停止中に参照されないことを使う。
- `restart_replace` / `tick_restart_replace` は有効なrestartについて、差し替え前後で
  **後状態そのものが同じ**と証明する。全カウンタが入口で上書きされるため。
- `fallback_replace` / `arrive_replace` / `starved_replace` / `control_replace` は
  fallback、到来、飢餓判定、有限制御でも差し替えが保持されることを証明する。
- `restartRead_running` / `phase_restart` は実窓のrestart選択を保証。
  `commands_restart` は既存scanCommandsの4ビューがstayになることを保証する。
- `nextControl` / `control_restart` / `boundary_restart` はDP live切替えを含む有限制御と
  マクロ境界を更新する。テープの用意ができたという仮定は置かない。

現行EncTapesはこれらの古いカウンタも無条件に表現する。そのまま再利用したことには
できないので、上の非参照性を根拠に保存契約を直す必要がある。**まだEncは変更していない。**
探索用lower/spanの各鏡を含む領域でコピーを準備する案は未検証。鏡を貸した後の再準備と
DPの消去済みバッファの供給も、actual ActRuleと同じEncへ接続する必要がある。
全モードに対する差し替えシミュレーションは、今回の局所可換性から自動では出ない。

T02 restart・M3-01は未完。**39項目21完了・18未完、旧T表15あり・8未を維持。**
検証ログは `/tmp/physical-restart-storage.log`、
`/tmp/physical-restart-storage-workbench.log`、`/tmp/physical-restart-storage-axioms.log`。

検証結果: 単体 **EXIT=0**、Workbench **BUILD=0**、最終公理監査 **AUDIT=0**。
3つの公理guardは標準公理のみ。禁止構文なし・diff check通過。最終追加公理は未変更。


## 探索領域の再利用とlastの独立コピー（2026-09-23）

前回の記録よりworktreeが進んでいたため、まず現物を検証した。
`PhysicalRestartStorage.Related` は、探索停止中だけlower/span/work/debtの保存値を
差し替え、探索中は同じ値を要求する。`related_tick` は全10モード、`related_feed` は
実到来、`related_starved` は飢餓判定を保存する。`Stored` はこの代表状態と既存Runningの
合成であり、抽象VMやTickの定義を変更しない。最終dispatcherのEncはまだ従来のまま。

`PhysicalSearchRecycle` は既存counter5/6/7/8とmirror3/4を、watch入口と同じsweepで
resetする。`running_watch_entry` / `stored_watch_entry` / `ready_watch_entry` が、
時計減算・period移動・FPP背景消去と6本の準備を証明する。単体EXIT=0、module BUILD=0。

今回追加した `PhysicalSearchSnapshots` は、この6本の上で2組の独立した
boundary/last/spareを作る。組は(counter5,counter6,counter7)と(mirror3,mirror4,counter8)。
保存代表のlower=boundary、span=last、work=debt=spareとして既存EncTapesをそのまま使う。

- `tapes_put` / `core_put` は6本以外の全Enc・未使用counter形・Cache・マクロ境界を保存。
- `running_increment` は源counterの有限窓から0〜3行動を発行し、独立した鏡と符号を保存。
  `repolarize` はゼロの符号が違う場合も扱い、入口の符号正規化を要求しない。
- `running_rotate` / `saved_rotate` は2組を同時に有限役割交換する。
  準備済みspare→boundary、旧boundary→last、旧last→次回spareとなる。
- `overlayWith_running` はVM行と6本の更新を同じ源窓・同じ実sweepへ合成する。
  更新されたコピーのEncは仮定せず、更新行の実行証明から供給する。
- `entry_saved` が既存watch入口の実行からこの表現を供給する。
- `watchRow` は有限制御のphaseと既存period窓のFIRST/LASTから更新を選択する。
  `watch_consume` が実consumeのboundary/lastと次のInvへ接続する。両方向・全tokenを含む。
- `running_decrement` / `shift_running` は符号反転を有限制御内で使い、6本を各1行動で
  減算する。実chainShiftOneと次のInvへ接続し、追加の物理tickはない。
- `saved_last_copies` はcounter6/mirror4上の独立した2つのlastのRepを取り出す。
  既存counter15と合わせたrestartの3コピー供給を意図する。

**残差を明示:** `watch_consume` / `shift_running` の `base` と `hbase` は、
VM側の同じsweepを供給する未統合の接続面である。共通dispatcherはまだ新しいStoredと
2組のsnapshotを保持していない。既存boundaryRolesとの合成、比較での二度消費、feedと
不消費の保持、restartでlower/work/鏡へ渡す役割交換とspan/debt初期化、貸した鏡の再準備、
DPリセット用バッファ、最終TickCasesへの接続が残る。watchRow単体を全機械の完成と数えない。

**39項目21完了・18未完、旧T表15あり・8未を維持。T02/M3-01は未完。**
検証: `/tmp/physical-search-snapshots.log` 単体**EXIT=0**、
`/tmp/physical-search-snapshots-workbench.log` **BUILD=0**（stored_savedを含む最終コード）、
`/tmp/physical-search-snapshots-axioms.log` **AUDIT=0**。
SearchRecycle/SnapshotsをWorkbench登録。新規4guardは標準3公理のみ、禁止構文なし、
git diff --check通過。unconditionalの追加公理obligation_localRealizationは残る。


## コピー不変量を共通dispatcherのcountへ接続（2026-09-23）

`PhysicalSnapshotCount` が前回のconsume側の `base/hbase` を放電した。
VM行は既存 `PhysicalCountSpare.countStep rest`。`rotate_mix` がcounter14/15/10の交換と
探索6本のoverlayの可換性を、符号・テープともに証明する。`jointRoles` は旧3役と追加2組を
1つの有限役割更新にまとめ、`decode_row` が同じ実sweepの結果を同定する。
`forward_match` は実Tickからverifierの可用性を供給し、源窓のphase/FIRST/LAST選択を閉じ、
全token・両方向の成功countについて追加コピーと次のInvを返す。base/hbaseを引数に持たない。

`PhysicalSnapshotInvariant.Enc` は同じbootタグ・有限役割・118本・半径1536上の述語。
canonical状態とStateRelatedな代表の旧Encを持ち、watch/brokenのときはさらに
boundary/last/spareで上書きした代表の旧EncとInvを持つ。`of_watching` が実コピー状態から
全Encを構成する。`feed` は実到来、`preserve` は不変な物理遷移に対してこの契約を保存する。
追加の符号化事実を後状態の仮定として受け取らない。

`PhysicalSnapshotMachine.machine rest` は既存PhysicalShiftDispatchを拡張した共通dispatcher。
通常のsome入力とstarvedは旧行へ、watch入口は6本reset行へ、成功countは全3組同時交換行へ
源窓で分岐する。以下はすべて同じ新しいEncとこのmachine上で接続済み:

- `enc_initial` / `forward_feed`: 全空白開始、初回を含む全some到来。
- `forward_starved`: 全starved、watch/brokenのコピー保持を含む。
- `forward_atRest`: chain idle/search idle-or-missedの静止count。
- `forward_match` / `forward_mismatch` / `forward_quiet` → `forward_watch`:
  watch count全体。源のspare/Inv/コピーはEncから供給。token・方向・lag符号・成否の追加仮定なし。
- `forward_entry`: 正規back/FIRSTからwatchへ、同じ実sweepで6本をresetして新しいEncを構成。
  元の探索storageがcanonicalと違っていても、`saved_related` で実際の後状態を一致させる。
- `cases_of_remaining`: OnRun由来のperiod形とhを供給し、静止count/watch count/CountBackReadyを
  最終TickCasesへ渡す。boot/feedと同じ述語・機械・有限役割である。

既存APIは必要な源条件へ整理した。PhysicalBoundaryCount.running_match、
PhysicalCountMismatch.forward_count、PhysicalBoundaryCount.forward_mismatchは、局所証明に
必要なcanRightを受け取る。上位呼び出しは従来通り実際の合法Tickからそれを供給する。
探索代表へ偽のOnRunやTickを仮定して運んだものではない。
PhysicalWatchEntry.entryRead_runningは既存selected_entryの源窓証明を切り出して共有した。

**残差:** 新しいコピー付きEncの `hother` にはshift全体・shift入口・比較・restart等が残る。
旧PhysicalShiftDispatchではshift入口/進行/終了が証明済みだが、旧CoreInvには探索コピーが
無いため、その証明だけで新Encの保存を主張しない。新dispatcherのその枝はこれから追加コピー
更新を組み込む。shift_runningの局所base接続、二度consumeとsnapshot交換の融合、restartの
last3コピー引き渡し・span/debt/鏡/DPの再準備は未完。Count以外の未実装行restも残る。

次手は新dispatcherのshift行に`overlayWith decrement (workStep rest)`を組み込むこと。
進行はremaining正のときだけ6本を減算し、終了は保持する。合法shift Tick/RemainingBound/
CopyIdleはsearch4値を参照しないので、canonicalから保存代表へ源条件を運ぶ。
その後、既存の二段比較/shift入口のLocalRoleFusion計画へ同じsnapshot行を加える。

**39項目21完了・18未完、旧T表15あり・8未を維持。T02/M3-01は未完。**
単体ログ `/tmp/physical-snapshot-count.log`、`/tmp/physical-snapshot-invariant.log`、
`/tmp/physical-snapshot-machine.log` はいずれもEXIT=0。
最終検証: `/tmp/physical-snapshot-machine-workbench.log` **BUILD=0**、
`/tmp/physical-snapshot-machine-axioms.log` **AUDIT=0**。
新規3モジュールをWorkbench登録。count.forward_match、invariant.feed、
machine.cases_of_remaining/forward_watch/forward_entry/forward_match/forward_feedの
公理guardは標準3公理のみ。禁止構文なし、git diff --check通過。
unconditionalは依然としてobligation_localRealizationに依存し、無条件PALは未完。


## コピーを保つshift進行・終了を同じ最終TickCasesへ接続（2026-09-23）

`PhysicalSnapshotShift` が前節のshift側のbase/hbaseを放電した。
`saved_tick` は元の合法Tickからcenter/left/right(left)の可用性を取り出し、探索4値だけを
差し替えた保存代表の合法shiftを構成する。代表へOnRunを仮定しない。
`RemainingBound` はchainとremainingだけを読むので同じ源条件をそのまま使える。
`running` は既存 `PhysicalShift.running` と探索6本の `decrement` を
`overlayWith decrement (workStep rest)` にまとめる。源窓・実sweepは1つのまま、
正負・ゼロ越えを含む全コピーの減算と次回用Invを得る。後状態の符号化仮定は取らない。

`remaining_read` / `step_moving` / `step_exit` が実窓のremaining選択を抽象ガードへ結ぶ。
`exit_enc` は残量終了時の保存代表とwatch/brokenのコピーをすべて保持し、
`successor_saved_exit` で実際のtickFun後状態へ運ぶ。終了では6本を減算しない。

`PhysicalSnapshotShiftDispatch.machine rest` は直前のSnapshotMachineを拡張した共通dispatcher。
同じ有限制御・役割・118本・半径1536・`PhysicalSnapshotInvariant.Enc`を使用する。
`forward_shift` は全shiftモードを処理し、`cases_of_remaining` が消費者のOnRunから
CopyIdleと残量上限を供給する。shiftは新Encのhotherから外れた。
`previous_nonshift` / `forward_feed` / `forward_starved` により、blank/feed/starved/
idle静止count/watch count全体/正規watch入口も同じ機械・最終TickCasesで保つ。
旧ShiftDispatchのshift入口証明は維持するが、新Encの入口を証明したことには数えない。

**残差・次手:** 比較の内部＋即時消費、shift入口、restartに追加コピーの更新を組み込む。
接続先は `PhysicalWatchActions.plan`（32+32）と `PhysicalShiftStart.plan`（64+64）。
`PhysicalSearchSnapshots.rule` / `step` は現状microRadius/macroRadius固定なので、
小半径のActRuleへの一般化か同じ源窓からのoverlayを先に行い、LocalRoleFusionで1sweepへ戻す。
2回のmacro stepを抽象1tickとして扱わない。途中の14/15/10交換と追加2組の交換、
2回目のphase・token窓を同時に運ぶ必要がある。restartのlast3コピー引き渡し、
span/debt初期化・鏡再準備・DPリセット用バッファも未完。

**39項目21完了・18未完、旧T表15あり・8未を維持。T02/M3-01は未完。**
新2モジュールはWorkbench登録済み。最終コードの検証:
`/tmp/physical-snapshot-shift-workbench.log` **BUILD=0**、
`/tmp/physical-snapshot-shift-axioms.log` **AUDIT=0**。
running/exit_enc/forward_shift/cases_of_remainingの4guardは標準3公理のみ。
新規axiom/sorry/admit/native_decideなし、git diff --check通過。
無条件PALは未完。unconditionalのobligation_localRealizationは残る。


## コピー付き二度消費とshift入口を最終TickCasesへ接続（2026-09-23）

`PhysicalSearchSnapshots`のincrement compilerを窓半径Kへ一般化した。
`boundedRule` / `ideal_increment_bounded` / `running_increment_ideal` は3≤K≤marginで
既存6本を最大3増分する。従来のrule/step/ideal_increment/running_incrementは特殊化として保持。
`consume_updated`は具体updateの保存証明を受け取る共通合成部で、従来のconsume_mixも保持した。

`PhysicalSnapshotWatch` は元の `PhysicalWatchActions.rule` と小半径のincrement行を同時に実行する。
`mixed_logical` は旧境界交換が6本のoverlayを乱さないことを証明し、`logical_completed` が
旧14/15/10と追加2組の交換を同じ有限役割にまとめる。runningのbaseは既存WatchStepで放電済み。
`running_pair_ideal` / `running_pair` がoptional内部消費＋即時消費を32+32の1sweepへ融合する。
2回目は実際の中間phase・period・役割交換後の窓を読む。両方向・FIRST/LAST・連続境界を含む。
`goodAge/goodSpare`は抽象watch状態から決まる値で、物理証人ごとに任意の後状態を選ばない。
`running_good_ideal`が元のGoodからcaught/immediateと一致させ、Verifierだけをビュー実行待ちにする。

`PhysicalSnapshotEntry.plan` はこの64と既存entryRule/entryChangeの64を合成したmicroRadius=128。
`running_ideal` / `running` がradius/length/cycle/remainingの更新、h鏡の貸出しと全コピーを
同じ非ヘッドsweepで保持する。`PhysicalSnapshotEntryTick` がその行を既存12段ビュー実行へ載せる。
roles_headは追加2組の交換も全head bankを固定すると証明。next_controlは旧保存値と新保存値を
分け、左右カーソルの観測値だけを源窓で更新する。runningは3カーソル移動と全コピー・次回Invを
同じ半径1536の実sweepで返す。2つのmacro tickを1つに数えていない。

`PhysicalSnapshotEntryDispatch.machine rest` が最新の共通機械。
`forward_entry`は元の合法Tick/ArrivedOnRunから比較関係、両Good、到来prefix、period形を供給し、
`moved_eq_entry` / `tick_eq_entry`で実際のtickFun後状態を同定する。保存代表へOnRunを仮定しない。
`PhysicalCompareGuard.scanShiftRead_running_ready`は源verifierのcanRightだけを受け取り、
元のTick付きscanShiftRead_runningもwrapperとして維持。entry_saved/entryTest_readyが
保存代表の実窓guardと元のEntryを接続する。feed/starved/既存count/watch入口/shift進行・終了も
同じEncとmachineで保ち、`cases_of_remaining`のhotherからshift入口を外した。

**残差:** 成功二度消費の共通行とshift入口は接続済みだが、他の比較腕（matched、beginFallback等）、
restart、DP等はhother/restに残る。全比較・全機械が完成したとは数えない。
**次手:** M3-01/T02へ戻り、lastのcounter15/counter6/mirror4からlower/work/鏡3へ渡す
有限役割を具体化する。span/鏡4は同じsweepでresetできるが、debt=initialDebt(radius)には
半径コピーと符号反転が必要。radius鏡を貸すなら旧Encの全mirror義務と再準備を解決する。
DP resetのinactive bankの空白、live反転、背景消去も実装して供給する。後状態Encや空白を
未供給の仮定として置いてrestart完成にしない。

**39項目21完了・18未完、旧T表15あり・8未を維持。T02/M3-01は未完。**
新4モジュールはWorkbench登録。最終コードの検証:
`/tmp/physical-snapshot-entry-workbench.log` **BUILD=0**、
`/tmp/physical-snapshot-entry-axioms.log` **AUDIT=0**。
Watchのrunning/running_pair/running_good_ideal、Entry.running、EntryTick.running、
EntryDispatch.forward_entry/cases_of_remainingの7guardは標準3公理のみ。
禁止構文なし、git diff --check通過。unconditionalはobligation_localRealizationに依存し、無条件PALは未完。


## restartのlast3コピー引き渡し（2026-09-23）

`PhysicalRestartCopies` は同じ118本・Γmの上に、restartへ融合する半径32の中間行を実装した。
`slots`は(c5,c6)、(c7,c15)、(mirror3,mirror4)の3交換。
源c5/鏡3へseparatorを各1行動で書き、交換後はlower=c6のlast、work=c15のlast、
lower鏡=mirror4のlast、span/鏡4=resetになる。旧chainをidleへ退役させるため、
入れ替わったc15に旧lastを保持する義務はなく、全counterの段形は保存する。
`prepared`はclock=2048、chain=idle、search=grow/final=false/quarter=0まで更新し、
**debtとDPは源の値を保持**する。半径鏡を渡したことにはしていない。

`control_prepared` / `tapes_prepared` / `shapes_prepared` → `core_prepared`は全ヘッド、
FPP/DP両live bank、退役FPP、残りのカウンタ・全mirror・マクロ境界を含むCoreInvを保存。
`logical_prepared`は実rule/changeのreset後交換を同定する。`running_ideal`はTEqG表現へ、
`running`は任意の源役割を持つcompiled planの実sweepへ運ぶ。行は2テープに各1アクション。
`from_copies`は現在の`PhysicalSnapshotInvariant.Enc`のCopiesから源の保存代表を取り、
lastの準備や後状態Encを追加仮定にしない。

`finishDebtDp`は残る抽象2更新を明示するためだけの定義。
`completed_is_restart`が、restartGuardとmode=scanのもとでこの2更新後に実tickFunの
successorと一致することを証明する。guard由来のlast正によりSearch.beginのwork=lastも同定。
**finishDebtDpの物理行は未実装。中間行を完成restartや追加の抽象tickとして数えない。**

次はdebt=initialDebt(radius)の半径コピー引き渡し。mirror2等を貸す場合、現行EncTapesは
全radius鏡を無条件に要求するため、交換だけでは後状態Encが成立しない。
必要時だけ鏡を要求する契約・再準備の保存、または同じレイアウト内での別の具体供給を閉じる。
inactive DP bankは現行Encでmarginしか拘束されておらず、空白と仮定できない。
DP live反転・実reset用バッファ・背景消去の充足、その後のrestart全行融合と実窓dispatchが残る。
共通機械は`PhysicalSnapshotEntryDispatch.machine rest`のまま。T02/M3-01は未完、
**39項目21完了18未完、旧T表15あり8未を維持**。

新モジュールはWorkbench登録済み。`/tmp/physical-restart-copies-workbench.log` BUILD=0、
`/tmp/physical-restart-copies-axioms.log` AUDIT=0。running/from_copies/completed_is_restartの
3guardは標準3公理のみ。禁止構文なし、git diff --check通過。
unconditionalのobligation_localRealizationは残り、無条件PALは未完。


## debtの半径鏡借用と再準備の実行（2026-09-23）

`PhysicalDebtMirror`は現行Encが全radius鏡を常時要求する問題を明示的に扱った。
実mirror2をcounter8へ有限交換し、q.polarity8を!q.polarity2にすることでinitialDebt radiusを
定数時間で渡す。旧counter8はseparatorでresetし、交換後のmirror2として再準備を始める。
レイアウト・Γm・118本・半径1536・有限制御の型は維持した。

`RebuildingCore`の契約:
- 実mirror2は `credit x = ofNat (value radius + min (value debt) 0).toNat` の段カウンタ。
- `CoreInv w x (q,repaired T)`でそれ以外の全テープと制御を拘束する。
- `repaired`は証明側でmirror2だけを実mirror0と置換する。物理コピーも未検証のghost行もない。
- `Rebuilding`はこの述語の既存sweepClosure。TEqGによる任意の物理表現を受け取る。

`tapes_patched`/`core_borrowed`は新debtとreset済み部分鏡、全残存テープ・counter形・
マクロ境界を保存する。`running`は32窓の実rule/有限役割をcompiledの1sweepへ運ぶ。
`tapes_unrepair`/`core_ready`/`ready`は、半径とdebtが非負なら実部分鏡が半径に等しく、
従来Runningへ戻せることを証明。途中の鏡を全半径コピーと誤って扱っていない。

`restartPlan = seqRule RestartCopies.plan DebtMirror.plan`は32+32。
`restart_running`が2段の実有限交換を単一sweepで実行し、`restart_from_copies`が同じ
canonical Encから源のlast3コピーを供給する。`only_dp_left`はこの後にDP resetを施せば
実tickFunのrestartになることを証明。**残るDP resetはまだ抽象関数finishDpであり物理未実装。**

`PhysicalDebtRebuild`は部分鏡を次のtickへ維持する実行部品。
`paid`はdebt++。`credit_paid`が負の場合のみcredit++、非負ならcredit維持と証明する。
`negative_read`は証明用補完が実debtテープの窓に影響しないことを使って実有限判定へ結ぶ。
`core_paid`/`core_ideal`はdebt tape/signと部分鏡を更新し、その他全Encを保持。
`running`は半径32の実sweep。`running_double`は2回を32+32へ融合し、途中のdebt=-1→0では
2回目の更新済み窓を使い、鏡を余計に増やさない。growのspan/work更新はこの定理に含めない。
`borrowed_balance`は借用直後のradius+debt≥0を無条件で供給、`paid_balance`は増分で保存。
`credit_advance`は同時radius++/debt--の再準備量を同定するが、その物理行はまだ未実装。

**再準備出口での注意:** SafeCallsの非負検査は最後のadvance aより前にある。
終了時debt=-1の可能性を、SafeQuantaだけで消さない。`credit_one_short`はdebt≥-1なら
鏡の不足が高々1であると証明する。実不足の補完行、到達状態からの境界条件供給は残る。

**統合の残差:** RebuildingCore/Runningは部品の契約で、まだ最終共通Encに入っていない。
共通機械は引き続き`PhysicalSnapshotEntryDispatch.machine rest`。
比較時の再準備保存、feed/starvedの保存と共通Enc/dispatch統合、search完了の補完、
DPのinactive bank空白・消去・live反転、restart全行を同じmacroへ接続する仕事が残る。
統合案はchain=idleかつsearchActiveのとき部分鏡を要求し、他の既接続ケースは旧契約を
使う形。これはまだ設計案であり、全モード保存の証明済み契約ではない。
DP空白や後状態Encを未供給の仮定に置き換えない。

両モジュールはWorkbench登録。`/tmp/physical-debt-rebuild-workbench.log` BUILD=0、
`/tmp/physical-debt-rebuild-axioms.log` AUDIT=0。
DebtMirror.running/ready/restart_from_copies/only_dp_leftとDebtRebuild.running/running_doubleの
6guardは標準3公理のみ。新axiom/sorry/admit/native_decideなし、git diff --check通過。
**39項目21完了18未完、旧T表15あり8未を維持。T02/M3-01未完。**
追加公理obligation_localRealizationは残り、無条件PALは未完。


## 2026-09-23: 再準備契約を共通機械へ接続

最新の機械は`PhysicalLoanDispatch.machine rest`、符号化は`PhysicalLoanInvariant.Enc`。
旧SnapshotEntryDispatchは既証明の非飢餓行とblank bootの実装として再利用する。
118本・Γm・micro128/macro1536・12段ヘッド実行・有限役割は変更していない。

`NeedsLoan`はscanかつchain idleかつsearchActive。該当時は`Balanced`（radius≥0、radius+debt≥0）と
実部分鏡の`Rebuilding`を要求し、非該当時は従来のSnapshot Encを要求する。
proof用の`repaired`を実コピーと混同せず、実mirror2の信用量を別に保持する。
`PhysicalDebtFeed.view_repaired/head_control_repaired/feed_nq_congr`から、補完前後で同じ
ヘッド処理が選ばれる。`step_complete/run_complete`が12段との可換性、`run_mirror`が実鏡の不変を証明。
`core_feed/running_feed`は全残存CoreInv・マクロ境界と部分鏡を実sweepへ運ぶ。
`starved_repaired/starved_running`は実窓による飢餓判定を復元する。
具体readWinを含む大きなfeed.nq等式はkernel timeoutになったため、窓を記号的に取る
`feed_nq_congr`へ分離し、headの一致だけを渡した。heartbeat増加で回避していない。

`PhysicalLoanInvariant.enc_initial/running_feed`は全空白と有限役割を含む入力行を同じEncへ接続。
`PhysicalLoanDispatch.transportTest`は実finite control/windowだけでrunningのsomeとstarvedを選び、
従来の`hold feedStep`を実行する。bootは既存実装。`forward_feed`は最初の到着も含む。
`forward_starved`は部分鏡を含む全starvedを保存する。
`previous_active`により、非飢餓の実行行は以前の機械と同じ。
`cases_of_remaining`はCountAtRest、CountWatch全体、CountBackReady、Entry、shift全体を保持する。
これらの源/後状態がNeedsLoanでないことも証明した。shift終了の源chain非idleは
`shift_nonidle_tick`をpre-traceで運び、OnRunの入力切詰め/plateauに接続して供給する。
後状態Encや部分鏡の完成を未供給の仮定にしていない。

**残差:** 非飢餓のactive idle-chain searchは依然hother。既存DebtRebuild.payの単/二回実sweepを
span/work更新へ融合し、比較時radius++/debt--、search出口の不足1補完を閉じる必要がある。
DPの退役bank消去・初期化とrestart全行のdispatchも未完。restart中間行の存在は全restartの完成ではない。
既存のSafeCallsの非負検査は最後のadvance前なので、出口debt=-1を考慮する。

3モジュールをWorkbench登録。`/tmp/physical-loan-dispatch-workbench.log` BUILD=0、
`/tmp/physical-loan-dispatch-axioms.log` AUDIT=0。
DebtFeed.running_feed/starved_running、LoanInvariant.enc_initial、
LoanDispatch.forward_feed/forward_starved/cases_of_remainingの6guardは標準3公理のみ。
新axiom/sorry/admit/native_decideなし、git diff --check通過。
**39項目21完了18未完、旧T表15あり8未を維持。T02/M3-01未完。**
最終のobligation_localRealizationは残り、無条件PALは未完。


## 2026-09-23: active idle-chain searchのgrow countを接続

`PhysicalGrowStorage`は既存段付きcounterの源窓からspanの8増分・workの1減算を生成する。
spanの実counter6と独立mirror4は、同じ源窓の途中符号を使って更新し、零を跨ぐ場合も保存。
`withErase`で退役FPPを背景消去し、全CoreInv・未使用counter形・マクロ境界を保持する。
`sign_repaired/actions_repaired/step_complete`は部分radius mirror2のproof補完と可換。
実mirror2は不変で、`rebuilding_core/rebuilding_ideal`がRebuilding全体を保持する。

`PhysicalGrowCount.grown`はこのspan/work更新とpaid×2。`background_grow/successor_eq`が
sourceのscan/clock>1/chain idle/search grow/work正と非飢餓から実tickFunと同定する。
`body = seqRule GrowStorage.rule DebtRebuild.doubleRule`は64+(32+32)=128。
2返済は中間のdebt窓を読み、-1→0を跨ぐときの過剰な鏡pushを避ける。
`body_ideal`はbalanceと実部分鏡を同じ融合内で保存する。
`windows`はmacro1536から128を読むだけで、追加の機械tickではない。
`rule/running`がclock減算も含む1回の実macro sweepを証明する。
このcountでは抽象ヘッドが不変なので物理ヘッドテープ/制御とslot0/owed0もそのまま保持。
feedや移動tickに必要な12段executorを追加実行として数える構成ではない。

`CountGrow`を新しい実分岐条件とし、`guard_running`は共通Encから物理controlとwork窓の一致を供給。
非借用のSnapshot側でも同じguardの正しさを証明し、他の既接続ケースを誤選択しない。
`PhysicalLoanDispatch.machine rest`へgrowTest/hold GrowCount.stepを追加。入力・飢餓判定が先。
`forward_grow`→`cases_of_remaining`でhotherに¬CountGrowを追加し、この残差を実際に除いた。
初回到来・全starved・idle静止count・watch count全体・watch入口・shift入口/進行/終了も保持。
118本・Γm・finite role・micro128/macro1536の固定値を維持する。

**残差:** work=0でprepareへ移る行、clock=1の比較とradius++/debt--、他の探索モード、
search終了の不足1補完、DP初期化/bank再利用、restart全行は未完。
prepareの実定義はDP reset(pc320)、tape10の初期マーク、work=lower、walker=centerを同時に要求する。
doubleはspan+=2・work--・quarter=(quarter+1)%4、debt++はquarter=3だけ。
その定義をgrowのspan+=8/debt+=2と混同しない。SafeCallsの出口debt=-1にも引き続き注意する。

2モジュールをWorkbench登録。`/tmp/physical-grow-count-workbench.log` BUILD=0、
`/tmp/physical-grow-count-axioms.log` AUDIT=0。
GrowStorage.rebuilding_ideal、GrowCount.running/forward、LoanDispatch.forward_growの4新guardと
更新したcases_of_remaining guardは標準3公理のみ。新axiom/sorry/admit/native_decideなし。
git diff --check通過。**39項目21完了18未完、旧T表15あり8未、T02/M3-01未完を維持。**
最終のobligation_localRealizationは残り、無条件PALは未完。


## 2026-09-23: grow比較の非ヘッド更新と部分鏡対応のヘッド組み立て器

`PhysicalMatchCounters`は同じ118本・Γm・段カウンタでradius++/length+=2/debt--と、
periodOnly/replayingで選ぶcycle/replayの減算を実行する。全量鏡の参照行は`rule`、
実部分鏡を扱う行は`actual/currentRule`。実mirror2をpushするのはこの行の源debtが正の場合だけ。
それ以外は鏡を動かさず、radius+min(debt,0)の増分式から正しい信用量を証明する。
`step_complete`は証明用補完と参照行の可換性、`rebuilding_core/running/running_current`は
実部分鏡・他の全CoreInv・counter形・マクロ境界の保存を与える。zero時の負符号も処理する。
比較によるradius++/debt--はbalanceを保存する。

`PhysicalGrowStorage.rule`の内部半径は行動長を検証して64から32へ縮小した。
spanの8増分とwork減算、独立span鏡、背景FPP消去の機能は同じ。
`PhysicalGrowCount.body`は32+(32+32)=96となり、既存grow countのmacro1536接続も維持する。
`PhysicalGrowMatch.body`がgrow96＋比較32を既存micro128へ融合。
2回の返済と比較の減算は、それぞれ中間窓を読み、debtの零跨ぎと部分鏡のpushを同じsweep内で扱う。
`running`は半径128の実sweep、`matched_grow`はchain idle/search grow/work正/比較一致から
compareFunとmatchedPlaceのVM更新が、この行＋left/right移動に等しいことを証明した。
比較行だけを新たな抽象tickにしていない。ctl/output更新はこのVM同定には含まれない。

`PhysicalTickAssembly.running_tick_optional`はheadOfがnoneのカーソルをstayで処理できる。
元の`running_tick`は全headがsomeの場合の互換ラッパーとして維持した。
`PhysicalLoanAssembly.running_tick`は源/非ヘッド後状態のRebuildingを使い、
実部分鏡をcanonical witnessに残したままヘッドだけ12段実行の結果に差し替える。
proof viewだけをrepairし、実テープにradiusの瞬間コピーは行わない。
`running_fused_route`は同じ有限役割とmacro1536の実sweepへ輸送する。
名前のないidle verifierも含み、ヘッドをすべてsomeとする偽の源条件を要求しない。

**未接続:** grow比較に固有のctl/output・head readiness・実窓guardを供給し、
LoanAssemblyを適用して最終TickCasesへ渡す部分。共通`PhysicalLoanDispatch.machine rest`の
最終残差から除いた探索行は依然CountGrowだけで、matched growはhotherに残る。
prepare/他の探索行/search出口補完/DP reset・bank再利用/restart全行も未完。
**39項目21完了18未完、旧T表15あり8未、T02/M3-01未完を維持。**

3モジュールをWorkbench登録し、旧TickAssemblyの互換APIも維持した。
`/tmp/physical-grow-match-workbench.log` BUILD=0、
`/tmp/physical-grow-match-axioms.log` AUDIT=0。
MatchCounters.running/running_current、GrowMatch.running/matched_grow、
TickAssembly.running_tick_optional、LoanAssembly.running_tick/running_fused_routeの新7guardは
標準3公理以内。新axiom/sorry/admit/native_decideなし、git diff --check通過。
最終obligation_localRealizationは残り、無条件PALは未完。


## 2026-09-23: grow一致比較を同じ最終TickCasesへ接続

`PhysicalGrowMatchTick`は実body（grow96＋比較32）へ有限制御の`scanMatchedCtl`と出力2bitを重ねる。
`next_control`は部分鏡のproof補完がhead/counter4の読みを変えないことから、源窓のonLetter/leftFirstと
減算後replayのzero判定を実VMの後状態へ結ぶ。clock=2048、outputの条件更新、replaying終了も含む。
`commands`は左moveLeft・右moveRight・他stay。`ready`はright.canRightから到来を供給する。
`running_ideal/running`が同じ12段・macro1536の実sweepで全Rebuildingと実部分鏡を保存する。
未命名のidle verifierにheadOf=someを要求しない。118本・Γm・有限役割は従来と同じ。

`MatchGrow`は(scan/clock≤1/chain idle/search grow)∧work正∧左右着地文字一致。
`PhysicalGrowMatchCase.successor_eq`は非飢餓から実tickFunがこの行のtargetに等しいことを証明する。
`guard_running`は同じ有限control/windowからこの条件を復元し、非NeedsLoan状態での誤選択も排除。
`forward`は源Encからbalance/部分鏡、後状態NeedsLoanを供給し、共通Encへ実sweepを戻す。

`PhysicalLoanDispatch.machine rest`にtransport→CountGrow→MatchGrow→旧実行行の順で組み込んだ。
入力到来・飢餓が先で、countと比較はclock条件で排他的。`forward_match`が選択と実sweepを接続する。
`cases_of_remaining`のMatchGrow枝では、`PhysicalShiftSource.heads_onRun`を再利用し、
ArrivedOnRun/PreTraceIMWから同じ到来prefix表現と長さ上限を供給する。right.canRightは非飢餓scanから得る。
**hotherに¬MatchGrowを追加し、この実行由来の比較ケースを最終残差から除いた。**
初回feed/全starved/CountGrow/idle静止count/watch count全体/watch入口/shift全体も保持している。

**残差:** work=0のprepare、他の探索モード、比較不一致/fallback、search出口の部分鏡不足1補完、
DP初期化・bank再利用、restart全行。現EncTapes.idleShapeはFPP9本で、DP退役側の形もまだ契約にない。
prepareはpc320/reset/tape10のLEFT-right/work=lower/walker=centerを同時に実行する。
lower→workや後のspan→workのaliasを追加tick・後状態仮定で置き換えない。
matched全体は未完なのでM4-01/T05を完了にしない。

2モジュールをWorkbench登録。`/tmp/physical-grow-match-final-workbench.log` BUILD=0、
`/tmp/physical-grow-match-final-axioms.log` AUDIT=0。
GrowMatchTick.running、GrowMatchCase.guard_running/forward、LoanDispatch.forward_matchの新4guardと
更新したcases_of_remaining guardは標準3公理以内。新axiom/sorry/admit/native_decideなし。
git diff --check通過。**39項目21完了18未完、旧T表15あり8未、T02/M3-01/T05未完を維持。**
最終obligation_localRealizationは残り、無条件PALは未完。


## 2026-09-23: DP退役テープの有限消去器を実sweepで検証

**Workbench BUILD=0・最終公理監査AUDIT=0・無条件 PAL は未完。**
`PhysicalProgramErase`をWorkbenchへ登録。同じΓm・118本の退役DP12本に対し、
rewind/clear/home/doneの有限制御と半径1の行動列を実装した。
`left_only_stuck`は旧eraseActが非空白のrootでも停止し、右側を消去しない具体例を証明する。
`Dense`（rootから非空白接頭辞と空白接尾辞）の源条件の下で、`reusable`は
3*(left.length+right.length)+5回以内の消去・root復帰を証明。
`bank_sweep/stored_run/bank_real_reset`が実compStepの反復まで運び、最終物理テープを
canonical resetとTEqGで結ぶ。空白接尾辞をリテラルに捨てる操作は要求しない。
各sweepは各退役DPテープを最大1アクション更新し、他のテープはTEqGで保持する。
`encTapes_retired_dp/bank_enc/bank_sweep_enc`で既存の全Encと余白も同じ実sweepへ保持した。
長さは証明側のみで、有限制御に格納しない。**この別の有限制御は共通LoanDispatchへ未統合。**
Denseと必要な消去時間は定理の明示的な源条件で、実DP trace/スケジュールからの供給は未完。
既存EncのDP退役側契約・live切替え・prepare/restart接続も未完。hotherは減っていない。
新5guardは標準3公理以内。ログ: `/tmp/physical-program-erase-{workbench,axioms}.log`。
git diff --check通過。**KPI21完了18未完、T15あり8未、T02/M3-01/T05未完を維持。**

次は源条件供給と共通契約への統合。GalilDpCodeの小さい381実行（binary長0..6、lower1..3）で
全途中状態のDenseに反例なし、最大860命令。これはPython診断でありLean証明ではない。
`/tmp/physical-dp-density-probe.json`に結果あり。
PCごとにfrontier距離を0/1/2以上へ抽象化した診断では10/12本で不正更新候補なし。
marksの8/9だけ右移動の候補が残る（8:229/232/235/238、9:323/326/329/332）。
この表も未検証。GalilDpSimulation.Relatedのmarks/head同期と、0/8/9の位置・長さ関係を
使うか、既存prepared実行の途中状態の不変量を強める必要がある。
新しい仮定や小さい実験で実行全体のDenseを代用しない。


## 2026-09-23: DP12本・FPP9本の全実行途中から消去のDenseを供給

**Workbench BUILD=0・最終公理監査AUDIT=0・無条件 PAL は未完。**
`GalilDpDensity.onRun`は任意のFin3入力・任意lowerの実DP初期配置から、成功命令の
任意prefixで12本すべての非空白接頭辞＋空白接尾辞を証明する。Denseの追加仮定はない。
`fpp_onRun`は既存`GalilDpSimulation.steps`で9本FPPへ同じ結論を戻した。

難所はMARKS8/9のheadがblank frontierを越える点。単純なhead上限は偽になり得る。
`GalilDpDenseMarks.future_prepared`は実行の一意性とsearch閉包から、実prefixを
既証明のprepared終状態へ延長する。`emit_inside`はpc36/321以後のMARKS書込みが8だけである
有限表と、完成形のEND=5・blank suffixから、実emitの位置が現在の密な接頭辞内だと証明した。
その源条件と、`GalilDpDensityTable.rows`の全373命令×12本×4位置区分のカーネル検査を合わせる。
表の位相はfrontierに対するheadのpast/edge/last/interior。生成データ自身は信頼せず、
`GalilDpDensity.step`がread/move/writeの実意味に対する保存を証明する。
表を巨大な配列で一括decideするとメモリが増えたため、その検証プロセスを止めて
4bit/PCのNat定数と32命令ごとの検査に変更。最終Table buildは約12秒、native_decide不使用。

`PhysicalDpDensity.dense_onRun/dense_fpp_onRun`は実`GalilScaffoldControl.Run`から
待機・halt・halt後を含めてこの形を取り出し、既存の`PhysicalProgramErase.Dense`へ変換する。
`run_size`は各テープのleft+right長を初期長＋enabled call数で抑える。
`bank_reset_onRun`は前回の実sweep消去器へDenseを供給し、
3*(max(w.length+1,lower+1)+bs.count true)+5回以上ならresetへのTEqGを返す。
後状態の空白やDenseを仮定しない。初期preloadからの実行履歴と元のBankRep/Storedは必要。

**残差:** その消去回数を再liveまでに既存ティック内の背景処理へ割り当てる証明、
有限phaseを共通LoanDispatchへ載せること、PAL全体のOnRunから当該program Runを供給する接続、
preload完成前のlower/sourceロード中の打切り、DP live切替え・prepare/restartの実行行が未完。
共通機械は`PhysicalLoanDispatch.machine rest`のまま、hotherも未変更。
FPPの旧左向きeraseOfは引き続き置換が必要。今回のDenseはlive programの実行由来であり、
既に旧消去を受けた退役FPPに無条件で当てはめない。
追加tickや後状態Encを仮定して再利用を閉じない。

4モジュールをWorkbench登録。新8guardは標準3公理以内（Table.rowsはpropext/Quot.soundのみ）。
ログ: `/tmp/physical-dp-density-{workbench,axioms}.log`、git diff --check通過。
**KPI21完了18未完、T15あり8未、M3-06/T02/M3-01/T05未完を維持。**
`obligation_localRealization`は残る。正本はAGENTS.md §0とPHYSICAL_CONNECTIONS.md末尾。


## 2026-09-23: DP消去を共通dispatcherと同じsweepへ載せ、boot/feed/starvedを接続

**Workbench BUILD=0・最終公理監査AUDIT=0・無条件PALは未完。**
`PhysicalDpCleanup.machine rest`は既存`PhysicalLoanDispatch.machine rest`に
12本分のrewind/clear/home/doneだけを有限制御として加える。同じΓm・118本・半径1536。
通常処理の次の役割/live bitを源窓から計算し、次に退役側となるDPだけを、同じ源窓から
消去する。bankを切り替えればphaseをrewindへ戻す。物理テープごとに通常処理/消去の
窓と移動量を選ぶので、半径を足したり抽象tickを追加したりしない。

`PhysicalEraseBatch.stored`は任意の固定n段を半径nの1回の実sweepへ融合する。
共通機械ではn=1536（各テープ最大1536アクション）。`Good`は密な源からの実消去経過を
証明側だけに持ち、`done_clean`と`PhysicalDpCleanup.ready`がdoneからresetへのTEqGを供給。
長さや経過時間は有限制御に持ち込まない。`PhysicalRetiredDpFrame.loan`はDP退役側の変更を、
snapshot・貸し出し中の部分鏡を含む既存の共通Loan Encへ通す。
`apply_running/forward`は実際の並行sweepの等式と旧Enc・消去状態の保存を証明する。
`forward_kept`はbankとDPの役割が変わらない任意の検証済み行へ進捗を運び、
`forward_retired`は切替え前の新退役テープのDense/表現を源条件に新しい消去を開始する。
これらの一般補題にある旧Encの後状態は、接続先の各行の証明で供給する必要がある。

`PhysicalDpCleanupBoot.boot_banks`は実blank bootが両bankへ番兵・空白を用意することを証明。
`forward_feed/forward_starved`で、初回を含む全feedと全starvedを新しい同じ機械/Encへ接続した。
源条件は既存Encから取り出し、後状態の空白は仮定しない。新ControlのFintype/DecidableEqも確認。
具体的な12段実行を直接change/rflで比較すると時間切れになったため、`held_bank/held_roles`、
`boot_nonhead`の一般補題と、融合規則全体の記号化で回避した。新Boot moduleは最終build約5秒。

**残差:** 非飢餓の既存count/watch/shift/grow/match行を新Progress付きEncへ移す接続、
最終TickCasesの更新、再liveまでの消去期限、PAL全体のOnRunからprogram Runを供給する接続、
preload完成前のロード打切り、live切替え・prepare/restartの実行行は未完。
旧`PhysicalLoanDispatch.cases_of_remaining`は保持し、hotherはまだ減らしていない。
FPP旧左向き消去の置換も残る。live時のDenseを、既に穴ができた退役FPPへ当てはめない。
新機械のboot/feed/starved接続と、既存の全activeケースの移行完了を混同しない。

4モジュールをWorkbench登録。新13guardは標準3公理以内、sorry/新axiomなし。
ログ: `/tmp/physical-dp-cleanup-{workbench,axioms}.log`。git diff --check通過。
**KPI21完了18未完、T15あり8未、M3-06/T02/M3-01/T05未完を維持。**
`obligation_localRealization`は残る。


## 2026-09-23 15:05: Claude Codeへ引き継ぎ — 最新はCLAUDE.md冒頭

ユーザーの依頼により、具体的な再開手順・未解決・注意点を `CLAUDE.md` 冒頭に記載した。
**無条件PAL未完、KPI21完了18未完、局所実現公理1本は残る。**

`PhysicalDpCleanup.machine rest` / `PhysicalDpCleanup.Enc` が最新の共通接続。
`PhysicalDpBank.machine`が現在のLoanDispatch全体のDP live bit/両bankアドレス保存を証明し、
`PhysicalDpCleanupDispatch.cases_of_remaining`で既存7activeケースを新機械/Encへ移行した。
boot/feed/starvedも接続済み。同じ118本・半径1536・1sweepで背景消去し、hotherの7除外条件は変更なし。
`PhysicalLoanDispatch.active_of_remaining`を抽出したことで局所ケースを再利用できる。

`PhysicalDpPreload`は実prepareから任意の途中Runで12本Denseと長さ≤1+enabled回数を証明。
`PhysicalDpRetirement.live`はsnapshot/部分鏡を含む共通源Encからlive DPのTEqGを供給する。
`forward_preparing/program`が実Run由来のDenseを同じwrapの退役開始へ渡す。
ただし通常reset行の後状態Enc/実step等式・PAL全体からの当該Run供給・再liveまでの時間は未解決。
現在の全dispatcherはDP bitを保持する。reset/flip行を追加するときは保持行と別扱いする。
FPP旧左向き消去の置換、prepareのlower→work/span→work、restart全行なども残る。

新4モジュールをWorkbenchへ登録。今回の新10guardは標準3公理以内、sorry/追加axiomなし。
**Workbench BUILD=0（9810 jobs）、最終公理監査AUDIT=0。**
ログ: `/tmp/physical-dp-retirement-{workbench,axioms}.log`。git diff --check通過。
ビルド実行は終了済み。大量の既存変更/未追跡ファイルは保存し、commit/pushはしていない。
詳細な次手と性能上の注意は `CLAUDE.md` 冒頭を参照。
