## 2026-09-19: inline draft reverted; checkpoint

ユーザー指示で未完成・未検証の cycle inline proof を撤去し、既存の2公理による
最終定理へ戻した。`CanonicalChainMinimal` の shift 最小性、search/chain readiness、
fallback/replay、および周期境界の証明は保持。cycle と local realization は未解消。

**次の作業で要確認:** Scala/Python は broken chain で search を restart するが、
Lean の `GalilTickFair.Canonical.noRestart` は禁止する。Python 正本の broken-restart
分岐だけを省いた実行で、入力 prefix `abaaaaababaaabaaaaabaaaaabaaaaabaaaa`、
centre=45、radius=25、fallback move=6、chain=broken を観測した。
従って、この実行では `radius ≤ 4*move` は不成立。これは Python 診断であって
Lean の packed-run 到達可能性の証明ではなく、cycle 公理そのものの反証とも断定しない。
この条件の相違を解決せず、残差を単なる接続作業と扱わないこと。

検証: checkpoint build / 公理監査は実行中。

## n267 — cycle oracle / `hmove` の長半径 branch

```text
obligation_cycleOracleOnPackedRun
└─ OracleReady.cycleOracleOn_of_readyLeaves
   ├─ searchReady                         ✓
   ├─ ChainReady                          ✓
   ├─ shiftPeriodMinimal_packed           ✓
   └─ hmove
      ├─ idle + missed DP                 ✓ move_of_idle_missed_packed
      └─ active chain
         ├─ chainAt → Sem                 ✓
         ├─ Sem → MoveMinimal h           ✓
         ├─ Rad ≤ 4*h                      ✓ move_of_activeBound
         └─ 4*h < Rad
            ├─ fallback period `2*d`       ✓ fallback_window_period
            ├─ least period `2*h`          ✓ MoveMinimal / TailMinimal
            ├─ Fine–Wilf + boundary break  ← TOP
            │  ├─ fallback_window_boundary ✓ written
            │  └─ galil_move_of_minimal_period_boundary ✓ written
            └─ packed RoundScan 接続
```

一律 `Rad ≤ 4*h` は post-shift round には強すぎるため、短半径 branch だけを既存
consumer で閉じる。長半径 branch は fallback move `d` が `h` 未満なら
`MoveMinimal`、`h` 以上なら period `2*d` と `2*h` の Fine–Wilf を使う。
短すぎる move は `2*h ∣ 2*d` を強制するが、fallback の境界記号を使うと古い周期が
不一致の一文字まで延長され、`RoundScan.pred` と実比較の mismatch に反する。
純粋周期補題は書き込み済み。次は Lean 修正後、packed `RoundScan` へ接続する。

## n265 — fallbackと全replayをoracle本体へ接続

残る公理は2本、未解消。`hfallback`の実行構成を証明し、残差を移動量の不等式`hmove`へ縮めた。
- `CanonicalFallbackInput.begin_at_mismatch`: finite packed prefixからコピー長・入力・着地MInvを構成。
- `CanonicalReplay.segment`: chainが途中で誕生する場合も含む全replayを構成。
- `packRunR_MWR_front`: replay中のfront上界でpackingを供給。従来版はこの系。
- `OracleReady.cycleOracleOn_of_readyLeaves`: 上記を実際に消費し、全体のfallback葉を閉じる。
単体Lean検査成功、追加定理の依存は標準3公理のみ。全体buildはユーザー指示で停止。oracle公理1本の証明を書き終えてから再開する。
n264全体buildは成功（`/tmp/pal-full-rightplace-20260919.log`, BUILD=0）。

## n264 — canonical fallback のコピー元を Scala の右ヘッドへ修正

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_cycleOracleOnPackedRun` | 未解消。canonical policy と fallback 葉のpinを修正したため義務の意味は変わる。これは以前の公理を証明したことではない。 |
| `obligation_localRealization` | 未解消。参照する canonical policy が同様に変わる。 |

- Scala正本 `scala/pal/src/main/scala/pal/ScaffoldGalil.scala:309` の `beginFallback()` は line 314 で **`walker.copyFrom(right)`** を実行する。旧canonical条件 `u.fpp.walker = u.walker` は、Leanでは保存される旧search cursorを選んでおり、このコピー元と違っていた。`prepareWindow()` の `walker.copyFrom(center)` との混同を訂正した。
- `GalilTickFair.rightPlace` は右ヘッドのfocus・left stack・gapを既存 `lettersOf` でdecodeする。`Canonical.fallbackPlace`、`canonical_of_scan_copy`、`OracleRun` と `OracleReady` のfallback葉を `u.fpp.walker = rightPlace u` に変更。
- `tick_scan_noRestart_unique` を「fallbackで保存されるselector」で一般化して証明の重複を回避。旧 `Fair` は過去の条件付き定理のためsearch cursorのpinを維持し、**Scalaそのものだという説明を撤回**。新canonical一意性はright-head selectorで証明済み。
- `fallbackAt_rightPlace` が新しいpinを満たす入口を構成する。`fallback_right_not_searchPin` は、コピー長の境界を満たす入口で新旧pinが一致しないことをLeanで証明する（標準公理のみ）。この反例をbootからの到達可能性やPAL公理全体の反証と取り違えない。
- `beginFallbackVM'` のコピー長境界は変更していない。抽象VMではsearchとFPPのwalkerを別フィールドで持つため、その全体モデルをScalaとの状態同一性だとは主張しない。

**検証状態: 修正後の一意性・新旧pinの不一致は単体Lean検査成功。全体buildと最終公理監査を再実行中。無条件PALは未完、残り2公理。**

## n263 — boot 起点の canonical prefix は探索下限ゼロ、oracle の周期葉へ接続

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_cycleOracleOnPackedRun` | 未解消。ただし運ぶ述語の起点を boot 到達済み `InvLPS` に限定したため、義務は以前より弱い。公理を証明した／減らしたわけではない。周期葉へは `lower = reset` を構成して渡す。 |
| `obligation_localRealization` | 未解消、変更なし。 |

- `CanonicalPeriod.tick_lower_zero` は restart を除く各 tick で下限ゼロを保存する。search/phase は保存、init/replayStart は reset。`trace_lower_zero` と `packed_lower_zero` で任意長の有限 prefix に持ち上げた。`preTrace_lower_zero` はその系。
- `noBelow_first_canonical` は **有限の boot 起点 packed prefix** と既存の幾何学的 `Entry`・DP `Result` から最初のshiftに必要な最小周期性を示す。`hlow` は下限ゼロから消える。完成済み `PreTrace` を前提にすると oracle の構成へ循環するので、prefix だけで証明した。
- `CloseoutCheckW.PackedFromBoot` を追加し、`ScanOnPackedRunFromInvLPS` の origin にその証拠を保持。boot constructor は既存の1 tickを使い、oracle の各着地は同じ起点を引き継ぐ。最終消費者の結論は変わらない。
- `OracleRun.cycleOracleOn_of_leaves` は originまでのprefixと比較点までのprefixを連結し、`packed_lower_zero` を **実際に使用**。`OracleReady` の `hshiftPeriodMinimal` は `s.lower = reset` を受け取れるようになった。
- 未解決: 現在の watch の周期と DP Result・ReadOrigin を結ぶ構成、繰り返しshiftへの最小性の運搬。さらに readiness、ChainReady、fallback/replay、具体的局所機械。下限ゼロだけでこれらが閉じるとは主張しない。

**検証状態: n263 のmodule build成功（`/tmp/pal-boot-oracle.log`, `BUILD=0`）、全体build成功（`/tmp/pal-full-boot-20260919.log`, `BUILD=0`）。無条件PALは未完、残り2公理。**

## n262 — 受理結果と状態一致を区別し、最終消費者を短縮

先輩の「fable のアプローチがミスっている可能性、2前提を難しく考えすぎているふし」
との指摘を受け、前提の内容から再確認した。

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_cycleOracleOnPackedRun` | 宣言・型とも変更なし、未解消。 |
| `obligation_localRealization` | 宣言・型とも変更なし、未解消。ただし「非決定的な全 trace との一致は不可能」という n260 の根拠は誤りだった。型が要求しているのは受理結果の一致で、状態列の一致ではない。 |

- `GalilLookRefined.reported_throttledLG'` は従来の ledger 証明を1入力・1 trace に切り出したもの。既存 `ledger_throttledLG'` はその系に置換し、証明を重複させていない。
- `CloseoutFinalFour.latch_iff_pal_of_preTrace` は `PreTraceB` と消費者が既に持つ `hNeed` から、**canonical 性なしに** `LatchTrue … ↔ w ∈ PAL` を証明する。旧 `PreTraceB` だけの全称前提が真だと主張するものではない。
- `given_preTraceIMW_on` はこの iff を実際に使い、入力ごとに1本の trace を取り出して `pal_in_peg_of_structured` へ直接接続する。全入力にわたる trace の `choose` と、消費されない `_H_run` のための `AbstractRun'` 構成を除去。最終定理の型と witness は維持。
- canonical な exact tracking は局所実現を証明する **一つの十分な方法** であり、受理結果だけの義務から必要性は導けない。n261 で指摘した無限 trace / finite prefix の差も、その exact-tracking 経路の接続課題であり、目標定理そのものの必須前提ではない。
- `CloseoutFinalW` と `PalInPegUnconditional` の「producer は原理的に無い」という説明を訂正。引き継ぎ文にも訂正を明記。

- 周期葉の監査: `result_least` は `lower` より大きい候補の最小性しか返さない。既存 `GalilNoBelowFirst.noBelow_first_of_result` は別途 `hlow`（`0 < δ ≤ lower` の周期排除）を要求する。引き継ぎの「DP result を運ぶだけ」はこの条件を省略している。canonical policy では restart が無いので boot から `lower = reset` を運ぶ簡略化の余地があるが、現行 oracle の起点は任意 `InvLPS` であり、そのままゼロと仮定してはならない。未証明の残差として記録する。

**検証状態: n262 の全体 build 成功（`/tmp/pal-full-latch-20260919.log`, `BUILD=0`）。独立した公理監査も成功（`/tmp/pal-axioms-20260919.log`, `BUILD=0`）。新規補題は標準公理のみ、`unconditional` には従来の2独自公理が残る。無条件 PAL は未完。**

## n261 — canonical tick の一意性と、切り詰められた局所 trace への接続

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_cycleOracleOnPackedRun` | 未解消。既存の4葉は変更していない。 |
| `obligation_localRealization` | 未解消。`tick_canonical_unique`、`canonical_trunc`、`realizes_canonical` を構成し、canonical な局所 successor と trace の successor の一致を証明した。具体的な局所 step、その物理不変量、word-independent な有限テープ符号化はこの定理の結論には含まれない。 |

- `GalilTickFair.tick_scan_noRestart_unique` に既存 scan 証明を共通化。`tick_fair_scan_unique` と新しい `tick_canonical_unique` が同じ核を使う。
- `CanonicalLocalRealizes.canonical_trunc` は実際の tick について任意の `truncS d` で canonical 性を保存する。単に canonical 性があると仮定し直してはいない。背景・一致比較では broken chain の保存、shift では watch/broken の矛盾、fallback では search の idle/grow の矛盾で restart を除く。
- `LocalRealizesScan.realizes_of_refined_tick_det` に既存の successor 同定証明を共通化。旧 `realizes_of_tick_det` は `Refinement := True` の系。新しい `realizes_canonical` は canonical truncation と一意性を使う系であり、未証明の `H_scanDet` を要求しない。ただし canonical な局所 tick を実際に作る `hLocal` は依然として必要。
- `Axioms.lean` に上記3定理の標準公理のみの guard を追加。`unconditional` の残り2公理の guard は維持。
- 引き継ぎ §3 の「一意性で閉じる」は successor の同定についてのみ確認できた。`LocalLatchRealize.pal_in_peg_of_local_core` は `L0` / `enc_tick` / `enc_feed` 等を引数としており、今回の証明から具体的 `LocalStep` が得られたわけではない。
- 接続時の量化範囲にも注意: `realizes_canonical` は既存 `Realizes` と同じく全 `k` の trace tick を受け取る。一方 `CanonTrace` / `PreTraceIMW` は最終報告点までの有限 prefix である。この差を埋める bounded tracking または適切な延長も、最終公理から本定理を利用する際に必要。
- oracle の `hfresh` については、`ReadyPacedS` の量化対象が全 `PacedL` リストであり、実機の比較間隔より広いことに注意（`CloseoutReadyStage.ReadyIface` の説明と `StageRunPhase` / `StageEntryBudget`）。**現行の `hfresh` の反証はしていない。**

**検証状態: n261 の全体 build 成功（`/tmp/pal-full-20260919-fixed.log`, `BUILD=0`）。新規3定理の標準公理 guard 成功。無条件 PAL は未完（残り2公理）。**

## n259 — `hchain` を「packed run の scan 状態で `ChainReady`」（`StepsIMW` 形）に切り直し

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_cycleOracleOnPackedRun` | 葉 `hchain` の切り直し。旧形は `InvLPS` 起点からの shaped run **全点**（copy／fallback 相の中も含む）で `ChainReady` を要求していた。新形は `InvLPS … c₀ r₀ → StepsIMW … k ⟨c₀,r₀⟩ y → y.ctl.mode = .scan → ChainReady y.vm.chain`——`BranchSupply.ChainVerifierSupplyAlongTrace`（trace の scan 点で `VerRep ∧ LagCan`、producer 済み）と同じ形。`scanBackground_run` は背景 tick の中間状態を `packRunR_MW_marksFree` で packed run に載せて葉に渡す（右ヘッド不動なので位置条件は自明）。葉は 4 のまま（`hfresh`／`hchain`／`hshiftPeriodMinimal`／`hfallback`） |
| `obligation_localRealization` | 変化なし（次: `∀ PreTraceB` を canonical trace に限定する切り直し） |

**状態: 全体 build 成功（`BUILD=0`）・標準公理のみ（3 本）・無条件 PAL は未完（残り 2 公理）。**

## n258 — `hfallback` の量化子を直し（着地 `u` は葉が選ぶ `∃`）、最終 witness の `q` を 1 に

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_cycleOracleOnPackedRun` | 葉 `hfallback` の切り直し。旧形は `scanCompare_cases` が `beginFallback_exists`（**空の place** `⟨[], false⟩` を選ぶ）で作った任意の着地 `u` を葉に渡し「そこから完走せよ」と要求していた（量化子が逆、GPT-6 の指摘）。新形は不一致の源（`c s vq z`、guard 立たず）から `∃ u, beginFallback s1 u ∧ ∃ c' s' kk r fb replay, …` を葉が返し、tick は oracle 側が `Tick.scan_fallback` で作る（`scanCompare_cases` の fallback 枝は `∀ u, beginFallback s1 u → Tick …` を返す）。本物の構成（`scan_fallback_cycle_All`／`fallback_restarted_soundNR`）は右ヘッドから decode した非空 place を自分で選ぶので、この形なら繋がる。葉は 4 のまま（`hfresh`／`hchain`／`hshiftPeriodMinimal`／`hfallback`） |
| `obligation_localRealization` | 変化なし |

`PalInPegUnconditional.unconditional` の witness を `0 0 0` → `0 1 0`（`q = 1`）に変更: fallback 構成の定理群は `0 < q` を要求するので `q = 0` では葉が原理的に埋まらなかった。`first = 0` は変えず。

**状態: 全体 build 成功（`BUILD=0`）・標準公理のみ（3 本）・無条件 PAL は未完（残り 2 公理）。**

## n257 — `hminv`（run 全点の `MInv`）を運ぶ述語の場に移し、残差を shift 入口の周期最小性 1 点（`hshiftPeriodMinimal`）に局所化

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_cycleOracleOnPackedRun` | producer `OracleReady.cycleOracleOn_of_readyLeaves` の葉は 4 のまま（`hfresh`／`hchain`／**`hshiftPeriodMinimal`**／`hfallback`）だが、`hminv`（`InvLPS` 起点からの shaped run **全点**で `MInv`）が消え、**この `hminv` は偽だった**（n253 でウチが書いた葉。run 全点には fallback 入口（copy 相）の着地も含まれ、そこでは中心が死んでいるので `MInv` は立たない。核は `CloseoutPackRun4.minv_false_at_mismatch`、しかも `CloseoutLPack5.MInvG` で一度直した穴の再発。葉自体を `False` に落とす定理は未構成なので「偽の疑いが濃い」と記録。GPT-6 の指摘（コウタ経由、2026-09-19）で確認した。同じ指摘の残り——`hfallback` の `u` が `∀`（`scanCompare_cases` が空 place を選ぶ）、最終 witness の `q = 0` vs fallback 構成の `0 < q`、`hchain` の run 全点量化——は n258 で直す）、代わりの葉は **状態局所**: shift 入口（guard 立ち・比較不一致の状態）で watch chain の周期 `periodLength wg` が span `Span w C (n − C)` の最小周期であること（`∀ p, 0 < p → p < 2·periodLength wg → ¬ HasPeriod … p`）。`MInv` 自体は `CloseoutCheckW.ScanOnPackedRunFromInvLPS` の場として運ぶ（boot は `InvLPS` の `Inv.minv`／`InvK.minv`、一致比較は `minv_match`＋`minv_afterBirth`（既存）、shift 出口は `leftmost_shift`（`GalilLiveCentreShift`）で `hdead`＝`not_live_of_mismatch`、`hlive`＝出口の `ScanInvariant`、`hmin`＝新しい葉、fallback は `hfallback` の結論に `MInv w c' s'` を足した） |
| `obligation_localRealization` | 変化なし（GPT-6 の指摘＝過剰量化の疑いを受けて、消費側からの逆算を並列で調査中。n174 の診断と同型） |

**状態: 全体 build 成功（`BUILD=0`）・標準公理のみ（3 本）・無条件 PAL は未完（残り 2 公理）。**

**何をしたか**

* `CloseoutCheckW.ScanOnPackedRunFromInvLPS` に `MInv w c r` を追加（`Refreshed` の直後）。`scanOnPackedRunFromInvLPS_of_invLPS` は `hI.1.1.1.1.1`（`Inv ∨ ∃ k, InvK`）の両分岐の `.minv` で埋める。
* `OracleRun`: `scanCycle_of_leaves`／`cycleOracleOn_of_leaves`／`cycleOracleOn_of_fourLeaves` から `hminv` を削除。比較状態の `MInv` は `minv_same`（`scanCycle_of_leaves` の不一致分岐の結論に `t.replay = s.replay` を追加）で作り、`hshift`／`hfallback` の前提に `MInv w c s`、結論に `MInv w c' s'` を追加。`hland` は着地の `MInv` を受け取り運ぶ述語に詰める。`shiftLeaf` は `hminvS`（入口の `MInv`）と `hperiodMin` を取り、出口で `leftmost_shift` により `MInv` を返す。
* `OracleReady.cycleOracleOn_of_readyLeaves`: `hminv` → `hshiftPeriodMinimal`（統一した葉文）。
* 並列化を解禁（コウタ 2026-09-19「サブエージェント解禁していいけど、コミュニケーションコストがでかそうなのは任せない」）: 読み取り専用の地図作り 4 本（`hfresh`／`hchain`／`hfallback`／`localRealization`+`Fair`）を workflow で同時実行。lean プロセスは同時 2 本まで、`lake build` は 1 本。

**`hshiftPeriodMinimal` の帰着先**: 周期最小性は found 時の DP decode（`GalilMinimalPeriod.result_least`／`GalilSearchResult.search_result_at_tick`）が chain 誕生時に与える情報で、watch 相を通じて period テープに保存される。`hchain` の copy 相（誕生時の `∃ n, CopyInv`）と同じ起点データなので、両者は「誕生時の decode を chain の一生で運ぶ不変量」1 本にまとめるのが筋。

## n256 — 運ぶ述語に restart 無しの run（`ShapedRun.ShapedSteps`）を足し、`hrestart`／`hreplayStart` の 2 葉を消した

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_cycleOracleOnPackedRun` | producer `OracleReady.cycleOracleOn_of_readyLeaves` の葉が 6 → **4**（`hfresh`／`hchain`／`hminv`／`hfallback`）。`hrestart`（restart 着地の datum）と `hreplayStart`（replayStart 着地の datum）は**消えた**: oracle 自身の run は restart を出さず（broken chain は broken のまま tick する）、replayStart は fallback の着地 `Restarted raw t 0 reset` にしか無いので、運ぶ述語 `CloseoutCheckW.ScanOnPackedRunFromInvLPS` に「`InvLPS` 起点からの shaped run」を足し、readiness datum を `ReadyTransport.readyField3_of_invLPS_shaped`（`hfresh` だけから）で運ぶ |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`）・標準公理のみ（3 本）・無条件 PAL は未完（残り 2 公理）。**

**何をしたか**

* `ShapedRun.lean`（新規 module、n255 の末尾で `OracleReady` から分離）: `ShapedSteps`（scan-mode tick は `restartVM` でない、`replayStart` tick は `Restarted w _ 0 reset ∧ scan ∧ clock = 2048` に着地する run）、`restartVM_shape`／`chainTick_broken`／`chainAt_broken`／`not_restartVM_background`／`not_restartVM_compare`／`watchSegE_shaped`、今回追加の `not_restartVM_of_chainAt`（chain tick が broken を残さないなら restart でない）／`not_restartVM_of_chainAt_target`（着地の chain が chain tick の結果なら restart でない）／`not_restartVM_of_radius`（radius が変われば restart でない）。
* `ReadyTransport.lean`（新規）: `readyField3_alongShaped`（shaped run に沿った `ReadyFieldP3` の transport、`hfresh` だけ）と `readyField3_of_invLPS_shaped`（`InvLPS` 起点の `ReplayStage` が記録する fresh restart の datum を `WatchSegE` 区間（shaped）で起点まで運び、そこから shaped run 全点へ）。
* `CloseoutCheckW.ScanOnPackedRunFromInvLPS` に `∃ j', ShapedSteps … j' ⟨c₀, r₀⟩ ⟨c, r⟩` を追加（boot の着地は長さ 0）。
* `OracleRun`: `scanBackground_run` が背景 tick の shaped run も返す（`not_restartVM_background`）；`scanCycle_of_leaves`／`cycleOracleOn_of_leaves` の `hready`／`hchain`／`hminv` は **shaped run 上**の量化に弱めた；一致比較の着地は `not_restartVM_of_chainAt_target`、shift 入口は guard の `.watch` から `not_restartVM_of_chainAt`、fallback 入口は radius の `inc` から `not_restartVM_of_radius`；`shiftUnits_S`／`shiftLeaf`／`hshift`／`hfallback` の結論に相の shaped run を追加（shift 相は mode が shift なので条件は空虚）。
* `OracleReady`: `searchReady_of_invLPS_shaped (hfresh) (hI₀) (hsh) (hm)` で `hready` を放電。`readyField3_alongRun`／`readyField3_of_invLPS_steps`／`searchReady_of_invLPS_steps` は参照ゼロになったので削除。

**残り 4 葉の帰着先**（n255 の表から `hrestart`／`hreplayStart` を除いたもの）: `hfresh` は DP の較正（`stageDebt`／`dpDemandS`、最初の stage は slack 0 で `dpDemand 0 8 = 1 ≤ 2`）；`hchain` copy 相と `hminv` shift 相は found 時の decode（`GalilSearchResult.search_result_at_tick`／`later_stage_found_result`）；`hfallback` は `fallback_restarted_soundNR` の側条件（`ShiftIdle`／`Canonical length`／`heven`／`0 < q`／`first ≠ 7, 8`）＋ replay 区間の構成（既存 `replay_segment_construct` は偽の `hpres`／`hquiet` を取るので、`ReadyFieldP3` 版に切り直す）。着地に shaped run が要るのは replayStart tick 1 本だけで、その着地は `fallback_restarted_All` の `Restarted raw t 0 reset`。

## n255 — `hready` を原子の葉 3 本に分解（`OracleReady.searchReady_of_invLPS_steps`）、PR #72 を main に merge

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_cycleOracleOnPackedRun` | 葉 `hready`（`InvLPS` 起点からの run の chain idle な scan 状態で `SearchReady`）を定理化: `OracleReady.searchReady_of_invLPS_steps (hfresh) (hrestart) (hreplayStart)`。乗り物は `CloseoutPreload39.ReadyFieldP3 n`（今の readiness ＋ paced な未来全部の readiness）で、`readyField3_tick` が restart／replayStart の着地以外の全 tick で運ぶ（`BigPack2M''` 仮説は証明が `aux.front.notInit` しか使っていなかったので `mode ≠ init` に一般化）。起点の datum は `InvLPS.2 : ReplayStage`（fresh restart からの `WatchSegE` 履歴）で `hfresh` を transport。残る原子: `hfresh`（`Restarted w r Rad last ∧ StageEntry Rad last ∧ mode scan ∧ clock 2048 → ∃ n, ReadyFieldP3 n ⟨c, r⟩`＝具体 DP の stage 予算に対する較正）、`hrestart`／`hreplayStart`（fresh 起点から到達する restart／replayStart tick の着地の datum ＝ 着地が `Restarted ∧ StageEntry` であること ＋ `hfresh`）。`OracleReady.cycleOracleOn_of_readyLeaves (hP) (h4) (hfresh) (hrestart) (hreplayStart) (hchain) (hminv) (hfallback)` が oracle の producer（標準公理のみ）。`OracleRun` の `hready` は `y.ctl.mode = scan` に限定（使う場所は全部 scan 状態）。既存塔の判定: `readyField3_entry_of_datum` は `NoReturn`（一般には偽）を取るので使えず、`postRunC_galil_of_boot`（Preload36）の `StageChain` 経路は boot datum と `16 ≤ mw` が残差。PR #72（n245〜n254）を main に merge（`433ec7e`） |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`）・標準公理のみ（3 本）・無条件 PAL は未完（残り 2 公理）。**

**残り 6 葉の帰着先（n255 追記）**: `hchain` の copy 相は誕生時の `∃ n, CopyInv answer reset walker (start cc) h`（`AnswerAheadDecode.copyInv_of_found`: `denote answer = output h`／`head answer = h`／`focus = 8`／`Candidate (stream p take (span+1)) lower h`）を要り、`hminv` の shift 相は `leftmost_shift` の周期最小性（`∀ g < h, ¬Candidate`）を要る。どちらも **found 時の DP 出力の decode**で、既存: `GalilSearchResult.search_result_at_tick (hP : Decodes P) … (hR : Restarted raw r Rad last) (hstage : 3·Rad ≤ 5·k) (hseg : WatchSegE … c0 r cF sF) (hsF : chain idle) (hcF : clock 1) (hq : searchEffect P true sF vq) (hfound) : (∃ k h, Result (stream take (8·max k 1+1)) k 0 (denote vq.dp.config) ∧ pc = 346 ∧ pos 11 = h ∧ Candidate … h ∧ (∀ g < h, ¬Candidate …) ∧ sF.search.mode = run) ∨ (第 1 段で run を抜けた)`（第 1 段）、後段は `search_later_stage'`／`later_stage_found_result`／`laterStage_dpEntry`。つまり `hchain`／`hminv` は「fresh restart からの chain idle 区間の found」＝`hfresh` と同じ起点データ（`Restarted ∧ StageEntry`＋`ReplayStage` の履歴）で決まる。運び方: `WindowInv.copy` に `∃ n, CopyInv` を足し、`windowInv_start`（誕生）で `copyInv_of_found` を使う——その入力（`Result`）を `windowRunPack_tick` 経由で `packRunR_MW_marksFree` に thread する（found 比較の decode は run 形で供給）。`hfallback` の replay 区間は `hready` と同じ datum で背景 tick が出る。

## n254 — shift 相の葉を放電（`OracleRun.shiftLeaf`）、新 oracle は run 形の葉 4 本に

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_cycleOracleOnPackedRun` | `OracleRun.cycleOracleOn_of_fourLeaves (hP) (h4) (hready) (hchain) (hminv) (hfallback)`（標準公理のみ）。shift 相の葉は `shiftLeaf` で定理化: 比較状態の pack から `four_of_guard`（4h ≤ 半径）、入口状態の pack の窓（`periodLength_of_coreP`＋`periodLength_consume`、`Coupled'.block`）から `0 < h`、`GalilShiftPack.shiftHeads_of_scan`＋`shift_heads_counters`＋`shift_run_chain` で chain shift run、`shiftUnits_S`（`shift_run_lift` を 1 単位ずつ `tick_pull`／`shift_transfer`／`tick_S_of_tick` で `galilFrameS` へ、`StepsAll (SoundScanNR)`）、出口は `shiftExit_S`（`shift_done` を直接構成、`refresh` を露出）、着地の `SoundScanNR` は remaining 尽きた shift 状態の pack の `LPackM2.shiftGeom` → `shiftGeom_exit` → `outputRel_of_refresh`。葉 `hshift`／`hfallback` は「比較データ形」（`searchEffect`／`chainAt`／guard／entry／tick を明示、prefix は `StepsIMW`）に切り直し（tick の `cases` を避ける）。残る葉: `hready`（chain idle での `SearchReady`）／`hchain`（`ChainReady`）／`hminv`（`MInv`）／`hfallback`（fallback＋replay） |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`）・標準公理のみ（3 本）・無条件 PAL は未完（残り 2 公理）。**

**次（n254 の見立て）**: 残り 4 葉のうち `hready`（chain idle での `SearchReady`）と `hchain` の copy 相（`∃ n, CopyInv`、誕生時の `copyInv_of_found` は found 時の DP 出力の decode 事実 `hDenote`／`hHead`／`hFocus`／`Candidate` を要る）は**同じ探索側の run 不変量**に帰着する: `InvLPS` 起点（`search = begin last radius`、`searchReady_of_begin`）から compare 1 回ごとに debt が 1 減り（`searchReady_run_true_iff`）、DP は予算内に終わる（`dp_quanta_safe`／`calibrated_quanta_safe`、`StageEntry : 3·Rad ≤ 5·last`）——これを run に沿って持ち回る `RdPaced` の producer `PostRun`／`RestartS2` を書くのが本丸。`hminv` の shift 相は `leftmost_shift`（`¬Live`／`Live (C+h)`／周期の最小性 `GalilMinimalPeriod.result_least`）、`hfallback` は `fallback_restarted_soundNR`（側条件 `ShiftIdle`／`Canonical length`／`heven`／`first ≠ 7,8`／`0 < q`）＋ replay 区間の新構成（既存の replay 構成子は偽の `hpres`／`hquiet` を取る）。

**`hready` の既存塔（n254 追記）**: `CloseoutPreload40.HpresAt P c s := ∀ a v, chain idle → (a → clock ≤ 1) → searchEffect P a s v → SearchReady v`（pointwise の保存則）。`CloseoutPreload41.hpresAt_along_soundScanNR (hr : BigResid6) (het : H_extraTick3) (hme : H_marksEntry') (hIC : InvLPC) (hjx) (hbx : BigPack2M'') (hf : ReadyFieldP4 (n+1) x) (hentry) (hentry') : HpresRepAt x`（`SoundScanNR` run の各 scan 点で `HpresAt`）。起点の `SearchReady`（`Inv.search`／`searchReady_restarted`）と `HpresAt` の各点保存で `hready` が出る。塔の入力: `ReadyFieldP4`（fuel 付き readiness datum、boot は Preload39）、`hentry`／`hentry'`（restart／replayStart 直後の `ReadyFieldP3`）、`BigResid6`（`bigResid6_of_lpackM2`）、`H_extraTick3`（`h_extraTick3_of_h_extraTick4`）、`H_marksEntry'`（`h_marksEntry'_of_layout`）。`.run` 入口の帰納は `CloseoutPreload36.postRunC_galil_of_boot (hres : RestartOnBroken P) (hsup : ScanSupplyInv) (hboot : EntryDatum) (hch : StageChain)`（`StageChain` に沿った `DpSafeStage`）。**次はこの塔を新 oracle の `hready`（`InvLPS` 起点・`Steps` 各点・chain idle）に合わせて 1 本の定理に束ねる。**

**`hready` の塔の入口条件（n254 追記 2）**: `CloseoutPreload39.readyField3_entry_of_datum (hclk) (hR : Restarted) (hSE : StageEntry) (hcl : CentreLongRun) (hnr : NoReturn) (hdep : EntryDepthG) (hD) : ReadyFieldP3 (dpEntryG …) ⟨c, r⟩` と `readyField3_along_run (hr : StepsAll (BigPack2M'') m x y) (hf : ReadyFieldP3 n x) (hentry) (hentry') : ReadyFieldP3 n y`、`readyField3_to_ready`。ただし `NoReturn u`（`ReachL` の非 run 状態は全部 `ReachP`）は Preload8 の記述どおり一般には偽で、producer `noReturn_of_avoidRun` は「`.run` に一度も入らない」退化ケースのみ。**使う経路は Preload36 `postRunC_galil_of_boot (hres : RestartOnBroken P) (hsup : ScanSupplyInv F 2048 I) (hp : I p) (hclk) (hboot : EntryDatum k mw pre p p0) (hmw : 16 ≤ mw) (hch : StageChain k mw mw' evs tail p0 pn) (hpaced) : EntryDatum … ∧ 16 ≤ mw' ∧ (… ∨ DpSafeStage (search pn) tail)`**（`RestartOnBroken` は `CloseoutPreload33.restartOnBroken_sharedC` で証明済み）と Preload40／41（`ReadyFieldP4`、`hpresAt_along_soundScanNR`）。束ね方: `InvLPS` 起点を `EntryDatum` に読み替え（`Restarted` の `begin last radius`）、oracle が構成する run を `StageChain` に分解して各 `.run` 入口の `DpSafeStage` を得、`ReadyFieldP3/4` の各点保存で chain idle の `SearchReady` を出す。`16 ≤ mw`（窓が小さい restart）と `ScanSupplyInv`／`I` が新しい側条件の候補。

## n253 — 新 oracle の一致分岐を証明（`OracleRun.scanCycle_of_leaves`、run 形の葉 3 本のみ）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_cycleOracleOnPackedRun` | 一致分岐が閉じた: `scanCycle_of_leaves (hP : Decodes) (h4 : first ≠ 4) (hm1) (hmle) (hI : ScanOnPackedRunFromInvLPS w c s) (hp : right ≤ 2m−1) (hready) (hchain) (hminv) : CycleOutOn … w m c s ∨ (right < 2m−1 ∧ ∃ t, StepsAll (SoundScanNR) (clock−1) ⟨c,s⟩ ⟨{c with clock := 1}, t⟩ ∧ heads 不変 ∧ 不一致)`。報告点にいる状態はそれ自身が報告（`Refreshed` は運ぶ述語が持つ）、下にいれば `scanBackground_run`（背景 tick）→ `scanCompare_cases`（比較）で、一致なら右 +1 の同形状態（`packRunR_MW_marksFree` で pack、`minv_match`／`minv_afterBirth` で `MInv`、1 `Piece` の `CostedRun`、`mu` 減少）か報告。残る入力は run 形の葉 3 本: `hready`（chain idle での `SearchReady`）、`hchain`（`ChainReady`）、`hminv`（`MInv`）——いずれも「`InvLPS` 起点からの `Steps` の各点」で量化（状態全体への過剰量化はしていない）。不一致分岐（shift 相／fallback＋replay）は次 |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`）・標準公理のみ（3 本）・無条件 PAL は未完（残り 2 公理）。**

### n253 addendum — oracle 全体が run 形の葉 5 本に還元された（`OracleRun.cycleOracleOn_of_leaves`）

`cycleOracleOn_of_leaves (hP : Decodes) (h4 : first ≠ 4) (hready) (hchain) (hminv) (hshift) (hfallback) : CycleOracleOn … (ScanOnPackedRunFromInvLPS …) w`（標準公理のみ）。葉はすべて「`InvLPS` 起点 `⟨c₀,r₀⟩` から `Steps k` で到達する状態」で量化:
1. `hready`: chain idle な状態で `SearchReady (searchLens.get vm)`（chain 生存中は不要）。
2. `hchain`: `ChainReady chain`（idle／broken 自明、copy は `CopyInv`、back は `canRight ver`＋`OnBlock`、watch は `chainReady_watch_of_watchWindow`）。
3. `hminv`: `MInv w ctl vm`（背景 `minv_same`、一致 `minv_match`＋`minv_afterBirth`、shift は `leftmost_shift`、fallback は `minv_after_fallback`）。
4. `hshift`: clock 1 の ScanNR 状態からの shift 入口 tick の先から、`StepsAll (SoundScanNR) n` で refresh 済み ScanNR 着地へ。右ヘッドは比較後の位置（＝元 +1）、中心は真に右、`n ≤ adv + 1`（`ShiftEv.ticks_le`）。部品: `GalilScaffoldTopShiftCycle.scan_shift_cycle`（`ChainShiftRun` から shift 相全体を構成、`galilFrame` の Steps → `tick_S_of_tick` で `galilFrameS`）、`shift_run_chain`、着地の `SoundScanNR` は shift_done 直前の pack（`packRunR_MW_marksFree` を非 scan 終端に適用）の `LPackM2.shiftGeom` → `shiftGeom_exit` → `outputRel_of_refresh`。
5. `hfallback`: copy 入口 tick の先から `fb + replay` tick で refresh 済み ScanNR 着地へ。右ヘッドは元 +1、中心は `+ (kk + 1 − r)`（`r ≤ kk`）、`fb ≤ 12704(kk+1−r)+4012`、`replay ≤ 8·2048·(kk+1−r)`（`FallbackEv`）。部品: `fallback_restarted_soundNR`（`Restarted 0 reset` まで `StepsAll (SoundScanNR)`）＋ replay 区間の新構成（既存 `replay_segment_construct`／`match_round` は偽の `hpres`／`hquiet` を取るので使えない。run 形の `hready` から書き直す）。

背景 tick・比較・pack・`CostedRun`・`mu`・報告点は全部 `scanCycle_of_leaves`／`cycleOracleOn_of_leaves` の中で済んでいる。公理 `obligation_cycleOracleOnPackedRun` は 5 葉が定理になった時点で消える（葉を公理に割らない: 本数を増やさない）。

## n252 — `obligation_cycleOracle`（`CycleOracleMC3`）を run 形 `obligation_cycleOracleOnPackedRun` に切り直し（旧形は着地に chain idle を要求しており偽の疑いが濃い）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_cycleOracleOnPackedRun`（新） | 旧 `obligation_cycleOracle`（`CycleOracleMC3`）と差し替え。`CycleOutMC3` の報告分岐は `m < |w| → 次の報告点 `2(m+1)−1` までに `InvLPS` に着地` を要求し、`InvLPS` は `Restarted`／`InvScan.chainIdle` により **chain が idle**。Scala 正本では chain は fallback（`ScaffoldGalil.scala:320`）か broken からの restart（`:233`）でしか idle に戻らず、`matched()` は Watch のまま `consume()` を続ける（`ScaffoldChain.scala:161`）。よって `aaaa…` のように chain が生き続ける入力では旧形は満たせない。**機械検査済みの反証は無い**（`REFUTED` とは書かない）。新形は `CloseoutCheckW.CycleOracleOn (ScanOnPackedRunFromInvLPS)`: 「`InvLPS` 起点からの packed run 上の非 replay な scan 状態（`ScanNR ∧ ∃ 起点 j, InvLPS 起点 ∧ StepsIMW j 起点 x`）から、報告点 `2m−1` に達するか、`mu` を減らして同じ形の状態に着地する」。消費側の checkpoint 再帰 `checkpoints_costIMW_upto1` は運ぶ述語を `hor` に渡して受け取るだけだったので、`CloseoutCheckW` を述語 `I` で一般化（`ReachAtOn`／`CycleOutOn`／`CycleOracleOn`／`reachOn_fuel`／`reachOn_from`／`checkpoints_costOn_upto1`／`H_bootOn`／`preTraceOn_exists`）し、旧名（`ReachAtIMW`…`preTraceIMW_exists`）は `InvLPS` instance として残した（下流の旧系統は無変更）。新 trace 生成は `preTraceOnPackedRun_exists (hboot : H_bootIMW) (hor)`（boot 側の義務は増えない: `scanOnPackedRunFromInvLPS_of_invLPS` が `j = 0` で出す）。`CloseoutFinalFour.given_preTraceIMW`（trace 生成を抽象化した最上位）を切り出し、`given_needBound` はその系。`given_scanLandingObligations` は `hor` を新形で取り `h4` を落とした（`packRunR_MW_marksFree` は oracle の証明側へ移る） |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`）・標準公理のみ（3 本）・無条件 PAL は未完（残り 2 公理）。**

### 新 oracle の証明計画（必要な部品だけ）

1 回の oracle 呼び出しは「clock 分の背景 tick ＋ 比較 1 回（＋ shift 相／fallback＋replay）」で `mu` を 1 以上減らす（比較で右ヘッド +1、shift／fallback で中心が右へ）。chain の死は不要。
- run の存在: `OracleRun.scan_tick_exists_PofC`（`SearchReady` ＋ `ChainReady`）／`phase_tick_exists_PofC`（`PhaseEnabled`）。`ChainReady` は `IPackMW.win`（`WindowRunPack`）から（watch は `chainReady_watch_of_watchWindow`）。
- pack: run が出来たら `packRunR_MW_marksFree` で `StepsIMW`（着地は非 replay かつ右ヘッド ≤ 2M−1 が条件）。
- `SoundScanNR`: 背景は `outputRel_background`、比較は `outputRel_of_refresh`＋`scanInvariant_matched`、fallback は `fallback_restarted_soundNR`。
- 報告点: `ReportPointAt` の `scanInv` は `LPackM.scanGeom`、`centre : MInv` は別途運ぶ（`minv_same`／`minv_match`／`minv_afterBirth`／`leftmost_shift`／`minv_after_fallback`）。`Refreshed` は比較 tick の `ho`。
- `CostedRun`: 1 比較 = 1 `Piece`（`wait := clock−1`, `cmp := true`, `place := 着地の右ヘッド`）。
- 未解決の入力: chain idle 区間での `SearchReady`（`RdPaced` の producer `PostRun`／`RestartS2` は未証明）。

### 新 oracle の証明の分解（n252 addendum、必要な部品の所在）

1 呼び出し = 「背景 tick × (clock−1) → 比較 1 回 → (shift 相 ｜ fallback＋replay)」。各部品:
1. **chain 側の tick 存在** `ChainReady`: idle／broken は自明、copy は `∃ n, CopyInv`（誕生 `AnswerAheadDecode.copyInv_of_found`、1 歩 `GalilBranchInvariants.copyInv_step`）、back は `WindowInv.back`（`VerAt`／`LagAt` → `canRight ver`）＋ `OnBlock`（`BlockInv`、`blockInv_steps` で run 全点）、watch は `OracleRun.chainReady_watch_of_watchWindow`。
2. **search 側の tick 存在** `SearchReady`（chain idle のときだけ必要、chain 生存中は `searchEffect` が恒等）: `RdPaced` の閉包 `readyClosure_S2 (hpost : PostRun) (hS : RestartS2)` の **producer が無い**（`hpres` の沼、DP のタイミング層の配線）。**これが oracle 証明の唯一の未証明入力**。構成子には run 形 `hready : ∀ k y, StepsAll … k x y → y.vm.chain = idle → SearchReady (searchLens.get y.vm)` として渡す。
3. **run の組み立て**: 背景は `GalilScaffoldTopProgressS.backgroundS_exists` ＋ `Tick.scan_count`（`backgroundS_fields` で heads／center／replay 不変、`outputRel_background` で `SoundScanNR`）、比較は `compare_progress_gen` 相当を 3 択（match／`scan_shift`／`scan_fallback`）に開いて構成、phase は `OracleRun.phase_tick_exists_PofC`（`ShiftEnabled` は `LPackM2.shiftGeom`）。
4. **pack**: 出来た `StepsAll (SoundScanNR)` に `packRunR_MW_marksFree`（終端は ScanNR かつ右 ≤ 2m−1）。
5. **`MInv`**（`ReportPointAt.centre`）: 背景 `minv_same`、一致 `minv_match`、誕生 `minv_afterBirth`、shift `leftmost_shift`、fallback `minv_after_fallback`。
6. **`CostedRun`**: 比較 1 回 = `Piece`（`wait := clock−1`, `cmp := true`, `place := 着地の右ヘッド`）; shift は `ShiftEv`、fallback は `FallbackEv`。
7. **`mu` 減少**: 一致で右 +1、shift で中心 +h、fallback で中心が右へ（`leftmost_after_fallback`）。

次に書く定理（`OracleRun`）: `scanBackground_run` — ScanNR 状態から `clock−1` 個の背景 tick の `StepsAll (SoundScanNR)` を構成し、heads／center／replay／remaining が不変で clock が 1 になることを返す（`hready`／`hchain` は run 形の仮説）。

## n251 — `ChainReady` から `Good` を外した（正 lag の watch は必ず tick できる）／run 構成の API 確定

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_cycleOracle` | run の存在が chain 側で無条件になった: `GalilTickFun.ChainReady (.watch w)` の場を `positive lag → canRight verifier ∧ ∃ a, symbol focus = some a`（読みが当たれば `Internal.take`、外れれば `watchBreak`）に緩め、`.broken` は `True`（`brokenIdle`／`brokenMatched` で常に進む）。`GalilBranchInvariants.chainStep_watch_total`／`chainTick_watch_total` も同じ仮説に。`Good` を持つ producer は `readyWatch_of_good` で変換（`chainReady_of_blockInv`／`chainReady_of_chainOk`）。**run 構成の API**: scan は `GalilTickFun.scan_tick_gen (P) … hshift hfall hsearch hchain`（frame 汎用）、init／restart／replayStart は `*_tick_gen`、phase モード（shift／copy／fpp／home／markEnd／choose／rewind）は `GalilTickFun3.phase_tick_gen (P) (hx : PhaseEnabled q first x)`——全部 `P := PofC …` で使える。`tick_exists`／`tick_exists_R`／`tick_exists_P`／`runFun_steps` は `sharedFun`（fallback 先を `place s` に固定した frame）用なので `CycleOracleMC3`（frame `PofC`＝`sharedC`、fallback は `beginFallbackVM'`）には直接使えない。`PofC` 側の `hfall` は証人 `place s` と `(stream (place s)).length ≤ position right`（`Decodes`＋`CentreRep` から）で出す |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`）・標準公理のみ（3 本）・無条件 PAL は未完（残り 2 公理）。**

### `Enabled`（scan）の各場の供給元

| 場 | 供給元 |
|---|---|
| `1 ≤ clock` | `Bounded`／tick の構成子（clock は `delay` から減る） |
| `replaying = false` | `ScanNR`（replay 中は `tick_exists_R` の `ReplayEnabled`: 左右の読みが一致） |
| `∀ a, ∃ v, searchEffect P a s v` | `GalilBranchInvariants2.searchEffect_exists`（`SearchReady`）／`GalilOracleLeaves2.hsearch_C` |
| `ChainReady s.chain` | `WindowRunPack.window`（`WindowInv`）: copy は `CopyInv`、back は `OnBlock`＋`canRight ver`、watch は `LagAt`（正 lag ⇒ `position ver < position right` ⇒ `canRight ver`、`canRight_of_bound`）＋`symbol_of_coreP`（bounce の添字は常に `some`）＋`WatchBlock`＝`OnBlock` |

### 次

`FoundExitLPS`（`CloseoutWatchRound31.cycleOutMC3_of_foundExitLPS` の入力）を `WindowRunPack` の上で構成する:
found tick（`CloseoutFoundRoute1.found_first_tick` の形）→ 決定的 run（上の API）→ 着地の分類（`scan_shift`：`shiftPal_of_windowRunPack`／`scan_fallback`／`restart`）→ `Inv`（`restarted`／`fallback_restarted_All`）。停止性は右ヘッド位置（各比較で +1、上限 `2m−1`）と clock。

### 実装（n251 の続き）

`PalPeg/OracleRun.lean`（登録済み・標準公理のみ）: `scan_tick_exists_PofC (c s) (hm : scan) (hclk : 1 ≤ clock) (hr : replaying = false) (hsearch : SearchReady (searchLens.get s)) (hready : ChainReady s.chain) : ∃ st', Tick (galilFrameS (PofC …) q first) 2048 ⟨c, s⟩ st'`（`scan_tick_gen` ＋ `beginShift_exists`／`beginFallback_exists`／`searchEffect_exists`／`chainAt_exists`）と `phase_tick_exists_PofC (hx : PhaseEnabled q first x)`。copy 相の `ChainReady.copy`（`∃ n, CopyInv t h p v n`＝DP 答えテープの残り `n` と place の残り `n`）は誕生時に `startShape'_of_decodes`（`AnswerAhead`／`PlaceAhead`）から。
`OracleRun.chainReady_watch_of_watchWindow (hW : WatchWindow raw cen₀ (position r) cc b xs (.watch w)) (hrep) (hpres) (hcan : canRight r) : ChainReady (.watch w)`: `LagAt` で verifier は右ヘッドの手前、`CoreP` で表現＋`OnBlock`、`symbol_of_coreP`＋`bounce_length` で焦点記号は常に `some`。これで `WindowRunPack` の watch 状態は右ヘッドが動ける限り `scan_tick_exists_PofC` の `hready` を満たす。

### found 経路の run 構成（設計、n251 確定版）

found tick 後の chain の一生を `PofC` frame で構成する。各 tick の存在は `scan_tick_exists_PofC`（scan）／`phase_tick_exists_PofC`（phase）。
1. **watch 相**（copy／back は `GalilPrepConstruct.prep_segment_construct` が明示的に構成する）: 不変量は `WindowRunPack`（`windowRunPack_tick`、源に `LPackM`／`LPackM2`／`AuxPack`）＋ `SearchReady`（chain 生存中は `searchEffect` が探索を進めないので不変、`readyPacedS_effect_*` の `hidle` 参照）。`ChainReady` は `chainReady_watch_of_watchWindow`（右ヘッドの `canRight` が要る＝報告点 `2m−1` の手前）。
2. **終端の分類**（比較 tick、clock 1）: 一致 → 続行（右ヘッド +1、`position right ≤ 2m−1` で停止性）；不一致＋guard → `scan_shift`（`ShiftEnabled` は `LPackM2.shiftGeom` から、shift 後は scan に戻り `WindowRunPack` 継続）；不一致＋¬guard → `fallback_restarted_All`（`hg : ¬ shiftGuardVM (afterMismatch …)`、`heven`＝DP 窓長の偶数性、`hi : ShiftIdle`）が restart 直後の `Restarted raw t 0 reset` まで run を作る；break（`brokenMatched`／`breaks`）→ lag ゼロなら `restart` tick で `Restarted`、正 lag なら chain は死んだまま次の不一致で fallback。
3. **着地**: `Restarted` ＋ `SpanRep` ＋ `CopyPack` → `invLPC_of_landed` → `InvLPS`（`replayStage_of_inv`）→ `cycleOutMC3_of_centre`（`mu` は辞書式: 中心前進 or 同中心で右ヘッド前進）。報告点 `2m−1` に達したら `ReachAtC3`。

### 次に書く定理（正確な文、n251）

`GalilRoundConstruct.scan_half` は継続 round 用（`SInv`: lag ゼロ、`hmid` で round 内の一致が予測される）。
found 直後の**新鮮 watch**（`prep_segment_construct` の出口: lag = `inc radius`、追いつき中）には使えないので、
`OracleRun` に新鮮 watch の segment 構成子を書く:
```
theorem freshWatch_segment (centre place entry q first) (raw) :
  ∀ (fuel : ℕ) (c : Control) (s : GalilVM),
    FreshInv raw c s →                       -- scan ∧ ¬replaying ∧ 1 ≤ clock ≤ 2048 ∧ BigPack2MG7W'' ⟨c,s⟩
                                             --   （IPackMW.win で WindowRunPack、chain は watch か broken）∧ SearchReady (searchLens.get s)
    (2 * raw.length - position s.right) * 2049 + c.clock ≤ fuel →
    ∃ (n : ℕ) (c1 : Control) (s1 : GalilVM),
      ScanSeg (PofC centre place entry raw) q first 2048 n c s c1 s1 ∧ FreshInv raw c1 s1 ∧
      s1.center = s.center ∧
      (¬ canRight s1.right ∨ LastLetterEnd c1 s1 ∨
        (c1.clock = 1 ∧ canRight s1.right ∧ read (left s1.left) ≠ read (right s1.right)))
```
中身: 背景 tick は `scan_tick_exists_PofC`（`hready` は `chainReady_watch_of_watchWindow`、broken は `True`）で存在し
`FreshInv` は `bigPack2MG7W''_tick_M`＋`windowRunPack_tick`（`hSP` は `shiftPal_of_windowRunPack`）で保存、
`SearchReady` は chain 生存中は不変。一致比較は segment に含めて続行（右ヘッド +1 で fuel 減少）。
終端 3 択のあと: 不一致∧`shiftGuardVM (afterMismatch …)` → `scan_shift`（`ShiftEnabled` は `LPackM2.shiftGeom`）、
不一致∧¬guard → `fallback_restarted_All`、`¬canRight` → 報告点。

## n250 — モデル欠陥 `M-watchBreak` を修正（`ChainStep.watchBreak`／`ChainMatched.brokenMatched`）、全体 build 緑

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_cycleOracle` | **証明可能になった**（証明はこれから）。n249 のとおり `CycleOutMC3` は run の存在を主張し、正 lag の watch が予測を外す状態に Lean の `ChainStep` は後続を持たなかった（`ChainStepGap`、機械検査済み）。`GalilScaffoldTopChainVM` に `WatchBreak w := positive lag ∧ canRight ver ∧ ∃ a, symbol focus = some a ∧ read (right ver) ≠ some a` と `ChainStep.watchBreak (w) (hb : WatchBreak w) : ChainStep (.watch w) (.broken ⟨⟨right ver, control⟩, lag, margin⟩)`、`ChainMatched.brokenMatched (w) : ChainMatched (.broken w) (.broken ⟨machine, inc lag, inc margin⟩)` を足した（Scala `consume()`／`matched()` 通り）。`ChainStepGap.chainStep_exists_at_positive_lag_mismatch` が gap の閉鎖を記録（`Canonical.model_gap_watchBreak_closed`）。`#print axioms unconditional` は変わらず標準 3 ＋ `obligation_cycleOracle`／`obligation_localRealization` |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完（残り 2 公理）。**

### 何を変えたか（71 ファイル、定理は 5 本だけ新規: `not_good_of_watchBreak`／`watchBreak_arrive`／`watchBreak_trunc`／`lagLe_break`／`lagLe_breaks`——全部既存の `cases` を通すための対）

- `ChainStep`／`ChainMatched` の `cases` に alternative を追加（`.broken` 行きは不変量が `True`／空虚）。`chainStep_unique`／`chainMatched_unique`（2 ファイル）は `Internal.idle`（`positive lag = false`）／`take`（`Good`）と `WatchBreak` の排他。
- 終端比較を扱う定理群（`foundRouteMC_noshift'(_Inv)`／`life_restarted`／`found_life`／`found_to_found`／`chain_life` …、`FoundCycle`／`BreakEnd`／`ShiftTailC`／`NoShiftTailC(0/L)`／`hcont` 型）は、正 lag の break だと結論（restart）が偽になるので、終端 watch に `zero w3.lag = true` を仮説／成分として一括追加（regex、`hz3`）。producer 側（`GalilRoundConstruct`／`GalilMidRoundFallback`）は `RoundInv.wit` の `hzw` を渡すだけ。`rounds_break` は `scanSeg_only` で自前に導くので不要。
- `GalilTrailAssembly.LagLe`: broken chain の lag を `reset` と読む（`lagOf`）。break 前 `ver + lag ≤ r`・`lag ≥ 1` ⇒ break 後 `right ver ≤ r`（`lagLe_break`）。`ChainBudget.pos`（先読み予算）が broken の verifier にも要るため空虚化はしない。
- `GalilArriveChain`／`GalilTruncTick`: 到着・切り詰めとの可換（`watchBreak_arrive`／`watchBreak_trunc`、`breakStep_*` の対）。verifier を動かす Scala 通りの break 先だと切り詰め補題が自然に通る（`usedChain` が読んだ cell を数える）。
- dead 塔の切り離し: `unconditional` の閉包外で、構成子追加により**偽になった**補題（`CloseoutWatchRound2.watchClosed : WatchClosedC`「背景 tick は watch を watch に保つ」／`distance_mono_false`／`CloseoutTickFalse.step_ne_broken`）を含む round 塔（`CloseoutWatchRound*`／`WatchPhase*`／`TerminalN`／`MismatchCompare`／`TickFalse`／`LagAll`）を build から外した: Workbench 登録 9 本を削除、`Canonical.lean` の alias 11 本（`mismatchCompare_*`／`shiftEntry_exists`／`copyIdle_congr`／`shiftRun_exists_from_round`／`shiftAtMismatch_from_round`／`backgroundTick_keeps_watch`／`backgroundTick_is_identity_at_lagZero`／`step_never_breaks`／`landingReady_from_parts`／`chainReady_from_round`／`distance_eq_radius`／`radius_nonneg`）と import 4 本を削除。ファイルは未削除（build 対象外、後で削除）。
- `ChainReady`（`GalilTickFun`）の `positive lag → Good` 場はまだ残っている（run の存在に不要になったので次に緩める）。

### 次

`obligation_cycleOracle`: n248 の計画どおり `WindowRunPack` の上で found 経路（`FoundExitLPS`）を構成する。
run の存在は `GalilTickFun.tick_exists`（`Enabled`）で、`ChainReady.watch` の `positive lag → Good` を `watchBreak` で外す。

## n249 — `obligation_cycleOracle` の前に `M-watchBreak` を直す（run の存在が欠陥に当たる）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_cycleOracle` | 変化なし。ただし**順序が確定**: `CycleOutMC3` は「`InvLPS` から次の着地までの run が存在する」主張で、found 後の chain の一生（copy → back → watch、正 lag で追いつき）を通る。正 lag の watch で予測が外れると Lean の `ChainStep` には後続が無い（`PalPeg.ChainStepGap.no_chainStep_at_positive_lag_mismatch`、機械検査済み）。Scala `ScaffoldChain.step()` はそこで `consume()` → `Mode.Broken`（`ScaffoldChain.scala:136,178`）。DP が周期を決める窓は `stream.take (8·max k 1 + 1)` で、右腕がそれより長ければ外れうる（Scala に分岐がある理由）。**よって `M-watchBreak` を直すまで `CycleOutMC3` は証明不能**（run が止まる状態が到達可能） |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、n246 の木）・標準公理のみ（3 本）・無条件 PAL は未完（残り 2 公理）。**

### 直し方（一次情報: `GalilScaffoldTopChainVM.lean:26-75`）

`ChainMatched.breaks (w w') (hb : BreakStep w w')` は lag ゼロ経路の break。`ChainStep` に
正 lag 版を足す:
```
| watchBreak (w) (hp : positive w.lag = true) (hng : ¬ Good w) :
    ChainStep (.watch w) (.broken ⟨consume w.machine, w.lag, w.margin⟩)   -- 目標状態は Scala に合わせて確認
```
影響: `ChainStep` に触れるファイル 80、`watchStep` の出現 109。ほとんどは `cases` に
`.broken` 行きの alternative が 1 つ増えるだけ（`WindowInv .broken = True`、`SumRel .broken = True`、
`WatchOK` は broken で空虚、`Coupled.idleOut` は mode guard、`chainStep_unique` は `Good`／`¬Good` で排他）。
`ChainReady`（`GalilTickFun`）の `positive lag → Good` 場は消せる（run の存在に不要になる）。
手順: 構成子を足して `lake build --quiet PalPeg` の error 一覧を作業リストにする。

### 実装（n249 の続き、作業中・未コミット）

`GalilScaffoldTopChainVM.lean` に 2 構成子を足した（core ファイル単体は `lake env lean` で `BUILD=0`）:
```
| watchBreak (w) (hp : positive w.lag = true) (hng : ¬ GalilScaffoldChainWatch.Good w) :
    ChainStep (.watch w) (.broken ⟨⟨GalilScaffoldChainVerifier.right w.machine.verifier, w.machine.control⟩, w.lag, w.margin⟩)
| brokenMatched (w) : ChainMatched (.broken w) (.broken ⟨w.machine, inc w.lag, inc w.margin⟩)
```
根拠（Scala 一次情報）: `consume()` は先に `verifier.right()`、不一致なら `mode = Broken` で `false`
（`distance`／`period`／`lag` は触らない）；`matched()` は `margin.inc()` のあと Watch∧lag=0 以外は
`lag.inc()`；restart guard は `Broken ∧ margin ≥ 0 ∧ last > 0 ∧ lag == 0`（`ScaffoldGalil.scala:230-231`）
なので正 lag の broken chain は fallback まで生き続ける。
壊れる箇所のパターン: (A) `ChainStep` の `cases` に `watchBreak` 行き `.broken` の alternative
（不変量は `.broken` で `True`／空虚）、(B) `ChainMatched` の `cases` に `brokenMatched`、
(C) `chainStep_unique`／`chainMatched_unique` は `Internal` の `idle`（`positive lag = false`）／`take`（`Good`）
と `hp`／`hng` で排他、(D) `ChainStepGap.no_chainStep_at_positive_lag_mismatch`（＋`Canonical.model_gap_watchBreak`）
は**偽になる**ので削除して「gap は閉じた」に書き換える。作業リストは `lake build --quiet PalPeg` の error 一覧。
- 進捗（作業中）: 低層 11 モジュール＋中層（TrailChain／TrailAssembly／CopyPhase*／BranchSupply／
  TickFalse／PreludeDone／PreludeEnds）を修正済み。break 終端の定理群（`foundRouteMC_noshift'(_Inv)`／
  `rounds_break`／`life_restarted`／`found_life`／`found_to_found` …）は正 lag の break で結論（restart）が
  偽になるので、終端比較の仮説に `(hz3 : zero w3.lag = true)` を全ファイル一括で足した（regex、29 ファイル）。
  `CloseoutTickFalse.step_ne_broken` は `hOk : WatchOk Ok` を取るように（`WatchOk` は反証済みの死路）。
- dead 塔の切り離し: `unconditional` の import 閉包（598 モジュール）の外にある Workbench 登録 9 本
  （`CloseoutLagAll`／`CloseoutSegCheckpoint`／`CloseoutWatchRound26`／`51`／`53`／`FoundPackCorrected`／
  `FoundPackRefute`／`ReachesWatchFromRun`／`RoundHistory`）は、構成子追加で**偽になった**補題
  （`CloseoutWatchRound2.watchClosed : WatchClosedC`「watch は背景 tick で watch のまま」、
  `distance_mono_false`）を含む round 塔（`CloseoutWatchRound*`／`WatchPhase*`／`TerminalN`／
  `MismatchCompare`／`TickFalse`）を引き込んでいたので登録を外した（ファイルは未削除、build 対象外）。
  `WatchClosedC` はモデル欠陥 `M-watchBreak` の上でだけ真だった。
- 台帳 `GalilTrailAssembly.LagLe` は broken chain の lag を `reset` と読む（`lagOf (.broken w) = some (verifier, reset)`）:
  break 前 `ver + lag ≤ r`・`lag ≥ 1` から break 後 `right ver ≤ r`（`lagLe_break`）。`ChainBudget.pos`（先読み予算）は
  broken の verifier にも要るので空虚化はしない。

## n248 — `obligation_cycleOracle`: found 経路の既存入口は死んでいる（修理しない）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_cycleOracle` | 変化なし（地図の続き）。`hfound` の既存入口 `CloseoutFoundRoute1.foundExit_compare_final20` は **約 25 個の名前付き前提**（`ChainTickable`＝`WatchOk` 経由で反証済み、`StageEntryC`＝`fuel` 場が偽（n181）、`ShiftBreakOracleC`／`ShiftRoundAtC`／… の round 機構）を取る。round 機構は n233 で左端の番兵に壊れることも分かっている。**この塔は修理せず、found 経路を一から `WindowRunPack` の上に組む** |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、n246 の木）・標準公理のみ（3 本）・無条件 PAL は未完（残り 2 公理）。**

### `FoundRouteMC2`（`GalilOracleMC2:374`、inductive）が要求するもの

found tick の着地 `⟨c', t⟩`（segment の終端、`SegReachedW`）から:
* `report`（`ReachAtC2`: 報告点 m に着く）、または
* `shift`／`noShift`: `FoundCost`（`StepsAll (SoundScanNR) k ⟨c',t⟩ ⟨cT,sT⟩ ∧ CostedRun`）＋ `MInv`（最左 live 中心）＋ `Restarted`＋`FoundResidual`（mode scan・clock 2048・`StageEntry`・`Frontier`・`ReplayRest`・`ShiftIdle`）＋`SpanRep`＋中心前進＋`position sT.right ≤ 2m−1`、または
* `broke`: run＋`CostedRun`＋`InvLP2`＋`CentreRep`＋中心同じ＋右ヘッド前進。

一次部品 `GalilScaffoldTopLifeRestart.life_restarted`／`FoundLoop.found_to_found` は run の**形**（segment `bs ++ dm :: cs`、rounds、最後の segment、壊れる比較）を仮説に取る「形が与えられれば台帳が出る」定理。**欠けているのは形の存在**＝決定的な機械を found tick から回して、最初の不一致（shift／fallback）か break（restart）に着くまでの run を構成すること。

### 組み方（次のセッションの一手目）

1. run の存在: `GalilTickFun.tickFun`（choice で 1 つ選ぶ）の反復で `Steps k x (iterate tickFun k x)`。`SoundScanNR` の注釈は `OutputRel` の tick 保存から。
2. found tick 後の chain は `WindowRunPack.window`（`ChainWindowRun`）が run に依らず記述する（n238–n246）。copy → back → watch の相は `WindowInv` の分岐そのもの。
3. 着地の分類は `Tick` の構成子で機械的: `scan_shift`（guard 成立→`ShiftPal` は `shiftPal_of_windowRunPack` で既にある）／`scan_fallback`／`restart`（broken）。`life_restarted` の後半（restart tick → `Restarted`）を流用。
4. `MInv`（`Leftmost`）は `GalilLiveCentre*`（2026-09-16、scan segment・fallback・replay の保存）にある。

## n247 — `obligation_cycleOracle` の地図（葉の塔は `hpres`（偽）の上に建っている）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_cycleOracle` | 変化なし（地図のみ、定理は足していない）。下の表が一次情報（`grep "^theorem"` と署名の実読） |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、n246 と同じ木）・標準公理のみ（3 本）・無条件 PAL は未完（残り 2 公理）。**

### 消費者から見た形

`obligation_cycleOracle entry q first : ∀ w, 0 < |w| → CycleOracleMC3 (PofC centreC placeC entry w) q first w`。
`CycleOracleMC3 P q first raw := ∀ m c r, 1 ≤ m → m ≤ |raw| → InvLPS P q first raw c r → position r.right ≤ 2m−1 → CycleOutMC3 …`、
`CycleOutMC3 := ReachAtC3（報告点 m に着く）∨ ∃ cT sT k L, StepsAll (SoundScanNR) k ⟨c,r⟩ ⟨cT,sT⟩ ∧ CostedRun ∧ InvLPS cT sT ∧ mu sT < mu r ∧ position sT.right ≤ 2m−1`。
つまり「`InvLPS` から次の `InvLPS`（`mu` 減少）か報告点まで、機械の run を**構成**する」。

### 既存の塔（`CloseoutOracleBridge.hor_of_H_oracle` ＋ `CloseoutOracle8.h_oracle_of_leaves7`）

| 葉 | 現状の producer | 状態 |
|---|---|---|
| `hlift : InvL → InvLPS`（bridge） | `Inv` 枝は `replayStage_of_inv`、`InvScan` 枝は `hstage_of_scanBranch (hsc : H_stageScan)` | `H_stageScan` は**反証済み**（`InvScan` は radius に触れない）。再切り出し `InvScanS`（`CloseoutStageSupply`）／`InvSS`（`CloseoutInvScanS`） |
| `hreadyB`（`ReadyIface` ＋ Φ at `InvLPC`） | `readyIface_readyPacedS` ＋ `readyPacedS_restarted`（`CloseoutReadyStage`） | 閉じそう（未接続） |
| `hpresRepAt`（`HpresRepAt` at every `InvLPC`） | **なし**（`CloseoutOracle7` ヘッダが理由を明記） | producer ゼロ |
| `hshape : StartShape` | `startShape'_of_decodes` は **`StartShape'`**（replay 中・`ReplayStageD` 付き） | `StartShape` は**偽**（CLAUDE.md §3b）。塔がこの形を要求する限り塔は使えない |
| `hstage : ReplayStageInv` | **なし** | producer ゼロ |
| `hended` / `hlastMatch` / `hlastMismatch` | `GalilLeafReport.hended_C`／`GalilOracleMC4.hlastMatch_C'`／`GalilLeafReport.hlastMismatch_C` | 全部 `hpres : SearchReady → searchEffect → SearchReady` を取る。**偽**（`CloseoutPresRefute.hpres_fails_at_zero_debt`: debt 0 で破れる）。`hlastMismatch_C` は加えて `LastMismatchReport`（producer なし） |
| `hmismatch` | `GalilLeafDp.hmismatch_of_residues'` | 側入力 `hdp'`（`MismatchDp`）／`hbud`（`StageBudgetAt`）／`hfb`／`hpos`（producer 未確認） |
| `hfound` / `hfoundBg` / `hfoundReplay`（`FoundRouteMC2`／`FoundInReplayRouteMC2`） | **なし** | producer ゼロ。found 経路そのもの |

### 判断

葉の塔は `hpres`（偽）の上に建っていて、`hshape` も偽の形。**塔を修理するより、`ReadyClosure`
（`GalilReplaySpan.ReadyClosure`: `ready`／`seg`／`restart` の 3 場、`CloseoutPreload11.readyClosure_S2`
が `PostRun` ＋ `RestartS2` から出す）の上で `InvLPS → 次の着地` を直接構成する。**
一次部品: `restarted_next_found`（`GalilScaffoldTopReadyFound`）、`life_restarted`／`found_to_found`
（`GalilScaffoldTopLifeRestart`／`FoundLoop`）、`fallback_restarted_All`
（`GalilScaffoldTopFallbackRestartAll`）、`prep_segment_construct_of_found`、`SegReachedW`
（`segment_of_invLP`）。次の一手は `hshape` の消費点（`CloseoutOracle5:249`、found-in-replay 経路）
を読んで `StartShape'` で足りるかを機械で確認すること。

## n246 — **公理 3 → 2**: `obligation_shiftPalResiduesAlongRun` を証明して削除

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | **消えた。** `#print axioms PalPeg.PalInPeg.unconditional` は `[propext, Classical.choice, Quot.sound, obligation_cycleOracle, obligation_localRealization]`（`Axioms.lean` の guard 更新済み、`lake env lean` で直接確認）。残差は run 上の pack `WindowPack.WindowRunPack`（`ChainWindowRun`／`Coupled'`／scan・shift での `CentreRep`／`RadiusRep` 台帳）から読み出せる: `WindowPack.shiftPal_of_windowRunPack (hpack : LPackM) (hx : WindowRunPack) (hcan : canRight right) (hs : ScanNR) : ShiftPal`。`2h ≤ R` は `Coupled'.watch` の両枝（fresh: `FreshC` ＋ phase 4 → `four_of_freshC`、post-shift: `CloseoutPackRun40.four_of_other'`）から `four_of_guard : 4h ≤ radius`。pack は `IPackMW` の新しい場 `win : Decodes (PofC …) → WindowRunPack` として oracle の鎖（`StepsIMW`／`CycleOutIMW`／`H_bootIMW`／`PreTraceIMW`）を自動で流れる。run 形の消費者 `packRunR_MW_marksFree` は `hShiftPalAlongRun` の代わりに `hP : Decodes` を取り（`given_scanLandingObligations` は `decodesC entry w`）、tick ごとに `hn.ipackM.win hP` から `ShiftPal` を出す。trace 形 `obligation_shiftPalAlongTrace` は `PreTraceIMW.packs j` の `win` から定理に |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`）・標準公理のみ（3 本）・無条件 PAL は未完（残り 2 公理）。**

### 何を足し、何を消したか

- 新: `PalPeg/WindowPack.lean` — `WindowRunPack`（5 場）、`windowRunPack_boot`／`_of_invLPC`（起点）、`four_of_freshC`／`four_of_guard`（guard 点の `4h ≤ radius`）、`source_watch_of_guard`（guard が立つ着地の源 chain は watch、`backDone` の新鮮 watch は phase 0 で矛盾）、`shiftPal_of_windowRunPack`、`ledger_tick`（24 構成子）、`windowRunPack_tick`。全部標準公理のみ。
- 変更: `IPackMW` に `win` 場（`CloseoutPackW`）。`ipackMW_tick`／`bigPack2MG7W''_tick`／`_tick_M` が `windowRunPack_tick` で運ぶ。`ipackMW_of_invLPC`（起点）と `h_bootIMW_of_bootIPack`（boot の i = 0, 1）が供給。`chainWindowRun_tick` の側仮説は mode guard 付きに弱め、`canRight` は tick 構成子の `available`（非 replay）と `FrontPack`（replay: `canRight_of_frontPack`）から。
- 消した: 公理 `obligation_shiftPalResiduesAlongRun`、`obligation_shiftPalAlongRun`、`obligation_shiftPalResiduesAlongTrace`、`given_scanLandingObligations` の `hShiftPalAlongRun`、参照ゼロの `bigPack2MG7W_of_bigPack2MG7`、`ShiftPalAlongTrace.chainIdle_after_init`（`BranchSupply` の import を切るため。`ShiftPalAlongTrace` は `BranchSupply` → `CloseoutCheckW` → `CloseoutPackW` を経由していたので、`CloseoutPackW` が `WindowPack` を import すると循環した）。

### 次

残り 2: `obligation_cycleOracle`（`CycleOracleMC3`、found 経路の葉 `hshape`／`hfound`／`hfoundBg`／`hfoundReplay`／`hpresRepAt` は producer ゼロ ＝ 形式化のミスとして再切り出し）と `obligation_localRealization`（`H_realizeLIMW'`）。

## n245 — 公理進捗: `ChainWindowRun` の `Tick` 保存 `WindowTick.chainWindowRun_tick`（24 構成子）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 残差の窓を運ぶ run 不変量 `ChainWindowRun` が **`galilFrameS` の 1 tick（24 構成子全部）で保たれる**ことを証明（`WindowTick.chainWindowRun_tick`、標準公理のみ）。周辺事実は仮説で取る: `Decodes (PofC …)`（`decodesC` でタダ）、`AuxPack`（`idleOut` で非 scan/shift/init の chain idle、`copyP` で `shift_one` の `remainingPos` 選言を潰す）、`CentreRep`、右ヘッドの `Represents`/`focus ≠ none`、scan かつ `clock = 1` での `canRight right`、scan での `RadiusRep radius R' ∧ position right = center + R'`。scan 側 4 構成子は `chainWindowRun_background_case`（`backgroundS` 展開: chain 1 歩／idle／誕生）・`_match_case`（一致比較の `afterCompare`＋`matchedPlace`）・`_shift_case`（不一致 → `shiftGuardVM` → `beginShiftVM'`、`Good w` は guard の記号一致と `WindowInv` の lag 0 窓から `good_of_guard`）・`_shiftOne_case`（`shiftLens.rel` 越しの `shiftTick`）。残り: `Steps` 帰納で周辺事実を run に沿って供給する層（`auxPack_steps` は各到達点の `CentreLive` を要求、`RadiusRep` は `Restarted`＋`radius_rep_inc`）と、guard 点での残差取り出し（`2h ≤ R` の cycle 算術） |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### 起きたこと（機械の出力）

- `lake env lean PalPeg/WindowTick.lean` → `BUILD=0`、`sorryAx` なし、7 定理すべて `[propext, Classical.choice, Quot.sound]`。
- `import PalPeg.WindowTick` を `Workbench.lean` の `WindowRun` 直後に登録、`lake build --quiet PalPeg` → `BUILD=0`。
- 直したもの（前ノートの型検査エラー 7 件）: `open A (x) B (y)` は 1 行に書けない（分割）／`rewindLens_rel_chain` の `rw` 後の `rfl`／`compare_target_heads` の未使用 implicit 3 つ／`rw [← hy, …]` の向き／`shiftOne_case` の `htright` に `rfl`、`right_position s.center hcanC'`（`shiftLens.get` 越しの `canRight` は defeq）／`match_case`・`shift_case` 呼び出しの `hmode := rfl`／fpp・rewind 構成子の idle 分岐は `apply chainWindowRun_of_idle; rw [lens]; exact hidle …` の 3 行に展開。

## n244 — 公理進捗: run 層の窓不変量 `ChainWindowRun` と VM 遷移ごとの transport 8 本

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 残差の窓を run に沿って運ぶ `State GalilVM` 上の不変量 `WindowRun.ChainWindowRun`（`WindowInv`＋右ヘッド `R = position s.right`＋中心のずれ: scan で `center = cen₀ + k·h`、shift 中は `center + remaining = cen₀ + (k+1)·h`）と、VM 遷移ごとの transport が揃った（全部標準公理のみ）: `chainWindowRun_of_idle`／`_of_broken`／`_chainStep`（background の chain 1 歩）／`_birth`／`_birth_matched`（誕生）／`_matched`（一致比較: `ChainStep` → `ChainMatched`、右ヘッド +1）／`_shift`（不一致 → `immediate`、phase 0 の新鮮 watch は guard の phase 4 と矛盾）／`_shiftOne`／`_shiftDone`。残るのは `Tick` ごとの組み立て（`backgroundS`／`compareFound`／`beginShiftVM'`／`shiftOne` の展開と周辺事実）と `Steps` 帰納、そして残差の取り出し |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### `Tick` 組み立てに要る周辺事実（run 層が供給するもの）

| 事実 | 使う遷移 | 供給元候補 |
|---|---|---|
| `Coupled.idleOut`（非 scan/shift/init で chain idle） | rewind 等 | `AuxPack.coupled`（`auxPack_steps`） |
| `CopyPack`（`mode ≠ copy → CopyIdle`） | `shift_one`/`shift_done` の `remainingPos` | `AuxPack.copyP` |
| `CentreRep raw s` | 誕生・shift 1 歩 | `InvLPC` 起点＋`centreRep_congr` |
| `Represents s.right.head ∧ focus ≠ none`、`canRight s.right` | 比較 | `Inv.input`／`Extra7.scanAvail`／replay は `Frontier` |
| `RadiusRep s.radius R' ∧ position s.right = center + R'` | 誕生 | `Restarted`＋`radius_rep_inc`（scan 区間の不変量、要確認） |
| 中心記号 `x[center]? = some (P.centre s)` | 誕生 | `decodesC`＋`CentreRep`（`read_represent`・`represented_read`） |

## n243 — 公理進捗: chain の一生の不変量 `WindowInv` と 5 つの transport（DP の形の葉なし）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 残差の窓 `WatchWindow` を chain の一生（誕生 `chainStart` → copy → back → watch）を通して運ぶ chain 側の不変量 `WindowInv.WindowInv` と、全遷移の transport が揃った（`windowInv_start`／`_step`（`ChainStep`）／`_matched`（`ChainMatched`）／`_immediate`（shift 入口）／`_shiftOne`、標準公理のみ）。**`AnswerAhead`／`PlaceAhead`／`StartShape` などの DP の形の葉は使わない**——ブロックの中身 `b xs` は `copyEnd` で決まり、`backDone` で `coreX_born` が制御を作る。残るのは run 層（`Tick` ごと）への持ち上げと、中心のずれ `cen = cen₀ + k·h`・`2h ≤ R`・`ScanInvariant`／`canRight` の供給 |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### `WindowInv raw cen₀ R cc : ChainVM → Prop`

| 枝 | 中身 |
|---|---|
| `idle`／`broken` | `True` |
| `copy … v lag _ ver` | `VerAt raw cen₀ ver ∧ LagAt lag ver R ∧ ∃ ys, v = fill (start cc) ys` |
| `back v _ lag _ ver` | `VerAt raw cen₀ ver ∧ LagAt lag ver R ∧ ∃ b xs, flat v = blockTokens cc b xs` |
| `watch w` | `∃ b xs, WatchWindow raw cen₀ R cc b xs (.watch w)` |

誕生: verifier ＝ 中心ヘッド（`VerAt`）、lag ＝ 半径カウンタ（`lagAt_radius`）。
`copyBit` は `fill_append`、`copyEnd` は `fill_last_focus`＋`flat_block`、`backStep` は
`flat_moveLeft`、`backDone` は `rewound_of_flat`＋`coreX_born`（窓は空虚）、watch は n242 の補題。

### 次の一手（run 層）

`Tick` ごとの持ち上げ: `scan_wait`／`scan_count`（`backgroundS` の `chainAt false` ＝ `ChainStep`）、
`scan_match`（`compareFound` の `chainAt true` ＝ `ChainStep` → `ChainMatched`、誕生は第 3 選言）、
`scan_shift`（`ChainStep` → `beginShiftVM` の `immediate`）、`scan_fallback`（chain idle）、
`shift_one`（`chainShiftOne`）、他のモードは chain idle。中心のずれは scan で `cen₀ + k·h`、
shift 中は `center + remaining = cen₀ + (k+1)·h`。

## n242 — 公理進捗（訂正 3）: `WatchWindow` の制御を `SamePrediction` 版 `CoreP` に

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 残差の文面は不変（`WatchWindow` の名前で参照）。中身の `CoreX`（制御 ＝ `run (ready …) pre` そのもの）は `chainShiftOne` が sweep カウンタ（distance/boundary/last）を `dec` するので shift 以降は偽——`SamePrediction m.control (run … pre)`（period テープと進行方向だけ）＋`broken = false` の `CoreP` に置き換えた。予測記号は `GalilScaffoldChainPrediction.continued_prediction`（「カウンタを調整した継続は元の予測器の位相を保つ」）で従来どおり出る。**これで `WatchWindow` は chain の全遷移で保たれる形になった** |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### 何を証明したか（`ShiftPalAlongTrace`、全部標準公理のみ）

| 定理 | 内容 |
|---|---|
| `CoreP` / `coreP_of_coreX` | `CoreX` の弱化と、誕生時（`coreX_born`）からの変換 |
| `symbol_of_coreP` | 予測記号（`continued_prediction` 経由、右端の余裕不要） |
| `coreP_consume` | `Good` 付き consume で保存（`coreX_consume` の `SamePrediction` 版） |
| `coreP_chainShiftOne` | `chainShiftOne` で保存（defeq） |
| `window_consume_of_good` | `Good` 付き consume: verifier +1・窓 +1・`CoreP` |
| `watchWindow_step` / `watchWindow_outer` / `watchWindow_shiftOne` | background（`Internal`）／一致比較（`Outer … true`: `queued` は `lagAt_inc`、`immediate` は consume）／shift 1 歩 |

### 次の一手

chain の一生の不変量 `WindowInv raw cen₀ R cc : ChainVM → Prop`（idle: True／copy: `VerAt`＋`LagAt`＋
`∃ ys, v = fill (start cc) ys`／back: `VerAt`＋`LagAt`＋`∃ b xs, flat v = blockTokens cc b xs`／watch:
`∃ b xs, WatchWindow`／broken: True）と、`ChainStep`／`ChainMatched`／誕生（`chainStart`）／
`immediate`（shift 入口）／`chainShiftOne` の transport。**DP の形の葉（`AnswerAhead`／`PlaceAhead`／
`hshape`）は不要**——ブロックの中身 `b xs` は `copyEnd` で決まる。その後 run 層（`Tick` ごと）へ。

## n241 — 公理進捗（訂正 2）: `WatchWindow` の窓を「verifier が消費した接頭辞」に

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 残差の文面は不変（guard 点は lag ゼロなので verifier ＝ 右ヘッド）。`WatchWindow` の定義を `BlockOn … (cen₀+1) (position ver)`（消費接頭辞）に直した——n240 の形（`BlockOn … R`、右ヘッドまで）は **lag > 0 の間の run 不変量としては過剰**（`chainW_matched` は窓の終端 `E` を変えずに右ヘッド `R` だけ進める）。この形なら chain 自身の歩みだけで維持できる: `take`／`immediate` は持参する `Good`（予測 ＝ 次の読み）で窓が 1 つ伸び（`blockOn_succ_of_symbol`）、`queued` は不変、shift（`chainShiftOne`）も不変 |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### producer の設計（一次情報で確認したもの）

* 誕生: `chainAt` の第 3 選言で chain は `chainStart answer (P.centre s) walker s.center s.radius`（`.copy`）。
  `backDone` で `.watch ⟨ver, watchControl v⟩` になり、`CoreX` は `coreX_born`（DP の形の葉は不要:
  `Represents ver.head`・存在・`position ver + 1 = anchor` だけ）、`LagAt` は `lagAt_radius`、
  窓 `BlockOn … (cen₀+1) cen₀` は空虚。中心記号は `Decodes`＋`read_represent`＋`represented_read`
  （`InvLPC` の `CentreRep`）から `(encoded raw)[position s.center]? = some (P.centre s)`。
* 一致比較: `ChainMatched.watch (ho : Outer w true w')`——`queued`（lag +1、`lagAt_inc`）か
  `immediate`（`Good` 持参で窓 +1）。background: `ChainStep.watchStep (Internal)`（`watchWindow_step`）。
* shift: `beginShiftVM` の `immediate`（窓 +1、guard の予測一致）と `shift_one` の `chainShiftOne`
  （sweep カウンタと margin だけ、窓と lag は不変）。
* `2h ≤ R`: 新鮮な shift は guard の margin（`4h ≤ R`）、継続 round は cycle 算術
  （shift 直後 `R + 1 − h ≥ 3h + 1`、round 中は増えるだけ）。

## n240 — 公理進捗（訂正）: 残差の chain データを `ChainW` から 3 場の `WatchWindow` に絞った

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | n238 の残差は `ChainW … cen₀ …`（margin 等式込み）を要求していたが、**これは最初の shift 以降は偽**（下記）。producer が使う 3 場（`LagAt`／`BlockOn`／`CoreX`、誕生中心 anchor）だけを要求する `ShiftPalAlongTrace.WatchWindow` に置き換えた。**公理は弱くなり、`periodOnly = true` の shift 入口でも真たりうる形になった** |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### なぜ `ChainW` では偽だったか（一次情報）

`GalilScaffoldChainInputSupply.chainShiftOne`（`:1478`）は shift 1 歩ごとに `margin` を `dec` し、
`beginShiftVM` の `immediate` は `inc margin` と verifier +1。`ChainW` の `.watch` 枝の等式
`value margin + 4h = R − C` は `C` を**現在の中心**（shift ごとに `+h`）に取れば保たれるが、
`BlockOn`／`CoreX` の anchor は**誕生中心**（`bounce cc b xs` の位相）。1 つの `C` で両方は
満たせないので、誕生中心を `C` にした `ChainW` は最初の shift 以降は成り立たない。
自分で書いた残差の過剰な主張——`chainShiftOne` を読んで気づいた（機械検査した反証は無い）。

### 何を証明したか

| 定理 | 内容 |
|---|---|
| `ShiftPalAlongTrace.WatchWindow` | `.watch w ↦ LagAt w.lag ver R ∧ BlockOn … (cen₀+1) R ∧ CoreX … (cen₀+1) w.machine`、他は `False` |
| `ShiftPalAlongTrace.watchWindow_of_chainW` | `ChainW … cen₀ R R …` の `.watch` 枝から（誕生直後、shift 前） |
| `ShiftPalAlongTrace.watchWindow_step` | `Internal` 1 歩（`idle` は不変、`take` は verifier +1・lag −1、`Good` は `take` が持参） |
| `freshShiftLedger_of_chainW`／`_scan` | 仮説を `WatchWindow` に差し替え。`_scan` は `chainW_step`／`chainStep_unique`／`LandingData` が不要になった（`ChainStep` の `.watch` 構成子は `watchStep` だけ） |

### 残差（run 層に要求するもの）の現在形

不一致比較の直前 `z` で shift guard が立つなら
`∃ cc b xs cen₀ k R, position z.vm.center = cen₀ + k·h ∧ WatchWindow w cen₀ (cen + R) cc b xs z.vm.chain ∧
ScanInvariant w cen R … ∧ canRight z.vm.right ∧ x[cen₀] = cc ∧ 2h ≤ R`。
producer は `WatchWindow` を run に沿って運ぶ: 誕生（`chainW_start`＋`blockOn_of_candidate` →
`watchWindow_of_chainW`）、background（`watchWindow_step`）、一致比較（窓 +1: `coreX_consume`＋
`blockOn_succ_of_symbol` 形）、shift 相（`immediate`＋`chainShiftOne`: `LagAt` は verifier +1、
`BlockOn`／`CoreX` は不変——`chainShiftOne` は sweep カウンタと margin しか触らない）。

## n239 — 後始末: 参照ゼロになった `ShiftInv` 入口の組み立て群を削除、docstring を現状に

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 変化なし（n238 の窓 1 本のまま）。次は run 層の producer |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

削除（参照ゼロ・round 機構経由の旧経路。n232 の git 履歴に残る）:
`shiftInv_of_watch_entry`／`pred_immediate`／`immediate_lag_unbroken`／`coreX_immediate`／
`palNext_of_centre`／`shiftPal_of_chainNotWatch`。残した部品は全部 `freshShiftLedger_of_chainW`
が使う（`symbol_of_coreX`／`blockOn_succ_of_symbol`／`cells_run`／`periodLength_of_coreX`／
`block_last_of_blockOn`／`palAt_block_of_centre`／`bounce_getElem?_symm`／`periodOn_of_blockOn`／
`palAt_mirror`／`periodOn_extend_left`／`palAt_shift_half`／`palAt_block_periodic`）。
`ShiftPalAlongTrace` の冒頭と `Workbench` の該当節を n238 の形に書き換えた。

### 次の一手（run 層の producer）

窓の残差を run に沿って運ぶ pack 場を足す:
`ChainWindowAt raw s := ∃ cc b xs cen₀ k R bud, position s.center = cen₀ + k·h ∧
ChainW raw cen₀ (cen+R) (cen+R) bud false cc b xs s.chain ∧ x[cen₀] = cc ∧ 2h ≤ R`
（chain が watching のとき）。維持: 一致比較 `chainW_matched`、background `chainW_step`、
shift 相（右ヘッド不動・chain は lag 0 で idle）、誕生 `chainW_start`＋`blockOn_of_candidate`
（found／replay 両経路とも `Candidate` を持つ）。

## n238 — 公理進捗: `obligation_shiftPalResiduesAlongRun` を窓 1 本に置換（偽の第 2 連言と `H_readsShift` が消えた）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 3 連言（`H_readsShift`／`H_freshShiftAtShiftEntry`／窓）→ **1 連言**: 不一致比較の直前で shift guard が立つ点 `z` に、誕生中心 `cen₀` に anchor した `ChainW` の窓（現在の中心は `cen₀ + k·h`、窓は右ヘッドまで）＋`ScanInvariant`＋`canRight`＋`x[cen₀] = cc`＋`2h ≤ R`。`periodOnly` の区別なし。n233 で偽（条件付き）と分かった `H_freshShiftAtShiftEntry` と、round 機構の `H_readsShift` は**公理から消えた**。`ShiftPal` は round 機構（`shiftPal_of_run_B`／`RoundScan`）を経由せず、窓の周期構造から直接出る |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### 何を証明したか

| 定理 | 内容 |
|---|---|
| `ShiftPalAlongTrace.palAt_shift_half` | 半径 `h` の回文は周期 `2h` で `h` だけ右へ写る |
| `ShiftPalAlongTrace.palAt_block_periodic` | 誕生中心から `h` 刻みの全中心 `cen₀ + (j+1)h` はブロック回文（`j = 0` は `palAt_block_of_centre`、以降は `palAt_shift_half`） |
| `ShiftPalAlongTrace.freshShiftLedger_of_chainW`（一般化） | 誕生 anchor の窓＋`cen = cen₀ + k·h`＋`2h ≤ R` から `FreshShiftLedger` の 5 成分。margin には触れない |
| `ShiftEntryFromLanding.freshShiftLedger_of_chainW_scan`（一般化） | 比較前の窓から（chain の 1 歩を `chainW_step`＋`chainStep_unique` で渡す） |
| `obligation_shiftPalAlongRun` / `obligation_shiftPalAlongTrace` | 窓の残差 → `shiftPal_of_freshShiftLedger` で `ShiftPal`。trace 形は `canRightAtScanOrShift_alongTrace` で `canRight` を取る |

削除（参照ゼロ）: `shiftPal_alongRun`／`shiftPal_alongTrace`／`roundBundle_alongTrace`
（round 機構経由の旧経路）、`freshShiftLedger_of_landing`（`LandingData` 射影のデモ）。

### なぜこれで正しいか（一次情報）

* 窓 `ChainW … cen₀ …` は一致比較で 1 つ伸び（`GalilReplaySpan.chainW_matched`）、shift は右ヘッドを
  動かさない（`beginShiftVM`／`shiftOne` は `center`・`left` だけ）。誕生 anchor は変わらない。
* 現在の中心 `cen₀ + k·h` の右 `h` の回文は `palAt_block_periodic`、`h < i` は現在の回文で鏡映して
  窓の周期で進める。左端の不一致は語レベルの主張に影響しない。
* Scala `ScaffoldChain.checkPair` の assert（継続中は予測一致、`cycleEnd` でだけ不一致）とも整合。

### 残差（run 層に要求するもの）と producer 候補

| 残差 | producer 候補 |
|---|---|
| `ChainW`（誕生 anchor）を不一致比較の直前まで運ぶ | replay 生まれ: `CloseoutWatchRound48/50/53`（`LandingData` の transport、ただし `C := position t.center` で shift を越えると anchor がずれる → `cen₀` 固定に直す）。found 生まれ: `GalilReplaySpan.blockOn_of_candidate`＋`chainW_start`（誕生時）＋同じ transport |
| `x[cen₀] = cc` | 誕生時の `Candidate`（`candidate_bounce` の `hc0 : w[0]? = some c`、`blockOn_of_candidate` の `hcen`） |
| `2h ≤ R` | 新鮮な shift: guard の margin（`4h ≤ R`）。継続 round: 半径は `R + h` ずつ増える |
| `ScanInvariant`／`canRight` | `LandingData`／`LiveScanChain`／`WatchSegE.match` の `ha` |

## n237 — 公理進捗: 第 3 連言を「不一致比較直前の窓＋中心記号」に置き換えた（操作 B）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 第 3 連言が `FreshShiftLedger` から、その**十分条件である一次事実**——不一致比較直前 `z.vm` の `ChainW … (position z.vm.center) (cen+R) (cen+R) bud false cc b xs z.vm.chain`＋`ScanInvariant … R`＋`canRight`＋中心記号 `(encoded w)[cen]? = some cc`（`shiftGuardVM s'` の下で）——に置き換わった。橋は `ShiftEntryFromLanding.freshShiftLedger_of_chainW_scan`（標準公理のみ）。trace 形定理も同形に。**本数は 3 のまま、中身は run 層に既にある形（`LandingData` の射影）になった** |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### 次の一手（設計が確定した）

`GalilRoundPeriod.ReadOrigin`／`roundScan_entry` は `hroom : radius + 2 ≤ center` を仮説に取る
——round 機構は最初から左端を除外している（第 2 連言が偽だった理由）。一方、窓の議論は
左端でも成り立ち、**`periodOnly = true` の shift 入口でも同じ**: 誕生中心 `cen₀` に anchor した
`ChainW` の窓は一致比較で伸び（`chainW_matched`）、shift は右ヘッドを動かさないので保たれる。
現在の中心 `cen' = cen₀ + k·h` について、shift 先 `cen' + h` の半径 `h` の回文はブロックの
周期構造（`bounce` は `b` と `cc` の両方で対称）から出る。

したがって **3 連言全部を「不一致比較直前の誕生 anchor 窓」1 本に置き換えられる**:
`∃ cc b xs cen₀ k R bud, position z.vm.center = cen₀ + k·(|xs|+1) ∧ ChainW w cen₀ … ∧ ScanInvariant ∧ canRight ∧ x[cen₀] = cc ∧ 2(|xs|+1) ≤ R`。
`FreshShiftLedger` の producer を `cen₀`/`k` で一般化し（margin の代わりに `2h ≤ R` を取る）、
`shiftPal_of_freshShiftLedger` で `ShiftPal` を直接出す——`shiftPal_of_run_B`（round 機構）を
経由しない。偽の第 2 連言と `H_readsShift` は公理から消える。

## n236 — 公理進捗: 第 3 連言の guard を `¬ matched s'` に狭めた（操作 A・公理は弱化）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 第 3 連言が不一致比較（`¬ (galilFrameS …).matched s'`）でだけ `FreshShiftLedger` を要求する形になった。消費者 `shiftPal_of_freshShiftLedger` は `ShiftPal` の前提から `¬matched` を持っているので何も失わない。一致比較の着地（`afterCompare`、chain は `ChainMatched` 越し）を主張から外した |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

編集 5 箇所: `shiftPal_of_freshShiftLedger`／`shiftPal_alongTrace`／`shiftPal_alongRun`（`ShiftPalAlongTrace`）、
run 形公理と trace 形定理（`PalInPegUnconditional`）。`Axioms.lean` の guard は変化なし（3 本）。

## n235 — 公理進捗: 第 3 連言の wrapper `freshShiftLedger_of_landing`（`LandingData` から）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 第 3 連言 `FreshShiftLedger w z.vm s'` が、比較前・clock 1 の状態の `CloseoutWatchRound42.LandingData`＋`canRight`＋中心記号 `x[cen] = cc`＋`compareFound`（不一致枝）から出る（`ShiftEntryFromLanding.freshShiftLedger_of_landing`、標準公理のみ）。比較量子の中の chain の 1 歩は `chainW_step`＋`chainStep_unique` で渡した。**第 3 連言に残る run 層の入力は「不一致比較の直前で `ChainW` 形の窓と中心記号を持つ」だけ** |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### 次の一手

1. 第 3 連言の guard を `¬ matched s'` に狭める（消費者 `shiftPal_of_freshShiftLedger` は
   `ShiftPal` の前提から `¬matched` を持っている——操作 (A)、公理は弱くなる）。
2. 第 3 連言を「不一致比較の直前で `ChainW` 形の窓（`z.vm.chain`）＋`position z.vm.right = cen + R`＋
   `ScanInvariant`＋`canRight`＋`x[cen] = cc`」に置き換える（操作 (B)）。producer 候補は
   replay 経路の `LandingData`（射影するだけ）と found 経路の `blockOn_of_candidate`＋`chainW_start`。

## n234 — 公理進捗: 第 3 連言 `FreshShiftLedger` の producer（左端でも真）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 第 3 連言の中身 `FreshShiftLedger w s s'` が、`ChainW` 形の窓（比較後の chain）＋中心記号 `x[cen] = cc`＋比較後の右ヘッド 3 事実から 1 本の定理で出る（`ShiftPalAlongTrace.freshShiftLedger_of_chainW`、標準公理のみ）。**左端の不一致でも成り立つ**（n233 で偽と分かった第 2 連言と違い、5 成分とも語レベルで左端に触れない）。残るのは `LandingData` からの wrapper（次） |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### 部品（全部 `shiftInv_of_watch_entry` と共用）

| 定理 | 内容 |
|---|---|
| `block_last_of_blockOn` | `x[cen + 2h]? = some cc`（`bounce` の末尾は `cc`） |
| `palAt_block_of_centre` | `PalAt x (cen + h) h`（ブロック回文。`palNext_of_centre` から切り出し） |
| `palAt_mirror` | `PalAt x C R → PalAt x (C+d) r → d + r ≤ R → PalAt x (C−d) r` |
| `periodOn_extend_left` | 周期区間を左へ 1 つ伸ばす |
| `freshShiftLedger_of_chainW` | 5 成分: `palAt_mirror`（`hIn`）／`periodOn_mirror`＋`periodOn_extend_left`（`hLeft`）／`periodLength_of_coreX`／margin／`blockOn_succ_of_symbol`（`hCaught`） |

### 供給側（一次情報で確認）

* `BlockOn` の producer は `CloseoutWatchRound48/50/53`（`LandingData` の transport）と
  `GalilReplaySpan.blockOn_of_candidate`（誕生時、DP の `Candidate` から）、
  `chainW_start`（誕生時の `ChainW`、`hwin : BlockOn` を入力に取る）。
* `CloseoutWatchRound42` ヘッダ: found 起点の経路（`ShiftTailC`／`foundRouteMC_shift_Inv`）は
  `InvLPC` ＋ DP レコードに根ざし `ChainW` を運ばない。replay 生まれの経路は `ChainW` を運ぶ。
  **両経路とも誕生時に `Candidate`（`x[cen] = cc` を含む）を持つ**ので、found 起点でも
  `blockOn_of_candidate`＋`chainW_start` で `LandingData` を立てれば同じ transport が使える。

## n233 — 公理進捗: 第 2 連言 `H_freshShiftAtShiftEntry` は左端の不一致で偽（REFUTED・条件付き）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 第 2 連言（run の各 tick で `H_freshShiftAtShiftEntry`）が**左端の不一致では `False` を導く**と機械検査した（`ShiftEntryBoundary.refuted_freshShiftAtShiftEntry_at_left_end`、公理 `propext`・`Quot.sound` のみ）。証人（その状態に `InvLPS` から到達する run）は未構成なので **REFUTED（条件付き）**。この連言は再切り出しが要る。第 1・第 3 連言は変化なし |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### 反証の中身（一次情報）

* ヘッドモデル `GalilScaffoldInputHead.layout`（`GalilScaffoldInputHead.lean:14`）: 左スタックの末尾は
  `none` 番兵。最初の文字に居るヘッド `⟨layout [a] rs qs, false⟩`（位置 1）を `left` すると
  `moveLeft` が番兵を焦点に持ってきて `focus = none`、`read = none`。
* Scala 正本 `ScaffoldInput.read()`（`ScaffoldInput.scala:79`）も「`None` at the origin」と明記。
  **番兵は忠実。** `ScaffoldGalil.scala:267-272` は `left.read() == right.read()` で不一致なら
  `chain.canShift && chain.prediction() == right.read()` で `beginChainShift()`——左端に
  条件は無い。
* 到達可能性（未構成）: `a^n` では `GalilLiveCentre.Live` の `n < 2c` が右ヘッド `2c−1` で
  中心 `c` を強制し、次の比較は必ず左端。chain は DP が `4h+1` セル見て生まれ `4h` セルで
  phase 4、`margin = R − 4h ≥ 0` は `c ≥ 4h+1` で成立。
* 反証定理は「左ヘッドが最初の文字に居る `s` から `scan_shift` 形の tick（compare・不一致・
  `shiftGuardVM`・`beginShiftVM'`）が出る」ことだけを仮定し、`ShiftInv.leftPresent`
  （`t.left = u.left = left s.left` の焦点が `none`）で `False`。

### 何が壊れていて何が無事か

| 述語 | 左端の不一致での状態 | 理由 |
|---|---|---|
| `ShiftInv`（`CloseoutPackRun37:59`） | **偽** | `leftPresent`（焦点 none）、`room : R + 2 ≤ C`（`C − R − 1 = 0`）、`origin`（`x[0]? = some 2 = x[2C]?`：語レベルの `≠` は偽） |
| `RoundScan`（`GalilRoundPeriod:175`） | **偽** | 同じ `room`／`origin` |
| `ShiftPal`（`CloseoutPackRun29:87`） | 真 | 結論は shift 先の回文 `PalAt (cen+h) (r₀+1−h)` だけ |
| `FreshShiftLedger`（第 3 連言） | 真 | 5 成分とも語レベルで左端に触れない |
| Scala `ScaffoldChain.checkPair` | 整合 | 継続 round の終端（`cycleEnd`）は再び左端に来るので assert は矛盾しない |

**つまり round 機構（`ShiftInv`/`RoundScan`）は「不一致は本物の文字の不一致」を前提に
語レベルで書かれており、機械レベルの不一致（`read = none`）を表せない。** 正しい形は

* `room : R + 1 ≤ C`
* `origin : C − R − 1 = 0 ∨ (encoded raw)[C−R−1]? ≠ (encoded raw)[C+R+1]?`
* `leftPresent : 1 ≤ C − R − 1 + 2k → v.left.head.focus ≠ none`（`leftRep` は番兵でも成立）

影響範囲（grep）: `.room` 18 箇所／6 ファイル、`.origin` の実消費は `GalilRoundPeriod:256` と
`CloseoutAdvanceT.period_at_next`、`CloseoutRoundUnique:72`。`CloseoutPackRun31`／
`CloseoutShiftRun`／`ShiftPalAlongTrace` は運ぶだけ。**作業量の問題。**

### 供給側の所在（一次情報）

* `BlockOn raw`（chain の窓）を produce するのは `CloseoutWatchRound48/50/53`・`GalilReplaySpan`
  だけ——**replay 生まれの chain の層**。
* 公理の起点 `InvLPS`（非 replay の found）側の landing は `CloseoutWatchPhase2.ShiftTailC`
  （`:225`）で、chain データは `WatchSegE` ＋ **DP の `GalilDpCorrect.Result`**（誕生時の
  `Candidate`、`x[cen] = cc` と `4h+1` の回文を含む）。走査に沿って伸びる窓は持っていない。

### 次の一手

1. **第 3 連言（`FreshShiftLedger`）を先に落とす**——左端でも真で、必要なのは
   `ChainW` 形の窓＋`x[cen] = cc`＋直前の回文だけ（`palNext_of_centre` の `i ≤ h` 部分＋
   `periodOn_mirror`＋`blockOn_succ_of_symbol`）。producer を書き、run 層の残差を
   「shift 入口で `ChainW` 形の窓を持つ」1 つに絞る。
2. 第 2 連言は `ShiftInv`/`RoundScan` の左端対応（上の 3 場の書き換え、7 ファイル）を
   済ませてから、`shiftInv_of_watch_entry`（n232）の左端版で再切り出す。

## n232 — 公理進捗: `ShiftInv` 23 場が 1 本の定理で出た（`shiftInv_of_watch_entry`）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 残差 `H_freshShiftAtShiftEntry` の中身 `∃ C R k, ShiftInv …` が、run 層の**一次事実だけ**から 1 本の定理で出るようになった（`ShiftPalAlongTrace.shiftInv_of_watch_entry`、標準公理のみ）。残るのはその一次事実を run 層から届ける配線（下の残差表） |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### 何を証明したか

`shiftInv_of_watch_entry` の入力（= `H_freshShiftAtShiftEntry` の producer が run 層に要求する残差）:

| 入力 | 内容 | 供給元（一次情報で確認したもの） |
|---|---|---|
| `hCW` | `GalilReplaySpan.ChainW raw cen (cen+R) (cen+R) bud lim cc b xs (.watch w)` | `CloseoutWatchRound42.LandingData` の第 2 成分（`E = R_chain = position t.right`） |
| `hpal` | `PalAt (encoded raw) cen R` | `LandingData` の `ScanInvariant.palindrome` |
| ヘッド 6 事実 | 比較後 `u.left`/`u.right` の `Represents`・存在・位置 `cen ∓ (R+1)` | `ScanInvariant` ＋ `scanFrame.compare`（`u.left = left s.left ∧ u.right = right s.right`）＋ `left_word`/`right_word`/`left_present`/`right_present` |
| `hmis` | `read u.left ≠ read u.right` | `Tick.scan_shift` の `¬ matched`（`Frame.pull scanLens` で `matched u = (read u.left = read u.right)`） |
| `hguard` `hpo` | `shiftGuardVM u`、`u.periodOnly = false` | `Tick.scan_shift` の `hg`／`H_freshShiftAtShiftEntry` の前提 |
| `hb` | `beginShiftVM (periodLength w) w u t` | `Tick.scan_shift` の `hb`（`beginShiftVM'`） |
| **`hcentre`** | **`(encoded raw)[cen]? = some cc`** | **窓に無い**。DP の `Candidate`（`GalilDpCorrect.lean:7`、`(w.take (2h+1)).reverse = w.take (2h+1)`）が誕生時に持つ静的事実。`LandingData` には**未記録** |

### 設計上の発見 3 つ（一次情報）

1. **窓は右ヘッドまでしか届かない。** `LandingData` の `ChainW` は `BlockOn … (cen+1) E` で
   `E = position t.right`。shift 判定はその右端で起きるので `coreX_next`/`coreX_good`
   （右に 1 歩の余裕を要求）は使えない。予測記号は `symbol_of_coreX`（境界自由版）で取り、
   `Good` は `shiftGuardVM` の最後の連言 `symbol focus = read s.right` から作る。
2. **`ScanInvariant` は不一致直後には成り立たない**（`palindrome` 場を持つ）。n214 の
   `shiftInv_frame_of_beginShift` は `beginShift` の源で `ScanInvariant` を取っていたので
   **使えない形だった**——削除し、ヘッドの 6 事実をばらして受け取る形にした。
3. **`palNext` の `i = h` は窓の外。** `PalAt (cen+h) (R+1−h)` の添字 `i = h` は
   `x[cen] = x[cen+2h]`、右辺は `bounce[2h−1] = cc` だが `x[cen]` は窓 `[cen+1, E]` に無い。
   n213 の `palNext_of_blockOn`（`anchor ≤ C + 1` を仮定）は**この窓では適用不能だった**
   ——削除し、`hcentre` を明示の入力にした `palNext_of_centre` に置き換えた。

### 削除した宣言（参照ゼロ・この窓では使えない形）

`palNext_of_blockOn`／`origin_of_blockOn`／`shiftInv_frame_of_beginShift`／
`periodLength_immediate_pos`／`size_of_margin`（n213〜n219）。いずれも真だが、
`LandingData` の窓（`cen+1` から）と不一致直後の状態には合わない仮定を置いていた。
代わりに `bounce_getElem?_symm`／`palNext_of_centre`／`blockOn_succ_of_symbol`／
`cells_run`／`periodLength_of_coreX` を入れた（全部 `shiftInv_of_watch_entry` が使う）。

### 次の一手（wrapper と、run 層の 2 残差）

`H_freshShiftAtShiftEntry centre place entry q first raw c s t` を
`LandingData raw R sT cc b xs c s` ＋ `ChainStep s.chain y → ChainW … y`（compare 量子の中で
chain は 1 歩進む: `ChainTick false x z := ∃ y, ChainStep x y ∧ z = y`）から出す wrapper を書く。
その wrapper が run 層に要求する新しい残差は 2 つだけ:

* **中心記号** `(encoded raw)[cen]? = some cc`（誕生時の `Candidate` から運ぶ）
* **左の余裕** `R + 2 ≤ cen`（左ヘッドが番兵に当たった不一致では `ShiftInv.room`/`leftPresent`
  が成り立たない。`CloseoutPackRun13.CentreMargin`（`r + pairOff c + 2 ≤ position s.center`）
  が意図された供給元）

通れば `roundScan_of_shiftInv` 経由で公理の第 1・第 3 連言が落ちる。

## n231 — 公理進捗: `ShiftInv` 23 場すべてに producer が揃った（`pred` 陥落）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 最後に残っていた `pred` 場が落ちた。`pred_immediate` は `aligned` 場も同時に出すので、**`ShiftInv` 23 場すべてに producer が存在する**状態になった（証明済み 21 / インライン 2） |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### `pred` の producer は既にあった

`pred : symbol w.machine.control.period.focus = (encoded raw)[C + R + 2]?` の攻略は、
**新しい数学ではなく既存部品 2 つの合成**だった。探し当てた一次情報は 2 つ:

| 部品 | 場所 | 内容 |
|---|---|---|
| `GalilScaffoldChainPrediction.successful_prediction` | `GalilScaffoldChainPrediction.lean:181` | `symbol (run (ready cc xs b) actual).period.focus = (bounce cc b xs)[actual.length % 2h]?`。探していた `run`/`bounce` 対応そのもの |
| `GalilReplaySpan.coreX_next` | `GalilReplaySpan.lean:166` | 上を `CoreX` の `pre` に適用済み。`symbol m.control.period.focus = bounce[(position m.verifier + 1 − anchor) % 2h]?` |

`BlockOn raw cc b xs anchor E` は**まさにその `bounce` 添字を encoded 語に戻す辞書**
（`∀ j, anchor + j ≤ E → (encoded raw)[anchor+j]? = bounce[j % 2h]?`）なので、窓の内側では

    symbol m.control.period.focus = (encoded raw)[position m.verifier + 1]?

が出る（`ShiftPalAlongTrace.pred_of_coreX`、6 行）。

### 窓の右端で判定が起きるので、`bounce` 添字のまま `2h` 戻す（訂正）

最初に書いた「`immediate` で予測を `C + R + 2h + 2` まで前へ伸ばし、`periodOn_of_blockOn` で
`2h` 戻す」経路は**使えない**。`LandingData`（`CloseoutWatchRound42.lean:128`）の窓は
`BlockOn … (C_chain+1) E` で `E = position t.right`——走査の右ヘッドちょうどまでしか届かず、
shift 判定はまさにその右端で起きる。`coreX_next` は `canRight` のために
`position ver + 1 < |encoded raw|` を要求するのでこれも使えない。

正しい経路（`ShiftPalAlongTrace.symbol_of_coreX` / `pred_immediate`、typecheck 済み・標準公理のみ）:

1. `symbol_of_coreX`: 予測記号は `CoreX` の `m.control = run (ready cc xs b) pre` と
   `successful_prediction` **だけ**で `bounce[(position ver + 1 − anchor) % 2h]?` と決まる
   （右端の余裕は不要）。
2. `Good w` は窓からではなく **`shiftGuardVM` の最後の連言**
   `symbol w.machine.control.period.focus = read s.right` から来る（窓が届かない場所で
   `Good` を供給するのが guard の役目という形）。`coreX_consume` で `CoreX (immediate w)`。
3. `bounce` の添字のまま 1 周期 `2h` 戻す: `BlockOn` は添字 `target − anchor` でも成立し、
   `(target − anchor + 2h) % 2h = (target − anchor) % 2h`（`Nat.add_mod_right`）。
   `target = C + R + 2 = position ver + 2 − 2h ≤ E` なので窓の内側。

**`pred_immediate` は結論に `aligned` 場（`position (immediate w).machine.verifier =
position w.machine.verifier + 1`、`right_position` ＋ `Good.1` の `canRight`）も含む。**

### 結果: `ShiftInv` 23 場の内訳

| 場 | producer |
|---|---|
| `chain` `remaining` `canon` `count` `leftRep` `leftPresent` `rightRep` `rightPresent` `leftPos` `rightPos` | `shiftInv_frame_of_beginShift`（n214） |
| `verifierRep` `verifierPresent` | `coreX_immediate`（n215） |
| `lagZero` `unbroken` | `immediate_lag_unbroken`（n216） |
| `posH` | `periodLength_immediate_pos`（n218） |
| `size` | `size_of_margin`（n219） |
| `pal` `palNext` `origin` | `palNext_of_blockOn` / `origin_of_blockOn`（n213） |
| **`aligned` `pred`** | **`pred_immediate`（このノート）** |
| `kle` `room` | 組み立て本体に直書き（n230） |

### 次の一手（組み立て）

残るのは 23 場を 1 本の `H_freshShiftAtShiftEntry` に束ねること。数値対応は確定している:

* `LagAt lag ver R := lag.neg = [] ∧ position ver + lag.pos.length = R`
  （`GalilReplayGeneral2.lean:179`）なので、lag ゼロなら `position w₀.machine.verifier = R_chain`。
  これが `pred_immediate` の `halign` 仮説に直接入る。
* `ChainW … (.watch w₀)` の 5 成分（`LagAt` / `BlockOn` / `CoreX` / `Canonical margin` /
  `value margin + 4·(|xs|+1) = R_chain − C_chain`）が、上の表の producer の入力を全部供給する。
* `ShiftInv` 側の `C = position u.center − h`、`R = r₀ − h − 1`、`h = |xs| + 1`、`k = 0`。

通れば `roundScan_of_shiftInv`（`CloseoutPackRun37.lean:95`）経由で
`obligation_shiftPalResiduesAlongRun` の第 1・第 3 連言が落ち、**公理が 3 → 2 本**になる。

## n230 — 公理進捗: 実質の残りは `pred` 1 場（`kle`/`room` はインライン）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 残り 3 場のうち **2 場（`kle` / `room`）は定理にする必要がない**と確定。実質の残りは `pred` 1 場 |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### `kle` と `room` はインラインで済む（定理を積まない）

* `kle : 0 ≤ h` — `Nat.zero_le`（`k = 0`）
* `room : R + 2 ≤ C` — `C = centre − h`、`R = r₀ − h − 1`、走査の位置境界
  `r₀ + 1 ≤ centre`（`ScanInvariant.leftPos` ＋ `represented_position` の `0 < left.length`）から
  `omega` 一発。実際 `R + 2 = r₀ − h + 1` と `C = centre − h ≥ r₀ + 1 − h` で等号ぎりぎり。

CLAUDE.md の「定理を無駄に積み上げるな」に従って、この 2 つは組み立て本体に直書きする。

### 残る 1 場 `pred` の形

`ShiftInv.pred : symbol (immediate w).machine.control.period.focus = (encoded raw)[C + R + 2]?`

`CloseoutAdvanceT.origin_prediction_wrap` / `GalilGoodLag.origin_prediction_index` は
どちらも `ReadOrigin` 経由（＝第 1 連言の結論 `ReadsInv` 由来）なので、
**`periodOnly = false` の最初の shift には使えへん**。

代わりの経路は `GalilReplaySpan.CoreX` の
`m.control = GalilScaffoldChainSweep.run (GalilScaffoldChainConsume.ready cc xs b) pre`
と `BlockOn raw cc b xs (C+1) E` の組み合わせ:

* `BlockOn` は `enc[anchor + j]? = (bounce cc b xs)[j % (2*(xs.length+1))]?`
* 必要なのは「`run (ready cc xs b) pre` の `period.focus` の記号」＝「ブロックの
  `pre.length % 2h` 番目」という対応

**次の一手はこの対応補題（`GalilScaffoldChainSweep.run` と `bounce` の関係）を探すこと。**
既存にあれば `pred` は即出る。無ければ書く。

### `ShiftInv`（23 場）の最終状況

| 状態 | 場数 |
|---|---|
| 証明済み | 20 |
| インラインで済む | 2（`kle` / `room`） |
| **残り** | **1（`pred`）** |
## n229 — 公理進捗: `ShiftInv` 23 場中 20 場（`size_of_margin`）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 第 2 連言 `ShiftInv` の `size : 2h ≤ R` が出た。**23 場中 20 場が証明済み**、残り 3 場 |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

```lean
theorem size_of_margin {h r₀ R : ℕ} {margin : GalilScaffoldCounter.Counter}
    (hcan : Canonical margin) (hneg : GalilScaffoldCounter.negative margin = false)
    (heq : value margin + 4 * (h : ℤ) = (r₀ : ℤ))
    (hR : R = r₀ - h - 1) (hp : 0 < h) : 2 * h ≤ R
```

`GalilReplaySpan.ChainW` の margin 等式 ＋ `shiftGuardVM` の非 `periodOnly` 枝
（`negative w.margin = false`）から `GalilScaffoldCounter.negative_iff` で
`0 ≤ value margin`、よって `4h ≤ r₀`。`ShiftInv` の `R = r₀ − h − 1` なので `2h ≤ R`。

**Scala の `canShift` の `margin.sign >= 0` 枝がここで効いてる。**

### `ShiftInv`（23 場）の到達状況

| 状態 | 場 |
|---|---|
| **証明済み 20** | 枠 10 ＋ `pal`/`palNext`/`origin` ＋ `verifierRep`/`verifierPresent`/`aligned` ＋ `lagZero`/`unbroken` ＋ `posH` ＋ `size` |
| 残り 3 | `kle : 0 ≤ h`（`Nat.zero_le`）`pred`（`CoreX` の `OnBlock` の展開）`room : R+2 ≤ C`（位置境界の算術） |

### セッション累計（この公理）

ガード追加 2・成分の語化 1・**成分削除 2**（`hEnd` / `hHi`）・**橋/producer 新設 10**
（`bal_of_count` / `periodOn_of_blockOn` / `palAt_next_of_period` / `palNext_of_blockOn` /
`origin_of_blockOn` / `shiftInv_frame_of_beginShift` / `coreX_immediate` /
`immediate_lag_unbroken` / `periodLength_immediate_pos` / `size_of_margin`）。
## n228 — 公理進捗: `ShiftInv` 23 場中 19 場（`periodLength_immediate_pos`）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 第 2 連言 `ShiftInv` の `posH` が出た。**23 場中 19 場が証明済み**、残り 4 場 |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

```lean
theorem periodLength_immediate_pos {w : GalilScaffoldChainWatch.State}
    (hb : GalilBranchInvariants.OnBlock w.machine.control.period)
    (hp : 0 < periodLength w) :
    0 < periodLength (GalilScaffoldChainWatch.immediate w)
```

`GalilChainCoupling.periodLength_consume` が「`OnBlock` の下で周期長は `consume` で不変」を
言うてて、その `OnBlock` は `GalilReplaySpan.CoreX` の第 1 成分やから
run が運ぶ `ChainW` からタダで出る。

### `ShiftInv`（23 場）の到達状況

| 状態 | 場 |
|---|---|
| **証明済み 19** | 枠 10（n224）＋ `pal`/`palNext`/`origin`（n222/n223）＋ `verifierRep`/`verifierPresent`/`aligned`（n226）＋ `lagZero`/`unbroken`（n227）＋ `posH`（本ノート） |
| 残り 4 | `kle : 0 ≤ h`（`Nat.zero_le`）`pred`（`CoreX` の `OnBlock` の展開）`size : 2h ≤ R`（margin 等式の算術）`room : R+2 ≤ C`（位置境界の算術） |

**数学は一つも残ってへん。**

### このセッションでこの公理に入れた変更（累計）

| 種類 | 件数 |
|---|---|
| ガード追加（過剰量化除去） | 2（`compareFound` / `shiftGuardVM`） |
| 成分の語化 | 1（`hCaught`） |
| **成分削除** | 2（`hEnd` / `hHi`） |
| **橋・producer 新設** | 9（`bal_of_count` / `periodOn_of_blockOn` / `palAt_next_of_period` / `palNext_of_blockOn` / `origin_of_blockOn` / `shiftInv_frame_of_beginShift` / `coreX_immediate` / `immediate_lag_unbroken` / `periodLength_immediate_pos`） |
## n227 — 公理進捗: `ShiftInv` 23 場中 18 場が証明済み（`immediate_lag_unbroken`）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 第 2 連言 `ShiftInv` の `lagZero` / `unbroken` が出た。**23 場中 18 場が証明済み**、残り 5 場 |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

```lean
theorem immediate_lag_unbroken {w : GalilScaffoldChainWatch.State} {a : Fin 3}
    (hlag : zero w.lag = true) (hbroken : w.machine.control.broken = false)
    (hsym : GalilScaffoldChainConsume.symbol w.machine.control.period.focus = some a)
    (hread : GalilScaffoldInputHead.read
      (GalilScaffoldChainVerifier.right w.machine.verifier) = some a) :
    zero (GalilScaffoldChainWatch.immediate w).lag = true ∧
      (GalilScaffoldChainWatch.immediate w).machine.control.broken = false
```

`immediate` は `lag` を触らんので `lagZero` は直。`unbroken` は
`GalilScaffoldChainVerifier.consume` が `GalilScaffoldChainConsume.consume` を呼ぶところで、
`shiftGuardVM` の**予測一致**（周期テープの focus と右ヘッドの読みが同じ）が
`consume_keeps_unbroken` の仮説をちょうど与える。
Scala の `chain.canShift && chain.prediction() == right.read()` がここで効いてる。

### `ShiftInv`（23 場）の到達状況

| 状態 | 場 |
|---|---|
| **証明済み 18** | 枠 10（n224）＋ `pal`/`palNext`/`origin`（n222/n223）＋ `verifierRep`/`verifierPresent`/`aligned`（n226）＋ `lagZero`/`unbroken`（本ノート） |
| 残り 5 | `kle`（自明）`posH`（`periodLength_consume`）`pred`（`CoreX` の `OnBlock`）`size`（margin 等式の算術）`room`（位置境界の算術） |
## n226 — 公理進捗: `ShiftInv` 23 場中 16 場が証明済み（`coreX_immediate`）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 第 2 連言 `ShiftInv` の `verifierRep` / `verifierPresent` / `aligned` が出た。**23 場中 16 場が証明済み**、残り 7 場 |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

```lean
theorem coreX_immediate
    (h : PalPeg.GalilReplaySpan.CoreX raw cc b xs anchor w.machine)
    (hc : GalilScaffoldChainVerifier.canRight w.machine.verifier) :
    Represents (GalilScaffoldChainWatch.immediate w).machine.verifier.head raw ∧
      (GalilScaffoldChainWatch.immediate w).machine.verifier.head.focus ≠ none ∧
      ∃ pre : List (Fin 3),
        position (GalilScaffoldChainWatch.immediate w).machine.verifier = anchor + pre.length
```

`GalilScaffoldChainVerifier.consume s = ⟨right s.verifier, …⟩` で verifier が 1 進むだけなので、
`BranchSupply.representsAfterRight_free`（**無条件**、`canRight` 不要）と
`right_position` でそのまま移る。

### `ShiftInv`（23 場）の到達状況

| 状態 | 場 |
|---|---|
| **証明済み 16** | 枠 10（n224）＋ `pal`/`palNext`/`origin`（n222/n223）＋ `verifierRep`/`verifierPresent`/`aligned`（本ノート） |
| 残り 7 | `kle`（自明）`posH`（自明）`lagZero`（ガード直読み）`unbroken`（ガード＋`consume_keeps_unbroken`）`pred`（`CoreX` の `OnBlock`）`size`（margin 等式の算術）`room`（位置境界の算術） |

**数学はもう一つも残ってへん。** 残り 7 場は自明・直読み・算術のみ。
## n225 — 公理進捗: `ShiftInv` 23 場すべてに出所が確定（残りは組み立てのみ）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 第 2 連言 `ShiftInv` の **23 場すべてに具体的な出所が確定**。13 場は証明済み、残り 10 場も既存部品か `ChainW` の成分から出る |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### `GalilReplaySpan.ChainW` の `.watch` 枝（一次情報、:318）

```lean
| .watch w => LagAt w.lag w.machine.verifier R ∧ BlockOn raw cc b xs (C+1) E ∧
    CoreX raw cc b xs (C+1) w.machine ∧ Canonical w.margin ∧
    value w.margin + 4 * ((xs.length + 1 : ℕ) : ℤ) = (R : ℤ) - C ∧
    (lim = true → w.lag.pos.length ≤ bud)
```

### `ShiftInv`（23 場）の対応表

| 場 | 出所 | 状態 |
|---|---|---|
| `chain` `remaining` `canon` `count` `leftRep` `leftPresent` `rightRep` `rightPresent` `leftPos` `rightPos` | `shiftInv_frame_of_beginShift`（n224） | **済** |
| `pal` | `ScanInvariant.palindrome` | **済** |
| `palNext` | `palNext_of_blockOn`（n222） | **済** |
| `origin` | `origin_of_blockOn`（n223） | **済** |
| `kle : 0 ≤ h` | 自明（`k = 0`） | 部品済 |
| `lagZero` | `shiftGuardVM` の `zero w.lag = true`（`immediate` は lag を触らん） | 部品済 |
| `unbroken` | `shiftGuardVM` の `broken = false` ＋ `GalilGoodLag.consume_keeps_unbroken` | 部品済 |
| `verifierRep` `verifierPresent` | `BranchSupply.chainVerifierRepresents_immediate` | 部品済 |
| `posH : 0 < h` | `h = xs.length + 1 ≥ 1`（自明） | 部品済 |
| `size : 2h ≤ R` | `ChainW` の margin 等式 ＋ ガードの `negative margin = false` ⇒ `4h ≤ R − C` | 部品済 |
| `aligned` | `ChainW` の `LagAt w.lag w.machine.verifier R` | 部品済 |
| `pred` | `ChainW` の `CoreX`（周期テープの中身） | 部品済 |
| `room : R + 2 ≤ C` | 走査の位置境界（`position s.left ≥ 1`）＋ `C = position s.center − h`, `R = r₀ − h − 1` | 部品済 |

**未知の箱ゼロ・未知の数学ゼロ・producer 不明の場ゼロ。** 残るのは 23 場を 1 本の定理に
組み上げる作業だけ。組み上がれば `roundScan_of_shiftInv` 経由で第 1・第 3 連言も落ちて、
**`obligation_shiftPalResiduesAlongRun` が公理でなくなる**。
## n224 — 公理進捗: `ShiftInv` の枠 10 場も出た（残り 10 場）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 第 2 連言 `ShiftInv`（23 場）のうち **13 場が出た**（実質 3 場 ＋ 枠 10 場）。残り 10 場 |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

```lean
theorem shiftInv_frame_of_beginShift
    (hb : beginShiftVM h w s t)
    (hi : ScanInvariant raw (position s.center) r₀ s.left s.right) :
    t.chain = ChainVM.watch (GalilScaffoldChainWatch.immediate w) ∧
      t.remaining = ofNat h ∧ Canonical t.cycle ∧ value t.cycle = 0 ∧
      Represents t.left.head raw ∧ t.left.head.focus ≠ none ∧
      Represents t.right.head raw ∧ t.right.head.focus ≠ none ∧
      position t.left = position s.center - r₀ ∧ position t.right = position s.center + r₀
```

証明は `rw [hb.2]` の後ぜんぶ `rfl` か `hi` の場。`beginShiftVM` が着地状態を等式
`t = {s with remaining := ofNat h, chain := .watch (immediate w), cycle := reset, …}` で
与えるので、**`k = 0` での `remaining = ofNat (h−0)` と `count = 2*0` がちょうど合う**。

### `ShiftInv`（23 場）の到達状況

| 群 | 場 | 状態 |
|---|---|---|
| 実質 | `pal` / `palNext` / `origin` | **済**（n222/n223） |
| 枠（chain/counter/head） | `chain` `remaining` `canon` `count` `leftRep` `leftPresent` `rightRep` `rightPresent` `leftPos` `rightPos` | **済**（本ノート） |
| 残り 10 | `kle` `posH` `size` `room` `verifierRep` `verifierPresent` `aligned` `lagZero` `unbroken` `pred` | 未 |

残り 10 場の見通し（すべて出所は特定済み）:

* `kle : 0 ≤ h` — 自明
* `lagZero` — `shiftGuardVM` の `zero w.lag = true`（`immediate` は lag を触らん）
* `pred` — `shiftGuardVM` の symbol 場
* `unbroken` — `shiftGuardVM` の `broken = false` ＋ `consume_keeps_unbroken`
* `verifierRep` — `BranchSupply.chainVerifierRepresents_immediate` が実在
* `posH` / `size` / `room` — `ChainW` の margin 等式と `phase = 4`、走査の `room`
* `aligned` — `immediate` が verifier を 1 進めることと lag 0 の整合
## n223 — 公理進捗: `ShiftInv` の実質 3 場すべてが機械側データから出るようになった

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 第 2 連言 `ShiftInv` の**実質 3 場（`pal` / `palNext` / `origin`）すべて**が run の運ぶデータから出る。**数学の部分は完了**、残るは枠 15 場と区間の合わせ込み |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### 書いたもの

```lean
theorem origin_of_blockOn
    (hblk : PalPeg.GalilReplaySpan.BlockOn raw cc b xs anchor E)
    (hmis : (encoded raw)[C - R - 1]? ≠ (encoded raw)[C + R + 1]?)
    (hanchor : anchor ≤ C + R + 1)
    (hend : C + R + 2 * (xs.length + 1) + 1 ≤ E) :
    (encoded raw)[C - R - 1]? ≠ (encoded raw)[C + R + 2 * (xs.length + 1) + 1]?
```

走査が伸びへんかった事実（shift 遷移の `¬ matched`）が不一致を与え、`BlockOn` の周期が
右添字 `C+R+1` と `C+R+2h+1` を同一視するので、不一致がそのまま移る。

### `ShiftInv`（19 場）の到達状況

| 場 | 供給 | 状態 |
|---|---|---|
| `pal : PalAt (C+h) (R+h)` | `ScanInvariant.palindrome` そのもの | 済 |
| `palNext : PalAt (C+2h) (R+1)` | `palNext_of_blockOn`（n222） | 済 |
| `origin` | `origin_of_blockOn`（本ノート） | 済 |
| 枠 15 場 | `beginShiftVM` の等式 `t = {s with …}` から `s` の不変量を書き写す | 未 |

**数学は全部片付いた。** 残るのは機械的な書き写しと、区間の合わせ込み
（`anchor ≤ …` / `… ≤ E`、`ChainW` の `anchor = position t.center + 1`、
`E = position sT.right + R_land`）だけ。

このセッションで `obligation_shiftPalResiduesAlongRun` に入れた変更:
ガード追加 2（n211/n212）・成分の語化 1（n213）・**成分削除 2**（n214 `hEnd`、n217 `hHi`）・
**橋/producer 新設 4**（n219 `periodOn_of_blockOn`、n221 `palAt_next_of_period`、
n222 `palNext_of_blockOn`、n223 `origin_of_blockOn`）。
## n222 — 公理進捗: `ShiftInv.palNext` を機械側データから出す橋（`palNext_of_blockOn`）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 第 2 連言 `ShiftInv` の `palNext` が、run が運ぶ `ChainW` の `BlockOn` と走査不変量の回文から**直接出る**ようになった。数学の残りはゼロ、残るは区間の合わせ込み |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

```lean
theorem palNext_of_blockOn
    (hblk : PalPeg.GalilReplaySpan.BlockOn raw cc b xs anchor E)
    (hpal : Manacher.PalAt (encoded raw) (C + (xs.length + 1)) (R + (xs.length + 1)))
    (hanchor : anchor ≤ C + 1)
    (hend : C + 2 * (xs.length + 1) + R + 1 ≤ E)
    (hlen : C + 2 * (xs.length + 1) + (R + 1) < (encoded raw).length) :
    Manacher.PalAt (encoded raw) (C + 2 * (xs.length + 1)) (R + 1)
```

`periodOn_of_blockOn`（n219）で周期にし、`palAt_next_of_period`（n221）で回文を伸ばすだけ。
**残る仮説は区間の合わせ込み 2 本（`anchor ≤ C+1` / `C+2h+R+1 ≤ E`）と長さ 1 本。**

### `ShiftInv`（19 場）の到達状況

| 場 | 状態 |
|---|---|
| `pal` | `ScanInvariant.palindrome` そのもの |
| `palNext` | **`palNext_of_blockOn`（本ノート）で機械側から出る** |
| `origin` | `¬ matched` ＋ 周期で添字を戻す（未着手） |
| 枠 15 場 | `beginShiftVM` が `t` を完全決定（`k = 0`、`wch = immediate w`）。未着手 |

証人は計算済み: `C = position s.center − h`、`R = r₀ − h − 1`、`k = 0`。
## n221 — 公理進捗: `ShiftInv.palNext` の producer を書いた（実質 3 場すべてに producer）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 梃子の第 2 連言 `ShiftInv` の `palNext` に **producer が付いた**。これで実質 3 場すべてが埋まる目処 |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### 書いたもの

```lean
theorem palAt_next_of_period {x : List α} {C R h : ℕ}
    (hpal : Manacher.PalAt x (C + h) (R + h)) (hp : 0 < h)
    (hlen : C + 2 * h + (R + 1) < x.length)
    (hper : PeriodOn x (2 * h) C (C + 2 * h + R + 1)) :
    Manacher.PalAt x (C + 2 * h) (R + 1)
```

構成は 2 行の事実だけ:

* 左側 — `C+h` を軸にした鏡映で `x[C+2h−i]? = x[C+i]?`（`i ≤ h` と `i > h` の両方で同じ結論）
* 右側 — 周期 1 歩で `x[C+i]? = x[C+i+2h]?`

`Manacher.palAt_succ_iff` も `palAt_shift_of_period` も要らんかった。半径 `R+1` を直接構成できる。
入力の `hper` は n219 の `periodOn_of_blockOn` が `ChainW` の `BlockOn` から供給する。

### `ShiftInv`（19 場）の供給状況

| 場 | 供給 |
|---|---|
| `pal : PalAt (C+h) (R+h)` | `ScanInvariant.palindrome` そのもの（添字書き換えのみ） |
| `palNext : PalAt (C+2h) (R+1)` | **`palAt_next_of_period`（本ノート）** |
| `origin : enc[C−R−1]? ≠ enc[C+R+2h+1]?` | shift 遷移の `hmt : ¬ matched u`（走査が伸びへんかった）＋ 周期 `2h` で右添字を `C+R+1` に戻す。`RoundScan.origin` と同値 |
| 枠 15 場 | `beginShiftVM` の遷移から計算 |

**未知の数学は残ってへん。残りは配線の作業量だけ。**
## n220 — 公理進捗: 第 2 連言 `ShiftInv` の実質 3 場すべてに供給元が付いた

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 梃子である第 2 連言 `ShiftInv` の**実質 3 場すべてに供給元が確定**。未知の数学ゼロ |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### `ShiftInv`（19 場）の内訳

| 場 | 供給元 |
|---|---|
| `pal : PalAt (encoded raw) (C+h) (R+h)` | **`ScanInvariant.palindrome` そのもの**。`CloseoutAdvanceT:146` と `CloseoutPackRun31:167` はどちらも `hI.caught.scan.palindrome` を `R + 1 - h + used = R + h` で書き換えてるだけ。新しい数学ゼロ |
| `palNext : PalAt (encoded raw) (C+2h) (R+1)` | `palAt_shift_of_period` が `pal` ＋ 周期 `2h` から `PalAt (C+2h) R` を出す。**足りん 1 箇所**は Scala の shift 条件の後半 `chain.prediction() == right.read()`（Lean では `shiftGuardVM` の `symbol …period.focus = read s.right`）が与える |
| `origin : enc[C−R−1]? ≠ enc[C+R+2h+1]?` | scan の不一致（`RoundScan.origin` と同型） |
| 枠 15 場 | `beginShiftVM` の遷移から計算 |

周期 `2h` は n219 で架けた `periodOn_of_blockOn` が `ChainW` の `BlockOn` から供給する。

### 注意（消費者と producer の取り違えを 1 件回避）

`CloseoutAdvanceT.period_at_next:95` は `pal` と `palNext` を**両方取って**予測添字の等式を出す
**消費者**であって、`palNext` の producer やない。署名を読んで気づいた。

### 公理全体の絵（確定版）

```
CloseoutWatchRound43.ChainWRun（run が運ぶ）
  → GalilReplaySpan.ChainW (.watch) = BlockOn + CoreX + margin 等式
  → periodOn_of_blockOn（n219）→ PeriodOn (2h)
  ＋ ScanInvariant.palindrome（run が InvLPC で運ぶ）
  ＋ shiftGuardVM の予測場
  → ShiftInv（第 2 連言）
  → roundScan_of_shiftInv → RoundScan
       ├→ 第 1 連言 H_readsShift のガード
       └→ 第 3 連言 FreshShiftLedger の 5 成分
```

**未知の箱も未知の数学も無い。残りは配線の作業量だけ。**
## n219 — 公理進捗: `BlockOn → PeriodOn` の橋を架けた（`hLeft` の供給経路が通った）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 第 3 連言の成分 `hLeft` を、run が実際に運んでるデータから供給する橋が架かった |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### 架けた橋

```lean
theorem periodOn_of_blockOn {raw : List (Fin 2)} {cc b : Fin 3} {xs : List (Fin 3)}
    {anchor E : ℕ} (h : PalPeg.GalilReplaySpan.BlockOn raw cc b xs anchor E) :
    PeriodOn (encoded raw) (2 * (xs.length + 1)) anchor E
```

`BlockOn raw cc b xs anchor E := ∀ j, anchor + j ≤ E →
  (encoded raw)[anchor + j]? = (bounce cc b xs)[j % (2 * (xs.length + 1))]?`
は「入力の `[anchor, E]` が長さ `2h` のブロックの巡回」。周期の形に直すだけ（`Nat.add_mod_right`）。

**これが無かったせいで、`ChainW` が運ぶ `BlockOn` と第 3 連言の `hLeft` が繋がってへんかった。**
`grep` で確認したとおり `BlockOn` から `PeriodOn` を出す補題は存在せえへんかった。

### 供給経路（これで通った）

```
CloseoutWatchRound43.ChainWRun（run が運ぶ）
  → GalilReplaySpan.ChainW (.watch 枝) → BlockOn raw cc b xs (C+1) E
  → periodOn_of_blockOn（本ノート）
  → PeriodOn (encoded w) (2h) (C+1) E
  → .mono → hLeft : PeriodOn (encoded w) (2h) (c−r₀) c
```

残るのは区間の合わせ込み（`C+1 ≤ c − r₀` と `c ≤ E`）だけ。

### ビルド確認の注意（再確認）

バックグラウンドの通知は `failed`／`exit code 1` やったが、これは末尾の
`grep -c "error"` が 0 件で返した終了コードで、ビルドの結果やない。
`BUILD=` 行は `0`、エラー 0。**CLAUDE.md の「`BUILD=` 行だけを信じる」規律どおり。**

### 次

`ShiftInv` の `pal : PalAt (C+h) (R+h)` / `palNext : PalAt (C+2h) (R+1)` は、
既存の `periodOn_span_of_next`（`GalilLiveCentreLife:179`、`GalilRoundsLeftmost:120`、
`GalilCycleFoundBackground:260` で使用実績あり）と `palAt_shift_of_period` で
周期から回文を伸ばす形。材料は揃ってる。
## n218 — 公理進捗: `obligation_shiftPalResiduesAlongRun` の供給鎖が全部繋がった

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 3 連言すべての**供給元が名前付きで確定**。未知の箱ゼロ。残るは配線作業 |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### 供給鎖（すべて一次情報で確認）

```
CloseoutWatchRound43.ChainWRun（run に沿って ChainW を運ぶ。:140/:202 で
  ChainW raw (position t.center) (position sT.right + R) (position t.right) … を確立）
  ↓
GalilReplaySpan.ChainW … (.watch w) :318
  = LagAt ∧ BlockOn raw cc b xs (C+1) E ∧ CoreX raw cc b xs (C+1) w.machine
    ∧ Canonical w.margin ∧ value w.margin + 4*(xs.length+1) = R − C
  ↓
第 2 連言 H_freshShiftAtShiftEntry → ShiftInv（CloseoutPackRun37:59、19 場）
  実質は pal : PalAt (C+h) (R+h) / palNext : PalAt (C+2h) (R+1) /
  origin : enc[C−R−1]? ≠ enc[C+R+2h+1]? の 3 場。残り 15 場は beginShiftVM が決める枠
  ↓
CloseoutPackRun37.roundScan_of_shiftInv:96 → RoundScan
  ├→ 第 1 連言 H_readsShift のガードそのもの（periodOnly = true 相）
  └→ 第 3 連言 FreshShiftLedger の 5 成分（periodOnly = false 相）
        posH = hPos / pred = hCaught / size + phase = hLo /
        pal + (ReadsInv → ReadOrigin → GalilOriginPeriod.origin_periodOn) = hIn, hLeft
```

### 相の対応（Scala 正本）

`ScaffoldChain.beginShift()` が `periodOnly = true` にするので

* 第 3 連言 = `periodOnly = false` = **最初の** shift（`canShift` の `margin.sign >= 0` 枝）
* 第 1 連言 = `periodOnly = true` = **2 回目以降**（`cycleEnd` 枝）
* `ChainRound`（`periodOnly = true` ガード）は最初の shift には使えへん。
  だから第 2 連言が独立した名前付き残差になってる

### `hLo` の源も確定

`ChainW` の margin 等式 `value w.margin + 4*(xs.length+1) = R − C` に
`shiftGuardVM` の `negative w.margin = false` を合わせると `4h ≤ R − C`。
`RoundScan` 側の `size : 2h ≤ R` と `phase = 4` と整合する。

### 残り

配線 3 本:
1. `ChainWRun` → shift 入口の `ChainW`（`periodOnly = false`）
2. `ChainW` の `BlockOn`/`CoreX`/margin 等式 → `ShiftInv` の `pal`/`palNext`/`origin`
3. `ShiftInv` の枠 15 場 → `beginShiftVM` の遷移から計算
## n217 — 公理進捗: 仕様に無い前提 `hHi` を除去（第 3 連言 6 → 5 成分）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 第 3 連言から **`hHi : r₀ ≤ 4h` を除去**。成分 6 → 5。しかも `hHi` は `RoundScan` の場の算術だけで矛盾する（下記） |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

### 何を替えたか

| 旧 | 新 |
|---|---|
| `hOut : PalAt (encoded w) (c−2h) (2h)` | `hLeft : PeriodOn (encoded w) (2h) (c−r₀) c` |
| `hHi : r₀ ≤ 4h` | **削除** |

語の補題側は `GalilPeriodUnion.reshift_of_palAt_period` として切り出した。
`periodOn_mirror' hcur hLo hLeft` が直接 `PeriodOn (2h) c (c+r₀)` を出すので `hHi` が要らん。
旧 `reshift_of_palAt_pair` は `phase = 4` 特化の系として残した（`r ≤ 4h` 付き）。

### 根拠（Scala 正本）

`ScaffoldChain.consume()` は**マッチ 1 箇所ごと**に呼ばれ、`distance.inc()` し、
周期境界で `phase = math.min(4, phase + 1)`。つまり検証済み周期区間は固定の `4h` やのうて
**走査半径と一緒に伸びる**。`canShift` は `r₀ ≤ 4h` をどこにも検査してへん。

### `hHi` が偽である算術（`RoundScan` の場から）

`GalilRoundPeriod.RoundScan raw C R h used v w` は
`caught : CaughtScan raw (C + h) (R + 1 - h + used) …` を持つので、
`FreshShiftLedger` の `c = C + h`、`r₀ = R + 1 - h + used`。

* `hLo : 2h ≤ r₀` ⟺ `3h ≤ R + 1 + used` ← `phase = 4`（`4h ≤ R`）から出る
* `hHi : r₀ ≤ 4h` ⟺ `R ≤ 5h − 1 − used`。`fresh : used < 2h` で `used` は `2h` 近くまで伸びるので、
  `R ≥ 4h` と**両立せえへん**

機械検査した反証はまだ書いてへんので `REFUTED` とは書かへん。

### 残り 5 成分と `RoundScan` の場の対応

| 成分 | `RoundScan` 側 |
|---|---|
| `hPos : 0 < h` | **`posH` そのもの** |
| `hCaught` | **`pred` の内容そのもの** |
| `hLo : 2h ≤ r₀` | `size` ＋ `phase = 4` |
| `hIn` / `hLeft` | `pal : PalAt (encoded raw) C R` ＋ `ReadsInv → ReadOrigin → origin_periodOn` |

`RoundScan` は**同じ公理の第 1 連言 `H_readsShift` のガード**や。
つまり第 3 連言の残差は新しい数学やのうて、第 1 連言が既に持ってる情報の再配線。
**第 1 と第 3 は同じ材料の上に載ってる。**

### 3 連言は独立やない（本ノート最大の発見）

`CloseoutPackRun37.roundScan_of_shiftInv:96`（「at exhaustion (`k = h`) the datum *is* the `RoundScan`」）が
`ShiftInv → RoundScan` を与える。そして `ShiftInv` は**第 2 連言 `H_freshShiftAtShiftEntry` の結論**。

```
第 2 連言 (H_freshShiftAtShiftEntry) → ShiftInv
  → roundScan_of_shiftInv → RoundScan
       ├→ 第 1 連言 (H_readsShift) のガードそのもの
       └→ 第 3 連言 (FreshShiftLedger) の 5 成分に対応する場
             posH = hPos / pred = hCaught / size + phase = hLo /
             pal + (ReadsInv → ReadOrigin → origin_periodOn) = hIn, hLeft
```

**`obligation_shiftPalResiduesAlongRun` の 3 連言は 1 本の鎖に載ってる。**
第 2 連言が、他の 2 つが消費するデータ（`RoundScan`）を作る側や。
よって梃子は第 2 連言 `H_freshShiftAtShiftEntry`（`∃ C R k, ShiftInv w C R (periodLength wch) k t wch`）で、
そのガードは `mode = scan ∧ replaying = false ∧ clock = 1 ∧ periodOnly = false ∧ shift 遷移の存在` と十分狭い。

相の対応:
* 第 3 連言 = `periodOnly = false` = **最初の** shift（`canShift` の `margin.sign >= 0` 枝）
* 第 1 連言 = `periodOnly = true` = **2 回目以降**（`cycleEnd` 枝）
## n216 — 公理進捗: `hHi` は仕様に無い前提（形式化のミスを確定）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 第 3 連言の 5 残差のうち **`hHi : r₀ ≤ 4h` が仕様に存在しない前提**だと確定。切り直しの対象が名指しされた |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### 一次情報（Scala 正本）

`scala/pal/src/main/scala/pal/ScaffoldChain.scala`:

```scala
/** Whether four verified semiperiods permit a chain shift now. */
def canShift: Boolean = {
  val ready = mode == Mode.Watch && lag.sign == 0 && phase == 4
  ready && (if (periodOnly) { cycleEnd } else { margin.sign >= 0 })
}
```

`ScaffoldGalil.scala:270` は `!replaying && chain.canShift && chain.prediction() == right.read()` で shift する。

* `phase == 4`（four verified semiperiods）＝ `hIn`/`hOut`（`[C−4h, C]` 上の周期）**そのもの**
* `lag.sign == 0` ＝ `shiftGuardVM` の `zero lag = true`
* `margin.sign >= 0` ＝ `4h ≤ radius + count`（`GalilScaffoldChainReady:26` の
  `value final.margin = value radius − 4h + count`）——**`hHi` と逆向き**
* `cycleEnd` ＝ `singlePositive cycle`

**`canShift` は `r₀ ≤ 4h` をどこにも検査してへん。** Lean 側でも `r ≤ 4 * …` は
`ShiftPalAlongTrace`（本件）と `GalilSourceCost.move_cost` の **2 箇所で仮定されるだけ**で、
producer はゼロ。常設制約「producerがないときは確実に形式化ミス」で確定。

### どこを切り直すか

`hHi` は `GalilPeriodUnion.periodOn_right_of_palAt_pair` の
`PeriodOn word (2h) C (C + r)` を出すためだけに要る。中身は
「`hIn`/`hOut` が与える `[C−4h, C]` の周期を、`hcur`（中心 `C` 半径 `r`）で鏡映して右へ移す」で、
鏡映が届くのに `r ≤ 4h` が要る。`r > 4h` のときは `[C, C+4h]` までしか出えへん。

よって切り直しの候補は 2 つ:

1. `periodOn_right_of_palAt_pair` の結論を `PeriodOn word (2h) C (C + min r (4h))` に弱め、
   `reshift_of_palAt_pair` 側で `j + 2h ≤ C + r` の場合分けを `min` に合わせる
2. `r ≤ 4h` を機械が本当に保証する形（`margin`／`phase` から出る形）に置き換える

**次のティックで 1 を試す**（語の補題側の作業で、機械側の新しい不変量を要求せえへん）。

### 残差の現状（第 3 連言）

| 成分 | 状態 |
|---|---|
| `hIn` / `hOut` | `phase == 4` に対応。周期テープの中身（DP の `Candidate`） |
| `hPos` | `periodLength_watchControl_pos` が実在 |
| `hLo` | `CloseoutLPack` 系が場として運ぶ |
| `hHi` | **仕様に無い。切り直し対象（本ノート）** |
## n215 — 公理進捗: 第 3 連言が「証明済みの語の補題の 5 仮説」に一致した

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 第 3 連言 `FreshShiftLedger` が `GalilPeriodUnion.reshift_of_palAt_pair`（**証明済み**）の残り 5 仮説とちょうど一致する形になった。供給元を 5 本とも名指しした |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### 到達点

`ShiftPalAlongTrace.shiftPalAt_fresh_of_candidate` の核は

```lean
PalPeg.reshift_of_palAt_pair (encoded w) (position s.center) h r₀
  hIn hOut hScanInv.palindrome hPos hLo hHi hEnd hpredIdx
```

で、`reshift_of_palAt_pair`（`GalilPeriodUnion:218`）は**既に証明されてる純粋な語の補題**。
n213/n214 で

* `hcur` ← `hScanInv.palindrome`（元から無料）
* `hend` ← `hCan` から導出（n214、成分から除去）
* `hpred` ← `shiftGuardVM` ＋ `right_read_index` で語の言明に（n213）

を片付けたので、**`FreshShiftLedger` の残りはちょうど `reshift_of_palAt_pair` の 5 仮説**:

| 成分 | 内容 | 供給元 |
|---|---|---|
| `hIn` | `PalAt (encoded w) (c−h) h` | 周期テープの中身（DP の `Candidate` 由来） |
| `hOut` | `PalAt (encoded w) (c−2h) (2h)` | 同上 |
| `hPos` | `0 < periodLength wch` | **`CloseoutWatchShiftAudit.periodLength_watchControl_pos` が実在**（`backDone` 生まれの watch 用） |
| `hLo` | `2h ≤ r₀` | `CloseoutLPack` 系が場として運ぶ（`shiftBud_of_scanInv` は逆に仮説で取ってる＝消費者） |
| `hHi` | `r₀ ≤ 4h` | **producer 見つからず** |

### `hHi` は形式化のミスの疑い（producer ゼロ）

`grep "≤ 4 \* periodLength"` の結果は `ShiftPalAlongTrace` 自身以外ゼロ。
逆向きなら `CloseoutPackRun40:249` に `4 * (periodLength w : ℤ) ≤ value s.radius + 1` がある。
常設制約「producerがないときは確実に形式化ミス」に従えば、`hHi` は切り方が間違ってる。
`reshift_of_palAt_pair` 側で `hle : r ≤ 4 * h` は `periodOn_right_of_palAt_pair` にだけ使われてるので、
そこを機械が実際に持ってる向き（`4h ≤ r + 1`）で通せるかを次に見る。

### 次の一手

1. `periodOn_right_of_palAt_pair` の `hle` を機械の持つ向きに合わせられるか（`hHi` の切り直し）
2. `hPos`: 「shift 相の watch は `backDone` 生まれ」を run から取る配線
3. `hLo`: `LPack` 系の場を shift 相まで運ぶ配線
## n214 — 公理進捗: `FreshShiftLedger` の成分を 7 → 6 に減らした（`hEnd` 除去）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 第 3 連言 `FreshShiftLedger` の**成分が 1 本消えた**（7 → 6） |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### 消した成分

`hEnd : position s.center + r₀ + 1 < (encoded w).length`

消費者 `shiftPal_of_freshShiftLedger` は `hCan : canRight s.right` を持ってる。
右ヘッドが右に動けるということは、その先に記号が実在するということ:

```lean
right_word / right_present  → (right s.right).head は raw を表現し focus ≠ none
represented_position        → 長さの下界・上界
right_position              → position (right s.right) = position s.right + 1
hScanInv.rightPos           → position s.right = position s.center + r₀
```

`scan_initial` が同じ手順で `position p < (encoded raw).length` を出してたので、それをなぞっただけ。
**新規補題ゼロ。**

### `FreshShiftLedger` の残り 6 成分

| 成分 | 形 |
|---|---|
| `hIn` | `PalAt (encoded w) (c − h) h` — 語のみ |
| `hOut` | `PalAt (encoded w) (c − 2h) (2h)` — 語のみ |
| `hPos` | `0 < periodLength wch` — 機械 |
| `hLo` | `2h ≤ r₀` — 機械と語の橋 |
| `hHi` | `r₀ ≤ 4h` — 機械と語の橋 |
| `hCaught` | `enc[c+r₀+1−2h]? = enc[c+r₀+1]?` — 語のみ（n213） |

6 成分中 3 つが語だけ。n210 以降この公理に入れた変更は
**ガード 2 本追加（n211/n212）→ 機械の状態を 1 成分から除去（n213）→ 成分 1 本除去（n214）**。
## n213 — 公理進捗: `FreshShiftLedger` の `hCaught` から機械の状態を消した

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 第 3 連言 `FreshShiftLedger` の 7 成分目 `hCaught` が**純粋な語の言明**になった |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### 書く前に止めた誤り

`hCaught` を `hIn`/`hOut` から導けると見込んだが、`span_hasPeriod_of_two_palAt` の結論は
span `[c−4h, c]` 上の周期で、`hCaught` が触る `c+r₀+1`（`r₀ ≥ 2h`）は**その外**やった。
補題を書く前に定義を読んで気づいた。

### 代わりにやったこと（機械 → 語）

旧:
```lean
(encoded w)[c + r₀ + 1 - 2h]? = GalilScaffoldChainConsume.symbol wch.machine.control.period.focus
```
新:
```lean
(encoded w)[c + r₀ + 1 - 2h]? = (encoded w)[c + r₀ + 1]?
```

導出（`shiftPal_of_freshShiftLedger` 内、新規補題ゼロ）:
* `shiftGuardVM s'` の `hsym` : `symbol wch…focus = read s'.right`
* `hRight` : `s'.right = right s.right`
* `GalilRoundPeriod.right_read_index` : `read (right q) = (encoded w)[position q + 1]?`
* `hScanInv.rightPos` : `position s.right = c + r₀`

**帰結: 残差から機械の周期テープが消え、`encoded w` の周期性という語だけの言明になった。**
これで `Manacher` / `GalilPeriodUnion` / `Words` 層が直接攻められる。
n212 で入れた `shiftGuardVM` ガードが無ければこの書き換えはできひんかった。

### 残り 7 成分の現状

| 成分 | 形 |
|---|---|
| `hIn` / `hOut` | `PalAt` 2 本（語のみ） |
| `hPos` | `0 < periodLength wch`（機械） |
| `hLo` / `hHi` | `2h ≤ r₀ ≤ 4h`（機械と語の橋） |
| `hEnd` | `c + r₀ + 1 < (encoded w).length`（語のみ。`hScanInv.palindrome` が `c + r₀ < length` を与えるので **1 つ違い**） |
| `hCaught` | **語のみになった（本ノート）** |

7 成分中 4 つが語だけの言明になった。
## n212 — 公理進捗: `obligation_shiftPalResiduesAlongRun` 第 3 連言を 2 段階弱めた

**公理への進捗（これを毎回書く）**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 第 3 連言 `FreshShiftLedger` に **2 本のガードを追加**（`compareFound` / `shiftGuardVM`）。真に弱くなった |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### 何を弱めたか

旧（n210 時点）:
```lean
z.vm.periodOnly = false → ∀ s' : GalilVM, FreshShiftLedger w z.vm s'
FreshShiftLedger w s s' := ∀ wch, s'.chain = watch wch → ∀ r₀, ScanInvariant … → (7 成分)
```

新:
```lean
z.vm.periodOnly = false → ∀ s' : GalilVM,
  compareFound (PofC centreC placeC entry w) q first z.vm s' → FreshShiftLedger w z.vm s'
FreshShiftLedger w s s' := shiftGuardVM s' →
  ∀ wch, s'.chain = watch wch → ∀ r₀, ScanInvariant … → (7 成分)
```

根拠（一次情報、`ShiftPalAlongTrace.shiftPal_of_freshShiftLedger:186` の本体）:
```lean
intro s' hCompare hNotMatched wch hChain hGuard r₀ hScanInv
```
消費者は `hCompare`（`compareFound … s s'`）と `hGuard`（`shiftGuardVM s'`）を**両方持ってる**のに、
`FreshShiftLedger` はどちらもガードに入れてへんかった。CLAUDE.md の過剰量化の型そのもの。

効果: `wch`（周期テープ）が任意でなく `s'` の chain に、さらに `s'` が `s` の実際の比較先に縛られた。
旧形は任意の `wch` に対し `2·periodLength wch ≤ r₀ ≤ 4·periodLength wch` を主張してて、
`p` を大きく取れば破れる形やった。

### 次の一手（残り 7 成分のうち `hCaught` を消す）

`shiftGuardVM` は `symbol wch.machine.control.period.focus = read s'.right` を持ち、
`shiftPalAt_fresh_of_candidate` は `hRight : s'.right = right s.right` を持つ。
`hCaught` は `(encoded w)[position s.center + r₀ + 1 - 2h]? = symbol …focus` なので、
`ScanInvariant` が右ヘッドの読む位置を与えれば `enc[c+r₀+1-2h]? = enc[c+r₀+1]?`（周期 `2h`）に落ちる。
これは `hOut`（`PalAt` 半径 `2h`）から出るはず。出れば **7 成分が 6 成分になる**。
## n211 — 公理 `obligation_shiftPalResiduesAlongRun` を弱めた（`∀ s'` の過剰量化を除去）

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### 見つけた過剰量化（同型 10 例目、しかも公理の中）

公理の第 3 連言は

```lean
z.vm.periodOnly = false → ∀ s' : GalilVM, FreshShiftLedger w z.vm s'
```

`FreshShiftLedger w s s'` は `s'.chain = ChainVM.watch wch` でしか `s'` を縛らんので、
`wch`（＝周期テープ、`periodLength wch` は任意の自然数）が自由になる。そのうえで
`2 * periodLength wch ≤ r₀ ≤ 4 * periodLength wch` を主張してた。`p` を大きく取れば破れる形。

### 消費者が実際に渡すもの（一次情報）

`ShiftPalAlongTrace.shiftPal_of_freshShiftLedger:186` の本体:

```lean
intro s' hCompare hNotMatched wch hChain hGuard r₀ hScanInv
obtain … : compareFound (PofC centre place entry w) q first s s' := hCompare
…
obtain … := hLedger s' wch hChain r₀ hScanInv
```

`ShiftPal` の `s'` は **`compareFound … s s'` を伴って来る**——`s` の実際の比較先や。
`hLedger` はそこにしか適用されてへん。

### やったこと

`∀ s'` に `compareFound (PofC …) q first s s' →` のガードを入れた:

* `ShiftPalAlongTrace.shiftPal_of_freshShiftLedger` の `hLedger`
* `shiftPal_alongRun` の `hFreshLedger` / `shiftPal_alongTrace` の同型場
* **`PalInPegUnconditional` の `obligation_shiftPalResiduesAlongRun` 第 3 連言**（および trace 形）

証明本体の変更は `hLedger s' hCompare …` の 1 引数追加だけ（`:= id hCompare` で `hCompare` を残す）。
全体 build 緑。

**公理は 3 本のままやが、その 1 本が真に弱くなった。** `wch` が `z.vm` の chain に縛られたので、
周期テープと `w` を結びつける場が原理的に存在しうる形になった（以前は任意の `wch` に対する主張で、
それは成り立たへん）。

### 方法の訂正（コウタ）

* 「producer 0 は形式化のミスで断定できる」——CLAUDE.md の常設制約どおり。
  `hpresRepAt` / `hshape` / `hfound` / `hfoundBg` / `hfoundReplay` の 5 本は**難しいんやのうて切り方が間違ってる**。
* 「公理が遠いという思い込みは思考から追い出せ。難しいことは原理的にありえない。作業量の問題でしかない」。
  n210 で「`obligation_cycleOracle` は遠い」と書いたのは禁止された考え方やった。
## n210 — 経路を検証し、`obligation_cycleOracle` の経路から**反証済みの前提**を外した

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本、変化なし）・無条件 PAL は未完。**

### 方法の訂正（コウタの指摘）

「定理を 40 本足して公理が 1 本も落ちてへんことに疑問を持て」。正しい。
n195〜n209 の 15 ティックは **`StageEntryC.fuel` を磨いてたが、それはどの公理の経路にも無い**。
計器は `#print axioms` やのに、ウチは「定理を何本足したか」で満足してた。
**「何も落としてへん」が 2 回続いた時点で止まるべきやった。**

### 経路の検証（grep、docstring は一次情報にせず）

| 名前 | コード上の参照 |
|---|---|
| `CloseoutOracle8.h_oracle_of_leaves7` | **ゼロ**（3 件とも docstring/コメント） |
| `CloseoutOracleBridge.hor_of_H_oracle` | **ゼロ** |
| `obligation_cycleOracle` | `PalInPegUnconditional.lean:346` で公理として直接使用 |

**記録されてた経路は散文であって鎖やない。** さらに両経路とも反証済みの葉を通ってた:

* `GalilFinalAssembly4.h_oracle2_of_leaves` — `hpres` / `hquiet` / `houtReplay`（CLAUDE.md の反証済み 3 葉）
* `CloseoutOracle6/7/8.h_oracle_of_leaves5/6/7` — `hreadyB : ReadyFuel …`（`ReadyFuelRefute.not_readyFuel_v0`）

型は合っている: `hor_of_H_oracle2_invSS` / `hor_of_H_oracle` の結論は
`∀ w, 0 < w.length → CycleOracleMC3 (PofC …) q first w` で、**公理の型そのもの**。
つまり仮説さえ埋まれば公理はその場で定理に置き換わる。

### やったこと（前提を 1 本崩した）

`CloseoutOracle6.h_oracle_of_leaves5` は `hreadyB`（反証済み `ReadyFuel`）を
`GalilSegmentConstructB.segment_of_invLPCB` に食わせてた。結論が同型の
`CloseoutReadyStage.segment_of_invLPCS`（n200 で `Φ` ＋ `ReadyIface` に一般化した版）に差し替え、
`hreadyB` の型を

```lean
∃ Φ, ReadyIface (PofC centreC placeC entry w) Φ ∧
  Φ (searchLens.get r) (headRank r.right * 2048 + c.clock) (2048 - c.clock)
```

に切り直した（`CloseoutOracle6` / `7` / `8` の 3 ファイル）。全体 build 緑。

**これで `obligation_cycleOracle` の経路が「偽の前提を要求する」状態でなくなった。**
n195〜n209 の readiness 仕事は、ようやくここで公理の経路に接続された
（接続先は `StageEntryC.fuel`＝`ReachAtC3` 側やのうて、`h_oracle_of_leaves5`＝`H_oracle` 側やった）。

### 正直な計測

**公理は 3 本のまま。** 落ちたのは「反証済み前提の要求」であって公理やない。
次にやるのは `h_oracle_of_leaves7` の残り 10 葉のうち producer が実在するものを数えること。
**producer が無い葉の数が、この公理までの本当の距離。**
## n209 — 未来リスト依存を全部外した。4 相の不変量が完全に継続フリーになった

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### 1. `bal_of_count`（`CloseoutPreload35` を in-place で分割）

`bal_of_paced_slack_S` は仮説 `hp : PacedL 2048 slack (bs ++ [a])` を**1 回しか読んでへん**
（`hp (bs++[a]).length` で比較回数の上界を取るだけ）。そこで算術の核を切り出した:

```lean
theorem bal_of_count {k mw slack cnt : ℕ}
    (hcal : 8 * max k 1 ≤ 2 * mw) (hmw : 16 ≤ mw) (hslack : slack ≤ 2047)
    (hc : 2048 * cnt ≤ mw + 1 + slack) :
    4 * dpDemandS k (2 * mw) + 4 * cnt ≤ mw
```

`bal_of_paced_slack_S` は**その 4 行の系**になった（証明の重複ゼロ、既存消費者はそのまま）。

### 2. `DoubleLeg` を継続フリーに切り直した（`StageDoubleLeg`）

旧: `DoubleLeg k mw slack u v as := ∃ ds, DoubleTrace ds u v ∧ PacedL 2048 slack (ds ++ as) ∧ …`
— **未来リスト `as` に依存してた**。

新: `DoubleLeg k mw slack u v kcur := ∃ ds, DoubleTrace ds u v ∧ PrepPaced (ds.count true) ds.length slack kcur ∧ …`

`PrepPaced`（n206）は `2048 * spent + k ≤ len + slack₀` で、`ReadyIface` の添字 `k` と
同じ動き方をする。ステップも `ReadyIface` に合わせて 2 本に割った:

* `doubleLeg_background`（`kcur' ≤ kcur + 1`）
* `doubleLeg_comparison`（`2048 ≤ kcur + 1` → `kcur' = 0`）
* `doubleLeg_exit`（比較で出るときだけ `hcmp : a = true → 2048 ≤ kcur + 1`）

使わんくなった `pacedL_prefix_slack` は削除（参照ゼロを残さんため）。

### いま立ってる絵

**4 相すべての不変量が、未来のイベント列に一切量化してへん。**

| 相 | 不変量 | 継続依存 |
|---|---|---|
| run | `DpBudgetAt v k` | 無し |
| prep | `PrepAt` ＋ `ReachP` ＋ `PrepPaced` | 無し（n206 で除去） |
| wait | `WaitPhase k mw v` | 無し |
| double | `DoubleLeg k mw slack u v kcur` | **無し（本ノートで除去）** |

これで `Φ` を組んでも `ReadyPacedS` の `∀ as` は一切戻ってこーへん。

### 残り

1. `.run` → 直接 `.double` の未決分岐（n208）
2. 4 相の選言を 1 つの `Φ` にして `ReadyIface P Φ` のインスタンス
3. wait 出口の `a = false`

**今回も何も落としてへん**（公理 3 本のまま）。
## n208 — `StageRunPhase`：4 相の枠と相間の受け渡しが全部つながった

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

`PalPeg/StageRunPhase.lean`（2 定理、標準 3 公理、全体 build 緑、一発で通った）:

* `RunPhase k mw v := mode = run ∧ span = ofNat mw ∧ lower = ofNat k ∧ Canonical debt`
* `runPhase_step` — `.run` に留まる刻みは枠を保つ。`runTrace_frame` を 1 手トレースで読み、
  `stageSpan` が `.run` でも `.wait` でも span である（`stageSpan s = if mode = double then work else span`）
  ことが窓を出口越しに運ぶ鍵
* `waitPhase_of_runExit` — `.wait` に着地すると `WaitPhase k mw`。`run_exit_frame` を空トレースで読んだだけ

### 相の鎖が閉じた

```
RunPhase --waitPhase_of_runExit--> WaitPhase --doubleLeg_head_of_waitExit--> DoubleLeg
   ^                                                                            |
   |                                                                     doubleLeg_exit
   |                                                                            v
   +--- dpBudgetAt_of_prepEntry (+ RunPhase の枠) <--- PrepAt k (2mw) + StageInvS
```

各辺はステップ局所で、未来のイベント列に一切量化してへん。

### 見つかった未決の分岐（正直に）

`GalilScaffoldSearchRun.ExitMode` は `.run` から**直接 `.double`** への着地も許す。
`run_exit_frame` はそこで `work = ofNat mw` / `span = reset` / `quarter = 0` を与えるが、
`StageDoubleLeg.DoubleLeg` はさらに `value debt = 0` を要求し、それを立てるのは `.wait` 脚
（`wait_exit_debt_zero`）や。**機械がその出口を実際に取れるかは未確定**で、
束ねのときに排除するか債務を別に運ぶかせなあかん。ファイルの docstring に明記した。

### 残り

1. 上の未決分岐の処理
2. 4 相の選言を 1 つの `Φ` にして `ReadyIface P Φ` のインスタンスを作る
3. wait 出口の `a = false` を `Φ` の slack 添字から出す（n207 で翻訳可能性は確認済み）

**今回も何も落としてへん**（公理 3 本のまま）。
## n207 — `StageWaitPhase`：4 相のうち 3 相がステップ局所になった

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

`PalPeg/StageWaitPhase.lean`（2 定理、標準 3 公理、全体 build 緑、一発で通った）:

```lean
def WaitPhase (k mw : ℕ) (v : SearchVM) : Prop :=
  v.search.mode = Mode.wait ∧ v.search.span = ofNat mw ∧ v.lower = ofNat k ∧
    Canonical v.search.debt
```

* `waitPhase_step` — `.wait` に留まる刻みは枠を保つ（窓・下界・正準性は不変、債務だけ減る）
* `doubleLeg_head_of_waitExit` — 背景イベントで `.wait` を出ると、着地は
  `StageDoubleLeg.DoubleLeg` が要求する先頭データそのもの
  （`work = ofNat mw` / `span = reset` / `quarter = 0` / 債務 0 / `lower = ofNat k`）

### 出口イベントが背景である理由（翻訳できることを確認した）

`CloseoutPreload34.exitNotFire_of_wait` は機械レベルで `p3.ctl.clock ≠ 1` を出す。
その論証は「wait 脚が空なら run→wait の出口イベントが比較（`run_exit_wait_match`）で、
比較直後はクロックが 2048 に戻る。よって次の刻みは比較でけへん」。

**`ReadyIface` の会計ではこれがそのまま出る**——`comparison` の結論が `Φ v n 0`（slack が 0 に戻る）で、
比較には `2048 ≤ k + 1` が要るから。つまり制御層の事実やのうて、`Φ` の添字だけで言える。
ただし本ファイルではその論証は運んでへん（出口は `a = false` を仮説に取ってる）。

### 4 相の現状

| 相 | ステップ局所の不変量 | 出口 |
|---|---|---|
| run | `DpBudgetAt`（n202/n203） | 非 run へ（節が空虚になる） |
| prep | `PrepPaced` ＋ `ReachP`（n206） | `dpBudgetAt_of_prepEntry`（n206） |
| **wait** | **`WaitPhase`（本ファイル）** | **`doubleLeg_head_of_waitExit`** |
| double | `DoubleLeg`（n198） | `doubleLeg_exit` → `PrepAt k (2mw)` ＋ `StageInvS` |

**4 相すべてにステップ局所の不変量と出口が揃った。** 残るのは

1. run → wait の出口（`run_exit_frame` / `run_exit_wait_match` が材料）
2. 4 相の選言を 1 つの `Φ` にして `ReadyIface P Φ` のインスタンスを作る
3. wait 出口の `a = false` を `Φ` の slack 添字から出す

**今回も何も落としてへん**（公理 3 本のまま）。
## n206 — 入口定理から未来リスト依存を外し、prep 脚の pacing 算術も揃えた

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### 1. `dpBudgetAt_of_stagePrepS` → `dpBudgetAt_of_prepEntry`（仮説を真に弱めた）

n205 の証明を読み直したら、`StagePrepS k m D slack v x (a :: as)` の

* 長さ節 `D + dpEvents (m+1) ≤ bs.length + as.length` を**一度も使うてへん**
* pacing 節も接頭辞 `bs ++ [a]` しか読んでへん（`pacedL_prefix_count_slack` 経由）

ことが分かった。よって未来リスト `as`・`DepthAt`・slack をすべて落として

```lean
theorem dpBudgetAt_of_prepEntry
    (hp : PrepAt k m v) (hE : StageInvS k m v)
    (hreach : ReachP v bs x)
    (hadv : 2048 * ((bs ++ [a]).count true) ≤ prepLen k + 2047)
    (hs : searchStep c a x x') (hrun : x'.search.mode = Mode.run) :
    DpBudgetAt x' 0
```

に切り直した（操作 (A)、真に弱い）。**これで `Φ` が継続への量化を一切持たんで済む。**
`ReadyPacedS` の `∀ as` を捨てた目的からして、ここが継続に依存してたら意味が無かった。

### 2. prep 脚の pacing も同じ形で釣り合う（`DpBudgetBalance` §2）

```lean
def PrepPaced (spent len slack0 k : ℕ) : Prop := 2048 * spent + k ≤ len + slack0
```

* `prepPaced_background` — `k' ≤ k + 1`、`len + 1`
* `prepPaced_comparison` — `2048 ≤ k + 1` のとき `spent + 1`、`len + 1`、`k → 0`
* `prepPaced_entry` — 上の `hadv`（`2048 * (spent + [a]) ≤ prepLen k₀ + 2047`）を
  `len + 1 ≤ D ≤ prepLen k₀` と `slack0 ≤ 2047` から出す

比較で `2048*spent + 2047 ≤ len + slack0` から `2048*(spent+1) ≤ len + slack0 + 1` が
**ちょうど**出る。DP 側（`DpBudget`）と同じ厳密な釣り合いや。

### いま揃ってる部品（`Φ` 組み上げ用）

| 相 | ステップ | 入口/出口 |
|---|---|---|
| run | `dpBudgetAt_background` / `_comparison` | 入口 `dpBudgetAt_of_prepEntry` |
| prep | `PrepPaced` の 2 補題 ＋ `ReachP` の snoc | 出口が run 入口 |
| double | `StageDoubleLeg.doubleLeg_step` / `_exit` | 出口が `PrepAt k (2mw)` |
| wait | **未着手**（`wait_step_cases` が材料） | 出口が double 脚の先頭 |

`PrepInv` は全相で `prepInv_searchStep`。`ready`/`mono` は `ReadyAt` で済み。

**今回も何も落としてへん**（公理 3 本のまま）。残りは wait 相と、4 相を 1 つの `Φ` に束ねて
`ReadyIface P Φ` のインスタンスを作ること。
## n205 — `StageEntryBudget`：入口の残差も埋まった。`ReadyIface` の中身が全部揃った

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

n204 で `readyAt_background` / `readyAt_comparison` が残した唯一の残差 `hentry`
（非 `.run` → `.run` の新規入口で DP を融資する）を供給した。

`PalPeg/StageEntryBudget.lean`（1 定理、標準 3 公理、全体 build 緑、**一発で通った**）:

```lean
theorem dpBudgetAt_of_stagePrepS
    (hp : PrepAt k m v) (hE : StageInvS k m v)
    (hdep : DepthAt v D) (hD : D ≤ prepLen k) (hslack : slack ≤ 2047)
    (hq : StagePrepS k m D slack v x (a :: as)) (hs : searchStep c a x x')
    (hrun : x'.search.mode = Mode.run) :
    DpBudgetAt x' 0
```

入力は `CloseoutPreload35.dpSafe_of_stagePrepD_slack` と**まったく同じ**で、
結論だけリスト課金の `DpSafeStage` から状態局所の `DpBudgetAt` に替えた。

### 余裕の内訳

`StageInvS` が与える債務は
`dpDemandS k m = (prepLen k + 2047)/2048 + (prepLen k + 2047 + dpEvents (m+1))/2048 + 1`。
準備脚が使えるのは第 1 項まで（pacing）、DP 自身の需要 `⌈dpEvents (m+1)/2048⌉` は第 2 項以下。
よって **`+1` は手つかずのまま余る**。算術に無理はない。

### いま立ってる絵（`Φ = ReadyAt`）

| `ReadyIface` の場 | 状態 |
|---|---|
| `ready` | 済（n203） |
| `mono` | 済（n203） |
| `background` | 済（n204）＋ 入口は本ファイル |
| `comparison` | 済（n204）＋ 入口は本ファイル |

**4 場すべての中身が揃った。** まだ `ReadyIface P Φ` の**インスタンスは作ってへん**——
`Φ` が単なる `ReadyAt v k` では入口の `hentry` を自前で出せへん（`PrepAt` 起点の
ステージデータを持ってへんから）。最終形は

```
Φ v n k := ReadyAt v k ∧ <現在のステージの PrepAt 起点と StagePrepS の持ち回り>
```

で、ステージ境界での起点の張り替えが `prepAt_of_double_exit`（n189 `StageLocalPrep`）と
`StageDoubleLeg`（n198）の仕事になる。

**今回も何も落としてへん**（公理 3 本のまま）。
## n204 — 輸送 2 場も立った。残差は `.run` 新規入口 1 点に凝縮

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

`PalPeg/DpBudgetState.lean` に 3 定理を追加（全 12 定理、標準 3 公理、全体 build 緑）。

### `PrepInv` の保存

```lean
theorem prepInv_searchStep (hprep : PrepInv v.toPrep) (hstep : searchStep center a v v') :
    PrepInv v'.toPrep
```

`CloseoutReadyStage.readyRemS_step` の第 1 成分を単体で取り出したもの。`searchStep` の
どの分岐も、4 つの準備モードの外に着地する（`prepInv_of_notPrep`）か、準備 tick を回す
（`prepInv_tick`）か、`prepare` を発行する（`prepInv_prepare`）かのいずれかや。
既存の部品だけで、新しい数学はゼロ。

### 輸送 2 場

```lean
theorem readyAt_background (hk : k' ≤ k + 1) (h : ReadyAt v k)
    (hstep : searchStep center false v v')
    (hentry : v.search.mode ≠ .run → v'.search.mode = .run → DpBudgetAt v' k') :
    ReadyAt v' k'
theorem readyAt_comparison (hk : 2048 ≤ k + 1) (h : ReadyAt v k)
    (hstep : searchStep center true v v')
    (hentry : v.search.mode ≠ .run → v'.search.mode = .run → DpBudgetAt v' 0) :
    ReadyAt v' 0
```

run 相の中の刻みは `run_step_quanta` ＋ n202 の `dpBudgetAt_background` / `dpBudgetAt_comparison`
でそのまま通り、非 run のままの刻みは節が空虚。**残るのは「非 `.run` → `.run` の新規入口」1 点だけ**で、
それを名前付き仮説 `hentry` に出した。

### いま立ってる絵

`Φ = ReadyAt` に対して `ReadyIface` の 4 場のうち

* `ready` — 済（n203）
* `mono` — 済（n203）
* `background` / `comparison` — **`hentry` を除いて済**

`hentry` の中身は n203 の `dpBudgetAt_entry` により

```
(dpEvents w.length + 2047) / 2048 ≤ (value v'.search.debt).toNat
```

の 1 本（preload `w` は `run_entry_preload` が与える）。つまり**「ステージ債務が
DP の必要イベント 2048 ごとに比較 1 回を賄う」だけが残差**や。これは
`bal_of_paced_slack_S` / `dpDemandS` が言うてる内容そのもので、
`StageLocalPrep`（n189）と `StageDoubleLeg`（n198）がその供給側の部品になる。

**今回も何も落としてへん**（公理 3 本のまま）。`hentry` を閉じて初めて
`StageEntryC.fuel` が埋まり、`NoReturn` / `EntryDepthG` 経路が不要になる。
## n203 — `.run` 入口と `ReadyAt`：`ReadyIface` の `ready`/`mono` が周期全体で立った

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

`PalPeg/DpBudgetState.lean` に 3 定理を追加（全 9 定理、標準 3 公理、全体 build 緑）。

### `.run` 入口

```lean
theorem dpBudgetAt_entry
    (hdp : v.dp = ⟨GalilScaffoldPreload.initial w lower, false⟩)
    (hm : v.search.mode = .run) (hc : Canonical v.search.debt)
    (hd0 : 0 ≤ value v.search.debt)
    (hfunded : (dpEvents w.length + 2047) / 2048 ≤ (value v.search.debt).toNat) :
    DpBudgetAt v 0
```

`hdp` は `CloseoutRunEntriesS.run_entry_preload` が与え、到達は `dpReached_start`（空接頭辞）。
**残差は `hfunded` 1 本だけ**——「債務が DP の必要イベント数 `2048` ごとに比較 1 回を賄う」。
これが `bal_of_paced_slack_S` / `dpDemandS` が言うてる内容そのものや。

### 周期全体の可読性述語

```lean
def ReadyAt (v : SearchVM) (k : ℕ) : Prop :=
  PrepInv v.toPrep ∧ (v.search.mode = Mode.run → DpBudgetAt v k)
```

非 run 相では `SearchReady` の DP 節が空虚なので `PrepInv` だけで済む。これで

* `searchReady_of_readyAt` — **`ReadyIface.ready`**（周期全体で成立）
* `readyAt_mono` — **`ReadyIface.mono`**（周期全体で成立）

が立った。**4 場のうち 2 場が `Φ = ReadyAt` で揃った。**

### 残り（輸送 2 場）

`background` / `comparison` は `ReadyAt (searchLens.get s) k → searchEffect P a s v → ReadyAt v k'`。
中身は 3 つ:

1. `PrepInv` が探索量子で保存されること
2. 源も着地も `.run` のとき → `dpBudgetAt_background` / `dpBudgetAt_comparison`（済）
3. **源が非 `.run` で着地が `.run`（新規入口）** → `dpBudgetAt_entry` の `hfunded` を作らなあかん。
   ここだけがステージ債務の話で、`ReadyAt` にステージデータ（窓 `mw`、下界 `k`、
   `PrepAt`/`StagePrepS`）を持たせる必要がある。

つまり **`Φ` の最終形は `ReadyAt` ＋ ステージデータ**になる。`StageDoubleLeg`（n198）と
`StageLocalPrep`（n189）がそのステージデータ側の部品や。

**今回も何も落としてへん**（公理 3 本のまま）。
## n202 — `DpBudgetState`：会計を `SearchVM` の上に載せた（run 相の 4 場が出た）

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

n201 の算術を `DpReached` に接続した。`PalPeg/DpBudgetState.lean`（6 定理、標準 3 公理）:

```lean
def DpBudgetAt (v : SearchVM) (k : ℕ) : Prop :=
  ∃ w lower s0 bs, s0.mode = .run ∧ Canonical s0.debt ∧ 0 ≤ value s0.debt ∧
    DpReached w lower s0 bs v.search v.dp ∧
    DpBudget (dpEvents w.length - bs.length) (bs.count true) (value s0.debt).toNat k
```

* `dpSafeHere_of_dpBudgetAt` — **`ready`**。`DpSafeHere` は継続を存在量化してるので、
  全背景の継続（`List.replicate (dpEvents w.length) false`）を取れば `spent ≤ debt` に潰れる。
* `dpBudgetAt_mono` — **`mono`**。
* `dpBudgetAt_background` / `dpBudgetAt_comparison` — **輸送 2 場**。`DpBudgetBalance` の算術そのまま。
* `dpBudgetAt_need_pos` — run 中は DP が予算を使い切ってへん。
  `CloseoutReadyStage.dpSafeStage_pre_ne_nil` を**空の課金接頭辞**で読んだだけ（新しい数学ゼロ）。
* `dpEvents_covers` — `3186n + 1683 ≤ 64 * dpEvents n`。

### いま立ってるもの

**`ReadyIface` の 4 場が、run 相については揃った。** ただし `DpBudgetAt` が言うのは run 相だけで、
`ReadyIface` の `Φ` は prep / `.wait` / `.double` 相でも成り立たなあかんし、
各 `.run` 入口で `DpBudgetAt` を**再確立**せなあかん。再確立こそがステージ債務と
`bal_of_paced_slack_S` の出番や。

### 残り

1. 非 run 相で `Φ` を定義（`SearchReady` の `run → …` 節が空虚になるので `PrepInv` だけが要る）
2. `.run` 入口で `DpBudgetAt v' 0` を作る：`run_entry_startRun` が `v'.dp = ⟨Preload.initial w lower, false⟩`
   を与えるので `DpReached w lower v'.search [] v'.search v'.dp` は `dpReached_start`。
   あとは `DpBudget (dpEvents w.length) 0 debt 0` ＝ 債務がステージ 1 本ぶんの比較を賄えること。
   これが `bal_of_paced_slack_S` の内容や。
3. 4 相を束ねて `Φ` を定義し、`ReadyIface P Φ` を証明 → `StageEntryC.fuel` が埋まる

**今回も何も落としてへん**（公理 3 本のまま）。
## n201 — `DpBudgetBalance`：`ReadyIface` の 2 場がぴったり釣り合う算術を切り出した

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### 測ったこと

`GalilBranchInvariants2.DpSafeHere:295` は継続 `as` を**存在量化**してるので、`as` を全部 false に
取れば「DP 開始以降の比較回数 ≤ 開始時債務」に潰れる。つまり `ready` が要求するのは
**局所的な債務超過なし**だけで、`DpSafeStage`（リスト依存）ほど強くない。

そのうえで `ReadyIface` の 2 つの輸送場の収支を並べると:

| 場 | ガード | DP の残り必要イベント `need` | slack `k` | 債務 |
|---|---|---|---|---|
| `background` | — | `-1` | `≤ k + 1` | 不変 |
| `comparison` | `2048 ≤ k + 1` | `-1` | `→ 0` | 比較 1 消費 |

背景では `need + k` の和が保存され、比較（ガードにより `k = 2047` でしか起きん）では
和がちょうど `2048` 減る。よって

```
spent + ⌈(need + k) / 2048⌉ ≤ debt
```

は**両方の刻みで厳密に保存される**。機械の至る所に 2048 が出てくる理由がこれや。

### 書いたもの

`PalPeg/DpBudgetBalance.lean`（5 定理、標準 3 公理、全体 build 緑）:

* `DpBudget need spent debt k := spent + (need + k + 2047) / 2048 ≤ debt`
* `dpBudget_spent` — `ready` が要る `spent ≤ debt`
* `dpBudget_mono` — slack を下げるのは弱める
* `dpBudget_background` / `dpBudget_comparison` — 2 場ぶんの保存
* `dpBudget_comparison_needs_full_slack` — **ガードが鋭いことの証人**。
  `k = 2046` では `DpBudget 2 0 1 2046` は成り立つのに、比較後の `DpBudget 1 1 1 0` が破れる。
  つまり `ReadyIface.comparison` の `2048 ≤ k + 1` は `2047 ≤ k + 1` に弱められへん。

（最初 `dpBudget_comparison_sharp` として `¬ DpBudget (need-1) 1 0 0` を書いたが、
これは `hneed` を使わん自明な文で「鋭さ」を何も示せてへんかった。linter の未使用警告で気づいて
本物の証人に差し替えた。）

### これが `ReadyPacedS` と違う点

`ReadyPacedS` は同じ上界を `PacedL 2048 k as`（任意の継続）から得る。`PacedL` は
**リストの先頭からの累積**上界なので、長い背景で予算を貯めてから一気に撃つ列
（`replicate (2048*m) false ++ replicate m true` は `PacedL 2048 0`）を許すが、機械は出せへん。
`DpBudget` は**現在の slack** に対して述べるので、そういうスケジュールは最初から入らへん。

### 残り

この算術を `DpReached` / `SearchVM` / `ReadyIface` に接続すること。**まだ接続してへんので
何も落ちてへん**（公理 3 本のまま）。次は

1. `need` を `dpEvents w.length - bs.length` として `DpReached w lower s0 bs v.search v.dp` に結ぶ
2. `spent` を `bs.count true`、`debt` を `value s0.debt` に結ぶ
3. run 相の 1 刻みで `DpReached` が伸びること（背景・比較とも）を確認
4. prep / wait / double 相（`StageDoubleLeg` 済み）と合わせて `Φ` を定義し `ReadyIface` の 4 場を証明
## n200 — `StageEntryC.fuel` を `ReadyIface` の存在形に切り直した（継ぎ目が run 線に届く形になった）

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本、`Axioms.lean` のラチェット健在）・
無条件 PAL は未完。**

n199 の訂正どおり道を戻して、n195 の計画 1〜3 を実行した。

### 1. `ReadyIface` を `CloseoutReadyStage` §4 末尾に移した

`PalPeg/ReadyInterface.lean` は**削除**（Workbench の登録も）。定義が 4 つの証人
（`readyPacedS_ready` / `_mono` / `_effect_false` / `_effect_true`）の真下に来たので、
別ファイルに置く理由が無くなった。コピペを残さんため。

### 2. 5 定理を `Φ` ＋ `ReadyIface P Φ` で再証明（その場で一般化、22 パッチ）

`watchSegE_constructS` / `segment_of_invLPCS` / `readyPacedS_watchSegE`（→ **`readyIface_watchSegE`** に改名）/
`reachAtC3_of_target_matchS` / `reachAtC3_of_crossS`。
本文の変更は 4 補題呼び出しを 4 場に置き換えただけ。外部呼び出しは 3 箇所
（`CloseoutSegCheckpoint` / `CloseoutContracts` / `CloseoutPreload`）で、
`readyIface_readyPacedS P` を渡して従来どおりの挙動を回復。

### 3. `StageEntryC.fuel` を切り直した

```lean
-- 旧
fuel : ReadyPacedS (searchLens.get r) (headRank r.right * 2048 + c.clock) (2048 - c.clock)
-- 新
fuel : ∃ Φ : SearchVM → ℕ → ℕ → Prop,
  ReadyIface P Φ ∧ Φ (searchLens.get r) (headRank r.right * 2048 + c.clock) (2048 - c.clock)
```

`readyIface_readyPacedS` で旧形は新形に入るので**真に弱い**（操作 (A)）。
`StageEntryC` を構成してる箇所は**ゼロ**（全部仮説として受け取るだけ。継ぎ目やから当然）、
`.fuel` の使用は `reachAtC3_of_crossF_C` の 1 箇所だけやったので、切り直しの波及はそこだけ。

### なぜこれが効くのか

`ReadyPacedS` は `PacedL 2048 k` の**全**リストに量化する。`PacedL` は累積の上界なので、
背景で予算を貯めて一気に比較を撃つスケジュールを許すが、実機は比較を `clock = 1` でしか撃たず
直後に `clock := 2048` に戻すのでそれを出せへん。`ReadyIface.comparison` の `2048 ≤ k + 1` が
そのクロック規律そのものやから、**クロック添字の run 局所な `Φ` はこの場を正当に満たせる**。

### 残り

**`Φ` を実際に供給すること。** ステージ周期不変量（`StageDoubleLeg` が 1 相、
prep 相は `StagePrepS` が既にステップ局所）をクロック添字で組み、`ReadyIface` の 4 場を証明する。

**今回も公理は落ちてへん**（3 本のまま）。落ちたのは `StageEntryC.fuel` の強さだけ。
`NoReturn` / `EntryDepthG` を取る `runEntriesS_of_namedG` 経路は第 1 ステージ用として温存してある。
## n199 — n196 の判断は間違い。`ReadyIface` は producer を助ける。`EntryDepthG` も起点依存

**状態: 全体 build 成功・標準公理のみ（3 本）・無条件 PAL は未完。このターンは Lean 編集なし。**

### 1. `EntryDepthG` も `NoReturn` と同型（過剰量化の 9 例目）

一次情報 `CloseoutPreload5.EntryDepthG:607`:

```lean
def EntryDepthG (u : GalilVM) (D : ℕ) : Prop :=
  ∀ bs v v' c a, ReachL (searchLens.get u) bs v → searchStep c a v v' →
    v.search.mode ≠ .run → v'.search.mode = .run → bs.length + 1 ≤ D
```

restart 起点 `u` から到達する**すべての** `.run` 入口が `D ≤ prepLen k` 手以内、と主張してる。
第 2 ステージの入口は `prepLen k + mw + …` 手目やから、**第 2 ステージが存在した時点で破れる**。

よって `runEntriesS_of_namedG` は起点依存の仮説を **2 本**（`NoReturn` と `EntryDepthG`）
取っており、どちらも第 1 ステージでしか成り立たん。
機械検査した反証はまだ無いので `REFUTED` とは書かへん。

### 2. `ReadyPacedS` 自体が怪しい（疑い。反証はまだ無い）

`DpSafeStage v as`（`CloseoutReadyStage:93`）は

```lean
as = pre ++ post ∧ 3186*w.length+1683 ≤ 64*(bs ++ pre).length ∧
  ((bs ++ pre).count true : ℤ) ≤ value s0.debt
```

——`as` の先頭 `≈ dpEvents(2mw+1) ≈ 100·mw` 手の**比較回数**が債務（`≈ 2·max k 1`）以内、を要求する。

一方 `PacedL 2048 slack as := ∀ n, 2048 * (as.take n).count true ≤ n + slack` は**累積**の上界で、
「長い背景のあとに比較をまとめて撃つ」バーストを許す
（例: `replicate (2048*m) false ++ replicate m true` は slack 0 で paced）。
実機の制御はバーストを出せへん——比較は `clock = 1` でしか起きず、直後に `clock := 2048` に戻る。

`ReadyPacedS v n 0 = ∀ as, n ≤ as.length → PacedL 2048 0 as → SearchReadyS v as` の `n` は
**下界**なので、バースト列も全部対象に入る。バーストを跨ぐステージの `DpSafeStage` は
比較回数が債務を超えて破れるはず。**つまり `ReadyPacedS` は機械が絶対に出さんスケジュールにまで
量化しており、偽の疑いが濃い。** 前身の `ReadyFuel` が偽やったのと同じ病。

### 3. n196 の訂正（ウチの判断ミス）

n196 で「`ReadyIface` による `Φ` 抽象化は producer を 1mm も助けへん」と書いた。**間違いやった。**

`ReadyIface` の場を読み直すと:

```lean
comparison : 2048 ≤ k + 1 → s.chain = ChainVM.idle →
  Φ (searchLens.get s) (n + 1) k → searchEffect P true s v → Φ v n 0
```

**比較は slack が満杯（`k = 2047`）のときしか許されへん。** これがまさにバーストを禁じる
クロック規律や。つまり `ReadyIface` は最初から「機械が実際に出すスケジュール」だけを要求してる。
`ReadyPacedS` がそれを満たすのは、`ReadyPacedS` が（おそらく）強すぎる＝偽やから。
**クロック添字の run 局所な `Φ` なら、`ReadyIface` を正当に満たせる。**

n195 は正しい道具を、間違った理由で作った。n196 はそれを、不十分な理由で捨てた。両方ウチの判断ミスや。

### 次（道が戻った）

1. `watchSegE_constructS` と 4 消費者を `Φ` ＋ `ReadyIface P Φ` で再証明（n195 の計画どおり）。
2. `StageEntryC.fuel` を `∃ Φ, ReadyIface P Φ ∧ Φ …` に切り直す。
3. ステージ周期不変量（`StageDoubleLeg` はその 1 相）を **clock/slack 添字**で組み、`Φ` として供給する。
   slack ≤ 2047 は制御の `2048 ≤ clock + k` が与えるので、純 `SearchVM` の `∀ as` では出えへんかった
   ものがここで出る。
4. `runEntriesS_of_namedG` 経路（`NoReturn` ＋ `EntryDepthG`）は第 1 ステージ専用として温存。

**今回も何も落としてへん**（公理 3 本のまま）。
## n198 — `StageDoubleLeg`：ステージ周期 4 相のうち double 相をステップ局所にした

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

`EntryInv Q` は不変量に `searchStep` を 1 手ずつ渡し、**任意の**イベント列に量化するので、
`Q` は「いま自分がいる脚」を丸ごと名指しでけへん。既存の
`CloseoutPreload17.double_spends` と `CloseoutPreload35.postRunF_round_trip_S` は
どちらも `.double` 脚を `bs.length = mw` ごと仮説に取る。そこをステップ局所に切り直した。

`PalPeg/StageDoubleLeg.lean`（5 定理、標準 3 公理、全体 build 緑）:

* `doubleTrace_snoc` — `DoubleTrace` は前方 cons なので、末尾で伸ばすには別の帰納法が要る
* `doubleTrace_frame` — `ds` 手後に work は `ds.length` 減り span は `2*ds.length` 増える。
  **`ds.length ≤ mw` はここから出る**（仮定せんでええ）
* `pacedL_prefix_slack` — 既存 `pacedL_prefix_of_append` は slack 0 固定。`.double` 脚は
  クロック位相が任意の所で始まるので slack 版が要った
* `DoubleLeg k mw slack u v as` — 不変量。pacing を**脚の先頭 `u` から**測るのが要点で、
  `bal_of_paced_slack_S` が脚全体の比較回数を読むため、現在時刻の状態述語では間に合わへん
* `doubleLeg_step` / `doubleLeg_exit` — 1 手の 2 分岐。work が残れば不変量が続き、
  使い切れば `PrepAt k (2*mw)` ＋ `StageInvS k (2*mw)` に落ちる

### 残り

ステージ周期は 4 相（`.run` / `.wait` / `.double` / preparation）。**double 相だけ**が
ステップ局所になった。残り 3 相と、それらを `EntryInv` の `Q` に組み上げるところは未着手。
**今回も何も落としてへん**（公理 3 本のまま、`NoReturn` も残ったまま）。

### 次

1. prep 相は `StagePrepS` がそのままステップ局所（`stagePrepS_next` ＋
   `dpSafe_of_stagePrepD_slack`）。4 相のうちこれで 2 相。
2. `.wait` 相：`wait_step_cases` が後続を `.wait ∨ .double` に限定し、`.double` へ出るときに
   `wait_exit_double` が `DoubleLeg` の先頭データ（`work = ofNat mw` / `span = reset` /
   `quarter = 0` / `debt = 0`）を与える。`WaitTrace` の snoc/frame を `DoubleTrace` と
   同じ形で作ればよい。
3. `.run` 相：`RunTrace` と `run_exit_frame`。`run_exit_wait_match` が出口の event を縛る。
4. 4 相の選言を `Q` にして `EntryInv Q`。入口節は `run_entry_startRun` により prep 相以外は空虚。
## n197 — `StageCycleSearch`：一周を制御層から切り離した。全域性が残りの全部

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### 既にあったもの（書く前に見つけた）

`PalPeg/CloseoutRunEntriesS.lean` に汎用ドライバが既にあった:

* `run_entry_startRun:87` — `.run` に入る直前のモードは **`.home` に限る**。
  よって run/wait/double/lower/lowerHome/copy の全相で `RunEntryS` は空虚。
* `EntryInv Q:212` / `runEntriesS_of_inv:220` — `searchStep` で保存され各 `.run` 入口で
  `DpSafeStage` を出す `Q` があれば、**`as` の長さにも比較回数にも条件なしで**
  `RunEntriesS as v`。`EntryInv` の実体化はまだ無い（ドライバはある、`Q` が無い）。

空虚性補題を自分で書きかけてたが、`run_entry_startRun` がそれやった。**書かんで済んだ。**

### このターンで書いたもの

`PalPeg/StageCycleSearch.lean`（1 定理、標準 3 公理、全体 build 緑）。

`CloseoutPreload35.postRunF_round_trip_S` は frame 仮説を 5 本（`hsup` / `hsc` / `hp` /
`hclk` / 全ストリームの pacing）取るが、その全部が

```lean
have hph := prefixPhase_of_scan_inv hsup hsc hp hclk.1 hclk.2
have hpa : PacedL 2048 2047 (bs ++ [a3]) := pacedL_suffix_2047 hpaced hph
```

の 1 事実を出すためだけに使われてる。そこで 5 本を `PacedL 2048 2047 (bs ++ [a3])`
1 本に差し替えた `stageCycle_of_runEntry` を切った。**仮説は真に弱い**（操作 (A)）。
結果、一周（`.run` 入口 → run/wait/double 脚 → `PrepAt k (2*mw)` ＋ `StageInvS k (2*mw)`）が
frame・control・`GalilVM` を一切含まん純 `SearchVM` の定理になった。

これが必要な理由: `EntryInv Q` は**任意の**イベント列と**任意の** `searchStep` 後続に量化するので、
`Q` が実機の `ScanTrace` を持つことはできひん。

### 残り（これが全部）

**全域性**: 任意の paced なイベント列を脚（`RunTrace rs` / `WaitTrace ws` / `bs.length = mw`）に
分解すること。`stageCycle_of_runEntry` は脚をまだ仮説として取る。これが出れば

```
Q（ステージ周期不変量）→ EntryInv Q → runEntriesS_of_inv → RunEntriesS（∀ as）
  → readyField2_entry_of_datum から NoReturn が落ちる → StageEntryC.fuel
```

が通る。**今回は何も落としてへん**（公理 3 本のまま、`NoReturn` も残ったまま）。

### 次

1. ステージ周期不変量 `Q` を定義する。2 つの選言（prep 相 = `StagePrepS`、
   run/wait/double 相 = 脚の途中）で、後者は `run_entry_startRun` により入口節が空虚。
2. `EntryInv Q` の prep 半分は `dpSafe_of_stagePrepD_slack` ＋ `stagePrepS_next` で出る。
3. run/wait/double 半分が本体。`searchStep` は各相で関数（`double_step_pos` /
   `wait_step_cases` / `run_step_quanta` はどれも `subst hs` で進む）なので、
   脚の分解は決定的に取れるはず。まずそこを測る。
## n196 — n195 の診断は間違いやった。`NoReturn` が producer の壁（一次情報で確定）

**状態: 全体 build 成功（このターンは編集なし）・標準公理のみ（3 本）・無条件 PAL は未完。**

### n195 の訂正

n195 で「`ReadyPacedS` の `∀ as` が過剰量化で、それが `StageEntryC.fuel` の壁」と書いた。
**過剰量化の測定自体は正しい（消費者は 4 補題しか通らず、任意リストに具体化しない）が、
それは producer の壁やない。**

一次情報 `CloseoutPreload37.readyField2_entry_of_datum:199`:

```lean
have hp : ReadyPacedS (searchLens.get r) (dpEntryG (value last).toNat D) 0 :=
  readyPacedS_restarted hR _ 0
    (fun as hlen hpaced => runEntriesS_of_namedG hR hSE hcl hnr hdep hD as hlen hpaced)
```

`∀ as` は `runEntriesS_of_namedG` が既に捌いてる。詰まってるのは仮説 `hnr : NoReturn u` や。
**`ReadyIface` による `Φ` 抽象化は consumer 側の記録としては有効やが、producer を 1mm も助けへん。**
15 ファイル超の改修に入る前に測って助かった。

### `NoReturn` の正体（`CloseoutPreload6.runEntriesS_of_namedG:231`）

`hnr` の使用は 3 箇所、全部同じ形 `(hnr bs v hreach hne) : ReachL … bs v → ReachP … bs v`。
渡し先は 2 本だけ:

* `CloseoutPreload5.entry_shape:498` — `ReachP` → prep 形（`PrepTrace v0 n v` ＋ 窓の較正）
* `CloseoutPreload5.entry_debt:529` — `ReachP` → 入口債務 `stageDebt Rad k − (bs++[a]).count true`

どちらも `ReachP` を `phase_reach hR hcl hp` に食わせてるだけ。
`NoReturn` は **「restart 起点 `u` からの `ReachL` を `ReachP` に変える変換器」以外の仕事をしてへん。**
偽になる理由も同じで、`.run` を一度通ったら `u` 起点の `ReachP` は破れる。

### `PrepAt` 基底版は既にある

`CloseoutPreload35.dpSafe_of_stagePrepD_slack:145` の中身が一次情報:

```lean
obtain ⟨W, lower, hW, hpreload⟩ := entry_preload_at_prep hp hreach hs hrun
obtain ⟨hcan, hdv⟩          := entry_debt_at_prep   hp hreach hs hrun
```

`entry_preload_at_prep` / `entry_debt_at_prep` が `entry_shape` / `entry_debt` の `PrepAt` 基底版で、
**`NoReturn` を取らへん**。2 つの到達述語は同じ形で基底だけ違う:

| | 到達関係 | 基底 | 追加仮説 |
|---|---|---|---|
| `QG u k D`（Preload6） | `ReachL` | restart `u` | **`NoReturn`**（偽） |
| `StagePrepS k m D slack w`（Preload35:127） | `ReachP` | `PrepAt` 状態 `w` | なし |

### それでも単純な差し替えは効かへん（ここが本当の壁）

`StagePrepS` は `ReachP` やから `.run` を通れへん。`stagePrepS_next` は `hne : v'.mode ≠ run` を要求する。
よって **1 つの `PrepAt` から伸びるのは 1 ステージ分だけ**。
`RunEntriesS as v` は `as` 全体に沿った**すべての** run 入口で `DpSafeStage` を要求するので、
ステージを跨ぐには基底を置き直さなあかん。その置き直しが `CloseoutPreload10.prepAt_of_double_exit`
（`.double` 出口で `PrepAt k (2m)` を再確立）であり、それを鎖にしたのが
`CloseoutPreload36.StageChain` や。

つまり n194 で「2 本の線が食い違う」と書いたものの正体は、抽象化の不足やなくて
**「任意の paced リストに対してステージ鎖が張れるか」という全域性**やった。

### 次（この順）

1. **全域性補題**: `PrepAt k m v` と十分長い paced `as` から `StageChain k m mw' evs tail` を構成する。
   材料は `CloseoutPreload35.postRunF_next_entry:429`（run 入口から次の入口）と
   `doubleTrace_det:489`（double 相の決定性）。`RunEntriesS` の `∀ center v', searchStep …` に
   応えるには決定性が要るので、まず `doubleTrace_det` の届く範囲を測る。
2. 1 が出れば `postRunC_galil_of_boot` で `RunEntriesS` が出て、`runEntriesS_of_namedG` から
   `NoReturn` が落ちる。**公理の下の偽の前提が 1 本減る**（操作 (C)）。
3. `readyField2_entry_of_datum` → `StageEntryC.fuel` は配線済みなのでそのまま通る。
4. 残る boot 段（`k ≤ 1`、窓 8、slack 0）は `CloseoutPreload28` 経路で別途。

`ReadyInterface.lean` は消さへん。consumer 側の過剰量化の測定は事実として正しく、
`StageEntryC.fuel` を将来切り直すときの記録として残す。ただし **今のところ何も落としてへん**。
# 証明スタック（今どこにいるか）

**運用（コウタの指示 2026-09-19）**: 追っている前提を push（このファイルに書く）、
そこからサブ定理に潜るときも push、解けたら pop。**これで自分がどこにいるか忘れない。**

規律（CLAUDE.md より、ここでも効く）:
* **公理の本数は増やさない。** 難しいときはサブ前提を定理として証明し、公理の文を弱める
* **「弱くなった」と書けるのは guard を狭めたときだけ**（n147 の訂正）。
  結論を「十分な前提」に置き換えるのは**弱化ではない**——残差は結論を含意するので
  論理的には強い。それでも前進なのは、残差に **producer が特定済み**で、
  機械レベルの事実に寄っているから。本数が減るのは (C) サブ前提を定理にして
  公理から外したときだけ
* 一次情報だけ。散文・過去の自分の記述・docstring は根拠にしない
* **新しい補題を書く前に `grep -n "^theorem"` を関連ファイルに掛ける。**
  n170 で 4 本を既存の再発明として消した（`CloseoutMismatchCompare` /
  `CloseoutWatchRound4` / `GalilMismatchCaught` を先に読めば書かずに済んだ）。
  とくに `Closeout*` は同じ問題を既に扱っている可能性が高い
* **参照ゼロの宣言を残さない。** 置き換えたら古い方を消す（n170 で 5 本消した）
* `REFUTED` は `False` を導く機械検査済みの定理があるときだけ

---

## 現在のスタック（上が浅い、2026-09-19 n265作業中）

```
[0] GOAL PalPeg.PalInPeg.unconditional : RecognizedByTotalPEG PAL
    残り2公理: obligation_cycleOracleOnPackedRun / obligation_localRealization
[1] obligation_cycleOracleOnPackedRun
    producer: OracleReady.cycleOracleOn_of_readyLeaves
    残差: hfresh / hchain / hshiftPeriodMinimal / hmove
[2] POP hfallbackの実行構成: CanonicalFallbackInput.begin_at_mismatch
    → CanonicalReplay.segment → OracleReady本体への接続。単体Lean検査成功。
    コピー、再開、全replay、MInv、canonical/shaped、費用を構成済み。
    残るhmoveは移動量不等式。公理数は減っていない。
[2] WRITE hchain: WindowRunPack → back/watch、ProgramInv → DP出力 → CopyReady → oracle接続を実装済み。
    未検証。公理1本の全証明を書き終えるまでbuildしない（ユーザー指示）。
[2] PUSH readiness: 有限の任意継続ReadyPacedSを実際の時計creditへ置換する。
    D = 2048*debt + clock。grow: D+3583*work ≥64*span+2*lower+128。
    double: D+383*work+512*quarter ≥64*span+2*lower+128。
    prep残長とDP上限50*window+27をDで支払い、run中のdebt非負を示す。
[待] obligation_localRealization: 具体的LocalStepとencodingは未構成。
```

前ターンは作業方針の確認のみ（no progress）。n264全体buildは既存session 72109
がliveなことを再確認済み。次の全体buildは変更をまとめた後に行う。

### n195: 測定完了——`ReadyPacedS` は過剰量化。インターフェイスに切った

`CloseoutReadyStage` の全消費者が通るのは 4 補題だけ（`ready` / `mono` /
`effect_false` / `effect_true`）。**任意リストへの具体化はゼロ。**
`PalPeg/ReadyInterface.lean` に `ReadyIface P Φ`（4 場）を切り出し、
`readyIface_readyPacedS` で `ReadyPacedS` が満たすことを確認（標準 3 公理）。

**まだ何も外れていない。** `watchSegE_constructS` とその 4 消費者を抽象 `Φ` で
再証明するのが次（機械的だが長い）。そのあと `StageEntryC.fuel` を
`∃ Φ, ReadyIface P Φ ∧ Φ …` に切り直せば、run 線が直接埋められる。

### n194（訂正）: n189 の「背骨を作った」は誇張。線は 2 本あって噛み合っていない

`CloseoutPreload28/35/36` の線は**もともと状態局所**だった
（`dpSafe_of_stagePrepD_slack` の `StagePrepS` は基点が `PrepAt` 状態、
境界は `prepAt_of_double_exit` で再成立）。`StageLocalPrep` が足したのは
包装と、較正仮説を落とした `preloadAt_of_prepPhase` だけ。診断自体は有効。

**本当の壁**: 旧線（`Preload6/8/11/37`）は `ReadyPacedS`（**状態量化**）を出せるが
`NoReturn`（偽）／`PostRun`（producer なし）を要る。新線（`Preload28/35/36`）は
証明できるが run に沿った事実しか出ない。`CloseoutPreload36` 自身が
「run 帰納は `PostRunPh`/`PostRunC` を作れない」と書いている。
**食い違いの場所は `StageEntryC.fuel : ReadyPacedS`。**

→ 次: `ReadyPacedS` が消費者（`segment_of_invLPCS` / `readyPacedS_watchSegE` /
`reachAtC3_of_crossS`、どれも run に沿った watched segment を作る）に対して
**過剰量化していないか**を測る。run 形に切れれば新線が `StageEntryC` を直接埋める。

### n189: `PostRun` と `NoReturn` は同じ欠陥だった（producer 不在の理由が確定）

`StageEntryC.fuel = ReadyPacedS` の producer を辿ると
`CloseoutPreload37.readyField2_entry_of_datum` → `CloseoutPreload6.runEntriesS_of_namedG`
で、そこが `NoReturn` を取る。`NoReturn` は `ReachL` の着地が `ReachP` だと言うが、
`run → wait → double → prepare` の往復を通った歩きは `ReachP` ではない。
`PostRun` も `StagePrep2` の `ReachP w bs v` が段境界で切れることの言い換え。

**つまり形式化ミスは「歩きで書いたこと」**（コウタの
「producerがないときは確実に形式化ミス」がそのまま当たった）。
状態局所に書き直すと段境界を越える: `StageLocalPrep.PrepPhase`（n189、4 定理、標準公理）。

    prepPhase_of_double_exit : .double 出口 → PrepPhase k m 0 t'

### 次にやること（n189 時点）

1. 状態局所の `Q` を作って `CloseoutPreload6.runEntriesS_of_preloadInvG`
   （`EntryPreloadG Q k` → `RunEntriesS`）に食わせる。`Q` の中身:
   `PrepPhase k m n v`（済） ＋ **負債の下界** ＋ **供給・ペーシングの帳簿**（未）
2. 負債: `∃ adv, 2048*adv ≤ prepLen k ∧ stageDebt Rad k + stageCredit k m - adv ≤ value v.search.debt`
   ——状態局所に書ける。保存は 1 手で debt が最大 1 減ることから
3. 供給: `dpEvents (m+1) ≤ as.length` を段境界で再供給する
   ——ここだけが本当の算術（`CloseoutPreload35` §3 の `8 ≤ mw < 32`）

### n190: 算術の穴 3 つのうち 1 つを閉じた

`CloseoutPreload7.depth_exceeds_prepLen`（機械検査済みの否定的結果）は
`runEntriesS_of_namedG` の `D ≤ prepLen k` が満たせないことを言っていた。
`D ≤ prepLen k` の唯一の使い道 `budget_adv` の `2048*adv ≤ prepLen k` を
**実際の深さ `prepLen k + max k 1 + 1` ちょうど**に緩めて再証明した
（`StageBudgetShift.budget_adv_nat_shift` / `budget_adv_shift`、標準 3 公理）。
`k ≤ 8` は 9 ケース手計算（`k=1,2,3,5,6` で余裕 0）、`k ≥ 9` は緩い上界で足りる。

### n191: 2 つめの穴を `k ≤ 3` に縮めた

`CloseoutPreload35` §3 の残差記録「`8 ≤ mw < 32`」は両端とも間違いだった。
同じ入力で `16 ≤ mw` から成立する（`StageBudgetShift.bal_of_paced_slack_S16`）。
`mw ≤ 3` は較正が空虚にする。**真の残差は `4 ≤ mw ≤ 15` ＝ `k ≤ 3`**
（`window_covered_of_k` / `window_residual`）。

### n192: 本線に入れた。残差は `k ≤ 1` の第 1 段だけ

`CloseoutPreload35.bal_of_paced_slack_S` 自体を `16 ≤ mw` に下げ、下流
（`postRunF_*`、`CloseoutPreload36` の 10 箇所）も緩めた。
`postRunF_step` は較正 `8 * max k 1 ≤ mw` を持つので覆われるのは `k ≥ 2`、
残差は `k ≤ 1`。さらに窓は倍々（`mw0 = 8 * max k 1`）なので
**残るのは第 1 段（窓 8）だけ**。

### n193: 穴 2 は boot 段だけ。しかも boot は slack 0

boot は `lower = 0` → 窓 `8`、以降倍々。しきい値 16 で第 2 段以降は全部覆われる
（`boot_windows_covered`）。boot 段は `initial delay` の `clock = delay` で
**slack 0** なので、`CloseoutPreload28`（`dpDemand`、`8 ≤ mw`）が使える。
→ 算術としては両側に材料がある。**残るのは配線と boot datum。**

残り: (3) 段境界のイベント供給（`StageLegs` の `hlen`）、
`CloseoutPreload36` の boot datum、boot 段を Preload28 経路で通す配線。

### n176: 残り 3 本のうち 2 本が同じ底を共有している（実測）

`obligation_shiftPalResiduesAlongRun` の 3 残差の producer を辿ると全部
**found 経路の底**に集まる:

    (a) H_readsShift             → first_round（第 1 shift）／RoundHistory（以降）
    (b) H_freshShiftAtShiftEntry → first_round
    (c) FreshShiftLedger         → prep_of_prepInputsG3 の Candidate ＋ 着地 watch

そして found 経路の入口は `CloseoutPrepInputs3.prepInputs3_of_found_or_later` で、
その 2 大入力が **`StageEntryC`** と **`SegReachedW`**。両方とも producer がゼロ
（`grep` で consumer しか出ない）。ただし:

| 入力 | `InvLPC` からの差 |
|---|---|
| `SegReachedW` | `GalilInvPlus.segment_of_invLP`（`InvLP` から区間を出す）がある。残る名前付き仮説は `hlive`（`GalilOracleLeaves2.hlive_of_invLPC` で無償）と `hends`（CLAUDE.md §3 で**閉**）。`hsegmentM`（`segment_of_invLPC` ＋ `hends_C`）も **閉** |
| `StageEntryC` | **`= InvLPS ＋ ReadyFuel`**（`CloseoutContracts:65`）、`InvLPS = InvLPC ＋ ReplayStage`。差は **`ReplayStage` ＋ `ReadyFuel` の 2 つだけ** |

**`ReplayStage` と `ReadyFuel` は CLAUDE.md §3 が `obligation_cycleOracle` の
残り葉として挙げている `hstage` と `hpres` そのもの。**
つまり 3 本のうち 2 本（`shiftPalResiduesAlongRun` と `cycleOracle`）が
**同じ 2 つの葉で詰まっている**。

### 次の一手（(A) の操作：公理を弱める）

`obligation_shiftPalResiduesAlongRun` の仮説を `InvLPC` から **`StageEntryC`**（または
`InvLPS`）に強める＝**公理は弱くなる**。ただし消費者
（`CloseoutMarksPack.packRunR_MW_marksFree` → `PackRunRMW`）が `InvLPS` を供給できることが条件。
CLAUDE.md の記述では `CycleOracleMC3` は origin/着地とも `InvLPS` なので、
**文脈上は `InvLPS` が来ている可能性が高い**（未検証——`PackRunRMW` の呼び出し元を辿って確認する）。

**済（n177）**: `PackRunRMW` を `InvLPS` に上げた。`h_oracleIMW_of_MC3_W:148` が
`hI : InvLPS` を持ちながら `hI.1` だけ渡していた（destructure して捨てる）ので、
`ReplayStage` はその場で無償だった。全体 build 緑。

**残る差は `ReadyFuel` 1 つ**（`StageEntryC = InvLPS ＋ ReadyFuel`）。
`SegReachedW` は `GalilInvPlus.segment_of_invLP` ＋ 既に閉じている `hlive`/`hends`。

### n178: `ReadyFuel` は素朴な形が 2 つとも**機械検査で偽**（書く前に探して助かった）

`StageEntryC = InvLPS ＋ ReadyFuel` の残る差 `ReadyFuel` を攻めようとして、
先に producer を探した。結果:

| 候補 | 状態 |
|---|---|
| `GalilReplaySpan.RunEntriesAtBegin` | **偽**（`CloseoutReadinessAudit.not_runEntriesAtBegin`、機械検査済み） |
| `GalilReplaySpan.RunEntriesPaced 2048` | **偽**（`CloseoutRunEntriesPaced`、機械検査済み） |

`readyFuel_of_stage`（`GalilReplaySpan:3764`）は `ReplayStage` ＋ `RunEntriesAtBegin` から
任意の `n K` で `ReadyFuelD` を出すが、**その第 2 入力が偽**なので使えない。

理由（`CloseoutRunEntriesPaced` の冒頭、一次情報）:
`RunEntriesAllD` は `.run` 入口で残り全部に `DpSafeRem` を要求し、
`DpSafeRem v as → as.count true ≤ value v.debt`。つまり**固定の債務で
いくらでも長い tail を払え**と言っている。pacing は比較の**頻度**を縛るが**回数**は縛らない。

**正しい形**（同ファイルが明記）:

    RunEntriesPacedS delay : … → StageEntry Rad last →
      ∀ av, (advances delay delay (av.map (·, true))).count true ≤ stageDebt Rad →
        RunEntriesAllD (advances delay delay (av.map (·, true))) v

`stageDebt Rad k = 2 * max k 1 - Rad`（`CloseoutPreload11:109`）。
つまり **stage 債務の会計**が要る。`CloseoutPreload11` が `stageDebt` ＋ `stageCredit` で
それを展開している。

**教訓**: `ReadyFuel` を「証明しにいく」前に探したので、偽の命題を証明しようとして
無駄にする事故を避けられた。CLAUDE.md の「まず証明を書こうとする」は
「先に既存の反証を探す」と両立する。

### n179: `ReadyFuel` 近傍の地図（実測、これ以上掘る前に見るもの）

`StageEntryC.fuel : GalilSegmentConstructB.ReadyFuel (searchLens.get r)
(headRank r.right * 2048 + c.clock) (headRank r.right)` の producer を探した結果:

| 項目 | 状態 |
|---|---|
| `ReadyFuel` そのものの producer | **無い**。`CloseoutWatchRound11:191,216` / `CloseoutReportCase:322` はどれも仮説として取っている |
| `readyFuel_restarted`（`GalilSegmentConstructB:109`） | `Restarted` ＋ `hE : ∀ as, n ≤ as.length → as.count true ≤ K → RunEntriesAll as …` から出す。**`hE` が残差** |
| `readyFuel_of_stage`（`GalilReplaySpan:3764`） | `ReplayStage` ＋ `RunEntriesAtBegin` から。**`RunEntriesAtBegin` は偽**（n178） |
| **正しい形の機械**（`CloseoutPreload11`） | `runEntriesS_of_restartS2:327` が `Restarted` ＋ `StageEntry` ＋ `CentreLongAt` ＋ `DepthAt` ＋ `PostRun` から `RunEntriesS as` を出す（条件は `D + dpEvents(…) ≤ as.length` ＋ `PacedL 2048 0 as`）。`readyClosure_S2:347` がそれを `ReadyClosure … RdPaced` に束ねる |
| その底 | `PostRun`（`CloseoutPreload8`）と `RestartS2`（`CloseoutPreload11:320`）。**どちらも producer 無し** |
| `ReadyClosure` の消費者 | `CloseoutWatchRound28.replayRunC_of_decodes`（**replay 経路**。`StageEntryC.fuel` ではない） |

**通貨が 3 つある**: `RunEntriesAll`（`GalilLeafPres:228`）/ `RunEntriesAllD`
（`GalilReplaySpan:3685`）/ `RunEntriesS`（`CloseoutPreload*`）。
`ReadyFuel` は `RunEntriesAll`、`ReadyFuelD` は `RunEntriesAllD`、
`CloseoutPreload11` の機械は `RunEntriesS`。**橋が要る。**

条件の形も違う: `ReadyFuel` は `as.count true ≤ K`（マッチ回数の上界）、
`runEntriesS_of_restartS2` は `PacedL 2048 0 as`（比較の間隔）。
長さ `headRank * 2048 + clock` の paced 列なら true の個数は `headRank` 程度なので
**方向としては噛み合うはず**（未検証）。

**次にやること**: (1) 3 つの `RunEntries*` の関係を一次情報で確認する、
(2) `PostRun` と `RestartS2` の中身を読んで producer が本当に無いか確かめる。
**どちらも「書く」前に「読む」作業。**

### n180 → n181: **`StageEntryC.fuel` は偽**（`PalPeg/ReadyFuelRefute.not_readyFuel_v0` で機械検査済み。以下は n180 時点の推論、結論は確定した）

n179 の地図に従って `ReadyFuel` を展開した（一次情報）:

    ReadyFuel v n K  := ∀ as, n ≤ as.length → as.count true ≤ K → SearchReadyB v as
                                                                  (GalilSegmentConstructB:71)
    SearchReadyB v as := ReadyRem v as ∧ RunEntriesAll as v        (GalilLeafPres:237)
    RunEntriesAll     := GalilSearchReadyInv.RunEntry の ∀-閉包     (GalilLeafPres:228)
    RunEntry c a v v' as := searchStep … → v.mode ≠ .run → v'.mode = .run → DpSafeRem v' as
                                                                  (GalilSearchReadyInv:161)
    DpSafeRem v as := ∃ w lower s0 bs, … ∧ ((bs ++ as).count true : ℤ) ≤ value s0.debt ∧ …
                                                                  (GalilSearchReadyInv:53)

**つまり `.run` 入口の債務 `s0.debt` が、以後のマッチを全部払えと要求している。**

`StageEntryC.fuel`（`CloseoutContracts:68`）の `K` は `headRank r.right`——
右ヘッドの残り段数。一方 `CloseoutRunEntriesPaced` の監査が一次情報で確定させたのは
「`initialDebt reset = reset`、`begin` が dispatch する grow tick 1 回で `+2`、
よって `.run` 入口の債務は **2**」。

**`headRank r.right ≥ 3` になる入力（長さ数文字以上）で `StageEntryC.fuel` は成り立たない
はず。** これは `RunEntriesAtBegin` / `RunEntriesPaced 2048` が偽である理由と**同型**で、
どちらも機械検査済み（`CloseoutReadinessAudit` / `CloseoutRunEntriesPaced`）。

**n181 で確定した**: `PalPeg/ReadyFuelRefute.not_readyFuel_v0` が
`¬ ReadyFuel v0 n (paced.count true)` を機械検査で示した（標準 3 公理のみ、
証人は `CloseoutRunEntriesPaced` のものをそのまま使用、新規証人ゼロ）。
`readyFuel_mono` より、`paced.count true`（= 3）以上の `K` ではすべて偽。

### 帰結（`PROOF_STACK` の見立ての訂正）

n176 で「`StageEntryC = InvLPS ＋ ReadyFuel` なので残る差は `ReadyFuel` 1 つ」と書いたが、
**その `ReadyFuel` が埋めるべき穴ではなく偽の契約である可能性が高い。**
found 経路の入口 `prepInputs3_of_found_or_later` が `StageEntryC` を取っている以上、
そこも切り直しが要る。

### 次にやること（優先順）

1. ~~**反証を試みる**~~ → **済（n181）**: `PalPeg/ReadyFuelRefute.lean`
2. 切り直しの形: `RunEntriesS`（`CloseoutReadyStage:444`、`DpSafeStage` で**stage で切った**版）が
   正しい通貨。`CloseoutPreload11.runEntriesS_of_restartS2` が既にそれを出している
3. `StageEntryC.fuel` を `RunEntriesS` 系に差し替えた `StageEntryS` を作り、
   消費者（`reachAtC3_of_crossF_C` など）を追従させる

**注意**: `RunEntriesAll`（`GalilLeafPres:228`）と `RunEntriesAllD`（`GalilReplaySpan:3685`）は
**同じ定義の重複**（どちらも `GalilSearchReadyInv.RunEntry` の ∀-閉包）。
`ReadyFuelD` の docstring も「`GalilSegmentConstructB.ReadyFuel`, restated」と書いている。
通貨は実質 2 つ（`…All` 系と `…S` 系）。

### n182: 切り直しの設計が確定（`ReadyFuel` → `ReadyClosure`、置換は 1:1）

**消費者が `hready` から取り出しているのは最終的に `SearchReady` だけ**（実測、
`CloseoutReportCase:380-390`）:

    readyFuel_mono → readyFuel_watchSegE → readyFuel_ready → SearchReady (searchLens.get s1)

つまり `ReadyFuel` は「区間に沿って `SearchReady` を運ぶ乗り物」で、
その乗り物が偽だった（n181）。**正しい乗り物は既にある**:

    structure ReadyClosure raw P q first delay (Rd : Control → GalilVM → Prop) : Prop where
      ready   : ∀ c s, Rd c s → SearchReady (searchLens.get s)
      seg     : ∀ es c c' s t, WatchSegE … es c s c' t → t.chain = .idle → Rd c s → Rd c' t
      restart : ∀ c u Rad last, c.mode = .scan → c.clock = delay →
                  Restarted raw u Rad last → StageEntry Rad last → Rd c u
                                                        (`GalilReplaySpan:5621`)

### 置換表（1:1、しかも `ReadyClosure` 側は燃料の算術が無いぶん簡単）

| 旧（偽） | 新 |
|---|---|
| `ReadyFuel (searchLens.get r) (headRank … * 2048 + c.clock) (headRank …)` | `Rd c r` |
| `readyFuel_watchSegE h ht n K` | `hcl.seg es c c' s t h ht` |
| `readyFuel_ready` | `hcl.ready` |
| `readyFuel_restarted` | `hcl.restart` |
| `readyFuel_mono` | **不要**（`Rd` に燃料の指標が無い） |

`readyFuel_watchSegE`（`CloseoutReportCase:87`）と `ReadyClosure.seg` は
**仮説の形がそのまま同じ**（`WatchSegE` ＋ `t.chain = idle`）。

### 手順

1. **済（n184）**: `StageEntryC.fuel` を `ReadyPacedS … (2048 - c.clock)` に差し替え
2. **不要だった**: `CloseoutReadyStage.reachAtC3_of_crossS:945` と
   `reachAtC3_of_target_matchS:841` が**既に存在していた**（docstring の
   「§5–§6 re-prove … on `ReadyPacedS`」は計画ではなく完了報告）
3. **済（n184）**: `reachAtC3_of_crossF_C` を `reachAtC3_of_crossS` に向け直した
4. found 経路の入口（`CloseoutPrepInputs3.prepInputs3_of_found_or_later`）の
   `StageEntryC` を `StageEntryS` に
5. `Rd := RdPaced` を選べば `CloseoutPreload11.readyClosure_S2` が producer。
   その底は `PostRun` ＋ `RestartS2`（**どちらも producer 無し、次の的**）

**注意**: これは (A)（弱化）ではなく**偽の契約の修理**。`StageEntryC` を要求している
定理は全部「空虚に真」なだけで使えない状態だった。

### n183: **`ReadyFuel` の API 全体に `ReadyPacedS` の双子がある**（切り直しは機械的）

n182 の置換表を一次情報で確認したら、**`CloseoutReadyStage` に対応物が全部そろっていた**:

| 旧（`ReadyFuel`、偽） | 新（`ReadyPacedS`） |
|---|---|
| `readyFuel_ready` | `readyPacedS_ready`（`CloseoutReadyStage:496`） |
| `readyFuel_mono` | `readyPacedS_mono`（`:499`） |
| `readyFuel_effect_false` | `readyPacedS_effect_false`（`:504`） |
| `readyFuel_effect_true` | `readyPacedS_effect_true`（`:513`） |
| `readyFuel_restarted` | `readyPacedS_restarted`（`:523`） |
| `readyFuel_watchSegE` | `readyPacedS_watchSegE`（`:778`） |

### なぜ `ReadyPacedS` は反証されないか（本質）

    ReadyFuel   v n K := ∀ as, n ≤ as.length → as.count true ≤ K       → SearchReadyB v as
    ReadyPacedS v n k := ∀ as, n ≤ as.length → PacedL 2048 k as        → SearchReadyS v as

* 第 2 指標が **`K` = マッチ予算（`headRank`＝入力長に比例）** から
  **`k` = クロック由来の slack（`2048 ≤ c.clock + k`）** に変わった
* 結論が `SearchReadyB`（`DpSafeRem`＝残り全部）から
  `SearchReadyS`（`DpSafeStage`＝**stage で切った**）に変わった

**債務 2 で入力長ぶんのマッチを払え、という要求が消えている。** これが n181 の反証を
受け付けない理由で、`CloseoutPreload11.readyClosure_S2` が実際に producer を出せている理由。

### 切り直しの残り作業（完全に特定済み）

1. `CloseoutContracts.StageEntryC.fuel` を `RdPaced c r` に差し替え（`StageEntryS`）
2. `CloseoutReportCase.reachAtC3_of_crossF`（`:316`〜）と
   `reachAtC3_of_target_matchF`（`:196`〜）を上の置換表で再証明。
   **注意**: `readyPacedS_watchSegE` の結論は `∃ k', 2048 ≤ c'.clock + k' ∧ …` で
   `readyFuel_watchSegE` より 1 段包んである（`RdPaced` の `∃ n0` がそれを吸収する）ので、
   純粋なテキスト置換ではなく `obtain` を 1 つ挟む
3. `CloseoutContracts.reachAtC3_of_crossF_C` と found 経路の入口を追従
4. producer は `CloseoutPreload11.readyClosure_S2`（底は `PostRun` ＋ `RestartS2`）

### n185: `PostRun` / `RestartS2` の地図（`readiness` 部分系、最深部）

`StageEntryC` は修理できた（n184）。次の底は `RdPaced` の producer
`CloseoutPreload11.readyClosure_S2` が取る 2 つ:

    PostRun := ∀ v as, v.search.mode = .run → DpSafeStage v as → RunEntriesS as v
                                                       (`CloseoutPreload8:253`)
    RestartS2 raw := ∀ u Rad last, Restarted raw u Rad last → StageEntry Rad last →
      ∃ D ≤ prepLen (value last).toNat, CentreLongAt … ∧ DepthAt (searchLens.get u) D
                                                       (`CloseoutPreload11:320`)

| 項目 | 状態 |
|---|---|
| `PostRun` の変種の鎖 | `postRunP_of_postRun`（`Preload17:71`）/ `postRunC_of_postRunP`（`Preload24:89`）/ `postRunPh_of_postRunP`・`postRunC_of_postRunPh`（`Preload30:106,109`）/ `postRunC'_of_double_leg`（`Preload26:143`）——**全部「変種 → 変種」** |
| 帰納段 | `CloseoutPreload35.postRunF_step`（1 つの `.run` 点から次へ） |
| 脚のデータ | `CloseoutPreload36.StageLegs`（`postRunF_step` が読む形） |
| **基底** | **無い**（`PostRun*` を仮説なしで出す定理は 1 本も無い） |
| `RestartS2` | **producer 無し** |
| ファイル数 | `CloseoutPreload1`〜`41`。**プロジェクト最深部** |

`CloseoutPreload41` の冒頭は replay 半分の 3 つの所見（`ReadyFieldP4` は不要、
`hpresRep` は普遍なので反証、…）で、**まだ基底に到達していない**。

**次にやること**: `postRunF_step` ＋ `StageLegs` の帰納が何で止まっているかを
`CloseoutPreload35` / `36` の冒頭で確認する。CLAUDE.md n49 の
「readiness は `ScanRealized` 矛盾で `PostRunPh/F` へ再基底化中」がその記録。

### n186: `PostRunF` 帰納の**具体的な穴**が出た（`8 ≤ mw < 32` の窓）

`CloseoutPreload35` の冒頭（一次情報）:

* §6 **`postRunF_step`** は存在する——「1 つの `.run` 入口の datum から次の入口の datum へ」
* §5 `postRunF_next_entry` — dispatch 状態 → 準備脚 → 入口 tick で次の datum
* §3 **ここが穴**: 「the `.double` exit satisfies `StageInvS` when `32 ≤ mw`
  (`bal_of_paced_slack_S`, `stageInvS_of_double_exit`); **the four windows
  `8 ≤ mw < 32` do not absorb the two extra units at slack `2047`**」

### 穴の大きさ（計算）

窓は restart で `mw = 8 * max k 1`、`.double` で倍々。だから

    8 ≤ mw < 32  ⟺  k ≤ 3（の初期 stage、倍化 0〜1 回まで）

**つまり穴は「lower bound `k` が 3 以下の初期 stage」だけ**で、`k ≥ 4` なら
`8k ≥ 32` で §3 が閉じる。境界ケース 4 つ（`mw ∈ {8, 16}` × 位相）。

### 追加の穴: 帰納の基底

`postRunF_step` は帰納段。**基底（boot / restart 後の最初の `.run` 入口の `PostRunF` datum）を
出す定理は見つかっていない。** `CloseoutPreload.run_entry_preload:130` は
`.run` 入口の DP 機械が `GalilScaffoldPreload.initial w lower` であることを言う
**局所事実**で、基底ではない。

### 次にやること（優先順）

1. `stageInvS_of_double_exit` の `32 ≤ mw` 条件を、`8 ≤ mw < 32` の 4 窓について
   別途詰める（`dpDemandS k m := (prepLen k + 2047)/2048 +
   (prepLen k + 2047 + dpEvents (m+1))/2048 + 1` の算術。`CloseoutPreload35` §2）
2. 基底を探す/作る: restart 直後（`Rad = 0`, `k = value last`）の最初の `.run` 入口
3. 1 ＋ 2 ＋ `postRunF_step` で `PostRunF` の帰納を閉じ、`PostRun` へ落とす

**これが `shiftPalResiduesAlongRun` と `cycleOracle` の共通の底の最後。**

### n187: **`PostRun` に producer が無い理由が割れた**（コウタ「producer がないときは確実に形式化ミス」）

    PostRun := ∀ v as, v.search.mode = .run → DpSafeStage v as → RunEntriesS as v
                                                              (`CloseoutPreload8:253`)

**`∀ v as` が run にも供給条件にも縛られていない。** 落としているものが 2 つある:

| 消費者が持っているもの | `PostRun` の文 |
|---|---|
| `PacedL 2048 0 (bs ++ as)`（`StagePrep2`） | **無い** |
| `D + dpEvents (m+1) ≤ bs.length + as.length`（供給＝列が十分長い） | **無い** |

そして**短さで落ちることは既に機械検査済み**:

    CloseoutPreload3.not_runEntriesS_eight : ¬ RunEntriesS (List.replicate 8 false) v0

節タイトルが「**`RestartEntryS` is false: the paced list may be too short**」。
8 番目のイベントで `.run` に入ると残りが `[]` になり、`DpSafeStage (w p8) []` の
課金プレフィックスが空になって `dpSafeStage_pre_ne_nil` に当たる。

**同じ証人が `PostRun` も落とす**（`v := w p8` 相当の `.run` 入口で残りを空にすればよい）。
→ **`PostRun` は偽の疑いが濃い**（まだ `False` を導く定理は書いていないので `REFUTED` とは書かない）。

### なぜ帰納が止まっていたか（構造）

    StageInv2 k m D w v as := StagePrep2 k m D w v as ∨ RunEntriesS as v
    runEntriesS_of_stageInv2 … (hpost : PostRun) : ∀ as v, StageInv2 … as → RunEntriesS as v

`as` に帰納しているが、`.run` 入口の枝で `hpost v' as hr hsafe` を使うので
**`as` が縮まない**。そこを global 仮説で埋めてある。
`.run` 相でもイベントは消費されるので、本来は `as.length` の整礎帰納で閉じられるはず——
**ただし各 stage 入口で「残りが十分長い」が要る**。それが上の落とした供給条件。

### 正しい形（切り直しの方向）

* 供給条件は**per-stage** でないといけない（global な `as.length` の下界では
  後段の stage を保証できない）
* 「各 stage 入口で残りが十分長い」は **run に沿ってしか言えない**
  （入力が続く限りイベントが来る、という run の性質）
* → **`PostRun` は trace/run 形の義務に切り直す**。CLAUDE.md の
  「global 形は原理的に落ちない」がそのまま当てはまる

### 次にやること

1. `PostRun` の反証を書く（`not_runEntriesS_eight` の証人を `.run` 入口に合わせる）
2. run 形 `PostRunAlongRun`（trace の各 `.run` 入口で、残りイベント数が
   `dpEvents (m+1)` 以上）に切り直す
3. `runEntriesS_of_stageInv2` を整礎帰納で書き直し、`hpost` を外す
   * **原子は済（n188）**: `PostRunInduction.runEntriesS_cons_of_run`——
     `.run` 相の 1 手で `RunEntriesS` が縮む（`RunEntryS` は源が `.run` なら空虚）
   * 材料: `CloseoutPreload13.RunTrace` / `run_step_quanta` / `run_exit_frame`、
     `CloseoutPreload35.postRunF_next_entry` / `postRunF_step`

### n175 の教訓（これが一番大事）

**44 本書いて計器は 1 本も動かなかった。0 本書いて 1 本外れた。**
コウタの「定理ふえすぎてへん？ほんとうに必要？」の直後にこれが出たのは偶然ではない。
**既存部品を探す姿勢に切り替えたから見つかった。**

以後: **新しい定理を書く前に、その繋ぎを既にやっているファイルを探す。**
とくに `BranchSupply` / `Closeout*` は同じ形の配線を既に持っている可能性が高い。

---

## 構造的な発見（n147、これが本筋）

**残差 3 つは全部「chain の誕生時に立つ事実を run に沿って運ぶ」に帰着する。
1 個の部品で 3 つ同時に落ちる。**

| 残差 | 誕生時の producer | 運ぶ機構 |
|---|---|---|
| `H_readsShift` | `first_round` → `Entry`/`OriginAt`（無条件） | `CloseoutOriginRounds.originAt_of_rounds` / `CloseoutRoundSeg.originAt_of_roundSeg` |
| `H_freshShiftAtShiftEntry` | `first_round` 自身 | 同じ（最初のラウンドだけ） |
| `FreshShiftLedger` ① | `CloseoutFoundBackground` → `Candidate` ＋ `1 ≤ h` ＋ `value radius ≤ 2h` | 同じ |

さらに **CLAUDE.md §1 の壁 (1) `ScanToScan` は要らない**（`Workbench.lean:425` の
見立てが正しい）。`PalPeg/MatchedRunSnoc.lean` が区間抽出なしで run から
`ScanSeg` を作る道具を揃えている:

* `scanSeg_snoc_tick` — scan 相の `Tick` 1 手を `ScanSeg` に吸収（出口 3 つ:
  伸びる / mode が scan を離れる / chain が壊れる）
* `scanSeg_of_steps` — それを `Steps` に沿って反復。側条件は `hScanWatchAll`
  （その区間の全点が scan ∧ 非 replay ∧ watch ∧ `singlePositive cycle = false`）
* **`onlyMatchedRun_of_steps`** — 射影まで一気に。`CompareRounds.next` の第 1 引数

そしてラウンドの閉じ方は `GalilScaffoldTopRoundS.round_next`（無条件）が
`ScanSeg` ＋ 終端比較 ＋ shift から `CompareRounds h (toOnly s w0) 1 (toOnly · v)`
を出す。`CloseoutRoundSeg.RoundSeg` はまさにこれ。

### なぜ「状態局所な不変量」では駄目か（測定済み）

ラウンド境界（`scan_shift`）で origin を貼り替えるには
`CompareRounds h (toOnly s w0) 1 (toOnly s' v)`——**ラウンド 1 周ぶんの履歴**が要る。
1 手の `Tick` からは作れない。だから不変量は**履歴を持ち歩く**形でないと閉じない。

### 次に作る部品（設計）

```
RoundHistory P q first delay w (c : Control) (s : GalilVM) : Prop :=
  ∃ (n : ℕ) (c₀ : Control) (s₀ : GalilVM),
    ScanSeg P q first delay n c₀ s₀ c s ∧          -- ラウンド内の履歴
    OriginAt w s₀ ∧                                -- ラウンド起点の origin
    s₀.periodOnly = true ∧
    (∃ w₀, s₀.chain = ChainVM.watch w₀ ∧ zero w₀.lag = true)
```

* **tick 保存**: `scan_wait`/`scan_count`/`scan_match` は `scanSeg_snoc_tick` で
  `ScanSeg` を伸ばすだけ（起点は不変）。`scan_shift` は `round_next` で
  `CompareRounds` を作り、`originAt_of_roundSeg` で**起点を貼り替える**
* **`H_readsShift`**: `originShift_of_roundSeg` に流す
* **基底**: chain 誕生（found 経路）で `first_round` が `Entry` を出す

**これが `hSP` 2 本（run 形・trace 形）の残り全部。**

### 進捗

* **済（n148）**: `PalPeg/RoundHistory.lean` — `RoundHistory` ＋ 起点 ＋ tick 保存 ＋
  run 沿い ＋ 射影取り出し（5 宣言、標準 3 公理のみ、全体 build 緑）。
  **計器は動いていない**（これは足場で、(C) ではない）
* **次（特定済み・未着手）**: `chain_shift_period`——
  `ChainShiftRun s w cycle n t v finish → periodLength v = periodLength w`。
  **存在しない**。`chain_shift_lag`（`GalilScaffoldTopRounds:19`）と
  `chain_shift_phase`（`GalilScaffoldChainReadOrigin:451`）が同じ帰納法なので同型に通る。
  `ChainShiftRun.next` の 1 手は `chainShiftOne w`、これが period テープの
  `left.length + right.length` を変えないことを示す
* **済（n149）**: `chain_shift_period` / `chain_shift_periodLength` /
  `chain_shift_period_focus`（`RoundHistory.lean` 内）。
  `chainShiftOne`（`GalilScaffoldChainInputSupply:1478`）が変えるのは
  `distance`/`boundary`/`last`/`margin` **だけ**なので period テープは shift を通して不変。
  前 2 本は **公理ゼロ**
* **次（大物）**: ラウンド境界。`GalilScaffoldTopRoundS.round_next` の入力を run からそろえる

### `round_next` の入力と出どころ（○=確認済み / △=未確認 / ✗=無い）

| 入力 | 出どころ | 状態 |
|---|---|---|
| `hseg : ScanSeg P q first delay n c s c1 s1` | `RoundHistory` の第 1 場 | **○** |
| `w0` ＋ `hp0 : s.periodOnly = true` ＋ `hs0 : s.chain = .watch w0` ＋ `hz0 : zero w0.lag = true` | `RoundHistory` の残りの場 | **○** |
| `hm1 : c1.mode = .scan` / `hr1 : replaying = false` / `hc1 : c1.clock = 1` | `scan_shift` tick 構成子（`GalilScaffoldTop:123`：`hm` / `hr` / `hc`） | **○** |
| `w` ＋ `hs1 : s1.chain = .watch w` | 呼び手（run の scan∧watch 区間） | **○** |
| `hav : canRight s1.right` | `Extra7.scanAvail`（`mode = scan ∧ ¬replaying`） | **○** |
| `hcmp` / `hmis` / `hq` | `scan_shift` の `hcmp` / `hmt` ＋ `compare_mismatched_parts`（`MatchedRunSnoc:406`） | **○** |
| `hend : singlePositive s1.cycle = true` | `shiftGuardVM` の `if periodOnly then singlePositive cycle = true` 節。`RoundHistory` が `periodOnly = true` を持つ | **○** |
| `hpred : read (right s1.right) = symbol w…period.focus` | `shiftGuardVM` の最後の節。**n152 で確認済み**: `afterMismatch s vs vq = {searchLens.set (scanLens.set s vs) vq with radius := radiusAfter s}` なので right は `vs.right = right s1.right`。compare 前/後の watch の差は lag ゼロなら消える（`RoundHistory.watch_eq_of_mismatch_lagZero`） | **○** |
| `hlen : Canonical s1.length` | `LPackM2` / `RadLedger` 側（`hlc0` と同種） | **△** |
| `hg : P.shiftGuard (afterMismatch s1 vs vq)` ＋ `s2` ＋ `hb : P.beginShift …` | `scan_shift` の `hg` / `hb` | **○** |
| `hs2 : beginShiftVM h w (afterMismatch …) s2` | `beginShiftVM' s t := ∃ w, beginShiftVM (periodLength w) w s t`（`GalilScaffoldTopGuards:35`）。よって `h = periodLength w` | **○** |
| `hi2 : CopyIdle s2` | `AuxPack`（`roundBundle_tick` の `hci : mode = shift → CopyIdle`） | **○** |
| `hchain : ChainShiftRun ⟨s1.center, left s1.left, ofNat h, inc s1.radius, inc (inc s1.length)⟩ (immediate w) reset h t' v cycle` | **`RoundHistory.chainShiftRun_of_steps`（n151 で作った）**。基底は `beginShiftVM` が `chain := .watch (immediate w)` / `remaining := ofNat h` / `cycle := reset` を置くので `.stop` でタダ | **○** |
| `o` ＋ `ho : refresh …` | `shift_done` の `o` / `ho` | **○** |

**~~つまりラウンド境界の残りは `ChainShiftRun` の収集 1 個。~~ → n151 で作った。**
**n152 で `hpred` も確認済み。未確認は `hlen : Canonical s1.length` の 1 個だけ**（`LPackM2` / `RadLedger` 側から出る見込み）。
found 経路の `CloseoutWatchRound33` / `37` も `ChainShiftRun` を**仮説として取っている**
（`ShiftRoundInvCL` / `ShiftOriginRestCL` は open な `def`）ので、ここは共通の穴。

設計（次に作る）:

```
ShiftHistory P q first delay (c : Control) (s : GalilVM) : Prop :=
  ∃ (k : ℕ) (c1 : Control) (s1 : GalilVM) (vs : ScanVM) (vq : SearchVM)
    (w : GalilScaffoldChainWatch.State) (s2 : GalilVM) (t' : ShiftState)
    (v : GalilScaffoldChainWatch.State) (cycle : Counter),
    -- ラウンド終端の比較と shift 入口
    … ∧ beginShiftVM (periodLength w) w (afterMismatch s1 vs vq) s2 ∧
    -- ここまでに済んだ shift の k 手
    ChainShiftRun (shiftLens.get s2) (immediate w) reset k t' v cycle ∧
    s = shiftLens.set s2 ⟨t', .watch v, cycle⟩
```

`shift_one` tick で `k` を 1 増やし（`ChainShiftRun.next`）、`shift_done`
（`¬ remainingPos`）で `k = periodLength w` が確定して `round_next` に流す。

### `ShiftHistory` の部品の状況（n150）

**済**（`PalPeg/RoundHistory.lean`、全体 build 緑）:

* `chainShiftRun_snoc` — `ChainShiftRun` を後ろから 1 手伸ばす。**公理ゼロ**
* `chainShiftRun_snoc_shiftOne` — `shiftOne` 関係 1 手を吸収。
  `Tick` の 23 構成子は場合分けしない（消費者側でやる）

**一次情報で確認した形**:

* `shiftOne`（`GalilScaffoldTopShift:42`）＝
  `canRight center ∧ canRight left ∧ canRight (right left) ∧
   ∃ w, chain = .watch w ∧ t = ⟨shiftTick shift, .watch (chainShiftOne w), inc (inc cycle)⟩`
  ——**`ChainShiftRun.next` の 1 手そのもの**
* `beginShiftVM h w s t`（`GalilScaffoldTopShiftCycle:23`）＝
  `s.chain = .watch w ∧ t = {s with remaining := ofNat h, length := inc (inc s.length),
   chain := .watch (immediate w), cycle := reset, periodOnly := true}`
  ——だから shift 入口では `ChainShiftRun … 0 …` が `.stop` で立つ（基底はタダ）
* 合併フレームの `remainingPos`（`GalilScaffoldTopMerge:65`）＝
  `H.remainingPos s ∨ B.remainingPos s`。copy 側を殺すのに `CopyIdle`
  （`GalilScaffoldTopSteps:17` ＝ `¬ (fppLens に pull した fallbackFrame).remainingPos`）が要る
* `chain_shift_exhausts`（`GalilScaffoldTopInvariant:46`）＝
  `s.remaining = ofNat h → ChainShiftRun s w cycle h t v finish → positive t.remaining = false`
  ——終端判定はこれ

**済（n151）**: `chainShiftRun_tick`（shift mode の `Tick` 23 構成子の場合分け。
21 個は mode guard、`shift_done` は行き先 mode で落ちる）＋ `chainShiftRun_of_steps`
（run に沿って伸ばす）。側条件は区間の全点が shift mode ∧ `CopyIdle`。

**済（n152）**: `RoundSeg` の第 1 節 `periodLength wch' = periodLength wch` の材料が全部そろった:

* shift 相 → `chain_shift_periodLength`（**公理ゼロ**）
* scan 相 → `periodLength_onlyMatchedRun`。`periodLength_consume` は無条件ではなく
  `OnBlock` を取るが、`OnBlock` は `consume` で保たれる
  （`GalilBranchInvariants.onBlock_verifier_consume`）ので**起点 1 点だけ**でよく、
  起点の `WatchBlock` は `CloseoutRoundReads.blockInv_of_chainPosInv2` から出る
* `periodLength (immediate w) = periodLength w` → `periodLength_consume` そのもの

**済（n152）**: `hpred` の橋（`watch_eq_of_mismatch_lagZero`）。
lag ゼロでは `Internal` は `idle` のみ（`take` は `positive lag = true` を要求）、
不一致（`b = false`）では `Outer` は `idle` のみ（`queued`/`immediate` は `b = true`）。
よって不一致比較で watch は不変。

**済（n153）**: `hlen` も出どころ確定（`GalilScaffoldTopSegmentHeads.scanSeg_counters`）。
`RoundHistory` に `Canonical s₀.radius ∧ Canonical s₀.length` を足して運ぶようにし、
`onlyMatchedRun_of_roundHistory` が末尾の `Canonical s.radius ∧ Canonical s.length` も返す。

**`round_next` の入力 15 個すべての出どころが確定した。**

### 次にやること: `roundSeg_of_run`（組み立て、手順を全部書く）

1. `RoundHistory P q first delay w c1 s1` を持つ（ラウンド終端）
   → `onlyMatchedRun_of_roundHistory` で
   `⟨n, s₀, w₀, wch, OriginAt w s₀, …, OnlyMatchedRun (toOnly s₀ w₀) n (toOnly s1 wch),
     Canonical s1.radius, Canonical s1.length⟩`
2. `scan_shift` tick（`Tick … ⟨c1, s1⟩ ⟨{c1 with mode := .shift, clock := delay}, s2⟩`）から
   `hm1`/`hr1`/`hc1`/`hcmp`/`hmis`/`hg`/`hb` を取る。
   `hs2 : beginShiftVM (periodLength wch') wch' (afterMismatch s1 vs vq) s2` は
   `beginShiftVM'` の定義（`GalilScaffoldTopGuards:35`）から。
   `wch' = wch` は `watch_eq_of_mismatch_lagZero`（**済**）。
   shift 状態の形の一致は `shiftEntry_shape`（**済 n155**、側条件は
   比較の `vs.left = left s1.left` だけ）
3. `hpred` は `shiftGuardVM (afterMismatch s1 vs vq)` の最後の節から
   （`afterMismatch` の right は `right s1.right`。**済**）
4. shift 相を `chainShiftRun_of_steps`（**済**）で通す。基底は `beginShiftVM` が
   `chain := .watch (immediate wch)` / `remaining := ofNat h` / `cycle := reset` を
   置くので `.stop`
5. shift 末尾の状態 `y` について `y.vm = shiftLens.set s2 (shiftLens.get y.vm)`
   → **済（n154）**: `shiftLens_frame_tick` ／ `shiftLens_frame_steps`。
   `shiftOne` は `Lens.rel` なので第 2 成分が `t = L.set s (L.get t)`、
   つまり「lens の場以外は変わらない」。`Lens.set_set` で `Steps` に沿って合成
6. `shift_done` tick は VM を変えない（`Tick ⟨c, s⟩ ⟨{c with mode := .scan, output := o}, s⟩`、
   `GalilScaffoldTop:136`）
7. **済（n158）**: `RoundHistory.compareRounds_one_of_run`。`CompareRounds.next` を直接埋めた
   （`round_next` は使わなかった——`Steps` は既に手元にあるので `CompareRounds` だけ要る）。
   旧メモ: `GalilScaffoldTopRoundS.round_next`（または `CompareRounds.next` を直接）を適用
   → `CompareRounds h (toOnly s₀ w₀) 1 (toOnly post v)`。
   shift 相の手数が `h` であることは `chainShiftRun_length_eq`（**済 n156**）で、
   `ShiftRun` は `shiftRun_of_chain hchain` からタダ、
   `hlen : Canonical (inc (inc s1.length))` は `inc_canonical` 2 回
8. **済（n159）**: `RoundHistory.roundSeg_of_run`。第 1 節 `periodLength v = periodLength w₀` は
   `periodLength_onlyMatchedRun`（scan 相、**済**）＋ `periodLength_consume`（`immediate`）＋
   `chain_shift_periodLength`（shift 相、**済**）の合成
9. **済（n159）**: `RoundHistory.originAt_next_of_run`（`originAt_of_roundSeg` の上に 1 行）
10. `roundHistory_start` で次のラウンドの `RoundHistory`
11. **済（n159）**: `RoundHistory.h_readsShift_of_run`（`originShift_of_roundSeg` ＋ `h_readsShift_of_originShift`）
    → **`H_readsShift`**

**手順 7〜9・11 は済（n158/n159）。残るは基底と境界検出（下）。**

### 最後の壁: `RoundHistory` を run に沿って引き継ぐ帰納

* **基底**: chain 誕生時の `OriginAt` ← `GalilScaffoldTopFirstRound.first_round`（無条件）
* **帰納**: `originAt_next_of_run`（済）でラウンドごとに引き継ぐ
* **境界検出**: 2 つの carrier の**選言**を run に沿って運ぶ
  （`RoundHistory` = scan 相、`ShiftPhaseHistory` = shift 相。どちらも tick 保存は済 n160）。
  残るのは相の遷移 2 つ:
  * `scan_shift`（`RoundHistory` → `ShiftPhaseHistory`）——**済（n162）**:
    `shiftPhaseHistory_of_scanShift`
  * `shift_done`（`ShiftPhaseHistory` → `RoundHistory`）——**済（n161）**:
    `roundHistory_of_shiftDone`

### 4 遷移は全部済（n160〜n162）。残るのは結合 carrier と基底

    RoundCarrier P q first delay w c s :=
      (c.mode = Mode.scan  → RoundHistory P q first delay w c s) ∧
      (c.mode = Mode.shift → ShiftPhaseHistory w s)

* carrier の定義と取り出しは**済（n163）**:
  `RoundCarrier` / `h_readsShift_of_roundCarrier` / `originShift_of_roundCarrier`
* tick 保存 → **済（n164）**: `scanShift_parts` / `shiftDone_parts`（23 構成子の照合）
  ＋ `roundCarrier_tick` ＋ `roundCarrier_of_steps` ＋ **`h_readsShift_alongSteps`**

### 残り 2 つ（これで第 1 残差が公理から外れる）

1. **起点の `RoundCarrier`（基底）** — 橋は**済（n165）**:
   `periodLength_after_shift` ＋ `originAt_of_firstShiftEntry`。
   残るのは `first_round` の 30 個以上の仮説を run から供給すること
   （＝ CLAUDE.md §3 の `hfound` / `hfoundBg` / `hfoundReplay`、
   自分で「未着手、最大の残り」と書いた項目）
2. **側条件** — n166 で**使う分岐だけに絞った**（旧版は過剰量化で、
   「全 scan 点で周期が終端でない」はラウンド境界で偽だった）。いまの形:
   * 区間の全点が scan / shift 相
   * scan 点で `replaying = false`、shift 点で `CopyIdle`
   * scan → scan の遷移で周期が終端でない・行き先の chain が watch
   * scan → shift の遷移で右ヘッドが読める
   既存の pack（`Extra7` / `AuxPack` / `LPackM`）から出る見込み（**未検証**）
* `H_readsShift` → scan 相は空虚（guard が `mode = shift`）、
  shift 相で `remaining` が尽きた点は `shiftPhaseHistory_readsShift`（済）
* **基底が最後の壁**: `scan_fallback` で copy 相に落ちると chain が作り直されるので
  carrier は保たれない。そこは `GalilScaffoldTopFirstRound.first_round`（無条件）が
  新しい `OriginAt` を出す点

これができたら `H_readsShift` が trace / run の全点で出て、
`obligation_shiftPalResidues*` の第 1 残差が**公理から外れる**（(C) の操作）。
`PalPeg/RoundHistory.lean` は 20 宣言、全部標準 3 公理以内（3 本は公理ゼロ）。
shift 末尾の射影の形は `toOnly_shiftEnd_eq`（**済 n157**）。

---

## 第 2 の筋: `obligation_localRealization`（n166 で調査、未着手）

コウタの指摘（2026-09-19）:
> 「localRealizationとかも一見難しく見えてるだけ。producerがいないってことは
>   モデル化を何か間違ってる」

### 中身（一次情報 `CloseoutFinalW:96`）

    H_realizeLIMW' centre place entry q first :=
      ∃ Q' Γ' (Fintype Q') (DecidableEq Q') (Fintype Γ') (DecidableEq Γ')
        (t K : ℕ) (L : Local.LocalStep (Fin 2) Q' Γ' t K) (blank initQ outQ n) …,
        ∀ w, 0 < w.length → ∀ st Tc, PreTraceB … w st Tc →
          ((L.realize …).SAccepts w ↔ LatchTrue (PofC …) q first w (stLG' τF w st (Tc w.length)) …)

つまり「**Galil 機械を本当に局所（有限制御・有界窓）な機械で実現する**」。
`∃ … L` は構成そのもの。

### 障害は「抽象 `Tick` が非決定的」——そしてその対策は**完成している**

CLAUDE.md §1: 「**scan/init/replayStart は抽象 tick の非決定性で閉じない**」。
CLAUDE.md §2 の方針: モデルは編集せず、Scala の優先順位と固定値を表す `Fair` を
定義して `Tick ∧ Fair` の一意性を証明する。

**`PalPeg/GalilTickFair.lean` の `tick_fair_unique`（`:429`）は証明済み**で、
docstring は「**with no reachability pack at all**: every remaining branch overlap is
settled by the constructor guards」と書いている（宣言の存在は `grep "^theorem"` で確認済み）。

### 次の一手（CLAUDE.md §4 の項目 1 そのもの）

> `Fair` 一意性（`GalilTickFair`）→ **構成 witness/局所 step の `Fair` 監査** →
> `Realizes` の scan/init/replayStart

関係ファイル: `LocalSysConcrete`（tick/到着/stutter/出力 oracle は無仮定）/
`LocalRealizesScan`（rewind/choose 閉）/ `LocalRealizesPhase`（shift/copy/home/markEnd 閉、
fpp は局所 1 量子のみ残）/ `LocalWF` / `LocalTick1`。

**`H_readsShift` の筋（第 1）は found 経路の配線待ちで、そこはプロジェクト最大の
既知項目。こちらの方が安い可能性がある。**

### 診断（n166、確認できた事実と推論を分けて書く）

**確認できた事実**:

1. `Realizes`（`LocalSysConcrete:285`）は
   「mode の局所 step **関数** `f` が trace の次状態に着地する」を要求する:

       Realizes raw stOf f md :=
         ∀ m k j, InvC raw stOf m → m.vm.ctl.mode = md → ¬ Starved m.vm →
           Needy raw stOf k j m.vm → needT' raw stOf k ≤ j →
             Needy raw stOf (k+1) j (f m).vm ∧ PhysWF (f m).vm ∧ MirInv1 (f m)

2. trace `stOf` は `PreTrace` の `trace` 場（`Tick (st i) (st (i+1))`）でしか縛られていない。
   **`Tick` は非決定的**（`GalilTickDet`、CLAUDE.md §2 に 5 つの分岐が列挙されている）
3. `Fair`（Scala の優先順位と固定値）を足すと一意になる:
   **`GalilTickFair.tick_fair_unique`（`:429`）は証明済み**、docstring は
   「with no reachability pack at all」
4. **`Fair` は `PalPeg/Local*.lean` のどこでも使われていない**
   （`grep -rln "Fair" PalPeg/Local*.lean` が空）

**推論（未検証）**: だから `Realizes` は「決定的な関数に、非決定的な trace と
一致せよ」と要求していることになり、producer が原理的に作れない。
コウタの言う「モデル化を何か間違ってる」はこれではないか。

**直し方の候補**: `PreTrace`（または `PreTraceB` / `InvC`）に `Fair` の場を足す。
`PreTraceIMW` は上位で**仮説**として現れるので、場を足すと義務は**弱くなる**（(A) の操作）。
構成側（実 run から trace を作るところ）が `Fair` を供給できるかは別途確認が必要——
CLAUDE.md §2 は「構成側の witness と局所 step が `Fair` を満たすことを別途確認」と書いている。

**注意**: `Realizes` が `Fair` なしでは証明不可能だと**機械検査した反証はまだ無い**。
上は「`Fair` が未使用」「`Tick` が非決定的」「対策は証明済み」の 3 事実からの推論。

### 影響範囲の実測（n167）

`PreTrace` の構造（`GalilFinalAssembly:81`）:

    start : st 0 = boot w
    tc0   : Tc 0 = 0
    trace : Trace (galilFrameS (PofC …) q first) 2048 (SoundScanNR w) st (Tc w.length)
    mono / report / cost

`Fair` を足す先は **`PreTraceB`**（`PreTrace` ＋ `tc1 : Tc 1 = 1`）が blast radius 最小。
`PreTrace` 自体は消費専用（`CloseoutLPack6:21`「is a chain of `∀ w st Tc, PreTrace → …`
implications」）で、**構成しているのは次の 3 箇所だけ**（実測）:

| 場所 | 形 |
|---|---|
| `GalilFinalBaseNeed:196` | `∃ st Tc, PreTraceB centre place entry q first w st Tc` |
| `GalilFinalBaseNeed:310` | `0 < w.length → PreTraceB centre place entry q first w st Tc` |
| `GalilFinalAssembly4:258` / `:285` | 同型 |
| `GalilFinalAssembly3:81` | 同型 |

**段取り**:

1. `PreTraceB` に `fair : ∀ i, i < Tc w.length → Fair entry 2048 (st i) (st (i+1))` を足す
2. 上の構成側 3〜4 箇所で `Fair` を供給する。run をどう作っているかを一次情報で読む
   （`tickFun` を使っているなら `Fair` な witness の存在が要る）
3. `Realizes` の scan / init / replayStart を `tick_fair_unique` で閉じる
4. `H_realizeLIMW'` の `∃ … L` を構成する（`LocalSysConcrete.sysC` が候補）

### 決定的な発見（n167）: trace の出どころは `obligation_cycleOracle`

`preTraceB_exists`（`GalilFinalBaseNeed:193`）を読んだ。trace は

    hor : CycleOracleMC (PofC centre place entry w) q first w
    → checkpoints_cost_upto1 … hor …
    → ⟨st, Tc, …⟩

で作られている。**つまり trace の tick 列は `obligation_cycleOracle`（4 本のうちの 1 本）が
供給する run そのもの。**

→ **`cycleOracle` の文に「run の各 tick は `Fair`」を入れれば trace が `Fair` になる。**

| 操作 | 効果 |
|---|---|
| `obligation_cycleOracle` の文を強める（`Fair` な run を要求） | 1 本の中身が強くなる |
| `obligation_localRealization` が**公理から外れる** | **本数 4 → 3** |

**これは (C)。本数が減る。** しかも強める側は妥当: `Fair` は Scala の優先順位と固定値を
表すものなので（CLAUDE.md §2）、**実機の run は定義上 `Fair`**。
オラクルの仕事は run を提示することなので、提示する run が fair であることは
モデルの忠実性の要求そのもの。

### `Fair` の 3 場は witness が揃っている（n172、一次情報）

| 場 | witness | 側条件 |
|---|---|---|
| `keepsSearchCursor` | 定義自体に入っている（`GalilScaffoldTopReplay:26,39`）。`Tick` からタダ | なし |
| `fallbackPlace` | `GalilTickFair.fallbackAt_walker_self:466` | `(stream s.walker).length ≤ position s.right` |
| `restartFirst` | `GalilTickFair.fair_restart:454` | なし |

**fair な run は存在する。** だから `cycleOracle` の文に `Fair` を入れるのは
モデルの忠実性の要求で、無根拠な強化ではない。

**ただし `Fair` が閉じるのは決定性の半分だけ。** 局所 step の構成
（`H_scanLoc` / `H_initLoc` / `H_replayStartLoc`）は残る。
起点は `LocalTick2.commitReplay` の `LocalTick1.Inv` 保存補題
（`LocalRealizesScan` の冒頭が「まだ無い」と書いている）。

### 段取り（改訂）

1. `Fair` の定義を確認し、`PreTraceB` に `fair` 場を足す
2. `preTraceB_exists` の `hor` を `Fair` 版オラクルに差し替え、
   `checkpoints_cost_upto1` から `Fair` を運ぶ
3. `PalInPegUnconditional` の `obligation_cycleOracle` の文に `Fair` を追加
4. `Realizes` の scan / init / replayStart を `tick_fair_unique` で閉じる
5. `H_realizeLIMW'` の `∃ … L` を構成して `obligation_localRealization` を**外す**

### 段取り 4 の検証結果（n168、一次情報）

`LocalRealizesScan` が残している義務を宣言の存在で確認した:

| mode | 決定性の半分 | 局所の半分 |
|---|---|---|
| `rewind` / `choose` | **閉**（`tick_det_rewind` / `tick_det_choose`） | `H_rewindWF` / `H_chooseWF` |
| `init` | `H_initFun` | `H_initLoc` |
| `replayStart` | `H_rsFun` | `H_replayStartLoc` |
| `scan` | **`H_scanDet`** | **`H_scanLoc`** |

そして `PalPeg/GalilTickFair.lean` に**そのまま合う 3 本が証明済み**:

    tick_fair_scan_unique        (:308)  hm : c.mode = Mode.scan        ＋ 両 tick の Fair → y₁ = y₂
    tick_fair_init_unique        (:381)  hm : c.mode = Mode.init        ＋ 同 → y₁ = y₂
    tick_fair_replayStart_unique (:400)  hm : c.mode = Mode.replayStart ＋ 同 → y₁ = y₂

**つまり `Fair` は決定性の半分（`H_scanDet` / `H_initFun` / `H_rsFun`）を閉じる。**
これが「原理的に作れない」部分だった。

**残るのは局所側の構成**（`H_scanLoc` / `H_initLoc` / `H_replayStartLoc` ＋
`H_rewindWF` / `H_chooseWF` ＋ fpp の 1 量子）。こちらは**構成作業**で、
不可能ではない。`LocalReplayParked.commitReplayParked` が `H_replayStartLoc` の
意図された witness だが `LocalTick2.commitReplay` に `LocalTick1.Inv` 保存の補題が
まだ無い（`LocalRealizesScan` の冒頭に書いてある）。

**注意**: `scan` 相の非決定性の原因は `Tick.restart` が 5 つの scan 構成子と競合すること
（`Fair.restartFirst` がそれを潰す）と、`background` / `compare` の
`SafeQuanta` / `chainAt` が関係であること（`GalilTickDet.safeQuanta_unique` /
`chainAt_unique` が潰す）。**どちらも `Fair` 側で済んでいる。**

---

## この session で機械検査／一次情報で確定したこと

### (a) `H_readsShift` は「guard の差」ではない（ReadsRun 案は却下）

`CloseoutRoundReads.ReadsRound`（`mode = scan` guard）と
`CloseoutRoundUnique.H_readsShift`（`mode = shift` guard）は結論が同一の `ReadsInv` で、
mode guard だけが違う。`ReadsRun`（mode guard なし）も既にある。
**しかし free ではない**: `ReadsInv` は「watch の machine が本物の `ReadOrigin` の
shifted machine を `used` 回 sweep したもの」で、shift 終端では
**次のラウンドの origin に貼り替わる**ことを主張する。これがラウンド引き継ぎの本体。
n146 のノートに書いた「guard を広げれば無償かも」という見立ては**外れ**。

供給鎖は存在する（`CloseoutReadsOrigin.h_readsShift_of_rounds`）:

    first_round（無条件）→ Entry → CloseoutOriginRounds.originAt_of_rounds
                        → h_readsShift_of_originAt → H_readsShift
    Rounds ← CloseoutWatchRound9.roundOne_of_segRun_N（+ ShiftAtMismatchN）

足りないのは **run/trace への配線**（`∀ m z, Steps … → H_readsShift w z.ctl z.vm` の形）。

### (b) `H_freshShiftAtShiftEntry` は `OriginAt` からは出ない（測定済みの negative）

`CloseoutReadsOrigin` の「`H_freshShift` is **not** reachable this way」節が一次情報:
`OriginAt` はラウンドの `used` を 0 に固定するので `RoundScan.count` が
`value cycle = 2h` を強制し、`terminal_iff` で `singlePositive cycle = true` が
`1 = 2h` と同値になってしまう。fresh chain の最初の shift は `used = 2h − 1`
（`WatchSeg` を一周した後）で起きるのでラウンド開始点ではない。
→ **`GalilScaffoldTopFirstRound.first_round` 自身の義務のまま。**

### (c) `first_round` の文脈が (c) の材料をちょうど持っている

`first_round` の仮説に `hcand : Candidate ((stream ⟨a::ls,gap⟩).take (span+1)) lower h`、
`hi0 : ScanInvariant raw (position cen) initialRadius v0.left v0.right`、
`hpred : symbol w.machine.control.period.focus = some predicted`、
`hread : read (right s1.right) = some predicted` が**全部そろっている**。
結論は shift 入口の `∃ o', Entry raw o' (toOnly e v) ∧ …`。

---

## 解けたら pop するときの手順

1. その定理を書いて単一ファイルで `lake env lean` を通す
2. 上の該当スタックフレームを消し、1 段浅いフレームに「済」を書く
3. 公理の文を弱める（**本数は増やさない**）
4. 全体 build → `#print axioms` で計器を読む → `PalPeg/Axioms.lean` のラチェット更新
5. `CLAUDE_RESUME.md` と `ASSEMBLY_PLAN.md` の先頭にノート

**当時の記録（現在の状態ではない）: 全体build成功、無条件PALは未完、公理4本。現在は2本。**
# n266 (Codex): cycle/hmove active pre-shift consumer

Stack: `obligation_cycleOracleOnPackedRun → OracleReady.hmove → active fallback
→ pre-shift quarter bound`.

- `CanonicalChainMinimal.move_of_preShift_packed` now recovers the semantic
  least candidate from the packed run, transports it through the mismatch's
  `chainAt`, and feeds `move_of_activeBound`.
- The theorem is kernel-checked.  Its sole remaining input is the genuine
  phase fact `radius < 4*h`; it is not an isolated helper: this is the exact
  pre-shift arm of `OracleReady.hmove`.
- Current leaf: transport the birth estimate (`radius_birth ≤ 2*h`) through
  copy/back progress to obtain the strict quarter bound.  Watch/post-shift is
  the sibling arm and uses the round ledger.

# n267 (Codex): cycle/hmove long-radius boundary connection

Stack: `obligation_cycleOracleOnPackedRun → OracleReady.hmove → active watch fallback
→ 4h < Rad → retained period fails at new fallback boundary`.

- `GalilMoveLemma`: Fine–Wilf/minimal-period boundary argument and its fallback consumer are checked.
- `GalilRoundPeriod.RoundScan.current_hasPeriod` is checked.
- `RoundScan.cons_period_predicts` is checked: extending `2h` to `x :: Span` forces `x` to equal the chain prediction.
- `RoundScan.not_cons_period_of_mismatch_guard_false` is checked: the actual mismatch and false shift guard refute that extension, including the terminal-cycle case.
- Current leaf: extract the needed period/prediction datum for the post-shift watch from the packed `ChainWindowRun`/`Coupled'` state after `chainAt false`, then call `move_of_activePeriodBreak`.

# n268 (Codex): packed-window shortcut audit

Stack remains `obligation_cycleOracleOnPackedRun → hmove → post-shift watch → round datum`.

- Tested the proposed shortcut `ChainWindowRun + current PalAt → HasPeriod current Span (2h)` directly in Lean.
- It closes the left-only and right-only comparisons, but the `2h` comparisons crossing the current centre require the previous round's origin palindrome. `ChainWindowRun` intentionally retains only the birth-anchored right block, so it cannot supply that fact alone.
- `MInv` supplies leftmostness, not the missing symbols left of the current span; it does not prove a uniform `Rad ≤ 4h` for an arbitrary post-shift round.
- The failed shortcut was removed; `WindowPack.lean` is kernel-clean again. The checked `RoundScan` boundary lemmas remain the correct consumer.
- Current leaf: recover/carrry `RoundScan` (or the equivalent previous-origin datum) at the packed post-shift watch point.
