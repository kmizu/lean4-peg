## 2026-09-19 n135: `LagPos` を trace に載せる道の測定（`IPackMW` に lag 場は無い）

**全体 build 成功（EXIT=0、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 6。
無条件 PAL は未完。§10.5 は未達。**

### 測定 1: `PreTraceIMW` は lag を運んでいない

`IPackMW`（`CloseoutPackW:64`）＝ `LPackM` ＋ `LPackM2`。
`LPackM`（`CloseoutPackRun10:140`）の場は `lrepM`（左ヘッドの表現）と
`scanGeom`（`ScanInvariant`）の 2 つだけで、**chain の lag に触れる場は無い**。

したがって `obligation_shiftPalAtFreshChainAlongTrace` を `.watch` 相に狭めるには
`LagPos (st j).vm.chain` を別途調達する必要があり、**いま狭めても差し引きゼロ**。

### 測定 2: lag が要るのは `.back` 相だけ（線引きが細かくなった）

| `s.chain` | `ShiftPal` の空虚性 | lag 仮定 |
|---|---|---|
| `.idle` | 空虚（誕生しても `.copy`、しなければ `.idle`） | **不要** |
| `.copy` | 空虚（`FoundPackRefute.chainTick_copy_not_watch`） | **不要** |
| `.broken` | 空虚（`ChainStep.brokenIdle`） | **不要** |
| `.back` | 空虚（`backDone` の watch は lag を継承） | **要る** |
| `.watch` | 本体 | — |

`shiftPal_of_copyOrBack`（n134）は `.copy` と `.back` を束ねて lag を要求しているが、
**`.copy` 側だけなら lag 無しで済む**。必要なら分けられる。

### 測定 3: 「found 時の半径が正」は**導出されていない**（アセンブリ全体の仮定）

`GalilScaffoldTopFoundLife`（`:28`）は `hRpos : 0 < R` を**明示の仮定として取っている**
（`R` は `ScanInvariant` の半径）。`GalilScaffoldTopFirstRound.first_round` も
`hrp : 0 < value radius` を仮定で取る。CLAUDE.md の記憶欄「仮定：Decodes、delay=2048、
3·Rad≤5·k、**found 半径正**、窓長偶数」と一致する。

**この 1 つの側条件が今日 3 箇所で出た**:

1. `ReachesWatchFromRun.reachesWatchPhase_or_segEnd_at_foundBirth_canonical` の
   `hRadiusPos : 0 < value radius`（n125）
2. `LagPos` を誕生点で立てるため（n134/n135、`.back` 相の空虚性）
3. `first_round` / `chain_life` の既存仮定

つまり**これを 1 本潰すと 3 箇所に効く**。逆に言えば、いまはどこにも producer が無い。
真偽の見立て: `Candidate w lower h` は `4h+1 ≤ w.length` かつ `h ≥ 1` を要求するので
place stream に 5 記号以上が要り、walker は scan と共に進むから半径も進んでいるはず——
**だが `radius` と `place stream` の長さを結ぶ場は未確認**。次に見るならそこ。

## 2026-09-19 n134: `periodOnly = false` 分岐の空虚な半分を落とした

**`PalPeg.ShiftPalAlongTrace.shiftPal_of_copyOrBack` — 標準公理、`sorry` ゼロ、単体 build EXIT=0。**
（全体 build は未実行。公理は 6 のまま。無条件 PAL は未完、§10.5 は未達。）

### 証明したもの

    theorem shiftPal_of_copyOrBack (hPhase : CopyOrBack s.chain) (hLag : LagPos s.chain) :
        ShiftPal centre place entry q first w s

**`CopyOrBack`（lag 正）の点では `ShiftPal` は空虚に成り立つ。** 理由:
`ShiftPal` は比較の行き先 `s'` に `shiftGuardVM s'` を要求し、それは
`zero w.lag = true` を含む。しかし copy/back から 1 手で生まれる watch は lag を
そのまま受け継ぐ（`backDone`）か `inc` する（`Outer.queued`）ので、誕生 chain の正 lag が
保たれて guard が落ちる。`Outer.immediate` と `ChainMatched.breaks` は
どちらも `zero lag = true` を要求するので正 lag では使えない。

支えは `CopyPhaseNoShift.tick_not_watch_or_posLag`（事象によらない版、今回追加）。

### 効く範囲（`periodOnly = false` 分岐の場合分け）

| `(st j).vm.chain` | `ShiftPal` |
|---|---|
| `.idle` | **空虚** — 誕生しても `.copy`、しなければ `.idle`。どちらも watch ではない |
| `.copy` / `.back`（lag 正） | **空虚** — `shiftPal_of_copyOrBack`（今回） |
| `.broken` | **空虚** — `ChainStep.brokenIdle` で `.broken` のまま |
| `.watch` | **本体** — 準備した周期が入力の本物の周期であること（DP 正当性の帰結のはず） |

つまり `obligation_shiftPalAtFreshChainAlongTrace` は
**`.watch` 相だけに狭められる**。

### 残る側条件

狭めるには trace の各点で `LagPos (st j).vm.chain`（copy/back 相の lag が正）が要る。
`PreTraceIMW` が各点で運ぶ `IPackMW` に lag の場があるかは**未確認**。
無ければ新しい義務になるので、その場合は差し引きゼロ——**先に `IPackMW` を確認すること。**

## 2026-09-19 n133: 3 原子の producer を一次情報で測った（CLAUDE.md の記述は楽観的だった）

**全体 build 成功（EXIT=0、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 6（n132 の分解後）。
無条件 PAL は未完。§10.5 は未達。**

### 訂正: `first_round` は `H_freshShiftAtShiftEntry` を出さない

CLAUDE.md と `PalInPegUnconditional` の表は「`H_freshShiftAtShiftEntry`（←`first_round`）」と
書いていたが、**一次情報を読むと違う**:

* `GalilScaffoldTopFirstRound.first_round` の結論は
  `(∃ k, Steps …) ∧ e.chain = .watch v ∧ zero v.lag = true ∧ e.periodOnly = true ∧
   ∃ o' : ReadOrigin raw, Entry raw o' (toOnly e v) ∧ …`
  ——**origin/`Entry` 形**。
* `H_freshShiftAtShiftEntry` が要るのは `∃ C R k, ShiftInv w C R (periodLength wch) k t wch` で、
  `ShiftInv`（`CloseoutPackRun37:59`）は 13 場（`kle` / `posH` / `size` / `room` /
  `remaining` / `canon` / `count` / `leftRep` / `leftPresent` / `leftPos` / `rightRep` / …）の
  **幾何と台帳**。

`Entry` → `ShiftInv` の橋が要る。**1 適用では落ちない。**
同様に `obligation_readsShiftAlongTrace` の候補 `RoundSegFromRun.readsShift_at_actual` も
前ラウンド起点の `OriginAt` ＋ 構成 run / 実 run の対を要求する（n125 で測定済み）。

**過去の自分の記述（CLAUDE.md の「経路と残り」欄）を一次情報として使わない**——
今日 4 回目の同じ教訓。

### 見えた筋: `obligation_shiftPalAtFreshChainAlongTrace` は**半分が空虚**

`ShiftPal` は `∀ s', compare s s' → ¬matched s' → ∀ wch, s'.chain = .watch wch →
shiftGuardVM s' → …` の形。`periodOnly = false` の点で chain の相を場合分けすると:

| `s.chain` の相 | 状況 |
|---|---|
| `CopyOrBack`（lag 正） | **空虚**——`CopyPhaseNoShift.not_shiftGuardVM_of_copyOrBack_tick` が
  「compare の行き先に shift guard は立たない」を証明済み |
| `.watch`（準備完了、まだ shift していない） | **本体**——「準備した周期が入力の本物の周期」 |

後者は DP 正当性（n114 で「探索側は無条件で証明済み」と測定済み）の帰結のはずで、
新しい数学ではなく層の配線。**`ShiftPal` の `periodOnly = false` 分岐は
「copy/back なら空虚、watch なら DP 正当性」に割れる。**

次はこの割り方を実装して、空虚な側を落とす。

## 2026-09-19 n132: トップダウンに切り替え — `obligation_shiftPalAlongTrace` を 3 原子に割った

**全体 build 成功（EXIT=0、エラー 0、`sorry` ゼロ）。ラチェット更新済み・緑。
公理は 4 → 6（1 本を 3 原子に割ったため）。無条件 PAL は未完。§10.5 は未達。**

### コウタの指摘（受けた）

* 「変によく考えず定理ふやすのやめよ」——今日だけで新規ファイル 6 本。
  CLAUDE.md に自分で「これ以上増やす前に、既にあるものを探す」と書いていながら守れていなかった。
  実際に効いたのは**削除・弱化**の方（`hwatch` の除去は「足した」のではなく依存を切った結果）。
* 「今残ってる前提を証明するためにトップダウンで」「せっかく機械的に残り前提検査
  できるようにしたんだから」——**found 経路の作業は `obligation_cycleOracle` の部分木の中**
  なので `#print axioms` の針が動かない。計器を使う形に戻す。

### やったこと

`PalInPegUnconditional.lean` の `axiom obligation_shiftPalAlongTrace` を
**`ShiftPalAlongTrace.shiftPal_alongTrace` の適用に置き換え**、足りない引数を
その場で原子的な `axiom` に切り出した。

| 新しい原子 | 中身 | producer 候補 |
|---|---|---|
| `obligation_readsShiftAlongTrace` | trace 各点で `H_readsShift` | `RoundSegFromRun.readsShift_at_actual` |
| `obligation_freshShiftAtShiftEntryAlongTrace` | trace 各 tick で `H_freshShiftAtShiftEntry` | `GalilScaffoldTopFirstRound.first_round` |
| `obligation_shiftPalAtFreshChainAlongTrace` | `periodOnly = false` 点での `ShiftPal` | 未特定 |

**2 つの側条件は文脈から出た**（新しい公理にならなかった）:

* `0 < w.length` — `w = []` なら `Tc 0 = 0`（`PreTrace.tc0`）で `1 ≤ j ≤ Tc w.length` が空虚
* `1 ≤ Tc w.length` — `PreTraceB.tc1`（`Tc 1 = 1`）＋ `PreTrace.mono`

### 現在の針（実測）

    [propext, Classical.choice, Quot.sound,
     obligation_cycleOracle,
     obligation_freshShiftAtShiftEntryAlongTrace,
     obligation_localRealization,
     obligation_readsShiftAlongTrace,
     obligation_shiftPalAlongRun,
     obligation_shiftPalAtFreshChainAlongTrace]

数は増えたが、これが CLAUDE.md の「公理は 1 場ずつの原子に分解する
（束ねると『1 個外す』が測れない）」。次は `obligation_shiftPalAlongRun` にも
同じ手（`CloseoutBundleRun.shiftPal_of_run_B`）を当て、そのあと原子を 1 本ずつ潰す。

## 2026-09-19 n131: `WatchMismatchNoShiftC` のガードを「tick できる相」に広げた

**全体 build 成功（EXIT=0、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4 義務のまま。
無条件 PAL は未完。§10.5 は未達。**

n130 で「正しい弱化先は `CopyOrBack ∨ watch`」と書いた線をそのまま実装した。

### 新規 `PalPeg/CopyPhaseNoShift.lean`（すべて標準公理）

| 定理 | 内容 |
|---|---|
| `tick_false_not_watch_or_posLag` | copy/back の background 1 手の行き先は、watch でないか、**lag が正の** watch |
| `not_shiftGuardVM_of_copyOrBack_tick` | **copy/back 相では不一致の行き先に shift guard が立たない** |
| `watchMismatchNoShift_parts_of_copyOrBack` | `WatchMismatchNoShiftC` の 2 節が copy/back 相でそろう |
| `TickablePhase` / `LiveScanTickable`（def） | 「tick できる相」＝ lag 正の `CopyOrBack` か watch |
| `liveScanTickable_ne_idle` | それは非 idle |

第 2 節の内訳:
* `.copy` から出た 1 手は `.copy` か `.back` で **watch ではない**（`chainStep_copy_shape`）
* `.back` から `backDone` で生まれた watch は **lag をそのまま受け継ぐ**
  （`chainStep_back_shape'`）。誕生 chain の lag は正なので `shiftGuardVM` の
  `zero w.lag = true` が落ちる

### ガードの差し替え

`CloseoutWatchRound22.WatchMismatchNoShiftC` の guard を
`LiveScanWatch c1 s1` → `CopyPhaseNoShift.LiveScanTickable c1 s1` に変更。
producer `CloseoutWatchRound23.watchMismatchNoShiftC_of_split` は**選言対応**にした:

* watch 相 → 従来どおり `TerminalRunFallbackGC` 経由
* copy/back 相 → `watchMismatchNoShift_parts_of_copyOrBack`（新しい直接経路）

変換補題 `CloseoutWatchRound22.liveScanTickable_of_liveScanWatch` を置いて、
既存の `LiveScanWatch` 消費者（Round22 / Round36）を通した。

**import の向き**: `CopyPhaseNoShift` は `CopyPhaseTickMatched` だけを import する
（`FoundPackRefute` を入れるとビルドサイクル——あれは `CloseoutFoundRoute1` を引く）。
その形なら `CloseoutWatchRound22` から import できる。

### 次

`WatchFallbackC` / `FallbackReachS` / `LandingRestartReachF` の guard も同じく
`LiveScanTickable` に広げる。そうすると `reachesWatchPhase_or_segEnd` の**第 2 枝**
（準備完了前の不一致）が `FoundExitLPS.landedS` に着地でき、節 4 の供給が閉じる。

## 2026-09-19 n130: `LiveScanWatch` ガードの線引きが確定した（`CopyOrBack ∨ watch` が正しい弱化先）

**全体 build 成功（EXIT=0、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4 義務のまま。
無条件 PAL は未完。§10.5 は未達。**

### 放電できたもの（検証済み）

| 定理 | 元の仮定 | 実際に使っていたもの |
|---|---|---|
| `CloseoutWatchRound21.fallbackLanding_of_pack` | `LiveScanWatch c1 s1` | `mode = scan ∧ replaying = false`（clock と watch を `obtain ⟨hm, hr, -, -⟩` で捨てていた） |
| `CloseoutWatchRound22.fallbackTick_of_watchTick` | `s1.chain = .watch w` | `s1.chain ≠ .idle`（watch は `≠ idle` を出すためだけ） |

`CloseoutWatchRun.LiveScanNonIdle`（`mode ∧ ¬replaying ∧ 1 ≤ clock ∧ chain ≠ idle`）と
`liveScanNonIdle_of_liveScanWatch` を追加。

### 弱化を試して**戻した**もの（正直な記録）

`WatchFallbackC` / `WatchMismatchNoShiftC` / `WatchFallbackCostC` / `LandingRestartReachF` /
`FallbackReachS` の guard を `LiveScanNonIdle` に弱める sweep を当てたが、
`CloseoutWatchRound23.watchMismatchNoShiftC_of_split` が
`TerminalRunFallbackGC`（`LiveScanWatch` guard を持つ watch ラウンドの機械）から
`WatchMismatchNoShiftC` を作っているので通らない。**これは形式化のミスではなく本物のギャップ。**

さらに **`≠ idle` だけでは足りない**ことも分かった:
`WatchMismatchNoShiftC` の第 1 節「`∃ z, ChainTick false s1.chain z`」は、
`ChainStep` が `.copy` から出るのに `CopyInv`（`t.focus = 8`、`t.left ≠ []`、
`read (left p) = some a`）を要求するので、任意の非 idle chain では出ない。

### 正しい弱化先（次に書くもの）

    CopyOrBack s1.chain ∨ (∃ w, s1.chain = ChainVM.watch w)      -- 「tick できる相」

この guard なら両節とも出る。材料は全部ある:

| 節 | copy/back 側の材料 |
|---|---|
| `∃ z, ChainTick false s1.chain z` | `CopyPhaseTick.copyOrBack_tick_false_exists` |
| `∀ vs vq, ChainTick false … → ¬ shiftGuardVM (afterMismatch …)` | `.copy` なら `FoundPackRefute.chainTick_copy_not_watch`；`.back` から `backDone` で生まれた watch は lag が正なので `shiftGuardVM` の `zero w.lag = true` が落ちる（`CopyPhaseTickMatched` の `LagPos` 系） |

つまり `watchMismatchNoShiftC_of_split`（watch 経路）の**兄弟**として
copy 相版の producer を書けばよい。`TerminalRunFallbackGC` を経由しない。

### 診断の定着（今日 4 件目）

**`LiveScanWatch` を取る定理は、まず本体での使われ方を数える。**
`obtain ⟨…, -, -⟩` で捨てているなら過剰。今日これで 4 件落ちた
（`split4_of_prefix` / `split3_of_prefix` / `fallbackLanding_of_pack` /
`fallbackTick_of_watchTick`）。**ただし「使っている」場合は本物**——
`TerminalRunC` / `TerminalRunFallbackC` / `watchMismatchNoShiftC_of_split` は弱められない。

## 2026-09-19 n129: 節 4 の供給 — `SegEnd` 枝は fallback へ。`LiveScanWatch` ガードの棚卸し

**全体 build 成功（EXIT=0、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4 義務のまま。
無条件 PAL は未完。§10.5 は未達。**

### 放電済み（今回）

`CloseoutWatchRound21.fallbackLanding_of_pack` の `hlive : LiveScanWatch c1 s1` は
**過剰**だった——`obtain ⟨hm, hr, -, -⟩ := hlive` で clock と watch を捨てており、
使っていたのは `mode = scan` と `replaying = false` だけ。その 2 つに弱めて
呼び出し側 4 箇所（Round21/29/31/36）を通した。全体 build 緑。

### 次の設計判断（材料は揃っている）

`ReachesWatchFromRun.reachesWatchPhase_or_segEnd` の**第 2 枝**（準備完了前に不一致）を
`FoundExitLPS.landedS` に着地させたい。材料:

* 第 2 枝が返すのは `WatchSegE … es cP sP c' s'` ＋ `SegEnd P c' s'` ＋ `CopyOrBack s'.chain`
  ＋ `c'.mode = .scan` ＋ `c'.replaying = false`
* `SegEnd` は live 構成では `.mismatch` のみ（clock = 1、`canRight`、不一致）
* `FoundPackCorrected.no_shift_from_copyChain` が「`.copy` 相では shift guard が立たず
  `scan_fallback` へ」を証明済み
* `FoundExitLPS` は `exit` と `landedS` の 2 構成子で、fallback 着地は `landedS`

受け皿は `CloseoutWatchRound31.FallbackReachS` だが、その guard が `LiveScanWatch c1 s1`。

**訂正（自分の見立ての修正）**: これを「`s1.chain ≠ .idle`」まで弱めるのは**行き過ぎ**。
`ChainStep` が `.copy` から出るには `CopyInv`（`t.focus = 8`、`t.left ≠ []`、
`read (left p) = some a`）が要るので、「chain が 1 手進める」
（`WatchMismatchNoShiftC` の第 1 節）は任意の非 idle では出ない。
**正しい弱化先は「tick できる相」** :

    CopyOrBack s1.chain ∨ (∃ w, s1.chain = ChainVM.watch w)

`CopyOrBack` は `CopyInv` を含むので第 1 節が `copyOrBack_tick_false_exists` で出る。
第 2 節（不一致後に shift guard が立たない）は `.copy` 相では
`FoundPackRefute.chainTick_copy_not_watch` でむしろ**簡単**。

`LiveScanWatch` を guard に持つ定義の棚卸し（弱化候補）:

| 定義 | ファイル |
|---|---|
| `WatchFallbackC` | `CloseoutWatchRound21:85` |
| `WatchMismatchNoShiftC` / `WatchFallbackCostC` | `CloseoutWatchRound22:131` / `:143` |
| `LandingRestartReachF` | `CloseoutWatchRound29:104` |
| `FallbackReachS` | `CloseoutWatchRound31:246` |

**`TerminalRunC` / `TerminalRunFallbackC` の `LiveScanWatch` は本物**（watch 無しで
ラウンドは回らない）。弱化してはいけない。

### 診断の定着

**`LiveScanWatch` を取る定理は、まず本体での使われ方を数える。**
`obtain ⟨…, -, -⟩` で捨てているなら、その分は過剰。今日これで 3 件
（`split4_of_prefix` / `split3_of_prefix` / `fallbackLanding_of_pack`）が落ちた。

## 2026-09-19 n128: `hpack` の**両方の偽の節**（4 と 7）を found 経路から消した

**全体 build 成功（EXIT=0、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4 義務のまま。
無条件 PAL は未完。§10.5 は未達。**

n127 で節 4（`PrepLandingWatchC`）を消した。n128 で節 7（`BreakLandingC`）も同じ手で消えた。
**`FoundPackRefute` が反証した 2 つは、どちらも同じ 1 つの欠陥だった**——
`∀ es c2 s2, WatchSegE … cP sP c2 s2 → …` が `es = []`（＝`WatchSegE.stop`）を含むので、
誕生状態 `sP` 自身について主張してしまう。誕生直後の chain は `.copy` なので偽。

### 直し方（節 4 と節 7 で同一）

**着地に `(∃ w, s2.chain = ChainVM.watch w) →` のガードを足す。** それだけ。
消費者はそのガードを既に持っているか（`RoundsRouteLPraw` / `BreakRouteLPraw` は
`es.length = 2*hh+2` と `∃ ww, s2.chain = .watch ww` を渡す）、`hland` の出力から取れる。

ガードを足した定義（すべて trailing `∀`）:

| 定義 | ファイル |
|---|---|
| `ShiftTailC` | `CloseoutWatchPhase2:247` |
| `NoShiftTailC` | `CloseoutWatchPhase2:347` |
| `NoShiftTailC0` / `NoShiftTailC0L` | `CloseoutWatchPhase3:150` / `:382` |
| `BreakLandingC` | `CloseoutWatchRound5:409` |
| `BreakLandingLedgerC` | `CloseoutWatchRound10:208` |

### 反証の扱い

`FoundPackRefute.breakLandingC_false_of_foundCompareCtx` は**ガード無しの旧形**についての
定理として残した（`refuted_BreakLandingUnguardedC` を新設して、それを取る形に変更）。
現行のガード付き `BreakLandingC` には当たらない。**削除せず、なぜガードが要るかの記録として残す。**

### 帰結

`CloseoutFoundRoute1` の `hpack` 7 節のうち、**反証済みだった 2 節（4 と 7）が両方とも
真の形になった**。節 4 は `∃ es c2 s2, WatchSegE ∧ LiveScanWatch c2 s2`
（＝`ReachesWatchPhase` ＋ 制御 3 節）、節 7 はガード付き `BreakLandingC`。

公理の本数は変わらない（`hpack` は公理ではなく `obligation_cycleOracle` の部分木内部の
仮定）。**変わったのは、その部分木が偽の仮定を 1 つも通らなくなったこと。**

## 2026-09-19 n127: 反証済み `PrepLandingWatchC`（`hpack` 節 4）を found 経路から**消した**

**全体 build 成功（EXIT=0、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4 義務のまま。
無条件 PAL は未完。§10.5 は未達。**

コウタの指摘 2 つがそのまま当たった:

* 「難しく考えなさんな。未解決問題とはいえ難問というより単純に規模が大きいだけの問題」
* 「producer がいないってことはモデル化を何か間違ってる」

### 何が間違っていたか

`CloseoutWatchRound23.split4_of_prefix` は `hliveP : LiveScanWatch cP sP`
（＝誕生状態の chain が `.watch`）を取っていたが、**本体で 1 回しか使っておらず、
しかも `sP.chain ≠ ChainVM.idle` を取り出すためだけ**だった。誕生直後の chain は
`.copy` なので `.watch` は偽（`FoundPackRefute`）、しかし**非 idle は真**で、
`FoundCompareCtxC` が `ch ≠ ChainVM.idle` を конъюнкт として直接持っている。

`CloseoutWatchRound40` の docstring は「`exitSplit4C_of_tick` は `.watch` を要求するが
`ChainW` は `.copy`/`.back` のこともある」と書いて**新しい仮定を立てる方向へ逃げていた**。
仮定を弱めるのが正しかった。**自分の過去の記述を判断材料にした失敗の再発。**

### 効いた置き換えは 2 種類だけ

| 消費者が要求していたもの | 実際に使っていたもの | 出どころ |
|---|---|---|
| `LiveScanWatch cP sP`（誕生状態が watch） | `sP.chain ≠ .idle` | `CloseoutWatchRound2.chain_ne_idle_of_foundCompareCtx`（新規、タダ） |
| 全着地で `LiveScanWatch`（`hlive`） | その着地の watch だけ | `∀` にガードとして追加（`TerminalRunShiftC` は元から同じガードを持っていた） |

**producer が無かったのは、`ShiftTailC` の末尾 `∀` にガードが無く、それを供給するのが
`TerminalRunShiftC`（ガード付き）だったから。** 橋渡しのためだけに `hlive` が要り、
その `hlive` が `hwatch` を要求していた。ガードを揃えたら鎖ごと消えた。

### 変更（全体 build 緑）

* `CloseoutWatchPhase2.ShiftTailC` — 末尾 `∀ es c2 s2` に watch ガードを追加
* `watchSegE_live_control` を `CloseoutWatchRound7` → `GalilScaffoldTopWatchSegE`（定義ファイル）へ移動。
  `WatchSegE` の素の構造的事実なのに下流に埋まっていて上流から使えなかった
* `split4_of_prefix` / `exitSplit4C_of_tick`（Round23）、`split3_of_prefix` /
  `exitSplit3C_of_tick`（Round19）、`exitSplit4C_of_liveScanWatch`（Round42）— 仮定を弱化
* `shiftExitTailC_of_parts` / `breakExitTailC_of_parts`（Round5）、
  `breakExitTailLC_of_parts`（Round10）、`mismatchShift_to_shiftRoute`（Round25）、
  `shiftTailC_of_dataL`（Round37）/ `dataL'`（Round41）— `hlive` を**引数ごと削除**
* `foundExit_of_split3` / `_split3S` / `_split3F` の 3 変種 — **到達 watch 着地版**に置換
  （`foundExit_of_split3_atReachedWatch` ほか）。仮定は
  `∃ es c2 s2, WatchSegE … cP sP c2 s2 ∧ LiveScanWatch c2 s2`
* `CloseoutFoundRoute1` の `hpack` 束の**節 4 を同じ形に差し替え**
* Round14/15 は `hwatch` を完全に失った

### 帰結

**`(hwatch : PrepLandingWatchC …)` の宣言は `PalPeg/` 全体で 0 本になった**
（残る参照は `open` 行と docstring のみ）。found 経路は反証済みの仮定に依存しなくなり、
代わりに要求するのは `∃ es c2 s2, WatchSegE ∧ LiveScanWatch c2 s2`——これは
`FoundPackCorrected.ReachesWatchPhase` ＋ `watchSegE_live_control` そのもので、
n125/n126 で作った `ReachesWatchFromRun.reachesWatchPhase_or_segEnd_at_foundBirth` の
**第 1 枝が出す**。第 2 枝（`SegEnd` で早期終了＝準備中の不一致）の配線が次の仕事。

公理の本数は変わらない（`hpack` は公理ではなく `obligation_cycleOracle` の部分木内部の
仮定だった）。**変わったのは、その部分木が偽の仮定を通らなくなったこと。**

## 2026-09-19 n126: `PalInPegUnconditional.lean` の docstring が腐っていた（表 9 行 vs `axiom` 4 本）

**全体 build 成功（EXIT=0、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4 義務のまま。
無条件 PAL は未完。§10.5 は未達。**

コウタの指摘「4 本って書いてることとちゃうやん」で発覚。照合結果:

| 出どころ | 数 |
|---|---|
| `#print axioms PalPeg.PalInPeg.unconditional` | **4**（`shiftPalAlongRun` / `shiftPalAlongTrace` / `cycleOracle` / `localRealization`） |
| `grep "^axiom " PalPeg/PalInPegUnconditional.lean` | **4**（`:85` `:96` `:104` `:109`） |
| `CLAUDE.md:102` | **4** |
| **同ファイルの docstring の表** | **9 行**（← ズレていたのはここだけ） |

`obligation_verifierRunAlongRun` / `matchLanding_alongTrace` / `shiftEntryLanding_alongTrace` /
`chainBackLag_alongTrace` / `shiftExitLedger_alongTrace` / `rewindMargin_alongTrace` の 6 行が、
**既に存在しない公理を載せたまま**だった（`axiom` 宣言ゼロ、参照は docstring のみ）。
経路メモは捨てずに「公理としては消えた 6 本」節へ移した。

**CLAUDE.md の「ファイル自身の docstring も一次情報ではない」に自分で引っかかった。**
n116 で `CloseoutRealize1.lean` について同じことを書いたのに、正本の入口ファイルで
同じ腐り方をさせていた。**数えるときは `grep "^axiom "` か `#print axioms`。**
表を書き換えるときは同時に `axiom` 宣言と突き合わせる。

## 2026-09-19 n125: live chain 版の区間構成ができた — clock の余裕は要らなかった（n124 の訂正 2 段）

**全体 build 成功（EXIT=0、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4 義務のまま。
無条件 PAL は未完。§10.5 は未達。**

### まず訂正 2 段（自分の見積もりが 2 回とも外れた）

**訂正 1（n124 が甘かった）**: 「残る外部入力 4 つのうち最後の 1 つ
`clock の余裕 n < cP.clock` は予算層の話」と書いたが、`watchSegE_backgroundRun_live`
（`.count` / `.wait` だけで作る区間）が走れるのは高々 2047 手で、準備に要る `2h+2` 手は
`h ≤ 1022` の入力にしか収まらない。一次情報:

* `WatchSegE.count` は `1 < c.clock` を要求し `clock := c.clock - 1`（`GalilScaffoldTopWatchSegE.lean:26`）
* `WatchSegE.match` は `c.clock = 1` を要求し `clock := delay`(=2048) に戻す（同 `:33`）

**訂正 2（訂正 1 のあと考えすぎた）**: そこから「`ReachesWatchPhase` の無条件形は
成り立たない、選言に作り直して消費者も書き換えが要る」と書いた。**これは考えすぎ。**
既存の idle chain 版 `GalilSegmentConstructB.watchSegE_constructB` は `n < c.clock` を
**要求していない**——clock を構成の中で処理し、結論は既に
`es.length = n ∨ SegEnd P c' t` という 2 択になっている。呼び出し側が渡す `n` は
`headRank r.right * 2048 + c.clock`（入力が尽きるまでの全機械ステップ数）。

**live chain 版も同じ形でよかった。** 新しい概念は要らない。
異なる操作的意味論を持つ機械同士の対応を、既にある型に合わせて写すだけ。

### 今日証明したもの（すべて標準公理、`sorry` ゼロ）

**`PalPeg/ChainReachesWatchFromFound.lean`（新規）**

| 定理 | 内容 |
|---|---|
| `chainReachesWatch_of_found` | found 文脈から「長さ `2h+2` の任意のイベント列で watch に着く」 |

`found_to_watchStart_least` の `dm`（中央の事象）は**引数**なので、`list_split_mid` が
出す実際の中央要素ごとに定理を当て直す。そのとき `h` が揺れないことを保証するのが
`hCursor : (denote y.config).pos 11 = h`（DP 出力カーソル）。**これが無いと `h` の
一意性が言えず、「長さ `2h+2`」という主張そのものが `dm` 依存になって壊れる。**
誕生 chain と `chainStart` の同一視は `chainMatched_unique`。

**`PalPeg/CopyPhaseTickMatched.lean`（新規）** — `.match` を区間に載せるための前提

| 定理 | 内容 |
|---|---|
| `LagPos`（def） | chain の lag が正（`.copy` / `.back` 相でだけ内容がある） |
| `lagPos_tick` | `LagPos` は 1 tick で保たれる（事象によらず） |
| `lagPos_chainStart` / `lagPos_of_chainMatched_chainStart` | 誕生時の lag は `radius = ofNat (r0+1)` で正 |
| `chainStep_back_shape'` | `.back` の 1 手は lag を保った `.back` か lag を受け継いだ `.watch` |
| `backChain_tick_true_exists` | **`.back` 相でも一致事象の `ChainTick` は存在する**（lag 正のとき） |
| `copyOrBack_tick_true_exists` | `CopyOrBack` ＋ lag 正なら一致事象でも 1 手ある |
| `copyOrBack_tick_true` | 一致事象でも相は copy/back か watch に閉じる |

**以前 `sorry` を書きかけた場所の本当の障害はここだった。** `.back` から `backDone` で
生まれた watch に `ChainMatched` を当てるには `Outer w true w'` が要り、その 2 枝は
`queued`（`zero w.lag = false`）と `immediate`（`zero w.lag = true` ∧ `Good w`）。
`Good` は誕生時には出ない（`WatchOkRefute.watchOk_false`）。しかし
**誕生した chain の lag は正**（`chainStart … radius` が `lag = margin = radius` を置き、
copy/back の `ChainStep` は lag を触らず `ChainMatched` は `inc` するだけ）なので
`Outer.queued` が無条件に使え、`Good` は要らない。
同じ正値が `ChainMatched.breaks`（`BreakStep` は `zero w.lag = true` を要求、
`GalilScaffoldTopChainVM:27`）も排除する。

**不変量は `positive` で書くこと。** `zero lag = false` では `inc` で保たれない
（`⟨[], [()]⟩` の `inc` は `reset`）。`positive` なら保たれる。

**`PalPeg/LiveSegmentConstruct.lean`（新規）** — `constructB` の live chain 版

| 定理 | 内容 |
|---|---|
| `match_step_live` | 一致比較 1 手分の証人（`WatchSegE.match` の側条件をすべて作る） |
| `watchSegE_constructLive` | **live chain 版の区間構成。clock の余裕は要らない** |

探索側の帳簿（`ReadyFuel` / `hsearch`）は live chain では**丸ごと不要**——
`searchEffect P a s v` は `s.chain ≠ .idle` の枝で `v = searchLens.get s` に潰れ、
`chainBorn` も `false` になるので誕生も起きない。`SegEnd` の 5 枝のうち live で
実際に出るのは `.mismatch` だけ（`.ended` は `.wait` で素通しして chain を進める方が得、
`.found` / `.foundBackground` は探索が不活性、`.lastLetter` は入力側の都合）。

**`PalPeg/ReachesWatchFromRun.lean`（新規）** — 橋

| 定理 | 内容 |
|---|---|
| `reachesWatchPhase_or_segEnd` | **`ReachesWatchPhase` ∨ `SegEnd` で早期終了**（clock の余裕なし） |
| `prepLandingWatchC_or_segEnd` | 節 4 の正しい形まで（到達した側） |

### 次にやること

1. found 文脈から `reachesWatchPhase_or_segEnd` の 3 入力を作る配線:
   `CopyOrBack sP.chain`（`copyOrBack_of_chainMatched_chainStart` ＋ `copyInv_of_found`）、
   `LagPos sP.chain`（`lagPos_of_chainMatched_chainStart`）、
   `hChainReachesWatch`（`chainReachesWatch_of_found`）。
   `FoundCompareCtxC`（`CloseoutWatchRound2:270`）が `ChainMatched (chainStart … sF.radius) ch` と
   `sP = afterBirth true (afterCompare …)` を持っているので材料は揃っている。
   **残る側条件は `sF.radius = ofNat (r0+1)`**（`found_to_watchStart_least` が
   `ofNat (r0+1)` 形を要求し、`LagPos` も `positive sF.radius` を要求する）。
   これは radius 台帳の話で、found 時点で radius が正の canonical counter であること。
   `hmP` / `hrP` / `hcP`（`1 ≤ cP.clock`）は `foundExit_compare_final20` に既にある。
2. その 2 択を `foundExit_compare_final18` の節 4 / 節 7 に配線する。**消費者側を
   書き換える必要がある**（`hpack` の `∀` 形は `FoundPackRefute` で反証済み）。
3. 4 義務のうち最短は `obligation_shiftPalAlongTrace`。`ShiftPalAlongTrace.
   shiftPal_alongTrace` が既に正しい形で、残差は `H_readsShift` / `H_freshShiftAtShiftEntry` /
   `hFreshBranch` の 3 本。ただし `H_readsShift` の producer
   `RoundSegFromRun.readsShift_at_actual` は前ラウンド起点の `OriginAt` と
   構成 run / 実 run の対を要求するので、1 手では落ちない。



































## 2026-09-19 n124: 節 4 / 節 7 の供給経路が繋がった — 残るは `AnswerAhead` の復号 1 本

**全体 build 成功（EXIT=0）。公理は 4 義務のまま。無条件 PAL は未完。§10.5 は未達。**

### 今日繋げた経路（すべて標準公理、`sorry` ゼロ）

    FoundCompareCtxC
      → copyOrBack_of_chainMatched_chainStart      （CopyPhaseTick）
      → CopyOrBack sP.chain
      → watchSegE_backgroundRun_live               （CopyPhaseTick、帰納の本体）
      → 「watch 到達」∨「n 手走破でまだ copy/back」
      → reachesWatchPhase_of_backgroundRun         （FoundPackCorrected）
      → ReachesWatchPhase
      → prepLandingWatchC_at_reachedWatch          （節 4 の正しい形）
        reachesWatchPhase_of_breakLandingAtReachedWatch（節 7 も同じ供給）

### 残る外部入力は 4 つ、うち 3 つは found 文脈にある

| 入力 | 出どころ | 状態 |
|---|---|---|
| chain が `n` 手で watch に着く | `GalilPrepLeast.found_to_watchStart_least` | **既存**（イベント列の中身を問わない） |
| clock の余裕 `n < cP.clock` | 誕生時の clock は `delay = 2048`、`n = 2h+2` | 予算層 |
| `PlaceAhead walker n` | `GalilPrepLeast.found_copy_walk_least` の `CopyWalk` | 既存（取り出しは未実装） |
| **`AnswerAhead answer n`** | `GalilScaffoldChainAnswer.found_output` の復号 | **未実装（次の 1 本）** |

### `AnswerAhead` の復号（次にやること）

`found_output` は `SafeQuanta` ＋ `Result` から

    denote (y.config.tapes 11) = GalilDpCounters.output h ∧
    head (y.config.tapes 11) = h ∧ (tapes 11).focus = 8 ∧ (tapes 11).left ≠ []

を与える（標準公理）。一方

    output h i = if i = 0 then 4 else if i ≤ h then 8 else 6
    denote t   = read (t.left.reverse ++ t.focus :: t.right)
    head t     = t.left.length
    AnswerAhead t n := ∃ ls, t.focus :: t.left = List.replicate n 8 ++ 4 :: ls

なので、`t.left.reverse` は index 0..h-1 で `[4, 8, …, 8]`、つまり
`t.left = [8, …, 8, 4]`（8 が `h-1` 個）、`t.focus` は index `h` で `8`。
したがって `t.focus :: t.left = List.replicate h 8 ++ 4 :: []` で
**`AnswerAhead t h` が `ls = []` で成り立つ**。

証明は `denote` の index 等式からリスト等式を復元する機械的な作業
（`List.ext_getElem?` 系）。**これが節 4 / 節 7 の供給に残る唯一の未実装。**

### `StartShape` は使わないこと

`GalilLeafStartShape.not_startShape` が**あらゆる `Shared` について**反証済み
（`∀ s : GalilVM` が無制約で、`.found` 状態の任意の VM に DP の形を要求する）。
`AnswerAhead` / `PlaceAhead` は `found_copy_walk_least` / `found_output` から取ること。

## 2026-09-19 n123: live chain 版区間構成の材料一覧（これで全部）

**全体 build 成功（EXIT=0）。公理は 4 義務のまま。無条件 PAL は未完。§10.5 は未達。**

次のセッションが `GalilSegmentConstructB.watchSegE_constructB` の live chain 版を
書くときに要るものを、**全部一次情報で確認して**並べる。

### chain 側（すべて既存、標準公理）

| 定理 | 場所 | 内容 |
|---|---|---|
| `copy_step_exists` | `GalilBranchInvariants:350` | `CopyInv` から `ChainStep` の存在 |
| `copyInv_step` | `GalilBranchInvariants:369` | `CopyInv … (n+1)` は 1 手で `CopyInv … n` |
| `copy_run_to_back` | `GalilBranchInvariants:383` | copy 相は `n+1` 手で `.back` に着き `OnBlock v'` を渡す |
| `chainReady_of_blockInv` | `GalilChainReadyProgress:59` | `BlockInv` ＋ 各相の追加事実から `ChainReady` |
| `found_to_watchStart_least` | `GalilPrepLeast:121` | `SafeQuanta` ＋ `Result` から `ChainTicks (bs ++ dm :: cs) x1 (.watch (watchStart …))`（イベント列の中身は任意） |

### 今日足した差分（`PalPeg/CopyPhaseTick.lean`、標準公理）

| 定理 | 内容 |
|---|---|
| `chainStep_copy_shape` | `.copy` から出る `ChainStep` の行き先は `.copy` か `.back` |
| `chainMatched_exists_copy_or_back` | その両方に `ChainMatched` の構成子がある |
| `copyChain_tick_exists` | よって `ChainTick a` は一致ビット `a` によらず存在する |
| `copyChain_tick_not_idle` | 行き先は idle にならない（次段の `WatchSegE.match` の側条件） |

### run 側（既存、模倣する対象）

| 定理 | 場所 | 内容 |
|---|---|---|
| `watchSegE_constructB` | `GalilSegmentConstructB:124` | **idle chain 版**。結論は `(es.length = n ∨ SegEnd P c' t)` |
| `watchSegE_constructS` | `CloseoutReadyStage:544` | 同上（`ReadyPacedS` 版） |
| `watchSegE_events` | `GalilScaffoldTopWatchSegE:170` | 区間から `ChainTicks es s.chain t.chain`（`chain ≠ idle` が要る） |
| `chainTicks_unique` | `GalilScaffoldTopChainUnique:87` | `ChainTicks` は行き先を一意に決める |

### 到達後（今日実装、`PalPeg/FoundPackCorrected.lean`）

    reachesWatchPhase_of_chainTicks → ReachesWatchPhase
      → prepLandingWatchC_at_reachedWatch（節 4 の正しい形）
      → BreakLandingAtReachedWatch / reachesWatchPhase_of_breakLandingAtReachedWatch（節 7）

### 書くべきもの（唯一の残り）

`watchSegE_constructB` の **live chain 版**。変更点は 3 つだけ:

1. 不変量 `s.chain = ChainVM.idle` を「`s.chain` が `.copy` で `∃ n, CopyInv …`」に替える
   （`copyInv_step` で運ぶ）。
2. 構成子は `matchIdle` / `countR` / `matchIdleR` の代わりに `match` / `count` / `wait`
   （`WatchSegE.match` の側条件は `s.chain ≠ .idle` だけ、`copyChain_tick_not_idle` で維持）。
3. chain の 1 手は `copyChain_tick_exists` から取る（`WatchOk` 経由は不可、反証済み）。

`MInv` と `ScanInvariant` は chain に触れないので `constructB` の扱いをそのまま使える。

## 2026-09-19 n122: live chain 版区間構成の材料も既にある（`copy_step_exists`）

**全体 build 成功（EXIT=0）。公理は 4 義務のまま。無条件 PAL は未完。§10.5 は未達。**

n121 で「live chain 版 `watchSegE_construct` が唯一の残り」と測った。その構成に要る
**chain 側の全域性**も既存だった:

* `GalilBranchInvariants.copy_step_exists`（`:350`）— `CopyInv t h p v n` から
  `∃ y, ChainStep (.copy t h p v lag margin ver) y`（**copy tick の全域性**）
* `GalilBranchInvariants.onPrefix_start` / `onPrefix_put` — `OnPrefix` の維持
* `GalilChainTickable`（`:186`, `:201`）にも `.copy` からの `ChainStep` 構成がある

したがって live chain 版の帰納は

| 必要なもの | 出どころ |
|---|---|
| chain の 1 手（`.copy` 相） | `copy_step_exists`（`CopyInv` から） |
| `WatchSegE.match` の側条件 | `s.chain ≠ .idle` のみ（`GalilScaffoldTopWatchSegE:34`） |
| `MInv` / `ScanInvariant` の維持 | chain に触れないので `constructB` と同じ扱い |
| 結論の選言 | `(es.length = n ∨ SegEnd P c' t)` をそのまま踏襲 |

で組める。**残っているのは `CopyInv` を誕生から区間に沿って運ぶ部分と、
`constructB` の並行版を書く作業（~150 行の帰納法）。**

`WatchOk` 経由の `chainOk_tick_false` は使えない（`WatchOk` は反証済み、
`WatchOkRefute.watchOk_false`）。`CopyInv` 経由で行くこと。

## 2026-09-19 n121: `ReachesWatchPhase` の最後の 1 ピースは「live chain 版の区間構成」

**全体 build 成功（EXIT=0）。公理は 4 義務のまま。無条件 PAL は未完。§10.5 は未達。**

### 測ったこと

区間構成の既存定理は 2 本:

* `CloseoutReadyStage.watchSegE_constructS`（`:544`）
* `GalilSegmentConstructB.watchSegE_constructB`（`:124`）

どちらも

    s.chain = ChainVM.idle → … →
    ∃ es c' t r', WatchSegE P q first delay es c s c' t ∧ … ∧ t.chain = ChainVM.idle ∧ …
      ∧ (es.length = n ∨ SegEnd P c' t)

**`chain = idle` を要求し、かつ保存する**——つまり**誕生前の相専用**。

**誕生後（`.copy` 相）の live chain 版は存在しない。** これが `ReachesWatchPhase` に
残る唯一のピース。

### 良い知らせ

* 結論の形 `(es.length = n ∨ SegEnd P c' t)` は**まさに必要な選言**
  （「`n` 手走る」か「区間が終わる」）。設計はそのまま使える。
* `GalilLiveCentreReplay.MInv` は **chain に触れない**（replay と中心の事実だけ）。
  `ScanInvariant` も同様。したがって live chain 版は構造的に並行で、
  `matchIdle` / `countR` / `matchIdleR` の代わりに `match` / `count` / `wait` を使うだけ。
* `WatchSegE.match` が要求するのは `s.chain ≠ .idle` だけ（`GalilScaffoldTopWatchSegE:34`）で、
  `.copy` 相はそれを満たす。chain は誕生後 idle に戻らない。

### `ReachesWatchPhase` の残り（これで全部）

    live chain 版 watchSegE_construct（未実装、~150 行、既存 constructB の並行版）
      → 長さ 2h+2 の区間
      → reachesWatchPhase_of_chainTicks（今日実装、標準公理）
      → ReachesWatchPhase
      → prepLandingWatchC_at_reachedWatch / BreakLandingAtReachedWatch（今日実装）
      → hpack の壊れていた 2 節の正しい形

chain の中身（`found_to_watchStart_least`）も、shift に行けないこと
（`no_shift_from_copyChain`）も、橋（`reachesWatchPhase_of_chainTicks`）も済んでいる。

## 2026-09-19 n120: `hpack` 7 節の監査完了 — **壊れているのはちょうど 2 節、同じ欠陥**

**全体 build 成功（EXIT=0）。公理は 4 義務のまま。無条件 PAL は未完。§10.5 は未達。**

`CloseoutFoundRoute1.foundExit_compare_final20` の `hpack`（7 節の束）を
1 節ずつ定義に当たって測った結果:

| # | 節 | 判定 | 理由 |
|---|---|---|---|
| 1 | `PrepInputsG3` | **健全** | `ChainMatched (chainStart …) sP.chain` を言う。誕生直後の `.copy` と整合 |
| 2 | `MismatchExitG` | **健全** | `GalilPrepMatch.PrepChain s1.chain` で guard（prep 相向けに設計されている） |
| 3 | `FallbackReachS` | **健全** | `LiveScanWatch c1 s1` を**仮説**に取る（watch でなければ空虚） |
| 4 | `PrepLandingWatchC` | **偽** | `∀ es c2 s2, WatchSegE … → ∃ w, s2.chain = .watch w`。`WatchSegE.stop` で `sP` 自身に当たる |
| 5 | `PrepBirthLagC'` | **健全** | 誕生データ（`sP = afterBirth true (afterCompare …)`）を仮説に取る |
| 6 | `LandingFreshC'` | **健全** | `s1.chain = .watch w` を**仮説**に取る |
| 7 | `BreakLandingC` | **偽** | `∀ es c2 s2, WatchSegE … → s2.chain = .watch (freshWatch …)`。同じ形 |

**壊れているのはちょうど 2 節で、どちらも同じ形**——
「`∀ (WatchSegE 区間)` の結論で watch を要求する」。`WatchSegE.stop cP sP` が
無条件に存在するので、その `∀` が誕生状態 `sP` 自身に当たる。

機械検査（`PalPeg/FoundPackRefute.lean`、標準公理のみ）:

    hpack_false_of_foundCompareCtx          （節 4）
    prepLandingLiveC_false_of_foundCompareCtx（節 4 の親戚 `PrepLandingLiveC`）
    breakLandingC_false_of_foundCompareCtx   （節 7）
    hpack_false_of_foundReachable            （到達可能性込み）

### 直し方（節 4 は実装済み、節 7 は同型）

`FoundPackCorrected.ReachesWatchPhase`（`∀` → `∃`）に付け替え、到達先で主張する。
節 4 については `prepLandingWatchC_at_reachedWatch` が既存 producer
（`CloseoutWatchRound10.prepLandingWatchC_of_short`）をそのまま当てる形で実装済み。
節 7 も同じ形に直せる（`BreakLandingC` の結論を到達先 `(c2, s2)` で主張する）。

**5 節は触らなくてよい。** 健全な 5 節を巻き添えで書き換えないこと。

## 2026-09-19 n119: `ReachesWatchPhase` の chain 側は既に証明済み — 残りは「誕生後 `2h+1` tick を scan で走れるか」

**全体 build 成功（EXIT=0）。公理は 4 義務のまま。無条件 PAL は未完。§10.5 は未達。**

### chain 側（既存、無条件）

`GalilPrepLeast.found_to_watchStart_least`（および `GalilScaffoldTopChainEntry.found_to_watchStart`）は、
`SafeQuanta` ＋ `GalilDpCorrect.Result` から

    ∃ h c ys b, Candidate w lower h ∧ read p = some c ∧ ys.length + 1 = h ∧
      (denote y.config).pc = 346 ∧ (denote y.config).pos 11 = h ∧
      ∀ bs cs, bs.length = h → cs.length = h+1 →
        ∃ x1, （x1 は chainStart …（または ChainMatched 1 歩））∧
          ChainTicks (bs ++ dm :: cs) x1 (.watch (watchStart ver c ys b …))

を与える。**イベント列 `bs` / `cs` の中身には条件が無い**（長さだけ）。
そして `SafeQuanta` ＋ `Result` は `GalilScaffoldSearchRun.calibrated_quanta_safe` が
無条件に出す（n114）。

**つまり「誕生した chain は `2h+1` tick で watch になる」は既に証明済み。**

### 残りは run 側の条件（そしてそれは無条件ではない）

`ReachesWatchPhase` に必要なのは、その `2h+1` tick が**実際に走ること**＝
`WatchSegE` が誕生から `2h+1` 手続くこと。`WatchSegE` の構成子はすべて
`c.mode = .scan` を要求するので、途中で scan を離れたら区間が切れる。

**そして途中で scan を離れる経路が実在する。** copy/back 相の chain は `.watch` では
ないので `shiftGuardVM`（`s.chain = .watch w` を要求）が立たず、不一致が来たら
`Tick.scan_shift` は使えず `scan_fallback` になる
（既存の定理 `not_shiftGuard_afterMismatchB`、CLAUDE.md §3c に記録あり）。

したがって正しい形は**選言**:

    「誕生後 `2h+1` tick 走って chain が watch になる」
      ∨ 「その前に不一致が来て fallback に落ちる（chain は捨てられる）」

found 経路のラウンド機構は**前者の枝でだけ**適用できる。
`FoundPackCorrected.ReachesWatchPhase` は前者を名指したもので、
`prepLandingWatchC_at_reachedWatch` がその到達先で既存 producer を当てる。

### 次にやること

1. 選言の後者（fallback 枝）を `foundExit_compare_final20` の結論側で吸収する形に切り直す。
2. `hpack` の残り 6 節（`MismatchExitG` / `FallbackReachS` / `PrepBirthLagC'` /
   `LandingFreshC'` / `BreakLandingC` / `PrepInputsG3`）を**同じ目で**洗う——
   誕生直後の状態に watch 相の性質を要求していないか。
   （`PrepInputsG3` は `ChainMatched (chainStart …) sP.chain` を言うので整合的。
   `LandingFreshC` は Round 44 で既に反証済み。）

## 2026-09-19 n118: **found 経路が閉じなかった根本原因**（`PrepLanding*` 一族が誕生直後に watch を要求）

**全体 build 成功（EXIT=0）。公理は 4 義務のまま。無条件 PAL は未完。§10.5 は未達。**

### 機械検査した事実（`PalPeg/FoundPackRefute.lean`、標準公理のみ）

| 定理 | 内容 |
|---|---|
| `chainMatched_copy_stays_copy` | `ChainMatched` は `.copy` から `.copy` にしか行かない |
| `chainStart_is_copy` | `chainStart` は `.copy`（`rfl`、公理ゼロ） |
| `prepLandingLiveC_watch_start` | `PrepLandingLiveC cP sP` → `∃ w, sP.chain = .watch w` |
| `hpack_false_of_foundCompareCtx` | `FoundCompareCtxC` ＋ `PrepLandingWatchC` → `False` |
| `prepLandingLiveC_false_of_foundCompareCtx` | `FoundCompareCtxC` ＋ `PrepLandingLiveC` → `False` |
| **`hpack_false_of_foundReachable`** | **`InvLPC` ＋ `SegReachedW` ＋ found 比較 → `False`** |

### 根本原因

`CloseoutWatchRun.LiveScanWatch c s` の最終節は `∃ w, s.chain = .watch w`。
`PrepLandingLiveC` / `PrepLandingWatchC` はどちらも
`∀ es c2 s2, WatchSegE … cP sP c2 s2 → …` の形で、`WatchSegE.stop cP sP` が
無条件に存在するため `es = []` 実例で **`sP` 自身が watch であること**を強制する。

ところが found 比較直後の `sP` の chain は `chainStart …`（`.copy`）から
`ChainMatched` で 1 歩進んだもので、**`ChainMatched` は構成子の形を保つ**
（`.copy → .copy` / `.back → .back` / `.watch → .watch` / `.watch → .broken`、
`GalilScaffoldTopChainVM:69`）から、必ず `.copy`。

**つまり found 経路の設計は「chain は誕生直後から watch している」を前提にしている。**
モデルは Scala 正本どおり `chain.start()` が `.copy` 相を作り、周期を写し、巻き戻し、
それから `.watch` になる。1 tick では届かない。

**これが found 経路が閉じなかった根本原因**と見られる。`hpack`（7 節の束）を
証明しようとしていた作業は、偽の命題を証明しようとしていた。

### 直し方の方向（未実施）

`PrepLanding*` を `sP`（found 比較直後）ではなく、**chain が `.watch` になった後の
landing** で主張する。`CloseoutWatchRound10.prepLandingWatchC_of_short` は
watch 始点 ＋ clock 上界から `PrepLandingWatchC` を出すので、正しい場所では真。
`FoundCompareCtxC` から watch 相までを繋ぐ区間（copy → back → watch）を
別に持つ必要がある。

### 副次的な修理

`CloseoutFoundRoute1` はビルド不能だった（`:238` の `StepsAll.zero` 型不整合、
モデル修正 `M-periodOnly` の取り残し）。直した（`afterBirth` はヘッドを触らないので
`OutputRel` / `ScanInvariant` / `chain` は congruence で移る）。
これで `foundCompareCtxC_of_found` が使えるようになり、到達可能性込みの反証が書けた。

## 2026-09-19 n117': **`hpack` は REFUTED（条件付き）** — 機械検査済み

`PalPeg/FoundPackRefute.hpack_false_of_foundCompareCtx`（標準公理 `propext`/`Quot.sound` のみ）:
`FoundCompareCtxC` の証人 ＋ `PrepLandingWatchC` から `False`。決め手は
**`ChainMatched` が構成子の形を保つ 1 歩の関係**であること
（`.copy → .copy` / `.back → .back` / `.watch → .watch` / `.watch → .broken`、
`GalilScaffoldTopChainVM:69`）で、`chainStart` は `.copy`（`:41`）だから
`ch` は `.watch` になれない。

**未構成の証人は `FoundCompareCtxC`** なので `REFUTED（条件付き）`。
また `CloseoutFoundRoute1` 自体はビルドが壊れている（`:238`、`StepsAll.zero` の型不整合）。

下は反証前の記録。

## 2026-09-19 n117: found 経路の `hpack` は**偽の疑いが濃い**（節どうしが衝突している）

**全体 build 成功（EXIT=0）。公理は 4 義務のまま。無条件 PAL は未完。§10.5 は未達。**

### 一次情報で見たこと

`CloseoutFoundRoute1.foundExit_compare_final20` の `hpack` は

    ∀ cP sP a ls rs qw gap,
      FoundCompareCtxC centre place entry q first w c r cP sP → w = … →
      PrepInputsG3 … cP sP ∧ MismatchExitG … ∧ FallbackReachS … ∧
      PrepLandingWatchC … cP sP ∧ PrepBirthLagC' … ∧ LandingFreshC' … ∧
      (∀ sF, BreakLandingC … sF cP sP)

**節 4 `PrepLandingWatchC` は `sP.chain` が watch であることを強制する。**
定義（`CloseoutWatchRound7:123`）は

    ∀ es c2 s2, WatchSegE P q first 2048 es cP sP c2 s2 → ∃ w, s2.chain = .watch w

で、`WatchSegE.stop cP sP` は無条件に存在するから `es = []` 実例で `s2 = sP` となり
`∃ w, sP.chain = .watch w` が出る（これは既存の定理
`CloseoutWatchRound8.prepLandingWatchC_watch_start` そのもの）。
同ファイル `:341` には `not_prepLandingWatchC_of_idle`
（「無制限の `PrepLandingWatchC` は idle 始点で偽。**この述語は書かれていない前提を
持っている**」）という反証まで既にある。

**ところが guard の `FoundCompareCtxC`（`CloseoutWatchRound2:270`）は
`sP = afterBirth true (afterCompare sF ⟨…⟩ vq)`、すなわち `sP.chain = ch` で、
`ch` は `ChainMatched (chainStart …) ch ∧ ch ≠ .idle` を満たす**任意**の chain。
`chainStart` は `.copy` なので `ch` は `.copy` でありうる。** つまり
found 比較の**直後**（chain が生まれたばかり）に `sP.chain` が watch であることを
要求している。chain は 1 tick に 1 歩しか進まないので、これは成り立たないはず。

### 位置づけ

* `hpack` は 7 節の**束**。CLAUDE.md「葉を束に畳み込むと偽になりうる」の典型。
  しかも `hpack` という名前は**前にも偽になっている**（`CloseoutPackRefute.hpack_false`）。
* `PrepLandingWatchC` 自身は偽ではない。正しい場所（chain が watch になった後の
  landing）で使えば真で、producer もある（`CloseoutWatchRound10.prepLandingWatchC_of_short`、
  watch 始点 ＋ clock 上界から）。**束ねる場所が間違っている。**

**`REFUTED` とは書かない**（`False` を導く機械検査済みの定理がまだ無い）。
反証のレシピ: `FoundCompareCtxC` の証人を 1 つ作り（`WatchSegE` / `searchEffect` /
`refresh` の証人が要る、ここが手間）、`ch` を `chainStart …` の直後の `.copy` に取る。
そのうえで `prepLandingWatchC_watch_start` を当てれば `.copy = .watch w` で矛盾。

### 次に触るときの指示

**`hpack` を束のまま証明しようとしない。** 7 節を個別に、それぞれ正しい guard の下で測る。
特に `PrepLandingWatchC` / `PrepBirthLagC'` / `LandingFreshC'` は
「chain が watch になった後」の述語なので、found 比較直後の `sP` で要求するのは誤り。
（`LandingFreshC` は Round 44 で既に反証され `LandingFreshC'` に割られている——
同じ場所で同じ種類の誤りが繰り返されている。）

## 2026-09-19 n116: **ファイルの docstring が未実装の定理を完了として書いていた**（監査上の発見）

**全体 build 成功（EXIT=0）。公理は 4 義務のまま。無条件 PAL は未完。§10.5 は未達。**

### 何を見つけたか

`PalPeg/CloseoutRealize1.lean` の冒頭 docstring は §1〜§6 の 6 節を列挙しており、
そのうち

> §6 `pal_in_peg_of_progPal` — the *direct* `Prog` route, which bypasses the
> latch (and therefore all of `CloseoutPackRun*`) entirely via
> `PalPeg.pal_in_peg_of_structured`.

は「latch を——したがって `CloseoutPackRun*` 全体を——迂回する直接経路」と読める。
`hC`（`obligation_localRealization`）の壁を丸ごと回避できる話に見える。

**実際にはこのファイルは 89 行・宣言 2 つしかない**（`H_realizeSMG2'` と
`h_realizeSMG2'_of_LIMG2'`）。§3〜§6 は**存在しない**。書いた当時の計画を、
完了したかのような文体で docstring に書いていた。

docstring を実態に合わせて訂正した（§1/§2 は「実装済み」、§3〜§6 は「構想のみ、未実装」、
特に §6 は「存在しない。迂回路があると思って探すと時間を失う」と明記）。

### 位置づけ

CLAUDE.md は「散文の論証・他ファイルのヘッダ・類推・過去の自分の記述は一次情報として
扱わない」と定めている。今日それに違反した例が 3 つ出た:

1. n114 — CLAUDE.md §3 の「found 経路は未着手」を信じた（実際は DP 側が無条件で証明済み）
2. n115 — 同様に `PrepInputsG3` を葉だと思った（実際は producer が標準公理で存在）
3. n116（これ）— **ファイル自身の docstring** が未実装の定理を完了として書いていた

**3 番目が一番危険**で、「このファイルにこう書いてある」は普通なら信頼できるはずの情報源に
見える。**宣言の存在は `grep "^theorem"` で確認する。docstring の節番号を数えない。**

### `hC` の現状（実測）

* `CloseoutRealize1.h_realizeSMG2'_of_LIMG2'` — 実装済み（標準 3 公理）。
  `LocalStep` の証人は付随的で、任意の厳密実時間 `StructuredMachine` で足りる、を
  `H_realizeLIMG2'` について示す。
* ただし最上位が使うのは `H_realizeLIMW'` で、そこへの連結は**未確認**。
* `Workbench` §4 の記録（`TextFeed*` 153 モジュールが正本に 1 本も届いていない）は有効。


## 2026-09-19 n115: found 経路の `hpack` 7 節のうち少なくとも 2 節は既に無条件で産出済み

**全体 build 成功（EXIT=0）。公理は 4 義務のまま。無条件 PAL は未完。§10.5 は未達。**

`hor`（`obligation_cycleOracle`）の found 葉の最上位は
`CloseoutFoundRoute1.foundExit_compare_final20` で、その `hpack` は 7 節の束:

| 節 | producer | 公理 |
|---|---|---|
| `PrepInputsG3` | **`CloseoutLaterEntry.prepInputs3_of_found_C`** | 標準 3 のみ（実測） |
| `MismatchExitG` | 未確認（`CloseoutPrepInputs2:145` に定義） | — |
| `FallbackReachS` | 未確認 | — |
| `PrepLandingWatchC` | **`CloseoutWatchRound10:153`** | 未実測 |
| `PrepBirthLagC'` | 未確認 | — |
| `LandingFreshC'` | 未確認 | — |
| `BreakLandingC` | 未確認 | — |

`prepInputs3_of_found_C` は `StageEntryC` ＋ `SegReachedW` ＋ tick のデータ ＋
`PostCompareG` から `PrepInputsG3` を**無条件で**出す
（`prepInputs3_of_found_or_later` は `Classical.choice` すら使わない）。

**つまり found 経路は「未着手」ではなく、部品が散らばったまま束が組まれていない状態。**
`hpack` は 7 節の**束**なので、CLAUDE.md の「葉を束に畳み込むと偽になりうる」の
対象でもある。次に触るときは 7 節を個別に測ること。

### このセッションで 2 回やった同じ誤り

n114 と n115 はどちらも「CLAUDE.md の散文（過去の自分の記述）を信じて
『未着手』『最大の残り』と報告し、一次情報を見たら既に証明されていた」という形。
**地図を更新する前に断定しない。** 部品の不在は grep 1 回では示せない。

## 2026-09-19 n114: 探索（DP）側は**無条件で証明済み**だった — 自分の前の報告を訂正

**全体 build 成功（EXIT=0）。公理は 4 義務のまま変化なし。無条件 PAL は未完。§10.5 は未達。**

### 訂正

n113 のあと「`cycleOracle` の found 経路は未着手、探索の `Result` を run から供給する
のが最大の残り」と書いた。**これは誤り。** CLAUDE.md §3 の散文
（「`hfound`/`hfoundBg`/`hfoundReplay` ← 未着手、最大の残り」）を一次情報として
扱ってしまった。CLAUDE.md 自身が禁じている振る舞い
（「散文の論証・他ファイルのヘッダ・類推・**過去の自分の記述**は一次情報として
扱わない」）をやった。

### 一次情報で確認したこと（すべて標準 3 公理のみ、`#print axioms` 実測）

| 定理 | 内容 |
|---|---|
| `GalilDpCorrect.initial_correct` | **無条件**。fresh な物理プリロードから走らせると `∃ y qs, Completed GalilDpCode.code (initial w lower) qs y ∧ Result w lower 0 y` |
| `GalilDpCorrect.Result` | 「OUTPUT が `first` 以上の**最小**候補を符号化している（`Candidate` と最小性つき）」または「候補が存在しないことを正しく報告」 |
| `GalilMinimalPeriod.result_least` | `Result` ＋ `pc = 346` から `∃ k, Candidate ∧ pos 11 = k ∧ 最小性` |
| `GalilScaffoldSearchRun.dp_quanta_safe` / `calibrated_quanta_safe` | **無条件**。run 相の探索状態と較正済み予算から `SafeQuanta s ⟨Preload.initial w lower, false⟩ used t ⟨v,true⟩ ∧ t.mode ≠ .run ∧ Result w lower 0 (denote v)` |
| `GalilTickFair.readFun_code` | **`decide` で証明済み**（`ReadFunB` 経由）。これで `safeQuanta_unique` が探索量子の決定性を与える |

さらに `calibrated_quanta_safe` / `dp_quanta_safe` は既に
`GalilScaffoldStagePrepare`（:207, :304）、`GalilBranchInvariants2`（:251）、
`GalilScaffoldChainFallback`（:1848）で**消費されている**。

### したがって

**探索の正しさ（DP が最小周期を出すこと、量子化しても結果が同じこと、決定的であること）
は既に無条件で証明され、ステージ層まで配線されている。**

`CloseoutPrepInputs3.PrepInputsG3` が `SafeQuanta` ＋ `Result` を**仮説として束ねている**
のは、ステージ層とそこの間が繋がっていないだけ。つまり found 経路の残りは
「新しい数学」ではなく**層と層の配線**。

`first_round` が要る `Candidate` も `result_least` から出る。

### 次

`GalilScaffoldStagePrepare` の結論と `CloseoutPrepInputs3.PrepInputsG3` の間を繋ぐ。
これが通れば `hor` の found 葉と、`shiftPal*` の基底（新鮮な chain の第 1 shift、
`first_round`）の両方に効く。


## 2026-09-19 n113: 偽の疑いが濃い公理を run 形／trace 形に差し替えた（3 → 4）

**全体 build 成功（EXIT=0、エラー 0、`sorry` なし）。ラチェット緑（4 義務に更新）。
無条件 PAL は未完。計画書 §10.5 は未達。**

    'PalPeg.PalInPeg.unconditional' depends on axioms: [propext,
     Classical.choice, Quot.sound,
     obligation_cycleOracle, obligation_localRealization,
     obligation_shiftPalAlongRun, obligation_shiftPalAlongTrace]

### なぜ増やしたか

n112 で `obligation_shiftPalAtScanStates`（一状態述語 `BigPack2MG7W` の形）が
**偽の疑いが濃い**と分かった。放置すると「公理 3 個」という数字が進捗の指標として
機能しない。CLAUDE.md「偽の前提で数字を作らない」に従い、**数が増えても真であろう
形に割った**。

| 新しい公理 | 形 | 消費者 |
|---|---|---|
| `obligation_shiftPalAlongRun` | `InvLPC w c r` 起点から `Steps` で到達する scan 状態 | `packRunR_MW_marksFree`（`h_oracleIMW_of_MC3_W` 経由） |
| `obligation_shiftPalAlongTrace` | `PreTraceIMW` の trace の scan 点（`1 ≤ j ≤ Tc`） | `BranchSupply` の 5 定理（`scanLandingObligations_alongTrace_of_matchRest` ほか） |

どちらも**履歴が run で固定される**ので、旧版の欠陥（状態述語から履歴の事実を要求する）は無い。

### 危うくもう 1 個過剰量化を撒くところだった

trace 形の公理を最初 `PreTraceIMW` の仮説**なし**で書きかけた。そうすると
`st` が無制約関数になって `∀ z, … → ShiftPal z.vm` と同値に潰れる——
`hav` が偽になったのとまったく同じ形（過剰量化 13 例目、自分で撒く 5 例目になるところ）。
書いた直後に気づいて `PreTraceIMW` を仮説に入れた。**trace 形を書くときは
`PreTrace*` を仮説に入れたか必ず確認する。**

### 放電器は用意してある

| 公理 | 放電器 | 残差 |
|---|---|---|
| `shiftPalAlongTrace` | `ShiftPalAlongTrace.shiftPal_alongTrace` | `H_readsShift`（trace 形）＋ `H_freshShiftAtShiftEntry`（tick 形）＋ `periodOnly = false` 分岐 |
| `shiftPalAlongRun` | `CloseoutBundleRun.shiftPal_of_run_B` | 同じ 3 つ（run 形） |

`AuxPack` と `canRight` はどちらも既存の trace 補題で放電済み。
`H_readsShift` は `RoundSegFromRun.readsShift_at_actual` が実状態で出す
（`OriginAt` → `roundSeg_at_actual` → `originShift_of_roundSeg` → `h_readsShift_of_originShift`）。

### 触ったファイル

`BranchSupply`（5 署名を trace 形に、適用 1 箇所）、`CloseoutMarksPack`
（`packRunR_MW_marksFree` を run 形に）、`CloseoutFinalBranch`
（`given_scanLandingObligations`）、`PalInPegUnconditional`（公理 2 本）、`Axioms`（ラチェット）。


## 2026-09-19 n112: **`obligation_shiftPalAtScanStates` は偽の疑いが濃い**（進捗計器の訂正）

**全体 build 成功（EXIT=0、エラー 0、`sorry` なし）。ラチェット緑。公理は 3 義務。
無条件 PAL は未完。計画書 §10.5 は未達。
そして下に書くとおり、その 3 個のうち 1 個は偽の疑いが濃い。**

### 何を測ったか

`obligation_shiftPalAtScanStates` の文はこう:

    ∀ w x, BigPack2MG7W centreC placeC entry q first w x → ScanNR x →
      ShiftPal centreC placeC entry q first w x.vm

`ShiftPal w s` の結論は

    Manacher.PalAt (encoded w) (position s.center + periodLength wch) (r₀ + 1 - periodLength wch)

で、`periodLength wch` は chain の**周期テープの長さ**。つまり
「chain が持っている周期が、入力語 `w` の本物の周期である」という**履歴の事実**を
主張している。

そこで guard `BigPack2MG7W` の場を一次情報で全部展開した:

| 場 | 中身 | 入力語 `w` に触れるか | chain に触れるか |
|---|---|---|---|
| `IPackMW.pack = LPackM` | `lrepM`（左ヘッドが `w` を表現）／`scanGeom`（`ScanInvariant w …`） | ○ | **×** |
| `IPackMW.m2 = LPackM2` | `scanGeomR` / `shiftGeom` / `rrep` / `centreRep` / `centreOrder` | ○ | **×** |
| `AuxPack.coupled = Coupled` | `idleOut` / `block : BlockInv s.chain` / `sum : SumRel s.chain (value s.radius)` / `watch : WatchOK s.chain …` | **×** | ○（ただし**カウンタだけ**） |
| `AuxPack.front = FrontPack` | front ポテンシャル | × | × |
| `AuxPack.copyP = CopyPack` | `mode ≠ copy → CopyIdle s` | × | × |
| `CentreLive` | `mode = rewind → pair → 0 < position s.center` | × | × |
| `Extra8` | `rewindMargin`（marksTape/left）／`scanAvail`（`canRight right`） | × | × |

一次情報:
`CloseoutPackRun10:140`（`LPackM`）、`CloseoutPackRun23:99`（`LPackM2`）、
`CloseoutPackRun2:105`（`AuxPack`）、`GalilChainCoupling:359`（`Coupled`）、
`GalilBranchInvariants:425`（`BlockInv`）、`GalilChainCoupling:190`（`SumRel`）、
`GalilChainCoupling:199`（`WatchOK`）、`GalilRewindSafe:50`（`CentreLive`）、
`CloseoutPackRun46:67`（`Extra8`）。

**`w` に触れる場はどれもヘッド（`Represents` / `ScanInvariant` / `RRep` / `CentreRep` /
`ShiftGeom`）の話で、chain に触れる場はどれもカウンタ（`distance` / `lag` /
`periodLength` と `radius` / `cycle` / `remaining` の数値関係）の話。
chain の周期テープの中身と入力語 `w` を結びつける場が 1 つも無い。**

`shiftGuardVM` が足すのも `symbol (period.focus) = read s.right` の **1 記号**だけで、
窓全体が周期を持つことは言わない。よって周期テープが出鱈目でも guard は通り、
結論の `PalAt` は一般に成り立たない。

### 位置づけ

これは `hpack` が偽だったのと**同じ欠陥**（`CloseoutPackRefute.hpack_false`:
「run 沿いの束を一状態述語として書いており `ChainPosInv2` からは出ない」）。
CLAUDE.md 自身が `ShiftPal` を過剰量化の 5 例のうちの **1 番目**として挙げていた。
`BigPack2MG7W` という guard を付けたのは是正のつもりだったはずだが、
上のとおりその guard は chain と `w` を一切結びつけていない。

**`REFUTED` とは書かない**（`False` を導く機械検査済みの定理がまだ無い）。
反証のレシピ: `BigPack2MG7W` の証人を 1 つ作り、chain だけを
`periodLength = 1` の watch に差し替える（どの場も chain の周期テープの中身を
縛らないので pack は保たれる）。そのうえで `PalAt (encoded w) (C+1) r₀` が破れる
`w` を選ぶ。手間は `compare` の証人（`searchEffect` を含む）の構成。

### 正しい経路は run 形（既に作ってある）

`CloseoutBundleRun.shiftPal_of_run_B` が run 形の `ShiftPal` 産出器で、
`InvLPC` の起点が idle chain なので `packRunR_MW_marksFree` の中でそのまま使える。
残差は `H_readsShift`（→ n111 の `readsShift_at_actual` で実状態で出る）と
`H_freshShiftAtShiftEntry`（狭めた版、`first_round` から）。

**したがって「公理 3 個」という数字は、そのうち 1 個が偽の疑いが濃い以上、
このままでは進捗の指標として信用できない。** 次にやるべきは数を減らすことではなく、
`hSP` を run 形に差し替えること（数は一時的に増える）。


## 2026-09-19 n111: `ScanToScan`（区間抽出）を迂回できる — `scanSeg_snoc_tick`

**全体 build 成功（EXIT=0、エラー 0、`sorry` なし）。公理は 3 義務のまま変化なし
（`obligation_cycleOracle` / `obligation_localRealization` /
`obligation_shiftPalAtScanStates`）。無条件 PAL は未完。計画書 §10.5 は未達。**

### 測定（一次情報を読んだ結果）

`obligation_shiftPalAtScanStates` の残差は `CloseoutRoundSeg` によれば 2 つ
（`RoundSeg` ＝ `CompareRounds h _ 1 _` と `H_fresh`）で、どちらも
`GalilScaffoldTopRoundS.round_next` / `GalilScaffoldTopFirstRound.first_round` が
要求する **`ScanSeg`（run の区間）** に帰着する。区間を run から抽出するのが
CLAUDE.md §1 の壁 (1)（`ScanToScan`、`CloseoutSegment`）。

さらに `CloseoutOriginRounds` のヘッダは、**`hSP` の残差と `hor` の found 経路の葉
`ShiftRoundC` は同じもの**だと定理にしている。つまり 2 つの壁ではなく 1 つ。

### 迂回路が通った

`ScanSeg` は `wait` / `count` / `match` の 3 構成子が `Tick` の
`scan_wait` / `scan_count` / `scan_match` と 1 対 1（`scanSeg_steps` がその対応を作る）。
障害は inductive が**前からしか積めない**ことだけやった。

`PalPeg/MatchedRunSnoc.lean`（新規、全定理が標準公理のみ）:

| 定理 | 内容 |
|---|---|
| `onlyMatchedRun_snoc` / `_head` / `_trans` | 射影側の末尾伸長・先頭剥がし・連結 |
| `matchedSeq_snoc_background` / `_compare` | VM 側（`MatchedSeq`）の末尾伸長 |
| `scanSeg_snoc_wait` / `_count` / `_match` | 制御つき（`ScanSeg`）の末尾伸長 |
| `compare_matched_parts` | `compareFound` ＋ `matched` ＋ watch から `galilFrame` 側の比較と `afterCompare` を取り出す（tick 逆向きの核） |
| **`scanSeg_snoc_tick`** | **run の 1 tick を `ScanSeg` に吸収。`Tick` の 24 構成子を全部潰して出口は 3 つだけ** |
| `restartNeedsBroken_of_restartVM` | 上の側条件を具体枠で放電 |

`scanSeg_snoc_tick` の 3 つの出口:

1. `ScanSeg` が 1 手伸びる
2. mode が scan を離れる（`scan_shift` / `scan_fallback` ＝ ラウンド境界）
3. chain が watch でなくなる（終端の一致比較で chain が壊れる場合）

側条件 `singlePositive cycle = false` は `RoundScan.fresh` ＋ `terminal_iff` から無償。

### `ScanToScan` は要らない公算が大きい（反証はまだ無い）

`CloseoutSegment` は「`SpanRep` は `ScanToScan` の下流」と書いていたが、`SpanRep` は
n109〜n110 で `BranchSupply.spanRepOnScanAndShift_alongTrace` により **tick ごとに**
証明できた。`RoundSeg` も同型で、区間を抽出せずに tick ごとに積めば足りるはず。

なお `ScanToScan` は「任意の scan→scan 健全 run が `ScanSeg` ＋ `Rounds` に分解する」と
全称量化しており、`ScanSeg.match` が `hwatch`（chain が watch）を要求する一方で
**idle chain の一致比較も合法な `Tick`** である以上、**偽の疑いが強い**。
機械検査した反証はまだ無いので `REFUTED` とは書かない。

### 続き（同日、`scanSeg_of_steps` 以降）

`scanSeg_snoc_tick` を `Steps` に沿って回して run 不変量に仕立てた:

* `scanSeg_of_steps` — scan ＋ watch の区間に沿って `ScanSeg` が伸びる
  （出口 2 / 3 は呼び手の不変量が潰す）
* `onlyMatchedRun_of_steps` — その末尾で **実際の状態の** `OnlyMatchedRun`
  （`CompareRounds.next` の第 1 引数そのもの）
* `compare_mismatched_parts` — ラウンド境界（`scan_shift`）で `round_next` に渡す
  `vs` / `vq` / `hcmp` / `hmis` / `hq` を `compareFound` から取り出す

さらに `PalPeg/ShiftPhaseDeterminism.lean`（新規、全定理が標準公理のみ）:

| 定理 | 内容 |
|---|---|
| `refresh_det` | 出力の更新は一意 |
| `shiftOne_det` | 1 単位の shift は行き先を一意に決める |
| `tick_shift_det` | shift 相の tick は一意（`Fair` 不要） |
| `steps_shift_det` | 中間が全部 shift 相なら同じ長さの 2 本は同じ状態に着く |
| `steps_shift_exit_unique` | **shift 相の出口は状態も長さも一意**（長さを仮定しなくてよい） |

### `round_next` の入力はすべて出どころが付いた

| `round_next` の入力 | 出どころ |
|---|---|
| `hseg : ScanSeg` | `scanSeg_of_steps`（新規） |
| `w0` / `hp0` / `hs0` / `hz0`（ラウンド起点） | ラウンド不変量 |
| `hm1` / `hr1` / `hc1`（終端の制御） | `scan_shift` tick の構成子 |
| `w` / `hs1`（終端の watch） | 不変量 |
| `hav : canRight s1.right` | tick の `replaying ∨ available` |
| `vs` / `vq` / `hcmp` / `hmis` / `hq` | `compare_mismatched_parts`（新規） |
| `hend : singlePositive cycle = true` | `RoundScan.terminal_iff` |
| `hpred` | `shiftGuardVM` の最終連言 |
| `hlen : Canonical s1.length` | `CPack.canon` |
| `hg` / `s2` / `hb` / `hs2` | `scan_shift` tick の `hg` / `hBegin` |
| `hi2 : CopyIdle s2` | `AuxPack.copyP` |
| `hchain : ChainShiftRun` | `shiftRun_exists_round` ＋ `shift_run_chain`（ラウンド不変量だけから出る） |
| `o` / `ho : refresh` | `CloseoutFoundRoute1.exists_refresh`（refresh は全域） |

**残るのは配線と、構成した着地と run の実際の着地の同一視。** 後者の差は shift 相
だけで（scan 側は `onlyMatchedRun_of_steps` が実際の状態で直接出す）、
`steps_shift_exit_unique` で `Fair` なしに閉じられる。


## 2026-09-19 n110: `obligation_marksEntry` を放電（公理 4 → 3）

**全体 build 成功（EXIT=0、エラー 0、`sorry` なし）。`PalPeg/Axioms.lean` のラチェット緑。
`PalInPeg.unconditional` の公理は
`[propext, Classical.choice, Quot.sound, obligation_cycleOracle,
obligation_localRealization, obligation_shiftPalAtScanStates]` の 3 義務。
無条件 PAL は未完。計画書 §10.5（前提ゼロ）は未達。**

### 何が起きたか

`hme : ∀ w, H_marksEntry' (PofC centreC placeC entry w) q first` の消費者は
`CloseoutOracleW.packRunR_MW` の **2 箇所だけ**で、どちらも `MarksInv'` を作るため
だけにあった（`CloseoutMarksPack` の冒頭が既にそう書いていた）。

ところが `CloseoutPackRun17.marksInv'_of_run'` は **`H_marksEntry'` なしで**
run の全点に `MarksInv'` を与える定理で、その 4 入力が `InvLPC` の origin では
すべて無償だった:

| 入力 | 出どころ |
|---|---|
| `first ≠ 4` | 側条件。`first = 0` なので `by decide` |
| `hfl`（scan 状態で `0 ≤ value length`） | `GalilInvPlus2.hfloor_of_invLP2`。`InvLPC.1` がそのまま `InvLP2` |
| `hwin`（copy 状態で `WindowInOrigin`） | `CloseoutPackRun25.windowInOrigin_alongRun`。origin は scan なので origin 側の前提が空虚 |
| `CPack q c r` | `GalilCentreLive.cpack_of_entry` ＋ `CloseoutMarksFree.entryCounters_of_invLPC` |

`windowInOrigin_alongRun` が `Fair` なしで通るようになったのは n107 のモデル修正
`M-fallbackPlace`（`beginFallbackVM'` が fallback 先の窓長を `position right` で抑える）
のおかげ。つまり **n107 のモデル忠実性の修正がそのまま義務 1 個を消した。**

### 追加/変更したもの

* `CloseoutMarksPack.packRunR_MW_marksFree`（新規、標準 3 公理）—
  `packRunR_MWP` と本体は同じで、`hpk`（反証済みの `ChainPack`）の代わりに
  `marksInv'_of_run'` を使う。前提は `h4 : first ≠ 4` と `hSP` だけ。
* `CloseoutFinalBranch.given_scanLandingObligations` — `hme` パラメータを削除し
  `h4 : first ≠ 4` に置換（`packRunR_MW` → `packRunR_MW_marksFree`）。
  兄弟の `given_landingObligationsAlongRun` /
  `given_landingObligationsSansRadiusLedger` は歴史的経路なので触っていない。
* `PalPeg/PalInPegUnconditional.lean` — `axiom obligation_marksEntry` を削除、
  呼び出しを `(by decide)` に。
* `PalPeg/Axioms.lean` — ラチェットを 3 義務に更新。

### 教訓

**`hme` は最初から独立した義務ではなかった。** `CloseoutMarksPack` の冒頭は
「`hme` は `hpack` の中にある」と書いていたが、正しくは **`hme` は run の中にある**。
`hpack`（反証済み）を経由する必要すらなかった。
`marksInv'_of_run'` は `hme` を落とすために作られた定理として既に存在していたのに、
「`hme` の producer は `hpack` だけ」という**過去の自分の記述**を一次情報として
扱っていたせいで 1 日以上見落としていた。

### 残り 3 義務（難易度は宣言しない）

| 公理 | 内容 | 既知の経路 |
|---|---|---|
| `obligation_shiftPalAtScanStates` | scan 状態で `ShiftPal` | `CloseoutBundleRun.shiftPal_of_run_aux`。残差は run 形の `ChainPositionInvariantWithShiftPhase` ＋ `H_readsShift` ＋ `H_freshShift` ＋ `periodOnly = false` 分岐（`H_fresh`）。`hcan` は `BranchSupply.canRightAtScanOrShift_alongTrace` で**放電済み** |
| `obligation_cycleOracle` | `CycleOracleMC3` | `CloseoutOracleBridge.hor_of_H_oracle` ＋ `CloseoutOracle8.h_oracle_of_leaves7`（11 葉、CLAUDE.md §3） |
| `obligation_localRealization` | `H_realizeLIMW'` | producer なし（5 機械の鎖の 2→3 段） |


## 2026-09-19 n109: `SpanRep` の正しい guard は `scan ∨ shift`（一次情報で確定）

**全体 build 成功（EXIT=0）。既存の旗艦定理は標準公理のみ。
`PalInPeg.unconditional` は残り 4 個の原子的義務を axiom として持つ。
無条件 PAL は未完。計画書 §10.5（前提ゼロ）は未達。**（このエントリは調査結果のみ。
`sorry` を含む下書きは挿入していない。）

### 一次情報で確認した `length` / `radius` の遷移

    afterCompare_radius : (afterCompare s vs vq).radius = inc s.radius     （TopInvStep:20）
    afterCompare_length : (afterCompare s vs vq).length = inc (inc s.length)（TopInvStep:21）
    afterMismatch_radius : (afterMismatch s vs vq).radius = inc s.radius    （TopRoundS:93）
    afterMismatch_length : (afterMismatch s vs vq).length = s.length        （TopRoundS:94）
    beginShiftVM : length := inc (inc s.length)、radius 不変               （TopShiftCycle:24）
    beginFallbackAt : length / radius ともに不変                            （SharedFunctional:76）
    rewindFrame.choose : length := ofNat 1、radius := reset                （TopRewind:56）
    replayStartVM : length := ofNat 1、radius := reset                      （TopReplay:29）

したがって `SpanRep s := value length = 2 * value radius + 1` は:

| 相 | 状態 |
|---|---|
| boot（`init`） | **偽**（両方 reset なので `0 = 1`） |
| scan（一致比較） | 保存（`afterCompare` は length +2 / radius +1） |
| scan → shift | **不一致で壊れ、`beginShift` の length +2 で回復**（`spanRep_shift` の入口形が `⟨…, inc radius, inc (inc length)⟩` なのはこれ） |
| shift | 保存（`shiftTick` は length −2 / radius −1、`spanRepS_shiftTick`） |
| scan → copy（fallback） | **壊れたまま**（`beginFallbackAt` は counters を触らない） |
| copy / home / fpp / markEnd / choose | 壊れたまま（counters 不変） |
| choose → rewind | `length := 1`、`radius := 0` で回復 |
| rewind 奇数側 | 壊れる（`rewindOne` は length のみ inc） |
| replayStart → scan | **前提なしで再確立**（`length := 1`、`radius := 0`） |

**よって正しい guard は `c.mode = Mode.scan ∨ c.mode = Mode.shift`。**
`RadiusExactOffRewindPhase` のような「除外リスト」ではなく「許可リスト」になる。
`EntryCounters` が要るのは scan 状態だけなので、これで十分。

    def SpanRepOnScanAndShift (c : Control) (s : GalilVM) : Prop :=
      c.mode = Mode.scan ∨ c.mode = Mode.shift → PalPeg.GalilSpanCounter.SpanRep s

guard が scan/shift だけなので、24 ケースのうち実際に仕事があるのは 7 つ:

    init          spanRep_of_init（側入力: boot の radius = reset ∧ length = reset）
    scan_wait     spanRep_background
    scan_count    spanRep_background
    scan_match    spanRep_afterCompare ＋ replayDec ＋ afterBirth_length/radius
    scan_shift    afterMismatch ＋ beginShiftVM の合成（下記）
    shift_one     spanRepS_shiftTick（`shiftLens_set_radius` / `_length` で持ち上げ）
    shift_done    counters 不変
    replayStart   spanRep_of_fallback（**前提なし**）

残り 16 ケースは行き先の mode が scan / shift でないので guard で空虚、
または `restart`（counters 不変）。

### 実装上の 1 つの引っかかり（次のターンの最初の作業）

`scan_match` で `a = true`（一致分岐）を取り出す必要がある。
`compareFound` の第 6 成分は `(a = true ↔ (galilFrame …).matched (scanLens.set s vs))` で、
tick が持っているのは `hmt : (galilFrameS …).matched s'`。
`s'` の scan 射影が `vs` 由来なので一致するはずだが、**橋渡しの補題を先に探す**
（`radiusExact_after_compare` は radius が両分岐で inc なので `a` を場合分けせずに
済んでいた。`SpanRep` は length が分岐で違うので `a` が必要）。

`scan_shift` 側は `a = false`（不一致）で、`afterMismatch` の length 不変 ＋
`beginShiftVM` の length +2 ＋ radius の inc で `SpanRep` が回復する:
`length = 2·radius + 1` → `length + 2 = 2·(radius + 1) + 1`。

## 2026-09-19 n108: `marksEntry` は `SpanRep`（mode guard 付き）1 点に帰着した

**全体 build 成功（EXIT=0）。既存の旗艦定理は標準公理のみ。
`PalInPeg.unconditional` は残り 4 個の原子的義務を axiom として持つ。
無条件 PAL は未完。計画書 §10.5（前提ゼロ）は未達。**（このエントリは調査結果のみ。）

### `marksEntry` を回避する経路（`H_marksEntry'` を使わない）

`CloseoutMarksFree.marksInv'_of_marksRun` は `H_marksEntry'` **なしで** `MarksInv'` を
run に沿って与える。入力は 4 つ:

| 入力 | 状態 |
|---|---|
| `first ≠ 4` | 側条件（`first = 0` なので `by decide`） |
| `CPack q x.ctl x.vm` | **タダ**: `cpack_of_entry q (invS_of_inv hInv) hEC`（`GalilTrailRad.live_pack_trace` の証明が `st 1` で `hInv` / `hEC` を実際に作っている） |
| `x.ctl.mode = Mode.scan` | **タダ**: `init_tick_target_is_scan`（`st 1` は scan） |
| `MarksRun … raw x` | 2 半分（下記） |

`MarksRun` の 2 半分:

| 半分 | 状態 |
|---|---|
| `WindowInOrigin`（copy 状態） | **タダ**（`CloseoutPackRun25.windowInOrigin_alongRun`、n107） |
| `EntryCounters`（scan 状態） | 分解すると 4 節（下記） |

### `EntryCounters` の 4 節 — 3 つは今日の成果でタダ

    EntryCounters raw r := ∃ Rad,
      ScanInvariant raw (position r.center) Rad r.left r.right ∧
      RadiusRep r.radius Rad ∧ SpanRep r ∧ Canonical r.length
    （`GalilGlueBLeaves:74`）

| 節 | 出どころ |
|---|---|
| `ScanInvariant …` | **タダ**: `LPackM.scanGeom` / `LPackM2.scanGeomR`（trace は各点で `IPackMW` を持つ）。`Rad` はここから取る |
| `RadiusRep r.radius Rad`（＝`Canonical radius ∧ value radius = Rad`） | **タダ**: `RadLedger.canon` ＋ `BranchSupply.radiusExactOffRewindPhase_alongTrace`（**今日証明**）＋ `ScanInvariant.rightPos`（`position right = position center + Rad`） |
| `Canonical r.length` | **タダ**: `CPack.canon` |
| `SpanRep r`（`value length = 2 * value radius + 1`） | **残り 1 点** |

### 残り 1 点: `SpanRep` の mode guard 付き tick 搬送

`GalilSpanCounter` は遷移ごとの補題を既に持っている:

    spanRep_afterCompare / spanRep_background / spanRep_shift / spanRep_rounds /
    spanRep_restart / spanRep_of_init / spanRep_of_fallback /
    spanRepS_shiftTick / spanRepS_shiftRun / spanRep_replayDec

**無いのは `Tick` の 24 構成子に対する 1 本と、run/trace 搬送。**
そして rewind 相では破れる（`length` は毎 tick +1、`radius` は 2 tick ごとに +1 なので
`length = 2·radius + 1` はペア境界でしか成り立たない）。つまり
`RadiusExactOffRewindPhase`（今日書いた）と**同じ形の mode guard** が必要:

    def SpanRepOffRewindPhase (c : Control) (s : GalilVM) : Prop :=
      c.mode ≠ Mode.choose → c.mode ≠ Mode.rewind → c.mode ≠ Mode.replayStart →
        value s.length = 2 * value s.radius + 1

出口の `replayStartVM` は `length := ofNat 1`、`radius := reset` なので
`spanRep_of_fallback` と同型で前提なしに再確立する（`radiusExact` と同じ理屈）。

**これが `marksEntry` を落とす最後の 1 本。** 今日 2 回書いた形
（`radiusExactOffRewindPhase_tick` / `headsRepresent_tick`、どちらも 24 ケース）と
同じ作業で、材料（遷移ごとの補題）は既に全部ある。

## 2026-09-19 n107: `M-fallbackPlace` を修正し `WindowInOrigin` を `Fair` なしに（`marksEntry` の実体が確定）

**全体 build 成功（EXIT=0）。既存の旗艦定理は標準公理のみ。
`PalInPeg.unconditional` は残り 4 個の原子的義務を axiom として持つ（数は不変）。
無条件 PAL は未完。計画書 §10.5（前提ゼロ）は未達。**

### `M-fallbackPlace`（修正済み・全体 build 緑）

Scala 正本の `beginFallback` は search の walker place からコピーし、その walker は
到着済みの入力しか見ていない。Lean の `beginFallbackVM'` は `p` を無制限にしていた。

    def beginFallbackVM' (s t) := ∃ p, beginFallbackVM p s t ∧
      (GalilScaffoldPlace.stream p).length ≤ position s.right

**`p = s.walker` ではなく境界にしたのが要点。** `p = s.walker` は DP の walker との
結合が必要で `FallbackRestart` 系（`chosenRadius` を `p` で書く大きい定理群）に
波及する。境界なら `position_represent`（`GalilScaffoldChainFallback:110`、
**等式で既存**）からそのまま出て、しかも `WindowInOrigin` に必要なのは境界だけ。

配線: 分解 29 箇所（自動置換）、producer 3 定理、`FallbackRestart` 系 5 箇所、
`arrive` / `trunc` の保存義務 4 箇所（`position_arrive` / `position_trunc` は `rfl`）、
`GalilSharedFunctional` / `GalilTickFair` の 4 箇所。

### `WindowInOrigin` は `Fair` なしで run 全域に出る

    windowInOrigin_of_beginFallback   着地でそのまま（境界 ＋ beginFallbackAt_walker）
    windowInOrigin_tick_free          1 tick（copy へ入るのは scan_fallback だけ）
    windowInOrigin_alongRun           run 全域

`(stream t.fpp.walker).length = (stream p).length ≤ position s.right = position t.right`。
**`WalkerInOrigin` も `Fair` も経由しない。** n104 で「`FairSteps` が穴」と書いた所は
`Fair` を定理にするのではなく**迂回できた**。

（`M-initCursor` の副産物として `walkerInOrigin_of_run` も `Steps` 形になっているが、
`WindowInOrigin` はそれさえ要らなくなった。）

### `marksEntry` の実体が確定: marks テープの幾何 1 点

`CloseoutMarksFree.marks_steps_free` は `H_marksEntry'` なしで `MarksInv'` を運ぶ。
必要なのは `first ≠ 4` と `MarksRun`（2 半分）で、

| 半分 | 状態 |
|---|---|
| `WindowInOrigin`（copy 状態） | **タダ**（`windowInOrigin_alongRun`、今回） |
| `EntryCounters`（scan 状態） | `entryCounters_of_invLPC` 経由。ただし `InvLPC` は**cycle 起点**の不変量で、run の各 scan 状態には無い |

側入力もほぼ揃っている:

    CPack q (st 1).ctl (st 1).vm  ← cpack_of_entry q (invS_of_inv hInv) hEC
                                     （`GalilTrailRad.live_pack_trace` の証明が
                                       `st 1` で `hInv` / `hEC` を実際に作っている）
    (st 1).ctl.mode = Mode.scan   ← init_tick_target_is_scan

**残るのは `H_marksEntry'` そのもの**（`CloseoutPackRun16:165`）:

    H_marksEntry' P q first := ∀ c s, c.mode = Mode.choose → c.odd = true →
      (galilFrameS P q first).markSet s → MarksEntry' first s

    MarksEntry' first s := ∃ f, 1 ≤ f ∧ f ≤ mh s ∧
      denote (marksTape s.fpp) f = first ∧ mh s + 1 ≤ position s.left + f

つまり「`choose` 相で marks ヘッドがマーク上にあるとき、FIRST マークが
`f ≤ mh s` にあって `mh s + 1 ≤ position left + f`」——**marks テープの版面の幾何**。
`CPack.choose`（`mh s ≤ 2 * position s.right`）と marks テープの内容
（`GalilFppMarkedLayout.marks`）から出るはずで、`GalilCentreLive.layout_end`
（`:123`）が同種の補題。

**注意: `∀ c s` の形（過剰量化）。** 到達しない状態まで量化しているので、
まず trace 形に切り直してから測る（`CLAUDE.md` の規律）。

## 2026-09-19 n106: モデル欠陥 `M-initCursor` を修正（`Fair` の 3 場のうち 1 つが定理に）

**全体 build 成功（EXIT=0・sorryAx 0）。既存の旗艦定理は標準公理のみ。
`PalInPeg.unconditional` は残り 4 個の原子的義務を axiom として持つ（数は不変）。
無条件 PAL は未完。計画書 §10.5（前提ゼロ）は未達。**

### `M-initCursor`（修正済み・全体 build 緑）

Scala 正本の `stepInit` / `stepReplayStart` は `walker`（search の copy cursor）も
`periodOnly` も触らない。ところが Lean の `initVM` / `replayStartVM`
（`GalilScaffoldTopReplay:20,28`）は `GalilVM` の 15 場のうち 13 場しか縛らず、
この 2 つを**自由**にしていた。その分を `Fair.keepsSearchCursor` が仮定として抱え、
`marksEntry` の残差 `WindowInOrigin` が `FairSteps` を要求する原因になっていた。

末尾に `t.periodOnly = s.periodOnly ∧ t.walker = s.walker` を追加。

**消費者は 1 箇所も壊れなかった。** Lean の anonymous constructor は右結合の `∧` の
末尾を `-` 1 個で吸収するので、`obtain ⟨-, …, hch, -⟩ : initVM entry s s'` のような
既存パターンは 13 → 15 連言でもそのまま通る。直したのは producer 9 箇所だけ
（`GalilScaffoldTopReplay` / `TopScanRun` / `GalilTickFun` / `GalilTickDet` /
`GalilTickFair` / `CloseoutFairWitness` / `LocalTick2` / `LocalReplaySwap` /
`LocalReplayParked`）。

**モデル欠陥を記録していた定理が、修正で偽になった**ので差し替えた:

    initVM_not_unique / replayStartVM_not_unique / tick_init_not_det /
    tick_replayStart_not_det   （GalilTickDet、削除）
      → initVM_keepsSearchCursor / replayStartVM_keepsSearchCursor（正しい向き）

`GalilTickFair.tick_fair_init_unique` / `tick_fair_replayStart_unique` は
`Fair.keepsSearchCursor` を**読まなくなった**（`initVM` の射影で足りる）。
`GalilTickDet` の非決定性 (e) の init / replayStart 側は閉じた。

### `Fair.fallbackPlace` は着手して巻き戻した（記録）

`beginFallbackVM' s t := ∃ p, beginFallbackVM p s t`（`TopGuards:38`）の `p` を
Scala どおり `s.walker` に固定する試み:

    def beginFallbackVM' (s t) := ∃ p, beginFallbackVM p s t ∧ p = s.walker

分解パターン 27 箇所は機械的に直る（`⟨pl, ht⟩ : beginFallbackVM'` →
`⟨pl, ht, -⟩`、23 ファイルを自動置換で処理できた）。**しかし producer 側が重い**:
`GalilScaffoldTopFallbackCycleS` の `chosenRadius` 系の大きい定理が `p` を
自由な引数として取り、結論全体を `p` で書いているので、`hp : p = … .walker` を
足すと呼び出し側まで波及する。緑を壊さないため巻き戻した。

**次の一手**: `beginFallbackVM p s t` 自体に `t.walker = p` を足す案もある
（`beginFallbackVM'` の型は変わらないので 27 箇所は無傷）。ただし
`GalilTickFair.beginFallback_walker`（`t.walker = s.walker`）が偽になるので、
`WalkerInv` の走り方を確認してから入れる。

### 残る `Fair` の 2 場

| 場 | Scala 正本 | 入れ方 |
|---|---|---|
| `fallbackPlace` | `beginFallback` は search の walker place からコピー | 上記（`beginFallbackVM` 側に寄せる） |
| `restartFirst` | `transition` の前置きで broken chain の restart が mode step より先 | `Tick` の scan 構成子に `¬ restartGuardVM s` を足す |

3 場が全部定理になれば `FairSteps` が `Steps` から出て、`WindowInOrigin` が落ちて
`marksEntry` が消える（4 → 3）。

## 2026-09-19 n105: `marksEntry` はモデルの忠実性に帰着する（`Fair` を公理に隠さない）

**全体 build 成功（EXIT=0・sorryAx 0）。既存の旗艦定理は標準公理のみ。
`PalInPeg.unconditional` は残り 4 個の原子的義務を axiom として持つ。
無条件 PAL は未完。計画書 §10.5（前提ゼロ）は未達。**（このエントリは調査結果のみ。）

### `Fair` の 3 場（`GalilTickFair:195`）

    restartFirst      : mode = scan → restartGuardVM x.vm →
                        y.ctl = {x.ctl with clock := delay} ∧ restartVM entry x.vm y.vm
    fallbackPlace     : mode = scan → y.ctl.mode = copy → y.vm.fpp.walker = y.vm.walker
    keepsSearchCursor : mode = init ∨ mode = replayStart →
                        y.vm.periodOnly = x.vm.periodOnly ∧ y.vm.walker = x.vm.walker

`WindowInOrigin`（`marksEntry` の唯一の残差）の producer
`CloseoutPackRun28.walkerInOrigin_of_run` は `FairSteps` を要求し、
`walkerInv_tick` が各 tick で `Fair` を読む。

### 2 つの道があり、片方は不正直

**(A) oracle を強めて `PreTrace` に `Fair` を持たせる。**
trace は `preTraceIMW_exists` が `H_bootIMW` ＋ `H_oracleIMW` から作る。
`H_oracleIMW` は `obligation_cycleOracle`（`CycleOracleMC3`）から来ているので、
`Fair` を要求すると**`cycleOracle` の内容が強くなる**。
公理の数は 4 → 3 になるが、それは n96 で自分がやった誤りと同型
（数だけ減らして内容を強化）。**採らない。**

**(B) モデルを Scala に忠実にして `Fair` を定理にする。**
`Fair` の 3 場はすべて「Scala がやっていることを Lean の非決定性が落としている」分:

| 場 | Scala 正本 | Lean の現状 |
|---|---|---|
| `keepsSearchCursor` | `stepInit` / `stepReplayStart` は `walker` も `periodOnly` も触らない | `initVM` / `replayStartVM` が両方**自由** |
| `fallbackPlace` | `beginFallback` は search 自身の walker place からコピー | `beginFallbackVM'` は着地場所が**自由** |
| `restartFirst` | `transition` の前置きで broken chain の restart が mode step より**先** | `Tick` に優先順位が**無い**（`restart` と `scan_wait` が競合） |

つまり `Fair` は**モデル欠陥 3 件の集合**であり、`M-periodOnly` / `M-watchBreak` と
同じ種類。CLAUDE.md §2 の当時の方針は「モデルは編集せず（使用箇所 300 超）`Fair` を
定義して一意性を証明」だったが、その `Fair` がいま `marksEntry` を塞いでいる。
**`marksEntry` を正直に落とすには (B) しかない。**

### (B) の具体形（次の一手）

1. `initVM` に `s'.walker = s.walker ∧ s'.periodOnly = s.periodOnly` を追加
   （`GalilScaffoldTopReplay:20` 付近、`replayStartVM` も同様）。
   → `Fair.keepsSearchCursor` が定理になる。
2. `beginFallbackVM'` の `∃ p` を search の walker に固定
   （`beginFallbackVM (P.place s')` 相当）。→ `Fair.fallbackPlace` が定理。
3. `Tick` の scan 構成子に `¬ restartGuardVM s` を足す。
   → `Fair.restartFirst` が定理（`GalilTickDet` の (a) も閉じる）。

影響は `initVM` / `replayStartVM` / `beginFallbackVM'` / `Tick` の使用箇所で、
`M-periodOnly`（誕生時の `periodOnly` リセット）と同規模の見込み。
`M-periodOnly` は実際に入って全体 build 緑になっているので、手順は確立している。

### (1) のコストを下げる実装上の観察（今日確認）

`initVM`（`GalilScaffoldTopReplay:20`）は 13 連言で、**`t.fpp = s.fpp` を既に持つ**
（fpp walker は保存されている）。足りないのは `periodOnly` と `walker` の 2 つ。

Lean の anonymous constructor は右結合の `∧` を途中で `-` 1 個で吸収できるので、
**新しい連言を末尾に足せば既存の分解パターンは壊れない**。実例:

    obtain ⟨-, -, -, -, -, -, -, -, -, hch, -⟩ : initVM entry s s' := hInit

は 11 項で 13 連言を分解している（11 番目の `-` が 11〜13 を吸収）。
15 連言にしても同じパターンが通る。**壊れるのは producer 側だけ**（新しい 2 つを
供給する必要がある）。だから (1) は「消費者 300 箇所」ではなく
「producer 数箇所」の作業。

`t.search = GalilScaffoldSearchFinish.begin reset s.radius` が search をリセットする
ので、`walker` が `search` の射影なら (1) の `walker` 側は既に決まっている可能性がある
（未確認。`GalilVM` の場一覧を見て `walker` が独立場かを先に確かめる）。

## 2026-09-19 n104: 公理 5 → 4（`centreMargin` 吸収）＋ 残り 4 個の難易度順と `marksEntry` の実体

**全体 build 成功（EXIT=0・sorryAx 0）。既存の旗艦定理は標準公理のみ。
`PalInPeg.unconditional` は残り 4 個の原子的義務を axiom として持つ
（`cycleOracle` / `localRealization` / `marksEntry` / `shiftPalAtScanStates`）。
無条件 PAL は未完。計画書 §10.5（前提ゼロ）は未達。**

### 公理の推移（今日）

```
11 相当 → 10 → 9 → 8 → 7 → 5 → 4
  bg / chainBackLag / shiftExitLedger / matchRest / verifierRunAlongRun / centreMargin
```

### `centreMargin` は新規証明ゼロで `marksEntry` に吸収された

`CloseoutPackRun16.MarksInv'` の第 2 成分が
`position left + r + pairOff c ≤ position center` ——`RCouple` が持っていない向き。
第 1 成分 ＋ `¬ atFirst` から `two_le_left_of_marksInv'` が `2 ≤ position left`。
`Tick.rewind_one` / `rewind_pair` は `hf : ¬ atFirst s` を**構成子として持つ**。

`¬ atFirst` guard を 3 層に入れた:

    LTickLeaves.rewindLeft / LTickLeavesN.rewindLeft   CloseoutLPack3 / PackRun11
    Extra8.rewindMargin                                CloseoutPackRun46（first を引数に）
    RewindMarginAt / ChainBackLagAndShiftExitLedgerAt.rewindMargin   BranchSupply

`LTickLeavesG` / `LTickLeavesO` 系は未 guard のまま（触る必要なし）。
`rewindMarginAt_alongTrace` は `two_le_left_of_marksInv'` 1 行になった。

**訂正**: n96 の「`rewindMargin` を `CentreMargin` 1 葉に縮めた」は数だけの削減で
内容は強化だった（guard なしでは `1 ≤ position left` しか出ないので `+1` 分強すぎ）。
**過剰量化の 11 例目・自分で撒いた 4 例目。**

### 残り 4 個の難易度順（簡単なものから）

| 順 | 公理 | 残差 | 障害 |
|---|---|---|---|
| 1 | `marksEntry` | `WindowInOrigin`（copy 状態）1 つ | **`FairSteps`**（下記） |
| 2 | `shiftPalAtScanStates` | `ShiftPal` | `ChainOk` の再設計（`WatchOk` は反証済み） |
| 3 | `cycleOracle` | `CycleOracleMC3` | found 経路の葉（§3） |
| 4 | `localRealization` | `H_realizeLIMW'` | producer なし |

### `marksEntry` の実体は `Fair` である（今日確定）

`CloseoutMarksFree.marks_steps_free` は `H_marksEntry'` なしで
`CPack` / `WPack` / `MarksInv'` を run に沿って運ぶ。必要なのは `first ≠ 4` と
`MarksRun`（2 半分）で、`marksRun_of_window` により

| 半分 | 状態 |
|---|---|
| `EntryCounters`（scan 状態） | **タダ**（`entryCounters_of_invLPC`） |
| `WindowInOrigin`（copy 状態） | producer は `CloseoutPackRun28.walkerInOrigin_of_run` |

`WalkerInOrigin s := (stream s.walker).length ≤ position s.right`（`PackRun25:53`）、
`WindowInOrigin s := (stream s.fpp.walker).length ≤ position s.right`（`PackRun17:62`）、
橋は `windowInOrigin_of_fair`（`PackRun25:57`）。

`walkerInOrigin_of_run` の入力:

    hplace : ∀ u, (stream (place u)).length ≤ position u.right   -- placeC は具体関数
    hdelay : 2 ≤ delay                                           -- 2048
    hcan   : … replaying = true → canRight z.vm.right            -- CloseoutReplayCanRight でタダ
    hx     : WalkerInv x.ctl x.vm                                 -- boot 形（walker 空）
    hz     : FairSteps …                                          -- ★ここだけが穴

**`PreTrace.trace` は素の `Trace`（`Steps`）で `Fair` を持たない。**
`Tick` 単体は非決定的（`beginFallbackVM'` の着地場所、`initVM`/`replayStartVM` の
`periodOnly`/`walker` が自由）なので、`Fair` なしでは walker が任意に置かれうる。
だから `WindowInOrigin` は原理的に `Fair` を要する。

**次の一手**: `PreTrace` / `PreTraceIMW` に `Fair` を持たせる（oracle 側の証人が
`Fair` を満たすことを確認する）。`GalilTickFair` は `Tick ∧ Fair` の一意性まで
証明済みなので、材料は揃っている。これは `marksEntry` を落とす唯一の道。

## 2026-09-19 n103: `headsRepresent` を `MarksInv'` 基底へ（内容の訂正）＋ `CentreMargin` に偽の疑い

**全体 build 成功（EXIT=0）。既存の旗艦定理は標準公理のみ。
`PalInPeg.unconditional` は残り 5 個の原子的義務を axiom として持つ（数は不変）。
無条件 PAL は未完。計画書 §10.5（前提ゼロ）は未達。**

### 内容の訂正（数は減らない）

n96 で「`rewindMargin` を `CentreMargin` 1 葉に縮めた」と書いたのは**強化**だった。
`RCouple` は `position center ≤ position left + r + pairOff` の向きしか持たないので、
`2 ≤ position left` から `CentreMargin`（`r + pairOff + 2 ≤ position center`）は出ない。
**数だけ見て「縮めた」と書いてはいけない。**

`headsRepresent_tick` の側入力を `CentreMargin` 由来の `hCentreTwoLe` から
`MarksInv'` ＋ `RCouple` に差し替えた（どちらも真に弱い）:

* `Tick.rewind_pair` は `hf : ¬ atFirst s` を**構成子として持つ**（`GalilScaffoldTop:164`）
* `CloseoutPackRun16.two_le_left_of_marksInv'` がその `hf` から `2 ≤ position left`
* `RCouple`（`rcouple_alongTrace`、葉なし）で `2 ≤ position center`

追加: `BranchSupply.marksInv_alongTrace`（`H_marksEntry'` から trace 全域へ、
`marksInv'_of_run` ＋ `steps_of_trace`、boot は `init` 相）。

これで **`CentreMargin` の消費者は `Extra'.rewindMargin` 系 1 本だけ**になった。

### 決定的な発見: `MarksInv'` は `RCouple` の**逆向き**を持っている

`CloseoutPackRun16:191` の `MarksInv'` は 2 成分:

    MarksInv' first c s := c.mode = Mode.rewind →
      (∃ f, 1 ≤ f ∧ f ≤ mh s ∧ denote (marksTape s.fpp) f = first ∧
        mh s + 1 ≤ position s.left + f) ∧
      (∃ r, s.radius = ofNat r ∧ position s.left + r + pairOff c ≤ position s.center)

**第 2 成分が `position left + r + pairOff ≤ position center`** ——`RCouple` が持って
いない向きそのもの。だから `2 ≤ position left`（第 1 成分 ＋ `¬atFirst`）と
合わせると

    r + pairOff + 2 ≤ position left + r + pairOff ≤ position center

で **`CentreMargin` が丸ごと出る**。つまり

* **`¬atFirst` で guard した `CentreMargin` は `MarksInv'` から無償**
  （＝既存の公理 `obligation_marksEntry` に完全に吸収される）
* guard なしでは第 1 成分から `1 ≤ position left` しか出ない
  （`one_le_left_of_marksInv'`）ので `r + pairOff + 1 ≤ position center` まで。
  **現行の（guard なしの）`CentreMargin` は `+1` 分だけ強すぎる**

### `obligation_centreMargin_alongTrace` に偽の疑い（未検査・要確認）

`rewindMarginAt_alongTrace` は `CentreMargin` から**guard なしの**
`RewindMarginAt c s := c.mode = Mode.rewind → 2 ≤ position s.left` を出す。
ところが `CloseoutPackRun16` は 2 本を区別している:

    one_le_left_of_marksInv' : MarksInv' → mode = rewind → 1 ≤ position left
    two_le_left_of_marksInv' : MarksInv' → mode = rewind →
                               (marksTape s.fpp).focus ≠ first → 2 ≤ position left

**`2` は `¬atFirst` の下でしか主張されていない。** `atFirst`（＝ rewind の歩きが
FIRST に到達した最後の状態、次の tick は `rewind_done`）では `position left = 1`
でありうる。もしそれが到達可能なら `RewindMarginAt` は偽で、したがって
`CentreMargin`（それより強い）も偽。

**これは `canRNext` と同型（「着地/端の状態まで量化した」）。** 確認手順:
`rewind_done` の直前状態で `position left = 1` を作れるかを `MarksInv'` の定義
（`CloseoutPackRun16:191`）から検査する。作れれば機械検査済みの反証を書き、
`RewindMarginAt` を `¬atFirst` で再 guard する。

### 再 guard の影響範囲（実測）

    rewindMargin : … → 2 ≤ position left        8 箇所
      CloseoutLPack4:207 / PackRun11:368 / PackRun43:82 / PackRun3:117 /
      PackRun45:85 / PackRun46:68 / BranchSupply:2200,2519
    rewindLeft : … → 0 < position (left s.left)  2 箇所（CloseoutLPack3:279 / PackRun11:107）
    producer `rewindLeft := fun hm => left_pos_of_two (… .rewindMargin hm)`  4 箇所
      CloseoutLPack4:259 / PackRun11:460 / PackRun43:175 / PackRun8:439

消費点は `lpackM3_tick` の `rewind_one` / `rewind_pair` ケースで、そこには
tick 自身の `hf : ¬atFirst` が来ている。よって再 guard は機械的だが 14 箇所以上。

## 2026-09-19 n102: `centreMargin` の放電経路が確定（部品は全部既にある）

**全体 build 成功（EXIT=0・sorryAx 0）。既存の旗艦定理は標準公理のみ。
`PalInPeg.unconditional` は残り 5 個の原子的義務を axiom として持つ。
無条件 PAL は未完。計画書 §10.5（前提ゼロ）は未達。**（このエントリは調査結果のみ。）

### 一次情報で確定したこと

1. **`rewindOne` / `rewindPair` はどちらも `x.marks.left ≠ []` を構成子として持つ**
   （`GalilScaffoldTopRewind:59,61`）。「rewind の歩きが原点前で止まる」側条件は
   **tick が既に持っている**（「側条件は構成子が持っている」4 例目）。
2. **`Tick.rewind_one` / `rewind_pair` は `hf : ¬ F.atFirst s` を持つ**
   （`GalilScaffoldTop:162,164`）。`galilFrameS` の `atFirst` は
   `(marksTape s.fpp).focus = first`（`rewindFrame.atFirst`）。
3. **`CloseoutPackRun16.two_le_left_of_marksInv'` が既に存在する**:

       MarksInv' first c s → c.mode = Mode.rewind →
         (marksTape s.fpp).focus ≠ first → 2 ≤ position s.left

   つまり **(2) の `hf` と合わせて `2 ≤ position left` がそのまま出る。**
4. `RCouple`（`rcouple_alongTrace` で**葉なし**）が `position left ≤ position center`
   を持つので、`2 ≤ position center` も同時に出る。
5. `MarksInv'` は trace の各点で `CloseoutPackRun16.marksInv'_of_run`
   ＋ `steps_of_trace` から出る（boot は `init` 相なので `h1 : m ≠ rewind` が満たされる）。
   入力は `H_marksEntry'`＝**既存の公理 `obligation_marksEntry`**。

### 帰結: `CentreMargin` は消せる（`marksEntry` に吸収）

`CentreMargin`（`r + pairOff c + 2 ≤ position center`）の消費者は 2 つだけ:

| 消費者 | 本当に要るもの |
|---|---|
| `rewindMargin_of_centreMargin` → `LTickLeavesN.rewindLeft` | `2 ≤ position left` |
| `headsRepresent_tick` の `hCentreTwoLe`（`rewind_pair` ケースのみ） | `2 ≤ position center` |

**`CentreMargin` は両方より真に強い**（`RCouple` は `position center ≤ position left +
r + pairOff` の向きしか持たないので、`2 ≤ position left` から `CentreMargin` は出ない）。
n96 の「`rewindMargin` を `CentreMargin` 1 葉に縮めた」は**数は減ったが内容は強くなっていた**。

必要な改修は 2 点で、どちらも `¬atFirst` guard を入れるだけ:

* `headsRepresent_tick` の側入力を `hCentreTwoLe` から
  `MarksInv' first x.ctl x.vm` ＋ `RCouple x.ctl x.vm` に差し替える
  （`rewind_pair` ケースには `hf : ¬atFirst` が来ている）
* `RewindMarginAt` を `c.mode = Mode.rewind → ¬ atFirst s → 2 ≤ position s.left` に
  再 guard する（消費者は `rewind_one` / `rewind_pair` の tick なので `hf` がある）

これで `obligation_centreMargin_alongTrace` は落ちて **5 → 4**。

### `marksEntry` 自身の残差（`CloseoutMarksFree`）

`marks_steps_free` は `H_marksEntry'` なしで `CPack` / `WPack` / `MarksInv'` を run に
沿って運ぶ。必要なのは `first ≠ 4` と `MarksRun`（2 半分）:

| 半分 | 状態 |
|---|---|
| `EntryCounters`（scan 状態） | **タダ**（`entryCounters_of_invLPC`、`InvLP := InvL ∧ EntryCounters`） |
| `WindowInOrigin`（copy 状態） | **真の入力**（これが `marksEntry` の実体） |

つまり残り 5 個のうち `centreMargin` と `marksEntry` は**1 つの残差
`WindowInOrigin`（copy 状態、run 形）に統合される**見込み。

## 2026-09-19 n101: 公理 7 → 5（`matchRest` ＋ `verifierRunAlongRun`）

**全体 build 成功（EXIT=0・sorryAx 0）。既存の旗艦定理は標準公理のみ。
`PalInPeg.unconditional` は残り 5 個の原子的義務を axiom として持つ
（`centreMargin` / `cycleOracle` / `localRealization` / `marksEntry` /
`shiftPalAtScanStates`）。無条件 PAL は未完。計画書 §10.5（前提ゼロ）は未達。**

### 公理の推移

```
11 相当 → 10 → 9 → 8 → 7 → 5
  bg 場              放電（CentreLedger ← LPackM3）
  chainBackLag       放電（不変量を全構成子に広げた）
  rewindMargin       → centreMargin に縮小（RCouple はタダ）
  matchLanding + shiftEntryLanding → matchRest 1 つに合流
  shiftExitLedger    放電（HeadsRepresent ＋ ShiftGeom ＋ RadiusExact）
  matchRest          放電（4 場とも）
  verifierRunAlongRun 放電（run 形 → trace 形に切り直し）
```

### `MatchRest` の 4 場の決着

| 場 | 決着 |
|---|---|
| `canRNext` | **偽**（`MatchRestRefute.matchRest_alongTrace_false`）。着地側の 1 歩分に切り直し |
| `repV` | `VerRun` の第 1 成分そのもの → `ChainVerifierRepresents` |
| `replayPay` | `ChainPositionInvariantWithShiftPhase.payload` の guard を `ScanNR` → `mode = scan` に広げたら**義務ごと消滅** |
| `repVmid` | `ChainVerifierRepresents` を 1 手進めるだけ |

`replayPay` が存在した理由: `payload` の guard が `ScanNR`（`mode = scan ∧
replaying = false`）で replay 中の台帳が抜けていた。guard を広げたら源で両分岐が出た。
**「狭く切った guard」の 8 例目。** 副産物として `bg` / `matchLand` の `ScanNR` 仮説と
そこでしか使われていなかった `(o b : Bool)` が全部落ちた。

### `VerRun` は run 形だったから出なかった

`CloseoutVerSide.VerRun` は `Steps` 到達可能な**任意の**状態に量化していた
（`Tick` は決定的でないので trace からは出ない）。trace の点で述べた
`BranchSupply.ChainVerifierSupplyAlongTrace` に切り直すと

    VerRep  ← ChainVerifierRepresents の .watch 場
    LagCan  ← ChainLagCanonical の .watch 場

でどちらも搬送済み。**過剰量化の 10 例目。run 形と trace 形は別物。**

### 鍵: `right` は入力端で no-op

    canRight p = (gap = false ∨ head.right ≠ [] ∨ head.incoming ≠ [])
    moveRight h = match h.right with | a :: rs => … | [] => match h.incoming with | [] => h | …

`¬canRight p` なら `gap = true` かつ右も incoming も空で `moveRight h = h`。
`representsAfterRight_free` でこれを示したので **`ChainVerifierRepresents` は
`canRight` の供給を一切要らない**。`verRep_next` が `canRight` を取っていたのは
無条件版を書いていなかったからで、障害ではなかった。

### 残り 5 個の分析

| 公理 | 内容 | 次の一手 |
|---|---|---|
| `centreMargin` | rewind 相で `r + pairOff c + 2 ≤ position center` | **marks テープの下限が必要**（下記） |
| `marksEntry` | `H_marksEntry'`（rewind 入口の marks 不変量） | `centreMargin` と同じ壁 |
| `shiftPalAtScanStates` | scan 状態の `ShiftPal` | `ChainOk` の再設計（`WatchOk` 反証済み、n74 系） |
| `cycleOracle` | `CycleOracleMC3` | §3 の葉（found 経路が最大） |
| `localRealization` | `H_realizeLIMW'` | producer なし。難易度は宣言しない |

**`centreMargin` の位置づけ（今日確定）**: `GalilCentreLive.CPack` は既に marks テープの
束縛を**場として運んでいる**:

    CPack.rewind : c.mode = Mode.rewind → mh s + (if c.pair then 1 else 0) ≤ 2 * position s.center
    （`mh s = GalilScaffoldTape.head (marksTape s.fpp)`）

これは `position center` の**下限**を与えるので `CentreLive`（`0 < position center`）は
そこから出る（`centreLive_of_pack`）。ところが `CentreMargin` に必要なのは
`position right ≥ 2·r + pairOff + 2`、すなわち **`mh` の下限**（rewind の歩数 `r` が
marks テープの FIRST までに収まること）で、`CPack` の場はすべて `mh` の**上限**。
よって新しい場（rewind 中に `2·value radius + pairOff + 4 ≤ mh s` に相当するもの）が要る。
`radiusExact` が rewind 中も保存されること（`position center + radius = position right`、
`0 < position center` が要る＝`CentreLive`）は既に材料がある。

## 2026-09-19 n100: `MatchRest` は主張が強すぎた — `canRNext` を反証し `repV` を放電（4 場 → 2 場）

**全体 build 成功（EXIT=0・sorryAx 0）。既存の旗艦定理は標準公理のみ。
`PalInPeg.unconditional` は残り 7 個の原子的義務を axiom として持つ。
無条件 PAL は未完。計画書 §10.5（前提ゼロ）は未達。**

### 公理 8 → 7（`shiftExitLedger` 放電）

`obligation_shiftExitLedger_alongTrace` を `BranchSupply.shiftExitLedgerAt_alongTrace`
で放電。新規入力は既存の公理 `obligation_centreMargin_alongTrace` だけ。

    canRight center   HeadsRepresent ＋ 中心の位置上界（RadLedger.le ＋ .nonneg）
    Sane center       LPackM2.shiftGeom が直接持っている
    radiusExact       RadiusExactOffRewindPhase（shift 相は rewind guard の外）

原因は `LPackM2.centreRep` の guard が `rewind ∨ replayStart` だけだったこと
（`LagCan` と同じ「狭く切った」パターン、6 例目）。

側条件が 2 つ「タダ」になった:
1. `radiusExact_after_shiftOne` の `1 ≤ value radius` は算術に使われていなかった
2. `0 < head.left.length` は `represented_position`（`Represents` ＋ `focus ≠ none`）から直接

### `MatchRest.canRNext` は偽だった（機械検査済み・REFUTED 条件付き）

`PalPeg.MatchRestRefute.matchRest_alongTrace_false`
（`PreTrace` ＋ `0 < |w|` ＋ trace 全域の `MatchRest` → `False`。標準公理のみ）。

    canRNext : canRight (right s.right)     -- mode guard すら無し

`ReportPointAt.atPrefix` は報告点で `position right = 2|w| − 1` を**等式**で与える。
`not_canRight_iff`（`¬canRight p ↔ position p = 2|w|`）より 2 歩分の余裕は原理的に無い。

コウタの診断そのまま:「反証ができたとしたら、定理の内容がまずかったんやろ」
「定理の主張が強すぎたが一番ありそう」。

| | |
|---|---|
| 書いた義務 | 源状態で **2 歩分**（trace 全域・guard なし） |
| 実機の要求 | compare 前に `canRight right`（**1 歩分**、Scala `available`） |
| 消費者の要求 | **着地状態**の `canRight t.right`（1 歩分） |

正しい切り方: `matchLand` / `entryLand` の**仮説**に `canRight t.right` を移し、
消費者 `chainPosInv2_tick_of_landingObligationsAt` が
`y.ctl.mode = scan ∨ shift → canRight y.vm.right` を取る。本線はこれを
`BranchSupply.canRightAtScanOrShift_alongTrace` で埋める（新規入力ゼロ）。
旧 global/`Steps` 経路には過剰量化の供給を明示仮定として足し、
名前に過剰量化を出した（`hCanRightAtAnyScanOrShiftState`）。

### `MatchRest.repV` も放電（新規入力ゼロ）

`CloseoutVerSide.VerRun` の第 1 成分が `VerRep w z.vm.chain` そのもの。
`steps_of_trace` で trace の scan 状態に落ちる。
**`MatchRest` は 4 場 → 2 場**（`repVmid` / `replayPay`）。

### 次の 2 手（`obligation_matchRest_alongTrace` を消すため）

1. **`repVmid`**（1 `ChainStep` 先の verifier 表現）。`ChainStep` は**7 構成子**
   （`idle` / `brokenIdle` / `copyBit` / `copyEnd` / `backStep` / `backDone` / `watchStep`）。
   `.watch` を作るのは `backDone`（verifier = `.back` の `ver`、不変）と
   `watchStep`（`Internal`: `idle` は不変、`take` は `right`）。
   よって **`ChainPositionLedger` と同じ 3 相を覆う `VerRep` 全相版**を作り、
   誕生（`chainStart` の verifier = `s.center`）を `HeadsRepresent.centre`（証明済み）
   から出せば、`repV` / `repVmid` だけでなく
   **`obligation_verifierRunAlongRun` 自体も落ちる見込み**（7 → 5）。
   移動補題は既にある: `CloseoutVerRep.verRep_next` / `verRep_of_chainPos`。
2. **`replayPay`**（replaying 時の payload）。3 節のうち `canR` は
   `canRightAtScanOrShift_alongTrace`、`radLe` は `radiusLe_of_radLedger` で**タダ**。
   残るのは `ChainPositionLedger s.chain (position s.right)` で、これは
   `ChainPositionInvariantWithShiftPhase.payload` の guard が `ScanNR`
   （＝ `replaying = false`）に切られているために抜けている。
   **guard から `replaying = false` を外す**のが筋（また「狭く切った guard」）。

## 2026-09-19 n99: 公理 9 → 8、そして中心ヘッドの遷移表（`CentreRep` 広げ用）

**全体 build 成功（EXIT=0・エラー 0・sorryAx 0）。既存の旗艦定理は標準公理のみ。
`PalInPeg.unconditional` は残り 8 個の原子的義務を axiom として持つ。
無条件 PAL は未完。計画書 §10.5（前提ゼロ）は未達。**

### 9 → 8: インターフェースを広げただけ（コピー 0 行）

`CloseoutPackRun48` の `h_matchP2_of_target` / `h_shiftEntry2_of_target` は
`hres`（global な `H_matchRes2` / `H_shiftRes2`）を**源状態 `(c, s)` でだけ**使う。
署名を `MatchRes2 w c s` に変えて本体は `intro` と `have R` の 2 行だけ直した
（70 行の本体はそのまま）。global 版は 5 行のラッパー。

両方の入力が同じ `MatchRes2` と確定したので、`obligation_matchLanding_alongTrace` と
`obligation_shiftEntryLanding_alongTrace` を `obligation_matchRest_alongTrace` 1 つに
統合した（`BranchSupply.matchRes2_alongTrace` /
`scanLandingObligations_alongTrace_of_matchRest`）。

### 公理の推移

```
11 相当（束を分解した換算） → 10 → 9 → 8
  bg 場              放電（CentreLedger ← LPackM3）
  chainBackLag       放電（不変量を全構成子に広げた）
  rewindMargin       → centreMargin に縮小（RCouple はタダ）
  matchLanding + shiftEntryLanding → matchRest 1 つに合流
```

### 次: `CentreRep` を広げて `shiftExitLedger` を落とす

`shiftExitLedger` の `CentreLedger` は `canRight center ∧ Sane center ∧ radiusExact`。
`Sane` は `SanePack.saneC` でタダ、`radiusExact` は tick 全 24 ケース済み（n96）。
残るのは `canRight s.center` で、それには `Represents s.center.head w` が要る。
`LPackM2.centreRep` の guard は `rewind ∨ replayStart` だけ（`Run23:105`）——
また「狭く切った」パターン。

**中心ヘッドの遷移表（一次情報で確認、これが探すのに手間な部分）**

| tick | center |
|---|---|
| `init`（`initVM`、`TopReplay:20`） | `= right s.right` |
| `shift_one`（`shiftTick`、`ChainInputSupply:1445`） | `= right s.center` |
| `choose_select`（`rewindFrame.choose`、`TopRewind:56`） | `= x.right` |
| `rewind_pair`（`rewindFrame.rewindPair`、`TopRewind:62`） | `= left x.center` |
| `replayStart`（`replayStartVM`） | `= s.center`（不変） |
| `markBack` / `markForward` / `rewindOne` / `fppReset` | **不変**（`fpp` だけ） |
| fpp 相 8 遷移（`fppLens`） | **不変** |
| `backgroundS` / `compare`（`afterCompare_center`）/ `beginShift` / `beginFallback` / `restart` / `shift_done` | **不変** |

必要な移動補題は既にある: `right_word` / `right_present`（`canRight` を要する）、
`left_word`（`focus ≠ none` だけ）。

側入力もタダ: `position center ≤ position right`（`RadLedger.le` ＋ `.nonneg`）
＋ `position right ≤ 2|w| − 1`（`rightHeadPos_le_alongTrace`）
→ `canRight_of_position_bound`。

**注意 2 点**
1. `initialHead raw = ⟨⟨none, [], [], raw⟩, true⟩` で focus が `none` なので
   **boot では `CentreRep` は偽**（`AuxPack` と同じ）。`1 ≤ i` から始める。
2. `choose_select` は `center := x.right` なので**右ヘッドの表現も同時に要る**。
   `LPackM2.rrep` の guard は `OffScan c.mode`、scan では `scanGeom` が与える。
   中心と右の 2 つを同時に運ぶ帰納になる。

### 要確認（切り方の疑い）

`MatchRest.canRNext : canRight (right s.right)` は無条件だが、Scala 正本
`ScaffoldGalil.scala:255` の `available = replaying || right.canRight` が比較自体を
守っているので、入力が尽きた時点では比較が起きない。**最終位置で `canRNext` が
本当に要るのかを確かめる**（要らないなら `m < w.length` で守るべき）。

また `MatchRest.repV` は `VerRun` の第 1 成分と同内容なので、
`obligation_verifierRunAlongRun` から供給できる（`MatchRest` が 4 場 → 3 場に縮む）。

## 2026-09-19 n98: `matchLanding` と `shiftEntryLanding` は `MatchRest` 1 つに合流する

**全体 build 成功（EXIT=0・エラー 0・sorryAx 0）。既存の旗艦定理は標準公理のみ。
`PalInPeg.unconditional` は残り 9 個の原子的義務を axiom として持つ。
無条件 PAL は未完。計画書 §10.5（前提ゼロ）は未達。**

### 合流の発見

`CloseoutPackRun48` を読んだら:

```
H_shiftRes2 w := ∀ c s s' t, mode = scan → ChainPositionInvariantWithShiftPhase w c s →
    compare s s' → ¬ matched s' → shiftGuardVM s' → beginShiftVM' s' t → MatchRes2 w c s
h_shiftEntry2_of_target (hres : H_shiftRes2 …) : H_ShiftEntryChainLedger …   (:374)
h_matchP2_of_target     (hres : H_matchRes2 …) : H_MatchLandingChainLedger … (:243)
```

**両方の入力が同じ `MatchRes2 w c s`。** そして
`CloseoutPackRun49.matchRes2_of_lpackM3`（:448）が
`LPackM3`（§5e で運べる）＋ `LTickLeavesN`（タダ）＋ `LTickLeaves3`（`shiftExitLedger`
以外タダ）＋ **`MatchRest`** から `MatchRes2` を出す。

つまり `obligation_matchLanding_alongTrace` と
`obligation_shiftEntryLanding_alongTrace` の **2 公理が `MatchRest` 1 つに合流する**
（9 → 8）。

### `MatchRest` の 4 場と現状

| 場 | 内容 | 状態 |
|---|---|---|
| `repV` | chain の verifier が入力を表現 | **`VerRun`（axiom で保持）** |
| `repVmid` | verifier を 1 `ChainStep` 進めた先でも表現 | `right_word` / `right_present` で出るはず |
| `replayPay` | `replaying = true` のときの source の payload | `ChainPositionInvariantWithShiftPhase.payload` は `ScanNR`（＝非 replaying）で守られているので別途 |
| `canRNext` | `canRight (right s.right)` | **最終位置で偽の疑い**（下記） |

### 要確認 — `canRNext` の切り方

`canRight_next_of_bound` は `m < w.length`（**厳密**）と `position p ≤ 2m − 1` を要する。
いま持っている予算は `position right ≤ 2|w| − 1`（`rightHeadPos_le_alongTrace`）なので
`position (right right) ≤ 2|w|` となり、**最終位置（`m = |w|`）では `canRight` が偽**。

`MatchRest.canRNext` は無条件なので、**最終位置で本当に要るのかを確かめる**。
要らないなら `m < w.length` で守るべき＝切り方の間違い。
（`Run48:439` は shift 入口の `chainPos_immediate` に `R.canRNext` を渡している。
shift 入口は不一致 ＋ shift guard で起きるので、最終位置で起きうるかを Scala 正本
`ScaffoldGalil.canShift` で確認すること。）

### 次の一手（順番）

1. `h_matchP2_of_target` / `h_shiftEntry2_of_target` を**状態局所化**する
   （どちらも `hres` を `(c, s)` でだけ使う。`bg_at_of_supply` と同じ形）。
2. `MatchRest` を trace 形の 1 公理にまとめ、`matchLanding` / `shiftEntryLanding` の
   2 公理を消す（**9 → 8**）。
3. `canRNext` の切り方を Scala 正本で確認し、必要なら `m < w.length` で守る。
4. `shiftExitLedger` は `CentreRep` を shift 相へ運ぶ仕事。
   `CloseoutPackRun21` 自身が「`FrontPack.rewind` の `Sane s.center` を
   `CentreRep w s` に強化すべき」と書いている（`Run21:52` 付近）。これも「狭く切った」パターン。

### 今日のパターン集（全部「難解」ではなかった）

| 症状 | 正体 |
|---|---|
| producer が無い | 不変量を**狭く切っていた**（`LagCan` は `.watch` 相だけ） |
| 同じ導出が各所にある | **分類器に対する補題が無い**（`chainAt` を手開きしていた） |
| 「幾何が要る」と感じる | **リストの長さの算術**だった（`position p = 2·|left| ± 1`） |
| 前提が 1 単位足りない | **義務の切り方**が間違っている（guard が抜けている） |
| 束ねた前提数が少ない | 偽の前提を隠している（`hpack` / `hav`） |

## 2026-09-19 n97: 公理を 1 個放電（10 → 9）＋ 「狭く切った不変量」が詰まりの正体

**全体 build 成功（EXIT=0・エラー 0・sorryAx 0）。既存の旗艦定理は標準公理のみ。
`PalInPeg.unconditional` は残り 9 個の原子的義務を axiom として持つ。
無条件 PAL は未完。計画書 §10.5（前提ゼロ）は未達。**

### ラチェットで初めて公理が減った

`obligation_chainBackLag_alongTrace` を削除し `BranchSupply.chainBackLagAt_alongTrace`
で置き換えた（**新規入力ゼロ**）。`Axioms.lean` の guard も 10 → 9 に更新。

### コウタの基準で診断した結果（2 つの構造的な問題だけだった）

> 「producer がないのは何か間違っているとおもう。単なる機械のエミュレートが正しい証明やん。
> そこが難解なら何かがミスっている」「純粋に作業量が多いならわかる」
> 「構成的にできればあとは本当に作業になる」

**(a) 不変量が狭く切られていた。**
`CloseoutPackRun48.LagCan` は `.watch` 相だけ。実機の lag は `chain.start()` で
`radius` から作られ `inc`/`dec` でしか動かないので `Canonical` と非負は構成から自明。
全構成子に広げた `ChainLagCanonical` を作ったら落ちた。

**(b) 分類器に対する補題が無く各所で手開きしていた。**
`compareFound` の 8 番目の成分 `chainAt`（`GalilScaffoldTopSearch:130`）が
tick の chain 効果の分類器そのもの:

```
chainAt a found … x z :=
  (x ≠ .idle ∧ ChainTick a x z) ∨ (x = .idle ∧ found = false ∧ z = .idle) ∨
  (x = .idle ∧ found = true ∧ (if a then ChainMatched (chainStart …) z else z = chainStart …))
```

`lpackM3_tick` はこれを各ケースで手で開いていた（`Run49:162–290` の約 60 行、
`lagCan` 用と `chainPos` 用に二重化）。**分類器に対する補題 1 本
（`chainLagCanonical_chainAt`）で chain の不変量が全部乗った。**

さらに `fppLens` / `rewindLens` はどちらも `chain` を含まないので、fpp 相 8 遷移と
rewind/choose 相 6 遷移は `chainLagCanonical_of_chainEq` 1 本で潰れた。

**難解な箇所は 1 つも無かった。** 詰まっていたのは可読性と構造の問題だけ。

### 同じパターンが次にも当てはまる — `CentreRep`

`obligation_shiftExitLedger_alongTrace` の `CentreLedger` は
`canRight center ∧ Sane center ∧ radiusExact`。`Sane` は `SanePack.saneC` でタダ、
`radiusExact` は tick 全 24 ケース済み（n96）。残るのは `canRight s.center` で、
それには `CentreRep`（中心ヘッドが入力を表現）が要る。

**`LPackM2.centreRep` の guard は `rewind ∨ replayStart` だけ**（`Run23:105`）。
`LagCan` と同じ「狭く切った」パターン。`Represents` はテープ内容の性質でヘッド移動で
保たれる（`right_word` / `left_word` が既にある）ので、広げるのは機械的。

側入力は**タダ**: `position center ≤ position right`（`RadLedger.le` ＋ `.nonneg`）
＋ `position right ≤ 2|w| − 1`（`rightHeadPos_le_alongTrace`）→ `canRight` は
`canRight_of_position_bound` で出る。中心が動くのは `init`（`= right s.right`）/
`shift_one`（`= right s.center`）/ `replayStart`（`= s.center`）/ `choose_select`
（`center.copyFrom(right)`）/ rewind（`= left s.center`）の 5〜6 ケースだけ
（`fppLens` は center を含まない）。

**注意（同時帰納になる）**: `CentreRep (st (i+1))` は `right_word` に
`canRight (st i).vm.center` を要し、それは `CentreRep (st i)` から出る。
`i` に関する 1 本の帰納の中で導けばよい。

### 先に確かめること — `MatchRest.canRNext` は最終位置で偽の疑い

`obligation_matchLanding_alongTrace` の経路は
`CloseoutPackRun49.matchRes2_of_lpackM3`（`LPackM3` は運べる）＋ `MatchRest` の 4 場。
そのうち `canRNext : canRight (right s.right)` は
`canRight_next_of_bound` に `m < w.length`（**厳密**）を要する。
いま持っている予算は `position right ≤ 2|w| − 1` なので、
`position (right right) = position right + 1 ≤ 2|w|` となり**最終位置で `canRight` が偽**。
**`MatchRest` に乗る前に、最終位置で `canRNext` が本当に要るのかを確かめること。**
（要るなら `MatchRest` の切り方が間違っている＝また「狭く/広く切った」問題。）

### 残り 9 個

`matchLanding` / `shiftEntryLanding` / `shiftExitLedger` / `rewindMargin` /
`shiftPalAtScanStates` / `verifierRunAlongRun` / `marksEntry` / `cycleOracle` /
`localRealization`。

## 2026-09-19 n96: 目標を固定し公理を原子化（10 個）— `bg` 場を放電、経路を全原子に記録

**全体 build 成功（EXIT=0・エラー 0・sorryAx 0）。既存の旗艦定理は標準公理のみ。
`PalInPeg.unconditional` は残り 10 個の原子的義務を `axiom` として持つ。
無条件 PAL は未完。計画書 §10.5（前提ゼロ）は未達。**

### 進捗の計器が変わった

コウタの提案で `PalInPeg.unconditional : RecognizedByTotalPEG PAL` を**閉じた項**として
置き、足りない義務を `axiom` にした。`PalPeg/Axioms.lean` の
`#guard_msgs in #print axioms` がラチェットになっている。

**公理は 1 場ずつの原子に分解した。** 束ねると「1 個外す」が測れないため。
数は 6（束）→ 10（原子）に増えたが、束を分解した等価な数は 11 で、
`bg` 場の放電で 1 つ減っている。

### 今回放電したもの（すべて新規入力ゼロ or 既存 axiom のみ）

| 放電 | 鍵 |
|---|---|
| `bg` 場（scan landing 3 つのうち 1 つ） | `CentreLedger` ← `LPackM3`、`canRight`・半径上界はタダ |
| `LPackM3` の trace 搬送（1 手目以降） | 4 葉パックのうち 3 つがタダ |
| `AuxPack`（1 手目以降） | `Coupled`/`CopyPack` は boot からタダ（tick が側条件なし）、`FrontPack` は 1 手目以降 |
| `LTickLeaves3.initLedger` / `.replayLedger` | `initVM` の `center = right`、`LPackM2.centreRep` |
| `CentreLedger` の `canRight center` / `Sane center` | `RadLedger.le` ＋ `rightHeadPos_le_alongTrace` ＋ `SanePack.saneC` |
| `shift_done` の `canRight` と半径上界 | 終端報告点から front ポテンシャルで後ろ向き伝播 |
| `Extra7.scanAvail`（＝`hee`/`het`） | 同上（CLAUDE.md の「偽の疑い」は誤りだった） |

### 10 原子の経路は `PalPeg/PalInPegUnconditional.lean` の docstring に表で埋め込んだ

要約: producer が無いのは `chainBackLag` / `rewindMargin` / `localRealization` の 3 つ。
`shiftExitLedger` は `radiusExact` を shift 相へ運ぶ仕事（材料は §5d に揃っている）。
`matchLanding` は `MatchRest` の 4 場に割れ、`repV` は `VerRun`、残り 3 つが新残差。
`marksEntry` の `EntryCounters` は `RadiusRep`（＝`radiusExact` と同内容）を含むので
**`shiftExitLedger` と材料を共有する**。

### この近傍のタダ飯は尽きた

残り 10 原子はどれも実作業。ただし足場は揃った:
* 目標が閉じた項 1 個に固定され、ラチェットが後退を検出する
* 義務はすべて **trace 形**（global 形は原理的に落ちないと判明済み）
* 名前が中身を表すので同じ部品を二度探さない

## 2026-09-19 n95: `AuxPack` は boot で偽 — `lpackM3_steps` は boot 根では使えない（機械検査）

**全体 build 成功（EXIT=0・エラー 0・sorryAx 0）。既存の旗艦定理は標準公理のみ。
`PalInPeg.unconditional` は残り 6 義務を axiom として持つ。無条件 PAL は未完。
計画書 §10.5（前提ゼロ）は未達。**

`CentreLedger` の等式（`radiusExact`）を自前で運ぶ前に、既存の
`CloseoutPackRun49.lpackM3_tick` が同じ保存を全 tick 形について証明済みなので、
`lpackM3_steps` に乗れないかを確認した。**乗れない。**

```
-- PalPeg/AuxPackNotAtBoot.lean
theorem not_auxPack_at_boot (w : List (Fin 2)) : ¬ AuxPack (boot w).ctl (boot w).vm :=
  fun hAuxPack => hAuxPack.front.notInit rfl
```

`AuxPack` は `FrontPack` を場に持ち、`FrontPack.notInit : c.mode ≠ Mode.init`。
boot の制御は `initial 2048 = ⟨.init, …⟩` なので衝突する。
`lpackM3_steps` は `hLv : ∀ i ≤ Tc w.length, … ∧ AuxPack (st i).ctl (st i).vm ∧ …` を
取るが `st 0 = boot w` なので **`hLv 0` が充足不能**。
つまりこの定理は boot 根の trace には適用できない（偽の前提を要求しているのと同じで、
前進として数えられない）。

### `LPackM3` を運ぶための選択肢

1. 添字を `1 ≤ i` に制限する（`mode ≠ init` は 1 手目以降は定理:
   `BranchSupply.mode_ne_init_alongTrace_afterFirstStep`）
2. `AuxPack` の場を mode で守る
3. cycle 起点（`InvLPC` の scan 状態）から運ぶ ——
   `CloseoutOracleW.packRunR_MW` が実際にやっていること（`auxPack_steps` を
   `hlive_of_invLPC` ＋ `InvLPC` 起点の `AuxPack` から回す）

**1 が一番安い**（`FrontPack` は `frontPack_alongTrace` で 1 手目以降タダ。
残るは `Coupled` と `CopyPack`）。

### 教訓

`lpackM3_steps` は build が通っていて `#print axioms` も標準公理のみだが、
**前提が充足不能なので誰も使えない**。これは「build が通る」「公理が綺麗」では
検出できない種類の不良で、**前提の充足可能性を確認しないと前進と誤認する**。
`unconditional` の axiom 方式にした理由がまさにこれ:
目標から逆に辿るので、使えない補題は自然に浮かび上がる。

## 2026-09-19 n94: 目標 `PalInPeg.unconditional` を作り、残り 7 義務を `axiom` として明示

**全体 build 成功（EXIT=0・エラー 0・sorryAx 0）。既存の旗艦定理は標準公理のみ。
`PalInPeg.unconditional` は残り 7 義務を `axiom` として持つ。無条件 PAL は未完。
計画書 §10.5（前提ゼロ）は未達。**

### コウタの提案（そのまま採用）

* 「unconditional はつくっておいて、前提の and でうめりゃいいのでは。その前提を
  いったん axiom にしといて外していく」
* 「トップダウンにまずそれを書いておいてビルド通すために前提をいったん axiom に
  しておく。で、検証したい前提ごとに axiom をはずして全部外せたら証明完了」

### 実装

`PalPeg/PalInPegUnconditional.lean`:

```
theorem unconditional : RecognizedByTotalPEG PAL :=
  given_globalScanLandings 0 0 0
    (obligation_shiftPalAtScanStates 0 0 0) (obligation_marksEntry 0 0 0)
    (obligation_cycleOracle 0 0 0) (obligation_localRealization 0 0 0)
    (obligation_backgroundLandingPayload 0 0 0) (obligation_matchLandingPayload 0 0 0)
    (obligation_shiftExitPayload 0 0 0)
```

`#print axioms unconditional` がそのまま TODO リストになる:

```
[propext, Classical.choice, Quot.sound,
 obligation_backgroundLandingPayload, obligation_cycleOracle,
 obligation_localRealization, obligation_marksEntry,
 obligation_matchLandingPayload, obligation_shiftExitPayload,
 obligation_shiftPalAtScanStates]
```

### ラチェット（`PalPeg/Axioms.lean`）

`#guard_msgs in #print axioms PalPeg.PalInPeg.unconditional` を置いた。

* 義務を 1 個証明して `axiom` を外すと **guard が壊れて更新を強制される**（前進の記録）
* うっかり新しい穴を開けても guard が壊れる（気づける）
* **guard が標準 3 公理だけになったとき §10.5 達成**が機械検査される

これで「前提が何本か」を数える曖昧さが消えた。**進捗は `unconditional` の公理リストの
長さ**という 1 つの機械検査可能な数になった。

### 報告の仕方を変える

これまでの「標準公理のみ」は既存の旗艦定理についての主張として維持するが、
目標定理については **「残り N 義務を axiom として明示」** と書く。
`unconditional` があることを「無条件 PAL 完成」と誤読させないこと。

### ルートは 4 本

`PalPeg.PalInPeg`（目標と部分結果）/ `PalPeg.Canonical`（主線の索引）/
`PalPeg.Workbench`（未配線の部品）/ `PalPeg.Axioms`（監査とラチェット）。

## 2026-09-19 n93: `CentreEq` の遷移保存を 8 本 landing — rewind 相だけが heads を動かす

**全体 build 成功（EXIT=0・エラー 0・sorryAx 0）・標準公理のみ・無条件 PAL は未完。
計画書 §10.5（前提ゼロ）は未達。**

`CentreEq s := (position s.center : ℤ) + value s.radius = position s.right`
（＝`CloseoutPackRun47.CentreLedger` の第 3 節）の遷移保存を、一次情報で確認した分だけ
機械検査した（`PalPeg/BranchSupply.lean` §5d、8 本すべて一発で通った）。

| 定理 | 遷移 | 効果 |
|---|---|---|
| `centreEq_boot` | boot | `center = right`、`radius = 0` |
| `centreEq_init` | `initVM` | `center = right`、radius 保持（init 相で 0） |
| `centreEq_background` | `backgroundS` | 3 つとも不変 |
| `centreEq_beginShift` | `beginShiftVM'` | 3 つとも不変 |
| `centreEq_beginFallback` | `beginFallbackVM'` | 3 つとも不変 |
| `centreEq_restart` | `restartVM` | 3 つとも不変 |
| `centreEq_replayStart` | `replayStartVM` | **前提なしで再確立**（`center = right`、`radius = reset`） |
| `centreEq_of_eq_heads` | 汎用 | `center = right ∧ radius = 0 → CentreEq` |

### レンズで切り分けた結論（重要）

* `fppLens.get s = s.fpp` のみ（`TopVM:53`）→ **fpp 相の 8 遷移**
  （`copyOne`/`copyEnd`/`fppStart`/`homeStep`/`fppSlice`/`fppDone`/`atEnd`/`markForward`）は
  center/radius/right を**触らない**ので `CentreEq` は自明に保存される。
* `rewindLens.get s = ⟨s.fpp, s.left, s.center, s.right, s.length, s.radius⟩`（`TopVM:73`）
  → **`markBack` / `rewindOne` / `rewindPair` の 3 遷移だけ**が heads と radius を動かす。
* `matchedPlace` は `t = (if b then {s with replay := dec s.replay} else s)`
  （`TopMerge:59`）で右ヘッドを動かさない。右ヘッドが進むのは `compare`（`afterCompare`）で、
  そこでは `radiusAfter = inc` が同時に効くので保存される。

### 帰結: mode guard で残差ゼロになる見込み

rewind 相（`choose` / `rewind`）を除外し、`replayStart` も除外した

```
CentreEqG c s := c.mode ≠ Mode.choose → c.mode ≠ Mode.rewind →
                 c.mode ≠ Mode.replayStart → CentreEq s
```

なら、**壊れる 3 遷移はすべて行き先が除外領域**で、出口の `replayStartVM` が
前提なしで再確立するので、**追加の葉なしで tick 保存が示せる**見込み。
（`markBack` の行き先 mode が `choose` であることは `Tick`（`GalilScaffoldTop:109`）の
構成子表で確認済み。）

### 次のセッションの手順

1. `CentreEqG` を定義し `centreEqG_tick` を `cases` で書く（24 構成子）。
   除外領域が行き先の場合は `intro` の第 1〜3 引数で矛盾（`by decide`）。
   残りは §5d の 8 本と fppLens の射影（`Frame.pull` の定義を確認）で埋まる。
   **注意**: `cases ht` は非変数の状態では dependent elimination に失敗するので、
   状態を変数に一般化した補助補題にしてから `cases` する（n91 で確立した型）。
2. `centreEqG_trace` を帰納で出す（`chainPosInv2_trace` と同じ形）。
3. `CentreLedger` が全 scan 状態で出る → `BgStartP2` → `bg` 場が `hver` に合流。
   `shiftDoneLedger` も落ちる。`hme` の `EntryCounters` 半分も `RadiusRep` 経由で落ちる。

## 2026-09-19 n92: `CentreEq` 不変量の tick ごとの分析 — 次のセッションはこれを書く

**全体 build 成功（EXIT=0・エラー 0・sorryAx 0）・標準公理のみ・無条件 PAL は未完。
計画書 §10.5（前提ゼロ）は未達。**

`LTickLeaves3` の残り 2 場のうち `shiftDoneLedger` の本体は等式

```
CentreEq s := (position s.center : ℤ) + value s.radius = position s.right
```

を shift 相でも持つこと。**`LPackM2` に radius を縛る場は無い**（場は `packM`
（`lrepM`/`scanGeom`）・`scanGeomR`・`shiftGeom`・`rrep`・`centreRep`・`centreOrder` の
6 つだけ）ので、`RadLedger.le`（`≤`）からは出ない。

### 一次情報で確認した遷移ごとの効果

| tick 形 | center | radius | right | `CentreEq` |
|---|---|---|---|---|
| boot（`initVM0`） | `= right` | `reset`（0） | — | **成立** |
| `init`（`initVM`、`TopReplay:20`） | `= right s.right` | `= s.radius`（init 相で 0） | `= right s.right` | **保存**（n91 で機械検査済み） |
| `scan_wait` / `scan_count`（`backgroundS`） | 不変 | 不変 | 不変 | **自明に保存** |
| `scan_match`（`afterCompare` ＋ `matchedPlace`） | 不変 | **`radiusAfter = inc`（無条件）** | +1 | **保存** |
| `shift_one`（`shiftTick`、`ChainInputSupply:1445`） | `right s.center`（+1） | **`dec s.radius`（−1）** | 不変 | **保存** |
| `shift_done` | VM 不変 | VM 不変 | VM 不変 | **自明に保存** |
| `replayStart`（`replayStartVM`、`TopReplay:28`） | `= s.center` | `reset`（0） | `= s.center` | **成立**（center = right） |
| `scan_shift`（`beginShiftVM'`） | ? | ? | ? | **未確認** |
| fallback / rewind 系（`beginFallbackVM'`、`markBack`、`rewindOne`、`rewindPair`） | 中心を動かす | ? | ? | **未確認（ここが本体）** |
| copy / home / fpp / markEnd / choose | fpp walker と period テープのみのはず | — | — | **未確認（不変なら自明）** |

```
-- PalPeg/GalilScaffoldChainInputSupply.lean:1445
def shiftTick (s : ShiftState) : ShiftState :=
  ⟨right s.center, right (right s.left), dec s.remaining, dec s.radius, …⟩
```

### 次のセッションの手順（明確）

1. `CentreEq` を定義し、`centreEq_boot` を `rfl` 級で示す。
2. 上の表の「保存」行を機械検査する（`backgroundS_fields` / `afterCompare_radius` /
   `shiftTick` / `initVM` / `replayStartVM` の射影補題は既にある）。
3. 「未確認」行を一次情報で埋める。**`beginFallbackVM'` と rewind 系が本体**
   （中心を動かすので、radius と右ヘッドの関係を再確立する必要がある）。
   ここは `Manacher`/`PalAt` 層の材料（`GalilLiveCentre*`、`GalilPeriodUnion`）が効く可能性。
4. `centreEq_trace` が出れば:
   * `shiftDoneLedger` が落ちる（`CentreEq` ＋ n89 の無料 2 節）
   * `CentreLedger` が全 scan 状態で出る（`LPackM3` を経由せず）
   * → `BgStartP2` → `bg` 場が `hver` に合流
   * `hme` の `EntryCounters` 半分も `RadiusRep`（＝`Canonical radius` ＋
     `value radius = rad`、後者は `CentreEq` ＋ `ScanInvariant.rightPos`）で落ちる

**つまり `CentreEq` 1 本で `bg` と `hme` の両方が進む。** これが今の最短経路。

### 残っているもう 1 場

`backLag : ∀ v h lag margin ver, s.chain = .back v h lag margin ver →
Canonical lag ∧ 0 ≤ value lag`。`LagCan` は `.watch` 相なので別物。
chain の `.back` 相の lag 形状で、`ChainStep.copyEnd` が `.copy` の lag を
`.back` に持ち込むところで確立される。`CloseoutChainPack` / `CloseoutChainSideR` に
同名の場があるので、そこの証明を見ること。

## 2026-09-19 n91: `LTickLeaves3` は 4 場 → 2 場（`initLedger` もタダ）＋ 古い記憶の訂正

**全体 build 成功（EXIT=0・エラー 0・sorryAx 0）・標準公理のみ・無条件 PAL は未完。
計画書 §10.5（前提ゼロ）は未達。**

### 訂正: `radiusAfter` は無条件に `inc`

CLAUDE.md / 記憶に「`compareVM`/`compareFound` に `radiusAfter`（**search 活性 ∧ chain
idle なら不変**、さもなくば inc）を追加」と書いてあったので、
`CentreLedger`（`position center + value radius = position right`）が全 scan 状態では
偽ではないかと疑った。**一次情報を見たら違った**:

```
-- PalPeg/GalilScaffoldTopSearch.lean:37
def radiusAfter (s : GalilVM) : Counter := GalilScaffoldCounter.inc s.radius
```

**無条件の `inc`。** `backgroundS` は右ヘッドも radius も変えない
（`backgroundS_fields` の `hr : t.right = s.right`、`hrad : t.radius = s.radius`）ので、
等式は background で自明に保存され、matched compare では右ヘッドと radius が同時に +1。
よって `CentreLedger` が全 scan 状態で成り立つ設計は整合している。

**教訓**: 過去の自分の記述（CLAUDE.md・メモリ）を一次情報として使わない。疑ったら定義を開く。

### `LTickLeaves3.initLedger` はタダ

`initVM entry s t`（`GalilScaffoldTopReplay:20`）は `t.right = right s.right`、
`t.center = right s.right`、`t.radius = s.radius` を固定する。つまり
**`t.center = t.right`** なので等式は `value t.radius = 0` に落ち、それは
`RadLedger.initZero`。`canRight t.center` / `Sane t.center` は `t.center = t.right` と
**次状態が scan 相**（`Tick.init` の行き先）から §5 の無料補題で出る
（`initLedger_of_trace`）。

`t` は `initVM` で全成分が決まるわけではない（`periodOnly` などは自由）が、
`CentreLedger` が読むのは `center`/`radius`/`right` の 3 つだけで `initVM` が固定するので
trace 上の `st (i+1)` から移せる。

実装上の注意: `cases ht` は `ht : Tick F 2048 (st 0) (st 1)` のように**非変数**の
状態に対しては dependent elimination に失敗する。状態を変数に一般化した補助補題
（`key : ∀ x y, Tick … x y → x.ctl.mode = Mode.init → …`）にしてから `cases` する。
残りの 23 構成子は `| _ => simp_all` で落ちる（各構成子が mode を固定しているため）。

### `LTickLeaves3` の現状

| 場 | 状態 |
|---|---|
| `replayLedger` | **タダ**（n89） |
| `initLedger` | **タダ**（今回） |
| `backLag`（`.back` 相の lag 形状） | 残る |
| `shiftDoneLedger`（shift_done での `CentreLedger`） | 残る。等式 `value radius = r` が本体 |

`shiftDoneLedger` の等式について: `ShiftGeom`（rem = 0）は
`position right = position center + r` を与え、`RadLedger.le` は
`value radius ≤ r` の向きしか出ない。逆向き（`r ≤ value radius`）が要る。
`LPackM2` の場に radius を縛るものがあるか未確認。

### 次の一手

1. `LPackM2` の全場を列挙して、shift 相で radius を縛る場があるか確認する。
2. なければ `shiftDoneLedger` は真の残差。`backLag` と合わせて 2 場。
3. 2 場が埋まれば `LPackM3` が trace に載り、`CentreLedger` → `BgStartP2` → `bg` 場が
   `hver` に合流する（`hme` の `EntryCounters` 半分も同時に落ちる可能性が高い）。

## 2026-09-19 n90: `CentreLedger` の等式の出処は `EntryCounters` の `RadiusRep`

**全体 build 成功（EXIT=0・エラー 0・sorryAx 0）・標準公理のみ・無条件 PAL は未完。
計画書 §10.5（前提ゼロ）は未達。**

n89 で `CentreLedger` は等式
`position center + value radius = position right` 1 本に縮んだ。その出処が確定した。

```
GalilGlueBLeaves.EntryCounters w s :=
  ∃ Rad, ScanInvariant w (position s.center) Rad s.left s.right ∧
         RadiusRep s.radius Rad ∧ SpanRep s ∧ Canonical s.length
RadiusRep counter rad := Canonical counter ∧ value counter = rad
ScanInvariant.rightPos : position r = center + radius
```

差をとれば等式（`BranchSupply.centreEq_of_entryCounters`、標準公理のみ）。
`centreLedger_of_entryCounters` で `CentreLedger` が `EntryCounters` ＋ `CentreRep` から
完全に出る（`canRight center` と `Sane center` は n89 でタダ）。

### なぜ `RadLedger` では足りないのか（重要）

`RadLedger.le` は `position center + value radius ≤ position right` で**不等号**。
探索が活性のあいだ右ヘッドだけ進む場合があるので（`compareVM` の `radiusAfter` は
「search 活性 ∧ chain idle なら不変」）、等式は一般には成り立たない。
**正確さを担保するのは `RadiusRep`**（半径カウンタの値が `Rad` に等しい）。
だから `CentreLedger` は「どの scan 状態でも」ではなく、
`EntryCounters` が成り立つ状態（`Inv` ＋ `SpanRep`、`InvLPC` の各点）で使うもの。

### 残差の現状（`bg` 場まで）

`bg` ← `bg_at_of_supply`（状態局所、n88）の 4 入力:

| 入力 | 状態 |
|---|---|
| `hrepR` | **タダ**（`LPackM2.packM.scanGeom` / `scanGeomR`） |
| `hrepV` | `hver`（`VerRun`）の第 1 成分 |
| `hL` | `hver` の第 2 成分 |
| `hstart`（`BgStartP2`） | `bgStartP2_of_centre` の 3 入力のうち `canRight s.right` と半径台帳は**タダ**、`CentreLedger` は **`EntryCounters` ＋ `CentreRep` に帰着** |

つまり `bg` 場の残差は **`EntryCounters` ＋ `CentreRep` を chain 誕生点（scan かつ idle chain）で持つこと**に縮んだ。

### 次の一手

1. `EntryCounters` を trace の scan 状態で供給する経路を確定する。
   `GalilGlueBLeaves.entryCounters_of_inv (h : Inv raw c r) (hS : SpanRep r)` があるので、
   `Inv` と `SpanRep` が trace の scan 点で取れるかを調べる
   （`CloseoutMarksFree.entryCounters_of_invLPC` は `InvLPC` からは取れると書いている）。
2. `CentreRep` は `LPackM2.centreRep` の guard が `rewind ∨ replayStart` なので
   scan では取れない。scan 相の中心ヘッド表現の供給元を探す
   （`MInv` か `ScanInvariant` の left/right から中心を復元できるか）。
3. `LTickLeaves3` の残り 3 場（`backLag` / `initLedger` / `shiftDoneLedger`）は
   `LPackM3` 経路用。`bg` を `EntryCounters` 経路で直接落とすなら `LPackM3` は不要になる。

## 2026-09-19 n89: 中心ヘッドも動ける — `CentreLedger` は**等式 1 本**に縮んだ

**全体 build 成功（EXIT=0・エラー 0・sorryAx 0）・標準公理のみ・無条件 PAL は未完。
計画書 §10.5（前提ゼロ）は未達。**

`CloseoutPackRun47.CentreLedger s := canRight s.center ∧ Sane s.center ∧
(position s.center : ℤ) + value s.radius = position s.right` の 3 節のうち **2 節が落ちた**
（`PalPeg/BranchSupply.lean` §5b）。

| 節 | 出処 | 状態 |
|---|---|---|
| `Sane s.center` | `GalilTrailSane.SanePack.saneC`（`CloseoutLPack6.sanePack_pt` が `PreTrace` ＋ `LeftLive` だけで trace 全点に） | **タダ** |
| `canRight s.center` | `position center ≤ position right`（`RadLedger.le` ＋ `.nonneg`）＋ `rightPos_le_trace`（n87）＋ `CentreRep`（`LPackM2.centreRep`） | **タダ**（`centreCanRight_of_trace`） |
| `position center + value radius = position right` | — | **残る（等式）** |

### `LTickLeaves3.replayLedger` もタダ

`replayLedger : c.mode = Mode.replayStart → canRight s.center ∧ Sane s.center` は
上の 2 節そのもの。`LPackM2.centreRep` の guard は `rewind ∨ replayStart` なので
replayStart で使える（`replayLedger_of_trace`）。

### 等式について（なぜ独立なのか）

`RadLedger.le` は `≤` しか与えず、`ScanInvariant.rightPos`（`position right =
position center + rad`）と合わせても `value radius ≤ rad` の向きしか出ない
（`PosPayload2.radLe` も同じ向き）。**逆向き（半径カウンタが正確に距離を測る）は
独立した不変量**で、それが `LPackM3.centreLedger` の中身。boot で成立
（`position center = position right`、`radius = 0`）し、background で保存され、
3 つの landing（init / shift_done / replayStart）で再確立される。

### `LTickLeaves3` の現状（`LPackM3` を trace に載せるための唯一の残り）

| 場 | 状態 |
|---|---|
| `backLag`（`.back` 相の lag 形状） | 残る。`LagCan` は `.watch` 相なので別物 |
| `initLedger`（init 遷移先の `CentreLedger`） | 残る。boot 直後なので計算で出るはず |
| `shiftDoneLedger`（shift_done での `CentreLedger`） | 残る。**等式の再確立が本体** |
| `replayLedger` | **タダになった**（今回） |

### 次の一手

1. `initVM` の定義を読んで `initLedger` を計算で落とす（boot 直後、`center = right`、
   `radius = 0` から等式は自明のはず）。
2. `backLag` を `.back` 相の構成から出す。
3. `shiftDoneLedger` の等式を `ShiftGeom`（rem = 0）から出す。
4. 揃えば `LPackM3` が trace に載り、`CentreLedger` → `BgStartP2` → `bg` 場が
   `hver` に合流する。

## 2026-09-19 n88: `canRight` は trace 全域でタダ — `Extra7`（`hee`/`het`）も同時に落ちる

**全体 build 成功（EXIT=0・エラー 0・sorryAx 0）・標準公理のみ・無条件 PAL は未完。
計画書 §10.5（前提ゼロ）は未達。**

n87 の `shiftCan_of_trace` は shift 相専用に書いていたが、論法は mode に依存しない。
一般化した結果、**`canRight` は「右ヘッドが入力を表現している trace 点」でタダ**になった。

| 新しい定理（`PalPeg/BranchSupply.lean` §5） | 内容 |
|---|---|
| `canRight_at_trace` | `Represents` ＋ `focus ≠ none` があれば `canRight (st i).vm.right`（`1 ≤ i`） |
| `frontPack_of_trace` | `FrontPack` は trace の 1 手目以降タダ（`tick_mode_ne_init` ＋ `frontPack_trace`） |
| `scanCanRight_of_trace` | **scan 相の `canRight` ＝ `CloseoutPackRun46.Extra7.scanAvail`。つまり `hee` / `het` の中身がタダ** |

`Extra7.scanAvail := mode = scan → ¬replaying → canRight right` なので、
`scanCanRight_of_trace` はそれより強い（replaying でも成立）。
CLAUDE.md §3 が「`hee`/`het` の残差（scan 状態で `canRight`）は**偽の疑いが強い**」と
書いていたのは、`Inv.input` が右ヘッドの位置を縛らないことを根拠にしていた。
**位置を縛るのは `Inv` ではなく front ポテンシャルと終端の報告点だった。**

側条件 `htc : 1 ≤ Tc w.length` は `PreTraceB.tc1 : Tc 1 = 1` と `PreTrace.mono` から出る
（`1 = Tc 1 ≤ Tc w.length`）。

### `bg` 場の分解（§7）

`CloseoutPackRun48.h_bgP2_of_supply` は 4 入力すべてを源状態でだけ使う（`Run48:186–192`）。
状態局所版 `bg_at_of_supply` を置いた。入力の現状：

| 入力 | 状態 |
|---|---|
| `hrepR`（右ヘッドが入力を表現） | **タダ**（`LPackM2.packM.scanGeom` / `scanGeomR`） |
| `hrepV`（verifier が入力を表現） | `hver`（`VerRun`）の第 1 成分 |
| `hL`（`LagCan`） | `hver` の第 2 成分 |
| `hstart`（`BgStartP2`、chain 誕生の形） | **残る**。`CloseoutPackRun47.bgStartP2_of_centre` が `canRight s.right`（**タダになった**）＋ 半径台帳（**タダ**）＋ `CentreLedger` から出す |

**残る唯一の穴は `CentreLedger`**（`LPackM3.centreLedger`）。`LPackM3` を trace に載せる
には 4 葉パックのうち `LTickLeaves3`（`backLag` ＋ init/shift_done/replayStart の 3 台帳）
だけが要る（他 3 つは `auxPack_steps` / `CloseoutPackW.lticksN_of_lpackM2_W` /
`lTickLeaves2_of_shiftPalG` でタダ）。

### 次の一手

1. `LTickLeaves3` の 4 場を埋める（`backLag` は `LagCan` から、3 台帳は各 landing の幾何）。
2. `LPackM3` を trace に載せる → `CentreLedger` → `BgStartP2` → `bg` 場が `hver` に合流。
3. 同様に `matchLand` を `MatchRes2`（`matchRes2_of_lpackM3` ＋ `MatchRest`）から。
   `MatchRest.repV`/`repVmid` は `hver` と同型、`canRNext` は `canRight (right s.right)`
   なので `CloseoutCanRightBound` の 2 歩版（`:76`）で出るはず。
4. 残れば `entryLand` だけ。

## 2026-09-19 n87: `shiftDone` 義務を**完全に放電** — 新規入力ゼロ

**全体 build 成功（EXIT=0・エラー 0・sorryAx 0）・標準公理のみ・無条件 PAL は未完。
計画書 §10.5（前提ゼロ）は未達。**

`BranchAt.shiftDone`（＝旧 `H_shiftDoneRad2`）の 2 節が両方とも消えた。

### 半径台帳（n86）

`RadLedger.le : position center + value radius ≤ position right` ＋
`ScanInvariant.rightPos` の差。`RadLedger` は `CloseoutLPack6.radLedger_pt` が
`PreTrace` ＋ `LeftLive` だけで trace 全点に与える。

### `canRight s.right`（今回）

**終端の報告点から後ろ向きに伝播する。**

1. `PreTrace.report` → `GalilLedgerAssembly.ReportPointAt.atPrefix`:
   `position (st (Tc |w|)).vm.right = 2|w| − 1`
2. front ポテンシャル（`GalilRunTrace.front s = position right + value replay`）は
   tick で単調（`GalilFrontMono.front_tick_mono`）→ `front_mono_trace`（trace 指標の帰納）
3. `position right ≤ front`（`FrontPack.replayPos` / `.rest` だけから）→ `position_le_front`
4. 終端では `front = position right`（`CloseoutFrontExtra.front_eq_position`、
   `ReportPointAt.notReplaying`）
5. よって `position (st i).vm.right ≤ 2|w| − 1` が trace 全域で成立（`rightPos_le_trace`）
6. `CloseoutCanRightBound.canRight_of_position_bound` に `m = |w|` で流す。
   shift 相の右ヘッドの `Represents`/`focus ≠ none` は
   **`LPackM2.shiftGeom` の `RRep`** が持つ（`LPackM2` は `PreTraceIMW.packs .m2`）

**鍵になった補題（新規・一発で通った）**:
`tick_mode_ne_init` — **`Tick` には `mode := .init` へ行く構成子が無い**
（`GalilScaffoldTop:109` の全構成子の行き先 mode は scan/shift/copy/home/fpp/markEnd/
choose/rewind/replayStart か「変えない」）。だから trace は 1 手目以降 `init` に戻らず
（`mode_ne_init_of_trace`）、`GalilTrailRad.frontPack_trace` が trace の各点で使える。
`i = 0` は `mode = init ≠ shift` で除外される（`initial delay = ⟨.init, …⟩`）。

`Steps` 版（`CloseoutFrontExtra.position_le_of_front_steps`）ではなく **trace 指標**で
書く必要があった: 中間状態の `CentreLive` を `centreLive_trace` は trace の点でしか
与えないのに対し、`Steps` 版は任意の到達状態を量化するから。

### 最上位

`CloseoutFinalBranch.pal_in_peg_final43` — Prop 引数 6 本
（`hSP` `hme` `hor` `hC` `hres` `hver`）。残差は `BranchRes3` の **3 場**
（`bg` / `matchLand` / `entryLand`）＋ `hver`。**義務の実数 8。**

### 本数の誠実な読み方

| 定理 | Prop 引数 | 義務の実数 | 形 |
|---|---|---|---|
| `final39`（正本） | 7 | 7 | 分岐 3 本は **global**（放電不能） |
| `final43` | 6 | 8 | 分岐 3 場は **run/trace 形**（放電可能） |

義務の実数では `final39` の 7 が最小なので**正本は据え置き**。ただし `final39` の
`hbgP`/`hmatchP`/`hsdP` は global なので原理的に放電できず、実際に詰めるのは `final43` 側。

### 次の一手 — `bg` と `matchLand`

`H_bgP2` の docstring が明記している：「Everything chain-side now follows from
`chainPos_step`; what is left at the source is the chain-start shape
(`s.chain = idle`) together with `ConsumeAvail`」。`CloseoutPackRun48.h_bgP2_of_supply`
の 4 入力のうち

* `hrepR`（右ヘッドが入力を表現）← **`LPackM2.packM.scanGeom` でタダ**
* `hrepV`（verifier が入力を表現）← **`hver`（`VerRun`）の第 1 成分**
* `hL`（`LagCan`）← **`hver` の第 2 成分**
* `hstart`（`BgStartP2`）← `CloseoutPackRun47.bgStartP2_of_centre` が
  `canRight s.right`（scan 相、`Extra7`）＋ 半径台帳（済）＋ `CentreLedger`
  （`LPackM3.centreLedger`）から出す

**ただし Run48 のこれらの入力は「任意の scan 状態 ＋ `ChainPosInv2`」形なので、
そのままでは `hrepV` が偽の疑いが強い。trace 形に書き換えてから使うこと。**
うまく行けば `bg` / `matchLand` が `hver` に合流し、`final43` は
`hSP` `hme` `hor` `hC` `entryLand` `hver` の **義務 6 本**（`final39` の 7 を下回る）。

## 2026-09-19 n86: `shiftDone` 義務の半径台帳は**タダ** — `RadLedger` から出る

**全体 build 成功（EXIT=0・エラー 0・sorryAx 0）・標準公理のみ・無条件 PAL は未完。
計画書 §10.5（前提ゼロ）は未達。正本の最上位は引き続き `pal_in_peg_final39`（7 前提）。**

### 放電できたもの

`BranchAt.shiftDone`（＝旧 `H_shiftDoneRad2`）は

```
canRight s.right ∧ ∀ rad, ScanInvariant w (position s.center) rad s.left s.right →
  value s.radius ≤ (rad : ℤ)
```

の連言だが、**後者は新規入力ゼロで出る**：

* `CloseoutRadPack.RadLedger.le : position s.center + value s.radius ≤ position s.right`
* `ScanInvariant.rightPos : position s.right = position s.center + rad`
* 差をとって `value s.radius ≤ rad`（`BranchSupply.radLe_of_radLedger`）

そして `RadLedger` は **`CloseoutLPack6.radLedger_pt` が `PreTrace` ＋ `LeftLive` だけで
trace の全点に与える**（`radLedger_boot` は定理、`LeftLive` は `leftLive_of_lpackM`）。
つまり `needIMW'_le_R` の中で内部調達でき、前提として現れない。

### 追加した部品（`PalPeg/BranchSupply.lean` §3–§4）

* `radLe_of_radLedger` / `shiftDone_of_radLedger`
* `BranchRes` — 4 場のうち `shiftDone` を **`shiftCan`（`canRight s.right` のみ）** に縮めた構造
* `branchAt_of_res` — `BranchRes` ＋ `RadLedger` → `BranchAt`
* `chainPosInv2_trace` — `ChainPosInv2` を **trace 指標**で運ぶ（`lpackM3_steps` と同形の帰納）
* `BranchResTrace` / `needIMW'_le_R` — `RadLedger` を内部調達する `needL'` 上界

**なぜ trace 指標にしたか**: `BranchRun` は `Steps` で到達する**すべての**状態を量化するが、
`Tick` は関係なので trace 外の状態も含む。一方、放電の材料（`RadLedger`、`LPackM2`）は
`radLedger_pt` / `PreTraceIMW.packs` が **trace の点 `st i`** でしか与えない。
`chainPosInv2_steps_run` を使う経路は `steps_of_trace` で trace の鎖しか渡さないので、
trace 指標で十分かつ供給と噛み合う。

### 最上位

`PalPeg/CloseoutFinalBranch.pal_in_peg_final42` — Prop 引数 6 本
（`hSP` `hme` `hor` `hC` `hres` `hver`）。`final41` との違いは `hres` が
`BranchResTrace`（`shiftDone` の半径台帳を落とした 4 場）であること。

**正直な読み方**: Prop 引数は 6 のままで、減ったのは `shiftDone` 場の**半分**。
義務の実数は 9 → 8.5 相当。正本は引き続き `pal_in_peg_final39`（7 本、束ねていない）。

### 次の一手 — `shiftCan`（`canRight s.right` at shift_done）

経路は見えている：

* `CloseoutClockFront.canRight_of_run`（:152）は **mode 条件なしで** `canRight y.vm.right`
  を出す。必要なのは
  - `hg : ∀ m z, Steps … m x z → FrontPack z.ctl z.vm` — `GalilTrailRad.frontPack_trace`
    が trace から与える（`CloseoutLPack6:290` が既に使っている）
  - `hx0 : front x.vm = 0`, `hxc : x.ctl.clock = delay` — boot の値
  - `hrep`/`hpres`（右ヘッドの `Represents` と `focus ≠ none`）— shift 相では
    **`LPackM2.shiftGeom` の `RRep`** が持つ
  - `hn : n < delay * (2 * w.length)` — run 長の予算。**ここが唯一の未確認**。
    `PreTrace.cost` / `Tc` の上界と突き合わせること。
* これが通れば `shiftCan` も消え、`BranchRes` は `bg` / `matchLand` / `entryLand` の 3 場になる。

## 2026-09-19 n85: 4 分岐義務を run 形に弱めた — `∀ c s` では原理的に放電できない

**全体 build 成功（EXIT=0・エラー 0・sorryAx 0）・標準公理のみ・無条件 PAL は未完。
計画書 §10.5（前提ゼロ）は未達。正本の最上位は引き続き `pal_in_peg_final39`（7 前提）。**

### 何をしたか

`CloseoutPackRun41` の 4 分岐義務（`H_bgP2` / `H_matchP2` / `H_shiftEntry2` /
`H_shiftDoneRad2`）はどれも `∀ (c : Control) (s : GalilVM), …` で**任意の状態**を
量化している。ところが `chainPosInv2_tick` の本体を読むと、**4 本とも自分の `(c, s)` で
しか使っていない**（Run41 の旧 :289/:292/:296/:301/:318 の 5 箇所、すべて `hbg c s` の形）。

1. **状態局所化**（`CloseoutPackRun41` を編集、後方互換）
   * `BranchAt w c s` — 4 義務を 1 状態に束ねた構造
   * `chainPosInv2_tick_at` — 旧 `chainPosInv2_tick` の本体、`BranchAt` を取る
   * `branchAt_of_global` — global 4 本から `BranchAt` を作る
   * `chainPosInv2_tick` — 旧の名前と型のままのラッパー（**既存の呼び出し側は無改造**）
2. **run 形化**（新規 `PalPeg/BranchSupply.lean`）
   * `BranchRun w x := ∀ m z, Steps … m x z → BranchAt w z.ctl z.vm`
   * `branchRun_of_global`（global → run 形、**逆は無い**）
   * `chainPosInv2_steps_run` — `ChainPosInv2` を run 形の義務で運ぶ
     （再指標化は `Steps.succ ht`、`CloseoutBundleRun.roundBundle_steps_run` と同形）
   * `shiftLocalS_of_branchRun` / `needIMW'_le_B`（3 段の本体は n83 で括り出した
     `ShiftLocalRun.needIMW'_le_of_shiftLocal` に載せた）
3. **最上位**（新規 `PalPeg/CloseoutFinalBranch.lean`）
   * `pal_in_peg_final41` — Prop 引数 6 本（`hSP` `hme` `hor` `hC` `hB` `hver`）

### なぜ run 形でなければならないか（これが本質）

4 義務を放電する材料は run に沿ってしか存在しない：

* `LPackM2.shiftGeom`（`CloseoutPackRun23:103`）— `H_shiftDoneRad2` の `canRight` と
  半径上界はここから出る（`CloseoutShiftDoneP.canR_of_shiftGeom` /
  `radEq_of_shiftGeom_done`）。`LPackM2` は run の各点に `IPackMW.m2` としてある。
* chain 側台帳 `ChainPos`（Run41、Run38 の `SrcPos` を吸収）— `chainPos_step` /
  `chainPos_matched` で run を運ばれる。
* 入力供給（verifier が入力を表現する）— `CloseoutVerSide.VerRun` が run 形で束ねている。

**任意の状態にこれらは無い。だから `∀ c s` の形のままでは原理的に放電できない。**
これは `hpack` が偽だったのと同じ病の裏返し: `hpack` は run の事実を一状態述語として
書いたので**偽**になり、4 分岐義務は一状態述語の族を global に量化したので
**放電不能**になっていた。正しいのはどちらでもなく、**run に沿って量化する**こと。

### 本数の誠実な読み方 — `final41` は正本ではない

`pal_in_peg_final41` の Prop 引数は 6 本だが、**`hB` は 4 義務の束**である。
義務の実数で数えれば 9（run 形 4 ＋ `hver` ＋ `hSP`/`hme`/`hor`/`hC`）で、
`final39` の 7 より多い。**前進は本数ではなく「global → run 形」の弱化**であって、
義務が減ったわけではない。だから：

* **正本の最上位は引き続き `pal_in_peg_final39`（7 本、束ねていない）。**
* `pal_in_peg_final41` は**放電の作業場**として `Workbench` §2 に登録。

（Prop 引数の本数＝前提の本数ではない、という CLAUDE.md の規律をここでも適用した。
束ねて数字を作らない。）

### 次の一手

`BranchRun` の 4 場を run の各点で実際に放電する：

1. `shiftDone` ← `LPackM2.shiftGeom`（run の各点にある）＋ 区間予算
   ＋ `CloseoutShiftDoneP.canR_of_shiftGeom` / `radEq_of_shiftGeom_done`。
   **これが一番近い。** `LPackM2` は `PreTraceIMW.packs i hi |>.m2` で取れる。
2. `bg` / `matchLand` ← `ChainPos` の run 搬送（`chainPos_step` / `chainPos_matched`）。
   側入力の `ConsumeAvail` は全状態版が偽（`ConsumeAvailRefute.hav_false`）なので
   `CloseoutWatchSupply.chainPos_step_of_supply` ＋ `VerRun` を使う。
3. `entryLand` ← `ShiftPos2` の確立（`beginShiftVM'` の 1 consume）。

放電できた分だけ `BranchRun` の場が減り、全部落ちれば `final41` は
`hSP` `hme` `hor` `hC` `hver` の 5 本になる。

### 注意（引き継ぎ）

* `AuxPack` は **boot では成り立たない**（`AuxPack.front.notInit : mode ≠ init`）。
  だから `LPackM3` を boot 根の run に載せる道は無い。`AuxPack` は常に cycle 起点の
  `InvLPC` から `CloseoutPackRun2.auxPack_steps` で立てる。
* `CloseoutPackRun36.lticksN_of_lpackM2_pt` は `BigPack2MG`（＝`IPackMG` ＋ `Extra'`）を
  要るので W 経路では使えない。**W 版 `CloseoutPackW.lticksN_of_lpackM2_W` を使うこと。**
* `CloseoutBranchRes.shiftLocalS_of_run_res` はまだ `hfour` を取る（n83 以前）。
  残差経路では `ShiftLocalRun.shiftLocalS_of_run'` に載せ替える。

## 2026-09-19 n84: 3 分岐前提は同じ 1 つの run 形事実に合流する — 9 → 5 の筋

**全体 build 成功（EXIT=0・エラー 0・sorryAx 0）・標準公理のみ・無条件 PAL は未完。
計画書 §10.5（前提ゼロ）は未達。**

n83 で正本を 7 前提（`pal_in_peg_final39`）にしたあと、7 本それぞれの producer を
実見した（表は `lean-pal/PART_INDEX.md` §2a）。**残差は producer が 1:1 で化けるだけで
本数は減らない。** 減らすには残差を共有させるしかない。残差を並べて分かったこと:

### 発見 1: `ShiftGeom` は run 上でタダ

`hsdP`（`H_shiftDoneP`）は `CloseoutPackRun38:316` では**恒等**（`H_shiftDoneRes` は
`H_shiftDoneP` そのもの）だが、`CloseoutShiftDoneP.posPayload_of_shiftGeom`（:70）が
実質の分割を与える:

* `canR` ← `canR_of_shiftGeom`（`ShiftGeom` ＋ 区間予算 `position right ≤ 2m−1`）
* `radLe` ← `hrad`
* `pos` / `verNext` ← **`ChainSideAt`**（:61）

そして **`ShiftGeom` は `LPackM2` の場**（`CloseoutPackRun23:103`
`shiftGeom : c.mode = Mode.shift → ShiftGeom w s`）。`LPackM2` は
`IPackMW.m2`（`CloseoutPackW:67`）として run の各点にある。**つまりタダ。**

### 発見 2: 3 本の残差は同一の chain 側 verifier 台帳に合流する

| 前提 | 残差の chain 側の中身 |
|---|---|
| `hbgP` → `H_bgRes` | `SrcPos`（`saneVer` ＋ `backPos`）＋ `start`（idle 起点）＋ `verNext` |
| `hmatchP` → `H_matchRes` | `SrcPos` ＋ 起点の payload ＋ 同型の節 |
| `hsdP` → `ChainSideAt` | `pos`（`position verifier + lag = position right`）＋ `verNext` |

`ChainSideAt` の 2 節は `PosPayload` の `pos` / `verNext` と同一。そして
`CloseoutPackRun41:17` が明記している: **「`ChainPos` replaces Run38's `SrcPos`
(its `saneVer`/`backPos` are two of the clauses)」**、`:201`「which also absorbs
Run38's `SrcPos`」。

`ChainPos` は run を運ばれる: `chainPos_step`（Run41:101）/ `chainPos_matched`。
その唯一の側入力が `ConsumeAvail` で、
**全状態への量化版は偽**（n83、`ConsumeAvailRefute.hav_false`）だが
`CloseoutWatchSupply.chainPos_step_of_supply` が 4 つの局所供給事実に分解し、
`CloseoutVerSide.VerRun`（**run 形**）がそれを束ねている。

### 結論: 目標は `final38`（`CloseoutFinalVer`）の 9 → 5

`pal_in_peg_final38` の 9 前提は
`hSP` `hme` `hor` `hC` `hbgP2` `hmatchP2` `hentry2` `hsdP2` `hver`。
中 4 本（Run41 版の分岐前提）は `CloseoutPackRun48` に放電器があり、
その入力は上記の chain 側台帳＋`LPackM2`/`LPackM3` の場なので、
**run 形（`VerRun` と同じ形）に直せば `hver` 1 本に合流する** → `hSP` `hme` `hor` `hC`
`hver` の **5 前提**。

`final39`（7、Run34 版）はこの合流に乗らない（`ChainPosInv'` に shift 相の場が無く、
`ChainPosInv.payload` は `ScanNR` で守られていて shift 相をまたげない ——
`CloseoutPackRun38:290` の `chainPosInv_payload_vacuous_shift` がそれを記録している）。
**だから正本は当面 `final39`（7）だが、本数を下げる作業は `final38` 側で行う。**

### 具体的な手順（次のセッションの最初の一手）

1. `LPackM3` を run に載せる。4 葉パックのうち 3 つは既にタダ:
   * `AuxPack` ← `CloseoutPackRun2.auxPack_steps`（`CentreLive` ＋ 起点の `AuxPack`）
   * `LTickLeavesN` ← **`CloseoutPackW.lticksN_of_lpackM2_W`**（`BigPack2MG7W` ＋ `LPackM2`）
   * `LTickLeaves2` ← **`CloseoutPackW.lTickLeaves2_of_shiftPalG`**（同 ＋ `hSP`）
   （`CloseoutPackRun36.lticksN_of_lpackM2_pt` は `BigPack2MG`＝`IPackMG`＋`Extra'` を
   要るので W 経路では使えない。**W 版を使うこと。**）
   残るのは `LTickLeaves3`（`backLag` ＋ `initLedger` / `shiftDoneLedger` / `replayLedger`）。
2. `CloseoutPackRun49.matchRes2_of_lpackM3` で `MatchRes2` を出す（残差 `MatchRest`）。
3. `MatchRest.repV` / `repVmid` は `VerRun` の中身と同一なので `hver` に合流させる。
   `replayPay` / `canRNext` は `PosPayload2` と右ヘッド供給なので `LPackM2` から出るか確認。
4. Run48 の 4 放電器の入力を run 形に書き換える（**現状の「任意の scan 状態 ＋
   `ChainPosInv2`」形の `hrepV` は偽の疑いが強い**。`ChainPosInv2` は verifier の
   内容を縛らない）。
5. `CloseoutFinalVer.pal_in_peg_final38` の中 4 本を放電して `final41`（5 前提）を張る。

### 併せて記録した警告

`CloseoutBranchRes.shiftLocalS_of_run_res` はまだ `hfour` を取る（n83 より前の版）。
`hfour` は不要になったので、残差経路を使うときは
`ShiftLocalRun.shiftLocalS_of_run'` 側に載せ替えること。

## 2026-09-19 n83: `hfour` 放電 — 正本の最上位は 7 前提（`pal_in_peg_final39`）

**全体 build 成功（EXIT=0・エラー 0・sorryAx 0）・標準公理のみ・無条件 PAL は未完。
計画書 §10.5（前提ゼロ）は未達。**

### 結果

| 定理 | 前提数 | 偽の前提 |
|---|---|---|
| **`CloseoutFinalFour.pal_in_peg_final39`（新・正本）** | **7** | **なし** |
| `CloseoutFinalW.pal_in_peg_final30`（一代前） | 8 | なし |
| `CloseoutFinalVer.pal_in_peg_final38`（新・別系統） | 9 | なし |
| `CloseoutFinalS2.pal_in_peg_final31` | 9 | **`hav`** |
| `CloseoutFinalW3.pal_in_peg_final36` | 5 | **`hpack`** |
| `CloseoutFinalW4.pal_in_peg_final37` | 4 | **`hpack`** |

`final39` の 7 前提（`#check` で型を実見して確認、余計な隠れ前提なし）:
`hSP` `hme` `hor` `hC` `hbgP` `hmatchP` `hsdP`。`final30` から `hfour` だけが消えた形。

### `hfour` はなぜ消えたか — 何も足していない

`CloseoutPackRun40.ChainPosInv'` は `CloseoutPackRun34.ChainPosInv` の `coupled` 場を
`Coupled`（`Other`、2h）から `Coupled'`（`Other'`、5h ＋ 正半周期）に強めただけの構造。

* `watchShiftS_of_chainPosInv'`（`Run40:407`）は `H_fourOther` を**取らない**。
  `Other'` は `Coupled'.watch` の場から `compare'_inv` 経由で出てくるので
  `four_of_other'`（`Run40:368`）が直接効く。
* `chainPosInv'_tick`（`Run40:435`）が要求する分岐前提は `H_bgP` / `H_matchP` /
  `H_shiftDoneP` の **3 本だけで `final30` と同一**。
* boot は `coupled'_of_idle`（`Run40:87`）で無条件。

新規 `PalPeg/ShiftLocalRun.lean` がこれを run に載せる（`chainPosInv'_of_idle`、
`chainPosInv'_steps`、`shiftLocalS_of_chainPosInv'`、`shiftLocalS_of_run'`、
`needIMW'_le_W'`）。

### 偽の前提の発見（`hav`、過剰量化の 8 例目）

`final31` は `hfour` を落とすかわりに

```
(hav : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (i : ℕ), ConsumeAvail (st i).vm.chain)
```

を取っていた。`st` は**無制約な関数**なので `∀ z : ChainVM, ConsumeAvail z` と同値。
`ConsumeAvail z := ∀ wch, z = .watch wch → canRight (right wch.machine.verifier)` で、
`right p` は gap を反転するから、`gap = false` かつ右も incoming も空な verifier では
`canRight (right p) = (true = false) ∨ ([] ≠ []) ∨ ([] ≠ [])` が偽。
証人は既存の `GalilWatchOkInst.bornVer`。反証は `PalPeg.ConsumeAvailRefute.hav_false`
（標準公理のみ、`sorryAx` なし）。**`final31` は無価値。**

`bornVer_can : canRight bornVer` は成り立つ（`gap = false` なので第 1 選言）。
偽になるのは**一歩進めた後**の `canRight (right bornVer)` である。

### コピペの括り出し（コウタの指示どおり、計測から始めない）

* `RadPack` → `TrailF` → `needL'` の 3 段は **4 回**書かれていた
  （S＝`CloseoutShiftS`、S3＝`CloseoutWatchSupply`、S4＝`CloseoutVerSide`、＋今回）。
  本体は `hsh : ∀ i ≤ Tc w.length, ShiftLocalS … (st i)` しか使っていないので、
  `ShiftLocalRun.radPack_pt_of_shiftLocal` / `trailF_pt_of_shiftLocal` /
  `needIMW'_le_of_shiftLocal` として **1 度だけ**書いた。
* `pal_in_peg_final5MW` / `5MW2` / `5MW3` / `5MW4` は `needL'` の上界を作る 1 行を除いて
  **同一の 45 行**。`CloseoutFinalFour.pal_in_peg_of_needLe` がその 45 行で、上界自体を
  `hneed` として取る。以後の版は 4 行の instantiation。
  **既存 4 版の載せ替えは未実施**（別コミットにする。今やると 600 モジュールの再ビルドと
  同時に 4 ファイルを触ることになる）。

### `final38`（9 前提）を残す理由

前提数では `final39` に劣るが、分岐前提が Run41 系（`H_bgP2` / `H_matchP2` /
`H_shiftEntry2` / `H_shiftDoneRad2`）で、`CloseoutPackRun48` の 4 放電器
（`h_bgP2_of_supply` / `h_matchP2_of_target` / `h_shiftEntry2_of_target` /
`h_shiftDoneRad2_of_supply`）が効く**唯一の**経路。`final39` の 3 本を落とすには
こちらを詰める。`hpack` は `CloseoutVerSide` が run 形の `VerRun` に置き換えてあり、
`CloseoutFinalW5.pal_in_peg_final5MW4` がそれを受けていたが**最上位が張られていなかった**
（それを張ったのが `CloseoutFinalVer`）。

### 次の一手

Run48 の 4 放電器の入力はまだ「任意の scan 状態 ＋ `ChainPosInv2`」形で、
`hrepV`（verifier が入力を表現）はその形では**偽の疑いが強い**（`ChainPosInv2` は
verifier の内容を縛らない）。`VerRun` と同じ **run 形**に直してから使う。
それができれば `final38` の 4 分岐前提が `hver` 1 本に落ち、
`hSP` `hme` `hor` `hC` `hver` の **5 前提**になる。

### 教訓

* 「`hfour` が壁」と 1 日以上数えていたが、証明は `CloseoutPackRun40` にあり、
  `CloseoutPackRun41:213` の docstring が「so `H_fourOther` is a theorem」と書いていた。
  **地図が無いと既存の部品を取り落とす**（`Canonical.lean` / `Workbench.lean` に登録済み）。
* `hfour` を落とした既存の 3 版はどれも偽の前提を代わりに取っていた。
  **前提数だけ比べてはならない。型を見て、各前提に反証が無いかを確かめる。**

## 2026-09-19 n82: `hfour` は既存の部品で消える — `four_of_other'` が `H_fourOther` そのもの

**全体 build 成功（EXIT=0・エラー 0・sorryAx 0）・標準公理のみ・無条件 PAL は未完。
計画書 §10.5（前提ゼロ）は未達。**

`final30` の 8 前提の 1 つ `hfour : ∀ w, H_fourOther centreC placeC entry q first w` を
実際に追ったら、**既に証明済みの定理があった**。

### 在り処

* `PalPeg/CloseoutPackRun40.lean:368` — `four_of_other'`
  ```
  theorem four_of_other' (hx : Coupled' x.ctl x.vm) (hs : ScanNR x)
      (hcmp : compare x.vm s'') (hmt : ¬ matched s'') (hg : shiftGuardVM s'')
      (hch : s''.chain = .watch wch)
      (hO : Other' x.vm.periodOnly x.ctl.mode (value x.vm.radius) (value x.vm.cycle)
        (value x.vm.remaining) (periodLength wch)) :
      4 * (periodLength wch : ℤ) ≤ value wch.machine.control.distance
  ```
  これは `H_fourOther`（`CloseoutPackRun34:342`）の結論そのもの。

* 違いは結合の強さだけ:
  - `Other`（`GalilChainCoupling:353`）= `po ∧ (shift → 2h ≤ R+C+Rem) ∧ (¬shift → 2h ≤ R+C)`
  - **`Other'`**（`CloseoutPackRun40:56`）= `po ∧ 1 ≤ h ∧ (shift → 5h ≤ R+C+Rem) ∧ (¬shift → 5h ≤ R+C)`

  議論（docstring より）: `5h ≤ R + C`、`C ≤ 1`（shift guard の `singlePositive cycle` から
  `value_le_one_of_single`）、`distance = R`（`SumRel` ＋ lag ゼロ）、`1 ≤ h` で `4h ≤ distance`。
  `other_of_other'` で `Other' → Other` も既にある。

* **`ChainPosInv2` は既に `Coupled'` を含む。** `PalPeg/CloseoutPackRun41.lean:213` の
  docstring が明記している: 「`ChainPosInv2`: `Coupled'`（Run40、**so `H_fourOther` is a
  theorem**）」。

* `Coupled'` は run を運ばれる: `coupled'_of_idle`（`Run40:87`）で boot、
  `coupled'_tick`（`Run40:149`）で tick 保存、`coupled'_toCoupled`（`Run40:84`）で弱化。

### 次の一手（即実行できる）

`final30` の `hfour` を落とす。`hfour` の消費者は `CloseoutPackRun34.watchShiftS_of_chainPosInv`
で、そこは既に `ChainPosInv` を取っている。`ChainPosInv2`（`Coupled'` を含む）版に載せ替えれば
`four_of_other'` がそのまま効き、`hfour` は消える。**8 → 7。**

注意: `ChainPosInv2` からの `ChainPack` は**偽**（`CloseoutPackRefute.hpack_false`）なので、
`ChainPosInv2` を使うこと自体は問題ないが、そこから `ChainPack` を取る経路には乗らない。
必要なのは `Coupled'` の場だけ。

### 教訓（コウタの指摘どおり）

「最上位の 8 前提も既存の部品で書けるかもしれんやろ」「そこを疑えよ」。実際そうだった。
`hfour` は 1 日以上「壁」として数えられていたが、証明は `CloseoutPackRun40` にあり、
しかも `CloseoutPackRun41` の docstring が「so `H_fourOther` is a theorem」と書いていた。
**地図（`PalPeg/Canonical.lean` / `Workbench.lean`）に残り 7 前提の在り処も入れること。**

## 2026-09-19 n81: `M-watchBreak` 修正を 35 ファイルまで進めて revert — 義務の形を過剰量化で書き間違えた

**全体 build 成功（EXIT=0・エラー 0・sorryAx 0）・標準公理のみ・無条件 PAL は未完。
計画書 §10.5（前提ゼロ）は未達。**

### やったこと

`ChainStep.watchBreak`（正 lag の背景 break）と `ChainMatched.brokenMatched` を入れて
Scala 正本 `ScaffoldChain.step()` / `matched()` に忠実にし、構成子分岐を 35 ファイル分
修理した。その過程で得られたもの：

* `chainStep_watch_total_of_symbol` — **`Good` を仮定しない後続状態の存在**。
  必要なのは「verifier が右に動ける」と「period の焦点が記号を持つ」だけ。
  これが `ChainTickable` / `hready` の解錠にあたる。
* `internal_breakStepPos_false`（`Internal` と `BreakStepPos` は排他）、
  `breakStepPos_unique`（break の行き先は一点）。
* 修正で**真に偽になった**もの: `broken_stays`（`brokenMatched` でカウンタが動く）、
  `CloseoutTickFalse.step_ne_broken`、`WatchClosedC`、`distance_mono_false`。
  いずれも「watch または broken」の選言へ弱めるのが正しい形。
* lag 台帳 `LagLe`（`position verifier + lag ≤ r`）は背景 break で**ちょうど 1 だけ破れる**
  （Scala の `consume()` は `verifier.right()` を済ませてから `mode = Broken` にし
  `lag.dec()` を飛ばす）。`NoBgBreak` として義務化した。

### なぜ revert したか（自分の誤り）

ラウンド系の下流に撒いた義務を

```
(hnobg : ∀ (w' : GalilScaffoldChainWatch.State) v, ¬ BreakStepPos w' v)
```

と書いた。**`w'` を任意に量化している。** `BreakStepPos` は「正 lag ＋ 不一致」なので
そういう `w'` は確実に存在し、**この前提は偽**。付けた定理は全部空虚になる。
`CLAUDE.md` に自分で書いた過剰量化の欠陥の 7 例目。偽の前提を撒いたまま進めるのが
最悪なので緑に戻した。`GalilTrailAssembly` の `NoBgBreak (st i).vm.chain`（状態局所）が
正しい形で、ラウンド系も同じく状態局所にしなければならない。

実作業は `bb11acb` に履歴として残っているので、そこから再開できる（revert は `616c6e5`）。

### 8 前提の見立て

| 前提 | 状態 |
|---|---|
| `hSP` | **`M-watchBreak` 修正で通る見込みが高い**（`chainStep_watch_total_of_symbol` が既にある） |
| `hC`（局所実現） | 最大の未知。`TextFeed*` 153 ＋ `Prog*` 119 本が閉包外。`CloseoutRealize1` は証人が付随的と示すので層自体が不要な可能性もある。**未判定** |
| `hor`（oracle） | 葉 11 本、found 経路が未着手 |
| `hme` | 残差 `WindowInOrigin` 1 本 |
| 4 供給（`hfour` `hbgP` `hmatchP` `hsdP`） | `*Res` 残差 4 本に落ちるが producer が無い |

8 → 7 は `M-watchBreak` 修正（構成子分岐 48 箇所 ＋ 状態局所の threading）で見えている。
その先の `hor` の found 経路と `hC` が本体。

### 構造的な推奨: Scala を functional に直して Lean へ関数として写す

**モデル欠陥が 2 日で 2 件出た**（`M-periodOnly`、`M-watchBreak`）。どちらも
「Scala は全域関数、Lean は帰納的関係」という非対称から来ている。
**関係は場合を落とせるが全域関数は落とせない。**

`ScaffoldChain.step` / `consume` / `matched` を純関数として書き直し（Scala 側の
functional 化は許可済み）、Lean 側もそこから関数として写して、遷移関係はその関数から
導く形にすれば、この種の欠陥が構造的に起きなくなる。今の地図と欠陥 2 件を見た上で、
**これが最も効く一手**。

## 2026-09-19 n80: モデル欠陥 `M-watchBreak` を特定・機械検査 — `WatchOk` が偽である根本原因

**全体 build 成功（EXIT=0・エラー 0・sorryAx 0）・標準公理のみ・無条件 PAL は未完。
計画書 §10.5（前提ゼロ）は未達。**

`WatchOk` の反証（n79）の原因を Scala 正本と突き合わせて掘った結果、**モデル欠陥**だった。

### Scala 正本（`scala/pal/src/main/scala/pal/ScaffoldChain.scala:136,178`）

```scala
def step(answer: TapeView): Unit = {                    // 背景の 1 量子
  mode match {
    case Mode.Copy  => stepCopy(answer)
    case Mode.Back  => stepBack()
    case Mode.Watch if lag.sign > 0 => if (consume()) { lag.dec() }   // ← ここ
    case Mode.Idle | Mode.Watch | Mode.Broken => ()
  }
}
private def consume(): Boolean = {
  verifier.right()
  val token = period.read()
  if (!verifier.read().contains(token.takeRight(1))) { mode = Mode.Broken; false }
  else { distance.inc(); …; period.move(direction); true }
}
def matched(): Unit = {                                 // 新しい place が合流
  margin.inc(); if (periodOnly) cycle.dec()
  if (mode == Mode.Watch && lag.sign == 0) consume() else lag.inc()
}
```

`consume()` は **`step()`（正 lag）と `matched()`（lag ゼロ）の両方から呼ばれ、
どちらでも不一致なら `Mode.Broken` に落ちる。**

### Lean 側の欠落

`ChainStep` には `.watch → .broken` の構成子が無い（`watchStep` は `Internal w w'` を
取り、`Internal` は `.idle`（lag ゼロ）と `.take`（正 lag ＋ `Good`）の 2 つだけ）。
break は `ChainMatched.breaks` にあるが、その `BreakStep` は **`zero w.lag = true`** を
要求するので **lag ゼロ経路のみ**。つまり `step()` 経路（正 lag）の break が欠けている。

機械検査済み（`PalPeg/ChainStepGap.lean`、標準公理のみ・`sorryAx` なし）：

* `no_chainStep_at_positive_lag_mismatch (hp : positive w.lag = true)
  (hng : ¬ Good w) : ¬ ∃ z, ChainStep (.watch w) z`
* `no_chainTick_false_at_positive_lag_mismatch` — 背景量子（`a = false`）でも同じ

**現行モデルでは、正 lag で period と入力が食い違う watch に後続状態が存在しない。**
Scala ではそこで `Broken` に落ちる。

### これが `WatchOk` が偽である理由

`ChainStep` が break できないので、正 lag での背景遷移は `Internal.take` しかなく、
それは `Good` を要求する。だから `WatchOk.good` は「正 lag では period と入力が常に
一致する」と主張することになる。それは Galil の chain の設計（**予測が外れたら壊れる**。
周期区間の終端検出はまさにその break で行う）に正面から反する。**`WatchOk` は偶然
偽なのではなく、モデルの欠落を埋めるために書かれた偽の仮定だった。**

### 直し方と影響範囲

```
| watchBreak (w w') (hb : BreakStepPos w w') : ChainStep (.watch w) (.broken w')

def BreakStepPos (w w') : Prop :=
  positive w.lag = true ∧ canRight w.machine.verifier ∧
  ∃ a, symbol w.machine.control.period.focus = some a ∧
    read (right w.machine.verifier) ≠ some a ∧
    w' = ⟨consume w.machine, w.lag, w.margin⟩
```

`step()` は break 時に `lag.dec()` も `margin.inc()` もしない（`if (consume()) { lag.dec() }`、
`margin.inc()` は `matched()` 側）ので lag と margin は据え置き。

影響範囲: `ChainStep`/`ChainMatched` の構成子で分岐する箇所は **202**。`M-periodOnly`
修正（300 超）と同規模の機械的作業。これを入れれば `ChainTickable` の正直な形
（ready **または** broken）が `WatchOk` なしで証明できるようになり、`hSP` の
唯一の残り障害 `hready` が消える見込み。

### 付随して分かったこと

`WatchOk` を仮定する定理は全部空虚になった: `GalilChainTickable` の全定理、
`GalilReplayGeneral` の 7 本、`GalilOneFallback`、`CloseoutTickFalse.chainOk_tick_false`。
`WatchOk` に言及するファイルは 24。

## 2026-09-19 n79: `WatchOk` を無条件で反証 — `hSP` の壁の正体が確定した

**全体 build 成功（EXIT=0・エラー 0・sorryAx 0）・標準公理のみ・無条件 PAL は未完。
計画書 §10.5（前提ゼロ）は未達。**

再編でできた地図を使って `hSP` の唯一の残り障害 `hready : ChainTickable` に当たった。
まず**インスタンスを構成しようとして** `WatchOk.born` で詰まり、障害が偽の形だったので
反証に回った（`PalPeg/WatchOkRefute.lean`）。

### 反証

`watchOk_false {Ok} (hOk : WatchOk Ok) : False` — 引数は反証対象のみ、公理は
`propext`/`Quot.sound`、`sorryAx` なし。`no_watchOk : ¬ ∃ Ok, WatchOk Ok`。

論法: `born` は **lag と margin を任意に量化して** `Ok ⟨⟨ver, watchControl v⟩, lag, margin⟩`
を与える。`good` は正の lag で `Good` を要求し、`Good` は period テープの焦点記号と
入力右ヘッドの記号の**一致**を要求する。`born` の仮説（`canRight ver`、`OnBlock v`）は
その 2 つを一切関係づけないので、lag を正に取って不一致な証人を入れれば矛盾する。

証人はカーネル計算で確定（`#eval`。自分のコード読みは信用しない）:
`symbol (GalilScaffoldChainPeriod.moveRight bornBlock).focus = some 0`、
`read (right bornVer) = some 2`、`positive ⟨[0],[]⟩ = true`。

既存の `GalilWatchOkInst.no_watchOk_instance` は `WatchOk` に**加えて**無条件の
`∀ w, Ok w → Good w` を仮定した組を否定するもの（`born` を `lag = reset` で使う）。
本件は lag を正に取って `WatchOk.good` だけを使い、**`WatchOk` 単体**を否定する。

### 原因は `ChainOk` の設計（過剰量化の 6 例目）

```
def ChainOk (Ok : WState → Prop) : ChainVM → Prop
  | .back v _ _ _ ver => OnBlock v ∧ canRight ver      -- lag/margin を無視
```

`ChainStep.backDone` は `.back v h lag margin ver` から
`.watch ⟨⟨ver, watchControl v⟩, lag, margin⟩` へ遷移して lag/margin を継承する。
`ChainOk` が `.back` の lag/margin を無視する限り、`ChainStep` での閉性には
**任意 lag/margin での `Ok`** が要る。それが `born` であり、それが `good` と衝突する。

**これは「名前付き葉が偽になるのは、唯一の消費者が到達しない状態まで量化しているとき」
という同じ欠陥の 6 例目。** 実機で生まれた watch の lag/margin は `.copy` 相が積んだ値で
あって任意ではない。

### 次

`hready` を消すには `ChainOk` を再設計する:

```
| .copy t h p v lag margin ver => (∃ n, CopyInv t h p v n) ∧ canRight ver ∧ <誕生義務>
| .back v h lag margin ver     => OnBlock v ∧ canRight ver ∧ Ok ⟨⟨ver, watchControl v⟩, lag, margin⟩
```

`.back` に誕生義務を場として持たせれば `backDone` は自由になり、`born` は `WatchOk` の場から
消える。新たに必要になるのは `copyBit`（`margin ↦ decFour margin`、`v ↦ put v a`）と
`copyEnd`（`v ↦ write v (.last b)`）での義務の保存。`Good` の供給元は
`CloseoutWatchRound53.good_of_pos`（`ChainW` から `Good`）。

## 2026-09-19 n78: 証明をコードとして再編 — 根を 3 本に、`PackedRun` を括り出し

**全体 build 成功・標準公理のみ・無条件 PAL は未完。計画書 §10.5（前提ゼロ）は未達。**

コウタの指摘「コードベース全体把握してないのに断言するのやめろ」「ちゃんとメンテ可能な形に
再編してから物を言え」「このファイルやモジュールにはこの証明があるという頭の地図が作れないと
いくらやっても足踏みになる」を受けて、断定をやめて再編した。**証明は 1 行も意味を変えていない。**

### 実測（推測でなく機械で取った）

| 指標 | 値 |
|---|---|
| モジュール | 1143 |
| 行 | 331,884 |
| `theorem`/`lemma` | 12,613（`def` 4,246 / `structure` 393 / `inductive` 218） |
| 正本 `final30` の推移 import 閉包 | **526** |
| 閉包の外 | 617（うち登録済み 583） |
| 本体が完全一致する証明 | 162 群・419 定理・余剰 **2,483 行**（全体の 0.75%） |
| 誰も import せず名前も参照されないモジュール | 28（5,635 行・158 定理） |

層ごとの閉包との関係: `TextFeed*` は **153 本すべて閉包外**、`Prog*` は 119 本が閉包外
（閉包内の 6 本は `Galil*Program*` 系で別物）、`GS*` 13 本・`*Tapes` 15 本も閉包外。

### 再編（根を 3 本に）

`PalPeg.lean` は 1101 本の import を並べていた。これを 3 本にした。

* `PalPeg.Canonical` — 正本の鎖（閉包 526 本）＋意味のある別名 24 本。
  `lake build PalPeg.Canonical` で正本だけを速くビルドできる。
* `PalPeg.Workbench` — 作ったが未配線の 64 本の根（閉包 583 本）。
  **主定理との関係を層ごとに明記**。
* `PalPeg.Axioms` — 公理監査。

新根の閉包 1135 ⊇ 旧登録 1101、**欠落 0**（機械照合済み）。落としていない。

### 括り出し（`PalPeg/PackedRun.lean` 新規、σ 一般・最下層）

`StepsI` / `StepsIM` / `StepsIMW` / `StepsIMG` / `StepsIMG2` / `StepsIO` は
**文字通り同一の定義**を pack 述語だけ差し替えて 6 回書いたもので、`*_trans` は
6 本とも同じ 8 行、`*_of_*`（pack 弱化）は 3 本とも同じ 5 行だった。

`PackedRun F delay Q Pk k x y := ∃ g, g 0 = x ∧ g k = y ∧ Trace F delay Q g k ∧
∀ i ≤ k, Pk (g i)` を `GalilCheckpoints` だけに依存する σ 一般の部品として定義し、
`PackedRun.trans`（連結）/ `PackedRun.mono`（pack の弱化）/ `PackedRun.pack_at` の 3 本に括った。
`pack_concat`（`CloseoutLPack5`、`GalilVM` 固定・上の層）の 6 行はここに取り込んだ。

6 つの `Steps*` は定義を `PackedRun … pack …` に書き換え（4 行 → 2 行）、
`*_trans` 6 本は `PackedRun.trans h1 h2` の 1 行に、`*_of_*` 3 本は `PackedRun.mono` に委譲。
**文は 1 文字も変えていない。** 以後 pack の変種を作るときは `*_trans` を書き直さない。

### 削除

`PalPeg/Probe1.lean` 1 本のみ（`attribute [ext]` と `#check` と自明な `example` だけ、
定理 0、未登録、主定理と無関係）。**デッドコードかどうかは主定理との関係でしか判定できない**
ので、参照ゼロの 28 本のうち残り 27 本は関係を読んで全部残した。特に
`CloseoutClockFront`（`canRight_of_run` / `extra7_of_run`）と
`CloseoutWatchRound53`（`good_of_pos` ＝ `WatchOk.good` の内容）は**今の壁に直接効きそう**で、
未参照のまま転がっていた。

### 撤回した断定

「正本は `final30`（8 前提）で、8 が正直な床」と書いたが、確認したのは `final30` `final31`
`final33` `final36` `final37` の 5 本だけで、47 本を数えていない。`final32` `final34`
`final35` は grep が空振りしたのに理由を調べていない。**この断定は撤回する。**
前提の数は Prop 引数の本数では測れない（`∀ w, H_x w` は 1 本に見えて族、instance は自動放電）。
数えるべきは「producer が無い前提」であり、それは型を見て初めて決まる。

編集の規律は `CLAUDE.md` の「証明はコードである — lean-pal 編集の規律」に書いた。

## n81 (2026-09-19) `ShiftAtMismatchM` を**証明した** — Round 30 の piece 1〜4 が閉じた

**全体 build 成功（EXIT=0、エラー 0、sorryAx 0）・標準公理のみ・無条件 PAL は未完。**

`roundOne_of_segRun_M`（`Rounds … 1` の構成器）の唯一の残差 `ShiftAtMismatchM` を、
**運ばれる不変量だけから証明した**（`CloseoutMismatchCompare.shiftAtMismatchM_of_round`）。

`CloseoutWatchRound30` が「piece 1」と呼んで NAMED leaf にしていた事実——不一致比較の
無効 chain tick が watch を保つ——も定理になった。**ラウンド終端では lag がゼロ**
（`RoundScan.caught.lagZero`）なので、`Internal.idle` ＋ `ChainStep.watchStep` ＋
`ChainTick false` = step で恒等になる。

`CloseoutMismatchCompare.lean`（新規、8 定理）: `chainTick_false_idle`、
`compare_mismatch_of_lagZero`（**不一致比較を構成**）、`compare_mismatch_of_round`、
`chainStep_watch_of_lagZero`、`compare_chain_of_mismatch`（与えられた比較の双対）、
`copyIdle_congr`、`beginShift_of_guard`、**`shiftAtMismatchM_of_round`**。

前提は全部運ばれる不変量: 終端の `RoundScan` ＋ 周期の紐付け、`used + 1 = 2h`、
`Canonical s1.length`（`CPack.canon`）、`CopyIdle s1`（`AuxPack.copyP`）、
中心不変量 ＋ `CentreRep`。

**Round 30 の 6 部品のうち 1〜4 が PROVED。** 残りは piece 5（origin 台帳）と
piece 6（`Rounds … mm` と終端 `ScanSeg`）。次は `roundOne_of_segRun_M` の残る入力
（`ChainTickable` / `WatchClosedC` / `RoundDataC`）の現状を測る。

## n80 (2026-09-19) **正直な最上位は `final30`（8 前提・反証済みゼロ）** — `final37` の 4 は偽を 1 つ含む

**全体 build 成功（EXIT=0、エラー 0、sorryAx 0）・標準公理のみ・無条件 PAL は未完。**

`hpack` が偽と分かったあと用途を追跡して判明した：**`pal_in_peg_final30`（`CloseoutFinalW`）
は `hpack` を必要としない。** 8 前提 `hSP` `hme` `hor` `hC` `hfour` `hbgP` `hmatchP` `hsdP` で、
自身の docstring が「eight hypotheses, none refuted」と書いている。`#print axioms` は標準 3
公理のみ（本ターン再確認）。`final37` が 8 → 4 に減らした経路（`final5MW3` の `hpk`）は
**偽の前提を通っていた**。したがって**正直な最良状態は `final30` の 8 前提**で、
`final37` の 4 前提は「4 つの証明可能な前提」ではない。

### `final5MW3` 経路の修理（捨てずに直した）

`CloseoutVerSide.lean`: `shiftLocalS_of_chainPack` が読む 4 場（`inv`/`repR`/`repV`/`lagCan`）
に分解し（`shiftLocalS_of_parts`）、`repR` は run 自身の `LPackM2`（pre-trace の pack）から
出るので、`hpack` の寄与は `repV` ＋ `lagCan` だけと確定。それを **run 形**で名付けたのが
`VerRun`（`chainPosInv2_of_idle` では反証できない）。`shiftLocalS_of_verRun` /
`radPack_ptS4` / `trailF_ptS4` / `needIMW'_le_W4` / `verRun_of_hpack`。

`CloseoutFinalW5.lean`: **`pal_in_peg_final5MW4`** = `final5MW3` の `hpk` を
`hver : ∀ w st, st 0 = boot w → VerRun … w (st 0)` に置換。標準公理のみで通る。

ただし `final37` の他の `hpack` 用途（4 供給の導出と `packRunR_MWP`）は `VerRun` では
覆えない。それらは `final30` では前提として明示されているので、`final30` に戻るのが正しい。

### 追記（同ターン）— `hSP` を run 形に、`CopyIdle` の偽の前提も除去

`roundBundle_steps` の側入力は `∀ z : State GalilVM`（全状態）で量化されていて、
`CopyIdle` は copy 相で偽だった（`hpack` と同じ欠陥）。`hci` の使用箇所は
`shiftRound_tick` の `shift_one` 分岐 1 箇所だけで、そこには `c.mode = Mode.shift` が
scope にある。3 ファイル（`CloseoutPackRun37` / `CloseoutAdvanceT` /
`CloseoutRoundBundle`）で `hci` を `x.ctl.mode = Mode.shift → CopyIdle x.vm` に修正。

`CloseoutBundleRun.lean`（新規）: `roundBundle_of_idle`（**idle chain で束が成立**——
cycle の `InvLPC` 起点がこれ）、`roundBundle_steps_run`（側入力を run の状態に量化）、
`shiftPal_of_run`（`hSP` の内容を run から出す）。

さらに `CopyIdle` の残差は**タダ**だった: `AuxPack.copyP` が
`CopyPack c s := c.mode ≠ Mode.copy → CopyIdle s` で `shift ≠ copy`。`AuxPack` は
`auxPack_steps` で run 搬送され `packRunR_MW` が既に走らせている
（`copyIdle_shift_of_auxPack` / `shiftPal_of_run_aux`）。

さらに `ChainPosInv2` も**不要**だった。`roundBundle_tick` の `hinv` は 3 箇所とも
`blockInv_of_chainPosInv2` 経由で `BlockInv s.chain` だけを使い、それは
`Coupled.block` ＝ `AuxPack.coupled` の場。よって `roundBundle_tick_B` /
`roundBundle_steps_B` / `shiftPal_of_run_B` は `ChainPosInv2` を取らない。

**`hSP` の残差は run 形の 2 つ ＋ fresh 分岐**: `H_readsShift`（⟸ `OriginShift` ⟸
`Rounds`）、`H_freshShift`（⟸ `first_round`）、`periodOnly = false` の `ShiftPal`。
`BlockInv`/`CopyIdle`/`canRight` は全部 `BigPack2MG7W` の場から無料。

**正直な評価**: 前提数の削減ではなく構造の直し。台帳のルールでは `OPEN` のまま。
意味があるのは 3 つとも「run データの組み立て」に帰着し、その組み立て器
（`Rounds` ← `roundOne_of_segRun_M`、`first_round`）が名前付き葉を持たない定理である点。

### これからの道筋（`final30` の 8 前提）

`hSP` は `RoundBundle` ＋ `OriginShift` ＋ `H_freshShift` に還元済み（`ShiftRun` piece 4 は
本ターン PROVED）。`hme` は `marks_steps_free` が運ぶが残差は `WindowInOrigin`（モデル欠陥 (e)、
横移動）。`hor` は 11 葉 ＋ `hsc`。`hC` は未分解。`hfour`/`hbgP`/`hmatchP`/`hsdP` は tick 補題で、
結論が tick の目標状態に束縛されるので `hpack` のようには反証できない。

## n79 (2026-09-19) **`hpack` は偽だった** — 最上位 4 前提のうち 1 つを反証

**全体 build 成功（EXIT=0、エラー 0、sorryAx 0）・標準公理のみ・無条件 PAL は未完。**

`pal_in_peg_final37` の第 4 前提
`hpack : ∀ w c s, ChainPosInv2 w c s → ChainPack q first w c s` は**成立しない**。
機械検査済み（`PalPeg/CloseoutPackRefute.lean`）。

`ChainPosInv2` の場は 3 つだけ（`Coupled'`、非 idle chain の payload、shift 台帳）で、
`chainPosInv2_of_idle` は chain が idle なら**任意の `w` `c` `s`** に対してそれを与える。
ところが `ChainPack` は run の事実を主張する：

- `scanBound : c.mode = .scan → ∃ m, 1 ≤ m ∧ m < w.length ∧ position s.right ≤ 2m−1`
  は `w.length ≤ 1` で**充足不能**（PAL は 1 文字語を含み、run の開始点は
  `Tick.init` の着地＝scan モード・idle chain）
- `centreCanR : canRight s.center` は**モード前提なし**で、中心頭が入力末尾に達した
  状態（走査完了時）で偽

反証: `hpack_false_at_short_word` / `chainPack_false_at_short_word` /
`hpack_false_at_exhausted_centre`。

**原因（2 層）**: 直接原因は `ChainPack` が「run に沿って確立される事実の束」を
一状態述語として書き、前提を一状態不変量にしていること（`ChainPack` 自身の docstring が
「established **along the run**」と書いている）。その原因は、以前このセッション系列で
別葉だった `ScanBudget`（`CloseoutFinalPack` の `hbudget`）を束のフィールド `scanBound` に
**畳み込んだ**こと。台帳の自分のルール「未解消の前提を構造体フィールドへ移しただけなら
OPEN のまま」に照らせば前進ゼロで、しかも `ScanBudget` 自体が既に同じ反例で偽だった。

**直し方（論証）**: `ScanBudget` の唯一の用途は `matchRes2_of_chainPack` で
`canRight_of_position_bound` により `canRight s.right` を得ることだけ。必要なのは
チェックポイント `m` ではなく `canRight`。そして `canRight` も一状態の事実ではない。
よって正しい形は束を `Steps` に沿って運ぶこと——`CloseoutRoundBundle.RoundBundle`
（`roundBundle_tick` / `roundBundle_steps`）と同じ構成。boot 状態では全ヘッドが入力原点に
あるので `canRight` は全部成立し、各 tick はヘッドを保つか 1 進めるだけ。

### 追記（同ターン）— 修理の第 1 段

`CloseoutBudgetFree.lean`: `scanBudget_of_front_run`（偽だった `scanBound` の**本物の
producer**。`position_le_of_front_run` が cycle の出口上界を run に沿って遡らせる。
`Extra7` から `hee`/`het` を消したのと同じ機構）、`avail2_of_front_run`、
`ChainSideW`（修理された前提の形）、`chainSideW_of_hpack`。

`CloseoutChainSideR.lean`: `ChainSideR` = `ChainSide` − `scanBound`、
`chainSide_of_chainSideR`、`chainPack_of_chainSideR`、`chainSideR_of_chainSide`。

**正直な評価**: 実証された矛盾（`w.length ≤ 1` での `scanBound`）は消えたが、
`ChainSideR` は依然 run の事実を 3 場の前提の下で主張するので真にはなっていない。
「矛盾している」→「導出できない」に変わっただけ。前提を run 搬送パック
（`BigPack2MG7W''`）に変えるのが本筋で、各場の供給元は台帳に対応表で記録した。
残差は `walkerPin`/`walkerOrigin`（モデル欠陥 (e)）。

**最上位の正直な状態**: `pal_in_peg_final37` の型は正しく `#check` は 4 引数、
`#print axioms` は標準 3 公理。しかし 4 前提のうち `hpack` は**偽**なので、これは
「4 つの証明可能な前提」ではない。計画書 §10.5（前提ゼロ）は未達であり、この経路では
到達できない。`hpack` を run 沿いの束に置き換えるのが次の主要作業。

## n78 (2026-09-19) `H_readsShift` は「shift 完了時の read origin」に還元 — `hSP` の残差が 2 つとも同じ通貨に

**全体 build 成功（EXIT=0、エラー 0、sorryAx 0）・標準公理のみ・無条件 PAL は未完。**

最上位は `pal_in_peg_final37`（`CloseoutFinalW4`）の **4 前提**（`hSP` `hor` `hC` `hpack`）のまま。
`#check` で 4 引数、`#print axioms` は `[propext, Classical.choice, Quot.sound]` を再確認。
計画書 §10.5（前提ゼロ）は**未達**。残差の正本は `lean-pal/CLOSEOUT_LEDGER.md`。

### 先に立てた論証

`H_readsShift` の消費点は `readsRound_tick` の `Tick.shift_done` **1 箇所のみ**。
そこに何が足りないかを 3 方向から測った：(1) `ReadsInv` は等式なので `chainShiftOne` の
カウンタ減算で壊れ運べない、(2) `SweptOff` は `Offset` なので shift を生き延びるが
bounce→`encoded` の辞書が 1 周期対しか遡れず累積継続を変換できない（その変換が
`rounds_origin` の帰納法そのもの）、(3) `good_of_periodOn` も入力が `Entry` で同じ壁。
残るのは一つ、**ラウンド開始の read origin**。

### やったこと（`PalPeg/CloseoutReadsOrigin.lean` 新規、7 定理）

`readsRun_of_originAt`（`OriginAt → ReadsRun`：`round_of_originAt` が `used = 0` の
`RoundScan` ＋ `ReadsInv` を返し、`roundScan_unique` が任意の `RoundScan` の `used` を
`0` に強制する）、`readsRound_of_originAt`、`h_readsShift_of_originAt`、
`h_readsBirth_of_originAt`、`roundBundle_tick_O`（束の tick の葉を `OriginShift` に置換）、
`originShift_of_roundSeg`。

`H_readsShift` は `positive s.remaining = false`（shift 完了）を前提に追加して再定式化
（`CloseoutRoundUnique`、呼び出し側 1 箇所修正）。shift 途中の chain は部分 shift 済みの
watch で `Entry` を満たさないので、この前提なしでは偽になる。

### 状態

`H_readsShift` は **REFORMULATED**（供給未完なので OPEN のまま）。新 NAMED `OriginShift` は
`originAt_of_rounds`（証明済み）が controller `Rounds` から供給し、その `Rounds` は
`CloseoutWatchRound9` が無条件に構成する。つまり `hSP` の残差 2 つ
（`OriginShift` と `H_freshShift`）は**どちらも「run の断片を `ReadOrigin` に組み上げる」
同じ通貨**で、`hor` の found 経路系（`CloseoutWatchRound5.ShiftRoundC`）と同一。

### 追記（同ターン）

`h_readsShift_of_rounds`: controller `Rounds` ＋ 第 1 ラウンドの `Entry` から
`H_readsShift` が 1 行で出る。基底の `first_round` は名前付き葉を持たない定理、
`Rounds` は `roundOne_of_segRun` が構成（残差は `ShiftAtMismatchC` のみ）。
**負の結果**: `H_freshShift` は `OriginAt` からは出ない — `OriginAt` は `used = 0`
（`value s.cycle = 2h`）を固定するので `shiftInv_entry` が要る
`singlePositive s.cycle = true` と両立せず、fresh chain の初回 shift は
`used = 2h − 1` で起きる。`H_freshShift` は `first_round` 自身の義務。

### 追記 2（同ターン）— `ShiftAtMismatchC` を反証して再定式化

`roundOne_of_segRun` の唯一の残差 `ShiftAtMismatchC` は**過剰主張**だった。`SegEndS` の
第 3 出口は「cycle 終端 ∨ 不一致」の選言で、消費者は不一致側で cycle 終端を知らんのに、
葉の結論が `singlePositive s1.cycle = true` を主張していた。Scala 正本
（`ScaffoldGalil.scala:254`）では `canShift` が `if periodOnly then singlePositive cycle`
を含むので、**周期中の**不一致では機械は shift せず `beginFallback()` に行く。

`CloseoutShiftMismatch.lean`（新規）: `shiftAtMismatchC_false_at_nonterminal`（反証、
非終端 `RoundScan` の `terminal_iff` に接地）、`ShiftAtMismatchN`（cycle 終端を前提へ）、
`shiftAtMismatchN_of_C`、`roundOne_of_segRun_N`（終端出口が 2 種を区別し、新しい場合は
機械の `beginFallback`＝oracle の `hmismatch` 分岐）。既存の `roundOne_of_segRun` は
壊していない。

**同一の欠陥が 5 例目**（`ShiftPal` / `H_advanceT` / `MatchTickC` / `hpos` /
`ShiftAtMismatchC`）。新しい葉を測るときは、まず**消費者がその分岐で何を知っているか**
を先に読む。

### 追記 3（同ターン）— 自己訂正: `ShiftAtMismatchN` もまだ過剰主張だった

`N` の結論には予測一致 `read (right s1.right) = symbol w.machine.control.period.focus`
が残っていて、終端 `RoundScan` ではこれは入力依存の等式
`(encoded raw)[C+R+1]? = (encoded raw)[C+R+2h+1]?` に等しい（破れたら `beginFallback()`）。
`CloseoutWatchRound30.ShiftRoundAtC'` が既に正しい形（guard をトリガーとして前提に取る）
を持っていたので、それに合わせた。

`ShiftTrigger`（機械の `beginChainShift` 条件）、`ShiftAtMismatchM`（入力依存の 2 事実を
前提に移し、葉は機械的部品だけ）、`roundOne_of_segRun_M`（終端出口を 3 分割: break /
shift / fallback）。全部標準公理のみ・sorryAx なし。

**次の一手**: `ShiftRun` の存在（Round 30/33 の piece 4）。`ShiftRun.next` が要求するのは
`positive s.remaining = true` の算術と 3 つの `canRight`。中心は `C → C+h`、左ヘッドは
`C−R−1 → C−R−1+2h` で、`RoundScan.size : 2h ≤ R` より両方 `[C−R, C+R]` の内側。
`ScanInvariant` の `Represents` ＋ `size` から `h` の帰納法で構成できる。

### 追記 4（同ターン）— piece 4（`ShiftRun` の存在）を構成した

`ShiftAtMismatchM` に残った唯一の非自明な部品は**入力依存ではなかった**。
右移動が塞がるのは最終 gap セルちょうど（`GalilEndOfInput.not_canRight_iff`）なので、
`ShiftRun.next` の 3 つの `canRight` は厳密な位置上界にすぎない。

`CloseoutShiftRun.lean`（新規）: `canRight_of_lt`、`right_step`、`shiftRun_exists`
（`n` の帰納法）、`shiftRun_exists_entry`（shift 入口形）。
**`ShiftRunC` / `ShiftRunCL` / piece 4 は PROVED。**

残る供給は運ばれてる状態不変量だけ: 中心頭は `CloseoutPackRun21.CentreRep`
（`InvLPC` の場）、左頭は `RoundScan.caught.scan`。位置上界は `RoundScan.rightPos` ＋
`not_canRight_iff` ＋ `size : 2h ≤ R` の算術。**次は中心頭の位置と `C` の関係**
（`RoundScan` の場にはない）。

### 追記 5（同ターン）— piece 4 をラウンドから直接出した

`shiftRun_exists_round`: 終端 `RoundScan` ＋ `CentreRep`（`InvLPC` の場）だけから
`ShiftRun` の存在が出る。運ばれる中心不変量
`ScanInvariant raw (position s.center) rad s1.left s1.right` が
（`leftPos`/`rightPos` でヘッドから `(center, radius)` が一意に決まるので）
中心頭を `C + h` に固定し、`RoundScan.rightPos` が右頭を `C + R + 2h` に置き、
`GalilEndOfInput.position_le` がそれを `2 * raw.length` で抑え、
`size : 2h ≤ R` が中心の `h` 歩と左頭の `2h` 歩の両方に余裕を残す。
`left_word` / `left_present` / `left_position` で左頭を 1 歩左へ。
**piece 4 は完全に閉じた**（新しい仮定ゼロ）。

### 訂正

前ターンの「次は `segment_to_checkpoint` を `hsegmentM` の消費者に配線」は外れ。
`hsegmentM` は `h_oracle_of_leaves*` の葉から既に落ちている（`segment_of_invLPC` が
`hreadyB` に置換済み）。`segment_to_checkpoint` が閉じたのは `hmismatch` の `hpos` 残差側。

## n77 (2026-09-19) 最上位 4 前提を維持しつつ残差を 3 つの壁に統合、`hor` に初めて producer を付与

**全体 build 成功（EXIT=0、エラー 0、sorryAx 0）・標準公理のみ・無条件 PAL は未完。**

最上位は `pal_in_peg_final37`（`CloseoutFinalW4`）の **4 前提**（`hSP` `hor` `hC` `hpack`）。
計画書 §10.5（前提ゼロ）は未達。残差の正本は `lean-pal/CLOSEOUT_LEDGER.md`。

### 残る独立な壁は 3 つ

| 壁 | 内容 | 帰着 |
|---|---|---|
| **`ScanToScan`**（run の区間分解） | scan-to-scan の run が `ScanSeg` ＋ `Rounds` に分解する | `hSP` のラウンド境界と最初のラウンド、`hor` の found 葉（`ShiftRoundC`）、`SpanRep` 輸送 |
| **`hC`** | `H_realizeLIMW'`、局所機械の実現 | 未分解 |
| **`hpack`** のモデル欠陥 (e) 部分 | `marks` / `hwin` — `beginFallbackVM'` の着地場所が存在量化 | `Fair` かモデル変更が必要 |

### `hSP` の分解（`ShiftPal` → 束 ＋ 2 葉）

`shiftPal_of_readOrigin` の入力は `ChainRound` ＋ `canRight s.right` ＋ `H_fresh` だけになった。
運ぶ 5 場を `CloseoutRoundBundle.RoundBundle` にまとめ、`roundBundle_tick` で組み上げて
コンパイラに残差を検証させた。

| 場 | tick | 残差 |
|---|---|---|
| `ChainRound` | `chainRound_tick_S` | なし（`H_shiftDone` は束自身の `ShiftRound` から） |
| `ReadsRound` | `readsRound_tick_S` | `H_readsShift`（`SweptOff` 基底化で消える） |
| `ShiftRound` | `shiftRound_tick_A` | `H_freshShift` |
| `PeriodShape` | `periodShape_tick`（23 形） | なし |
| `NoReplayWatch` | `noReplayWatch_tick`（23 形） | なし |

証明した葉: `H_matched`（過剰量化）、`H_born`（phase 0 vs 4）、`H_advance`（`ReadsInv`）、
`BlockInv`（`ChainPosInv2`）、`H_birth` の誕生半分（`PeriodShape`）、
`H_birthR`/`H_readsBirth`（`NoReplayWatch`）、**`H_advanceT`**（palindrome 2 枚の鏡映 ＋
`continued_prediction` の mod 形）。
`WatchShift`（**偽**）は 1 節しか使われておらず `canRight s.right` に置換。

### `hor` に初めて producer を付けた

**訂正**: 「`h_oracle_of_leaves''` が `hor` を産出する」は誤り。tree 中の
`h_oracle_of_leaves*` は**全部** `GalilFinalAssembly.H_oracle`（`CycleOracleMC`、
origin/着地とも `InvL`）を結論とし、`hor` は `CycleOracleMC3`（origin/着地とも
`InvLPS`）で別物。

`CloseoutOracleBridge.hor_of_H_oracle` が橋（差は 2 つ：不変量と、中心進行 vs `mu` 進行）。
`CloseoutOracle8.h_oracle_of_leaves7` で `H_oracle` の葉を **13 → 11**
（`hbudget` と `hrs` を閉じた。鍵は **`Decodes` がタダ** — `decodesC` が証明済み）。

### 訂正した自分の誤り（このセッション）

1. 「`BigPack2MG7W''` に 5 場足す配線で `hme` が落ちる」→ 落ちない（`wpack_tick` が毎 tick `hwin` を要求）
2. 「`hended`/`hlastMatch` は閉」→ **閉じてない**。producer の側入力 `hpres` が偽（`searchReady_run_true_iff`、機械検査: `CloseoutPresRefute`）
3. 「`hor` に producer がある」→ 無い（型名は同じでも結論が違う）
4. 「原点はラウンド単位でしか運べない」→ `Offset` 形なら shift 相を生き延びる（`SweptOff`）
5. 「`H_advanceT` は窓の外」→ palindrome が 2 枚あるので窓の内側

**教訓**: 型名の一致で producer を判断せず、**定義を展開して origin と結論の不変量を照合する**。
CLAUDE.md §1 に記録した。

## n76 (2026-09-19) 最上位を 8 → 4 前提に。`hsc`/`hws`/`hsl`/`hni` は反証、`hbudget`/`hav`/`hstart`/`hee`/`het`/`hfl`/`hme` は run 束の場へ

**全体 build 成功（EXIT=0、エラー 0、sorryAx 0）・標準公理のみ・無条件 PAL は未完。**

### 最上位: 8 前提 → 4 前提

**`pal_in_peg_final37`（`CloseoutFinalW4`）は 4 前提**: `hSP`（scan 状態の `ShiftPal`）、
`hor`（`CycleOracleMC3`）、`hC`（`H_realizeLIMW'`）、`hpack`（`ChainPosInv2 → ChainPack`）。
残差の正本は `lean-pal/CLOSEOUT_LEDGER.md`。

### この区間で効いた 1 つの技法

**単一状態の性質は、別前提ではなく run が運ぶ束（`ChainPack`）の場に置く。**
`hav`（`ConsumeAvail`）、`hstart`（`BgStartP2`）、`hbudget`（位置上界）、`hfl`（`0 ≤ length`）は
すべてこれで落ちた。位置上界が単一状態の性質だと気づいた時点で `hbudget` は 5 分で落ちた
（その直前にウチは「見込みなし」と書いていた。誤り）。

### 反証した前提（4 つ）

| 前提 | 反例・理由 |
|---|---|
| `hsc`（`H_stageScan`） | `InvScan` の 11 場は `s.radius` に触れないが `ReplayStage` は `Canonical radius` を要求 → `InvLPS` に再切り出し |
| `hws`（`WatchShiftG`）/ `hsl`（`H_shiftLocalG` の一部） | `ChainStep.backDone` で生まれたばかりの watch は `distance = reset` なので `4 * periodLength ≤ distance` を破る |
| `hni` | `initVM` は `chain = .idle` を与え、`invLPC_init` は `mode = .scan` に着地する（空虚） |

### 主要な新規

| 名前 | ファイル | 内容 |
|---|---|---|
| `front_eq_position` / `extra7_of_front_steps_pack` | `CloseoutFrontExtra` | `hee`/`het` を `front = position right + value replay` の単調性で。34 分岐の右ヘッド解析は不要だった |
| `LagAll` + `lagAll_step`/`lagAll_matched` | `CloseoutLagAll` | lag の canonical + 非負が `ChainStep ∪ ChainMatched` で閉じる |
| `lenNonneg_of_span_radius` | `CloseoutSpanTick` | `hfl` を `SpanRep` + `RadiusRep` から。`shiftTick` は `length` を 2 減らすが `radius` も減るので関係は保存される |
| `windowInOrigin_tick_pin` / `walkerInv_tick_pin` | `CloseoutWinTick` / `CloseoutWalkerTick` | `Fair` 依存はどちらも 1 箇所・状態対の等式 1 本だけ。pin に置換して逐語保存 |
| `ChainPack`（約 25 場） | `CloseoutChainPack` | run が運ぶ中央の束。`q`/`first` は構造体引数 |
| `bigPack2MG7W''_tick_M` / `packRunR_MWP` | `CloseoutMarksPack` | `hme` は `hpack` の `marks` 場に包含されていた |

### 訂正した自分の誤り

1. 「`extra7_of_run` は 1 行で配線できる」→ できない（`PackRunRMG2` に位置上界がない）
2. 「`length` は減らない」→ `shiftTick` が `dec (dec s.length)`。代入の grep はレコード更新を見落とす
3. 「`hfl` は tick 不変量でない」→ `spanRepS_shiftTick` が存在する
4. 「`hbudget`/`hme` に見込みなし」→ どちらも落ちた
5. 「単一ファイル build が通れば十分」→ 構造体の引数を変えたら必ず全体 build（`ChainPack` の arity 変更で全体が 11 error / sorryAx 5 になった）
6. 「`hor` は producer ゼロで原理的に到達不能」→ 誤り。`h_oracle_of_leaves''` が 14 葉から産出し、13 葉版 `CloseoutOracle7` は build 済み・未登録だった
7. 「`Fair` の除去には構造変更が必要」→ 参照は各 1 箇所
8. 「`BigPack2MG7W''` に 5 場を足す配線で `hme` が落ちる」→ 落ちない。`wpack_tick` は着地の `hwin` を毎 tick 要求し、`hwin` を場にする道は `beginFallbackVM'` の着地場所 `p` が存在量化されたまま（モデル欠陥 (e)）なので閉じている

### 次

`hpack` の残差は `ChainSide`（`CloseoutChainPack:241`）。`lagCan`/`backLag` は `LagAll` で閉、
残りは `repV`/`repVmid`/`scanBound`、および `marks`（モデル欠陥 (e) に触れる）。

## n75 (2026-09-19) `hbs`/`hls`/`hsl` を定理化して最上位を 8 前提に、`M-periodOnly` をモデルに実装、`hsc` は反証して再切り出しへ

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規登録: `CloseoutCandOrient`、`CloseoutShiftLocalFree`、`CloseoutStageScan1`、`CloseoutPackRun51`、`CloseoutBirthFrame`、`CloseoutPeriodOnlyRegression`。sorry なし。

### 最上位: 11 前提 → 8 前提

`pal_in_peg_final25`（`CloseoutPackRun51`）。`final24` の 11 前提のうち 3 つが**義務ではなかった**ことを確認して供給した。

- `hsl`（`H_shiftLocalG`）: `InvLPC` のどの状態も chain は idle。`Inv.rest` が `Restarted` を出し、その第 1 連言が `r.chain = .idle`。scan 側は `InvScan.chainIdle`。chain が idle なら `ShiftLocalG` の全場は `beginShiftVM'` の watch 前提を要求するので空虚（`shiftLocalG_of_chainIdle`）。→ `CloseoutShiftLocalFree.chainIdle_of_invS` / `h_shiftLocalG`。
- `hbs`/`hls`（`H_bootShift`/`H_landShift`）: 同じ理由。`initVM0` が `chain := .idle` を置き、`initial` からの唯一の tick `Tick.init` がそれを保つ。既に `CloseoutPackRun6` に定理としてあった。

残る 8: `hSP`, `hws`, `hee`, `het`, `hme`, `hsc`, `hor`, `hC`。

### `hsc`（`H_stageScan`）は偽。再切り出しの第 1 段を証明

`H_stageScan` は「`InvScan` を満たす**すべて**の状態で `ReplayStage`」を要求する。`InvScan`（`GalilReplaySegment:317-341`）の 11 場は `s.radius` に一言も触れないのに、`ReplayStage` の `Restarted` は `RadiusRep r.radius Rad`＝`Canonical r.radius` を要求する。`Counter = ⟨pos neg : List Unit⟩` なので、任意の `InvScan` 住人の `radius` だけを値 `0` の非正準表現 `⟨[()],[()]⟩` に差し替えると 11 場は全部生き残り `ReplayStage` だけ壊れる。

修正は既知の型の再切り出し `InvScanS := InvScan ∧ ReplayStage`（`InvScan → InvScanO`、`SearchReady → SearchReadyB` と同じ手）。産出側は既にデータを持っていた: `replay_after_fallback` は `Restarted raw t 0 reset` と `c.clock = 2048` を前提に持ち、`WatchSegE` を返しながら `stage` 場だけ捨てていた（`GalilReplaySegment:310` の docstring がその旨を記録している）。`CloseoutStageScan1.replayStage_of_seg` / `replayStage_of_replay_after_fallback` で拾い直した。

### `M-periodOnly`: モデルの欠陥を実装して全体に通した

Scala `ScaffoldChain.start()` は `periodOnly = false` **かつ** `cycle.reset()` を行うが、Lean のモデルはどちらも落としていた。誕生条件は `found = true` ではなく「その遷移で新しい chain が実際に始まること」なので `chainBorn (found) (x : ChainVM) := x.isIdle && found`、状態側を `afterBirth born s`（`GalilScaffoldTopSearch:70,77`）で包む。`compareFound`/`backgroundS` の遷移先をこれで包んだ。

- 抽象側の破損は**射影を 1 個挟むだけ**の型ずれで、`GalilFrontier`、`GalilReplayRest`、`GalilScaffoldTopRoundS`、`GalilScaffoldTopFirstRound`、`GalilScaffoldTopFoundLife`、`GalilScaffoldTopLifeRestart`、`GalilScaffoldTopFoundLoop`、`GalilScaffoldTopFallbackCycleS`、`GalilScaffoldTopFallbackRestart`、`GalilScaffoldTopOutputRound`、`GalilScaffoldTopFallbackAll`、`GalilScaffoldTopOutputCycle`、`GalilTickFun`、`GalilTickFun2`、`GalilCycleNoShift`、`LocalReplaySwap`、`LocalReplayParked`。`GalilScaffoldTopSegmentHeads.watchSegE_heads` だけは単調形 `t.periodOnly = true → s.periodOnly = true` に弱めた。
- 伝播を止めた補題が 2 本。(1) `not_shiftGuard_afterMismatchB`（`GalilScaffoldTopFallbackCycleS`）: 誕生時は `chainStart` が `.copy` を返すのに `shiftGuardVM` は `.watch` を要求するので、誕生の有無にかかわらず guard は立たない。これで `¬ shiftGuardVM (afterMismatch …)` を仮定に持つ 20 ファイルへの伝播が消えた。(2) `refresh_afterBirth_iff`（`GalilScaffoldTopSearch`）: `P.onLetter = onLetterVM raw` と `P.leftFirst = leftFirstVM` の下で `refresh` は `afterBirth` 不変。`outputRel_matched_refresh'` 系の呼び出しをそのまま生かせる。
- 局所側は `LocalTick1` に `birthL` / `abs_birthL` / `inv_birthL` / `stepLocal_birthL` / `matchCtl_congr` を入れ、`bgState` に誕生元 chain を渡し、局所歩数 `c₁` を 66 → 67（match 分岐が `searchSteps + 3`）に上げて `tickL1_local` / `tickL1_inv` / `tickL1_abs` を再証明。
- `tickL1_abs` は新たに側条件 `hbirth`（`onLetter`/`leftFirst`/`replayExhausted` が `afterBirth` 不変）を取る。`Shared` の 3 場は抽象関数なので一般には示せないが、具体 `PofC` では `onLetterVM` が `position s.right`、`leftFirstVM` が `position s.left`、`replayExhaustedVM` が `s.replay` しか読まず、`afterBirth` はその 3 つを触らないので定理になる（`CloseoutBirthFrame.hbirth_PofC`）。
- 回帰テスト `CloseoutPeriodOnlyRegression.birth_resets` は修正前は失敗し修正後は通る。

### `hee` の残差は真偽未確定（偽の疑いが強い）

`H_extraEntry7` の残差は `∀ c r, InvLPC w c r → position r.right ≠ 2*w.length`。`Inv`（`GalilRunInv:29-49`）の 10 場のうち右ヘッドに触れるのは `input : Represents r.right.head raw` だけで、これは**内容を縛るが位置を縛らない**。入力を食い切った状態（`Tick.scan_wait` が回る状態）でも全場が成立しうる。攻め口は (a) `w = []` で `2*w.length = 0` と初期位置 `0` が一致する反例、(b) `InvLPC` への右ヘッド余裕場の追加（`hsc` と同じ再切り出し）。台帳に記録した。

### 既に反証済み（回帰テストとして常駐）

`H_candOrient`（裸の prefix→suffix `Candidate` 移送）は偽。証人 `W = [0,0,0,0,0,1]`, `n=5`, `lower=0`, `h=1`。`CloseoutCandOrient.unrestricted_transport_false`。正しい橋は同一窓＋反転の `GalilDpSuffix.candidate_iff`。

### `hme` への合成: `hcan` は `CPack` から出る（`CloseoutReplayCanRight`）

`CloseoutPackRun28.walkerInOrigin_of_run`（`WalkerInOrigin` の産出元、そこから `hme`）は義務 `hcan`＝「到達可能な各状態で `replaying = true` なら右ヘッドが動ける」を持っていた。これは仮定ではなく合成で出る。

- `FrontPack.replayPos`（`GalilFrontMono:98`）: `replaying = true → ∃ m, replay = ofNat (m+1)`。
- `FrontPack.frontier`: `Frontier s`＝`position right + m ≤ 2 * arrived right`。
- 右へ動けないなら終端 gap で右スタック空＝`PopsIncoming`。`consume_not_replaying_false`（`GalilFrontier:342`）がこれと正の replay カウンタから `False` を出す。
- **`CPack.front : FrontPack c s`**（`GalilCentreLive:152`）。`CloseoutPackRun25.wpack_of_fair` は既に `CPack` を持ち回っており、`cpack_tick` の唯一の入力 `hfl` もその仮定にある。

よって `cpack_steps` で `CPack` を歩数に沿って運べば `hcan` は定理（`hcan_of_cpack`）。新規入力なし。

## 2026-09-19 wave 10 — `ShiftLocalG` も消えた: **8 前提・反証済みゼロ**（`pal_in_peg_final30`）

**全体 build 成功（EXIT=0、エラー 0、sorryAx 0）・標準公理のみ・無条件 PAL は未完。**

`pal_in_peg_final30`（`lean-pal/PalPeg/CloseoutFinalW.lean`）は
`[propext, Classical.choice, Quot.sound]` のみに依存し、
**`WatchShiftG` も `ShiftLocalG` もコードに現れない**。

`final29` の `hsl : ∀ w y, ShiftLocalG … w y` も偽だった（`ShiftLocalG` の全場の
前提は `beginShiftVM'` で、`beginShiftVM` は `s''.chain = .watch w` のみ要求する
ので、`ChainStep.backDone` 生まれの `distance = reset` の watch が前提を満たしつつ
`4 * periodLength ≤ distance` を破る）。

弱化ではなく**削除**した。wave 8 で trail 橋を `ChainPosInv` に載せ替えた結果
`IPackMG.shift` を読む者が誰もいなくなったため。`Run30` から直接落とすと旧鎖
`final17 → … → final25` が壊れる（実測・ロールバック済み）ので非破壊複製:

- `CloseoutPackW` — `IPackMW := LPackM ∧ LPackM2`、`BigPack2MG7W`、`ipackMW_tick`
- `CloseoutCheckW` — `StepsIMW` 〜 `preTraceIMW_exists`
- `CloseoutOracleW` — **`packRunR_MW`（shift 仮説ゼロ）**、boot、oracle、`needL'`
- `CloseoutFinalW` — `H_realizeLIMW'`、**`pal_in_peg_final30`**

`hC` は `PreTraceB` を取る形（`H_realizeLIMW'`）に変えた。`LatchTrue` は
`stLG' τF w st (Tc w.length)` だけを読み run pack に触れないので、これが自然な領域。

`final30` の 8 前提（すべて未反証）: `hSP`, `hme`, `hor`, `hC`,
`hfour`, `hbgP`, `hmatchP`, `hsdP`。後ろ 4 つは Run34 の guarded 分岐仮説で
`chainPosInv_tick` が 23 形状中 20 を閉じており残り 3 形状分。

**wave 6 からの推移**: 8（`hsc` 偽）→ 7 → 5（`hws` 偽）→ 9（`hsl` 偽）→
**8（反証済みゼロ）**。数の増減より「偽の前提が残っているか」が判定基準。

## 2026-09-19 wave 9 — 偽の `hws` が最上位から消えた（`pal_in_peg_final29`）

**全体 build 成功（EXIT=0、エラー 0、sorryAx 0）・標準公理のみ・無条件 PAL は未完。**

`pal_in_peg_final29`（`lean-pal/PalPeg/CloseoutWeakFinal.lean`）は
`[propext, Classical.choice, Quot.sound]` のみに依存し、**`WatchShiftG` は
もう現れない**。前提は 9 個で `final27`（5 個）より多いが、**偽の前提が
ゼロ**になった。数より正しさ。

`hws : ∀ w y, WatchShiftG … w y` は偽（`CloseoutPackRun32` の caveat:
`ChainStep.backDone` で生まれた watch は `distance = reset` なので
`4·periodLength ≤ distance` が破れる）。2 つの弱化で消した:

1. **trail 側**（wave 8）: `pal_in_peg_final5MG2T` が trail 橋の全体を
   `ChainPosInv` の上で走らせる（`ChainPosInv → shiftLocalS_of_run →
   radPack_ptS → trailF_ptS → needIMG2'_le_S`）。boot の `ChainPosInv` は
   chain が idle なので無料。
2. **pack 側**（wave 9）: `packRunR_MG27P` は `hws` を 1 箇所でしか使わず、
   そこが必要とするのは `ShiftLocalG`。`WatchShiftG` はそれを含意するだけ
   （`shiftLocalG_of_watchShiftG`）なので、`ShiftLocalG` を直接取れば
   厳密に弱い前提になる（`packRunR_MG27L`）。

`final29` の 9 前提: `hSP`, `hsl`（`ShiftLocalG`）, `hme`, `hor`, `hC`,
`hfour`, `hbgP`, `hmatchP`, `hsdP`。後ろ 4 つは Run34 の guarded 分岐仮説で
すべて `shiftGuardVM` 付き・unmatched 限定。`hsl` の 4 場のうち `move` は
wave 7 の `Extra7` で既に無料。

新規: `CloseoutShiftS`, `CloseoutShiftFinal`, `CloseoutShiftWeak`,
`CloseoutWeakFinal`（全て標準公理のみ）。

## 2026-09-19 wave 7 — `hee`/`het` を無条件化、最上位は **5 前提**

**全体 build 成功・標準公理のみ・無条件 PAL は未完。**

`pal_in_peg_final27`（`lean-pal/PalPeg/CloseoutExtraFinal.lean`）は
`[propext, Classical.choice, Quot.sound]` のみに依存し、残る仮定は 5 つ:
`hSP`, `hws`, `hme`, `hor`, `hC`。

`hee`（`H_extraEntry7`）と `het`（`Extra7` の tick 保存）は、いずれも
`packRunR_MG27` の `hprefix` を作るためだけに存在した。その `hprefix`（run の
各 scan/非 replaying 状態で `canRight`）は、**front ポテンシャルに乗って伝わる**:

- `front s = position s.right + value s.replay` は `CentreLive` run 上で単調
  （`GalilFrontMono.front_stepsAll_mono`、既存）。
- `FrontPack.rest = ReplayRest` より非 replaying 状態では `replay = reset`、
  すなわち `front s = position s.right`。
- よって出口 `y` が非 replaying かつ cycle の上界を持てば
  `position x.right = front x ≤ front y = position y.right ≤ 2m-1`。

右ヘッド自身の単調性（34 ケースの `Tick` 解析）は一切不要。`extra7_of_bound` の
残り 2 入力は `LPackM.scanGeom` の `ScanInvariant` から出る（発火条件が
`Extra7` の語る条件と完全一致）。帰納の循環は `bigPack2MG7''_tickE` が
`Extra7` を「構築済み pack の関数」として受け取ることで解消。

呼び出し側は全て上界を持つ: 進行分岐は `CycleOutMC3` の定義、checkpoint 分岐は
`ReportPointAt` の `notReplaying`/`atPlace`/`pos`/`le`。

新規: `CloseoutFrontExtra`, `CloseoutExtraFree`, `CloseoutExtraOracle`,
`CloseoutExtraFinal`（全て標準公理のみ）。

**訂正**: wave 5 の「`hee`/`het` の残差は偽の疑いが強い」は誤り。偽なのは
「任意の状態で `canRight`」であって、run 文脈では真。

## 2026-09-19 wave 6 — `hsc` 完全除去、最上位は **7 前提**

**全体 build 成功・標準公理のみ・無条件 PAL は未完。**

`pal_in_peg_final26`（`lean-pal/PalPeg/CloseoutStageFinal.lean`）は
`[propext, Classical.choice, Quot.sound]` のみに依存し、残る仮定は 7 つ:
`hSP`, `hws`, `hee`, `het`, `hme`, `hor`, `hC`。

wave 5 の `pal_in_peg_final25`（8 前提）から `hsc`（`H_stageScan`）が消えた。
`hsc` は wave 5 で反証済みだったが、**再切り出しすら不要**だった:

1. 主経路上の消費者は `cycleOracleIMG2_of_cycleOracleMC3R`（`CloseoutPackRun36:673`）
   だけで、そこが `hstage_of_scanBranch` を呼び `InvLPC → InvLPS` に持ち上げている。
2. その持ち上げの `Inv` 側は `replayStage_of_inv` で既に無条件（`CloseoutOracleI2:179`）。
3. `CycleOutMC3` は**両出口で `InvLPS` を返している**（`GalilInvPlus3:193, :212`）。
   `hIS.1` で捨てていただけ。
4. boot も `Inv` 分岐に着地する（`GalilFinalAssembly4.invLPC_init:94` の `hI : Inv`）。

よって Run36 §2 のチェックポイント再帰を `InvLPS` 上で再走させれば
`hstage_of_scanBranch` は一度も呼ばれない。`preTraceIMG2S_exists` の結論
`PreTraceIMG2` は Run36 の同名 structure そのものなので下流は無改造。

新規（全て標準公理のみ）: `CloseoutStageRecur`, `CloseoutStageCheck`,
`CloseoutStageBoot`, `CloseoutStageOracle`, `CloseoutStageFinal`。
PR #65 マージ済み。残差の正本は `lean-pal/CLOSEOUT_LEDGER.md`。

**次の狙い**: `hee`/`het`/`hws` の共通核は `canRight`（`extra7_of_bound` で
位置上界から出せるが、`PackRunRMG2` の `hprefix` に位置上界が無い）。
`hme` は `ChooseLayout` の run 不変性に還元できる（`marksEntry'_of_layout` は
**副条件なし**、`CloseoutPackRun16`）。

## n20 (2026-09-17 朝) 葉の放電・偽仮定 4 件・非決定性

## n74 (2026-09-19 未明) 外部レビューを受けて**台帳導入**・`H_candOrient` 反例確定・自分の誤報 1 件を訂正・oracle から `hpres` 消滅

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規登録: `CloseoutCandOrient`、`CloseoutWatchRound52`、`CloseoutPackRun49`、`CloseoutOracle6`、`CloseoutWatchRound53`、および `GalilReplaySpan.lean` への**追記のみ**の §24。sorry なし。

### 進め方の是正（`lean4-peg-closeout-followup-2026-09-17.md` を受けて）

外部レビューの指摘を妥当と認める。**「新ファイル＋新しい `finalN`＋build 緑」を単独では前進として数えない。** `final13 → final24` の番号増加は義務の減少を意味しない。
新設した **`lean-pal/CLOSEOUT_LEDGER.md`** が残差の正本（区分: `OPEN`/`REFUTED`/`REFORMULATED`/`PROVED`/`INTEGRATED`）。
未解消の前提を `H_x → H_y`・構造体フィールド・instance・別 oracle へ移しただけなら `OPEN` のまま。
`#print axioms` は推移的公理依存の検査であって、引数に置いた前提の成立は検証しない。

### REFUTED を 1 件、Lean で確定

`H_candOrient`（裸の prefix→suffix `Candidate` 移送）は**偽**。証人 `W = [0,0,0,0,0,1]`, `n=5`, `lower=0`, `h=1`（`W.take 5` の接頭辞 3/5 は回文、`W.drop 3 = [0,0,1]` は非回文）。
`PalPeg/CloseoutCandOrient.lean`: `prefix_ok`、`suffix_bad`、**`unrestricted_transport_false`**、対比として正しい橋 `correct_bridge`（= `GalilDpSuffix.candidate_iff`、同一窓 + 反転）。標準公理のみ。回帰テストとして常駐させ、旧契約名が消えても反例が残るようにした。
なお `Extra.cand` は既に主経路から削除済み（n67/n69）なので、この反例は削除が正しかったことの裏付け。

### 自分の誤報の訂正

n72 で「`WatchFreshAtC` は文脈だけで閉じた」と書いたのは**誤り**。`CloseoutWatchRound52` により、着地の chain は `copy`（`chainStart` は `ChainVM.copy`、`ChainMatched` は構成子を保つ）であって `watch` ではないので、`WatchFreshAtC … cP sP` は**前提が充足不能＝空虚**（`landing_chain_copy`:120、`landing_not_watch`:135、`watchFreshAtC_vacuous`:148）。watch 誕生は着地の `2h+3` prep tick 後で、そこでの clock は fresh でない。→ 誕生時刻版 `WatchBirthFreshC` が `OPEN`。純益は、**反証済みの `WatchFreshC` schema と `watchClockC_of_fresh` が経路から外れた**こと（`WatchClockAtC` は birth ごとに証明可能な形）。

### oracle: 反証済みの普遍葉が経路から消えた

`GalilReplaySpan.lean` §24（追記のみ、既存宣言は不変）: `HpresRun`、`hpresRun_mono`、`found_resultRP`、`idle_countdown3RP`、`idle_compare3RP`、`replay_construct3RP`、`replay_after_fallback_general''RP` — 不変版の 6 つの `hpres` 使用箇所を全部放電。`CloseoutOracle6`: `invScanO_of_replay_generalR'`、`cycleOracleMC2C_of_piecesP'`、**`h_oracle_of_leaves5`**。
**`hpres`/`hpresRep`（普遍形、`hpres_false_at` が反証）は oracle のどこにも現れなくなった。** ただし後継の `hpresRepAt`/`hpresT` は「供給可能」であって**まだ供給されてへん**＝台帳では `REFORMULATED`。実供給は `CloseoutOracle7` で試行中。

### その他

- `CloseoutPackRun49`: `LPackM3` = `LPackM2` + `centreLedger` + `lagCan`、`lpackM3_tick`（全 23 分岐）。`MatchRes2` の成分は `repR`/`saneR`/`canR`/`repNext`/`radNext`（中心台帳が `rad = value radius + 1` を厳密に固定）/`startLedger`/`lagCan`/`backLag` が閉。残 `repVmid`/`replayPay`/`repV`/`canRNext`。
- `CloseoutWatchRound53`: **`WatchTailC` は定理**（`watchTailC_of_coreX`:213）。credit の形は不安定だが**形の対が安定**（`WRel`: `queued` か `immediate`）、run 長は不変なので `ChainWRun` の測度修正は不要。入力は Round50 の呼び出し側に既にあり新規の未解決なし。`ClockOneC` は `MatchCoreC`（純粋に機械レベル）1 つから従う。
- **build 失敗の記録**: 一つ前の全体 build は EXIT=1 / errors=4。全部 `Lean exited with code 139`（SIGSEGV）で、サブエージェントが `lean -o` で `.olean` を上書きしたことによる成果物の競合。証明の失敗ではない。再実行で緑。今後、全体 build 中は共有 `.lake` への書き込みを行わせない。
- `M-periodOnly`（chain 誕生時に `periodOnly = false` と `cycle.reset()` が漏れている）の先送りを解除し、隔離 worktree で専任担当を開始。boolean 一個の代入では不十分で、誕生条件は「その遷移で新しい chain が実際に誕生すること」（`found = true` ではない）。


## n73 (2026-09-19 未明) chain 台帳の葉が 3 つ閉・fallback replay は `Mode.scan` + `replaying` フラグ・oracle 橋が閉

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 3 本登録（`CloseoutPackRun48`、`CloseoutPreload41`、`CloseoutWatchRound50`）、sorry なし、build ログ `build_n73c.log` EXIT=0。
- **pack（`ChainPosInv2` の葉）**: `CloseoutPackRun48`: **訂正** `LagNonneg` は自動でない（`value : Counter → ℤ` で空 `pos` の `dec` は −1、`lagNonneg_not_of_canonical` :27）が、`LagCan`（:35、watch で `Canonical lag ∧ 0 ≤ value lag`）は**自己保存**（`lagCan_step` :51（`take` の `positive` ガードが減分を払う）、`lagCan_matched` :74）→ 場を 1 つ足せばよい。**より良い経路**: `ConsumeAvail` が参照されるのは `Internal.take`（ガード `positive lag`）と `Outer.immediate`（ガード `zero lag`）だけなので、`chainPos_step_of_supply`（:107）は**源自身の `canRight s.right` だけ**で済み、**`H_bgP2` から供給の葉が消滅**（`h_bgP2_of_supply` :172）。葉 (2) 閉（`h_matchP2_of_target` :250、供給は目標 payload 自身の `canR`）、葉 (4) 閉（`chainPos_immediate` :330 + `h_shiftEntry2_of_target` :365）、葉 (5) は chain 内容を持たず 2 つの素の pack 場（`h_shiftDoneRad2_of_supply` :418）。残: `MatchRes2` の成分（`repVmid`/`backLag`/`replayPay`/`saneR`/`radNext`/`startLedger`）と新規場 `CentreLedger`（scan で `canRight center ∧ Sane center ∧ pos center + value radius = pos right`；`scan_match` で両辺 +1、`shift_done` は `shiftGeom`+`shiftGeom_exit` から再確立、ヘッド半分は `CentreRep` のモードガードを scan に広げる）→ `CloseoutPackRun49`（`LPackM3`）進行中。
- **readiness/oracle（訂正）**: `CloseoutPreload41`: **「fallback replay は `Mode.replay`」は誤り** — `GalilReplaySpan.idle_countdown3`(:1484–87)/`idle_compare3`(:1737) はどちらも `c.mode = .scan` で走り `c.replaying = true` は**フラグ**。`ReadyFieldP3` は `replaying` に言及せんので `paced`/`paced0` がそのまま適用でき、**新しい節は不要**（`ReadyFieldP4 := ReadyFieldP3`）。`hpresAt_replaying`(:86)、`hpresAt_countdown`(:97)/`hpresAt_compare`(:104)（`HpresAt` の 2 ケースと一致）。`hpresRep` 自体は普遍（∀ s a v）なので `hpres_false_at` が反証 → 制限形 `HpresRepAt`(:148)。**橋は閉**: `stepsAll_bigPack2M''_of_soundScanNR`(:117、`packRunR_M''` の内側帰納を再走して run を昇格)、`hpresAt_along_soundScanNR`(:155) が `HpresRepAt` を供給（残は restart/replayStart の再入 2 つのみ）。残るは `GalilReplaySpan` に制限形を受ける primed 版を**追加**する編集（~9 署名 / 6 使用箇所、3 重化されたブロック）→ 進行中（`GalilReplaySpan` への追記 + `CloseoutOracle6`）。
- **watch**: `CloseoutWatchRound50`: **`WindowEndC` は仮定ゼロで閉**（`windowEndC_free` :86；`LandingData` の `ScanInvariant` が `Represents t.right.head raw` を持つので `position_le_of_represents` で `pos t.right ≤ 2|raw| < |encoded raw|`）。`ClockOneC` の match 側は 2 葉に: `WatchTailC`(:207) と `MatchQuantumC`(:254)。閉じた補助: `chainW_setE`/`chainW_setBud`、`chainW_bump`（:166、着地では窓端と右ヘッドが一致するので `E` は `R → R+1` と伸びる）、`inc_dec_comm`/`inc_decFour_comm`、**`bump_step`（:181、`copyBit`/`copyEnd`/`backStep`/`backDone` で credit の可換性を証明）**、`chainWRun_bump`（:219）。**訂正**: 「`inc lag`/`inc margin` は後段に読まれん」は copy/back までで、`.watch` では credit は場の加算でなく `Outer.queued`（`zero lag = false` のとき）/`Outer.immediate`（実際の consume）に分岐し、`queued` 後の `Internal` は `positive s.lag` を見る（`inc` が `reset` lag で反転）→ `WatchTailC` は `coreX_good` 経由。
- 進行中: `CloseoutPackRun49`、ReplaySpan primed 版、`CloseoutWatchRound50`、`52`。
- **偽だった主張の訂正**: 「`0 ≤ value lag` は表現から自動」→ 偽。「replay は `Mode.replay` 状態」→ `Mode.scan` + フラグ。
- 残: n72 と同じ、pack は `MatchRes2` 2 成分 + `CentreLedger`、oracle は `hpres` 消去の編集 + 既知の葉一覧。


## n72 (2026-09-19 未明) oracle の `hpres` は scan 側のみ放電・`WatchFreshC` は全区間量化で偽（着地形は文脈から閉）

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 2 本登録（`CloseoutOracle5`、`CloseoutWatchRound51`）、sorry なし、build ログ `build_n72b.log` EXIT=0。
- **oracle**: `CloseoutOracle5`: `reachAtC2_of_target_matchP`（:64、`GalilOracleMC2.reachAtC2_of_target_match` を `HpresAt` で再証明；唯一の使用箇所 `MC2:544` は chain idle の scan 着地で `clock = 1`、まさに `HpresAt` の側条件）、`cycleOracleMC2C_of_piecesP`（:160、`hpres` を `hpresRep`（普遍、fallback replay 専用）と `hpresT`（到達可能性限定）に分割）、`h_oracle_of_leaves4`（:274）。**`hpres` は未放電**で、残差 `hpresRep` は `Mode.replay` 状態（`GalilReplaySpan:1480–1900` の `replay_construct3`/`idle_countdown3`/`idle_compare3`）にあり、`ReadyFieldP3` は `Mode.scan` 条件付きなので `hpresAt_along_run` が届かん → readiness に replay 節（`CloseoutPreload41` 進行中）。もう 1 つ小さい隙: `hpresT` の配線に run 述語の橋（oracle の `StepsAll … (SoundScanNR raw)` vs Preload40 の `BigPack2M''`）。
  - **oracle 葉の現況**: 閉 = `hex`, `hsearch`, `hends`, `hbudget`, `hrs`, `hended`, `hlastMatch`, `hstr`。残 = `hpresRep`, `hstage`（`ReplayStageInv`、mid-replay restart の `3·radius ≤ 5·last`）, `hshape`（`StartShape` は偽 → `StartShape'`）, `hlastMismatch`（最終文字分岐 + `EntryRefreshed`）, `hmismatch`（`hdp` → `MismatchDp`+`StageBudgetAt`、`hpos` → 区間予算；`hfb` 閉）, `hfound`/`hfoundBg`（着地不変量に `Restarted`/`StageEntry` + found tick からの経路構成、**最大の未着手**）, `hfoundReplay`（未着手）, `hreadyB`（着地での `RunEntriesAll`）。
- **watch（2 つの訂正）**: `CloseoutWatchRound51`: (a) `FoundCompareCtxC` は `cF.clock = 1` と `cP = {cF with clock := 2048}` を持つので **fresh clock は found tick でなく着地**（`foundCtx_landing_clock` :44）、文脈に `WatchSegE … cF sF cP sP` は無く輸送は `(cP, sP)` から始めるしかない。(b) **`WatchFreshC`（Round49:87）は偽** — 全 watch 区間を量化して `cb.clock = 2048` を主張するが `WatchSegE.stop` は任意の clock で成立（`not_watchFreshC` :68）。`WatchClockC`（Round47:111）も `watchClockC_of_fresh` 経由でこの欠陥を継承 → **`final19` の葉は着地形に切り直す必要**（`CloseoutWatchRound52` 進行中）。着地限定形 `WatchFreshAtC`（:78）は **文脈だけで閉**（`watchFreshAtC_of_ctx` :86、`cP.clock = 2048` は場、birth の `BlockInv` は `blockInv_matched`∘`blockInv_chainStart`）。`prepPaceC_of_seg`（:105）は `PrepSegLenC`（:99、長さ `2h+3`・マッチ数 `m` の着地区間）1 つを残して閉。`PrepBirthLagC'` の残りは台帳恒等式 `value w0.lag = value sF.radius + m` で、着地区間の chain tick が `prepEvents sm dm bs cs` と一致することを言えば `prep_value` で出る。
- 進行中: `CloseoutPackRun48`、`CloseoutPreload41`（replay 節）、`CloseoutWatchRound50`（`WindowEndC`/`ClockOneC`）、`52`。
- **偽だった主張の訂正**: 「fresh clock は found tick にある」→ 着地。「`WatchFreshC` は成り立つ」→ 全区間量化で偽。
- 残: n71 と同じ（watch は着地形への切り直し、oracle は上記一覧）。


## n71 (2026-09-19 未明) 相跨ぎで較正の穴が解消（`h ≤ 681` 不要）・マッチ時計 2 葉が閉じて `final19`

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 2 本登録（`CloseoutWatchRound48`、`CloseoutWatchRound49`）、sorry なし、build ログ `build_n71b.log` EXIT=0。
- **watch（較正の穴を解消）**: `CloseoutWatchRound48`: copy/back 相を複数クロック窓に跨がせる `ChainWatchReachM`（:175）、`reachM_run`（:189）、**`chainWatchReachM_of_background`（:230、跨ぎ回数は無制限、run 長は毎 tick 減る）**。`landing_run`（:126）は窓予算だけで閉じ**クロックが入らん**ので、n68 で問題になった `h ≤ 681` の要求は**消滅**。残 2 葉: `WindowEndC`（:116、`position sT.right + R < |encoded raw|`、旧 `PhaseWindowC` の生き残り）、`ClockOneC`（:159、clock 1 で match なら clock 2048・半径 `R+1` に転送、mismatch なら round 自身の出口 `X`；未閉部分は新規マッチ位置の `BlockOn` と `ChainMatched`（`inc lag`/`inc margin`）を run の残りと可換にすること）。消費側は Round42 の `ReplayBornRoundC` を**半径自由**にした `ReplayBornRoundC'`（:265）に直すだけで、`liveChainRoundC_of_reachM`（:281）が両分岐を同じ経路に流す。
- **watch（マッチ時計）**: `CloseoutWatchRound49`: `fresh_advances_pace`（:61、`2048·#true ≤ length`、`advances_le_compares` + `compare_budget`）、`pace_of_length`（`2048·#true ≤ len ↔ 2047·#true ≤ #false`）、**`watchClockC_of_fresh`（:95、`WatchClockC` 閉）**、**`prepClockC_of_length`（:117、`2048·m ≤ 2h+2` は `2h+3` 版からパリティで無料）**、**`foundExit_compare_final19`**（:141、`WatchClockC` → `WatchFreshC`）。**訂正**: `CloseoutPreload22.ClockInv delay c` は位相 `1 ≤ clock ≤ delay` だけで計数恒等式ではない（`run_invariant` は `#true + clock' = clock + 2048·fires` なので `clock < 2048` だと余分に 1 回 fire できる）→ 新鮮さ `clock = 2048` が本質的に要る。
- **収束**: 残る watch 葉 `WatchFreshC`・`PrepPaceC`・`PrepBirthLagC'` は**全部同じ対象**（found tick から着地までの `WatchSegE`、開始時の時計が fresh）に帰着 → `CloseoutWatchRound51` 進行中。
- 進行中: `CloseoutPackRun48`、`CloseoutOracle5`（`h_oracle_of_leaves'''`）、`CloseoutWatchRound50`（`WindowEndC`/`ClockOneC`）、`51`。
- **偽だった主張の訂正**: 「`ClockInv` から計数不等式が出る」→ 位相だけ、新鮮さが要る。
- 残: pack `hSP`/`hws` 供給 + `Extra7` 残差 2 + `hme`/`hsl`/`hsc`/`hbs`/`hls`/`hC`; readiness `hOP` のみ; watch found→着地 segment + `WindowEndC`/`ClockOneC` + `ReplayBornRoundC'` + tie + `RestartLandingDataC`; core debris 配線・有限制御。


## n70 (2026-09-19 未明) readiness が最後の消費先 `hpres` に接続・`final18`・`0 < lag` は機械と矛盾

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 3 本登録（`CloseoutPackRun47`、`CloseoutWatchRound47`、`CloseoutPreload40`）、sorry なし、build ログ `build_n70c.log` EXIT=0。
- **readiness（接続完了）**: `CloseoutPreload40`: `searchReadyS_of_readyPacedS`、`HpresAt`（:74、chain idle + (`a = true → clock ≤ 1`) + `searchEffect` ⇒ `SearchReady v`）、`searchReadyB_of_readyField3`（:81、`ReadyFieldP3 (n+1)` の scan 状態から）、`hpresAt_along_run`（:100）、`h_oracle_hpres_of_readiness`（:123）。**2 つの構造的事実**: (a) `GalilOracleMC3.h_oracle_of_leaves''` の `hpres` は普遍法則で `GalilLeafPres.hpres_false_at` が反証済み → 状態限定形でしか放電できん、(b) `ReadyPacedS` は `SearchReadyS`（`ReadyRemS = PrepInv ∧ DpSafeStage`）で閉じており `SearchReadyB`（`ReadyRem ∧ RunEntriesAll`）ではないが、`hpres` の結論は素の `SearchReady` なので `DpSafe` 変換は不要。残 `hOP`（`GalilOracleMC3` を点ごとの葉で受ける `h_oracle_of_leaves'''`）→ `CloseoutOracle5` 進行中。これが済めば **readiness 層は `final24` 経路に未解決の消費先を持たん**。
- **pack（訂正）**: `CloseoutPackRun47`: 「`ChainPos.watch` に `0 < value lag` を足す」は**機械と矛盾**（`Outer.immediate` は `zero lag = true` がガード、`lagPos_contradicts_immediate` :91；`take` も `value lag = 1` から lag 0 の `.watch` に落ちる、`take_lag_vanishes` :63）。正しい形は `LagNonneg`（:105）+ **1 セル先の供給**: `consumeAvail_of_next_supply`（:114）は目標側の右ヘッド（そこでの `canR` は `PosPayload2` の場そのもの）から出す。`bgStartP2_of_centre`（:163）で `BgStartP2` を `CentreLedger`（:153、中心ヘッドの present + 半径の**等式**）に還元（`scanGeomR` の `ScanInvariant` は不等式しか与えず、`CentreRep` は rewind/replayStart にガードされてる）。
- **watch**: `CloseoutWatchRound47`: `sumRel_ticks`/`sumRel_internal`（半径台帳の輸送、閉）、**`watchDrainC'_of_clock`**（:119、`m' := es2.count true`、`d1 := 0`）、**`foundExit_compare_final18`**（:166、`hdrain` → `hclock : WatchClockC`）。残 2 葉は同型のマッチ時計事実: `WatchClockC`（`2047·#true ≤ #false`）と `PrepClockC`（`2048·#true ≤ 2h+2`、prep 流の長さは `2h+3`）→ `CloseoutWatchRound49` 進行中。
- 進行中: `CloseoutPackRun48`、`CloseoutOracle5`、`CloseoutWatchRound48`（相跨ぎ）、`49`。
- **偽だった主張の訂正**: 「watching chain は `0 < lag`」→ `immediate` のガードと矛盾。
- 残: pack `hSP`/`hws` 供給 + `Extra7` 残差 2 + `hme`/`hsl`/`hsc`/`hbs`/`hls`/`hC`; readiness `hOP` のみ; watch 相跨ぎ + `ReplayBornRoundC` + マッチ時計 2 葉 + `PrepBirthLagC'` + tie + `RestartLandingDataC`; core debris 配線・有限制御。


## n69 (2026-09-19 未明) `pal_in_peg_final24`（Extra は `scanAvail` のみ、残差 2 つ）・**周期 `h` は非有界**（`ChainWatchPhaseC` の形が誤り）・readiness の tick は残差ゼロ

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 2 本登録（`CloseoutPackRun46`、`CloseoutPreload39`）、sorry なし、build ログ `build_n69b.log` EXIT=0。
- **pack**: `CloseoutPackRun46`: `Extra7`（:70、`scanAvail` のみ）/`Extra8`（`rewindMargin` + `scanAvail`）、読み手を全部再証明（本体不変）、**`pal_in_peg_final24`**（:319）。仮定: `hSP`（`BigPack2MG7` 上）, `hws`, `hee : H_extraEntry7`, `het`（素の `Extra7` tick）, `hme`, `hsl`, `hsc`, `hor : CycleOracleMC3`, `hbs`, `hls`, `hC`。**`ready`/`failed`/`cand` を全部削除した結果、`ReadyFieldP`/`ReadyPacedS`/readiness 連鎖は pack 経路から完全に消滅**。残差はちょうど 2 つ:
  - 入口: `∀ c r, InvLPC w c r → position r.right ≠ 2 * w.length`（右ヘッドの end-of-input）
  - tick: `(mode ≠ scan ∨ clock = 1) → y.mode = scan → y.replaying = false → canRight y.vm.right`（`scan_match` の clock 1、`shift_done`、`replayStart` でのみ発火）
- **watch（較正の訂正）**: scout 調査の結果、**chain の周期 `h` は非有界**（入力とともに伸びる；`found_radius_le_two_period` は半径を周期で抑えるだけで逆は無い、`GalilReplayBudgetProof:19–22`、`GalilReplaySpan:116–118`）。よって `ChainWatchPhaseC`（`CloseoutWatchRound43:120`、copy/back 相が 1 クロック窓 2048 に収まる）は**一般には偽**で、`chainWatchPhaseC_of_window`（Round46:189）が `h ≤ 681` で止まったのは正しい。機械側は問題なく、Scala は 1 tick に 1 `stepCopy`/`stepBack`（`ScaffoldChain.scala:178–187`）で相は複数の比較周期を跨ぐ。→ obligation を跨ぎ可能な形に書き直す（`CloseoutWatchRound48` 進行中: clock 1 の match tick で継続、mismatch なら相を抜けて round 自身の shift/fallback 出口へ）。
- **readiness**: `CloseoutPreload39`: `paced` の idle 条件を外すのは偽（`scan_count` が clock を減らすので凍結ビューでは slack が買えん）。正しいのは **slack 0 の節** `paced0`（比較着地は `clock := 2048` なので常にこれ）: `ReadyFieldP3`（:57）、`readyField3_entry_of_datum`（:75、入口は chain に言及せず free）、`readyField3_background`/`_shift`/**`readyField3_tick`**（:157、残差は `hentry`/`hentry'` のみでどちらも入口定理が点ごとに放電）、`readyField3_along_run`（:244）。**`hact` は消滅**。`Extra.ready` が消えた今、readiness の唯一の消費先は `CycleOracleMC3` の `hpres`（`SearchReadyB`）→ `CloseoutPreload40` 進行中。
- 進行中: `CloseoutPackRun47`（`ChainPos'` + 葉 2–5）、`CloseoutPreload40`、`CloseoutWatchRound47`（prep 輸送・時計台帳）、`48`。
- **偽だった主張の訂正**: 「copy/back 相は 1 クロック窓に収まる」→ 偽（`h` 非有界）。「`paced` の idle 条件は外せる」→ 偽、slack 0 の節に分ける。
- 残: pack `hSP`/`hws` の供給 + 上記 2 残差 + `hme`/`hsl`/`hsc`/`hor`/`hbs`/`hls`/`hC`; readiness `hpres` 接続; watch 相跨ぎ + `ReplayBornRoundC` + prep 2 葉 + tie + `RestartLandingDataC`; core debris 配線・有限制御。


## n68 (2026-09-19 未明) `Extra.ready` も死に場・`hshift` 放電・`ShiftPeriodC` は葉でなかった・`final17`

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 6 本登録（`CloseoutPreload38`、`CloseoutPackRun45`、`CloseoutWatchRound45`、`46`、`CloseoutPackRun44`）、sorry なし、build ログ `build_n68d.log` EXIT=0。
- **pack（監査）**: `CloseoutPackRun45`: **`Extra5.ready`/`Extra6.ready` は `final22` 経路のどのモードでも読まれん**（読み手は `scanAvail` と `rewindMargin` のみ）。`Extra5S`/`Extra6S`（scan/shift 相対 `ready`）、読み手を全部再証明（本体不変）、`extraTick5S_of_readyField2`（`ready` 半分を `readyField2_tick` から）、`pal_in_peg_final23`（:359、仮定の本数・形は final22 と同じ）。**ギャップ**: `readyField2_tick` が要求する `BigPack2M''` は削除済みの DP 場を持つ `Extra3` を含むので `BigPack2MG6S''` から供給できん（pack を使うのは `notInit` 1 点だけ）→ `ready` ごと削除する `Extra7`/`final24`（`CloseoutPackRun46` 進行中）。
- **readiness**: `CloseoutPreload38`: `scan_shift` は比較量子を 1 つ消費し（`hcmp` は `compareFound`）clock を 2048 にするので slack 0 = 比較後の値 → **`hshift` 放電**（`readyField2_shift` :51）、`readyField2_tick'`（:88）、`readyField2_along_run`（:114）。残 `hact`（active chain 時の paced 台帳）は `paced` の idle 条件を外せば消える → `CloseoutPreload39` 進行中。
- **pack（`WatchShiftS` 供給）**: `CloseoutPackRun44`: `position_le_of_represents`（:47）、`consumeAvail_of_supply`（:74、葉 (1) を `LagPos`（watching chain で `0 < lag`）1 つに）、`h_bgP2_of_start`（:126、葉 (2) を `BgStartP2`（source chain idle の場合のみ）に）。`LagPos` は `ChainPos` の watch 節に組み込むのが正しい（`CloseoutPackRun47` 進行中）。
- **watch**: `CloseoutWatchRound45`: **`ShiftPeriodC` は葉でなかった**（`ShiftRoundDataL` の `chain` 場と `remaining` 場から `period_of_beginShift` :81 で導出）、`watchStart_distance_zero`/`_broken_false`（birth では無料）、`PrepBirthLagC'`/`WatchDrainC'` の分割、**`foundExit_compare_final17`**（:219、`LandingFreshC` 消滅）。残 2 葉（prep 区間輸送、時計台帳）→ `CloseoutWatchRound47` 進行中。`CloseoutWatchRound46`: `chainW_true_of_window`（:106、`lim = false` の着地を明示予算 `2|xs| + 4 + (R_head − C)` で `lim = true` に格上げ）、`reach_watch`（:150）で **`n ≤ 2|xs| + 4 + (R_head − C)` が無条件**。残 1 葉 `PhaseWindowC`（:170）: `2|xs| + 4 + d ≤ 2047`。**未解決の較正問題**: `R_f ≤ 2h` はあるが `h` の上界が無く、`h ≤ 681`（= `d ≤ 1363`）が要る。`h` が入力とともに伸びるなら `delay = 2048` 内に copy/back 相が収まらん → Scala で copy/back 相が 1 比較周期に収まるのか、多周期に跨るのかを調査中（scout）。
- 進行中: `CloseoutPackRun46`（`Extra7`）、`47`、`CloseoutPreload39`、`CloseoutWatchRound47`、scout（周期上界と相の跨り）。
- 残: n67 と同じ + 較正（`h` の上界）。


## n67 (2026-09-18 深夜) `pal_in_peg_final22`（DP 関連が経路から消滅）・`ChainPosInv2` で先読み不要・`ChainWatchReachC` は歩数 1 葉

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 3 本登録（`CloseoutWatchRound43`、`CloseoutPackRun41`、`CloseoutPackRun43`）、sorry なし、build ログ `build_n67b.log` EXIT=0。
- **pack（死に場の削除）**: `CloseoutPackRun43`: `Extra5`（:73、`ready` + `scanAvail`）、`Extra6`（:80、`Extra'` − `failed`/`cand`）、`extra6_of_extra5`、読み手を `Extra6` 上で再証明（本体は不変: `lticksN_of_lpackM2_pt6`、`ipackMG2_tick_pt6`、`bigPack2MG6''_tick`、`packRunR_MG26`）、**`pal_in_peg_final22`**（:323）。仮定本数は final20 と同じ（`hSP`, `hws`, `hee`, `het`, `hme`, `hsl`, `hsc`, `hor`, `hbs`, `hls`, `hC`）で `hee`/`het` の形だけ変更、**`DpFieldP` と `H_candOrient` はこの経路から完全に消滅**。残差: `H_extraEntry5` は end-of-input（`pos R ≠ 2|w|`）1 つ、`H_extraTick5P` は `scanAvail` 転送（`scan_match`/`shift_done`/`replayStart` でのみ発火）+ `ready` 転送。**指摘**: `Extra5.ready` は無条件 `SearchReady` だが `ReadyFieldP` は scan 限定なので直結できん → `Extra5S`（scan/shift 相対）で繋ぐ（`CloseoutPackRun45` 進行中）。
- **pack（`WatchShiftS` 供給）**: `CloseoutPackRun41`: `ChainPos z R`（:62、live chain の 3 形それぞれで `canRight ver ∧ Sane ver ∧ pos ver + lag = R`）が Run38 の `SrcPos` を包含し**先読みを不要化**、`chainPos_step`/`chainPos_matched`（`ChainStep`/`ChainMatched` を通す）、`PosPayload2`/`ChainPosInv2`（:215）、`chainPosInv2_tick`（:272、**`shift_one` は無条件で閉**（`right` は `shiftLens` に無い）、init/replayStart/restart/scan_fallback・全 off-mode も閉）、`watchShiftS_of_chainPosInv2`（:357、`H_fourOther` も先読みも不要）。残 5 葉は全部入力供給型: `ConsumeAvail`（移動後 verifier の `canRight`）、`H_bgP2`、`H_matchP2`、`H_shiftEntry2`、`H_shiftDoneRad2`（半径台帳 + `canRight R` のみ）→ `CloseoutPackRun44` 進行中。
- **watch**: `CloseoutWatchRound43`: `chainWatchReachC_of_background`（:215）、`background_chainStep`、`ChainWRun`、`landing_step`（bundle 全転送）、`phase_run`。残 1 葉 `ChainWatchPhaseC`（:120、copy/back → watch の歩数 `n ≤ 2047`）: `lim = false` の `ChainW` は予算節が vacuous なので窓データ（`n ≤ xs.length + 1`、`BlockOn`）から出す → `CloseoutWatchRound46` 進行中。
- 進行中: `CloseoutPackRun44`、`45`、`CloseoutPreload38`（`hshift`）、`CloseoutWatchRound45`（lag 0 再基底化）、`46`。
- 残: pack `hSP`/`hws` の供給 + `Extra5S` 化 + `hplace`/`first ≠ 4`; readiness `hshift` + 帰納組立; watch `ReplayBornRoundC`/`ChainWatchPhaseC`/`PrepBirthLagC'`/`WatchDrainC'`/`ShiftPeriodC`/片 3–6 の L 版/tie/`RestartLandingDataC`; core debris 配線・有限制御。


## n66 (2026-09-18 夜) `Extra3.failed`/`cand` は死に場と確定・`LandingFreshC` 反証・readiness 入口が残差ゼロ

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 3 本登録（`CloseoutPackRun42`、`CloseoutWatchRound44`、`CloseoutPreload37`）、sorry なし、build ログ `build_n66c.log` EXIT=0。
- **pack（重要な監査結果）**: `CloseoutPackRun42`: `Extra4`（`parked` を場に昇格、`failed` を stage 相対形に、`cand` を DP の prefix 向きに）、`extra3_of_extra4`、`H_extraEntry4`/`H_extraTick4P`、`pal_in_peg_final21`（:277、`hO : H_candOrient` 追加）。**ただし監査で `Extra3.failed` と `cand` はどの消費側も読まんことが判明**: `Extra3` は `extra'_of_extra3` 経由でしか消費されず、`Extra'` の読み手（`canR_of_partsM`、`lticksN_of_big6`/`_big6G`/`_lpackM2_pt`、`extra3_scanAvail_tick`）は `scanAvail` と `rewindMargin` しか触らん。DP の実消費は `MismatchDp`（`GalilLeafDp:123`）が自前で `StageFailed` を出して `GalilOracleMC3.hdp` に渡す経路。→ **2 場を削除**する `Extra5`/`final22`（`CloseoutPackRun43` 進行中）で `H_candOrient` と `DpFieldP` の 6 分岐が丸ごと消える見込み。
- **watch（訂正）**: `CloseoutWatchRound44`: **`LandingFreshC`（Round41:151）は偽** — `h` が普遍量化で制約は `beginShiftVM h w' …` だけ（どの `h` でも充足）なので `periodLength w' = h` が `0 = 1` を強制。分割形 `LandingFreshC'`（:82、`h` 自由な転送 3 節）+ `ShiftPeriodC`（:90、`h` を選ぶ側の period 節）、`landingFreshC_of_parts`（:100）。`SumRel (.watch w) R` は `broken = true` で vacuous、さもなくば `distance + lag = R`（`sumRel_watch_broken`/`_of_unbroken`）。`WatchDrainC` は birth での `distance = 0` 節が要り、それは `PrepBirthLagC` 側に載せる。`CloseoutWatchRound45`（再基底化 + `PrepBirthLagC'`/`WatchDrainC'`）進行中。
- **readiness**: `CloseoutPreload37`（再実装）: `ReadyFieldP2 n`（:46、`ready`/`readyS`/`paced`/`shifting`；shift 中は `searchEffect` が発火せんので idle 前提なしで保存）、`readyField2_tick`（:105、fuel は単調 `n ≤ n'`）、**`readyField2_entry_of_datum`（:194、残差ゼロ）**: clock 2048 で `Restarted`/`StageEntry`/`CentreLongRun`/`NoReturn`/`EntryDepthG`/`D ≤ prepLen k` のみから（`readyPacedS_restarted` + `runEntriesS_of_namedG`）、**`ScanRealized`/`PostRunC`/`ScanSupplyInv` 不使用なので vacuous でない**。fuel は `dpEntryG k D`（0 では `not_runEntriesS_eight` で偽）。残 1 葉: `hshift`（`scan_shift` tick、`CloseoutPreload38` 進行中）。
- 進行中: `CloseoutPackRun41`（payload 残差）、`43`（死に場削除）、`CloseoutPreload38`、`CloseoutWatchRound43`（copy/back→watch）、`45`。
- **偽だった主張の訂正**: 「`LandingFreshC` は転送で閉じる」→ `h` の量化で偽、分割要。
- 残: pack `hSP`/`hws`/`Extra5` 化/`hplace`/`first ≠ 4`; readiness `hshift` + 帰納組立; watch `ReplayBornRoundC`/`ChainWatchReachC`/`PrepBirthLagC'`/`WatchDrainC'`/`ShiftPeriodC`/片 3–6 の L 版/tie/`RestartLandingDataC`; core debris 配線・有限制御。


## n65 (2026-09-18 夜) chain ブロック符号化 `chainRepD`（shift 1 手は ≤ 2 手）・replay 生まれ chain は 4 分割が使える

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 3 本登録（`CloseoutWatchRound42`、`CloseoutCoreEnc24`、`CloseoutWatchRound41`）、sorry なし、build ログ `build_n65b.log` EXIT=0。
- **core**: `CloseoutCoreEnc24.chainRepD`（:221、watch chain を `mkChain` で: verifier `viewOfHead`、period テープ、6 カウンタ `lag/margin/h/distance/boundary/last` を `ctrTapeD`（`replicate n mark ++ [sep]` + 符号ビット `ctrPol`、`spare` = distance テープ））、`absChain_chainRepD_watch`（`Canonical` 下で忠実）、**`chainShiftBoundedD`**（:402、実際の上限は **≤ 2 手**、`chainTapes_shift`）、`restC_of_chainRepD`（`restC_of_rep` の形）。`chainShiftOne` が変えるのは `margin/distance/boundary/last` の 4 つだけで各 1 `dec`、コピーも改名も無し。**2 つの残差（いずれも証明不能、要契約修正）**: (1) `ChainShiftBounded chainRep` は `c` を `w` と独立に量化してて偽（実際に使う `c := .watch w` の形のみ真）、(2) debris 無しの関数的 `rep` は不可（mark を pop すると右に blank が残り、削除するマイクロ動作が無い）→ カウンタテープに debris 引数 `d` が要る（`dTape`/`dbg` と同機構）。`Lay`/`shiftVm_tapeActKQ_run` への `d` の配線は `CloseoutCoreEnc23` の編集が要る（次 wave）。
- **watch**: `CloseoutWatchRound42.liveChainRoundC_of_life`（残 `ReplayBornRoundC` + `ChainWatchReachC`）。**発見**: Round23 の 4 分割（`exitSplit4C_of_tick`）は replay 生まれの `.watch` 着地でも **found tick 無しで使える**（入力は `LiveScanWatch` と無条件の `WatchPrefixC` だけ）。found tick が要るのは route 消費側 —`roundsRouteLP_of_tail`/`breakRouteLP_of_tail` が食う `ShiftTailC`/`NoShiftTailC` の頭が「非 replay の found 比較 + `StageEntryC` からの `WatchSegE` + `InvLPC`」で、replay 生まれ chain（birth は `replaying = true` の found 量子、`ChainW` 起点）には偽。DP candidate は再供給可能だが `InvLPC`/stage 入口の根付けは不可 → `ReplayBornRoundC`（replay found 量子を頭にした `ShiftTailC` 類似）。`ChainWatchReachC`（copy/back → watch、機械的）は `CloseoutWatchRound43` 進行中。
- **watch (lag 0)**: `CloseoutWatchRound41`: 大域 `MismatchLandingLagZeroC` は偽なので消費側が実際に到達する着地に制限した `MismatchLandingLagZeroL`(:90) を `mismatchLandingLagZeroL_of_ctx`(:165) で放電、`shiftTailC_of_dataL'`(:215)、**`foundExit_compare_final16`**(:250、`hlag0` 消滅)。`R_f ≤ 2h` は仮定でなく導出（`StageEntryC.stage` → `ReplayStage` → `Restarted`/`StageEntry` → `found_radius_le_two_period`、`h` は `pos 11` で同定）。新たな文脈 3 葉: `PrepBirthLagC`(:115、`FoundCompareCtxC` に載せる)、`WatchDrainC`(:138、`PrepLandingLiveC`)、`LandingFreshC`(:151、`PrepLandingWatchC`) → `CloseoutWatchRound44` 進行中。
- 進行中: `CloseoutPackRun41`（payload 残差）、`42`（`Extra4` → final21）、`CloseoutPreload37`（fuel 付き `ReadyFieldP2`、`ScanRealized` 不使用で再実装）、`CloseoutWatchRound41`（lag 0、検証中）、`43`。
- 残: n64 と同じ + core の debris 引数配線。


## n64 (2026-09-18 夜) `Extra3.failed` は restart 着地で偽（stage 相対形へ）・readiness の消費先は `ReadyFieldP` と `hpres` だけ・replay 中に生まれた chain の round

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 2 本登録（`CloseoutPackRun39`、`CloseoutWatchRound40`）、sorry なし、build ログ `build_n64.log` EXIT=0。
- **pack（訂正）**: `CloseoutPackRun39.DpStage`/`DpFieldP`（scan で `parked`/`pc347`/`stage`、shift で `found`）、`dpField_to_failed`（scan 全状態で無条件）、`dpField_to_cand`（shift 状態で DP の成功 `Candidate`；`Extra3.cand` の形は **prefix/suffix の向き**の差 `H_candOrient` が要る）、`dpField_tick`（`init`/`scan_wait`/`scan_count`（parked search は不活性）閉、残 `hmatch`/`hshiftEntry`/`hshiftOne`/`hshiftDone`/`hreplayStart`/`hrestart`）。**`Extra3.failed` は restart 着地で偽**（`restartVM` が `dp := reset entry`、`pc = entry`；`hpres_false_at` と同型）→ `Extra3.failed` を「parked 後に failed」の stage 相対形に弱める必要。
- **readiness（配線の確定）**: scout の結果、readiness の消費先は `Extra3.ready`（`ReadyFieldP`、普遍 `SearchReady`）と `CycleOracleMC3` の `hpres`（`SearchReadyB`）のみ。`H_stageScan`/`H_bootShift`/`H_landShift` は readiness を読まん。普遍 `PostRunC`/`PostRunPh` は run 帰納から出んので、`postRunC_galil_of_boot` の run 限定 `DpSafeStage`/`EntryDatum` を `ReadyFieldP.hentry`（restart/replayStart 再入の `RunEntriesS`）に接続する（`CloseoutPreload37` 進行中）。
- **watch**: `CloseoutWatchRound40.chainRoundRouteC_of_life`（:131、残 `LiveChainRoundC`）、`chainW_shape`（`.copy ∨ .back ∨ .watch`）、着地から `LiveScanChain`/`OutputRel`/`Leftmost`/`ReplayLanding`/`SpanRep`/中心単調は導出。**発見**: 既存の split/経路（`exitSplit4C_of_tick`、`roundsRouteLP_of_tail`、`fallbackReachS_of_context`、`chain_life`）は全部 found tick 起点（`ShiftTailC`、`InvLPC` からの `foundRouteMC_*`、DP `Candidate` の `watchStart`）で、replay 中に生まれた chain（着地は `InvScan.chainIdle` を満たさん）には直接使えん → `ChainW` chain の copy/back → watch → shift/break の round（`CloseoutWatchRound42` 進行中）。
- 進行中: `CloseoutPackRun41`（payload 残差）、`CloseoutCoreEnc24`（`chainRep`）、`CloseoutWatchRound41`（lag 0 を found 半径予算から）、`42`、`CloseoutPreload37`。
- **偽だった主張の訂正**: 「`Extra3.failed`（`pc = 347`）は全 scan 状態で成立」→ restart 着地で偽。
- 残: n63 と同じ + `Extra3.failed` 弱化 + `H_candOrient` + `DpFieldP` の 6 分岐。


## n63 (2026-09-18 夜) `Coupled'`（sharp `5h`）で `H_fourOther` が定理・core 初期配置 + run 版・lag 0 は found 半径予算経由

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 3 本登録（`CloseoutCoreEnc23`、`CloseoutPackRun40`、`CloseoutWatchRound39`）、sorry なし、build ログ `build_n63b.log` EXIT=0。
- **pack**: `CloseoutPackRun40.Other'`（:56、`periodOnly ∧ 1 ≤ h ∧ (shift → 5h ≤ R+C+Rem) ∧ (¬shift → 5h ≤ R+C)`；shift 出口は `R = R₀+1, C = 0, Rem = h` で fresh guard `4h ≤ R₀` から `k ≤ 5` が上限）、`Coupled'`、**`coupled'_tick`（:127、全分岐無仮定）**、`coupled'_steps`、**`four_of_other'`**（`H_fourOther` の内容が定理）、`ChainPosInv'`、`watchShiftS_of_chainPosInv'`（`H_fourOther` 不要）、`chainPosInv'_tick`（残は Run34 の payload 3 残差のみ → `CloseoutPackRun41` 進行中）。
- **core**: `CloseoutCoreEnc23.laysS_initial`（空 queue で `SBound ∧ SInj ∧ LaysS ∧ RTQueue.Inv`）、`qLay_initial`（`InitialQueues m`）、`restC` は `rep` が未解釈なので `ChainShiftBounded rep`（:177）でしか縛れん（`CloseoutCoreEnc24` で `chainRep` を具体化中）、**`shiftVm_tapeActKQ_run`**（:284、run 添字の配置族 `lay i`/`dbg i`、各段 ≤ K=28、残 head margins）。`TapeActK` 本体（有限制御）は未。
- **watch**: `CloseoutWatchRound39`: `MismatchLandingLagZeroC` は大域では**偽**（`chainStart` が `lag = radius` を種にする; `R_f = 3069, h = 512` で pre-lag 1 の guard 通過着地、`budget_counterexample`）、実着地では真: `pre_lag_le_one`、`watchSegE_zero_lag`、`fresh_phase4_budget`（`4h ≤ R_now`）、`lag_zero_of_budget`（birth lag `R_f + m`、drain ≥ `2047·m' + d1`、prep `2048·m ≤ 2h+2`、**`R_f ≤ 2h`** ⇒ lag 0）、`landing_lag_zero_of_budget`（:182）。`RoundsL` 一般化（24 ファイル再移植）は却下、葉を found 半径上界入力形に（`CloseoutWatchRound41` 進行中）。
- 進行中: `CloseoutPackRun39`（DP 場）、`41`、`CloseoutCoreEnc24`、`CloseoutWatchRound40`（`ChainRoundRouteC`）、`41`、scout（readiness の消費先）。
- **偽だった主張の訂正**: 「live 着地で lag 0 は clock 構造だけから」→ found 半径予算 `R_f ≤ 2h` が要る。
- 残: n62 と同じ、pack は `ChainPosInv` payload 3 残差 + `ShiftLocalS` 再配線、core は `chainRep` + head margins + 有限制御。


## n62 (2026-09-18 夜) **モデル欠陥: chain 誕生で `periodOnly` が `false` に戻らん**（修正保留）・`H_shiftDone` 放電・readiness 帰納 `postRunC_galil_of_boot`

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 2 本登録（`CloseoutPackRun37`、`CloseoutPreload36`）、sorry なし、build ログ `build_n62b.log` EXIT=0。
- **モデル欠陥（要修正、Scala が正本）**: Scala `chain.start()`（`ScaffoldChain.scala:90`）は `periodOnly = false` にするが、Lean の `chainAt`/`chainStart`（`GalilScaffoldTopChainVM.lean:41`、`GalilScaffoldTopSearch.lean:69`）は `s.periodOnly` を触らず、`restartVM`/`replayStartVM` も保持、`beginShiftVM` だけが `true` にする。結果: restart 後の fresh chain は stale `periodOnly = true` で走り、`shiftGuardVM`（`GalilScaffoldTopGuards.lean:27`、`if periodOnly then singlePositive cycle else negative margin = false`）が stale な cycle を見て **Scala なら許す shift を Lean が拒む**、`cycleAfter`（`GalilScaffoldTopSearch.lean:41–42`）も誤って減る。`Fair.keepsSearchCursor`（GalilTickFair:201）は init/replayStart しか pin しない。**最小修正**: `afterCompare`（`GalilScaffoldTopSearch.lean:47`）で chain 誕生（found = true）時に `periodOnly := false`。参照 99 ファイル、壊れやすい補題群: `*shiftGuard*`（9 ファイル）、`*Cycle*`/`cycleAfter`（~10）、`afterCompare`（~7）。**専用 wave で実施**（走行中 agent が古いモデル上なので、完走後に編集 → 全 build → 破損修復）。修正後は `chainRound_tick` の `H_birth` 分岐が vacuous になる。
- **pack**: `CloseoutPackRun37`: `ShiftInv`/`ShiftRound`（shift 相不変量）、`roundScan_of_shiftInv`（尽きたら `RoundScan (C+h) (R+h) h 0`、`terminal_palindrome` 経由、残差なし）、**`h_shiftDone_of_shiftRound`**（`H_shiftDone` 放電）、`shiftInv_entry`/`shiftInv_step`、`shiftRound_tick`（22 分岐、残 `H_advanceT`（終端 consume 後の予測、`mod 2h` 形）、`H_freshShift`（`periodOnly = false` での初回 shift、`GalilScaffoldTopFreshEntry`））。比較中に生まれた chain は phase 0 で guard の phase 4 と矛盾（`chainAt_false_born`）。`H_birth` は上記モデル欠陥そのもの。`ReadsInv`（origin `o`/`extra` で `w0.machine.control = run o.shifted.machine.control extra`）、`h_advance_of_readsInv`（`H_advance` を導出）、`readsInv_immediate`（`scan_match` 段）；残 `shift_done` での `ReadsInv` 入口と `H_advanceT`。
- **readiness**: `CloseoutPreload36.EntryDatum`（`.run` 入口 datum、DP 節不要）、`StageLegs`/`StageChain`、`entryDatum_step`、**`postRunC_galil_of_boot`**（:157、全後続入口で datum + `32 ≤ mw'` + `DpSafeStage`）、`postRunC_galil_of_initial`（`clockInv_initial`）。残: boot datum、`32 ≤ mw0`（`mw0 = 8·max k 1` なので `k ≥ 4`；`k ≤ 3` は最初の 1–2 stage が別扱い）、全流の pacing、stage ごとの供給前提、`RunEntriesS` の組立。**注意**: 普遍形 `PostRunC`/`PostRunPh` は全 `SearchVM` 上の量化なので run 帰納から出ず、`H_stageScan`/`H_bootShift`/`H_landShift` はどれも readiness を消費してへん → readiness の成果がどの最上位仮定に繋がるかを scout で確認中。
- 進行中: `CloseoutPackRun39`（DP 場）、`40`（`Other` 強化）、`CloseoutWatchRound39`（lag 0 判定）、`40`（`ChainRoundRouteC`）、`CloseoutCoreEnc23`（初期配置）、scout（readiness 消費先）。
- 残: n61 と同じ + モデル修正 wave。


## n61 (2026-09-18 夜) `ChainEnd` は「round 完了」でなく「生存」・`ChainPosInv` は残差 3 つ・`H_fourOther` は `WatchOK` から出ない

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 2 本登録（`CloseoutWatchRound38`、`CloseoutPackRun38`）、sorry なし、build ログ `build_n61b.log` EXIT=0。
- **watch（訂正）**: `CloseoutWatchRound38.restartLandingC_of_landing`（:94、`InvLPC` は導出、残 `RestartLandingDataC`（`RadiusRep`/`SpanRep`/`Canonical`/`ReplayStage`/`CostedRun`/右上界；`BrokeAndRestarted` は pre-restart 状態としか結ばれず着地まで `WatchSegE` が届かん））、`chainEndLandingC_of_route`（:162、残 `ChainRoundRouteC`）。**訂正**: `ChainEnd`（GalilReplaySpan:1308）は chain が round を終えたのでなく span 末まで**生存**する（`t.chain ≠ .idle`、`ChainW … B`）。shift/break の場合分けは無く、`roundsRouteLP_of_tail`（`ShiftTailC` は found tick 状態上の契約）では供給できん → 生きた `ChainW` chain の round 経路（着地からのコスト込み）が要る。
- **pack**: `CloseoutPackRun38`: `posPayload_background`（残 `BgRes`: 元 verifier の `Sane`、chain 開始時の head 事実、1-tick 先読み `verNext`）、`posPayload_match`（`pos` は `ChainTick true` を通して閉、残 `MatchRes`: `SrcPos`/`saneR`/`canRNext`/`radNext`/`replayPay`/`verNext`）、`posPayload_shiftDone`（残差 = shift モード状態での payload そのもの、`ChainPosInv` は shift を跨がん → `shift_one` を通す shift モード payload が要る）。**`H_fourOther` は `WatchOK` の帰結でない**（`other_guard_lower`: `2h−1 ≤ distance` が sharp、`R = 2h−1, C = 1` が `Other`+guard を満たす）。機械では未到達の見込み（fresh guard `R ≥ 4h` → shift `−h` → countdown `C: 0→2h→1`、match 中 `R+C` 一定で実 guard は `R ≥ 5h−1`）→ `Other` の `2h` を強めて shift 出口補題を再証明（`CloseoutPackRun40` 進行中）。
- 進行中: `CloseoutPackRun37`（`ChainRound` 誕生）、`39`（`Extra3.cand/failed` の DP 場）、`40`、`CloseoutPreload36`（`PostRunC` 帰納）、`CloseoutWatchRound39`（lag 0 判定）、`CloseoutCoreEnc23`（初期配置・`restC`）。
- **偽だった主張の訂正**: 「`ChainEnd` = chain の round 完了」→ 生存。「`4h ≤ distance` は `WatchOK.Other` から」→ 出ない。
- 残: pack `hSP`（`ChainRound` 4 葉）+ `hws`（`ChainPosInv` 3 残差 + `Other` 強化 + `ShiftLocalS` 再配線）+ `hplace` + `hentry` + `Extra3.cand,failed` + `first ≠ 4`; readiness 帰納組立 + 小窓; watch lag 0 判定 + 片 3–6 の L 版 + tie + `RestartLandingDataC`/`ChainRoundRouteC` + `FallbackCostInputsC`/`RegionBudgetC` + 家族 1–3 の `ShiftRoundAtC`; core 初期配置・`restC`・有限制御。


## n60 (2026-09-18 夜) readiness 帰納段 `postRunF_step` 成立（`32 ≤ mw`）・`ReplayRunW` 無条件・`take` 経路は `Rounds` に乗らん

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 3 本登録（`CloseoutWatchRound36`、`CloseoutWatchRound37`、`CloseoutPreload35`）、sorry なし、build ログ `build_n60c.log` EXIT=0。
- **readiness**: `CloseoutPreload35.dpSafe_of_stagePrepD_slack`（:145、`StagePrepS … slack`、`StageInvS`/`dpDemandS`（`dpDemand + 2` 以下））、`postRunF_round_trip_galil_S`（:301、残 **`32 ≤ mw`**: 追加 2 単位のコスト 8 が slack 2047 で `8 ≤ mw < 32` では吸収できん）、`postRunF_next_entry`（:419、dispatch → prep 脚 → 次 `.run` 入口で frame・`Canonical`・`DpSafeStage`・拡張 `ScanTrace`）、**`postRunF_step`**（:502、`.run` 入口 → 次 `.run` 入口、全脚 `IdleLeg`、`idleLeg_doubleTrace`/`doubleTrace_det`）。残: 帰納の組み立て（boot datum + step → `PostRunPh` → `PostRunC` on `galilFrameS`、`CloseoutPreload36` 進行中）、`RunEntriesS` の wait/double/prep 脚（入口 tick 以外 vacuous）、小窓 `k < 4`。
- **watch**: `CloseoutWatchRound36.ReplayRunW`（:75、replay run / `ChainEnd` / `BrokeAndRestarted` の 3 形）、`replayRunW_of_decodes`（:99、**`ReplayOutC`/`ReplayNoBusyC` 不要**）、`fallbackReachS_of_context'`（`watchFallbackCostC_of_context`/`ReplayRunC` 不要に）、`foundExit_compare_final15`（:246、残 `ChainEndLandingC`（Round15 `roundsRouteLP_of_tail` で供給）・`RestartLandingC`（`invLP_of_landing_replay` + restart 形）、`CloseoutWatchRound38` 進行中）。`CloseoutWatchRound37`: **`ShiftTailC`/`roundsRouteLP_of_tail`/`Rounds.next` は単一 `w` を束縛**するので `take` 経路（`w' ≠ w`）は `Rounds` に乗らん → `MismatchLandingLagZeroC`（:112、live な不一致 shift 着地で lag 0）が新葉、または `Rounds.next` を `Internal w w'` に一般化（`CloseoutWatchRound39` で判定中）。`ShiftRoundInvCL`/`ShiftOriginRestCL`、`shiftBreakRunCL_of_tail`、`shiftOriginCL_of_ctx`、`mismatchShiftRouteL_of_tick`、Round37 版 `foundExit_compare_final15`（:303、仮定: `μ`、`ShiftCopyIdleC`、`ShiftRunCL`、`ShiftRoundInvCL`、`∀h ShiftBreakOracleC`、`∀h ShiftBreakFitC`、`ShiftOriginRestCL`、`MismatchClassifierTieC`、`MismatchLandingLagZeroC`；`ShiftRoundAtC` は家族 1–3 用に残る）。
- 進行中: `CloseoutPackRun37`（`ChainRound` 誕生）、`38`（`ChainPosInv` 残分岐）、`CloseoutPreload36`、`CloseoutWatchRound38`、`39`。
- 残: pack `hSP`（`ChainRound` 4 葉）+ `hws`（`ChainPosInv` 4 葉 + `ShiftLocalS` 再配線）+ `hplace` + `hentry` + `Extra3.cand,failed` + `first ≠ 4`; readiness 帰納組立 + 小窓; watch lag 0 判定 + 片 3–6 の L 版 + tie + `ChainEndLandingC`/`RestartLandingC` + `FallbackCostInputsC`/`RegionBudgetC` + 家族 1–3 の `ShiftRoundAtC`; core 初期配置・`restC`・有限制御。


## n59 (2026-09-18 夕) `pal_in_peg_final20`（`BigResid6G`/`H_packOnRunG`/trace 葉が消滅、pack 残は `hSP`+`hws`）・`ShiftLagZeroC` 反証→`ShiftRoundDataL`

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 2 本登録（`CloseoutWatchRound33`、`CloseoutPackRun36`）、sorry なし、build ログ `build_n59b.log` EXIT=0。
- **pack**: `CloseoutPackRun36.IPackMG2`（:73）= `IPackMG ∧ LPackM2`。`lticksN_of_lpackM2_pt`（:90、`LTickLeavesN` は `BigPack2MG x + LPackM2 x` から**点ごとに**出るので葉でない）、`lTickLeaves2_of_shiftPalG`、`bigPack2MG2''_tick`（rewind-on-FIRST は `replayStart` 着地の `LPackM2` を直接）、§2 trace 層（Run30 §3 の写し）、`h_trailI_MG2`、`H_realizeLIMG2'`（`H_realizeLIMG'` より弱い）、`lpackM2_of_invLPC`、`packRunR_MG2`、`cycleOracleIMG2_of_cycleOracleMC3R`、**`pal_in_peg_final20`**（:712）。仮定: `hSP : ∀ w x, BigPack2MG2 … x → ScanNR x → ShiftPal w x.vm`、`hws : WatchShiftG`、`H_extraEntry3/Tick3`、`H_marksEntry'`、`H_shiftLocalG`、`H_stageScan`、`CycleOracleMC3`、`H_bootShift`、`H_landShift`、`H_realizeLIMG2'`。`hSP` は `ChainRound`（Run31、`CloseoutPackRun37` 進行中）、`hws` は `ChainPosInv`（Run34、`CloseoutPackRun38` 進行中）+ `ShiftLocalS` 再配線が供給元。
- **watch（訂正）**: `CloseoutWatchRound33`: `ShiftLagZeroC` は**偽**（`w.lag = 1` の `Internal.take` で `caught w` が lag 0 で着地し guard を通る；`backDone` で lag が溜まり background tick で 1 ずつ減るので clock 2 で lag 1 → clock-1 compare で lag 1 は到達可能）。`compare_of_take`、`not_shiftLagZeroC`（そういう状態の存在を仮定）、修正データ **`ShiftRoundDataL`**（:129、pre `w`/post `w'`、`Internal w w' ∧ vs.chain = .watch w'`、guard/`beginShiftVM h w'` は `w'` 上）。Round7 の `ShiftRoundData`（従って Round30 `ShiftRoundAtC'`、`ShiftTailC` の旧形）は `take` 経路で到達不能。`ShiftPeriodC` は `h` が消費側（`ShiftTailC`）で存在量化なので `h := periodLength w'` を選べて消滅。`ShiftRoundAtCL'`（:200）、`shiftRoundAtCL_of_tick`（:283、片 3–6 のみ: `ShiftCopyIdleC`、`ShiftRunCL`、`ShiftOriginCL`、`ShiftBreakRunCL`）。`CloseoutWatchRound37`（`ShiftRoundDataL` → `ShiftTailC` → final15）進行中。
- 進行中: `CloseoutPackRun37`、`38`、`CloseoutPreload35`（stage 継続）、`CloseoutWatchRound36`（`ReplayRunW`）、`37`。
- **偽だった主張の訂正**: 「clock-1 不一致で lag は 0」→ 偽（lag 1 の `take`）。
- 残: pack `hSP`（`ChainRound` 4 葉）+ `hws`（`ChainPosInv` 4 葉 + `ShiftLocalS` 再配線）+ `hplace` + `hentry` + `Extra3.cand,failed` + `first ≠ 4`; readiness prepare 継続; watch 片 3–6 の L 版 + tie + `ReplayRunW` + `FallbackCostInputsC`/`RegionBudgetC`; core 初期配置・`restC`・有限制御。


## n58 (2026-09-18 夕) `ShiftPal` は `RoundScan` から（`ReadOrigin` 不要）・`WatchShiftS`/`ShiftLocalS` 再切り出し・break run の iteration 構成

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 3 本登録（`CloseoutWatchRound34`、`CloseoutPackRun31`、`CloseoutPackRun34`）、sorry なし、build ログ `build_n58.log` EXIT=0。
- **pack (`ShiftPal`)**: `CloseoutPackRun31.ChainRound`（:183、watching chain ⇒ `GalilRoundPeriod.RoundScan w C R (periodLength wch) used s wch`、`ReadOrigin` の中身は既にループ不変量に還元済み）、`terminal_palindrome`（:134、終端 `RoundScan` + `canRight` + 予測 = 右記号 ⇒ `PalAt (C+2h) (R+1)`、C と C+h の 2 回鏡映 + `reshift_from_right`）、`shiftPal_of_readOrigin`（:265、`ChainRound` + `WatchShift`（`canRight` のみ使用））。`chainRound_tick`（:340）: init/restart/replayStart・非 scan・`scan_wait/count`（lag 0 の `Internal` は恒等）・`scan_match` 非終端（`roundScan_step`）・終端（chain は `Good` でなく破れる）閉。残: `H_shiftDone`（shift 出口での次 round の誕生 = 本体）、`H_advance`（`roundScan_step` 自身の名前付き仮定、round の `Reads` trace 要）、`H_birth`/`H_fresh`（fresh chain データ；`periodOnly` は `restartVM` でも `false` に戻らんので restart 後の fresh chain は `H_birth` 側）、`H_matched`（matched 目標での `ShiftPal` は導出不能だが `shiftEntry_of_guard` は `¬matched` しか使わん）。`CloseoutPackRun37` 進行中。
- **pack (`WatchShiftS`)**: `CloseoutPackRun34`: `WatchShiftS`（:60、`¬matched ∧ shiftGuardVM` 付き payload）。**消費側は `beginShiftVM'` 目標で guard なしに `ShiftLocalG` を読む**（`halfBound_of_ipackMG`、`shiftVerSane_ptMG`；`beginShiftVM'` は `shiftGuardVM` を含意せん）→ `ShiftLocalS`（:82、全場に `¬matched ∧ shiftGuardVM`）、`shiftLocalS_of_watchShiftS`、`RShiftNextMS`、読み手の再切り出し `halfBound_of_shiftLocalS`/`shiftOrd_tickS`（`scan_shift` は `hmt`/`hg` を持つ）。`PosPayload`（:313）+ `ChainPosInv`（:330、`Coupled` の `sum` が `distance + lag = radius`）、`four_of_freshC`（phase 4 + `FreshC` ⇒ `4h ≤ distance`）、`watchShiftS_of_chainPosInv`（:364）、`chainPosInv_tick`（20/23）。残: `H_fourOther`（post-shift `Other` 半分での `4h ≤ distance`、`guard_budget` は `h ≤ R+1` のみ）、`H_bgP`/`H_matchP`/`H_shiftDoneP`（`CloseoutPackRun38` 進行中）。次: `IPackMG` を `ShiftLocalS` で再々配線（Run30 の鏡像）。
- **watch**: `CloseoutWatchRound34`: 片 6 `shiftBreakRunC_of_tail`: 「欠落 iteration」`rounds_construct_break`（:67、`rounds_construct_of_measure` を `BreakEnd` に制限）を無条件で構成、`BreakEnd` から refresh・broken chain・3 カウンタ（`rounds_break` + `RoundInv.Entry` + `read center ≠ none`）。残 `ShiftRoundInvC`（post-shift 状態の `RoundInv h raw`）、`ShiftBreakOracleC`（`BreakEnd` か測度減少の 1 round、`InputEnd`/`GuardFail` の除外点）、`ShiftBreakFitC`（head 上界 `≤ 2m−1`、Round11 の `hfit`）。片 5 `shiftOriginC_of_ctx`: `RoundInv` から `org`/`Entry` 転送、残 `ShiftOriginRestC`（`org.center = pos sF.center`、`Aligned`（fresh origin、`shifts = 0`）、`pos 11 = h`、period 下界の `HasPeriod (Span …)` 形）。
- 進行中: `CloseoutPackRun36`（`IPackMG2`）、`37`、`38`、`CloseoutPreload35`（stage 継続）、`CloseoutWatchRound33`（lag/period）、`36`（`ReplayRunW`）。
- 残: pack `IPackMG2`/`ShiftLocalS` 再配線 + `ChainRound` 4 葉 + `ChainPosInv` 4 葉 + `hplace` + `hentry` + `Extra3.cand,failed` + `first ≠ 4`; readiness prepare 継続; watch 片 1/2 + `ShiftRoundInvC`/`ShiftBreakOracleC`/`ShiftBreakFitC`/`ShiftOriginRestC` + tie + `ReplayRunW` + `FallbackCostInputsC`/`RegionBudgetC`; core 初期配置・`restC`・有限制御。


## n57 (2026-09-18 夕) readiness 往復が `galilFrameS` 上で自前仮定のみに・`ReplayNoBusyC` は偽（replay 中も chain は始まる）

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 2 本登録（`CloseoutPreload34`、`CloseoutWatchRound35`）、sorry なし、build ログ `build_n57b.log` EXIT=0。
- **readiness**: `CloseoutPreload34.exitNotFire_of_wait`（:163）: wait 脚が空でなければ最後の tick は `true`（`idleLeg_wait_last`）で clock := 2048（`scanTrace_single_true_clock`）、空なら run 出口 tick 自体が fire（`run_exit_wait_match`: `finish` は `zero debt = false` でしか `.wait` に入らん）。**`postRunF_round_trip_galil'`**（:199）: `.run→.wait→.double→dispatch` が `galilFrameS` 上で往復の自前仮定のみ。次: `prepare → 次 .run 入口`（`dpSafe_of_stagePrepD` を slack 2047 で言い直し、`PostRunF` datum の再成立 = 帰納段、`CloseoutPreload35` 進行中）。
- **watch（訂正）**: `CloseoutWatchRound35.replayOutC_of_landing`（:61、無条件: `ReplayLanding.rest` の半径 0 `ScanInvariant` + `watchSegE_right_position/center` で `count true = R > 0`、`watchSegE_outputM`）。**`ReplayNoBusyC` は一般に偽**: shift は replay 中無効（Scala `ScaffoldGalil.scala:270`、Lean `scan_shift.hr`）だが、watch chain は found 量子で `chain.start()`（Scala `:226-228`、Lean `compareFound`/`backgroundS` の `chainAt … (mode = .found)`）に `replaying` guard がなく、replay 中に chain が始まる。Lean/Scala の乖離ではない。`ReplayNoShiftC`（:85、replay 中の tick は scan に留まる）は無条件。→ `replayRunC_of_decodes` は replay 定理の 3 分岐（replay run / `ChainEnd` / `BrokeAndRestarted`）全部を消費する形に（`ReplayRunW`、`CloseoutWatchRound36` 進行中）。
- 進行中: `CloseoutPackRun31`（`ShiftPal`）、`34`（`WatchShiftS`）、`36`（`IPackMG2`）、`CloseoutPreload35`、`CloseoutWatchRound33`（lag/period）、`34`（片 5/6）、`36`。
- **偽だった主張の訂正**: 「replay 中は chain が始まらん（`ReplayNoBusyC`）」→ 偽。
- 残: n56 と同じ、readiness は prepare 継続のみ、watch は `ReplayRunW` + 片 1/2/5/6 + tie + `FallbackCostInputsC`/`RegionBudgetC`。


## n56 (2026-09-18 午後) R>0 の watch fallback は存在（`ReplayedLandingRestartC` 反証）→ `FoundExitLPS`・`final14`・`final19`

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 3 本登録（`CloseoutWatchRound32`、`CloseoutWatchRound31`、`CloseoutPackRun35`）、sorry なし、build ログ `build_n56c.log` EXIT=0。
- **watch（訂正）**: `CloseoutWatchRound31`: 判定 (B)。`chosenRadius` は右ヘッドで終わる最長奇回文で chain と無関係、Scala は watch 中 `canShift ∧ prediction == right.read()` が破れたら常に fallback → 反例 `c·(abb)^8·a` + `a`（chain h=3 phase 4、予測 `b ≠ a`、encoded 接尾辞 `a#a` で R=1）。`replayedLanding_not_restart`（:180、R>0 着地 + `ReplayRun` + `LandingRestart` → False、`Rad = R`、`last = reset` で `3R ≤ 0`）、`replayedLandingRestartC_iff`。代わりに **`FoundExitLPS`**（:230、`InvLPS` 着地 + 中心前進）、`cycleOutMC3_of_foundExitLPS`（`cycleOutMC3_of_centre` で消費可）、`FallbackReachS`/`fallbackReachS_of_context`（R>0 枝は `InvLPS`: `InvLP` + `CopyPack` + `CentreRep` + `ReplayStage`）、**`foundExit_compare_final14`**（:377、着地側の仮定なし）、`_of_context`。残る上流: `WatchMismatchNoShiftC`（Round23 で放電済）、`EntryCostC`（Round26 閉）、`FallbackCostPieceC`/`ReplayRunC`（Round28: `FallbackCostInputsC`/`RegionBudgetC`/`ReplayOutC`/`ReplayNoBusyC`、`CloseoutWatchRound35` 進行中）。`CloseoutWatchRound32`: 片 1 は tick から出ない（`watch_after_compare`: lag 正なら `Internal.take` で `caught w`）→ `ShiftLagZeroC`；片 2 は `h` が外部固定 → `ShiftPeriodC`；片 3 `shiftCopyIdleC_of_copyPack`、片 4 `shiftRunC_of_scanInv`（`ShiftScanInvC`）。`CloseoutWatchRound33`（lag/period）・`34`（片 5/6）進行中。
- **pack**: `CloseoutPackRun35.lpackM2_at_traceG`（trace 上の `LPackM2`、`TraceLeaves = LTickLeavesN ∧ AuxPack ∧ ShiftPal`）、`pal_in_peg_final19`（:114、`hall` → `hLv` + `H_packOnRunG`）。**`H_packOnRunG` は循環**（pack 状態は `CycleOracleIMG` の任意 `InvLPC` 起点の run、trace はそこから作る）→ 非循環案 `IPackMG2 := IPackMG ∧ LPackM2` を run pack に持ち込む再配線（`CloseoutPackRun36` 進行中、final20）。
- 進行中: `CloseoutPackRun31`（`ShiftPal`）、`34`（`WatchShiftS`）、`36`、`CloseoutPreload34`（`H_exitNotFire`）、`CloseoutWatchRound33/34/35`。
- **偽だった主張の訂正**: 「watch 不一致からの fallback は R=0」→ 偽（R>0 あり）。「`hall` は trace 限定で消える」→ 循環。
- 残: pack `IPackMG2` 再配線 + `ShiftPal` + `WatchShiftS` + `hplace` + `hentry` + `Extra3.cand,failed` + `first ≠ 4`; readiness `H_exitNotFire` + prepare 継続; watch 片 1/2/5/6 + tie + replay/cost 4 葉; core 初期配置・`restC`・有限制御。


## n55 (2026-09-18 午後) `pal_in_peg_final18`（`BigResid6G` 消滅）・`LegsCoupled` 放電・`WalkerInOrigin` 全分岐保存

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 4 本登録（`CloseoutPackRun32`、`CloseoutPreload33`、`CloseoutPackRun33`、`CloseoutPackRun28`）、sorry なし、build ログ `build_n55c.log` EXIT=0。
- **pack**: `CloseoutPackRun33.bigResid6G_of_lpackM2`（:101、5 契約を `BigPack2MG` 上で同じスクリプトで再証明、どれも `ShiftLocal.mode` を読まん）、**`pal_in_peg_final18`**（:126）。仮定: `hall : ∀ w x, BigPack2MG … x → LPackM2 w x.ctl x.vm`、`hws : ∀ w y, WatchShiftG …`、`H_extraEntry3/Tick3`、`H_marksEntry'`、`H_shiftLocalG`、`H_stageScan`、`CycleOracleMC3`、`H_bootShift`、`H_landShift`、`H_realizeLIMG'`。`hall` は trace 状態への限定で消せる見込み（`CloseoutPackRun35` 進行中）。`CloseoutPackRun32`: `ChainScanInv`/`chainScanInv_tick`（19/23）、`WatchShiftG` は無ガード目標で偽（`backDone` 直後 distance = 0）→ `shiftGuardVM` 目標に限定した `WatchShiftS` + 位置不変量 `ChainPosInv`（`CloseoutPackRun34` 進行中）。`CloseoutPackRun28`: `WalkerInv`（init/Bounded/Fresh の 3 相、`replayStart` は R を左へ動かすので `Fresh` 相が要る）、`walkerInv_tick`（全 26 分岐）、`walkerInv_of_fair`、**`walkerInOrigin_of_run`**（`wpack_of_fair` の `hwalk` そのもの）。残: `hplace : |stream (place s)| ≤ pos R`（`placeC` なら `C ≤ R`）、`2 ≤ delay`（2048 で真）、replaying 中の `canRight R`。
- **readiness**: `CloseoutPreload33.legsCoupled_galil`（:240）: `IdleLeg`（chain idle・search mode 付き 1-tick `ScanTrace` の列）、`scanTrace_single_searchStep`（per-tick 結合、`tick_scan_cases`）、`idleLeg_runTrace`/`idleLeg_waitTrace`、`scanTrace_append`、`RestartOnBroken`（`sharedC` で放電）。`postRunF_round_trip_galil`（:267、4 脚の `SearchVM` は `searchLens.get` で導出）。残 **`H_exitNotFire : p3.ctl.clock ≠ 1`** 1 つ（`CloseoutPreload34` 進行中）。
- 進行中: `CloseoutPackRun31`（`ShiftPal`）、`34`（`WatchShiftS`）、`35`（`hall` → final19）、`CloseoutPreload34`、`CloseoutWatchRound31`（R>0 判定）、`32`（`ShiftRoundAtC'` 片 1–4）。
- 残: pack `hall`/`ShiftPal`/`WatchShiftS`/`hplace`/`hentry`/`Extra3.cand,failed`/`first ≠ 4`; readiness `H_exitNotFire` + prepare 継続; watch 6 片 + tie + R>0 + replay/cost 4 葉; core 初期配置・`restC`・有限制御。


## n54 (2026-09-18 午後) `pal_in_peg_final17`（ガード付き `IPackMG` で全層再配線、追加ガード不要）・`ShiftRoundAtC'` producer 骨格

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 2 本登録（`CloseoutWatchRound30`、`CloseoutPackRun30`）、sorry なし、build ログ `build_n54b.log` EXIT=0。
- **pack**: `CloseoutPackRun30`: `IPackMG`（`shift : ShiftLocalG`）、`BigPack2MG`/`BigPack2MG''`、`BigResid6G`（5 契約は `BigPack2MG` 上、`rShiftNext : RShiftNextMG` は `∀ y, WatchShiftG y` で閉）、`lpackN_tickG`、`bigPack2MG''_tick`、`packRunR_MG`、trace 層 `StepsIMG/ReachAtIMG/CycleOutIMG/CycleOracleIMG/PreTraceIMG`、trail `halfBound_of_ipackMG`（`ScanNR` 付き）・`shiftOrd_ptG`/`verSane_ptG`・`h_trailI_MG`、`H_realizeLIMG'`、**`pal_in_peg_final17`**（:848）。仮定: `BigResid6G`, `H_extraEntry3/Tick3`, `H_marksEntry'`, `H_shiftLocalG`, `H_stageScan`, `CycleOracleMC3`, `H_bootShift`, `H_landShift`, `H_realizeLIMG'`。`.shift.*` を非 scan 状態で読む trace 補題は無い。`BigResid6G` は `BigResid6` から出ない → `bigResid6G_of_lpackM2`（`CloseoutPackRun33` 進行中）。
- **pack (`WatchShiftG`)**: `CloseoutPackRun32`（未登録、次 build）: `ChainScanInv`（一歩先の watch に対する `WatchPayload`）、`watchShiftG_of_chainScanInv`、`chainScanInv_tick`（19/23 閉、残 `H_bg`/`H_match`/`H_shiftDone`）。**発見**: `WatchShiftG` は無ガードの目標で偽（`backDone` で生まれた watch は distance = reset = 0 なので次の比較で `4h ≤ distance` が破れる）→ payload を `shiftGuardVM` 目標（phase 4, lag 0）に限定する再切り出しが要る。その上で位置不変量（`distance + lag = radius`、verifier = `pos right − lag`）。
- **watch**: `CloseoutWatchRound30.ShiftRoundAtC'`（:75、トリガー = frame の compare での post-compare guard）、`shiftRoundAtC'_of_tick`（:170、6 片: `ShiftChainStableC`（`ShiftRoundData` が post-tick chain を `w` のまま束縛する設計問題）、`ShiftPeriodC`、`ShiftCopyIdleC`、`ShiftRunC`、`ShiftOriginC`、`ShiftBreakRunC`）、`mismatchShiftRouteC'_of_shiftRoundAtC'`（残 `MismatchClassifierTieC`）、`foundExit_compare_final13'`。`CloseoutWatchRound32`（片 1–4）進行中。
- 進行中: `CloseoutPackRun28`（`WalkerInOrigin`、コンパイル待ち）、`31`（`ShiftPal`）、`33`、`CloseoutPreload33`（`LegsCoupled`）、`CloseoutWatchRound31`（R>0 判定）、`32`。
- **偽だった主張の訂正**: 「`WatchShift(G)` は無条件で全 compare 目標に成立」→ `backDone` 直後で偽、`shiftGuardVM` 目標に限定要。
- 残: pack `BigResid6G` 組立 + `ShiftPal` + `WatchShiftG` 再切り出し + `WalkerInOrigin` + `hentry` + `Extra3.cand/failed` + `first ≠ 4`; readiness `LegsCoupled` + prepare 継続; watch 6 片 + tie + R>0 + replay/cost 4 葉; core 初期配置・`restC`・有限制御。


## n53 (2026-09-18 午後) `BigResid6` は `LPackM2`-on-pack + `WatchShift` だけで組めた

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 1 本登録（`CloseoutPackRun29`）、sorry なし、build ログ `build_n53.log` EXIT=0。
- **pack**: `CloseoutPackRun29.bigResid6_of_lpackM2`（:143）: `BigResid6` を `∀ x, BigPack2M x → LPackM2 …` と `∀ y, WatchShift y` のみから（Run19/20/21/23/24 の断片を合成）。`shiftEntry_of_guard`（:94）: `ShiftGeom` の heads/`Sane`/positions/`remaining` は pack から、回文本体は `ShiftPal`（:82、`1 ≤ h ≤ r₀+1 ∧ PalAt (pos C + h) (r₀+1−h)`、`reshift_palindrome` の中身だが `ReadOrigin`/`OnlyScan`/`Trace` の round データが要る）1 葉；`lTickLeaves2_of_shiftPal`。`lpackM2_on_pack_of_run`（:171）は葉の毎状態成立と `H_packOnRun`（`BigPack2M` 状態は run 上のどれかの `st i`）を要る；`bigResid6_of_run`。
- 進行中: `CloseoutPackRun28`（`WalkerInOrigin`）、`30`（`IPackMG` 再配線 → final17）、`31`（`ShiftPal` via `ChainRound`）、`32`（`WatchShiftG` via `ChainScanInv`）、`CloseoutPreload33`（`LegsCoupled` on `galilFrameS`）、`CloseoutWatchRound30`（`ShiftRoundAtC'` producer）、`31`（R>0 fallback 判定）。
- 残: n52 と同じ、pack は `ShiftPal` + `WatchShift(G)` + `H_packOnRun` + `IPackMG`。


## n52 (2026-09-18 午後) **訂正: `ShiftLocal` は shift 着地で偽**（`ShiftLocalG` へ）・`final13`（`hLR` 消滅）・`Canonical` 閉・`ReplayRunC`/`FallbackCostPieceC`

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 5 本登録（`CloseoutPackRun26/27`、`CloseoutWatchRound28/29`、`CloseoutPreload32`）、sorry なし、build ログ `build_n52b.log` EXIT=0。429 で落ちた 8 agent は SendMessage で再開して全部完走。
- **pack（訂正）**: `CloseoutPackRun26`: `ShiftLocal` は**反証**。全 `scan→shift` tick は chain `.watch (immediate w)`, `zero w.lag` で着地し（`shift_landing`）`Internal.idle` が有効（`internal_enabled_at_landing`）、heads 不一致なら `afterMismatch` が `compareFound` 目標でその watch を保つ（`compare_watch_target`）ので `ShiftLocal.mode` は偽（`shiftLocal_false_at_landing` :148、pack 仮定なし）、`watchShift_false_at_landing`。修正: `ShiftLocalG`（:197、4 場を `ScanNR := mode = scan ∧ replaying = false` でガード、`mode` 場は削除）、`WatchShiftG`、`rShiftNextG_of_pack`、`RShiftNextG`、橋 `shiftLocal_of_shiftLocalG`/`h_shiftLocalC_of_G`、ガード付き tick 複製 `shiftOrd_tickG`/`saneTickG`。**`pal_in_peg_final16`**（:523）: `hsl : H_shiftLocalG`（他は final15 と同一）。ただし `BigResid6.rShiftNext` は未ガードのまま（`IPackM.shift : ShiftLocal` が `StepsIM/ReachAtIM/CycleOracleIM/PreTraceIM`（Run10/12/14/18）と `shiftEntry_ptM/shiftVerSane_ptM/halfBound_of_ipackM` に直結）→ `IPackMG` 再配線を `CloseoutPackRun30` で進行中。`CloseoutPackRun27`: `ReadyFieldP`（`ready` + chain idle 時の `ReadyPacedS … 0 (2048−clock)`、slack はクロックが補充）、`readyField_tick`（`scan_wait/count/match`、`init` 閉）、残 `hentry`（`restart`/`replayStart`/`shift_done` 再入で `RunEntriesS` = `readyPacedS_restarted` の `hE`、**readiness との接続点**）。
- **watch**: `CloseoutWatchRound29`: `LandingRestartReachF`（fallback 枝のみ）、`landingRestartReach_fallback`（R=0 無条件）、消費側の `hLR` 依存は fallback 枝のみと確認、**`foundExit_compare_final13`**（:264、`hfb`+`hLR` → `hfbF`）。残 `ReplayedLandingRestartC`（R>0 の post-replay 着地は `InvScan` で `Restarted` は `3R ≤ 0` を強制 → 怪しい；`CloseoutWatchRound31` で R=0 か `FoundExitLPS` かを判定中）。`CloseoutWatchRound28`: `replayRunC_of_decodes`（残 `ReplayOutC`（replay 着地の `OutputRel`）、`ReplayNoBusyC`（`¬ChainEnd ∧ ¬BrokeAndRestarted`、replay 中の found tick が chain を生むので着地データでは除外不能））、`fallbackCostPieceC_of_inputs`（`costedRun_fallback_replay` を R 一様に、残 `FallbackCostInputsC`（供給元: `FoundCompareCtxC`/`fallback_landing_len_le`/`PrepInputsG3`/`MismatchDp`/replay 分岐 1）、`RegionBudgetC`（`GalilOracleMC4` の `≤ 2m−2`）、`1 ≤ m`）。`CloseoutWatchRound30`（`ShiftRoundAtC'` producer）進行中。
- **readiness**: `CloseoutPreload32`: `canonical_runTrace`/`canonical_waitTrace` 閉（`safeCalls_debt` + `dec_canonical`）、`postRunF_round_trip'`（:143、残 `LegsCoupled` :117 = `a2 = false ∧ ScanTrace` の 4 脚延長；generic frame では `State σ → SearchVM` がないので `galilFrameS` 上の per-tick 結合 `background_event_false`/`compare_event_false_of_mismatch` からしか出ない → `CloseoutPreload33` 進行中）。
- **compact 前の agent の完走**: `GalilLeafDp`（`hdp` の ∀ 形は反証、`StageFailed` へ；登録済み）、`CloseoutCoreStep`（M3、登録済み）。
- **偽だった主張の訂正**: 「`ShiftLocal`（`mode = scan` 場付き）は tick で保存される」→ shift 着地で偽。「`ReplayedLandingRestartC` は着地から出る」→ R>0 では `3R ≤ 0` を強制、要判定。
- 残: pack `IPackMG` 再配線 + `shiftEntry` + `WalkerInOrigin` + `hentry` + `Extra3.cand/failed` + `first ≠ 4`; readiness `LegsCoupled` + prepare 継続; watch `ShiftRoundData` producer + `ReplayedLandingRestartC` 判定 + `ReplayOutC`/`ReplayNoBusyC`/`FallbackCostInputsC`/`RegionBudgetC`; core 初期配置・`restC`・有限制御。


## n51 (2026-09-18 未明) `LPackM2` で `BigResid6` の 4 契約が閉（shift 入口 1 葉）・`PostRunF` 往復・`EntryCostC` 閉

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 4 本登録（`CloseoutWatchRound26`、`CloseoutPreload31`、`CloseoutPackRun23`、`CloseoutWatchRound27`）、sorry なし、build ログ `build_n51c.log` EXIT=0。
- **pack**: `CloseoutPackRun23.LPackM2`（:99）= `LPackM` + `scanGeomR` + `shiftGeom`（`ShiftGeom` :87、round 進行中の幾何: `remaining = ofNat rem`、目的中心 `pos C + rem` 相対の heads、`PalAt`）+ `rrep`（`OffScan` モード shift…choose）+ `centreRep`（rewind ∨ replayStart）+ `centreOrder`（rewind で `pos L ≤ pos C`）。`lpackM2_tick`（:173、全 23 分岐、`LPackM` 半分は `lpackN_tick` 再利用）: `scanGeomR`/`rrep`/`centreRep`/`centreOrder` は全 tick **無条件**、`shiftGeom` は `shift_one`/出口閉、**唯一の葉 `LTickLeaves2.shiftEntry`**（:150、`scan_shift` 着地での `ShiftGeom` = `reshift_palindrome` at 中心 `pos C + periodLength`、半径 `radius+1−periodLength`）。`lpackM2_boot`（無条件）、`lpackM2_steps`。契約: `scanGeomReplay_of_lpackM2`/`shiftDoneGeom_of_lpackM2`/`rrepChoose_of_lpackM2`/`centreReplay_of_lpackM2`（:447–470）で `H_scanGeomReplay`/`H_shiftDoneGeom`/`RRepChoose`/`H_centreReplay` 全放電。→ `BigResid6` は `LPackM2`-on-pack + `WatchShift` + `shiftEntry` に（`CloseoutPackRun29` で組み立て中）。
- **readiness**: `CloseoutPreload31.PostRunF`（:64、`PostRunPh` + `.run` 入口 frame + 到達可能 `ScanTrace` 位相節、`ScanRealized` なし）、`postRunF_of_postRunPh`、**`postRunF_round_trip`**（:110、`.run→.wait→.double→dispatch` で `PrepAt ∧ StageInvD ∧ walker = c' ∧ 8·max k 1 ≤ 2mw`、`hbal` 導出済み）。残: `hsc`（run+wait 脚上の `ScanTrace` 延長、機械事実）、`hs2`（wait 出口 tick は false）、`hcan1/hcan0`（`Canonical` 保存）→ `CloseoutPreload32` 進行中。`postRunC_of_postRunF` は不成立（`PostRunC` の `.run` 状態に frame がない）。続き: `prepare → 次 .run 入口`（`StagePrep2` の `PacedL 2048 0` を slack 2047 で言い直す）。
- **watch**: `CloseoutWatchRound26.entryCostC_of_ctx`（:44）: `EntryCostC` 閉（`FoundCompareCtxC` + 入口の `EntryCounters`/`OutputRel`/`clock ≤ 2048`）。`CloseoutWatchRound27`: `¬MismatchGuardFails` の witness `vs` は `vs.right` が自由で `compare_scan_unique` に結べん → frame の compare で量化する `MismatchGuardFailsC`（:79）、`guard_of_mismatchShift`（:97、post-compare 状態での guard + `beginShiftVM'` 発火）。**発見: `ShiftRoundAtC`（Round7:384）は木のどこにも producer がない名前付き契約**。pre-compare の `shiftGuardVM s1` は post-compare guard から導出不能（chain 状態と `read s1.right` vs `read (right s1.right)` が違う）→ `ShiftRoundAtC` を post-compare guard で言い直して `ShiftRoundData` の producer を作るのが正道（`CloseoutWatchRound30` 進行中）。
- 進行中: `CloseoutPackRun26`（`ShiftLocal` ガード）、`27`（予算付き ready）、`28`（`WalkerInOrigin`）、`29`（`shiftEntry` + `bigResid6_of_lpackM2`）、`CloseoutPreload32`、`CloseoutWatchRound28`（`ReplayRunC`/コスト片）、`29`（`LandingRestartReach`）、`30`。
- 残: pack `shiftEntry` + `WatchShift` + `WalkerInOrigin` + `Extra3` 3 場 + `first ≠ 4`; readiness `hsc/hs2/hcan` + prepare 継続; watch `ShiftRoundData` producer + `FallbackCostPieceC`/`ReplayRunC` + `LandingRestartReach`; core 初期配置・`restC`・有限制御。


## n50 (2026-09-18 未明) `foundExit_compare_final12`（4 分割消費）・`WindowInOrigin` は search cursor 不変量 `WalkerInOrigin` に

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 2 本登録（`CloseoutWatchRound25`、`CloseoutPackRun25`）、sorry なし、build ログ `build_n50b.log` EXIT=0。
- **watch**: `CloseoutWatchRound25.foundExit_compare_final12`（:173）: `final11` の仮定 + `MismatchShiftRouteC` のみ、`exitSplit4C_of_tick` + `watchPrefixC_of_unique` で分割、家族 1–3 は定数 `ExitSplit3C` で `final9` へ、家族 4 は `mismatchShift_tick`（:100、`¬MismatchGuardFails` から guard 通過の disabled tick が存在し `beginShiftVM'` が発火）→ `mismatchShift_to_shiftRoute`（:136、`ShiftTailC` へ）→ `roundsRouteLP_of_tail` → `roundsExit_of_LP` → `foundExit_of_compare3`。`WatchPrefixC`・`WatchMismatchNoShiftC` は放電済み。残 `MismatchShiftRouteC`（:120、`ShiftRoundAtC` のトリガーを不一致 shift 着地の記録に置換した形；`shiftGuardVM s1` は着地で読み、記録された guard は `afterMismatch s1 vs vq` 上で読むので、`vs` を frame の `compare` に `compare_scan_unique` で結ぶ必要；`CloseoutWatchRound27` 進行中）。
- **pack**: `CloseoutPackRun25`: `Fair.fallbackPlace` は `t.fpp.walker = t.walker`（search 副プロセス自身の cursor）であって `stream (P.place s)` ではない。`windowInOrigin_of_fair`（:56、`WalkerInOrigin y.vm` から 1 rewrite）、`windowInOrigin_left`、`windowInOrigin_tick`、`FairSteps`、`wpack_of_fair`（:120、`hwalk : FairSteps 到達可能な copy 状態で WalkerInOrigin`）。残 `WalkerInOrigin s := |stream s.walker| ≤ pos R`: search 副プロセスの不変量（boot で `emptyPlace`、init/replayStart は `Fair.keepsSearchCursor`、`prepare` で `walker := center = P.place s` かつ `|stream (P.place s)| ≤ pos R`、以後左へのみ、R は右へのみ）→ `CloseoutPackRun28` 進行中。
- 進行中: `CloseoutPackRun23`（`LPackM2`）、`26`（`ShiftLocal` ガード判定 + `final16`）、`27`（予算付き ready）、`28`、`CloseoutPreload31`（`PostRunF`）、`CloseoutWatchRound26`（`EntryCostC`）、`27`（`MismatchShiftRouteC`）。
- 残: n49 と同じ、watch は `MismatchShiftRouteC` + コスト 3 葉 + `LandingRestartReach`、pack は `WalkerInOrigin`。


## n49 (2026-09-18 未明) **訂正: `ScanRealized` は `ScanSupplyInv` と矛盾（Preload24〜29 の `hreal` 定理は vacuous）**・`Extra3` 部分閉・watch コスト閉包 3 葉

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 3 本登録（`CloseoutPreload30`、`CloseoutPackRun22`、`CloseoutWatchRound24`）、sorry なし、build ログ `build_n49b.log` EXIT=0。
- **readiness（訂正）**: `CloseoutPreload30.scanRealized_absurd`（:72）: `ScanSupplyInv F 2048 I → ScanRealized F I → False`。`ScanRealized` は全 `bs : List Bool` を量化しており、`prefixPhase_of_scan_inv` で任意脚が `PrefixPhase`（`len ≤ 2048·count + 2047`）になるが `bs = replicate 2048 false` で破れる。**結果: `hreal` を取る全定理（Preload24 `runEntriesS_of_stageInv2C`…`round_trip_entries`、Preload28 `runEntriesS_of_stageInvD`/`_double_exitD`、Preload29 `postRunD_of_machine(_galil)`）は vacuous**。n45〜n47 の「readiness は `ScanRealized` 1 つ」「9 割」は過大評価。正直な置き換え: `PostRunPh`（:102、`PostRunP` を slack 2047 で、prep 接頭辞の `PrefixPhase` は**到達可能**な接頭辞のみ）、`postRunPh_of_postRunP`/`postRunC_of_postRunPh`（実現性節なし）。`.found`/`.missed` 出口は閉（吸収）。`.wait→.double→prepare` の往復は `PostRunC` の前提から合成できない: (1) `DpSafeStage` に frame（`span = ofNat mw`, `lower = ofNat k`, 較正, DP preload）がない、(2) `.double` 出口の流れは接尾辞なので slack ≤ 2047 に 4 脚分の `ScanTrace` クロック事実が要る。`runP_exit_debt_at_exit_scan` は無傷。次: `PostRunF`（framed・到達可能接頭辞、`CloseoutPreload31` 進行中）。
- **pack (`Extra3`)**: `CloseoutPackRun22`: entry は `ready`/`cand` 閉、`scanAvail` は原点で `pos R ≠ 2|w|` 1 事実、`failed` は DP テープ（`pc = 347`）の事実で `InvLPC` 外。tick は pack 相対形 `H_extraTick3P`（`BigPack2M'' x → Tick x y → Extra3 y`、`bigPack2M''_tick` が実際に使う形）: `scanAvail` は `scan_match`（次の入力文字の到着 = 動いた R での `canRight`）と `shift_done`/`replayStart` 再入以外閉；`ready` は `scan_count`/`scan_match` で bare `SearchReady` が既知の偽 `hpres` → 予算付き `SearchReadyS`/`ReadyPacedS` を pack に要；`cand` は `scan_shift`（`shiftGuardVM` から `Candidate` の producer なし）；`failed` は DP テープ。
- **watch**: `CloseoutWatchRound24.watchFallbackCostC_of_context`（:189）: `WatchFallbackCostC` を `EntryCostC`（stage 入口→着地の costed run、`FoundCompareCtxC` の `WatchSegE` + found tick から）、`FallbackCostPieceC`（`costedRun_fallback_replay/zero` の出力形、DP `Result`/`hlow`/`chosenRadius`/`hfb` + `GalilOracleMC4` 区間予算が入力）、`ReplayRunC`（`replay_after_fallback_general''_R_of_decodes` の第 1 分岐）の 3 葉に。run 連結・cost 合成・centre 上界・R>0 の `InvLP` は閉。
- 進行中: `CloseoutPackRun23`（`LPackM2` 4 場）、`25`（`WindowInOrigin`）、`26`（`ShiftLocal` ガード + `final16`）、`CloseoutPreload31`（`PostRunF`）、`CloseoutWatchRound25`（4 番目の家族）。
- **偽だった主張の訂正**: 「readiness の残りは `ScanRealized` の具体化だけ」→ `ScanRealized` 自体が矛盾、`hreal` 定理は空。「`Extra3` は機械事実で閉じる」→ `ready`/`cand`/`failed` は pack の場（予算付き ready、`Candidate`、DP テープ）を要る。
- 残: readiness `PostRunF` 往復 + 4 脚 `ScanTrace` クロック; pack `LPackM2` 4 場 + `WatchShift` + `WindowInOrigin` + `Extra3` 3 場 + `first ≠ 4`; watch 4 番目の家族 + コスト 3 葉 + `LandingRestartReach`; core 初期配置・`restC`・有限制御。


## n48 (2026-09-18 未明) `shiftVm_tapeActKQ` K=28（`hrot`/`near ≠ []` 消滅）・`H_marksEntry'` は run 限定で `WindowInOrigin` 1 点・出口分割 4 通り

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 4 本登録（`CloseoutCoreEnc22`、`CloseoutPackRun17`、`CloseoutPackRun24`、`CloseoutWatchRound23`）、sorry なし、build ログ `build_n48c.log` EXIT=0。
- **core**: `CloseoutCoreEnc22`: `tViewQ = 9`、`encTapesQ rep lay dbg m`（Enc19 の `encTapesD` の 6 cursor block を `viewTapesQ` に拡張）、`tail_chainLe`（`RTQueue.tail` は ≤ 6 SStep の定数）、`chain_actList`（n sub-step ⇒ 各番地 ≤ 2n）、`moveRightQ_actList`（全分岐 ≤ 14/番地、`near ≠ []` 不要）、**`shiftVm_tapeActKQ`（:673）: K = 28**（左 2×14、中央 14、尾 ≤ 4；較正 64 内）。**`hrot` は仮定でなくなった**（`tail_hrot`: `RTQueue.Inv` から `pot_len` + `eq_idle_of_rem_zero` で導出、`PInv` は `RTQueue.lean:223`）。残仮定: `RTQueue.Inv m.vm.left.far/.center.far`、block 0/1 の初期 `LaysS/SInj/SBound`、chain block `restC/hrestC`（≤ 4）、head margins。未着手: `TapeActK` 構造形（配置を `m` の関数に）、有限制御。
- **pack**: `CloseoutPackRun17`: `WindowInOrigin s`（copy 状態で `|stream walker| ≤ pos R`）が唯一の新仮定（`beginFallbackVM'` の着地が存在量化なので `Tick` から不可視、`Fair` の witness = `P.place s` で真）。`WPack`/`wpack_tick`/`wpack_steps`、`chooseLayout_of_wpack`（**偶数長は不要**: cell 0 は `4` を読むので `first ≠ 4` で除外、`first ≠ 7/8` と同型）、`chooseLayout_of_run`、`marksEntry'_of_run`、`marksInv'_of_run'`、`corners_of_marks'_run`（`sharedC` run 上、`CPack` 付き、**`H_marksEntry'` 不要**）。残: (a) `WindowInOrigin` を `Fair` witness から（`CloseoutPackRun25` 進行中）、(b) `first ≠ 4` を最上位へ、(c) 大域 `H_marksEntry'` は証明不能 → 消費側を run 限定形へ、(d) 結果は `galilFrameS (sharedC …)` 上。
- **pack (rShiftNext)**: `CloseoutPackRun24.rShiftNext_of_pack`（:81）: `WatchShift`（:43、非 idle chain の compare 目標 `s''` に対し `mode=scan ∧ ¬replaying`、`canRight`、`4·periodLength ≤ distance`、`distance ≤ 2·rad`、verifier の `canRight/Sane`）1 葉。pack は `Coupled.watch = WatchOK`（round 上界）しか持たん → `AuxPack` に chain–scan 結合場を追加要。**警告**: `compareFound` に mode guard がなく `beginShiftVM'` は `chain = .watch _` しか要らんので、shift モードで `Internal` step が有効なら `ShiftLocal.mode`（`mode = scan` 要求）は偽 → `rShiftNext`/`H_shiftLocalC` は現行の形では shift 状態で証明不能の疑い。修正: `ShiftLocal` の各場（または `WatchShift`）を `mode = scan ∧ replaying = false` でガード（scan tick はそれしか使わん）。
- **watch**: `CloseoutWatchRound23`: 3 分割の家族は排他でない（guard 通過の不一致 = 機械の本物の `beginChainShift` 出口）ので **`ExitSplit4C`**（Shift / Break0 / FallbackG（`MismatchGuardFails`）/ `TerminalRunMismatchShiftC`）に強化、`exitSplit4C_of_tick`、`watchMismatchNoShiftC_of_split`（FallbackG から無条件）、`exitSplit3C_of_4`。残: 4 番目の家族の消費（shift 着地経路へ合流、`CloseoutWatchRound25` 進行中）、`WatchFallbackCostC`（`CloseoutWatchRound24` 進行中）。
- 進行中: `CloseoutPackRun22`（`Extra3`）、`23`（`LPackM2` 4 場）、`24`（`rShiftNext`）、`25`、`CloseoutPreload30`（`PostRun` 帰納）、`CloseoutWatchRound24/25`。
- 残: pack `LPackM2` 4 場 + `rShiftNext` + `WindowInOrigin` + `Extra3` + `first ≠ 4` threading; readiness `PostRun` 帰納 + `ScanRealized`; watch 4 番目の家族 + コスト閉包 + `LandingRestartReach`; core 初期配置・`restC`・有限制御。


## n47 (2026-09-18 未明) `BigResid6` の 5 契約が pack の場不足 4 点に還元・`PostRunD` 組み立て・`WatchFallbackC` 分解

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 5 本登録（`CloseoutPackRun19/20/21`、`CloseoutPreload29`、`CloseoutWatchRound22`）、sorry なし、build ログ `build_n47e.log` EXIT=0。
- **pack**: `rInitPackM` は**無条件**（`AuxPack.front.notInit` で pack は `init` に居らん、`CloseoutPackRun21.rInitPackM_of_pack`）。`rScanInvR` は `replaying = false` で無料（`LPackM.scanGeom`）、`replaying = true` は `H_scanGeomReplay`（Run19:74）；`rShiftDoneScan` は `H_shiftDoneGeom`（Run19:85、実体は `reshift_palindrome` の round 主張）；`rChoosePackL` は `RRepChoose`（Run20:55、`choose_left_eq_right` で `t.left = s.right`、`rrepChoose_of_pos` で `Represents R ∧ 0 < pos R`）；`rReplayPackM` は `H_centreReplay`（Run21:122、`replayStart_heads` で L=C=R=旧 C、`Fair` 不要）。**4 葉とも「`LPackM` に場が無い」型** → `CloseoutPackRun23`（`LPackM2 := LPackM ∧ scanGeomR ∧ shiftGeom ∧ rrepChoose ∧ centreRep`、`lpackM2_tick`）進行中。`bigResid6_of_leaves`（Run19:117）で残り `rShiftNext` と合わせて `BigResid6` を組む。
- **readiness**: `CloseoutPreload29`: `PostRunD F I`、`postRunD_of_machine`（仮定 `ScanSupplyInv`・`ScanRealized`・`PostRunC`）、`postRunD_of_machine_galil`。**小窓は非残差**（Scala `stepGrow` は単位 8 span セル → 全 `.double` 入口で `mw ≥ 8·max k 1`、`eight_le_of_cal`）。残: `PostRun`/`PostRunC` の機械証明（stage 帰納本体、`CloseoutPreload30` 進行中）、`ScanRealized`。
- **watch**: `CloseoutWatchRound22.watchFallbackC_of_context`（:176）で `WatchFallbackC` を `WatchFallbackResidC = WatchMismatchNoShiftC ∧ WatchFallbackCostC` に分解、tick pack 4 つは着地から輸送（`tickPack_of_landing`）。**訂正**: 「不一致なら shift できない」は偽。shift 出口も不一致で、chain が右の記号を予測する場合（Scala `stepScan` は外側不一致分岐でのみ `canShift ∧ prediction == right.read()` を見る、Lean の disabled tick は `Internal` で left/right を読まん）。残差 (a) は shift/fallback 分類器（`MismatchExitG` 形、`CloseoutWatchRound23` 進行中）、(b) はコスト閉包。
- 進行中: `CloseoutPackRun17`（`ChooseLayout`）、`22`（`Extra3`）、`23`（`LPackM2`）、`CloseoutPreload30`、`CloseoutCoreEnc22`（glue）、`CloseoutWatchRound23`。
- 残: pack `rShiftNext` + `LPackM2` 4 場 + `H_marksEntry'` + `Extra3`; readiness `PostRun` 帰納 + `ScanRealized`; watch `WatchMismatchNoShiftC`/`WatchFallbackCostC`/`LandingRestartReach`/`MismatchExitG`; core glue・`hrot`・有限制御。


## n46 (2026-09-18 未明) final15: rewind の角が pack から消えた（`H_marksEntry'` 1 点）

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 1 本登録（`CloseoutPackRun18`）、sorry なし、build ログ `build_n46.log` EXIT=0。
- **pack**: `pal_in_peg_final15`（`CloseoutPackRun18` line 258）。仮定: `BigResid6`（不変）、`H_extraEntry3`/`H_extraTick3`（`Extra3` = `Extra'` − `rewindMargin`、rewind 角なし 4 場）、**新** `H_marksEntry' (PofC …) q first`、以下不変 `H_shiftLocalC`、`H_stageScan`、`CycleOracleMC3`、`H_bootShift`、`H_landShift`、`H_realizeLIM'`。`BigPack2M''` は `MarksInv' first` を派生場として持つ（`marksInv'_of_run` を `InvLPC` 起点で、`marksInv'_tick` を毎 tick）。`first` は `galilFrameS` の section 変数なので追加 threading なし。要注意点: FIRST セル上の rewind 状態では `MarksInv'` は `1 ≤ pos L` しか与えず `BigPack2M` に忘却できない → `bigPack2M''_tick` を分岐: セル外は忘却して `lpackN_tick`/`rShiftNext` 再利用、セル上の tick は `rewind_done` のみ（`tick_rewind_atFirst`）、`LPackM` はその分岐固有のスクリプト、`replayStart` 着地の `ShiftLocal` は `AuxPack.coupled.idleOut` + `CloseoutPackRun6.shiftLocal_of_chainIdle` で vacuous。`CentreMargin`/final14 経路は不要になった（残すが使わない）。
- 進行中: `CloseoutPackRun17`（`ChooseLayout` → `H_marksEntry'`）、`CloseoutPackRun19`（`rScanInvR`/`rShiftDoneScan`）、`CloseoutPackRun20`（`rChoosePackL`）、`CloseoutPackRun21`（`rInitPackM`/`rReplayPackM`）、`CloseoutPreload29`（`PostRunD`）、`CloseoutCoreEnc22`（glue）、`CloseoutWatchRound22`（`WatchFallbackC`）。
- 残: pack `BigResid6` 6 契約 + `H_marksEntry'` + `H_extraEntry3/Tick3`; watch/readiness/core は n45 と同じ。


## n45 (2026-09-18 未明) `.double` 出口義務が Scala の形（`StageInvD`）で脚長 `mw` のまま閉じた

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 1 本登録（`CloseoutPreload28`）、sorry なし、build ログ `build_n45.log` EXIT=0。
- **readiness**: `StageInvD k m v := dpDemand k m ≤ debt`（`dpDemand k m := prepLen k / 2048 + (prepLen k + dpEvents (m+1)) / 2048 + 1`、比較単位、`Rad`/`stageCredit` 不使用 = Scala の「run 脚は自分の比較分の負債があればよい」）。鍵: `dpSafe_entry_km` は半径/credit 形を `(slack + dpEvents |W|)/2048 + 1 ≤ debt` の導出にしか使っておらず、`dpSafe_of_stagePrepD` はそこへ直行（`budget_adv2` 迂回）。`runEntriesS_of_stageInvD`（stage 帰納）、`stageInvD_of_double_exit`（`double_exit_debt_ge` + `prepAt_of_double_exit`）、**`runEntriesS_of_double_exitD`**（`runEntriesS_of_double_exitC` と同結論、脚長 `bs.length = mw` で真、`hstage`/`hcal`/半径形 `hE` 消滅）。残 `hbal : 4*dpDemand k (2mw) + 4*count ≤ mw` はペーシングから放電: `bal_of_paced`（入口位相、`8·max k 1 ≤ 2mw` のみ）、`bal_of_paced_slack`（任意位相 `slack ≤ 2047`、`8 ≤ mw` 要）。n37〜n43 の `.double` 脚問題はこれで決着（Lean の義務形が初回 run 用の半径形だったのが原因）。次: `PostRunD`（`.double` 節を `StageInvD` 形に）と `postRunD_of_machine`（`CloseoutPreload29` 進行中、残るのは `ScanRealized` の `galilFrameS` 具体化と窓 4〜7 の位相）。
- 進行中: `CloseoutPreload29`、`CloseoutCoreEnc22`（glue）、`CloseoutPackRun17`（`ChooseLayout`）、`CloseoutPackRun18`（`final15`）、`CloseoutWatchRound22`（`WatchFallbackC`）。
- 残: n44 と同じ、readiness は `ScanRealized` 具体化のみ。


## n44 (2026-09-18 未明) 影コピー queue で回転が全番地 ≤ 2 手・`MarksEntry` は place-1 で偽→ガード付き `MarksInv'`・`FallbackRouteW` は `WatchFallbackC` に

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 3 本登録（`CloseoutCoreEnc21`、`CloseoutPackRun16`、`CloseoutWatchRound21`）、sorry なし、build ログ `build_n44c.log` EXIT=0。
- **core**: `CloseoutCoreEnc21`: 7 役割 `SRole`（Enc20 の 6 + `shadow`）、影は状態から派生（reversing/appending 中は `r'` を写す、`.done` で `f`、idle で `front`）。ウチの「`g = popped ++ front` + カウンタ」案は実時間予算を破る（size-1 queue に `2m+1` の discard が溜まり 2 回目の回転が `PInv.rot` を破る）ので、idle の `tail` は front と shadow を両方 pop（各 1 手）して `g = front` 厳密に。`LaysS q ρ L J`（junk を live の下に置く配置、消去は役割改名で無料）。`SStep`（snocPush/tailPop/inval/rotStart/exec/install）、`snoc_steps`/`tail_steps`（`hrot : lenf < lenr → state = idle` の下で `ReflTransGen`）、`rotRolesS`（fwd ↦ shadow, rev ↦ rear, rear ↦ fwd, shadow ↦ rev）、`sstep_lays`（全 SStep が Delta 族）、**`moveRightS_actList`**（全 SStep で全番地 actList ≤ 2）。Enc20 の逃げ道 `ρ'.fwd = ρ.rear` は `ρ'.fwd = ρ.shadow` として実現。残: glue（`encTapesQ`/`shiftVm_tapeActKQ`、`tViewQ = 9`、`CloseoutCoreEnc22` 進行中）、`hrot` の放電（HM 不変量）、live/junk を判別する有限制御。
- **pack**: `CloseoutPackRun16`: 無ガード `MarksEntry` は place-1 の角で**偽**（`marksEntry_false_at_place_one`: `pos R ≤ 1 → ¬MarksEntry`；`marksEntry_false_of_whole_prefix`）。ガード付き `MarksEntry'`（`mh+1 ≤ pos R + f`）は `ChooseLayout first s`（`denote = update (marks w) 1 first ∧ 1 ≤ mh ≤ w.length ∧ w.length ≤ pos R`）から無条件（`marksEntry'_of_layout`）。`MarksInv'` は全 24 分岐で保存（`marksInv'_tick`）、角 `rewindLeft_of_marksInv'`（`0 < pos (left L)`）、`rewindCentre_of_marksInv'`、`corners_of_marks'`。残: `ChooseLayout` の産出（コピー walker が原点を越えない `w.length ≤ pos R` と偶数長；`CloseoutPackRun17` 進行中）。`final15`（ガード付き角を元の `LTickLeavesN.rewindLeft` に直結、`CentreMargin`/final14 を迂回；`CloseoutPackRun18` 進行中）。
- **watch**: `CloseoutWatchRound21.fallbackRouteW_of_tick`（line 121）: `FallbackRouteW` を `WatchFallbackC`（line 77）+ `0 < q`, `first ≠ 7, 8` の下で産出。`fallbackLanding_of_pack`（watch 中 clock-1 不一致からの fallback tick は `1+(n+1)` tick で着地、R=0 なら `Inv`、R>0 なら `ReplayLanding`、`SpanRep`、中心厳密前進）。**発見**: `GalilInvPlus.fallback_pack_span` は `chain = .idle` を要らない（idle 要求は `SegReached.idle` 由来のみ）。`WatchFallbackC` の中身: (a) 不一致状態の tick pack `ShiftIdle ∧ MInv ∧ FallbackCounters ∧ FallbackTick ∧ OutputRel`（実質 `FallbackTick` = watch 不一致で `¬shiftGuardVM`）、(b) stage 入口からのコスト閉包（`StepsAll … ∧ CostedRun` と R>0 の `InvLP`）。`CloseoutWatchRound22` 進行中。
- **readiness**: `CloseoutPreload28`（倍化後 stage 不変量 `StageInvD` を Scala の形 `debt ≥ 0` で）進行中。Scala 照合: `stepWait` は `debt.sign == 0` のときだけ `doubleWindow()`（`wait_exit_debt_zero` は忠実）、Scala が主張する不変量は `debt ≥ 0` のみ（`IllegalStateException` 2 箇所）。`.double` 出口での「stage 予算再成立」は Scala にない → Lean の定式化ミス。
- **偽だった主張の訂正**: 「影コピーは `popped` カウンタで管理」→ 予算を破る。「無ガード `MarksEntry` は真」→ place-1 で偽。
- 残: pack `BigResid6` 6 契約 + `ChooseLayout`; watch `WatchFallbackC`/`LandingRestartReach`/`MismatchExitG`/存在形 RoundsExit・BreakExit; readiness `StageInvD`・`ScanRealized` 脚構成; core glue・`hrot`・有限制御・`restC`・`nq/hctl`・`CounterPark`/`FlagPark`; `H_realizeLIM'`; `CycleOracleMC3` 葉。


## n43 (2026-09-18 未明) `.double` 義務の真の障害は基底負債（除数は無関係）

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 1 本登録（`CloseoutPreload27`）、sorry なし、build ログ `build_n43.log` EXIT=0。
- **readiness**: `stageCredit8`（除数 8）で `budget_adv2_nat8`/`budget_adv2_8` は同じ入力で閉じる。しかし `double_len_of_leg8`: 十分な脚長は `mw + 4·max k 1 + 4c + 7`、`double_len_needs8`: 必要条件 `mw + 4·max k 1 + 4c + 4 ≤ L + 4·Rad`。`L = mw` では `Rad ≥ max k 1 + c + 1` を強制（`double_len_forces_rad8`）、`Rad = 0` で反証（`double_len_false_of_rad_zero8`）。**除数は無関係**: 任意の credit `cr ≥ 0` で `8·max k 1 + 4c + 4 ≤ L + 4·Rad` が必要（`double_len_needs_any`）、`L = mw = 4·max k 1, Rad = 0` で反証（`double_len_false_any`）。除数 16 でも `mw < 12·max k 1 + 8c + 7` で破綻。**真の障害**: 基底負債 `stageDebt Rad k = 2·max k 1 − Rad`（4 tick/単位で 8·max k 1 tick 分）を `wait_exit_debt_zero` がリセットし、`mw ≥ 4·max k 1` tick の脚では再獲得できない。除数は `mw − 4·max k 1` の超過分にしか効かない。候補: (a) `.wait` 出口で負債を保持、(b) `Rad ≥ max k 1 + c + 1` を側条件（Preload26 と同値）、(c) `.double` 脚 ≈ `2·mw`（Preload25）。Scala で stage 負債の初期化と wait 出口の扱いを照合中（scout）。`PostRunC8` は未作成（節が偽なので）。
- **偽だった主張の訂正**: 「`stageCredit` の除数を 8 にすれば `.double` 義務は無条件で閉じる」（n40）→ 偽。障害は基底負債と wait リセット。
- 進行中: `CloseoutPackRun16`（`MarksEntry`）、`CloseoutCoreEnc21`（影コピー queue）、`CloseoutWatchRound21`（`FallbackRouteW`）、Scala 照合 scout。
- 残: n42 と同じ、readiness は「基底負債の扱いを Scala に合わせる」に変更。


## n42 (2026-09-18 未明) `WatchPrefixC` は無仮定の定理 → `foundExit_compare_final11`

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 1 本登録（`CloseoutWatchRound20`）、sorry なし、build ログ `build_n42.log` EXIT=0。
- **watch**: `watchPrefixC_of_unique`（`CloseoutWatchRound20` line 172）は全 `P q first cP sP` で**無仮定**（`LiveScanWatch`/`Fair` 不要）。`refresh_unique`、`compare_scan_unique`（`scanLens.get_set` + `GalilTickDet.chainTick_unique` + `scanVM_ext`）、`watchSeg_step_unique`（構成子族は重ならない：`wait` は `¬canRight`、`count`/`match` は `canRight` で `1 < clock` vs `clock = 1`）、`watchSeg_prefix`（第 1 走行への帰納）。`GalilTickDet` の `Tick` 非決定性（restart stutter・fallback 着地・init/replayStart）は `WatchSeg` に入らない。`foundExit_compare_final11`（line 180）= final10 から `hpre` 除去。残契約: `FallbackRouteW`（`CloseoutWatchRound21` 進行中）、`LandingRestartReach`、`MismatchExitG`、存在形 RoundsExit/BreakExit。
- 進行中: `CloseoutPackRun16`（`MarksEntry`）、`CloseoutCoreEnc21`（影コピー queue）、`CloseoutPreload27`（`stageCredit8`）、`CloseoutWatchRound21`。
- 残: n41 と同じ、watch は `WatchPrefixC` 消滅。


## n41 (2026-09-18 未明) `CentreMargin` は MARKS テープ不変量経由で `MarksEntry` 1 点に

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 1 本登録（`CloseoutPackRun15`）、sorry なし、build ログ `build_n41.log` EXIT=0。
- **pack**: `MarksInv first c s`（rewind 中: FIRST セル `f ≥ 1` が MARKS ヘッド以左で `mh s + 2 ≤ pos L + f`、かつ `pos L + r + pairOff ≤ pos C`）。`centreMargin_of_marksInv`、`marksInv_tick`（全 `galilFrameS` tick で保存、`rewind_one/pair` は `focus_eq`/`left_head`/`position_left` で閉、他は vacuous、`choose_select` だけが `MarksEntry` を消費）、`centreMargin_of_marks`（rewind 外始動の run 全状態）。**残る仮定は `H_marksEntry P q first` 1 点**（`choose_select` 時点で `mh s + 2 ≤ pos R + f`、FIRST がセル 1 なら `mh s + 1 ≤ pos R`）。注意: 無ガードの `CentreMargin` は `rewind_done` でも `2 ≤ pos L` を要求するので、入力 1 文字目から始まる回文を選ぶ場合を除外している可能性 → `CloseoutPackRun16` で真偽判定（偽ならガード付き `MarksEntry'` へ、`GalilScaffoldTopFallbackAll` の FIRST = `head − 2r` から導出を試みる）、進行中。
- 進行中: `CloseoutPackRun16`、`CloseoutCoreEnc21`（影コピー queue）、`CloseoutPreload27`（`stageCredit8`）、`CloseoutWatchRound20`（`WatchPrefixC`）。
- 残: n40 と同じ、pack は `MarksEntry` に置換。


## n40 (2026-09-18 未明) `.double` 義務の根本原因は `stageCredit` の除数・`ExitSplit3C` は `WatchPrefixC` 1 葉に

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 2 本登録（`CloseoutPreload26`、`CloseoutWatchRound19`）、sorry なし、build ログ `build_n40b.log` EXIT=0。
- **readiness**: `CloseoutPreload26`: `doubleCarry mw c := (mw+4c+10)/4`、`PostRunC' carry`（round-trip の `.double` 節で `hlen : bs.length = mw`、不足分を半径に繰り入れ `3*(Rad + carry) ≤ 5*k`）、`postRunC'_of_double_leg`/`postRunC'_double_spends`。ただし側条件 `3*(Rad + doubleCarry) ≤ 5*k` は導出不能（`mw ≲ 20k/3` を強制）。**根本原因**: `stageCredit k m = (m − 8·max k 1)/4`（`CloseoutPreload11`:66）が甘すぎる。長さ `mw` の `.double` 脚が稼ぐのは ≈ `mw/4`、要求は `stageCredit k (2mw)` ≈ `mw/2`、しかも `.wait` が負債を 0 に戻す（`wait_exit_debt_zero`）ので蓄積しない。**修正は除数 8**（`budget_adv2_nat` は要求 ≈ `m/41` で閉じる）。`CloseoutPreload27`（`stageCredit8`、`budget_adv2_nat8`、`double_len_of_leg8`、`PostRunC8`）進行中。
- **watch**: `CloseoutWatchRound19.exitSplit3C_of_tick`（line 191）で `ExitSplit3C` 放電、`foundExit_compare_final10`（line 206）。新仮定 1 つ: `WatchPrefixC P q first cP sP`（line 95、prep 着地からの任意 2 本の `WatchSeg` 走行は接頭辞比較可能）。`ExitSplit3C` は ∀/∨ 交換なので `WatchSeg` の `background`/`compare`/`searchEffect` が関係的な限り導出不能。機械上は段決定性（`GalilTickFair` の `*_unique` 群）から従う。`CloseoutWatchRound20`（`watchPrefixC_of_unique` → `final11`）進行中。補題 `watchSeg_not_canRight`（尽きは吸収）、`watchSeg_stuck_of_mismatch`（clock-1 不一致は `stop` のみ）。
- 進行中: `CloseoutPackRun15`（`CentreMargin`）、`CloseoutCoreEnc21`（影コピー queue）、`CloseoutPreload27`、`CloseoutWatchRound20`。
- **偽だった主張の訂正**: 「`.double` 出口義務の側条件は負債持ち越しで消える」→ 消えない（除数が原因）。
- 残: n39 と同じ、readiness は `stageCredit8` 化、watch は `WatchPrefixC` 産出。


## n39 (2026-09-18 未明) 6-stack 役割表: 回転開始は無料、代償は `f := front` の複製へ

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 1 本登録（`CloseoutCoreEnc20`）、sorry なし、build ログ `build_n39.log` EXIT=0。
- **core**: `QRole`/`Lays q ρ L`（役割表、`queueTapes6_roleList` で `queueTapes6` = 恒等役割表）。`Delta`(keep/pop/push) は `dTape` 上で無条件に各番地 ≤ 2 手（`dActs_length`）。**回転開始 `rear := []` は役割付け替えのみ**（`rotStart_actList`: 全番地 actList `[]`）。Enc19 の `not_bounded_rot_rear` は 4 テープ層だけの否定と確定。`exec`/`invalidate`/`tail` も Delta 族。**ただし** `front_fwd_sep`（`SInv` より `f = front.drop ok`、`0 < ok` で別名禁止）+ `not_bounded_install_fwd`: 空スタックへの `fwd` 設置（`f := front` の複製）は生セル数の手数が要る。代償が「消去」から「複製」へ移っただけ。未否定経路は `ρ'.fwd = ρ.rear` 1 本。
- 次（`CloseoutCoreEnc21`、進行中）: 影コピー方式。appending 中に新 front と影 `g` へ二重 push（別番地なので各 ≤ 2 手）、`tail` は front だけ pop、`g = popped ++ front` を不変量に持ち、回転時は `g` を反転源に役割付け替え（無料）して先頭 `popped` 個を捨ててから反転。HM の `ok` 簿記と同じ 2 倍ペースに吸収。
- 進行中: `CloseoutPackRun15`（`CentreMargin`）、`CloseoutPreload26`（`PostRunC'`）、`CloseoutWatchRound19`（`ExitSplit3C`）。
- 残: n38 と同じ。


## n38 (2026-09-18 未明) final14: rewind の角を `CentreMargin` 1 葉に

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 1 本登録（`CloseoutPackRun14`）、sorry なし、build ログ `build_n38.log` EXIT=0。
- **pack**: `pal_in_peg_final14`（`CloseoutPackRun14` line 300）。仮定は final13 と同一で `H_extraEntry''`/`H_extraTick''` のみ差し替え（`Extra''`: `rewindMargin` → `centreMargin`）。`LTickLeavesN'`（`rewindLeft` を `CentreMargin c s` に）、`LTickLeavesN'.toN` は `RCouple c s` を要するが run 上では定理（`rcouple_of_invLPC`）。`lpackN'_tick` は `lpackN_tick` との合成のみ（22 分岐は再走せず）。`BigPack2M'` は `RCouple` を派生場として持ち `BigPack2M` に忘却するので `BigResid6` は不変。
- 進行中: `CloseoutPackRun15`（`CentreMargin` を `marksTape s.fpp` の FIRST 位置不変量から）、`CloseoutPreload26`（`PostRunC'`: `.double` 出口の負債持ち越し形）、`CloseoutWatchRound19`（`ExitSplit3C` 放電）、`CloseoutCoreEnc20`（6-stack 回転）。
- 残: n37 と同じ（`CentreMargin` が `rewindMargin` を置換）。


## n37 (2026-09-18 未明) rewindMargin は削除不能→CentreMargin 1 葉・`.double` 脚の正確な閾値

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 2 本登録（`CloseoutPackRun13`、`CloseoutPreload25`）、全モジュール sorry なし、build ログ `build_n37b.log` EXIT=0。
- **pack**: `rewindMargin` 葉（`LTickLeavesN.rewindLeft`）は**削除不能**。`CloseoutPackRun13.rewind_left_step`: rewind に留まる tick は L を必ず 1 左へ動かす（`rewindOne`/`rewindPair` とも `left := left x.left`）。前夜の「rewind は R だけ動かす」は誤読で、毎 tick 動くのは L、2 tick に 1 回が C。代わりに `RCouple`（`pos L ≤ pos C ≤ pos L + radius + pairOff`）を全 tick 無仮定で保存（`rcouple_tick`、rewind 外始動の run では定理 `rcouple_of_run`）し、`CentreMargin`（rewind 中 `radius + pairOff + 2 ≤ pos C`）1 葉から `rewindMargin` と `GalilRewindSafe.CentreLive` の両方を供給（`corners_of_centreMargin`）。`CentreMargin` は MARKS テープの「FIRST が原点 gap より右」で `Tick` から不可視、未証明。次: `rewindLeft` を `CentreMargin` に差し替えた `LTickLeavesN'` で `lpackN'_tick` → `final14`（`CloseoutPackRun14`、進行中）。
- **readiness**: `postRunC_of_machine` の `.double` 脚数値義務 `4*(stageDebt+stageCredit+1)+4*count+3 ≤ mw` は脚長 `L = mw` では**偽**（`CloseoutPreload25.double_len_false_of_rad_zero`、Rad=0 で反証）。十分条件は `double_len_of_leg`: `L ≥ 2*mw + 4*count + 7`。Scala 正本（`ScaffoldSearch.scala:144,147,275`）は double 相を**正確に `mw` tick**で抜ける（`alias(work, span)` → `Mode.Double` → work 空で `prepareWindow()`）。したがって偽なのは機械ではなく **`PostRunC`（`CloseoutPreload24`）の `.double` 出口義務の定式化**：倍化後の窓のコストを出口時点で一括請求しているが、Scala は次の run 相で償却する。次: `.double` 出口義務を「負債の持ち越し」形（`stageDebt` を次 run の `DpCharged` に繰り入れ）に書き直して `PostRunC'` を定義し、`runP_exit_debt_at_exit_scan` と接続。wait 脚→`DepthAt` は閉（`depth_supply_of_wait_leg`/`stage_supply_after_wait`）。`ScanRealized` の `galilFrameS` 具体化は未達。
- **core**: `CloseoutCoreEnc20`（6-stack `RTQueue` + role swap 回転）進行中、未登録。
- **偽だった主張の訂正**: 「rewind は L を動かさない（rewindMargin は vacuous）」→ 偽。「`.double` 出口で倍化窓のコストが払い済み」→ 偽（Scala は `mw` tick で抜け、次 run で償却）。
- 残: pack `BigResid6` 6 契約 + `CentreMargin`; watch `FallbackRouteW`/`ExitSplit3C`/`LandingRestartReach`/`MismatchExitG`/存在形 RoundsExit・BreakExit/StepsAll 決定性; readiness `PostRunC'` 再定式化・`ScanRealized` 脚構成; core `moveRightQ_actList`・`restC`・`nq/hctl`・`CounterPark`/`FlagPark`; `H_realizeLIM'`; `CycleOracleMC3` 葉。


## n36 (2026-09-18 未明) final13・scanLeft 葉削除・PostRunC・shiftVm K=64・キュー配置

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 12 本登録（`CloseoutPackRun11–12`、`CloseoutPreload19–24`、`CloseoutCoreEnc17–19`、`CloseoutScanMargin4`）。
- **pack**: `pal_in_peg_final13`（`CloseoutPackRun12`）。Lean の `read` は gap で sentinel `2`、原点のみ `none`（Scala と一致：gap は `"s"`、原点 `None`）→ 原点比較は必ず不一致、`scan_match` は `position L = 1` から発火しない（`ScanMargin4.no_scanMatch_at_pos_one`）。`scanLeft` 葉は「無条件版は偽・matched 前提つきは真」なので葉から完全削除（`LTickLeavesN`、`lpackN_tick`、PackRun11）。`Extra'`＝`Extra` − `scanMargin`（反証済）。残仮定 9：`BigResid6`（`rInitPackM`/`rScanInvR`/`rShiftDoneScan`/`rChoosePackL`/`rReplayPackM`/`rShiftNext`）、`H_extraEntry'`/`H_extraTick'`（角は `rewindMargin` のみ、PackRun13 進行中）、`H_shiftLocalC`、`H_stageScan`、`CycleOracleMC3`、`H_bootShift`、`H_landShift`、`H_realizeLIM'`。Scala 全 tick 追跡（`a`,`aa`,`aab`,`aba`,`abab`）で「mode=scan かつ L=原点」の tick は 0 件、`PlaceHead.left` の例外は到達不能。
- **readiness**: `PostRun` → `PostRunP`（paced）→ `PostRunC`（clock 位相形、Preload24）。閉じたもの：`.run` 相のイベント長 ≤ `dpEvents`（測度は `DpSafeStage.pre`、Preload15）、`StagePrep` 切り直し（16）、`.wait` は `.run` に戻らず債務が測度（14）、`.double` 消化 `double_complete`（17）、時計位相 `PrefixPhase`（18/19：`PacedL` は上界のみ＝下界は `LiveL`）、`LiveL` はマッチクロック保存則から（20）、帳簿同定 `scanTrace_eq_runTrace`（21）、`searchStep` の boolean＝`ScanTrace` 事象、`ClockInv` は Tick 不変（22）、右ヘッド供給 `ScanSupplyInv`（`Extra.scanAvail` 経由、23）、`slack ≤ 2047` を位相から（24）。残：`.double` 脚の数値義務、wait 脚長→`DepthAt` 変換、`ScanRealized`（Preload25 進行中）。
- **核**: `shiftVm_tapeActK`（K≥4、Enc17；ミラー 7 番地込み）。`moveRight` は現配置では pop 不可能（偽）→ debris 配置 `dTape`（pop 1 手・push 2 手、Enc18）→ `encTapesD` 上 `shiftVm_tapeActK'`（Enc19、`near ≠ []` 側条件）。回転開始は 4 本 cursor では有界不可（`not_bounded_rot_rear`）→ 6 スタック＋役割置換（Enc20 進行中）。
- **偽だった主張の訂正**: 「Lean の compare に左端停止則がない＝モデル不備」（ScanMargin3）は過剰判定、不備なし。「`∀ s, F.available s`」は偽（`ScanSupplyInv` で置換）。「`rear := []` は消去」は誤読（役割付け替え）。

## n35 (2026-09-17 夜) final12・final9・PostRunP・chooseVm K=64・原点角の実態

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 21 本を登録（`CloseoutPackRun7–10`、`CloseoutPreload12–17`、`CloseoutCoreEnc13–16`、`CloseoutWatchRound14–18`、`CloseoutScanMargin1–3`）、`GalilFoundLandingL`/`GalilInvPlus2` に着地 `Inv` を export する `_Inv` 版を追記（既存宣言不変、`GalilInvPlus2` に import 1 行追加）。
- **pack**: `pal_in_peg_final12`（`CloseoutPackRun9`）：`IPackO`（MInv/PalAt なし、`lrep`+`scanGeom`）で `StepsI…PreTraceI` 全 7 定義を再カット、`H_trailI` は定理（`h_trailI_O`）で放電。残仮定 9（`BigResid5O` 6 契約 = 旧 7 − `rShiftDoneMinv`、`H_extraEntry/Tick`、`H_shiftLocalC`、`H_stageScan`、`CycleOracleMC3`、`H_bootShift`、`H_landShift`、`H_realizeLIO'`）。`lpackO_tick` は minv コーナー削除で欠落なし。`CloseoutPackRun10`：strict は `scan ∨ rewind` に限定（`lrepM`）、`scan_shift/fallback` は `Represents` のみで閉じ、`shift_done` は `leftPresent` で再取得。
- **原点角（重要）**: `Extra.scanMargin`（`r+2 ≤ C`）は 1 文字語の初期 scan 状態で反証（`CloseoutScanMargin2`）。`lrep` 下では `position L = 0` は到達不能（`lrep_pos`）、真の角は `position L = 1` からの比較 tick で `focus = none` になる（`ScanMargin3`）。Scala 実走で確認：原点では `left.read() == None` → 必ず不一致 → fallback、例外なし（`aab`,`aaab`,`abab`,`aabaa` 全接頭辞一致）。Lean の `compare` も同じ。残る欠落は `scan_match` の `scanLeft` 葉 1 つ（右が letter でも `position L = 1` は `ScanInvariant` から排除できない：gap 一致の扱いを tick 追跡で確定中）。
- **watch 経路**: `foundExit_compare_final9`（`CloseoutWatchRound18`）：3 way 出口（shift／入力枯渇／外側不一致 `FallbackRouteW`）。`FallbackRouteLP` は producer なしの契約と判明、watch 版 `FallbackRouteW` も契約。`LandingRestartReach` は fallback 分岐のみ、`hLR` は round/break 分岐から除去（`final8`）。`watchSegE_of_watchSeg` 追加。残契約：`FallbackRouteW`、`ExitSplit3C`、`LandingRestartReach`、`MismatchExitG`、`RoundsExit`/`BreakExit` の存在型化。
- **readiness**: `PostRun`→`PostRunP`（paced 版、置換無料、`CloseoutPreload17`）。`.run` 相：`run_exit_frame`（Preload13；`.double` 出口は `work = ofNat m`、span は reset）、`RunTraceP` 債務上界（14）、イベント長 ≤ `dpEvents`（15、測度は `DpSafeStage.pre`）、`StagePrep` 切り直し（16）、`.wait` は `.run` に戻らず債務が測度（14）、`.double` 消化レグ `double_complete`/`double_leg_entries`（17）。残：時計相 `slack ≤ 2047`、`.wait` レグ長、`hE`（Preload18 進行中）。
- **核**: カウンタ reset は役割切替不要（`applyAction` 1 発、`CloseoutCoreEnc13`）；`chooseVm` は全番地で `TapeActK`（K≥2）完成（`chooseVm_tapeActK`、Enc16；lengthMir は 2 発）。`Seg→Γc` 埋め込みとスロット番地（Enc14）、`shift1/padRN` と `actList` の可換条件（Enc15；左マージンは `padRN` から出ない＝`pos(phys j)+1`）。残：`shiftVm`（left/center/chain カーソル）、有限制御 `nq`/`hctl`、`CounterPark`/`FlagPark` 実体、`shiftPick` の view 2 手。
- **偽だった主張の訂正**: 「`.double` へ span 不変で抜ける」（work に移る）、「wait は 1 tick で run に戻る」（戻らない）、「`padRN` の余白で左マージン」（右側なので寄与ゼロ）、「lengthMir 1 発」（2 発）、「scan_match で右 letter → `position L ≥ 2`」（偽）。

## n34 (2026-09-17) 合成 step・段 2 添字化

`CloseoutCoreEnc12`（1 抽象 tick＝高々 K=64 マイクロ動作の合成、番兵 `Option Γc`、`TEqG`）、`CloseoutPreload11`（段 readiness を `(k,m)` で再証明、倍化は自弁）、`CloseoutPackRun6`（boot/init `ShiftLocal` 閉）。**全体 build 成功・標準公理のみ・無条件 PAL は未完。**

## n33 (2026-09-17) final11・台帳化・段 2 添字化

`pal_in_peg_final11`（`IPackG` 差し替え完了、`MInv` は scan 限定；残 `BigResid5G` 7＋extra、boot/init の `ShiftLocal` は閉）。watch 経路：`NoShiftTailC0` を台帳形へ（`foundRouteMC_noshift_L`）、交差 report の live-chain 版（`reachAtC3_of_crossW'`）。段 readiness：`NoReturn`/`StageBoundary` 偽→2 添字 `(k,m)` 化進行中、短入力は `dpSafeStage_entry_real` で解決。core：多くの step は 1 tick 1 マイクロ動作でない→合成 step（K=c）へ設計修正中。**全体 build 成功・標準公理のみ・無条件 PAL は未完。**

## n32 (2026-09-17) MInv 設計修正・watch 残渣の欠落事実確定

`CloseoutPackRun4`：`rMismatchMinv` 偽（不一致着地で中心は死ぬ）→ `LPack.minv` を scan 限定に切り直し中（`PackRun5`）。`CloseoutWatchRound8`：残りの真の欠落＝準備中比較ゼロの全着地版、`freshWatch` 構文一致→台帳化、exit の restart 証人、DP 窓一意性、shift 後 rounds 構成（`WatchRound9/10` 進行中）。**全体 build 成功・標準公理のみ・無条件 PAL は未完。**

## n31 (2026-09-17) 債務再較正・core ActPieces

`CloseoutPreload6`（準備中 advance 込みで入口債務を再較正、`k ≤ 2045` 消滅、残 `CentreLongRun`/`NoReturn`/`EntryDepthG`）、`CloseoutCoreEnc10`（幅 9 本閉、窓 13 は `ActPieces` へ）。**全体 build 成功・標準公理のみ・無条件 PAL は未完。**

## n30 (2026-09-17) final10・watch/core 残渣の切り直し

`pal_in_peg_final10`（`CloseoutPackRun3`：`BigPack2`＝`Extra`（DP 最大性・候補周期・段余裕）付き、残 `BigResid5` 9 契約）、`CloseoutWatchRound7`（残 7）、`CloseoutPreload5`（入口債務は準備中 advance 分の再較正が必要と判明）。**全体 build 成功・標準公理のみ・無条件 PAL は未完。**

## n29 (2026-09-17) final9・core 窓の step 単位還元

`pal_in_peg_final9`（`CloseoutPackRun2`：入口残余ゼロ、残 `BigResid4` 12 経路契約）、`CloseoutWatchRound5`（tail は 6 契約に）、`CloseoutCoreEnc9`（phase 窓は 12 `winOn`＋5 原子＋9 `widthStep` に）。**全体 build 成功・標準公理のみ・無条件 PAL は未完。**

## n28 (2026-09-17) final7・PackRun・core 残債の細分化

`pal_in_peg_final7`（`CloseoutPackRun`：`BigPack` で `PackRun` を証明、残 `BigResid` 12 経路契約）。`CloseoutWatchRound6`（台帳契約 8→4）、`CloseoutCoreEnc7/8`（`widthFeed`/`encInjective7` 偽→修理、phase 7 は `branchRead`/`winOn`/`widthEnc1` に細分化）。**全体 build 成功・標準公理のみ・無条件 PAL は未完。**

## n27 (2026-09-17) OracleI・watch rounds・core 窓関数

`CloseoutOracleI/I2`（`IPack` 着地は `ShiftLocal` のみ、`H_lrepC` 閉、残 `PackRun`＝走行保存）、`CloseoutWatchRound3/4`（`foundExit_compare_final4`、残 tails と台帳契約）、`CloseoutPreload4`（`RestartTrace` 偽→entry 版、残 3 契約）、`CloseoutCoreEnc6`（恒等 3 モード閉、残 phase 7 の `DetWin`）。**全体 build 成功・標準公理のみ・無条件 PAL は未完。**

## n26 (2026-09-17) final6・watch 相・段切り台帳の修正

`pal_in_peg_final6`（`BootIPack`/`H_oracleI`/`H_realizeLI'`、`H_trailI` は定理化 `CloseoutLPack6`）。`foundExit_compare_final`（`CloseoutWatchRound2`、残 `MatchTickC`/`LandingReadyC`/`TerminalTailsC'`）。段切り台帳を `stageWindow1`・`RdPaced` 長さ下限で修正、`readyClosure_C` は `RestartTrace` 1 つ残し。core は `CoreLocal` 項構成済み、残債はモード別窓関数 ×10 と feed 配置。**全体 build 成功・標準公理のみ・無条件 PAL は未完。**

## n25 (2026-09-17) watch 相の構成・LPack 葉・core 残債

`CloseoutWatchRun/Round`（watch 相の燃料帰納構成、1 round 構成；残 `RoundDataC`/`TerminalTailsC`）、`CloseoutLPack3/4`（23 構成子分岐、残 `LTickLeaves4`＝run レベルで輸送予定）、`CloseoutCoreEnc3`/`Preload`/`RunEntriesS`（`CoreLocal` 項構成、`RunEntriesS` 全列で閉、残 `PreloadAtEntry`）、`GalilReplaySpan ''_R_of_decodes`（抽象台帳 `ReadyClosure`、`hpres`/`RunEntries*` 消滅）。**全体 build 成功・標準公理のみ・無条件 PAL は未完。**

## n24 (2026-09-17) 第2波続き：段切り readiness・LPack・core 符号化

`CloseoutReadyStage`（`SearchReadyS`/`ReadyPacedS`：予算上限なしの区間構成、`hpres` 不要）、`CloseoutLPack/2`（`TrailF` は `LPackTick` 1 tick 保存＋shift 入口条件に還元）、`CloseoutPrepInputs3`/`LaterQuantum`/`LaterEntry`（found の DP データは named なしで閉）、`CloseoutWatchPhase/2`（found 経路は `ShiftTailC`/`NoShiftTailC`＝watch 相の実走行のみ残）、`CloseoutCoreEnc/2`/`CoreAgree`/`RightBounds`（K=1 窓局所性、語依存除去、chain 表現；queue 配置と margin は修正版へ）。**全体 build 成功・標準公理のみ・無条件 PAL は未完。**

## n23 (2026-09-17) 計画第2波：契約・found 3葉・core・債務監査

`CloseoutContracts`（StageEntryC/SegResult/CostedRouteC/FoundExit/CheckpointRunC）、found 3葉は `FoundExit` 型で `RoundsRouteLP`/`BreakRouteLP`（watch 相の per-instance 構成）まで還元、`PrefixCost` は点ごと版に修正。`RunEntriesPaced`/`ReplayFitsStage` 偽（`CloseoutRunEntriesPaced`/`CloseoutDebtAudit`）→ 段切り readiness `SearchReadyS` へ再定式化中。`TrailF` は `LPack`（左ヘッド走行 pack）1 つに集約。core は `Q/Γ/t` 具体化、`AgreeOn`×7・`encC`・窓局所性が残り。**全体 build 成功・標準公理のみ・無条件 PAL は未完。**

## n22 (2026-09-17) 計画 §8 第1波 A–E 完了

`RunEntriesAtBegin` 偽（`CloseoutReadinessAudit`）→ `RunEntriesPaced`（`GalilReplaySpan ''_fuel'`）。`Fair` witness（`CloseoutFairWitness`）。`RadLedger`（`CloseoutRadPack`、`startLe` 閉、`shiftCR` は remaining=0 で要修正）。core は `CoreLocal` 束に還元（`CloseoutCoreAudit`：閉じた `LocalStep` 項なし、語依存あり）。横断 report は `InvLPS`+入口予算で閉（`CloseoutReportCase`）。**全体 build 成功・標準公理のみ・無条件 PAL は未完。**

## n21 (2026-09-17 朝) Fair 完成・hpres/StartShape 置換・TrailF は RadPack に集約

`GalilTickFair`（`Tick ∧ Fair` 一意）、`StartShape'`、`ReadyFuel`、`GalilLeafFb/Dp/Pos`、`GalilTrailRad`、`LocalWF`（局所 7/10）。**全体 build 成功・標準公理のみ・無条件 PAL は未完。**

`pal_in_peg_final4`（`H_oracle2`/`H_needLB'`/`H_realizeLB'`）。葉: `hends`/`hended`/`hlastMatch`/`ReplayBudgetR`/`RestartShape` 閉、`hquiet`/`houtReplay`/`hpres`/`hpos` は偽と判明し置換中。抽象 Tick の非決定性（`GalilTickDet`）→ `Fair` 方針。`TrailF` は `RadPack` 1 つに集約。局所モード 6/10 閉。詳細はルート CLAUDE.md 進捗節。**全体 build 成功・標準公理のみ・無条件 PAL は未完。**

## n19 (2026-09-17) 5 エージェント統合・作業停止

GalilLexMeasure / GalilFinalAssembly3 / GalilNeedBound / GalilLookRefined / GalilNoShiftStage / GalilChainCoupling / LocalTrackingLatch / GalilReplaySpan を登録。lookahead を遅れ量依存にして needL' を Trail 不変量に還元、hbudget を無仮定で証明、shift 無し break の段入口を証明、ReplaySpan は偽（反例 aaaaabaaaab）で ReplayBudget+RestartShape に置換、局所ラッチ追跡から PAL を oracle 付きで導出。残りは ReplayBudget 条項 2・3、H_trail、hcopy/hcenR 接続、H_oracle 葉、局所 oracle 4 系統（詳細はルート CLAUDE.md の進捗節）。**全体 build 成功・標準公理のみ・無条件 PAL は未完。**

## 2026-09-17 追記（最終定理 `pal_in_peg_final` の骨組み — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

`GalilFinalAssembly.lean`（登録・build 0 errors・標準公理のみ）: `pal_in_peg_final : RecognizedByTotalPEG PAL`。**残る名前付き仮定は 6 個に確定**:
- (A) `H_oracle`：各語で cost 付き prefix oracle `CycleOracleMC`（区間構成の葉・出口ごとの `CostedRun`）
- (B) `H_truncTick`（未着文字を切っても tick が成り立つ）、`H_suf`（FIFO は語の接尾辞）、`H_needLe`（checkpoint m+1 前の消費 ≤ m+1）、`H_base`（`Tc 1 ≤ 2050`）
- (C) `H_realize`：局所 `LocalStep` 機械（ラッチ・stutter・2^18 手/文字）の受理 ↔ `LatchTrue`
（`H_letter`/`H_first`/`H_empty`/`needS 0`/`Preload.tc0/mono`/`O_cost`/報告点は証明済み。）
同時に登録: `GalilCostedFound`（found サイクルの `CostedRun`、shift あり・なし）、`GalilReplayGeneral2`（replay 中 chain の再証明、`WatchOk` 撤廃；残 `ReplaySpan`＝replay 中に found した周期ブロックが着地回文の周期であること — 真偽要検証、偽なら replay 中の break→restart を許す必要）。**無条件 PAL ∈ PEG は未完**。

## 2026-09-17 追記（台帳の骨組み完成・大量の穴埋め — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

登録・build 0 errors・標準公理のみ（Opus 5 での再開分、2 回目のまとめ）:
- **台帳の骨組みが閉じた**: `GalilLindley`（Lindley 漸化式 ≤ backlog、`run_on_time`）、`GalilLedgerCentres`（語だけの中心列 `Cw`、`cw_pal`）、`GalilLedgerQ64`（K=10 最小、`alpha' = 8M+12704`, `beta' = 4M+8026+shiftCost`, `2(α'+β')+1 = 90617`）、`GalilLedgerAssembly(2)`（`ledgerObligation_of_oracles'`：O-check/O-base/O-step/O-cost → `LedgerObligation`）、`GalilThrottledRun`（到着待ちで stutter する抽象走行、`O_step_throttled`（仕事量 2Δ+1）、`ledger_throttled`；残 `TruncTick`・`SufVM`・`Preload`）、`GalilLedgerThrottled`（τ = 2^18：`2·90617 ≤ 2^18`；局所 `nLocal` を 2^18 に）、`GalilLatchTracking`（受理＝ラッチ、`pal_in_peg_of_latch`）、`GalilArriveChain`（到着が chain verifier にも届く、`NoStart` 撤廃、`pal_in_peg_of_latch'`）、`GalilTickArrive`。
- **checkpoint と区間コスト**: `GalilReportPrefix`（任意 prefix の報告点、replay 後も）、`GalilCheckpoints`（`CycleOracleM` → 単一走行上の単調 checkpoint 時刻）、`GalilOracleM`（`cycleOracleM_of_pieces`、報告点後の再開は無仮定）、`GalilRunTrace`（サイクル記録、frontier 単調）、`GalilFrontMono`（frontier は tick ごとに非減少、`cycleOracleL'_of_pieces`；残 `CentreLive`）、`GalilIntervalCost`/`GalilPlaceEvents`/`GalilOneFallback`/`GalilTraceCost`（`PlaceEvent`・`ShiftEv`・`FallbackEv`、場所ごと fallback ≤ 1、`checkpoints_cost`：m ≥ 1 の区間コスト）、`GalilCostedFallback`（走査区間・目標一致・fallback+replay の `CostedRun`）。
- **H_run の穴**: `GalilOracleLocal`（局所形 `InvL`/`LocalReport`）、`GalilFoundRadiusBound`＋`GalilLaterRadius`（`radius ≤ 4090h−2052` を全 stage で穴なし：debt 台帳の打消し）、`GalilPrepClock`（準備区間を任意 clock で）、`GalilPrepMatch`（**`hmatch` は一般に偽** → 準備中の不一致は fallback：`prep_segment_construct_or_fallback`、`fallback_from_prep`）、`GalilCatchUpDistance`（`4h ≤ distance` ⇔ shift guard）、`GalilEarlyBreak`＋`GalilBreakTerminal`（`StageEntry` 完全放電）、`GalilReplayGeneral`（**空虚と判明**：`WatchOk`+`hgood` 矛盾、`GalilWatchOkInst.no_watchOk_instance`；`SpanCore`/`span_watch_tick` で再証明中）、`GalilGlueBLeaves`＋`GalilInvPlus`（`InvLP`＝`InvL`＋カウンタ、全 landing で保存、`SegReachedW`、`fallbackRouteP_of_mismatch''`）。
- **H_realize 局所層**: `LocalArrivalTiming`（**`hfast` 偽**：scaffold は fallback 中 scan 停止 → ラッチ方式へ）、`LocalReplaySwap`（2 本 swap は閉じない：`never_twin_of_sigma_lt`）→ `LocalReplayParked`（replay 中の右頭＝停めたビューの `left^[残 replay]`、左ミラー 1 本で足りる）、`LocalTick3`（shift/fallback 各モードの局所 tick、c₃ = 66）。
**走行中**: found の cost 付き走行、replay 中 chain の再証明、`CentreLive`、`TruncTick`、τ 汎用の到着待ち走行。**無条件 PAL ∈ PEG は未完**。

## 2026-09-17 追記（Opus 再開分：局所 oracle・ラッチ還元・台帳の橋の設計 — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

登録・build 0 errors・標準公理のみ: `GalilOracleLocal`（`InvL = InvS ∧ OutputRel`、`LocalReport`（現在状態からの報告）、`run_from_invL`、`H_run_of_oracleL`、`cycleOracleL_of_pieces`）、`GalilFoundRadiusBound`（第 1 stage `radius ≤ 2h ≤ 4090h−2052`、後段は `n < 4h`；残 `htime`/`hprev`/`hbar` 外注中）、`GalilPrepClock`（準備区間を任意 clock・比較混在で構成、`2h+2 < delay` 撤廃；残 `hmatch`・`1 ≤ lag0`）、`GalilCatchUpDistance`（**`4h ≤ distance` は候補からは出ず shift guard の margin ≥ 0 と同値**：shift 分岐で `places_of_guard`・`phase_of_guard`）、`GalilEarlyBreak`＋`GalilBreakTerminal`（break は一致比較なので終端でしか起きない ⇒ `stageEntry_after_found_closed`：`StageEntry` 完全放電）、`LocalArrivalTiming`（`Ahead` は位置上界から；**`hfast`（1 文字ごとに 1 place）は偽**：scaffold は fallback/shift/replay 中に scan が止まる）、`GalilLatchTracking`（**受理＝ラッチ**：最新文字位置の非 replay refresh の出力；`latch_sound`/`latch_complete`、最終定理 `pal_in_peg_of_latch`（仮定 `AbstractRun`・`H_realize`（受理↔`LatchTrue`）・`H_ledger`（回文なら T(w) までに refresh 済み報告点）・`H_empty`））、`LocalReplaySwap`（2 本ミラー swap は正しいが旧右ビューは再利用不能（`never_twin_of_sigma_lt`）→ 右頭は「停めた物理ビューの `left^[残 replay]`」と読む設計 (b) を外注中）、`GalilReplayGeneral`（`hquiet` 撤廃：replay 中 found → `FoundLanding`（`ReplayChainSeg` で replay 完走、chain 稼働中 landing）；残 `StartOk`・`WatchOk`/`hgood`）。

**台帳の橋（Plan 結論）**: `C m` は語だけで定義（位置 2m−1 の最左 live 中心、`m ≤ C m`・単調・回文なら `C |w| = |w|`）。`d (m+1)` = 報告点 m→m+1 の抽象 tick 数。到着で絞られた走行の遅延は Lindley 漸化式で `backlog d c m` に上から抑えられ、backlog 0 ⇒ `S m ≤ (m+1)τ`（τ = ticksPerSymbol、`T w = (|w|+1)τ`）。**定数が不整合**：`nLocal = 4096` では足りず `c ≈ 45296` → τ = 2^17 に；`stage_meets_barrier` の M ≥ 9600 は q=64 版の係数補題（K=10, M ≥ 240）で回避；chain shift 費用を 6 つ目の和分項に。補題順: cw 系 → q64 係数 → `runL_trace`（landing 列）→ **`report_at_prefix`（任意 prefix m の報告点到達）** → **`interval_decomp`（6 和分解）** → hledger' → **`tick_arrive_comm`**／到着絞り走行 → `lindley_le_backlog` → `ledgerObligation`。最大リスク：到着待ちは実機では `scan_wait` 背景 tick（search は進む）なので、pre-loaded 走行との一致ではなく「到着絞り走行そのもの」で checkpoint を定義すること。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（停止前の最終バッチ — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

登録・build 0 errors・標準公理のみ（usage limit 復帰後のバッチ）: `GalilPrepTrace`（prep 補題を `ChainTicks` トレース基準に、`ReplayChainSeg` からも供給可）、`GalilEmptyWord`（`H_empty`：`accept' q := outQ q ∨ q = initQ`、`init` モードには戻らない）、`LocalSchedule`（DP/fpp 消去・ミラー再構築の期限；**replay 後の右頭複写は 1 セル/tick 歩行では半径 > 2049 で不可能**（`walk_schedule_infeasible`）→ 中心同期ミラー・カーソルとの `vmViewSwap`（0 tick、`abs_vmViewSwap` 証明済）に設計変更）、`GalilOracleGlueB`（`hmismatch` 放電：`fallbackRoute_of_mismatch`、残 `FallbackCounters`（偶数窓長）と `FallbackTick`）、`GalilLastLowerBreak`（`3h ≤ last` は `4h ≤ distance` に還元＝phase 4 と同じ穴）、`GalilChainTickable`（`ChainOk` 不変量、`chainTickable_unless_break`、`no_break_during_replay`）、`LocalAlloc`（予備 3 本・P = 13 で役割単射保存）、`GalilOracleGlueA`（`hsegment` 放電（残 `hout/hlive/hends`）、`lastMatch_report`；**発見**：`GlobalReport` は `Control.initial` からの走行を要求するので、再帰途中では接頭辞が無い → oracle は局所形 `CycleOracle`（`ReportReach`）に再配線すべき）、`GalilPreludeEnds`（**発見**：`chainStart` の初期 lag は `radius` なので `PreludeEnds` の上界は `radius + 2h+2`；`prelude_done_before_extent'` は新義務 `radius ≤ 4090h − 2052` を要求）、`LocalChain`（chain のテープ化：`ChainL`、`absChain`、全 `ChainStep`/`ChainMatched` 構成子の単一動作ステップと模倣、`c₂ = 4`、`alias(last, boundary)` は役割回転＋detach ミラー；残 `SpareSynced`/`Refilled`/`Fed`/`ProperView` の保存）、`LocalTick1`（scan の wait/count/match の局所 tick、c₁ = 66、`tickL1_abs`・`tickL1_local`・`tickL1_inv`；残 `SearchLocal.effect`・chain tick・`Ahead` の保存）、`GalilOracleGlueC`（`hfound` 放電：`foundRoute_of_pieces` で `RealStop` 5 分岐・round 終端 5 分岐を全部処理、葉仮定約 30 個を列挙；`hfoundBg` は `prep_segment_construct` が `clock = delay` を要求するため未（`clock ≥ 2h+3` 版が要る））。

**次回の再開手順**: (1) `CycleOracle`（局所形）への再配線と GlueA/B/C の葉仮定の放電（多くは `InvS` に `OutputRel`・`FallbackCounters`・`Aligned` を足すだけ）、(2) `hquiet` を `ReplayChainSeg` 経路に置換、(3) `4h ≤ distance`（catch-up 台帳）、`radius ≤ 4090h−2052`、`prep_segment_construct` の clock 緩和、(4) 局所層：`TickL1`、`TickL` 全構成子＋stuttering 模倣、`vmViewSwap` を `GalilVML` に組込、O5 の到着タイミング、`LocalChain` を `GalilVML.chain` に接続。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（本日の到達点まとめ・作業停止前 — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

**状態**: `lake build --quiet PalPeg` 0 errors、`PalPeg.lean` 約 690 import、新規モジュール約 100 本（全て標準公理のみ、`sorry` なし）。usage limit のため一時停止。次回は下記「残作業」から再開。

**トップダウン骨組み（確定）**
- 最終定理 `pal_in_peg_of_tracking : Tracking M … → RecognizedByTotalPEG PAL`（`GalilRealizeOfTracking`）と `pal_in_peg_of_oracles`（`GalilRunSkeleton`）。`ScaffoldRun` の述語は `True` に弱化済み（最終定理は走行の内容を使わない）。
- **H_run** = `CycleOracleG`（`GalilRunSkeleton`）の放電。`GalilOracleDischarge.cycleOracle_of_pieces` が全終端の場合分けを済ませ、残りは名前付き仮定 11 個：`hex`（具体 Shared の replayExhausted）、`hsearch`/`hpres`（search 共走の存在・保存＝`SearchReady`、`GalilSearchReadyInv` で `RunEntries` に還元、第 1 stage は `GalilRunEntries`、後段は `GalilSearchWait`）、`hquiet`（replay 中に found にならない — **偽**：`GalilReplayFound`；対処は `GalilReplayChainSeg`（replay 中に chain が動く区間帰納）で `replay_after_fallback` を置換すること）、`houtReplay`（replay 後の出力健全性）、`hsegment`/`hended`/`hlastMatch`/`hlastMismatch`（区間終端→報告点：`GalilOracleGlueA` 外注中）、`hmismatch`（`GalilOracleGlueB` 外注中）、`hfound`/`hfoundBg`（`GalilOracleGlueC` 外注中）。
- 供給側の補題は揃っている：区間構成 3 種＋`lastLetter` 終端、`FoundCycle`/`FallbackCycle` 接着、`foundCycle_step'`（landing 記録・半径同定）、`cycle_found_noshift`、`cycle_found_*_bg`、`fallback_landing`（全輸出）、`inv_after_fallback'`、`replay_after_fallback`（→`InvScan`）、`fallback_from_watch`（round 途中の不一致）、`round_scan_construct`/`roundEnd_midFallback`、`GalilRoundPeriod`（ℓ+π=2C の同一性で `Good`/`hbreak` 完全放電）、`shiftPack_concrete`、`prep_segment_construct`＋`prep_then_watch_construct`、`GalilWatchPhase`（phase=4 は消費数 4h から；残り `htrace`・`hcount`）、`GalilPreludeDone`（残 `PreludeEnds`）、`GalilRadiusConsumed`/`GalilLastRadius`（`StageEntry` 放電、残 `Aligned` の配線と `3h ≤ last`）、L1–L11 全部。
- **H_realize** = `Tracking`。骨組み `LocalTracking.tracking_of_oracles`（O1–O6；O7 は消滅）。局所層：`LocalCounter`/`LocalRoles`/`LocalMirror`（radius・lower・length のミラー）/`LocalBuffers`/`LocalInputView`/`LocalBudget`/`LocalState`（`GalilVML`・`abs`）/`LocalArrival`（到着不可視の `abs'`、`Ahead`）/`LocalTick2`（restart 系 4 コミット）/汎用 `LocalStepRealize`（K 局所 step ⇒ `StructuredMachine`）。未：`LocalTick1`（scan tick）、`LocalChain`（chain のテープ化）、`LocalSchedule`（ジョブ期限、replay 後の頭複写は 1 セル/tick では間に合わず view swap 設計が必要）、`LocalAlloc`（役割単射・空きテープ）、`H_empty`（`initial.output = false` なので accept を `outQ ∨ q = initQ` に）、O5（到着タイミング・報告点）、chain の `last`/`periodLength` テープとの接続。
- **実時間台帳**：義務 1–5・7・8 形式化済み（機械仮定つき）、義務 6＝`MInv`。`hledger` の 5 和分解は未。

**モデル修正（本日）**: `periodLength` の +1 削除（Scala 準拠、具体 P で life 系が空虚やった）。**モデルの事実**: 背景 tick でも found → chain 起動（`hbg` 偽）、replay 中でも found → chain 起動（`hnfR` 偽）、round 途中の不一致は fallback（`shiftGuardVM` は `singlePositive` 要求）、`Restarted` は replay 後には成立せず `InvScan` で再帰。

**残作業（優先順）**: (1) GlueA/B/C の着地と `hquiet` を `ReplayChainSeg` 経路に置換 → `CycleOracleG` 完全放電 → `H_run` 完了。(2) `SearchReady` の `RunEntries` を stage ごとに再索引（連結全体は debt 非単調で偽）。(3) 局所層：`LocalTick1`/`LocalChain`/`LocalSchedule`/`LocalAlloc`、`TickL` の全構成子と stuttering 模倣、O5 の到着タイミング、`H_empty`。(4) `PreludeEnds`・`htrace`/`hcount`・`3h ≤ last`・`Aligned` 配線の小穴。

## 2026-09-16 追記（RunInv2・PrepConstruct・LocalTick2 — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

登録・build 0 errors・標準公理のみ: `GalilRunInv2.lean`（`inv_after_fallback'`：`R = 0 → Inv`、`0 < R → LandingReplay`；残る仮定 `hfrT`＝`Frontier` は `fallback_landing` に `t.right = left^[R] (right s.right)` を輸出させれば消える）、`GalilPrepConstruct.lean`（`prep_segment_construct`：copy h・分岐・back h+1 ＝ 2h+2 の背景 tick を `WatchSegE` として構成（`active_background_exists`：非 idle chain の各 `ChainStep` は背景 tick 1 つで実現可能）；`hh : 2h+2 < delay` はこの構成の都合（モデルは copy 中の比較も許す）、`hphase = 4` は watch 中に確立されるので未）、`LocalTick2.lean`（restart 系の局所コミット：`commitRestart`（1 step：役割再指定・`resetSeg`・`resetL`・ミラー detach・極性反転）、`commitReplay`（2 step）、`commitShift`（2 step）、`commitFallback`（2 step）；`abs_commit*` と `restartVM_commitRestart`/`replayStartVM_commitReplay`/`beginShiftVM_commitShift`；残: `length` のミラー（`work := inc length`）、chain 局所化との接続（`last`/`periodLength` を持つテープ）、役割単射の再確立と空きテープ割当、ジョブの期限）。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（H_run 骨組み完成・補題群 12 本 — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

登録・build 0 errors・標準公理のみ: `GalilRunSkeleton.lean`（`CycleOracle(G)` ⇒ `run_from_restarted`（測度 `2|w|−position center`）⇒ `H_run_of_oracleG` ⇒ `pal_in_peg_of_oracles`；残り＝oracle の放電）、`GalilBootVM.lean`（`initVM0`、`H_run_of_oracle_boot`）、`GalilRewindSafe.lean`（`RewindPhase` で mode ガード；`CentreLive`（rewind 中に中心が原点に達しない、MARKS 印の性質）が唯一の仮定）、`GalilPreludeDone.lean`（`prelude_done_before_extent`；`PreludeEnds`＝copy/back の tick 数 2h+2 が仮定）、`GalilShiftPack.lean`（`shiftPack_concrete`：`0<h ≤ radius` と `ScanInv` から `ShiftRun` 構成；`hlock` は使用点で自明）、`GalilReplayFound.lean`（**replay 中の found は Scala でも Lean でも起きる**：replayStart で search 再開、第 1 stage ≤ 504 tick ≪ 2047；`SearchHalted` 版の報告点補題）、`GalilReplaySegment.lean`（`replay_after_fallback`：r·delay tick の replay 区間、landing は `InvScan`（`Restarted` は search の条件で不成立）；仮定 `SearchQuiet`）、`GalilFoundLanding.lean`（`foundCycle_step'`：landing 制御記録・半径同定、`stageEntry_after_found`；仮定 `Aligned`（`Inv` に入れる）、`hend3/hcenterS`、`hlow`）、`GalilRoundPeriod.lean`（**同一性 ℓ+π = 2C**：左読みと chain 予測は原点中心の鏡像 ⇒ 終端前は予測が常に正しく（`Good`）、終端では origin の不一致対で必ず破れる（`hbreak` 完全放電）；`hmid` の残りは「round 途中で scan が不一致にならない」ではなく、**途中不一致は起こりうる**（周期が延びない入力）→ `RoundEnd` に 4 つ目の終端（fallback）が要る）、`GalilSearchWait.lean`（`searchRun_waiting`、`runEntries_of_later_stage`、`runEntries_two_stages`；連結全体の `RunEntries` は debt 非単調で偽、stage ごとに再索引が必要）、`GalilCycleNoShift.lean`（shift 無し found サイクル 3 本）、`LocalTracking.lean`（追跡骨組み `tracking_of_oracles`（O1–O7）；**発見** O4/O4b が矛盾：抽象 `Tick` に到着規則が無いので、到着は抽象で不可視にする設計（abs の incoming = far ++ pending）が必要）。区間構成 3 種に `lastLetter` 終端を追加済み。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（接着・背景起動・fallback landing・追跡還元 — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

登録・build 0 errors・標準公理のみ: `GalilReportReplay.lean`（replay 後の報告点 `scaffoldRun_report_after_replay`；仮定 `hnfR`＝replay 中に search が found にならない（調査中）、`hhead/hlast`）、`GalilCycleGlue.lean`（`fallbackCycle_of_constructions`・`foundCycle_of_constructions`：区間構成 3 本から前提束を組立；**構造的穴** `hland`：`life_restarted` は準備区間 `bs ++ dm :: cs`（copy h・分岐・back h+1）を要求するが L7b は空の準備区間を出す → `GalilPrepConstruct` 外注中）、`GalilCycleFoundBackground.lean`（`life_from_prep_*`（found tick を外した life）、`cycle_found_stepsAll_bg/_minv_bg`：背景 tick で chain 起動する found サイクル）、`GalilFallbackLanding.lean`（`fallback_landing`：制御記録・`Restarted`・`hpal/hmax`・`replay = ofNat R`・`ShiftIdle`・chain idle を一括輸出；`leftmost_after_fallback_landing`）、`GalilRealizeOfTracking.lean`（`Tracking M …`＝M の走行が 1 本の scaffold 走行を追跡して報告点で出力一致 ⇒ `pal_in_peg_of_tracking : RecognizedByTotalPEG PAL`；`H_realize` の ∀y 形は `Refreshed` 無しでは導けないが `pal_in_peg_of_galil`（結合存在形）経由で不要）。新たな穴: shift 前に period が破れる「shift 無し found サイクル」（`GalilCycleNoShift` 外注中）。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（L9 Inv・1 round の scan 構成 — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

登録・build 0 errors・標準公理のみ: `GalilRunInv.lean`（`Inv` 10 項目のうち stage/block/search/input は `Restarted` から無料（`restarted_unique`）、`inv_init` は完全放電、`inv_after_fallback` は `chosenRadius = 0` 限定（**発見**: 正の半径では landing が `replaying = true` なので `Inv` に replay 版が要る）、`inv_after_found` は `FoundResidual`（mode・stage・frontier・replayRest・shiftIdle）を仮定、`RewindSafe`・`frontier_replayRest_steps`）、`GalilRoundConstruct.lean`（`scan_half`：measure 付きで 1 round の scan を構成（燃料なし）、`round_scan_construct`＝`hround` そのもの；`hidx` は不要（lag 0 では `Internal` は idle のみ、一致比較は `chainMatched_watch_total` の二分法）；残る仮定 `hmid`（終端前は一致＋Good）・`hbreak`・`hpack`（`ShiftPack`）・`hsinv`・`hmeasure`）。外注中 13 本（replay 区間、fallback landing の輸出、found landing の制御記録と半径同定、`RewindSafe`、`hmid/hbreak`、`hpack`、`hcaught`、接着、背景起動 found、wait 相持ち上げ、局所層 TickL1/TickL2）。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（後段 stage'・mismatchOther・LocalState — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

登録・build 0 errors・標準公理のみ: `GalilSearchResult.search_later_stage'`（後段 stage の `.run` 突入で preload 恒等式・`Canonical debt`・count ≤ debt・予算を追加；残: wait 相 `enter_boundary` の `searchStep` への持ち上げと `es` の分割）、`GalilMismatchCaught.lean`（`match_of_palAt`、`run_lag_zero`（lag 0 は watch tick で不変）、`lag_zero_before_bound`（2k+2 tick で追いつく）、`no_mismatch_before_caught`（候補の回文延長は `2h`）、`mismatchOther_impossible(_of_candidate)`；残る仮定 `hcaught`＝不一致時に chain が既に watch である＝copy/back 前奏の完了）、`LocalState.lean`（`Ctr` 10 種、`GalilVML P`（InputView 5 本（search walker も）、分節カウンタ bank＋roles/pol、radius/lower ミラー、DP/fpp 二重バッファ、chain は抽象のまま）、`abs`/`absState`、`abs_job_irrelevant`・`abs_resetL_dp/fpp`・`abs_radius_mirror_negate`・`absCtrs_move`、局所性 `StepLocal`/`Local`）。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（RunEntries 第 1 stage・hbg は偽 — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

登録・build 0 errors・標準公理のみ: `GalilRunEntries.lean`（`runEntries_of_calibrated`：`Restarted` 形の search から calibrated 第 1 stage の `RunEntries`（長さ仮定は等式：debt 側条件が余剰イベントに非単調なため）；後段 stage（wait/double 経由）は `search_later_stage` に preload 恒等式・debt 条件を追加要求中）、`GalilBackgroundNotFound.lean`（**`hbg` は偽**：DP quantum はイベント非依存で背景 tick でも `.found` に達し、`backgroundS` が `chainStart` を据える（`chainAt_background_found`）。対処: L7a に `SegEnd.foundBackground` を追加、found サイクル補題の背景起動版 `cycle_found_*_bg` を外注中）。外注中: L9 `Inv`、replay 後の報告点、mismatch は catch-up 後のみ、1 round の scan 構成、サイクル接着、局所層 `LocalState`。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（L4/L7/L11 完了・局所層 6 部品・汎用実現補題 — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

登録・build 0 errors・標準公理のみ:
- L7a `GalilSegmentConstruct.lean`（`watchSegE_construct`：chain-idle 区間を燃料で構成、終端は `SegEnd`＝入力尽き/不一致/found；新仮定 `hbg`＝背景イベントで search が found にならない）、L7b `GalilSegmentConstruct2.lean`（`watchSeg_construct`、終端 `WatchStop`＝ended/mismatchWatch/mismatchOther/broke/outOfFuel；`Good`（lag 正）と `Ctx.hpres` は仮定）、L7c `GalilSegmentConstruct3.lean`（`rounds_construct_inv`：`RoundInv`（`rounds_leftmost` の束）を保って m round → `RoundEnd`＝break/入力尽き/guard 失敗；1 round の scan 半分は oracle `hround`、`roundInv_good` は `hidx`（span の 2 つ右まで周期）を要求）。
- L4 `GalilReportReach.lean`（`report_of_last_consume`：最後の文字を消費する一致比較の直後が報告点、`scaffoldRun_report_of_last_consume` は `H_run` の形そのもの；不一致＋shift 経路は `shift_done` 後、不一致＋fallback 経路は replay 完了後の一致比較まで報告点にならない（`Refreshed`・`notReplaying` が失敗、正しい））。
- L3 補強 `GalilReplayRest.lean`（`replayRest_tick`：全 24 構成子で保存、`replayStart` は `radius = ofNat r` を要求）、L11 完結 `GalilRadiusConsumed.lean`（`Aligned o`（`ofOnly`・`rounds_origin` から無料）、`radius_le_distance`、`foundCycleStage_final`：`3h ≤ last` と break データだけで `StageEntry`）、`GalilFppRunSupply.lean`（`fpp_scheduled` の停止走行から `Supplies`、`fppEnabled_along_phase`）、`GalilRunEntries.lean`（`RunEntries` 放電、詳細は次エントリ）。
- 局所層: `LocalInputView.lean`（`RTQueue`（Hood–Melville、登録済）を再利用、`InputView` は back/focus/near/far、`reposition_reaches`：距離 d の頭複写＝d 局所 tick、`two_views_absHead`）、`LocalBudget.lean`（`clear_fits_stage`、`counter_rebuild_fits_stage`、`radius_changes_slowly`：2048 tick 内に radius 変化 ≤ 1；`lag/margin` は copy 相を跨いで detach 不可、`work` は二重バッファ必須、`restart` の radius 保存は仮定）、汎用 `LocalStepRealize.lean`（`LocalStep`（K 局所）→ `realize : StructuredMachine … (n·(7K+2))`、`realize_srun`/`realize_SAccepts` 無条件；意味論は `readWin_eq`/`pos_sweep`/`rd_sweep`（`K ≤ pos` の余白が必要、`STape` は片側無限））。
**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（L3 Frontier・fpp quantum — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

登録・build 0 errors・標準公理のみ: `GalilFrontier.lean`（L3：`Frontier s`（`position right + replay ≤ 2·arrived`）、`frontier_replayStart(_scan)`、`frontier_tick`（具体 frame の全 25 構成子で保存；仮定 `ReplayRest`＝replaying フラグが下りてれば replay カウンタは reset、`hrep`＝replayStart 時の再播種）、`consume_not_replaying`：新文字を pop する tick は replay 中でない）、`GalilFppQuantum.lean`（`Safe`/`Reach`/`Legal`、`run_exists_of_reachSafe`、`fpp_run_exists(_of_legal)`；pc の範囲外は `marked_targets_lt` で排除済み、残るは `Legal`＝marked プログラムのテープ内容不変量、あるいは FPP 正当性定理の走行から直接引く）。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（L11 GalilLastRadius — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

`GalilLastRadius.lean`（登録・build 0 errors・標準公理のみ）: 境界台帳 `Aligned`・`aligned_word`・**`sweep_gap`**（未破断の掃引で `distance + 1 ≤ last + 2h`、`+1` の厳密さが break 場所を吸収）、`offset_gap`・`break_gap`（shift・break で不変）、`stageEntry_of_gap`（`3h ≤ last ∧ Rad ≤ last+2h → 3·Rad ≤ 5·last`）、`foundCycleStage`。残る唯一の隙間 `RadiusConsumed Rad c : Rad ≤ distance + 1`（半径−距離のロックステップ不変量、基底は `ReadOrigin.startBefore` の shift 版 `position start + shifts·h ≤ center` が必要）。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（L6・局所層 Roles/Mirror — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

登録・build 0 errors・標準公理のみ: `GalilSearchReadyInv.lean`（L6：`DpSafeRem`（残イベント数で再索引した `DpSafeHere`）、`ReadyRem`、`searchReady_begin/restarted/step/run`、`searchEffect_exists_of_restarted`；残る唯一の仮定 `RunEntries`＝`.run` 突入 tick で preload 恒等式と残イベント予算が成立すること、calibrated stage 補題との接続が未）、`LocalRoles.lean`（役割置換 `moveRoles`＋1 本の `resetSeg` で `dst := src; src := reset`、`absL_move`）、`LocalMirror.lean`（同期ミラー `pushAll/popAll/resetAll` は各テープ 1 動作、`absCtr_mirror`、`negate_via_pol`（= `initialDebt`）、再構築は犠牲複製 `don` を pop しつつ spare に push（`read_costs_value`：単頭では読取が値を壊す obstruction を定理化）、`rebuild_done`）。外注中: L3・L7a/b/c・L11・後段 stage・fpp quantum・`RunEntries` 放電、局所層 InputView/Budget、汎用 LocalStepRealize。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（L5/L10・L8 — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

登録・build 0 errors・標準公理のみ: `GalilChainReadyProgress.lean`（L5 `chainReady_of_blockInv`：`BlockInv` 超過分は copy の `CopyInv`、back の `canRight`、watch の `Good`/`canRight`、broken 排除のみ；L10 `found_cycle_center_progress`：中心は正確に `(m+1)·h` 前進（`MInv` 不要）、`fallback_cycle_center_progress`：`cen+1 ≤ 新中心`（境界 `2r = position` の除外 `hrn` が追加仮定））、`GalilTickFun3.lean`（L8 `PhaseEnabled`（shift/copy/home/fpp/markEnd/choose/rewind の前提）、`phase_tick_exists`、`EnabledP`/`tick_exists_P` で全モード被覆；fpp は Machine 9 の quantum 存在を仮定＝未存在の補題）。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（L1/L2・局所層 Counter/Buffers — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

登録・build 0 errors・標準公理のみ: `GalilEndOfInput.lean`（L1 `not_canRight_iff`：`¬canRight ↔ position = 2|w|`、L2 `last_letter_position`：最後の文字を pop する移動で `2|w|−1`、`position_le`）、`LocalCounter.lean`（分節 unary カウンタ：`push/pop/resetSeg` は 1 書込＋1 移動、`absCtr`、`absCtr_reset = reset`、極性反転 `neg_flip`；頭は最上マークの一つ上（frontier）に置く設計）、`LocalBuffers.lean`（`Buffered n`：二重バッファ、`resetL` は O(1)、`clearTick` で idle 側を並列 1 セル/tick 消去、`clearTick_done`（W+1 tick）、`abs_resetL_matches_control`：`GalilScaffoldControl.reset` と一致）。外注中: L3・L5/L10・L6・L8・L11、局所層 Roles/Mirror/InputView/Budget、汎用 LocalStepRealize。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（periodLength 修正の追従完了 — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

`GalilShiftH.lean`（`shift_h_eq_pos11`：shift の h ＝ DP の `pos 11`、`interior_eq_pos11`）・`GalilSearchResult.lean`（`periodLength_watchStart = ys.length+1`）を新定義に追従、`GalilStructuredSkeleton.lean` の `ScaffoldRun` を `galilFrameS`・`SoundScanNR` に変更（サイクル補題の形と一致）。全体 build 0 errors。外注中: L1/L2（入力尽き位置）、L3（frontier）、L5/L10、L6（`SearchReady` 保存）、L8（残モードの全域性）、L11（`Rad ≤ last+2h`）、局所層 `LocalCounter`、汎用 `LocalStepRealize`。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（主ループ Cycles・periodLength 修正・2 設計書 — 全体 build は 2 ファイル修正中・標準公理のみ・無条件 PAL は未完）

登録: `GalilMainLoopMInv.lean`（`FoundCycle`/`FallbackCycle` 前提束、継続スタイルの `Cycles`、`foundCycle_step`/`fallbackCycle_step`/`cycles_stepsAll_minv`、`leftmost_one`、`init_minv`；found 側の `Restarted` は `life_restarted` の前提が広いので前提束に同梱）、`GalilShiftH.lean`。
**モデル修正**: `GalilScaffoldTopGuards.periodLength` の `+1` を削除（FRONT セルを数えていた；Scala `beginChainShift` は DP の h＝複写ビット数で shift）。修正前は具体 `P := galilShared … beginShiftVM'` で `hint : interior.length+1 = h` と `hb` が両立せず life/rounds 系が**空虚**やった（抽象 `P` では無矛盾）。`GalilShiftH`/`GalilSearchResult` の周辺補題を追従修正中。
**H_run 構成計画（要点）**: `run_from_restarted` を測度 `2|w| − position center` の整礎再帰で。`Restarted` 状態の不変量束 `Inv` = Restarted・MInv・OutputRel・mode=scan/¬replay/clock=2048・StageEntry・SearchReady・BlockInv・Decodes・入力配置・ShiftIdle。3 分岐: 入力尽き（報告点＝最後の文字を pop した tick 直後、`¬canRight ↔ position = 2|w|`）／found／fallback。骨組み側の必須修正: `ScaffoldRun` を `galilFrameS`・`SoundScanNR` に。欠落補題 L1（`¬canRight ↔ position=2|w|`）L2（最後の pop で `2|w|−1`）L3（frontier 不変量）L4（区間の切詰め）L5（`ChainReady` ← `BlockInv`+`good_of_periodOn`）L6（`SearchReady` 保存＝debt 台帳、研究級）L7（区間構成 4 分岐、決定性不要）L8（shift/fallback モードの全域性）L9（`Inv` 再確立）L10（中心の前進）L11（`StageEntry`＝`GalilLastRadius`）。
**局所化計画（要点）**: 新層 `PalPeg/Local*`（既存無変更）、`GalilVML`・`TickL`・`abs`・stuttering 前方模倣＋2048 tick 内の進行補題。op1 reset＝区切り印 1 セル書込（分節 unary）、op2 死ぬ源の複写＝役割置換、生きる源＝常時同期ミラー＋背景再構築、op3 debt＝ミラー＋極性ビット、op4 `ofNat h`＝役割移動、op5 プログラム reset＝二重バッファ＋背景消去、op6/7 walker・頭複写＝カーソル専用入力複写テープ（実時間キュー）＋再配置ジョブ。見積 ≈3400 行。最大リスク: read-barrier と入力ビューの実時間キュー。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（局所性調査・restart 忠実性・EnabledR — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

登録・build 0 errors: `GalilTickFun2.lean`（`clock_pos_invariant`：どの Tick も clock を 0 にしない、`replay_match_of_minv`：replay 中の比較は `MInv` から必ず一致、`EnabledR`・`tick_exists_R`・`enabledR_of_minv`）、`GalilChainEncode.lean`（`Sym2` 25 種、`encodeChain`（8 テープ）、`encodeAll_injective`）、`GalilSearchResult.lean` 追加分（`search_later_stage`・`later_stage_found_result`：後段 stage の帰納ステップ；全体の帰納は `.wait` 相の debt 台帳（実時間台帳そのもの）と `false` 詰め物の非可換で未閉）。
**H_realize の構造的障害（局所性調査）**: Tick の大半は O(1) 局所やが、7 種の効果が非局所 — `Counter.reset`（Θ(値)）、カウンタ複写（`work := span`、`lower := last`、`chainStart` の radius 二重化）、`initialDebt`（テープ反転）、`ofNat h`、`GalilScaffoldControl.reset`（全 12/9 テープ消去）、`beginFallback` の `walker := p`（Place 全体複写）、`initVM`/`replayStartVM` の頭 3 重複写。Scala 回路はこれらを O(1) ポインタ代入（`Ref.select`）で行う**ポインタ模型**で、テープ機械としては未償却。対処は「消去・複写を 1 セル/tick の遅延モード（`.clearing`/転送関係）に置換」というモデル改修で、上位補題に波及する。汎用「K-局所 step ⇒ StructuredMachine」補題（`LocalStepRealize`）は外注中。
**restart の忠実性（Scala 調査）**: `restartVM` の `lower := last` は `ScaffoldGalil.scala:230-238` と一致、窓 `8·max(k,1)` も一致、`3·Rad ≤ 5·lower` は機械の guard ではなく監査契約（`GalilContracts.scala:207`）。欠けるのは連鎖不変量 `Rad ≤ last + 2h`（`GalilLastRadius` 外注中）。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（restart の設計仮定は偽 — 全体 build は SearchResult 改修中で一時保留・標準公理のみ・無条件 PAL は未完）

`GalilRestartStage.lean`（登録、標準公理のみ）: clock = delay は fallback/found 両 restart で `rfl`、init は `Control.initial` から継承（G1）。**G2: `3·Rad ≤ 5·value last` は found サイクル後の restart で偽**（反例 `(orgRadius,h,m,n,k) = (0,1,0,10,3)` 等）。`last` は連鎖の credit カウンタ（≈3h、減るだけ）で、半径は round 数 m・最終区間 n で増える。`search_result_at_tick`/`found_to_found` の `hstage` は現状放棄不可能な仮定。対処候補: (a) `Restarted` に stage 障壁を持たせ各サイクルで再証明（現状の `last` 意味では不成立）(b) `restartVM` の lower を連鎖 credit ではなく確認済み半径系の量に変える（Scala 正本の確認中）。`GalilSearchContractStage.lean`（登録）: `search_contract_of_stage` は `r ≤ span` が必要。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（tickFun・lag 正の Good・台帳 4/7/8 — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

登録・build 0 errors・標準公理のみ: `GalilTickFun.lean`（`sharedFun`（Shared を関数版で固定）、`ChainReady`/`ScanEnabled`/`Enabled`、`tick_exists`、`tickFun`＋`tickFun_spec`、`runFun_steps`；除外: shift/copy/…/rewind モードの全域性補題無し、scan で clock=0、replay 中の不一致、broken chain は restart guard で被覆）、`GalilGoodLag.lean`（`good_of_periodOn`・`good_run_of_periodOn`：round の `PeriodOn` から lag 正でも `Good`、残る仮定は span 包含 `hidx`・`canRight`・`Reads`）、`GalilLedgerObligations2.lean`（義務 4 `fallback_cost_move` n ≤ 12704δ+4012、義務 7 `telescope_busy`/`realtime_of_telescope`、義務 8 `buffer_transparent`/`pal_in_peg_of_galil_buffered`、`hledger_of_obligations`：5 和分解の下で区間台帳）。方針メモ: scaffold は clock 駆動（delay 固定）なので実時間性は構成的、台帳は「報告点に間に合う」＝`H_run` の中身に畳み込まれる。次: `Enabled` の replay 拡張・clock≥1、Tick の局所性調査（`H_realize` の要）。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（DP 共走の結果取り出し — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

`GalilSearchResult.lean`（登録・build 0 errors・標準公理のみ）: `SearchInv`（区間に沿った `SearchRun`）、`searchInv_watchSegE`、`search_result_at_tick`（restart 状態から idle 区間を経た found tick で `Result (take (8·max k 1+1)) k 0`・pc 346・pos 11 = 最小候補 h、または「前段 stage が非 found で終了」の escape）、`missed_pc_347`。隙間: (a) shift の h と pos 11 の同一視（`GalilShiftH` 外注中）、(b) 現在半径と stage 窓の較正（`GalilSearchContractStage` 外注中）、(c) 後段 stage の found（同エージェントに追加依頼）、(d) restart 時の `c0.clock = 2048` と `3·Rad ≤ 5·k`（設計仮定、未証明）。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（分岐網羅 (iii)(iv) — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

`GalilBranchInvariants2.lean`（登録・build 0 errors・標準公理のみ）: (iii) `PrepInv`（LEFT 印がテープ 7/10 で頭の左）を `prepare` で成立・全 `Tick` で保存、`prep_tick_exists`；(iv) `DpReached`/`DpSafeHere`（SafeQuanta 到達可能性）、`safeQuanta_exists_of_reached`（残予算で停止まで走り `Result` を出す）、`quantum_exists_of_reached`、`searchStep_exists`・`searchEffect_exists`（`SearchReady` の下で全モード）。残: `SearchReady` を top 側（`prepare` 発火・preload 入口）から配線、`hchain` 側は `BlockInv`、Tick 決定性は不要化の方針（`tickFun` は存在だけ使う）。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（GalilVM のテープ符号化 — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

`GalilVMEncode.lean`（登録・build 0 errors・標準公理のみ）: 記号 `Sym`（14 種）、`encodeVM : GalilVM → Fin 41 → STape Sym`、`encodeState`（tape 0 = clock）、有限制御 `CtlFin`（`Fintype`）、`encode_injective`（`(encodeCtl x, x.vm.chain, encodeState x)` が単射）。残: `chain : ChainVM` の符号化（`Token` 11 種の `Fintype` と watch/verifier/consume 状態のテープ化）。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（モデルの条件性の発見 — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

調査結果: Lean の `GalilScaffoldChainWatch.Internal` には lag 正のときの period break 構成子が無く（Scala `ScaffoldChain.scala:182` にはある）、`Good` は全上位補題の背景ステップ前提に埋め込まれた**暗黙の仮定**。モデルは「不忠実」ではなく「条件付き」（lag 正で消費が不一致にならない走行に限定）。対処: 新構成子を足さず、round の `PeriodOn`（span は周期 2h の回文）から「verifier の読取位置が span 内なら `Good`」を証明する（`GalilGoodLag.lean` を外注中）。scan 不一致が period break より先に起きる Galil の性質そのもの。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（Shared の関数化 — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

`GalilSharedFunctional.lean`（登録・build 0 errors・標準公理のみ）: `beginShiftVM'` は一意（`beginShiftVM'_unique`）・`shiftGuardVM` の下で存在、`beginShiftFun`＋spec；`beginFallbackVM'` は本質的に非関数的（walker が任意、`beginFallbackVM'_not_unique`）だが `place s` で固定すれば一意（`beginFallbackFun place`）；`restartVM entry` は一意・`restartGuardVM` の下で存在（`restartFun`）。`H_realize` の道筋: (1) テープ符号化（実行中）(2) Shared 固定（済） (3) `tickFun`（次） (4) `Prog` 化・固定 B (5) 前方模倣。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（分岐網羅 (i)(ii)・台帳義務 3 — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

`GalilBranchInvariants.lean`（登録・build 0 errors・標準公理のみ）: `OnBlock/OnPrefix/WatchBlock/CopyInv/BlockInv`、`BlockInv` は `chainStart` で成立し `ChainStep/ChainMatched/ChainTick/ChainSteps` で保存（transfer 補題の `Q` としてそのまま使える）、`watch_good_or_break`・`chainMatched_watch_total`（`WatchReady` の下で全域）、`copy_step_exists`・`copy_run_to_back`・`back_step_exists`。残: `Internal.take` に break 構成子が無い（lag 正の背景 tick で `Good` を入力供給から示す必要）、`canRight` は実時間入力供給、back 歩行の停止、`CopyInv` の到達可能性、(iii)(iv)。
`GalilSearchContract.lean`（登録・標準公理のみ）: `search_contract_of_idle_search`（DP 結果 `hres`（idle 分岐 pc=347）と `hlow` の下で `galil_move_of_contract` の契約そのもの）、`galil_move_of_idle_search`（k ≤ 4δ）。義務 3 は `hres`/`hlow` に還元（`cycle_found_minv` と同じ仮定）。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（cycle_found_minv — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

`GalilLiveCentreCycle2.lean`（登録・全体 build 0 errors・標準公理のみ）: `cycle_found_minv` — restart 状態から idle 区間・found tick・chain の一生を経て次の restart 状態まで `MInv` を運ぶ（`cycle_found_stepsAll` の `MInv` 版、追加仮定は `hex`・語の分解・`hM0`・DP 結果 `hres/hpc/hout/hlow`）。fallback 側は `cycle_fallback_minv` 済み。次: サイクル列の帰納（`StepsAll ∧ MInv` を Restarted→Restarted で反復）と報告点到達。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（台帳義務 1・2・5 の Lean 化 — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

`GalilLedgerObligations.lean`（Opus 外注、登録・全体 build 0 errors・標準公理のみ）: 義務 1 `stage_deadline`（`stageCost ≤ K·ell ∧ ≤ M·(2r−rad)`、K≥400・M≥24K の一様版；残る機械仮定 `hcost`）、義務 2 `verifier_catchup`（到着/サービス模型 `vlag`、追いつき 2·lag0、半径 4h 以内；残る仮定 `hmodel`）、義務 5 `replay_cost_le_window`（`galil_move_of_contract` を実窓に適用、残る仮定 `hreplay` と探索契約＝義務 3）、組立 `hd_of_interval_ledger`/`realtime_of_interval_ledger`（区間台帳 `d ≤ α·δ+β` ⇒ `realtime_of_predictable` の `hd`）。未: `hledger` の組立（義務 3・4・6・8）。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（CC：life_minv — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

`GalilLiveCentreLife.lean`（Opus 外注、登録・全体 build 0 errors・標準公理のみ）: `life_minv` — found tick → 準備区間 → watch → 最初の shift → rounds → 最終区間 → break → restart 直後まで `MInv` を運ぶ（`hscan` は `position sF.center` 中心、`hraw` で語を分解、`hex` 追加、rounds の `replaying` は `hr1`）。完全性の機械側は残り「主ループ合成（found/fallback サイクルで `MInv` を一周させ、報告点まで到達）」のみ。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（トップダウン骨組み — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

`GalilStructuredSkeleton.lean`（Opus 外注、登録・全体 build 0 errors・標準公理のみ）: `pal_in_peg_of_galil`（`StructuredMachine M`・`Pof/qof/firstOf/delay`・`H_letter`・`H_first`・`H_report`・`H_empty` から `RecognizedByTotalPEG PAL`）。`ReportPoint`（非 replay・`ScanInvariant`・`MInv`・右頭が `2|w|−1`）と `Refreshed` を定義し、`output_iff_pal`（`refresh_exact` から報告点の出力 ↔ `w ∈ PAL`）を証明済み。残る実質は `H_report` ＝「scaffold の走行が報告点に到達する」（H_run）と「M の受理がその出力と一致する」（H_realize）の 2 つに分割中。以後はこの仮定リストを潰す。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（並列バッチ 9：restart 後の lower 履歴 — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

`GalilBreakNoBelow.lean`（Sonnet 外注、登録・全体 build 0 errors・標準公理のみ）: `noBelow_after_break`（span [a,b0] に p 未満の周期が無く、[a,b] で周期 p が破れれば、[a,b] に p 以下の周期が無い）と `noBelow_after_break_of_mismatch`（不一致対から直接）。`break_not_period` と合わせ、restart 時の「lower 以下の周期が無い」不変量は純粋部分が閉じた。残りは機械側の合成（`life_minv`）と骨組み。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（並列バッチ 8：break の周期破れ — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

`GalilBreakPeriod.lean`（Opus 外注、登録・全体 build 0 errors・標準公理のみ）: `break_not_period`（round の起点 `o : ReadOrigin raw`、終端比較状態 `s`、`hend : singlePositive s.cycle = true`、外側一致 `hmatch` の下で `¬ PeriodOn (encoded raw) (2h) (start+1) (position (right s.right))`）、`break_witness`（存在形）、`break_symbols_differ`、`break_prediction_mismatch`、純粋補題 `no_period_of_break`。既存の `matched_restart` は `broken = true` しか出さず、破れを起こす不一致は内部で消費されていたので、`check_pair` と `read_prediction_window` から再構成した。これで restart 後の lower 履歴（「span に lower の周期 2h が無い」）の材料が揃った。方針転換: 以後はトップダウン（`StructuredMachine` 骨組みを明示仮定付きで先に書き、残り仮定だけを外注）。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（並列バッチ 7：報告点の接続 — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

`GalilReportComplete.lean`（Opus 外注、ルート登録・全体 build 0 errors・標準公理のみ）: `leftFirst_iff_pal`（報告点 `position s.right = 2k−1`・非 replay・`ScanInvariant`・`MInv` の下で `leftFirstVM s ↔ IsPal (raw.take k)`）と `refresh_exact`（`refresh (galilFrame P q first)` の出力 `o = true ↔ IsPal (raw.take k)`）。これで「中心不変量 `MInv` が保たれていれば報告点の出力は回文フラグと一致」が閉じ、出力の完全性は `MInv` の維持（`life_minv`・主ループ合成）に還元された。**無条件 PAL ∈ PEG は未完**（残り: `life_minv`、restart 後の lower 履歴、主ループ MInv 合成、分岐網羅 (i)–(iv)、台帳義務 1・2・5、`StructuredMachine` 実現）。

# Claude Code 再開用 — PAL ∈ PEG の Lean 証明

更新: 2026-09-14（JST）。ユーザーから「現在の進捗を書き出して、あとでClaude Codeがresumeできるように」と依頼され、証明追加を止めて作成した。

## 最初に押さえること

## Resume checkpoint — 2026-09-15、Claude Code 再開

追記（2026-09-16 午前、並列バッチ 6）：AA `GalilRoundsLeftmost.lean`（**`rounds_leftmost`**：`Rounds` 帰納で各終端比較の `MInv`＋「2h 未満の周期なし」を継承、`periodOn_congr`）、BB `GalilNoBelowFirst.lean`（`noBelow_first`／`_of_result`：最初の終端比較の最小性）、DD `GalilPrepLeast.lean`（`prep_watch_start_least`：chain の半周期 h ＝ DP 出力 `(denote y.config).pos 11`、`found_output` で定義的一致；`result_pc_of_candidate`、`no_candidate_below_of_least`、`prep_least_no_candidate`）。全体 build 成功・標準公理のみ。外注中：CC `GalilLiveCentreLife.lean`（`life_minv`：found tick → 準備 → watch → 最初の shift → 周回 → 最終区間 → 破れ → restart で `MInv` 保存）。無条件 PAL は未完。

追記（2026-09-16 午前、並列バッチ 5）：V `GalilPeriodNext.lean`（`periodOn_restrict`／`periodOn_mul`／`periodOn_extend_dvd`（`0 < P` と長さ条件を追加）／`periodOn_fineWilf`／**`noBelow_next`**：周回間の最小性継承）、W `GalilPeriodSpan.lean`（`periodOn_span_of_next`／`hasPeriod_span_of_next`：右半分の周期＋現在と次の回文 ⇒ span 全体の周期 2h）、X `GalilReadOriginPeriod.lean`（`ReadOrigin.reshift_period`／`reshift_periodOn`）、Y `GalilCandidateWindow.lean`（`candidate_window_mono`、`no_candidate_below_least`）、Z `GalilOriginPeriod.lean`（`ReadOrigin.shifted_position`／`shifted_unbroken`／`origin_period`／`origin_periodOn`／**`origin_periodOn_right`**：各 origin の終端比較で右半分＋新 place の周期 2h、空トレースで `joined_input_period`）。すべてルート import 済み・標準公理のみ。外注中：AA `GalilRoundsLeftmost.lean`（`rounds_leftmost`：`Rounds` 帰納で `MInv`＋「2h 未満の周期なし」を各終端比較へ）、BB `GalilNoBelowFirst.lean`（`noBelow_first`／`_of_result`：最初の終端比較の最小性を DP 最小性＋origin の周期から）。進捗ボード artifact を v3 に更新。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（2026-09-16 深夜、並列バッチ 4）：U `GalilScaffoldTopProgressS.lean`（`backgroundS_exists`（探索 step と chain 効果の存在から background の存在）、`compare_progress_S`、`scan_tick_exists`：scan・`1 ≤ clock`・`replaying = false`・探索／chain の存在仮定の下で次 tick が存在。replay 中の不一致には `restart` しか無いので `replaying = false` を仮定）、S `GalilMinimalPeriod.lean`（`palAt_pair_of_period`、`result_least`（`Result` の証人 k は最小候補）、`no_short_period_of_minimal`：span の周期 2h＋DP 最小性（窓 `take (k+1)`）＋lower 以下の周期なし ⇒ 2h 未満の周期なし、Fine–Wilf 経由；元の `no_candidate_of_result` は偽（反例 `0^9`）で `result_least` に修正）。外注中：V（`noBelow_next`）、W（`periodOn_span_of_next`）、X（`reshift_period`：終端比較で検証済み区間の周期 2h を `joined_input_period` から）、Y（`candidate_window_mono`、`no_candidate_below_least`）。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（2026-09-16 深夜、並列バッチ 3）：L `GalilLiveCentreCycle.lean`（`cycle_fallback_minv`：Restarted＋`MInv`＋`SpanRep` → idle 区間 → 不一致 → fallback 一周 → `Restarted`＋`SpanRep`＋`MInv`）、T `GalilLiveCentreSegs.lean`（`minv_watchSeg`／`minv_scanSeg`）、N `GalilFallbackCost.lean`（`fallback_ticks_le`：fallback 一周（copy→replayStart）の tick 数 n ≤ 1588·(ℓ+1)+836；FPP の量子数上界を `FppOutcomeLe` で運ぶ再証明。台帳義務 4 の Lean 化）、Q の調査結果は ASSEMBLY_PLAN「分岐網羅の義務」節。**不変量 (3) の修正**：shift 直後の短い span に「lower 以下の周期なし」を要求すると反例あり ⇒ 終端比較時（半径 ≥ 2h）の「2h 未満の周期なし」（`NoBelow`）を FW で継承（ASSEMBLY_PLAN に記録）。外注中：S（`no_short_period_of_minimal`）、U（`backgroundS_exists`／`compare_progress_S`／`scan_tick_exists`）、V（`noBelow_next`：FW による周回間の継承）、W（`periodOn_span_of_next`：右半分の周期＋現在と次の回文 ⇒ span 全体の周期 2h）。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（2026-09-16、並列バッチ 2：chain shift の材料）：Opus/Sonnet 並列で新モジュール：`GalilLiveCentreMismatch.lean`（`not_live_of_mismatch`：不一致 ⇒ 中心は次の place で死ぬ）、`GalilSegmentCount.lean`（`watchSegE_steps_length`＝イベント数 tick、`watchSegE_clock_le`、`scanSeg_steps_ge`）、`GalilShortPeriod.lean`（`no_short_period_drop`／`_shift`：群補題 `hasPeriod_minimal_of_suffix` で shift 後も短周期なし、`hasPeriod_take_drop`／`drop_drop`）、`GalilCandidatePeriod.lean`（`candidate_hasPeriod`、`candidate_palAt`、`candidate_periodOn`：DP 候補 ⇒ [C−4h, C] の周期 2h）。自分で `GalilLiveCentreShift.lean`（`Span`、`leftmost_shift`：C 死亡＋C+h 生存＋span に 2h 未満の周期なし ⇒ C+h が最左、`live_shift_of_palAt`）。`ReadOrigin` には `reshift_palindrome`（round 終端で中心 o.center+2h・半径 o.radius+1 の回文）と `joined_input_period`（検証器が読んだ範囲の周期 2h）が既にある。実行中の外注：L（fallback 一周の `MInv` 合成 `cycle_fallback_minv`）、Q（tick の全域性の調査）、N（fallback 一周の tick 上界）、S（`no_short_period_of_minimal`：Fine–Wilf で「span の周期 2h＋DP 最小性＋lower 以下の周期なし ⇒ 2h 未満の周期なし」、`palAt_pair_of_period`、`no_candidate_of_result`）、T（`minv_watchSeg`／`minv_scanSeg`）。全モジュールはルート import 済み。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（2026-09-16、`Live` の厳密化と周期区間の和集合）：`Live raw n c` に「左端 ≥ 1」（`n < 2*c`）を追加（原点の gap（index 0）に達した回文は機械では不一致扱い＝候補から外れるので、モデルと一致させた）。`leftmost_fallback` に `hrn : 2*r < n+1` を追加（B は `chosen_spec` から供給）、`live_of_scanInvariant` は `leftPresent` から左端 ≥ 1 を導出。Opus D: `GalilPeriodUnion.lean`（`PeriodOn x p a b`、`periodOn_union`（重なり ≥ p の周期区間の和集合）、`hasPeriod_slice_iff`、`encoded_periodOn_even`（符号化語の周期は偶数）、`periodOn_mirror`（回文中心での鏡映））。全モジュールをルート import、全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（2026-09-16、完全性の機械側：区間・fallback・replay、並列化開始）：コウタの許可で Opus サブエージェント並列を開始。A: `GalilLiveCentreSeg.lean`（`leftmost_scanEvents`、`leftmost_watchSegE`／`watchSeg`／`scanSeg`、`scanSeg_heads`）、B: `GalilLiveCentreFallback.lean`（`leftmost_after_fallback`：`fallback_restarted` の輸出＋`span_covers`＋`position_represent` で fallback 後の新中心が最左の生存中心）、C: `GalilPeriodCentre.lean`（`hasPeriod_of_isPal_drop`、`isPal_drop_of_hasPeriod`、`isPal_span_of_palAt`、`palAt_of_isPal_span`、`span_hasPeriod_of_two_palAt`、`palAt_shift_of_period`、`no_centre_below_period`：chain shift の数学）。自分で `GalilSpanCounter.lean`（`SpanRep`：length = 2·radius+1 の各遷移での保存、`span_covers`）と `GalilLiveCentreReplay.lean`（`MInv raw c s`：replay 中は「replay カウンタ＝保存位置までの距離」＋保存位置で `Leftmost`、非 replay 中は右ヘッド位置で `Leftmost`；`minv_match`、`minv_matchR`（尽きた時点で右ヘッドが保存位置）、`minv_watchSegE`、`minv_after_fallback`）。全モジュールはルート import 済み、標準公理のみ。残り：不一致 ⇒ 中心死亡の補題、fallback 一周の `MInv` 合成、chain shift の機械側（周期 2h の供給と最小周期性）、restart、報告点。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（2026-09-16、完全性の核＝最左の生存中心）：新モジュール `GalilLiveCentre.lean`（ルート import 済み）：`Live raw n c`（右 place n で中心 c が生きている＝`PalAt (encoded raw) c (n−c)`）、`Leftmost raw n C`（C が最左の生存中心）、`live_pred`、`live_of_scanInvariant`、`leftmost_match`（一致比較で保存）、`leftmost_fallback`（C が n+1 で死んだとき、窓が旧半径以下を全て覆えば fallback の最大半径 r による新中心 n+1−r が最左の生存中心）、`leftmost_report`（letter place 2k−1 で `IsPal (raw.take k) ↔ C = k`）。これが台帳義務 6（中心不変量）の数学側。残り：機械の fallback（`fallback_restarted` の最大性＋窓長 ≥ 2·旧半径+1 の供給、`length` カウンタと半径の関係）、chain shift（最小周期で中心 C+h へ）、restart／replay、報告点の接続。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（2026-09-16、予算プローブの実測結果）：`RealtimeGalil`（FIFO service = 2×predictability = 6338 遷移／文字、q=64 派生値）で 42 語（ランダム 30・60、偶数回文 40・80、奇数回文 41・81、二重回文 81・161、a^80、(ab)^40、(ab)^30 b (ba)^30、(aab)^40 aa、(aabab)^20 a (babaa)^20 長さ 201）の全接頭辞を判定：**見逃し 0、全接頭辞正答**（TOTAL_MISMATCHES=0）。`REALTIME_BUDGET = 2048` ではなく派生値 6338 での実測で、派生議論の範囲内。最初の重い版（長さ 240 まで＋drain 実行）は 28 分で打ち切り。プローブは一時ファイルで、テスト木から退避済み（`scala/pal` の `sbt test` 時間を増やさないため；scratchpad に `WorkBoundProbeSuite.scala` と `probe2_results.log`）。これは有限テストであり、任意長の証明ではない。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（2026-09-16、予測可能性 ⇒ 実時間の抽象定理）：新モジュール `GalilPredictability.lean`（ルート import 済み、Mathlib のみ依存）：`backlog d c`（毎ラウンド 2c のサービス、ラウンド i に仕事 d i 到着の FIFO 残量）、`work d j i`（ラウンド j+1..i の到着仕事）、`exists_last_zero`（busy 区間の始点）、`backlog_telescope`、`backlog_zero_of_bounds`（全窓 j+1..i の仕事が 2c(i−j) 以下なら残量 0）、`work_bound_of_centres`（中心 C が単調・非遅延 m ≤ C m、仕事 d(m+1) ≤ c·(C(m+1)−C m+1) なら、C i = i の i について全窓の仕事 ≤ 2c(i−j)）、**`realtime_of_predictable`**（その仮定の下で正答ラウンドの残量 0＝`GALIL_CLOCK.md` §Predictability の台帳義務 7 を Lean 化）、`wrapper_exact`（追いついていれば源の答え、遅れていれば 0 を返すラッパーは、源が健全・完全で正答時 C i = i なら全ラウンドで正確）。残る契約は台帳義務 1〜6（仕事 d の費用上界、中心の単調・非遅延、正答時 C i = i）。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（2026-09-16、Galil の move 補題の組合せ論部分）：新モジュール `GalilMoveLemma.lean`（ルート import 済み）：`hasPeriod_of_isPal_take`（回文 x の長さ k の回文接頭辞 ⇒ x は周期 |x|−k を持つ）、`window_hasPeriod_of_chosen`（fallback 窓 T が回文なら T は周期 |T|−(2·chosenRadius T+1)＝中心前進量の 2 倍を持つ）、`isPal_take_of_hasPeriod`（逆向き：周期 p ⇒ 長さ |x|−p の接頭辞が回文）、`chosenRadius_ge_of_period`（窓の周期 p（|T|−p 奇数）⇒ chosenRadius ≥ (|T|−p−1)/2：fallback は周期の半分を超えて中心を進めない＝完全性側の材料）、`fallback_window_period`（窓 = 新記号 x :: 回文 P（|P| = 2k+1）のとき P は周期 |P|+1−2r = 2δ（δ = k+1−r は中心前進量）を持つ）、**`galil_move_of_contract`**（探索契約「P は k/2 以下の周期を持たない」の下で k ≤ 4δ：Galil の move 不等式を契約 1 個に還元）。Galil の move 不等式 k ≤ 4δ は、これに「半径の半分以下の周期は chain が既に捕捉している」という探索契約（完全性側、未着手）を足せば従う。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（2026-09-16、実時間台帳の紙スケッチ）：`ASSEMBLY_PLAN.md` に「実時間台帳の紙スケッチ」節を追加（8 義務：stage 締切／DP 発見と追いつき／**Galil の move 不等式 k ≤ 4δ（Lean 未存在・仕様側も留保）**／fallback 費用／replay／**中心不変量（完全性の核、未着手）**／telescoping／SCA ラッパー）。Lean の較正は `delay_calibration`（K=63、M=2048）、Scala 派生は K=10、M=256、service 6338。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（2026-09-16、経路比較・要判断）：無条件 PAL への 2 経路の現状。**旧経路（直接 SCA 構成、codex／GPT-5.6 が 09-07〜09-10 に推進）**：数学側の実時間予算（`Consumption x 8 b`、`PassPeriodSum`、`prefix_verifier_deadline`）は無条件で証明済み。最終定理 `pal_SAccepts_iff_embed`／`_embed9`（`FullMachineProg.lean`、HEAD には存在、作業ツリーでは `FullMachineProg.lean`／`StageLifecycleProg.lean` が未コミットのまま削除）は、具体機械側の仮定 `D : DecompOnTapes`、`hcost`／`hadvance`（走査費用）、`hpow`、`hinitS`（前処理初期状態）、`hround`／`hstepF`／`hstepG`／`hstepI`（具体 Prog がラウンド効果を実現）を残す＝有限制御の差し込みが大量に未完。**現行経路（Scala 忠実モデル、09-14〜）**：オンライン制御器の soundness は本日 `StepsAll (SoundScanNR)` で主ループ 2 周まで閉じたが、Scala 正本自身が「certified real-time recognizer ではない／仕事量台帳は未検証」と明記しており、固定 B の `StructuredMachine` に落とす実時間上界は紙の上でも未確立（予算 2048 の実測プローブ実行中）。判断事項：どちらの経路で無条件を狙うか（旧経路＝残りは差し込み作業だが量が多い／現行経路＝台帳の証明が先で、偽の可能性もある）。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（2026-09-16、主ループ 2 周の全状態で出力健全、および実時間に関する重要な発見）：新モジュール `GalilScaffoldTopOutputCycle.lean`（ルート import 済み）：`cycle_found_stepsAll`（`Restarted` → idle 区間 → found tick → chain の一生 → restart tick：`found_life`／`life_restarted` と同じ仮定の下で、全状態で `SoundScanNR`、終端は restart 後の状態）、`cycle_fallback_stepsAll`（`Restarted`＋`ShiftIdle` → idle 区間 → 不一致 → fallback 一周 → `Restarted raw t 0 reset`：全状態で `SoundScanNR`）。主ループの帰納は `stepsAll_trans` の反復なので、soundness 側は「各 checkpoint でどちらの周に入るか（分岐網羅）」を除いて閉じた。**重要**：Scala 正本 `docs/palindromes-in-peg/SCA_GALIL.md` は自身を「not a completed PAL PEG or a certified real-time recognizer」「A report made while behind is zero; proving the bound is what would exclude missed positives」「The proposed ledger here remains unverified」と明記し、`TRANSLATION_STRATEGY.md`（2026-09-06）は四段の機械翻訳を「実験であって現行の主経路ではない」としている。Lean の最終定理 `pal_in_peg_of_structured` は固定 B micro-step／文字の `StructuredMachine` を要求するため、この仕様の上では仕事量上界（Galil の nonchain 補題＋stage 締切の台帳）を証明せん限り無条件 PAL に到達できない。予算 2048 の実測プローブ（`scala/pal/src/test/scala/pal/WorkBoundProbeSuite.scala`、一時ファイル・コミット対象外）を実行中。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（2026-09-16、init と restart tick の健全性）：新モジュール `GalilScaffoldTopOutputInit.lean`（ルート import 済み）：`outputRel_transfer`（右ヘッドと出力が同じなら移送）、`soundScanNR_vm`、`outputRel_position_one`（右ヘッド位置 1 なら任意の出力が健全：1 文字接頭辞は回文）、`init_stepsAll`（init tick は `SoundScanNR` の 1 tick 走行、終端 `Restarted (a :: rest) t 0 reset`）、`stepsAll_keep_tick`（制御と右ヘッドを保つ tick＝restart tick で健全走行を延長）。これで init／idle 区間／found→chain の一生／restart／不一致→fallback の各部品が `StepsAll (SoundScanNR raw)` で揃った。全体 build 成功・標準公理のみ・無条件 PAL は未完。次: 主ループ 1 周（idle 区間＋found＋一生＋restart／idle 区間＋不一致＋fallback）の合成、主ループ帰納、フロンティア基準への変換、出力完全性。

追記（2026-09-16、fallback 一周の全状態で出力健全）：新モジュール `GalilScaffoldTopFallbackRestartAll.lean`（ルート import 済み）：`SoundScanNR raw st := mode = scan → replaying = false → OutputRel`（replay 中は右ヘッド基準の健全性が成り立たないので条件つき）、`soundScanNR_of_soundScan`、`fallback_restarted_All`（`fallback_restarted` の述語つき走行版＋`chosenRadius = 0 → refresh 節`）、`fallback_restarted_soundNR`（`onLetter = onLetterVM raw`、`leftFirst = leftFirstVM`、始点の `OutputRel` から、不一致比較→fallback→scan 再入の全状態で `SoundScanNR`、終端は `Restarted raw t 0 reset`；再入時 replaying=false なら r=0 で refresh 節と `Restarted` の走査不変量から `output_sound`）。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（2026-09-16、fallback 一周を状態述語つき走行に）：新モジュール `GalilScaffoldTopFallbackAll.lean`（ルート import 済み、`FallbackS`／`FallbackCycleS` からの機械的移植）：`NoScan st := st.ctl.mode ≠ .scan`、`stepsAll_transfer_generic'`、`stepsAll_transfer_fallback_S`／`_fpp_S`／`_markEnd_S`／`_rewind_S`（各相の走行を `StepsAll NoScan` で `galilFrameS` へ転送）、`copy_home_start_All`／`fpp_then_markEnd_All`／`choose_then_rewind_All`／`fallback_chain_All`（copy → replayStart まで `StepsAll NoScan`）、`fallback_to_scan_All`（任意の Q について「非 scan で Q」「再入状態で Q」⇒ 一周の全状態で Q；`r = 0 → refresh 節` を新たに輸出）、`scan_fallback_cycle_All`（不一致比較から scan 再入まで、始点・終点の Q を仮定して全状態で Q；`chosenRadius = 0 → refresh 節` 輸出）。これで `SoundScan`（replay 中は無条件では成り立たないので replaying=false 条件つきに落とす必要あり：`SoundScanNR`）を fallback 一周に通せる材料が揃った。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（2026-09-16、chain の一生の全状態で出力健全）：新モジュール `GalilScaffoldTopOutputLifeAll.lean`（ルート import 済み）：`scanSeg_mode`、`first_shift_stepsAll`（`round_next` の終端比較＋shift 相を切り出し：`hend`／`hpred`／`hlen` 不要、`hz : zero w.lag = true` を仮定、1+(h+1) tick の全状態で `SoundScan`）、`life_stepsAll`（found tick → 準備 `WatchSegE` → watch `WatchSeg` → 最初の shift → `Rounds` m 周 → 最終 `ScanSeg` → 破れ比較まで、`found_life` の内側の仮定＋`OutputRel cF sF`・found 時の `ScanInvariant`・最初の shift 終端の `Entry`・破れ比較後の `ScanInvariant` から、走行の**全状態**で scan モード時の出力が右ヘッド基準で健全）。全体 build 成功・標準公理のみ・無条件 PAL は未完。次: fallback 一周（copy/home/fpp/markEnd/rewind/replayStart は非 scan なので空、replay 区間は `SoundScan` が右ヘッド基準で成立するが意味付けはフロンティア基準へ要変換）と init、主ループでの接続、出力完全性。

追記（2026-09-16、再 shift 周回の全状態で出力健全）：新モジュール `GalilScaffoldTopOutputRound.lean`（ルート import 済み）：`SoundScan raw st := st.ctl.mode = .scan → OutputRel raw st.ctl st.vm`、`stepsAll_transfer_generic`（`steps_transfer_generic` の `StepsAll` 版：M モード内の状態は Q、E モードは tick を持たない）、`shift_stepsAll_S`／`shift_phase_stepsAll_S`（shift 相を `StepsAll` で `galilFrameS` へ転送、出口の Q は refresh の健全性）、`round_stepsAll`（`round_next` と同じ仮定＋区間頭の不変量・`OutputRel`・shift 終端の不変量 ⇒ 一周 k+1+(h+1) tick の全状態で `SoundScan`）、`rounds_stepsAll`（`Entry` から m 周の全状態で `SoundScan`、`rounds_origin` で次周の不変量）。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（2026-09-16、refresh 点と全状態の出力健全性）：新モジュール `GalilScaffoldTopOutputLife.lean`（`outputRel_of_refresh'`／`_S'`：任意の制御へ、`entry_scanInvariant`（`Entry` から走査不変量）、`outputRel_matched_refresh`（一致比較で半径 +1 と健全性）、`watchSegE_output_inv`／`watchSeg_output_inv`（終端の不変量つき）、`rounds_output`（再 shift m 周で `OutputRel` 保存：各周の走査は `Entry` の不変量、shift 終端の refresh は `rounds_origin` の次の origin の不変量））と `GalilScaffoldTopOutputTrace.lean`（`StepsAll F delay Q k x y`：全状態が Q を満たす走行、`stepsAll_steps`／`_head`／`_last`／`_trans`／`_mono`／`stepsAll_of_steps`、`SoundOut raw st := OutputRel raw st.ctl st.vm`、`matched_invariant`、`watchSegE_stepsAll`／`scanSeg_stepsAll`／`watchSeg_stepsAll`：区間の**全状態**で出力が右ヘッド基準で健全）。ルート import 済み。注意：`OutputRel` は右ヘッド位置基準なので、shift 中・replay 中（右ヘッドが入力フロンティアより後ろ）の出力の意味付けは別途フロンティア基準の関係が要る（実時間供給と一緒に扱う）。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（2026-09-16、出力の健全性）：新モジュール `GalilScaffoldTopOutputSound.lean`（ルート import 済み）：`OutputRel raw c s`（output=true ⇒ 右ヘッド位置 2k−1 の接頭辞 `raw.take k` は回文）、`outputRel_of_refresh`（`refresh_sound` の包装）、`scanInvariant_matched`、`watchSegE_output`／`scanSeg_output`／`watchSeg_output`（`ScanInvariant` を運びつつ区間に沿って `OutputRel` を保存：background は出力とヘッドを変えず、各一致比較で半径 +1 の不変量から `refresh` の健全性）、`report_sound`（右ヘッドが gap 上でなく `OutputRel`＋`ScanInvariant` なら output=true ⇒ 読んだ接頭辞は回文）。残り：区間外の refresh 点（shift 終端・replayStart・init）の `OutputRel` 供給、出力の完全性（回文なら true）、分岐網羅、実時間供給、`StructuredMachine` 化、`SAccepts ↔ PAL`。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（2026-09-16、init と不一致前提の供給）：新モジュール `GalilScaffoldTopInitRestart.lean`（ルート import 済み）：`afterCompare_remaining`、`watchSegE_remaining`（区間は shift counter を保つ＝`ShiftIdle` 保存の材料）、`initialHead raw`（先頭 place 手前の gap 上・語は未着）、`initialHead_right_represents`／`_focus`／`_position`（`right` で先頭 place、位置 1、`Represents`）、`init_restarted`（`init` tick を `galilFrameS` に：L=R=C＝先頭 place、`Restarted (a :: rest) t 0 reset`、位置 1、remaining／replay 不変）、`segment_mismatch_ready`（`Restarted` からの chain idle 区間の終端で R 可用なら、`right s.right` は `Represents`・実記号、length 正準、remaining 保存、`ScanInvariant`（半径 Rad＋一致数）＝`fallback_next_found` の前提）。これで init → 走査 → 最初の不一致 → fallback → replay＋探索 → found → chain の一生 → restart → … の各接続部が `galilFrameS` 上で揃った（replay 中の found・後段 stage・missed・空語は未対応）。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: 分岐網羅（各 scan 状態で必ず次の tick が存在し、上記のいずれかの区間に入ること）と主ループの帰納、出力の完全性、実時間供給、`StructuredMachine` 化、`SAccepts ↔ PAL`）。

追記（2026-09-16、不一致 → 次の found）：新モジュール `GalilScaffoldTopFallbackFound.lean`（ルート import 済み）：`fallback_next_found` — `fallback_restarted`＋`restarted_next_found` の合成（`delay = 2048`、`Decodes P`）。chain idle の不一致比較から fallback 一周を経た状態 t（`replay = ofNat r`）に対し、t から chain idle の `WatchSegE`（replay 中の tick を含む）で終端 idle・一致数 ≥ 1・clock 1 に達し、そこでの一致比較で探索が found なら `FoundReady` と（第 1 stage の found なら）直前 run・DP `Result`（lower 0）・Candidate、または区間内の非 found exit。これで主ループの二つの再入口（restart 後、fallback 後）から次の found 状態までが揃った。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: init tick → 最初の走査（初期 `ScanInvariant` 半径 0、search `begin reset radius`）→ 最初の不一致（L の左端）→ fallback の接続；replay 中の found・後段 stage・missed は未対応；`3·Rad ≤ 5·k`、found 時の半径正は仮定）。

追記（2026-09-16、fallback → restart 状態）：`Restarted` を緩和（`0 < Rad` を外し `positive last` を `0 ≤ value last` に）、`restarted_next_found` に `hpos : 0 < Rad + es1.count true`（found 時の半径正）を仮定として追加、`found_to_found` に対応する `hpos'` を追加。`replayStart_tick`／`fallback_to_scan_S`／`scan_fallback_cycle_S` の結論に `t.search = begin reset reset`、`t.lower = reset` を輸出。新モジュール `GalilScaffoldTopFallbackRestart.lean`（ルート import 済み）：`leftMoves_eq`、`stream_ne_nil`、`fallback_restarted` — chain idle の不一致比較から fallback 一周を経た状態 t について、右ヘッドの `represent` 分解 `⟨a :: xs, gap⟩` が存在し、`Restarted raw t 0 reset`（chain idle・中心 `Represents`・`ScanInvariant` 半径 0・radius reset・length 1・`search = begin reset reset`）、`t.replay = ofNat r`、`position t.center = position (right s.right) − r`、`PalAt (encoded raw) (…) r` と窓内最大性（下層 `fallback_replay`）。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: `fallback_restarted`＋`restarted_next_found` で「不一致 → fallback → replay＋探索区間 → found」を合成；init tick からの初期不変量；replay 中の found は未対応；`3·Rad ≤ 5·k`、found 時の半径正は仮定）。

追記（同日、replay 中の tick と区間の一般化）：`TopSearch` に `replayDec b s`（`matchedPlace` の replay 減算）と射影補題、`matchedPlace_replayDec`、`scan_match_S'`／`scan_match_idle_S'`（replaying の有無を問わない一致比較 tick：`available` は `replaying ∨ canRight`、到達制御は `replaying := c.replaying && !replayExhausted (replayDec …)`、到達 VM は `replayDec c.replaying (afterCompare …)`）を追加。`WatchSegE` に replay 中の構成子 `countR`（replaying・clock>1・chain idle）と `matchIdleR`（replaying・clock 1・R 可用・chain idle・非 found・replay 減算）を追加し、`watchSegE_steps`／`append`／`trans`／`events`／`ne_idle`／`searchRun`／`advances`／`center`／`clock`（`replaying` 保存の結論は削除）／`search_not_found`／`heads`／`watchSeg_of_E` を更新。これで replayStart 後の replay 区間（探索は同時に進む）も chain idle 区間として扱える。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: fallback 後の状態から replay 区間の存在と `ScanInvariant raw c r` の再構成（下層 `fallback_replay`／`replay_scan`）、その後の探索区間→found への接続で「不一致 → fallback → replay → 探索 → found」の経路；init tick からの初期不変量；replay 中の found（chain start）は未対応）。

追記（同日、chain idle の不一致 → fallback 一周）：新モジュール `GalilScaffoldTopFallbackCycleS.lean`（ルート import 済み）：`scan_fallback_cycle_S` — `P := galilShared onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' rs centre place entry` の `galilFrameS` 上で、scan（clock 1・replaying false）から不一致比較（`compareFound` の witness：探索 step `searchEffect false`、chain 効果 `chainAt false`（idle なら idle のまま、found なら chainStart）、`¬ shiftGuardVM`）で `beginFallback`（FPP 準備・chain idle・search idle）に入り、`fallback_to_scan_S` で scan に復帰：L=R=C は `left^[r] (right s.right)`（r = `chosenRadius` の窓）、`replay = ofNat r`、`radius = reset`、`length = ofNat 1`、chain idle、`replaying := decide (0 < r)`。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: replay 区間（`replaying = true` の比較列：`available` は常時、一致で `replay` 減算、尽きたら `replaying := false`）の定義と探索事象、その後の chain idle 区間への接続、init tick からの初期不変量、fallback 後の `ScanInvariant`（選ばれた中心の回文性＝`chosenRadius` の仕様）と replay の一致保証）。

追記（同日、fallback 経路の `galilFrameS` 化）：新モジュール `GalilScaffoldTopFallbackS.lean`（ルート import 済み）：`steps_transfer_fallback_S`／`fpp_S`／`markEnd_S`／`rewind_S`（pull frame の相 run を `tick_S_of_tick` 経由で `galilFrameS` へ）、`copy_home_start_S`／`fpp_then_markEnd_S`／`choose_then_rewind_S`／`fallback_chain_S`／`fallback_to_scan_S`（元定理の本文を機械的に置換：copy モードの `beginFallback` 状態から replayStart tick を経て scan モードへ、L=R=C は選ばれた中心、`replay = ofNat r`、`radius = reset`、`length = ofNat 1`、chain idle、`replaying := decide (0 < r)`）。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: chain idle の不一致比較 tick `scan_fallback_S`（`compareFound` の第 2／3 枝＋`beginFallbackVM`）と `fallback_to_scan_S` の合成、replay 区間（`replaying = true` の比較列）の定義と探索事象、init tick からの最初の走査不変量）。

追記（同日、replay の減算＝忠実性修正）：`galilFrame.matchedPlace` は scan frame 経由で `s' = s`（replay counter を減らさない）だったので、Scala `matchedPlace` の `if (replaying) replay.dec()` を反映して `matchedPlace b s t := t = (if b then {s with replay := dec s.replay} else s)` に修正（`replaying := c.replaying && !replayExhausted s''` と整合）。`scan_match_S`／`scan_match_idle_S`／`found_start_match`／`compare_progress`／`scan_match_merge` は `replaying = false` の下で更新。全体 build 成功・標準公理のみ・無条件 PAL は未完。**未解決の下層前提（メモ）**：(i) `3·Rad ≤ 5·k`（restart 時の走査半径と `last` の関係、第 1 stage の debt 障壁）は下層 `first_stage_safe` 以来の仮定；(ii) found 時の半径 `0 < r0`（`stage_found_supplied`）は replay 後の半径 0 の found を排除できていない（restart 後は Rad ≥ 1 で満たす）。

追記（同日、主ループの一周）：新モジュール `GalilScaffoldTopFoundLoop.lean`（ルート import 済み）：`found_to_found` — `life_restarted` と `restarted_next_found` の合成。found 状態 `⟨cF, sF⟩`（`found_life` の静的前提）から、chain の一生・restart・chain idle の探索区間・次の found 比較まで `galilFrameS` の `Steps` が通り、次の found 状態 s1' で `FoundReady` が再成立、かつ（第 1 stage の found なら）直前 run・DP `Result`（k = value last）・Candidate、または第 1 stage が区間内で非 found exit。`Decodes P`、`delay = 2048`、`3·Rad ≤ 5·k` を仮定。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: init／replay から最初の found 状態へ（`Restarted` の `positive last` を `0 ≤ value last` に緩めて lower = 0 を許す）、後段 stage（wait/double）、missed／fallback 枝、出力の完全性、実時間供給、`StructuredMachine` 化、`SAccepts ↔ PAL`）。

追記（同日、chain の一生 → restart 直後）：新モジュール `GalilScaffoldTopLifeRestart.lean`（ルート import 済み）：`watchSeg_counters`（chain 条件なしの counter 正準性保存）、`life_restarted` — `found_life` と同じ前提（found 状態の静的前提＝`FoundReady` の中身、found tick、準備期間、watch 期間、終端不一致＋shift、m ラウンド、区間＋破れ比較）に `entry` と `hres : ∀ s t, restartVM entry s t → P.restart s t` を加え、破れ状態からの restart tick（`Tick.restart`）で、found 状態から restart 直後の状態 `{e3 with chain := .idle, lower := last, search := begin last e3.radius, dp := reset entry e3.dp}` までの `galilFrameS` の `Steps` と `∃ Rad, Restarted raw r Rad last`（中心は `rounds_centerRep`＋`scanSeg_center`、`ScanInvariant` は `rounds_restart` の結論を位置 `org.center+(m+1)h` に合わせ、length の正準性は prep／watch／shift／rounds／区間の各保存補題で輸送）。これで `life_restarted` → `restarted_next_found` により「found 状態 → 次の found 状態（`FoundReady`）」が閉じた（第 1 stage で found する場合；`3·Rad ≤ 5·k` は仮定）。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: 一周の合成定理 `found_to_found`、init／replay から最初の `FoundReady`／`Restarted` へ、missed／wait／double・fallback 枝、出力の完全性、実時間供給、`StructuredMachine` 化、`SAccepts ↔ PAL`）。

追記（同日、restart 後 → 次の found 状態）：新モジュール `GalilScaffoldTopReadyFound.lean`（ルート import 済み）：`Decodes P`（`P.centre`／`P.place` は中心ヘッドの `represent ⟨a :: ls,gap⟩ …` から記号と place を読む；`P.place` は中心のみに依存）、`FoundReady P raw s`（`found_life` の静的前提：中心の分解、`ScanInvariant`、radius 値・正準、length 正準、R > 0、復号）、`Restarted raw r Rad last`（restart 直後の事実：chain idle、中心 `Represents`・実記号、`ScanInvariant` 半径 Rad、`RadiusRep`、length 正準、Rad > 0、`search = begin last radius`、`lower = last`、last 正準・正）、`restarted_next_found`：`Restarted` な r から clock 2048 で chain idle の `WatchSegE es1` を経て、終端 idle の状態 s1 での一致比較（clock 1）で探索が found に至れば、`FoundReady P raw s1` が成り立ち、かつ（第 1 stage 終端なら）直前 run・`Result`（窓 `8·max k 1 + 1`、k = value last）・Candidate、または第 1 stage が区間内で非 found exit。`3·Rad ≤ 5·k` は仮定。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: `FoundReady sF` ＋ `found_life` の動的前提 ＋ restart tick ⇒ `Restarted` の定理（`life_restarted`）、両者の合成で found→found の一周）。

追記（同日、中心・ヘッド・counter の輸送）：`chain_life`／`found_life` の結論に `Entry raw org (toOnly e v)`（ラウンド開始時の入口不変量）を追加。新モジュール（すべてルート import 済み）：`GalilScaffoldTopCentre.lean`（`represents_decompose`：`Represents` かつ focus ≠ none なら `represent ⟨a :: ls, gap⟩ (rs.map some) q` の形、`place_read_some`、`scanSeg_center`、`rounds_centerRep`：m ラウンド後の中心ヘッドは `Represents`・実記号・位置 `org.center + m*h + h`）、`GalilScaffoldTopSegmentHeads.lean`（`watchSegE_heads`：chain 条件なしで `ScanEvents`・periodOnly・radius＝一致数・counter 正準性保存、`scanSeg_counters`）、`GalilScaffoldTopRoundsCounters.lean`（`rounds_counters`：ラウンドは radius／length の正準性を保つ、`shift_run_canonical`）。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: 「found 状態の不変量」`FoundReady`（中心の `represent` 分解、`ScanInvariant`、radius 値・正準、length 正準、`P.centre`／`P.place` の復号）を定義し、`found_life` → restart tick → idle 区間 → `idle_segment_found_first` で次の found 状態でも `FoundReady` が成り立つ「一周」定理；`3*rad ≤ 5*k`（restart 半径と `last` の関係）は下層でも未証明の前提として明示）。

追記（同日、found tick の特定）：新モジュール `GalilScaffoldTopIdleFound.lean`（ルート import 済み）：`map_fst_map_pair`、`advances_replicate_false`、`idle_segment_found_first` — `Search.start(lower)` 直後（clock 2048、chain idle、`P.place r = ⟨a :: ls,gap⟩`、`r.search = begin lower radius`、lower 正準 k、radius 正準 rad、`3*rad ≤ 5*k`）から chain idle の `WatchSegE es1`（終端も idle）と、その次の tick の探索 step（比較なら `aF = true` かつ clock 1、background なら `aF = false`）が found に至るとき、(左) その tick が第 1 stage の終端：`vq.dp = ⟨dpv, true⟩` に DP `Result`、直前の探索は run、Candidate と半周期の存在（＝`found_life` の入口）、または (右) 第 1 stage が区間内の L ≤ |es1| で run 以外・found 以外の mode（missed／wait／double）で既に終わっていた（後段 stage の found；下層 `later_stage_chain` の領分）。証明は inactive 探索の padding（`searchRun_pad`）で `search_first_stage` を適用し、`stage_prefix_mode`／`searchRun_unique`／`watchSegE_search_not_found` で三分岐。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: restart tick の出口（`restart_tick`：`begin last radius`、clock delay、chain idle）とこの定理、`found_start_match`／`backgroundS_idle` と `found_life` の接続；wait/double 後段 stage；missed のときの走査継続と fallback）。

追記（同日、chain idle の比較 tick と区間の事実）：`WatchSegE.match` は scan 側の `ChainTick` 前提（非 idle）なので chain idle 区間に比較 tick を含められなかった。`scan_match_idle_S`（chain idle・探索が found に至らない一致比較：`compareFound` の第 2 枝で chain は idle のまま）を `TopSearch` に追加し、`WatchSegE` に構成子 `matchIdle` を追加、`watchSegE_steps`（`galilFrameS` の `Steps`）を新設、`watchSeg_of_E` は非 idle 前提つきに。`watchSegE_append`／`trans`／`events`／`ne_idle`／`searchRun`／`advances` を更新。新モジュール `GalilScaffoldTopSegmentFacts.lean`（ルート import 済み）：`watchSegE_center`（中心保存）、`watchSegE_clock`（事象列＝`advances delay c.clock`、終端 clock＝`MatchClock.run`、mode・replaying 保存）、`searchRun_pad`（inactive な探索は任意事象で不変）、`watchSegE_search_not_found`（終端 idle の区間では途中のどの時点でも探索は found でない：found なら chain が始まり idle に戻らない）。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: restart 出口＋idle 区間＋found tick から、padding で `search_first_stage` を適用し `stage_prefix_mode`／`watchSegE_search_not_found` で found tick＝第 1 stage の終端を特定、`found_life` の入口（`Result`・Candidate）を供給；第 1 stage が wait/double で終わる枝は `later_stage_chain`）。

追記（同日、第 1 stage の構造化と接頭辞）：`search_first_stage` を構造化（`es = as ++ bs ++ usedQ ++ rest`、各相の `SearchRun`、`v0` grow・work = |as|、`PacedPrepared (ofNat k) … v1.toPrep bs v2.toPrep`、`v1` grow・work 非正・lower = ofNat k、`v2` run、`SafeQuanta v2.search v2.dp usedQ v3.search v3.dp`、`v3` 非 run、DP `Result`、found → Candidate）。新モジュール `GalilScaffoldTopStagePrefix.lean`（`searchStep_unique`／`searchRun_unique`（決定性）、`searchRun_grow_prefix`、`pacedRun_split`、`pacedRun_cons_prepMode`、`safeQuanta_prefix_run`）と `GalilScaffoldTopFirstStagePrefix.lean`（`zip_replicate_append`、`pacedPrepared_split`、`safeQuanta_nil`、`searchRun_prefix_eq`、`stage_prefix_mode`：第 1 stage の事象列 `as ++ bs ++ usedQ` の任意の真の接頭辞の後で探索は found でなく、最後の 1 事象の直前では run）。両方ルート import 済み。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: restart tick の出口から chain idle の `WatchSegE` を取り、`search_first_stage`＋`stage_prefix_mode` で「最初に found になる tick」＝`usedQ` の終端を特定し、その tick が比較なら `found_start_match`、background なら `backgroundS_idle` で chain が始まることを `found_life` の入口に接続；missed／wait／double・fallback 枝）。

追記（同日、restart 後の第 1 stage の実走行）：新モジュール `GalilScaffoldTopFirstStage.lean`（ルート import 済み）：`searchRun_split`、`toPrep_search_eq`、`search_first_stage` — `Search.start(lower)` 直後（scheduler `begin lower radius`、lower 正準で値 k、radius 正準で値 rad、`3*rad ≤ 5*k`）から、chain idle 区間の実走行 `SearchRun ⟨a :: ls,gap⟩ es v0 v'` で、事象列 es が可用性列 av の `advances 2048 2048` であり、長さが `max k 1 + (2k+2|w|+7) + runBudget(8·max k 1)` 以上なら、`es = used ++ rest` に分割でき、`used` の終端 v3 で探索は run 以外の mode、`v3.dp = ⟨dpv, true⟩` に DP `Result w k 0`（w は中心から `8·max k 1 + 1` 個の窓）、found なら Candidate と半周期の存在。証明は `first_stage_chain_run` の存在結果を `searchRun_growing`／`pacedGrowing_unique`／`searchRun_prepared`／`searchRun_quanta` で実走行に同一視。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: restart tick（`restart_tick`）の出口状態から `search_first_stage` の前提（`begin last radius`、chain idle、clock = delay = 2048）を供給し、found のときは `used` の終端 tick で chain が始まる（比較 tick なら `found_start_match`、background なら `backgroundS_idle`）ことと `found_life` を接続；missed／wait／double の枝、fallback 枝）。

追記（同日、探索段階の同一視）：新モジュール `GalilScaffoldTopSearchStage.lean`（ルート import 済み）：`toPrep_ofPrep` 等の往復補題、`searchRun_growing`（grow・work = n の状態からの n tick の `SearchRun` は `PacedGrowing`、終端は grow・work 0、quarter／lower 保存）、`pacedGrowing_unique`、`PrepMode`／`tick_prepMode`／`searchStep_prep`、`searchRun_paced`（全 enabled の下層 `PacedRun` を実走行が状態ごとに辿る：`tick_unique`）、`searchRun_prepared`（grow・work 零からの dispatch＋本体＝下層 `PacedPrepared` の終端 p に到達）、`safeQuanta_single`、`searchRun_quanta`（下層 `SafeQuanta … used …` を実走行が辿り、残り `rest` はその後：`safe_calls_unique`）。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: これらと `first_stage_chain_run`／`begin_entry`／`watchSegE_advances`／`advances_take` を合成した「restart 後の第 1 stage」上層定理：区間の事象列を `as ++ bs ++ used ++ rest` に分割し、`used` の終端で探索が exit mode・DP `Result`・found なら Candidate）。

追記（同日、background での chain start）：Scala の `background` は探索 quantum の後に found なら **任意の scan tick で** `chain.start()` する（比較 tick に限らない）ので、`backgroundS` を「ヘッド不変・探索 step（advance なし）・chain 効果は `chainAt false found …`（active なら無効 tick、idle かつ found なら `chainStart`、idle かつ非 found なら idle）・他フィールド不変」に書き直し、`backgroundS_fields`／`backgroundS_chainTick`（active chain なら `ChainTick false`）／`backgroundS_idle`（idle chain の 2 分岐）を用意。`watchSeg_events`／`watchSegE_events` は `s.chain ≠ .idle` 前提つき（`ChainTicks` の結論のため）に変更し、`prep_watch_start`／`first_round`／`found_life` の呼び出しに前提を供給。`chainTick_ne_idle'`。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: `SearchRun` と下層段階 run の同一視モジュール、background 起点の chain start（`sm = false`）版 `prep_watch_start`）。

追記（同日、chain idle 区間の探索の駆動）：新モジュール `GalilScaffoldTopSearchRun.lean`（ルート import 済み）：`SearchRun center es v v'`（`searchStep` の列）、`searchRun_append`、`chainTick_ne_idle`（chain tick は idle に戻らない）、`watchSegE_ne_idle`／`watchSegE_idle_start`（区間の終端で chain idle なら開始も idle＝区間内で chain start なし）、`watchSegE_searchRun`（終端 idle の `WatchSegE es` は、`P.place` が中心のみに依存する前提で、探索を `SearchRun (P.place s) es` として駆動する）、`watchSegE_advances`（区間の事象列 es は可用性列 av に対する `advances delay c.clock (av.map (·, true))` に等しい：下層の段階補題が消費する事象形）。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: `SearchRun` を下層の `PacedGrowing`／`PacedPrepared`／`SafeQuanta` と同一視（`growStep` は関数、`tick_unique`／`run_unique`、`safe_quanta_unique`）して `first_stage_chain_run` の結論を実走行に移し、restart tick → found tick を一本化）。

追記（同日、探索共走過程の上層統合）：`GalilVM`／`SearchVM` に探索の walker place（`walker`）を追加。`GalilScaffoldTopSearch.lean` に `SearchVM.toPrep`／`ofPrep`（`PrepareControl.State` との往復、`runState`）、`searchStep center a v v'`（Scala `background` の探索 1 step＋`advanceMatch` の debt 減算 `a`：idle/found/missed は不変、grow は `growStep` か `prepare` の dispatch、lower/lowerHome/copy/home は `PrepareControl.Tick true`、run は `SafeQuanta … [a]`（64 呼び出し＋advance）、wait は `advance a (waitStep true …)`、double は `advance a (Double.step …)` か `prepare`）、`searchEffect P a s vq`（chain idle なら `searchStep (P.place s) a`、chain active なら不変）、`backgroundS`（scan 側 background＋advance なしの探索 step）を定義し、`compareFound` の quantum 節と `galilFrameS.background` を置換（`searchQuantum`／`searchIdle` は不使用に）。`backgroundS_fields`（background tick の各フィールド）、`searchEffect_run`／`searchEffect_active`。下流（`MatchedSeq`／`ScanSeg`／`WatchSeg`／`WatchSegE`／`round_next`／`terminal_shift_steps`／`rounds_break`／`chain_life`／`found_life`／`found_start_match`）の `hq` 仮定と background 型を差し替え。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: chain idle 区間の探索の段階（`PacedGrowing`→`PacedPrepared`→`SafeQuanta`→wait/double）を `searchStep` の列から復元して `first_stage_chain_run`／`restart_first_stage` に接続し、restart → found tick（`found_life` の入口）を一本化）。

追記（同日、init／replay／fallback の忠実性修正）：Scala の `stepInit`（`search.start(zero)`）、`stepReplayStart`（chain idle、`radius.reset()` 後に `search.start(zero)`）、`beginFallback`（`search.mode = Idle`、`chain.mode = Idle`）に合わせ、`initVM entry`／`replayStartVM entry`（`t.chain = .idle`、`t.search = begin reset s.radius`／`begin reset reset`、`t.lower = reset`、`t.dp = Control.reset entry s.dp` を追加）と `beginFallbackVM`（`chain := .idle`、`search := {s.search with mode := .idle}`）を強化。`galilShared … centre place entry` に DP entry を追加し、`init_tick`／`replayStart_tick`／`fallback_to_scan`／`scan_fallback_cycle` の自由な `ch : ChainVM` を除去（終状態の chain は `.idle`）。全体 build 成功・標準公理のみ・無条件 PAL は未完。**残りの主要作業（設計メモ）**：(1) 探索共走過程の上層統合：現在の `searchQuantum`（run モードの 64 呼び出し＋`advance a`）／`searchIdle`（run 以外は不変）は Scala の `background` の「run 以外でも 1 step」（grow／lower／lowerHome／copy／home／wait／double）を含まない。下層には `GalilScaffoldPrepareControl.Tick`（paced 準備）、`StagePrepare.PacedGrowing`／`Double.Run`／`WaitInterrupt.Run`、`first_stage_chain_run`／`later_stage_chain`／`restart_first_stage`／`begin_entry`／`replay_stage_entry` が揃っており、`SearchVM`（scheduler `SearchFinish.State`＋`dp`＋`lower`）の 1 tick を mode 別にこれらへ対応づける `searchTick a` を定義して `compareFound` の quantum 節を置換する必要がある。(2) restart tick → `SearchSeg`（chain idle の走査区間、探索 tick 付き）→ found tick（`found_life` の入口）／missed／不一致→fallback。(3) init と replay 後の `ScanInv` の確立、fallback 経路（`fallback_chain`＋`replayStart_tick`）と `ScanInv`。(4) 出力の完全性（中心の正しさ＝Galil の大域不変条件）。(5) 実時間入力供給（`right.gap`／`inputReady`、1 入力あたりの tick 数の有界性）。(6) `galilFrameS` の `StructuredMachine` 化と `SAccepts ↔ PAL`。

追記（同日、found tick からの一本化）：新モジュール `GalilScaffoldTopFoundLife.lean`（ルート import 済み）：`found_life` — found 状態 `⟨cF, sF⟩`（scan・replaying false・clock 1・R が読める・chain idle・中心 `represent ⟨a :: ls,gap⟩ (rs.map some) q`・`ScanInvariant` 半径 R（value radius = R、R > 0）・counter 正準・探索 quantum が found で終わり DP `Result`・`P.centre sF` が中心記号、`P.place sF` が中心 place・外側一致・`ChainMatched (chainStart …) ch`・`refresh`）から、`∃ h ys b, Candidate ∧ ys.length+1 = h ∧ ∀ bs cs（長さ h, h+1）, 準備期間 `WatchSegE (bs ++ dm :: cs)` → watch 期間 `WatchSeg` → 終端不一致＋shift → `Rounds m` → 区間 n ＋破れ比較 ⇒ `galilFrameS` の `Steps` が found 状態から broken 状態まで通り、`restartVM` の前提条件（`org.center = position sF.center`、中心 `+(m+1)*h`）が成立`。初期条件（`ScanInv` の found tick 通過、準備期間の `ScanEvents`、radius＝lag の一致 `prep_value`、`canonical_nat` による `sF.radius = ofNat (r0+1)`）は内部で供給。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: restart tick（`restart_tick`）から次の探索へ、探索 idle 期間の走査（chain idle・found でない区間）、found 前の `ScanInv` の確立（init／replay から）、実時間供給、`StructuredMachine` 化、`SAccepts ↔ PAL`）。

追記（同日、単一フレームへの統合）：`galilFrameS` の `compare` を `compareVM` から `compareFound`（chain start を含む比較：chain が active なら `ChainTick`、idle かつ探索が found で終われば `chain.start()`＋一致 credit、idle で found でなければ idle のまま）に置き換え、`galilFrameF` を廃止して `found_start_match` も `galilFrameS` の tick に。中心記号・中心 place の読み出し `centre`/`place` は `Shared` のフィールド（`P.centre`/`P.place`）に移し、`galilShared … rs centre place` と各補題（`replayStart_tick`／`fallback_to_scan`／`restart_tick`／`scan_fallback_cycle`／`init_tick`／`compare_progress_concrete`）に引数追加。`scan_match_S`・`WatchSeg`/`WatchSegE` の `match`・`ScanSeg`（`chainTick_source_ne_idle` で導出）・`round_next`/`terminal_shift_steps`/`rounds_break` は「chain が idle でない」前提を付けて `compareFound` の第 1 枝を使う。これで found tick から chain の一生（`chain_life`）まで同じフレーム上の `Steps` で繋がる。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: found tick → 準備期間（`prep_watch_start`）→ `chain_life` の一本化と初期条件供給、restart 以降、実時間供給、`StructuredMachine` 化、`SAccepts ↔ PAL`）。

追記（同日、chain start と準備期間、忠実性修正）：(1) 忠実性修正：Scala の `background` は探索 quantum の後に `chain.start()` を呼び、chain は answer tape の現在値を読む。`GalilScaffoldTopFound.lean` の `compareFound`／`found_start_match` は quantum 前の `s.dp` の tape 11 を snapshot していたので、quantum 後の `vq.dp.config.tapes 11` に修正（`found_to_watchStart` の `y.config.tapes 11` と整合）。(2) `found_shift_entry`／`first_round`／`chain_life` の `∃ h ys b, Candidate ∧ ys.length+1 = h ∧ split ∧ …` を `∀ h ys b, Candidate → ys.length+1 = h → …` に変更（`fresh_watch_entry` の存在量化を経由せず、chain start 側が出す h・ys・b をそのまま渡せる）。(3) 新モジュール `GalilScaffoldTopWatchSegE.lean`（ルート import 済み）：`WatchSegE es`（事象列を添字にした一般走査区間）、`watchSeg_of_E`、`watchSegE_append`（任意位置で分割）、`watchSegE_trans`、`watchSegE_events`、`prep_watch_start`：found 探索（`SafeQuanta` … found）と一致した start tick（`ChainMatched (chainStart (y.config.tapes 11) c p ver (ofNat (r0+1))) ch`）のあと、事象列 `bs ++ dm :: cs`（長さ h・1・h+1）の `WatchSegE` の終端で chain は `.watch (watchStart ver c ys b (run (start (ofNat (r0+1))) (prepEvents true dm bs cs)))`（`found_to_watchStart`＋`chainMatched_unique`／`chainTicks_unique`）。これは `first_round` の開始条件 `v0.chain = .watch s0` を供給する。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: found tick → 準備期間 → `chain_life` を `WatchSegE` の分割で一本化、`ScanInvariant`／radius の初期条件の供給、restart 以降、実時間供給、`StructuredMachine` 化、`SAccepts ↔ PAL`）。

追記（同日、chain 一生分の合成）：新モジュール `GalilScaffoldTopChainLife.lean`（ルート import 済み）：`chain_life` — found 側前提（`found_rounds_restart` と同じ）のもと、`WatchSeg` の watch 期間＋終端不一致＋最初の shift（`first_round`）、`Rounds m`（`rounds_lift`）、最後の走査区間 n ＋破れる終端比較（`rounds_break`）を合成し、(i) `galilFrameS` の `Steps` で found 直後の状態から broken 状態 `afterCompare s3 vs3 vq3` へ到達、(ii) `∃ org : ReadOrigin raw` で `org.interior.length+1 = h`、`org.center = position cen`、`org.shifts = 0`、中心 `org.center+(m+1)*h`・半径 `org.radius+1+m*h-h+n+1` の `ScanInvariant`、broken、margin 非負、`last` 正、lag 零、`RadiusRep`、`begin … .work`、`Canonical last`（＝`restartVM` の前提）。注意: 文中の `let` が「unknown free variable」を起こしたので、`raw`／`final`／`s0` は展開して書く。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: chain start（found tick）の上層供給と `WatchSeg` の開始状態の接続、restart tick 以降の探索、実時間供給、`StructuredMachine` 化、`SAccepts ↔ PAL`）。

追記（同日、最初の一周）：新モジュール `GalilScaffoldTopWatchSeg.lean`（`WatchSeg`：chain の状態を問わない一般の走査区間、`watchSeg_steps`＝`galilFrameS` の `Steps`、`watchSeg_events`＝tick ごとの `Bool` 列で `ChainTicks`／`ScanEvents`、中心・periodOnly 保存、radius は一致数だけ増加、counter の正準性保存）と `GalilScaffoldTopFirstRound.lean`（`terminal_shift_steps`：終端不一致比較＋shift を `Steps (1+(h+1))` に；`first_round`：`found_rounds_restart` と同じ found 側前提のもと、`WatchSeg` の watch 期間（開始 chain＝`watchStart cen c ys b final`）＋終端不一致（phase 4・lag 零・予測一致）＋shift ⇒ `galilFrameS` の `Steps`、終状態は watching・lag 零・periodOnly、かつ `Entry raw o' (toOnly e v)`（`o'.interior.length+1 = h`、`o'.shifts = 0`））。両方ルート import 済み。これで `first_round` → `rounds_lift`（m 周）→ `rounds_break`（破れ）が一本につながる材料が揃った。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: 三者を合成した chain 一生分の定理、found tick（chain start）の上層供給、restart 後の探索、実時間供給、`StructuredMachine` 化、`SAccepts ↔ PAL`）。

追記（同日、found からの `Entry`）：`GalilScaffoldTopFreshEntry.lean` に `found_shift_entry` を追加：`found_rounds_restart` と同じ前提（found 探索、中心 `represent`、半径正準・正、prep の一致列、watch 期間の `Run`、phase 4、lag 零、`ScanInvariant`、予測一致、counter 正準、終端不一致）に実機の `ChainShiftRun ⟨cen, left l, ofNat h, radiusCounter, lengthCounter⟩ (immediate t') reset h …` を与えると、shift 後状態に `Entry raw o`（`o.interior.length+1 = h`、`o.center = position cen`、`o.radius = scanRadius`、`o.shifts = 0`、中心が読める）。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（同日、最初の shift の `Entry`）：新モジュール `GalilScaffoldTopFreshEntry.lean`（ルート import 済み）：`fresh_shift_entry` — `scan_prediction_shift` と同じ前提（fresh start `ready c xs b`、Represents、位置、`ScanInvariant`、phase 4、lag 零、予測一致、counter の正準性、prep credits、終端不一致）に、実機が行った `ChainShiftRun`（同じ開始状態）を加えると、`chain_shift_unique` で解析側の shift と同一視され、`entry_of_only` により shift 後の状態 `⟨endpoint.center, endpoint.left, right outer, watchEnd, cycleEnd, endpoint.radius⟩` に `Entry raw o` が成立（`o.interior.length+1 = xs.length+1`、`o.center = position s.machine.verifier`、`o.radius = radius`、`o.shifts = 0`、中心が読める）。これで `rounds_lift`（m ラウンド）→ `rounds_break`（破れ枝）の入口が下層から供給できる。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: 上層状態から `fresh_shift_entry` の前提を供給する「最初の一周」補題（found→prep→watch 期間→終端不一致→shift）、restart 後の探索と found tick 供給、実時間供給、`StructuredMachine` 化、`SAccepts ↔ PAL`）。

追記（同日、破れ枝＝`rounds_restart` の上層化）：新モジュール `GalilScaffoldTopRoundBreak.lean`（ルート import 済み）：`chainTick_true_broken`（lag 零で一致 tick が破れたら記録される watch は `immediate w` かつ `BreakStep`）、`afterCompare_only'`（watching/broken を問わず一致比較の射影は `onlyCompareNext`）、`afterCompare_chain`、`rounds_break`：`Rounds m` ＋ 走査区間 n ＋ 終端の一致比較で chain が破れる（`vs.chain = .broken w'`）とき、(i) `galilFrameS` の `Steps` で `afterCompare s1 vs vq`（output は `refresh`）に到達、(ii) `Entry raw org (toOnly s w0)` かつ中心が読める限り、下層 `rounds_restart` の結論（累積中心・半径での `ScanInvariant`、broken、margin 非負、`last` 正、lag 零、`RadiusRep`、`begin … .work`、`Canonical last`）が実状態で成立。これは `restartVM` の前提そのもの。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: `Entry` の初期成立（found→watch→最初の shift と `entry_of_only`）、restart 後の探索と found tick 供給、実時間供給、`StructuredMachine` 化、`SAccepts ↔ PAL`）。

追記（同日、m ラウンドの連結）：`shift_phase_S`／`round_next` の shift 出口の output を存在量化から `refresh (galilFrameS …) 終状態 c1.output o` を仮定した明示の `o` に変更（`shift_steps_S` に転送部分を分離）。これで次ラウンドの開始制御が具体的に決まる。新モジュール `GalilScaffoldTopRounds.lean`（ルート import 済み）：`chain_shift_lag`（chain shift は lag を保つ）、`compareRounds_append`、`Rounds P q first delay h m c s c' s'`（`round_next` のデータを m 回、各回は直前の shift 出口の制御から開始）、`rounds_lift`：periodOnly・lag 零の watching 開始から、`Steps (galilFrameS)` の存在と `CompareRounds h (toOnly s w0) m (toOnly s' w')`（終状態も watching・lag 零・periodOnly）。`rounds_origin` と組めば `Entry` が m ラウンド保存される。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: `Entry` の初期成立（found→watch 開始との接続）、終端一致で chain が破れる枝＝`rounds_restart`、found tick の供給、実時間供給、`StructuredMachine` 化、`SAccepts ↔ PAL`）。

追記（同日、一周＝`CompareRounds` の 1 段）：`beginShiftVM` の radius 二重加算（比較の `afterMismatch` で既に +1）を除去し、`shift_round` の前提を `⟨s1.center, s1.left, ofNat h, s1.radius, inc (inc s1.length)⟩`（`CompareRounds.next` の `inc t.radius` と同形）に。新モジュール `GalilScaffoldTopRoundS.lean`（ルート import 済み）：`shiftRun_of_chain`、`shift_phase_S`（shift 期間を `galilFrameS` 上の `Steps` に：`steps_transfer_generic` を Inv＝`CopyIdle ∧ s = shiftLens.set s2 v0` で使い、frame 再パラメータ化と `tick_S_of_tick`）、`afterMismatch_*` 射影補題、`round_next`：periodOnly・lag 零の watching 状態から、走査区間（`ScanSeg`）＋終端の不一致比較（`cycleEnd`・予測一致・guard・`beginShiftVM`）＋`ChainShiftRun` h 単位で、(i) `galilFrameS` 上の `Steps (k+1+(h+1))` で scan モードに戻り、(ii) 射影が `CompareRounds h (toOnly s w0) 1 (toOnly 終状態 v)`（`.next … (.stop _)`）になる。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: m ラウンドの連結と `rounds_origin` による `Entry` 保存、終端が一致で chain が破れる枝（`rounds_restart`）、found tick の供給、実時間供給、`StructuredMachine` 化、`SAccepts ↔ PAL`）。

追記（同日、消費のタイミングの修正）：Scala では `prediction()` は chain 消費の前に評価され、`chain.matched()`（lag 零なら即時消費）は一致時は `matchedPlace`、shift 時は `beginChainShift` の中で起きる。これに合わせ `scanFrame.compare` の chain 効果を `ChainTick (decide (read (left L) = read (right R)))`（一致なら消費込み、不一致なら背景のみ）にし、`beginShiftVM` は `chain := .watch (immediate w)`（入口で消費）、`shiftGuardVM` の periodOnly 側は `singlePositive cycle`（不一致時は cycle 未減算）に戻した。`compare_lift`/`break_lift`/`grun_lift`/`compare_parts`/`compare_progress`（`hw : ∀ a, ∃ ch', ChainTick a …`）を更新。`shift_round`/`scan_shift_cycle` の `ChainShiftRun … (immediate w) reset h …` は `CompareRounds.next` の `hchain` と同形。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: 走査区間＋終端 shift 比較＋`shift_round` を `CompareRounds.next` に対応づけ、`rounds_origin` で `Entry` を保存）。

追記（同日、比較結果の分岐と二重計上の修正）：Scala との照合で 2 点修正。(1) `canShift` の `cycleEnd` は `matched()` の `cycle.dec` の前の値で判定され、一致時の `length += 2`（`matchedPlace`）が未反映だった → 比較の到達状態を一致ビットで分け、`afterCompare`（radius+1・periodOnly なら cycle−1・length+2、`GalilScaffoldTopSearch` に移動）と `afterMismatch`（radius+1 のみ）とし、`compareVM`/`compareFound` は `if a then afterCompare else afterMismatch`；`shiftGuardVM` の periodOnly 側は減算後の `zero cycle`（canonical なら減算前の `singlePositive` と同値）。`scanInv_compare_matched` の length canonical は `inc_canonical` ×2。(2) `beginChainShift` の `chain.matched()` は比較の `ChainTick true` で既に計上済みなのに `beginShiftVM` が再び `immediate` を掛けていた → chain はそのまま（periodOnly:=true・cycle リセットのみ）。`scan_shift_cycle`/`shift_round` の前提は `ChainShiftRun … w reset h …`（`CompareRounds.next` の `hchain` と同形：そこでの `immediate t.watch` が本コントローラの比較後の w）。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（同日、一致比較列と走査区間）：新モジュール `GalilScaffoldTopMatchedSeq.lean`（ルート import 済み）：`MatchedSeq n s t`（background のカウント tick と、chain が watching のまま・継続セルが末尾でない一致比較 n 回）、`compare_parts`/`matched_parts`、`background_only`（lag 零の背景 tick は射影不変）、`matchedSeq_only`（periodOnly・lag 零で `OnlyMatchedRun (toOnly s w) n (toOnly t w')` に射影）。新モジュール `GalilScaffoldTopScanSeg.lean`（ルート import 済み）：`ScanSeg`（コントローラの走査区間：wait/count/一致比較、clock 付き）、`scanSeg_steps`（`galilFrameS` の `Steps` へ）、`scanSeg_matchedSeq`、`scanSeg_only`（コントローラ実行 ⇒ 下層の `OnlyMatchedRun`）。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: 区間末尾の `cycleEnd` 比較＋`shift_round` を `CompareRounds.next` に対応づけ、`rounds_origin` で `Entry` 不変量を保存、found tick の供給、実時間供給、`StructuredMachine` 化、`SAccepts ↔ PAL`）。

追記（同日、only-compare 射影）：新モジュール `GalilScaffoldTopOnly.lean`（ルート import 済み）。`toOnly s w`（統合 VM の `OnlyCompareState` 射影）、`chainTick_true_immediate`/`chainTick_false_idle`（lag 零では有効 tick＝`immediate`、無効 tick＝不変）、`afterCompare_only`（periodOnly・lag 零での一致比較の到達状態の射影＝`onlyCompareNext`）を証明。`GalilScaffoldTopMatchedSeq.lean`（`MatchedSeq`：カウント tick と一致比較 n 回の列、`matchedSeq_only`：`OnlyMatchedRun` への射影）はドラフト中（未 import）。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（同日、periodOnly と cycle の反映）：Scala `canShift`（Watch∧lag 零∧phase 4∧（periodOnly なら `cycleEnd`＝`singlePositive cycle`、さもなくば margin ≥ 0））と `matched()` の `if (periodOnly) cycle.dec()`、`beginShift()` の `periodOnly = true; cycle.reset()` を反映：`GalilVM` に `periodOnly : Bool` を追加、`cycleAfter s` を定義して `compareVM`/`compareFound`/`afterCompare` の到達状態に `cycle := cycleAfter s` を追加、`shiftGuardVM` を Scala 通りに書き直し（`freshShiftGuard` は periodOnly=false の場合）、`beginShiftVM` で `periodOnly := true`。下層には `RestartState`（chainMode/periodOnly/restarts/clock を持つ Codex 期のコントローラ射影）と `dispatchOnlyMatch`・`restart`・`CompareRounds`（`OnlyMatchedRun` ＋ 末尾 `cycleEnd` ＋ `ShiftRun`/`ChainShiftRun` の m ラウンド）があり、`onlyCompareNext`（ヘッド移動・`immediate`・cycle−1・radius+1）は本コントローラの一致比較（periodOnly・lag 零）と一致する。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: 統合 VM の走査＋shift 一周を `CompareRounds.next` に対応づけ、`rounds_origin` で `Entry` 不変量を一周保存、found tick の供給、実時間供給、`StructuredMachine` 化、`SAccepts ↔ PAL`）。

追記（同日、一致比較での不変条件保存）：Scala `advanceMatch()` は `radius.inc()` も行う（`debt.dec()` と両方）と確認したので `radiusAfter s := inc s.radius` に修正（前段の設計メモは撤回：`ScanInv.radius` はそのまま正しい）。新モジュール `GalilScaffoldTopInvStep.lean`（ルート import 済み）：`afterCompare s vs vq`（`compareVM`/`compareFound` が作る到達状態）とその射影補題、`scanInv_compare_matched`（R 可用・外側記号一致・ヘッド移動の一致比較で `ScanInv` は半径 r+1 で保存：`scan_events_invariant`＋`inc_value`）。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: 不一致比較（shift 入口・fallback 入口）と shift 一周・fallback 一周での `ScanInv` の変化（中心と半径の更新）、found tick の供給、実時間供給、`StructuredMachine` 化、`SAccepts ↔ PAL`）。

追記（同日、比較 tick の radius 更新）：`GalilScaffoldTopSearch` に `ChainVM.isIdle`・`searchActive`（Scala `!mode.inactive`：idle/found/missed 以外）・`radiusAfter s`（search 活性かつ chain idle なら radius そのまま＝`advanceMatch`、さもなくば `inc`）を追加し、`compareVM`/`compareFound` の到達状態を `{… with radius := radiusAfter s}` に変更（`scan_match_S`/`found_start_match` も更新）。全体 build 成功・標準公理のみ・無条件 PAL は未完。**設計メモ**：`ScanInv.radius`（value radius = 走査半径）は search 活性中の一致では成り立たない（Scala は `advanceMatch` で search 側の debt に積む）。正しい不変条件は「value radius ＋（search 活性∧chain idle のとき search 開始以降の一致数）＝ 走査半径」の形で、search の `debt`/`span` との対応（`SearchFinish.begin`/`advance`）を読んで決める必要がある。次はここから。

追記（同日、shift 一周の接続）：新モジュール `GalilScaffoldTopShiftRound.lean`（ルート import 済み）。`shift_round`：`found_supplied_restart` が結論する形の `ChainShiftRun ⟨s1.center, s1.left, ofNat h, inc s1.radius, inc (inc s1.length)⟩ (immediate w) reset h endpoint watchEnd cycleEnd` を前提に、`beginShiftVM h w` の入口から `chain_shift_exhausts` と `scan_shift_cycle` で scan → shift → scan の一周（1+(h+1) tick）を `galilFrame` 上で得る。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: 比較 tick の radius カウンタ更新（Scala：search 活性かつ chain idle なら `advanceMatch`、さもなくば `radius.inc()`）を `compareVM`/`compareFound` に加え、`ScanInv` の一周保存を証明、実時間供給、`StructuredMachine` 化、`SAccepts ↔ PAL`）。

追記（同日、scan モード不変条件と shift の消尽）：新モジュール `GalilScaffoldTopInvariant.lean`（ルート import 済み）。`ScanInv raw s r`（下層の供給補題が比較 tick で仮定するもの：`ScanInvariant` を中心位置で、radius カウンタ＝走査半径かつ canonical、length canonical、中心ヘッドは入力の `represent` 形）を定義。`shift_run_remaining`/`chain_shift_exhausts`（remaining=h からの h 単位 shift で remaining が尽きる：`scan_shift_cycle` の `hz`）を証明。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: `found_supplied_restart` の結論 `ChainShiftRun` を `scan_shift_cycle` に渡す `shift_round`、`ScanInv` の一周保存、実時間供給、`StructuredMachine` 化、`SAccepts ↔ PAL`）。

追記（同日、入口の具体化）：新モジュール `GalilScaffoldTopGuards.lean`（ルート import 済み）。`shiftGuardVM`（watching な chain で `freshShiftGuard` かつ周期の予測記号＝R の読み）、`periodLength`（周期テープから半周期長 h）、`beginShiftVM'`/`beginFallbackVM'`（存在量化した入口効果）を定義し、`beginShift_exists`/`beginFallback_exists` から `compare_progress_concrete`（この具体入口を `galilShared` に与えた `galilFrame` で、scan モードの比較 tick は必ず存在）を証明。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（同日、watch 期間から shift guard）：新モジュール `GalilScaffoldTopWatchGuard.lean`（ルート import 済み）。`watch_tick_unique`/`watch_run_unique`（`Watch.Run` の決定性）、`ready_distance`、`watch_period_guard`：found tick の `ScanInvariant`、prep 期間の `ScanEvents (sm :: bs ++ dm :: cs)`、`watchStart` から watching のまま終わる watch 期間の `GRun`（chain 未破れ）から、イベント列 ws を取り出し、lag が尽き（`watchLag ws initialRadius = 0`）距離が 4h 以上なら、コントローラ自身の watch 状態で `freshShiftGuard = true`・距離＝走査半径・`ScanInvariant` が成り立つ（`watch_grun_supply` → `watch_shift_supply` → `shift_ready`、下層の証人は決定性でコントローラの状態に同定）。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: shift guard の残り条件（予測記号＝右読み）と `scan_shift_cycle` の入口前提への接続、fallback guard、found tick 自身の `ScanEvents` 供給、一周の連結、大域不変条件、実時間供給、`StructuredMachine` 化、`SAccepts ↔ PAL`）。

追記（同日、watch 期間の供給）：新モジュール `GalilScaffoldTopWatchSupply.lean`（ルート import 済み）。`watch_grun_supply`：`watchStart cen c ys b final`（lag=`ofNat initialRadius`）から始まり watching のまま終わる `GRun` から、イベント列 ws・`Watch.Run`・`VerifyRun.Run ⟨cen, ready c ys b⟩ (watchConsumes ws initialRadius) t'.machine`・`t'.lag = ofNat (watchLag ws initialRadius)`・ヘッドの `ScanEvents` を取り出す（`watch_shift_supply` の `hrun`/`hexhausted`/`hwatch` の形）。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（同日、watch 期間の chain tick と検証器実行）：新モジュール `GalilScaffoldTopWatchRun.lean`（ルート import 済み）。`broken_stays`（破れた chain は破れたまま、credit も受けない）、`chainTicks_watch_run`（watching のまま終わる chain tick 列は `Watch.Run`）、`verify_run_append`、`positive_ofNat_iff`/`zero_ofNat_iff`、`watch_run_verify`（lag が単進 `ofNat lag` の `Watch.Run` は検証器を `watchConsumes bs lag` 回消費し lag は `watchLag bs lag`：`Internal.take`/`Outer.immediate`/`Outer.queued` の算術が下層 `watchTick` と一致）を証明。これは `verify_watch_run_events` の逆向きで、コントローラ側の `GRun` から `watch_shift_supply` の `hrun`（`VerifyRun.Run ⟨cen, ready c ys b⟩ (watchConsumes ws r) z`）を作るための橋。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: `GRun`（watch 期間）→ `grun_events` → `chainTicks_watch_run` → `watch_run_verify` を `watch_shift_supply` に繋いで shift guard の成立を得る、fallback guard の具体化、大域不変条件、実時間供給、`StructuredMachine` 化、`SAccepts ↔ PAL`）。

追記（同日、prep 期間の連結）：新モジュール `GalilScaffoldTopPrep.lean`（ルート import 済み）。`prep_to_watch`：found な探索の後、chain が（同 tick の一致 sm で credit された）`chainStart` から始まる走査の一般実行 `GRun` のイベント列が `bs ++ dm :: cs`（copy h・終端・back h+1）なら、`grun_events`・`chainTicks_unique`・`found_to_watchStart` により終了時の chain は `watchStart ver c ys b (run (start (ofNat (r0+1))) (prepEvents sm dm bs cs))` に一致（ヘッドは同じイベント列の `ScanEvents` に従う）。これでコントローラの走査 tick 列から下層の watch 入口（`found_supplied_restart`/`watch_shift_supply` の前提の形）が得られる。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: watch 期間の `GRun` から `watchConsumes`/`watchLag` 型の前提を出して `watch_shift_supply` に接続、shift guard・fallback guard の具体化（`freshShiftGuard`・`FallbackGuard`）、大域不変条件（中心の正しさ）、実時間入力供給、`StructuredMachine` 化、`SAccepts ↔ PAL`）。

追記（同日、chain tick の決定性）：新モジュール `GalilScaffoldTopChainUnique.lean`（ルート import 済み）。`internal_unique`/`outer_unique`（watch の内部・外部 step は状態で決まる）、`break_not_good`/`break_outer_absurd`（破れは即時消費の失敗そのもので、`Outer true` と両立しない）、`chainStep_unique`（copy は答えセル、back は FIRST、watch は lag/Good で決まる）、`chainMatched_unique`、`chainTick_unique`、`chainTicks_unique`（同じイベント列・同じ開始状態の chain tick 列は一致）を証明。これで `found_to_watchStart` の到達状態は prep 期間の chain 状態そのもの（`grun_events` の `ChainTicks` と同定できる）。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（同日、一般走査実行のイベント抽出）：新モジュール `GalilScaffoldTopGeneralEvents.lean`（ルート import 済み）。`grun_events`（`GRun` から tick 単位のイベント列を取り出し、ヘッドは `ScanEvents`、chain は同じ列の `ChainTicks` に従う：`joint_run_events` の `ChainVM` 版）。これが下層の供給補題（`ScanEvents` と `prepEvents` 型の credit 実行を前提に取るもの）への接続口。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（同日、任意の chain での走査実行）：新モジュール `GalilScaffoldTopGeneralRun.lean`（ルート import 済み）。`GScan`（L/R・`ChainVM`・clock）と `GTick`（`JointTick` の `ChainVM` 一般化：R 不可用なら idle、clock>1 なら count、clock=1 で一致比較、chain は `ChainTick false/true`）、`GRun` を定義し、`grun_lift`（有効/無効イベント列上の `GRun` は scan frame の `Steps`、clock は 1..delay、replaying=false、odd/pair 不変）を証明。これで prep 中（copy/back）や idle/broken の chain を伴う走査 tick 列も scan frame に載る（イベントは tick 単位：`ScanEvents`/`prepEvents` と同じ粒度、copy step は 1 tick に 1 回）。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（同日、found → chain.start の比較）：新モジュール `GalilScaffoldTopFound.lean`（ルート import 済み）。`chainAt a found …`（比較時の chain 効果：通常は `ChainTick a`、chain が idle で search quantum が found に達したら `chainStart` してから一致なら credit）、`compareFound`（scan 射影の移動＋search quantum＋`chainAt`）、`galilFrameF`（`galilFrame` の compare を `compareFound` に）を定義し、`found_start_match`（idle な chain・found に達する quantum・一致比較 ⇒ `galilFrameF` の `scan_match` で chain が `chainStart` の credited 状態に）を証明。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（同日、Broken 後の restart tick）：新モジュール `GalilScaffoldTopRestart.lean`（ルート import 済み）。`restartVM entry`（chain が `.broken w` で margin 非負・last 正・lag 零のとき、chain idle・lower:=last・search:=`begin last radius`・DP プログラム `reset entry`）を `Shared.restart` に与え、`restart_tick`（scan モードで `Tick.restart`、clock リセット）を証明。`joint_break_restart` の結論がこの前提そのもの。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（同日、統合 VM の chain 載せ替え）：`GalilVM`/`ScanVM`/`ShiftVM` の `watch : Watch.State` を `chain : ChainVM` に置き換えた。`ChainVM`・`ChainStep`・`ChainMatched`・`ChainTick`・`BreakStep` の定義を早い段階の新モジュール `GalilScaffoldTopChainVM.lean`（ルート import 済み）へ移し、`chainTick_of_watch_false`/`chainTick_of_watch_true`（watching な chain の tick ＝ `Watch.Tick`）と `chainTick_of_break`（破れ＝`Internal.idle` の後 `ChainMatched.breaks` で `.broken`）を証明。`scanFrame` の background/compare は `ChainTick false/true`、`shiftFrame.shiftOne` は watching な chain の `chainShiftOne`、`count_lift`/`compare_lift`/`break_lift`/`joint_run_lift`/`shift_phase_vm`/`scan_shift_cycle`/`compare_progress`/`replayStart_tick`/`init_tick`/`fallback_to_scan` を `s.chain = .watch w` 前提で言い直し。`Top.Tick` に `restart` 構成子（scan モードで `F.restart s s'`、clock リセット）と `Frame.restart`/`Shared.restart` を追加し、レンズ引き戻し・転送・`galilShared` の全モジュールを更新。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: `restartVM`（Broken → `search.start(last)`・chain idle・DP リセット）の tick、found → `chainStart` を background に組み込む、大域不変条件、実時間供給、一本化、`SAccepts ↔ PAL`）。

追記（同日、chain 入口＝`watchStart`）：新モジュール `GalilScaffoldTopChainEntry.lean`（ルート import 済み）。`run_lag_ofNat`（credit 実行の lag は単進カウンタで単調増加）と `found_to_watchStart`：found な DP 探索（`found_start_back`）から、`chain.start()` と同 tick の credit sm、copy 歩行（一致列 bs）、終端 tick（credit dm）、back 歩行（一致列 cs）を `ChainTicks (bs ++ dm :: cs)` で辿ると、到達する watch 状態が下層の `watchStart ver c ys b (run (start (ofNat (r0+1))) (prepEvents sm dm bs cs))` に一致（半周期長 `ys.length+1 = h` は `Candidate` の `4h+1 ≤ |w|` から）。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: `ChainVM` を `GalilVM` に載せ替え `background`/compare を `ChainTick` で定義、`ChainMatched.breaks` からの restart、大域不変条件、実時間供給、一本化、`SAccepts ↔ PAL`）。

追記（同日、prep 中の走査クレジット）：`ChainStep.watchStep` を `Internal`（背景消費）に、`ChainMatched.watch` を `Outer true`（`chain.matched()`：margin+1、lag 零なら即時消費、さもなくば lag+1）に分離（`Watch.Tick w true` ＝ 両者の合成）。新モジュール `GalilScaffoldTopChainCredits.lean`（ルート import 済み）で `ChainTick a`（背景 step の後に一致なら credit）と `ChainTicks`、`creditsOf`、`step_copy`/`step_idle` を定義し、`copy_ticks`（copy 歩行＋一致列 bs ⇒ credit 状態は `run (creditsOf margin lag) (bs.map (true,·))`）と `back_ticks`（back 歩行＋一致列 cs、lag は正の単進カウンタなので最後の credit は `Outer.queued` ⇒ `run … (cs.map (false,·))`）を証明。これで `prepEvents` の各成分が `ChainVM` 上の tick 列に対応した。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: 開始 tick と終端 tick を含む `found_to_watchStart`（`GalilScaffoldTopChainEntry.lean` でドラフト中、未 import）、`ChainVM` の `GalilVM` への載せ替え、restart、大域不変条件、実時間供給、一本化、`SAccepts ↔ PAL`）。

追記（同日、found → watch）：新モジュール `GalilScaffoldTopChainStart.lean`（ルート import 済み）。`found_to_watch`：DP 探索が found で終わると（`found_start_back`）、`chainStart` から h 回の copy step・copy 終端・h+1 回の back step、計 h+(h+2) 個の `ChainStep` で `watch` モードに入り、その制御は `GalilScaffoldChainConsume.ready c ys b`（`ys ++ [b]` が半周期＝中心の次から h 個の場所）、lag=radius、margin=radius−4h（走査クレジットの割り込みなし版）。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: `ChainVM` を `GalilVM` の `watch` フィールドの代わりに載せて `background`/compare を `ChainStep`/`ChainMatched` で定義し直す（scan frame の `Watch.Tick` 前提を `ChainVM` 経由に一般化）、prep 中の走査クレジット割り込み版、restart（Broken → `search.start(last)`）、大域不変条件と実時間入力供給、複数プログラムの一本化、`SAccepts w ↔ w ∈ PAL` の合成）。

追記（同日、chain のモード VM）：新モジュール `GalilScaffoldTopChain.lean`（ルート import 済み）。Scala `ScaffoldChain` の Idle/Copy/Back/Watch/Broken を `ChainVM` として転写し、`chainStart`（found 時の `chain.start()`：period を FRONT+中心記号に、walker/verifier を中心に、lag=margin=radius）、`watchControl`（Back 終了時の制御＝`ready` の形）、`ChainStep`（`stepCopy`：答えテープの 1 セルごとに h+1・margin−4・walker 左・period に複写、LEFT で tail mark を書いて Back；`stepBack`：FRONT まで戻って 1 つ右へ進み Watch；Watch の無効 tick）、`ChainMatched`（`chain.matched()`：Copy/Back では lag+1・margin+1、Watch では有効 tick か破れ）、`ChainSteps` を定義。`copy_steps`/`back_steps` で下層の `GalilScaffoldChainPeriod.Copy`/`Back` 歩行と一致することを証明。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（同日、search 共走過程の frame）：新モジュール `GalilScaffoldTopSearch.lean`（ルート import 済み）。`searchQuantum a`（一致イベント a に対する 1 quantum＝`SafeQuanta … [a]`：64 回の安全な DP 呼び出しと `advance a`）、`searchIdle`、`compareVM`（scan 射影上の比較＋一致ビット a＋search 射影上の quantum か idle、他は不変）、`galilFrameS`（`galilFrame` の compare を `compareVM` に置換）を定義し、`tick_S_of_tick`（比較を含まない全 tick は `galilFrameS` でも tick）と `scan_match_S`（scan 側一致比較＋search quantum ⇒ `galilFrameS` の `scan_match`）を証明。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: init/replayStart の search 再始動の VM 効果、found → chain 開始（`found_supplied_restart`）と破れ後 restart の `galilFrameS` 上の接続、大域不変条件と実時間入力供給、複数プログラムの一本化、`SAccepts w ↔ w ∈ PAL` の合成）。

追記（同日、search 成分の VM 取り込み）：`GalilVM` に `search`（`SearchFinish.State`）・`dp`（DP 機械 12 テープ）・`lower` を追加し `searchLens` を定義（既存レンズ・証明は `{s with …}` のため無変更、`init_tick`/`replayStart_tick` のリテラルのみ修正）。全体 build 成功・標準公理のみ。init/replayStart の search 再始動（`search.start(zero)`＝`begin reset radius`＋DP プログラムのリセット）はまだ VM 効果に含めていない（次に追加）。無条件 PAL は未完。

追記（同日、出力健全性の統合 VM 版）：新モジュール `GalilScaffoldTopOutput.lean`（ルート import 済み）。`leftFirstVM`（L の位置が 1）と `onLetterVM raw`（R が k 文字目＝符号化位置 2k−1）を定義し、`output_sound`/`refresh_sound`（`ScanInvariant` のもとで refresh された出力が true なら先頭 k 文字は回文：`scan_output` を統合 VM の refresh に接続）を証明。出力の完全性（接頭辞回文なら出力 true）は「現在の中心が正しい」という Galil の大域不変条件そのもので、局所補題では閉じない。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: search 成分の統合 VM への取り込みと破れ後 restart、大域不変条件（中心の正しさ・`ReadOrigin`・restart 条件の一周保存）と実時間入力供給、複数プログラムの一本化、`SAccepts w ↔ w ∈ PAL` の合成）。

追記（同日、比較 tick の進行性）：`GalilScaffoldTopScan` の `scanFrame.compare` を「chain watch の `Tick true` か `BreakStep`（`JointBreak` の chain 側：lag 零・検証器可・周期記号と入力の不一致で消費し margin+1）」の選言に広げ、`break_lift`（`JointBreak` も出力 refresh つきの `scan_match`）を追加。新モジュール `GalilScaffoldTopBranches.lean`（ルート import 済み）で `compare_progress`（scan モード・clock 1・replaying=false・R 可用で、chain が tick か破れ、shift/fallback の入口効果が存在すれば、一致（`scan_match`）・shift（`scan_shift`）・fallback（`scan_fallback`）のいずれかの tick が必ず存在し、遷移先は scan/shift/copy）を証明。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: chain 破れ後の restart（`joint_break_restart` の条件から search 再開）と search 成分の統合 VM への取り込み、大域不変条件（`ScanInvariant`・`ReadOrigin`・restart 条件を一周ごとに保ち、出力＝接頭辞回文）と実時間入力供給、複数プログラムの一本化、`SAccepts w ↔ w ∈ PAL` の合成）。

追記（同日、chain watch tick の存在）：新モジュール `GalilScaffoldTopWatch.lean`（ルート import 済み）。`watch_tick_exists`（`Internal`（lag 正なら消費）と `Outer`（lag 零なら再消費、さもなくば queue）の両消費に必要な `Good` 条件のもとで `Watch.Tick s true t` が存在）と `watch_tick_false`（無効 tick は lag 正の消費が `Good` なら存在）を証明。`Good` が成り立たない場合が chain の破れ（`JointBreak` は lag 零・即時消費側の破れ）。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: 比較 tick での三枝の網羅（一致＝`JointTick.compare`、不一致＋guard＝shift、不一致＋¬guard＝fallback、chain 破れ＝restart）、大域不変条件（`ScanInvariant`・`ReadOrigin`・restart 条件を一周ごとに保つ）と実時間入力供給、複数プログラムの一本化、`SAccepts w ↔ w ∈ PAL` の合成）。

追記（同日、JointRun の持ち上げ）：新モジュール `GalilScaffoldTopJointRun.lean`（ルート import 済み）。`joint_run_lift`（有効イベント n 個の `JointRun` を、clock が 1..delay・replaying=false・各カウント tick で R が `canRight` の前提のもと、scan frame（`ScanVM`）の n tick の `Steps` に持ち上げ：clock>1 ではカウント、clock=1 で一致比較＋出力 refresh；終了時の clock は joint 側と一致、odd/pair 不変）を証明。`steps_pull scanLens` と `steps_transfer_scan` で `galilFrame` に載る。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: 三枝分岐の網羅（`JointBreak`・`FallbackGuard` から shift/fallback 入口前提を供給し、一致／shift／fallback のどれかが必ず起きることを示す）、大域不変条件（`ScanInvariant`・`ReadOrigin`・restart 条件を一周ごとに保つ）と実時間入力供給、複数プログラムの一本化、`SAccepts w ↔ w ∈ PAL` の合成）。

追記（同日、init と scan 実行の転送）：新モジュール `GalilScaffoldTopScanRun.lean`（ルート import 済み）。`init_tick`（init モードから 1 tick で scan モード・output=true、R 右・L/C を R に複写・length+1）、`scan_tick_stays`（scan frame の tick は scan モードと `replaying=false` を保つ：shift/fallback 入口は空）、`steps_transfer_scan`（scan frame の `Steps` 全体を `galilFrame` へ、frame の再パラメータ化つき）を証明。これで init を含む全モードの tick／実行が `galilFrame` 上に載った。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: `JointRun`（有効イベント列）を scan frame の `Steps` に持ち上げる `joint_run_lift`（clock 1..delay の不変条件）、三枝分岐の網羅（`JointTick`/`JointBreak`/`FallbackGuard` から入口前提を供給）、大域不変条件と実時間入力供給、複数プログラムの一本化、`SAccepts w ↔ w ∈ PAL` の合成）。

追記（同日、scan→fallback→scan の一周）：新モジュール `GalilScaffoldTopFallbackCycle.lean`（ルート import 済み）。`beginFallbackVM p`（`beginFallback` の VM 効果：FPP 状態を `FppControl.beginFallback program p length` に）を定義し、`scan_fallback_cycle`（scan モード・clock 1・replaying=false から、比較→不一致→shift guard 不成立→`beginFallback` の入口 tick に `fallback_to_scan` を連結：計 1+(n+1) tick で scan モード復帰、L=R=C は入口時の R から r 個下の中心、replay=r・radius=0・length=1・`replaying ↔ 0<r`、`ShiftIdle` 保存）を `galilFrame (galilShared …)` 上で証明。これで Scala コントローラの scan からの三枝（一致・shift・fallback）すべてが統合 VM 上で scan に戻る形になった。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: init 枝、`Steps` 版 scan 転送（count/wait の列）、三枝を選ぶ分岐の網羅（`JointTick`/`JointBreak`/`FallbackGuard` から入口前提を供給）、大域不変条件と実時間入力供給、複数プログラムの一本化、`SAccepts w ↔ w ∈ PAL` の合成）。

追記（同日、scan→shift→scan の一周）：新モジュール `GalilScaffoldTopShiftCycle.lean`（ルート import 済み）。`beginShiftVM h`（`beginChainShift` の VM 効果：remaining:=h・radius+1・length+2・watch:=`immediate`・cycle リセット）を定義し、`scan_shift_cycle`（scan モード・clock 1・replaying=false から、比較→不一致→shift guard→`beginShift` の入口 tick、`ChainShiftRun` n 単位、remaining 尽きて scan へ復帰、計 1+(n+1) tick、出力 refresh、`CopyIdle` 前提）を `galilFrame` 上で証明。`ChainShiftRun` と guard・入口の成立は `ReadOrigin`（`CompareRounds`）側から供給する前提。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: fallback 入口の具体化（`beginFallbackVM`：`FppControl.beginFallback` と `right_place`）と scan→fallback→scan の一周、init 枝、`Steps` 版 scan 転送、大域不変条件と実時間入力供給、複数プログラムの一本化、`SAccepts w ↔ w ∈ PAL` の合成）。

追記（同日、scan 枝の併合）：`Shared` に `shiftGuard`/`beginShift`/`beginFallback` を移し（`galilFrame` はこれらを `P` から取る）、`galilShared` はそれらをパラメータで受ける形に変更。新モジュール `GalilScaffoldTopScanMerge.lean`（ルート import 済み）で `scan_match_merge`（引き戻し scan frame の一致比較 tick を `galilFrame` の `scan_match` に、出力 refresh はレンズ等式で `t` に戻す）と `scan_transfer`（replaying=false のもとで scan frame の wait/count/match tick は `galilFrame` の tick；shift/fallback 入口は scan frame では空）を証明。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: `Steps` 版 scan 転送、shift/fallback 入口の VM 効果の具体化（`beginShift`：remaining:=h・radius+1・length+2・watch:=immediate・cycle リセット、`beginFallback`：`FppControl.beginFallback` と `right_place`）、init 枝、scan→shift→scan / scan→fallback→scan の一周、大域不変条件と実時間入力供給、複数プログラムの一本化、`SAccepts w ↔ w ∈ PAL` の合成）。

追記（同日、replayStart と fallback の scan 復帰）：新モジュール `GalilScaffoldTopReplay.lean`（ルート import 済み）。`Shared` の具体値 `galilShared`（`initVM`：R 右・L/C を R に複写・length+1、`replayStartVM`：replay:=radius・R/L/C:=C・radius リセット・length:=1、`replayPosVM`/`replayExhaustedVM`；chain/search の再始動は watch 成分に委ねる）と `positive_ofNat` を定義し、`replayStart_tick`（replayStart モードから 1 tick で scan モード・clock リセット・`replaying = positive radius`、出力は非 replay のときだけ refresh）と、`fallback_chain` に連結した `fallback_to_scan`（copy モードの `beginFallback` 状態から scan モード復帰まで一本：L=R=C が旧 R の r 個下の中心、replay=r、radius=0、length=1、`replaying ↔ 0<r`、`ShiftIdle` 保存）を証明。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: scan 枝の統合 VM への転送と shift/fallback 入口（`FallbackGuard` から `beginFallback` 状態を作る VM 効果）、init 枝、scan→shift→scan / scan→fallback→scan の一周、大域不変条件と実時間入力供給、複数プログラムの一本化、`SAccepts w ↔ w ∈ PAL` の合成）。

追記（同日、fallback 一周の連結）：新モジュール `GalilScaffoldTopCopyChain.lean`（ルート import 済み）。`copy_home_start`（`FppControl.fallback_prepared` を `fpp_control_run_lift`→`steps_pull`→`steps_transfer_fallback` で `galilFrame` に載せ、copy モードの `beginFallback` 状態から 2|w|+3 tick で fpp モード・準備済みプログラム実行中へ）と、それに `fpp_then_markEnd`・`choose_then_rewind` を連結した `fallback_chain`（copy モードから replayStart モードまで一本：`r = chosenRadius w` として L は R から 2r・C は r 戻り、length=2r+1・radius=r・FPP リセット・`ShiftIdle` 保存。前提は window 非空・|w| 偶数・FIRST ∉ {7,8}）を証明。これで Scala の fallback 経路（Copy→Home→Fpp→MarkEnd→Choose→Rewind→ReplayStart）が統合 VM 上で端から端まで繋がった。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: replayStart/init 枝の実体化、scan の転送と shift/fallback 入口（`FallbackGuard`→`beginFallback` の VM 効果）、scan→shift→scan と scan→fallback→scan の一周、大域不変条件と実時間入力供給、複数プログラムの一本化、`SAccepts w ↔ w ∈ PAL` の合成）。

追記（同日、choose→rewind→replayStart の連結）：`GalilScaffoldTopVM` に `choose_phase_vm`/`rewind_phase_vm` を追加。新モジュール `GalilScaffoldTopRewindChain.lean`（ルート import 済み）で `iterate_inc_ofNat`、`oddAt_false`、`marks_val`（cell 1..|w| は 7 か 8）と、`choose_then_rewind`（choose モード・`odd=false`・MARKS が `marks w` の cell 1 を FIRST にしたもの・ヘッド |w|・|w| 偶数・FIRST ∉ {7,8} のとき、`r = chosenRadius w` として (|w|−(2r+1)+1)+(2r+1) tick で replayStart モードへ到達、L は R から 2r 戻り・C は r 戻り・length=2r+1・radius=r・FPP リセット、`ShiftIdle` 保存）を `galilFrame` 上で証明。選択セルが `chosenRadius`（最長の奇数長回文接頭辞）に一致することは `marks_cell`・`chosen_spec`・`chosen_greatest` で示した。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: copy/home の連結（`fallback_prepared`）、replayStart/init 枝、scan の転送と shift/fallback 入口、一周の連結、複数プログラムの一本化、`SAccepts w ↔ w ∈ PAL` の合成）。

追記（同日、fpp→markEnd の連結）：新モジュール `GalilScaffoldTopFallbackChain.lean`（ルート import 済み）。`run_done_absorb`（halt 後の実行は不動）と `fpp_outcome_program`（fpp phase で halt したプログラムは `fpp_scheduled` の `⟨v,true⟩` に一致：実行の分割と決定性）、`markNew_tape`/`marks_after_fpp`（halt 後の MARKS は `marks w` の cell 1 を FIRST に置き換えたもの、ヘッドは 2）、`marks_no_end`/`marks_end`（cell 1..|w| は END でなく cell |w|+1 が END）を証明し、`fpp_phase_vm`（`Run` を返すよう拡張）・`steps_transfer_fpp`・`markEnd_phase_vm`・`steps_transfer_markEnd` を `galilFrame` 上で連結した `fpp_then_markEnd`（fpp モードの準備済みプログラムから n+1+|w| tick で choose モード・`odd=false`・MARKS ヘッドは cell |w|、fpp の他フィールド不変、`ShiftIdle` 保存）を証明。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: choose→rewind→replayStart の連結（`marks_cell` で選択セルを `chosenRadius` に同定）、copy/home の連結（`fallback_prepared`）、scan の転送と shift/fallback 入口、init/replayStart 枝、一周の連結、複数プログラムの一本化、`SAccepts w ↔ w ∈ PAL` の合成）。

追記（同日、markEnd の Steps 転送）：新モジュール `GalilScaffoldTopSteps3.lean`（ルート import 済み）。出口集合 E 内の tick も転送でき E が閉じている形の `steps_transfer_generic'` を証明し、`marks_choose_transfer`（marksFrame の choose モード tick は `choose_step` のみで、MARKS の markBack/markSet は fpp レンズ読みと rewind レンズ読みで一致）と `step_markEnd`・`step_marks_choose` により `steps_transfer_markEnd`（`ShiftIdle` 保存）を導出。これで shift/copy-home/fpp/markEnd/choose-rewind の 5 系統の `Steps` が `galilFrame` 上に転送できる。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: scan の転送（`compare_lift`/`count_lift` の `galilFrame` 版）、init/replayStart 枝、scan の shift/fallback 入口、`galilFrame` 上で init→scan→…→scan の一周を連結、複数プログラムの一本化、`SAccepts w ↔ w ∈ PAL` の合成）。

追記（同日、汎用 Steps 転送）：新モジュール `GalilScaffoldTopSteps2.lean`（ルート import 済み）。`steps_transfer_generic`（レンズ・部品 frame・モード集合 M・出口集合 E・不変条件 Inv を取り、「M 内の tick は M か E へ」「E からは tick 不能」「M 内の tick は転送可」から `Steps` 全体を転送）を証明し、`empty_rel` タクティクで空関係の構成子を落とす `no_tick_fallback`（fpp から）・`no_tick_fpp`（markEnd から）・`no_tick_rewind`（replayStart から）と、`ModeStep` 由来の `step_fallback`/`step_fpp`/`step_rewind` を用意して、`steps_transfer_fallback`・`steps_transfer_fpp`・`steps_transfer_rewind`（いずれも `ShiftIdle` 保存）を導出。`GalilScaffoldTopMerge` の fallback/fpp/markEnd/rewind の transfer は出力パラメータ f g について一般化。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: markEnd の `Steps` 転送（出口 choose で `choose_step` が残るため定常コントローラ形で扱う）、scan の転送、init/replayStart 枝、scan の shift/fallback 入口、一周の連結、複数プログラムの一本化、`SAccepts w ↔ w ∈ PAL` の合成）。

追記（同日、Steps 転送と不変条件）：新モジュール `GalilScaffoldTopSteps.lean`（ルート import 済み）。モード横断の不変条件 `CopyIdle`（copy モード外では FPP の複写カウンタが尽きている：走者読み不可 ∨ work 零）と `ShiftIdle`（shift モード外では remaining 非正）を定義し、`tick_pull_shape`（レンズ経由の tick の到達状態は `L.set s v` の形：22 構成子）から `copyIdle_shift`・`shiftIdle_fpp`・`shiftIdle_rewind`（他レンズの tick は不変条件を保つ）を導出。`no_scan_tick_shift`（shift frame では scan モードから tick できない）と frame の再パラメータ化を使い、`steps_transfer_shift`（shift モードで始まる shift frame の `Steps` は丸ごと `galilFrame` の `Steps`、`CopyIdle` 保存）を証明。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: fallback/fpp/markEnd/rewind/scan の `Steps` 転送、init/replayStart 枝、scan の shift/fallback 入口、`galilFrame` 上で init→scan→…→scan の一周を連結、複数プログラムの一本化、`SAccepts w ↔ w ∈ PAL` の合成）。

追記（同日、Frame 併合）：新モジュール `GalilScaffoldTopMerge.lean`（ルート import 済み）。共有パラメータ `Shared`（onLetter/leftFirst/init/replayStart/replayPos/replayExhausted）と、各モードのレンズ引き戻し frame からフィールドを取り寄せた統合 `galilFrame P q first`（remainingPos は shift 読みと copy 読みの選言）を定義。`wrong_mode` タクティク（`exfalso; simp_all; done`）で他モードの構成子を落とし、`shift_transfer`・`fallback_transfer`・`fpp_transfer`・`markEnd_transfer`・`rewind_transfer`（各モードの引き戻し frame の `Tick` は `galilFrame` の `Tick`、markBack は fpp レンズ読みから rewind レンズ読みへ書き換え）を証明。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: `scan_transfer`（replaying=false 前提）、init/replayStart 枝の実体化、scan の shift/fallback 入口、phase 定理群を `galilFrame` 上で連結して init から scan 復帰までの一周、複数プログラムの一本化、`SAccepts w ↔ w ∈ PAL` の合成）。

追記（同日、統合 VM）：新モジュール `GalilScaffoldTopVM.lean`（ルート import 済み）。Scala コントローラの VM 側部品（L/C/R ヘッド、chain watch、cycle/remaining/radius/length/replay カウンタ、FPP 状態）を一つの `GalilVM` に集め、`scanLens`/`shiftLens`/`fppLens`/`rewindLens` の 4 レンズ（3 則はすべて rfl）を定義。`steps_pull` により `shift_phase_vm`・`fpp_phase_vm`・`markEnd_phase_vm` を統合 VM 上で導出。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: 4 つの引き戻し frame を一つの `galilFrame` に併合するモード別の一致補題、init/replayStart 枝、scan の shift/fallback 入口、複数プログラムの一本化、`SAccepts w ↔ w ∈ PAL` の合成）。

追記（同日、VM 統合のためのレンズ）：新モジュール `GalilScaffoldTopLens.lean`（ルート import 済み）。`Lens σ σ'`（get/set と get_set・set_get・set_set 則）で部品側の `Frame σ'` を統合 VM 上の `Frame σ` に引き戻す `Frame.pull`（各関係は射影上で成立し、残りの σ は不変）を定義し、`tick_pull`（部品 frame の `Tick` は引き戻した frame の `Tick`、コントローラ記録は同一）を 22 構成子すべてについて、`steps_pull`（`Steps` も同様）を証明（公理は propext のみ）。これで `ScanVM`/`ShiftVM`/`FppControl.State`/`RewindVM` 上の各 phase 定理が、それぞれのレンズを通して一つの統合 VM 上に載る。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: 統合 VM の具体定義と各レンズ、init/replayStart 枝、scan の shift/fallback 入口、複数プログラムの一本化、`SAccepts w ↔ w ∈ PAL` の合成）。

追記（同日、choose/rewind 側 Frame 実体化）：新モジュール `GalilScaffoldTopRewind.lean`（ルート import 済み）。`RewindVM`（FPP 状態＋L/C/R ヘッド＋length/radius）と `rewindFrame first`（choose=L/C を R に複写・length=1・radius=0、rewindOne=MARKS 左・L 左・length+1、rewindPair=さらに C 左・radius+1、fppReset=`GalilScaffoldControl.reset 320`）を定義。`oddAt`（k 回トグル後の odd）と `pairAt`（m 歩後の pair）で、`choose_walk`/`choose_phase`（選択セルが k 個左なら k+1 tick で rewind モード・`pair=false`・L=C=R・length=1・radius=0・ヘッドは選択セル）、`rewind_walk`/`rewind_phase`（FIRST が m 個左なら m+1 tick で replayStart モード、L は m 回・C は m/2 回左、length は m 回・radius は m/2 回 inc、FPP リセット）を証明。これで init と replayStart 以外の全モード枝がコントローラ `Tick` に接続。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: replayStart/init 枝、scan の `scan_shift`/`scan_fallback` 入口、各枝 VM の統合（一つの σ）、複数プログラムの一本化、`SAccepts w ↔ w ∈ PAL` の合成）。

追記（同日、markEnd 側 Frame 実体化）：新モジュール `GalilScaffoldTopMarks.lean`（ルート import 済み）。FPP プログラムの物理テープ 8 を MARKS として `marksTape`/`markStep`、`MarksSame`（MARKS ヘッド位置以外の全保存：mode・走者・work・段フラグ・pc・done・他テープ・テープ内容）、`marksFrame first`（atEnd=focus が END(5)、markForward=右移動、markBack=左移動（左端でない）、markSet=focus が 8 か FIRST、atFirst）を定義。`markEnd_walk`（END でないセル k 個を右へ歩く k tick、ヘッド +k、内容保存）と `markEnd_phase`（ヘッドから k 先に最初の END があれば k+1 tick で choose モード・`odd=false`・ヘッドは END の 1 つ手前）を証明。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: choose/rewind/replayStart 枝（L/C/R ヘッドとカウンタを含む VM が必要）、scan の `scan_shift`/`scan_fallback` 入口、複数プログラムの一本化、`SAccepts w ↔ w ∈ PAL` の合成）。

追記（同日、fpp 側 Frame 実体化）：新モジュール `GalilScaffoldTopFpp.lean`（ルート import 済み）。`marked_wellFormed`（FPP マーク付きコード全命令の `WellFormed`、`decide`）、`control_run_unique`（`GalilScaffoldControl.Run` の決定性）、`control_run_split`、`markNew`（halt 後の `marks.move(1); write(FIRST); move(1)`）、`fppFrame q first`（fppSlice=quantum 個の有効 tick で未 halt、fppDone=quantum 個以内で halt しマーク）を定義。`fpp_slices`（m スライス後の不変条件）から `fpp_phase_lift`（スケジュール済みの実行が M·q tick 内で halt するなら、コントローラは fpp から markEnd へ到達し、走者・work・段フラグは不変）と `fpp_phase_scheduled`（`fpp_scheduled` の `1584·|w|+830` 命令上界を q で割ったスライス数で具体化）を証明。これで scan・shift・copy/home・fpp の四枝が接続。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: scan の `scan_shift`/`scan_fallback` 入口、markEnd/choose/rewind/replayStart 枝、複数プログラムの一本化、`SAccepts w ↔ w ∈ PAL` の合成）。

追記（同日、fallback 側 Frame 実体化）：新モジュール `GalilScaffoldTopFallback.lean`（ルート import 済み）。`FppControl.State` をそのまま VM とし、`fallbackFrame`（remainingPos=walker 読み可∧work 非零、copyOne=`copyBit`、copyEnd=`copyEnd`、atLeft=SOURCE focus が LEFT、homeStep=`sourceLeft`、fppStart=`startRun`）を定義。`FppControl.Mode.toController`（copy↦copy、home↦home、run↦fpp）で `fpp_control_lift`（有効な `FppControl.Tick` はすべて対応するコントローラ `Tick` で、記録は mode 以外不変）と `fpp_control_run_lift`（n tick の `Run` ⇒ `Steps n`）を証明。これで scan・shift・copy/home の三枝がコントローラ `Tick` に接続した。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: scan 枝の `scan_shift`/`scan_fallback` 入口と fpp/markEnd/choose/rewind/replayStart の Frame 実体化、複数プログラムの一本化、`SAccepts w ↔ w ∈ PAL` の合成）。

追記（同日、shift 側 Frame 実体化）：新モジュール `GalilScaffoldTopShift.lean`（ルート import 済み）。`ShiftVM`（`ShiftState`＋chain watch＋cycle）と `shiftFrame`（remainingPos=`positive remaining`、shiftOne=C 右 1・L 右 2・radius−1・length−2・`chainShiftOne`・cycle+2）を定義し、コントローラ `Tick` の n 回反復 `Steps` を導入。`shift_run_lift`（`ChainShiftRun … n …` ⇒ n 回の `shift_one`、コントローラ記録は不変）、`shift_exit_lift`（remaining 非正で `shift_done`、出力 refresh）、`shift_phase_lift`（shift 開始から scan 復帰まで n+1 tick）を証明。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: scan 枝の `scan_shift`/`scan_fallback` 入口（`JointBreak`・shift guard）と fallback 枝（`FppControl` 等）の Frame 実体化、複数プログラムの一本化、`SAccepts w ↔ w ∈ PAL` の合成）。

追記（同日、走査側 Frame 実体化）：`GalilScaffoldTop.Frame` に `background`（各 transition で mode step の前に走る chain/search の背景 tick）を追加し、`scan_wait`/`scan_count` がそれを通すよう修正。新モジュール `GalilScaffoldTopScan.lean`（ルート import 済み）：`ScanVM`（L/R ヘッド＋chain watch、clock はコントローラ側）と `scanFrame onLetter leftFirst`（available=`canRight`、compare=ヘッド移動＋`Watch.Tick true`、matched=L/R 読み一致、background=`Watch.Tick false`）を定義し、`count_lift`（`JointTick.count` ⇒ `Tick.scan_count`）と `compare_lift`（`JointTick.compare` ⇒ `Tick.scan_match`、出力は `onLetter`/`leftFirst` で refresh）を証明。これで `GalilScaffoldChainFallback` の統合 tick がコントローラ `Tick` の走査枝に接続した。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: shift/fallback 各枝の Frame 実体化、複数プログラムの一本化、`SAccepts w ↔ w ∈ PAL` の合成）。

追記（同日、コントローラ tick 骨組み）：新モジュール `GalilScaffoldTop.lean`（ルート import 済み）。Scala `ScaffoldGalil.transition` の `stepInit`〜`stepReplayStart` を、VM 側の効果（ヘッド・カウンタ・search・chain・fpp）を `Frame σ` の述語 31 個（init/available/compare/matched/shiftGuard/matchedPlace/…/replayStart/replayPos）に抽象化した上で、制御レベルの分岐・clock 規約・output/replaying/odd/pair の更新・mode 遷移を具体的に持つ `Tick F delay : State σ → State σ → Prop`（22 構成子）として転写。`tick_mode`（各 tick の mode は不変か `ModeStep` の辺）と `tick_bounded`（clock は正のとき −1 か delay へのリセットのみ、`Bounded delay` 保存）を証明。これで `GalilScaffoldController.BoundedControl` を有限制御成分として載せる形が固まった。今後は `Frame` を既存の `JointTick`/`JointBreak`/`FppControl`/`SearchFinish` 等で実体化し、`GalilScaffoldStructured.machine` を複数プログラム＋この制御に持ち上げる。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: `Frame` の実体化、複数プログラムの一本化、`SAccepts w ↔ w ∈ PAL` の合成）。

追記（同日、コントローラ有限制御）：新モジュール `GalilScaffoldController.lean`（ルート import 済み）。Scala `ScaffoldGalil.Mode` の 10 モード（init/scan/shift/copy/home/fpp/markEnd/choose/rewind/replayStart）を `Mode`（`Fin 10` との同型で `Fintype`）として転写し、`mode = Mode.X` 代入 11 箇所をそのまま `ModeStep` の辺に、`Reaches`（反射推移閉包）と `reaches_scan`（全モードが scan に戻る：fallback 環と shift 環が唯一の出口）、`no_step_to_init` を証明。Scala の `Control` レコード（mode/clock/output/replaying/odd/pair）を `Control` に転写し、clock ≤ matchDelay の `BoundedControl delay` を `Mode × Fin (delay+1) × Bool⁴` との同型で `Fintype` にした。これが `StructuredMachine` の有限制御に載せるコントローラ成分。公理依存なし。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: `stepScan`〜`stepReplayStart` の本体を Lean の tick 関係として転写し、`GalilScaffoldStructured.machine` を複数プログラム＋この制御に持ち上げて `SAccepts w ↔ w ∈ PAL` を合成）。

追記（同日、StructuredMachine 橋渡し）：新モジュール `GalilScaffoldStructured.lean`（ルート import 済み）。任意の scaffold プログラム `code : List (Instruction n)` を `StructuredMachine Unit (Fin (code.length+1) × Bool) (Fin 9) n 1`（有限制御＝clamp した pc と done フラグ、空白 `6`、入力 1 記号につき 1 micro step、入力記号は無視して tick の拍だけを与える）として実現する `machine hn code entry` を定義し、`tick_sim`（`GalilScaffoldControl.Tick code true x y` ⇒ `sMicroStep` が符号化構成上で一致）、`run_sim`（`Run code x (replicate m true) y` ⇒ `srun` 一致）、`saccepts_iff`（reset 構成からの m tick 実行の done フラグが `SAccepts (replicate m ())`）を sorry なしで証明。これでプログラム層（`GalilScaffoldControl`）と `Main.pal_in_peg_of_structured` が要求する機械型が初めて直結した。ただし Galil 全体は複数プログラム＋コントローラ＋実入力供給の合成であり、この橋は単一プログラム分。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: コントローラ全体を一本の `StructuredMachine` に落とし、`SAccepts w ↔ w ∈ PAL` を合成すること）。

追記（同日、出力完全性）：`GalilScaffoldChainFallback.lean` に `pairs_even`/`encoded_even`（符号化語の偶数位置はすべて区切り `2`）、`encoded_of_prefix_palindrome`（`prefix_palindrome_of_encoded` の逆：先頭 k 文字の回文 ⇒ 符号化語上で中心 k・半径 k−1 の `Manacher.PalAt`）、`scan_output_complete`（`ScanInvariant` が中心 k・半径 k−1 なら L=1・R=2k−1 の出力位置に立つ）を sorry なしで証明。これで走査の出力条件は健全性（`scan_output`）と完全性の両向きが揃った。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: `Main.pal_in_peg_of_structured` に渡す具体 `StructuredMachine` と `SAccepts ↔ PAL` の最終合成）。

追記（同日、破れ枝）: `GalilScaffoldChainFallback.lean` に統合 tick の「破れ」枝を追加。`JointBreak delay s t`（clock=1・右ヘッド可・走査側一致・lag 零・検証器 consume で不一致）とその事実集 `joint_break_facts`（broken=true、lag 不変、margin=inc、last/distance 不変、clock=delay、scan_matched）、`credits_margin_canonical`（前処理クレジットで margin の canonical 性が保たれる）、そして `joint_break_restart`（`joint_shift_supply` の供給結果 + `shift_ready` の freshShiftGuard から、破れ直後に restart 条件〈broken・lag 零・margin 非負・last 正・last canonical・成長〉が成り立つ）を sorry なしで証明。`#print axioms` は標準 3 公理のみ。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: 出力完全性、`Main.pal_in_peg_of_structured` への最終合成）。

**最新（2026-09-15、続き）：fresh shift → 任意回の再 shift → 終端 restart → 次 tick を実状態上で一気通貫。** `GalilScaffoldChainReadOrigin.lean` に追加：`shift_run_unique`/`chain_shift_unique`（決定性）、`Entry`（起点の再開入口不変量：OnlyScan/OnlyCredit/RadiusRep/machine=shifted/left=resumeLeft/center head 表現と位置）、`CompareRounds h s m s'`（一致周期 `OnlyMatchedRun` → cycleEnd＋右予測一致 → h 回の `ShiftRun`/`ChainShiftRun` 実行、の m ラウンド）、`rounds_origin`（Entry が保存され center/radius が m·h 進み shifts が m 増える帰納）、`rounds_restart`（末尾の左右一致・予測失敗枝で `Search.start` 入口条件）、`entry_of_only`（fresh `OnlyOrigin` ＋ shift 結果 ⇒ Entry）、`fresh_rounds_restart`（`scan_prediction_shift` の全前提から、ShiftRun/ChainShiftRun と「任意の m ラウンド＋終端一致 ⇒ center = 開始位置+(m+1)h、radius' = radius+1+m·h−h での restart 条件」）、`ReadOrigin.dispatch_match`、`read_terminal_dispatch_next_tick`（phase 前提・steps 前提なし版）、`rounds_dispatch_next_tick`（m ラウンド後の終端一致 → `dispatchOnlyMatch` → `restartInputTick` → 次 tick の scan/idle/restarts+1/clock/program/grow）。`scan_prediction_shift` の結論に `origin.center = position s.verifier`、`origin.radius = radius`、`4h ≤ distance (immediate t)` を輸出追加。全て標準公理のみ、`lake build PalPeg.GalilScaffoldChainReadOrigin` 8658 jobs 成功。未接続：周期途中の不一致（fallback 枝）、cycleEnd で左右不一致かつ予測不一致の枝、`CompareRounds` の各ラウンドの guard（右可用性・予測一致・length counter 正規性）を実 controller の tick から供給すること、実 restart の program.reset/lower alias/clock、物理 refinement、出力/締切、無条件 PAL。

追記（同日）：`ReadOrigin` に `phase : watched.control.phase = 4` を追加し、`phase_four_consume`/`phase_four_run`/`chain_shift_phase` で再 shift 越しに保存。`ReadOrigin.shift_guard`：Entry からの一致周期の末尾（cycleEnd・右可用・右＝予測）で、Scala `Chain.canShift`（periodOnly 側）の decoded 条件 lag=0・phase=4・左右不一致を導出。chainMode=watch / periodOnly は controller field として外部前提のまま。

追記（同日、fallback 側）：新モジュール `GalilScaffoldChainFallback.lean`（ルート import 済み）。`FallbackGuard`（matched 枝でも shift 枝でもない）と `fallback_window`：right head の `Represents` と length counter から、fallback の DP 窓が `w = (stream ⟨xs, right.gap⟩).take (ℓ+1)`（`raw = xs.reverse ++ rs ++ q`）で決まり、`place_ready` により fpp SOURCE の copy/home 後の内容が `bounded (w.map symbol)` になることを接続。これは後で `scan_prediction_shift` の `hw` が要求する形。**接続地図（次セッション用）**：(a) compare 側は `CompareRounds`/`rounds_dispatch_next_tick`/`shift_guard`/`FallbackGuard` で三枝が揃った。(b) fallback の残り：SOURCE 準備後の fpp プログラム実行（`GalilFppCode.code`、`GalilFppGeneration.process_all`、`GalilFppMarkSimulation.prepared_marks` は `List (Fin 4)` 入力）→ MarkEnd → Choose → Rewind → ReplayStart（Scala `ScaffoldGalil.scala` 355–440 行）→ fresh scan の `Run` と `scan_prediction_shift` の前提（`Candidate w lower h`、`hprepLag`/`hprepMargin`、`hstart`）の供給。MarkEnd/Choose/Rewind/ReplayStart の scaffold レベルの Lean モデルは未着手。(c) `PrepareControl`/`prepare_then_dp` は search 側 DP カーネル（`kernels.dp`、center 起点、LOWER）であって fpp ではないので混同しないこと。

追記（同日、Choose の意味論）：`GalilScaffoldChainFallback.lean` に `pairs_reverse_stream`/`encoded_of_represent`/`position_represent`/`stream_index`（right head から左へ読む stream と `encoded raw` の添字対応：`T[i] = e[position − i]`）、`stream_prefix_palindrome`（stream の奇数長 2r+1 の回文接頭辞 ⟺ `PalAt e (position − r) r`）、`chosenRadius`（Scala `stepChoose` の最長奇数 mark）、`choose_rewind`（新 center は head の r 下、radius r、かつ head で終わる最長奇数回文であること）。fpp の mark（`prepared_marks` の `(w.take b).reverse = w.take b`）を `Fin 3 → Fin 4` の埋め込みで stream の接頭辞回文へ移す橋と、Rewind/ReplayStart の head 操作（`copyFrom`/`left`）の decoded モデルは未接続。

追記（同日、fpp 合成）：`fallback_fpp_choose`：fallback 窓 `w = T.take (ℓ+1)` に対し、既存の `GalilFppPrepareLayout.marked_fpp w`（9 テープ fpp プログラムの実行終了時、mark テープ = w の回文接頭辞）と `chosenRadius w` を合成し、選ばれた奇数 mark が実際に立っていること、`PalAt e (|T|−r) r`（新 center は right head の r 下）、および窓内の最長性を一括で導出。`choose_rewind_window`/`window_take` も追加。**残る開口部**：scaffold の zipper SOURCE（`fallback_window` の `bounded (w.map symbol)`、`Machine 12`）と fpp の関数テープ `GalilFppPrepareInit.initial w`（`source w`、`Config 9`）の表現橋、Rewind/ReplayStart の head 操作の decoded モデル、replay scan、そして ReplayStart 後の background search（`prepare_then_dp`）から fresh watch（`scan_prediction_shift` の前提）への供給。

追記（同日、表現橋）：`fppInitial w`（9 テープ zipper、SOURCE = `bounded (w.map symbol)`）、`fppInitial_denote`（`denote` で `GalilFppPrepareInit.initial w`）、`fpp_realized`（`realize_completed` で `marked_fpp_exact_cost` を zipper 側へ：`Program.Completed` の実行、終了 pc=0、SOURCE 不変、mark テープ = `marks w`、歩数 ≤ 1584|w|+830）。zipper↔関数テープの橋は `Program.Completed` の粒度で閉じた。残り：`stepFpp` の quantum 刻み（`Control.Run`／`RawSchedule` 相当、DP 側 `GalilScaffoldDpCost.scheduled_correct` の fpp 版）、`fallback_window` の SOURCE（12 テープ `Machine 12` の tape 7）と `fppInitial`（9 テープ）の対応、Rewind/ReplayStart。

追記（同日、スケジューリング）：`fpp_scheduled`：`Control.scheduled_completed` で、命令機会が 1584|w|+830 回以上与えられれば `Control.Run GalilFppMarkedCode.code ⟨fppInitial w,false⟩ bs ⟨v,true⟩` で停止し mark が揃う（DP 側 `scheduled_correct` の fpp 版）。Scala `stepFpp` の quantum 刻みへの対応は `Control.Run` の粒度。残り：Copy/Home/Fpp 相の 9 テープ decoded controller（`PrepareControl` の fpp 版）で `beginFallback` から `fppInitial w` への到達、Rewind/ReplayStart。

追記（同日、fallback controller）：`FppControl`（9 テープ decoded controller：`Mode` copy/home/run、`State`、`beginFallback`（fpp reset・walker := right・remaining := length+1・SOURCE に LEFT）、`Tick` copyBit/copyEnd/sourceLeft/startRun、`Run`、`source_copy`/`source_home`）と `fallback_prepared`：`beginFallback old p length` から `2|w|+3` tick で run モードに入り、program がちょうど `⟨fppInitial w,false⟩`（`fpp_scheduled` の開始機械）。全 fallback 部品が揃った：`FallbackGuard` → `beginFallback` → `fallback_prepared` → `fpp_scheduled` → `fallback_fpp_choose`。次はこれらを right head（`Represents raw`）で一本に合成する `fallback_end_to_end`、その後 Rewind/ReplayStart の head 操作。

追記（同日、fallback 一本化）：`marks_cell`（`marks w i = 8 ⟺ 0<i≤|w| ∧ IsPal (w.take i)`）と **`fallback_end_to_end`**：compare 状態の right head（`Represents raw`、focus あり）と length counter から、`beginFallback` → `FppControl.Run`（2|w|+3 tick）で `⟨fppInitial w,false⟩` → `Control.Run`（機会 ≥ 1584|w|+830）で停止・mark = 窓の回文接頭辞 → 選ばれた奇数 mark が立ち、`PalAt (encoded raw) (position s.right − r) r` かつ窓内最長。Rewind の到達 center が `position right − r` であることまで意味論として固定。残り：Rewind/ReplayStart の head 操作（`copyFrom`/`left`）と counter 更新の decoded モデル、replay scan、background search → fresh watch。

追記（同日、replay）：`signedRead_pos` と **`replay_scan`**：新 center の head（`Represents`、位置 c、`r+1 ≤ c`）と `PalAt (encoded raw) c r` から、r 回の外側比較が全て一致し `ScanInvariant raw c k l r'`（k ≤ r）と `LeftMoves h k l` を帰納で復元（Scala の replay 中は shift/fallback が起きない、の Lean 側）。次：`fallback_end_to_end` と合成する `fallback_replay`（right head から r 回左へ動いた center head の存在：`Represents ∧ 位置 ≥ 1 → focus あり` の補題が要る）、その後 background search（`prepare_then_dp`）→ fresh watch。

追記（同日、fallback→replay 合成）：`present_of_position`（表現された head が位置 ≥ 1 なら focus あり）、`left_moves_exists`（位置 ≥ n+1 なら n 回の左移動が存在し表現保存）、**`fallback_replay`**：compare 状態の right head から、fallback の最長奇数回文の中心 head `h`（`LeftMoves right r h`、位置 `position right − r`）が存在し、replay の r 回比較で `ScanInvariant raw c k l r'`（k ≤ r）が復元される。fallback 枝は「入口 → fpp → 選択 → 巻き戻し → replay 復元」まで Lean 上で一本。残り：replay 完了後の background search（`prepare_then_dp` の `Result`/`Candidate`）から fresh watch（`scan_prediction_shift` の前提：`Candidate w lower h`、`hprepLag`/`hprepMargin`、`hstart`、`Run s bs t` の phase 4）への供給、Rewind/ReplayStart の counter 更新（length/radius/replay）の decoded 表現。

追記（同日、fresh watch 入口）：`fill_snoc_shape`（period tape の `fill` の形）、`copy_walk_period`（`ChainAnswer.CopyWalk` → `ChainPeriod.Copy`、period tape を `fill` で同時構成）、**`fresh_watch_entry`**：search が `.found` に達し DP `Result` を持つとき、`Candidate w lower h`、半周期 `ys ++ [b] = ((stream p).drop 1).take h`（|ys|+1 = h）、`Period.Copy` で `⟨(ys.map plain).reverse ++ [.first c], .plain b, []⟩`、tail mark 後の `Back (h+1)` で **`(ready c ys b).period`**、そして任意の外側一致イベント（|bs| = h、|cs| = h+1）に対する `prepare_paced` の credits（`final = run (start radius) (prepEvents sm dm bs cs)`、lag 非零）。これは `scan_prediction_shift` の `hs`（ready 制御）・`hprepLag`/`hprepMargin`・`hcopyLength`・`hc` の供給元。未接続：`ready` の他フィールド（counter reset/phase 0）を Scala `Chain.start` の decoded 状態として置く定義、verifier = center head（`hh`/`hstart`）の明示、そして Watch の実 `Run`（入力駆動）を SearchRun/tick から供給する部分。

追記（同日、found→restart 合成）：`watchStart cen c ys b final`（Scala `stepBack` 直後の decoded watch 状態：verifier = center head、`ready c ys b`、credits の lag/margin）と **`found_rounds_restart`**：search の found ＋ DP `Result`（center place ⟨a::ls,gap⟩ の窓）から、`fresh_watch_entry` で chain 側前提（ready 制御・半周期・Candidate・credits・center 位置）を全部埋めて `fresh_rounds_restart` を適用。外部前提として残るのは実 watch `Run s0 bs t'`（phase 4・lag 0）、fresh shift 時点の `ScanInvariant`／右可用性／予測一致／counter 事実。これで「search found → 準備 → watch → fresh shift → 再 shift × m → 終端 restart」が一本。未接続：watch `Run` 自体を tick から供給（Watch の Tick/Outer は既存、外側 scan の一致イベントと入力到着の interleave）、restart 後の background search と `SafeQuanta` の接続、fallback 後の replay 完了から search 開始（`search.start(zero)`）への接続、出力/締切、物理 refinement、無条件 PAL。

追記（同日、Candidate→bounce）：`palindrome_prefix_index` と **`candidate_bounce`**：DP `Candidate w lower h`（2h+1・4h+1 の回文接頭辞）、`w[0] = c`、半周期 `ys ++ [b] = (w.drop 1).take h` から `(w.drop 1).take (4h) = bounce c b ys ++ bounce c b ys`（純粋な添字論、標準公理のみ）。これは `caught_shift_guard`/`prepared_shift_guard` が要求する `Reads cen (bounce ++ bounce) q` の記号列側。残り：scan の回文（`PalAt e center radius`、4h ≤ radius）と `stream_index` の鏡映で verifier の右 4h 読みが窓の左 4h と一致すること（head からの Reads 存在補題が要る）、その Catch から watch `Run` の phase 4・lag 0 到達。

追記（同日、watch Run 供給）：`good_of_consume`（unbroken な consume ⇒ `Watch.Good`）、`verify_watch_run`（`VerifyRun.Run s n t` unbroken ⇒ `Watch.Run ⟨s, ofNat (n+k), margin⟩ (replicate n false) ⟨t, ofNat k, margin⟩`：内部 take のみ、lag が 1 読みごとに減る）、`verify_run_position`、**`found_watch_run`**：Codex の `found_window_safe`（found ＋ `Reach` ＋ 回文 ⇒ verifier の n ≤ min(radius, 4h) 読みが unbroken）と合成し、`watchStart` から `Watch.Run`（外側イベントなし）で lag が v−n、unbroken・表現保存・distance = n、4h ≤ n なら phase 4（`watch_phase`）。これで `found_rounds_restart` の外部前提 `hrun`/`hphase`/`hzero` の「外側一致イベントが interleave しない場合」の供給ができた。残り：外側一致（`true` tick、lag/margin の queued/immediate）の interleave と lag = v の一般会計（Codex の `prepared_balance`/`shift_ready`）、fresh shift 時点の `ScanInvariant`／右可用性／予測一致の供給、restart 後・replay 後の search 起動、出力/締切、物理 refinement、無条件 PAL。

追記（同日、外側イベント interleave）：`watchTick`/`watchConsumes`/`watchLag`（tick ごとの consume 数と lag：lag>0 なら内部 take、`true` なら lag=0 で immediate・そうでなければ queued）、`verify_run_add`（`VerifyRun.Run` の分割）、**`verify_watch_run_events`**：任意の外側イベント列 `bs` と初期 lag に対し、`watchConsumes bs lag` 本の unbroken な consume があれば `Watch.Run ⟨s, ofNat lag, ofNat margin⟩ bs ⟨t, ofNat (watchLag bs lag), ofNat (margin + count true)⟩`。これで watch の `Run` は「その本数の unbroken 読みが存在する」ことに帰着した（`found_window_safe` は 4h まで保証）。残り：fresh shift 時点の `ScanInvariant`／右可用性／予測一致の供給（scan 側の一致イベントと `bs` の同一視）、lag 会計の一般化（Codex `prepared_balance`/`shift_ready`）、search 起動、出力/締切、物理 refinement、無条件 PAL。

追記（同日、watch 相の供給）：`incN`/`incN_value`/`incN_canonical`、`verify_watch_run_events` を任意 margin counter に一般化（外側イベントごとに `inc`）。`ScanEvents`（watch 中の scan 側：`true` = 一致比較で `scan_matched`、`false` = 静止）と `scan_events_invariant`。**`watch_shift_supply`**：chain 開始時の `ScanInvariant`（radius r₀ = value radius）、prep 中と watch 中の `ScanEvents`、`watchConsumes` 本の unbroken 読み、lag 枯渇（`watchLag = 0`）から、`Watch.Run s0 ws t'`・`value s0.lag = r₀ + prep 一致数`・lag 0・distance = scanRadius・（4h ≤ scanRadius なら phase 4）・`ScanInvariant raw (position cen) scanRadius l₂ rr₂` を一括導出（`prep_value` で lag と scan radius の会計を同一視）。これで `found_rounds_restart` の外部前提のうち watch 相の分が「同じイベント列」から出る。残り：fresh shift 時点の右可用性・予測一致・counter 事実（radiusCounter = scanRadius+1 等）の供給と `found_rounds_restart` への最終合成、restart 後・replay 後の search 起動、出力/締切、物理 refinement、無条件 PAL。

追記（同日、最終合成）：`credits_lag_canonical` と **`found_supplied_restart`**：`found_rounds_restart` の watch 相前提を `watch_shift_supply` で埋めた版。外部前提は、chain 開始時の `ScanInvariant`（radius r₀ = value radius）、prep 中と watch 中の `ScanEvents`（scan と chain が同じイベント列を見ること）、`watchConsumes` 本の unbroken 読み、lag 枯渇、4h ≤ scanRadius、shift 枝の入力側条件（右可用・予測＝右読み・左右不一致）、counter 表現のみ。結論は `∃ t', Watch.Run (watchStart …) ws t' ∧ t'.machine = z ∧ lag 0 ∧ ∃ endpoint…, ShiftRun ∧ ChainShiftRun (immediate t') ∧ ∀ m n…（再 shift × m → 終端 restart 条件）`。残り：restart 後・replay 後の search 起動（`SafeQuanta` と `search.start`）、周期途中の不一致（chain broken → restart）の scan レベル接続、出力/締切、物理 refinement、無条件 PAL。

追記（同日、出力の意味論）：`pairs_odd`/`encoded_odd`（`encoded raw` の奇数位置 2i+1 は `letter raw[i]`）、`letter_inj`、`prefix_palindrome_of_encoded`（`PalAt (encoded raw) k (k−1) → IsPal (raw.take k)`）、**`scan_output`**：`ScanInvariant raw c r l rr` で L が位置 1（Scala `left.isFirst`）、R が位置 2k−1（k 番目の文字上）なら `IsPal (raw.take k)`。Scala の `output = left.isFirst` の健全性側。完全性側（接頭辞が回文なら scan がそこに到達する）は `Assembly.answer_length_iff_mem_PAL` 等の仕様レベルに対応し、scaffold レベルでは未接続。

追記（同日、staged search との接合）：`stage_found_supplied`：`GalilScaffoldStagePrepare.prepared_exit` の探索実行 `SafeQuanta (runState p q) p.program cs u y` が `.found` で終わり `y` に DP `Result` があるとき、`found_supplied_restart` がそのまま適用できることの接合。これで Codex の「準備 → run → found/missed/次 stage」（時間予算つき）と、ウチの「found → chain → shift/再 shift → restart」が同じ状態の上で繋がった。残る大物：`prepared_exit` の found 出口から `Result` を取り出す（`dp_quanta_safe` の存在実行と実際の実行の同一視、または `prepared_exit` に Result を輸出させる）、restart（`restart_input_tick` の `.grow`）から次の `PacedPrepared` へ、fallback/replay 完了から `search.start(zero)` へ、出力の完全性、物理 refinement、無条件 PAL。

追記（同日、探索の決定性）：`execute_unique`（`WellFormed` な命令の zipper 側 `Execute` は決定的：read 表の `Nodup`）、`control_tick_unique`（`dp_wellFormed` で DP コードの `Control.Tick` が決定的）、`safe_calls_unique`/`safe_quanta_unique`/`safe_quanta_append`/`safe_quanta_cons_run`、**`dp_run_result`**：DP 予算（3186|w|+1683 ≤ 64|cs|、count true ≤ debt）を持つ実際の `SafeQuanta s ⟨Preload.initial w lower,false⟩ cs u y` は `dp_quanta_safe` の停止実行そのものであり、`y = ⟨v,true⟩` かつ `Result w lower 0 (denote v)`。これで `stage_found_supplied` の `hv` は実行から取り出せる（`prepare_complete` の `program.config = Preload.initial w lower ∧ done = false` と合わせる）。残り：restart（`.grow`）→ 次の `PacedPrepared`、fallback/replay 完了 → `search.start(zero)`、出力の完全性、物理 refinement、無条件 PAL。

追記（同日、found ↔ 候補）：`RunInvariant`（`run` ↔ 未停止、停止後は `found ↔ pc = 346`）、`safe_calls_invariant`/`safe_quanta_invariant`（`SafeCalls`/`SafeQuanta` に沿って保存、`finish_run_iff`・`found_iff` を使用）、**`run_found_candidate`**：DP 予算つきの実 `SafeQuanta s ⟨Preload.initial w lower,false⟩ cs u y` は `y = ⟨v,true⟩`・`Result`・`u.mode ≠ run`・`u.mode = found ↔ ∃ k, Candidate w lower k`。これで `stage_found_supplied` の `hu`/`hv` は「実行が found で終わった」事実そのものから出る。残り：`prepare_complete` の出口（`program.config = Preload.initial w lower`）と `runState` の接合定理、restart（`.grow`）→ 次の `PacedPrepared`、fallback/replay 完了 → `search.start(zero)`、出力の完全性、物理 refinement、無条件 PAL。

追記（同日、stage → chain）：**`stage_run_chain`**：`prepare_complete` の出口 `t`（run、`program = ⟨Preload.initial w lower,false⟩`）と実際の `SafeQuanta (runState t q) t.program cs u y`（DP 予算つき）から、`y = ⟨v,true⟩`・`Result`・`u.mode ≠ run`・`found ↔ 候補あり`、そして found なら `stage_found_supplied` の chain 入口。残り：restart（`.grow`、`GalilScaffoldGrow`）→ `PacedPrepared` の dispatch、fallback/replay 完了 → `search.start(zero)`、found 後の chain と scan の同一イベント列の供給元、出力の完全性、物理 refinement、無条件 PAL。

追記（同日、第 1 stage との接合）：**`first_stage_chain`**：Codex の `StagePrepare.first_stage_safe`（grow → `PacedPrepared` → 実 DP 実行、`advances 2048 2048 es` の時計対応、`3·radius ≤ 5·r`）の出力に `stage_found_supplied` を当てる。`t.mode = found` かつ `p.mode = run` なら DP 候補と半周期（ひいては `found_supplied_restart` の全鎖）。これで「探索の第 1 stage（時計付き）→ found → chain → shift/再 shift → 終端 restart」まで同じ状態の上で接続。残り：`p.mode = run` を `PacedPrepared` から導出、restart（`restart_input_tick` の `.grow`）から第 2 stage 以降（`NextStage`）へ、fallback/replay 完了 → `search.start(zero)`、found 後の scan と chain の同一イベント列の供給元、出力の完全性、物理 refinement、無条件 PAL。

追記（同日、準備の決定性）：`Prep` 名前空間：`Same`（debt 以外の場の同値）、`tick_same`（`PrepareControl.Tick` は `Same` に沿って移送）、`tick_unique`（enabled tick は決定的：mode／work の正負／テープ focus／walker の読みで排他）、`run_unique`、`paced_same`（全 enabled の `PacedRun` は debt 以外で plain `Run` と一致）、**`paced_prepared_mode`**：`PacedPrepared (ofNat lower) center s bs p` で `|bs| = 2·lower+2|w|+7`、`s.span = ofNat span` なら `p.mode = run ∧ p.program.config = Preload.initial w lower ∧ done = false`。`first_stage_chain` の `p.mode = run` 前提はこれで落とせる（`u.span` の値が `PacedGrowing` から要る）。残り：restart（`.grow`）→ 第 2 stage 以降、fallback/replay 完了 → `search.start(zero)`、scan/chain の同一イベント列の供給元、出力の完全性、物理 refinement、無条件 PAL。

追記（同日、stage 接合の完成）：`paced_growing_span`（grow tick ごとに span +8）、**`first_stage_chain_run`**（`p.mode = run` を `paced_prepared_mode` から導出した版）、**`later_stage_chain`**：Codex の `later_stage_safe`（`.double` から `Double.Run` → `restoreState` → `PacedPrepared` → 実 DP 実行、時計 `advances 2048 clock es`）の found 出口に `stage_found_supplied` を当てる（span は `Double.span_of_run` で供給）。これで第 1 stage・後段 stage の両方から chain 入口へ繋がった。残り：restart（`restart_input_tick` の `.grow`）から `later_stage_safe` の入口（`.double`、work = |as|、span 0、debt 条件）への遷移、fallback/replay 完了 → `search.start(zero)`、scan/chain の同一イベント列の供給元、出力の完全性、物理 refinement、無条件 PAL。

追記（同日、restart → 第 1 stage）：`initialDebt_value`/`initialDebt_canonical`、**`begin_entry`**（`Search.start` 直後の scheduler `begin lower radius` は grow・`work = ofNat (max k 1)`・span 0・`value debt = −radius`・Canonical）、**`restart_first_stage`**：`restoreState b0 (begin lower radius)` から `first_stage_chain_run` を適用し、restart 後の探索（grow → 準備 → DP → found）から chain 入口まで。`restart_input_tick` の scheduler が `begin last radius` であることは `restart` の定義から読めるが、`restartInputTick`/`receiveRestart`/`restartScanTick` が search を触らないことの明示補題はまだ（次）。残り：その明示、fallback/replay 完了 → `search.start(zero)`（`begin_entry` で同型に接続可）、scan/chain の同一イベント列の供給元、出力の完全性、物理 refinement（RawTick `Represents` と `Control.Machine` の橋は `restart_input_tick` が輸出）、無条件 PAL。

追記（同日、restart tick の scheduler）：**`restart_input_tick_scheduler`**：`restartInputTick entry delay replaying trailing input s = some t` なら `t.search = startSearch entry last radius arrived.search`（`arrived := receiveRestart s input`）、scheduler = `begin last radius`、program = `RawTick.reset entry …`。これで `rounds_dispatch_next_tick`（終端一致 → dispatch → restart tick）の出口が `begin_entry`／`restart_first_stage` の入口（`begin lower radius`）に文字通り繋がる。残り：`RawTick.Machine`（heap 実装）と `Control.Machine 12` の `Represents` 橋を `restoreState` の program に通すこと、fallback/replay 完了 → `search.start(zero)`、scan/chain の同一イベント列の供給元、出力の完全性、無条件 PAL。

追記（同日、prepare の物理実現）：`RawPrep` 名前空間：`written_heap`/`moved_heap_other`（heap frame）、`represents_write`/`represents_write_right`/`represents_left`/`represents_start`（抽象テープ操作の raw 対応、`HeapProgram.written_represents`/`moved_right`/`moved_left` から）、**`prepare_tick_raw`**（`PrepareControl.Tick` は heap 機械上で fresh セル高々 1 個で実現され `RawTick.Represents` を保つ、他セル不変）、**`prepare_run_raw`**（`PrepareControl.Run` は distinct な fresh 番地列に沿って実現）。これで `restart_input_tick` が輸出する `Represents t.search.program ⟨⟨entry,reset⟩,true⟩` から、抽象 stage（`prepare_complete`）の出口 `⟨Preload.initial w lower,false⟩` を表す raw 機械が得られ、DP 実行は `RawSchedule.realize_run` で raw 側へ写せる。残り：`prepare` dispatch（`reset 320` と LOWER 書き込み）の raw 対応、scan/chain の同一イベント列の供給元、出力の完全性、無条件 PAL。

追記（同日、prepare dispatch の物理実現）：**`RawPrep.prepare_raw`**（`prepare x lower center` の program = `reset 320` ＋ LOWER への write-right は heap 機械上で `RawTick.reset` ＋ `written`/`moved` で実現、fresh セル 1 個、他セル不変）と **`RawPrep.prepared_run_raw`**（`PreparedRun lower center s n t` は distinct な fresh 番地 n 個で実現され、出口 `t.program`（`prepare_complete` なら `⟨Preload.initial w lower,false⟩`）を表す raw 機械が存在）。DP 実行側は `RawSchedule.realize_run`（`Control.Run` → raw `Run`、fresh 番地列）で対応済み。残り：`SafeQuanta` の機械列を `Control.Run`/`GuardedRun` として取り出して `realize_run` へ渡す接合、scan/chain の同一イベント列の供給元、出力の完全性、無条件 PAL。

追記（同日、DP 実行の物理実現）：`safe_calls_control_run`/`control_run_append`/`safe_quanta_control_run`（`SafeQuanta` の機械列は有効フラグ列 `es`（|es| = 64|as|）に対する `Control.Run`）、`dp_wellFormed_lookup`、**`quanta_raw`**：`RawSchedule.realize_run` により、実探索 `SafeQuanta s x as t y` は `Represents raw x` な heap 機械上で fresh 番地列（64|as| 個）に沿って `RawSchedule.Run` として実現され、終端は `Represents raw' y`。`prepared_run_raw` の出口 raw 機械をここに渡せば、restart → 準備 → DP → found までが raw 側でも一本。残り：restart tick の `Represents t.search.program ⟨⟨entry,reset⟩,true⟩` から `prepared_run_raw` へ渡す際の番地 fresh 性（heap の有限性 `FiniteHeap` から fresh 番地列を取る補題）、scan/chain の同一イベント列の供給元、出力の完全性、無条件 PAL。

追記（同日、stage の物理実現）：`RawPrep` に `moved_finite`、`fresh_addresses`（有限 heap から distinct な fresh 番地列を任意個）、`prepare_tick_raw`/`prepare_run_raw`/`prepare_raw`/`prepared_run_raw` に `FiniteHeap` 保存を輸出、`paced_run_raw`/`paced_prepared_raw`（`PacedPrepared` の raw 実現）。`paced_growing_program`（grow は program 不変）と **`stage_raw`**：`s.program` を表す有限 heap の raw 機械から、`PacedGrowing → PacedPrepared → SafeQuanta` の stage 全体が fresh 番地列に沿って raw 側で実現され、終端は `⟨v,true⟩` を表す（`Represents`）。`restart_input_tick` の `Represents t.search.program ⟨⟨entry,reset⟩,true⟩` を入口にすれば、restart 後の探索は raw 側でも `stage_raw` で一本。残り：raw 番地列と Scala の実 heap 割り当て（`Allocator`/`Bounded`）の対応、scan/chain の同一イベント列の供給元、出力の完全性、無条件 PAL。

追記（同日、Scala 割り当てとの橋）：**`bounded_finite`**（Codex の `Allocator` の `Bounded` 不変量 ⇒ `FiniteHeap`）と **`blocks_fresh`**（現在 node 以降の m 個の連続 `block (node+1+i) 64 slots` の連結は長さ 64·m・distinct・fresh）。これで `stage_raw`/`quanta_raw` の fresh 番地列を Scala の実割り当て（tick node ごとの 64 セルブロック）で供給できる。残り：scan/chain の同一イベント列の供給元、出力の完全性、無条件 PAL。

追記（同日、統合 tick）：**`JointState`/`JointTick`/`JointRun`**（scan の左右 head・chain の `Watch.State`・match clock を 1 つの遷移に：不可用 tick／カウントダウン／clock=1 で発火する一致比較、chain 側は同じ tick の `Watch.Tick`）と **`joint_run_events`**：1 つの `JointRun` から同一のイベント列で `Watch.Run` と `ScanEvents` が出て、`true` の個数と終了 clock が Codex の `MatchClock.run delay clock avail` に一致。これが「scan/chain の同一イベント列の供給元」。shift／fallback の比較枝は別関係（`shift_guard`・`FallbackGuard`）で扱う。残り：`JointRun` から `watch_shift_supply` 相当を出す系（次）、出力の完全性、無条件 PAL。

追記（同日、統合 tick からの供給）：**`joint_shift_supply`**：`JointRun` 1 本（`watchStart` から、match clock `delay`/`clock0`、可用列 `avail`）と lag 枯渇から、同一イベント列 `events`（`count true = (MatchClock.run delay clock0 avail).2`）で `Watch.Run`、`value s0.lag = r₀ + prep 一致数`、distance = scanRadius、（4h ≤ scanRadius なら phase 4）、`ScanInvariant raw (position cen) scanRadius t.left t.right`、終了 clock。`watch_shift_supply` の「同一イベント列」前提が `JointRun` の定義そのものに帰着した。残り：`JointRun` の各 tick の `Watch.Tick`（`Good` = 予測と入力の一致）を入力側から供給する扱い（これは shift 枝の分岐条件そのもの）、出力の完全性、無条件 PAL。

追記（同日、replay 後の探索入口）：`begin_entry` を `k = 0` を含む形へ一般化（`zero lower` なら `work = inc lower = ofNat 1 = ofNat (max 0 1)`）、**`replay_stage_entry`**：`ReplayStart` の `search.start(zero)`（`begin (ofNat 0) reset`）は grow・work 1・span 0・debt 0。`restart_first_stage` と同型に `first_stage_chain_run` へ渡せる（radius 0 なので `3·radius ≤ 5·k` は自明）。残り：`RawTick.Machine` と `Control.Machine 12` の `Represents` 橋を program に通すこと、scan/chain の同一イベント列の供給元、出力の完全性、無条件 PAL。

**最新（2026-09-15、Claude Code）：再 shift を起点から起点へ回せる形にした。** 新モジュール `lean-pal/PalPeg/GalilScaffoldChainReadOrigin.lean`（ルート import 済み）。`Offset k c d`（control が参照 sweep `run ready pre` の counter 一様 −k、period/forward/broken 一致）を定義し、`consume`/`run`/`ChainShiftRun` で保存されることを証明（`Offset.run`/`Offset.shift`）。`OnlyOrigin` の fresh watch `Run` 依存を外した `ReadOrigin`（`pre`/`reads`/`shifts`/`offset`/三 counter Canonical/`length : 2(k+2)h ≤ |pre|`）を定義し、`check_pair`/`joined_reads`/`joined_input_period`/`reshift_compare`/`reshift_palindrome`/`matched_checked`/`matched_restart` を Reads ベースで移植（`read_prediction_window`/`read_check_pair`/`read_compare_restart`、`sweep_last_lower` は m 周期版 `last` 下界）。`ReadOrigin.ofOnly`（fresh 起点＋distance≥4h ⇒ shifts=0 の起点）と **`ReadOrigin.reshift_origin`**（一周期の一致比較＋cycleEnd＋右予測一致 ⇒ center+h, radius+h, shifts+1 の起点と、その resumed 端点の OnlyScan/OnlyCredit/RadiusRep）を証明。`lake build PalPeg.GalilScaffoldChainReadOrigin` 8658 jobs 成功・標準公理のみ。Codex 最終定理 `reshift_initialized` のビルド失敗も修正済み。次は `OriginRun`（複数ラウンドの実行関係）で不変量を帰納し、終端枝（`matched_restart`）と接続する。全 controller / 実 restart 全更新 / 無条件 PAL は未完。

**修正**：Codex 最終ターン（9/14 09:59）の `OnlyOrigin.reshift_initialized`（`GalilScaffoldChainInputSupply.lean` 約3014行）は `hnew` の `simpa` が算術正規化でずれてビルド失敗していた。`hpos` と `omega` で `rw` する形に直し、`lake build PalPeg.GalilScaffoldChainInputSupply` が exit 0、同定理の公理は propext/Classical.choice/Quot.sound。全体 build は未再実行。

**進行中の設計（次の実装）**：再 shift 後に起点を再構成するため `OnlyOrigin` を fresh watch の `Run` 依存から外す。
- 新フィールド：`pre : List (Fin 3)`、`reads : Reads start.verifier pre watched.verifier`、`shifts : ℕ`（これまでの shift 回数 k）、`control : Offset (k*h) watched.control (run (ready token interior boundary) pre)`（SamePrediction ∧ broken 一致 ∧ phase 一致 ∧ distance/boundary/last の値が −k·h）、三 counter の Canonical、`length : 4h + k*h ≤ pre.length`。`ticks/watchRun/startPosition` は削除（`endPosition` は残す）。
- 根拠：`chainShiftOne` は distance/boundary/last を一様に −1 し period/phase を保つ（`chain_shift_values`）。`consume` の counter 更新は last:=boundary、boundary:=distance、distance:=inc なので一様オフセットと可換。よって shift 後の control は `run ready pre` の一様オフセットに正確に等しい。
- 移し替える補題：`watch_previous_window`（Reads + `successful_cycles` + `reads_index` で証明し直す）、`shifted_prediction_window`、`shifted_check_pair`、`only_history_check_pair`、`watch_last_lower`（m 周期版：`round_trip` を m 回で `(2m−1)h ≤ last`）、`watch_shift_last_positive`、`history_terminal_last/canonical`、`only_compare_restart`。Run 版は run_trace から導く薄い wrapper として残す。
- 新定理 `OnlyOrigin.reshift_origin`：`reshift_after_matches`＋`reshift_compare`＋`reshift_initialized` から `center' = center+h, radius' = radius+h, k' = k+1, pre' = pre ++ actual(2h)` の起点を構成し、その resumed 端点の OnlyScan/OnlyCredit/RadiusRep を返す。これで only=true の再 shift を帰納で回せる。
- 全 controller / 実 restart 全更新 / 無条件 PAL は未完。

## Resume checkpoint — 2026-09-14、今回の引き継ぎ

**最新：現在半径R+hを継続実行から導出**：OnlyOrigin.reshift_after_matchesを追加。shift入口OnlyScan(c+h,R+1−h)と同じ初期machine/left、OnlyMatchedRun n、cycleEndからn+1=2hを導き、実counterのRadiusRep(R+h)、OnlyCredit、再shift後PalAt(c+2h,R+1)を一括証明。現在scan半径を独立前提にしない。全体build9121 jobs成功/exit 0・標準公理のみ、ジョブ39463終了済み。次は実center表現/length counterと合わせ同じ再shift microsteps/終了OnlyScanを構成し、次OnlyOriginへ更新。全controller/無条件PAL未完。

**最新：実履歴から再shift後の回文性を導出**：OnlyOrigin.reshift_palindromeを追加。現在OnlyScan(c+h,R+h)、同じTrace/LeftMoves、cycleEnd/右可用/予測一致から最後consumeを実行し、joined_input_periodを実verifier終点まで供給。旧scanと短回文継承によりPalAt(c+2h,R+1)を証明。独立した新PalAt/右周期/短DP候補/終点位置は要求しない。全体build9121 jobs成功/exit 0・標準公理のみ、ジョブ42505終了済み。現在OnlyScanのc+h,R+hはまだ前提で、継続比較帰納からの座標/半径同期と再shift実行/新OnlyOriginの構成が残る。全controller/無条件PAL未完。

**最新：shift前後を通す実入力周期を導出**：OnlyOrigin.joined_input_periodを追加。joined_reads→successful_cycles→hasPeriod_take→reads_indexにより、旧center<jかつj+2h≤現在verifier位置の全範囲でencoded raw[j]=encoded raw[j+2h]。実Traceとbrokenfalseだけから導き、独立period前提なし。全体build9121 jobs成功/exit 0・標準公理のみ、ジョブ51466終了済み。次はreshift_compareの最後consume後Traceへ適用し、current verifierと外側rightの座標対応/現在PalAtを介してreshift_from_rightへ接続。再shift新起点/全controller/PALは未完。

**最新：shiftをまたぐ実read列を元ready予測へ接続**：OnlyOrigin.joined_readsを追加。同じorigin watchのpreと、shift後の成功Trace extraをverifier位置不変で連結し、Reads start(pre++extra)currentと元readyからの同列成功を導出。shiftでdistance counterが変わってもSamePrediction/broken保存から成功を逆向きに移す。全体build9121 jobs成功/exit 0、新補題公理propext/Quot.sound、ジョブ25852終了済み。次はjoined列のsuccessful_cycles＋reads_indexから旧watchと継続全体の右側周期性を導きreshift_from_rightへ接続。再shift新起点/全controller/PALは未完。

**最新：再shiftの短回文は旧centerから継承**：reshift_from_rightを追加。旧PalAt(c,R)、一周期後のPalAt(c+h,R+h)、h≤R、右側周期性/終端範囲からPalAt(c+2h,R+1)を証明。必要な短PalAt(c,h)は旧回文の制限から内部導出し、新DP Candidateを要求しない。全体build9121 jobs成功/exit 0・標準公理のみ、ジョブ53232終了済み。右側周期性はまだ前提で、実2h Traceから旧watch区間まで含めて供給する接続が残る。一周期後のscan座標/半径対応も履歴から組み立てる必要がある。全PAL未完。

**最新：再shift比較の終端実記号と一周期履歴を接続**：OnlyOrigin.reshift_compareの結論を強化。同じGoodから読んだaを取得し、Trace(extra++[a])と比較後LeftMovesを返し、cycleEndからその長さ=2hを導出。追加の成功列や長さ仮定は不要。全体build9121 jobs成功/exit 0・標準公理のみ、ジョブ39267終了済み。左右不一致なので旧centerのscanをradius+1へ延長したとは扱わない。次はこのちょうど2hの成功履歴と再shiftの新center/周期窓を接続して新PalAt/OnlyOriginを再構成。全PAL未完。

**最新：再shift終端比較の不一致/consume成功を同時導出**：OnlyOrigin.reshift_compareを追加。固定起点と同じOnlyScan/Trace/LeftMoves、cycleEnd、右可用、実右read=予測から、実左≠右・Good watch・合法1consume・broken=falseを一括導出。checkPair/予測token存在は内部供給。左右一致優先枝には入らないことを実headで確定。全体build9121 jobs成功/exit 0・標準公理のみ、ジョブ30848終了済み。mode/watch/phase4/replay=falseを含むcanShift dispatch、再shift後PalAt/周期window/起点更新は未完。全PAL未完。

**最新：再shiftのcredit収支を接続**：Scala beginChainShiftはchain.matched()→beginShift(cycle reset)→shiftの順。reshift_only_creditで旧OnlyCredit＋cycle正規形/cycleEndから、matched.margin.incの非負性を導出し、同じChainShiftRun(immediate w,reset cycle)終点へOnlyCreditを供給。比較前margin≥0というfresh専用前提は再shiftでは不要。全体build9121 jobs成功/exit 0・標準公理のみ、ジョブ86278終了済み。再shiftの新PalAt/周期window/OnlyOrigin更新・同じ実行の合法性/全controller/PALは未完。下記の「再shift収支未完」はこのcredit部分に限り更新済み。

**最新：終端dispatch→次tick到着/restart/時計を接続**：旧terminal_dispatch_restartをterminal_dispatch_next_tickへ置換。OnlyOrigin/同じ履歴から終端一致dispatchを通し、Option到着込みrestartInputTickにbind。拡張rawの半径+1 scan、Idle/回数/到着後可用性での時計/空program/growを一括証明。delay>1が必要。旧集約のheap/lower/work結論はこの新集約では省略（下位restart/startSearch定理に保持）。全体build9121 jobs成功/exit 0・標準公理のみ、ジョブ87529終了済み。全controller mode/全head/報告出力/成功watch到達性/他分岐/無条件PALは未完。

**最新：到着・実head可用性・restart・同tick時計を統合**：scanAvailable（Scala同様replaying || trailing設定でplace/head可用性を選択）、receiveRestart（Option入力）、restartInputTick/restart_input_tickを追加。到着有無の両方で拡張raw上scan、Idle、restarts+1、到着後rightから算出した時計、空program/growを証明。delay>1のbroken-chain scan枝の射影であり、全mode dispatch/報告output/walker等全head/heapの入力Ref対応は未完。全体build9121 jobs成功/exit 0・標準公理のみ、ジョブ43307終了済み。次は終端比較から次tickのこの関数へ接続し、後続検索準備・他分岐・全controllerへ進む。無条件PAL未完。

**最新：restart同tickのscan時計更新を接続**：Scala runはbackground→stepScanの順。restartScanTick/restart_scan_tickを追加し、restart後に既存MatchClock.runを同tickのavailabilityで1回進める。delay>1なら比較0回、利用可能なら時計delay−1、不可ならdelay、scan保存/Idle/growを証明。局所restartのclock=delayをtick終了値と誤認しないこと。全体build9121 jobs成功/exit 0・標準公理のみ、ジョブ58581終了済み。availabilityは現状Bool前提で、実replay/advanceTrailingGap/head可用性からの計算と到着込みtickへの統合は未完。restartScanTickはdelay>1でのみ比較を省略できる射影。全controller/他分岐/無条件PAL未完。

**最新：restart直前の入力到着を保存**：compareArrivalで射影中のcenter/left/right/verifierへ同じ到着aを追加。OnlyRestartReady.arrivalが拡張raw上のscanと全restart条件を保存。restartArrival/restart_after_arrivalで到着後もrestart成功、拡張入力上scan/Idle/clock/回数/program reset/heap保存を証明。全体build9121 jobs成功/exit 0・標準公理のみ、ジョブ96159終了済み。初回record構文/射影展開を修正済み。到着しないtick、broken時背景no-opとclock実順序、他head（walker等）を含む全controllerへのrefinementは未完。無条件PAL未完。

**最新：guard付き終端dispatch→restartを直接合成**：terminal_dispatch_restartを追加。OnlyOrigin＋同じ現在履歴/OnlyScan/Credit/RadiusRep、watch/only/cycleEnd/可用性/左右一致から、(dispatchOnlyMatch s).bind(restart entry delay)の成功とscan半径+1/Idle/回数/clock/空program/heap保存/grow等を一括証明。OnlyRestartReadyと距離下界は内部導出（origin watched.phase=4使用）。全体build9121 jobs成功/exit 0・標準公理のみ、ジョブ20124終了済み。これは二局所遷移の合成であり、Scalaの次tickまでの入力到着や背景・時計スケジュールを飛ばして証明したわけではない。そのinterleave・到達性・他分岐・全controller/無条件PALは未完。

**最新：caught only一致枝に実guard dispatchを追加**：RestartStateへperiodOnlyを追加、dispatchOnlyMatchでwatch/only/lagzero/canRight/cyclepositive/checkPair/左右一致を検査。dispatch_only_matchはOnlyOrigin＋同じOnlyScan/Trace/LeftMovesからlag/cycle/checkPairを内部供給し、有効更新matchedRestartStateを返す。mode watch/only true/可用性/左右一致は実枝の前提。Noneはこの枝の非適用であり言語拒否ではない。canRightのDecidableを定義展開で供給し計算可能性を維持。全体build9121 jobs成功/exit 0・標準公理のみ、ジョブ12807終了済み。初回Decidable不足とsimpによる左右書換え不一致は修正済み。全背景tick/再shift/fallback/到達性/無条件PALは未完。

**最新：比較失敗flag→chain Broken→restartを局所接続**：Scala consumeの不一致時mode=Brokenとmatchedの順序を再確認。matchedRestartState（有効なcaught only一致枝の射影）とrestart_after_matchを追加。onlyCompareNextのbrokenからchainModeを計算し、OnlyRestartReadyだけでrestart成功/scan保存/Idle/時計/回数/検索resetへ接続。独立chainMode=broken前提はこの合成では不要。全体build9121 jobs成功/exit 0・標準公理のみ、ジョブ3624終了済み。matchedRestartStateは有効枝の更新関数で、旧mode/only/lag/左右一致のdispatchを自身では検査しない。その合法性は既存比較定理から供給する必要がある。背景tickの入力到着/時計順序、全controller/他分岐/無条件PALは未完。

**最新：局所restart遷移を統合**：InputSupplyにChainMode/RestartState（対象フィールドの射影）/restart/restart_readyを追加。chainMode=brokenとOnlyRestartReadyから全guardを通過し、同じscan保存、検索start、chain Idle、restarts+1、clock=delay、program空テープ対応/heap保存/lower=last/grow/work=lowerを一括証明。全体build9121 jobs成功/exit 0・標準公理のみ、ジョブ93194終了済み。初回record更新構文とsimp残ゴールは修正済み。これはScala backgroundのrestart対象フィールドのdecoded射影であり、全controller refinementではない。OnlyCompareState.watch.control.brokenと新chainModeの対応、実背景tickへの組込み、次の検索実行、他分岐・到達性・物理refinement/無条件PALは未完。

**最新：終端last Canonicalの独立前提を除去**：history_terminal_canonicalで同じready Watch.Run→ChainShiftRun→Trace→最後consume（失敗含む）のlast正規形を導出。only_compare_restart/only_matched_restart/OnlyRestartReadyの結論にlast Canonicalを追加し、OnlyRestartReady.start_searchのhc引数を削除。scan_prediction_shift経由の生成契約にもそのまま伝播。全体build9121 jobs成功/exit 0、新補題公理propext/Quot.sound、ジョブ94523終了済み。これで前回発見したlower非負の正規形不足は同じ履歴で解消。次は検索startと外側chain Idle/restarts++/clock更新の統合。成功watch/準備の全controller到達性、他分岐、物理refinement/無条件PALは未完。

**最新：OnlyRestartReady→検索startを接続、lower guardの不足を明示**：OnlyRestartReady.start_searchを追加。同じ終端last/radiusをstartSearchへ渡し、lower/radius非負とcenter.read存在、program reset/heap保存/lower/work/grow/debt等を一括証明。last.positiveだけではnegative=falseを言えないため、lastのCanonicalを追加前提として要求。これは残る履歴接続であり、隠してはいけない。全体build9121 jobs成功/exit 0・標準公理のみ、ジョブ5799終了済み。次はchain_shift_control_canonical＋Restart.run_canonical/consume_canonicalから終端last Canonicalを同じ履歴で導出しOnlyRestartReadyへ含める。外側chain Idle/clock/restarts更新、全controller/PALは未完。

**最新：検索startのprogram/lower/schedulerを統合**：SearchFinishにSearchState(n,slots)（raw program、lower counter、既存scheduler）、startSearch(entry,lower,radius)、startSearch_positiveを追加。RawTick.resetとbeginを同時実行し、正lowerなら空テープ/PC開始/done=trueへの対応、heap保存、lower=work、grow/spanreset/debt=-radius/finalfalse/quarter0を一括証明。全体build9121 jobs成功/exit 0、同定理公理propext/Quot.sound、ジョブ30279終了済み。Counterはdecoded値でphysical alias encodingまでは未証明。次はOnlyRestartReadyからこの更新を適用して外側chain Idle/restarts++/clock resetへ接続。SearchStateは検索startの射影で、既存全controllerとのrefinementはまだない。全PAL未完。

**最新：Scala program.resetの共有heap側操作を追加**：ScaffoldProgram.scala:103のresetを確認し、GalilScaffoldRawTickにreset entry x（heap保存、全private tape roots none/focus6、pc=entry、done=true）、reset_represents、reset_heapを追加。任意旧状態からlist-levelの空private tapes/開始PC/停止状態への対応を証明。全体build9121 jobs成功/exit 0、reset_representsの公理propext/Quot.sound、ジョブ54923終了済み。これはdecoded raw heap機械上のresetで、実circuit field書込みへのrefinementではない。次はSearchFinish.beginとlower aliasを同じ検索restart状態にまとめ、OnlyRestartReadyを入口条件としてchain Idle/clock=matchDelay更新へ接続。Scalaのbackground restartはchain Brokenかつmargin≥0,last>0,lag=0でsearch.start(last)→chain Idle→restarts++→clock reset。全controller/PALは未完。

**最新：準備creditの実更新列から入口収支を供給**：scan_prediction_shiftの入口CanonicalState/balance=4hを直接引数から削除。prepRadiusの正規形、start/done/copy/backのmatched列、copy列長=h、s.lag/s.marginが同じCredits.run(start prepRadius)(prepEvents ...)の終点である等式を受け、run_canonical/prepared_balanceから内部導出するよう更新。全体build9121 jobs成功/exit 0・標準公理のみ、ジョブ5456終了済み。等式と準備イベントの実controller対応は依然外側で供給が必要。成功Watch.Run/DP窓/radius対応・実restart/再shift/fallback/全controller/PALは未完。

**最新：比較時margin条件を準備収支から導出**：scan_prediction_shiftのt.margin Canonical/非負の直接引数を、入口sのCanonicalStateとbalance s=4hへ置換。同じRunのrun_canonicalとcaught_margin、およびphaseから導いたdistance下界/lagzeroで比較時margin条件を内部供給。既存prepared_balanceと接続できる署名。全体build9121 jobs成功/exit 0・標準公理のみ、ジョブ83582終了済み。準備の実終点がsであることの同一性とbalance供給はまだ外側で必要（準備全体到達性を証明したわけではない）。成功watch/実restart/再shift/fallback/全controller/無条件PALは未完。

**最新：半径下界も比較前phase guardから内部導出**：scan_prediction_shiftのhsize（2h≤radius）を削除し、比較前t.phase=4へ置換。同じwatch_phase_distanceとwatch_progress、初期lag/比較回数/終了lagzeroからdistance=radiusを使ってhsizeを内部導出。返り値のrestart継続契約から追加phase guardも削除し、同じ最後の予測tickの進行収支から必要距離を供給。全体build9121 jobs成功/exit 0・標準公理のみ、ジョブ33603終了済み。成功watch/DP窓/初期lagとradius対応/counter正規形/fresh marginなどは依然入口前提。実restart/再shift/fallback/全controller/無条件PALは未完。

**最新：phase4逆方向を証明し距離仮定を置換**：Predictionにconsume_phase_mono/run_phase_mono/before_four_phase/watch_phase_distanceを追加。readyからの同じ成功Watch.Runでphase=4→distance≥4h。4h−1長の成功予測prefixのphase=3、成功列のprefix一意性、phase単調性による矛盾。scan_prediction_shiftのrestart継続契約は独立distance≥4hからimmediate t.phase=4へ変更し、同じhextから下界を内部導出。全体build9121 jobs成功/exit 0・標準公理のみ（最終ジョブ80324終了）。初回失敗はconsume場合分け/bounce展開/appendの正規化を修正済み。下記の「phase4逆方向未完」は旧履歴。成功watchの到達性や半径hsize等の全controller供給、実restart/再shift/fallback/物理refinement/無条件PALは未完。

**最新：予測比較の返り値へrestart接続を統合**：`OnlyRestartReady`（scanとbroken/margin/last/lag/center/radius/Search.begin.work条件、実reset遷移ではない）を定義。scan_prediction_shiftの結論をさらに強化し、生成した同じendpoint/watchEnd/cycleEndからの任意OnlyMatchedRun nと終端一致について、OnlyRestartReadyを返す継続契約を追加。OnlyOriginは内部生成、only_matched_restartへ空履歴/生成入口を直接供給。distance≥4h、終端cycleEnd/canRight/一致は継続契約の条件。全体build9121 jobs成功/exit 0・標準公理のみ、ジョブ52740終了済み。予測→shift→一致区間→終端restart入口は一つの条件付き定理に接続済み。未完：実guardからdistance下界、成功watch等の入口到達性、再shift/fallback、reset/idle/clockを含む実restart、全controller/物理refinement/無条件PAL。

**最新：同じ予測shiftからOnlyOriginも構成**：scan_prediction_shiftに実左右不一致hmismatchを追加（Scala shift枝の条件）。結論へOnlyOriginの存在とstart=s/watched=immediate t/shifted=watchEnd/shiftEnd=endpoint/resumeLeft=endpoint.left/interior=xs/steps=xs.length+1/finish=cycleEndを追加。最後の予測tickを含む同じWatch.Run、同じChainShiftRun、実終了scanとcenter位置から構成し、OnlyOriginを別途仮定しなくてよくなった。全体build9121 jobs成功/exit 0・標準公理のみ、ジョブ88644終了済み。次はこの返り値をonly_matched_restartへ直接接続。distance≥4hのguard導出、成功watch/DP窓/counter/margin前提の全controller供給、実restart/再shift/fallback/無条件PALは未完。

**最新：予測比較→shift→比較入口まで既存定理を強化**：`scan_prediction_shift`の署名を更新。radius/length counterのCanonical、比較前t.marginのCanonical/非負を追加し、既存PalAt/同じShiftRun/ChainShiftRun/終了counter/OnlyScanに加えOnlyCredit/RadiusRep/空Trace/LeftMoves/center.read存在を返す。追加tickのmargin.incからfresh収支条件を内部供給し、shift_only_entryへ接続。全体build9121 jobs成功/exit 0・標準公理のみ、ジョブ96400終了済み。OnlyOrigin構築と同じshift起点でのonly_matched_restart合成はまだ必要。成功Watch.Run/DP窓/半径下界/counter正規形/margin条件の全controllerからの供給、実restart/再shift/fallback/無条件PALも未完。

**最新：終了scan前提をshift生成から供給**：`shift_to_only_initialized`を追加。旧scan/shift後PalAt/caught watch/初期counter正規形/fresh margin非負から、shift_to_onlyで同じShiftRun/ChainShiftRun/終了scanを生成し、shift_only_entryへ渡す。終点のOnlyScan/Credit/RadiusRep/空Trace/0歩LeftMoves/center.read存在を一括返す。終了scan自体は新定理の引数にない。全体build9121 jobs成功/exit 0・標準公理のみ、ジョブ19239終了済み。shift後PalAt、caught watch、初期counter/margin条件は未除去。次はscan_prediction_shift由来のPalAt/終端watchとOnlyOriginを同じ起点にそろえて、only_matched_restartまで合成。実restart/再shift/fallback/全controller/無条件PALは未完。

**最新：shift終点から比較入口を一括構成**：`shift_only_entry`を追加。同じShiftRun/ChainShiftRun(reset cycle)から、実終点のOnlyCompareStateにOnlyScan、OnlyCredit、RadiusRep、空Trace、0歩LeftMoves、center.read存在を一括供給。shift初期counter正規形/値/減算範囲、fresh margin非負、終了scanとcaught watch条件は依然要求する。全体build9121 jobs成功/exit 0・標準公理のみ、ジョブ23907終了済み。次はshift_to_only等の生成した終了scanをこの入口へ渡し、OnlyOriginとonly_matched_restartを同じ起点で接続。起点到達性/実restart/再shift/fallback/全PAL未完。

**最新：終端checkPairも内部導出**：`only_matched_restart`を追加。OnlyOriginとOnlyMatchedRunから継続比較をcheckedへliftし、同じ終点履歴で終端checkPairも導出、only_compare_restartへ合成。定理の引数に独立checkPairはない。shift回数=interior.length+1、distance≥4h、入口OnlyScan/Credit/RadiusRep/Trace/LeftMoves/center.read存在、終端cycleEnd・canRight・左右一致は要求する。全体build9121 jobs成功/exit 0・標準公理のみ、ジョブ35698終了済み。次はOnlyOrigin/入口状態の構成と実restart更新、または残る再shift/fallback枝。全PAL未完。下記の「次は終端checkPair」は完了した履歴。

**最新：各比較のcheckPair仮定を除去**：InputSupplyに固定入口`OnlyOrigin`（同じ成功watch/shift、旧scan不一致、表現/位置/半径下界/再開scan）と`OnlyOrigin.check_pair`、`OnlyMatchedRun`、`only_matched_checked`を追加。OnlyMatchedRunにはcanRight/cycleEnd=false/左右一致だけを要求し、checkPairは要求しない。固定起点からTrace/LeftMoves/OnlyScan等を帰納更新して各stepのcheckPairを導出し、既存OnlyCompareRunへliftする。全体build9121 jobs成功/exit 0、標準公理のみ、ジョブ10297終了済み。次は同じ起点で終端checkPairも内部導出してonly_compare_restartへ合成。OnlyOriginの到達性・成功Watch.Run・距離guard・入力到着・再shift/fallback・実restart更新・全controller/PALは未完。OnlyOriginは既存の入口前提をまとめたもので、入口前提自体を証明したわけではない。

**最新：比較区間→終端restart入口**：`only_compare_restart`を追加。同じready Watch.Run/ChainShiftRunと入口Traceから、OnlyCompareRunの任意n回＋終端一致後のscan、broken、margin非負、last正、lagzero、center.read存在、実radiusのRadiusRep/非負、SearchFinish.begin.work=lastを一括導出。center.readは区間入口で仮定し、区間不変から終点へ運ぶ。全体build9121 jobs成功/exit 0・標準公理のみ、ジョブ8097終了済み。実restartのprogram.reset/idle/clock更新そのものは未モデル化。各比較guard、ready成功watch、distance≥4hなどの起点条件も依然前提。次は固定入口からcheckPairを供給するか実restart全更新へ接続する。無条件PAL未完。

**さらに最新（比較区間の帰納）**：InputSupplyに`OnlyCompareState`/`onlyCompareNext`/`OnlyCompareRun`/`only_compare_history`を追加。非終端only一致比較の任意n回について、center不変、同じbaseからの実Trace、LeftMoves、OnlyScan(radius+n)、OnlyCredit、実counterのRadiusRepを一括保存。入口履歴extraから終点履歴長extra.length+nも導出。全体build9121 jobs成功/exit 0、標準公理のみ、ジョブ59012終了済み。これはdecoded比較区間の帰納であり、OnlyCompareRunの各stepにcanRight/cycleEnd=false/checkPair同値/左右一致を要求する。固定shift起点の`only_history_check_pair`からstep guardを供給する接続、到着イベント、終端dispatch/実restart、全controllerは未完。次はこの区間関係を既存の起点条件と終端分岐につなぎ、guardを独立前提のまま残さないこと。

**引き継ぎ後の再開追記（この段落を優先）**：`GalilScaffoldChainInputSupply.only_terminal_radius`を追加。終端一致で同じscan半径+1、broken、margin非負に加え、実counter.incのRadiusRepとnegative=falseを合成した。全体`lake build`9121 jobs成功・exit 0、同定理の公理はpropext/Classical.choice/Quot.sound。ジョブ84268は終了済み。下の「今回は文書だけ」「終端radius接続が次」は保存時点の履歴となった。次はcenter不変と実restart更新、固定入口の比較区間帰納。全PAL未完。

この節が下記の多数の「最新」「次」より優先。今回は引き継ぎ文書のみ更新し、証明コードは変更していない。

- **達成済みの境界**：Scala準拠のdecodedな局所実行について、予測一致→shift→OnlyScan入口、継続一致のTrace/LeftMoves/OnlyScan/OnlyCredit保存、終端一致でscanが伸びchainがbrokenになる条件を接続。最後の実装は実radius counterを表す`RadiusRep`と、`only_history_matched`のcounter.inc保存。
- **未達の境界**：固定した入口から全比較区間を回す帰納、実restart全更新、全オンラインcontroller、物理実装へのrefinement、出力/締切、無条件PAL定理。`Main.pal_in_peg_of_structured`は依然として具体機械の正しさを要求する条件付き定理。
- **検証記録**：直前作業の全体`lake build`は9121 jobs成功・exit 0、追加定理の公理監査は標準公理のみ。今回そのbuildは再実行していない。今回の`git diff --check`成功、プロセス確認で実行中のLean/buildなし。

### 再開直後の具体的な作業

1. `lean-pal/PalPeg/GalilScaffoldChainInputSupply.lean`の`only_scan_terminal_match`（約2194行）、`only_terminal_restart_conditions`（約2228行）、`RadiusRep`〜`only_history_matched`（約2263–2328行）を読む。
2. 終端一致にも同じ実radiusCounterのincと`RadiusRep(radius+1)`を接続し、`radius_rep_nonnegative`からSearch.startのradius guardを得る。`RadiusRep`は現在終端定理より後ろにあるので、定義を前へ移すか後ろに合成定理を置く。
3. 比較区間でcenter不変・read存在を保持する。shift直後のcenter条件は`shift_run_center`/`shift_search_guards`から取得できるが、その後の実状態への保存は別途必要。
4. 固定入口から`only_history_check_pair`と`only_history_matched`を帰納で回し、最後の一致/repeated shift/fallbackを同じcontroller実行へ接続する。独立した成功履歴やguardを新たな仮定として置くだけでは完了扱いにしない。

### 残る重要な前提・落とし穴

- fresh watchの成功Run、初期lag/radius/DP窓と実centerの対応を全controllerから供給する必要がある。
- `distance ≥ 4h → phase4`はあるが、実guardから必要な下界を得る逆方向は未接続。
- fresh非負marginからの`OnlyCredit`初期化はある。only=trueで再shiftする場合の一般化は未完。
- `SearchFinish.begin`はスケジューラ射影のみ。program.reset、lower alias、chain idle、clock resetを含む完全なSearch.startではない。
- Scalaは左右一致を先に判定する。cycleEndで左≠予測でも左右一致ならscanは伸び、chainだけbrokenになって次tick restartへ進む。
- encoded位置0のgapと、物理headのfocusなし/readなしを混同しない。sentinelには`signedRead`を使う。
- replayはradiusを0へ戻すので、全状態でradius正と仮定しない。時計のLean側delay2048とScalaの時間校正も全体接続が残る。

### 参照と検証の最短経路

- 主作業：`GalilScaffoldChainInputSupply.lean`。補助：`GalilScaffoldChainPrediction.lean`、`GalilScaffoldCounter.lean`、`GalilScaffoldSearchFinish.lean`。
- 仕様の根拠：`scala/pal/src/main/scala/pal/ScaffoldGalil.scala`と`ScaffoldChain.scala`（対応Circuit版も参照）。
- `cd /home/mizushima/repo/lean4-peg/lean-pal`で`lake build`。Leanジョブは同時に1本。依存更新に`lake env lean`だけを使ってもoleanは更新されない。
- repo直下で`git diff --check`。多数のuntracked Leanファイルと既存削除を含むため、worktree全体をそのまま引き継ぐ。commit済みファイルだけでは再開できない。
- サブエージェント不使用。部品数で進捗を表さず、実際に除去した仮定・接続した実行区間を報告する。

## 従来の基本方針

- **最終目標は無条件の `PAL ∈ PEG`。まだ未完成。** DP単体や局所接続の完成を大定理の完成と報告しない。
- repo: `/home/mizushima/repo/lean4-peg`。Lean作業ディレクトリ: `lean-pal/`。
- 現在の構成の根拠は **Scalaの実装**。新しい別算法や旧4スロット方式を勝手に主経路にしない。
- ユーザーはサブエージェント禁止、速度と実質的な接続を重視。既存部品の置換・整理は許可されているが、無関係な作業を壊さない。
- 非常に大きいdirty worktreeで、多数の重要ファイルがuntracked。`git reset --hard`、`git clean`、一括checkoutをしない。今回commitはしていない。
- ローカルの現物が正。古い`PROGRESS.md`や`docs/palindromes-in-peg/HANDOFF.md`本文は歴史資料。現状は本書と`lean-pal/ASSEMBLY_PLAN.md`冒頭を優先する。
- 記憶ツールはユーザーが削除済み。再導入や探索は不要。

## 現在地の要約（今回の保存時にソース照合済み・ここを優先）

**最新：実radius counterを一致履歴へ接続。** InputSupplyに `RadiusRep`（counter Canonical/value=自然数半径）、`radius_rep_inc`、`radius_rep_nonnegative`、`shift_radius_rep` を追加。shift_radius_repは同じShiftRunと初期正規形/値/減算範囲から終了RadiusRepを構成。`only_history_matched`へ実radiusCounter/RadiusRepを引数追加し、同じ比較でincしたcounterのRadiusRep(radius+1)も履歴/OnlyScan/OnlyCreditと一緒に返すよう更新。全体build9121 jobs成功/exit 0、標準公理のみ、最終ジョブ終了済み。

次は最後の比較（chainがbrokenになるがscanは伸びる枝）にもradius.incを同じ形で付け、実Search.startへ半径非負を供給する。centerは継続比較で不変であることを外側状態に保持する必要がある。現モデルはradius counterの対応を持つが、全controllerのmode/時計/初期化を証明してはいない。全PALは未完。

**最新：同じshift終点のcenter/半径入口条件。** InputSupplyに `shift_run_center`（入口center表現/focusから終了centerのRepresents/focus/position開始+n）、`shift_search_guards` を追加。後者は同じShiftRun、初期ShiftCanonical、n≤初期radius値から、終了center.read≠noneと終了radius.negative=falseを同時に導出。全体build9121 jobs成功/exit 0、標準公理のみ、最終ジョブ終了済み。初回の帰納ケースで外側tを参照したchange不一致はshiftTick限定展開で修正。

これはshift直後の条件。restart時はその後の一致比較でradiusを増やし、centerは不変なので、同じ実counterをその区間も追跡する接続が残る。現OnlyScanは自然数radiusを持つが外側の実radius counterをフィールドに保持していない。program reset/lower alias/idle/clock、全比較帰納/全PALも未完。

**最新：Search.startの検索状態更新と終端lastを接続。** `GalilScaffoldSearchFinish.lean` に `begin lower radius` と `begin_positive` を追加。既存State上でmode=grow/finalStage=false/span=reset/work=(lower zeroならinc、それ以外lower)/debt=initialDebt radius/quarter=0。positive lowerならwork=lower等を証明。`only_terminal_restart_conditions` の結論を拡張し、同じ終端lastをbeginへ渡したworkがそのlastに等しいことも返す。全体build9121 jobs成功/exit 0、標準公理のみ、最終ジョブ終了済み。初回のpositiveからzero=falseのsimp残ゴールはBool場合分けで修正。

Scala確認：Search.startはlower非負だけでなくradius非負・center.read存在を要求。**beginは検索スケジューラ状態の射影であり、program.reset、lower別名参照、chain.mode=Idle、clock reset、上記入口guardの全実行をまだ表していない。** 新たに全restartが閉じたとは扱わない。次は現center/半径counterの到達不変条件とprogram/control側resetを合わせるか、未接続の全比較帰納を進める。全PALは未完。

**最新：only最終一致のrestart条件を同じ終端へ一括合成。** InputSupplyに `history_terminal_last`（同じwatch/shift/Traceの現在machineが実readをconsumeした後のlast正値。read noneも対応）と `only_terminal_restart_conditions` を追加。後者は同じOnlyScan/OnlyCredit/cycleEnd/checkPair/実左右一致から、**終了ScanInvariant、broken=true、margin.negative=false、last.positive=true、lag.zero=true** を同じimmediate currentについて同時に返す。全体build9121 jobs成功/exit 0、標準公理のみ、最終ジョブ終了済み。

これはfresh ready開始watchのdistance≥4hとh回shift、同じ成功継続Traceを前提にしたrestart直前条件。**Search.start(last)、chain idle化、clock resetという実restart操作自体には未接続。** 入口guard・only再shiftの一般化・比較履歴全体の到達帰納、全controller/全PALは未完。次はScalaの実restart更新にこれら条件とscan保存を渡すか、phase4からdistance下界を導いて入口前提を減らす。

**最新：margin収支を履歴延長と終端へ合成。** `only_history_matched` にOnlyCredit前提を追加し、同じ実読出しaによるTrace/LeftMoves/OnlyScanの延長に加え、更新後OnlyCreditも返すよう変更。`only_scan_terminal_match`にもOnlyCreditを受け、従来のscan成功/broken/lagzero/cyclezero/margin+1に加えて、同じimmediate状態のmargin.negative=falseを返すよう更新（両署名変更）。全体build9121 jobs成功/exit 0、標準公理のみ、最終ジョブ終了済み。

残るrestart条件は、watch_shift_last_positiveを同じ終端consumeへ合成するlast正値と、実restart呼出し・Search状態更新。OnlyCredit入口はshift_only_creditがfresh非負marginから供給するが、全呼出しのguard由来やonly再shift収支は未完。全PALは未完。

**最新：only区間のmargin＋cycle収支。** InputSupplyに `OnlyCredit`（margin Canonicalかつvalue margin+value cycle≥0）、`chain_shift_margin_canonical`、`shift_only_credit`、`only_credit_step`、`only_credit_terminal` を追加。reset cycleからの同じn回shiftで、入口margin≥0/Canonicalなら終了OnlyCreditを構成。以後immediate（失敗含む）とcycle.decの同時更新で保存。cycleEnd=true/Canonicalから最後のimmediate.margin.negative=falseを導出。全体build9121 jobs成功/exit 0、標準公理のみ、最終ジョブ終了済み。固定reset添字への直接帰納とvalueの過剰展開のエラーは一般化補題/限定rewriteで修正済み。

**未合成：** OnlyCreditを現在のonly_history_matchedの履歴と同時に保持し、only_scan_terminal_matchの結果へ組み合わせること。last正値はwatch_shift_last_positiveから同じ終端へ渡す。入口margin非負はfresh guard向けで、only再shiftには別収支が必要。実restart/全controller/全PALは未完。

**最新：同じ成功watch→shift後last正値。** InputSupplyに `watch_last_lower` と `watch_shift_last_positive` を追加。ready開始成功Watch.Runのdistance≥4hから、実成功語の二往復prefixを取り出しlast≥3hを導出。後者は同じwatch終点からh回のChainShiftRunを経た後、任意の追加consume語（失敗含む）のlast.positive=trueを返す。Ordered/Canonical/last>hを独立前提にせず同じTraceから内部供給。全体build9121 jobs成功/exit 0、標準公理のみ、最終ジョブ終了済み。

**残る条件：** distance≥4hとready開始成功Watch.Runは前提。実phase4 guardから距離下界を導く逆方向、only再shift時の履歴一般化は未完。margin非負の累積収支と最終失敗の同じ実状態への接続、restart/全PALも未完。

**最新：shift後から失敗consumeまでlast正値を保存。** InputSupplyに `chain_shift_order`、`chain_shift_control_canonical`、`chain_shift_future_last` を追加。同じChainShiftRunがlast/boundary/distanceを同じ回数減らすのでOrderedと各Canonicalを保存。入口last値>shift回数なら、任意の追加consume語（最後の失敗も含む）後のlast.positive=trueを既存Restart.run_order/run_canonicalから導出。全体build9121 jobs成功/exit 0、標準公理のみ、最終ジョブ終了済み。

**入口のlast>hはまだ前提。** fresh phase4時のlast下界、または同じ二往復prefixから供給する必要がある。再shiftでのonly周期収支も別途必要。margin非負の累積収支、最終失敗との同一履歴合成、restart実行・全PALは未完。

**最新：cycleEnd一致枝の同時更新。** InputSupplyに `only_scan_terminal_match` を追加。OnlyScan、cycleEnd=true、checkPair同値、実左右一致から、radius+1のScanInvariant、watch.immediate後broken=true/lagzero、cycle.dec後zero=true、margin値+1を同時に導出。左≠予測とcycle値1は内部供給。全体build9121 jobs成功/exit 0、標準公理のみ、最終ジョブ終了済み。

この枝は成功OnlyScanへ戻さず、scan成功/chain失敗として扱う。**まだrestartに必要なmargin≥0とlast>0を供給していない。** 継続中のmargin増加総数とshift前後のlast/境界更新を同じ履歴へつなぐ必要がある。次tickの実restart、最後の予測一致shift/不一致fallback、全PALは未完。

**最新：最後の比較で外側一致・chain失敗の枝。** Scala ScaffoldGalilの257–304行を再確認：左右一致を最優先しmatchedPlace→chain.matched、そうでなければ予測一致＋canShiftでshift、残りfallback。cycleEndでcheckPairが左≠予測を保証していても、左右が一致する枝はあり得る。この場合、回文は伸びるがchain consumeは失敗する。

InputSupplyに `caught_scan_terminal_match` を追加。CaughtScan、外側right合法、実比較左≠予測、実左右一致から、終了ScanInvariant(radius+1)、合法verifier1-step、終了broken=trueを同時に証明。verifier右readと外側右readの一致は同位置/同入力から内部導出し、予測tokenがnoneでも対応。全体build9121 jobs成功/exit 0、標準公理のみ、最終ジョブ終了済み。

**次：** only_history_check_pairとcycleEnd=trueからこの左≠予測を供給し、同時margin.inc/cycle.dec/lag保存と次tickのrestart条件（margin≥0,last>0,lagzero）をつなぐ。最後の比較すべてをshift/fallback扱いにしない。継続全体の帰納・実mode/時計・全PALは未完。

**最新：checkPair/cycle実判定から履歴延長。** `only_history_matched` の署名を変更。独立したhprediction/hremainを削除し、`singlePositive cycle=false` と `only_history_check_pair` が返す比較同値を受ける形へ更新。予測一致はその同値から、extra.length+1<periodはOnlyScanのcycle収支・dispatch同値から内部導出して既存の履歴同時延長へ渡す。全体build9121 jobs成功/exit 0、標準公理のみ、最終ジョブ終了済み。

checkPair同値自体は引数で、直前定理から同じ状態に供給する設計。次はこの二つを旧watch/shiftを固定した継続履歴の帰納へ一括合成し、最後cycleEnd=trueのdispatch・不一致fallbackを扱う。実only/mode/時計と全PALは未完。

**最新：同じ履歴からcheckPairのcycle条件を導出。** InputSupplyに `only_history_check_pair` を追加。同じ成功watch/shift/旧scan不一致/再開scan、現在OnlyScan、v.machine→現在machineのTrace(extra)、再開left→現在leftのLeftMovesから、**cycle.positive=true ∧（次の実左read=現在実token ↔ cycle.singlePositive=false）** を導出。成功extraはTrace.controlと現在unbrokenから、比較済み左移動は既存履歴＋次の合法左一歩から内部供給。cycleEndとの対応はonly_scan_dispatchを使用。全体build9121 jobs成功/exit 0、標準公理のみ、最終ジョブ終了済み。

これで前段の「hprediction/hremainを同じ履歴から供給」が可能になったが、全controllerのassert安全性は未完成。次はcycleEnd=falseの実一致比較でonly_history_matchedへ渡し、最後cycleEnd=trueのdispatchと不一致fallbackを同じ実行へ接続する。現在の入口/再開scan/only flag/時計の実到達性、全PALは未完。

**最新：only一致比較の履歴を同時延長。** InputSupplyに `left_moves_append` と `only_history_matched` を追加。OnlyScan(used=extra.length)、同じbase→現在machineのTrace(extra)、初期左head→現在左headのLeftMoves(extra.length)から、一致比較の実読出しaを取得し、Trace(extra++[a])・LeftMoves(extra.length+1)・更新後OnlyScanを同じ一歩で返す。aはGoodから得た実verifier読出しで、任意の予測文字を入力に捏造しない。全体build9121 jobs成功/exit 0、標準公理のみ、最終ジョブ終了済み。

残るのはhpredictionとhremainをshifted_check_pair/only_scan_dispatchから同じ履歴に対して供給すること。Trace.control/OnlyScan.unbrokenから成功extra前提を導け、LeftMovesへ次の左一歩を追加してcheckPairへ渡せる。入口は空Trace/LeftMovesとscan_prediction_shiftのOnlyScan。実accepted/fallbackの分岐、mode/時計/全PALは未完。

**最新：最後の予測比較→shift→OnlyScanを主定理へ合成。** `scan_prediction_shift` の署名を更新。比較後のradiusCounter/lengthCounterとradiusCounter値=旧R+1を引数に追加。結論は新PalAtに加え、同じ終点のShiftRun・ChainShiftRun（開始watchは **immediate t**、cycleはreset）・remaining.zero・終了radius/length値・OnlyScan(period=2h,used=0)。従来の独立Reads列を返す結論から置き換えた（Readsが必要ならshift_scan_resumeを使う）。repo内の他の参照はなく、全体build9121 jobs成功/exit 0、標準公理のみ、最終ジョブ終了済み。

最後の予測tickを追加した同じWatch.RunのTraceからverifierのRepresents/focus/brokenfalseを取得し、caught_positionと外側right位置から同位置を内部導出。新PalAtもwatch_shift_palindromeから内部供給。そのままshift_to_onlyへ接続したため、OnlyScan入口のこれらを独立前提として渡す必要はなくなった。

**残る主前提：** ready開始の成功Watch.Run/同じDP窓と候補/旧ScanInvariant/初期lagと半径収支/2h≤R/終了lagzero/最後の予測一致。実centerとして開始verifierを使う配置対応、実guardからこれらの生成、only継続履歴の帰納・最後dispatch・時計/物理回路・全PALは未完。次はOnlyScanの比較履歴を保持し、shifted_check_pair→only_scan_matchedを同じ実行で帰納する。

**最新：合法shift構成→OnlyScanを一括化。** InputSupplyに `shift_to_only` を追加。旧ScanInvariant、新PalAt、h>0/h≤R、外側right合法、比較後radius counter=R+1、catch済みwatch条件から、同じ終点t/v/finishに対するShiftRun・ChainShiftRun・remaining.zero・終了radius値R+1−h/length−2h・OnlyScan(period=2h,used=0)を一括構成。終了ScanInvariantやcycle値を外から仮定し直さず、shift_scan_counters→shift_run_chain→shift_only_scanで内部供給。全体build9121 jobs成功/exit 0、標準公理のみ、最終ジョブ終了済み。

残る入口前提は新PalAtとcatch済みwatchの右位置/lagzero/brokenfalse等。これらはscan_prediction_shift/最後の予測tickの既存結論から同一状態で合成する必要がある。さらにaccepted比較履歴の帰納、cycle最後dispatch、実mode/時計/全controller/全PALは未完。

**最新：同じshift終点→OnlyScan入口。** InputSupplyに `shift_only_scan` を追加。beginShiftでresetされたcycleから同じChainShiftRunをn>0回進めた終点t/v/finishについて、t.center/t.leftそのものの終了ScanInvariant、入口verifier表現/右位置/lagzero/brokenfalseから、**OnlyScan(period=2n, used=0)** を構成。cycleの値/Canonicalとshift後verifier条件は既存の同じRunから内部供給。全体build9121 jobs成功/exit 0、標準公理のみ、最終ジョブ終了済み。

終了ScanInvariantはまだ前提だが、任意の別leftではなく同じshift終点t.leftへ固定した。次はshift_scan_countersが返す同じtのScanInvariantとshift_run_chainをこの入口へ一括合成し、accepted比較列の履歴（extra/LeftMoves）を保持してcheckPair→only_scan_matchedの帰納へ進む。mode flag/時計/最後dispatch/全PALは未完。

**最新：一致比較とcycle減算の同じ一歩。** InputSupplyに `OnlyScan`（CaughtScan＋cycle Canonical/value=period−used/used<period）、`only_scan_dispatch`、`only_scan_matched` を追加。dispatchはpositive=trueとsinglePositive=true↔used+1=periodを導出。matchedはused+1<periodの一致比較で、scan半径+1/左右移動/verifier immediateとcycle.dec/used+1を同時に保存する。最後の残り1比較は別dispatch枝で、保存定理の範囲外。全体build9121 jobs成功/exit 0、標準公理のみ、最終ジョブ終了済み。

これはonlyモード区間のdecoded不変条件で、mode flagや時計/イベント選択そのものは未モデル化。**次：** resetからの同じshift後CaughtScan/cycle=2hをOnlyScan used=0へ接続、shifted_check_pairと同じprefix履歴を保持したaccepted比較列の帰納、最後のdispatch/不一致fallback。hpredictionとhremainはonly_scan_matchedで依然前提。全PALは未完。

**最新：scanとcaught verifierの一致比較不変条件。** InputSupplyに `CaughtScan`（ScanInvariant、同じ入力verifier表現/focus、右headとの同位置、lagzero、brokenfalse）、`caught_scan_matched`、`shift_caught_scan` を追加。前者は左read=予測と実一致比較からGoodを内部導出し、radius+1/left.left/right.right/watch.immediateの同じ更新後にCaughtScanを保存。後者は同じChainShiftRunのverifier/lag/broken保存を使い、与えられた終了ScanInvariantと入口verifier条件からshift後CaughtScanを作る。全体build9121 jobs成功/exit 0、標準公理のみ、最終ジョブ終了済み。

**残り：** cycle/onlyはCaughtScanに未包含。caught_scan_matchedの左read=予測をshifted_check_pairから同じ状態で供給し、accepted比較列の帰納へまとめる必要がある。shift_caught_scanのScanInvariantと右headはまだ引数で、実shift終点との同一性は呼出側で結ぶ。時計/入力到着を含む全controller/全PALは未完。

**最新：実一致比較→成功consume。** InputSupplyに `matched_left_prediction` を追加。verifier/outerの同じ入力Represents・focus存在・同位置・外側right合法と、「比較済み左read=実予測token」「比較済み左read=移動後外側right read」から、Watch.Good、実VerifyRunの1-step、broken保存を同時に導出。外側の実read存在から予測token有効性を内部導出するので、Good/予測someを別途仮定しない。全体build9121 jobs成功/exit 0、標準公理のみ、最終ジョブ終了済み。

これはshifted_check_pairのk<2h枝と実一致比較から、成功継続を一文字延長するための部品。**未完：** 両定理の同一状態への合成、only継続の各tickで左/右/verifier/lag/cycleを同期する帰納、fallback/最終比較のdispatch、全PAL。新定理のverifierとouter同位置等は依然前提。

**最新：checkPairの現在左座標を実移動から導出。** InputSupplyに `LeftMoves`（各左移動前focus存在）、`left_moves_position`（同じ入力Represents保存とposition終了+n=開始）、`bounded_left_moves`（n≤開始positionから合法列を構成、終点番兵も可）、`left_moves_read` を追加。`shifted_check_pair` の署名を変更し、現在leftのRepresents/座標を直接仮定するのをやめ、shift終了ScanInvariantとそこからextra.length+1回のLeftMovesを受けて内部導出する。全体build9121 jobs成功/exit 0、標準公理のみ、最終ジョブ終了済み。

**未完：** hresumeの実shift終点との同一性、left移動と同じ継続比較の右/verifier消費数・cycleの同期、成功追加語の帰納構成、only/guard全体。LeftMoves単独は同じtickで右も動くcontrollerではない。全PALは未完。旧「現在左head座標を前提」という記述は上記に更新する。

**最新：実左read対実period tokenのcheckPairを合成。** InputSupplyに `shifted_check_pair` を追加。同じ成功Watch.Run/ChainShiftRun、旧ScanInvariant/実左右不一致、ready入口、開始verifier=center、watch終了=c+R+1、2h≤R、成功追加語extra（長さ<2h）、現在左headのRepresentsと座標から、**実左read=実次予測token ↔ extra.length+1<2h** を導出。旧右窓対応はshifted_prediction_windowから内部供給、番兵もrepresented_signed_read経由で対応。全体build9121 jobs成功/exit 0、標準公理のみ、最終ジョブ終了済み。

この定理はcheckPairの文字比較部分の合成であり、まだcontrollerの無条件assert安全性ではない。**残る前提：** 継続中の現在左head座標を同じ実行から導くこと、extraの成功をaccepted比較の帰納で保つこと、cycle=2h−extra.length/only/watch/lagzeroの同期、開始・終了verifierと外側scanの同一時系列。次はこの比較結果をcycleEnd判定と同期し、一致比較から次の成功consumeを構成する。全PALは未完。

**最新：shift後の各実tokenと旧右窓。** ChainPredictionの `continued_prediction` はcounter調整後の成功追加語から、通算pre.length+extra.lengthのmod添字で実tokenを返す。InputSupplyに `chain_shift_continued_prediction` と `shifted_prediction_window` を追加。後者は同じready開始成功Watch.Run→同じChainShiftRun→成功追加consume語を接続し、extra.length<2hなら、実次token=encoded raw[旧watch終了位置−2h+extra.length+1]を導出。予測窓対応そのものを独立した前提にしていない。全体build9121 jobs成功/exit 0、標準公理のみ、最終ジョブ終了済み。初回のgetElem?直前改行の構文エラーは修正済み。

**残り：** 成功追加consumeは前提。実only比較が一致ならこの成功を延長できること、左headの各比較座標、cycle値、最後の旧不一致の同じscanへの同期を合成する必要がある。shift長nと周期hの同一性もこの汎用定理自体は要求しない（呼出側で一致させる）。checkPair全体、全online/全PALは未完。

**最新：shift後のconsume成功と実Runを転送。** ChainPredictionに `consume_same_broken` / `run_same_broken`（SamePredictionと開始broken一致から同じ語の終了broken一致）。InputSupplyに `chain_shift_broken` / `chain_shift_future_success` / `chain_shift_supplied_run` を追加。最後は同じChainShiftRun、shift前verifierからの合法Reads、同じ語のshift前controlでの成功から、shift後machineの実VerifyRun.Run・同じ終了verifier・broken=falseを構成する。verifier保存はchain_shift_valuesから内部供給。全体build9121 jobs成功/exit 0、新しい主要定理はpropext/Quot.soundのみ、最終ジョブ終了済み。

**まだ条件付き：** 転送元の追加語の成功と合法Readsは前提。実only継続がその語を読むこと、供給/比較・cycle/checkPairの同一時系列は未証明。予測列を勝手に入力として供給して全online成功と見なさない。次は成功周期prefixから各継続予測を導き、左比較と同じ実右読出しを条件分岐へ接続する。全PALは未完。

**最新：shiftのcounter変更を跨ぐ予測保存。** ChainPredictionに `SamePrediction`（period/forward一致）、`consume_same_prediction`、`run_same_prediction` を追加。同じseen/語に対してperiod/forwardはcounter/phase/brokenの違いによらず同じ（不一致読出しも含む）。InputSupplyに `chain_shift_prediction` と `chain_shift_future_prediction` を追加し、同じChainShiftRun前後のperiod/forward保存、そこから同じ任意の追加consume語後の実予測token一致を導出。全体build9121 jobs成功/exit 0、両主要保存定理はpropext/Quot.soundのみ。初回のconsume内match/if分岐不足は修正、最終ジョブ終了済み。

**残り：** 実only継続で読む語と周期prefixの同一性・成功性、各kのtokenと旧右窓対応への合成、left/cycle/guard同期。SamePrediction自体はbroken保存や成功実行の存在を主張しない。ready開始の成功prefix定理と、shift後状態がそのperiod/forwardを共有することを使って接続する。全online/全PALは未完。

**最新：実period token→旧右窓。** ChainPredictionに `successful_next`（同じ開始状態から二つの成功語の長短を使い、短いrun終了period token=長い語の次文字）と `successful_prediction`（ready開始成功actual終了token=bounce[actual.length mod 2h]）を追加。InputSupplyの `watch_prediction_window` は同じ成功Watch.Run、開始Represents/focus、終了変位n≥2hから、**実終了period token=encoded raw[end−2h+1]** を導出。周期式だけだった前段から実tokenに接続した。全体build9121 jobs成功/exit 0、標準公理のみ、ジョブ終了済み。

適用範囲はfresh ready開始の成功watch終点。**shift後はdistance等を変更しているので、同じready開始runとそのまま同一視できない。** 次はperiod/forwardが同じならconsume後のperiod/forward/予測も同じという射影保存を使い、shift後継続各kのtokenへ拡張する。最初のtokenのshift保存はchain_shift_values.periodから供給可能。終了位置と旧scan最後の比較同期、only/cycle/全guard、全PALは未完。

**最新：周期語と同じ実入力の旧右窓を接続。** InputSupplyに `watch_input_cycle` と `watch_previous_window` を追加。前者はready開始の同じ成功Watch.Runから、各実読出しword[start+i+1]がbounce[i mod 2h]に等しいことと終了変位nを導出。後者は終了変位n≥2hで、1≤k≤2hについてbounce[(n+k−1) mod 2h]=word[end−2h+k]を導出する。これが継続比較に渡す旧右窓対応。全体build9121 jobs成功/exit 0、標準公理のみ、ジョブ終了済み。

**残る差：** この段階の「次の予測」は周期語の添字式。実period headが各継続consume前にそのtokenを返すこと（shiftでperiodが保存されること自体は証明済み）を証明する必要がある。watch終了=end=c+R+1を最後のshift比較と同期し、scan_continuation_pairへ合成する部分も残る。成功Watch.Runは依然前提。only/cycle/実guard/全PALは未完。

**最新：実scan不一致→番兵込み継続比較。** InputSupplyに `represented_signed_read`（focus存在不要、Representsだけで実read=signedRead(position)）、`left_signed_read`（実leftのread=signedRead(旧position−1)）、`scan_radius_lt`、`scan_failed_signed`、`scan_continuation_pair` を追加。最後は実ScanInvariant・合法right・実左右不一致から、旧PalAt/R<c/語レベル不一致を内部導出してcontinuation_pair_signedへ合成する。予測と旧右窓の対応、2h≤R、k範囲は依然前提。全体build9121 jobs成功/exit 0、標準公理のみ、最終ジョブ終了済み。初回のsimp条件消去失敗はsimp onlyで修正済み。

この更新で旧記述の「実head.readとsignedReadの対応」「実scanからR<c」「旧不一致の語レベル供給」は接続済み。**残り：shift後の各比較headが指定座標へ来る同一run、予測列と旧右窓の対応、cycle値/only時系列/checkPairの全guard、全online/全PAL。** 次は成功watch周期から予測窓の対応を導出するのが核心。

**最新：番兵を含む継続比較の語レベル定理。** InputSupplyに `signedRead` と `continuation_pair_signed` を追加。重要：encodedの0番はsynthetic gap=2だが、実headの最初の文字から左へ出た番兵はfocusなしでnone。したがってsignedReadは **i≤0をnone**、i>0をword[i.toNat]とする。負だけをnoneにする初案は、この実head対応の違いを確認して修正した。

`continuation_pair_signed` はR<c、2h≤R、旧PalAt、予測と旧右窓の対応、signedReadでの旧不一致から、1≤k≤2hで継続左比較一致↔k<2hを証明する。最後のc−R−1=0という番兵枝も含む。全体build9121 jobs成功/exit 0、propext/Quot.soundのみ、ジョブ終了済み。**まだ実head.readとsignedReadの等式、ScanInvariantからR<cの供給、予測列対応、cycle/only時系列への接続は未完。** 語レベルの番兵対応をcheckPair全体の完成と扱わない。次は実left読出し座標をこの定義へ接続する。全PALは未完。

**最新：only継続の文字比較（鏡映部分）。** InputSupplyに `continuation_pair` を追加。旧PalAt(c,R)、R+1≤c、2h≤R、旧境界word[c−R−1]≠word[c+R+1]、予測k=旧右窓word[c+R+1−2h+k]という対応を前提に、1≤k≤2hでshift後左文字word[c−R−1+2h−k]と予測の一致↔k<2hを証明。内部点は旧回文の鏡映、最後は旧不一致をそのまま使う。全体build9121 jobs成功/exit 0、propext/Quot.soundのみ、終了済み。初回の隣接doc comment構文エラーは修正済み。

**未接続を明記：** 予測列と旧右窓の対応は依然前提で、同じchain周期/継続consumeから導く必要がある。R=cで左がabsent sentinelになる枝はこの定理の対象外。実左head座標とcycle値=2h−k+1を結び、singlePositive判定と合わせる部分、onlyモードの実時系列も未完。checkPair全体や全PALを完成扱いしない。次はこの予測対応を成功watchの周期から供給するか、番兵枝を実Option読出しで補う。

**最新：shift直後のcycleとcycleEnd。** Counterに `singlePositive`（positiveかつpos.tailが空）とCanonical下の `singlePositive_iff`（値=1との同値）を追加。Scala cycleEndのdecoded判定に対応。InputSupplyに `chain_shift_cycle_canonical`、`chain_shift_reset_cycle` を追加し、同じChainShiftRunがreset cycleからh>0回進むと終了cycle値=2h、positive=true、singlePositive=falseを証明。共通Counter依存を含む全体build9121 jobs成功/exit 0、sorryなし、最終ジョブ終了済み。初回の整数算術残ゴールはomegaで修正。

Scala確認：beginShiftはonly=true/cycle.reset、shiftOneはcycle.inc×2、only中matchedはcycle.dec。**cycleEndはshift完了条件ではなく、継続比較の残り1セル判定。** 次の本質はcheckPair（only/watch/lagzero下でcycle>0、左文字とpredictionの一致がcycleEndの否定と同値）の文字列不変条件。算術だけでは証明できていない。mode/output、guardからのWatch.Run成立、全PALも未完。

**最新：chain.shiftOneを同一shift反復へ接続。** InputSupplyに `chainShiftOne`（既存Watch.Stateのcontrol distance/boundary/lastとmarginをdec）、`ChainShiftRun`（既存外側shiftTickとchainShiftOne、cycle.inc×2を同じtickで更新）、`shift_run_chain`、`chain_shift_values` を追加。任意の同じShiftRunと入口watch/cycleから同じ外側終点を持つChainShiftRunを構成できる。n回後のdistance/boundary/last/marginは各−n、cycleは+2n、verifier/period/lagは不変。全体build9121 jobs成功/exit 0、shift_run_chainは公理なし、chain_shift_valuesはpropext/Quot.soundのみ。初回のrecord改行構文エラーは修正済み、最終ジョブ終了済み。

これでshift中のchain私有counter更新のdecoded同期まで対応したが、beginShiftのonly=true/cycle.reset、cycle終了判定、mode=Scan/output、全controller到達性はまだ未接続。shiftRun存在は既存head/scan定理から供給できるが、成功watchと半径条件を実guardから導く課題は残る。全PALは未完。旧「chain.shiftOne同期未完」はこの更新で置き換える。

**最新：shiftの正規形と終了guard。** InputSupplyに `ShiftCanonical`、`shift_tick_canonical`、`shift_run_canonical`、`shift_run_values`、`shift_run_exit` を追加。同じ任意のShiftRunについてremaining/radius/lengthのCanonical保存と値の減少を証明。初期remaining値=nでn回実行した場合、終了zero=trueかつpositive=falseを導出する。これは開始remainingを構文的にofNat nと固定しない終了guardの定理（ただしRunの存在は前提）。全体build9121 jobs成功/exit 0、印字公理は標準公理のみ、終了済み。次は実chain.shiftOne/cycleと同じtickへの合成、または実guardから成功watch等の前提導出。mode=Scan更新・outputおよび全PALは未完。

**さらに最新：外側shift counterを同期。** 同じInputSupplyに `ShiftState`（center/left/remaining/radius/length）、`shiftTick`、`ShiftRun`、`shift_heads_counters`、`shift_scan_counters` を追加。Scala stepShiftのremaining.dec→center.right→left.right×2→radius.dec→length.dec×2をdecoded状態で表す。各tickのremaining正値guardと全head guardを持つh回のRunから、remaining=ofNat 0、radius値がh減少、length値が2h減少を導出。`shift_scan_counters` は比較直後radius値=旧R+1を受け、終了radius値=R+1−h、remaining.zero=true、同じ終了headのScanInvariantを一括で返す。

全体build9121 jobs成功/exit 0、両定理は標準公理のみ、ジョブ終了済み。これは**外側shift状態の射影**。chain.shiftOne（distance/boundary/last/marginのdec、cycleのinc×2）、mode復帰/output、counterの実初期化・Canonicalと実controller到達性はまだ含まない。旧「外側counter同期未完」の記述はこの更新で置き換える。実center配置、成功Watch.Run/半径条件の実guardからの導出、全PALは引き続き未完。次はchain私有counterを同じshiftTickへ接続するか、phase4→半径条件を閉じる。

**保存後の継続による更新：** `GalilScaffoldChainInputSupply.lean` に `ShiftHeads` と `reads_shift_heads` を追加。Scala `ScaffoldGalil.stepShift`（324行付近）のhead更新順に合わせ、各反復で中心right一回→左right二回の全guardを保持した同じh回の遷移を構成する。`shift_scan_resume` と `scan_prediction_shift` の結論にこの遷移を追加済み（署名変更）。独立したReads列しか返さない、という下方の記述は旧状態。

この更新の全体buildは9121 jobs成功/exit 0、`reads_shift_heads` は標準公理のみ。初回buildの不存在補題 `List.length_eq_zero.mp` エラーはリストの場合分けに直して解消。最終buildは終了済み。**同tickのhead射影までであり、radius/remaining/length/counter/chain.shiftOneの同期、実centerと開始verifierの一致、guardからの成功Watch.Run等の導出はまだ未完。** 次はこの関係に実counterとchain状態の更新を接続するか、phase4から半径条件を導出する。大定理は未完。

今回の依頼は進捗保存のみ。証明コードの追加・変更はしていない。以下より後ろの追記は履歴を含み、古い「次は」「未対応」は現在の指示ではない。

### 完了している接続

- `lean-pal/PalPeg/GalilScaffoldChainInputSupply.lean:1260` の `scan_prediction_shift` が最新の合成定理。比較前のScanInvariantとDP候補、成功Watch.Run、lag/半径収支、最後の予測一致から、shift先のPalAtに加え、中心h回・比較後left 2h回の合法Readsと終了ScanInvariantを返す。
- 同ファイルの `shift_scan_resume`（1111行）で移動の終点範囲・表現保存・番兵からの復帰を処理する。`GalilScaffoldChainPrediction.lean` の `watch_period` は同じ成功watchの読出し列に周期2hを与える。
- 初期scan、入力到着、比較一致による半径拡張、DP窓と実入力座標、found→Copy→Back→ready、既知回文半径内の安全な読出しも部品として接続済み。

### 未完の核心と次の作業

1. **別々のReads列をScalaの同一shift実行へ接続する。** 実centerと開始verifierの配置一致を示し、各tickのcenter.right / left.right×2 / radius.dec / chain.shiftOneを同期する。いま証明したのはdecoded headの射影で、全controllerの実行ではない。
2. `scan_prediction_shift` の残る前提を実guardから導く。特に `2h≤R`、予測token有効性、成功Watch.Runの存在、初期lag＋同じmatched数＝半径。phase4とdistanceの関係から半径条件を外せるか調べるのが次の小さい候補。
3. 正lagの内部catch不一致排除、back終了tick直後のlag=0 consume、only=true/cycleによる再shift、restart/fallback/replayを同じ実行へ合成する。
4. 入力到着・実時計・期限・出力認識を閉じ、論理head/FIFOから物理Ref/heap/回路へのrefinementを完成させ、具体的機械を `lean-pal/PalPeg/Main.lean:43` の `pal_in_peg_of_structured` に渡す。**この無条件の最終接続はまだない。**

### 再開時に読む順序と落とし穴

- まず上記InputSupplyの末尾2定理と `shift_scan_resume`。必要な依存だけChainPrediction → ChainWatch/WatchTrace → ChainCredits/Readyへ辿る。
- Scalaは `scala/pal/src/main/scala/pal/ScaffoldGalil.scala` と `ScaffoldChain.scala` で制御順序を確認し、実回路の `ScaffoldCircuitGalil.scala` / `ScaffoldCircuitChain.scala` と対応させる。入力経路はbuildOnline → event buffer → packService → GenerateOnlinePegの生ab入力。
- 比較では不一致判定より先にradiusが増える。shift終了半径は旧Rに対して **R+1−h**。旧中心でPalAt(R+1)やshift途中の各tickのPalAtを仮定しない。
- `acceptedRadius` は受理比較区間の射影。不一致でfallbackする比較のradius.incをfalseとして消してはいけない。replay開始はradius=0なので、開始半径が常に正という仮定も不可。
- Lean側delay=2048とScalaの旧時計較正の整合は残っている。成功列を仮定した時計補題だけで全onlineの期限を証明したことにしない。

### 検証・作業状態

- 直前の検証記録：全体 `lake build` **9121 jobs成功、exit 0**。新しい主要定理の公理監査は標準公理のみ。今回の保存ではソースの署名を照合したが、buildを再実行したとは主張しない。
- 検証コマンド：`lean-pal/` で `lake build`、repoで `git diff --check`。Leanジョブは一度に一つ。`lake env lean` は依存oleanを生成しない。
- この引き継ぎファイル自体を含め多数の重要ファイルがuntracked。削除済み表示の既存ファイルもある。すべて現状を保全し、履歴に戻す操作をしない。commitはしていない。
- サブエージェントは使わない。最終目標までの残りを部品数やテスト数で小さく見せない。再開時は上記1か2を具体的に進め、閉じた前提を報告する。

## 過去のチェックポイント（新しい順・上の要約が優先）

### 再開チェックポイント（2026-09-14・今回の保存）

**最新（予測shift→移動→走査再開）：** `shift_scan_resume` を追加。旧ScanInvariantと新PalAt、0<h≤R、外側right合法から、中心h回/比較後left 2h回の合法Readsを構成し、中心終了表現/focusと終了ScanInvariantを返す。各移動の終点範囲は旧scanから内部導出、sentinel経由も対応。
`scan_prediction_shift`の結論を強化（署名変更）。従来の新PalAtに加え、上記移動列と終了ScanInvariantも同時に返す。比較前scan→最後の予測一致→成功watch拡張→新PalAt→移動→再開まで接続。全体build成功9121 jobs/exit 0、標準公理のみ、終了済み。
ただしこれはdecoded headの別々のReads列を合成した射影。実centerは開始verifierと同配置であること、同tickでcenter1/left2/radius.dec/chain.shiftOneする順序とcounter/cycle/onlyの同期、2h≤R/予測token有効性/全watch成功性、fallback・期限・物理回路・全PALは未完。

**最新（shift移動guardと番兵復帰）：** `bounded_right_moves`はRepresents/focus存在/position+n<入力長から、n回の合法Reads・終了座標/表現/focusを構成。`left_return_legal`は実leftの直後のrightが合法で元headへ戻ることを保証。
`shifted_left_moves`は比較前head pから、left p（focusなし番兵の場合も含む）を始点としてn+1回の合法Readsを構成し、終了位置=position p+nと表現/focusを返す。shift左2h回にはn=2h−1を渡す。全体build成功9121 jobs/exit 0、標準公理のみ、終了済み。
次はscan_prediction_shiftの新PalAtとこの移動構成を合わせて、center h回/比較後left 2h回/右head固定の終了ScanInvariantを構成。必要終点範囲を旧scan右端とh≤Rから導く。実同tick順序・counter/only/guardの全controller接続、全PALは未完。

**最新（比較前scan→最後の予測→shift先PalAt）：** `scan_prediction_shift` を追加。比較前ScanInvariant、同じDP窓/Candidate、ready開始成功Watch.Run、初期lag/半径収支、終了lagzero、2h≤R、外側合法右移動後の予測一致から、新中心c+h/半径R+1−hのPalAtを導出。
内部で同位置→Good→末尾true追加Run→count+1/lag保存→watch_shift_palindromeを合成。新右端までの周期/到達距離/短回文は別前提ではない。全体build成功9121 jobs/exit 0、標準公理のみ、終了済み。
次は実shiftのcenter+h/left+2h/radius−hをshift_geometryとつなぎ、終了ScanInvariantを構成する。比較直後leftがsentinelに落ちる可能性、実移動guard、phase4から2h≤R、イベント/半径同期、cycle/only再shift・fallback・全PALは未完。

**最新（scanから同位置/最後の予測tick）：** `caught_scan_prediction` を追加。ScanInvariantの右端、同じWatch.Runの開始distance0/lag初期値/終了zero、initialRadius+matched数=現半径から、外側右headとverifierの同位置を内部導出。外側の合法右移動後readとpredictionの一致を渡すとGoodと末尾true追加Runを返す。
全体build成功9121 jobs/exit 0、標準公理のみ、終了済み。次はこの追加Runをwatch_shift_palindromeへ一括合成（count追加分=1/lag保存）、その後実shift移動とScanInvariant再開。半径とmatched数の同一イベント対応、予測token有効性、2h≤Rの実guard、全online/全PALは未完。

**最新（最後の予測一致をwatchへ）：** `position_bound`、`canRight_of_bound`、`aligned_prediction_good`、`append_caught_tick` を追加。外側右headとverifierが同じ入力/同位置なら、外側の合法右移動後read=predictionからverifier側のcanRight/成功read、すなわちWatch.Goodを導出。
`append_caught_tick`は終了lagzero/GoodからInternal.idle→Outer.immediateの同じtickを構成し、Runのイベント末尾にtrueを追加。新右端を読む最後のshift予測比較を成功列へ含めるための接続。全体build成功9121 jobs/exit 0、標準公理のみ、終了済み。
次はprepared_radius_alignmentからの外側右headとの同位置を実scan状態から導き、この追加tickをwatch_shift_palindromeへ一括合成。cycle/only/beginShiftはWatch射影外なので全shift controller完成と数えない。実guard/全PALは未完。

**最新（同じイベント列のradius counter）：** `acceptedRadius`（true→inc/false→停止）とvalue/Canonical保存を追加。`prepared_radius_alignment`は同じ準備全イベント＋watchイベントで更新したこのcounter値が、終了lagzero時のverifier変位に等しいと証明。開始radiusの自然数値前提も不要（整数valueで直接合成）。
全体build成功9121 jobs/exit 0、標準公理のみ、終了済み。**acceptedRadiusは受理比較区間のcounter射影であり、Scala guardからこのイベント列が生成される証明ではない。** 不一致非shiftの比較はfallbackへ出るので、この列のfalseとしてincを落としてはいけない。次はこの区間の実guard/半径更新対応、最後のshift比較、shift減算・resetとの接続。全PAL未完。

**最新（準備からwatch終点までの収支）：** `prepared_caught_position` を追加。start/copy/done/backの同じCredits.run終了lagをwatch入口に接続し、開始distance0と終了lag値0から、終了verifier位置=開始位置+準備前radius+全準備matched数+watch matched数を証明。start/done各イベントも数えている。
全体build成功9121 jobs/exit 0、標準公理のみ、終了済み。入口lag=準備run終了lagという同一状態の等式は前提（prepare_pacedが供給するもの）。終端backのready-consume分岐をこの非consume準備モデルへ混ぜない。次は実外側radiusの更新を同じイベント列に同期し、watch_shift_palindromeのhcountへ接続。全online/全PALは未完。

**最新（lagzero→実verifier終点）：** `watch_progress`で同じWatch.Runのdistance+lag増分=bs.count true。`caught_position`は開始distance0/開始lag値=initialRadius/終了lag値0から、終了position=開始position+initialRadius+matched数を導出。
`watch_shift_palindrome`を変更し、旧終了verifier到達前提を削除。代わりに開始lag値・終了lagzero・initialRadius+matched数=旧radius+1を受け取り、到達距離を内部導出する。全体build成功9121 jobs/exit 0、標準公理のみ、終了済み。
次はこの半径/同じmatched数の等式と準備開始lagを実controllerの比較・最後のshift比較に同期する。現定理はそれを前提とし、成功Watch.Run自体/2h≤R/実shift移動/終了ScanInvariant/全PALは未完。

**最新（DP＋同じwatch→shift先PalAt）：** `watch_shift_palindrome` を追加。同じDP窓/Candidate、ready開始成功Watch.Run、verifier開始座標=center、旧PalAt(c,R)、2h≤R、終了verifier位置≥c+R+1からPalAt(c+h,R+1−h)を導出する。短い左回文・全区間周期・右端の入力範囲は内部導出した。
全体build成功9121 jobs/exit 0、標準公理のみ、終了済み。**終了verifier到達条件はまだ前提**。次はdistance+lagの増分=matched数を同じWatch.Runから導き、ready開始distance0/開始lag=開始半径と終了lagzeroから実右端一致へ。外側比較の半径とmatched数（最後のshift比較含む）の同期が必要。2h≤Rの実guard、shift移動/終了ScanInvariant、全PALは未完。

**最新（DP短回文→実入力PalAt）：** `backward_palindrome` と `candidate_short_palindrome` を追加。後者は同じw=Place.stream.take span、実DP Candidateから、letter/gap共通でPalAt(encoded raw,center−h,h)を導く。centerは2L−1/2L。逆向き窓の全添字（先頭0含む）と範囲2h≤centerを内部導出。
全体build成功9121 jobs/exit 0、標準公理のみ、終了済み。次はこれをshift_from_rightへ合成し、watch_input_periodの開始位置=centerと終点≥center+R+1を同じ実lagzero/最後の比較から導く。2h≤R、成功watch区間の実時系列、only=true再shift、全online/全PALは未完。

**最新（周期の中心継ぎ目と左鏡映）：** `period_from_right`、`shift_from_right` を追加。旧PalAt(c,R)、2h≤R、短い左PalAt(c−h,h)、右側(c<j,j+2h≤c+R+1)の周期から区間全体の周期2hを導出。中心継ぎ目は短い左回文と旧回文の鏡映、左側は右側周期の鏡映を使用。
`shift_from_right`で0<h/新右端存在を加えてPalAt(c+h,R+1−h)へ合成。全体build成功9121 jobs/exit 0、標準公理のみ、終了済み。
次は短い左PalAt(c−h,h)を同じDP Candidateの長さ2h+1回文と窓座標から導く。右側はwatch_input_periodの終了変位がR+1まで届くこと（lagzero/最後の比較）と開始verifier=centerを同期する必要がある。2h≤Rの実guard導出、only=true再shift、全online/全PALは未完。

**最新（watch周期を実入力へ）：** ChainPredictionに `cycles_index`（添字mod往復長）、`cycles_period`、`watch_period` を追加。成功Watch.Runから同じTraceとHasPeriod(actual,2h)を抽出。Wordsを明示import。
ChainInputSupplyに `reads_index` と `watch_input_period` を追加。Readsのi番目=encoded raw[position開始+i+1]を導き、同じwatch終了変位nと、実入力右側でi+2h<nなら周期2hの文字一致を返す。全体build成功9121 jobs/exit 0、標準公理のみ、終了済み。添字加算形のエラーは明示的な等式で修正済み。
次は右側周期を既知PalAtで左側へ反映し、中心近傍の継ぎ目とshift開始の最後の比較を含め、shift_after_predictionの全区間周期へ接続。watch_input_periodは固定raw/成功Watch.Run/ready開始/開始verifier配置を前提とし、lagzeroによる右端一致と全online成功性は未接続。全PAL未完。

**最新（任意長の往復予測）：** ChainPredictionに `cycles`/`cycles_length`/`cycles_run`/`successful_cycles`/`watch_cycles` を追加。round_tripを任意回反復してperiod/方向/brokenを保存。成功列のprefix一意性から、任意有限成功語actualはcycles(bounce,actual.length).take actual.lengthと一致する。
`watch_cycles`は同じWatch.RunからTraceとこの反復prefix等式を一括抽出。二往復以降も対象にした。全体build成功9121 jobs/exit 0、標準公理のみ、終了済み。
次はこの反復prefixから周期2hの添字一致を導き、実入力の右側座標と既知PalAtによる左側への反映を経てshift_after_predictionの区間周期前提を埋める。watch_cyclesは依然「成功Watch.Run/ready開始」の定理で、全online成功性やshift最後の比較との同期は未証明。全PAL未完。

**最新（不一致後のshift先PalAt）：** `shift_after_prediction` を追加。古いPalAt(word,c,R)、0<h≤R、新右端c+R+1の存在、区間[c−R,c+R+1]上の周期2h一致からPalAt(word,c+h,R+1−h)を証明。古い中心でPalAt(R+1)を仮定しない。新中心の左点を古い回文で鏡映し、周期で右点へ渡す。
Scala Chain.canShift/beginShift/shiftOneを再確認。不一致比較でradius.inc済みなので、shift終了半径は旧R+1−h。以前のshift_geometryへ渡すradiusはこの増加後の値。途中microstepごとのPalAtは主張しない。
全体build成功9121 jobs/exit 0、標準公理のみ、終了済み。**重要：区間全体の周期2hは依然前提であり、DP候補・成功watch予測・lagzeroから導出していない。** 次はこの周期前提を同じ実watchの文字列から導き、shift_geometry/終了ScanInvariantへ接続。実guard/半径範囲・fallback・窓・時計・全PALは未完。

**最新（shift幾何とwatch位置）：** Scala Galil 198–252行でshiftのcenter.right/left.right×2/radius.decを確認。`reads_position`で実Readsの長さ=座標変位、`watch_displacement`で同じ成功Watch.Runのverifier変位=distance counter差および入力表現保存を証明。
`shift_geometry`は実centerのh回右移動とleftの2h回右移動（Readsを前提）、h≤radius≤center座標から、終了left=newCenter−(radius−h)、右端newCenter+(radius−h)=旧右端を導出。shift途中の各microstepでPalAtが成立すると仮定しない。移動guard供給とshift先の回文性は別途必要。
全体build成功9121 jobs/exit 0、標準公理のみ、終了済み。次はDP候補/period予測からshift先のPalAt、実shift guardとradius範囲、watch lagと左右位置の同期へ。fallback/窓/時計/期限/物理回路/全PALは未完。

**最新（固定中心の走査不変条件）：** `ScanInvariant raw center radius l r` を追加。左右Represents/focus存在/端点center±radius/PalAtを同時保持。`scan_initial`で同位置radius0、`scan_first`でreset→文字a到着→gap=trueから実right移動の初期化を導出。Scala Input.PlaceHeadの初期gap=trueを現物確認した。
`scan_arrival`は同じ両headへのappendで保存、`scan_matched`は合法rightと実移動後read一致からradius+1の同じ不変条件を返す。全体build成功9121 jobs/exit 0、標準公理のみ、終了済み。
これは固定中心の成功走査射影であって全Galil機械ではない。次はshift/fallbackで中心が変わる枝、Search窓/Chain/clock/counterとの同時不変条件へ接続する。最初の文字一つ以外の初期バッファ、失敗・再走査・出力判定・内部catch全域・期限/物理回路/全PALは未完。

**最新（成功比較の移動を合成）：** `right_present`、`left_word`、`comparison_extends` を追加。比較前の同じrawのRepresents/両focus存在/端点center±radius、right.canRight、既知PalAt、実left/right移動後のread一致から、PalAt(radius+1)と両移動後Representsを同時導出する。
半径<center、移動後の端点、右focus存在、左focus存在を内部導出。左focusは右readがsomeであることと一致から導くため、番兵への左移動を成功枝から排除できる。全体build成功9121 jobs/exit 0、標準公理のみ、終了済み。
次はこの成功比較と入力到着保存を同じ到達不変条件へ組み込み、初期化・中心shift/fallback・Search窓と同期する。現在は比較前の端点対応が前提。counter/時計/モード全体、内部catch全域、期限/物理回路/全PALは未完。

**最新（実比較移動の座標）：** `right_position`/`left_position`/`comparison_positions` を追加。実PlaceHead.right（stack/FIFO含む）は座標+1、leftは座標−1。比較前position=center±radiusから、同じ実移動後position=center±(radius+1)を導出する。条件は両head左長正、right.canRight、radius<center。
全体build成功9121 jobs/exit 0、標準公理のみ、終了済み。次は移動後のRepresents/focus存在を保存してmatched_extendsへ合成。先頭sentinelへ左移動する枝はfocusなしになり得るので、座標更新だけでfocus存在を仮定しない。実center/半径の初期化・shift・窓同期・全PALは未完。

**最新（実read→比較一致→半径拡張）：** `reverse_prefix_read`、`layout_read_coordinate`、`position`、`represented_read`、`matched_extends` を追加。両gapの実head.readを同じencoded raw[position]へ接続。matched_extendsは同じrawを表す左右headのread一致からPalAt(radius+1)を導く。右端範囲はRepresentsから内部導出する。
残る前提は左端非underflow（radius+1≤center）と移動後の左右position=center±(radius+1)。実left/right更新からこの座標を導くのが次。Scala Galil 130–205行を再確認：比較ではright.right→left.left→radius.inc/advanceMatch→read→matchedの順なので、PalAt拡張は成功枝のみ。不一致後にも無条件にPalAtを置かない。
全体build成功9121 jobs/exit 0、標準公理のみ、終了済み。移動・中心shift・窓同期・時計・内部catch全域・全PALは未完。

**最新（入力到着のPalAt保存）：** `palAt_append`、`encoded_arrival`、`palindrome_arrival` を追加。encoded(raw++[a])=encoded(raw)++[letter a,2]なので、以前の末尾gapを含む既知PalAtが保存される。同じInputTrace.append後のReachと、同じhead左長/gap座標におけるPalAtを同時に返す。全体build成功9121 jobs/exit 0、標準公理のみ、終了済み。
これは入力到着分岐の保存のみ。PalAtの初期化・比較一致による半径拡張・中心移動/shift・Search窓との同期はまだ実Galilの到達不変条件として閉じていない。次は実左右headの読出し座標と比較更新への接続。全PAL未完。

**最新（letter/gap共通化）：** `reachable_mirrored_safe`、`window_mirrored_safe`、`found_window_safe` をgap:Bool引数で一般化した（既存署名変更）。座標はgapなら2L、letterなら2L−1。右供給を場合分けしてPalAtの右端から必要量を導出し、左配置もそれぞれの既存補題から内部導出する。
同じfound→Copy→Back→ready.period→任意n≤radius,4hの安全Runが両中心を扱う。gap版の別経路を追加せず共通定理に統合。全体build成功9121 jobs/exit 0、標準公理のみ、終了済み。
次は実Galil到達状態からPalAt/center/radiusとSearch窓一致を導くこと、およびwatchのlag/比較時計・中断の実時系列への同期。focusなし番兵、n>4hの内部catch、shift/restart/期限/物理回路/全PALは未完。gap未対応という下方の記述は旧状態。

**最新（gap左配置）：** `encoded_take`、`gap_left_window_reads`、`candidate_gap_window_layout` を追加。gap座標2Lに対する左stream.drop1の読出しは、同じ拡張入力のleftReadsに一致する。n≤2*xs.length+1およびn≤span−1はDP Candidateとn≤4hから内部導出。全体build成功9121 jobs/exit 0、標準公理のみ、終了済み。
次は既存reachable_gap_supplyとこの配置を合成し、gap/letterを共通安全性定理へ整理してfound_window_safeを両中心へ拡張する。PalAtと窓の実時系列不変条件、内部catch全域、時計・物理回路・全PALは未完。

**最新（gap開始の右供給）：** `rightReads_tail` と `reachable_gap_supply` を追加。letter開始のn+1回Readsから最初のgap読出しを除き、同じHead/gap=trueから正確にn回の合法Reads、座標2*head.left.lengthのrightReads一致、終了Represents保存を導く。条件はReach/focus存在/n≤2*unread.length。末尾gapでn=0も含む。
全体build成功9121 jobs/exit 0、標準公理のみ、ジョブ終了済み。次はgap開始の左stream配置と鏡映安全性へ接続し、letter/gapの共通定理へ整理。gap版のfound安全性、実PalAt/時計/内部catch全域/全PALは未完。先頭focusなしの番兵は対象外。

**最新（found→copy/back→安全Runを合成）：** ChainInputSupplyに `window_mirrored_safe`、`copied_window_head`、`found_window_safe` を追加。window_mirrored_safeは同じlayout/Reachとw=stream.take spanから左右座標を内部導出。copied_window_headはCandidateと実read/copy列からh=xs.length+1および予測head形を導出する。
`found_window_safe` は同じSafeQuanta/found/DP Resultからfound_start_backを使い、同じh・文字列・periodに対するCopyとBack（終点がConsume.ready.period）を保持し、そのreadyから任意n≤radiusかつn≤4hの実verifier Run/broken=false/入力表現保存を返す。右Reads・左右配置・予測head形を外から仮定し直していない。
全体build成功9121 jobs/exit 0、標準公理のみ、終了済み。なお入力Reach、w=同じ左stream.take(span+1)、PalAtは依然前提で、これらとSearch/Chainの実時系列の同期を証明したわけではない。Copy/Backはdecoded無中断射影で、credits/outer matched/clockとの合成も残る。次は実Galilのcenter/radius/左窓の到達不変条件、gap開始と内部catch全域。全PAL未完。

**最新（左窓座標）：** ChainInputSupplyに `pairs_append`/`encoded_reverse`、`leftReads_prefix`、`pairs_gaps`、`left_window`、`left_window_reads`、`candidate_window_layout` を追加。raw=(a::xs).reverse++suffixのletter座標で、拡張入力のprefix反転=Place.stream++[2]。左streamが先頭番兵gapを含まない差を明示した。
`candidate_window_layout` はw=stream.take spanとCandidate/n≤4hから、既存mirrored_candidate_safeの左配置等式を導出。範囲n≤2*xs.lengthとn≤span−1はCandidateの長さ条件から内部導出する。新規定理は標準公理のみ、全体build成功9121 jobs/exit 0、ジョブ終了済み。
次は同じInputTrace.layout/Reachの分解とこの左窓定理を `reachable_mirrored_safe` に一括合成し、実Searchの窓コピー結果に接続。その後実Galilのcenter/radius/PalAt不変条件。左窓定理自体はw=stream.take spanを依然前提とし、全online到達性を証明したものではない。gap開始/内部catch全域/全PALは未完。

**さらに最新：** `reachable_mirrored_safe` を追加し、Reachからの実右読出しを鏡映安全性へ直接合成した。`reads_present` から最後のgap読出しを追加し、`reachable_coordinate_supply` の供給長を `2*unread.length+1` へ拡張。新しい安全性定理では供給長をPalAtの右端条件から内部導出するため、右配置・Reads・独立した供給長の前提は不要。結論は同じverifierのn回Run、broken=false、終了入力表現保存。
全体build成功（9121 jobs、exit 0）、標準公理のみ、終了済み。残る条件はletter開始/focus存在、左DP配置、PalAt、n≤radiusかつn≤4h、DP候補/head形。次は左stream配置と実到達PalAt。末尾gapは対応済み（下記の未対応記述は旧状態）、gap開始は未対応。全online/全PALは未完。

**保存後の自動継続で更新：** ChainInputSupplyに `encoded`、`pairs_length`、`pairs_drop`、`encoded_suffix`、`rightReads_suffix`、`encoded_rightReads`、`represented_position`、`reachable_coordinate_supply` を追加。以下の着手案1とletter位置の右座標接続は実装済みになった。
`reachable_coordinate_supply` は同じrawのReach/focus存在/供給長条件から、合法Reads・正確にn文字・その列のmap someが同じencoded rawのrightReadsと一致・終了Represents保存を返す。Lの正性と入力長以下はRepresentsから内部導出。全体build再実行成功（9121 jobs、exit 0）、標準公理のみ。ジョブ終了済み。
次はこれをmirrored_candidate_safeへ直接合成し、左DP stream配置およびPalAtの実到達不変条件を導く。gap開始/末尾gapは未対応。大定理は未完。以下の「今回コード変更なし」は保存依頼時点の記録で、この追記がそれ以後の現在地。

**この節が現在地。以下の「最新追記」は新しい順の履歴で、下方の旧「次に実装するもの」や旧build件数は現在の指示ではない。**

- 最後に完了したコードは `GalilScaffoldChainInputSupply.lean`。現物を今回再確認した。直前セッションの検証記録は全体 `lake build` 9121 jobs / exit 0、印字公理は標準公理のみ。今回の保存では証明コードを変更せず、全体buildは再実行していない。
- 到達点：DP候補の二回文条件から二往復予測語を導出し、既知 `PalAt` と左右配置等式があれば実verifierの安全なRunへ渡せる。さらに、論理入力の `Reach` から右stack/FIFOを跨ぐ実読出し列を構成済み。
- **まだ無条件のPAL定理には接続していない。** `mirrored_candidate_safe` の左右配置・既知回文半径は依然前提。成功Watch.Runの時計・収支定理も、その成功区間が実online実行で成立することまでは示していない。
- 中断直前は次の座標接続を検討し、関連ソースを読んだだけ。未保存の実装や実行待ちのLeanジョブは引き継いでいない。

#### 次の着手箇所（提案、まだ未実装）

まず `GalilScaffoldChainInputSupply.lean`、`GalilScaffoldChainMirror.lean`、`GalilScaffoldChainVerifyRun.lean` の `pairs`、`GalilScaffoldInputTrace.lean` を読む。

1. 生入力 `raw : List (Fin 2)` の拡張語を `pairs raw ++ [2]` とする座標補題を作る。`pairs` は各文字を **gap=2, letter** に展開する。`pairs_append`、長さ `2 * raw.length`、`drop (2*n)` と生入力の `drop n` の対応が候補。
2. focusが存在するletter位置では `L = head.left.length ≥ 1`、拡張語上の現在位置は `2*L-1`。その右読出しは `pairs (raw.drop L)`。この対応から `ChainMirror.rightReads` への配置等式を導く。`n` 回を主張するには `n ≤ 2*(raw.drop L).length` 等の供給長条件が必要。`take n` だけでは不足時に短くなる。
3. 現供給定理はletter開始限定で最終gapを含めない。gap開始と末尾gap、左DP streamの座標を別途接続する。resetのfocusなしを先頭gapと同一視しない。
4. 同じ実Galil到達状態からcenter/radius/PalAtを導き、内部catchと早期不一致の排除へ進む。座標補題の追加だけをその不変条件の完成と報告しない。

#### 大定理まで残る接続

- 上記配置と回文不変条件、特に `n > 4h` の内部catchも含む安全性。
- back最終tickでwatchへ移行した直後のouter matched/lag=0 consume、失敗後のSearch.start、shift/only=true、fallback・pauseの同一実行への合成。
- 実時計とmatched/availableの対応、成功区間の存在、正例の期限。Lean側delay=2048とScala側の旧時計較正の整合。
- 論理head/list/FIFOから物理Ref/heap/回路・初期化へのrefinement、および具体的機械を `Main.pal_in_peg_of_structured` に渡す全認識証明。

再検証は `cd /home/mizushima/repo/lean4-peg/lean-pal` で `lake build`。一度に一ジョブ、終了を確認して次へ。`lake env lean` は依存oleanを生成しないので依存更新にはbuildが必要。repoで `git diff --check`。多数のuntrackedファイルも引き継ぎ本体なので削除しない。

### 最新追記：reachable inputからstack/FIFOを跨ぐprefix読出し

新規`GalilScaffoldChainInputSupply.lean`（root import済み）。mixed_supplyは右stack→incoming FIFOを跨いでpairs(rs++qs)を読む。
represented_supplyはInputTrace.Representsとfocus存在から、同じ到着済みwordのdrop(head.left.length)をgap/letter化した実Readsを構成。保存領域の分割を外から仮定し直さない。
right_word/reads_wordは同じwordのRepresents保存。reads_split_atで有限prefixへ分割し、reachable_prefix_supplyはInputTrace.Reachから配置前提を導出して、そのprefix Readsと終了word表現を返す。
全体build成功（9121 jobs、exit 0）、標準公理のみ、build終了済み。letter位置(gap=false)/focus存在が条件。prefix takeは不足入力では短くなるのでn回完走と誤認しない。
次はこのpairs(word.drop position)をChainMirror.rightReadsのFin3拡張入力添字へ対応させ、gap開始・左DP streamも同じ座標に接続。PalAt/center/radiusの実Galil到達不変条件・内部catch全域・時計/restart/shift/期限/物理回路/全PALは未完。

### 最新追記：既知回文半径の左右読出しから実verifier安全性へ

ChainVerifier.headRightを既存InputTrace.moveRightのabbrevへ統一（重複定義を除去、既存依存build検証済み）。
新規`GalilScaffoldChainMirror.lean`（root import済み）。leftReads/rightReadsは同じFin3入力wordのcenter±(i+1)をOptionで読む。既存Manacher.PalAtからmirror_readsで半径内の列一致を導く。
mirrored_candidate_safeはn≤既知radiusかつn≤4h、DP Candidate/head prefix、左DP窓・右実Readsが同じword/centerを表す二つの配置等式から、同じverifierのn回Runと終了brokenfalseを構成する。candidate_prefix_safeを実右読出しへ渡した。
全体build成功（9120 jobs、exit 0）、標準公理のみ、build終了済み。
まだ左右の配置等式/PalAt/合法Readsは前提。これらをInputTrace.Representsと実center/left/right/radiusの到達不変条件から導くことが次。n>4hの内部catch、既知半径境界の早期不一致、restart/shift/clock/期限/物理回路/全PALは未完。

### 最新追記：DP回文候補と二往復予測列の文字列一致

新規`GalilScaffoldChainPalindrome.lean`（root import済み）。palindrome_split/palindrome_prefixは奇数長回文を前半+中心+反転前半へ分解。
candidate_wordはCandidate w lower h（h=xs.length+1）とtake(h+1)w=center::(xs++[b])から、take(4h+1)w=center::(bounce++bounce)を証明。長さ2h+1と4h+1の**両方の実DP回文条件**を使用。
candidate_prefix_safeはその既知語のdrop1から任意n≤4hをconsumeするとbrokenfalseを保証。早期不一致排除に必要な予測文字列一致まで到達。
全体build成功（9119 jobs、exit 0）、標準公理のみ、build終了済み。
まだこれはDPの左向き入力窓の語。実verifierの右向き既知履歴が同じprefixになる対応（center周辺で既に一致した範囲/lag）を導く必要がある。未来の任意入力が一致するとは主張しない。次はこの対応を同じReads/consumeへ接続し、内部catch/4h以前の不一致を排除する。全online/期限/物理回路/全PALは未完。

### 最新追記：同じwatch prefixから実verifier不一致のrestart条件を導出

ChainRestart.watch_last_positiveはready入口の同じ成功Watch.Runで距離≥2hなら、成功prefix一意性から一往復を内部導出して終了last.positive=trueを保証。
failed_after_watchは同じWatch.Run/Canonical/ready/balance4h、終了lagzeroと距離≥4h−1からmargin≥−1を導出。実verifier.canRightと同じright後readの不一致にouterMatched(true)を適用し、Right実行・broken・margin非negative/last positive/lagzeroを同じ結果に保証。
旧failed_outer_restartの独立した一往復・margin条件と独立seenを、同じwatchと移動後readへ接続した。
全体build成功（9118 jobs、exit 0）、標準公理のみ、build終了済み。
距離≥4h−1より早い不一致と内部catch中の不一致が到達しない証明はまだ必要。予測token有効性とcanRightも実配置からの導出待ち。次tick Search.start(chain.last)への接続、実clock/shift/only=true、正例期限、物理回路、全PALは未完。

### 最新追記：outer consume失敗からrestart assertionへ

新規`GalilScaffoldChainRestart.lean`（root import済み）。Orderedはlast≤boundary≤distance。consume_order/run_orderで順序とlast単調、consume_canonical/run_canonicalで3counterのCanonicalを保存（不一致含む）。
last_positive_after_bounceは最初の往復後last=h>0が任意suffix（失敗含む）でも保持されると証明。
failed_outer_restartは一往復後のcontrol、lagzero、margin Canonical/value≥−1、予測との不一致seenからouterMatched(true)後broken=true/margin非negative/last positive/lagzeroを同じ結果について導く。失敗時にもmargin.incが先行することを使用。
全体build成功（9118 jobs、exit 0）、標準公理のみ、build終了済み。
まだseenは右移動後のverifierへ接続する必要がある。実到達状態で一往復済み・margin≥−1を導く証明、内部catch中の不一致排除、次tick Search.startへの実状態接続、時計/中断/only=trueは未完。全PAL/期限/物理回路も未完。

### 最新追記：初期margin非負の制約を除去

ChainPrediction.margin_exactで同じWatch.Runの終了margin=開始margin+matched数を証明。
clock_shiftのhm前提を`0≤開始margin+bs.count true`へ一般化（旧開始margin非負から変更）。clock_shift_supplyは開始margin≥−deficit、matched数=同じ時計のcompare数、available数≥2048*deficitからこの条件を内部導出。
clock_shift_readyはreadyのdistance0/balance4h/lag非負からmargin≥−4hを導き、available数≥8192hと区間長≥2k+2（lag≤k）でfreshShiftGuardへ接続。初期marginの前提は不要になった。
全体build成功（9117 jobs、exit 0）、標準公理のみ、build終了済み。
供給条件は保守的な十分条件で、実onlineの完走や期限をまだ保証していない。成功Watch.Runの継続、matched=compare（中断/shift/失敗なし）の実対応、入力供給と初期配置は残る。次は失敗出口/restartのassertionと、実イベントから成功区間または中断を構成する。shift実行/only=true・物理回路・全PALは未完。

### 最新追記：成功prefixを自動導出し時計→shiftを同じRunで合成

新規`GalilScaffoldChainPrediction.lean`（root import済み）。successful_prefixは同じ制御から成功した二列の共通prefix一意性。watch_phaseはWatch.Run/ready入口/距離≥4hから抽出列の二往復prefixを内部導出しphase4/unbrokenを返す。prefix文字列の外部仮定を除去。
margin_monoは同じ成功Watch.Runでmargin単調。clock_shiftはready入口、balance4h、初期margin非負/lag非負≤k、delay2048の同じavailable/compare対応、2k+2以上の成功有効tickからfreshShiftGuard=trueを導出。lagzero/距離≥4h/phase4はすべて内部導出。
全体build成功（9117 jobs、exit 0）、標準公理のみ、build終了済み。
残件は成功Watch.Runの実online到達と継続、初期margin非負（準備直後には負もあり得る）、実matched/clock対応、不一致restart・shift動作/only=true、正例期限、物理回路、全PAL。今回のclock_shiftを無条件の全online認識定理とは扱わない。次は失敗/負marginの枝と準備→watch到達条件へ進む。

### 最新追記：同じwatchのconsume列とphase/shiftを接続

新規`GalilScaffoldChainWatchTrace.lean`（root import済み）。Traceは同じverifier.Reads、終了control=Sweep.run、distance増分=列長、broken保存をまとめる。
internal_trace/outer_trace→tick_trace→run_traceで同じWatch.Runから実consume文字列を抽出。internal→outer順を保持、一tick最大2文字、全長≤2*tick数。
four_prefixはその列が二往復++suffixなら同じ終了controlのphase4/距離≥4h/unbrokenを導出。shift_from_traceはそれを同じWatch.Runのlag/margin収支へ渡してfreshShiftGuardを保証。
全体build成功（9116 jobs、exit 0）、標準公理のみ、build終了済み。
残る重要前提：抽出した成功列の先頭が二往復になること（現在はprefix Traceとして入力）、終了lagzero、準備balance=4h/ready配置。次は成功予測の決定性からprefixを自動導出し、clock_catchesと同じRunで合成する。実時計対応/失敗restart/期限/物理回路/全PALは未完。

### 最新追記：watch lag解消を比較時計のtick上界へ接続

新規`GalilScaffoldChainLag.lean`（root import済み、MatchClockを直接import）。tick_lagは同じWatch.Tickに対して非負保存とlag≤max(0,旧lag−非matched指示値)。matched tickもlagを増やさない。
run_lagは全Watch.Runでlag≤max(0,初期lag−count false)。catchesは非matched tick数≥初期lagからzeroを導出。
clock_catchesはdelay2048/任意初期clock位相、同長available列、matched数≤その時計のcompare数から、初期lag≤kかつ2k+2≤区間長なら終了lagzeroを証明。availableは任意で、compare数上界に時計不変式を使用。
全体build成功（9115 jobs、exit 0）、標準公理のみ、build終了済み。途中のimport/Bool count補題エラーは修正済み。
**連続して有効な成功watch区間の条件付き上界。** 実onlineでそのRunが存在・継続することとmatchedが同じcompareの部分集合である対応はまだ前提。中断/失敗restart、正例期限全体、物理回路、全PALは未完。次は同じWatch.Runのconsume列/phase4へ持上げ、時計対応と失敗時出口を統合する。

### 最新追記：内部catchと外側matchedの同tick収支

新規`GalilScaffoldChainWatch.lean`（root import済み）。Stateは実Verifier.Stateとlag/margin。Goodは同じverifier.canRight・右移動後readと予測token一致。
Internalはpositive lagなら成功consume+lag.dec、それ以外はidle。Outerはmatchedなしidle、lag非zeroならlag/margin.inc、lagzeroなら即時成功consume+margin.inc。TickはInternal→Outerなので一tick二consumeも表現。
run_balanceはdistance+lag−marginの厳密保存。prepared_balanceで準備収支とdistance0からその値=4hを導く。run_canonicalは同じlag/marginのCanonical保存。
shift_readyは同じRunに対し、終了lagzero/distance≥4h/phase4/unbrokenからmargin非negativeを内部導出しfreshShiftGuardへ接続。外側matchedなしという旧Catchの制限をこの成功watch射影では外した。
全体build成功（9114 jobs、exit 0）、標準公理のみ、build終了済み。
これはfresh watch/only=false・成功列で、失敗時restart/shift/fallbackやwatchの有効化・時計生成は未統合。Goodが実入力から成立すること、phase4/距離条件を同じWatch.Runへ持ち上げること、lagが期限内にzeroになる供給上界が次。実物理回路/全PALは未完。

### 最新追記：準備収支からcatch後のmargin/shift条件を導出

ChainCatch.canonical_natはCanonical counterでvalue=nなら実stack表現がofNat nと一致。prepared_marginは同じCredits.runの準備終了margin=lag−4*copy列長。
prepared_shift_guardはlag=4hの準備終了counterからmargin0を導き、別の仮想lagではなくfinal.lagでCatchを構成。
さらにphase4_consume/phase4_runでphase4保存、prepared_shift_afterでlag=4h+suffix.lengthへ一般化。二往復予測列++成功suffixの同じReads/Runから全lagを消費し、margin=suffix.length≥0を準備収支から導出、freshShiftGuard=trueへ接続。
全体build成功（9113 jobs、exit 0）、標準公理のみ、build終了済み。
残る前提：準備counter finalのrun一致、copy長h、実Reads、suffixも含む終了brokenfalse、全読出し長=初期lag。これらの実online供給・clockとouter matchedを伴う到達証明は未接続。Catchは外側比較なしの有効watch列、freshShiftGuardはwatch/only=false射影。次はouter matchedとのinterleavingと準備→watch実到達、失敗時restart条件。全PAL/期限/物理回路は未完。

### 最新追記：同じverifier成功実行のlag catch-upとfresh shift条件

新規`GalilScaffoldChainCatch.lean`（root import済み）。broken_preserved/run_unbrokenで終了brokenfalseから途中のbrokenfalseを導く。
Catchはwatchのpositive lag guard、verifier canRight、consume成功の前後brokenfalse、実lag.decを各tickで要求。catch_runは同じVerifyRun.Run n/終了brokenfalseから、lag=ofNat(n+k)→ofNat kのCatchを構成。
four_boundariesは同じ二往復Readsに適用し4h回Catch→phase4/境界4h/last3h/残lag k。caught_shift_guardはk=0、Canonical非負marginからfreshShiftGuard=trueを導く。
freshShiftGuardは**watch継続・only=falseの射影**で、brokenfalse/lagzero/phase4/margin非negative。全Scala mode/only/shift/replay条件を実controllerから導いたわけではない。
Catchは外側matched/shift/fallbackを挟まない有効watch tick列。初期lag=4hやmargin非負を実準備終了から得ること、途中外側matchedの扱い、時計供給は未接続。marginはこの区間で不変なので、次は準備収支margin=lag−4hとこのcatchを同じ状態へ接続する。
全体build成功（9113 jobs、exit 0）、標準公理のみ、build終了済み。正例期限/全PAL/物理回路は未完。

### 最新追記：同じverifier実行のphase4と格納内容からの供給

新規`GalilScaffoldChainVerifyRun.lean`（root import済み）。ReadsはcanRightと同じright後readを各stepで保証、Runは実Verifier.consumeを反復。realizeはReadsを同じ終了verifier/制御Sweep.runへ持ち上げる。
four_boundariesは二往復列のReadsから4h回の同じRun、終了verifier、period復元/距離境界4h/last3h/phase4を構成。
pairsは二進文字列をgap,letter列へ変換。stack_supply/queue_supplyは具体的右stack/FIFOのprefixからそのReadsを構成し未使用suffixを保持、個々のread一致とcanRightを格納内容から導出。現在はletter位置開始/全prefixが片方の供給元にある場合。
全体build成功（9112 jobs、exit 0）、標準公理のみ、build終了済み。
Runは有効consume呼出しの列で、時計/lagによる有効化はまだ前提層。二往復予測列と実入力prefixの一致、stack→queueを跨ぐ供給、gap位置開始、中断/不一致restart、period左移動guardの全trace化、物理FIFOは残る。次は供給/consumeとlag catch-up・marginを同じ実行で同期しcanShiftへ。全PAL/期限は未完。

### 最新追記：任意開始状態の往復と4境界/phase4

ChainSweep.forward_boundaryは任意開始distance/phase/境界の成功片道。round_tripはreadyと同じperiod/forward=trueを持つ任意Stateから、period復元、distance+=2h、boundary=distance、last=開始distance+h、phase=advancePhase×2、broken保存を証明。
bounce=(xs++[b])++(xs.reverse++[center])。four_boundariesは同じrunへbounceを二回連結し、readyからdistance=boundary=4h、last=3h、phase4、forwardtrue/brokenfalse、period復元を証明（h=xs.length+1）。
全体build成功（9111 jobs、exit 0）、標準公理のみ、build終了済み。
次はこの予測列/境界収支と実verifierの文字列・lag消費・marginへ接続し、phase4だけでなくcanShift全条件を導く。任意入力が一致するという主張ではなく、制御へ同じ予測列を与えた成功実行。中断/不一致restart/正例期限/物理回路/全PALは未完。

### 最新追記：成功した最初の往復でphase2へ到達

ChainSweepにrear/backward_interiorを追加。左向きplain走査はdistance+=長さ、右stackへ逆順積上げ、boundary/last/phase/broken保存でFIRSTに到達。
rear_after_lastで最初のLAST折返しTapeをその同じ逆向き入口へ接続。
first_round_tripはreadyから(xs++[b])++(xs.reverse++[center])を成功走査すると、periodがreadyの位置へ厳密に戻り、distance=boundary=2h、last=h、phase2、forwardtrue/brokenfalseを証明（h=xs.length+1）。
全体build成功（9111 jobs、exit 0）、標準公理のみ、build終了済み。
次は任意開始distance/phaseの往復補題へ一般化して4境界/phase4へ反復し、実verifier・不一致restart条件へ接続する。現在は一致列を与えたConsume制御射影で、未来の一致や物理機械実行を証明していない。正例期限/全PALは未完。

### 最新追記：最初のsemiperiod成功走査と境界更新

新規`GalilScaffoldChainSweep.lean`（root import済み）。runはConsume.consumeへsome文字を逐次供給する制御射影、frontはLASTまでの通常文字列のTape形。
forward_interiorは任意長plain区間の一致走査でdistance+=長さ、period左stackへ逆順積上げ、boundary/last/phase/broken保存、forward=trueを保証。
first_boundaryはready(center,xs,b)からxs++[b]を成功走査するとdistance=boundary=xs.length+1、last=reset、phase1、forwardfalse/brokenfalse、LASTから左移動したTapeになると証明。first_turn_legalはそのLAST左移動の非空stack guardをFIRST残存から導出。
全体build成功（9111 jobs、exit 0）、標準公理のみ、build終了済み。
これは予測と一致した入力列の制御実行で、未来の入力が必ず一致するとは主張しない。実verifierがこの列を読むこと・途中の不一致/restartは別接続。次は左向き走査→FIRST折返し→複数境界のphase/last収支とperiod移動合法性、同じverifier実行への対応。全PAL/正例期限/物理回路は未完。

### 最新追記：verifier右移動からconsumeの読出しを供給

新規`GalilScaffoldChainVerifier.lean`（root import済み）。既存InputHead.Head/PlaceHead上でheadRightは右stack優先、空ならincoming先頭を取る。Right/HeadRight関係とcanRightからのright_realizeを証明。gap=false→gap=trueはhead移動なし、gap=true→falseでheadRight。
stack_read/queue_read/gap_readで供給文字を明示。right_leftは合法な左移動の直後に右へ戻ると元状態と一致。
Verifier.StateはverifierとConsume.Stateを持ち、consumeは同じright後のreadをcontrolへ供給する。consume_realizeは右移動関係を保証、consume_agreesは距離+1/broken保存、consume_mismatchはbroken化。consume_gapは実letter focus→gapの読出しからgap予測との一致を導出。
全体build成功（9110 jobs、exit 0）、標準公理のみ、build終了済み。
incomingは論理FIFOリストで実Queue.work/Ref/heapのrefinementではない。canRightは依然入力条件。次は準備のverifier=center配置とこのRightをつなぎ、文字予測の一致/不一致・period移動合法性を回文/境界不変条件から導く。全watch反復、back最終outer matched合成、正例期限、物理回路、全PALは未完。

### 最新追記：watch consumeとlagゼロのouter matched分岐

新規`GalilScaffoldChainConsume.lean`（root import済み）。Stateはperiod/distance/boundary/last/phase/forward/broken。consumeは**verifier右移動後のseenを引数**に取り、一致時distance.inc→境界ならlast=旧boundary/boundary=新distance/phase増加/方向変更→新方向でperiod移動。不一致はbroken、他の投影状態は保持。
plain/first/last/mismatch各更新式、ready_symbol、ready_one（h=1の最初はLASTで左折・boundary1）、ready_long（plainで右進・phase0）を証明。
`outerMatched`はfresh watch/only=falseの外側処理。disabled不変、lag非zeroは旧Credits.step(false,true)、lagzeroはconsumeしmarginだけinc/lag不変。outer_zero_mismatch/outer_zero_creditsで失敗時もmargin増加・lag保持を保証。
全体build成功（9109 jobs、exit 0）、印字公理は標準のみ、build終了済み。
**まだverifier.right自体とseenの供給のrefinementはない。** readyはback終了Tape形を使うが全controllerのwatch状態の到達定理ではない。任意consumeに対するperiod移動guard/内容不変条件、回文候補からの一致保証、back最後のイベントとの合成が次。正例期限・中断・物理回路・全PALは未完。

### 最新追記：foundの同じ結果から準備全体の契約を構成

新規`GalilScaffoldChainReady.lean`（root import済み）。`Prepared`は実center read、PacedCopy、OUTPUT LEFT/h positive/末尾plainのassertion群、PacedBack、終了Canonical/lag非zero、全matched込み収支、period読出し列/終了walkerをまとめる。
`found_prepared`は同じSafeQuanta/found/Resultから候補hを取り、そのh長copy列とh+1長back列の任意matched配置に対してPreparedを構成。窓配置一致とCanonical/正radiusは依然前提。
**重要な再確認：Scala replay_start(ScaffoldCircuitGalil.scala 271–284付近)はradius.resetしてsearch.startする。よって正radiusを全Search開始の普遍不変条件と置かない。found時の正性は未証明で、ゼロ分岐も必要。**
PacedBack.doneのガードを`b=true → lag.zero=false`へ精密化。matchedがfalseならlagゼロでもconsumeは無効。`pace_back_quiet`は全matched=falseのBackをradius/lagの正性なしで構成する（終了credits不変）。
全体build成功（9108 jobs、exit 0）、標準公理のみ、build終了済み。次はback終端のmatched/lagゼロ分岐をwatch.consumeへ接続し、正radiusを安易に仮定して閉じない。guard/eventの実対応、pause/fallback、正例期限、物理回路、全PALは未完。

### 最新追記：start/copy/done/backの同一credit状態を合成

`ChainCredits.prepare_paced`は同じCopy nとLAST化TapeからのBack(n+1)、正でCanonicalなradius、start/doneのmatched Bool、copy/back各matched列から、同じ中間creditsを使うPacedCopy→doneのstep→PacedBackを構成する。
`prepEvents`はstart(false,sm)::copy列(true,b)++done(false,dm)::back列(false,b)。最終状態=この全列をstart radiusからrunした状態、最終Canonical/lag非zeroを保証。
`prep_value`はその全matched数Mから最終margin=radius−4*copy列長+M、lag=radius+M。start/doneイベントを落としていない。
全体build成功（9107 jobs、exit 0）、標準公理のみ、build終了済み。
次はfound_start_backで得た実center/OUTPUT/末尾assertion群をprepare_pacedへ一括接続し、radius正を実Searchの到達状態から導く。prepare_paced単体はCopy/Backとradius正を入力する接続定理で、実mode guard・pause/fallback・全online controllerを証明したわけではない。watch/consume、正例期限、物理回路、全PALは未完。

### 最新追記：copy/backと外側matchedを同じ実行へ同期

ChainCreditsにCopyState(answer/h/walker/period/credits)、copyStep、PacedCopyを追加。各tickは実copy操作とcreditsのdec×4→outer matched加算を一緒に行う。
`pace_copy`は同じChainPeriod.Copyと長さnのmatched Bool列からPacedCopyを構成。`pace_copy_balance`はその終了creditsのCanonical、margin=開始−4n+matched数、lag=開始+matched数を返す。
`PacedBack/pace_back`は同じBackと同長matched列を同期。最後のFIRST→右/watch tickでlag.zero=falseを実関係のガードとして要求し、入口Canonical/lag正からそれを導出する。back途中はmatchedによるlag.inc、periodへの作用なし。
全体build成功（9107 jobs、exit 0）、標準公理のみ、build終了済み。これは中断なし・各tick有効のモデル。pause/fallback/shiftは未対応。
次はcopy終了credits→doneのLAST化tick（outer matchedあり）→back入口を同じ状態で合成し、実Chain.startのradius正条件を導く。start tick自身のouter matchedも省略しないこと。watch/consume、正例期限、物理回路、全PALは未完。

### 最新追記：found→start/copy/backの集約と準備counter収支

`ChainPeriod.found_start_back`は同じSafeQuanta/found/Resultとwindow=stream.takeの配置仮定から、center.read=someを導出し、そのcenterのFIRST初期化、同じOUTPUT/h/walker/periodのCopy、末尾plain、OUTPUT LEFT/counter positive、LAST化後h+1回Back、読出し列/終了walkerをまとめる。
`GalilScaffoldChainCredits.lean`新規/root import。Counter実dec×4（copy時）→inc（matched時）の順序でmargin、matched時incでlagを更新。`run_value`はmargin=初期−4*copy数+matched数、lag=初期+matched数、`run_canonical`はCanonical保存。
`lag_not_zero`は初期radiusがCanonicalかつ正なら準備イベント列後lag.zero=false。これはpositive radiusと実guard列対応が前提で、実到達条件からの導出はまだない。
**境界注意：Scalaはback最後のtickでwatchに変えてから外側matchedを呼ぶ。lag.zeroならそのtick中にconsumeしperiod/verifier等がさらに動く。found_start_backの出口は外側matched前であって無条件のtick終了状態ではない。Creditsはpre-watch射影で、shift/fallback/ready-consumeは含まない。**
全体build成功（9107 jobs、exit 0）、標準公理のみ、build終了済み。次は実radius開始条件・copy/backとCreditsの同一イベント列への同期、watch入口/consumeへ進む。正例期限・実heap/bit回路・全PALは未完。

### 最新追記：period copyとLAST化後のbackを接続

新規`GalilScaffoldChainPeriod.lean`、root import済み。Tokenはblank/LEFT/plain(Fin3)/FIRST(Fin3)/LAST(Fin3)の11種、Tapeはdecoded二stack。DPのFin9を流用していない。
`Copy`はOUTPUT/h/Placeの更新とperiod.moveRight→writeを同時に行い、`copy_period`が同じCopyWalkから実行を持ち上げる。
`fill_stack`で書込みのstack内容、`back_exact`でFIRSTまで左移動し最後に右移動する実back traceを証明。
`copy_then_back`は非空CopyWalkから末尾plain文字、同じperiod copy、LAST化したTapeからn+1回のBackを同時に構成する。n回copy→doneでLAST化（別1 tick）→n+1回back。backの終了はFIRSTの一つ右で、FIRSTそのものではない。
全体build成功（9106 jobs、exit 0）、標準公理のみ、build終了済み。途中の長さ補題エラーは修正済み。
まだcenterのread/start assertionはcenter引数との対応が必要。margin/lag、mode更新・pause・外側matchedとのinterleaving、物理StackPoolは未接続。次はfound_copy_walkとcopy_then_backをChain.startの実center読出しへ結び、margin/lag収支とwatch入口へ進む。全PAL/正例期限は未完。

### 最新追記：foundから同じOUTPUT/h/walker実行を構成

`ChainAnswer.CopyWalk`はAnswerCopyと同じmoveLeft/incに、Place.left後のread=someを同期させた関係。
`copy_walk`はn<stream.lengthからその実行を構成し、読出し列=(stream.drop 1).take n、終了stream=stream.drop nを保証。
`found_copy_walk`は同じSafeQuanta/found/Resultから候補hを取得し、候補の4h+1≤窓長からwalker長条件を導出。reset→h counter、OUTPUT LEFT、counter positive、読出し列と終了walkerを一つの実行にまとめた。
前提`w=(stream p).take(span+1)`は実online配置不変条件として残る。Placeは論理射影で、物理InputHeadへの全trace持上げは未実施。
全体build成功（9105 jobs、exit 0）、標準公理のみ、build終了済み。次はperiodのFIRST/plain/LASTを含む書込み・rewindへ進む。Scala period alphabetは11種類で、DP TapeのFin9をそのまま使うと不足する点に注意。margin/lag・正例期限・全PAL機械は未完。

### 最新追記：OUTPUT読出しとh counterのcopy射影が完走

`GalilScaffoldChainAnswer.AnswerCopy`は各copy tickのfocus=8・left非空を要求し、実moveLeft/incを行うOUTPUT/h射影。
`answer_copy_exact`はhead=n≤h、denote=output hからn回の同じ実行を構成し、head0/focusLEFT、counter=ofNat(k+n)を証明。
`answer_copy_done`はhead=h>0、counter resetからh回でLEFTかつcounter.positive=trueを保証し、Scalaのdone assertionに必要なOUTPUT/h条件を満たす。
全体build成功（9105 jobs、exit 0）、印字公理は標準3公理のみ。build終了済み。
これはOUTPUT/h射影であり、walker非None・period書込み・margin/lagを含むChain.copy全体ではない。
**次はこの実行へwalker/periodを加えて、suffix候補からwalkerのh回左移動の有効性とperiod内容を導く。** 下の要約の「OUTPUTをh回読む」はこの追記で完了した部分。

### 再開用の要約（この節を現在地として優先）

- **完成していないもの：無条件のPAL ∈ PEG。** `Main.pal_in_peg_of_structured`に渡す具体的機械と全体の認識証明が残る。
- **直近で閉じたもの：** DP成功結果のOUTPUT内容に加え、ヘッド位置=hを公開。`GalilScaffoldChainAnswer.found_output`で同じSearch実行のfoundから最小候補・OUTPUTの末尾1・左移動可能性まで接続した。Chain全体を証明したわけではない。
- **直前の検証記録：** 全体`lake build`成功（9105 jobs、exit 0）。今回の引き継ぎではソースと記録を照合し、`git diff --check`を再実行して成功。全体buildの再実行はしていない。
- **次に実装するもの：** Scala `ScaffoldCircuitChain.scala`のcopy分岐を読む。`GalilScaffoldChainAnswer.lean`から、OUTPUTをh回左へ読んでLEFTに到達し、同じ実行でh counterがhになる証明へ進む。その後walker/periodの構築、margin/lagの条件を接続する。OUTPUTだけの補題をChain完成と数えない。
- **並行して残る接続：** stage出口の候補意味と反復契約、同一event列のclock引継ぎ、初期radius条件、grow/prepare/run中のfallback・restart、正例期限、実heap/bit回路・FIFO・packing。論理List層の証明を物理回路の証明と扱わない。
- **時計の不一致に注意：** LeanのDP上界は3186N+1683、stage安全性はdelay 2048を使用。Scalaの`buildOnline`側の旧FppCost由来の時計較正は未更新。最終構成で一致させる必要がある。
- 再開時は`GalilScaffoldChainAnswer.lean`、`GalilScaffoldTape.lean`、ScalaのChainを先に読む。巨大な履歴全体を読み直す必要はない。検証手順とScala入口は本書末尾の該当節を参照。

以下は新しい順の作業履歴。各項目の「次」「未接続」はその時点の記録であり、後続作業で解消済みの場合がある。現在地は上の要約と先頭の完了記録を優先する。

### 最新：chainへ渡すOUTPUTヘッド位置をResultへ追加・検証完了

Scala Chain.stepはanswer.focus=1から左へ読み、LEFTで終わる。旧DpCorrect.ResultはOUTPUT内容だけでheadを公開していなかった。
DpCorrect.Resultの成功枝をpc346∧tape11=output h∧pos11=hへ強化し、correct_loopのTracked.outputPosから証明。DpSuffix.Resultも同様に強化。末尾のtape等式は現在tape等式∧位置等式なのでconsumerの分解に注意。
新規ScaffoldChainAnswer.found_outputは同じSafeQuanta/Result/foundから最小候補、OUTPUT内容/head h/focus8/left非空を取り出す接続（root import追加）。
全体build成功（9105 jobs、exit 0）、ChainAnswerも検証済み、標準公理のみ。起動build終了済み。最初のbuildは途中追加したroot importのolean未生成で失敗し、終了後の再buildで新依存を生成して成功。Result変更による既存証明の破綻はない。
次はOUTPUTをh回左へ読みh counterを構成するChain.copy実行へ接続。walker/period/lag/marginと正例期限は未完。最終目標は未完。

### 最新：controller出口をsuffix回文候補へ接続

`DpSuffix.result_of_reverse`を任意の同じResultへ適用できる形で抽出しinitial_correctを再利用する形へ整理。
`SearchRun.quanta_suffix_result/quanta_window_result`がSafeQuantaの同じ終了Machineについてsuffix Result（最小候補・pc・単項OUTPUT）とfound/missed同値を同時保証。
窓はw.drop(w.length-(span+1))。DP入口のw.reverse.take(span+1)とList.take_reverseで厳密に一致する。
単体Lean検査・全体build成功（9104 jobs、exit 0）、標準公理のみ。diff check成功、起動build終了済み。wは論理入力窓の引数で、実center/online inputとの配置対応を新たに証明したわけではない。次はこのsuffix候補/OUTPUTをchainの入口条件へ接続し、stage反復と正例期限へ進む。初期radius/実制御/物理回路は未完。

### 最新：found/missedを同じDP結果へ接続

`SearchRun.TerminalLink`はrun中を除きfound iff pc346、missed iff pc≠346かつfinalStage。call→SafeCalls→SafeQuantaで保存。
`quanta_found_result`は同じ終了MachineのResultからfound iff Candidate存在を導出。
`quanta_missed_result`はmissed iff Candidate不在かつrun入口finalStage=true（finalStage保存を使用）。単なるmode列挙から候補意味との接続へ進んだ。
単体Lean検査・全体build成功（9104 jobs、exit 0）、標準公理のみ。diff check成功、起動build終了済み。CandidateはDP窓の条件で、最終PAL出力/chain正しさの証明ではない。次はstage存在・出口契約へこの意味を組み込み、同じイベント列での反復とclockを接続。初期radius/正例期限/物理回路は未完。

### 最新：run出口とwait処理を一つの分岐契約へ

`SearchRun.quanta_exit_mode`はrun入口から非run終了するSafeQuantaのmodeをfound/missed/wait/doubleに限定。
`StagePrepare.prepared_exit`は同じ準備/run traceから、必要ならwait prefixを実行し、found/missed/idle fallback/NextStageのいずれかを返す。terminal/direct doubleの場合は空wait traceで状態を保持し、waitの場合だけ供給条件を要求。
単体Lean検査・全体build成功（9104 jobs、exit 0）、標準公理のみ。diff check成功、起動build終了済み。mode found/missedとDP Resultの意味的対応（同じ終了Machine）はまだ未接続。次はこの対応、stage存在定理との合成、同じevent列の終了clock引継ぎ。全オンライン制御/初期radius/正例期限/物理回路は未完。

### 最新：NextStage契約から次の安全実行を構成

`StagePrepare.next_stage_safe`は前境界のSearchFinish.State sとNextStageを受け、**Double.Run s**から始まる次stageのdouble→PacedPrepared→SafeQuanta停止/Result/収支/終了Canonical/非負を構成。
runState(restoreState base s)0=sをquarter0から導き、別の仮想入口状態にはしていない。base側program/walkerは保持しprepareでresetする。
単体Lean検査・全体build成功（9104 jobs、exit 0）、標準公理のみ。diff check成功、起動build終了済み。時計生成列一致、double/prepare/runの予算列長、centerは依然入力条件。次はrunのfound/missed/wait/double各出口を分類して反復契約へまとめ、同じevent列と終了clockの対応を接続。実制御/初期radius/正例期限/物理回路は未完。

### 最新：stage→wait離脱から次stage入口をまとめて導出

`StagePrepare.NextStage lower n s clock`はmode.double/work=ofNat n/span0/quarter0/Canonical/debt-clock選言/clock範囲/StageSizeをまとめた契約。
`prepared_wait_next`は同じPacedPrepared→SafeQuantaのwait終了状態から、十分availableを持つWaitInterrupt.Run prefixを構成し、idle中断またはNextStageを返す。個別frame/reset/安全性補題を同じ終了状態へ集約した。
入口Canonical/非負は強化済みstage定理から渡せる。wait開始clockとavailable供給はまだ引数、前runの実event列終了clockとの一致は未接続。
単体Lean検査・全体build成功（9104 jobs、exit 0）、標準公理のみ。diff check成功、起動build終了済み。次はNextStageからlater_stage_safeへの接続と、run直接double/terminal分岐を含む反復契約。実制御/初期radius/正例期限/物理回路は未完。

### 最新：stage停止結果を次区間へ渡せる形に強化

`SearchRun.dp_quanta_safe/calibrated_quanta_safe`の戻り値に終了Canonical/非負を追加。既存quanta_safeのCanonical保存と消費prefix≤全advance予算から導出。
`StagePrepare.first_stage_safe/later_stage_safe`も同じ終了Canonical/非負を返すよう変更し、呼出し側を更新。**これらの戻り値の末尾は旧debt等式だけではなく等式∧Canonical∧非負。** 次wait入口で非負を仮定し直す必要がない。
`WaitInterrupt.double_reset`は同じRunのwait→double終了にspan reset/quarter0を保証。直接run→doubleとwait経由のreset条件がそろった。
全体build成功（9104 jobs、exit 0）、diff check成功、標準公理のみ。起動build終了済み。次は強化したstage結果→wait離脱→次stage/fallbackを一つの反復契約へまとめる。実制御/初期radius/正例期限/物理回路は未完。

### 最新：wait経由の次doubleへspanを受け渡し

`WaitInterrupt.run_stopped`は非wait入口ならRunが空で状態/clock不変と証明。`tick_span/run_span`は非idle終了ならstageSpan（doubleではwork）を保持し、`double_work`で終了work=wait入口span。
`StagePrepare.prepared_wait_double_work`は同じPacedPrepared→SafeQuanta→WaitInterrupt.Run→doubleから次work=準備入口spanを導く。直接run→doubleとwait経由の両方で受け渡しがそろった。
単体Lean検査・全体build成功（9104 jobs、exit 0）、標準公理のみ。diff check成功、起動build終了済み。まだ全stage存在定理の戻り値にwait入口Canonical/非負やspanなどをまとめて反復する接続は未完。wait→doubleのreset/quarter条件も同じRunへ追加する必要あり。実制御/初期radius/正例期限/物理回路は未完。

### 最新：fallback込みwaitの供給量付き離脱

`WaitInterrupt.tick_debt/run_debt`でfallbackによるmode変更も含めdebt=開始値−同じ実行の比較数を証明。
`supplied_exit`は初期debt=k、available数≥2048*(k+1)から安全Run prefixでmode≠waitを構成。Outcomeよりidle中断かdouble。列末までwaitの枝を収支と時計供給量の矛盾で排除。
これは保守的なavailable-tick上界で、壁時計や全オンラインstep上界ではない。scopeは引き続きscan/chain idle/非replayのSearch射影。
単体Lean検査・全体build成功（9104 jobs、exit 0）、標準公理のみ。diff check成功、起動build終了済み。次はstage停止後のwait入口条件/保持spanとこの離脱を合成し、double反復またはfallback本体へ接続。初期radius/実制御refinement/正例期限/物理回路は未完。

### 最新：fallback込みwaitを有限イベント列へ拡張

`WaitInterrupt.Run`は各wait入口assertion、tick（wait→advance→fallback）、実clock更新を含む。
`run_prefix`は任意有限(available,equal)列から最初のwait離脱まで（または列末まで）のRunを構成し、used/rest分割、Canonical、clock範囲、idle/非負wait/debt-clock条件付きdoubleのOutcomeを返す。restが残れば終了mode≠wait。
`run_clock`で終了clockが同じusedイベント列をMatchClockへ通した結果と厳密一致。
単体Lean検査・全体build成功（9104 jobs、exit 0）、標準公理のみ。diff check成功、起動build終了済み。scopeはscan/chain idle/非replayのSearch射影。次は十分なavailable供給で「列末wait」の枝を排除し、zero到達/中断の二択を証明、stage/FPP fallbackへ渡す。初期radius/正例期限/物理回路は未完。

### 最新：fallback込みwait tickを分類

新規`GalilScaffoldWaitInterrupt`（root import済み）。scan/chain idle/非replayのSearch射影。Chain.canShiftはwatchを要求するのでidleではfalse（Scala確認）。tickはwaitStep→compareによるadvance→不一致compareならmode.idle。
`safe_tick`は入口wait/Canonical/非負/clock範囲からassertion安全・終了Canonicalと、idle中断 / 非負wait継続 / debt-clock条件付きdouble移行の三分岐を証明。
`fallback_idle`と`uninterrupted`で中断と旧モデルへの一致を明示。idleをwaitの続きとして扱わない。
単体Lean検査・全体build成功（9104 jobs、exit 0）、標準公理のみ。diff check成功、起動build終了済み。**有限イベント列で最初の中断/離脱までを構成する反復関係は未実装。fallbackのFPP/heads/g.mode更新全体・replay禁止assertionの到達不変条件も未接続。** 次はこの三分岐をイベント列へ持ち上げる。初期radius/正例期限/物理回路は未完。

### 最新：wait guardのScala対応範囲を確認

Scala ScaffoldCircuitGalil.scala 141–170を再読。search.tickのenabledはscanning && !chainActive && search.active（availableに依存しない）。比較時計はdispatch.scan && available。advanceは比較後Search.activeとchain.idleで判定。
`Wait.active/searchEnabled/advanceGuard`をdecoded定義し、`idle_scan_wait_guards`でscan/chain idle/mode.waitならsearch enabled=true、waitStep後（double移行含む）のadvance guard=available&&clock1を証明。`not_scanning_guards`でscan外は両方false。
**重要：同ファイル後段fallbackはsearch.modeをidleへ上書きする（190行付近）。wait供給定理を無条件のオンラインwait継続・停止と扱ってはいけない。scan継続/chain idle/非fallback区間の不変条件、または中断を含むモデルが必要。** chain active→idle/restartのtickも単純pause扱い不可。
単体Lean検査・全体build成功（9103 jobs、exit 0）、標準公理のみ。diff check成功、起動build終了済み。次はイベント列を実制御へ接続する前にfallback/restartによる中断の扱いを組み込む。初期radius/正例期限/物理回路は未完。

### 最新：wait→doubleの次イベントを同じ列に固定

`Wait.clock_sequence_double`は2048k availableを供給するbsに1イベントextraを追加したevents=bs++[extra]を用いる。
zero到達prefix nに対しn<events.length、Runのadvance列=events.take nの生成列を保証。double dispatch末尾のavailabilityは別引数ではなくevents[n]!から読む（範囲内を証明済み）。同じprefix終了clockを使用しdouble入口条件を保持。
単体Lean検査・全体build成功（9103 jobs、exit 0）、標準公理のみ。diff check成功、起動build終了済み。全eligible・各dispatch有効というモデル条件は依然残る。終了clockはprefix時計から次イベントを1回更新した定義で、元列take(n+1)との補題化は未実施。次はオンラインenabled/eligible条件とstage間接続。初期radius/正例期限/物理回路は未完。

### 最新：wait prefixの終了時計からdouble入口へ合成

`Wait.clock_prefix_double`がclock_prefix_zeroの同じprefix終了clockをDouble.enter_boundaryへ渡し、次の有効wait dispatch→advance後のdouble入口条件をまとめる。
次work=wait開始span、span reset、quarter0、Canonical、debt≥0または(debt≥−1/clock reset)、clock範囲を保証。
前提はdebt=k、2048k available、prefix全eligibleなど従来の供給条件。**次の有効tickのavailable/eligibleは別引数で、元bsの次要素との一致や途中pauseのrefinementはまだない。**
単体Lean検査・全体build成功（9103 jobs、exit 0）、標準公理のみ。diff check成功、起動build終了済み。次は同じオンラインevent列でstage終了→wait prefix→次double stageを組む。初期radius/実guard/正例期限/物理回路は未完。

### 最新：wait停止prefixと同じ時計位相を取得

`AdvanceClock.advances_take`でイベントprefixの生成advance=全生成列のprefix。
`Wait.clock_prefix_zero`はclock_reaches_zeroのusedを元available列bsのtake nへ戻し、n≤bs.length、同じprefixから生成するRun、zero/Canonical/span保存と、同じbs.take nを実行した終了clockの1..2048を同時保証。
単体Lean検査・全体build成功（9103 jobs、exit 0）、標準公理のみ。diff check成功、起動build終了済み。次はこの終了clockをDouble.enter_boundaryの引数へ渡し、次の有効wait dispatchでdouble入口条件を合成する。実eligible/available供給・初期radius・正例期限・物理回路は未完。

### 最新：waitへのadvance供給を比較時計から導出

`AdvanceClock.advances_append`はイベント区間分割に対し前区間終了clockを後区間へ渡す厳密な生成列等式。
`eligible_compares`で全eligibleならadvance数=比較数、`eligible_supply`で有効clock位相からk*delay個のavailable tickがk advances以上を供給すると証明。
`Wait.clock_reaches_zero`はdelay2048、初期debt=k、available数≥2048kから安全wait prefixのzero到達/span保存を構成。「advanceが十分」という前提は時計供給から導出した。
単体Lean検査・全体build成功（9103 jobs、exit 0）、標準公理のみ。diff check成功、起動build終了済み。**全eligibleはモデルの入力条件で、実active/chain idleの証明ではない。available供給と待機prefix終了clockへの接続は未完。** 次は実イベントprefixへ対応させ境界の位相を引き継ぐ。初期radius/正例期限/物理回路も未完。

### 最新：waitの安全なprefixでdebtゼロへ到達

新規`GalilScaffoldWait`（root import済み）。Runは非zero waitの実waitStep→advanceを繰り返し、各入口のnegative禁止assertionを含む。
`reaches_zero`はwait入口Canonical/非負とadvance列count≥入口debt値から、列のprefix usedで同じwait実行がzeroへ到達することを構成。Canonicalとspanを保持し、残り列restを返す。
ゼロ到達後をwait実行として消費しない。次の有効tickのwait_enter/enter_boundaryへ渡す設計。
単体Lean検査・全体build成功（9103 jobs、exit 0）、標準公理のみ。diff check成功、起動build終了済み。**十分なadvanceの供給は前提、実clock/eventからの待機時間上界は未接続。** 次は停止prefixのclock位相を追跡してdouble境界へ合成し、stage反復へつなぐ。実event/初期radius/正例期限/物理回路は未完。

### 最新：実doubleから次doubleへ倍増とreset条件を導出

`Double.span_of_run`は任意の同じRunについてspan=ofNat(n+2*length)を証明。
`StagePrepare.double_stage_next_size`はDouble.Run→PacedPrepared→SafeQuanta→doubleの同じtraceから次work=ofNat(2*double列長)とStageSizeを導出。中間span=2nは外部前提ではなくなった。
`SearchRun.double_reset_of_quanta`はrunからdoubleへ終了するSafeQuantaについてspan=reset/quarter0を保証。DoubleResetをfinish/SafeCalls/advanceで保存する。
単体Lean検査・全体build成功（9102 jobs、exit 0）、標準公理のみ。diff check成功、起動build終了済み。次は同じ終了traceのclock/debt境界条件を合成し、wait経由も含めstage反復へつなぐ。実event/初期radius/正例期限/物理回路は未完。

### 最新：準備span保存と次doubleの数値条件

`PreparePaced.paced_span/prepared_span`が任意advance込み準備実行でspanの厳密保存を保証。
`StagePrepare.prepared_double_work`は同じPacedPrepared→SafeQuantaからdouble終了work=準備入口spanを導く。
`StageSize lower n := 8≤n ∧ n%4=0 ∧ 4*lower≤n`。初回8*max(lower,1)で成立し、倍増で保存。`prepared_double_size`は入口span=ofNat(2n)を持つ実準備/run traceにこの数値条件を接続。
単体Lean検査・全体build成功（9102 jobs、exit 0）、標準公理のみ。diff check成功、起動build終了済み。まだspan=2nを前区間から自動取得する全stage合成やwait経由の反復は未完。double入口span reset/quarter0/clock-debtも同じtraceへまとめる必要がある。実event/初期radius/正例期限/物理回路は未完。

### 最新：run終了時のstage span受け渡し

`SearchRun.stageSpan`はdoubleならwork、それ以外ならspan。`finish_frame`→`safe_calls_frame`→`safe_quanta_frame`でfinalStageとstageSpanを厳密に保存する。
`double_work_of_quanta`はrun入口からdouble終了なら終了work=入口spanを導く。run終了後にspanがresetされるため、単純なspan保存ではなく実workコピーを追跡する。
単体Lean検査・全体build成功（9102 jobs、exit 0）、標準公理のみ。diff check成功、起動build終了済み。次は準備終了spanの保存とこのframeを合成し、stage間の倍増/4倍数/lower上界を接続。double入口span reset/quarter0とclock/debt境界の同じ実行への合成も必要。実event/初期radius/正例期限/物理回路は未完。

### 最新：run/wait→double境界のdebt/時計条件

`Double.enter`はScalaのwork=span/span reset/quarter0/mode.double。`finish_enter`は非final失敗PC347/debt.zeroから一致、`wait_enter`はwait/zeroから一致。
`enter_boundary`はzeroのCanonical debtと有効clockから、double更新後の実形式advance（available && clock=1 && eligible）を適用し、work/span/quarter/Canonical/次clock範囲と **debt≥0 または(debt≥−1かつ次clock=2048)** を導く。
`wait_positive_advance`はwait入口Canonical/非負/非zeroからwait継続、advance後非負、入口assertion安全を保証。
単体Lean検査・全体build成功（9102 jobs、exit 0）、標準公理のみ。diff check成功、起動build終了済み。次はこれら境界定理をstage終了状態とlater_stage_safeへ合成し、stage間のspan/lower不変条件を接続する。実event eligibility/初期radius/正例期限/物理回路は未完。

### 最新：後続stageのdouble→prepare→安全なDP停止を合成

`StagePrepare.later_stage_safe`を追加。非reset clockのadvance上界、実double/prepare tick数、calibrated runBudgetを合成しSafeQuanta停止prefix/Result/全debt収支を構成する。run入口debt予算・stage長上界は内部導出。
前提：double入口work=n/span0/quarter0、4|n、n≥8、4lower≤n、Canonical、clock範囲、予算列長と実時計生成列の一致。
入口debt条件は **debt≥0 または(debt≥−1かつclock=2048)**。Scalaはrun/wait→double更新後にもadvanceMatchを行い得るため、入口非負だけでは境界を落とす。リセット直後の時計上界で−1分の余裕も証明した。実到達状態がこの選言を満たす証明はまだ必要。
単体Lean検査・全体build成功（9102 jobs、exit 0）、標準公理のみ。diff check成功、起動build終了済み。次はrun/wait→double境界のclock/debt不変条件と、初期radius・実event guardへの接続。物理回路/正例期限/全PAL機械は未完。

### 最新：double終了から同じ状態のprepareへ接続

`StagePrepare.restoreState`はSearchFinishのcontroller fieldsを共有Stateへ戻しprogram/walkerを保持。`restore_runState`で射影の往復一致。
`double_then_prepare`はquarter0/work=n/span0/4|nからDouble.Run→PacedPreparedを構成し、正確なDP入口、終了quarter0、Canonical、debt=開始値+n/4-(double列++準備列).countを保証する。
`TimingCost.later_stage_ticks`はn≥8、4lower≤n、m≤2n+1からn+2lower+2m+7+runBudget(2n)≤63*(2n)。
double_then_prepareの単体検査・全体build成功（9102 jobs、exit 0）、標準公理のみ。diff check成功、起動build終了済み。次はlater_stage_advancesの全advance≤(2n)/8と収支を合わせ、後続SafeQuantaを構成する。入口debt0/初期lower条件/実clock-event対応は別途必要。

### 最新：後続doubleのquarter/advance収支と完走

新規`GalilScaffoldDouble`（root import済み）。SearchFinish.State上で旧quarter=3を検査し、work.dec/span.inc×2/quarter=(q+1)%4/debt.incを実行後、外側advance減算。
`complete`はwork=ofNat as.lengthから同じas列のRunを構成し、work0/span+2*length/mode.doubleを保証（終了zero dispatchはprepare側）。
`balance`は4*debt+quarterの厳密な収支、`completed_credit`は開始quarter0・回数が4の倍数なら終了quarter0/debt+length/4-countを証明。`canonical`はdebtのCanonical保存。
単体Lean検査・全体build成功（9102 jobs、exit 0）、標準公理のみ。diff check成功、起動build終了済み。次はdouble終了の同じ状態からprepareへ接続し、後続stageのclock予算と合成する。実オンラインguard/初期radius/正例期限/物理回路は未完。

### 最新：初回grow→prepare→安全なDP停止を一つに合成

`StagePrepare.first_stage_safe`が共有PacedGrowing/PacedPreparedから、`runState p quarter`と同じp.programを入口とするSafeQuantaの停止prefix、正しいDP Result、全stageの厳密なdebt収支を構成する。
**run入口debt予算とstage時間上界を外部前提から除去**。区間長からfirst_stage_ticks、時計advance総数からfirst_stage_barrier、準備収支からrun入口の残り予算を導く。
残る前提：初期mode/work/span/debtとCanonical、3radius≤5r、各区間の予算長、as++bs++csがdelay2048/reset時計の生成列と一致すること。quarterは引数（初回実装では0）。runStateは共有フィールドの射影で物理回路の証明ではない。
単体Lean検査・全体build成功（9101 jobs、exit 0）、標準公理のみ。diff check成功、起動build終了済み。次は実オンラインguard/eventの対応・初期radius契約と、後続double/wait stageを扱う。全PAL機械/正例期限/heap-bit-FIFO接続は依然未完。

### 最新：時計とDPの予算不一致を解消

`SearchRun.dp_quanta_safe`のhaを「3186*w.length+1683≤64*as.length」へ一般化した（旧50*m+27の等式ではない）。scheduled_correctから任意十分予算の実行を構成する。
`calibrated_quanta_safe`はw.length≤span+1から、TimingCost.runBudget span長のadvance列で安全な停止prefixと正しいResultを構成する。入口Canonical/debt予算はまだ前提。
`TimingCost.first_stage_ticks`は実grow/prepareコスト `max(r,1)+2r+2m+7` とrunBudgetの和≤63*(8max(r,1))をm≤span+1から導出。
単体Lean検査・全体build成功（9101 jobs、exit 0）、標準公理のみ。diff check成功、起動build終了済み。次は準備終了StateをSearchFinish.Stateへ写し、全stageのadvance列を分割して入口debt予算を導く。実guard対応と初期radius契約は未接続。

### 最新：advance込みrun実行の存在・停止を実DPから構成

`SearchRun.guarded_split`/`guarded_stopped`でGuardedRunを分割し、`realize_quanta`で64呼出しごとにadvanceを挿入するRunQuantaを構成。
与えたadvance列asのprefix usedだけを実行し、as=used++rest、同じ終了Machine、mode≠runを保証。run終了後の外側tickを架空のrun実行で埋めない。
`dp_quanta_safe`は実DPのquantum64_correctから、安全な外側tick実行・正しいResult・厳密なdebt収支を同時構成する。
予算列長は50*w.length+27。初期Canonicalと初期debt値≥as.count trueは前提。実行列の存在/停止は前提から外れた。
単体Lean検査・全体build成功（9101 jobs、exit 0）、標準公理のみ。diff check成功、起動build終了済み。次は共有準備状態からSearchFinish.Stateへの対応と全stage時計予算の接続。
注意：TimingCost.runBudgetはceilのより小さい予算なので、50*m+27を使うこの定理とそのまま同一視しない。scheduled_correctから任意十分予算への一般化が必要。

### 最新：run外側tickのadvance込み安全性

`SearchRun.RunQuanta`/`SafeQuanta`を追加。各tick入口mode.runを要求し、64回のCalls/SafeCallsの後に外側advanceを1回適用する。非run移行後の別dispatchをrun扱いしない。有効tickのみ（pauseの拡張は未実装）。
`quanta_safe`は既存RunQuanta、初期Canonical、初期debt値≥全advance数から全SafeQuanta、終了Canonical、厳密なdebt減算収支を証明する。
単体Lean検査・全体build成功（9101 jobs、exit 0）、標準公理のみ。diff check成功、起動build終了済み。**RunQuantaの存在/停止・実clockからの全advance予算・共有PrepareControl.Stateとの接続は未実装。**
次はGuardedRunの64呼出しごとの分割とfinish/debt差替えを扱い、mode.runが続く区間だけをRunQuantaへ構成する。終了tick以降をrun tickで埋めないこと。

### 最新：初回準備終了のdebt assertionを時計上界から導出

`StagePrepare.first_prepared_safe`を追加。共有PacedGrowing→PacedPreparedの実行と正確なDP入口を構成し、終了debtのnegative≠trueを導出。
前提は初期work=max(r,1)/span0/debt=-radius、Canonical、3radius≤5r、advance列がdelay2048/reset時計の生成列と一致すること、イベント長≤63*(8max(r,1))、各区間長。
終了debtのCanonicalは`paced_growing_canonical`と`PreparePaced.spend_canonical`で初期Canonicalから導く。終了debt収支・非負性を外部前提にはしない。
単体Lean検査・全体build成功（9101 jobs、exit 0）、diff check成功、標準公理のみ。起動build終了済み。**実イベントguard・初期radius契約・実tick長上界はまだ前提。run中のadvanceや終了時assertionは未接続。**
次はrun区間の外側tick（quantum64内の呼出しとの区別）とadvanceをモデル化し、全stageの時計上界を使用する。

### 最新：共有grow→prepare全体のadvance収支を合成

`GalilScaffoldStagePrepare.PacedGrowing`はpositive grow更新後にadvance減算する共有State実行。
`paced_growing_complete`でwork0/span+8g/debt+2g-countを証明。
`paced_grow_then_prepare`はその同じ終了Stateから`PacedPrepared`へ接続し、
DP初期config/run/done=false/finalStageと **debt値=初期値+2g-(grow列++準備列).count true** を同時保証する。
prepare開始dispatchのadvanceも含む。単体Lean検査・全体build成功（9101 jobs、exit 0）、標準公理のみ。diff check成功、起動build終了済み。
実compare/active/chain guardとの対応・run区間のadvance・初期radius・double quarterは未接続。
次はこの共有実行の収支をAdvanceClockへ接続する。下記の共有Growing未実装という記述は履歴となった。

### 保存後の継続：prepare開始tickのadvanceも接続

`GalilScaffoldPreparePaced.prepared_interleave`を追加。任意の`PreparedRun lower center s n t`と長さnのadvance列から、prepare dispatch直後のadvanceも含む`PacedPrepared`を構成する。
終了状態は厳密に`{t with debt := spend as s.debt}`。既存prepare_completeの証人へ直接適用でき、最初の1 tickを落とさない。
単体Lean検査・全体build成功（9101 jobs、exit 0）、diff check成功、標準公理のみ。起動build終了済み。実guard対応、共有Growingのadvance、runStep非負性は未解決。
次は共有Growingのcredit/advance収支とこの実行を合成する。

### 引き継ぎ確定版（2026-09-14、以下の履歴より優先）

今回の依頼は進捗保存。証明の追加はせず、現物を確認して保存した。
**全体 `lake build` 成功（9101 jobs、exit 0）、`git diff --check` 成功。**
最新の `GalilScaffoldPreparePaced` もroot import済み。今回起動したbuildは終了済み。
既存linter警告はある。commitなし。dirty/untrackedファイルも引き継ぎ対象であり、GitのHEADだけでは再現できない。

現在地を短く言うと、**実FPP/DPの正しさ・線形時間上界と、共有controllerのgrow→準備→DP入口までの局所接続がある。オンライン機械全体の正しさはまだない。**

- `GalilDpCost.initial_correct_cost`: 同じDP実行のResultと命令数 `3186*N+1683` 以下。
- `GalilScaffoldPrepareControl.prepare_complete`: resetからLOWER/SOURCEを準備し、`2*r+2*m+7` tickで正確なDP初期config、mode.run、done=falseへ到達。`m=min(stream.length,span+1)`。
- `GalilScaffoldStagePrepare.grow_then_prepare`: 共有Stateのgrow guardから上記へ接続。advanceなしでspanに8*g、debtに2*gを加算。
- `GalilScaffoldPreparePaced.interleave`: 準備Runへ任意advance列を挿入でき、終了状態のdebt以外は厳密に同じ。実オンラインguardとの対応は未証明。

**次に実装する接続（未実装）**:

1. `PreparePaced.interleave`を`PrepareControl.prepare_complete`へ適用する。prepare自身の1 dispatchにも外側advanceが起こり得るため、本文Runだけに適用して1 tick落とさない。
2. `StagePrepare.Growing`へ同じ共有State上のadvanceを挟み、grow credit込みで `debt=初期値+2*g-advance数` を導出する。既存`GalilScaffoldGrow.paced_stage`は射影モデルなので、そのまま全Stateの実行とは扱わない。
3. `GalilScaffoldAdvanceClock`のイベント列・stage長上界へ接続し、実runStep入口のdebt非負条件を導く。初期radius条件と実active/compare/chain guardは別途必要。

その後もdoubleのquarter更新、全controllerの進捗・正例期限、実heap/bit回路・固定割当・FIFO、packing、具体的StructuredMachineのPAL正しさが残る。
`Main.pal_in_peg_of_structured`は条件付きのまま。完成率や残り時間を裏付けなく述べない。
新DP上界に対応する時計候補はstage係数63・delay2048。**Scalaの`GalilClock.derive`の旧コスト表は未更新**であり、現実装が新上界で検証済みとは言えない。

まず上記4ファイルと`GalilScaffoldAdvanceClock.lean`、Scalaの`ScaffoldCircuitSearch.scala`/`ScaffoldCircuitGalil.scala`を読む。
以下の多数の「最新」「次」は逆時系列の履歴で、古い未完了記述はこの節で上書きする。サブエージェントは使わない。

### 最新：共有準備Runに外側advance減算をinterleave

新規 `GalilScaffoldPreparePaced`：tick_rebaseで全準備Tickがdebt差替えに不変と証明。
PacedRunは準備Tickの後にafterAdvanceでdebt.decする、Scala順序の共有State実行。
interleaveは任意Run x bs yと同長advance列asから、同じbs.zip asのPacedRunを構成し、
終了状態は厳密に{y with debt := spend as c}。他の全フィールドを保持する。
spend_valueでdebt値=開始値-as.count true。任意Bool pause列にも適用可能。
単体Lean検査成功、標準公理のみ。root import済み。

**advance列が実active/compare/chain条件を満たすことは依然別。**
この準備Tickはdebtを読まないため全符号で成立するが、runStep/waitのnegative禁止まで解決したわけではない。
次はprepare_completeの実行へ適用し、grow中のcredit更新＋advanceも共有Stateでinterleave、
初回stage収支とAdvanceClockへ接続。物理heap/bit/FIFO・正例期限・最終PAL機械は未完。

### 最新：共有Stateのgrow終了guardからprepareへ接続

新規StagePrepare：growStepは共有PrepareControl.Stateのwork/span/debtを更新。
Growingはpositive guardのg tickを実行し、mode.growかつpositive(work)=falseで終わる。
growing_completeはwork0/span=ofNat(span+8g)/debt値+2gを保証。
grow_then_prepareはその同じ終了Stateからprepare_completeへ接続し、正確なDP初期状態、
run/done=false/finalStageとdebt値+2gを保証。準備部分は2r+2m+7 tick、grow部分g tick。
単体Lean検査と全体build成功（9100 jobs、exit 0）、公理propext/Quot.sound。root import済み。
実行中プロセスなし。git diff --check成功。

**advance割込みなしの実行であり、実オンラインstage全体の証明ではない。**
次は共有Stateのdebtだけを外側でdecする操作をGrowing/準備Runに挟み、
Counter収支とAdvanceClockのイベント列を接続する。初期radius条件・doubleのquarter更新、
物理heap/bit/FIFO・正例期限・最終PAL機械は未完。

### 最新：初期prepare更新を含むcontroller準備完走

PrepareControl.prepareはScalaのreset320/walker=center/work=lower/LOWER LEFT-right/mode.lower/final=falseを実装。
PreparedRunはこの1 dispatchと既存Runを合成する関係。
prepare_completeはspan=ofNat spanを前提に、任意旧programから2r+2m+7 tickで
正確なDP初期config/run/done=false/debt保存/finalStageを保証する。
LOWER入口のreset/LEFT条件はprepareの定義から導出し、外部前提ではなくした。
単体Lean検査と全体build成功（9099 jobs、exit 0）、公理propext/Quot.soundのみ。
実行中プロセスなし。git diff --check成功。

PreparedRunはprepareの呼出しを記録するが、**grow/doubleの終了guardがその呼出しに到達する証明は未接続**。
次はgrowの共有状態へのliftとprepare呼出し境界、外側advanceの割込みを接続。
reset/counter/Placeは論理解釈で、heap/bit/FIFOや正例期限・最終PAL機械は未完。

### 最新：準備4区間の共有controller完走を合成

PrepareControl.prepared_runがlower入口から同じ共有StateのRunで
**2*lower+2*w.length+6有効tick**後、mode.run、program.config=ScaffoldPreload.initial w lower、
done=false、debt保存、finalStage iff stream終端を保証する。
w=(Place.stream s.walker).take(span+1)。入口はwork=ofNat lower/span=ofNat span、
LOWERがLEFT/right設定後、他テープreset。lower_load/lower_homeのwalker/SOURCE保存を強化し、
source_run_frameでSOURCE区間中のLOWER保存、run_span/run_appendを追加して合成した。
単体Lean検査と全体build成功（9099 jobs、exit 0）、公理propext/Quot.soundのみ。
実行中プロセスなし。git diff --check成功。

**初期prepare tick・grow・外側advanceMatchはまだ含めない。**
次はgrow終了のprepare実更新（reset/walkerコピー/work lower/LEFT right）を入口条件へ接続し、
外側advanceによるdebt減算と任意pauseを持つ準備Runへ拡張する。
DP予算との合成は最終configの完全一致を使える。物理heap/bit/FIFO・正例期限・最終PAL機械は未完。

### 最新：SOURCE Copy/Homeを共有controller Runへlift

PrepareControl.source_copyはPlace.Copyの同じn tickを共有Runへ持ち上げ、mode.home、
正確なwork=ofNat残量/walker/Tape/finalStageを保持。
source_homeはRewindを同じn tickで実startRunへ持ち上げ、mode.run、SOURCE最終Tape、
pc320/done=false、finalStage保存を保証。
単体Lean検査と全体build成功（9099 jobs、exit 0）、公理propext/Quot.sound。
実行中プロセスなし。git diff --check成功。

4区間のliftがそろった。**まだ全区間合成定理はない。**
次はRun.append、span/walkerのLOWER区間保存、SOURCE区間のLOWER保存などの
phase-specific frameを追加し、lower_ready/place_readyの実行を同じState上で合成する。
既存run_frameは7/10の両方を除外するため、SOURCE処理中の10保存をそのまま導けない点に注意。
正例期限・外側advanceMatch・物理heap/bit/FIFO・最終PAL機械は未完。

### 最新：LOWERの実行を共有controller Runへlift

PrepareControl.lower_loadは既存Lower.Load nを同じn有効tickのRunへ持ち上げ、
lower_home到達・同じwork/LOWER最終Tapeを保証。
lower_homeは既存Rewind nを同じn有効tickでcopy入口へ持ち上げ、LOWER最終Tape、
実work=inc span、SOURCEのLEFT/right設定を同じ共有Stateで保証する。
単体Lean検査と全体build成功（9099 jobs、exit 0）、公理propext/Quot.soundのみ。
実行中プロセスなし。git diff --check成功。

次はPlace.Copyを共有StateのcopyBit/copyEndへlift（workはofNat表現を使いzero/dec対応）、
SOURCE RewindをsourceLeft/startRunへlift。その後Run.appendとspan/debt/frame保存で
LOWER→SOURCE→runをつなぎ、具体初期状態から完走証明を得る。
外側advanceMatch・grow・物理heap/bit/FIFO・正例期限・最終PAL機械は未完。

### 最新：準備4モードの共有controller状態を定義

新規 `GalilScaffoldPrepareControl` はmode/program/work/span/debt/walker/finalStageを同じStateに持つ。
TickはlowerBit/lowerEnd/lowerLeft/beginCopy/copyBit/copyEnd/sourceLeft/startRunとdisabled identity。
beginCopyで実work=inc span、copyでPlace.read/left、homeでprogram.start320を更新する。
左移動の非空guardを明示。run_debt/run_frameで任意Tick列がdebtとテープ7/10以外を保存すると証明。
単体Lean検査と全体build成功（9099 jobs、exit 0）、公理propext/Quot.sound。root import済み。
実行中プロセスなし。git diff --check成功。

**この新しいRunで任意入力の準備が完走する証明はまだない。**
次は既存Lower.Load/RewindとPlace.Copyをこの共有StateのRunへliftし、phase間で
同じwork/program/walkerが受け渡されることを示す。grow/advance/heap/bit回路は別。
この定義追加を実controller全体の完成と報告しない。正例期限・最終PAL機械は未完。

### 最新：walker準備の全12テープ初期状態とDP開始を接続

SourceReady.prepare_programはreset後にLOWER、SOURCEのLEFT/right設定、同じPlace.Copyと
Rewindを合成し、最終全状態=ScaffoldPreload.initial w lowerを証明。
w=(stream p).take(span+1)。テープ基本操作は3*(lower+w.length)+8。
prepare_then_dpはこの準備結果からstart320を通じ、3186*w.length+1683有効tick以上の
任意スケジュールで正しいResult/doneへ接続する。コピー終端finalStageも保持。
単体Lean検査と全体build成功（9098 jobs、exit 0）、標準公理のみ。
実行中プロセスなし。git diff --check成功。

**準備の基本操作数とDPの有効tick数を混ぜて外側経過時間としない。**
controller mode grouping、準備中のCounter/InputHead全状態、外側tickとdebt収支・初期radius、
物理回路/FIFOがまだ残る。resetはここでは既存論理reset後を開始状態とし、そのheap実装は別。
最終PAL機械・正例期限は未完。

### 最新：同じSOURCE実行を12テープへlift、他テープ保存

ScaffoldLower.load_ops/rewind_opsでcontroller groupingを外して同じTape実行の基本操作列を導出。
SourceReady.place_program_opsは同じPlace.CopyとRewindからLoading.Runを構成し、
任意12テープ状態のSOURCEだけを正確なbounded payloadへ更新する。PCと他11テープはputで保存。
開始はSOURCEのLEFT/right設定後。基本操作数3m+2であり、controller tick数2m+3とは別。
単体Lean検査と全体build成功（9098 jobs、exit 0）、標準公理のみ。
実行中プロセスなし。git diff --check成功。

まだLOWER・SOURCE setup2操作・reset/startをこの同じ実行と合成していない。
次は既存Loading.load_programの組立てを使い、SOURCE側にplace_program_opsを差し込み、
最終全状態をScaffoldPreload.initialへ一致させる。その後DP予算契約へ。
controller全mode、heap/FIFO、debt/正例期限、最終PAL機械は未完。

### 最新：Place/InputHead walkerとSOURCE preloadの同一実行接続

新規 `GalilScaffoldSourceReady`：copy_resultは任意Copy実行から正確なコピー長・最終Tape・
finalStageを抽出。place_readyはPlace.runs/copy_soundを通し、同じwalker実行の出力Tapeを
Rewindへ接続。input_readyはInputHead.realize_copyでfocus/左右スタック更新へ持ち上げる。
入力の文字/gapを実際に読むCopy m+1 tickとRewind m+2 tick、正確なbounded payload、
final iff stream長≤span+1を保証。incoming列qは保存され、左移動guardも既存実現証明が保証。
単体Lean検査と全体build成功（9098 jobs、exit 0）、公理propext/Quot.sound。root import済み。
実行中プロセスなし。git diff --check成功。

これはlogical InputHeadであり物理Ref/FIFOではない。全12テープのframe・LOWERとの合成、
mode/外側tick/debt/初期radiusの接続は残る。次は準備全体の初期/最終program状態を
既存ScaffoldPreload.initialへ同一状態として結び、DP開始へ渡す。
大定理・正例期限・最終PAL機械は未完。

### 最新：SOURCEコピー/homeを正確なDP preloadへ接続

ScaffoldLower.source_readyを追加。Counter.Copyでwork=span+1からm+1 tick、
実LEFT検査Rewindでm+2 tick、bounded((xs.take(span+1)).map symbol)を構成。
m=min(xs.length,span+1)。残りstreamとworkも正確に保持し、finalStage=true iff xs.length≤span+1。
単体Lean検査と全体build成功（9097 jobs、exit 0）、公理propext/Quot.soundのみ。
実行中プロセスなし。git diff --check成功。

LOWERの2r+3とSOURCEの2m+3は具体Counter/論理Tape操作として接続できた。
まだPlace/InputHeadのwalker実行、全プログラムの他テープframe、mode間遷移、
外側tick/debt収支をひとつの準備実行へ合成していない。入力streamはここでは引数。
既存Place.copy_sound/copy_counter/InputHead.realize_copyの接続を使えるが、
単に同じxsの名前を置くだけでwalker対応済みにしない。
最終PAL機械・正例期限は未完。

### 最新：LOWER書込みとhomeの具体テープ接続

新規 `GalilScaffoldLower`：LoadはCounter.positive/decとwrite8/moveRightを1 controller tickに
まとめ、終了tickでENDを書き込む。load_exactでr+1 tickの正確なテープを証明。
Rewindは実focus=LEFTを停止条件にし、既存Homeの移動数に終了判定1 tickを加える。
lower_readyはprepareのLEFT/right設定からLoad r+1、Rewind r+2で
DPのbounded(replicate r 8)を構成する。計2r+3 tick。
単体Lean検査と全体build成功（9097 jobs、exit 0）、公理propext/Quot.soundのみ。
root import済み。実行中プロセスなし。git diff --check成功。

準備コストのLOWER区間をCounter/論理テープ実操作へ接続できた。
残りはSOURCEコピー/homeとmode間の全状態合成、実外側tick/debt収支、初期radius条件。
物理StackPool回路・FIFO・最終PAL機械は未完。lower_ready自体はheap/circuit評価ではない。

### 最新：grow後のadvanceまで含むCounter収支

ScaffoldGrowにpaced_zero/paced_append/paced_stageを追加。
growAdv.length回のgrowと、その後のlaterAdv列を合成し、最終debt値を
初期debt+2*growAdv.length-(growAdv++laterAdv).count trueと証明。
grow終了後はwork=0でgrow更新せず、advanceのみ減算する射影モデル上の定理。
単体Lean検査と全体build成功（9096 jobs、exit 0）、標準公理のみ。
実行中プロセスなし。git diff --check成功。

これで実収支を構成する部品はgrow区間だけでなく後続区間にも使える。
**prepareはworkをlowerへコピーするため、このworkフィールドをそのまま実Search.workと同一視しない。**
後続区間ではgrowを再実行しないこと、debtのみの射影が正しいことを実mode遷移から示す必要がある。
double/restartを跨ぐ適用は不可。実stage時間・初期radius・正例期限・最終PAL機械は未完。

### 最新：初回barrierと後続stageの比較上界

AdvanceClock.first_stage_barrierは3*radius≤5*rとイベント列長≤63*(8*max(r,1))から、
delay2048/reset入口でradius+advance数≤2*max(r,1)を証明。r=0も含む。
first_stage_debtはCanonicalと実収支値=-radius+2*max(r,1)-advance数を前提にnegative禁止を導く。
later_stage_advancesはspan≥16、任意clock∈[1,2048]、列長≤63*spanからadvance数≤span/8。
clock=1で即比較が来る場合も含む。単体Lean検査と全体build成功（9096 jobs、exit 0）、標準公理のみ。
実行中プロセスなし。git diff --check成功。

**source radius条件・実stage時間・実Counter収支は依然前提。**
それらをオンラインGalil全体から証明したわけではない。数値上のbarrier義務を明示条件から
解いた段階。次は準備/runtime/refinementで列長を、開始/advance/growで収支を満たす実traceを接続。
delay2048は新コスト用の候補設定でありScala既定を変更していない。
最終PAL機械・正例期限は未完。

### 最新：clock由来advance列とgrow収支の接続

新規 `GalilScaffoldAdvanceClock`：各tickの(available,eligible)から
available∧clock=1∧eligibleを出力するadvancesを定義。eligibleはSearch.tick後の
Search.active∧chain.idleに対応させる入力値。advances_length、advances_le_compares、
advances_budgetでreset間のadvance数*delay≤available数を証明。
grow_before_first_compareはes.length<delayかつgrow区間内ならadvance数0を導き、
実Counter収支へ接続してdebt=初期値+2*es.lengthを保証する。
単体Lean検査と全体build成功（9096 jobs、exit 0）、標準公理のみ。root import済み。
実行中プロセスなし。git diff --check成功。

**eligibleが実Search/chain状態に対応することやreset境界は未接続。**
これは任意長stageのdebt非負性ではない。初期radius条件、grow完了後の準備/run時間、
比較回数の全区間合算が必要。次は短区間だけでなく全stageの収支を明示上界へ接続する。
正例期限・物理回路/FIFO/最終PAL機械は未完。

### 最新：grow中の外側advance列を含む収支

ScaffoldGrowにafterMatch/paced/paced_valuesを追加。positive(work)ならgrow更新し、
その後にBool列のadvanceがtrueならdebt.decするScala順序をモデル化した。
bs.length≤gなら、work=ofNat(g-bs.length)、span値=初期値+8*bs.length、
debt値=初期値+2*bs.length-bs.count trueを証明する。任意prefixに適用可能。
単体Lean検査と全体build成功（9095 jobs、exit 0）、標準公理のみ。
実行中プロセスなし。git diff --check成功。

終端prepare tickとその後の他modeはまだこの定理に含めない。
**bsが実Galilのcompare∧active∧chain.idleに一致することは未証明。**
次はMatchClockのcompare頻度とbs.count上界を接続し、終了tickを含む収支とdebt境界へ進む。
最終PAL機械・正例期限は未完成。

### 最新：growの二スタックCounter更新とtick収支

新規 `GalilScaffoldGrow` はCounter.inc反復add、work.dec/span+8/debt+2のstep、
positive guardを使うGrow関係を定義。grow_exactはwork=ofNat gから終了判定込みg+1回、
work=0、span値+8g、debt値+2g、Canonical保存を証明する。
初期debtは負でもよい。既存Counterの論理二スタック実装に基づき、Nat残量だけのモデルから一段接続。
単体Lean検査と全体build成功（9095 jobs、exit 0）、公理はpropext/Quot.sound。root import済み。
実行中プロセスなし。git diff --check成功。

**外側advanceMatchが途中に挟まる減少分はまだ含めない。**
最終prepare tickのcounterコピー・program.reset/loadや物理StackPoolも別契約。
次はgrow/debtの収支をcompare列と合成するか、lower/home/copy区間の具体counter/head距離を
PrepareClockへ接続する。正例期限・最終PAL機械は未完。

### 最新：準備モードのtick収支を定義・証明

GALIL_CLOCK.mdを読み、Scala Search.stepと照合。grow g回＋終了1、lower r回＋終了1、
lower_home r+1移動＋終了1、copy m回＋終了1、home m+1移動＋終了1で計g+2r+2m+7。
新規 `GalilScaffoldPrepareClock` はPhase/tick/remaining/advanceを定義し、
tick_decreasesとpreparation_ticksでこのdecodedカウント遷移のrun到達を証明した。
単体Lean検査と全体build成功（9094 jobs、exit 0）、標準公理のみ。root import済み。
実行中プロセスなし。git diff --check成功。

**これは具体counter/tape/walkerのrefinement証明ではない。**
copyのmは実コピー長でありspanと同一視しない。終了理由（walker=None/work=0）、
各head距離、grow/span/debt更新を既存Copy/Counter/Loadingと接続する必要がある。
次はこの収支をspan=8*max(r,1)、m≤span+1へ特殊化しTimingCostへ接続しつつ、
実モード不変条件を証明する。doubleは同じ回数式に入れられてもdebtのquarter更新は別。
正例期限・回路/FIFO・最終PAL機械は未完。

### 最新：主経路のclock導出を再確認、新コストの数値校正

重要な訂正：`ScaffoldCircuitGalil.buildOnlineWithViews` は `GalilClock.derive(quantum)` の
matchDelayを使う。build/buildWithViewsの引数既定256と混同しない。
Scala GalilClock.scalaはFppCost.boundsの旧ledger由来DP係数からstage/clockを導出している。
今回の証明済みDP係数3186/1683を使うなら、quantum64のfirst式はceilで63、
24*63=1512を覆う最小2冪delayは2048。**現Scalaコードの数値を変更したわけではない。**

新規 `GalilScaffoldTimingCost`：runBudget(span)=ceil((3186*(span+1)+1683)/64)、
runBudget_sufficient、first_stage（span≥8で19*span/8+10+runBudget≤63*span）、
later_stage（span≥16で11*span/4+10+runBudget≤63*span）、delay_calibrationを証明。
除算はNat除算。実spanは初回8の倍数・以後倍増だが、そのschedule不変条件は別。
単体Lean検査と全体build成功（9093 jobs、exit 0）、標準公理のみ。root import済み。
実行中プロセスなし。git diff --check成功。

これは**数値式の校正であり、実stage処理の19/8・11/4上界を証明したものではない**。
次はdocs/palindromes-in-peg/GALIL_CLOCK.mdのsource contractと実Searchの
grow/lower/rewind/copy/home/runのtick数を対応させ、外側advanceMatchとの収支を証明する。
旧delayを維持するには旧小さいコストの証明が必要か、別のより鋭い上界が必要。
大定理・正例期限・物理回路/FIFO/最終機械は未完。

### 最新：runStepのdebt assertionを含む安全な呼出し列

SearchRunにfinish_debt、SafeCalls、calls_safe、quantum64_safeを追加。
SafeCallsはenabled∧done時のScala negative禁止を各呼出しに含む。
finishはdebtを保存するので、入口debtがCanonicalかつ非負なら、既存の有界Callsを
安全な呼出し列へ変換し、正しいResult/done/run退出とdebt保存を保証できる。
単体Lean検査と全体build成功（9092 jobs、exit 0）、標準公理のみ。
実行中プロセスなし。git diff --check成功。

**入口非負性は仮定であり、online全体から導出したわけではない。**
外側advanceMatchが呼出し間にdebtを減らす履歴には、そのまま適用できない。
次は外側tick間のadvanceMatch回数とrun時間上界の収支へ戻ること。
Search.startのdebt=-radiusを非負扱いしない。debt条件を名前変更して解決済みにしない。
外側tick/正例期限・物理回路/FIFO/最終PAL機械は未完。

### 最新：run呼出し列の有界終了と残余呼出しの不変性

SearchRun.quantum64_exitsは、具体DP preloadとmode.runから
64*(50*N+27)呼出し枠でCallsの終了状態がprogram.done=true、mode≠run、正しいResultを持つと証明。
calls_stoppedは、入口mode≠runならCallsがSearch状態とprogram状態を両方保存すると証明。
単体Lean検査と全体build成功（9092 jobs、exit 0）、標準公理のみ。
実行中プロセスなし。git diff --check成功。

注意：**runStep呼出し列の定理であり、外側tick全体の定理ではない。**
外側tickのstepは非runモードでgrow/lower/copy/wait/double等を動かすため、
calls_stoppedを外側tickの停止と誤解しない。次は入口running保存を持つquantum block対応、
停止に至るまでの外側tick列、その間のdebt/advanceMatchを接続する。
正例期限・物理回路/FIFO・無条件PAL∈PEGは未完。

### 最新：run modeとdoneの対応を呼出し列へ接続

新規 `GalilScaffoldSearchRun`：finish_run_iff、run_call、Calls、realize_callsを追加。
入口で `s.mode=run ↔ x.done=false` のとき、program Tickの後に実finish分岐を適用しても
同じ対応を保つ。GuardedRunの任意呼出し列を、mode.runでguardしfinishを更新するCallsへ
同じ最終program状態のまま実現する。単体Lean検査と全体build成功（9092 jobs、exit 0）。
公理はpropext/Quot.soundのみ。root import済み。実行中プロセスなし。git diff --check成功。

これはrunStepのdecoded program/finish部分。**debtのrequireはまだ含めていない。**
外側tickの入口running保存、非run時の他mode dispatch、各段階の初期run/done対応、
debt境界/正例期限、物理回路/FIFO/最終機械は未完。
次はquantum64_correctのGuardedRunをrealize_callsへ渡し、外側tick境界のrun維持と
停止後slotの無効化を実Scala tickの入口running条件に対応させる。

### 最新：done後の呼出し抑制とquantum64予算

ScaffoldCircuitSearch.scalaのtick/runStepを再確認：入口runningを保存し、step(enabled)の後、
1 until quantumでenabled∧入口running∧現在mode.runを使う。runStepはprogram.step後に
doneならfound/missed/double/waitへ遷移する。
`GalilScaffoldDpCost.GuardedRun` は要求slotのenabledを `b && !x.done` にする実行関係。
`guard_run` で通常Runから同じ終了状態への変換を証明し、`quantum64_correct` で
**64*(50*N+27)個の要求slot**が正しいDP終了に十分と証明した。
単体Lean検査と全体build成功（9091 jobs、exit 0）、標準公理のみ。
実行中プロセスなし。git diff --check成功。

**実Search.tickの経過時間を50*N+27以内と証明したわけではない。**
GuardedRunはmode/finishをまだ持たない。次はrun入口からdoneまでmode.runが保持され、
各有効外側tickの64 slotがこの関係に対応することをSearchFinishと結ぶ。
非run→runへの移行tickでは入口running=falseなので追加63呼出しは無効、という差も扱う。
debtのrequire条件・正例期限・物理回路/FIFO/最終機械は未完。

### 最新：明示DP上界をScaffoldの有効tick契約へ接続

`GalilScaffoldDpCost.scheduled_correct` を追加しroot import済み。
具体的な論理テープpreloadから、任意Boolスケジュールbsに対し
`3186*w.length+1683 ≤ bs.count true` ならRunがdone=trueかつ正しいResultに到達する。
DPの同一実行コストとrealize_completed/scheduled_completedを合成。
単体Lean検査と全体build成功（9091 jobs、exit 0）、標準公理のみ。
実行中プロセスなし。git diff --check成功。

**これは実Search.tickがその数の有効呼出しを供給する証明ではない。**
次はScala ScaffoldCircuitSearch.tick/runStepのmode・enabled列とquantum呼出し数を形式化し、
実経過tickに対するDP進捗をつなぐ。debt境界/正例期限・物理回路/FIFO・最終PAL機械は未完。

### 最新：DP正しさと時間上界を同じ実行に統合

`GalilDpCost.initial_correct_cost` は実初期状態からのCompletedと
`GalilDpCorrect.Result w lower 0 y`（候補最小性・正確なOUTPUTまたは候補不在）、
**`qs.length ≤ 3186*w.length+1683`** を同じy/qsについて保証する。
`execute_unique` / `completed_unique` を追加し、既存dp_wellFormedのread-key Nodupから
終了状態の決定性を証明して、コスト実行と正しさ実行を一致させた。
単体Lean検査と全体build成功（9090 jobs、exit 0）、標準公理のみ。
GalilDpCostにCorrect/ScaffoldNextPcを追加import。実行中プロセスなし。git diff --check成功。

次はこの定理をScaffold側DP実行・Search.tickの実enabled列へ渡し、
grow/double/compareとdebtの境界上界・正例期限へ接続する。
旧時間定数をこの新しい上界で無検証に再利用しない。
無条件PAL∈PEGはまだ未完成。回路の物理解釈・実スケジュール・FIFO・最終機械も残る。
下の「Resultとの同一実行接続が残る」は解消済みの履歴。

### 最新：DP全体の停止コストを証明

新規 `GalilDpCost.initial_terminated_cost` は任意Fin3入力・任意lowerについて、
実12テープ初期状態からのCompleted、終了PC346または347、
**`qs.length ≤ 3186*w.length+1683`** を保証する。root import済み。
準備3168*N+1661、start6命令、長入力next_candidate15命令＋loop18*(N-1)+19、
短入力short_next≤16を合成。単体moduleおよび全体build成功（9090 jobs、exit 0）、標準公理のみ。
実行中プロセスなし。git diff --check成功。

**次は正しさResultとこの時間上界を同じ実行へ接続する。**
既存 `GalilDpCorrect.initial_correct` は別の存在実行を構成するため、単に両定理を
並べて同じ終了状態と見なさない。選択肢はcorrect_loopへコストを保持して再合成、
または実codeのread-key一意性（ScaffoldNextPc.dp_wellFormedが既存）から
Completedの決定性を証明して終了状態を一致させること。まだどちらも実装していない。
Galil期限・実回路/FIFO/最終機械・無条件PAL∈PEGは未完成。

### 最新：DP準備のコスト付き接続が完了

`GalilDpPreparedCost.prepared_cost` を新規追加しroot import済み。
実12テープ初期状態からPC372まで、既存preparedの全テープ/head契約を保ち、
**`qs.length ≤ 3168*w.length+1661`** を証明。marked変換2倍＋dispatch1命令。
単体Lean検査と全体build成功（9089 jobs、exit 0）、標準公理のみ。
実行中プロセスなし。git diff --check成功。

次は `GalilDpStart.long_terminates` / `short_terminates` と同じ構成で、prepared_costを使う。
`GalilDpLoop.terminates` は既に `18*(w.length-h)+19`、`short_next` は16命令上界を持つ。
`next_candidate` と `start_run` も実traceがある。既存Startはこれらのコストを捨てているので
保持して全DP上界を作る。正しさResultとの同一実行への接続も忘れない。
DP全体コスト・Galil期限・無条件PAL∈PEGはまだ未完成。

### 最新：9テープmarked FPPの全体コストを接続

新規 `GalilFppMarkedCost.lean` の `marked_fpp_exact_cost` は、任意Fin3入力について
実9テープ初期状態からCompleted、pc=0、SOURCE/MARKS head=0、SOURCE保存、
正確なmarksテープ、および **`qs.length ≤ 1584*w.length+830`** を同時に保証する。
準備24*N+42、prepared word長2*N+1、7テープ390*長さ+4、命令変換高々2倍を合成。
単体Lean検査と全体build成功（9088 jobs、exit 0）、標準公理のみ。root import追加済み。
実行中プロセスなし。git diff --check成功。

次の具体箇所：`GalilDpPrepared.prepared` と同じ構成でmarked_fpp_exact_costを用い、
`GalilDpSimulation.completed` の既存2倍上界を保持する。
dispatchは追加1命令なので、DP準備部分は **3168*N+1661** が候補上界。
まだこのDPコスト定理は書いていない。DP探索自体のコスト・Galil期限も未接続。

### 最新：FPP全体の線形時間上界が閉じた

`GalilFppGenerationCost.initial_completed_cost` は任意の `w : List (Fin 4)` に対して、
実Scala由来FPP命令表の `Completed code (initial w) qs y`、正しいborder列出力、
終了pc=0/A-head=0、**`qs.length ≤ 390*w.length+4`** を同時に証明する。
初期化・全入力処理・失敗探索・出力・haltを含む。空入力も含む。
`process_prefix_cost` の帰納ではB advanceの実2命令をpotential付きで保守的に24計上し、
一文字366と合わせ390。`process_all_cost` ではReadyのS≤failureを用い、残ったfailure
potentialで出力側25*failure+2を払う。したがって全体で390*N+4となる。
追加3定理の単体Lean検査と全体build成功（9087 jobs、exit 0）。
公理はpropext/Classical.choice/Quot.soundのみ。git diff --check成功。実行中プロセスなし。

**次はこの全体コストをmarked FPP/DPの実行へ持ち上げ、Galilの正例期限へ接続する。**
旧132*N+12の定数を証明したわけではない。既存quantum/matchDelayで十分かも未検証。
無条件PAL∈PEGは未完成。物理回路・実スケジュール・FIFO・最終機械への接続も残る。
以下の「FPP全体線形上界は未完成」は過去の記録で、この節が更新する。

### 保存後の再開で更新：input_stepの償却上界まで証明済み

`GalilFppGenerationCost.lean` に `execute_potential`、`steps_potential`、
`search_supply_cost`、`input_step_cost` を追加。下に記した未実装案の1〜2と終端合成は完了した。
探索の係数は348。入力一文字の機能契約（Ready/Supply/生成位置/入力テープ/B-head保存）を保ち、
`qs.length + 5*y.pos 5 + 11*x.pos 3 + 348*failure w (N+1)
 ≤ 366 + 5*x.pos 5 + 11*y.pos 3 + 348*failure w N`
を証明した。両分岐を含む実Stepsの上界であり、抽象コストへの置換ではない。
単体Lean検査および全体build成功（9087 jobs、exit 0）、追加定理は標準公理のみ。
実行中のLean/buildプロセスなし。

**次は `advance_input` と `process_prefix` へ持ち上げ、入力列全体でpotentialを相殺する。**
advance_inputの既存契約にはBACK位置保存が明示されていないので、実2命令から保存を取り出すか、
steps_potentialで保守的に計上する。初期化とChain出力まで含めたFPP全体上界はまだ未完成。
旧132*N+12やGalil正例期限は未証明のまま。以下の「今回証明コード変更なし」は最初の保存時点の記録。

今回の依頼は進捗の保存。証明コードは追加せず、以下を引き継ぐ。
**下の時系列ログにある「次は」「未証明」は当時の状態。現在の優先順位はこの節を正とする。**

### 到達点と未完了

- 大定理は未完成。`lean-pal/PalPeg/Main.lean:43` の `pal_in_peg_of_structured` は、具体的な構造化機械とPAL認識証明を引数に取る条件付き定理のまま。
- 実Scala由来のFPP/DP命令表、FPPの停止・生成、DPの候補探索正しさは証明済み。decoded制御からheap実行への局所接続もあるが、実bit回路全体の完成ではない。
- 最新の完了箇所は `GalilFppGenerationCost.lean` の `hit_ready_cost` と `zero_miss_supply_cost`。両終端分岐で、機能契約に加えて同じ償却上界を保持した：
  `qs.length + 5*y.pos 5 + 11*x.pos 3 ≤ 18 + 5*x.pos 5 + 11*y.pos 3`。
  BACKはテープ5、Sはテープ3。zero_missの実命令数は8、BACK増加は2。
- `GalilFppReadCost` / `GalilFppSupplyCost` / `GalilFppGenerationCost` は `PalPeg.lean` にimport済み。
- **失敗探索と終端分岐を合わせたinput_stepのコスト、FPP全体線形上界はまだ未証明。** さらにGalilの進捗・正例期限、物理field/bit回路、実制御スケジュール、入力FIFO、具体初期heap、buffer/packから最終機械への接続が残る。

### 次の具体的な一手（未実装の案）

直前は `GalilFppRetry.lean` の失敗探索を読み、`GalilFppInstruction.lean` の
`Execute` / `Steps` を調べるところで停止した。新しい証明の書きかけはない。

1. `Execute` は1命令で高々1ヘッドを1動かすので、BACK/Sの重み付き変化について
   `5*y.pos 5 + 11*x.pos 3 ≤ 11 + 5*x.pos 5 + 11*y.pos 3`
   をケース分けで証明できるか確認する。`Steps` へ帰納して
   `qs.length + 5*y.pos 5 + 11*x.pos 3 ≤ 12*qs.length + 5*x.pos 5 + 11*y.pos 3`
   を導く方針。**この補題はまだ書いていない。**
2. `GalilFppGeneration.search_supply` は既に `qs.length ≤ 29*(failure w N-r)` を持つ。
   上記が通れば探索を係数348のpotential上界にでき、終端分岐の固定費18と合成できる。
3. hitでは次failure=r+1、missではr=0かつ次failure=0を使い、failureにも重みを付けて
   入力列に沿って償却する。`advance_input` の2命令、初期化、最後のChain出力も計上する。
4. これは粗い線形上界を先に閉じる案。**Scala側の旧132*N+12や33*N+3を証明したことにはならない。**
   quantum=64 / matchDelay=256で期限が満たせるかは、得た定数で別途検証が必要。

### 検証と作業状態

- 直前の検証記録：全体 `lake build` 成功（9087 jobs、exit 0）、`git diff --check` 成功。
  印字した追加定理の公理は標準公理のみ。今回の文書保存では全体buildは再実行していない。
- 今回、上記2定理の現物・root import・条件付き最終定理を再確認。実行中のLean/buildプロセスなし。
- commitしていない。多数の既存変更・untrackedファイルをそのまま保持すること。
- 再開は本節→対象3 Costファイル→Generation.search_supply/input_step→Instruction.Execute/Stepsの順で十分。
  下の長い履歴を全部読み直す必要はない。サブエージェントは使わない。

## 作業履歴（新しい順。古い未完了記述は上のスナップショットを優先）

### 最新作業：zero_missも同じ償却形へ

GenerationCostに `zero_miss_supply_cost` を追加。比較4命令と2回のenqueue（各2命令）を
実行合成し、Ready 0/Supply/生成位置/B-head保存を保証する。
命令8＋BACK高さ増加2×potential5で18となり、
`命令数 + 5*終了BACK高さ + 11*開始S位置 ≤ 18+5*開始BACK高さ+11*終了S位置`。
一致分岐と同じ形式になった。次の未接続点は失敗探索の全体コストとinput_stepへの合成。
全体build成功（9087 jobs、exit code 0）、印字した公理は標準公理のみ。`git diff --check`成功。
実行中プロセスなし。

### 最新作業：一致分岐のReady復元とS位置による償却

`GalilFppGenerationCost.hit_ready_cost` を追加。比較2命令をSupplyCostの一致分岐へ合成し、
次入力用Ready/Supply/入力head保存を保ったまま
`命令数 + 5*終了BACK高さ + 11*開始S位置 ≤ 18 + 5*開始BACK高さ + 11*終了S位置`
を証明する。`開始S + delta(failure,p) = 終了S`をReadyから導出し、候補依存deltaを位置差へ変換した。
leaf検査成功、標準公理のみ。
全体build成功（9087 jobs、exit code 0）、`git diff --check`成功。実行中プロセスなし。

次はsearch_supplyの失敗探索とzero_miss分岐にも位置/potential付き上界を付け、input_stepへ合成する。
一致分岐だけなので、全入力・FPP全体の線形上界はまだ未完成。

### 最新作業：一致分岐のSupplyコスト

`GalilFppSupplyCost` を追加。`scan_candidate_cost` は既存Supplyの候補条件からscan償却上界へ接続。
`matched_lazy_cost` はPC62からのenqueue・C移動・scanを合成し、
`qs.length + 5*y.pos 5 ≤ 11*delta(failure w,p)+16+5*x.pos 5` を保証する。
16はscan固定費8＋実命令3＋BACK増加potential5。
`matched_generated_cost` は実生成位置と次failureの条件から同じ上界を保つ。
機能契約（Supply、C/S位置、他テープframe）も保持している。
全体build成功（9086 jobs、exit code 0）、印字した公理は標準公理のみ。実行中プロセスなし。

次はGeneration.hit_ready/input_stepへつなぎ、失敗探索で増えるBACKとA/C/Sの移動を合算する。
delta(p)は処理入力番号Nのdeltaとは限らないので、単純なΣdelta(N)への置換は不可。
実際のC/S移動・fallback差との償却が必要。FPP全体線形上界は依然未完成。

### 継続作業：read/scanコストの持ち上げ

`GalilFppReadCost.lean` を新規作成（既存build中に対象ファイルは変更せず、未importの新ファイルで作業）。
dequeue_all_cost、forward_blank_cost、read_cost、scan_costを記述。
六つのread instanceへ7+BACK potential、forward readへ8+potential、delta scanへ11*d+8+potentialを渡す。
旧buildは9084 jobsで成功し終了済み。新ファイルのleaf検査も成功（4定理とも標準公理のみ）。
root importを追加。次はSupply/Generationのmatched/input_stepへコストを持ち上げ、
enqueueのpotential増加とfailure差・delta総和を合算する。全体線形上界はまだ未完成。
最新全体build成功（9085 jobs、exit code 0）。`git diff --check`成功。実行中プロセスなし。

### 最新作業：FPP dequeueの償却コストを復元

FPP全体コストへ戻った。`search_supply` は29*(failure差)の上界を持つが、
LazyForward/Supply/Generationの上位契約はmaterializationの命令数を捨てている。
`GalilFppMaterialize` に `stack_height` と `dequeue_cost` を追加し、既存証明を強化した。
同じ実行結果・Regionに加え `qs.length + 5*y.pos 5 ≤ 7 + 5*x.pos 5` を保証する。
FRONT非空時は5命令でBACK不変、空時は全BACK補充の5*長さ+7をBACK高さの減少で支払う。
旧 `dequeue` は互換wrapperとして残した。leaf検査成功、標準公理のみ。
Materialize変更後の全体buildは9084 jobsで成功。旧session29724は終了済み。
今回の`git diff --check`は成功。

**FPP全体の線形時間上界はまだ未完成。** 次はReadInstances.dequeue_all/forward_blank、
LazyForward.read/scanへこのpotential付き上界を落とさず持ち上げ、enqueueの増加分と合算する。
単にqueue長に比例する上界を各readに掛けると二次上界になるので避ける。

### 最新作業：match clockの比較回数上界

Galil側を確認。search.tickはcompareより前に実行され、advanceSearchは
compare ∧ search.active ∧ chain.idle。compareはavailableなscanでclock=1の時だけ。
clockはmatchDelay周期で減少し、restart/replay_start時にmatchDelayへ戻る。
`GalilScaffoldMatchClock` の `run_invariant` は任意available Bool列でclock範囲と収支
`available数 + 最終clock = 初期clock + compare数*delay` を証明。
初期clock=delayなら `compare_budget` / `compare_remainder` により
`compare数*delay ≤ available数 < (compare数+1)*delay`。
leaf検査成功、標準公理のみ。
root import後の全体build成功（9084 jobs、exit code 0）、`git diff --check`成功。実行中プロセスなし。

これはclock reset間のdecode済み更新。advanceSearchがcompareの部分列である実イベント対応、
search処理進捗・DP/FPP全体時間・restart境界を接続してdebt境界上界を導く作業は残る。
比較頻度だけでdebt非負性や正例期限が閉じたとは言わない。

### 最新作業：debt非負性の必要な範囲と収支

Scalaの全debt更新を確認。startはradiusのpos/negを交換しdebt=-radius、advanceMatchは
radius.inc/debt.dec、growはdebt.incを2回、double中はquarterEndごとにdebt.incを1回。
**debtが常に非負という不変条件は誤り。** 非負性が必要なのはrunStepのfinished時とwait dispatch時。

SearchFinishに `initialDebt` / `initial_balance` / `advance_balance` / `grow_balance` /
`quarter_balance` を追加。debt+radiusはstartで0、advanceで不変、growで+2、quarterEndで+1。
`boundary_guard` はこの収支とradius≤creditsから既存のnegative禁止条件を導く。
まだ全履歴の収支定理・finished/wait時のradius≤creditsというスケジュール上界は未証明。
この上界を仮定の名前変更だけで解決済み扱いしない。Galil側のadvanceSearchと実処理時間を接続する必要がある。
全体build成功（9083 jobs、exit code 0）、印字した公理は標準公理のみ。実行中プロセスなし。

### 最新作業：Search.runStep停止後分岐とDP結果

`GalilScaffoldSearchFinish` を追加。Scalaの11 mode、finalStage/span/work/debt/quarterを
持つStateで、program.step後のfinish分岐を記述。enabledかつdoneで、PC346→found、
それ以外はfinalStage→missed、debt.zero→double、残り→wait。
doubleではwork=旧span、span.reset、quarter=0も反映する。
`result_found` は既存DP Resultの下でfoundと候補存在の同値、`failed_no_candidate` は
PC347の現在DP窓内の候補不在を証明する。`debt_guard` はCanonicalかつ非負のdebtで
Scalaのnegative禁止条件を満たすことを示す。
root import後の全体build成功（9083 jobs、exit code 0）、印字した公理は標準公理のみ。
実行中プロセスなし。

まだpost-program-stepの論理Stateであり、heap側Search counter全体や実mode/Exprには未接続。
finalStage/debtの正しさ・非負性をonline全体から導出する証明、次段階の進捗/期限も残る。
現在窓の候補不在をPAL全体の不受理と報告しない。

### 最新作業：単一ノードinstruction blockとsuffix保存

RawScheduleの `run_other` は指定列にない全heapセルの保存。
`block_suffix_frame` はinstruction prefix終了以降のslot（別ノードを含む）の保存。
`realize_block` は任意Control.Runを同一ノードのslot0..bs.length-1で実現し、
初期prefix未使用性だけから実行とcontroller suffixのセル保存をまとめて保証する。
leaf検査成功、標準公理のみ。
全体build成功（9082 jobs、exit code 0）、`git diff --check`成功。実行中プロセスなし。

Scala `ScaffoldCircuitSearch.tick:144–147` はstep内runStepと `1 until quantum` の追加runStep。
`runStep:68–69` はprogram.stepを一回呼ぶ。正のquantumなら構文的にquantum呼び出し。
ただしこの呼び出し列のenabled/mode更新・controller操作・実instructionIndexとの対応は
まだLeanに接続していない。suffixセル保存はcontroller実行自体の正しさの証明ではない。

### 最新作業：事前固定したAddress列でraw Runを実現

`GalilScaffoldRawSchedule` を追加。`tick_other` は指定割当Address以外のheapセルが不変。
Address列を明示する `Run` と `realize_run` は、Bool予定と同長・Nodup・初期未使用の
固定Address列で任意Control.Runを実現する。途中で新規ノードを選び直す必要はない。
`block node quantum slots hq` は同一ノードのslot0..quantum-1を並べ、長さ・Nodup・
instruction prefix内に収まることを証明する。
root import後の全体build成功（9082 jobs、exit code 0）、印字した公理は標準公理のみ。
実行中プロセスなし。

実Scalaのtick呼び出し数とinstructionIndex/quantumの対応、controller suffixとの
実割当干渉、複数ノードのスケジュールへの接続はまだ必要。固定列の初期未使用性は前提。
bit回路・field decoding・online全体と最終PEGは依然として未完。

### 最新作業：pause付きraw実行全体と停止への接続

RawTickに `loop_finite` / `tick_finite`、raw `Run`、`realize_run` を追加。
任意の既存Control.Runを同じBool予定列で実現し、最終状態の表現対応とheap有限性を保存。
`scheduled_completed` は既存Program停止traceと、十分な有効tickを持つ任意pause列から、
raw heap実行のdone=true・同じ最終テープ解釈を保証する。
全体build成功（9081 jobs、exit code 0）、印字した公理は標準公理のみ。実行中プロセスなし。

WellFormed/初期heap表現/有限性/slots>0は前提。各tickで未使用ノードのslot0を選ぶ存在証明で、
実Scalaの固定slot割当や時間期限を証明したわけではない。bit回路・field decoding・
online Galil/FIFO/packing/最終PEGとの接続は残る。

### 最新作業：decoded raw tickと既存制御を合成

`GalilScaffoldRawTick` にheap Config+doneのMachineと `tick` を追加。
disabled/doneなら不変、haltならPC/テープを保存しdone=true、他命令なら入口focusから
次PCを計算して実順序のテープfoldを適用する。PCまたはread target欠落はNone。
`tick_execute` / `realize_tick` は既存 `GalilScaffoldControl.Tick` のidle/halt/executeをすべて実現する。
leaf検査成功、標準公理のみ。
root import後の全体build成功（9081 jobs、exit code 0）。`git diff --check`成功、実行中プロセスなし。

fresh Addressとread表WellFormedは前提。tick関数自体はallocation/left guardを検査する関数ではなく、
対応する合法実行に対してrefinementが成立する。実Value/Expr bit評価・field decodingとの接続、
全pause付きRunへの持ち上げ、実slot schedule/時間上界はまだ未完。
decoded tickの完成を実Scala回路全体の完成と同一視しない。

### 最新作業：target別イベント集約とlookupの同値

NextPcに `lookup_sound`（lookup結果は実read表の要素）、`Forward`、`TargetEvent` を追加。
TargetEventはScala forward(target,event)のtarget別OR集約を存在量化で表す。
`targetEvent_iff` はWellFormedな選択命令について、targetイベント有効と
active=trueかつlookup/直接targetの計算結果との同値を証明。
`target_unique` は異なる二つのtargetが同時に有効にならないことを導く。
leaf検査成功、印字した公理は標準公理のみ。
全体build成功（9080 jobs、exit code 0）、`git diff --check`成功。実行中プロセスなし。

decode済みPC/focusでの意味論的な集約対応まで。Value(nextPc)のbit符号化・validity、
実Expr OR評価、done/halt更新を含むraw tickとの合成は未完。

### 最新作業：次PCをread表から計算

`GalilScaffoldNextPc` を追加。`lookup` はread表から記号のtargetを返す。
`WellFormed` はread表の記号列Nodup、`lookup_mem` は表内の分岐とlookup結果の一致。
`next_execute` は既存命令実行の次PCを入口focusから計算する。
`realize_next` は計算されたPCでraw tape loopを更新し、既存結果の表現対応を保証する。
`dp_wellFormed` は実 `GalilDpCode.code` の全373命令を `by decide` で検証済み。
leaf検査成功、標準公理のみ。
root import後の全体build成功（9080 jobs、exit code 0）。`git diff --check`成功、実行中プロセスなし。

**ScalaのnextPcターゲット別イベント集約とlookupとの同値はまだ未証明。**
done/halt更新、active/doneを含むraw tick、bit回路のValue選択・validity、field decodingも残る。
lookupの決定性をbit回路全体の検証と取り違えない。大定理はまだ未完成。

### 最新作業：write→left→rightの実順序を合成

`GalilScaffoldRawTapes` を追加。decode済み命令とactiveを入口snapshotとして固定し、
各テープでwriteGroup→moveGroup false→moveGroup trueを実行するfoldを定義。
`loop_write` / `loop_move` は一回のheap操作へ簡約、`loop_read` / `loop_halt` /
`loop_inactive` はテープ無変更を証明する。
`realize_loop` は既存List Programの任意非halt実行に対し、次PCをその意味論から与えれば
この具体的順序のheapループが結果を表現することを証明する。

**nextPcはまだ計算していない。** read分岐のtarget集約・PC/done更新・イベントのdecodeから
この命令snapshotへの対応、bit回路/field get-putは残る。fresh Addressも引数。
初回leaf検査は成功。大定理は依然として未完成。
`realize_loop` のpc射影の型合わせを `GalilScaffoldProgram.changed` の展開で修正し、
最終全体build成功（9079 jobs、exit code 0）。印字した公理は標準公理のみ。
`git diff --check`成功。実行中プロセスなし。

### 最新作業：writeイベントと全テープwriteループ

`GalilScaffoldWriteGuards` を追加。`WriteEvent` はcode.indicesのイベント集約、
`selected_write` は実write命令のtape/symbolとの一致。`writeLoop` はdecode後の入口PCを
固定した全テープfoldで、`loop_write` / `loop_heap_write` が一回の選択writeへ簡約する。
`loop_inactive` / `loop_nonwrite` はinactiveまたは非write命令時の無変更。
root import済み、全体build成功（9078 jobs、exit code 0）、印字した公理は標準公理のみ。
実行中プロセスなし。

移動ループとはまだ別foldで証明している。Scalaのtapeごとのwrite→left→rightという
interleavingへの合成、nextPc/read分岐・done更新、Value/Exprのbit意味論との接続は残る。
これをraw instructionStep全体の完成と報告しない。

### 最新作業：具体的テープ列と非move時の不変性

MoveGuardsの `keys n = (List.finRange n).product [false,true]` はScalaの各テープ左→右の順序。
`keys_nodup` / `mem_keys` を証明し、`concrete_loop_move` から列のNodup/被覆前提を除いた。
`inactive_loop` はinactive時の無変更、`nonmove_loop` は選択命令がmoveでなければ
全移動ループが無変更であることを証明（read/write/haltにはコンストラクタ不一致で適用可能）。
初回leaf検査成功、標準公理のみ。
全体build成功（9077 jobs、exit code 0）、`git diff --check`成功。実行中プロセスなし。

次はwriteイベント集約・PC/done更新とheap実行の合成。Value/Exprのbit評価、field get/put、
instructionIndex/quantumと実割当、全体online正しさ・時間上界・最終PEGは依然未完。

### 最新作業：moveイベントの逐次ループ合成

`GalilScaffoldMoveGuards` に `dispatch` / `dispatch_absent` / `dispatch_once` を追加。
重複しないtape/directionキー列に選択キーが含まれれば、全ループはその一回の操作に一致。
`dispatch_heap_move` が共有heap moveへ特殊化する。
`eventLoop` は命令入口のcode/pc/activeから集約したMoveEventを評価するfold。
`eventLoop_selected` / `eventLoop_once` が実イベント条件を選択キー一致へ変換し、全foldを簡約する。

キー列のNodup/被覆はまだ引数。Scalaの `tapes.indices` × 左右という具体的列への特殊化、
inactive/halt/read/write時のループ不変、PC/done更新、Value/Exprのbit評価はまだ残る。
guardは入口snapshotに固定している。実回路のsnapshot意味論との対応も別途必要。
最終全体build成功（9077 jobs、exit code 0）、印字した公理は標準公理のみ。実行中プロセスなし。

### 最新作業：raw命令の共有slot排他条件

`ScaffoldCircuitProgram.scala:74–109` を確認。raw instructionStepはactiveかつpc=iの
イベントをtape/direction別に集約し、その呼び出しの共通slotで左右moveを発行する。
`GalilScaffoldMoveGuards` の `MoveEvent` / `event_iff` はこの集約を具体的PCへ簡約。
`move_unique` は有効なtape/directionが高々一つ、`selected_move` は選択moveとの一致を証明。
`exclusive_writes` は排他的な2分岐の同一Address書き込みが選択側のみの書き込みに一致する。

これは具体的にdecodeされた単一PCを前提にした証明。Value/Exprのbit評価・validity、
全tapeループのfold、shared slotのinstructionIndex/quantum上界、controller extraMovesとの
分離、Circuit field get/putへの接続は未完。coarse block実行にはそのまま適用しない。
初回leaf検査成功、印字した公理はpropextのみ。
root import後の全体build成功（9077 jobs、exit code 0）。`git diff --check`成功、実行中プロセスなし。

### 最新作業：heap上の停止traceへの持ち上げ

`GalilScaffoldHeapProgram` に `FiniteHeap`（有限ノード境界以降は未使用）と
`put_finite` / `execute_finite` を追加。`Completed` は同じcode/PC traceを使うheap実行。
`realize_completed` は既存List Programの任意停止traceを、表現対応する有限heap初期状態から
同じPC列・最終List解釈で実現する。slots>0のみ要求し、各stepで新規ノードのslot0を選べる。
終了heapも有限である。leaf検査成功、標準公理のみ。
全体build成功（9076 jobs、exit code 0）、`git diff --check`成功。実行中プロセスなし。

**これは意味論的な割当の存在証明であり、実Scalaの固定ノード/slot配置と一致する証明ではない。**
有限heap初期状態の具体的構成、実Circuit field decoding、predicated schedule、実割当と
時間上界への接続は依然として必要。新規ノードを自由に取れることを実時間制約の解消とみなさない。

### 最新作業：共有heapのProgram命令対応

`GalilScaffoldHeapProgram.lean` を追加。Configは共有heap・pc・全テープrootを持つ。
`moved_right` / `moved_left` / `written_represents` は選択テープを更新し、他の全テープの
List解釈を保存する。`Execute` は同じ `GalilFppWide.Instruction` のread/write/左右moveを使う。
`realize_step` は既存 `GalilScaffoldProgram.Execute` の任意1命令をheap側へ持ち上げる。
左moveのroot非空guardとread分岐のfocus一致は表現関係から導出する。
root import済み。全体build成功（9076 jobs、exit code 0）、印字した公理は標準公理のみ。
実行中プロセスなし。

**fresh Addressはまだ引数。** 全実行列にわたる割当・停止traceへの持ち上げ、実Circuitの
field decodingとpredicated instruction選択、実slot割当の非衝突性は残る。
単一命令の対応をDP全体の物理実装証明と同一視しない。

### 最新作業：heap tapeを既存List tapeへ接続

`GalilScaffoldHeapTape.lean` を追加。左右Rootとfocusを持つTape、heap lookupによるtop、
pop/pushを合成した左右移動を定義。`right_represents` / `left_represents` は既存
`GalilScaffoldTape.moveRight/moveLeft`への対応を証明し、右側空ならblank、左側の合法guardも扱う。
`right_frame` / `left_frame` は他の任意rootのList内容を保存する。
`reset_represents` / `write_represents` も追加。resetはrootを切るだけでheapを消さない。

fresh Addressが前提（前項Allocatorのunused_freshで導出可能）。まだ実Circuitのfield
get/put・tag decodingとは未接続。次はこのheap tapeとProgram全テープ/命令実行の合成、
または実割当/field decodingの残前提を閉じること。新しい別構成へ乗り換えない。
leaf検査・root import後の全体build成功（9075 jobs、exit code 0）。印字した公理は標準公理のみ。
実行中プロセスなし。

### 最新作業：heap割当状態からfreshnessを導出

`GalilScaffoldHeap` に `Allocator`（heap/node/used slots）と `Bounded` を追加。
`unused_fresh` は現在ノードで未使用のslotが空であることを導出。
`allocate_bounded` / `nextNode_bounded` は同一ノードへの追加割当とノード進行で不変条件を保存。
`allocated_push` はこの導出を共有root保存つきpushへ接続する。
`initial_bounded` と `disabled_preserves` も追加し、空heapとdisabled書き込みを扱う。

**未使用slot条件そのものは依然として仮定。** Scalaのlayout/name/index→有限tag対応、
明示slotの再使用と互いに排他的なguardの扱い、実CircuitのNEW/field get-putへの接続が残る。
保守的な予約集合モデルを実Scalaの全ケースと同一とみなさない。
leaf検査と最終全体build成功（9074 jobs、exit code 0）。印字した公理は標準公理のみ。
実行中プロセスなし。

### 最新作業：共有heapのList解釈

`GalilScaffoldHeap.lean` はノード番号×有限slotをAddressとし、below pointer/tagを
一つのRootにまとめ、payloadを任意型としたheap解釈を追加する。
`Models` はrootからの有限List内容。`fresh_preserves` は未使用Addressへの書き込みが
全既存rootを保存すること、`push_with_alias` はpushと共有rootの内容保存、`pop` は
payload/belowの取り出し、`empty_iff` は空rootと空Listの対応を証明する。
根拠は `ScaffoldCircuitStructs.scala` のStackPool.allocateとStack.push/drop/copyFrom。
root import済み、全体build成功（9074 jobs、exit code 0）。印字した公理はpropextのみ、
または公理なし。実行中プロセスなし。

**未使用Addressの条件はまだ仮定。** 実回路のNEWノード・slot割当（同一ノード内の複数書き込みを含む）
がこの条件を満たすこと、tag選択とfieldのget/put、enabled=falseの挙動、既存Tape/Counter/InputHead
のList表現への合成は残る。これはStackPool全体の検証完了ではない。

### 最新作業：online head到達状態の配置不変条件

`GalilScaffoldInputTrace.lean` を追加。`Represents h word` は到着済み入力全体を
`xs.reverse ++ rs ++ incoming` と分解し、focus/左stackを`layout xs`、右stackを
`rs.map some`と対応づける。resetで成立し、append・右stack優先の右移動・FIFOからの
右移動・合法な左移動で保存される。`reachable_represents` は任意の到着/左右移動列に一般化。
`reachable_copy` はその到達状態から、別途layoutを仮定せずstack版copyが実行できることを証明。
この定理単独は停止・実行存在の契約であり、最終DP/PEG認識定理ではない。

**incomingを論理FIFOとして扱っている。Scala Queue.work/pop、物理Ref/StackPool、
predicated circuitとの対応は未証明。** copyFromの共有rootは物理層で扱う必要がある。
leaf検査・root import後の全体build成功（9073 jobs、exit code 0）。印字した公理は
標準公理のみ。実行中プロセスなし。

### 最新作業：focus・左右stackによるcopy実行

`GalilScaffoldInputHead.lean` を追加。`Head` は解釈済み入力参照（Option Fin2）のfocus、
左右Listスタック、抽象incoming Queueを持つ。`layout` は現在から左向きの文字列を
focusと「残りのsome列＋末尾none」の左スタックに配置する。
`moveLeft_at` はScalaと同じ「focusを右へpush、左をpopしてfocusへ」の意味を証明する。
`left_represent` はPlaceHeadのgap分岐を保ち、必要な左スタック非空条件も導出する。
`realize_copy` はPlace版copyの全実行をこの明示的stack版へ、同じ反復数・結果フラグ・
テープ・残量で持ち上げる。右スタックの更新は存在量化し、incoming Queueは不変。
leaf検査成功、印字した公理は標準公理のみ。root import済み、全体buildも成功
（9072 jobs、exit code 0）。`git diff --check`成功。実行中プロセスなし。

**まだ解釈済みListスタックであり、物理Ref/StackPoolの証明ではない。**
`layout` がreset・右移動・入力追加・copyFromで保たれる証明と、実Queue/物理セルのrefinementが残る。
この層の追加をonline入力供給全体の完成とは報告しない。

### 最新作業：letter/gap walkerの論理接続

`GalilScaffoldPlace.lean` を追加。根拠は `ScaffoldCircuitInput.scala` の
`InputHead` と `PlaceHead`、および `ScaffoldCircuitSearch.scala` のcopy分岐。
PlaceHeadは文字だけでなく隙間`s`を読む。gap=trueの左移動はheadを動かさずgap=falseへ、
gap=falseの左移動はInputHeadを左へ動かしてgap=trueへ進む。focus不在ならgapに関係なくNone。

`Place.letters` は現在文字から左向きの文字列を表す論理射影。`read_stream` / `left_stream` が
この2種類の移動と `s,letter,s,letter,...` のstreamを対応づける。
`runs` は任意Place/残量のcopy停止、`copy_sound` は既存Nat版copyへの実行対応を証明。
`copy_counter` は二スタックcounter版へ、`copy_ops` は原始テープ操作へ接続する。
**InputHeadの物理Ref、左右Stack、incoming Queueがこの射影を保つことはまだ未証明。**
したがってonline入力供給全体が完成したという意味ではない。次の実装接続ではこの表現不変条件が必要。
初回leaf検査、root import追加後の全体buildとも成功（9071 jobs、exit code 0）。
印字した4定理の公理は `[propext, Quot.sound]` のみ。実行中プロセスなし。

### 最新：Counterの修正・root検証完了

引き継ぎ後の継続で下記Counterエラーは修正済み。`zero_iff` / `negative_iff` の
`simp_all` 後に `omega` を追加し、leaf検査成功。
`GalilScaffoldCounter.copy_exact` を追加し、Nat版copyの正確なコピー範囲・残stream・残量・
finalStageを二スタックcounter版へ移した。root import済み。
**全体 `lake build` 成功（9070 jobs、exit code 0）。** 印字した公理は標準公理のみ。
実行中プロセスなし。次はonline walker・状態選択・物理StackPoolへの実接続。
Counterは依然として論理List表現であり、物理共有セルを検証したわけではない。

### 前回保存時点の記録（以下のCounterエラーは解消済み）

2026-09-14、ユーザーの引き継ぎ依頼に応じて証明追加を停止し、現物を再確認した。
**最新の作業ファイルは `lean-pal/PalPeg/GalilScaffoldCounter.lean`。未完成・root未import。**
今回 `lake env lean PalPeg/GalilScaffoldCounter.lean` を実行し、exit code 1を確認した。
現在実行中のLean/buildプロセスはない。過去のsession 44782を待つ必要はない。

CounterはScala `ScaffoldCircuitStructs.scala` のpos/neg二スタックを `List Unit` で解釈する。
`inc`/`dec`、整数値、Canonical（少なくとも片方が空）、正負・零判定、`ofNat`、
Nat版copyから二スタック版copyへの `realize_copy` を記述済み。
これは論理スタック表現であり、物理StackPoolの検証ではない。

確認した未解決ゴールは以下の4つだけ（このleaf検査の出力範囲）:

- 46行 `zero_iff`: `¬ -1 + -↑tail.length = 0` と `¬ ↑tail.length + 1 = 0`。
- 54行 `negative_iff`: `-1 < ↑tail.length` と `0 ≤ ↑tail.length + 1`。

両証明末尾の `simp_all [...]` の後に `omega` を適用するのが最初の修正候補。
**この修正はまだ実施・検証していない。** `inc_value` / `dec_value` / `realize_copy` の
公理出力は `[propext, Quot.sound]` だが、ファイル全体は失敗しているので完成扱いしない。

再開手順:

1. 上記2証明を修正し、Counterのleaf検査を通す。
2. 必要なら `realize_copy` と既存 `copy_exact` を合成し、残量・最終フラグまで明示する。
3. `PalPeg.lean` にCounterをimportし、全体 `lake build` と `git diff --check` を実施する。
4. 次の実接続はonline walker・状態選択・物理StackPool。以下の残件一覧に従う。

最後に確認済みの全体buildは **Counter追加前の9069 jobs成功**（以前の検証記録）。
今回の保存作業では全体buildを再実行していない。証明ファイルは変更せず、引き継ぎ文書のみ更新した。

**`GalilScaffoldLoad.lean`の旧型エラーは修正済み。** `load` / `load_source` / `load_lower`のleaf検査は成功し、root importにも追加した。標準公理のうち`[propext, Quot.sound]`だけに依存し、`sorryAx`はない。

修正は`home_exact`のcons枝で、`Home.left`の引数を`by simpa [moveLeft] using hr`として先に型合わせし、その後`convert`で結果のリスト・操作数を正規化したもの。古いエラーを再修正する必要はない。

継続して`GalilScaffoldLoading`を追加し、原始ロードをSOURCE/LOWERを持つプログラム全体へ接続した。
`load_program`は任意の旧状態を論理resetした後、LOWER→SOURCEの順で具体的DP初期配置へ到達する。
原始操作数は3*(lower+入力長)+8。`load_then_dp`がstartとpause付きの正しいDP実行へ接続する。
次はオンラインwalker・counter・copy/homeの状態選択回路との対応。供給payloadはまだ引数であり、controller全体の実装検証ではない。

続けて`GalilScaffoldCopy`を追加。論理streamと残量counterに対するguarded copyループの
コピー範囲・残stream・残量・finalStageを`copy_exact` / `final_iff`で証明し、
`copy_ops`で既存の原始操作へ、`copy_home`でbounded配置への巻き戻しへ接続した。
streamは読み取り順のList、counterはNatという論理表現。実walkerポインタ・物理counter・
predicated回路との対応は未完成。`finalStage`は残量0そのものではなく残stream空で決まる点に注意。

### 検証済みloaderの内容

`ScaffoldCircuitSearch.scala`のLOWER/SOURCEロードは、LEFTを書き、payloadをwrite+rightで並べ、ENDを書き、focusがLEFTになるまでleftする。

`GalilScaffoldLoad`には以下を書いた:

- `fill` / `fill_stack`: write+right列が左スタックへ逆順payloadを積む。
- `Run`: write/right/合法なleftの原始操作列。カウントはテープ操作数でありcontroller tick数ではない。
- `Home`: focus=LEFTなら停止、それ以外なら合法なleftを行うマーカー駆動ループ。
- `home_exact`: 内部payloadにLEFT=4がない場合の正確な巻き戻し。
- `load`: reset後のテープから`bounded xs`へ、原始操作数`3*xs.length+4`で到達する合成定理。reset操作自体のコストはこの値に含まない。
- `load_source` / `load_lower`: 実SOURCEのFin3記号列とunary下限へ特殊化し、LEFTがpayloadに含まれない前提を導出した。

これは供給されたpayloadのロード証明。オンラインwalker・work counter・状態選択回路が実際にそのpayloadを供給することは別途必要。

## 検証済みの到達点

以下はルートimport済みで、標準公理`propext`, `Classical.choice`, `Quot.sound`の範囲で検査済み。有限テストを一般証明の代わりにはしていない。

### 1. 実FPPカーネルとmarked FPP

- `GalilFppCode`: Scala由来の7テープ・228命令。`GalilFppGeneration`が任意入力の生成処理、`GalilFppChain.initial_completed`がborder列出力まで接続。
- `GalilFppMarked.prepared_kernel_exact`: `w ++ [#] ++ reverse w`のborderが、元入力の正の回文prefix長と過不足なく一致。
- `GalilFppMarkedCode`: `FppSubroutine.buildMarkedProgram("abs")`由来の9テープ・321命令、開始PC320。
- `GalilFppMarkTransform` / `GalilFppMarkSimulation`: 元の命令を実marked命令へ持ち上げる。A移動にMARKS移動を追加、emitをMARKSへの1書き込みに置換。
- `GalilFppPreparation`, `GalilFppPrepareCopy`, `...Rewind`, `...Cells`, `...Init`, `...Layout`: SOURCEだけの初期状態から準備・コピー・逆転・巻き戻しまで合成。準備は正確に`24*n+42`命令。
- **`GalilFppMarkedLayout.marked_fpp_exact`**: 任意の`List (Fin 3)`入力で実初期状態から停止し、MARKS全セルが正確。0位置LEFT、1..nは回文prefixなら1・それ以外0、n+1にEND、以後blank。終了PC0、SOURCE/MARKS頭0、SOURCE保存。
- **FPP全体の線形時間上界は未完成。** `GalilFppExecution.instructions_le_four_charges`は命令数≤4×ledger chargesを証明するが、全実行ledgerの線形上界がまだ必要。

### 2. 実DPの正しさ・最小性

- `GalilDpCode`: `DpFinite.buildDpProgram("abs")`由来の12テープ・373命令。開始320、成功halt346、失敗halt347、検索入口372。
- `GalilDpTransform`: 元321命令全検査、MARKS操作をSECONDにも実行する変換とFPP終了時の検索dispatch。
- `GalilDpSimulation`: marked FPPの任意実行をDPへ最大2倍の命令数で持ち上げる。
- `GalilDpFrames`: FPP領域で終了するprefixがLOWER/OUTPUT内容・頭を保存することを実コード領域の閉性から証明。
- `GalilDpPrepared.prepared`: SOURCEとunary LOWERのみを置いた実初期状態からPC372へ到達。両マークテープの正確さ、関連頭位置、LOWER保存、OUTPUT空白を保証。
- `GalilDpSearch`: 成功、下限スキップ、マーク0スキップ、終端失敗の実分岐。
- `GalilDpAdvance`: 出力1追加、MARKS+2、SECOND+4を14命令で行う。範囲内の次候補入口348まで15命令。
- `GalilDpExhaustion`: 範囲外の次候補で最大16命令の失敗停止。`exhausted_of_room`は初回h=0・長さ2以上にも使える。
- `GalilDpLoop.terminates`: 有効な正の候補hから検索ループが停止。検索命令数≤`18*(w.length-h)+19`。
- `GalilDpStart.initial_terminates`: 初回6命令・h=1への接続・長さ0..4を含め、実DP全体が任意入力・任意下限で停止。
- `GalilDpCounters`: OUTPUT全体=`^`+h個の1+blank、出力頭h、LOWER頭=min(cursor,lower+1)を追跡。
- **`GalilDpCorrect.initial_correct`**: 実初期状態から、`h>lower`, `4*h+1≤入力長`, 長さ`2*h+1`と`4*h+1`のprefixが回文、を満たす最小hを正確なunary出力で返す。候補が存在しなければ失敗する。
- `GalilDpSuffix.initial_correct` / `window_correct`: 逆順入力のprefix条件を元窓のsuffix条件へ接続。`w.reverse.take (span+1)`について、対応するsuffix窓内で最小候補を返す。

### 3. Scalaのテープ表現・制御への論理層での接続

- `GalilScaffoldTape`: 左右スタックをList、focusをFin9として解釈。read/focus、write、左右move、resetの非負位置テープ意味論を証明。
- `GalilScaffoldProgram.realize_completed` / `completed_sound`: 同じ命令表で、有限テープ実行と論理2スタック実行を双方向に接続。同じ命令列・命令数・最終テープ解釈。
- `GalilScaffoldControl`: enabled/doneプロトコル。haltでdone、停止後の呼び出しは不変。`scheduled_completed`は任意pauseを含む予定で有効tick数≥命令数なら完了する。`dp_scheduled`はDPの正しさを接続。
- **`GalilScaffoldPreload.scheduled_correct`**: 具体的なSOURCE/LOWERのスタック配置から、初期表現一致を前提とせずDPの正しさと任意pause実行を保証。
- **物理StackPool、共有セル、Scalaのpredicated circuitがこの論理層を実装することは未証明。** 新しい論理意味論を定義しただけで実回路の検証完了とは言わない。

## 本当の残作業と主経路

主経路:

```text
Scala ScaffoldCircuitGalil.buildOnline
  → ScaffoldEventBuffer.bufferSource
  → packService
  → GenerateOnlinePeg（未加工のab入力）
```

1. loaderの型エラー修正・root import、および`GalilScaffoldLoading`による全テープ構成への持ち上げは完了。
2. source/LOWERロードを具体的初期配置と結び、online walker・work counter・copy/home制御・reset/再利用を実装に即して証明する。
3. predicated instruction選択とStackPool/共有セルを論理2スタック実行へrefineする。
4. 実FPPを含む全体資源・時間上界を閉じ、online Galilの進捗・出力正しさ・期限を証明する。
5. 実FIFO、固定packing、最終StructuredMachineとPEGを接続する。

これは細部の残りだけではない。3〜5にはまだ大きな接続義務がある。
負例の回答が遅れること自体を欠陥としない。正例の期限と最終契約を守り、全入力でzero-lagを勝手に追加しない。

`lean-pal/PalPeg/Main.lean:43`の`pal_in_peg_of_structured`は依然として、PALを認識する具体的な`StructuredMachine M`と`hM`を要求する条件付き定理。**その具体例と全証明はまだ揃っていない。**

## Scalaの入口と記号

`scala/pal/src/main/scala/pal/`:

- `FppFinite.scala`, `FppSubroutine.scala`, `DpFinite.scala`: 実有限命令表。
- `ExportFppCode.scala`, `ExportFppCostCertificate.scala`, `ExportMarkedCode.scala`, `ExportDpCode.scala`: 実Scalaからのexporter。表を手で別物へ差し替えない。
- `ScaffoldCircuitGalil.scala`: online制御。DPとmarked FPPの両方を呼ぶ。
- `ScaffoldCircuitSearch.scala`: LOWERロード、walkerを左へ進めるSOURCEコピー、span+1の窓、home、DP run、倍増・待機。
- `ScaffoldCircuitProgram.scala`: start/reset、raw instructionStep、done、オプションのread-block実行。
- `ScaffoldCircuitStructs.scala`: Tapeの左右Stackとfocus。resetはroots clear+blank。左moveは左Stack非空を要求。右moveは空の右Stackからblankを補う。

記号`Fin 9`: a=0, b=1, s=2, #=3, LEFT=4, END=5, blank=6, bit0=7, bit1=8。
テープ: A0 B1 C2 S3 T4 BACK5 FRONT6 SOURCE7 MARKS8 SECOND9 LOWER10 OUTPUT11。
`ScaffoldCircuitGalil`が使用するFIRST等の追加記号や有限回路のalphabet拡張は、既存Fin9モデルとの接続で別途扱う必要がある。

## 検証・作業方法

Lean/buildプロセスは同時に一つ。遅いだけで再起動しない。liveなhandleをpollし、終了確認後に次を動かす。

```sh
cd /home/mizushima/repo/lean4-peg/lean-pal
lake env lean PalPeg/GalilScaffoldLoad.lean
# 成功後、依存ファイルから使う前にoleanを作る:
lake build PalPeg.GalilScaffoldLoad
# root importを追加してから全体検査:
set -o pipefail
lake build 2>&1 | tail -n 8
git diff --check
```

`lake env lean FILE`は`.olean`を作らない。依存変更後は`lake build PalPeg.Module`が必要。
`#print axioms`で`sorryAx`や独自公理を許さない。`native_decide`で証明を置換しない。
既存ファイル全体の無関係なlinter警告は残っている。全体ビルド成功と未importファイルの成功を混同しない。

既知の落とし穴:

- `GalilFppWide.Config`に自動extはない。`GalilScaffoldProgram.wide_ext`を利用できる。`apply wide_ext rfl`は推論で両辺を潰すことがあるので`apply wide_ext`後にpcを`rfl`。
- record更新の複数行で関数引数の継続インデントが浅いとparse errorになる。
- `read`は`MonadReader.read`と曖昧になる。simp内では`GalilScaffoldTape.read`を完全修飾する。
- `simpa using Constructor ... hr`は、内部引数`hr`の型エラーを外側のsimpで直せない。
- `List.replicate_succ`を明示的にsimpする必要がある場合がある。
- 大きな命令表を扱うファイルは`set_option maxRecDepth 100000`。`by decide`の有限証明に局所heartbeat増加がある。
- 初期化証明等が遅くても、同じビルドを複数起動しない。

Scala実行が必要なら`scala/`で一時runtime dirを使用:

```sh
task_runtime_dir=$(mktemp -d /tmp/pal-sbt-runtime.XXXXXX)
XDG_RUNTIME_DIR="$task_runtime_dir" sbt 'pal/runMain pal.ExportDpCode'
```

## 引き継ぎ時の検査範囲

引き継ぎ保存時は`GalilScaffoldPreload`までのroot build成功（9066 jobs）。
その後loaderのleaf検査に成功し、rootへ`GalilScaffoldLoad`を追加した。
**最新の全体ビルドは成功（9069 jobs、exit code 0）。** `GalilScaffoldCopy`を含む。起動したLean/buildプロセスは終了済み。
当時の`git diff --check`も成功。最新の未完成Counterと今回のleaf検査結果は冒頭の「最終保存時点」を参照。
古いsession IDをliveとみなさず、現在のプロセス状態を確認すること。

ユーザーへの報告は「何の前提が外れたか」「何がまだ未証明か」を明確に。追加ファイル数やbuild件数を大定理への距離の代わりにしない。
