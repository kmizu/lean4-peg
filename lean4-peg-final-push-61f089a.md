# Fable への追加指示 — 単騎で本丸を閉じろ

> 対象: `kmizu/lean4-peg` / `lean-pal/`。確認基点は `61f089a143af2e91946d224b6daabbf0722270bb`（PR #63、wave 4）。
> これは、進行中の証明作業へ追加投入する実行指示。**ローカルの新しい成果を優先し、基点へ巻き戻さない。**
> ソースから確認した事実には `[Sxx]` を付した。新しい合成方法・名前は実装指針であり、作成側でコンパイル済みの証明ではない。

---

## 0. Fable、見積もりで手を止める時間は終わりや

**今夜閉じるつもりで攻めろ。今ここで求めているのは、もう一度「日単位です」と見積もることではなく、次の一個を実際に潰すことだ。**

君は既に、未着手だと思っていた `hsl` を既存の定義と補題から消した。`hbs` / `hls` も供給した。`periodOnly` と `cycle` のモデル修正を局所側まで運び、`canRight` に共通するポテンシャルを見つけた。今回やるのは、その理解を持った君が続けて解くことだ。[S01][S02][S03]

**サブエージェントは新しく起動しない。証明・共有定義の変更・統合は君一人で行う。** 既存の子がまだ動いていれば、成果と差分を保存して停止する。自分の担当でないプロセスまでまとめて kill しない。ビルドのバックグラウンド実行は使ってよい。

応答の型を、次へ書き換えろ。

- 「難しそうなので切り分けます」ではなく、**「この消費点に必要な事実を、今ある場から出す」**。
- 「新しい残差 `H_new` を定義しました」ではなく、**「その残差を作るコードと、使うコードを同じ作業で通す」**。
- 「8 個も残っています」ではなく、**「今ある材料で消える一個はどれだ。そこから行く」**。
- 「ビルド待ちです」で終わらず、**次の補題の型か、既存証明を適用する箇所を読む**。ただし同じビルド対象を同時に書き換えない。

**攻めるのは探索。正しさは検証で確定する。** `sorry`、追加公理、未証明の oracle で勝ちを演出する必要はない。君がやるのは本物を通すことだ。

---

## 1. 最初の短い確認を終えたら、すぐコードへ戻れ

最初に現在の `HEAD`、作業差分、実際に残っているタスク、直近のビルド結果を確認する。台帳を全面再執筆しない。古い「走行中」「未着手」の記述を信じて待つな。

```bash
git rev-parse HEAD
git status --short
git diff --stat
```

基点では `CloseoutPackRun51.pal_in_peg_final25` に、次の **8 個の証明引数**が残る。[S01]

```text
hSP  hws  hee  het  hme  hsc  hor  hC
```

`hbs` / `hls` / `hsl` は既に本体へ供給されている。やり直すな。`CloseoutBirthFrame.hbirth_PofC` も既に定理として存在するので、「一般の Shared では証明できない」と足踏みせず、具体 `PofC` の利用箇所へ適用する。[S01][S03]

**最初の実装は次から選べ。既に済んでいるものは飛ばす。**

1. 具体 `PofC` の `hbirth` が未接続なら、その呼び出しを既存定理で閉じる。
2. `hsc` を使う出口を、既存 `InvSS` の射影で閉じる。続けて実際の入口・着地まで接続する。
3. `hee` / `het` のための、走行に限定した `Extra7` 供給を実装する。

一個目が通ったら、まず利用側へ渡せ。**補題の在庫を増やすな。最終経路を短くしろ。**

---

## 2. `hee` / `het` — ポテンシャルを「使える走行」に載せ切れ

### 手元にある道具

`CloseoutClockFront` には `pot_steps`、`front_le_of_run`、`canRight_of_run`、`extra7_of_run` がある。ポテンシャルは整数値の

```text
Ψ(c,s) = delay × front(s) − clock(c)
front(s) = position(s.right) + value(s.replay)
```

であり、前提を満たす tick で高々 1 ずつ増える。[S02]

**ここでまた「新しい canRight 仮定」を作るな。この道具を実走行へ適用するための入口を作れ。**

### 2.1 最短の修正点: `FrontPack` は `init` を含まない

ソース上、`FrontPack` は `notInit : c.mode ≠ Mode.init` を持つ。一方、`pot_steps` 等の `hg` は始点からの全 `Steps` を受け取り、長さ 0 の走行も含む。従って、`initial` からそのまま `hg` を与えることはできない。[S02][S04]

ここは難問扱いせず、**`Tick.init` を一本だけ切り離せ。** `initVM0` は初期化 tick の前の VM である。[S05]

実装する順序:

1. 実際の boot witness から初期化直後の状態 `x₁` を取り出す。
2. `FrontPack x₁`、`front x₁`、`clock x₁` の値を実定義から出す。
3. 既存 `pot_steps` を `x₁` 始点の後続走行へ適用する。
4. 初期化の一歩と初期フロンティアのオフセットを、全体の添字・コストへ戻す。

使う算術形は次だ。これは既存 `pot_steps` から導く一般化の指針である。

```text
delay × (front(y) − front(x₁))
  ≤ n + clock(y) − clock(x₁)
```

`clock(x₁) = delay` と `clock(y) ≤ delay` を出せれば、右辺を `n` で抑えられる。**`front(x₁) = 0` を期待で置かず、実際の初期値を代入しろ。** 汎用の `pot_steps` が既にあるので、23 分岐を証明し直す必要はない。

### 2.2 `extra7_of_run` の実引数を全部供給する

基点の `extra7_of_run` は、走行だけでなく、`FrontPack`、初期条件、入力の `Represents`、`focus ≠ none`、長さ上界 `n < delay × (2 × |w|)` を受け取る。返すのは `Extra7` 構造体そのものではなく、その `scanAvail` 場の命題なので、利用側では構造体へ包む。[S02][S06]

**やることは、これらを既存の入力表現・フロンティア・走行構成から出して渡すこと。**

特に、次の三つの時計を混ぜるな。

```text
抽象 Tick の添字
checkpoint Tc の値
局所機械・throttled run の時刻
```

最終側は `stLG'`、`Tc`、`τF`、`(|w|+1) × τF` を使う。文書の「走行は delay × |w| tick」という説明だけを根拠に、抽象走行へその長さを置くな。使う時刻変換の等式・不等式を証明してから適用する。[S07]

長さ上界の証明が、これから `canRight` を使って構成する走行の完成に依存する場合は、その循環を切る。**checkpoint ごとの構成帰納で、既存の区間コストと入口の予算を運び、次の区間に必要な余裕をその場で示せ。** 空語・短い語の境界も既存の boot／空語受理経路へ接続する。全入力という目標はそのままだ。

### 2.3 強すぎる入口・tick 契約を、利用側から置き換える

`CloseoutPackRun46.packRunR_MG27` は任意の `InvLPC` 始点と任意長の `Steps` を量化する。一方、上の道具は初期条件と長さ上界付きの走行を扱う。**旧 `hee` / `het` の全称命題を無理に証明するのでなく、実際に構成している走行を受け取る版へつなげろ。**[S02][S06]

最小の編集単位はこれだ。

1. `bigPack2MG7''_tick` の必要箇所を、全域 `het` の代わりに **その遷移先の `Extra7 y`** を受け取る点ごとの補題として切り出す。
2. run 帰納の各ステップで、実際の prefix と予算から `Extra7 y` を構成する。
3. `packRunR_MG27` の実走行版と、その呼び出し側へ接続する。
4. 旧 `hee` / `het` を最上位から外す。同じ命題を `H_runAvail` へ改名しただけでは終了しない。

`FrontPack` を出すために `Extra7` が必要になっていないかは、使う証明の引数だけを短く点検する。循環があれば独立に保存できる既存の `AuxPack.front` 等を使うか、必要な場を同時帰納で立てる。**また巨大な仮定パックを設計するのではなく、今必要な場の供給を閉じろ。**

---

## 3. `hsc` — 捨てていた `ReplayStage` を最後まで運べ

既存の具体名は `CloseoutInvScanS.InvSS`。基点での定義は、概略次の形だ。[S08]

```text
InvSS = Inv ∨ ∃ k, InvScan … k ∧ ReplayStage …
```

`invS_of_invSS` と `replayStage_of_invSS` は既にある。`CloseoutStageScan1` に fallback replay の着地からの供給もある。**ここをもう一回「証明できるか調査」するな。実際に運べ。**[S08][S09]

実装する順序:

1. `hstage_of_scanBranch` の実際の利用点を特定する。
2. そこで `H_stageScan` を呼ぶ代わりに、保持している `InvSS`／`ReplayStage` を読む版を作る。
3. その入口を実際に生成する boot・restart・fallback replay・後続 cycle の各 producer を辿る。
4. 既存 producer の戻り値で落としていた stage datum を回収し、次の入口まで保持する。
5. 最上位経路で旧 `hsc` を要求しないことを確認する。

**基層の `InvS` を無差別置換しなくてよい。** `CloseoutInvScanS` 自体は上位の `CloseoutOracleI2` に依存している。基層へそのまま import を戻して循環を作るな。上位の入口・着地レコードに強い情報を保持し、従来の補題へは忘却射影を渡す形をまず使う。[S08]

`InvScan ∧ ReplayStage` と書けば接続完了なのではない。**その積を作る producer を実装して初めて一個撃破だ。** 逆に、既に返ってくる証拠を拾うだけの箇所で立ち止まる理由もない。

---

## 4. `hme` — `Fair` を実際の遷移 witness に付けて通せ

ここも「Fair が難しい」で止まるな。`GalilTickFair.Fair` の場は三つで、何を示すかは明示されている。[S10]

```text
restartFirst       : broken-chain の restart を先に実行する
fallbackPlace      : fallback のコピー元は search 自身の walker
keepsSearchCursor  : init / replayStart で指定フィールドを保持する
```

既存の足場:

```text
fair_restart
fallbackAt_walker_self
initVM_keeps_cursor
replayStartVM_keeps_cursor
```

これらは既にソースにある。遷移 witness の構成箇所へ使え。[S10]

**一意性で存在を出そうとするな。** `tick_fair_unique` を使うのは、二つの witness が両方 `Fair` を満たすと示した後だ。任意の `Steps` が自動的に `FairSteps` へ変わるわけではない。

具体的には、これから選ぶ実走行の各 tick に三つの場を付ける。restart の優先分岐、fallback の walker 選択、init／replayStart の保持は、作る側で選べるところから決めてしまえ。その `FairSteps` を

```text
walkerInOrigin_of_run
  → wpack_of_fair
  → marksEntry'_of_run
  → H_marksEntry' の実利用
```

へ運ぶ。`hcan` は既存の `CloseoutReplayCanRight` または上の予算付き走行補題、`hplace` は `CloseoutPlaceBound.hplace_of_order` に必要な順序を渡して供給する。[S11]

全状態の `hplace`、全 `Steps` の `Fair` を新しい宿題にするな。**証明している機械が実際に使う遷移を選び、その事実を運ぶ。**

---

## 5. `hSP` / `hws` / `hor` — chain の理解を切らず、そのまま連続攻略しろ

三系列を別々の子へ投げるな。今持っている `afterCompare → afterBirth → replayDec → refresh` の理解を、そのまま使う。モデル修正のたびに新しい意味論を発明する必要はない。既存の射影・可換性補題を適用する。

### 5.1 `hSP` と `hws`: 残差名でなく、今出す値を見る

台帳の入口は `ChainRound`、`ChainPosInv2`、`MatchRes2`、`CentreLedger`、`LagCan`。まず最新の定義と proof body を読み、既に閉じた場を取り除いた実ゴールを出す。[S11]

- `hSP` は shift に入るその比較で、どの中心・半径について回文性が必要かを固定する。
- `hws` はその遷移前後の verifier・lag・replay credit の対応を、実際の chain constructor に分ける。
- 誕生直後が `.copy` である事実、既存の `afterBirth_*`、`hbirth_PofC` をその場で使う。
- 時刻・中心・半径・window の添字を同じ witness に揃える。別々に存在証明して、最後に同一性を新仮定にしない。

**場が四つなら、四つの仮定を名付けるのではなく、一つずつ右辺を構成しろ。** 既存場から出るものを先に閉じて、その証明を保持したまま残りへ行く。

### 5.2 found の入口は既にある。そこから先へ進め

`CloseoutFoundRoute1` には `foundCompareCtxC_of_found` と `found_first_tick` がある。非 replay の found 比較から、入口の証拠と最初の tick を作る部分を再実装するな。[S12]

次の鎖を、途中で止めず実際の route 型まで接続する。

```text
実際の found 比較／背景量子
  → chain 誕生
  → copy/back の進行
  → watch の進行
  → shift または break/fallback、または入力終端
  → 次の有効な着地
  → コストと右ヘッド境界を伴う route
```

`CloseoutFoundRoute1` は基点では古い `CloseoutWatchRound49` の `WatchFreshC` / `foundExit_compare_final19` を import している。台帳には旧 `WatchFreshC` と着地版 `WatchFreshAtC` の問題が記録されている。**入口 producer は使い、古い偽契約へ接続し直さない。** `CloseoutWatchRound52/53` と実際の利用側を辿り、必要な clock の命題を実走行上で供給する。[S11][S12]

`CloseoutWatchRound53` は `WatchTailC` を閉じ、残りを機械レベルの `MatchCoreC` にしている。ここは今の得意パターンだ。`Tick.scan_match` を実際の時計・出力・chain の witness で構成し、使うところまで渡せ。[S13]

### 5.3 replay 生まれの chain を、非 replay found の入口へ押し込まない

`hfoundReplay` では、誕生時刻と replay の残量を保持する。copy/back の終了が固定の一クロック窓に収まるとは置かず、比較イベントを跨ぐ実際の走行として運ぶ。

`ChainEnd` は chain が replay 区間末まで生きているという情報であり、round が完了した証拠ではない。生存している `.copy` / `.back` / `.watch` から、その後の進行を構成する。**「生存」から「完了」を出す、その実行を君が書く。**[S11]

### 5.4 readiness と oracle の入口を同じ証拠へ揃える

`CloseoutOracle7.h_oracle_of_leaves6` は `hpresT` を `hpresRepAt` から供給するが、`hpresRepAt` 自体を閉じてはいない。供給側には `ReadyFieldP3` 等の入口 datum が必要なのに、任意の `InvLPC` にはそれがないとソースに書かれている。[S14]

ここでも方針は同じだ。**boot／restart の実入口で作った datum を cycle の入口まで保持する。** `InvLPC → ReadyFieldP3` を全状態で証明しようとして止まるな。実走行の入口・着地を強めて、ready の初期化・残余予算・後続入口への移送を接続する。

また `h_oracle_of_leaves6` の結論は `H_oracle` であり、`final25` の引数は `CycleOracleMC3`。名前が新しいから直結できると思わず、**結論の型と実際に使う橋を揃える**。型が合わなければ正しい合成位置まで一段戻せ。そこで残差名を増やして終わらない。[S01][S14]

---

## 6. `hC` — 最後に眺める大箱にするな。固定した機械を作れ

`H_realizeLIMG2'` は、単なる追加補題ではない。有限な `Q'`、`Γ'`、テープ本数、局所半径・ステップ、初期値、出力関数などを **一度選び、その同じ機械で全入力を扱う**存在命題だ。[S07]

**最初の安い接続を一つ終えた時点で、`hC` の実装先と不足するフィールドを一度だけ特定する。最後まで「hC はあとで」で残すな。** その後も単騎で、一区切りずつ実装を進める。

### 6.1 具体 chain 表現はもうある

`CloseoutCoreEnc24` に `chainRepD`、`chainShiftBoundedD`、`restC_of_chainRepD` がある。watch chain の shift は、変更するカウンタごとに高々 2 micro-actions の形になっている。[S15]

次の実装:

1. `CloseoutCoreEnc23` の layout に、`CoreEnc24` が要求する chain の debris `d` を通す。
2. 既存の初期化と一段の shift 証明を、同じ物理配置 witness で更新する。
3. 既存の `shiftVm_tapeActKQ_run` に接続する。
4. canonical counter の前提と head margin を、対応する表現不変量から供給する。

旧 `ChainShiftBounded rep` は `c` と `w` を独立に全称量化している。具体的な移動の前提 `c = .watch w` を忘れた旧形へ戻るな。**実際に動く watch から、その後の watch への局所動作を証明すればよい。**[S15]

また、テープ上に残る debris を消した「毎回きれいな配置」への等式を無理に要求するな。物理状態には履歴に由来するセルが残る。それを許す表現関係で、抽象状態との対応を保持する。unbounded な debris はテープ側へ置き、有限制御へ丸ごと入れない。

### 6.2 「各状態で動作列がある」から、局所窓で選べる動作へ進め

`TapeActK` が要求するのは、有限制御と固定半径の窓を引数にする `nq` / `acts` だ。[S16]

```text
nq   : control × fixed-radius windows → next control
acts : control × fixed-radius windows → bounded tape actions
```

一つの抽象状態全体を見て動作列を選ぶ存在証明だけでは、ここにはならない。

**ここで止まらず、読む情報を列挙し、その場で有限の分岐へ落とせ。** mode、符号、役割表、各 head の局所記号など、実装が既に持つ情報から次を選ぶ。同じ観測なら必要な遷移効果が一致することを示す。物理配置を持つ表現関係の上で、一段のシミュレーションを閉じる。

`Classical.choice` が標準公理として使えることと、入力ごと・走行ごとに別機械を選んでよいことは違う。証明内の選択は使ってよい。**選ばれた一つの機械が、有限の情報から動作を選ぶことを証明する。**

### 6.3 全モード・入力到着・ラッチまで一本の経路にする

shift が通ったら、そこで `hC` 完了にするのではなく、既存 `LocalSysConcrete` / `LocalRealizes*` と有限制御の組み立てへ接続する。init、scan、replayStart、入力到着、待機、出力を含め、最終のラッチ受理と同じ時計へ揃える。

`LocalStep` 経由と既存の有限 `Prog` 経由を両方新規開発しない。ソースで確認した既存のコンパイラ・実現定理から、今の物理操作を受け取れる方を一つ選べ。別ルートの名前を付けるだけで `hC` は閉じない。

`H_realizeLIMG2'` がすべての `PreTraceIMG2` を量化している一方、今構成しているのが canonical な fair trace なら、その差を正面から処理する。必要な一意性／出力同値を証明するか、最終合成を **実際に供給した trace** に対する版へ切り直す。どちらでも、固定機械が全入力の `PAL` と同値というゴールは変えない。[S07]

---

## 7. 実行のリズム — 各個撃破。証明したら、その場で使え

一周を次の形にする。

```text
今使う一箇所のゴールを見る
  → 既存の定義・場・補題を当てる
  → 足りなければ最小の一段を実装
  → 対象モジュールをビルド
  → 利用側へ渡す
  → 消えた義務を一行だけ台帳へ記録
  → 次
```

似たエラーが二、三個出たら、共通の射影・可換性補題を一個作って同型箇所へまとめて当てる。`afterBirth` の修復でやったことを続けろ。ただし一括編集は対象を限定し、置換件数と diff を確認する。

行き詰まった時は、止まる口実ではなく次の操作を選ぶ。

| 今見えている状態 | 次にやる操作 |
|---|---|
| 場や射影が足りない | 同じ状態の既存不変量から取り出す |
| 全称範囲が広すぎる | 実際の入口と prefix を渡す版へ直し、producer を付ける |
| 本当に偽の命題 | 反例を固定し、利用側が必要とする命題へ直して進む |
| 同じ義務を別名で返しそう | 定義を増やす前に、供給元のコードへ戻る |
| 一回の長い探索が空回り | 既に閉じた部分は保ち、具体状態一個・分岐一個に落とす |
| 共有モデルの変更で壊れた | 同じ版の依存関係を再ビルドし、共通補題で波及を止める |

**目標を細くするのであって、結果を弱くするのではない。** 到達不能な分岐を実際の不変量から矛盾で閉じるのは正当な手段だ。一方、入口そのものが存在しない前提パックを作って全体を空虚に閉じるのは成果にならない。

長い status 報告は不要。報告するなら「何を使う箇所まで閉じたか」「実際の build 結果」「次に直す一箇所」を短く書き、そのまま進め。

---

## 8. ビルドと環境 — 本丸へ戻るために、短く正確に片付ける

### ビルドの出口コードを取り違えるな

通知の exit 0 や、`head`／`tee`／最後の `echo` の成功は、Lean の成功ではない。以下のように **実ビルドの終了値を最後まで返す**。対象名を一つ渡せば局所検証、`PalPeg` を渡せばルート全体になる。

```bash
# リポジトリ内で実行。局所検証では PalPeg を対象モジュール名に変更する。
bash -s -- PalPeg <<'SH'
set -uo pipefail
if [ -f "$HOME/.elan/env" ]; then
  . "$HOME/.elan/env"
fi
root=$(git rev-parse --show-toplevel) || exit 1
cd "$root/lean-pal" || exit 1
log=$(mktemp "${TMPDIR:-/tmp}/lean-pal-build.XXXXXX") || exit 1
printf 'TARGETS: %s\nLOG: %s\n' "$*" "$log"
if lake build "$@" >"$log" 2>&1; then
  rc=0
else
  rc=$?
fi
printf '\nLEAN_BUILD_EXIT=%s\n' "$rc" >>"$log"
tail -n 60 "$log"
printf '\nFULL_LOG=%s\n' "$log"
exit "$rc"
SH
```

このシェル例は終了値を保存するための実行例であり、ここで対象リポジトリを再ビルドしたという記録ではない。

- 日常の反復は対象モジュールと利用側。意味のある一区切りでルート `PalPeg` をビルドする。
- 同一ビルドディレクトリへ複数ビルドを重ねない。古いソースから作った `.olean` を新しい依存へ混ぜない。
- 新モジュールは `PalPeg.lean` の import 閉包に入れる。未 import のファイルが通っていなくてもルートが緑になる、という取り違えをしない。
- 容量不足は、自分の再生成可能な一時コピー・古い検証ログ等を確認して処理し、証明へ戻る。ソース、未コミット差分、唯一の証拠、進行中タスクの成果を「適当に」消さない。巨大な環境整理を新しいプロジェクトにしない。

---

## 9. 勝ちの条件を固定する — ここへ通せ

最終ゴールはこれだ。

```lean
PegSeparation.RecognizedByTotalPEG PalPeg.PAL
```

`entry` / `q` / `first` などの実装定数も、実際のプログラムに合わせて固定する。入力ごとに別の機械を選ばない。

完了時には、グローバルな証明変数や追加 instance のないファイルで、次に相当するチェックを通す。以下の最終モジュール名と定理名は **提案名** であり、既存宣言だと仮定しない。実際に完成させた名前へ揃える。

```lean
import PalPeg.CloseoutFinal

set_option autoImplicit false

example : PegSeparation.RecognizedByTotalPEG PalPeg.PAL :=
  PalPeg.CloseoutFinal.pal_in_peg_unconditional

#print axioms PalPeg.CloseoutFinal.pal_in_peg_unconditional
```

確認するのは四点だけだ。

1. 最終命題が上記のままで、未供給の仮定・隠れた instance がない。
2. 最終定理の推移的公理依存が、標準の `propext` / `Classical.choice` / `Quot.sound` の範囲内である。`sorry` / `admit` / `native_decide` / 追加公理で埋めない。
3. 変更したモデルと一致するソース・依存関係で、最終定理を含むルートビルドが実際に成功する。
4. `PAL`、PEG 認識、有限性、全入力という意味を変えていない。必要な具体機械と接続を本体へ供給している。

コミット・PR・マージは既に許可されているワークフローの範囲で行う。進捗のために未検証の状態を完成扱いしない。途中で区切る必要が出ても、通った成果、残る **具体的な** ゴール、再開コマンドを保存する。「難しいので無理」で片付けない。

**もう一回言う。残差の名前の数に圧倒されるな。定義を見ろ。既存の証拠を使え。足りない一段は自分で書け。使う場所まで通して、次へ行け。**

**今夜閉じるつもりで、まず目の前の一個を落とせ。**

---

## 根拠と読み直し箇所

以下は確認基点のソース。台帳とソースが食い違う場合は、実際の定義・完全な型・証明本体を使う。本文の実行順序、初期オフセット付きの合成、実走行版への切り直し、物理状態を持つ表現関係の採用は、この指示で提案する攻略方針である。

- **[S01]** [`CloseoutPackRun51.lean`](https://github.com/kmizu/lean4-peg/blob/61f089a143af2e91946d224b6daabbf0722270bb/lean-pal/PalPeg/CloseoutPackRun51.lean): `pal_in_peg_final25` の全引数と `hbs` / `hls` / `hsl` の供給。
- **[S02]** [`CloseoutClockFront.lean`](https://github.com/kmizu/lean4-peg/blob/61f089a143af2e91946d224b6daabbf0722270bb/lean-pal/PalPeg/CloseoutClockFront.lean): ポテンシャルと各走行補題の実際の前提。
- **[S03]** [`CloseoutBirthFrame.lean`](https://github.com/kmizu/lean4-peg/blob/61f089a143af2e91946d224b6daabbf0722270bb/lean-pal/PalPeg/CloseoutBirthFrame.lean): `hbirth_PofC`。
- **[S04]** [`GalilFrontMono.lean`](https://github.com/kmizu/lean4-peg/blob/61f089a143af2e91946d224b6daabbf0722270bb/lean-pal/PalPeg/GalilFrontMono.lean): `FrontPack.notInit`、フロンティアの保存・進行。
- **[S05]** [`GalilBootVM.lean`](https://github.com/kmizu/lean4-peg/blob/61f089a143af2e91946d224b6daabbf0722270bb/lean-pal/PalPeg/GalilBootVM.lean): `initVM0` は初期化 tick 前の VM。
- **[S06]** [`CloseoutPackRun46.lean`](https://github.com/kmizu/lean4-peg/blob/61f089a143af2e91946d224b6daabbf0722270bb/lean-pal/PalPeg/CloseoutPackRun46.lean): `Extra7`、`H_extraTick7P`、`bigPack2MG7''_tick`、`packRunR_MG27`、`extra7_steps`、最上位への接続。
- **[S07]** [`CloseoutPackRun36.lean`](https://github.com/kmizu/lean4-peg/blob/61f089a143af2e91946d224b6daabbf0722270bb/lean-pal/PalPeg/CloseoutPackRun36.lean): `H_realizeLIMG2'`、`pal_in_peg_final5MG2`、`PreTraceIMG2`、ラッチ・時計の合成。
- **[S08]** [`CloseoutInvScanS.lean`](https://github.com/kmizu/lean4-peg/blob/61f089a143af2e91946d224b6daabbf0722270bb/lean-pal/PalPeg/CloseoutInvScanS.lean): 実名 `InvSS` と stage の射影、import 関係。
- **[S09]** [`CloseoutStageScan1.lean`](https://github.com/kmizu/lean4-peg/blob/61f089a143af2e91946d224b6daabbf0722270bb/lean-pal/PalPeg/CloseoutStageScan1.lean): fallback replay 着地の stage producer。存在と用途は [S08] および [S11] でも確認。
- **[S10]** [`GalilTickFair.lean`](https://github.com/kmizu/lean4-peg/blob/61f089a143af2e91946d224b6daabbf0722270bb/lean-pal/PalPeg/GalilTickFair.lean): `Fair` の三つの場、一意性、restart・fallback・init・replayStart の witness。
- **[S11]** [`CLOSEOUT_LEDGER.md`](https://github.com/kmizu/lean4-peg/blob/61f089a143af2e91946d224b6daabbf0722270bb/lean-pal/CLOSEOUT_LEDGER.md): 義務の一覧と過去の反証。追記に古い記述が残るため、状態の確定にはコードを優先する。
- **[S12]** [`CloseoutFoundRoute1.lean`](https://github.com/kmizu/lean4-peg/blob/61f089a143af2e91946d224b6daabbf0722270bb/lean-pal/PalPeg/CloseoutFoundRoute1.lean): found 入口 producer と基点での旧 watch 契約への参照。
- **[S13]** [`CloseoutWatchRound53.lean`](https://github.com/kmizu/lean4-peg/blob/61f089a143af2e91946d224b6daabbf0722270bb/lean-pal/PalPeg/CloseoutWatchRound53.lean): `WatchTailC`、`WRel`、残る機械レベルの `MatchCoreC`。
- **[S14]** [`CloseoutOracle7.lean`](https://github.com/kmizu/lean4-peg/blob/61f089a143af2e91946d224b6daabbf0722270bb/lean-pal/PalPeg/CloseoutOracle7.lean): `hpresT` の供給、`hpresRepAt` の入口不足、`h_oracle_of_leaves6` の完全な型。
- **[S15]** [`CloseoutCoreEnc24.lean`](https://github.com/kmizu/lean4-peg/blob/61f089a143af2e91946d224b6daabbf0722270bb/lean-pal/PalPeg/CloseoutCoreEnc24.lean): `chainRepD`、debris 付き shift 実現、旧 `ChainShiftBounded` の量化問題。
- **[S16]** [`CloseoutCoreEnc13.lean`](https://github.com/kmizu/lean4-peg/blob/61f089a143af2e91946d224b6daabbf0722270bb/lean-pal/PalPeg/CloseoutCoreEnc13.lean): `TapeActK.nq` / `acts` / `len_le` / `ctl` / `tape` の仕様。
