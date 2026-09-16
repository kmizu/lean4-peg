# Fable 5 引継ぎ — PAL 判定機・SCA・PEG の Lean 4 形式化

> 2026-09-14: Claude Code向け最新の再開情報は [CLAUDE_RESUME.md](CLAUDE_RESUME.md)。実DPの正しさ・最小性、論理スタック初期配置、原始ロード操作まで検証済み。loaderの旧型エラーは修正しroot importへ追加した。以下の古い記録と区別する。

## 有限な後処理プログラム（2026-09-08）

`GSPreprocessProg73.finiteEpilogue_spec` は、固定プログラムによる周期・到達範囲の
正規化とパターン2本の消去を証明。周期が0なら残り文字を走査して `L-s+1` を
カウンタに構成し、到達範囲を0にする。その他のテープは厳密に不変で、
動作数は `6*L+2*r+11` 以下。ゼロ判定のprobe/restoreも動作数に含む。
標準3公理のみのguardと `lake build --quiet PalPeg` が成功。
分解器本体の15テープ有限制御への埋め込みと、中央区間・
ライフサイクル・全体機械への接続は未完了。

## 有限な初期化プログラム（2026-09-08）

`GSPreprocessProg69.finitePrologue_spec` は、入力長に依存しない有限プログラム
`finitePrologue` が `PrepPre` から分解器の初期 `EncS` を構成することを証明。
2本コピー、番兵設置、ヘッド整列、入力ヘッドの復元を含み、動作数は `8*L+12`。
テキスト2本は厳密に不変。入力にblankが現れないという仮定は不要で、
開始・終了番兵がパターン中に現れず、互いに異なることを用いる。
標準3公理のみのguardと `lake build --quiet PalPeg` が成功した。
分解器の15テープ上の有限制御への埋め込み、中央区間・ライフサイクル・
全体機械への接続は引き続き未完了で、無条件のPAL認識定理の完成は主張しない。

## 最新の追記：12テープ前処理の接続（2026-09-08）

符号つき差分カウンタの初期化・第2相・終了清掃を `stepProg_spec` から
`decProg_spec` / `decompose2_on_tapes` まで接続した。全体の動作数上界は
`(23*k+120)*decompose2Work + (7*k+24)*(n+1)`。
`StageTapes.PrepPre` の補助3テープの零条件を、段生成と `PrepInstance` まで接続。
中央区間用 `DecompInstance` / `DecompUniform` も3テープのマーカー初期化と
コストを更新し、`lake build PalPeg.DecompUniform` が成功した。
`DecompUniform` を通常の `PalPeg` ルートの import に追加。

`GSPreprocessProg4.SCAN_spec` では内側走査全体を固定の有限 `SCAN : Prog A9 Cond9`
として実装。停止判定用の2本の probe と復元を含め、元の `sProg` と終了テープ状態が
一致し、コスト `27*sWork+4` を証明した。入力長は停止証明の fuel にのみ現れ、
プログラム値には現れない。公理は標準3種のみ。`GSPreprocessProg4` もルートへ追加。

`PERIOD_SIGNED_spec` は周期ずらしを `Cf` 駆動の有限プログラムとして実装し、
位置と符号つきカウンタの更新、周期値の復元、操作数 `n*(3*k+10)+4` を証明した。
`k` のみをプログラムの定数とし、周期長 `n` は実行時のテープから読む。
この定理も標準3公理のみを guard で確認し、ルートの全体ビルドが成功した。

`GSPreprocessProg5.SHIFT_SIGNED_spec` は再配置後半を `Ce` 駆動の有限プログラム
として実装し、元の符号つき移動ループとの終了状態の一致と
操作数 `n*(3*k+7)+2` を証明した（標準3公理の guard 付き）。
`MAX_ONE_exec` は移動量を最低1にする有限分岐を実装。
巻き戻し用には `GSPreprocessProg6.QBLOCK` の実行・状態・カウンタ減少・
コストを証明した。

`GSPreprocessProg7.QGROUP_spec` は固定ブロックをカウンタ駆動で繰り返し、
任意の意味的不変条件を保存する有限ループの定理。
`GSPreprocessProg8.REWIND_SIGNED_spec` で巻き戻し全体（位置・符号つき差分・
Ce へのブロック数の記録）を接続し、操作数 `15*n+2` を証明した。
`GSPreprocessProg9.RESET_SIGNED_spec` は巻き戻し、最低1への補正、ずらしを合成。
終了位置と SignedOK に必要な差分更新、および操作数
`15*q+7+(3*k+7)*shiftNoPeriod q k` を証明した。
両定理とも標準3公理のみを guard で確認。Prog7/8/9 をルートへ追加し、
`lake build --quiet PalPeg` の全体ビルドも成功した。

`GSPreprocessProg10.TRY_DEC_exec` は固定個数の減算と失敗時の巻き戻しを実装。
成功時のカウンタ値、失敗時の厳密な全テープ復元、他テープの保存、
`3*min(k,n)+2` の動作数上界を証明した。`Cq` 上の EncS 保存も接続。
これは比較器の下位部品であり、周期ずらし判定の有限比較器自体はまだ作業中。

`GSPreprocessProg11` で倍率比較の完了組数を形式化。
`scaledGroups_complete_iff` は比較結果との同値、`scaledGroups_eq_min_div` は
`min(a,b/k)` との一致（`k>0`）、`scaledGroups_restore` は減算量の復元、
`scaledGroups_work_bound` は検査する総量の上界を証明する。
`CMUL_LE` は Ce だけを scratch に使う有限プログラム候補として定義した。
失敗時は左カウンタの probe 位置に一時マーカを置いて停止させ、Ce のフラグで
成功・失敗を区別する。算術部分に続き、下記 Prog12 で有限実行まで接続した。

同ファイルで失敗停止用の仮マーカと scratch フラグを消す全状態復元、
成功した `TRY_DEC` を `k` 回の増加で巻き戻す全状態復元を証明した。
復元部分 `CMUL_RESTORE` は有限実行・左右の値 `a+e` / `b+k*e`・scratch のゼロ化、
動作数 `e*(k+3)+2` まで接続。これらの主要定理は標準3公理のみ。

`GSPreprocessProg12.CMUL_LE_spec` で比較本体を復元へ接続した。
有限プログラムが `k*a≤b` に対応する継続へ進むこと、実際の出力状態との一致、
左右のカウンタ値の復元、Ce のゼロ化、残り9本のテープ保存を証明。
ループ回数は `scaledGroups` と一致し、比較部分の動作数は
`g*(4*k+10)+3*min(k,b-k*g)+11` 以下。`k>0` なら `14*b+11` 以下、
`k=1` なら `14*a+14` 以下で、過大なもう片方の値には依存しない上界が使える。
主要定理の公理監査は標準3公理のみ。

`GSPreprocessProg13.ORC2_oracle_spec` で周期ずらしの複合判定を有限化。
`k*Cf≤Cq ∧ Cq≤Cr` を二つの比較器で実装し、`orc2R` と同じ分岐、
`EncS` 全体の保存、実際の出力状態との一致、`28*Q+25` の動作数上界を証明。
前提は `k>0` と scratch の `Ce=0`。第2相の外側ループへの接続は未完了。

`GSPreprocessProg14.SABORT_exec` は周期発見判定を有限の条件分岐へ接続。
2本の probe と復元は合計4動作で、分岐前の全テープを厳密に復元する。
`GSPreprocessProg15` は外側の guard を `Ce=0 ∧ p<|x.drop s|` に結び、
有限ループの停止・継続・終了時のヘッド復元を証明した。主要定理は標準3公理のみ。
`SECOND_OUTER` の有限な構文は定義したが、全体の意味・線形コストは未証明。
特に `ORC2` の `28*q+25` を毎反復に加算するだけでは、周期ずらしを連続して
行う場合の線形上界を導けない。逐次更新する `r-q` の符号などによる
定数時間の `q≤r` 判定へ改良する必要があり、この候補を完成版とは扱わない。

`GSPreprocessProg16/17` で1テープの符号つき単進カウンタを実装。
原点マーカーで大きさを保持し、現在のヘッドの blank/mark で正負を表す。
`oneInc_spec` / `oneDec_spec` は差分 `M-N` の加減算、
`oneInc_exec` / `oneDec_exec` は固定の有限プログラム実行を証明した。
正負・ゼロの境界を含め、各更新は最大4動作。他の11本のテープも保存する。
`OneSgn_nonneg` により `r-q` をこの表現で保持すれば `q≤r` をヘッド読みだけで
判定できる。スキャン・巻き戻し・周期ずらしへの逐次更新の接続はまだ必要。

`GSPreprocessProg18.ORC2_FAST_spec` は `Cr=r-q` を読む新しい有限比較器。
`EncR` は他の11テープの意味を保ち、`q=0` で元の `EncS` へ戻せる。
比較結果・`EncR` 保存に加え、成功枝の操作数を `(4*k+10)*first+3*k+11`、
失敗枝を `14*q+11` 以下と証明し、周期ずらし時の `q` 全体への課金を避けた。
`GSPreprocessProg19/20.SCAN_R_spec` は走査と同時に差分を更新する有限プログラム。
位置、SignedOK、`Cr=r-q` を同時に保存し、操作数 `17*sSteps+4` 以下を証明。
新しい比較器とスキャンの主要定理は標準3公理のみ。
この走査を巻き戻し・周期シフト・外側反復につなぐ証明は下記22–32で追加した。

`GSPreprocessProg21.oneIncTrace_exec` は任意のテープ状態から動作列を取り出す
符号つき加算の実行定理。符号表現が妥当なら元の `oneIncL` と一致し、
加算の意味と最大4動作・他テープ保存を保つ。これは既存の汎用カウンタループへ
巻き戻しの差分更新を合成するための部品。

`GSPreprocessProg22–24` で `Cr=r-q` を保つ有限巻き戻しとリセットを証明。
`REWIND_R_spec` は任意の `q` に対し最大 `19q+2` 動作で通常の `Cr=r` に戻る。
`GSPreprocessProg25–27` は周期シフト後の差分更新と `SignedOK` の維持を証明。
`PERIOD_R_spec` の上限は周期長 `f` に対して `(3k+17)f+8`。
`GSPreprocessProg28–32.SO_RUN_R_spec` は、この新しい有限外側ループについて
参照 `secondOuter` との結果一致、十分な証明用fuelに対する停止、および
`L.length + (7k+100)q_final ≤ (10k+200)secondOuterWork + (7k+100)q_initial`
を証明した。実行プログラムには入力依存fuelや入力長は含まれない。
`GSPreprocessProg33–35.SECOND_SEARCH_spec` は出口の通常形式への清掃まで合成した。
最終状態は `EncS`、`q=0`、元の成功フラグを保存し、SignedOK・結果一致を保つ。
清掃込みで `L.length ≤ (10k+200)secondOuterWork + (7k+100)q_initial + 13`。
これらの主要定理の公理検査は標準3公理のみ。
第1相・分解器への接続・全体機械の未実装を解消したという意味ではない。

`SECOND_SEARCH_linear` は具体的な第2探索の清掃込み操作数を入力長で評価する。
`n = (x.drop s).length`、`k≥3`、正の開始候補と入力内の両ヘッドを仮定し、
上界は `((10k+200)(2k+5)+(7k+100))*n + (10k+200)(k+2)+13`。
`GSPreprocessProg36.SAT_DEC` は上限残距離 `bound-p` の飽和減算を、常に2動作で
実行し、他テープを保存する。`GSPreprocessProg37.FIRST_SCAN_spec` は第1相の
内側走査を有限構文へ移し、元の `mProg` と動作列そのものが一致することを証明。
追加の実行コストはなく、上界は `5*mWork`、補助3テープも不変。
十分なfuelは証明のみに現れ、`FIRST_SCAN` のプログラム値には含まれない。
主定理の公理guardは標準3公理のみ。

`GSPreprocessProg38–41` で第1相の巻き戻し・候補シフト・リセットも有限化。
上界はそれぞれ `10*q+2`、`(k+6)*delta+2`、`10*q+7+(k+6)*delta`。
候補上限の残距離を飽和減算で更新し、走査後の予算を `(k-1)*p_new` に戻す。
`GSPreprocessProg42–45.FIRST_OUTER_spec` は上限あり／なしの第1探索全体を実装。
`firstOuter` との結果一致、成功時の一致長、失敗時の停止条件、候補の大きさ、
補助カウンタの保存、入口・出口のprobe復元まで含めて証明した。
具体的な動作数は `(k+40)*firstOuterWork+4` 以下（標準3公理guard確認）。
上限値自体や入力長、証明用fuelは有限プログラムの構文に含まれない。
第1相の初期化・reach伸長との合成、分解器・全体機械への接続はまだ未完了。

`GSPreprocessProg46.EXTEND_REACH_spec` はreach伸長の走査を有限化。
通常の `Cd` ヘッドがblankであることを使って既存の有限判定を再利用し、
`rProg` と動作列が一致すること、補助3テープを保存すること、`3*rWork` の上界を
証明した（標準3公理guard確認）。第1探索との合成はまだ残っている。

`GSPreprocessProg47.LOADR_spec` は補助3カウンタを保存する転送と正確な
動作数 `3*Q+7*P+6` を証明し、`LOAD_EXTEND_spec` でreach伸長まで合成した。
`GSPreprocessProg48.FIRST_SEARCH_spec` は初期化を第1探索につなぎ、
ゼロカウンタの入口から結果一致・停止条件・補助状態・動作数
`(k-1)+8+(k+40)*firstOuterWork` を証明した（いずれも標準3公理guard確認）。
`GSPreprocessProg49.FIRST_PHASE_success/failure` で成功／失敗分岐も合成した。
成功時は `extendReach` に一致する最終ヘッド・カウンタ値と動作数上界、
失敗時は転送をスキップして探索の最終状態を保つことを証明済み。
分解器・全体機械への接続は未完了。

`GSPreprocessProg50.REPO_spec` は第2探索への再配置を有限化し、補助3テープの
保存と `8*r+17*p+23` 以下の動作数を証明した。Prog51 の `COPY_RA_spec` と
`SEED_SIGNED_spec` は到達距離を実行時のテープからコピーし、`SignedOK` と
`EncR` を確立する。Prog52 の `CLEAR_SIGNED_spec` は4本の比較用カウンタを
有限ループでゼロ化し、正確な動作数 `2*(D+A+B+C)+8` を証明した。
Prog53 の `SECOND_PHASE_spec` で再配置・初期化・第2探索・消去を合成済み。
Prog54 の失敗時清掃と仕事量補題を使い、Prog55 の
`STEP_SEARCH_success/failure` は第1相から第2相までの一反復を有限化した。
成功時の周期・フラグ・正規化された出力状態、失敗時のゼロ状態への復帰、
`stepRate k * decomposeStepWork + 4*k+112` の上界を証明した。
主要定理はすべて標準3公理のみを guard で確認。
周期削除ループを含む分解器全体と全体PAL機械への接続は引き続き未完了。

Prog56 は探索後の `DRST` / `DSWAP` の EncS と正確なコストを接続した。
Prog57 は削除探索の上限値を Cf から Ca へコピーする `COPY_FA` と、
候補長を Ca へ戻す `PA` を有限化。Prog58 の `REWIND_TO_CUT` は周期長を
先に差し引いて退避・復元し、入力依存の停止閾値を有限ループへ持ち込まずに
両ヘッドを切断位置へ戻す。Prog59 の `ADVANCE_BOUND_spec` は
`r-k*p+1` の前進と上限値の復元、`24*r+3*k*p+4*k+17` のコストを証明した。
Prog60 の `STRIP_STEP_success/failure` は境界付き探索と前進処理を合成。
成功時の厳密な前進・上限復元・仕事量に比例するコスト、失敗時の停止状態を
標準3公理のみで検証した。これを繰り返す削除ループ全体はまだ未接続。

これはテープ動作列の正当性・コストの接続である。分解器全体の入力長非依存な
有限 `Prog`、中央バッチの実体、段のライフサイクルとスロット実装、
`FullMachineProg` の構造的仮定を埋めた無条件の PAL 定理は引き続き未完了。

## 最新の追記：Consumption の解決（2026-09-08）

`lean-pal/PalPeg/Consumption.lean` の `PassSum10.consumption_eight` で、任意の
アルファベット・入力 `x`・上限 `b` に対する `Consumption x 8 b` を無条件に証明した。
反例なら消費位置全体が小周期の 8 乗で被覆される。その 1 周期幅内にある「親の先頭と
同じ位相」の位置から小周期を先頭へコピーし、親の最小周期性に矛盾させる。
遅い UP の追加仮定も、外部の局所周期定理も不要。
`passPeriodSumGen_eight` / `passPeriodSum_eight` も無条件の系として接続。
`lake build --quiet PalPeg.Consumption` 成功。主定理と両方の系の公理 guard は
`propext / Classical.choice / Quot.sound` のみで、`sorryAx` や追加公理はない。
下記の古い進捗にある「Consumption は未証明」はこの結果で更新される。
具体的な有限制御機械の組み立てなど、別途残る作業まで完了したという意味ではない。

更新: 2026-09-07 17:50 JST。これは今回の引継ぎメモ。
過去の構成ログ `docs/palindromes-in-peg/PROGRESS.md` は別ファイルとして保持している。

## 1. 最新の依頼と停止位置

ユーザーの目標:

> 次に判定機やSCA, PEGの変換をLean4で書き下して正しさを証明してほしい。なるべくトークン使わずに

その後「いったんfable 5に引き継ぐからこれまでの経緯をPROGRESS.mdとして書き出して」と指示されたため、実装を止めてこのファイルを作成した。
**新しい具体的判定機のLean実装にはまだ着手していない。** モデル・既存証明・キャッシュの所在を確認したところである。今回の新目標について開始したビルドやバックグラウンド処理はない。

目標は既存の条件付き定理の前提を実際の機械と証明で埋め、判定機→SCA→PEGの正しさまで接続すること。単なるリスト反転比較の正しさや有限長テストで、この目標を達成したことにしない。

## 2. 現在のリポジトリ

- 作業場所: `/home/mizushima/repo/lean4-peg`
- ブランチ: `feat/pal-plain-peg-artifact`
- このメモ追加前のHEAD: `4995ae3` (`docs(pal): record final Scala test counts`)
- メモ追加前の作業ツリーはclean。今回、既存コードは変更していない。
- 前のScala移植作業の担当エージェントはすべて終了済み。
- コミットはローカルにある。pushは今回実施していない。

## 3. 完了したScala移植

Claude Codeの利用上限で止まった作業を引き継ぎ、`docs/palindromes-in-peg/` のPython **94実装モジュール・66テストファイル**に対応するScala実装を `scala/pal/` に揃えた。Python側は比較基準として変更していない。

最終統合コードで、2026-09-07 14:42に以下を実行済み:

```sh
cd /home/mizushima/repo/lean4-peg/scala
XDG_RUNTIME_DIR=/tmp/xdg-1000 sbt -batch pal/compile pal/Test/compile pal/test
```

結果: **471 passed、0 failed、0 errors、ignoredなし**。テスト部分707秒。
`git diff --check` も成功。これは `pal` サブプロジェクトの全テストであり、リポジトリ全体の `make verify` を今回再実行したという意味ではない。

主な追加・修正:

- SCAVM制御、回路、GS、window worker、最終 `GenerateWindowPal` まで移植・統合。
- `PortCoverageSuite` がPythonファイルを走査してScala対応ファイルの欠落を検査。
- `PhasePeg` のphase-return計算を単調な依存worklistへ変更。元の最小不動点と出力順を維持し、Pythonとの差分・再帰・star・長い参照鎖を検証。
- `PyDiff` のstdout/stderr逐次読み取りによる停止を修正。stderrを並行して読み、256KiBの正常／異常出力を回帰テスト。
- compactorの分割メモリマップ境界、生成器のキャッシュ無効化・中断報告も検証。

重要コミット: `e9023db` (phase worklist)、`eb55bb6` (PyDiff)、`4d89691` (旧生成器の検証分割)、`4995ae3` (最終結果)。

### 検証の境界

- **既定WindowPALの巨大文法をScalaで全生成して既存SHAと比較する検証は未実施。** 小さなcheckpointテストを、その代わりの証拠にしていない。
- 旧実験用 `GenerateGalilPeg` は現在のWindowPALとは別。`--quantum 1 --match-delay 2 --budget 2 --raw-instructions --omit-invariant-monitors --expanded-only` で1,420,678規則・50,121,014 bytesがPythonと全バイト一致。
- その逆変換後の698,145,389 bytesはScalaで生成できたが、Pythonの再帰AST登録が再帰上限100,000でも失敗し、全体比較は未検証。実際の `emitInverse` を小規模Scaffold fixtureで比較するテストは成功。
- `CompactScaffoldPeg` の2GiB超対応は分割マップ設計と小さい窓での境界テストによる。別クラス `FileGrammar` は約2GiB超を明示的に拒否する。

詳細: `docs/palindromes-in-peg/STATUS.md`、`PLAIN_PAL_ARTIFACT.md`、`docs/superpowers/plans/2026-09-07-pal-python-to-scala.md`。

## 4. Leanで証明済みのこと／未証明のこと

`lean-pal/` は既存のShallot用 `lean/` と別パッケージ。
`lean-pal/PalPeg/Existence.lean` の主定理は次の形:

```lean
theorem pal_recognizedByTotalPEG (h : RealTimeTM.RecognizedBy PAL) :
    RecognizedByTotalPEG PAL
```

具体的な機械を受け取る版:

```lean
theorem pal_in_peg_of_realTime {t s k : ℕ}
    (M : RealTimeTM.Machine (Fin 2) t s k)
    (hM : ∀ w, M.Accepts w ↔ w ∈ PAL) :
    ∃ (n : ℕ) (G : PegGrammar (Fin 2) n),
      G.IsLoffTotal ∧ ∀ w, G.Recognizes w ↔ w ∈ PAL
```

証明の接続:

1. `RealTimeTM.toSCA_accepts_iff`: 厳密実時間TM→SCAの言語保存（依存成果物）。
2. `SCAToPEG.loffBackward`: SCA→total PEG、認識言語は反転（依存成果物）。
3. `PAL_reverse_mem`: 回文の反転不変性（このパッケージ）。

`Basic.lean`、`Existence.lean`、`EvenLength.lean`、`Axioms.lean` があり、偶数長回文への制限も条件付きで証明済み。`lake build` と公理guardの成功を前作業で確認した。標準公理以外の新規公理や `sorry` は使っていない。

**未証明なのは前提 `RealTimeTM.RecognizedBy PAL`。** 有限制御・有限個のテープを持つ具体的 `M` と、全入力に対する `hM` がまだない。文献の実時間性とこのモデルとの接続・必要な正規化も証明していない。
`sorry`なしなのは「含意」の証明が完成したという意味であり、前提を証明済みにするものではない。

また、この存在定理は生成済み巨大PEGファイルを直接検証する定理ではない。依存するSCA→PEGの存在構成にはnoncomputableな番号付けがある。具体的生成器の出力まで対応付けるには別の接続証明が必要。

### 引継ぎ時にモデルの実コードで確認した注意点

`PegSeparation/Common/Compiler/RealTimeTM/Model.lean`:

- `transition` は有限状態・今回の入力記号・各テープの注目記号から次の命令を決める。
- `run` は入力リストを `foldl step` する。1入力記号につき1遷移で、入力終了後の追加計算はない。
- `Accepts` は最終状態の受理集合への所属。
- `TapeAction` は書く記号と移動を指定するが、**移動には `.stay` もある**。「必ず左右へ1セル動くモデル」と誤読しない。
- 初期テープはblank。左端からの左移動は端に留まる実装。

旧調査の「1書込/1移動」はこのアクション形式のこと。調査中のtape compression案や必要行数の見積もりは証明ではなく、設計の正しさは再確認が必要。

## 5. Lean環境と再利用できるキャッシュ

- `lean-pal/lean-toolchain`: `leanprover/lean4:v4.31.0`
- Mathlib: `v4.31.0`
- `PegSeparation`: `https://github.com/kimjg1119/peg-separation-artifact`
- pin: `c364edbc1003292097e5fbac3a5607c021226a15`（引継ぎ時も実際のcheckoutで確認）
- `lean/` 側は別バージョン・Mathlib非依存なので混ぜない。

通常のビルド:

```sh
cd /home/mizushima/repo/lean4-peg/lean-pal
lake exe cache get
lake build
```

ルートの `make lean-pal` も利用可能。通常の `make verify` には含まれない。

**メインの `lean-pal/.lake` はまだない。** 前作業でビルドした依存・成果物は次に残っている:

```text
/home/mizushima/repo/lean4-peg/.claude/worktrees/agent-ae9087ce84c0c538c/lean-pal/.lake/
```

このworktreeは引継ぎ時cleanだった。別checkoutなので、メインに追加したファイルが自動で反映されるわけではない。キャッシュ再利用の方法を決めてから検証し、別の古いソースのビルド成功を新実装の成功として報告しない。

## 6. 再開時の入口

必要なところから読む（全履歴の再読は不要）:

1. `lean-pal/README.md` と `PalPeg/Existence.lean`: 実際の到達点。
2. 依存成果物の `RealTimeTM/Model.lean`、`Correctness.lean` と `SCAToPEG/Final.lean`: 接続先の型・制約・既存の証明。
3. `docs/palindromes-in-peg/FORMALIZATION_SURVEY.md`: 関連経路の調査。未確認の引用・正規化案を事実として引き継がない。
4. `GALIL_CLOCK.md` と `delayed_pal.py`／`scaffold_window_*.py`、読みやすい対応Scala実装: 具体的な制御・時間保証の候補。

次に必要なのは機械状態と不変量の設計、各遷移の保存、全接頭辞での判定正しさ、実時間モデルの制約、既存コンパイラへの接続。変換の既存証明を無意味に作り直す必要はないが、抽象モデルを弱めたり入力反復・長さ上限・判定オラクルを入れて元の要求を置き換えない。

ユーザーは少ないトークンでの継続を希望している。検索・ログは絞り、長いビルドにはToken Sieveを使える。過去の見積もりだけで実装を諦めず、同時に部品や有限テストを全体証明として報告しない。

## 7. 2026-09-07 夕方の更新（Fable 5.1）

- `lean-pal/.lake` を本体に複製し `lake build` 成功（依存の再取得なし）。
- 方針変更：RTTM ではなく成果物の SCA を直接構成する（`RecognizedBySCA PAL` →
  `SCAToPEG.loffBackward` → PEG）。SCA は永続ポインタ機械なので Galil の「p ステップ前の状態」
  はスナップショット辺で表せる。設計と未解決点は `lean-pal/DESIGN_SCA_PAL.md`。
- 追加した証明（sorry なし、公理 guard 済み）：
  - `PalPeg/Words.lean`：拡張則、境界＝回文接頭辞／接尾辞、周期⟺境界、Fine–Wilf（正確な
    `p+q-gcd` 境界、Mathlib `List.HasPeriod.gcd` へ橋渡し）、周期の伝播、group 補題
    `hasPeriod_minimal_of_suffix`。
  - `PalPeg/Chain.lean`：オンライン鎖算法 `chain` と `mem_PAL_iff_length_mem_chain`
    （`w ∈ PAL ↔ w.length ∈ chain w`）。これは SCA の仕様層で、実時間ではない（O(n)/step）。
- **未達**：`RecognizedBySCA PAL` そのもの。SCA 実装・実時間性（young run の cursor 実体化、
  break 後の下位構造再構築、実時間キュー）は設計に留まり、`DESIGN_SCA_PAL.md` §4 が証明義務。
- 追記：`PalPeg/Structure.lean`（レプリカ補題、最小周期回文の境界、予測補題、禁止帯
  `lsp_shift_bound`）。設計メモの (M)「成熟なら `LSP(n-p)=ℓ-p`」は **偽**（反例 `001000` を
  Lean で機械化）。昇格時の cursor を「p ステップ前のスナップショット」から取る案は break 直後には
  使えず、設計の見直しが要る（`DESIGN_SCA_PAL.md` §2 (M)、§4）。
- 追記（部品層）：`PalPeg/Groups.lean`（group 圧縮鎖、`expandAll_groupChainRev`；群数の対数上界は
  未証明）、`PalPeg/Matching.lean`（KMP 一歩、Galil 予測補題 `predictability_step`/`work_le`、
  `border_snapshot`）、`PalPeg/RTQueue.lean`（Hood–Melville 実時間キューの FIFO 仕様）。
  すべて sorry なし・公理 guard 済み。`DESIGN_SCA_PAL.md` §7 に dyadic stage 構成の要件と
  残る証明義務（オンライン Manacher、実時間 KMP の π 取得、SCA 符号化）を記載。

## 8. 上位方針（2026-09-07 夜、Fable 5.1）

目標 `RealTimeTM.RecognizedBy PAL` へは repo の dyadic stage 設計（`ALGORITHM_SPEC.md`）を
層ごとに Lean 化する。RTTM（テープ双方向）を採用し、SCA 直接構成は取り下げ。

- L0 部品（済・sorry なし）：Words, Chain, Structure, Groups, GroupsLog, Matching, RTQueue,
  Manacher, Stages（`pal_prefix_iff_stage`, `live_stages`）, Schedule（`finishTime_le`,
  `fifo_meets_deadlines`）。
- L2 進行中：GSScan（GS 走査の安全シフト・正しさ・ポテンシャル）、GSDecomp（分解の存在と L1 境界）、
  ManacherHeads（テープ上のヘッド移動の telescoping 上界）。
- L4 進行中：Speedup（1 記号 B 操作の機械 → 厳密実時間 `Machine`、線形加速）、TapeLib
  （zipper/stack/seq/counter ビュー）。
- 未着手：u 検証器の締切補題、段の組み立て（抽象 dyadic 機械の全接頭辞正しさ）、
  抽象機械の `MultiStepMachine` への符号化。
- 進捗（深夜、コミット 4cca565 まで）：L2 済＝GSScan（走査）、GSRealTime（レート k+1 で実時間、
  有界遅れ不変量 `Φ ≥ (k+1)n − k|v|`、u 検証器の締切）、GSDecomp（分解述語・k 反復補題・`KSimple`
  への橋。**L1 の厳密境界 `(k−1)s<|x|` は未証明**、弱い定数版を続行中）、MiddleJob（Manacher 版の
  中央フラグ締切。ただし TM 化は rad のランダムアクセスで不可なので repo の境界列挙版 BorderJob に
  切替中）。L4 済＝Speedup（`multiStep_recognizedBy`）、TapeLib。
  稼働中：RTQueueTapes、Assembly（段の組み立て）、BorderJob、GSScanTapes、GSVerifier、GSPreprocess。
- 進捗（コミット db53dea まで）：Assembly（段の組み立て `dyadicAnswer_correct`）、GSVerifier（u 検証器、
  オラクルなし）、StageMatcher（GS 照合器が `MatchOracle` を満たす、`dyadic_gs_mem_PAL`：各段の分解
  witness に `cut < W` があれば全体正しい）。稼働中：RTQueueTapes、BorderJob、GSScanTapes、
  GSDecomp 弱定数版、GSPreprocess、OnlineMachine（全体機械の添字モデル、中央/前処理はインターフェース）、
  ProgramMachine（構造化 `StructuredMachine` → `MultiStepMachine` → `RecognizedBy`）。
- 残：BorderJob/GSPreprocess/走査/キューのテープ化を `StructuredMachine` で組み、OnlineMachine の
  インターフェースを満たすことを示して最終定理 `RealTimeTM.RecognizedBy PAL`。
- 進捗（コミット e9bfb1e まで）：ProgramMachine（構造化機械→`RecognizedBy`）、GSScanTapes（走査の
  3 テープ化、判定 bit はオラクル→カウンタ化を続行中）、BorderJob（中央フラグの GS 境界列挙、仕事 ≤ 258|x|、
  段ごとに L1 を仮定）、RTQueueTapes（キューの 9 テープ化、`lenr≤lenf` 判定は仮定→差分カウンタ化を続行中）。
  **critical path：GSDecomp の真の L1 境界（`(k−1)s<|x|`, `(k−2)s<(k−1)p₁`）**。GSVerifier と BorderJob が
  これを仮定してるので、GS の内側削除ループの補題を形式化中。
  稼働中：GSPreprocess、OnlineMachine、GSVerifierTapes、BorderJobTapes、TextFeed（到着記号を FIFO 経由で
  走査テープへ供給）。
- 進捗（コミット c9f36a2 まで）：GSPreprocess（計算可能分解）、OnlineMachine（全体機械の添字モデル、
  `output_correct`）、GSVerifierTapes（u 検証器の 5 テープ化）。
  設計修正：段 S の分割点を S/2 に変更（パターン `rev(w.take(S/2))` は S/2 で確定、前処理 (S/2,S]、
  テキスト `w.drop S` を S から実時間走査）。これで「2W 時点での追いつき」の隙間が消える。Assembly /
  StageMatcher / OnlineMachine を改修中。
  L1 境界：欠けていた補題は「1 パス内の削除は位置 p₂ より手前で止まる」（run 0 は T 未満で終わり、
  位置 T の最小周期は p₀ に戻るので単調性と矛盾）。新エージェントで証明中（GSDecompL1）。
  稼働中：GSScanTapes カウンタ化、RTQueueTapes 差分カウンタ、TextFeed、BorderJobTapes、GSPreprocess 全体
  線形上界、GSPreprocessTapes、GSVerifierTapes の償却。
- 進捗（コミット直近）：GSPreprocess 全体線形上界 `decomposeWork ≤ (16k+38)|x|+2k+5`、RTQueueTapes の
  数値比較を差分テープに置換、GSVerifierTapes の償却（L1 不要）、GSScanTapes のオラクル bit 除去（8 テープ）、
  TextFeed（`feed_online`）。稼働中：BorderJobTapes、GSPreprocessTapes、GSDecompL1、OnlineMachine 半分割、
  MiddleBorder（BorderJob 版 MiddleImpl）。
- 22:00 の API 上限リセット後：半分割再スケジュール完了（`output_correctH`、`round_cost_leH` 条件なし、
  常駐段 ≤ 3）をコミット（413fee4）。落ちた 7 本（L1 最終補題、BorderJobTapes、GSPreprocessTapes、
  検証器/TextFeed の 8 テープ版移植、MiddleBorder、PatternTapes）を再開。加えて Main.lean（構造化機械 →
  `RecognizedByTotalPEG PAL` の糊）と InputCopy.lean（入力コピーのフロンティア書き込み）を Sonnet に依頼。
- **L1 境界の真の存在定理が取れた**（`GSDecompL1.gsDecomp_exists`、`stageOK_exists`、`gsDecomp_verifier_data`；
  鍵は「パスは第 2 周期 T の手前で停止」を最大周期の帰納で示す `pass_stops_before_second`）。コミット 4696181。
  続き：計算可能 `decompose` の出力に対する L1（`decompose_gsDecomp`）、`PrepImpl` 実装（PrepDecompose）、
  検証器の Txt2 供給（VerifierFeed）。Main.lean に糊 `pal_in_peg_of_structured` あり。
- 進捗（コミット 9907aac まで）：BorderJobTapes（6 テープ、仕事 ≤ 4000|x|）、InputCopy、MiddleBorder
  （`MiddleImplSpecH (borderMiddle) 27901`、各段 L1 を仮定）、PrepDecompose（`PrepImplSpecH`、`decompose` の
  L1 を仮定）。添字レベルの全体機械は両インターフェース実装が揃い、残る仮定は `decompose_gsDecomp` 1 本。
  稼働中：decompose_gsDecomp、GSPreprocessTapes、PatternTapes、VerifierFeed、EndToEnd（添字の端到端定理）、
  MiddleTapes（中央ジョブのテープ化＋二重バッファ出力）。残る大物：段のテープ組み立てと全体機械の
  `StructuredMachine` 化。
- 進捗（コミット c62d193 まで）：`decompose2`（失敗位置へジャンプする strip）で L1 が無条件に成立
  （`decompose2_gsDecomp`）。仕事量は窓の入れ子木で償却：子 `(k−1)q < p`（A）と兄弟の重なり `< p+q`（B）を
  証明済み、残るは木の帰納 Σp ≤ C₁T（新エージェント）。PatternTapes（段セットアップ ≤ 21h）、VerifierFeed
  （Txt2 も FIFO 供給；`.X .right` ごとの fill 版を続行中）、MiddleTapes（バッチ実行はテープ化済み、ラウンド
  組み立て続行中）、GSPreprocessTapes（firstPeriod/extendReach/secondInner 済、残り続行中）。
- 進捗（コミット 4389b84 まで）：VerifierFeed の逐次 fill 版（`vfeed_online''`、仮定なし）、GSPreprocessTapes
  が secondOuter まで（1 反復 ≤ (2k+65)·work）、GSDecompose2Work（線形は Σp_j ≤ C₁T を仮定；子 (A)・兄弟 (B)
  補題は証明済み。ウチの見立てでは Σp_j は最悪 T log T になりうるので、Python で全探索して事実確認中）。
  新規：Metered（1 ラウンド固定 B 動作の de-amortization 補題）。残り：MiddleTapes のラウンド組み立て、
  前処理テープ化の strip2、段の照合フェーズ組み立て、全体 `StructuredMachine` 化、最終定理。
  **前処理の線形性が未解決の場合の代替案**：分割点を S/2 に置いたまま前処理に S/2 ラウンドしか使えないので、
  線形でなければ設計変更（別の照合器 or 別の分解法）が要る。
- 進捗（コミット ff37ac6 まで）：MiddleTapes のラウンド組み立て完了（`middle_flag_read`）、Metered（固定 B
  動作/ラウンド、`metered_phi`；`rem=0` 仮定の除去を続行中）。稼働中：PassSum（Σp_j ≤ C₁T の証明/反例）、
  EndToEnd2（`decompose2` へ切替、残る仮定は `PassPeriodSum` のみ）、前処理テープ化の strip2、
  StageMatcherTapes（段の照合フェーズ：setup → 固定 B 動作のラウンド）。
  設計メモ：テープ集合は 4 組を回して使う（常駐 ≤ 3、退役後 4S ラウンドで O(S) のクリアを分散）。
- 進捗（コミット 7fc4811 まで）：Metered（`rem=0` 仮定なし）、EndToEnd2（添字レベルの端到端、仮定は
  `PassPeriodSum 8 C₁` のみ）、PassSum（二分律・領域端の増減）、StageMatcherTapes（段の照合フェーズを固定予算
  で実行、`stage_answer_stageMatchH`）。稼働中：前処理 strip2 のテープ化、Prologue（テープ初期化/クリア）、
  PassSum2（`Σp_j ≤ C₁T` の再挑戦：着地補題）、StageTapes（段の全ライフサイクル）。
  **現状の唯一の数学的仮定**：`PassPeriodSum`（`decompose2` の 1 パス内 run start 周期和 ≤ C₁·p₂）。
  実測（k=4、T≤60 全探索＋山登り）では最大 0.39T で線形が濃厚。
- 進捗（コミット f4d0e1c まで）：Prologue、README 更新、PassSum2/3（(j,j+2) 補題、同周期領域の右端一致、
  兄弟の成長条項）。`PassPeriodSum` は依然未証明（3 回の試行が「pass 固有の着地補題が要る」で一致）。
  稼働中：前処理 strip2 のテープ化、StageTapes（段ライフサイクル）。残り：全体機械、最終定理。
- 進捗（コミット 479e7c7 まで）：StageTapes（段の全ライフサイクル、`stage_tapes_spec`）。稼働中：
  strip2 テープ化、`hgm0`（起動フェーズ分散）の解消、FullMachineTapes（全体機械：常駐 ≤3 段、
  入力コピーは「前段の凍結コピー＋新鮮なフロンティア」のペア方式）、PatternTapesPair（ペア源からのセットアップ）。
  残り：`StructuredMachine` 化（有限制御・テープ数固定）と最終定理。
- 進捗（コミット d0236f1 まで）：StageTapes の `hgm0`/`hsetup` 解消、前処理テープ化が strip2 まで
  （`stripProg2_spec ≤ (16k+32)·work + (k+4)·fuel`）。稼働中：外側ループ `decompose2_on_tapes`、
  照合器初期テープの導出（設置ではなく `setup_spec` から）、FullMachineTapes、PatternTapesPair、PassSum4。
- 進捗（コミット 38b85df まで）：StageTapes の照合器初期テープをセットアップ出力から導出（設置を撤去）。
  PassSum4（連続する子は `(k−2)/(k−1)` 倍まで；幾何成長せず、`PassPeriodSum` は仮定のまま）。
  稼働中：`decompose2_on_tapes`（外側ループ）、FullMachineTapes、PatternTapesPair。
  残り：`PrepOnTapes`/`DecompOnTapes` の具体化（有効周期の正規化込み）、`StructuredMachine` 化、最終定理。
- 進捗（コミット 34f81d1 まで）：FullMachineTapes（4 スロット回転、`full_answer_mem_PAL` は `StageIface` 前提）、
  PatternTapesPair（凍結入力対からのセットアップ、`setup_spec_pair`）。**ビルド注意**：lakefile は
  `autoImplicit = false` だが `lake env lean` はそれを読まないので、単体検査は
  `lake env lean -DautoImplicit=false <file>` で行うこと（MiddleTapes の「`lake build` だけ失敗」の原因）。
  稼働中：`decompose2_on_tapes`（外側ループ）、ProgLang（有限制御プログラム言語 → `StructuredMachine`：
  今のテープ実装は「動作リスト」意味論なので、これが最終定理への最大の残工事）、PassSum5（全探索の再確認と
  証明再挑戦）、ClearAny（任意形状のテープの消去 ≤ 3·幅+3）。
- 進捗（コミット 377c425 まで）：
  * `PassPeriodSum`：全探索＋状態空間探索で反例なし。Lean で DOWN 側を閉じた（PassSum5
    `passSumLinear_of_upSum`：UP ジャンプの周期和 ≤ C·b ⟹ `PassPeriodSum`）。PassSum6 は UP 回数 n₀ で
    `PassPeriodSum 8 (7(n₀+1))`（無条件）。**注意**：「1 パス ≤ 3 反復」は偽（[1,9,1,64,1]、b=65、Σ=76 の
    5 反復例をシミュレータで確認）。正しい構造は「脱出周期 P > (k−1)p_c − 1 − 消費量 t_c」（Fine–Wilf）で、
    根の周期は幾何的に成長する。証明は PassSum7 で継続中。
  * ProgLang（有限制御プログラム言語 → `StructuredMachine`、`progMachine_recognizedBy`）完成。既存の
    動作リスト実装の移植を GSScanProg から開始。
  * 前処理テープ化 `decompose2_on_tapes` 完成、オラクル完全除去。ただし費用上界に fuel 由来の二次項があり
    線形化中。
  * PrepInstances：`stage_tapes_spec'` 用の `res`/`GSCore`/`hs` パッケージ済。インタフェース側の不備を
    4 点発見（`PrepOnTapes.post` の前提条件欠如、二次費用、`p₁=0` で `hkp` 矛盾、`OvTapes` のテープ不足と
    `decompose`/`decompose2` の不一致）→ StageTapes / MiddleTapes / GSPreprocessTapes を修正中。
  * ClearAny（任意テープの消去 ≤ 3·幅+3）。
- 進捗（コミット b36837a まで、2026-09-08 深夜）：
  * **`PassPeriodSum` の現在地**：PassSum7 で「Σp ≤ 2·(パス内最大周期)」に帰着（スケール不変、実測最大 1.304、
    自己相似族の極限 ≈1.31）。PassSum8 で木の再帰を閉じた：**残る唯一の命題は「同じ親の連続する子（兄弟）の
    周期比 ≥ 14/5」**（`PassHasTree`；実測の最小比は 7.1、根同士は 7.4）。これが取れれば
    `passPeriodSum_eight_of_hasTree : PassPeriodSum 8 2`。PassSum4 の `children_growth` は比 6/7 しか出せず、
    差は「子の部分木の消費量 C(c) を |R_c| でなく再帰的に抑える」こと。`dichotomy_insufficient`（PassSum7）で
    二分律だけでは不可能なことも形式的に示した。
  * **有限制御化（ProgLang 移植）**：完了＝GS 走査器（GSScanProg）、実時間キュー（RTQueueProg）、
    検証器の比較分岐（GSVerifierProg、8→10 テープ持ち上げ `exec_lift`）、境界列挙の一部（BorderJobProg）。
    発見した「動作リストのままでは有限制御で実現不能」な箇所：(a) 検証器のシフト分岐（Txt2 の残差移動を走査の
    シフトループに融合する必要）、(b) BorderJob の `periodActs`（カウンタ消去後の復元；第 2 カウンタが要る）、
    `uBack`/`resetWalk`（probe-tail 形へ書き換え）、(c) TextFeed（テープ添字の直和で解釈を合成する組合せ子が
    未作成）。段セットアップの移植 PatternProg は途中（1081 行、sorry なし、12 テープ実体化の手前）。
  * **インタフェース修正**：`PrepPre` 前提条件、`rateS=160`、`DecompOnTapes.dec/decOK` フィールド化、
    `OvTapes` に S1–S9、前処理費用の線形化、オラクル完全除去。`prepInstance`（decProg → `PrepOnTapes`）は
    9 テープ→12 テープ埋め込み＋prologue/epilogue の構築が未着手（レート制限で中断）。
  * **残作業（順）**：prepInstance と decompInstance の具体化 → `StageIface` の具体化（`stage_tapes_spec'`＋
    `PrepInstances.prep_res_eq5`）→ 上記 (a)(b)(c) の書き換えと残りの移植（前処理・中央ジョブ・段・全体機械）→
    全体機械を ProgLang の 1 ラウンド Prog として組み、`progMachine_recognizedBy` → `Main.pal_in_peg_of_structured`
    で最終定理（`PassPeriodSum` が未証明なら「兄弟比 ≥ 14/5」を仮定した条件付き定理として明記）。
- **次の一手（数学、2026-09-08 深夜に判明）**：木解析の実測（入れ子べき乗語 1500 本、ノード 1500 個）で
  「領域 R_c 内での子孫の消費量 C(c) < p_c」（最大 0.915·p_c）、1 ノードの子は最大 3。**補題 C(c) < p_c**
  （c の子孫はすべて R_c の最初の 1 周期以内に始まる）が取れれば、S1（脱出周期 P > (k−1)p_c − 1 − C(c)）から
  兄弟比 > (k−2)p − 1 ≥ (14/5)p が即座に従い、PassSum8 の `PassHasTree` → `PassPeriodSum 8 2` が閉じる。
  証明の筋：領域は p_c 周期的なので、オフセット ≥ p_c に最初に到達する子孫 j の p_c だけ左の「翻訳像」は
  同じ最小周期・同じ走行長を持つ仮想ノードで、直前に訪れたノード i の走行 [a_i, E_i) の内部（尾部 R_i より前）に
  落ちる。UP/DOWN で場合分けして Fine–Wilf で矛盾を導く（未完；agent はレート制限で 3 時まで停止）。
- 進捗（このセッション、PassSum9.lean 追加、コミットせず）：`C(c) < p_c` を **8873 語・35117
  ノード**（seed 1–25、深さ2–6、長さ〜6万まで）で再確認、最大比 **0.9255**（反例なし）。
  ヒルクライム（ビット反転）は周期構造を壊すだけで有効な反例探索にならなかった。
  Lean 側の追加ファイルは既存定理の再掲だけだったので破棄した（`#print axioms` は `[propext, Quot.sound]`
  のみ）を追加したが、`consumption_lt_period`（翻訳像 → Fine–Wilf 矛盾の場合分け）は
  本セッションでは組み上がらず、**新しい証明済み定理は追加できなかった**。唯一残る課題は
  依然として `PassSum8.PassHasTree`。
- 進捗（2026-09-09 早朝、コミット 461ca0c 以降）：
  * **`PassPeriodSum` の現在地（PassSum9）**：走行終端不変量 (E)「c の子孫 j は E_j < a_{c+1} + p_c + p_j」で
    C(c) < p_c と子孫開始位置の上界が出る（証明済）。(E) の DOWN 側は証明済（`runEnd_down_step`）、UP 側は
    「P + q ≤ r_j」の場合のみ証明済（`runEnd_up_step_le`、Fine–Wilf の周期伝播エンジン
    `period_factor_propagate`）。**残る唯一の命題**：UP 側で r_j < P + q（実測 96% のケース）のとき、
    最鋭の形は t + P ≤ p_c（t = 子孫の開始オフセット；実測 t ≤ 0.23(p_c − P)、(E) の実測スラックは 2–3 セル）。
    「span_i ≤ q_{i+1}」（前回の帰着）は偽（u = 0^m 1 (0^7 1)^8 w で反例、実測比 2.88）。
  * **有限制御化**：`setupProgL`（入力非依存の段セットアップ、カウンタ駆動＋左番兵、`VEncodes'` 到達）完成。
    検証器は融合巻き戻し `uxWalk` まで完成（Prog 実現 `shiftProg`/`vprogX` は作業中）。BorderJob は uBack 済、
    periodActs/resetWalk 作業中。**`DecompOnTapes` は充足不能と判明**（`Act` に P/U 書き込みがない；
    `decompOnTapes_isEmpty`）→ `Pset`/`Uset` 構成子を追加中。`PrepOnTapes` に禁止記号パラメータと
    `len_le` の前提条件を追加（費用はテープ内容依存のため）。TextFeed は `fill'`（横断書き込み）が作業中。
- 進捗（2026-09-09 午前、コミット 25f9b3d/5ab98d7 まで）：
  * **`PassPeriodSum`**：PassSum10 で組み立てが完全に閉じた——`passPeriodSum_eight_of_treeFacts`
    （`RootGrowth ∧ LastChildBound ⟹ PassPeriodSum 8 2`、再帰 `stripLoop2` 上に直接）。`LastChildBound` は
    `child_period_bound` から従う（貼り付け中）、`RootGrowth` は `sibling_growth_eight` と
    `consumption_lt_period_of_dichotomy`（(G)∨(H) ⟹ C(c) < p_c）から従う。**残る唯一の未証明命題は (H)**：
    「t_j ≥ (k−1)p_j な子孫は周期境界を跨がへん（E_j < a_{c+1}+p_c）」。自己相似族の正しいコーパス（閉じた
    ノードに ≥2 子孫、332 例）で違反 0。(E) は反例あり（比 1.027）で不要になった。
  * **有限制御化**：完成＝GS 走査器、実時間キュー、検証器（`vprogX`、`vprogramX_amortized` A=9k+14/B=16、
    `matchProg`）、境界列挙 1 ステップ（`ovStepProg_exec_full`、`Act` に `Pset/Uset`）、段セットアップ
    （12 テープ `setupProgL`、13 テープ対版 `setupProgPairL`、カウンタ駆動＋左番兵）、TextFeed（`fill'`、
    phase 1）、ProgLang 直和組合せ子、**持続制御機械 `progMachineP`（`progMachineP_grind`）**。
    作業中：前処理 `decProg` の Prog 移植、中央ジョブ Prog の番兵駆動化、TextFeed phase 2、StageTapes の
    X 版（Ψ 込み Metered）。
  * **テープ意味論側**：`prepInstance`（`PrepOnTapes` の具体化、`forb`・`len_le` 前提付き）、
    `StageIfaceInstance.stageIface`（`full_answer_mem_PAL_of`）完成。`DecompOnTapes` は `EntryBlank` 前提が
    要ると Lean で証明（`decompOnTapes_isEmpty`）→ MiddleTapes を修正中、`decompInstanceB` は修正後の
    インタフェースの witness。生の `DecOK` 仮定を `gsDec2` 版に置換中。入力コピーの左番兵化
    （`InputCopySentinel`、FullMachineTapes `stage_birth_pair_prepView`）完了。段誕生時の初期テープ
    （`hinit`）構築中。
  * **残り**：段ライフサイクルを 1 本の持続 Prog に（idle→前処理 grind→セットアップ→照合＋中央ジョブ）、
    全体機械の 1 ラウンド Prog（4 スロット＋入力コピー＋消去）、Prog 機械の挙動とテープ意味論
    （`full_answer_mem_PAL_of`）の対応、`progMachineP_recognizedBy` + `pal_in_peg_of_structured` で最終定理。
- 進捗（2026-09-09 昼、コミット 6eea622 まで）：
  * **`PassPeriodSum`**：`PassSum10.passPeriodSum_eight_of_consumption` により残る仮定は `Consumption`
    （再帰上の C(c) < p_c）ただ 1 つ。証明済みの部分ケース（PassSum9 冒頭の要約参照）：DOWN 伝播、
    最初の子、早期 UP（`up_violation_early`、UP の ~95%）、深い横断の q₁ = P 重なり（glue）、q₁ < P（dvd、
    両側）。残る角 2 つ（r₁ = L の循環構成、q₁ < P で Fine–Wilf 窓が入らん場合）は実測 0 例
    （2286 子孫、横断 69 はすべて浅く・すべて直接の子）。循環構成の直接構成を試行中（見つかれば設計に影響）。
  * **有限制御化**：TextFeed 完了（phase 2 `feed_online_prog`）、一様分解器の部品完了、前処理 Prog の
    カウンタ層完了（分岐比較層を作業中）、中央ジョブ Prog は数値展開を除去済み（MiddleTapes 側の
    フラグ番兵・S3/S4 複写・`keepS` 緩和・`clearF` 掃引の 4 点修正待ち）、StageTapes X 版
    （`stage_tapes_specX`；feed 付き `vprogramX` ステップと Ψ 込み Metered を作業中）。
  * **テープ意味論側**：`stageIface`＋`initOf_hinit`（`hinit` は `S/2 ≤ |w|` ガード付きで充足）、
    `PrepPre.inb` は番兵つき `w.take L` の形に直す必要あり（未来の入力を要求してしまう；証明付き）。
    `DecompOnTapes` の `EntryBlank` 前提と `gsDec2` 参照モデルへの置換を作業中。
- 進捗（2026-09-09 午後、コミット f4f40ca まで）：`lean-pal/ASSEMBLY_PLAN.md`（最終組み立て設計：T=260 テープ、
  直列化＋テープ再開マーカー、`roundBody_exec` を核とする対応証明、残り約 6,300 行）。設計で見つかった
  ギャップ 3 点を並行修正中：`progMachineP` の到着動作を複数テープ書き込みに一般化、入力アルファベットの
  埋め込み ι : Fin 2 ↪ Fin sc（`full_answer_mem_PAL_of` は Fin 2 では空虚）、`MState.cp1/cp2` の有限化。
  MeteredX（Ψ 込み Metered）は `TightLagBoundary` を残して完成（選言不変量で攻略中）。前処理 Prog は
  第 2 フェーズ再設計（`orcR` 閾値カウントダウン、Cd 解放）中。中央ジョブは目印ツールキット完成、
  MiddleTapes 核の書き換え（フラグ/継ぎ目/消去＋gw カウンタ）待ち。数学：PassSum11 で循環角を
  `t + q₁ ≤ r₁` の下で閉じ、残りは `RemainingGap`（実測 8,820 子孫で 0 例）。
- 進捗（2026-09-09 夕、コミット 8873899 まで）：`PrepPre`/`SetupPre` を番兵形に修正し全体ビルド成功。
  `InputEmbed`（入力 Fin 2 ↪ Fin 9 の埋め込み、`full_answer_mem_PAL_embed`）、`ProgLangPersist2`
  （複数テープ到着、`progMachinePM_rounds_effect`＝組み立て用ラウンド帰納）、`DecompUniform` 配線完了
  （窓仮説つき `DecompOnTapesW`、Cd=40290C₁+220680）。**設計判断 2 つ**：(a) MeteredX の TightLag 経路は
  `debtSlack_false` で不成立と証明→検証器の U テープを 2 本にして巻き戻し費用を消す（Ψ 不要、元の Metered が
  そのまま使える）方針に変更、作業中。(b) 前処理 `orcR` は 9 テープでは O(1)/step 不可（符号付きカウンタに
  4 本必要）→ 11 テープ化、作業中（段側の埋め込みは誕生時に空の `sT`/`sX2` を一時利用）。MiddleTapes 核の
  書き換え（窓仮説・継ぎ目・消去・cp1/cp2 有限化・S10/S11）も作業中。
- 進捗（2026-09-09 夜、コミット 610446b まで）：`PassSumGen`（一般アルファベット `Consumption` ⟹ `PassPeriodSum`）
  と `full_answer_mem_PAL_of_embed'`（唯一の数学仮定 `hcons`、sc=9 版あり）。前処理を 11 テープ化（`OvTapes` は
  15 のまま：Ca↦Cnt、Cb↦U）。検証器：`rewind_not_pointwise` で巻き戻し設計の点ごと費用不可を証明→
  **ジグザグ u 検証器**（`GSVerifierZ`、巻き戻しなし、1 前進あたり 4 移動で `prefix_verifier_deadline` から
  締切成立）に切替、テープ/feed/Prog/段の 4 層を作業中。段ライフサイクル骨格 `StageLifecycleProg`
  （`Resumable`＝PC テープでチャンク再開、`stageRoundProg_effect`）完成、全体機械ラウンド本体
  `FullMachineProg`（4 スロット直列化、到着、消去、受理フラグ、`progMachinePM_rounds_effect` 接続）作業中。
  MiddleTapes 核書き換えと `decProgP` は継続中。
- 進捗（2026-09-10 未明、コミット dc09d00 まで）：`FullMachineProg`（T=260、直列化ラウンド本体、ラウンド帰納、
  `pal_SAccepts_iff_of`／`pal_recognizedBy_of`；空語 ε の受理は初期フラグの引数化で修正中）。前処理は 12 テープ
  （符号付きカウンタの核 `orcAB` 完成、第 2 フェーズ仕様の再証明と組み立てを新 agent で継続）。段バンドルを
  13 スロットに拡張して `PrepInstance` を再埋め込み中。MiddleTapes (1)（窓仮説つき `DecompOnTapes`）着地、
  (2)–(5) 継続中。ジグザグ検証器のテープ/feed/Prog/段の 4 層と、スロット予定表（`stageInSlot`/`Restart`）の
  単進カウンタ実現を作業中。最終定理の残り：具体 Prog の差し込み（`hstepF/G/I`）と `hPAL` の接続。
- 進捗（2026-09-10 早朝、コミット 2ffdf1b まで）：**ジグザグ u 検証器が全 5 層で完成**（`stage_tapes_specZ`：
  `Metered` 無改造、A=9k+14/B=16、レート 918、Ψ なし）。段バンドル拡張＋`PrepInstance` 再埋め込み完了、
  `progMachinePMb`（初期フラグ）で ε 受理を修正、`fullAnswer_zero`。MiddleTapes は S10/S11 と cp1/cp2 の
  有限化（Fin 14 世代 = 28 テープ、4 本化には再利用スケジュールの再設計が要る）まで。
  Opus のレート制限（8 時リセット）で中断：前処理 `decProgP` の第 2 フェーズ再証明、MiddleTapes の継ぎ目/
  消去/具体 `batchProg`、スロット予定表 `SlotSchedule`（書きかけ）。残り：これらの再開、具体 Prog の
  `FullMachineProg` への差し込み（`hround`/`hstepF/G/I`）、`pal_SAccepts_iff_embed`、最終定理。
  数学は `Consumption`（残角 `ShortRunGap` 1 条件）を仮定として保持。
- 進捗（2026-09-08、Codex・サブエージェントなしで Consumption を再開）：
  `Consumption.lean` を追加。`segExit_crossing` は実行ループの境界横断から最初の横断ステップを抽出。
  `not_consumption_witness` は `¬ Consumption x k b`（`k ≥ 4`）から、親の周期境界より手前で
  始まり、それを越える内側 run と `(k-1)*q < p` / `(k-1)*q ≤ u-nextPos` を導く。
  `lake build PalPeg.Consumption` 成功、公理は `propext / Classical.choice / Quot.sound` のみ。
  **Consumption 自体は未証明**。次は横断前の実行経路を保持して、遅い横断が起きないことを証明する。
  PassSum11 の短さと遅さの「一般の違反で同値」というコメントを修正（同値は閾値ちょうどのみ）。
- Consumption 続き：`SegPath` で実行経路を保持するよう反例抽出を強化。
  `step_covers_krep` / `SegPath.covers` / `inner_step_period_bound` をつなぎ、
  `consumption_failure_cover` を証明した：反例なら親の残存領域の先頭 p セルの各位置が
  `(k-1)*q < p` を満たす周期 q の k 乗で始まる。経路の途中の位置も含む。
  `lake build --quiet PalPeg.Consumption` 成功、反例抽出と被覆定理の公理監査も成功。
  未証明なのは、この小周期 k 乗による全位置被覆が親の最小周期と両立しないこと。
  Mignosi–Restivo–Salemi, *Periodicity and the golden ratio*, DOI
  `10.1016/S0304-3975(98)00037-1` は片側局所周期の関連文献（抄録確認のみ、定理適用は未確定）。

- 有限制御への接続（GSPreprocessProg61）：`STRIP_FLAG_STEP` の成功・失敗の
  EncS 仕様と費用を証明。成功は Ce=0 を保ち、失敗は Ce=1 とする。
  既存の `.soReady` を用いた `STRIP_RUN` / `STRIP_CORE` を定義し、
  継続・停止・probe 復元の実行補題を証明した。構文は k のみに依存する。
  一回分と制御の証明であり、stripLoop2 全体の帰納的仕様・後片付けと
  全体 PAL 機械への接続は引き続き未完了。

- 続き（GSPreprocessProg62–63）：`STRIP_RUN_spec` と `STRIP_CORE_spec` を
  入力位置の単調進行による帰納法で証明し、燃料なしの有限ループが十分な燃料の
  `stripLoop2` と一致することを示した。`STRIP_spec` は初期 bound コピー・
  終了フラグ消去・ヘッド巻き戻し・scratch 消去まで含む。
  費用は `(stripRate k + 2*k + 9) * stripLoop2Work + 11*F + 3*k + 42` 以下。
  主要定理の公理監査は標準三公理のみ。削除ループの帰納仕様と後片付けは完了。
  前処理本体の有限ループと全体 PAL 機械への接続は引き続き未完了。

- 続き（GSPreprocessProg64–65）：第二周期発見時の厳密な前進と、本体の
  三分岐（第一周期なし／第二周期なし／削除後継続）の実行・費用を証明。
  `DECOMP_RUN_spec` により有限ループ全体と `decomposeLoop2` の一致を証明し、
  `DECOMPOSE_initial` は `decompose2` の切断位置・周期・到達域を返し、
  全 scratch カウンタをゼロに戻す。構文に入力・燃料・オラクルは含まれない。
  費用は `decompRate k * (decompose2Work x k + x.length + 1) + 8` 以下。
  主要定理の公理は標準三公理のみ。前処理本体の有限ループ接続は完了。
  この有限実行を前処理・段インタフェースへ組み込み、全体 PAL 機械へ接続する作業は未完了。

- GSPreprocessProg66：証明済み `consumption_eight` の任意アルファベット版周期和を
  接続し、`DECOMPOSE_eight_linear` を無条件（入力表現・番人条件のみ）で証明。
  固定有限構文 `DECOMPOSE 8` の費用は
  `255 * decompRate 8 * |x| + 22 * decompRate 8 + 8` 以下。
  周期和・Consumption を仮定として残していない。全体 PAL 接続は未完了。

- GSPreprocessProg67：新しい `DECOMPOSE 8` の実行証拠を15本の段テープへ
  射影・埋め込みで接続。prologue 後の分解結果、入力・テキスト保存、
  線形費用を証明し、既存 epilogue との合成が `SetupPre` を満たすことも証明。
  旧 `decProg` とのトレース一致は仮定しない。前後処理自身の有限構文と
  全体機械への組み込みはまだ未完了。両定理の公理は標準三公理のみ。

- GSPreprocessProg68：前処理入口の有限ループ用に、左端番人で止まる2本同時
  コピーと、右端番人まで2ヘッドを同じ距離だけ進める処理を証明。
  コピーは旧 `copyLoop2` と作用が一致し、後者は入力ヘッドを余分に空白へ
  進めずに復元するための部品。実行証拠・長さ・逐次ビューと他テープ保存を検証。
  入口全体の有限プログラム合成は引き続き未完了。

- GSPreprocessProg69–73：入口全体、番人付きテープの消去、結果カウンタの
  正規化と後片付けを有限 `Prog` として証明。各処理の状態・保存条件・費用を検証。
- GSPreprocessProg74：12本の分解本体を共有15テープへ埋め込み、入口・本体・
  後片付けを同じ解釈上で逐次合成する `exec_shared_seq` を証明。
  `finitePrep` の有限構文を定義し、埋め込み後の最終状態も既存のテープ実行と一致。
  合成補題の公理は標準三公理のみ。
- GSPreprocessProg75：`finitePrep_exec_normalized` が `PrepPre` から有限前処理の
  実行、具体的テープ終状態、周期・到達域の正規化と作業2テープの空状態を証明。
  全体の動作数は `(preprocessSlope+16)*L+preprocessOffset+23` 以下。
  到達域が入力長以下であることも使った線形上界で、標準三公理のみのguardを含む
  `lake build PalPeg.GSPreprocessProg75` が成功。さらに入力・テキストの保存と全カウンタの
  条件を合わせ、完全な `SetupPre` への接続も同定理内で証明・再ビルド済み。
  PAL全体への接続は未完了。
- GSPreprocessProg76：固定構文 `finitePrepSetup` が有限前処理から有限セットアップへ
  進み、走査器・検証器の初期配置 `VEncodes'` を作ることを証明。
  正規化周期が `L+1` 以下であることも証明し、動作長は
  `(preprocessSlope+25+7*k)*L+preprocessOffset+37+11*k` 以下。
  入力内容・長さ・分解結果をプログラム構文に埋め込まず、共有15本テープ上で実行する。
  `lake build PalPeg.GSPreprocessProg76` と標準三公理guardが成功。
- ProgLangBank / ProgLangBankTapes：固定個数のプログラムの継続を有限制御の
  直積で保持する `bankMachine` を定義し、1ラウンドの具体的動作を証明。
  独立したテープ区画では、任意の切替列を各スロットへ射影した実行が
  単独の `runInputs` と一致する。完了後の余分な実行枠でも終状態を保持する。
  これにより、PCテープの `Resumable` を仮定せずに有限プログラムを中断・再開できる。
- FinitePrepBank：具体的な `finitePrepSetup` を上記の多重化へ接続。
  各スロットに線形上界以上の実行枠を割り当てれば、他スロットの進み方に
  依存せず、既に証明した走査器初期配置へ到達する。
  初期配置・自スロットの継続の開始条件は明示的な前提であり、段の誕生・再利用・
  入力供給・照合ループ・全体PAL受理の接続はまだ未完了。
  標準三公理guardを含む `lake build PalPeg` が成功（8769 jobs）。
- GSVerifierProgZLoop：ジグザグ照合の向きを1本の停留テープへ最後に1回書き戻す
  `unitsReturn` と `stepProg` を構成。途中で折り返す場合も含め、作業テープの
  終状態と次の向きが既存の `vprogramZ'` / `vDirZ` と一致し、追加は正確に1動作。
  入力長・反復回数を含まない単一の `loopProg` へ戻る `loopProg_chunk` も証明。
  `loopProg_chunk_spec` は具体的実行・継続保存・`VEncodesZ'` 保存・点ごとの
  費用 `≤ (9*k+14)*ΔΦ+18` をまとめて保証する（ループ頭の恒等動作を含め追加2）。
  各定理の標準三公理guardと単体Lean検査は成功。
  入力供給と段の期限・再利用をこの固定ループに接続する部分は残る。
- FiniteMatcherBank：固定 `loopProg` を独立スロットへ埋め込み、任意の切替列の下でも
  自スロットの必要な実行枠がそろえば、正しいジグザグ次状態・向き・ループ継続へ
  到達することを証明（`loopProg_interleaved`）。入力供給はこの定理に含まない。
  `lake build PalPeg.FiniteMatcherBank` が成功し、標準三公理guardを確認。
  続けて全体 `lake build PalPeg` も成功（8771 jobs）。
- RTQueueDispatch：待ち行列の回転処理を、4種類の粗い状態 `Phase` と
  先頭セル／単進カウンタの読み取りで分岐させる固定 `dispatchProg` を構成。
  `dispatchProg_exec` は既存 `execProg` とテープ終状態が一致し、読み取りと
  正確な復元の追加2動作を含めても11動作以内であることを証明。
  `phaseAfter_eq` は実行した分岐から次の粗い状態を計算できることを保証する。
  `EShape` を外から渡す必要はなくなったが、`Phase` と役割割当の保持・更新を
  snoc/tail全体へ接続する部分はまだ残る。単体Lean検査と標準三公理guardは成功。
  全体 `lake build PalPeg` も成功（8772 jobs）。
- RTQueueControl：専用の停留セルに `Phase × (Role → Role)` を符号化し、
  キュー10本＋制御1本の直和インタープリタで実際に読み書きする固定プログラムを構成。
  `rotation_runs` は回転と段階更新を12動作以内、`twiceAndInstall_runs` は
  2回転と取り付け・役割割当の保存を28動作以内で行い、キュー不変条件を回復する。
  `checkQueue_runs` は差分カウンタを読み、回転開始時の役割変更もセルに保存して31動作以内。
  `enqueue_runs` は後尾追加を含め34動作以内で抽象 `snoc` のテープ表現を保存する。
  これらのプログラムにはキュー値や実行ごとの分岐タグを渡さない。有限な制御符号化の
  存在も `canonicalCode` で構成した（最小アルファベットを主張するものではない）。
  4つの主要定理の標準三公理guard、単体Lean検査、全体 `lake build PalPeg`
  （8773 jobs）が成功。dequeue側の無効化・入力供給・段ライフサイクルの接続は未完了。
- **機械内モードからのdequeue（2026-09-08）**: `RTQueueDequeue.lean` で
  `dequeue_runs` を証明。プログラムはキュー値や分岐タグを引数に取らず、前面テープを
  読み戻して空判定し、格納済みphaseとokカウンタから無効化を選択する。
  非空の構造不変条件からappending 0のrp非空を導き、追加のrpプローブは不要。
  `invalidateQueue_runs` は7動作以内、`dequeuePrefix_runs` は11動作以内、
  `dequeue_runs` は空の場合も含め44動作以内で抽象 `tail` の表現とphase一致、
  役割割当の単射性を保存する。表現保存の前処理も `tailPrep_encodes` として独立化。
  単体Lean検査と4定理の標準三公理guardが成功。繰り返し利用のためのマーカー非混入の
  保存、入力供給および段ライフサイクルとの接続は別途必要で、PAL全体証明はまだ未完了。
  全体 `lake build PalPeg`（8774 jobs）と `git diff --check` も成功。
- **キュー操作の反復可能な契約（2026-09-08）**: `RTQueueClosed.lean` に
  `Ready`（Inv、抽象FIFO内のマーカー非混入、テープ表現、格納phase一致、役割単射性）を
  定義し、`enqueue_ready` と `dequeue_ready` がこの同じ条件を返すことを証明。
  非混入条件は生きたFIFOデータにだけ課し、任意のテープ残骸の消去は仮定しない。
  `operations_from_empty` は初期表現から任意個の混合操作を44×操作数以内で実行し、
  FIFOリスト仕様とReadyを保存する（追加データはマーカー以外）。この列は要求操作の列で、
  内部phase/branchを補う列ではない。`peek_runs` は先頭を読んで復元した後に、
  抽象FIFOの先頭値を有限分岐の後続処理へ渡すCPS契約を2動作で証明。
  単体Lean検査と4主要定理の標準三公理guardが成功。初期表現を空白テープから生成する
  コスト、入力供給・段ライフサイクルの接続は本定理の範囲外で、全体証明は未完了。
  全体 `lake build PalPeg`（8775 jobs）および `git diff --check` も成功。
- **機械内制御付き入力供給（2026-09-08）**: `ProgLangChoice.lean` の有限CPS分岐を
  用い、`TextFeedControl.lean` を追加。11本のキュー（モードセル込み）と8本の走査器の
  19本テープ解釈を構成した。既存 `I8` の走査命令は `executes_scan` でそのまま移送可能で、
  有限アルファベットの文字を書き込む命令のみを追加。`supply` は先頭を読み戻して
  走査テープへ書き、dequeueする固定プログラムで、外部q/phase/役割割当を引数に取らない。
  `supply_runs` は47動作以内、`feedRound_runs` は到着・供給・右移動を81動作以内で
  実行してReadyを保存する。右移動は書き込みと融合したが、`feedRound_matches` が
  既存 `TextFeed.startRound'` と走査テープ結果・抽象キューの一致を証明している。
  `supply_matches` も既存 `fill'` に対応。5主要定理の標準三公理guardと単体検査が成功。
  なお、到着文字aは有限引数のままであり、実入力の取り込み、供給タイミングの条件分岐、
  段ライフサイクルを含む全体機械への接続はまだ残る。PAL全体の証明完了ではない。
  全体 `lake build PalPeg`（8777 jobs）と `git diff --check` も成功。
- **供給タイミングとオンライン反復（2026-09-08）**: `TextFeedTiming.lean` で
  `fillIf_matches` を証明。既存 `TextFeedProg2` のテープ読みによる判定補題を再利用し、
  新しいモードセル付きキューでは、走査テープの空白とキュー先頭のマーカー判定だけで
  `fillIf'` を47動作以内で実現する。判定失敗時は0動作、先端だが空キューなら復元込み2動作。
  `micro_matches` は供給後のenabled判定も実テープで行い、旧 `runInT' … 1` と一致する。
  `runIn_matches` は同じ固定microプログラムの反復で、旧実装の実行ごとのπFやqの引数を
  不要にした。`round_matches` は到着＋`gsRate rate`反復を旧 `roundT'` に接続し、
  Readyと走査テープの一致を保存する。動作上限は既存と同じ走査一歩の上界cの仮定の下で
  `34 + gsRate rate * (c + 47)`。c自体の新しい一様評価を主張するものではない。
  4主要定理の標準三公理guardと単体検査が成功。実入力captureと全体の中断・再開・段回収への
  接続は引き続き未完で、PAL全体の完了とは区別する。
  全体 `lake build PalPeg`（8778 jobs）と `git diff --check` も成功。
- **実入力到着との接続（2026-09-08）**: `TextFeedInput.lean` に20本目の静止入力セルと
  既存 `ArriveAct` 形式の `capture` を構成。`workerRound` は記号引数を取らず、そのセルを
  有限分岐で読んで閉じたオンラインラウンドを実行する。`arrivalRound_matches` は
  実Terminalからの到着1動作と後続実行の結果を旧 `roundT'` に結び、
  `35 + gsRate rate * (c + 47)` の上限とReady保存を証明（走査stepCostの上界c仮定は維持）。
  `capture_worker_frame` は他19本への非干渉、`bank_capture_zero` は既存の継続保持バンクの
  フェーズ0で全継続を保持し、入力セルだけを更新することを証明。
  4主要定理の公理guardと単体検査が成功（新規公理・sorry依存なし）。
  ただしこの接続は未読入力の上書きを防ぐ全体スケジュールをまだ構成していない。
  実行窓の予算・中断点、段生成から回収までの接続は残っており、PAL全体証明は未完了。
  全体 `lake build PalPeg`（8779 jobs）と `git diff --check` も成功。
- **安全なキュー操作スロット（2026-09-08）**: `ProgLangBudget.lean` と
  `RTQueueSlots.lean` を追加。短いExecの残りを固定長の実行窓で待機させる補題を証明し、
  操作44動作＋継続正規化1クロックの45クロック枠で、キューReadyと空の継続を回復する。
  「現在のテープでは動かない」SEqAtだけでは後のテープ変更で残存条件分岐が再び動けるため、
  境界条件を継続リストの厳密な `=[]` に強めた。
  `bank_slot_ready` は他のバンク継続を保持し、`transact_ready` は完了済みのエントリだけを
  再開して同じ空継続・Readyを返す。`restartDone` は未完了の継続を捨てずそのまま残す。
  3主要定理の標準三公理guardと単体Lean検査が成功。型検査時の実行展開によるtimeoutは、
  局所的にrunChunkの定義展開を抑え、証明済みの実行補題を使うことで解消した。
  全体の入力到着・走査・段処理をこの切替境界に沿って配置するスケジュールはまだ未構成。
  この局所スロット証明だけで入力欠落や全体PALの証明が閉じたとは主張しない。
  全体 `lake build PalPeg`（8781 jobs）と `git diff --check` も成功。
- **キュー枠の実フェーズ化（2026-09-08）**: `ProgLangTransaction.lean` に
  `transactionBody` と有限制御 `transactionMachine` を追加。
  phase 0 は完了済み継続だけを再開し、テープを保持する。残りの各phaseは
  バンクの実マイクロステップと一致する。`transactionBody_block` は
  H+1フェーズの実行が `restartDone` 後のHクロック実行と一致することを証明。
  `RTQueueSlots.phaseRun_transact` により、キュー取引を再開1＋実行45の
  46実フェーズへ接続した。主要なブロック定理と接続定理の標準三公理guard、
  `lake build PalPeg.RTQueueSlots` が成功。これは入力到着を含まない内部ブロックであり、
  全体入力スケジュール・実時間上限・PALの無条件証明は依然未完了。
  全体 `lake build PalPeg`（8782 jobs）と `git diff --check` も成功。
- **動的呼び出し・実入力フレーム・給送器（2026-09-08）**:
  `ProgLangCalls.lean` は有限外側制御とテープの先頭記号だけから呼び出し先を選び、
  その番号をブロック終了まで保持する。`callRun_exec` は短いExecの終点・空継続・
  他継続の不変を保証し、未使用または完了済みのバンク境界 `AtBoundary` を保存する。
  `RTQueueCalls.call_ready` はこの動的選択を実キュー操作へ接続した。
  `ProgramFrame.lean` / `ProgLangCallFrame.lean` は、実入力1回の到着動作と
  固定R個の内部呼び出しを `StructuredMachine.sRound` へ接続する。
  `callFrameMachine_round` の物理クロック数は `1 + R*(H+1)` で、内部入力はnone。
  `TextFeedAtomic.lean` の `low_bounded` は追加・空判定付き供給・GS基本命令・待機を
  一律47動作以下とし、任意の途中走査テープ上でもキューReadyを回復する。
  `call_ready` で再開1＋実行/正規化48の49クロック枠へ接続。長いGSループ全体を
  定数時間と仮定せず、各基本命令だけを呼び出しにする。
  `TextFeedSchedule.lean` は実際の到着レジスタを使う有限給送器を定義。
  1入力につき最初の1呼び出しで追加、その後R回だけ永続GSワーカーを再開し、
  物理予算は `1 + 49*(R+1)`。`run_first_enqueue` は追加のFIFO効果とワーカー不変、
  `run_enqueues_once` は枠内の追加が最初の1回だけ、`machine_round_ready` は
  到着から実ラウンド終了までのキューReady・バンク境界・カウンタ復帰・入力レジスタ保存を証明。
  ここでRは固定機械パラメータ。十分なRの選定、途中GS制御の参照算法への対応、
  走査結果の締切、空テープからの初期化、複数段への統合はまだ証明していない。
  この給送器はPAL認識器そのものではなく、全体PALの無条件証明は未完了。
  主要定理の標準三公理guard、全体 `lake build PalPeg`（8788 jobs）、
  `git diff --check` が成功。全体ログはToken Sieveで保存して確認した。
- **中断GS走査と実入力列の対応（2026-09-08）**: `TextFeedScan.lean` を追加。
  GS条件が走査8テープだけを読むことを証明し、`run_scan_step` / `run_scan_prefix` で
  実給送器のワーカー呼び出しが元GSプログラムの各命令・残存継続に一致することを証明。
  `busy_frame` / `busy_frames` は、走査がまだ命令を出し続ける範囲で、実入力1回ごとに
  到着文字を追加し、GSをR命令進めることを任意の入力列について示す。
  その間のキューは受信列を順序どおり追加したものとなり、`arrivals_fifo` は
  内容が元のFIFO列と受信列の連結になることを示す。両フェーズ・呼び出し境界も保存する。
  `run_scan_return` は走査終了時に外側の継続と同じ次の制御遷移へ戻ることを証明。
  `source_certificate` が既存 `GSProg.scanProg_exec` / `scanProg_tapes` から、
  途中実行の前提・実際のGS終点・終了を供給する。GS全体を定数時間と仮定していない。
  まだ給送ワーカーの全反復（供給・GS開始・完了の切替）の参照不変量、十分な固定Rと
  出力締切、空テープ初期化、多段統合は未完了。全体PALの完成は主張しない。
  主要定理の標準三公理guard、全体 `lake build PalPeg`（8789 jobs）と
  `git diff --check` が成功。
- **給送ワーカー全フェーズの参照不変量（2026-09-08）**:
  `TextFeedCycle.lean` が実制御の待機・供給・走査入口を接続し、GS終了時の
  制御同値から次の反復へ戻す。`TextFeedCycleModel.lean` は供給効果を参照
  `fillIf'` と一致させ、ヘッド記号による走査許可の安全性を証明した。
  供給確認とゲートの間に到着があると、参照Enabledが真でも実ゲートが偽で
  一度待機し得る。これを偽の同値で消さず、`disabled_pending` で必要な供給として
  特定し、開始してよい条件の片方向の安全性は到着の有無に依存させていない。
  `TextFeedRefine.lean` の `Sim` は参照FeedInv、キューReady、バンク境界、各制御相、
  中断GSの元状態と進捗をまとめる。進捗数や参照Machine'は証明用で、実制御には渡さない。
  `worker_step` は全制御相を覆う決定的参照遷移への対応、`worker_steps` はその任意回数の
  合成、`arrival_step` は中断中でも参照キューと到着数だけを更新する対応を証明。
  `frame_step` は実 `StructuredMachine.sRound` の到着1回＋全ワーカー窓について
  `Sim` と両フェーズ・マクロカウンタの復帰を証明した。
  機能的な給送器の全相接続は進んだが、十分な固定Rのサービス・出力締切保証、
  空テープ初期化、多段統合、最終受理フラグは未完了。PAL全体の完成ではない。
- 上記 `TextFeedRefine` 接続後の全体 `lake build` は8792ジョブで成功。
- `TextFeedWork` で中断走査の実進捗を含む償却評価
  `(8*rate+22)*Phi + progress` を導入。`retirement_work` は走査完了時に
  実動作数と復帰1回分を払い切ること、`advance_work_mono` は全制御相での
  非減少、`scan_advance_work` は走査中の各呼出しで1以上の増加を証明。
  この段階では締切証明の処理量部分であり、以下で待ち相とサービス保証を接続した。
- **給送器の固定レートサービスと出現締切（2026-09-08）**:
  `TextFeedWork.enabled_productive` は参照Enabledが真なら3呼出し以内の進捗を証明。
  到着で古くなった偽ゲートも、待機→供給→走査開始の3回で覆う。
  `work_service` は任意窓Nで、入力先端に到達するまで少なくともfloor(N/3)の
  credit増加を保証する。`workRate = 3*(8*rate+22)*(rate+1)` はパターン長・入力長に
  依存しない。`onlineWork_credit` は有効な初期参照状態から任意の入力長について
  この固定レートで先端creditの不変量を証明した。
  `TextFeedDeadline.onlineWork_stable_deadline` は、KSimple走査不変量と安全なずらしを
  合わせ、位置iの出現が終了する入力ラウンドi+|v|の中で報告されることを証明。
  最初の報告は走査完了後のfill相であり、中断中の進捗だけでは締切を満たせない。
  `TextFeedPhysicalDeadline` はこの報告を実20テープのパターン終端記号読取へ接続。
  初期化済み状態とのSimを前提に、実入力capture＋enqueue＋固定ワーカー窓内の
  実macrocall列について報告の存在を示す。参照credit・追い越し禁止は
  `online_frame_deadline` 内で先行するオンライン実行の定理から導いている。
  未完了なのは、空テープからこの初期条件を構築する統合、複数段・接頭辞検証器との
  接続、報告を実受理フラグへ保存してPAL受理と同値にする部分。途中の終端記号読取を
  最終受理フラグとは扱っていない。
  さらに `TextFeedStream.preparedRun_refine` は実 `machine.sRound` の入力列foldについて、
  初期Sim一つから全接頭辞のSimと両時計の復帰を証明。
  `preparedRun_deadline` は各ラウンドのSim・credit・追い越し禁止を個別に仮定せず、
  初期化済みのSim一つから全出現の物理的締切報告を導く。
  初期走査不変量も到着数0のFeedInvから導出する。
  `preparedRun` は準備済みテープからの実sRound実行であり、空テープの`sInit`とは別物。
  全体 `lake build PalPeg` は8796ジョブで成功。新しいサービス・安定締切・連続実行の
  主要定理は `#guard_msgs` により標準の3公理のみであることも検査した。
- **空キュー生成と有限前処理の同居（2026-09-08）**:
  `RTQueueInit.init_exec` は真の空白10本からマーカーと差分カウンタを11命令で構築。
  `TextFeedInit.boot_exec` は私有モードの書込みも含め12命令で初期化し、既存の
  走査8本と入力レジスタを保存する。`boot_to_sim` はその実行結果から初期Simを導出し、
  配置済みキューマーカーやReadyを前提にしない。
  `TextFeedPrepare.prepareProg` はqueueBootと既存のfinitePrepSetupを同じ27本
  （queue11＋前処理/検証器15＋入力1）上の有限プログラムとして合成。
  `prepare_spec` は既存StageTapes.PrepPreからの実Exec、長さLに対する線形費用上界、
  出力VEncodes'と初期Simを同時に証明した。費用は既存前処理上界に12を加えたもの。
  給送器20本へのfeedSlotは固定単射で、物理的なテープコピーは行わない。
  ここで全体の空テープsInitが完成したわけではない。元パターン/StageTapes.PrepPreの
  生成・各段の誕生時刻との統合、前処理から常設ワーカーへの実有限制御の引継ぎ、
  接頭辞検証器との接続、最終受理フラグへの保存がなお必要。
- **将来の入力長に依存する空白配置の除去（2026-09-08）**:
  現行のSeqViewは右リストに空白を明示するため、`birthTapes ... n` のnは物理的な
  事前配置ではなく証明用の代表として扱う必要がある。
  `ProgramBlankEq` は左側の長さとヘッドを同一に保ち、右側だけを無限空白補完で比較する。
  全書込み・左右移動、実StructuredMachineの全入力実行と受理制御がこの同値性を保存。
  `ProgLangBlankEq.exec_blankEq` は有限プログラムのExecを、同じ動作列・同じ費用のまま
  明示空白のないテープへ移送する。
  `TextFeedUnpadded.prepare_unpadded` は実初期テープに`birthTapes ... 0`を使い、将来の
  Text.lengthに依存する余分な右空白を一切配置せずに前処理・給送器初期化を実行する。
  Text.lengthは証明用の同値な代表を選ぶためだけに現れる。
  出力は初期Simを持つ代表と全ヘッドが一致し、`future_blankEq` が以後の各入力ラウンドと
  ラウンド途中の任意マイクロステップ列でも実制御・ヘッドの同値性を保証する。
  この証明は、パターンコピーやカウンタの初期設置、段誕生時刻・有限制御の引継ぎ、
  検証器と最終受理の統合が済んだという主張ではない。
  これらを取り込んだ全体 `lake build PalPeg` は8803ジョブで成功。
  `init_exec`・`boot_to_sim`・`prepare_spec`・`exec_blankEq`・`prepare_unpadded`・
  `future_blankEq` の主要定理は標準3公理のみのguardも通過した。
- **同じ27本で動く実給送器（2026-09-08）**:
  `TextFeedMachine27.on27` は既存のStructuredMachineを固定feedSlotへ載せる実機定義。
  `on27_micro_view`・`on27_run_view` は各物理マイクロステップと任意入力列について
  20本の元の実行との厳密一致を証明。時計上界と有限制御の型は増えない。
  `on27_run_aux` は残り7本の前処理/検証器テープが全入力長で完全に不変と示す。
  `run27_blank_view` は余分な右空白を持たない前処理出力にも既存の実行証明を移送する。
  全体 `lake build PalPeg` は8804ジョブで成功、主要定理の標準3公理guardも通過。
  前処理終了からこの給送器への実制御引継ぎと、前処理中の到着文字保持は別途必要。

- **到着を止めない有限前処理スケジューラ（2026-09-08）**:
  `TextFeedStartup.firstEnqueue_exec` は白紙FIFOの初期化12動作と最初のenqueue最大34動作を
  合わせ、46動作以内で同じ最初の入力を保持することを証明。
  `TextFeedStartupBank.shared` は既存の給送器と前処理を同じ27本に載せた解釈。
  `first_exec`・`feed_exec`・`prep_exec` はそれぞれ46・47・1動作の上界を持つ。
  `TextFeedStartupSchedule.machine` は入力長に依存しない有限制御で、
  `seq finitePrepSetup worker` を中断・再開する実機。各実入力は1回だけcaptureされ、
  `run_enqueues_once` が1ラウンドにつきenqueueを1回だけ選ぶと示す。
  `TextFeedStartupRun.run_first` は実呼出しからReadyキューを生成し、
  `machine_round_ready` は以後の各入力ラウンドでキュー呼出しの完了・入力レジスタ保持・
  enqueue位相への復帰を証明する。前処理中のGS不変条件を仮定しない。
  `TextFeedPrepResume.run_prefix` は前処理の任意の生産的命令区間について、元の15本の
  プログラムとのテープ・継続の厳密一致を証明。
  `TextFeedPrepInterrupt.run_enqueue` は入力割込みが15本すべてと継続を保つと示す。
  `TextFeedPrepFrames.busy_frames` は任意の実入力列に対し、元の前処理が
  `word.length * R` 命令進む間、到着がすべて順序通りFIFOへ蓄積されると証明した。
  これらの主要定理は標準3公理のみのguardを通過。
  前処理完了境界と蓄積済みキューを既存の締切不変条件へ接続する証明、
  段誕生の有限初期化、全体段スケジュール、prefix検証器・最終受理の統合は残る。

- **前処理完了と空白埋めなしの引継ぎ（2026-09-08）**:
  `TextFeedPrepEndpoint.end_at_cost` は実入力列を受けながら進む前処理全体を、
  最後の部分ラウンドとworker継続への引継ぎまで一つの定理にまとめた。
  到着済み文字はFIFOに保持され、元の15本の前処理出力と一致する。
  `TextFeedPrepared.prepared_link` はこの出力と準備済み給送不変条件を接続する。
  ここまでの全体ビルドは8821ジョブで成功。
  `TextFeedStartupUnpadded.birth_prefixRun_blankEq` は新しい統合機について、
  段誕生時の余分な右空白をゼロにしても、任意入力列・次の到着・任意回数の呼出し後の
  制御状態、左側テープ列、ヘッド値が一致することを証明した。
  将来の入力長に依存する空白は証明用代表にのみ置き、実機には要求しない。
  新定理の標準3公理guardと全体ビルド（8822ジョブ）が成功した。
  段誕生そのものの有限初期化、蓄積入力を含む開始時刻からの締切証明、
  prefix検証器・全体段スケジュール・最終受理の統合は未完。

- **実開始時刻からの給送締切と統合実機への移送（2026-09-08）**:
  `TextFeedRefine.onlineWorkFrom` は実到着数 `base` から開始し、以後の文字だけを
  enqueueするモデル。開始時点のFIFO内の文字を捨てたり再入力したりしない。
  `onlineWorkFrom_credit`・`onlineWorkFrom_no_skip_before` は開始時点の仕事量条件を
  一度だけ仮定し、以後の全ラウンドで仕事量と締切前の非飛越しを帰納的に保つ。
  `preparedRun_offset_refine`・`preparedRun_offset_deadline` は実入力の
  `(input.drop base).take n` の連続実行と、絶対時刻 `base+n+1` の物理報告を証明。
  `TextFeedWorkerBridge.frame_link`・`workerRun_link` は到着処理を含む各ラウンドと
  任意入力列について、27本の統合機と20本の給送器を対応づける。
  `workerRun_offset_deadline` はこの対応を使い、統合機の実テープへ締切報告を移送する。
  制御の置換・テープコピー・毎ラウンドの新しいSim/credit仮定は使わない。
  主要定理の標準3公理guardは通過。開始時点のLink/Sim/creditは依然として前提であり、
  前処理の最終部分ラウンドから通常境界までの接続と、段初期化・prefix検証器・
  全体段スケジュール・最終受理の実装証明はまだ必要。
  全体 `lake build PalPeg` は8826ジョブで成功、`git diff --check` も通過。

- **前処理から通常境界までの接続と生の段テープ（2026-09-08）**:
  `TextFeedWarmBoundary.finish_frame` は前処理の最後の部分ラウンドを処理しきり、
  Link/Sim・仕事量・走査不変条件・未飛越しを保って通常の入力境界へ戻ると証明。
  `TextFeedStartupClock.finish_prefix` はその処理が新しい時計窓ではなく、同じ入力の
  実フレーム内の残り呼出しそのものであることを示す。
  `TextFeedStartupBoundary.end_at_boundary` は実前処理の完了からこの境界までを接続。
  `TextFeedStageStartup.setup_reaches_boundary` は固定レート `startupRate 8` と
  既証明の有限前処理を使い、`1 ≤ n ≤ L/2` 回の実入力でStreamReadyへ到達すると証明。
  分解・初期credit・前処理費用・結果のSimを独立の仮定にせず、PrepPreから導く。
  `birth_reaches_boundary` は実機の初期テープを `birthTapes ... L 0` とし、
  将来の入力長に依存する空白なしで同じ境界へ到達することを示す。
  `observed_ready_deadline` はこの空白埋めなしの実機にも締切報告を移送する。
  主要定理は標準3公理guardを通過。ここでいう生の段テープには入力コピーと
  カウンタ番兵が既にあるため、その段誕生プログラムの有限実装は依然として未完。
  prefix検証器・全体段スケジュール・受理ラッチとPAL全体の接続も残る。
  全体 `lake build PalPeg` は8832ジョブで成功、追加6モジュールに警告なし。

- **prefix検証器の細粒度給送を有限キューへ接続（2026-09-08）**:
  `VerifierFeedClosed.fill_matches`・`step_matches` は既存の `vfillHead2` と
  `vstepXR` を有限モード付きFIFOのプログラムで実現し、給送47・右移動込み48動作以内。
  判定はテープヘッドだけで行い、実キューと参照モデルの物理role配置を同一と仮定しない。
  `VerifierFeedShared` はFIFO11本と走査器/検証器10本を同居させた21本への固定埋込み。
  `step_matches` は全テープの結果一致、`step_safe` はTxt2の書込み済み領域に穴を作らず
  次のセルを読み出せることを、既存の到着範囲不変条件から示す。
  `VerifierFeedPrimitive.low_matches` は有限な10本テープ命令の全てについて48動作以内の
  呼出しを与え、Txt2のkeep-rightだけは給送を挟む。
  `VerifierFeedMachine.run_refine_iterate` は任意の固定sourceプログラムについて、
  その有限継続を進める実呼出しと給送付き命令モデルの一致を任意回数で証明。
  `machine_blocks` は1呼出し50マイクロステップの実機実行と厳密に一致すると示す。
  `VerifierFeedCompare.comp2_matches` は2回の比較を給送込み98動作以内で実現し、
  2回目が1回目の給送後のテープを読むことまで結果一致で検証した。
  主要定理の標準3公理guardは通過。これは入力到着を含む完全な検証器ではまだなく、
  第2FIFOへのenqueue、zigzag source・初期位置・走査側給送との接続、
  検証器全体の締切・報告ラッチと、段生成/全体PAL機械の統合は残る。
  全体 `lake build PalPeg` は8837ジョブで成功、追加5モジュールに警告なし。

- `DualQueue` / `DualQueueInput` / `DualQueueMachine` / `DualQueueShared`：
  一度の実入力到着で走査用と検証用の両FIFOへ追加する有限プログラムを実装。
  二重enqueueは68動作以内、空白からの初期化込みは92動作以内。
  入力レジスタへの一度のcaptureを含めると通常69・初回93動作以内で、
  プログラム自身が同じレジスタを読み、外部入力の反復はしない。
  `DualQueueMachine` は有限の初回ビットとプログラムバンクを持つ実23本機械。
  `first_refine` / `arrival_refine` は1文字あたり固定95クロックの実ラウンドから
  両FIFOの更新、呼出し境界と位相0への復帰まで示す。
  `srun_contents` は完全に空白の初期テープから任意の非空入力を読み、
  両方のキュー内容が入力列の符号化に厳密一致することを証明。
  `DualQueueShared` はQ1=0..10、前処理/走査=11..25、入力=26、
  Q2=27..37、方向用=38の39本配置へ移送し、予約した16本を変更しない。
  `arrival_feedInv` は両キューの実更新と参照モデルの到着後の給送不変条件を接続。
  実FIFOとモデルFIFOの物理role配置の一致は仮定しない。
  主要定理の標準3公理guardは通過。検証器への初期位置合わせ、左右移動中の
  給送と締切、前処理/検証器を共有する実機制御、段生成・回転・報告ラッチ、
  無条件のPAL認識定理はまだ残る。
  全体 `lake build PalPeg` は8841ジョブで成功、追加4モジュールに警告なし。

- `TextFeedAlign` / `TextFeedPrefixControl` / `TextFeedPrefixReady`：
  前処理後の走査位置0から、検証器が要求する接頭辞長 `|u|` への位置合わせを実装。
  `TextFeedAlign.program_matches` は既到着FIFOからの給送＋右移動を48動作以内で示し、
  空のFIFOではヘッドを動かさない。`advance_iterate` は到着数を固定したまま
  進めた位置が `min (元の位置 + 歩数) 到着数` になることを証明。
  `TextFeedPrefixControl.program` は接頭辞テープの終端記号で止まり、開始記号まで
  巻き戻して先頭へ復帰する固定プログラム。入力長・接頭辞長はプログラムの引数でない。
  `step_empty` はFIFOが空の間、テキストと接頭辞の両ヘッドを動かさない。
  `program_runs` は必要な文字が既に到着していれば `51|u|+2` 動作以内で
  走査位置 `|u|`、一致長0、書込み済み長 `|u|`、接頭辞ヘッド1に到達すると示す。
  この位置合わせ中には新しい入力到着を呼ばない。
  `TextFeedPrefixReady.ready_after_prefix` は39本配置へ移し、第2FIFO・Txt2・補助・
  入力レジスタ・方向テープを保持したまま、実キューの表現から検証器の
  `VFeedInv'` を構築する。`pos = 0` を不正に検証器初期位置とみなす仮定は置かない。
  `unpadded_runs` は空白同値を使い、証明用の右空白列を実テープに要求しない。
  主要定理の標準3公理guardは通過。これは位置合わせの物理プログラムと終点仕様であり、
  位置合わせ中の到着を原子的な給送呼出しの間で受ける固定レート制御への接続、
  zigzag検証器の給送・締切、方向初期化、段生成・回転・報告ラッチ、最終PALは残る。
  全体 `lake build PalPeg` は8844ジョブで成功、追加3モジュールに警告なし。

- `TextFeedPrefixAtomic` / `TextFeedPrefixBank` / `TextFeedPrefixMachine`：
  位置合わせを給送・テキスト右移動・U移動・待機の有限命令に分割し、
  1命令47動作以内でFIFO更新を完了する呼出しへ落とした。
  `TextFeedPrefixBank` は二重enqueueと位置合わせを同じ39本テープ上で解釈し、
  `work_matches` はQ2・Txt2・補助・入力・方向を保存する。
  `enqueue_matches` はGS/U等を保存しつつ両FIFOへ追加し、68動作以内。
  `TextFeedPrefixMachine` は固定Rに対して `94*(R+1)+1` マイクロステップの
  入力フレームを持つ有限機械。入力捕捉を1回、enqueueを1呼出し、その後R回の
  位置合わせ命令を実行し、FIFO操作の途中には到着を割り込ませない。
  `run_refine_iterate` は各原子呼出しと参照モデルの任意回数の一致、
  `round_refine` は実1ラウンドで両Ready・呼出し境界・位相0の復帰を示す。
  `word_sim` は同じ有限制御を保持した任意の連続入力列へ拡張。
  `frame_q₂` / `word_q₂_contents` は第2FIFOへの追加が各入力につき厳密に1回で、
  内容が既存列＋入力列になることを示す。
  主要定理の標準3公理guardは通過。位置合わせフェーズの模倣定理は初期化済み
  FIFO・適切な呼出し境界からのもの。真の前処理終点からこの制御への引継ぎ、
  原子命令版の接頭辞完了・入力待ち込みの締切、zigzag給送/検証締切、
  方向初期化・段生成/回転・報告ラッチ・無条件PAL認識はまだ残る。
  全体 `lake build PalPeg` は8847ジョブで成功、追加3モジュールに警告なし。

- `TextFeedPrefixCycle` / `TextFeedPrefixFinish` / `TextFeedPrefixRank` /
  `TextFeedPrefixDeadline`：原子命令版の接頭辞位置合わせの終了と締切を証明。
  `source_completed` は接頭辞が利用可能なら正確に `5*|u|+2` 回の命令で
  継続が空になり、テキスト位置 `|u|`・U位置1へ到達することを示す。
  7種の途中状態に残作業量を定義し、到着で同じ量を保存、入力待ち中も
  不変条件を保存、接頭辞到着後は各命令で残作業量を1減らす。
  `physical_complete` は実際の39テープ有限機械へ接続し、有効な追加入力列wと
  初期化済み模倣関係・途中状態の不変条件を前提に、`fuel ≤ |w|*R` なら
  実機の継続が空となり、位置合わせ終点仕様を満たすことを証明する。
  この期限は1フレームR命令（物理 `94*(R+1)+1` ステップ）に対するもの。
  主要定理は標準3公理guard通過。真の前処理からの引継ぎ、終了後のGS起動、
  zigzag給送/締切・方向初期化・段生成/回転・報告ラッチ・無条件PALは未完。
  全体 `lake build PalPeg` は8851ジョブで成功、追加4モジュールに警告なし。

- `TextFeedPrefixDeadline` を入力待ち・初期命令列まで拡張し、
  `TextFeedPrefixVerifier` で到着を伴う実機終点を検証器の給送不変条件へ接続。
  `frames_preserve` は接頭辞未到着の任意フレーム列でも途中状態を保存する。
  `physical_wait_complete` は待機後の状態を仮定せず、接頭辞が揃ってから
  `5*|u|+2 ≤ |running|*R` の予算で実機の接頭辞制御が完了することを示す。
  `source_frame` / `physical_source_complete` は初期 `[source]` 継続から開始し、
  最初の正レートフレームで不変条件へ入り、待機・完了へ到達する。
  `source_ready` はそれらと第2FIFOの正確な到着列・第2テキストの不動性を統合。
  両FIFOの物理表現は実機の模倣関係から取り出し、`pos=|u|, q=0, m=|u|` と
  `VFeedInv'` を満たす実テープ終点を得る。主要定理は標準3公理guard通過。
  前提は初期化済みFIFO・初期走査テープの表現であり、真の前処理からの
  制御引継ぎ、接頭辞終了後のGS起動、zigzag給送/締切、方向初期化、
  段生成/回転・報告ラッチ・無条件PAL認識は引き続き未完。
  全体 `lake build PalPeg` は8852ジョブで成功、変更2モジュールに警告なし。

- `TextFeedPipelineBank` / `TextFeedPipelineControl` / `TextFeedPipelineHandoff` /
  `TextFeedPipelineArrival` / `TextFeedPipelineVerifier`：旧27テープの直接GS起動とは
  別に、共有39テープで前処理→接頭辞位置合わせ→方向初期化→給送つきzigzagを
  同じ有限命令列として実装。入力フレームは `94*(R+1)+1` 物理ステップで、
  `run_enqueues_once` は各フレームのenqueue選択が1回のみであることを示す。
  `run_start` / `run_prep_step` は実前処理命令を共有15テープビューで1つ進める。
  `run_prep_handoff` は前処理の残余制御が返った次の呼出しで接頭辞の最初の
  動作を実行し、外部リセットなしにその継続を保持する。
  `run_prefix_return` は接頭辞終了後に方向テープへ実際に上向き記号を書き、
  他38本を保存しつつGSループへ切り替える。`run_verify_start` は比較の前に
  第1FIFOを給送する。`run_instruction` は通常のGS/検証命令を同じ39本上で
  実行し、Txt2右移動には閉じたFIFO給送を含め、両FIFOのReadyを保存する。
  `run_first` は空FIFOから両キューを初期化、`run_enqueue` は両キューへ1回ずつ
  追加し、前処理/走査/方向と待機中の継続を保存する。主要定理は標準3公理guard通過。
  これは単一制御と局所引継ぎ・各原子呼出しの証明。前処理全体の到着込み終了、
  接頭辞の期限・開始条件をこの制御へ移す証明、zigzag意味論/給送締切、
  段生成/回転・報告ラッチ・無条件PAL認識は未完。独立接頭辞機械の終了後の
  idleと異なり、本制御は直ちにGSへ進むので旧期限定理をそのまま適用しない。
  全体 `lake build PalPeg` は8857ジョブで成功、追加5モジュールに警告なし。

- `TextFeedPipelinePrepWindow` / `PrepInput` / `PrepFrames` / `PrepFinish` /
  `PrepSetup` / `PrepReady` と `ProgLangCallFramePrefix`：新39テープ制御へ、
  初回FIFO初期化を含む前処理の到着込み実行・終了・初期表現を接続。
  `ControlEq` は初期taskの未展開seqも許す構造的な制御同値。
  `run_window` は生産的なN呼出しと元の前処理N動作の厳密な一致、
  `busy_frames` は任意の実入力列に対する一致と両FIFOの到着順保持を示す。
  `callFrameMachine_prefix` はフレーム途中の実マイクロステップ列を証明し、
  `finish_at` は全フレーム列＋最後の到着とJ命令で、前処理終了直後の
  実テープ・制御・両FIFOを取り出す（J≤R、以後の接頭辞動作を混入させない）。
  `setup_finishes` は実際の `finitePrepSetup` と線形費用・GS/VEncodes仕様を
  これに適用し、初期taskから前処理終点と接頭辞継続への制御同値を得る。
  `prepared_rep` は実15テープビューと両FIFOの物理表現から39本全体を復元し、
  接頭辞の初期 `Rep`（pos=0, U=1, m=0）を実到着数nのままで構成。
  `arrivals_contents` はそのnを準備中の全入力と最後の部分フレーム入力に結び付ける。
  主要定理は標準3公理guard通過。初期段テープの `PrepPre` は前提であり、
  段生成自体は未完。新制御での接頭辞の終了時点・締切、zigzag意味論/給送締切、
  段生成/回転・報告ラッチ・無条件PAL認識の証明は残る。
  全体 `lake build PalPeg` は8864ジョブで成功、追加7モジュールに警告なし。
- `TextFeedPipelinePrefixLink` / `PrefixWindow` / `PrefixStart`：単一39テープ
  pipelineの実prefix状態とFIFO付きモデルの対応を追加。実テープ上の全task guard
  を使う制御同値は到着・enqueueと生産的prefix命令の双方で保存される。
  `window_progress` は利用可能な接頭辞に対し残量を1呼出しずつ減らし、
  `window_preserve_or_hit` は待機中でも窓内の終了地点、または窓末の対応を返す。
  完了後のGS処理をidleへ置き換えず、終了地点で証明を止める。
  `normalize` は実制御・テープ・時計を一切変更せず、準備出口のsource stackを
  証明用loop stackへ対応させ、`initial_rank` は初期Repから残量5|u|+2を得る。
  入力フレーム列全体を跨ぐprefix終了/締切と物理的到達証拠への接続はまだ残る。
  GSZ意味論/給送締切、段生成/回転・報告ラッチ・無条件PAL認識も未完。
  全体 `lake build PalPeg` は8867ジョブで成功。追加3モジュールに警告なし、
  主要公理guard通過（initial_rankはpropext/Quot.soundのみ、他は標準3公理）。
- `TextFeedPipelinePrefixFrames` / `PrefixHit` / `PrefixPhysical` / `PrefixEndpoint`：
  実到着とenqueueを含むprefixの終了時点を、任意の入力フレーム列へ拡張。
  `frame_progress` / `frame_complete` は残量に応じ、全フレームまたは完了直後まで
  実行する。`frame_wait` は未到着の接頭辞を待つ場合も、途中終了か継続を区別。
  `reach_of_budget` は接頭辞利用可能時に残量≤入力数×Rなら終了イベントを示し、
  `reach_after_wait` は待機入力後に接頭辞が揃い、作業枠≥5|u|+2なら同じ結論を得る。
  `hit_witness` はそれを実機の全入力ラウンド列、または最後の生入力1回と
  (J+1)×94個の内部noneマイクロ入力（J≤R）による到達証拠へ変換する。
  `ready_to_prefix` は準備完了時の実ビュー・実FIFO・実制御同値から
  同一物理状態で初期Link/Goodを構成する。時計を0へリセットしない。
  上記フレーム列定理の開始時計は0が前提。準備終了がフレーム途中の場合の
  残余枠を消化し、終了イベントまたは次フレーム境界へ接続する部分は未完。
  GSZ意味論/給送締切、段生成/回転・報告ラッチ・無条件PAL認識も残る。
  全体 `lake build PalPeg` は8871ジョブで成功。追加4モジュールに警告なし、
  主要定理の標準3公理guard通過。
- `TextFeedPipelinePrefixResume` / `PrefixPartial` / `PrefixPrepared`：準備終了後の
  フレーム残余を接続。`nextPhase_finish` / `remaining_window` は実呼出し回数から
  時計0への復帰を証明し、`resume_or_hit` はその間のprefix終了か境界までの保持を返す。
  `after_input_remaining` はenqueue後J命令の実状態で残余がR−Jになることを示す。
  `reach_from_partial` / `physical_from_partial` は途中状態から待機・締切を適用し、
  元の生入力フレーム先頭からのHit/物理到達証拠を返す（時計リセットなし）。
  `endpoint_eq` は実準備終了の物理証明から正確な途中呼出し状態を復元。
  `prepared_deadline` はそれと実準備ビュー/FIFO/制御/VEncodesを使い、準備中の
  全入力＋最後の入力＋待機＋作業入力に対するprefix終了の実機Witnessを導く。
  準備出口の証明は `setup_finishes` から得られる形式だが、それらをまとめた
  初期PrepPreからの単一定理、初期段生成のPrepPre自体はまだ残る。
  GSZ意味論/給送締切、段生成/回転・報告ラッチ・無条件PAL認識も未完。
  全体 `lake build PalPeg` は8874ジョブで成功。追加3モジュールに警告なし、
  主要定理の標準3公理guard通過。
- `TextFeedPipelinePrefixSetup` / `PrefixReserve` / `PrefixFedHit` /
  `PrefixFedPhysical` / `PrefixFedSetup`：初期前処理から検証器給送準備までを接続。
  `setup_prefix` は初期PrepPre・実制御・FIFOと実到着列から準備出口を導き、
  prefix締切までを単一定理にまとめる。準備費用の線形上界も保持する。
  `Reserve` は第2FIFOの全到着接頭辞と未移動Txt2を記録し、命令・到着で保存。
  `FedHit` の待機/予算/途中フレーム定理は終了地点にこの不変条件も運ぶ。
  `FedPhysical.hit_witness` はそれを実sRound/部分マイクロ入力列に移し、
  `Complete.ready` は実39テープ・両FIFOのReady・VFeedInv・pos=|u|/q=0/m=|u|と
  実制御のafterPrefix継続を返す。
  `setup_ready` は初期PrepPreから、この強化された物理Witnessまでを証明する。
  前処理中の両FIFOの内容は実入力列から計算し、終了状態を別途仮定しない。
  初期PrepPre（段テープ生成）は引き続き前提。GSZ実行意味論/給送締切、
  段生成/回転・報告ラッチ・無条件PAL認識は未完。
  全体 `lake build PalPeg` は8879ジョブで成功。追加5モジュールに警告なし、
  主要定理の標準3公理guard通過。
- GS側給送制御の修正：旧 `verifyLoop` は各反復の先頭でQ1を無条件に消費し、
  既存セルを上書きしうる一方、反復内部のtT右移動にはQ1給送がなかった。
  旧形のままGS全体の正しさを証明済みとはしない。
  `TextFeedPipelineControl.feedHead` は実tTが空白のときだけsupplyを選ぶ。
  `liftVerify` は単なるmapから構文変換へ変更し、通常actとloop必須actの
  すべてのtT右移動後にfeedHeadを挿入する。次のguardより先に新セルを給送する。
  `verifyLoop` の必須動作はidleへ変更し、body先頭にもfeedHeadを置く。
  `run_verify_start` はこの新しいidle開始とverifyBody継続に更新。
  `TextFeedPipelineFeedSource` は空白時の選択、既存セル時の給送スキップ、
  通常/loop右移動直後の継続と実有界給送 `run_feed_blank` を証明する。
  `unguarded_overwrite` は旧無条件supplyが書く値を明示する。
  `run_after_prefix` は既存Complete.readyが返す現在評価の制御同値をそのまま使い、
  実方向設定とverifyLoopへの遷移を証明する（制御の構文的リセットを要求しない）。
  1呼出し94マイクロステップ/フレーム時計は不変だが、GS側の呼出し数は増える。
  新構文変換全体のGSZ意味論、到着済み先端の保証、追加給送込みの総締切は未完。
  初期段生成/回転・報告ラッチ・無条件PAL認識も残る。
  全体 `lake build PalPeg` は8880ジョブで成功。変更した制御に依存する
  prefix/初期準備の証明も再検証済み。Pipeline系の警告なし。
  追加調査：prefix出口のTxt2は未給送の0番セルであり、現在のXR後給送だけでは
  最初の比較前のQ2供給がない。GS開始時の初回Q2給送を接続する必要が残る。
- Q2初回給送を接続：`VerifierFeedPrimitive` の静止Txt2命令XSを
  `vfillHead2` の実給送へ拡張し、既存のXR後給送と同じ閉じたFIFO処理で実装。
  `low_matches` の48動作上界は維持、Q1保存の証明も更新した。
  `verifyBody` はQ1のfeedHead、Q2のfeedHead2、GSステップの順になった。
  `TextFeedPipelineFeed2.run_feed2` は実39テープの給送後も両FIFOのReadyと
  VFeedInvを保ち、Ok2を回復する。`initial_readable` はprefix終了位置で
  n>0なら初回セルが読めることを示す。右へ動いてから初回を埋める形ではない。
  `TextFeedPipelineFeed1Model.supply_blank` / `skip_present` はQ1の実テープ空白判定が
  到着数付き仕様vfillIf1'と一致することを示す。到着数は証明用で、実制御は読まない。
  `both_feedInv` はQ1→Q2の給送順で不変条件とOk2を保持する。
  `TextFeedPipelineFeed1.run_feed1` はこのQ1の対応を実39テープの給送に適用し、
  実制御の継続・両FIFOのReady・VFeedInvを返す。
  これは給送と開始部分の接続であり、新liftVerify全体のGSZ意味論・先端の到着保証・
  総締切、初期段生成/回転・報告ラッチ・無条件PAL認識はまだ未完。
  全体 `lake build PalPeg` は8883ジョブで成功。変更後のprefix/準備証明も再検証、
  Pipeline系とVerifierFeedPrimitiveに警告なし。主要公理guard通過。
- `TextFeedPipelineFeedBody`：検証本体の現在評価による分岐を実呼び出しへ接続。
  `body_step` / `run_body` はQ1セルが空白ならQ1供給と残りのQ2継続、
  非空白ならQ1を消費せずQ2供給とGS継続を選び、実テープ・両Ready・VFeedInvを保持する。
  `run_body_ready` は現在と次の位相がworker枠である条件下で、最大2回の実呼び出しが
  `vfillHead2 (vfillIf1' M)` とGS入口の実継続へ到達し、VFeedInvとOk2を返す。
  途中で制御・キューの再初期化はしない。到着割り込みをまたぐ補給の締切、
  GS全体の意味論と総締切、初期段生成・報告・無条件PAL認識は引き続き未証明。
  全体 `lake build PalPeg` は8884ジョブで成功。Pipeline系に警告なし、
  追加2定理の公理guardは標準3公理のみで通過。
- GS内部命令の意味論：`VerifierFeedRaw` は、macroゴースト状態zではなく
  実テープのヘッド添字2つに基づく `RawInv` を導入。Q1/Q2補給と途中到着で保持し、
  補給後の空白判定が「実ヘッド＝到着先端」と同値であることを証明した。
  `VerifierFeedRawPrimitive.raw_effect` はテキストを破壊しない命令と、未供給セルから
  右へ進まない条件の下で全GS命令を扱う。XRの移動後補給、XSの静止補給、
  左端での左移動の飽和も含む。右移動条件は `safe_of_reads` で実セルの読みから導ける。
  `TextFeedPipelineRaw` はこの不変条件を実39テープのQ1給送・命令呼び出し・
  到着割り込みへ接続し、実継続と両FIFOのReadyを保持する。
  `VerifierFeedRefinement` は全文字を持つ理想GSテープへの対応を定義し、
  実状態から理想証明用テープを構成する `initial`、macro境界の既存GS符号化へ戻す
  `Refines.encodes`、給送/到着の理想側での足踏み、実命令と理想命令の一歩の対応、
  読み取り・条件の一致を証明した。理想テープは証明用であり、実機が未来入力を持つ
  という前提ではない。比較条件はパターン終端なら不要な未来セルを要求しない。
  逆向きの `Refines.feed_of_encodes` は理想GSの終了時符号化から実機のVFeedInvを回復する。
  実ヘッド添字の一致は同じテープのSeqViewから導出し、更新はゴーストzだけ。
  実テープ・両FIFO・制御継続を変更しない。
  `TextFeedPipelineRefinement` は実39テープの待機条件から比較の一致を導き、
  実給送・実命令・実到着に対する理想側の対応も返す。
  未完：新liftVerifyの任意継続を通じた全実行の対応、sourceからの全命令安全性の導出、
  全段での到着先端保証と総締切、初期段生成/回転・報告・無条件PAL認識。
  全体 `lake build PalPeg` は8889ジョブで成功。追加5ファイルとPipeline系に警告なし。
  主要定理の公理guard通過、追加ファイルにsorry/admit/独自axiomなし。
- GS命令の安全条件を実sourceから導出：`ProgLangGuarded` の有限長安全性
  `Bounded` / `Certified` は任意の観測列を許し、待機・本命令・後処理を一組として扱う。
  `guarded_then` は待機が続くとき実継続に待機を残し、解除を観測した同じsource stepで
  本命令を選ぶことを使う。危険な裸の右移動命令を無条件に安全と仮定しない。
  `TextFeedPipelineGuarded.liftVerify_certified` は新liftVerifyの全構文とループ必須動作に適用。
  `TextFeedPipelineKeep.stepProg_good` は実GSの走査・周期ずらし・任意長reset鎖・
  zigzag両方向のテキスト書き戻し条件を証明し、`task_safe` で全sourceの前提を解消した。
  `TextFeedPipelineSourceSafety` の `start_safe` / `run_safe` / `machine_round_safe` は
  初期sourceから実呼び出し・入力フレームを通じてこの安全性を保持する。
  `machine_run_safe` は本物の全空白初期配置から任意の有限入力を読んだ実機に適用される。
  `selected_safe` は実39テープの読みとRawInvから選択された命令の数値的Safe条件を導出し、
  `run_instruction` は別途Safe前提なしで前項の理想GS一命令との対応を返す。
  これは前項のsource命令安全性の未証明部分を解消した。全継続での分岐・足踏みを含む
  GS実行全体の意味論、全段到着先端保証と総締切、初期段生成/回転・報告・PAL全体は未完。
  全体 `lake build PalPeg` は8893ジョブで成功。追加4ファイルの個別検証と
  主要定理の公理guardも通過。`git diff --check` は問題なし。
- `TextFeedPipelineBranch` は比較待機解除と同じ観測での分岐選択、待機中の
  実継続保持、ループidleによる反復の確定と必須命令の残存を証明した。
  `match_dispatch` / `comp_dispatch` は実39テープのRefinesから理想GSと同じ
  分岐を任意の既存suffix付きで選ぶ。`scan_wait_blank` / `comp_wait_blank` は
  実taskEvalの整合性から待機給送対象の空白を導出する。
  これは一回の分岐とループ選択の対応であり、全継続実行の対応・進行性はまだ未完。
  全体 `lake build PalPeg` は8894ジョブで成功。追加ファイルに警告・sorry/admitなし。
- `ProgLangWait.observe` は観測が呼び出しごとに変わる実sourceの実行列を定義し、
  合成則と任意回数待機後の解除時の正確な命令列を証明した。
  `TextFeedPipelineActionWait` はこの列を両テキストの右移動命令へ適用し、
  解除後にafter-feedと元のsuffixが残ることを証明する。
  `TextFeedPipelineObservations.run_observe` は実39テープの各runから観測列を
  抽出して実source継続と一致することを証明。enqueue呼び出しは観測列に含めず、
  ソースも進めない。`run_pending_release` は実観測列が待機・解除からなるときの
  実継続を返す。外から継続を再設定せず、任意回数のenqueueを許す。
  まだこの列の解除到達・期限内進行を導出したものではない。全GS実行対応と
  到着先端・総締切、段生成/回転・報告・PAL全体の証明は継続中。
  全体 `lake build PalPeg` は8897ジョブで成功。追加3ファイルに警告・sorry/admitなし。
- `TextFeedPipelineInputObservations` は実入力取り込みを含むフレームごとの観測を
  `frameObservations` として取り出し、`FrameTrace` で実入力語との関係を固定する。
  `frame_observe` は本物のsrunの一文字追加と観測実行の一致、`word_observe` は
  全空白初期配置から任意の有限語を読んだ実継続が、抽出した観測列を初期sourceへ
  適用した結果と一致することを証明。長さ上界は `(R+1)*word.length`。
  これは入力をまたぐsource実行の対応であり、理想GS状態との全継続対応や
  待機解除の到達・締切はまだ導出していない。
  全体 `lake build PalPeg` は8898ジョブで成功。追加ファイルに警告・sorry/admitなし。
- `ProgLangControlSteps` は純制御の有限遷移を明示し、ループ選択後に必須命令が
  未実行のまま残る状態を表す。`selected_iff` / `halted_iff` は既存stepStackとの
  正確な同値、`trace_iff` は任意の観測列に対する全有限実行の命令列・継続の同値を証明。
  `TextFeedPipelineBranch.loop_commit_refines` はコンパイルされたループidleを
  理想側の純制御遷移へ対応させる。理想命令をidle時点で先行実行しない。
  `word_control_trace` でこの表現を実機の全空白初期配置からの任意有限入力へ接続。
  これは意味論表現の同値とループ確定の対応であり、全GSコンパイラのシミュレーション、
  到着先端・締切、段生成/回転・報告・PAL全体は引き続き未完。
  全体 `lake build PalPeg` は8899ジョブで成功。今回の追加・変更モジュールに警告なし。
- `TextFeedPipelineFrames` はコンパイラの全構文と残余継続をcode/pending/after/
  test/cycle/body/bodyRest/skipの型付きフレームで表し、停止する一歩評価器を定義。
  `next_render` は実stepStackの正確な残余スタック・動作ラベルと一致し、
  `observe_render` は任意の観測列での全実行へ拡張する。`next_render_suffix` は
  任意の呼び出し元継続を保存し、終了時も同じsource呼び出しで呼び出し元へ戻る。
  `next_erase` は全残余フレームで、命令なら同じ理想命令の選択、給送・idleなら
  理想側の純制御だけの遷移になることを証明。ループidle後は必須命令が未実行で残る。
  `TextFeedPipelineGuardAgreement.next_erase_physical` はその条件一致前提を
  実39テープのRefinesから解消。全条件を扱い、テキストnotMarkは未到着blankでも
  成立するため余分な到着仮定を要求しない。
  `TextFeedPipelineFrameSafety.next_feed1_blank` はどの残余フレームから選ばれた
  Q1給送でも、実観測の空白セルだけを対象にすることを証明した。
  未完：この制御対応と全イベントの実テープ更新をまとめた反復不変条件、
  到着先端・締切、段生成/回転・報告・PAL全体。
  全体 `lake build PalPeg` は8902ジョブで成功。追加3モジュール・関連変更に警告なし。
- 残余フレームの制御対応と実39テープ更新を各非終了workerイベントで統合：
  `TextFeedPipelineFrameInstruction.run_instruction` は理想命令の選択と実命令効果、
  更新後Refines、両FIFO Ready、実継続・任意caller suffix・SourceSafeを同時に返す。
  `TextFeedPipelineFrameFeeds.run_feed1/run_feed2` は給送後も理想テープを進めず、
  実継続と状態対応を保持。Q1空白条件は実frameから導出し、供給後の空白は先端i₁=nと同値。
  `TextFeedPipelineFrameControl.run_idle` は物理Q1の内部維持動作を許しながら、
  論理モデル・理想テープを保持する。`run_direction` は方向テープの実書き込みと
  理想側の方向命令選択を接続し、他のモデル状態と継続を保存する。
  未完：これらを一つの状態付き反復不変条件へまとめ、入力到着・macro終了を含めて
  閉じること。全体締切と段生成/回転・報告・PAL全体も継続中。
  全体 `lake build PalPeg` は8905ジョブで成功。追加3モジュールに警告・sorry/admitなし。
- `TextFeedPipelineCoupled` は実継続・両物理FIFO・理想テープをSnapshot/Validへ統合。
  `worker_step` は全非終了workerイベントで、実runの結果が同じValidを満たし、
  理想側の制御・テープ・方向のAdvanceを伴うことを証明する。
  `worker_prefix` は任意N回までの実反復に拡張し、実際の入力投入clockまたは
  verifier終了へ達した場合だけ途中で止まることを結論に残す。無条件に進行を仮定しない。
  `capture_valid` は本物の入力capture、`arrival_step` は通常enqueueで先端nをn+1へ
  進めつつ同じValidを保持。入力追加時は理想テープ・方向・継続を変えない。
  残るのは入力フレーム列とmacro終了の統合、既存GS終了意味論への接続、
  到着先端・総締切、段生成/回転・報告・PAL全体。
  全体 `lake build PalPeg` は8906ジョブで成功。追加Coupledモジュールに警告・sorry/admitなし。
- `TextFeedPipelineIdealEngine` はCoupledの理想状態を既存11テープGSインタプリタへ接続。
  `eval_bundle` / `bundle_action` は条件評価・命令効果の一致を証明し、
  `follows_engine` は全有限Follows列から給送・idleを除くと既存runInputsが
  正確に同じ最終テープと制御同値な継続へ到達することを証明した。
  `halted_control` / `follows_halted` は実frame終了観測を既存GSの終了へ接続する。
  `Ends.unique` は終了までの回数が違っても最終テープが同じと証明し、
  `Ends.result_of_runsTo` が既存GS RunsTo定理の終了結果を利用可能にする。
  待機・給送回数とGS命令回数が等しいという前提は入れていない。
  残るのは具体的GS段初期条件/終了符号化への適用とmacro復帰、入力フレーム列、
  到着先端・締切、段生成/回転・報告・PAL全体の接続。
  全体 `lake build PalPeg` は8907ジョブで成功。追加IdealEngineに警告・sorry/admitなし。
- `TextFeedPipelineMacroResult` は終了した具体的 `stepProg` に既存GS意味論を適用。
  `macro_return` は実フレーム終了とFollowsから、理想テープと方向がGSの
  `vprogramZ'` の結果に正確に一致すると証明する。
  `encoding_of_result` は既存の符号化・境界条件の下で次の `vStepZ` の符号化を復元。
  `feed_of_zencoding` は参照状態の注釈だけを更新して給送不変条件を復元し、
  実39テープが変わらないことも証明する。
  初期符号化・走査範囲条件の全体的な導出、入力フレーム列の統合、
  到着先端・締切、段生成/回転・報告・PAL全体は引き続き未解決。
  全体 `lake build PalPeg` は8908ジョブで成功。追加MacroResultに警告・sorry/admitなし。
- MacroResultの `initial_encoding` は給送不変条件とRefinesの実テープviewから
  2本のヘッド添字の一致を導出し、初期GS zigzag符号化とq/head/pos境界を証明。
  別途の添字整合性・理想初期符号化の仮定は不要になった。
  `compiled_encoding` はこの導出を実macro終了・GS step正当性へ統合した。
  走査後の範囲hfit・方向テープ・ZWf・入力全体のFollows構築等は依然必要であり、
  全体のPAL正当性の完成を意味しない。
  この統合後も全体 `lake build PalPeg` 8908ジョブ成功。追加部分に警告・sorry/admitなし。
- `TextFeedPipelineMacroBoundary` はマクロ終了後の範囲条件を導出。
  `step_wf` / `step_bounds` は次のzigzag整合性とq/head/pos境界を保持する。
  `annotate_valid` は数学上の状態注釈だけを更新しても同じ実構成のValidが成立すると証明。
  `compiled_boundary` は初期給送不変条件からGSマクロ終了結果を経て、
  次状態のValid・給送不変条件・ZWf・方向テープの一致を一括で返す。
  終了後のq/head/pos境界を別途仮定せず、実テープ・キュー・スタックも変更しない。
  走査範囲hfit、到着をまたぐ実行列、全体締切・段回転・報告・PAL全体は未解決。
  全体 `lake build PalPeg` は8909ジョブ成功。追加MacroBoundaryに警告・sorry/admitなし。
- `Follows` に理想テープ・方向・継続を変えないstutterを追加し、
  既存GS意味論への `follows_engine` と実行列の連結を証明し直した。
  `TextFeedPipelineInputRun.capture_enqueue` は実入力captureとenqueueを
  そのstutterへ接続する。`arrival_worker` / `frame_or_return` は1フレームを
  完了するか、実macro終了がその厳密な途中位置で起こることを証明。
  `frame_round` はそのフレームが既存機械のsRoundであると確認する。
  `frames_or_return` は任意有限個の入力へ拡張し、完了時の実構成とFollows、
  または入力prefix・入力記号・フレーム内位置つきの終了実構成を返す。
  入力を除いたworkerイベント数も正確に数える。早期終了は仮定しない。
  MacroResult/Boundaryの開始・終了到着先端を独立なn₀/nへ一般化し、
  到着をまたぐFollowsを受けられるようにした。
  残るのはこの入力列の終了とmacro復帰の具体的な統合、走査範囲hfit・
  総締切、開始方向/ZWfの適用、段生成/回転・報告・PAL全体。
  全体 `lake build PalPeg` は8910ジョブ成功。変更/追加した上記Pipeline部分に警告・sorry/admitなし。
- `TextFeedPipelineInputMacro.return_boundary` / `frames_macro` は、入力列中の
  実終了位置とmacro復帰を統合。入力prefix長から終了時の到着先端の範囲を導き、
  同じ実構成で次GS状態の給送不変条件・方向一致を復元する。
- `TextFeedPipelineMacroFit.completed_fit` により、終了した実マクロの走査範囲
  `hfit` を仮定から除去した。初期理想テープと右空白同値な長い証明用表現を構成し、
  `Exec` を同値なテープへ転送。同じ実行の最終左テープ長が等しいことと、
  実給送不変条件のヘッド位置≤到着先端≤Text長から元の有限語の範囲を導く。
  実機械・入力の変更ではなく、空白表現の観測同値性に基づく証明である。
  `compiled_encoding` / `compiled_boundary` / 入力列中のmacro復帰からhfit前提を削除。
  残るのは実開始状態の方向/ZWf・コードの適用、終了までの進行と総締切、
  段生成/回転・報告・PAL全体。終了済みマクロの正当性は、終了の保証とは区別する。
  全体 `lake build PalPeg` は8912ジョブ成功。変更/追加部分に警告・sorry/admitなし。
- `TextFeedPipelineInstructionCost` は任意の途中FollowsのGS命令数が、
  既存GS RunsToの費用以下であると証明。`follows_trace_length` は全命令が
  実traceの動作であると確認し、`trace_bound` は終了後に動作を数えない。
  `Advance` に実nextフレーム遷移と非haltを追加し、worker_stepでその証拠を保持。
- `TextFeedPipelineFrameCost` はループ確定idleを未実行の必須命令へ対応づける。
  `idle_charge` を全Followsで合計し、`worker_bound` は
  workerイベント数≤2×GS費用+1+給送イベント数を証明した。
  `amortized_worker` はこれを既存GSのΦ差分による費用上界へ接続する。
  到着stutterはこの数え上げとGS意味論を保つ。締切や終了は前提にしていない。
  残る進行上の課題は、給送成功と入力先端での待機を区別した回数上界・
  全体の到着先端/締切への接続。実開始条件、段回転・報告・PAL全体も未完。
  全体 `lake build PalPeg` は8914ジョブ成功。変更/追加部分に警告・sorry/admitなし。
- `VerifierFeedSupplyProgress` は書込み済み文字数 `m1+m2` の単調性を証明。
  空白給送先の添字が到着先端nより小さければ給送でちょうど1増え、
  増えない空白給送は添字=nと示した。FrameSafetyには実feed2対象の空白性も追加。
  `Advance.model` はworkerが実行した具体的なmodelNextを記録する。
- `TextFeedPipelineSupplyCost.worker_credit` は先端要求でない実イベントの
  給送費用を新規書込み文字数で支払う。`productive_prefix` は実反復を進め、
  予算・clock・macro終了・先端要求までの給送総数≤新規書込み総数を証明。
  `productive_window` はGS費用costがあるマクロの実反復が
  2×cost+2×n+2回未満でclock・macro終了・先端要求のいずれかへ達すると示す。
  さらにイベント数+初期書込み数≤2×cost+1+最終書込み数を保持する。
  先端要求は選択された給送の入力不足を意味し、以降の制御全部の停止は主張しない。
  総締切には、到着フレームをまたぐこの評価とGSの進み具合の統合がまだ必要。
  実開始条件、段生成/回転・報告・PAL全体も引き続き未完。
  全体 `lake build PalPeg` は8916ジョブ成功。変更/追加部分に警告・sorry/admitなし。
- `TextFeedPipelineResumeCredit.resume_budget` は任意のフレーム位相からの
  残り実行と後続の実入力を接続。元のマクロの費用証明・既実行イベント・
  給送creditを保持し、予算内の停止または入力先端要求を導く。
  外側verifyLoopへの再入、先端要求の期限、段の生成・回転・報告の
  全体接続は引き続き未証明であり、無条件PAL定理の完成ではない。
- `TextFeedPipelineReentry` は実verifyLoopの再入を接続。
  戻り時の残留フレームを消去・制御をリセットせず、外側idleと
  条件付きQ1給送・必須Q2給送が実2〜3動作で次のmacroコードへ入る。
  同じ理想テープから給送不変条件を復元し、次macroのStartを得る。
- `TextFeedPipelineReentryInput` は到着を挟む再入へ拡張。
  実enqueueは全ソースガードを保持し、再入rankはworkerで厳密減少する。
  `tick_frame` は到着をphase=0に限ったmicrostep列が既存frameそのものと示す。
  `finish` / `reenter_macro` はR>0、同じTextの次の実入力が3文字以上利用可能なら、
  任意位相の実戻り状態から最大6呼出し・入力消費最大3文字で次のStartへ到達する。
  この3文字の利用可能性は前提であり、入力末尾での無条件再入は主張しない。
  `Restored` は実returnの証拠も保持するよう強化し、`restored_reenter` が
  その終了証明から次Startへ直接接続する（新たなhalt仮定は不要）。
  総先端締切、実開始方向/ZWfの適用、段の生成・回転・報告、PAL全体は未完。
  全体 `lake build` は8920ジョブ成功。今回の変更・追加部分に警告・sorry/admitなし。
- `TextFeedPipelineInputCredit` は実入力フレーム列の給送費用を接続。
  到着capture/enqueueでm1/m2が変わらないことを明示し、`frames_credit` は
  任意個の実フレームにわたる給送総数≤新規書込み総数を保持する。
  中断位置は入力prefix・記号・フレーム内回数と実構成で示し、m=Rでの
  ちょうどフレーム末尾の終了/先端要求も次の入力を待たずに拾う。
  `frames_budget` は2cost+1+2(n+入力数)<R×入力数+初期書込み数から、
  実macro終了または先端要求がその入力列内に存在することを導く。
  `bounded_frames` はR≥3、入力数=2cost+2n+2という具体的な十分量にも特殊化。
  `macro_budget` はGS初期符号化から費用を導出し、終了なら次の給送不変条件を
  同じ実構成で復元する。終了/先端到達を前提にはしていない。
  残るのはフレーム途中からの継続・実verifyLoopのmacro再投入、先端要求と
  GS進行量からの総締切、実開始条件、段生成/回転・報告・PAL全体。
  全体 `lake build PalPeg` は8917ジョブ成功。変更/追加部分に警告・sorry/admitなし。
- `ProgLangHeadMoves` は具体的な終了Execの右移動回数から、任意長prefixの
  ヘッド位置を上界化する。左端での左移動も含む実applyTraceの証明。
  `GSVerifierHeadMoves.step_bounded` は実GSマクロのTxt1右移動≤10、
  Txt2右移動≤開始時q+10を証明した。長いカウンタ操作を距離として数えない。
  周期ずらしのp≤qは実カウンタguardと初期符号化から導出する。
- `TextFeedPipelineFrontier.macro_heads` は到着をまたぐ途中Followsにも
  両ヘッド≤開始時pos+q+10を転送する。マクロ終了・hfitは仮定しない。
  `blocked_frontier` は選択された給送が未到着文字を要求するなら
  到着先端n≤開始時pos+q+10を与える。`stopped_result` は従来の
  終了/給送要求という分岐を、次状態の復元/数値的な先端近傍へ変換する。
  `backlog_budget` は開始時pos+q+10<nと既存の実入力予算条件の下で、
  給送要求だけの代替を除き、実際のマクロreturnと次GS状態の復元を証明。
  総締切には複数マクロのΦ差分・給送・再入費用の合算がまだ必要。
  この10文字の上界だけで入力末尾の報告が正しいとは主張しない。
  実開始条件、段の生成/回転・報告・PAL全体は引き続き未完。
  全体 `lake build` は8923ジョブ成功。追加3モジュールに警告・sorry/admitなし。

### 2026-09-11: 全体条件の修正と単一Prog構成の退役

- `StageIface` の全幅に対する偶数条件は奇数幅で矛盾するため除去した。
  主仕様を実際に使う2冪幅へ限定し、半分・四分の一の等式はその場で導出する。
  `StageIfaceInstance` / `StageBirth` / `InputEmbed` の全幅の整除仮定も除去した。
- `TextFeedPipelineFrameCost.afterDebt` と `SupplyCost.Barrier` により、
  EOFでの任意の事後給送を、必須の入力待ちと区別した。
  `Frontier.macro_credit` / `reenter_credit` はGSポテンシャル差分に
  給送・実際の外側ループ再入の費用を合算する。これらはLeanで検証済み。
  入力ごとの出力締切を証明したものではない。
- 先輩の指摘を受け、最終出口が要求しない「全体を一本のProgにする」制約を撤回。
  `FullMachineProg.lean` と `StageLifecycleProg.lean`（退避時計1,243行）を
  `lean-pal/archive/single-prog/` へ移し、root importを外した。
  現役Leanコードから両モジュールへの参照がないことを確認した。
  旧計画書も同所へ移し、現行計画を短い有限制御機械の接続方針へ置き換えた。
  3ファイルは未コミット変更を含め、退避前後のSHA-256が一致する。
- `FullMachineTapes` 等の数学的仕様、`ProgLangBank` と現行pipelineは残している。
  今回は不要な旧制御層の除去であり、依存中の旧補題まで一括削除したものではない。
  実入力での照合締切・出力、中央判定と段生成/切替/再利用の全体接続は未完。
  残り工数3〜5割という先の見積もりは、冗長な構成の切り分け前の数字として撤回した。
- 退役後の全体 `lake build` は8919ジョブ成功（既存の警告は残る）。

### 2026-09-11: 入力履歴に依存しない供給評価と実テープ上の報告読取り

- `VerifierFeedSupplyProgress.readyCredit` はテキスト2ヘッドの現在の非空白セルだけを
  数え、入力長によらず高々2。一命令はこの値を高々1減らし、未到着でない空白への
  給送はちょうど1増やす。到着そのものはヘッド下のテープと残存フレームを保つ。
- `SupplyCost.barrier_prefix/window`、`InputCredit`、`ResumeCredit` をこの評価へ統一。
  EOFの任意の事後給送は `afterDebt` で支払い、真の `Barrier` と区別したまま、
  中断・入力到着・再開にまたがって費用を合算する。従来の `2cost+2n+2` 型の
  評価を、`4cost+afterDebt+4` という入力履歴長に依存しない評価へ置き換えた。
  未参照になった旧productive評価と旧増加・停止補題、計171行を除去した。
- `Frontier.macro_credit/reenter_credit` は給送と実再入6呼出し、観測用2スロットを
  GSの進行量だけで支払う。結論に累積書込み数を持ち越さない。
- `TextFeedPipelineReport.reader` は39テープの実 `StructuredMachine`。
  有限状態でQ1の先頭役割を解読し、2マイクロステップで報告ビットを読み、
  全テープを復元する。マクロ境界の符号化から `zReportFlag` との一致を証明した。
  Txt1の空白だけでは先端を意味しないため、実Q1の空も同時に検査する。
  この読取り器を全体制御へ組み込んだわけではない。
- 全体 `lake build` は8920ジョブ成功。追加・更新部分の公理監査も通過。
  実入力到着ごとの正確な締切、読取り器の正しい境界での起動と出力集約、
  中央判定・段生成/切替/再利用、無条件の `PAL ∈ PEG` はまだ未完成。

### 2026-09-11: 報告器を実pipelineへ接続

- `TextFeedPipelineOutput.machine` を実装。39テープと有限制御を保ち、
  1入力の固定マイクロステップ数は `96*(R+1)+1`。1回の入力captureと、
  既存の94ステップ呼出しに観測2ステップを付けた呼出しR+1回を実行する。
  入力の反復、証明用の入力位置・ghost状態の読取り、無限状態のoracleはない。
- `atBoundary` は有限な実継続が `[verifyBody, verifyLoop]` であることを検査する。
  そこでだけQ1の先頭をprobeし、読取り後に復元する。enqueueの先頭で答えを
  リセットし、同一入力ラウンド内の境界報告をBoolのORで保持する。
- `machine_round` は実入力1回に対する全固定長実行を証明した。
  `return_report` は既存の `Reentry.return_idle` に接続し、実マクロ復帰の次の
  source呼出しで `zReportFlag` が反映されることを示す。
  `sample_preserves/step_preserves` により観測後も元の実制御とテープへ射影できる。
- `Report.reader_queue` に復元証明を分離し、GS境界の意味論を必要とせず、
  キューのReady条件だけで観測が非破壊であることを再利用する。
  旧worker機械は既存の実行証明の核として残しており、全体を再証明し直してはいない。
- 全体 `lake build` は8921ジョブ成功。新モジュールの公理監査は
  `propext, Classical.choice, Quot.sound` のみ。`git diff --check` も通過。
  締切までの必要な復帰の存在、全実行での境界意味論の不変条件、準備・中央判定・
  段生成/切替/再利用の統合と、無条件のPAL受理同値は未完成。

### 2026-09-11: 接頭辞照合の実機同値と前処理からの初期状態

- `TextFeedPipelineOutputSound.frames_iff` は、初期化済みService状態から
  任意の非空実入力列を処理した実機の受理と、末尾のRawMatchesとの同値を証明する。
  実入力待ち・マクロ途中の割込み・復帰・物理出力観測を含む。
  初期状態、意味論的不変条件、締切等の仮定は残っており、PAL全体の同値ではない。
- `run_prefix_return` を次命令の一致を使う形へ一般化し、
  `Complete.enter` で実際の前処理完了状態から方向初期化と検証ループへの移行を接続。
- `TextFeedPipelineInitial.prefix_snapshot/prefix_service` は、この同じ実行後の
  物理テープからValidとService.Entryを構築する。未来入力を物理テープへ置く
  仮定は使わない。SourceSafe、入力長の上界、方向テープの形、起動creditは仮定。
- `Entry.initial` は残り3命令をrankとして課金し、`Entry.initial_deadline` は
  その支払いを差し引いた締切条件を証明。段生成側からこの条件を得る接続は未完。
- 依存先Service/PrefixFedPhysicalの再buildは8843ジョブ成功。
  `lake env lean PalPeg/TextFeedPipelineInitial.lean` は成功し、両接続定理の
  公理監査は `propext, Classical.choice, Quot.sound` のみ。
  この変更後のルート全体buildはまだ実行していない。

### 2026-09-11: 空の左パターンを含む実起動

- `prefix_service` の起動credit仮定を非空左パターンから導出し、
  既存のZDeadlineから初期ScanInv/ZInvも構築した。
- GS分解は切断位置0を許すため、非空の枝だけでは全体を接続できない。
  `prefix_boot` はその制約を持たず、実入力つきの既存reentry処理を走らせ、
  最大6scheduled calls・3arrivalsで最初のService.Macroへ接続する。
  初期位置・q=0・空の検証済み区間を保ち、起動中の時間は実行回数として明示する。
- `prefix_boot` のLean検証・公理監査は通過。直前の全体buildは8931ジョブ成功。
  段の実生成からSourceSafe/方向テープ条件を導くこと、startup deadline、
  中央判定と段切替を含む全体機械のPAL同値は依然未完。

### 2026-09-11: 実起動の到着上限を締切へ接続

- `Macro.initial_deadline` により、初期位置が左長・q=0の実マクロで
  `(rate+1)*n ≤ (rate+1)*left.length + rate*right.length` からServiceの締切を導出。
  左長0にも適用できる。
- `prefix_boot` の結論に、起動中の最大3arrivalsを織り込んだ
  `(rate+1)*(n+3) ≤ (rate+1)*left.length + rate*right.length` から
  実到達状態の締切条件を導く証明を接続した。Lean検証・公理監査通過。
- この数値条件を実際の段生成と準備時間から導く接続はまだ必要。
  既存 `TextFeedStartupBudget.half_credit` は利用可能だが、旧startup機械の
  実行定理を現pipelineの実行として流用してはいけない。

### 2026-09-11: 途中位相からの実出力同値

- `Deadline.trace_report` / `Observed.trace_output` に既存フレーム証明の核を移し、
  任意の実Service.Traceが締切creditへ到達した場合の報告と物理観測bitを証明。
  既存のframes_report/frames_outputはこの一般形から導出する。
- `OutputSound.trace_iff` は、初期位置・意味論不変条件と最終creditのもとで、
  入力到着を少なくとも一度含むTraceの実観測出力とRawMatchesの同値を証明。
  frames_iffもこの定理へ接続し直した。全新定理の公理監査は標準3公理のみ。
- `Initial.pending_frames` は起動後に残るN worker callsと通常フレームのTraceを
  連結する。初期creditの不足分をこのN命令で支払う場合にも適用でき、
  スキャン状態・出力・入力位相をリセットしない。Lean検証通過。
- これは起動前からの全機械の実行証明ではない。前処理中の出力観測の接続、
  段生成からの残り位相/時間条件、全体PAL同値は未完。

### 2026-09-11: 前処理キューから96-step観測の保存へ

- `Report.reader_front` にキュー読取り復元の核を移し、既存reader_queueをそこから導出。
  Snapshot全体ではなく、先頭キューの物理タグ・テープ配置・Readyだけを使う。
- `OutputPrep.reader_ready/sample_ready/step_ready` は前処理のReadyAtから
  観測後の全39テープと元制御の一致を証明する。照合器のValidは要求しない。
- `steps_ready` は実行中の各post-call ReadyAtを仮定して任意長へ拡張し、
  `microsteps_ready` は実96-step call機械のN*96マイクロステップへ接続。
  Lean検証・公理監査通過（標準3公理のみ）。
- 実入力captureを挟む前処理全体で各ReadyAtを供給する接続と、最初のキュー
  初期化前の扱いはまだ必要。全体機械のPAL同値が完成したことは意味しない。

### 2026-09-11: 観測のキュー条件を実前処理から供給

- `OutputPrep.enqueue_step` は既存run_queueから、初回の空キュー初期化を含む
  実enqueue後のReadyAtを導き、その後の観測が元制御・全テープを保存すると証明。
- `prep_step` は実前処理命令のテープ更新がFIFO領域を保つことから同じ結論を導出。
- `prep_window` はN命令の実前処理traceがproductiveであるという既存条件から
  全prefixのproductivityを導出し、各post-callのReadyAtを初期ReadyAtから構築。
  任意の中間状態のReadyAtを仮定せず、96*N microstepsの実観測機械へ接続した。
  Lean検証・公理監査通過。
- 入力captureを挟んでこれらの区間を前処理完了まで連結する証明、prefix段の観測、
  実段生成と全体PAL同値は引き続き未完。

### 2026-09-11: 実入力capture込みの観測つき前処理フレーム

- `OutputPrep.busy_observed` は実入力captureを1回行い、初回キュー初期化を含む
  enqueueとJ命令のproductive prepを観測つきで実行した結果を、既存の
  core busy_callsに一致させる。J≤Rの部分フレームにも適用できる。
- 全J命令のtrace長から各prefixのtrace長を導き、busy_callsが返すReadyAtを
  観測保存へ供給。中間キューの正しさを外から仮定しない。
- `prep_round` はJ=Rを実Output.machine.sRoundへつなぎ、実際の入力フレームの
  全制御・全39テープの射影一致を証明。Lean検証・公理監査通過。
- 複数フレームと最終部分フレームを連結してprep完了に到達する接続、
  prefix段の観測、段生成と全体PAL同値は未完。

### 2026-09-11: 観測つき前処理を任意の入力列へ連結

- `OutputPrep.prep_frames` は任意のwordについて、実Output.machine.sRoundのfoldを
  productiveな前処理source実行へ接続する。初回キュー初期化も既存の
  QueuesAtのfirst分岐として含まれる。
- 各フレーム後の実制御・prepView・AtBoundary・正確なFIFO内容・source継続・
  入力位相0を帰納的に保持し、観測器のroleと出力bitも実到達値を保持する。
  観測用クロックと入力フレームクロックは実機の遷移により0へ戻る。
- Lean検証と標準3公理のみの監査は通過。最後の部分フレームを含むprep完了との
  接続、prefix段の観測、段生成・全体PAL同値は引き続き未完。

### 2026-09-11: 観測つき実機の具体的な前処理完了

- `OutputPrepFinish.machine_partial/finishAt` は96-step callを使う出力機械の
  部分フレームを定義し、実際のframeMachine.sMicroStep列と正確に一致させる。
- `finish_at` は任意の有限prep Execを、実入力列のfull framesと最後のpartial
  frameへ分け、終了時のprepテープ・キュー内容・source継続・途中位相を証明。
- `setup_finishes` は具体的なfinitePrepSetup_execを接続し、従来の線形cost上界を
  維持してVEncodes'とprefix継続へ到達する。実入力captureと観測はすべて含む。
  新定理のLean検証・標準3公理のみの監査は通過。
- 開始時のPrepPreと物理キュー/制御条件は仮定。これらを実段生成から構築すること、
  prefix alignmentの観測つき実行・締切と、全体PAL同値は未完。

### 2026-09-11: 観測つきprefix alignmentの実行

- `OutputPrefix.link_ready` は既存の物理Linkから観測用ReadyAtを導出する。
- `worker/arrival_step` は実命令・実capture/enqueue後のLinkを維持し、
  観測後の制御と全テープが旧core実行と一致することを証明。
- `window_progress` は入力が十分に届いたproductive区間について、任意N≤fuelの
  観測つき実行のLinkとGood(fuel-N)を維持する。fuel=0の終了点を越えて
  prefixを実行する仮定は置かない。Lean検証・公理監査通過。
- 入力待ち区間のhit/継続分岐、複数フレームと起動接続、段生成からの時間条件、
  全体PAL同値は未完。

### 2026-09-11: 観測つき位置合わせの入力待ちと終了

- `OutputPrefix.window_preserve_or_hit` はu.length≤nを仮定せず、入力待ち中の
  N命令区間について、J≤Nで終了するか全区間を実行するかを証明。
  coreの各実行prefixからReadyAtを構築し、観測後のLink/Goodを保持する。
- `window_complete` は十分な入力がある最終区間で残りfuel命令を実行し、
  Q2のReserveも保って、Initial.prefix_snapshot/bootが受け取るCompleteを
  実際の観測つき到達状態に構築する。Lean検証・公理監査通過。
- 位置合わせの複数入力フレームを連結して締切内のCompleteへ到達する接続と、
  段生成・全体PAL同値は未完。

### 2026-09-11: 入力到着と位置合わせ待ちを96-step実機へ

- `OutputPrefix.arrival_window` は実capture/enqueueと待ち区間を連結し、
  次の入力境界まで進むか、その前に位置合わせが終了するかを証明する。
  Link/Goodに加えて第2キューのReserveも実入力に対応して更新・維持する。
- `frame_or_complete` はこの結果をOutput機械のsMicroStep列へ接続し、
  終了した枝では実到達状態にInitialが必要とするCompleteを構築する。
  不足した入力を仮定せず、観測と入力captureを実行に含む。Lean・公理監査通過。
- 任意の複数入力フレームの到達証明と全体の締切条件、段生成・PAL同値は未完。

### 2026-09-11: 位置合わせ継続の次入力境界

- `OutputPrepFinish.phase_full/finishAt_full` はJ=Rの部分フレームが通常sRoundと
  一致し、入力フレーム位相が0へ戻ることを証明。
- `OutputPrefix.frame_cases` は途中のComplete到達か、実sRound後の
  Link/Good/Reserveとcore入力位相・96-step位相・外側フレーム位相のすべて0を返す。
  次入力へ渡す条件を、制御のリセットなしで構築。Lean・公理監査通過。
- 複数フレームの帰納接続と締切・段生成・全体PAL同値は未完。

### 2026-09-11: 観測つき位置合わせを任意の入力列へ連結

- `OutputPrefixFrames.frames_cases` は任意の実入力列を帰納的に処理し、
  途中のfull frames＋partial frameでCompleteへ到達するか、全入力後にも
  Link/Good/Reserveと3つの位相0を保って続くかを証明する。
- 終了した入力位置と実finishAtをReachedに保存する。機械の制御・テープ・
  観測状態は実sRoundから引き継ぎ、帰納ステップでリセットしない。
- Lean検証・標準3公理のみの監査は通過。十分な到着数とwork budgetから
  継続枝を排除する締切証明、前処理からの全接続、段生成・PAL同値は未完。

### 2026-09-11: 実機のprefix締切と前処理終了点の接続

- `OutputPrefixFrames.reaches_after_wait` は入力待ち後、十分な実フレーム数
  （`5 * u.length + 2 ≤ running.length * R`）から実finishAtでのComplete到達を証明。
  productive_casesで継続時のランク減少を示し、productive_reachesで帰納接続。
- `OutputPrepFinish.setup_prefix` は具体的前処理の線形実行上界と、実際の
  観測付き終了状態に対するLink/Good/Reserveを一つの定理へ接続した。
  途中フレーム位相を保持し、時計や観測状態をリセットしない。
- 部分フレームの残り実行から締切への接続、startup credit、空テープからの
  全段生成、無条件のPAL同値は未完。これらの局所定理を最終定理とは扱わない。

### 2026-09-11: 観測付き部分フレームの実行を保持

- `OutputPrepFinish.partial_extend` は部分フレームから追加の実microstepを
  実行した結果を、観測状態を保持するstep反復と正確な外側位相へ接続。
- `OutputPrefix.resume_cases` は残りworker区間でのComplete到達、または
  Link/Good/Reserveを保持して実入力カウンタ0へ戻ることを証明。
- `Output.step_counter_iterate` と `OutputPrepFinish.partial_remaining` は
  観測を含む実行でも、J呼び出し後の残りが正確にR-Jであることを証明。
- 各追加証明のLean検証通過。前処理から締切までの統合定理、startup credit、
  空テープからの全段生成と無条件PAL同値は引き続き未完。

### 2026-09-11: 具体的前処理から実prefix締切までを統合

- `OutputPrefixFrames.reaches_from_partial` は実finishAtの途中状態から、
  そのフレーム内での早期完了か、実sRoundの終了状態を通じた締切到達を証明。
  `rounds_clocks` と `prepend` で前処理中に消費した任意の入力列も接続。
- `OutputPrefixSetup.setup_reaches` は具体的な有限前処理の線形時間上界と、
  観測付き実機上のprefix Complete到達を一つの定理へ統合した。
  実capture・観測状態・テープ・途中の時計を保持する。Lean検証・標準3公理監査通過。
- PrepPre、実入力列の対応、十分な待機後の入力数は明示的な前提のまま。
  段生成からの前提充足、観測付きstartup接続とcredit、全段機械とPAL同値は未完。

### 2026-09-11: 観測付き起動から最初の照合macroへ

- `OutputInitial.prefix_snapshot` はCompleteからの方向設定と物理照合不変条件を
  観測付きstepへ接続。`complete_arrival` は入力境界で実到着してもCompleteを保つ。
- `entry_finish` は観測付き実到着スケジュールでrank sの起動を2*s呼び出し以内、
  s到着以内に完了する。実キュー・観測状態・first=falseを引き継ぐ。
- `prefix_boot` は方向設定後の最大6呼び出し・3到着でService.Macroを構築する。
  空の左パターンを除外せず、初期creditを明示的な数値条件から導く。各Lean検証通過。
- 外側microstep位相との統合と入力境界での起動全接続、具体的な初期creditの充足、
  段生成からのPrepPre供給、全段機械と無条件PAL同値は未完。

### 2026-09-11: 起動スケジュールを元の実microstep機械へ接続

- `OutputClock.clock` は入力カウンタに対応する実外側位相を表す。
  workerは96microsteps、arrivalはcapture+96microstepsとして時計を保持して実行。
- `ticks_realize` が任意の起動スケジュールを実microstep列へ写し、
  `microInputs_consumed` が到着入力は与えた列の接頭辞そのものであることを示す。
- `finishAt_embed` は任意の前処理/prefix終了点がこの時計対応を満たすことを証明。
  `boot_microsteps` はworker位相のCompleteから最大678microsteps・3到着で
  実Service.Macroを構築し、初期creditの数値条件も保持する。Lean検証通過。
- 入力境界のCompleteからの起動統合、段生成に基づく開始条件・初期credit、
  全段の具体的機械と無条件PAL同値は未完。

### 2026-09-11: 入力境界を含む全完了位相からの起動

- `OutputClock.arrival_controls` はCompleteへの実到着がSourceSafe・first=false・
  方向テープを保持することを証明。新しい仮定で制御状態を置き換えない。
- `boot_any_phase` は途中worker位相と入力境界の両方を扱い、必要な追加到着を
  実microstep列・消費入力・起動時間へ含める。最大775microsteps・4到着で
  初期状態のService.Macroと実scoreのcreditを得る。Lean検証・標準3公理監査通過。
- creditは `(rate+1)*(n+4) ≤ (rate+1)*左長 + rate*右長` を明示的な前提とする。
  段生成からの開始条件・この数値条件・SourceSafe・方向テープ条件の導出、
  全段機械と無条件PAL同値は未完。

### 2026-09-11: 固定速度から大きな段の起動creditを導出

- `OutputBudget.workerRate` は前処理の実装定数とserviceのprogressRateだけから
  決まり、入力・段長には依存しない。既存service速度条件も満たす。
- L≥32、rate≥2、前処理開始n≤L/8なら、前処理窓とprefix作業窓を各L/8以内に
  収め、待機と最大4起動到着を含めてL/2以内と証明。実GS分解の7*cut<Lから
  起動creditの数値条件を導く。
- `setup_timed` はこの計算を具体的な観測付き前処理・prefix到達へ接続。
  必要な入力スライス長を指定すれば、prefix作業量や起動creditを別に仮定せず
  実finishAtでのCompleteとcreditを得る。Lean検証・標準3公理監査通過。
- 実段生成からのPrepPre、開始n≤L/8、SourceSafe・方向テープ、入力スライス供給、
  L<32の段処理、全段機械と無条件PAL同値は未完。

### 2026-09-11: 未来長を使わない39本の初期配置から締切へ

- `OutputBirth.seed` は到着済みw.take L・空FIFO・固定初期カウンタを39本へ配置。
  `seed_take` によりwの未到着部分を参照しない。実初期配置はpadding=0。
- 空白の長さはText.lengthを使う証明用代表にのみ足す。`future_blankEq` と
  `finishAt_blankEq` は任意の将来入力・途中microstepで全有限制御（観測bitと時計を
  含む）の一致と空白同値を保つ。実テープを未来長で初期化しない。
- `seed_timed` は空FIFO、PrepPre、n=0を構成して実前処理・prefix締切へ接続。
  到達点の不変条件は空白同値な代表上に保持し、実制御・テープとの関係を明示する。
- 全段生成からこのseedを実現する有限制御、入力スライス供給、方向テープ等の
  起動条件の接続、小段処理、全段機械と無条件PAL同値は未完。

### 2026-09-11: 空白テープからseedを作る有限生成部品

- `BirthBuild.machine` はUnit制御・有限内部命令・39本テープ・1microstepの
  具体的StructuredMachine。初期化、記号コピー、凍結の命令を実行する。
- `build_machine` は全空白テープから|w|+2命令で、padding=0のseedと完全一致する
  テープを生成すると証明。番兵と固定カウンタを同時初期化し、各記号を一度コピー。
- `builtStart_eq` は生成結果のテープを使った前処理初期状態と既存startを同定。
  内部命令機械は最終PAL機械ではなく、begin/freezeを選ぶ全段制御と実到着の
  配線、段再利用・小段処理・無条件PAL同値は引き続き未完。

### 2026-09-11: 実到着を直接読む有限生成部品

- `BirthInput.machine` は実入力を固定2microstepで読む39本のStructuredMachine。
  Boolと有限記号レジスタを使い、初回だけ番兵・カウンタを初期化する。
- `run_input` は任意長の非空実入力を一度ずつ読んだコピー状態を証明。
  `input_seed` は固定のfreeze動作1回で既存の非パディングseedと完全一致し、
  `input_start` は固定制御への引継ぎ後の既存前処理startとの一致を証明。
- freeze時点の選択、全段への配線・再利用、小段処理、無条件PAL同値は未完。

### 2026-09-11: 実前処理の到達点からSourceSafeを供給

- `OutputBirth.finishAt_safe` は固定初期制御から任意入力列・任意の有効な
  部分フレーム終了点までSourceSafeを導く。観測器付きstep、入力捕捉、両時計を含む。
- `ObservedReady` を強め、`seed_timed` の証明用代表上のComplete・startup creditに
  SourceSafeを追加した。起動時の独立した未証明前提ではなくなった。
- 方向テープ条件、全段の生成・切替・再利用、小段処理、PAL受理同値は未完。

### 2026-09-11: 方向テープの起動条件を実行から導出

- `TextFeedPipelineDirection.act_stay` は全ての低水準命令が方向ヘッドを動かさない
  ことを証明。有限bankの中断・再開、観測器、実入力捕捉でも単一セル形状を保存。
- `finishAt_dir` は任意の実入力列・有効な途中フレーム終了点で、固定のmark書込みが
  正規の方向テープを与えることを証明。準備・prefixの個別トレース仮定は不要。
- 具体的seedからこの条件を供給し、`seed_timed` のObservedReadyに組み込んだ。
  SourceSafeと方向条件は独立した未証明起動前提ではなくなった。
- 全段への実入力供給、生成・切替・再利用、小段処理、無条件PAL受理同値は未完。

### 2026-09-11: 非パディング実機の準備完了から初回照合へ

- `OutputBoot.ready_boot` はObservedReadyと実入力word++tailを受け、準備完了の
  途中フレームから最大775microstep・4到着で初期credit付きservice macroへ接続。
- 実到達点の時計同期を証明用代表へ移し、SourceSafe・方向条件・creditを消費する。
  後続入力の添字対応は全入力の対応から導出し、入力捕捉を繰り返さない。
- 実機の非パディングテープと起動後の証明用代表のConfigBlankEqを維持する。
  代表上のMacroを実テープ上の文字通りのMacroと取り違えない。
- 後続入力4個の供給、全段streamingへの接続、生成・再利用、小段とPAL同値は未完。

### 2026-09-11: 起動後の照合トレースを実microstepと受理bitへ

- `OutputTrace.realize` は任意のservice Traceを同じ実機の外側microstep列へ展開。
  workerは96step、arrivalは入力1回と96step。途中位相からの開始・トレース連結を扱う。
- `expand_inputs` は展開前後の実入力記号列が同一であることを証明。
- `output_iff` は空白同値な非パディング実機の受理bitとRawMatchesを同定する。
  正の入力進行、semantic不変条件・GS分解条件・終点creditは明示したまま。
- 初期Semantic供給、pending worker数と通常ラウンドの接続、全段制御とPAL同値は未完。

### 2026-09-11: 途中フレームから通常sRound列へ復帰

- `OutputResume.pending_run` は残りN workerの展開をN*96実microstepへ同定し、
  その後の入力スケジュールが通常sRound列と完全一致することを証明。
- `remaining_workers` は現在位相から残りworker区間中に入力到着位相がないことを導出。
  既存remaining_windowで区間終端が入力境界になることも供給する。
- `resumed_iff` は起動後creditと空白同値を受け、実機で残りフレームを完走後の
  任意の非空通常入力列における実受理bitとRawMatchesを同定。状態も出力もリセットしない。
- 初期Semantic・GS分解条件の供給、全段入力スケジュール・生成再利用、小段とPAL同値は未完。

### 2026-09-11: 初回照合の意味的不変条件を導出

- `OutputResume.initial_semantic` は起動時のpos=|u|・q=0・空の比較区間から
  ScanInv/ZInvを構成。初期残仕事量の上界は既存ZDeadlineのq=0から導出する。
- `boot_resumed_iff` は起動定理のMacroと具体的な初期値を直接受け、Semanticを
  独立した未証明前提にせず、途中フレーム復帰後の実受理bitとRawMatchesを同定。
- 具体的GS分解・条件の供給、全段入力スケジュール・生成再利用、小段とPAL同値は未完。

### 2026-09-13: 具体的GS分解から照合条件を導出

- `TextFeedPipelineParameters.decomp` は実際のprepRes（固定rate=8）から
  KSimple・右パターン非空・ZDeadlineを証明。raw period=0の分岐も正規化後の
  |v|+1を使って処理し、別の存在分解へのすり替えはない。
- `conditions` は準備時Safeの記号分離と正規化周期の正値性から、全照合条件を供給。
- 起動・復帰定理への統合適用、全段の入力・生成再利用、小段処理、PAL同値は未完。

### 2026-09-13: 具体的段パターン全体の実照合へ統合

- `Parameters.stage_resumed_iff` は具体的prepResのGS条件・準備時の記号条件・
  固定workerRate 8の速度条件を、起動後Macroからの実復帰定理へまとめて適用。
  GS条件とSemanticを呼出し側へ要求しない。
- `raw_full` で左右の照合を再結合し、実受理bitの結論を元のstagePat全体の
  末尾出現（i+|stagePat|=入力時刻）にそろえた。
- 起動到達の存在証明との統合、全段の入力・生成再利用、小段処理、PAL同値は未完。

### 2026-09-13: 一段の準備から通常照合まで一本に接続

- `TextFeedPipelineStage.prepared_running` は具体的な非パディングseedから
  準備・prefix・起動・残りフレームの完走・通常sRound照合を統合。
  Complete、Macro、GS条件、Semanticを呼出し側の前提にしない。
- 起動中の実入力prefixと最大775microstep・4到着を明示し、その後の任意の
  非空で対応する入力列について、実受理bitとstagePat全体の末尾一致を同定する。
- 範囲はL≥32、固定rate=8。必要な入力スライスの長さ・記号対応・後続4到着の
  供給は前提。全段制御による供給・生成切替再利用、小段処理とPAL同値は未完。
- これは一段の統合の完了であり、全段制御の完成ではない。

### 2026-09-13: 四段への実入力配線を実装

- `ProgramBroadcast.machine` は4つの有限制御・独立テープ束へ実入力を同時供給。
  `run_slice` は任意の初期配置から各スロットの全実行が単独機械と一致すると証明。
- `TextFeedPipelineSlots.machine` は固定速度の照合器4個を156本へ配置した実物。
  `input_local` と `output_local` で時計・継続・テープ・観測bitの局所一致を証明。
- 既存SlotScheduleの更新はSchedOpsの仮定として残っており、実スケジューラではない。
  世代交代・有効段選択・再利用・最終PAL受理は未実装。今回閉じたのは配線のみ。
  配線部品のacceptingはfalseで、PAL認識器として完成したとは主張しない。

### 2026-09-13: 世代時計の有限制御を実装

- `SlotClock.machine` は2本のテープ・Bool×Fin30の制御・固定2microstepの時計。
  端記号で走査終了を検出し、後半16相位で次世代の区間を伸ばし、世代末に役割交換。
  自然数の時刻や区間長をmicro遷移から読む実装ではない。
- `round` は実2microstepの式、`rollover` は任意長の成長テープについて世代末の
  境界書込み・制御交換・旧テープ保持を証明。世代末にコピーも巻戻しも行わない。
- `first_generation` は長さ1の初期区間から30ラウンド後に長さ16となる具体的実行を
  kernelで検証。任意世代で正しく16倍になる証明とは区別する。
- 任意世代の不変条件、空白からの初期配置、4スロットの開始時刻との対応、
  照合器への切替・再利用、PAL全体同値は未完。

### 2026-09-13: 任意長の時計走査と最終相位の完走

- `SlotClockSweep.sweep_left` / `sweep_right` は任意の区間長について、通常相位が
  区間長ちょうどの実sRoundで反対側の境界へ到達し、相位を一つ進めると証明。
- `final_sweep` は相位29の全走査を扱い、任意長の区間を完走すると役割が交換され、
  成長テープへ走査ラウンド数だけtickが追加され、最後に右境界が書かれると証明。
  成長テープ左側の任意の履歴を保持し、全履歴の消去を仮定しない。
- 通常相位の成長側1ラウンド更新と待機も検証。上記全走査の公理監査にsorryAxなし。
- 30相位を合成した16倍成長、任意世代への反復、初期化・四段との時刻対応、
  照合器のライフサイクルとPAL全体同値は依然未完。

### 2026-09-13: 全走査中の成長側の内容を同定

- `SlotClockSweep.grow_left` は成長期の任意長の左走査について、最初の書込み
  （相位14かつ境界からの出発ならedge、それ以外はtick）に続きn個のtickが
  成長側へ積まれることを実sRound列で証明。相位14の左境界生成を含む。
- `grow_right` は14より後・29より前の右走査がn+1個のtickを追加すると証明。
  `idle_left` / `idle_right` は14より前の全走査が非活動テープを一切変えないと証明。
- これで通常相位の両テープの終状態がそろった。30相位の合成と16倍成長そのものは
  まだ未証明で、初期化・全段ライフサイクル・PAL同値も未完。

### 2026-09-13: 時計の任意世代16倍成長を証明

- `SlotClockGeneration.generation` は任意のn・両テープの任意の左履歴について、
  実機の30*(n+1)ラウンドが区間長16*(n+1)の次世代配置へ到達すると証明。
  通常29相位と最後の相位を合成し、両テープの終状態と役割交換を含む等式で閉じた。
- `generations` は任意世代数の反復を実sRound列へ接続。
  `interval_growth` は区間長が16^k倍になることを証明。
  Boundaryの自然数・履歴は証明側のデータであり、有限制御へ追加していない。
- 上記の公理監査にsorryAxなし。初期配置を前提にする時計の世代境界不変条件は閉じた。
- 空白からの初期化、世代途中のSlotScheduleとの時刻対応、四段の起動・切替・再利用、
  小入力処理とPAL全体同値は未完。PAL認識器の完成とは区別する。

### 2026-09-13: 四段時計を空白から起動し、通常実行へ自動接続

- `SlotClockStartup.machine` は8本・固定2microstepの有限制御。最初の32到着で
  区間長4/8/16/2の時計テープを実書込みで作り、相位6/2/0/14から自動で走行へ移る。
  初期化後のcounterは32で固定され、各スロットで既存SlotClock.bodyを実行する。
- `startup` は全空白sInitから32到着後の全配置をkernelで検証。
  `schedule_at_32` は上記の長さ・相位・残差0・次世代長0がcanonSlot 32と一致することを検証。
- `from_blank` は初期化後の任意の入力列について、各局所配置が適切なseedと初期相位からの
  単独時計の実行に等しいと証明。初期化後の切替を外部の仮定にしていない。
- これはUnit到着で駆動される時計部品で、acceptingはfalse。世代途中の全時刻での
  SlotSchedule同値、照合器の生成・切替・再利用、小入力処理、PAL全体同値は未完。

### 2026-09-13: 世代内の任意時刻の相位と、四段の初回世代交換

- `SlotClockPosition.prefix_left` / `prefix_right` は境界前の任意の実走査prefixについて、
  相位・役割の保存とテープ頭の正確な位置を証明。相位29でも早期交換しない。
- `phase_at_time` は初期相位p、区間長qから、世代末前の任意時刻tで実制御が
  p+t/qとなることを証明。相位間の境界と相位途中を一つの式で扱う。
- `generation_from_phase` は偶数相位p≤14からでも(30-p)*qラウンドで16*qの
  次世代配置へ至ると証明。省略された相位が成長前の待機だけであることを使う。
- `first_generation_from_blank` は四段時計の実空白起動から、各段の最初の世代末の
  両テープ・制御までを接続。初期相位が0でない段の初回交換も前提から除いた。
- canonSlotとの全時刻の一致（相位だけでなく残差・次世代長を含む）、照合器の
  ライフサイクル、小入力、PAL全体同値は未完。

### 2026-09-13: 四段の実相位・常駐判定を全時刻でスケジュールへ接続

- `SlotClockTime.elapsed_closed` はk世代の実所要時間を2*(16^k-1)*初期区間長と証明。
  `time_decomposition` / `control_at_time` は任意の実時刻を世代区間に分解し、
  実制御の役割・相位・microphaseを同定する。
- `canonical_window` は指数の窓の一意性から区間長・相位・残差の算術仕様を同定。
  `phase_matches_schedule` は一般の世代境界からの任意時刻で実相位とphaseAtが一致すると証明。
- `startup_phase_matches` は空白起動した四段の全時刻32+tについて、この一致を証明。
  `startup_resident` は有限制御から読んだ常駐bitがactiveAtに一致すると証明。
  SchedOpsのactive_readを仮定して得た結果ではなく、具体的な時計の実行から導出した。
- 再起動イベントの実読出し、照合器の生成・切替・再利用、小入力とPAL全体同値は未完。
  残差・成長長の実テープ表現とcanonSlot全フィールドの一致も、相位一致とは区別して未完。

### 2026-09-13: 再起動イベントを有限制御から取り出して全時刻で検証

- `SlotClockEvents.machine` は既存の四段時計に各段2個のBoolを付加。テープ8本・
  固定2microstepは変えず、各到着の先頭で相位14を読み、立上りパルスを出す。
- `run_project` は任意入力列で時計本体への射影が元の実行と完全に一致すると証明。
  `delayed_edge` はパルスが相位14に入った次の到着で出ることを証明。
- `canonical_edge` はこのタイミングが仕様の相位14・残差1と一致すると証明。
  `pulse_matches` は全空白起動から全時刻n≥32で実パルスがrsCanonと一致すると証明。
  初期のn=32,33はkernelで検証し、n≥34は一般証明で扱った。
- 再起動イベントの読出しは仮定から除けた。ただしパルスを照合器の生成・切替・再利用へ
  接続する実ライフサイクル、小入力処理、PAL全体同値は依然未完。

### 2026-09-13: 使用済みテープの実消去から照合器の再構築へ接続

- `ProgramRecycle.machine` は全作業テープを同時に空白で掃く有限制御の部品。
  既存MiddleClearを構造化実行へ移し、範囲上界mから左m+1・右2m+1・左2m+2の
  計5m+4命令で全テープが空白相当になると証明。旧テープのスタック形は仮定しない。
- `near_steps` / `near_run` は実microstep・実入力列から使用範囲を導出。
  `reset_after_run` は空白開始の任意の機械・入力列について実消去の正しさを証明。
- `TextFeedPipelineRecycle.rebuilt_seed` は消去済み39本で内部コピー命令を実行し、
  新品seedとの空白同値を構成。`start_blankEq` と `future_output` は固定制御への
  引継ぎ後、任意の将来実入力列で新品からの出力と一致することを証明。
- 消去方向列の時間制御と解放窓への費用割当、過去の入力コピーを再構築へ供給する
  実配線は未実装。内部命令列を供給した場合の再利用部品の証明であり、全段の
  ライフサイクル完成ではない。小入力処理・PAL全体同値も未完。

### 2026-09-13: 消去を六つの等長相位にそろえた

- `ProgramRecycleWindow.uniform_clear` は使用範囲m<Nなら、左N・右2N・左3Nの
  計6N動作で任意形のテープが空スタックになると証明。相位末の余分な掃きも安全。
- `direction` / `enabled` はFin30だけで相位14〜19の消去方向・有効性を判定。
  `phase_commands` は各相位q到着・各到着C動作の方向列が上記のN=C*qと一致すると証明。
- `reset_phases` はその方向列を実消去機械へ供給すると全作業テープが空白相当になると証明。
- 時計と作業テープを同一機械へ配線してこの方向列を自動生成する部分、および使用範囲
  m<C*qの全段実行からの導出はまだ未接続。入力履歴の供給・PAL全体同値も未完。

### 2026-09-13: 実時計と156本の消去を同じ有限機械へ接続

- `ClockRecycleMachine.machine` は時計8本＋作業156本、有限の積アルファベット、
  固定C+2microstep。先頭2ステップで時計を進め、残りCステップは保存した更新前の
  相位から消去方向を決める。空白初期化中は消去を無効にする。
- `clock_from_blank` は任意入力列で元の時計・イベント機械の実行を保存。
  `pulse_matches` は合成機械の実パルスも全時刻n≥32でrsCanonに一致すると証明。
- `work_round` は各ラウンドに各作業テープが更新前相位に従うC回の実消去を受けると証明。
  時計ステップ中は作業テープを保存し、作業中は時計を保存する。方向列の外部供給は不要。
- 6相位の全消去定理とこの実ラウンド列の合成、使用範囲と固定Cの全段時間評価、
  コピー元の入力履歴供給・照合器の実起動は未完。この機械のacceptingはfalseで、
  PAL認識器ではない。小入力処理とPAL全体同値も残る。

### 2026-09-13: 実時計で駆動する六相位の消去完了を証明

- `ClockRecycleTrace.work_trace` は各実ラウンドのC回動作を実相位列へ合成。
  `phases_canonical` は各要素を空白起動後のスケジュール相位と同定する。
- `phases_six` はスロットに対応する任意指数g≥3について、時刻16*qから6*q到着の
  実相位列が14〜19各q回となると証明（q=2^(g-2)）。方向列や相位列を前提にしない。
- `reset_window` はこの時計配置を持つ任意の使用済み作業テープについて、使用範囲
  m<C*qなら実機を6*q到着進めると当該39本が空白相当になると証明。
  空白の作業テープしか扱わない例ではなく、残った内容はNear上界以外制約しない。
- 使用範囲上界と固定Cの全段時間評価、入力履歴の供給、コピー・前処理・照合の
  ライフサイクル統合は未完。小入力処理とPAL全体同値も残る。

### 2026-09-13: 二本の入力履歴を実読取りで一本へ統合

- 既存PatternTapesPairは接頭辞と差分の二本表現を持つが、copyPairToSingleは長さと
  テープ状態から外で動作列を構成していた。`HistoryConcat.machine` は3本・Fin3制御・
  固定1microstepで、実ソース頭を読み、終端の空白で切替・停止する。
- `concat` は任意の非空白記号列u,v（空列も可）を|u|+|v|+2動作でu++vの最前線へ
  統合すると証明。コピー値は実読取りで得ており、語の内容・長さを制御に渡さない。
- `concat_prefix` は既存のw.take h₀と(w.drop h₀).take(h-h₀)の形に適用し、h+2動作で
  w.take hのコピーを得る。`stable_done` は完了後の追加tickで全テープが変わらないと証明。
- ソース履歴のオンライン維持・読取り開始位置への移動、新しい到着の同時保存、
  39本のseed生成への実配線と時間評価は未完。PAL全体同値もまだ未完。

### 2026-09-13: コピーと新着保存を固定長フレームへ接続

- `HistoryArrival.machine` は履歴統合の3本に新着ログ1本を追加し、実到着1回の保存と
  固定C回のコピーをC+1 microstepsで行う。制御やコピー量に入力長を渡さない。
- `round_log` は任意のコピー制御状態で1到着につき正確に1文字をログへ追加すると証明。
  `steps_log` はコピー中のログ不変、`steps_project` はコピー側3本の動作が既存の
  HistoryConcatと一致することを証明。PALの受理フラグではなくコピー完了フラグである。
- ログの次段ソースへの切替・巻戻し、任意長実行での履歴不変条件、seedへの接続、
  固定時間上界、最終PAL同値は未完。

### 2026-09-13: 任意長の同時保存と実ヘッドの巻戻し

- `HistoryArrival.rounds` は任意の実到着列wについて、コピー側が|w|*C tick進み、
  ログにはmap enc wが正確に残ることを同時に証明。`completed` はコピー予算が
  |u|+|v|+2以上なら、旧履歴u++vと新着履歴が別テープにそろうことを保証する。
- `HistoryRewind.machine` はFin3制御・1本・固定1microstepで、空白番兵まで実読取りで
  戻り、先頭へ右移動して停止する。`rewind` は任意の非空白語wを|w|+2 tickで
  読取り開始位置へ戻す。`rewind_source` は末尾の明示空白をBlankEqで除いた既存source形。
- 重要な前提：初期履歴最前線はleft=w.reverse++[blank]。物理左端は移動がclampされる
  ため番兵が必要。HistoryArrival.completedのout/log=[blank]と整合するが、番兵の
  実初期化とコピー・巻戻し・次段切替の一体制御はまだ接続していない。
- seed供給、照合機ライフサイクル、全段の固定速度上界、小入力、最終PAL同値は未完。

### 2026-09-13: コピー完了検出から巻戻しへの自動遷移と実到着

- `HistoryReady.machine` は3本・Fin3⊕Fin3制御・固定1microstep。コピー制御の完了を
  自分で読み、1tickで巻戻しへ移る。外から語長や切替動作列を渡さない。
  `handoff` は初回完了時刻の存在と実遷移を証明し、`ready` はh=|u|+|v|について
  2h+5 tick後にu++vを先頭から読めるsource（BlankEq）へ戻す。完了後は不変。
- `Program.ArrivalLog` は任意の固定1tick workerに専用ログ1本を追加する。
  `rounds` は実到着ごとにC回のworker動作と正確に1文字の保存を同時に保証。
- `HistoryReadyInput.prepared` で両者を接続。4本・固定C+1 microsteps/到着で、
  |w|*C≥2h+5なら旧履歴は読取り可能、新着map enc wはログに全保存される。
  readinessフラグはPAL受理とは区別する。
- 依然として初期ソース2本・宛先番兵・ログ最前線の仮定がある。全空白初期化、
  新着ログの凍結・役割回転・次回ソース化、seedへの配線、matcher統合、全段の
  固定速度評価、小入力、最終PAL受理同値は未完。

### 2026-09-13: 元テープ2本の回収を既存の履歴準備へ統合

- `HistoryErase.reusable` は任意の非空白左履歴lを|l|+2 tickで消し、空白番兵の直後へ
  戻す。余分なtickで内容を変えない。残る右側の空白はBlankEqで扱う。
- `HistoryRecover.recovered` は2本の元ソース消去と統合先巻戻しを並列化し、h+2 tickで
  読取り可能な統合ソースと再利用可能な2本を同時に返す。
- 既存 `HistoryReady` の巻戻し専用後半をこの回収処理に置き換えた。有限制御は
  Fin3⊕(Fin3→Fin3)。自動コピー終了検出を保ち、全体予算2h+5は増やしていない。
  循環利用のため、両ソースの左番兵も[blank]と明示する契約へ変更した。
- `HistoryReadyInput.prepared` を新しい制御へ接続し、新着ログの完全保存に加えて
  元ソース2本の再利用可能性を保証。`prepared_padded` は入力側のsource/最前線を
  BlankEqで受け取るので、前回実行に残った空白セルを外部で正規化する必要がない。
- 次はログを凍結して巻き戻す間に回収済みテープへ新着保存を切替え、
  (旧統合先,凍結ログ,空き宛先,新ログ)の役割を実制御で回す。全空白初期化、
  実クロックからの切替、seed・matcher接続、全段速度と最終PAL同値は依然未完。

### 2026-09-13: 凍結ログの巻戻しと物理テープの役割変更

- `HistoryFreeze.frozen_padded` は旧ログvを|v|+2 worker tickで読み出し可能に戻し、
  同時に実到着wを別のログへ全保存する。古い接頭辞と空き宛先は保持する。
  全4本の開始状態をBlankEqで受け取り、回収後の右空白を許す。
- `Program.TapeRename.run_view` は論理名→物理テープの対応を任意の固定置換で変えた
  StructuredMachineについて、同じ入力・同じmicrostepsでの全実行一致を証明。
  テープ内容の移し直しや追加テープはない。
- `HistoryRotation.frozen` は前段の役割から[2,3,1,0]へ配線を変えた実入力機械に適用。
  旧統合先2を接頭辞、旧ログ3を凍結ソース、空き1をコピー先、空き0を新ログにする。
  旧ログの長さ+2≤|w|*Cなら、次のHistoryReadyInputのデータ前提がそろう。
  この置換は4回で元の対応へ戻ることも証明。
- まだ各フェーズの開始制御を定理引数で指定している。凍結完了からコピーへの
  自動遷移、実クロックでの周期切替、全空白初期化、seed/matcher接続、全体時間評価、
  最終PAL受理同値は未完。役割置換の定理だけで全体循環機械が完成したとはしない。

### 2026-09-13: 凍結→統合→回収を一つの自動処理へ接続

- `HistoryNext.machine` は凍結制御が完了した次のtickでHistoryReadyへ自動遷移する。
  コピー→回収も既存の自動遷移を使う。`ready` は旧接頭辞u・凍結ログvから
  2*(|u|+|v|)+|v|+8 tickで統合ソースと再利用可能な2本を得ることを証明。
- `HistoryReady.ready_padded` で凍結時の末尾空白を実テープのまま次処理へ渡した。
  `HistoryNextInput.prepared_padded` は全4本をBlankEqで受け取り、全区間の新着保存を
  実入力列に対して証明。固定C+1 microsteps/到着を維持する。
- `HistoryRotation.cycled` は物理役割変更を含む実入力機械で、
  Layout e u v → Layout (roles.trans e) (u++v) (map enc w) を保証。
  Layoutは空き2本・読取り可能な接頭辞・新着ログで、次回も同じ形を使える。
  各パス内の凍結・コピー・回収について外部開始指示は不要になった。
- パス間の開始と役割更新を保持する有限ループ制御、実クロックからの起動、
  全空白初期化、seed/matcher接続、全段の固定速度評価、小入力、最終PAL同値は未完。

### 2026-09-13: 起動信号付き有限ループと実クロックの世代開始信号

- `HistoryLoop.machine` は物理役割の置換を有限制御に保持する。実入力に付いたstart bitで
  役割を一度更新して同じ到着を新パスへ渡す。`run_block`/`block_layout`で、起動入力の
  脱落・重複なしに次のLayoutが得られ、その後のquiet入力で役割が変わらないと証明。
- `short_window_budget` はh≥32,v≤hなら2h+v+8≤32*floor(h/8)。
  `block_by_eighth`でworker速度32（到着あたり合計33microsteps）が履歴準備の
  8分の1長窓を満たす。matcher全体やseedコピーを含む上界ではない。
- `SlotClockBirth` は既存の実8テープ・2tickクロックに相位0立上りのフラグを追加。
  `pulse_matches`/`fires_iff_power`でn≥32の実パルスがn=2^g+1と一致すると証明。
  `startNow_power`は到着前の有限制御だけから、既読長nが2の冪かを判定する信号を得る。
- ループは現段階ではTerminal×Boolを入力に取り、クロックは別実機である。
  同じ到着でstartNowをループへ渡す12テープ等の結合・射影証明が次の接続。
  全空白からの履歴番兵初期化、最初の入力保存、全周期Layout帰納、seed/matcher接続、
  全体速度・小入力・最終PAL受理同値は未完。

### 2026-09-13: 実クロックと履歴ループを同一到着へ配線

- `ClockHistory.machine` は12テープ・固定33microsteps/到着。最初の2tickで実birthクロック、
  全33tickで履歴ループを動かす。クロックと履歴のアルファベットは有限直積で分離。
- `history_round` は同じ到着aと到着前のstartNowがHistoryLoopへ正確に1回渡ることを証明。
  `clock_round`/`clock_rounds` は1到着につきSlotClockBirthの1ラウンドと一致すると証明。
- `clock_from_blank` は結合機械の全空白実行でも実clockに一致することを保証。
  `trigger_from_blank` は既読長≥32で起動信号がちょうど2の冪の長さで真となる。
  `history_from_blank_step` はこのclock信号を使った実履歴更新の逐次等式。
- 履歴テープの全空白開始はまだLayoutの番兵条件を満たさない。最初の入力を
  保存したまま番兵を先に置く初期化を追加する必要がある。クロックの全空白射影が
  通ったことを、履歴全周期の正しさやPAL受理の証明とは混同しない。
- 全周期Layout帰納、seed供給とmatcher接続、全体速度、小入力、最終PAL同値も未完。

### 2026-09-13: 全空白からの番兵初期化と実入力32文字の基底

- `Program.WarmStart` は有限入力アルファベットの到着をOptionで有限制御に保持し、
  最初だけ初期テープ動作を行ってから同じ到着を33tickの内側機械へ渡す。
  `from_blank`は任意長の非空入力について最初の文字を含む正確な実行一致を証明。
- `ClockHistoryStartup` は履歴4本だけを空白上で1セル右へ動かし、番兵を確保する。
  時計8本は動かさない。12テープ・固定34microsteps/到着で実装し、全空白実行から
  正しいseed上のClockHistory実行と一致する。入力の捨て・複製・到着遅延はない。
- `clock_from_blank`/`trigger_from_blank` は初期化後も時計の到着数と2の冪の起動時刻が
  一致すると証明。`SlotClockBirth.startNow_early` は最初の32到着前に起動しないことを検証。
- `startup_layout`/`startup_role` は任意の長さ32の実入力wを全空白から読んだ結果として、
  初期役割・空き2本・空の旧接頭辞・map enc wの新着ログを得る。全周期帰納の基底が閉じた。
- 次は2の冪から次の2の冪までの実入力区間をHistoryLoop.block_layoutへ接続し、
  全周期Layoutと期限内の履歴供給を証明する。seed/matcher統合、全体速度、小入力、
  最終PAL受理同値は未完。ここでのseedは履歴機械の初期配置で、matcher seed供給とは別。

### 2026-09-13: 実クロック駆動の全周期履歴と期限内スナップショット

- `ClockHistoryPeriods.block_run` は2^gから2^(g+1)までの実クロックが区間最初にだけ
  起動信号を出すことを証明し、HistoryLoopの実入力ブロックへ接続した。
  `block_layout` は外部start bitなしで、8分の1長窓から次の境界までのLayout再生成を保証。
- `ClockHistoryInvariant.actual_dyadic` は任意gと任意の長さ2^(g+5)の生入力に対し、
  全空白からの実行が再利用可能なLayoutを持ち、旧接頭辞uとログvの連結が入力全体の
  エンコードに正確に一致すると証明。32文字の基底から全周期へ帰納した。
- `actual_window` はN=2^(g+5)、N+N/8≤|w|≤2Nについて、実制御が完了状態となり、
  source=map enc (w.take N)、log=map enc (w.drop N)、空き2本のLayoutを保証。
  12本・固定34microstepsの実機、全空白開始、実クロック、有限入力アルファベット、
  enc記号が空白でない条件で閉じている。仮定したソースや外部起動表は使わない。
- 履歴供給の全周期・期限の部分は閉じた。まだmatcher seedへの実コピー配線、
  読取り後の履歴ヘッド復元、四段matcherライフサイクル、結合機械全体の速度/空間、
  小入力処理、最終PAL受理同値は未完。大定理の完成とは区別する。

### 2026-09-13: 実履歴ソースから39本のmatcher seedを生成

- `TextFeedPipelineBirthSource.machine` は共有ソース1本＋matcher39本・Fin3制御・
  固定1microstep。最初に既存beginCopy、ソース頭の非空白記号ごとにcopy、
  実際の空白終端でfreezeを実行する。語や長さや内部command列は実機へ渡さない。
- `seed_from_source` は任意非空白語wを|w|+2 tickで既存OutputBirth.seedへ正確に変換。
  コピー元は終端に残り、元の文字列は左側へ保持する。完了後は不変。
- `seed_padded` は履歴のBlankEq sourceと回収済み39本のBlankEq blankを受け取る。
  `start_blankEq`/`future_output`で生成テープを既存pipeline初期制御へ渡すと、
  既存のseedから始めた全将来入力と同じ出力になると証明。
- `seed_from_history` は全空白・実クロック駆動のactual_windowからソース条件を取得し、
  生入力wのtake Nをmatcher seedへコピーする接続を証明。workspace回収条件はまだ仮定。
- この部品は共有ソースへ実読取りを行うが、全体機械への配線・起動制御は未統合。
  動いた履歴ヘッドの復元、コピー中の新着保存との同時動作、四段のworkspace回収接続、
  seed生成までを含む期限評価、matcherライフサイクル、最終PAL受理同値が残る。
  既存history単独のN/8上界に新しいコピー時間を無条件で追加してよいとはしていない。
