# 追加実行指示：lean-pal の残差を実際の証明経路から減らす

このメッセージは、進行中の `PAL ∈ PEG` 形式化に対する**追加の実行指示**です。既存の成果と作業ツリーを保持し、下記を現在のセッションで実行してください。計画の説明や「全員の結果待ち」だけで終了せず、まず実際のタスク状態と成果物を確認してください。

**目標**：固定した一つの有限制御・有限本テープの機械から、未解消の数学的前提を残さず `PegSeparation.RecognizedByTotalPEG PalPeg.PAL` を導くこと。今回はその主経路から、少なくとも一つの意味的な未解消義務を除去することを優先します。除去できなかった場合は、具体的な反例・失敗ゴール・未解消の前提を正確に残してください。達成したことにするための仮定追加は禁止です。

**基準**：公開 `main` の確認済み基点は `e8e354bb40fbfe02e389edef492d202cdaa6aeaf`（PR #52）。加えて、ユーザー提示のローカルログでは `WatchRound42` の登録・全体ビルド成功、`WatchRound43` の開始、`Preload37` の差し戻しが報告されています。ローカルの後続ファイルはこの指示の作成側では未確認です。**着手時の HEAD・差分・実タスク状態を正本にしてください。**

**環境**：対象は `lean-pal/`。`lean/` とは toolchain が異なり、ルートの `make verify` は `lean-pal/` を検証しません。現在の `lean-toolchain`、依存 pin、`CLAUDE.md` を読み、勝手に更新しないでください。[S1]

---

## 1. 最初に「証明待ち」と「実行停止」を切り分ける

- [ ] `git status --short --branch`、`git rev-parse HEAD`、`git worktree list`、`git log -8 --oneline` を確認する。ユーザーや他エージェントの未コミット変更を保持する。`reset --hard`、`clean`、共有ブランチの force-push は行わない。
- [ ] 利用可能なタスク管理・メッセージ・ログ取得機能で、各エージェントの**実状態**を取得する。古い「走行中6本」という文章だけを根拠に待たない。
- [ ] 各担当について、実タスクID、稼働／完了／エラー／入力待ち、参照している HEAD、編集対象、最終出力、生成済み差分、停止理由を確認する。rate limit・コンテキスト切れ・完了通知の取りこぼしを、証明上の難所と区別する。
- [ ] 完了済みの結果はすぐ回収する。エラーや入力待ちは、その原因を解消してから再開する。長い経過時間やログの無変化だけで稼働中タスクを一括停止しない。

提示ログでの担当は次のとおりです。現在の実状態に更新してください。

| 担当 | 回収するもの／次の到達点 |
|---|---|
| `PackRun41` | payload 残差のうち実際に閉じた枝と、その利用側への接続 |
| `PackRun42` | `Extra4` 等による `Extra3.failed` の修正と、最上位経路までの再接続 |
| `CoreEnc24` | 具体的 `chainRep` と正しい遷移前提の下での局所更新 |
| `WatchRound41` | found 時の半径予算から実着地の lag 0 を供給する証明 |
| `WatchRound43` | replay 中に生まれた chain の copy/back 区間の機械的進行 |
| `Preload37` 再作業 | `ScanRealized` に依存しない、実際の再入点での readiness |

`WatchRound42` はログ上では登録済みです。まず実ファイルと import を確認し、同じ分解を再発注しないでください。

親は結果待ちの間にも、成果の監査・利用側への接続・反例の検証・モデル修正の影響調査を進めてください。本当に待つ必要がある場合だけ、待つタスクIDと必要な成果を一度明記して環境の待機機能を使ってください。同じ待機文を繰り返すことを進捗報告にしないでください。

## 2. 進捗の判断規則を置き換える

今後は「ファイル追加・新しい `finalN`・build 成功」を、単独では証明完了への前進と数えません。次の区分で管理してください。

| 区分 | 意味 |
|---|---|
| `OPEN` | 未証明の意味的義務が残っている |
| `REFUTED` | 現在の命題に反例がある。証明対象ではなく修正対象 |
| `REFORMULATED` | 命題を適切に変更したが、その成立や利用側との接続は未完 |
| `PROVED` | 新命題自体は証明した。ただし最終経路への供給は未確認 |
| `INTEGRATED` | 既に成立している前提から供給でき、主経路で利用され、対応する旧義務が消えた |

**未解消の前提を `H_x → H_y`、構造体のフィールド、typeclass instance、別の oracle に移しただけなら `OPEN` のままです。** 分解自体は有用ですが、それと閉包を区別してください。

`lean-pal/CLOSEOUT_LEDGER.md` を単一の短い台帳として使ってください（新規パスの提案。既存の同等台帳があればそれを更新）。各義務について以下だけを記録します。

```text
義務IDと意味 / 状態
現在の宣言と全前提 / 供給元 / 利用側
親義務との関係 / 今回消えた前提 / 新たに残った前提
実ファイル・HEADまたは差分 / 検証コマンド・結果
```

再定式化や名前変更でも同じ義務IDを引き継ぎます。「一つの仮定」に巨大な問題を詰め直して数を減らさないでください。進捗率は報告せず、今回何が `INTEGRATED` になったかを報告してください。

### 証明監査で混同しないこと

`#print axioms` は宣言の推移的な公理依存を検査するものです。定理の引数として置いた命題の成立や、その前提同士の整合性を自動検証するものではありません。[S10]

したがって「標準公理のみ・build 成功」でも、不成立の前提を受け取る条件付き定理は通ります。`#check`／`#print` で**完全な型**を確認し、未解消の前提の供給元まで追ってください。正当に到達不能な局所枝で矛盾を使うことは問題ありません。問題なのは、実走行を支えるはずの入口・不変量そのものが成立しないことです。

## 3. 共有モデルの欠陥を、次の修正単位として確定する

`periodOnly` の chain 誕生時リセット漏れを、他の全作業が終わるまで無期限に延期しないでください。ただし稼働中の共有ファイルを無調整で変更してはいけません。

1. 関係する担当から現時点の差分と checkpoint を回収する。
2. 親または一人の担当だけを共有モデルの編集責任者にする。必要なら隔離された worktree で先に調査・回帰テストを行う。
3. Scala `ScaffoldChain.start()` と、Lean の `chainAt`／`chainStart`、`afterCompare`／`afterMismatch`、背景処理の chain 誕生経路を比較する。
4. 旧モデルの欠陥を再現する最小の状態・遷移を記録し、正しい開始後条件を検証する回帰テストを用意する。
5. 意味的に最小の修正を行い、直接依存する補題を直し、全体 build を一度通す。
6. 修正済みの基点を担当へ通知し、旧モデル上の成果を再検証して接続する。

**注意：boolean 一個の代入だけで修正完了としないこと。** Scala の `start()` は `periodOnly = false` に加え `cycle.reset()` も行います。Lean の `cycleAfter` は元状態 `s.periodOnly` を読みます。chain 誕生と match 処理の順序を照合し、古いフラグによる余分な減算が残らないか調べてください。[S7][S8]

reset の条件は、単に検索結果の `found` が true であることではなく、**その遷移で新しい chain が実際に誕生すること**と対応させてください。継続中の chain を毎回 reset する修正は不可です。修正する経路・しない経路と理由を明示してください。

Scala と Lean の表現が異なること自体は問題ではありません。状態の対応と遷移の意味を照合し、必要な修正を決めてください。モデル変更を必要以上の全体再設計に拡大せず、独立な補題は再利用してください。build を通すために正しい仕様を旧モデルへ戻したり、壊れた補題を公理化したりしないでください。

## 4. DP：失敗状態と窓の向きを、実際の由来に合わせて直す

### 4.1 `Extra3.failed` は利用条件まで含めて修正する

基点の `DpFieldP` は scan 全状態で `.missed` と `pc = 347` を要求します。しかし restart は DP を入口へ reset します。`dpField_to_failed` 自体も `DpFieldP` を前提にしており、実走行の全 scan 状態で DP が失敗済みと証明したわけではありません。[S2]

`PackRun42` の成果を回収し、次を満たすようにしてください。

- 検索の実行中、成功、失敗確定を stage に応じて区別する。失敗確定の場を必要な状態・利用点にだけ要求する。
- `Extra4` 等の新しい型を作るだけでなく、旧 `failed` を読んでいた各利用側が、**その地点で失敗確定を要求してよい理由**を証明する。
- 新フィールドの入口・保存・読取りを接続し、最上位の実際の経路にある旧 `H_extraEntry3`／`H_extraTick3` の義務を除く。`final21` という名前だけでは完了にしない。
- DP 結果が属する窓の開始位置・長さ・向きを保持する。shift で中心が移動したからといって、既存の DP 結果が新しい中心の窓にもそのまま属すると要求しない。必要なら結果を得た時点の由来を不変量に保持する。

### 4.2 `H_candOrient` は裸の全称形を証明しない

基点の型は以下です。[S2]

```lean
∀ (W : List (Fin 3)) (n lower h : ℕ),
  GalilDpCorrect.Candidate (W.take n) lower h →
  PalPeg.GalilDpSuffix.Candidate W lower h
```

この形には反例があります。`W = [0,0,0,0,0,1]`、`n = 5`、`lower = 0`、`h = 1` では、先頭3文字・5文字は回文ですが、末尾3文字は回文ではありません。まず現在の定義で、この反例を Lean に確認させてください。[S3][S4]

以下は**未ビルドの回帰テスト案**です。現 HEAD でコンパイルしてから採用してください。旧契約名を消してもテストが残るよう、否定する命題を直接書いています。

```lean
import PalPeg.GalilDpSuffix

namespace PalPeg.CloseoutCandOrientRegression

private def badWindow : List (Fin 3) := [0, 0, 0, 0, 0, 1]

theorem prefix_ok : GalilDpCorrect.Candidate (badWindow.take 5) 0 1 := by
  unfold GalilDpCorrect.Candidate badWindow
  decide

theorem suffix_bad : ¬ GalilDpSuffix.Candidate badWindow 0 1 := by
  unfold GalilDpSuffix.Candidate badWindow
  decide

theorem unrestricted_transport_false :
    ¬ (∀ (W : List (Fin 3)) (n lower h : ℕ),
      GalilDpCorrect.Candidate (W.take n) lower h →
      GalilDpSuffix.Candidate W lower h) := by
  intro h
  exact suffix_bad (h badWindow 5 0 1 prefix_ok)

#print axioms unrestricted_transport_false

end PalPeg.CloseoutCandOrientRegression
```

**正しい接続の候補は既にあります。** `GalilDpSuffix.lean` の `candidate_iff`、`result_of_reverse`、`window_correct` を先に使ってください。[S3]

特に `window_correct` は、DP の入力が `w.reverse.take (span+1)` であるとき、結果が `w.drop (w.length-(span+1))` という suffix 窓に属することを与えます。ただし、実際の online copy/reset がその入力を構成することまでは証明していません。

従って担当の仕事は、次の接続です。

```text
実際の copy/reset と読み取り方向
  → DP が読んだ具体的な窓 X と、論理的な窓 Y の対応
  → X = Y.reverse 等の正しい関係
  → candidate_iff / result_of_reverse / window_correct
  → 利用側が必要とする同じ窓・同じ端点の Candidate
```

全体の stream と切り出した窓を同一視しないでください。窓から全体へ suffix 性を移す場合も、端点と長さの対応を証明してください。前提に欲しい対応を書いた `H_candOrientLocal` を新設するだけでは、この義務は閉じません。

## 5. Readiness：run 上の証明を、run 上で消費する

`Preload37` の旧提出物は、提示ログでは `ScanRealized` と `ScanSupplyInv` の矛盾により差し戻されています。同じ依存を別名で再導入しないでください。否定された条件を最終経路の証拠として再利用してはいけません。

基点の `postRunC_galil_of_boot` は、`EntryDatum`、`StageChain`、供給前提、pacing などを受け取る**条件付きの段帰納**です。名前だけを見て boot からすべて無条件に供給済みと扱わないでください。また、実走行の証明から任意の `SearchVM`・任意の中心を量化した `PostRunC` を導くことはできません。[S5]

担当は次の二つを、一つの接続された成果として提出してください。

**供給元**：実際の boot／restart／replayStart 等から始まる検索状態について、stage の由来、window、debt、clock の余裕、実イベント列を保持し、`RunEntriesS` または現在の fuel 付き代替条件を導く。`StageChain` の存在、供給前提、pacing が未証明なら、それらも明示的に台帳へ残す。

**利用側**：`ReadyFieldP.hentry` または `ReadyFieldP2` の該当箇所と、`CycleOracleMC3` 側の実際の使用点へ接続する。

重要な条件：

- 将来の任意イベント列を要求するのでなく、制御が生成する列と正しい残予算を扱う。
- `32 ≤ mw` を使う帰納に入るまでの小さい初期窓を別途処理する。`mw0 = 8 * max k 1` なら `k ≤ 3` を勝手に除外しない。[S5]
- 到達可能状態への限定を採用するなら、利用側も同じ到達証拠を受け取る形へ直す。任意の `InvLPC` 状態を入力に取る古い oracle に、boot 起点の証明をそのまま渡さない。
- 到達関係の定義に目的の readiness や出力正しさを組み込んで循環させない。実際の一歩・初期状態から必要な存在と不変量を導く。

`ReadyFieldP2` を定義し保存を別契約に丸投げしただけでは `REFORMULATED` です。新しい前提を使わず実再入点に証明を渡せた箇所を `INTEGRATED` としてください。

## 6. Watch：replay 中に生まれた chain の経路を閉じる

ローカルログによれば `WatchRound42` は `LiveChainRoundC` を `ReplayBornRoundC` と `ChainWatchReachC` に分解しています。これは有用な分解ですが、**二つの前提自体が供給されるまでは、元の round 義務は未解消**です。

`WatchRound43` は、copy/back の実遷移から、必要な時計・head・入力供給の条件を保存して次の相へ到達するところを担当してください。その際、次を先に確認します。

1. copy/back から必ず watch に到達する命題で本当に正しいか。途中の入力終端・break・restart が可能なら、必要な前提または正しい出口の選言を使う。
2. 背景遷移を何回でも選べるのか。実 scheduler／clock／供給制約の下で進行を構成し、必要なら well-founded な減少量を実フィールドから与える。
3. replay 中の found 量子に結び付いた出生証拠を、watch 到達後の round へ渡せるか。
4. コストの起点がずれていないか。copy/back、watch、shift/break、必要な fallback を、利用側が要求する同じ起点からの `CostedRun` に合成する。

親または同じ担当は、到達補題を `ReplayBornRoundC` と接続し、`LiveChainRoundC` の利用点まで戻してください。既存の found 起点の補題を再利用する場合は、その前提を replay の実際の出生状態から証明してください。

`WatchRound41` の lag 0 は、found 時の半径予算を実際の出生証拠から供給して接続します。半径予算を引数に受け取る式を新設しただけで完了としないでください。

## 7. Core：存在する配置と、一つの有限機械を区別する

基点の `CloseoutCoreEnc23` には、一段の局所更新・空 queue の配置・run に沿った配置族があります。一方、具体的 `chainRep`、head margins、有限制御 `TapeActK` は未解消です。[S6]

`CoreEnc24` の結果は、次の条件で採用してください。

- 表現は必要な状態を忠実に表すこと。定数関数の `rep` で操作上界だけを満たしても、復号・模擬関係が成立しなければ不可。
- `ChainShiftBounded rep` の `∀ w c` は、元 chain と shift に使う watch 状態の関係を要求していない。具体表現でこの一般性が正しいか先に確認し、必要なら**実際の遷移における対応条件付き**へ直す。その条件は実遷移から供給する。
- `shiftPick` 一段や shift-only run の証明を、機械全体の実現と呼ばない。
- 固定した有限制御と、有限個の読み取り結果に基づいて次の操作を決める形にする。配置の役割対応を記憶する必要があれば、固定の有限タグやテープ上の表現として実装する。
- run 全体を見て事後的に選んだ配置族があるだけでは、因果的な一つの機械は得られない。証明内の `Classical.choose` 自体を一律禁止するのではなく、実装が未来や入力全体を覗かずに同じ対応を維持することを示す。
- head margins と初期配置は、各 step の外部仮定ではなく実際の初期化・保存から供給する。

`K = 28` 等の既存上界を守るために誤った前提を置かないでください。別の固定定数が必要なら、正しい一様上界を証明し、下流の遅延・コスト計算への影響も更新してください。機械を入力ごとに取り替える `∀ w, ∃ M` へゴールを弱めてはいけません。

## 8. 再発注と統合のルール

最初から別の6体を追加しないでください。現在の成果を回収した後、必要に応じて **DP/readiness、watch、core の担当に集約し、親はモデル整合・監査・統合を担当**してください。共有ファイルの編集責任者と依存順を明示します。

各担当への追加指示は次の形に統一してください。

```text
担当する意味的義務と基点HEAD／モデル差分を確認する。
既存の証明・他担当の編集を保持する。
現在の命題が偽なら、具体反例と最小の修正案を先に提出する。
正しい前提から目的を証明し、少なくとも一つの実利用点まで接続する。
新しい命題を作る場合は、その供給元と利用側を明示する。
返却物は：差分、完全な定理の型、消えた義務、残義務、検証ログ。
未解消なら実際の失敗ゴールと不足データを示し、完了とは報告しない。
```

同じ義務が名前を変えて再登場したら、さらに別名へ分解する前に、初期状態・遷移・量化範囲・供給元へ戻って監査してください。必要な中間補題の追加は禁止しません。ただし、同値な wrapper を増やして「残り一葉」と言い換えることは禁止します。

到達可能性を使う修正は、任意状態版の古い最終定理へ無理に戻さず、実走行を一貫して保持する主経路へ接続してください。最終ゴールの言語・全入力性・機械の有限性・一様性は変更しません。[S9]

## 9. 検証と終了時の報告

- [ ] 担当成果を個別にコンパイルする。利用側もコンパイルし、「その補題だけ通った」で止めない。
- [ ] 新モジュールが `lean-pal/PalPeg.lean` の import 閉包に含まれることを確認する。必要な公理監査は循環 import を作らない位置に追加する。[S1]
- [ ] `sorry`、`admit`、`native_decide`、追加 `axiom` を採用しない。文字列検索は入口の検査にとどめ、重要宣言の推移的公理依存も確認する。
- [ ] 修正済みの同じ作業ツリーで、親が `cd lean-pal && lake build --quiet PalPeg` を実行する。共有 `.lake` と共有ソースを使った全体 build を重ねない。隔離環境での個別検証と区別する。
- [ ] build コマンド・実際の終了コード・ログの場所・検証した HEAD と未コミット差分を記録する。`tee` を使うなら `pipefail` を有効にし、`tee` の成功を build の成功と誤認しない。
- [ ] 回帰テストは局所的なモデル／契約の確認と明記する。有限個の入力テストを全入力の認識証明の代わりにしない。
- [ ] 変更後の最上位定理の型を表示し、未解消の前提が引数・構造体・instance に残っていないか台帳と照合する。

**最初の統合単位は、既存成果の回収後に選んだ一つの義務の閉包、または偽契約の反例に基づく実修正と利用側の修復です。** 全部が揃うまで成果を未登録のまま溜めないでください。一方、共有モデルが変更中なら、その統合基点へ揃えてから検証してください。

終了時の報告は次の形式だけで十分です。

```text
基点と変更：
今回 INTEGRATED になった義務：
REFUTED／REFORMULATED の義務と根拠：
まだ OPEN の義務（利用側と供給元を併記）：
モデル修正・回帰検証：
全体 build／公理監査の実行結果：
継続中タスクの実状態・成果物・次の具体作業：
```

文書の整理だけでセッションを終えず、現在回収できる成果と具体的な修正・検証を先に進めてください。完遂できない場合も、何を実行し、どこまで検証できたかを残してください。ユーザーが求めているのは進捗率の上昇ではなく、正しい証明が実際に閉じることです。

---

## 根拠と適用上の注意

この追加指示は、下記のコミット固定ソースとユーザーが提示したローカルログに基づきます。作成側では Lean の再ビルドおよびローカル後続ファイルの検証は行っていません。新しいファイル名・台帳・テストコードは提案であり、現 HEAD で確認して採用してください。

`n63`／`n64` の文書見出しには `2026-09-18` とありますが、この指示の作成日は **2026-09-17（日本時間）** です。見出しの日付ではなく、コミットと実際の実行記録で順序を判定し、新しい記録には環境の実日時を使ってください。

- [S1 — CLAUDE.md：サブプロジェクト、検証コマンド、import・監査](https://github.com/kmizu/lean4-peg/blob/e8e354bb40fbfe02e389edef492d202cdaa6aeaf/CLAUDE.md)
- [S2 — CloseoutPackRun39：DpFieldP、restart の問題、H_candOrient](https://github.com/kmizu/lean4-peg/blob/e8e354bb40fbfe02e389edef492d202cdaa6aeaf/lean-pal/PalPeg/CloseoutPackRun39.lean)
- [S3 — GalilDpSuffix：candidate_iff、result_of_reverse、window_correct](https://github.com/kmizu/lean4-peg/blob/e8e354bb40fbfe02e389edef492d202cdaa6aeaf/lean-pal/PalPeg/GalilDpSuffix.lean)
- [S4 — GalilDpCorrect：prefix Candidate の定義](https://github.com/kmizu/lean4-peg/blob/e8e354bb40fbfe02e389edef492d202cdaa6aeaf/lean-pal/PalPeg/GalilDpCorrect.lean)
- [S5 — CloseoutPreload36：段帰納の前提と適用範囲](https://github.com/kmizu/lean4-peg/blob/e8e354bb40fbfe02e389edef492d202cdaa6aeaf/lean-pal/PalPeg/CloseoutPreload36.lean)
- [S6 — CloseoutCoreEnc23：chain 表現、配置族、有限制御の残差](https://github.com/kmizu/lean4-peg/blob/e8e354bb40fbfe02e389edef492d202cdaa6aeaf/lean-pal/PalPeg/CloseoutCoreEnc23.lean)
- [S7 — GalilScaffoldTopSearch：chainAt、cycleAfter、afterCompare](https://github.com/kmizu/lean4-peg/blob/e8e354bb40fbfe02e389edef492d202cdaa6aeaf/lean-pal/PalPeg/GalilScaffoldTopSearch.lean)
- [S8 — ScaffoldChain.scala：chain 開始時の reset と canShift](https://github.com/kmizu/lean4-peg/blob/e8e354bb40fbfe02e389edef492d202cdaa6aeaf/scala/pal/src/main/scala/pal/ScaffoldChain.scala)
- [S9 — CloseoutPackRun36：pal_in_peg_final20 と主経路の前提](https://github.com/kmizu/lean4-peg/blob/e8e354bb40fbfe02e389edef492d202cdaa6aeaf/lean-pal/PalPeg/CloseoutPackRun36.lean)
- [S10 — Lean 公式：公理依存の表示](https://lean-lang.org/doc/reference/latest/Axioms/)
