# lean4-peg：無条件 PAL ∈ PEG の証明を閉じるための実行計画

> 対象：`kmizu/lean4-peg` の `main`、コミット **`7ffefeabf5ad53f037b87986526483012773082c`**。2026-09-17 05:07:44 JST の PR #9 マージ時点。前回確認した `735f15b7ef3acaff693d5c97dbe5c25208b1c517` からの更新を反映する。  
> エージェント向け：この文書は証明実行の計画であり、完成済み証明ではない。新しい型・ファイル・定理名は「提案」と明記する。着手時には対象 SHA とソースの型を再確認する。Superpowers を使う環境では `subagent-driven-development` または `executing-plans` を利用できる。

**目標**：入力・機械・oracle・不変量についての未解消の仮定を残さず、固定した一つの有限制御・有限本テープの機械から `PegSeparation.RecognizedByTotalPEG PalPeg.PAL` を導く。

**推奨構成**：到達可能な fair なコスト付き抽象走行を構成し、その走行に対して修正版の入力需要上界を証明する。次に、入力到着を含む一つの有限局所機械との対応を証明し、局所走行に対する締切評価とラッチ受理を合成する。

**技術基盤**：`lean-pal/`、Lean **v4.31.0**、リポジトリで固定された Mathlib／PegSeparation。`lean/` の別 toolchain や `make verify` と混同しない。[S00][S01]

**根拠資料**：`CLAUDE.md`、`CLAUDE_RESUME.md`、`lean-pal/ASSEMBLY_PLAN.md` と、末尾のコミット固定ソース一覧。記録が食い違う場合は、新しい名前ではなく、実際の定義・引数・証明本体を優先する。

**確認範囲**：GitHub コネクタで対象 SHA の主要ファイルを読み、定義・定理の前提と接続を点検した。今回、Lean の再ビルドおよび全宣言の依存公理監査は実施していない。「全体 build 成功・標準公理のみ」はリポジトリの記録による。本計画の新規インタフェースも、まだコンパイル済みではない。[S01][S02]

---

## 1. 結論：並列化の前に、証明の出口と量化範囲を固定する

**親エージェント 1 体＋第1波の担当 5 体**を推奨する。ただし、最初から found の3経路へ全員を投入しない。

優先順位は次のとおり。

1. **最優先監査**：`RunEntriesAtBegin` の任意イベント列への量化、`H_feed_track` の任意入力文字への量化、`Fair` の存在・切り詰め保存、有限局所機械の実装契約を点検する。
2. **親が共有契約を固定**：`InvLPS` を土台に、必要な検索予算と fair な到達履歴を保持する。旧 `hpres`／旧 `StartShape` を再輸出しない。
3. **独立した証明を並列化**：検索予算、fair witness、`RadPack`、局所機械、checkpoint/report の各系列。
4. **第2波で found 3経路を並列化**：比較時 found、背景処理時 found、リプレイ中 found。全員が同じ着地型とコスト型を返す。
5. **親が一つの経路に合成**：fair な checkpoint 走行 → 修正版入力需要 → 局所追跡 → 局所締切 → ラッチ → 厳密実時間機械 → PEG。

進捗の単位は「新しいファイル数」「最終定理の引数が何個に減ったか」ではなく、**最終経路から実際に消えた未解消の前提**とする。

---

## 2. 更新によって変わった点

| 項目 | 対象 SHA で確認した到達点 | 次に必要なこと |
|---|---|---|
| 決定性 | `GalilTickFair` に `Tick ∧ Fair` の一意性を示す系列がある。検索量子側の決定性も扱っている。 | 選んだ構成 witness と実装の双方が `Fair` を満たすこと。一意性から存在は出ない。[S03] |
| 入力追従 | 旧 `Trail` の右スタック空条件は破綻するため `TrailF` に変更。`GalilTrailRad.h_trailF_of_radPack` まである。 | `RadPack` の到達走行上での保存。旧 `Trail` を証明対象へ戻さない。[S04][S05] |
| 検索の準備状態 | `SearchReady` の一般的保存 `hpres` は反証され、`ReadyFuel` を用いた `watchSegE_constructB` がある。 | 実際の段・再始動から検索予算を供給し、区間出口にも後続処理用の予算を残す。[S06][S07] |
| リプレイ | `GalilReplaySpan.replay_after_fallback_general''_fuel` は `StartShape'` と `RunEntriesAtBegin` を受け取る。 | `_fuel` という名前だけで予算処理完了としない。特に `RunEntriesAtBegin` の量化を先に点検する。[S08][S09] |
| oracle の着地型 | `InvLPS = InvLPC ∧ ReplayStage`、`FoundRouteMC3` 等の系列がある。 | `MC4` の checkpoint 分岐と、stage・予算を運ぶ型を統一する。[S10][S11] |
| 局所モード | `LocalWF.realizes_seven` の系列があり、7モードを組み立てる道筋がある。 | `Geom` 等の前提の保存、残りの init／scan／replayStart、および本当の有限局所実装。[S12] |
| ラッチと締切 | `pal_in_peg_of_local_core` と `LocalLedgerShift` がある。 | core の符号化、入力時刻付き追跡、飢餓と必要入力量の対応、report の健全性・完全性。[S13][S14][S15] |
| 最上位 | `pal_in_peg_final4` は boot 側 oracle に変えて旧 `hstr` を不要にする。 | 依然として旧 need/realize 系の引数を受け取る経路なので、修正版需要へ自動的に接続できると扱わない。[S16] |

### 2.1 文書よりソースを優先すべき具体例

`GalilReadyFuelUses` の冒頭には、リプレイ側の `hpresR` が残り、当該 theorem はその引数に関して空虚だという説明がある。一方、同じ SHA の `GalilReplaySpan` 後半には、`RunEntriesAtBegin` を使う `_fuel` 版が存在する。[S08][S09][S17]

したがって、「リプレイの再証明がまったく存在しない」でも「リプレイの準備状態は無条件で閉じた」でもない。**新版は存在するが、その新版の前提を具体的な機械から供給できるかが未解消**と整理する。

同様に `MC4` は名前が新しくても、実際には `InvLPC`／`MC2` の型を使い、旧 `hpres` と旧 `StartShape` を引数に取る。`InvLPS` の found 葉をそのまま渡せないこともファイル内で説明されている。[S11]

---

## 3. 証明経路の選択

### 3.1 推奨する主経路

```text
固定した機械の有限制御・テープ符号化
                    │
到達可能な fair な抽象走行 ── コスト付き各サイクル
                    │                  │
              RadPack / TrailF    checkpoint 時刻・費用
                    │                  │
                 needL' / needT' の上界
                    │
        入力時刻付きの局所追跡 + readiness 判定
                    │
             LocalLedgerShift の締切
                    │
           局所 core + ラッチ受理の対応
                    │
      LocalLatchRealize の到達可能版で合成
                    │
             RecognizedByTotalPEG PAL
```

これは**提案する合成順序**である。各矢印の証明がすでに全て存在するという図ではない。

`LocalLedgerShift` は `stAbs` の走行と `|w|·τ` の締切を対象とする。古いスケジュール走行 `stTG`／`stLG'` と `(|w|+1)·τ` の結果を、そのまま局所機械に適用しない。[S14]

### 3.2 最終定理名を追うだけの進め方を避ける

`final4` にそのまま全てを押し込むよりも、**修正版の `needL'`／`needT'` と入力到着付きの局所走行を主経路にする**方が接続の取り違えを減らせる。

`TrailF` が与えるのは修正版 `needL'` の上界である。旧 `H_needLB'` という名前と、修正版のプライム付き需要を同一視しない。[S04][S16]

既存の final 系は、checkpoint・初期条件・PEG への接続の部品として再利用する。最終的には新しい一つの定理に集約する。最終ファイル名の提案は `lean-pal/PalPeg/CloseoutFinal.lean`、定理名の提案は `PalPeg.CloseoutFinal.pal_in_peg_unconditional`。

---

## 4. 着手前の最優先監査

### 4.1 `RunEntriesAtBegin`：予算なしの全イベント列は正しいか

対象定義は次の形になっている。[S08]

```lean
-- 既存定義。対象 SHA の GalilReplaySpan.lean で再確認すること。
def RunEntriesAtBegin : Prop :=
  ∀ (v : SearchVM) (last radius : Counter),
    v.search = GalilScaffoldSearchFinish.begin last radius →
    ∀ as, RunEntriesAllD as v
```

**確認済みの事実**：この前提は、任意の `v`、任意の `last`／`radius`、任意のイベント列を許す。`RunEntriesAllD` 自体も各ステップの中心を全称量化する。[S08]

**監査上の推論**：これは、`ReadyFuel` が導入した「残りイベント数・比較数の予算」を外してしまっている可能性がある。`GalilSegmentConstructB` は、全リストへの準備状態を `.run` に要求する形は強すぎると説明している。また `GalilLeafPres` は、準備状態に必要な負債が `true` ごとに減ることを具体的に示す。[S06][S07]

ただし、このレビューでは **`¬ RunEntriesAtBegin` をLeanで証明したわけではない**。したがって、最初の担当には「これを証明せよ」ではなく、次を渡す。

- [ ] `begin` から `.run` に入る具体的な有限走行を構成する。
- [ ] その到達状態で `RunEntry` が要求する残余長・`true` 数・負債を展開する。
- [ ] 許される任意イベント列や任意中心が、実際の段の制約を破れるか調べる。
- [ ] 真なら、追加 oracle なしで成立する補題を提出する。
- [ ] 偽なら、具体的な有限反例または反例を導く厳密な条件を提出し、実走行に限った契約へ書き換える。

**推奨する修復方向**：`Restarted`／`StageEntry`／到達履歴を保持し、実際の制御が生成するイベント列に対して `ReadyRem` と `.run` 入口条件を運ぶ。任意の中心を選び直せる履歴ではなく、実際の walker と結びつける。単に `RunEntriesAtBegin` を別名の前提に包み直すことは完了ではない。

### 4.2 `Fair`：一意性、存在、選択した走行を分ける

既存 `Fair` は、restart 優先、fallback のコピー場所、init／replayStart の cursor 固定を表す。[S03]

必要なのは、次の三つを別々に供給すること。

```text
提案する契約（以下はLeanの完成済み宣言ではない）

fair_step_exists:
  到達可能で必要入力が揃った x から、Tick x y ∧ Fair x y を満たす y が存在する。

local_step_is_fair:
  具体的局所ステップの抽象化が、上の Tick と Fair を満たす。

constructed_trace_is_fair:
  コスト付き区間・サイクル・checkpoint の構成に実際に使った全ステップが Fair。
```

**注意**：旧 `tickFun` が choice で選んだ `Tick` witness は、それだけでは fair ではない。二つの successor の等式を一意性から得るには、両方に `Tick ∧ Fair` が必要になる。

さらに、局所機械は切り詰めた入力で動く。`tick_trunc'` だけでなく、選択したステップについての **`Fair` の切り詰め保存**、または同等の branch/pin 保存証明を用意する。

全状態での `Tick` 定義の変更は行わない。fair な refinement を上に載せ、既存の意味論・費用補題へ射影する。末尾以降に無限個の `Tick` を要求せず、まず `Tc |w|` までの有限区間を契約にする。

### 4.3 入力追跡：任意の文字で固定語のトレースを保存しない

`LocalSysConcrete` のコメントは、追跡を保つ入力到着が「正しい次の文字」に限られ、誤った文字では成立しないことを明示している。一方、汎用ラッチ定理には `inv_feed : ∀ w a x, ...` という広い契約がある。[S13][S15]

**推奨変更**：物理的不変量と、固定語に対する時刻付き追跡を分離する。

```text
提案する追跡の形
TrackAt(w, s, localState, k) :=
  j = arrL w s
  ∧ localState の抽象化 = truncS (|w| - j) (stOf k)
  ∧ k は実際の局所走行から数えた抽象ステップ数
```

到着分岐では `inp w s = some a` から、実際に供給される文字と位置を得る。この分岐についてだけ追跡保存を示す。

**二案のうち推奨はA**：

- **A：局所ラッチ定理を実走行・時刻添字の帰納へ書き換える。** 任意文字での固定語追跡を要求しない。
- **B：汎用不変量には物理条件だけを入れ、語への追跡を独立した走行定理にする。** 意味論の正しさを別の証明で十分に供給できる場合に限る。

A/Bを未決定のまま別々のエージェントに進めさせない。親が最初に選ぶ。

### 4.4 関数的な動作と有限局所実装を区別する

`LocalWF.exists_fppRun` は、目標テープを与えられたときに、その抽象像へ到達する buffer 更新の存在を構成する。`ffpp` は witness を choice で選ぶ非計算的定義である。一方、`LocalLatchRealize` は実際の `LocalStep` と core の `enc_tick`／`enc_feed` を要求する。[S12][S15]

これは矛盾や証明失敗を意味しない。ただし、次は独立した義務である。

- 固定した有限状態型 `Q`、有限アルファベット `Γ`、テープ数 `t`、局所半径 `K` が入力に依存しないこと。
- 次の動作が有限制御と有限窓だけで決まり、遠方のテープ全体や入力語を参照しないこと。
- DP／fpp の実際の命令実行が、その窓内更新と変位上界で実装されること。
- ラッチの report/output が有限制御から読めること。

「同じ抽象テープになる何らかの関数が存在する」から、有限局所実装済みとは結論しない。逆に、choice の使用だけを理由に不可能とも判定しない。**要求される符号化対応を具体的に証明する**。

---

## 5. 親エージェントが固定する共有契約

以下の名前は**提案**。新規ファイルを作る前に名前の衝突を調べる。

### 5.1 `CloseoutContracts.lean`

親が所有する。新しい巨大な意味論ではなく、既存の型を束ねる薄い接続層にする。

保持すべき内容は次のとおり。

| 契約 | 必須の情報 | 避ける形 |
|---|---|---|
| 到達する段入口 | `InvLPS`、必要な検索予算、boot／restart からの履歴 | `InvL` なら何でもよいという全状態の補強仮定 |
| 区間結果 | 実際の event list、入口／出口、正確な長さと比較数、必要な残余予算 | 入口の存在的予算を、別の任意 event list に使うこと |
| コスト付き経路 | 実際の `StepsAll`、同じ走行に対応する `CostedRun`、`Fair`、着地不変量 | Aという走行の意味論とBという走行の時間上界を混ぜること |
| checkpoint 走行 | 初期状態、`Tc`、report／refresh、費用、fair、有限区間の境界 | 古い `PreTrace` に属する全走行へ不必要に一般化すること |
| 局所追跡 | 固定語・実時刻・到着数・抽象添字・切り詰め対応 | 任意の入力文字を与えて同じ語の走行を保つこと |
| core 実装 | 一つの `LocalStep`、固定符号化、初期対応、実行対応 | 入力ごとに別の有限機械を選ぶこと |

`InvLPS` が持つ履歴は found の半径評価と準備区間構成に必要であり、`InvLPC` だけへ落としてから回復できるとは限らない。[S10]

### 5.2 強化した型を弱い oracle に無理に戻さない

`InvLPS` 上で証明した oracle から、任意の `InvLPC` 上の oracle は一般には導けない。

親は `checkpoints_cost3` 系を土台として、強化した入口型のまま checkpoint 再帰を進める。`MC4` の次の三分岐だけを移植する。[S10][S11]

1. 入口が既に report 位置：その入口に `Refreshed` があるかを確認し処理する。
2. 区間が checkpoint を横切る：実際の途中状態を切り出して report を得る。
3. 区間出口が手前：`position t.right ≤ 2*m-2` を各葉に渡す。

これにより、古い無条件 `hpos` を復活させず、found／mismatch の位置条件を局所的に供給できる。

### 5.3 並列化の開始条件

- [ ] found の3葉が返す型を同じファイルで宣言し、型チェックする。
- [ ] 検索予算の入口・出口の意味を固定する。
- [ ] `Fair` と到達履歴をどこに載せるか決める。
- [ ] 入力追跡はA案かB案の一方を採用する。
- [ ] 既存ファイルを変更できる担当を一意に決める。

**この段階で証明本体に穴を置く必要はない。** 必要なインタフェースを `structure` の field や定理引数として表現することは可能だが、それらは未解消義務として台帳に残す。

---

## 6. 推奨するエージェント配置

### 6.1 第1波：親＋5担当

| 担当 | 推奨枠 | 最初に渡す1件 | 第一便の成果 | 書き込み範囲の提案 |
|---|---|---|---|---|
| P：親／統合 | 最も強い推論枠 | 共有契約と主経路の確定 | コンパイル可能な契約、依存関係台帳 | `CloseoutContracts.lean`、最終集約、root import、監査、進捗記録 |
| A：検索予算 | 強い推論枠 | `RunEntriesAtBegin` の真偽監査 | 証明、または具体的反例／厳密な失敗条件 | `CloseoutReadinessAudit.lean` |
| B：fair 接続 | 強い推論枠 | init と replayStart の構成 witness の `Fair` | cursor固定を含む witness 証明 | `CloseoutFairWitness.lean` |
| C：入力需要 | 強い推論枠 | 到達状態の `RadPack` 保存 | tick 保存または具体的な追加不変量 | `CloseoutRadPack.lean` |
| D：局所実装 | 強い推論枠 | core の有限局所符号化の依存監査 | 既存実装への接続、または真に残る符号化義務 | `CloseoutCoreAudit.lean` と短い報告 |
| E：出口条件 | 中程度以上の枠 | checkpoint 三分岐と最終文字処理の棚卸し | `hpres`／`hquiet` を使わない report の単一ケース | `CloseoutReportCase.lean` |

AとDは最初から大きな存在定理を閉じるよう命じない。**成立しない前提や省略された実装義務を早く発見する役割**を含める。

A・Dの監査、Bの既存witness確認、Cの変更分岐の棚卸し、Eの既存report経路の棚卸しは、共有契約の確定前から並列に開始できる。新しい共通型を消費する証明本体は、親がその型を確定・型チェックしてから着手する。

モデル名ではなく仕事の性質で割り当てる。量化の修正・不変量設計・実時間上界は強い枠へ、既知補題を指定できる型の持ち回り・初期条件・算術接続は軽い枠へ回す。

### 6.2 第2波：found の3葉

共有契約と検索予算の修復方針が確定した後に開始する。第1波の担当を再利用し、常時担当数を無制限に増やさない。

| 担当 | 入力 | 出力 | 特に保つもの |
|---|---|---|---|
| F1：比較時 found | stage履歴のある区間出口、比較成功、検索が found | 比較時 found のコスト付き経路 | 比較1回の半径増加・chain開始・`Fair` |
| F2：背景処理時 found | stage履歴のある区間出口、背景検索が found | 背景時 found のコスト付き経路 | 比較していない分のclock・半径・入口状態 |
| F3：リプレイ中 found | `ReplayStageD`、修復後の準備状態契約 | active chain／break→restart を含む経路 | replay残量・再始動後予算・着地stage・report可能性 |

共通に読む既存補題：`prep_segment_construct_of_found`、`found_stage_data`、`found_radius_le_all_stages`、`foundRouteMC_shift`、`foundRouteMC_noshift_dC`。これらの必要な履歴と数値条件は、現在の定理の引数から確認する。[S01][S10]

**F2をF1のBoolean置換だけで済ませない。** 区間出口と経路の起点が異なる既存インタフェースもあるため、開始状態からの正確なステップ合成を確認する。[S11]

### 6.3 3担当しか回せない場合

親は同じまま、A＝検索予算＋F3、B＝fair＋局所実装、C＝`RadPack`＋report とする。共有契約確定後、手の空いた担当へ F1／F2 を順に渡す。

親が一番難しい設計を保持することが重要であり、台数を増やすこと自体は目的にしない。

---

## 7. 各系列の具体的な証明方針

### 7.1 検索予算：入口にあった予算を、実際のイベント列に沿って消費する

既存 `ReadyFuel v n K` は、長さが `n` 以上で `true` 数が `K` 以下のイベント列への準備状態である。`n` が大きく、`K` が小さいほど要求対象は狭まる。大小関係の向きを取り違えない。[S07]

進め方：

- [ ] 最優先監査の結果から、全イベント列版を採用できるか決める。
- [ ] 採用できない場合、`Restarted`／`StageEntry` と実際の制御列に紐づく入口予算を証明する。
- [ ] `false` でイベント予算1、`true` でイベント予算1＋比較予算1を消費する。
- [ ] 区間が早く停止した場合、実際に消費した長さ・比較数を引いた残余を出口に返す。
- [ ] report 比較には追加の1イベント・1比較が必要。既存 `reachAtC2_of_target_matchF` の `ReadyFuel ... 1 1` を、入口から十分に予約するか、出口の残余から導く。[S17]
- [ ] mid-replay の break→restart では古い残余をそのまま流用せず、新stageの初期予算を導く。

`watchSegE_constructB` は出口の `SearchReady` を返すが、主定理が続きの予算を要するなら、その出力だけでは足りない。**必要なら区間定理自体を残余付きへ書き換える**。[S07]

親が認める変更範囲は、既存の `GalilReplaySpan.lean` の予算・stage構成の節、またはその系列を置き換える新モジュール。単なる wrapper に偽の前提を残す形は認めない。import 循環を避け、重複した `RunEntriesAllD`／`RunEntriesAll` の同値または共通基礎を明示する。[S08]

### 7.2 fair：同じ実行を意味論・コスト・局所実装で共有する

- [ ] init／replayStart の既存 witness が `periodOnly`／`walker` を保つことを示す。
- [ ] scan の restart guard が真なら、通常の scan 分岐を選ばない構成にする。
- [ ] fallback のコピー位置が、検索から選ばれた walker と一致することを示す。
- [ ] 各区間の `StepsAll` に同じ長さの fair 情報を添える。
- [ ] `Fair` の切り詰め保存を示し、局所ステップと切り詰めた構成 witness の両方に適用する。
- [ ] `tick_fair_unique` で successor の等式を得る。

**費用の注意**：restart 優先に変えることが、既存の区間長・待機時間・費用計算を変えないか監査する。非fair走行の存在と費用評価だけを示して、fair実機に転用してはいけない。

### 7.3 `RadPack`：最初は保存条件の最小集合を特定する

現在の残りは、左ヘッドの生存、shift中の順序、chain開始時の半径とヘッド位置の対応、検証器の整合性に集約されている。bootと、`H_radPack` から `H_trailF` を出す消費側は既にある。[S05]

- [ ] `RadPack` の各fieldについて、どの `Tick` 分岐が変更するか表を作る。
- [ ] 変更しない分岐は projection／frame 補題で閉じる。
- [ ] 比較・shift・rewind・replayStart・chain開始の分岐に集中する。
- [ ] `GalilChainCoupling.coupled_tick` 等の既存のカウンタ対応を利用する。
- [ ] 生の `RadPack x → Tick x y → RadPack y` が強すぎる場合、先に到達状態で得られる追加packを明示し、bootと保存を共に示す。
- [ ] 任意の旧 `PreTrace` でなく、選択したfair走行で必要十分ならその範囲に定理を限定する。
- [ ] `h_trailF_of_radPack` または選択走行版へ接続し、最終的に `needL'`／`needT'` の上界を得る。

**禁止事項**：右スタック空を再び仮定すること。入力を消費しない巻き戻し・再走査と、本当に新しい文字を読む動作を区別する。[S04]

### 7.4 局所実装：意味論と物理実装の両方を閉じる

`realizes_seven` は7モードを合成する成果であり、`Geom` や局所well-formednessの保存が自動的に消えたという意味ではない。[S12]

- [ ] 固定した `Q, Γ, t, K, L0, encC` を確認または構成する。
- [ ] 既存のphaseモードを `LocalWF` の消費側へ接続する。
- [ ] `Geom` のboot、各モード、到着による保存を示す。
- [ ] init／scan／replayStart の successor を fair な抽象 successor に合わせる。
- [ ] DP／fpp を実際の命令量子として符号化し、窓局所性と変位上界を示す。
- [ ] `enc_tick`／`enc_feed` を証明する。全状態版が不要に強ければ、到達状態での対応を利用するラッチ定理へ書き換える。
- [ ] report/output の有限制御への因子化を確認する。

関数としての `Starved` は現在、複数の `canRight` をまとめて要求している。modeごとに本当に必要な読み取りと一致するか、特に init、待機、fallback後の非空右スタック、正のlagを確認する。[S13]

「安全側に多めに止まる」だけでは、締切に間に合うとは限らない。局所readinessは、次の双方を満たす必要がある。

```text
安全性：進めると判定したなら、そのtickが読む必要入力は到着済み。
進行性：必要入力が到着済みでチェックポイント前なら、余計に止まらない。
```

### 7.5 report／最終文字／mismatch：都合のよい否定仮定を追加しない

`MC4` の位置分岐を用い、最終文字やcheckpointに既に達しているケースを先に処理する。[S11]

- [ ] `EntryRefreshed` を全ての抽象的 `InvLPC` から導こうとせず、入口を構成した履歴から保持する。
- [ ] report 比較と found が同時に起きるケースを実際に分岐する。
- [ ] 最終文字で必ず not-found とする新しい仮定を追加する前に、成立性を確認する。
- [ ] mismatch のDP情報とstage予算を入口から運び、位置はcheckpoint三分岐から得る。
- [ ] 戻り値は、report到達と継続可能な着地状態・費用を区別する。

---

## 8. そのまま渡せる担当プロンプト

以下は各エージェントに単独で渡せる。共通前提を省略しない。

### A：検索予算の監査

```text
対象repoは kmizu/lean4-peg、基準SHAは
7ffefeabf5ad53f037b87986526483012773082c。対象packageは lean-pal。

今回の一件：GalilReplaySpan.RunEntriesAtBegin の成立性を監査する。
証明できると決めつけず、定義の量化範囲から点検すること。

読む場所：
- PalPeg/GalilReplaySpan.lean:3640-3715
- PalPeg/GalilSegmentConstructB.lean:1-145
- PalPeg/GalilLeafPres.lean:1-160
- 必要な GalilSearchReadyInv の RunEntry / DpSafeRem 定義

RunEntriesAtBegin は任意の SearchVM・last/radius・イベント列、
RunEntriesAllD は各stepの任意centerを含む。
beginからrunへ入る具体走行と、run入口の残余予算を照合せよ。

出力：新規 PalPeg/CloseoutReadinessAudit.lean 1本。
真なら無条件の証明、偽なら有限反例の証明を目指す。
未決着なら「確認できた命題」「追加で必要な命題」「最小再現」を区別する。
別名のoracleを仮定して対象命題を言い換えるだけでは完了としない。

既存ファイル編集・root import編集・lake buildは禁止。
単体確認は lake env lean PalPeg/CloseoutReadinessAudit.lean。
sorry/admit/native_decide/追加axiomを使わず、末尾に #print axioms。
返却時に完全な定理型、残る前提、実行コマンド、終了コードを示す。
```

### B：fair witness の最初の接続

```text
対象repoは kmizu/lean4-peg、基準SHAは
7ffefeabf5ad53f037b87986526483012773082c。対象packageは lean-pal。

今回の一件：init/replayStart の既存構成witnessが
GalilTickFair.Fair の keepsSearchCursor を含む全fieldを満たすことを示す。

読む場所：
- PalPeg/GalilTickFair.lean:1-35,185-220
- GalilScaffoldTopScanRun.init_tick
- GalilScaffoldTopReplay.replayStart_tick
- 対応する init_restarted / fallback_replayStart_All

Tickの一意性は再証明しない。Tick単体やchoiceのwitnessをfairと仮定しない。
新規 PalPeg/CloseoutFairWitness.lean 1本に、具体witnessを取り出せる形で証明する。
入力切り詰めによる各pinの変化も調べ、別の必要補題があれば型を報告する。

既存ファイル・root importを編集せず、lake buildは禁止。
lake env lean PalPeg/CloseoutFairWitness.lean で確認する。
sorry/admit/native_decide/追加axiom禁止。#print axiomsを付ける。
返却は完全な定理型、使用したwitness、残る前提、検証結果。
```

### C：`RadPack` 保存

```text
対象repoは kmizu/lean4-peg、基準SHAは
7ffefeabf5ad53f037b87986526483012773082c。対象packageは lean-pal。

今回の一件：GalilTrailRad.RadPack を、選択した到達走行で保存する
tick補題を作る。必要なら明示的な補強packを提案するが、結論そのものを
前提に追加したり、未証明のH_radPackへ包み直したりしない。

読む場所：
- PalPeg/GalilTrailRad.lean、特に RadPack / radPack_boot / h_trailF_of_radPack
- PalPeg/GalilTrailBudget.lean の scanT_tick'
- PalPeg/GalilChainCoupling.lean の coupled_tick
- PalPeg/GalilTrailProof.lean:1-125

最初に各fieldを変更するTick分岐を特定する。
FrontPackやcounter/head関係が必要なら、その入手経路も併記する。
旧Trailの「右スタック空」は使用禁止。

新規 PalPeg/CloseoutRadPack.lean 1本。既存編集・root import編集・lake buildは禁止。
lake env lean PalPeg/CloseoutRadPack.lean で確認する。
sorry/admit/native_decide/追加axiom禁止。#print axiomsを付ける。
完全な定理型、追加packのboot/保存の状態、失敗分岐を報告する。
```

### D：有限局所coreの監査

```text
対象repoは kmizu/lean4-peg、基準SHAは
7ffefeabf5ad53f037b87986526483012773082c。対象packageは lean-pal。

今回の一件：具体coreが一つの LocalStep に符号化される経路を点検し、
LocalLatchRealize.pal_in_peg_of_local_core の L0/encC/enc_tick/enc_feed に
渡せる既存証明を特定する。無ければ実際に欠けている最小契約を列挙する。

読む場所：
- PalPeg/LocalLatchRealize.lean:1-215
- PalPeg/LocalSysConcrete.lean:1-210
- PalPeg/LocalWF.lean:1-250 と realizes_seven / Geom
- LocalStepRealize、LocalBuffers、LocalTick3 の局所性関連定義

特に、exists_fppRun/ffpp の抽象的なテープ更新の存在と、固定した有限窓から
実行できる実装を区別せよ。choiceの使用自体を禁止理由にしない。
Q, Γ, t, K, 遷移関数が入力語に依存しないことも確認する。

新規 PalPeg/CloseoutCoreAudit.lean 1本に #check 等の確認と可能な接続補題を置く。
既存編集・root import編集・lake buildは禁止。
lake env lean PalPeg/CloseoutCoreAudit.lean で確認する。
sorry/admit/native_decide/追加axiom禁止。
「証明済み」「既存だが未接続」「要実装」「未確認」を分けて報告する。
```

### E：report出口の単一ケース

```text
対象repoは kmizu/lean4-peg、基準SHAは
7ffefeabf5ad53f037b87986526483012773082c。対象packageは lean-pal。

今回の一件：checkpointを横切る区間からreportを取り出す処理について、
旧hpresを要求する箇所を特定し、ReadyFuelを使う1比較の接続を示す。

読む場所：
- PalPeg/GalilOracleMC4.lean:1-240
- PalPeg/GalilReadyFuelUses.lean:1-130 と reachAtC2_of_target_matchF 本体
- PalPeg/GalilInvPlus3.lean:1-135

入力は親が固定するstage付き着地型に従う。
必要な ReadyFuel ... 1 1 は、入口や出口の予算から導けるかを区別する。
最終文字ではfoundしない、という否定仮定を勝手に足さない。

新規 PalPeg/CloseoutReportCase.lean 1本。既存編集・root import編集・lake buildは禁止。
lake env lean PalPeg/CloseoutReportCase.lean で確認する。
sorry/admit/native_decide/追加axiom禁止。#print axiomsを付ける。
返却は単一ケースの定理、必要な残余予算、未処理の同時foundケース。
```

### 親エージェントへの指示

```text
目標は、無条件 RecognizedByTotalPEG PAL の閉じた証明。
基準SHAは 7ffefeabf5ad53f037b87986526483012773082c。

第1波A-Eの結果が出るまで、found 3葉を異なる型で並列実装させない。
まず RunEntriesAtBegin、任意文字の H_feed_track、Fair witness、
coreの有限局所符号化を監査する。

主経路は、到達するstage付きfair走行、修正版 needL'/needT'、
時刻付き局所追跡、LocalLedgerShift、局所ラッチを合成する系列。
古いMC4のhpres/StartShape、旧H_needLB'を名前だけで接続しない。
InvLPSをInvLPCへ落とした後にstage履歴を無条件回復しようとしない。

親が所有するもの：共有契約、既存モデルへの限定的変更の承認、root import、
全体build、最終定理、公理監査、依存関係台帳、CLAUDE/RESUME/ASSEMBLY記録。

各waveで共有契約を固定し、部品の意味論・費用・Fairが同じ走行を表すか確認する。
エージェントの「完了」は、完全な定理型・証明・到達可能性・残前提を見て判定する。
偽前提や循環依存が見つかったら、関連作業だけを止めて契約を修正する。
最後は machine/oracle/入力語を引数に取らない閉じた定理で確認する。
```

---

## 9. 並列作業の実務ルール

### 9.1 ソースとビルド成果物の衝突を避ける

- 1回の依頼は、主定理1件・新規ファイル1本を原則とする。
- 既存の `GalilReplaySpan.lean` 等の修正が必要な場合は、親が編集者を1人に指定する。既存ファイルの編集禁止を理由に、偽前提を温存しない。
- root `PalPeg.lean`、最終定理、監査、進捗記録は親だけが変更する。
- 各waveの依存モジュールを親が先にビルドする。その間は統合対象のソースを凍結する。
- サブエージェントは `lake env lean 対象ファイル` の単体確認のみ。未ビルド依存が必要なら親へ返す。
- `.olean` を生成する場合は各worktreeまたは各worker専用出力先を使う。同一モジュールの成果物を複数workerが上書きしない。

別worktreeを使う場合も、大きい `.lake` を雑に共有して同時書き込みさせない。共有作業ディレクトリ方式なら、新規ファイルの所有権と「全体buildは親だけ」を厳守する。

### 9.2 依頼に必ず含める情報

```text
基準SHA：
主定理：
既存の入力型：
返す出力型：
読むファイル・行範囲：
使用候補の補題：
使用禁止の旧前提：
編集可能ファイル：
検証コマンド：
完了条件：
```

巨大な `CLAUDE_RESUME.md` 全体を各エージェントに読ませるより、この情報と該当ソースを渡す。親だけが全体の版の対応を管理する。

### 9.3 提出テンプレート

```text
Status: PROVED / CONDITIONAL / COUNTEREXAMPLE / BLOCKED
Base SHA:
Changed file:
Main theorem (fully qualified):
Full type:
Remaining assumptions:
Reachability / initialization source:
Consumers in final proof:
Verification command:
Exit code:
Axioms output:
Interface changes requested:
```

`PROVED` はその定理の型に対しての証明完了を意味する。最終PALへの接続済みかどうかは `Consumers` で別に評価する。

---

## 10. 検証手順と完了判定

### 10.1 着手時の確認

```bash
# リポジトリのルートで実行する。ユーザーの未コミット変更を消さない。
git status --short
git rev-parse HEAD
git diff --stat 735f15b7ef3acaff693d5c97dbe5c25208b1c517 \
  7ffefeabf5ad53f037b87986526483012773082c -- lean-pal CLAUDE.md CLAUDE_RESUME.md
cat lean-pal/lean-toolchain
```

対象SHAから進んでいる場合、親が差分を確認して計画を更新する。自動でcheckout/resetして現在の作業を戻さない。

### 10.2 サブエージェントの単体検証例

以下は `CloseoutRadPack.lean` を作った後に実行する例。他担当は自分のファイル名へ変更する。

```bash
cd lean-pal
if [ -f "$HOME/.elan/env" ]; then . "$HOME/.elan/env"; fi
command -v lake
lake env lean PalPeg/CloseoutRadPack.lean
```

必要なimportの `.olean` が無ければ、その証明が誤りだとは判断せず、親による依存ビルドを依頼する。実行していないコマンドを「成功」と報告しない。

### 10.3 親の統合検証

```bash
# リポジトリルートから。親だけが実行する。
set -o pipefail
mkdir -p /tmp/lean-pal-closeout
(
  cd lean-pal
  if [ -f "$HOME/.elan/env" ]; then . "$HOME/.elan/env"; fi
  lake build PalPeg
) 2>&1 | tee /tmp/lean-pal-closeout/build.log
```

rootへ新規モジュールを登録してから実行する。登録漏れのファイルがある状態で `lake build PalPeg` が成功しても、そのファイルを検証したことにはならない。[S01]

### 10.4 旧前提の残留監査

```bash
# これは候補箇所を拾う静的検索。コメント・歴史的反例にも一致するので、
# 一致0件だけを狙わず、最終定理が使う経路に残っているかを確認する。
rg -n 'hpresR|hpres|StartShape|RunEntriesAtBegin|H_feed_track|H_needLB' \
  lean-pal/PalPeg/Closeout*.lean

rg -n '\b(sorry|admit|native_decide|axiom|unsafe)\b' \
  lean-pal/PalPeg/Closeout*.lean
```

これは間接依存・マクロ展開・import先まで保証する監査ではない。最終定理の完全な型と `#print axioms` を併用する。

### 10.5 完成した定理に対する型チェック

次の名前は本計画で提案したもの。実装完了後、親が実際の名前に合わせて監査ファイルを作る。

```lean
import PalPeg.CloseoutFinal

set_option autoImplicit false

-- この型の項を、追加のmachine/oracle引数なしで作れることを確認する。
example : PegSeparation.RecognizedByTotalPEG PalPeg.PAL :=
  PalPeg.CloseoutFinal.pal_in_peg_unconditional

#print PalPeg.CloseoutFinal.pal_in_peg_unconditional
#print axioms PalPeg.CloseoutFinal.pal_in_peg_unconditional
```

`#print axioms` の出力に `sorryAx` や追加の公理がないことを確認する。許容される標準公理はリポジトリ方針に合わせる。表示順や使用公理の個数は実出力を見て監査を固定する。

**重要**：公理が標準だけでも、定理の引数に未解消の仮定が残ることはある。上の閉じた型の `example` と完全な定理表示を省略しない。

### 10.6 定義の意味を変えていないことも確認する

- [ ] `PAL`、PEGの受理・全域性、厳密実時間機械の意味を弱めていない。
- [ ] 空語、1文字、偶数長、奇数長の扱いが同じ仕様に対応する。
- [ ] 1つの機械・固定有限定数が全入力を扱い、入力長ごとの別機械になっていない。
- [ ] 到着後に余分な最終処理枠を暗黙に要求していない。
- [ ] 既存の反例 `aaaaabaaaab` や非空右スタックのケースを、前提で不当に排除していない。
- [ ] fair化による費用の変化と、同時found/reportの扱いを点検した。

有限例の実行は境界バグの発見用であり、全入力の形式証明の代わりではない。

---

## 11. マイルストーンと停止条件

| 段階 | 通過条件 | 通過したと見なしてはいけないもの |
|---|---|---|
| M0 契約 | 量化範囲・入力到着・fair・有限局所性の監査を反映した型が固定 | 引数名を置き換えただけの最終定理 |
| M1 抽象実行 | コスト付きfair走行が構成され、found/replay/報告の全出口が同じ着地契約を返す | 関係的な `Tick` が存在するだけ |
| M2 入力需要 | 選択走行に対する `RadPack`／`TrailF` と修正版需要上界 | 旧 `Trail` や旧 `needL` の条件付きwrapper |
| M3 具体実行 | 有限局所core、到着時刻付き追跡、readinessの安全性と進行性 | 7モードの合成だけ、または抽象buffer更新の存在だけ |
| M4 時間・受理 | 同じ局所走行の締切とラッチ受理を接続 | 別の走行の台帳、1枠余分な締切 |
| M5 最終監査 | 閉じた `RecognizedByTotalPEG PAL`、再ビルド、公理・型・仕様の監査 | `sorry` が無いことだけ |

**局所停止条件**：偽前提、同時に満たせないpack、必要な未来文字へのアクセス、非局所的な実装、循環的なlemma依存が見つかったら、その担当は追加wrapperを作らず、最小再現と修正候補を親へ返す。他の独立系列は続行してよい。

**最初の一手**：親が A〜E の第一便だけを配り、自分は共有契約の差分を確定する。Aの監査結果とDの符号化監査を見てから、第2波のfound 3葉を発行する。この順序が、現在のコードで最も避けたい「偽または強すぎる前提に大量の並列作業を積む」ことを防ぐ。

---

## 12. ソース索引（すべて対象 SHA に固定）

行番号はこのSHAにおける位置。実行エージェントは作業版で定理名から再確認すること。

- **[S00]** [コミットとPR #9](https://github.com/kmizu/lean4-peg/commit/7ffefeabf5ad53f037b87986526483012773082c) ／ [lean-toolchain](https://github.com/kmizu/lean4-peg/blob/7ffefeabf5ad53f037b87986526483012773082c/lean-pal/lean-toolchain)
- **[S01]** [CLAUDE.md：現状、葉、担当規約](https://github.com/kmizu/lean4-peg/blob/7ffefeabf5ad53f037b87986526483012773082c/CLAUDE.md#L88-L175)
- **[S02]** [CLAUDE_RESUME.md：n21とn20の記録](https://github.com/kmizu/lean4-peg/blob/7ffefeabf5ad53f037b87986526483012773082c/CLAUDE_RESUME.md#L1-L10)
- **[S03]** [GalilTickFair.lean：定義と一意性](https://github.com/kmizu/lean4-peg/blob/7ffefeabf5ad53f037b87986526483012773082c/lean-pal/PalPeg/GalilTickFair.lean)
- **[S04]** [GalilTrailProof.lean：Trailの反例とTrailF](https://github.com/kmizu/lean4-peg/blob/7ffefeabf5ad53f037b87986526483012773082c/lean-pal/PalPeg/GalilTrailProof.lean#L1-L125)
- **[S05]** [GalilTrailRad.lean：RadPack、boot、h_trailF_of_radPack](https://github.com/kmizu/lean4-peg/blob/7ffefeabf5ad53f037b87986526483012773082c/lean-pal/PalPeg/GalilTrailRad.lean)
- **[S06]** [GalilLeafPres.lean：hpresの問題と負債の変化](https://github.com/kmizu/lean4-peg/blob/7ffefeabf5ad53f037b87986526483012773082c/lean-pal/PalPeg/GalilLeafPres.lean#L1-L160)
- **[S07]** [GalilSegmentConstructB.lean：ReadyFuel、区間構成](https://github.com/kmizu/lean4-peg/blob/7ffefeabf5ad53f037b87986526483012773082c/lean-pal/PalPeg/GalilSegmentConstructB.lean#L1-L180)
- **[S08]** [GalilReplaySpan.lean：RunEntriesAtBeginとall-lists版](https://github.com/kmizu/lean4-peg/blob/7ffefeabf5ad53f037b87986526483012773082c/lean-pal/PalPeg/GalilReplaySpan.lean#L3640-L3715)
- **[S09]** [GalilReplaySpan.lean：replay_construct3SFと_fuel版](https://github.com/kmizu/lean4-peg/blob/7ffefeabf5ad53f037b87986526483012773082c/lean-pal/PalPeg/GalilReplaySpan.lean#L3970-L4140)
- **[S10]** [GalilInvPlus3.lean：InvLPSとstage付き着地](https://github.com/kmizu/lean4-peg/blob/7ffefeabf5ad53f037b87986526483012773082c/lean-pal/PalPeg/GalilInvPlus3.lean#L1-L135)
- **[S11]** [GalilOracleMC4.lean：位置分岐と現存する旧前提](https://github.com/kmizu/lean4-peg/blob/7ffefeabf5ad53f037b87986526483012773082c/lean-pal/PalPeg/GalilOracleMC4.lean#L1-L240)
- **[S12]** [LocalWF.lean：7モード、Geom、fpp量子](https://github.com/kmizu/lean4-peg/blob/7ffefeabf5ad53f037b87986526483012773082c/lean-pal/PalPeg/LocalWF.lean)
- **[S13]** [LocalSysConcrete.lean：Starved、追跡、入力到着](https://github.com/kmizu/lean4-peg/blob/7ffefeabf5ad53f037b87986526483012773082c/lean-pal/PalPeg/LocalSysConcrete.lean#L1-L210)
- **[S14]** [LocalLedgerShift.lean：局所走行と正しい締切](https://github.com/kmizu/lean4-peg/blob/7ffefeabf5ad53f037b87986526483012773082c/lean-pal/PalPeg/LocalLedgerShift.lean#L1-L155)
- **[S15]** [LocalLatchRealize.lean：core符号化と最終合成の引数](https://github.com/kmizu/lean4-peg/blob/7ffefeabf5ad53f037b87986526483012773082c/lean-pal/PalPeg/LocalLatchRealize.lean#L1-L215)
- **[S16]** [GalilFinalAssembly4.lean：boot側oracleとfinal4](https://github.com/kmizu/lean4-peg/blob/7ffefeabf5ad53f037b87986526483012773082c/lean-pal/PalPeg/GalilFinalAssembly4.lean)
- **[S17]** [GalilReadyFuelUses.lean：report比較の修復と旧リプレイ残差](https://github.com/kmizu/lean4-peg/blob/7ffefeabf5ad53f037b87986526483012773082c/lean-pal/PalPeg/GalilReadyFuelUses.lean#L1-L130)
- **[S18]** [GalilReplaySpan.lean：StartShape'とstage版](https://github.com/kmizu/lean4-peg/blob/7ffefeabf5ad53f037b87986526483012773082c/lean-pal/PalPeg/GalilReplaySpan.lean#L2900-L3090)
