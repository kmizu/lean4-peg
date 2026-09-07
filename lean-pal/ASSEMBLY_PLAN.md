# 最終組み立て計画（単一 `Prog` 機械 → `RealTimeTM.RecognizedBy PAL`）

作成: 2026-09-08（Fable 5.1）。対象は `lean-pal/`。
前提となる設計は `ALGORITHM_SPEC.md`（アルゴリズム）と repo ルートの `PROGRESS.md` §8 以降
（層別の到達点）。本ファイルは **最後の一段**、すなわち

* 既に証明済みの「テープ意味論」（`FullMachineTapes.fullRound` / `StageTapes.ststate` /
  `MiddleTapes.mround` / `StageMatcherTapesX.stageX`）と、
* 既に証明済みの「有限制御プログラム」（`ProgLang` の `Prog`、`ProgLangPersist.progMachineP`）

を突き合わせて、**1 本の持続 `Prog`** として全体機械を書き、
`Main.pal_in_peg_of_structured` に流し込むまでの手順を定める。

本ファイルは新しい定理を主張しない。既存の到達点の引用と、これから書く補題の
**形（statement の shape）と依存順序** だけを固定する。数学的な未解決は §7 に隔離する。

---

## 0. 記号と既に取れているもの

| 層 | 実体 | 主定理 |
| --- | --- | --- |
| 全体（テープ） | `FullMachineTapes.fullRound` / `fullState` | `full_answer_mem_PAL`、`full_round_actions` |
| 段（テープ） | `StageTapes.stround` / `ststate` | `stage_tapes_spec'`、X 版 `StageTapesX.stage_tapes_specX` |
| 段のインタフェース | `StageIfaceInstance.stageIface` | `stageIface_spec`、`full_answer_mem_PAL_of` |
| 中央ジョブ | `MiddleTapes.mround`（15 本 `OvTapes`） | `middle_flag_read` |
| 照合器 | `StageMatcherTapesX.stageX`（`fedStepX`, `xfRate`） | `stageX_answer_read`、`stageX_cost` |
| 有限制御 | `ProgLang.Prog` + `ProgLangPersist.progMachineP` | `progMachineP_rounds` / `_srun` / `_SAccepts_iff` / `_recognizedBy` |
| 出口 | `Main.pal_in_peg_of_structured` | `StructuredMachine` + `SAccepts ↔ PAL` ⟹ `RecognizedByTotalPEG PAL` |

`progMachineP` は `StructuredMachine Terminal ((CtrlS prog × Bool) × Fin B) Γ t B` であり、
`ofPhases` によりフェーズ `0` が **入力到着固定動作** `inputAct`、フェーズ `1..B-1` が
**制御スタックの継続実行**（ラウンド境界でリセットしない）になっている。
したがって「ラウンド」の境界は既に機械側が与えており、我々が書くのは
**ラウンドをまたいで走り続ける 1 本のプログラム** だけである。

---

## 1. 全体テープ配置（`Fin T`）

### 1.1 部品ごとのテープ束（実在する型から数える）

| 部品 | Lean の型 | 本数 |
| --- | --- | --- |
| GS 走査器 | `GSScanTapes.TapesState' sc = Fin 8 → TapeConfiguration sc` | 8 |
| 検証器の拡張 | `GSVerifierTapes.VExt`（`U`, `X`）、`VTapes' = TapesState' × VExt` | 2 |
| 実時間キュー 1 本 | `RTQueueTapes.QT = Role → TapeConfiguration`、`Role` は `front fdup rear f fp r rp rpdup ok dd` | 10 |
| 照合器の供給 | `VerifierFeed.VMachine'` は `vt : VTapes'` と **キュー 2 本**（`R1`, `R2`） | 10 + 2×10 = **30** |
| 中央ジョブ | `BorderJobTapes.OvTapes`（`P X Cnt U X2 F S1..S9`） | 15 |
| 中央ジョブ（出力側） | `MState.fout` | 1 |
| 中央ジョブ（入力コピー） | `MState.cp1`, `cp2 : ℕ → TapeConfiguration`（**要有限化**、§7.3） | 2×2 = 4 |
| 前処理＋段セットアップ | `PatternTapes.Tapes = Fin 12`（対版 `PatternTapesPair.Tapes13 = Fin 13`） | 13 |

段 1 個（`StageTapes.StageT` の `sm` / `md` / `pg`）＝ **30 + (15+1+4) + 13 = 63 本**。

### 1.2 大域配置

```
T = 4 * 63            -- 4 スロット × 段テープ 63 本      = 252
  + 1                 -- 大域入力テープ inp（arrival 専用）
  + 4                 -- スロットごとの入力コピー最前線 FullT.cpy
  + 1                 -- 消去済み空白テープ FullT.blankT
  + 1                 -- 若年ラウンド（n < 32）用の素朴テープ（§3.3）
  + 1                 -- ラウンド予算カウンタ（§2.3 の padding 用）
  = 260
```

`inp` を `Fin T` の最後（`⟨259, _⟩`）に固定する。`progMachineP` の `inp : Fin t` はこれ。
スロット `i : Fin 4` の段テープは区間 `[63*i, 63*i+63)`、その内部順序は上表の順（`sm` 30 →
`md` 20 → `pg` 13）に固定する。

**数え方の注意（正直に）**：63 は「現在の型がそのまま持っているテープ本数」であり、
最終的には (a) `cp1/cp2` の有限化（§7.3）、(b) 走査 8 本と検証器 2 本のうち退役段で
共有できるものの有無、(c) `Tapes13` の 13 本目（凍結コピー対の第 2 源）が
`FullT.cpy` と重複しないか、で ±数本ずれる。**この数は最終的に Lean の `Fin T` を
書いた時点で確定させ、本ファイルを更新すること。**

### 1.3 部品の解釈を `Fin T` へ移送する

`ProgLangSum` が必要な道具を全部持っている。使う順は次の 3 段。

1. **動作・条件識別子の再ラベリング**：`Prog.map (fa : A₁ → A₂) (fc : C₁ → C₂)` と
   `exec_map`（前提 `hcond : ∀ c σ, I₂.condOf (fc c) σ = I₁.condOf c σ`、
   `hact : ∀ a x σ, I₂.actOf (fa a) x σ = I₁.actOf a x σ`）。
   各部品の `A9 / Act10 / ActG 13 / Act15 / ActE(18)` を、大域の動作型
   `AFull := A9 ⊕ Act10 ⊕ ActG 13 ⊕ Act15 ⊕ ActE ⊕ Ans`（`Ans` は受理フラグ動作、§3）へ
   `Sum.inl/inr` で埋める。
2. **テープ添字の移送**：`Interp.transport (ι : Fin t₁ ↪ Fin T)` と `exec_transport`。
   これがまさに「部品の `Fin 9 / 10 / 13 / 15 / 18` を大域 `Fin T` に置く」操作。
   `ι` はスロット番号 `i` と部品ごとのオフセットで作る（例：スロット `i` の中央ジョブなら
   `ιmd i : Fin 15 ↪ Fin T`, `ιmd i j = ⟨63*i + 30 + j, _⟩`）。
3. **直和**：`Interp.sum` と `exec_sum_inl / exec_sum_inr / exec_sum_seq`。
   4 スロット分と大域テープを 1 本の `Interp` にまとめる。

**手本がある**：`ProgLangSum` 末尾の `e8Emb : Fin 8 ↪ Fin 10` と
`exec_lift_reproduced` が、`GSVerifierProg.exec_lift`（8→10 の持ち上げ）を
`transport` だけで再導出している。全部品の持ち上げをこの形にコピーすればよい。
`InputFree.transport` / `InputFree.sum` で「部品は入力記号を見ない」性質も一緒に運ぶ。

**未整備の組合せ子**：`TextFeedProg2` は `Fin 18 = Fin.append (queue 10) (scan 8)` を
`Fin.append` で手作りしている（`tPIdx = Fin.natAddEmb 10 GSTapes.tP` など）。
`transport` 版に統一して `Fin.append` 依存を落とすのが望ましい（タスク A3）。

---

## 2. ラウンドのプログラム

### 2.1 何をどこに置くか（重要な設計判断）

`progMachineP` は **すでにラウンド境界を持っている**。すなわち：

* フェーズ `0` = 入力到着（`inputAct`）。制御スタックには触らない（`bodyStepP_zero`）。
* フェーズ `1..B-1` = 現在のスタックを `B-1` マイクロステップ進める（`bodyStepP_ne`）。

よって全体機械のプログラムは **トップレベルの「ラウンドループ」を持たない**。書くのは
1 本の無限ループ

```lean
def fullProg : Prog AFull CFull :=
  Prog.loop condTrue roundBody     -- 停止しない
```

であり、`roundBody` が「1 ラウンド分の仕事」を行う。`progMachineP_rounds` により
`n` ラウンドの実行 ＝ `roundSem` の `n` 回畳み込みなので、
**`roundBody` の実行長がちょうど `B-1` マイクロステップであれば**、
機械のラウンド `n` と `roundBody` の `n` 回目の反復が 1 対 1 に対応する。

### 2.2 4 スロットの並行性をどう出すか

問題：`roundBody` の中で、4 スロットそれぞれの「長いプログラム」（前処理の挽き、
セットアップ、照合器のステップ、中央ジョブのバッチ、消去）を **各ラウンド固定予算だけ**
進めたい。しかし `Prog` の制御は 1 本のスタック（`Stack A C`）である。

* **(i) 有限制御に 4 本の部分スタックを持つラウンドロビン**：`Prog` では表現できない。
  `CtrlS prog` は `prog` の部分項からなる **1 本の** スタックの有限部分型
  （`ProgLangPersist.Inv` / `allStacks`）であり、4 本組にするには `progMachineP` と
  その全補題（`phaseRunP_eq` … `progMachineP_SAccepts_iff`）を作り直す必要がある。**却下**。
* **(ii) 直列化＋テープ上の再開点**：`roundBody` を
  「スロット 0 のチャンク → スロット 1 → スロット 2 → スロット 3 → コピー供給 → 消去チャンク」
  の `Prog.seq` にする。各チャンクは自分のテープ上のマーカーへ歩いて行き、
  `≤ B_i` 動作だけ進めてマーカーを置き直して戻る（`Metered` の pause/resume の
  テープ実装）。
* **(iii) `ProgLang` に独立テープ上の `Prog` の積・交錯合成を追加**：
  `Prog × Prog` と公平スケジューラを定義し、そのトレースが交錯であることを証明する。

**推奨は (ii)。** 理由：

* 既存部品はすでに **「1 ラウンド固定動作数」の形で証明済み** である。
  `StageTapes.sgstep` は毎ラウンド `rateP Pre` / `rateS = 160` 動作だけ挽く
  （`sgcost_le`）。照合器は `Metered`（`metered_phi`, `roundBudgetX U k = 85 + U * xfRate k`）
  で 1 ラウンド固定 `B` 動作。中央ジョブは `mround` のバッチ歩調。
  つまり **「チャンクに切る」という設計は既に済んでおり、(ii) は既存の証明をそのまま使える。**
* (iii) は新しい意味論（積の `stepStack`）とその健全性・公平性の証明が丸ごと増える。
  さらに `progMachineP` は `Prog` に対して定義されているので、積を導入すると
  `CtrlS` の有限性（`scap_stepStack` / `Inv_mem_allStacks`）から証明し直しになる。
  得られるのは記述の綺麗さだけで、**費用の議論は結局 (ii) と同じ** になる。

(ii) の採用によるコストは 1 つだけ：チャンクの「再開点」を制御ではなくテープに置くので、
各部品に **番兵（マーカー）記号** と「マーカーまで歩く」前置き・後置きが要る。
歩行距離はチャンク内の移動距離で抑えられる（`ClearAny` / `homeLeft_length_le` /
`walkByMarkProg_exec` と同型の議論）。この定数を `B_i` の中に畳み込む。

### 2.3 予算 `B` と `Cfull`

* 照合器 1 ラウンド：`roundBudgetX U k = 85 + U * xfRate k`、
  `xfRate k = (k+1) * (xfA k + xfB)`、`xfA k = 8k+47`、`xfB = 82`。
  `k = 8` なら `xfRate 8 = 9 * 193 = 1737`、`hU : 8k+124 ≤ U`（`uceil_fcostX_advance`）から
  `U ≥ 188`、よって `roundBudgetX 188 8 = 85 + 188*1737 = 326641`。
* 段 1 ラウンド：`CstageX D Pre U k = CmT' D + rateP Pre + 160 + 86 + roundBudgetX U k`
  （`CstageX_eq`、上界は `stage_round_actionsX`）。
* 全体 1 ラウンド：`Cfull I = 11 * I.C + 30`（`FullMachineTapes.Cfull`、
  上界は `full_round_actions`：常駐段 ≤ 3 個 ＋ 入力 1 ＋ コピー 4 ＋ 番兵 4 ＋
  消去チャンク `8C+1` ＋ 対複製 20）。

したがって **マイクロステップ数の予算は**

```
B := Cfull I + Wwalk + 1
```

とする（`Wwalk` は (ii) の再開点歩行の総定数）。`progMachineP` はフェーズ `0` を
入力到着に使うので、プログラムが使えるのは `B - 1` 動作であり、これが `Cfull I + Wwalk`
に一致する。`Cfull` はテープ意味論側の「動作数」であって、`Prog` 側の
「マイクロステップ数」とは **`applyTrace` の 1 要素 = 1 マイクロステップ** の対応で
等しくなる（`ProgLang.Exec` の `acts.length`）。この同一視を明示するのが補題
`cost_eq_trace_length`（§5 のタスク A4）。

### 2.4 `roundBody` の骨格（`B-1` ちょうどに揃える）

```lean
def roundBody : Prog AFull CFull :=
  Prog.seq (copyFeed)                 -- 入力記号を 4 スロットのコピー・供給キューへ
  (Prog.seq (slotChunk 0)
  (Prog.seq (slotChunk 1)
  (Prog.seq (slotChunk 2)
  (Prog.seq (slotChunk 3)
  (Prog.seq (clearChunk)              -- 退役スロットの定速消去（Prologue.spreadClear）
  (Prog.seq (answerStep)              -- 受理フラグの更新（§3）
            (padTo B)))))))           -- 残り予算を消化して長さをちょうど B-1 にする
```

`slotChunk i` は自分のスロットの状態（テープ上のフェーズ記号）を読み、
`idle / prep-grind / setup / matcher-step / middle-batch` のどれを行うかを分岐する。
これは `StageTapes.stround` の 5 分岐（`n ≤ S/2` / `≤ 3S/4` / `≤ S` / `≤ S+|u|` / それ以降）
と 1 対 1 に対応させる。分岐の判定は **ラウンド番号 `n` の比較** なので、
`n`, `S`, `S/2`, `3S/4` をユナリカウンタとして各スロットに持たせ、比較を
「2 本のカウンタを同時に歩いて先に番兵に当たった方」で行う（既存の `RTQueueTapes` の
差分カウンタ、`GSPreprocessProg2.CMPLT_PF` と同じ手口）。

`padTo B` は予算カウンタテープ（§1.2）を使って残りを no-op で消化する。
**これが「ラウンド境界とプログラムの同期」の全体である**：入力到着はプログラムから
見えないので（§7.1 の例外を除く）、同期はこの長さ合わせだけで担保する。

---

## 3. 受理ビット

### 3.1 どこに入るか

`InterpF` は `Interp` に `flagOf : A → Option Bool` を足したもので、
`updFlag` により **マイクロステップごとに** フラグが更新される
（`some b` なら `b` に書き換え、`none` なら不変）。`progMachineP` の受理は
`accepting q = q.2`（制御に載った `Bool`）であり、`progMachineP_SAccepts_iff` は
「`w` を読み終えたラウンド末のフラグ」が答えだと言っている。

したがって：

* 大域動作型に `Ans : Bool → AFull` を足す。`flagOf (Ans b) = some b`、
  他の全動作は `flagOf = none`。`actOf (Ans b) _ σ = fun j => (σ j, .stay)`（テープ不変）。
* `roundBody` の `answerStep` で、`if condAnswerTrue then Prog.act (Ans true) else Prog.act (Ans false)`
  を 1 回だけ実行する。フェーズ `0`（入力到着）はフラグを変えない
  （`bodyStepP_zero` が制御を素通しにする）ので、**1 ラウンドにフラグ書き込みは 1 回**。

### 3.2 `condAnswerTrue` の中身

`FullMachineTapes.fullAnswer` は `32 ≤ n` のとき
`(residentStages n).any (fun S => decide (S = stageOf n) && I.bit S n)` であり、
`I.bit` は `StageTapes.stAnswerBit`、その `stAnswerBit_eq` により

```
stAnswerBit … = manswer … && decide (Tape.read Scur.md.fout = one)
```

すなわち **照合器の報告ビット** と **中央ジョブの読み出しフラグテープ `fout` の現在記号**
の連言。よって `condAnswerTrue` は次の 3 条件の連言をテープから読むだけでよい：

1. 担当スロット（`stageOf n` が入っているスロット）を選ぶ：スロットごとに
   「自分が担当か」を示す 1 セルを持たせ、`slotChunk` が更新する。
2. そのスロットの照合器の報告セル（`Metered.mreported` に対応する 1 セル）が `one`。
3. そのスロットの `fout` の注目記号が `one`（`middle_flag_read`）。

### 3.3 `n < 32` の有限場合分け

`fullAnswer` は `n < 32` で `decide (IsPal (w.take n))` を返す。これは
「定数記憶で持てる」と `FullMachineTapes` のコメントにあるが、`Prog` の制御は
スタックなので **32 分岐のはしごを制御に書くのは避ける**。
§1.2 で確保した若年ラウンド用テープに `w` の先頭 31 記号を溜め、
毎ラウンド素朴に反転比較する（`≤ 62` 動作、定数）。`n ≥ 32` になったら
このテープは使わない（消去は `clearChunk` に相乗り）。
対応補題は `naiveWrite`（`MiddleTapes.mround` の `width < 8` 分岐）と同型なので流用できる。

---

## 4. 対応証明の戦略

### 4.1 符号化関数

```lean
noncomputable def encodeFull (F : FullT sc) (aux : AuxTapes sc) : Fin T → STape (Fin sc)
```

`aux` は `Prog` 側にしか無いもの（フェーズ記号、カウンタ、予算、若年テープ、再開マーカー）。
`encodeFull` は §1.2 の配置に従って `F.inp`, `F.cpy i`, `F.blankT`,
`F.slots i` の `sm`/`md`/`pg` を並べる。

### 4.2 中核となる 1 ラウンド補題

```lean
theorem roundBody_exec
    (n : ℕ) (F : FullT sc) (aux : AuxTapes sc) (hinv : FullInv n F aux) :
    ∃ acts : List (Fin T → Fin sc × Move),
      ProgLang.Exec IFull blank roundBody (encodeFull F aux) acts ∧
      acts.length = B - 1 ∧
      applyTrace blank (encodeFull F aux) acts
        = encodeFull (fullRound blank leftSym rs I (n+1) F) (auxStep n aux) ∧
      FullInv (n+1) (fullRound blank leftSym rs I (n+1) F) (auxStep n aux) ∧
      flagAfter acts = fullAnswer I (n+1)
```

すなわち **「`roundBody` の 1 反復のテープ効果 ＝ `fullRound` 1 回」** ＋
**「長さちょうど `B-1`」** ＋ **「フラグ ＝ `fullAnswer`」**。
`FullInv` は「各スロットのフェーズ記号・カウンタが `n` と整合」「再開マーカーが正しい位置」
「予算カウンタが 0」などの不変条件。

### 4.3 `roundBody_exec` の分解（使う既存補題）

| チャンク | 既存の `exec` 補題 | 既存の歩調・費用補題 |
| --- | --- | --- |
| 供給（copyFeed） | `TextFeedProg2.feed_online_prog`, `_halts`, `_trace` | `VerifierFeedX.fcostX_amortized` |
| 前処理挽き | `GSPreprocessProg*` の `decProgP`（`Fin 9`, 作業中）→ `PrepInstance.prepInstance` | `StageTapes.sgstep` / `sgcost_le`、`stripProg2_spec` |
| セットアップ | `PatternPairProg.pairLoopProg_exec`, `kLoopProg13_exec`, `prologueProgP`（`Fin 13`） | `setup_rate_ok`, `setup_complete'` |
| 照合器 1 ステップ | `GSVerifierProgX.vprogX_exec` / `_trace_length` / `_halts` / `_encodes`（`Fin 10`） | `StageMatcherTapesX.stageX_cost`, `uceil_fcostX_amortized` |
| 中央ジョブ | `MiddleProg.batchProg` / `stageProg_exec` / `jobLoopProg_exec`（`Fin 15`） | `MiddleTapes.mround` の `next` 歩調、`mcost_le` |
| 消去 | `ClearAny`（≤ 3·幅+3）、`Prologue.spreadClear` | `FullMachineTapes.clear_fits`, `pair_copy_rate_ok` |

各行を §1.3 の `transport` / `Prog.map` / `sum` で `Fin T` に持ち上げ、
`exec_sum_seq` で `Prog.seq` に沿って合成する。

### 4.4 ラウンドの反復

```lean
theorem progRound_effect (w : List (Fin sc)) :
    ∀ n ≤ w.length,
      ((progMachineP IFull fullProg inp encT htape hB blank).srun (w.take n)).tape
        = encodeFull (fullState blank leftSym rs I init n) (auxState n)
```

証明：`progMachineP_rounds`（`roundSem` の畳み込み）で 1 ラウンドに落とし、
`roundSem` の中身（`arrive` → `runInputs (replicate (B-1) none)`）を
`roundBody_exec` で置き換える。帰納は `n` について。
`arrive` は `inp` 以外を動かさない（`arrive_ne`）ので、スロット側の一致は
`roundBody_exec` の結論そのままで通る。

**注意**：ここで `progMachineP_grind` は **使わない**（§7.1）。使うのは
`progMachineP_rounds` / `_srun` / `_SAccepts_iff` の 3 本で、これらは
`NoInputTouch` を仮定しない。

### 4.5 受理の一致と最終定理

```lean
theorem prog_answer (w : List (Fin sc)) :
    (progMachineP IFull fullProg inp encT htape hB blank).SAccepts w
      ↔ FullMachineTapes.fullAnswer I w.length = true
```
（`progMachineP_SAccepts_iff` ＋ `roundBody_exec` のフラグ節の畳み込み。）

```lean
theorem pal_SAccepts (w : List (Fin 2)) :
    (progMachineP IFull fullProg inp encT htape hB blank).SAccepts w ↔ w ∈ PAL
```
（`prog_answer` ＋ `StageIfaceInstance.full_answer_mem_PAL_of`。§7.2 のアルファベット
問題をここで吸収する。）

出口は 2 つあり、**どちらを最終形にするか決めておく**：

* `Main.pal_in_peg_of_structured hB M hM : RecognizedByTotalPEG PAL`
  — `M : StructuredMachine (Fin 2) Q Γ t B` と `hM : ∀ w, M.SAccepts w ↔ w ∈ PAL` を取る。
  `progMachineP` はまさに `StructuredMachine` なので **こちらが直行ルート**
  （`RecognizedBy` を経由しない）。
* `ProgLangPersist.progMachineP_recognizedBy : RecognizedBy { w | … SAccepts w }`
  — 依頼にある `RealTimeTM.RecognizedBy PAL` の形が欲しい場合はこちら。
  言語の集合等式で書き換える（`Set.ext` で `pal_SAccepts`）。

最終形（両方書いておく）：

```lean
theorem pal_recognizedBy : RealTimeTM.RecognizedBy PAL := by
  have h : { w | (progMachineP IFull fullProg inp encT htape hB blank).SAccepts w } = PAL :=
    Set.ext pal_SAccepts
  simpa [h] using progMachineP_recognizedBy (I := IFull) (prog := fullProg) …

theorem pal_in_peg : RecognizedByTotalPEG PAL :=
  Main.pal_in_peg_of_structured hB (progMachineP IFull fullProg inp encT htape hB blank)
    pal_SAccepts
```

### 4.6 仮定の通し方（1 本だけ）

数学側の未解決は `Consumption` 1 本に集約されている
（`PassSum10.passPeriodSum_eight_of_consumption : Consumption → PassPeriodSum 8 2`）。
`stageIface` は `C₁` と `hsum : ∀ y b s, stripLoop2Periods y 8 b (y.length+1) s ≤ C₁ * b`
を取るので、`C₁ := 2` と `hsum := (passPeriodSum_eight_of_consumption hcons)` を渡す。
**したがって最終定理は**

```lean
theorem pal_recognizedBy (hcons : Consumption) : RealTimeTM.RecognizedBy PAL
```

の形になる。`Consumption` が証明できた時点で仮定は消える。
**これ以外の仮定を増やさないこと**（増やしたら本ファイルに追記する）。

---

## 5. 依存順のタスク一覧

規模は「新規に書く Lean 行数」の見積り。

### フェーズ A：持ち上げの土台（他の全部の前提）

| # | 内容 | 規模 |
| --- | --- | --- |
| A1 | 大域の動作型 `AFull` / 条件型 `CFull` / 解釈 `IFull : InterpF (Fin 2) AFull CFull (Fin sc) T` を定義。`Ans` 動作と `flagOf` を含む。 | 150 |
| A2 | 各部品の `ι`（`Fin 9/10/13/15/18 ↪ Fin T`）と `Prog.map` のラベル関数、`hcond`/`hact` の証明。`e8Emb` / `exec_lift_reproduced` が手本。 | 600（部品 6 種 × 100） |
| A3 | `TextFeedProg2` の `Fin.append` 手作り持ち上げを `transport` 版へ統一。 | 200 |
| A4 | `cost_eq_trace_length`：テープ意味論の「動作数」と `Exec` の `acts.length` の同一視。 | 80 |

### フェーズ B：欠けている部品の完成（`PROGRESS.md` 由来）

| # | 内容 | 規模 |
| --- | --- | --- |
| B1 | `GSPreprocessProg*` の `decProgP`（`Fin 9`）を完成（分岐比較層）。 | 400 |
| B2 | `prepInstance` の 9→13 埋め込みと prologue/epilogue（`PROGRESS.md` で「未着手」）。 | 300 |
| B3 | `MiddleTapes` 側 4 点修正（フラグ番兵・S3/S4 複写・`keepS` 緩和・`clearF` 掃引）と `DecompOnTapes` の `EntryBlank` 前提の反映。 | 400 |
| B4 | `cp1/cp2` の有限化（二重バッファ、§7.3）。 | 300 |
| B5 | `PrepPre` の番兵形への修正（§7.4）。`prepPre_inb_needs_future_input` / `not_prepPre_of_blank_right` が現形の不備を証明済み。 | 250 |

### フェーズ C：ラウンド本体

| # | 内容 | 規模 |
| --- | --- | --- |
| C1 | 再開マーカー機構（「マーカーへ歩く／`≤ B_i` 動作／置き直す」）の汎用補題。`walkByMarkProg_exec` と `ClearAny` の一般化。 | 350 |
| C2 | `slotChunk i`：5 フェーズ分岐（`stround` と 1 対 1）とその `exec` 補題。カウンタ比較（§7.5）を含む。 | 700 |
| C3 | `copyFeed` / `clearChunk` / `answerStep` / `padTo`。§7.1 の (α)/(β) の決定を含む。 | 400 |
| C4 | `FullInv` の定義と `roundBody_exec`（§4.2）。**最大の山**。 | 1200 |

### フェーズ D：仕上げ

| # | 内容 | 規模 |
| --- | --- | --- |
| D1 | `progRound_effect`（§4.4）。 | 250 |
| D2 | `prog_answer` / `pal_SAccepts`（§4.5）。 | 200 |
| D3 | アルファベット持ち上げ（§7.2）。 | 400 |
| D4 | `pal_recognizedBy` / `pal_in_peg` と `#print axioms` ガード。 | 80 |

合計おおよそ **6,300 行**。フェーズ A と B は並行可、C は A・B に依存、D は C に依存。

---

## 6. ビルド上の注意

`lakefile` は `autoImplicit = false` だが `lake env lean` はそれを読まない。単体検査は必ず

```sh
lake env lean -DautoImplicit=false PalPeg/<File>.lean
```

で行う（`MiddleTapes` の「`lake build` だけ失敗」の原因がこれ）。

---

## 7. 正直に残っているギャップ

### 7.1 `NoInputTouch` は全体機械では成り立たない

`progMachineP_grind` は「プログラムがラウンド境界を見ずに挽き潰される」という
気持ちのいい定理だが、その前提 `NoInputTouch` は
**「条件も動作も入力テープの読みに依存しない」**（`condIgnore` / `actOther`）を要求する。
全体機械は到着記号を `cpy` と供給キューへ複製しなければならないので、
`inp` を読む必要があり、この前提は **成り立たない**。

対応は 2 つ。

* **(α) `inp` を読む**（`progMachineP_rounds` は無仮定なのでそのまま使える）。
  ただし `inputAct` は書いてから右へ動くので、直前に書かれた記号は
  ヘッドの 1 つ左にある。`roundBody` の先頭で `left` → 読む → `right` と戻し、
  「ラウンド境界で `inp` のヘッドは最前線にいる」を `FullInv` の一部として持つ。
  この左右移動は動作数 2 で済む。
* **(β) `ProgLangPersist` を一般化**：フェーズ `0` の固定動作を `inputAct` から
  任意の到着動作 `arr : Option Terminal → (Fin t → Γ) → (Fin t → Γ × Move)` に
  パラメータ化し、到着記号を `inp` と 4 本の `cpy` と供給キュー先頭へ同時に書く。
  `bodyStepP_zero` 以降の補題はほぼそのまま通る（`arrive` の定義を差し替えるだけ）。

**推奨は (β)**（動作数・不変条件ともに軽く、`fullRound` が `inp` と `cpy` を同時に
書いている形とそのまま一致する）。ただし `ProgLangPersist` の変更なので、
`progMachineP_round` / `_rounds` / `_srun` / `_SAccepts_iff` の再証明（機械的、~150 行）が要る。
(α) を選ぶなら `ProgLangPersist` は無改造で済む。**どちらを採るかを C3 の着手前に決めること。**

### 7.2 アルファベットが `Fin 2` に潰れている

`FullMachineTapes.full_answer_mem_PAL` は `w : List (Fin 2)` を要求し、
`StageIfaceInstance.full_answer_mem_PAL_of` は
`blank startSym endSym mark leftSym one zero : Fin 2` を取る。
一方で設計は `mark ≠ blank`、`leftSym ∉ w`、`endSym ∉ w`、`one ≠ zero` を仮定しており、
**2 記号のアルファベットでこれらを同時に満たすのは（`w` が退化していない限り）不可能** である。
つまり `full_answer_mem_PAL_of` は現状ほぼ空虚に近い。

必要なのは **入力アルファベットとテープアルファベットの分離**：
`ι : Fin 2 ↪ Fin sc`（`encT` がまさにこれ）を入れ、
`FullMachineTapes` 側の `w : List (Fin sc)` を `w = w₀.map ι` の形に制限したうえで
`IsPal (w₀.take n) ↔ IsPal (w.take n)`（`ι` は単射なので成立）を経由して
`w₀ ∈ PAL` に落とす。作業は D3。**これは設計の穴ではなく形式上の穴だが、
分量はそれなりにある**（`occursAt` / `IsPal` / `effPeriod` の `map` 可換性）。

### 7.3 `cp1 / cp2 : ℕ → TapeConfiguration` は無限族

`MiddleTapes.MState` の入力コピーはバッチ番号で添字づけられた **無限族** であり、
このままでは `Fin T` に入らない。`mround` を見ると使われるのは `c1 j`（`j = idx+1`）と
`c2 j` だけなので、**生存しているのは高々 2 世代**。有限化は
「`cp1_cur`, `cp1_nxt`, `cp2_cur`, `cp2_nxt` の 4 本」で足りるはずだが、
`feed` が全世代に書き込む形になっているので、`feed` を「現世代と次世代だけに書く」形へ
書き換え、`mround` の仕様（`middle_flag_read` が依存する部分）を保つ証明が要る（B4）。

### 7.4 `PrepPre` の形（番兵）

`StageBirth` に監査結果が明示されている：`hinit_unsatisfiable`、
`prepPre_inb_needs_future_input`（現形の `PrepPre.inb` は **未来の入力** を要求してしまう）、
`not_prepPre_of_blank_right`。`initOf_hinit` は `S/2 ≤ |w|` ガード付きでのみ充足。
正しい形は「番兵つきの `w.take L`」であり、`InputCopySentinel` と
`FullMachineTapes.stage_birth_pair_prepView` がその形を用意している。
`PrepPre` の定義を番兵形に直し、`stage_tapes_spec'` の `hpinit` を差し替える（B5）。

### 7.5 カウンタ駆動 vs テープ駆動の混在

* **カウンタ駆動（`ℕ` の算術のまま）**：`stround` の 5 分岐（`n ≤ S/2` など）、
  `mround` の `next`、`setupGrind` の `n = 3*(S/4)+1`、
  `FullMachineTapes.stageInSlot` / `slotOf S = Nat.log 2 S % 4` / `residentStages n`。
  これらは `Prog` では **ユナリカウンタテープ＋差分比較** に落とす必要がある
  （`GSPreprocessProg2.CMPLT_PF`、`RTQueueTapes` の差分カウンタが手本）。
* **テープ駆動（既に済み）**：`decompose2_on_tapes`、`vprogX`、`batchProg`、
  `feed_online_prog` は番兵・マーカー駆動。

`slotOf S = Nat.log 2 S % 4` の実装（段幅は 2 冪なので「幅カウンタの長さの `log`」）は
**幅カウンタを 2 で割りながら 4 進カウンタを回す** で足りるが、
`Nat.log` の仕様との突き合わせ補題が要る（C2 に含む）。
`residentStages n`（常駐 ≤ 3）も同様に「幅カウンタ 3 本」で表す。

### 7.6 予算 `B` の確定

`B = Cfull I + Wwalk + 1` の `Wwalk` は C1・C2 を書き終えるまで確定しない。
`Cfull I = 11 * I.C + 30`、`I.C = CstageX D Pre U 8` で
`rateP Pre` と `CmT' D` はインタフェース依存（`prepInstance` / `decompInstance` の
具体値が決まってはじめて数になる）。
**`B` を数値リテラルで固定するのは最後にする。** それまでは
`B` を変数、`hB : 0 < B`、`hbudget : Cfull I + Wwalk ≤ B - 1` の形で持ち回り、
`padTo` で余りを吸収する（不等式のままで組み立てが通るようにしておく）。
`progMachineP` は `B` について多相なので問題なく可能である。
