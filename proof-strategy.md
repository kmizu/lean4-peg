# lean4-peg：証明完了に向けた大方針と進行計画 — Implementation Plan

> 実行するエージェントへ：本書は証明戦略のレビューと作業計画である。実装時は `superpowers:executing-plans` を使い、各段階の接続確認まで完了させる。並列化よりも、主定理までの依存関係を一人が把握することを優先する。

**Goal:** `PalPeg.PalInPeg.unconditional : RecognizedByTotalPEG PAL` から、最後の追加公理 `obligation_localRealization` を取り除く。

**Architecture:** 既存の canonical trace、抽象アルゴリズムの正当性、局所機械から PEG への経路を維持する。物理機械の証明を、最終消費者の仮定に合う「初期化・入力到着・通常 tick・停止・出力」の契約として組み立てる。

**Tech Stack:** `lean-pal/` の Lean **v4.31.0**、Mathlib **v4.31.0**、PegSeparation **c364edb**。隣の `lean/` の v4.32.0 と混ぜない。[設定][lake]

**Spec:** [AGENTS.md §0][agents]、[最終消費者 given_physicalMachine][consumer]、[目標定理][uncond]を基準にする。本書は §0 の「次は matched」という順序を、接続確認の結果に基づいて修正する提案である。

**調査基準:** 2026-09-22、main の `eb2b4d0e8e806effe27f2524e65038a291ef0ef7`。リンクはこのコミットに固定した。公開ソースと最近のコミット、引き継ぎ文書を静的に確認した。この調査環境では Lean / Lake を実行できておらず、以下の新しい補題案・接続案はビルド未検証である。既存 build 成功はリポジトリ側の記録として扱う。

---

## 1. 結論

**「あと一歩」という見立ては、証明の大きな構造については当たっている。ただし、最後の一歩は単一の難しい補題ではなく、物理実装と最終定理を結ぶ統合作業である。**

現在はアルゴリズム全体を考え直す段階ではない。次の三つを優先する。

1. **最終消費者から逆算し、必要な状態・ガード・不変量を固定する。**
2. **既存の簡単な分岐を一つ、物理ステップから最終接続まで実際に通す。**
3. **その同じ接続面に、matched、DP、境界カウンタ、カーソルの付け替えを追加する。**

とくに、現在の進行をそのまま「次は matched、その後に残りの枝」と続ける前に、**scan のガード、入力語に依存する Enc、空白テープからの初期化**を確認すべきである。ここには実際の型・定義の不一致がある。

Codex の推論時間・ビルド時間の内訳は測定していないため、「モデルが遅い」「コンパイルが主因」とは断定できない。一方、ソースからは、**最終接続で使えるかを確かめる前に、細かい部品の証明が積み上がる構造**が読み取れる。この構造を変えることが、最も確実な改善策である。

## 2. 現在地を正しく捉える

### 2.1 目標と残存義務

ソース上の目標は次である。

```lean
PalPeg.PalInPeg.unconditional : RecognizedByTotalPEG PAL
```

その本体は `entry = 0, q = 1, first = 0` を使い、未証明の局所実現を渡している。

```lean
axiom obligation_localRealization (entry q : ℕ) (first : Fin 9) :
    H_realizeCanonical centreC placeC entry q first
```

最終公理監査の期待値には、この公理がまだ含まれる。[目標と残存義務][uncond]／[監査][audit]

したがって、**最初に閉じる対象は固定証人 `0 1 0` に対する最終定理でよい**。任意の `entry q first` に対する物理機械の構成まで、最初の完了条件に含める必要はない。一般補題は再利用し、最後の組み立てだけを固定する。

### 2.2 既存の成果は大きい

主線には既に、cycle oracle、scan landing、chain verifier supply、canonical successor の同定、物理機械から `PAL ∈ PEG` を得る消費者がある。物理側にも、有限制御・118 本のテープ、ビューの12ステップ、窓による読み取り、プログラム実行の局所性、`TEqG` による輸送がある。[最終定理本体][uncond]／[消費者][consumer]／[物理符号化][physical]

これらを捨てて、別の回文アルゴリズム、別のテープ配置、汎用コンパイラを新しく作るのは勧めない。

### 2.3 「1公理」「12分岐」「約15,000行」は別の指標

`PhysicalEncoding.lean` は約15,000行あるが、行数は完了率ではない。`_of_tick` という文字列には、個別分岐だけでなく組み立て補題も含まれる。また、分岐定理に未供給の仮定が残っていれば、その定理の存在だけでは最終接続は閉じない。

例えば `rewind_one_of_tick` は、後状態の `hctl` と `htapes` を受け取る組み立て器であり、`rewind_one_of_tick_branch` 等とは役割が異なる。これらを同じ単位で足し算しない。[rewind の署名][rewind]

**最終完了の指標は追加公理ゼロのまま維持し、途中の作業管理には「最終消費者へ接続済みのケース」を使う。** 追加公理が1本のままでも有用な作業はできるが、それを最終定理の証明完了と区別する。

本書の完了対象は、この最終定理による言語の所属の証明である。巨大な生成済み PEG の各規則の翻訳検証や、Scala 実装との一致まで同じ完了条件に加えない。それらを追加する場合は別の目標として扱う。

## 3. 最優先で検査すべき接続上の問題

### 3.1 直近の scan 消費定理は、そのまま hideal に入らない

これは今回の調査で最も重要な点である。

`scan_consume_of_tick` と `background_still_of_tick` は、scan モードで次を仮定する。

```text
!replaying && !available = true
```

`galilFrameFun.available` は `canRightTest x.vm.right` である。一方、`FrameFunction.starvedTest` は scan モードでは右ヘッドが進めることを要求する。

したがって、定義を展開すると次の含意になる。

```text
mode = scan
∧ (!replaying && !available = true)
⇒ available = false
⇒ starvedTest x = true
```

しかし、`forwardTick_of_rule` の **hideal が処理するのは `starvedTest x = false` の場合**である。飢餓側では、抽象状態を保つことが要求される。[scan 消費定理][scan-consume]／[静止定理][scan-still]／[飢餓判定][starved]／[最終接続][forward-rule]

つまり、現在の quiet 分岐の証明を、そのまま「必要な非飢餓 tick を一つ閉じた」と数えることはできない。

これは既存補題が偽という意味ではない。生の `tickFun` の一分岐については有用な定理であり、カーソル、カウンタ、period テープの証明は再利用できる。問題は、**その外側にある飢餓停止の契約との接続**である。

**推奨する修正方向**

- 飢餓の場合は、最終消費者の要求どおり「同じ抽象状態の符号化を保つ」。
- 非飢餓の scan は、restart 優先を守って分類する。
- background の実作業は、まず **`1 < clock` の count 側**へ載せる。
- この場合は VM 側の効果だけでなく、`clock := clock - 1` も同時に証明する。
- count 側について、`hready`、比較結果の対応、符号更新を呼び出し元で供給する。

現在の `ruleNext` の scan 行は `chainConsumesTest` で分岐するだけであり、count 側の clock 更新はそこに入っていない。単に既存補題の `hquiet` を差し替えるだけでは完成しない。[ruleNext][rule-next]／[tickFun][tickfun]

**最初の作業は、このガード関係を Lean で小さく確認すること。** 検証用の補題案を付録Aに載せる。

### 3.2 Enc の入力語依存と、消費者の量化が一致していない

現在の物理側は、

```text
PhysicalEncoding.Enc w margin x p
```

という形である。`EncControl` には、

```text
q.onLetterBit = onLetterTest w x.vm
```

があり、`onLetterTest` は右ヘッド位置と **w.length** を比較する。

一方、`given_physicalMachine` と `forwardTick_of_rule` の `Enc` は、

```text
State GalilVM → PhysicalState → Prop
```

で、入力語を引数に取らない。さらに `forwardTick_of_rule.hideal` は、同じ Enc のもとで任意の `w` を要求する。[Enc][enc]／[EncControl][enc-control]／[onLetterTest][onletter]／[消費者][consumer]

**`Enc w` の w を適当に固定したり、`∃ w, Enc w` に包んだりするだけでは解決しない。** 存在する語が、実行中の語と一致する保証がないからである。

ここで必要なのは、次の量化順序を保った接続である。

```text
一つの有限機械 M を構成する
その M について、すべての入力語 w に対する正しさを証明する
```

証明用の不変量が w を参照すること自体は問題ない。機械の遷移表・初期制御・有限アルファベットを、未来の入力語ごとに選んではいけない。

**進め方**

1. `onLetterBit` を、到着済み入力と局所ヘッド情報から更新できることを、実行上の不変量と結び付ける。
2. その対応から入力語に依存しない Enc を作れるなら、既存消費者をそのまま使う。
3. 局所定理を `Enc w` のまま運ぶ方が小さい変更なら、**機械を w の外で固定したまま、証明述語だけを w で添字付けする**消費者を作る。元の定理本体から導き直し、最後まで標準公理のみであることを検査する。

この選択は matched の大量実装より前に終える。実装用の制御に w を持ち込むことは解決策にしない。

### 3.3 現在の Enc を、全空白の初期状態に直接使うことはできない

`given_physicalMachine.hencInit` が要求する物理初期状態は、

```lean
(q0, fun _ => STape.blankTape blankSymbol)
```

である。

しかし、`EncTapes.fpp` 等は `padLeft margin` による配置を要求する。`padLeft` は底の番兵を1セル追加し、

```text
pos (padLeft margin T) = pos T + margin + 1
```

となる。全空白の初期テープの位置は0なので、**現在のパディング済み Enc を hencInit に直接代入することはできない**。これは margin を0にしても残る。`sweepClosure` も位置を保存する `TEqG` による閉包なので、この差を消せない。[初期契約][consumer]／[padLeft][padding]／[EncTapes][enc-tapes]／[sweepClosure][closure]

ただし、ここをゼロから作る必要もない。

- `LocalQueueInit.compStep_apply_blankEdge`：左端の全空白からの最初の sweep。
- `LocalViewInit.viewRep_empty_of_seals`：空ビューの表現。
- `LocalBlankState`：抽象初期状態との対応。
- `ProgramWarmStart`：初回入力を保持して初期化する方式の参考。

これらは再利用候補だが、現在の `Γm`、底番兵、各スロットの配置への接続は別に確認する。特に `viewRep_empty_of_seals` の empty view と、`blankVML` が用いる gap=true の blank view の差を見落とさない。[空白開始][blank-edge]／[空ビュー][view-init]／[抽象初期状態][blank-state]

**必要な設計は、初期化前と初期化後の二段階である。**

- 初期化前を受け入れる外側の符号化を置く。
- 最初の物理遷移が、番兵・余白・カウンタ・制御を準備する。
- その遷移で与えられた入力を落とさず、対応する抽象入力到着まで扱う。
- 以降はパディング済みの通常 Enc を用いる。

未計上の準備 tick を挿入して、元の入力速度や報告時刻を変えてはいけない。

### 3.4 マクロ境界の不変量が、定理の引数として残っている

既存の tick 組み立て器は、

- `q.slot.val = 0`
- 全ビューについて、前のマイクロ処理の残り仕事が0
- moveRight に必要な `hready`

を引数として受け取る。

ところが、現在の `Enc` の定義だけを見ても、slot=0 や残り仕事0は含まれていない。したがって、Enc だけを受け取る最終接続に、これらの定理をそのまま適用することはできない。[Enc][enc]／[組み立て器][assembler]

「また hslot0 を引数に足す」で済ませず、**マクロステップの前後で保たれる物理不変量**にする。

ここは物理的な事実と、実行に沿った事実を区別する。

| 種類 | 例 | 供給元 |
|---|---|---|
| 物理境界 | slot=0、残り仕事0、パディング余白 | 初期化と12ステップ実行の保存 |
| 表現 | テープの符号化、符号ビット、役割割当 | Enc と各操作の保存 |
| 実行上の性質 | 右移動の可用性、head の位置関係、正当な chain の状態 | OnRun、CanonTrace、既存の run 不変量 |

`given_physicalMachine.hforwardTick` は `OnRun` と trace を受け取る。一方、汎用の `forwardTick_of_rule` ではそれらが落ち、任意の符号化状態に量化している。**後者が強すぎる場合は、OnRun を保持した接続補題を用意する。** 到達可能な状態でしか成り立たない性質を、任意状態に強めて証明しようとしない。

### 3.5 半径 K は、12ステップを融合すると 12K になる

`LocalStepFusion.iterRadius_eq` は、

```text
iterRadius K count = count * K
```

である。したがって、12ステップを一つの `ActRule` に融合する場合、融合後の窓半径は **12K** になる。`compStep_iterRule` も、その半径に見合うヘッド位置を要求する。[融合の定義と定理][fusion]

既存分岐の多くは `K ≤ margin` を受け取って12回の `idealRun` を証明している。この結論から実際の融合ステップへ進むときは、**少なくとも採用する融合定理が要求する 12K の余白**を別途そろえる必要がある。

文書とコードでは、

- `microRadius`：各マイクロステップの半径
- `macroRadius`：融合後の半径
- `margin`：物理配置が保証する余白

を区別する。これは新しい機械モデルを作る話ではなく、既存の型引数を取り違えないための整理である。

また、現在の `physRule`、`tickPhysRule`、その12回の `idealRun` は別物である。引き継ぎの概略よりも実際の定義を優先する。[規則の定義][rules]

### 3.6 境界イベントと alias は、戦術より表現設計の課題

`counterOf` は chain の distance / boundary / last を独立の読み取りとして扱っている。`scanConsumeActs` のコメントにも、ブロック境界の付け替えはまだ表現に入っていないと明記されている。[counterOf][counters]／[境界未対応][consume-acts]

`LocalCounter.resetSeg` があることは有利だが、**resetSeg があるだけでは、三つの論理カウンタをその段構造から読み出せるとは限らない**。その読み出しと保存を証明する必要がある。

先に固定するのは次の対応である。

| 操作 | 必要な契約 |
|---|---|
| カウンタを1増減する | 数値と polarity が一緒に更新される |
| 区切りを作る | 新しい段の値と、残る段の値が分かる |
| boundary / last を付け替える | 論理値の変更を定数個の操作で実現できる |
| 鏡を使う | 元の値を変えるすべての経路が鏡も更新する |
| カーソルをコピー・付け替えする | 有限の役割変更と、必要なら独立な複製の維持で実現する |
| 廃棄側を再利用する | 次に live になる時点で初期状態が供給される |

とくに、「同じ位置にする」ことを「同じ物理テープを共有する」ことで済ませると、後で二つの論理カーソルが別々に動く場合に困る。既存の role / mirror の仕組みを使い、将来の独立更新まで含めて契約にする。

## 4. 大方針：最終消費者を中心に組み立てる

### 4.1 完了までの経路を一本に固定する

推奨する主線は次である。

```text
既存の抽象正当性
  cycleOracleOnPackedRun
  scanLandingObligationsAlongTrace
  chainVerifierSupplyAlongTrace
              │
              ├──────────────────────────┐
              │                          │
     具体的な有限機械              物理機械の契約
     Q / Γ / L0 / q0                初期化 / feed / tick
     repQ / outQ                    frozen / report / output
              │                          │
              └──────────┬───────────────┘
                         ▼
                given_physicalMachine
                またはその健全な添字付き版
                         ▼
          PalInPeg.unconditional : RecognizedByTotalPEG PAL
                         ▼
       #print axioms が標準公理だけであることを確認
```

新しい補題には、**この図のどの矢印に使うか**を必ず付ける。

### 4.2 最終消費者の全引数を、先に棚卸しする

`given_physicalMachine` の物理側には、実際の署名上、以下の**8つの証明引数**と `PhysFrozen` という述語がある。tick だけで全部ではない。[署名][consumer]

| 証明引数 | 終わったと言える条件 |
|---|---|
| hencInit | 全空白の初期配置から、採用した外側の符号化が成立 |
| hforwardTick | 通常実行と飢餓停止の両方で、物理 none ステップが正しい後状態を表す |
| hforwardFeed | some letter ステップが arriveState' と一致 |
| hfrozenEnter | 最終報告後に、物理側の停止不変量へ入れる |
| hfrozenKeep | none ステップが停止不変量を保つ |
| hfrozenQuiet | 停止中は report ビットが false |
| hencRep | reportTest と物理 report ビットが一致 |
| hencOut | 報告点で抽象 output と物理 output ビットが一致 |

このほか、有限性・テープ数の正値性・固定パラメータの算術条件・既存の抽象側3契約がある。すべてを接続台帳に載せる。

述語を定義しただけ、前提として受け取っただけ、別の axiom に置き換えただけでは、その行を「完了」にしない。

### 4.3 完成の単位を「部品」から「消費者が使えるケース」へ変える

一つのケースの完成条件を次で統一する。

1. 最終消費者の仮定から、そのケースのガードが出る。
2. 制御・テープ・ヘッドの遷移が、**同じ実装済みの規則**について証明される。
3. hready などの側条件が、追加の未証明仮定なしに供給される。
4. slot=0、残り仕事0、余白、鏡、役割割当が後状態でも成立する。
5. idealRun から、採用した融合規則・sweepClosure まで輸送される。
6. 最終 tick dispatcher の一ケースに実際に組み込まれる。

「制御の式を証明した」「窓から文字を読めた」は必要な中間成果である。ケースの完成とは別に記録する。

## 5. 実行順序

以下の新規ファイル名は提案であり、現存するものではない。大きな既存ファイルの移動は、最初の作業に含めない。

### M0：接続面とガードを確定する

**読むファイル:** `ShadowedLocalFinal.lean`、`PalInPegUnconditional.lean`、`FrameFunction.lean`、`TickFunction.lean`、`PhysicalEncoding.lean` の署名部分。

**作成候補:** `PalPeg/PhysicalGuardProbe.lean`、`PalPeg/PhysicalContract.lean`。

- [ ] 付録Aの quiet ⇒ starved を Lean で確認する。
- [ ] 固定パラメータ 0 / 1 / 0 で、最終消費者の引数を一覧化する。
- [ ] Enc の w 依存、初期状態、OnRun の保持方法を決める。
- [ ] microRadius / macroRadius / margin、各プログラムの有限PC範囲を固定する。
- [ ] 未完成部分は名前付きの明示仮定として、接続の型を検査する。新規 axiom や sorry は導入しない。
- [ ] 仮定付き接続は「型が合うことの確認」と記録し、残存義務の解消とは数えない。

**出口:** 「残りの分岐を証明すれば接続できる」という前提が、型と量化のレベルで確認されていること。ここで壊れるなら、それを直すまで大量の分岐追加を止める。

### M1：初期化・入力到着・マクロ境界を先に通す

**利用するファイル:** `LocalQueueInit.lean`、`LocalViewInit.lean`、`LocalBlankState.lean`、`MachineStep.lean`、`LocalStepFusion.lean`、物理側の制御と配置。

**作成候補:** `PalPeg/PhysicalBoundary.lean`、`PalPeg/PhysicalBootFeed.lean`。

- [ ] 初期化前と通常動作中の外側の符号化を定義する。
- [ ] 全空白の初期状態を証明する。
- [ ] 初回入力を保持し、初期化と最初の到着を正しく接続する。
- [ ] 通常の some letter が `arriveState'` に対応することを証明する。
- [ ] 初期化・feed・12ステップ tick のそれぞれについて、マクロ境界の不変量を供給する。
- [ ] 融合後の余白を使って sweepClosure へ輸送する。
- [ ] 空入力、最初の1文字、入力到着直後の飢餓解除を検査する。

**出口:** hencInit と hforwardFeed が具体的な機械について成立し、tick の呼び出し元が hslot0 / howed を毎回供給できること。

入力到着を最後まで残さない。現在の `physRule` は nq / acts の入力引数を捨てているため、それだけでは hforwardFeed を満たさない。通常 tick の規則と入力到着の規則を区別して、同じ L0 の none / some に正しく割り当てる。[現在の physRule][rules]

### M2：非飢餓の scan count を、最初の接続例として完成させる

**変更対象:** `PhysicalEncoding.lean` の scan 分岐表と関連補題。必要なら新しい分岐判別子を `PhysicalScanDispatch.lean` に置く。

- [ ] 外側の飢餓停止と、内側の restart 優先を表にする。
- [ ] 非飢餓の count 側で静止するケースを閉じる。
- [ ] 既存の `scanConsume_*` と `stepState` を使い、plain token の消費ケースを閉じる。
- [ ] clock の減算、polarity、period の移動、verifier の右移動を一緒に確認する。
- [ ] hready と各読み取りの一致を、Enc と実行不変量から供給する。
- [ ] その結果を hforwardTick の実際のケースへ接続する。

**出口:** 生の tickFun の補題ではなく、最終消費者が使う**非飢餓の一ケース**が閉じること。

ここで得られた接続パターンを、以後の分岐の標準にする。現在の quiet 分岐で作った部品はこの作業に再利用する。

### M3：残りの分岐が共有する、表現上の難所を解く

**主対象:** カウンタの段構造、カーソルの付け替え、DP 実行、再利用されるバッファ。

**利用するもの:** `LocalCounter.resetSeg`、`mirrorSource`、role 系、`MachineAgree`、`progRunActs_of_agree`、`fppActs_eq` など。

- [ ] distance / boundary / last の読み出しを、段構造の不変量として確定する。
- [ ] 境界記号の first / last、方向反転を含む consume の各ケースを閉じる。
- [ ] init / replayStart / choose-select に必要なカーソル複製・役割交換を実装し、後の独立更新も保存する。
- [ ] chain 誕生時の idle → active に対して、verifier の表現を供給する。
- [ ] DP の12テープに、既存の有限窓による実行証明を接続する。
- [ ] DP・FPP の退役側を、再度 live にする条件を確認する。

**出口:** matched、beginShift、beginFallback、restart などが使う操作に、同じ配置上の保存補題があること。

FPP 用の窓シミュレータを DP に使う際、必要ならテープ本数の型引数だけを一般化する。一般化そのものを独立の大きなプロジェクトにしない。

### M4：matched と残りのケースを、同じ dispatcher に載せる

**matched で既に使えるもの:** `agreeTest_eq`、`matchedTest_compareFun`、着地先の読み取り、二状態の `enc_afterTickOfState`。[比較の読み取り][agree]／[matched の一致][matched]

matched の1ティックは、次を同時に行う。

- 左カーソルの左移動。
- 右カーソルの右移動。
- 移動先同士の比較。
- 探索の1量子。
- chain の一歩または誕生。
- radius / length / cycle、および output / replaying の更新。

証明は意味上の三部分、**比較・探索・chain**に分けてよい。ただし、最終的には同じ前状態の窓から作った同じ規則の結果として合成する。書き込み先が重なるところは、元の `compareFun` の順序を保つ。[compareFun][compare]

- [ ] matched の side conditions を呼び出し側で供給する。
- [ ] beginShift / beginFallback が、比較後の状態を使うことをそろえる。
- [ ] restart が最優先の scan 分岐であることを保持する。
- [ ] init、replayStart、choose-select、shiftOne、chain 誕生を接続する。
- [ ] 分岐表の残りパラメータ `rest` を具体化する。
- [ ] 各モードを場合分けし、未処理のケースが残らないことを Lean のゴールで確認する。

**出口:** 非飢餓の hforwardTick が全ケースで成立し、各枝の個別仮定が外へ漏れないこと。

### M5：停止・出力を閉じ、最終定理を切り替える

**変更対象:** 最終接続モジュール、`PalInPegUnconditional.lean`、`Axioms.lean`。新規モジュールは `Workbench.lean` または主線側の適切な import に登録する。

- [ ] PhysFrozen と enter / keep / quiet を、同じ機械の none ステップについて証明する。
- [ ] hencRep と hencOut を証明する。
- [ ] 既存の抽象側3契約を固定証人 0 / 1 / 0 で渡す。
- [ ] `unconditional` を具体機械からの経路へ切り替える。
- [ ] `obligation_localRealization` への依存を取り除き、未使用の追加公理宣言も整理する。
- [ ] 最終公理監査が標準公理だけになることを確認し、guard を更新する。
- [ ] ルート全体をビルドする。
- [ ] 「unconditional は存在しない」等の古い説明を、実際の結果に合わせて更新する。

**出口:** 最終定理の型が `RecognizedByTotalPEG PAL` のままで、追加公理・sorryAx に依存せず、全体 build が成功していること。

## 6. ケース台帳の持ち方

「あと約10枝」の固定リストだけでは足りない。モードの枝と、その内部の search / chain / token の場合分けが異なるからである。

まず次の表を作り、各行に**ガード、定理、側条件の供給元、最終接続の使用箇所**を記録する。

| 群 | 分けるべきケース | 注意点 |
|---|---|---|
| 初期化 | blank、最初の none / some | 余白がまだない |
| feed | some letter | 通常 tick と同一視しない |
| 飢餓 | starved=true | 抽象状態を保持 |
| scan restart | 非飢餓かつ restart guard | 他の scan より先 |
| scan count | 非飢餓、restart=false、clock>1 | clock を減らす |
| scan matched | 比較一致 | search と chain も更新 |
| scan shift/fallback | 比較不一致 | 比較後の状態から判定 |
| chain consume | 成功/失敗、plain/境界、方向 | plain の定理で全体を数えない |
| chain lifecycle | idle/copy/back/watch/broken、誕生 | head の有無が変わる |
| fallback 系 | copy/home/fpp/markEnd/choose/rewind | select と back を分ける |
| shift/replay | shiftOne/exit/replayStart | 役割変更と出力更新 |
| 終了後 | plateau/frozen | 余分な report を出さない |

表の全直積を機械的に展開してはいけない。到達可能性とガードから不要な組み合わせを落とす。逆に、到達不能性を使うなら、その証明を記録する。

各行の状態は次の四つで十分である。

- **未接続**：部品があっても、最終呼び出しには入っていない。
- **条件付き接続**：適用できるが、供給元のない側条件が残る。
- **接続済み**：側条件を閉じ、実際の dispatcher に組み込んだ。
- **不要と証明**：最終消費者の前提と両立しないことを証明した。

この表を、コミット数・補題数とは別に管理する。

## 7. Codex の進め方を変える

### 7.1 一回の依頼は、親のゴールとセットにする

「証明を進めて」ではなく、次の形式で渡す。

```text
対象：
  どの最終接続の、どのケースを閉じるか。

消費者：
  定理名と引数名。入力となる仮定を原文の型で示す。

使う既存部品：
  今回必要な定理名とファイル。

今回増やしてよいもの：
  不足する読み取り・輸送・保存補題。

完了条件：
  親の呼び出しに組み込まれ、追加の未証明仮定がない。
  単体・対象モジュールの検査が通る。
  追加公理を増やさない。

失敗時の成果：
  失敗したゴールの全文、足りない仮定、
  仮定の供給候補、反例の有無。
```

「最小の補題を一つ証明して終わり」にはしない。内部では細かく進めても、依頼の出口は親のゴールが一つ閉じるところに置く。

### 7.2 戦術を試す前に、仮定が十分かを確認する

長く詰まったら、同じ `simp` / `omeg合わせを繰り返す前に、次を確認する。

1. 結論は、受け取っている仮定だけで数学的に成立するか。
2. raw tick のガードと、外側の実行条件が矛盾していないか。
3. 必要な事実は Enc の事実か、OnRun の事実か。
4. 前状態と後状態、比較前と比較後を混ぜていないか。
5. 論理上の alias を、物理テープの走査に置き換えていないか。

原則として30〜60分同種の失敗が続いたら、ゴーã»®定の点検に切り替える。これは時間保証ではなく、探索の方向を変える運用上の目安である。

### 7.3 巨大な履歴文書を毎回読み直さない

既存の `PROOF_STACK.md` や `ASSEMBLY_PLAN.md` は経緯の保存には役立つが、最新タスクの入力としては大きすぎる。古い記述も混ざる。`AGENTS.md` 自体も §0 より下には古い到達点があると明記している。[引き継ぎ][agents]

毎回読む順序を固定する。

1. 最新の短い接続台帳。
3. 今回の消費者の型。
4. 必要な定義・既存補題。
5. 履歴は、設計理由や反証を探すときだけ。

`PhysicalEncoding.lean` は、全体を毎回読むより、宣言検索と局所的な読み取りを使う。部品を知らないと判断する前に、既存索引とソースを検索する。

### 7.4 ビルド回数より、フィードバックの適切さを優先する

推奨する検証範囲は次のとおり。

| 変更 | 最初のæ--|---|
| 小補題・局所修正 | 対象ファイル | ケースが閉じた時点で対象モジュール |
| Enc / QPhys / 分岐表 | 影響を受ける対象モジュール | 接続モジュールと公理監査 |
| 最終経路の変更 | 接続モジュール | PalPeg 全体と公理監査 |

依存モジュールを編集した場合、単なる `lake env lean` では古い olean を読む可能性がある。**変更した依存関係を `lake build 対象モジュール` で更新してからå を補題ごとに回す必要はない。逆に、単一ファイルが通っただけで、import される最終経路まで確認済みとはしない。

`iterRule` と大きな分岐表を何度も展開すると重くなることは、ソースコメントにも記録がある。小さい等式補題を境界に置き、融合は合成点で行う。大規模分割や heartbeat 上限の増加に着手する前に、対象コマンドの時間を一度測る。[融合を局所化する理由][rule5 中心設計は単独で保持する

現在は Enc、役割、分岐表、初期化が相互依存している。ここを別々のエージェントに自由に変更させるのは勧めない。

もし後で並列作業を使うなら、境界を固定した後に、

- 一つの読み取り補題。
- 決まった表現に対する一つの保存補題。
- ガードの網羅性のレビュー。

のような独立作業に限る。主線と最終接続は一人が保持する。今回の計画のå須ではない。

### 7.6 報告は短く、使える情報を残す

作業終了時の報告は次の5点でよい。

```text
接続済みになったケース：
残存する具体的なゴール：
新たに見つかった型・表現の問題：
実行した検証と終了コード：
次に触る消費者と、その理由：
```

途中の成功を長い進捗文書へ毎回追記するより、親のケースを閉じた時点で台帳と引き継ぎを更新する。

## 8. 重点レビュー局所補題は通っても最終定理が閉じないケースを先に固定する。

| 入力・状態 | 期待する確認 | 担当段階 |
|---|---|---|
| 空入力、初回入力 | 空白開始、初期化中の入力保持、出力の扱い | M1 / M5 |
| scan で右ヘッドが進めない | 外側の飢餓停止と raw background を区別 | M0 / M2 |
| clock>1 の scan | chain/search の動作と clock 減算が同居 | M2 |
| period の境界記号と方向反転 | boundary / last / distance のæ M3 |
| chain 誕生、replayStart、choose-select | カーソルの役割変更と独立更新を保存 | M3 / M4 |
| 最終報告の後 | none が続いても report を再発行しない | M5 |

有限入力の実行検査は、仕様やガードの誤りを早く見つけるために使う。長い入力や任意状態への証明の代わりにはしない。Lean 内で意味のある小さな反例・不可能性補題を残す方が、同じ誤った命題への再挑戦を防げる。

## 9. 最ç¡件

このプロジェクトの完了は、次のすべてで判定する。

- [ ] `PalPeg.PalInPeg.unconditional` の型が `RecognizedByTotalPEG PAL`。
- [ ] 同定理の公理依存が `propext`、`Classical.choice`、`Quot.sound` の範囲内。
- [ ] `obligation_localRealization`、別名の追加公理、`sorryAx` が最終依存にない。
- [ ] 具体的な機械は入力語によらず一つで、有限制御・有限アルファベット・有限テープ数が証明されている。
- [ ] 初期化、feed、tick、frozen、report、output が同じ機械・符号化について接続されている。
- [ ] 新しい主線が実際の import に含まれ、`lake build PalPeg` が成功する。
- [ ] 監査 guard が現実の結果を固定している。

典型的な確認コマンドは次である。実行ディレクトリは **lean-pal/** とする。

```sh
lake build PalPeg.Workbench
lake env lean PalPeg/Axioms.lean
lake build PalPeg
```

各コマンドの終了コードと出力ã¿え時には、その時点のソースから依存モジュールが再検査されていることも確認する。

**新しい追加公理で本数を維持する、目標を条件付きへ弱める、有限検査だけで普遍命題を済ませる、という変更は完了に数えない。** 固定証人0/1/0への特殊化は、入力語に対する全称性を保つ限り、目標を弱めない。

## 10. 次の Codex に渡す指示文

以下を、そのまま最初の依頼に使える。

> 無条件 PAL ∈ PEG の最後の接続を進めてください。対象の基準コミットは eb2b4d0e8e806effe27f2524e65038a291ef0ef7 です。現在の HEAD が進んでいる場合は、以下の指摘がまだ成り立つかを先に確認してください。
>
> 最初の対象は matched の大量実装ではなく、PhysicalEncoding と ShadowedLocalFinal.given_physicalMachine の契約を一致させることです。最終目標は PalPeg.PalInPeg.unconditional から obligation_localRealizaことです。
>
> まず、PhysicalEncoding.scan_consume_of_tick の hquiet が scan モードで FrameFunction.starvedTest=true を含意することを、小さい補題で検証してください。forwardTick_of_rule.hideal は starvedTest=false を要求するので、現在の quiet 側の定理をそのまま接続済みと数えないでください。既存のテープ・ヘッドの部品を、非飢餓の clock>1 側で再利用する方針を確認してください。
>
> 次に、given_physihine の全引数を、固定証人 entry=0、q=1、first=0 で棚卸ししてください。PhysicalEncoding.Enc の w 依存、全空白の初期状態と padLeft の違い、slot=0 / 残り仕事0の供給、12ステップ融合後の半径、hforwardFeed、PhysFrozen、report/output を明示してください。OnRun が必要な事実を、任意状態の仮定へ強めないでください。
>
> 新規 axiom・sorry を使わず、必要なら名前付きの明示仮定で接続の型だけを先に検査してください。その段階は証明完了とは報告しないでください。既存の LocalQueueInit、LocalViewInit、LocalBlankState、MachineStep、LocalStepFusion、PhysicalEncoding.sweepClosure_afterStep を検索して再利用してください。
>
> 今回の出口は、最終接続の契約を確定し、次に閉じる一ケースと、そこに必要な側条件の供給元を特定することです。可能なら、そのまま一ケースを親の接続まで閉じてくだã¶済みケース、残ったゴールの正確な型、検証コマンドと終了コードを報告してください。補題数や行数だけを進捗にしないでください。

## 付録A：最初に実行する、小さいガード検査

以下は**検証用コード案であり、この調査では Lean に通していない**。目的は、最終接続と quiet 分岐の前提が両立しないことを短い補題として確かめることである。

作成候補：`lean-pal/PalPeg/PhysicardProbe.lean`。

```lean
import PalPeg.FrameFunction

set_option autoImplicit false

namespace PalPeg.PhysicalGuardProbe

open PalPeg.GalilScaffoldTop
open PalPeg.GalilScaffoldChainInputSupply

theorem quiet_scan_starves
    (x : State GalilVM)
    (hmode :
      x.ctl.mode = PalPeg.GalilScaffoldController.Mode.scan)
    (hquiet :
      (!x.ctl.replaying && !canRightTest x.vm.right) = true) :
    PalPeg.FrameFunction.starvedTest x = true := by
  have hav : canRightTest x.vm.right = false := by
    cases h canRightTest x.vm.right <;> simp_all
  simp [PalPeg.FrameFunction.starvedTest,
    PalPeg.FrameFunction.starvedOf, hmode, hav]

#print axioms quiet_scan_starves

end PalPeg.PhysicalGuardProbe
```

検査：

```sh
lake env lean PalPeg/PhysicalGuardProbe.lean
```

この補題が通った後、既存の `hquiet` の available が `canRightTest` に展開されることまで確認する。続けて「非飢餓なら quiet 側には入らない」を dispatcher の場合分けで使う。

この検査は、ズム全体の反証ではない。**どの既存補題を最終接続のどのケースへ使えるかを正確にする検査**である。

## 付録B：判断の確度と調査範囲

| 判断 | 根拠・確度 |
|---|---|
| 最終定理に追加公理が1本残る | 目標の本体と公理監査の期待値を確認。今回の再ビルドは未実施 |
| quiet scan のガードは starved=true を含意 | 定義からの直接の論理的帰結。付録Aの Lean コードは未実行 |
| Enc w とç違う | 署名を確認 |
| パディング済み Enc は全空白初期状態を直接表せない | padLeft と EncTapes の定義・位置の式からの帰結 |
| slot=0 / howed が既存組み立て器の追加仮定 | 署名と Enc のフィールドを確認 |
| 12ステップ融合の半径は12K | iterRadius_eq と compStep_iterRule のソースを確認 |
| 境界カウンタの表現が未接続 | counterOf、scanConsumeActs、最新引き継ぎが一致 |
| 接続中心の進め方で改善ã 上記に基づく作業戦略の提案。速度の定量測定ではない |
| 残り何日・何％か | 判断材料不足。分岐数だけでは推定しない |

全1,248個の `lean-pal/PalPeg/*.lean` を一つずつ監査したわけではない。最終定理、その消費者、現在の物理構成、関連する初期化・融合・読み取り部品を重点的に調べた。「未接続」は、この主線へ接続されていることを確認できないという意味であり、別モã¨可能な部品がないという断定ではない。

[agents]: https://github.com/kmizu/lean4-peg/blob/eb2b4d0e8e806effe27f2524e65038a291ef0ef7/AGENTS.md
[lake]: https://github.com/kmizu/lean4-peg/blob/eb2b4d0e8e806effe27f2524e65038a291ef0ef7/lean-pal/lakefile.toml
[uncond]: https://github.com/kmizu/lean4-peg/blob/eb2b4d0e8e806effe27f2524e65038a291ef0ef7/lean-pal/PalPeg/PalInPegUnconditional.lean#L144
[audit]: https://github.com/kmizu/lean4-peg/blob/eb2b4d0e8e806effe27f2524e65038a291ef0ef7/lean-pal/Paxioms.lean#L392
[consumer]: https://github.com/kmizu/lean4-peg/blob/eb2b4d0e8e806effe27f2524e65038a291ef0ef7/lean-pal/PalPeg/ShadowedLocalFinal.lean#L1395
[physical]: https://github.com/kmizu/lean4-peg/blob/eb2b4d0e8e806effe27f2524e65038a291ef0ef7/lean-pal/PalPeg/PhysicalEncoding.lean
[rewind]: https://github.com/kmizu/lean4-peg/blob/eb2b4d0e8e806effe27f2524e65038a291ef0ef7/lean-pal/PalPeg/PhysicalEncoding.lean#L14556
[scan-consume]: https://github.com/kmizu/lean4-peg/blob/eb2b4d0e8e806effe27f2524e65038a291ef0ef7/lean-pal/PalPeg/PhysicalEncoding.lean#L14384
[scan-still]: https://github.com/kmizu/lean4-peg/blob/eb2b4d0e8e806effe27f2524e65038a291ef0ef7/lean-pal/PalPeg/PhysicalEncoding.lean#L13630
[starved]: https://github.com/kmizu/lean4-peg/blob/eb2b4d0e8e806effe27f2524e65038a291ef0ef7/lean-pal/PalPeg/FrameFunction.lean#L888
[forward-rule]: https://github.com/kmizu/lean4-peg/blob/eb2b4d0e8e806effe27f2524e65038a291ef0ef7/lean-pal/PalPeg/ShadowedLocalFinal.lean#L984
[rule-next]: https://github.com/kmizu/lean4-peg/blob/eb2b4d0e8e806effe27f2524e65038a291ef0ef7/lean-pal/PalPeg/PhysicalEncoding.lean#L10283
[tickfun]: https://github.com/kmizu/lean4-peg/blob/eb2b4d0e8e806effe27f2524e65038a291ef0ef7/lean-pal/PalPeg/TickFunction.lean#L119
[enc]: https://github.com/kmizu/lean4-peg/blob/eb2b4d0e8e806effe27f2524e65038a291ef0ef7/lean-pal/PalPeg/PhysicalEncoding.lean#L2066
[enc-control]: https://github.com/kmizu/lean4-peg/blob/eb2b4d0e8e806effe27f2524e65038a291ef0ef7/lean-pal/PalPeg/PhysicalEncoding.lean#L1966
[enc-tapes]: https://github.com/kmizu/lean4-peg/blob/eb2b4d0e8e806effe27f2524e65038a291ef0ef7/lean-pal/PalPeg/PhysicalEncoding.lean#L851
[onletter]: https://github.com/kmizu/lean4-peg/blob/eb2b4d0e8e806effe27f2524e65038a291ef0ef7/lean-pal/PalPeg/FrameFunction.lean#L783
[padding]: https://github.com/kmizu/lean4-peg/blob/eb2b4d0e8e806effe27f2524e65038a291ef0ef7/lean-pal/PalPeg/PhysicalEncoding.lean#L158
[closure]: https://github.com/kmizu/lean4-peg/blob/eb2b4d0e8e806effe27f2524e65038a291ef0ef7/lean-pal/PalPeg/MachineStep.lean#L40
[blank-edge]: https://github.com/kmizu/lean4-peg/blob/eb2b4d0e8e806effe27f2524e65038a291ef0ef7/lean-pal/PalPeg/LocalQueueInit.lean#L72
[view-init]: https://github.com/kmizu/lean4-peg/blob/eb2b4d0e8e806effe27f2524e65038a291ef0ef7/lean-pal/PalPeg/LocalViewInit.lean#L29
[blank-state]: https://github.com/kmizu/lean4-peg/blob/eb2b4d0e8e806effe27f2524e65038a291ef0ef7/lean-pal/PalPeg/LocalBlankState.lean
[assembler]: https://github.com/kmizu/lean4-peg/blob/eb2b4d0e8e806effe27f2524e65038a291ef0ef7/lean-pal/PalPeg/PhysicalEncoding.lean#L10913
[fusion]: https://github.com/kmizu/lean4-peg/blob/eb2b4d0e8e806effe27f2524e65038a291ef0ef7/lean-pal/PalPeg/LocalStepFusion.lean#L142
[rules]: https://github.com/kmizu/lean4-peg/blob/eb2b4d0e8e806effe27f2524e65038a291ef0ef7/lean-pal/PalPeg/PhysicalEncoding.lean#L10418
[counters]: https://github.com/kmizu/lean4-peg/blob/eb2b4d0e8e806effe27f2524e65038a291ef0ef7/lean-pal/PalPeg/PhysicalEncoding.lean#L178
[consume-acts]: https://github.com/kmizu/lean4-peg/blob/eb2b4d0e8e806effe27f2524e65038a291ef0ef7/lean-pal/PalPeg/PhysicalEncoding.lean#L8922
[agree]: https://github.com/kmizu/lean4-peg/blob/eb2b4d0e8e806effe27f2524e65038a291ef0ef7/lean-pal/PalPeg/PhysicalEncoding.lean#L8828
[matched]: https://github.com/kmizu/lean4-peg/blob/eb2b4d0e8e806effe27f2524e65038a291ef0ef7/lean-pal/PalPeg/PhysicalEncoding.lean#L14524
[compare]: https://github.com/kmizu/lean4-peg/blob/eb2b4d0e8e806effe27f2524e65038a291ef0ef7/lean-pal/PalPeg/FrameFunction.lean#L525
