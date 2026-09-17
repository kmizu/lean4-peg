# CLOSEOUT_LEDGER — lean-pal 残差台帳

**目的**: 無条件 `PAL ∈ PEG`（`PegSeparation.RecognizedByTotalPEG PalPeg.PAL`）へ向けて、
主経路に残る**意味的義務**だけを一元管理する。ファイル追加・新しい `finalN`・build 成功は、
それ単独では前進として数えない。

**状態区分**

| 区分 | 意味 |
|---|---|
| `OPEN` | 未証明の意味的義務が残っている |
| `REFUTED` | 現在の命題に反例がある。証明対象でなく修正対象 |
| `REFORMULATED` | 命題を適切に変更したが、成立または利用側との接続が未完 |
| `PROVED` | 新命題自体は証明した。最終経路への供給は未確認 |
| `INTEGRATED` | 成立済みの前提から供給でき、主経路で利用され、対応する旧義務が消えた |

**未解消の前提を `H_x → H_y`、構造体フィールド、instance、別 oracle へ移しただけなら `OPEN` のまま。**

基点: HEAD `b70b395`（PR #61）。検証コマンド: `cd lean-pal && lake build --quiet PalPeg`。
`#print axioms` は推移的公理依存の検査であって、引数として置いた前提の成立を検証しない。
最上位定理の**完全な型**を `#check` で確認し、各前提の供給元まで追うこと。

---

## 2026-09-19 訂正: `hor` に producer は無かった — `H_oracle` とは別物。橋を作った

**全体 build 成功（EXIT=0、エラー 0、sorryAx 0）・標準公理のみ・無条件 PAL は未完。**

### ウチの「訂正」自体が誤りだった

以前「`hor` は producer ゼロで原理的に到達不能」と書いたのを
「誤り。`h_oracle_of_leaves''` が 14 葉から産出する」と訂正した。
**その訂正が誤りだった。** 定義を読むと：

| 名前 | origin | 着地の不変量 |
|---|---|---|
| `GalilTraceCost.CycleOracleMC`（`H_oracle` の中身） | `InvL raw c r` | `InvL raw cT sT` |
| `GalilInvPlus3.CycleOracleMC3`（`hor` の型） | `InvLPS P q first raw c r` | `InvLPS P q first raw cT sT` |

`ReachAtC` / `ReachAtC3` も同じ 1 箇所だけ違う（`GalilTraceCost:115` vs
`GalilInvPlus3:194`）。そして tree 中の `h_oracle_of_leaves*` は**全部**
（`GalilOracleMC2`, `GalilOracleLeaves2`, `GalilOracleMC3`,
`GalilSegmentConstructB`, `GalilReadyFuelUses`, `GalilLeafReport`,
`CloseoutOracle5`〜`CloseoutOracle8`）`GalilFinalAssembly.H_oracle` を結論とする。
つまり `hor` には producer が無く、両者は交換不能（`MC3` は強い着地不変量を
**配らねばならない**）。

**教訓**: 型名の一致だけでなく、**定義を展開して origin と結論の不変量を照合する**。
`h_oracle_of_leaves` という名前が同じでも結論が違う。

### 橋（`CloseoutOracleBridge`）— 差は 2 つだった

| 名前 | 内容 |
|---|---|
| `invL_of_invLPS` | origin 側はタダ（`InvLPS → InvL` は射影 4 つ） |
| `reachAtC3_of_C` | `ReachAtC → ReachAtC3`（継続の不変量を lift） |
| `cycleOutMC3_of_MC'` | `CycleOutMC' → CycleOutMC3`（不変量のみ） |
| `cycleOutMC3_of_MC` | `CycleOutMC → CycleOutMC3`。**差は 2 つ**：`GalilLexMeasure.cycleOutMC'_of_MC` が中心進行を `mu` 進行に変換（`mu_lt_of_centre`）、lift が不変量を動かす |
| `cycleOracleMC3_of_MC` / `hor_of_H_oracle` | `hor` を `H_oracle` ＋ lift から |

すべて標準 3 公理のみ。

### `hor` の残差（確定）

```
hor  =  H_oracle（11 葉、CloseoutOracle8.h_oracle_of_leaves7）
      +  InvLPS 着地 lift（着地での Inv ＋ SpanRep）
```

lift はタダではない: `GalilInvPlus3.invLPS_of_landed` は着地の
`Inv raw cT sT`（`InvL` では不足 — `InvS` の半分は `Inv ∨ InvScan`）と
`SpanRep sT`、および origin の `CopyPack` から作る。`CopyPack` は `InvLPS`
origin が持つので、残るのは**着地の `Inv` と `SpanRep`**。
これは `CloseoutStageBoot` / `CloseoutStageCheck` が boot 状態でやった
`InvLPS` lifting と同種の作業。

**最上位は変わらず 4 前提**（`hSP` `hor` `hC` `hpack`）。計画書 §10.5 は未達。

---

## 2026-09-19 訂正: `hended` / `hlastMatch` は閉じていない（側入力 `hpres` が偽）

**全体 build 成功（EXIT=0、エラー 0、sorryAx 0）・標準公理のみ・無条件 PAL は未完。**

`CLAUDE.md` §3 は `hended` と `hlastMatch` を「閉」に挙げていたが**誤り**。

producer は 3 つあるが（`GalilLeafReport.hended_C`（`:234`）、
`GalilLeafReport.hlastMatch_C`（`:352`）、`GalilOracleMC4.hlastMatch_C'`（`:71`））、
どれも側入力

```
hpres : ∀ w s a v, SearchReady (searchLens.get s) →
          searchEffect (PofC centre place entry w) a s v → SearchReady v
```

を取る。ところが `GalilLeafPres.searchReady_run_true_iff` が既に正確な法則

```
SearchReady v' ↔ 1 ≤ value v.search.debt
```

を証明している（`.run → .run` の event `true` 量子について）。つまり readiness は
**debt に 1 単位残っているときだけ**生き残る。`SearchReady v` は
`0 ≤ value v.search.debt` しか与えないので、debt 0 では破れる。

機械検査可能な形で記録した: `CloseoutPresRefute.hpres_fails_at_zero_debt`
（標準 3 公理のみ）。

`hpres`: `REFUTED`。`hended` / `hlastMatch`: `OPEN`（`h_oracle_of_leaves7` の葉のまま）。
閉じるには `GalilLeafPres` が指定する `SearchReadyB := ReadyRem ∧ RunEntriesAll` への
再切り出しが必要で、現在の `hpres` を証明しようとしても無駄。

CLAUDE.md §3 の「閉」リストも訂正した。併せて **`Decodes` はタダ**（`decodesC` が
証明済み、`Closeout*` 全域の `hP : Decodes (PofC …)` は全部不要）を明記した。

**最上位は変わらず 4 前提**（`hSP` `hor` `hC` `hpack`）。計画書 §10.5 は未達。

---

## 2026-09-19 `hor` の葉が 13 → 11 — `Decodes` はタダだった

**全体 build 成功（EXIT=0、エラー 0、sorryAx 0）・標準公理のみ・無条件 PAL は未完。**

### 鍵：`Decodes` は義務ではない

`Decodes P`（`GalilScaffoldTopReadyFound:22`）は `P.centre` と `P.place` だけを縛る：

```
(∀ u a ls rs q gap, u.center = represent ⟨a :: ls,gap⟩ (rs.map some) q →
   read ⟨a :: ls,gap⟩ = some (P.centre u) ∧ P.place u = ⟨a :: ls,gap⟩) ∧
(∀ u v, u.center = v.center → P.place u = P.place v)
```

`centreC` / `placeC` は `s.center` の具体関数なので、これは
**`GalilFinalAssembly2.decodesC (entry) (w)` として既に証明済み**（`:327`）。
`Closeout*` 全域で `hP : Decodes (PofC centreC placeC entry w)` が素通し
仮説として threaded されていたが、それは全部タダだった。

### 閉じた 2 葉

| 葉 | producer |
|---|---|
| `hrs`（`RestartShape`） | `GalilReplaySpan.restartShape_sharedC` — 無条件 |
| `hbudget`（`ReplayBudgetR`） | `GalilFoundStageInv.replayBudgetR_of_decodes'` を `decodesC` で |

### 新規（`CloseoutOracle8`）

| 名前 | 内容 |
|---|---|
| `hbudget_C` | `∀ w, ReplayBudgetR w (PofC centreC placeC entry w) q first 2048` |
| `hrs_C` | `∀ w, RestartShape (PofC centreC placeC entry w)` |
| `h_oracle_of_leaves7` | `h_oracle_of_leaves6` の 13 葉 → **11 葉** |

残る 11 葉: `hreadyB`, `hpresRepAt`, `hshape`, `hstage`, `hended`, `hlastMatch`,
`hlastMismatch`, `hmismatch`, `hfound`, `hfoundBg`, `hfoundReplay`, `hstr`。

### `hstage` は再切り出し案件（測定）

`GalilFoundStageInv` のヘッダ自身が書いている通り、`ReplayStageInv` は
`MInv` ＋ `SearchReady` を持つ**任意の** `(c, s)` を量化しており、その形では
**証明不能**。`hsc` や `H_advanceT` と同じ再切り出し案件で、grind する義務ではない。

**最上位は変わらず 4 前提**（`hSP` `hor` `hC` `hpack`）。計画書 §10.5 は未達。

---

## 2026-09-19 `hSP` の残差は `hor` の found 経路の葉の**中**にあった — 2 つの壁は 1 つ

**全体 build 成功（EXIT=0、エラー 0、sorryAx 0）・標準公理のみ・無条件 PAL は未完。**

### 発見

`hSP` に残った 2 点（`RoundSeg`＝1 ラウンドの射影、最初のラウンド）は
**既に found 経路側で述べられていた**。`CloseoutWatchRound5.ShiftRoundC`
（`:328`、**NAMED (open)**）は、fuel を使い切ったか guard が立っている
live watch 着地について

```
WatchSeg → 終端不一致 → shiftGuard → beginShift → ChainShiftRun →
  Entry raw org (toOnly (shift 後の状態) v) → Rounds … → ScanSeg … → break
```

を一括で主張する。つまり**最初のラウンドの原点と後続ラウンドの両方**を含む。

**`hSP` のラウンド組み上げと `hor` の `hfound` 系は同じ named leaf であり、
独立した 2 つの問題ではない。**

### 新規（`CloseoutOriginRounds`）— 連結を定理にした

| 名前 | 内容 |
|---|---|
| `originAt_of_entry` | 状態での `Entry` は**そのまま** `OriginAt`（watch は状態で一意なので側条件なし） |
| `originAt_of_rounds` | `Entry` ＋ 制御側 `Rounds` から終端での `OriginAt`（`rounds_lift` → `rounds_origin`。座標は `m*h` 増えるので `radius + 2 ≤ center` は保たれる） |
| `round_of_rounds` | ↑と `round_of_originAt` の合成。**`ShiftRoundC` の `Entry` ＋ `Rounds` が配るもの**：全ラウンド開始での `RoundScan` と `ReadsInv` |

すべて標準 3 公理のみ。

### 残差の全体像（更新）

| 最上位前提 | 残差 |
|---|---|
| `hSP` | `ShiftRoundC` の中身（`Entry` ＋ `Rounds` ＋ `ScanSeg`）。連結は `round_of_rounds` で証明済み |
| `hor` | `h_oracle_of_leaves''` の 13〜14 葉。最大は `hfound`/`hfoundBg`/`hfoundReplay` ← **同じ `ShiftRoundC` 系** |
| `hC` | `H_realizeLIMW'`（局所機械の実現） |
| `hpack` | `ChainSide` の残り（`repV`/`repVmid`/`scanBound`/`marks`） |

**`hSP` と `hor` は 1 つの壁に統合された。** 残る独立な壁は
`ShiftRoundC` 系 ＋ `hC` ＋ `hpack` の 3 つ。

**最上位は変わらず 4 前提**（`hSP` `hor` `hC` `hpack`）。計画書 §10.5 は未達。

---

## 2026-09-19 `hSP` の残差を 2 点に確定 — ラウンド区間と最初のラウンド

**全体 build 成功（EXIT=0、エラー 0、sorryAx 0）・標準公理のみ・無条件 PAL は未完。**

### 3 ターンの測定の結論（検証済み）

| 範囲 | 状態 |
|---|---|
| ラウンド**内** | **閉じた**。witness の `n` はラウンドの `used`、`RoundScan.fresh` が `used < 2h` を与え、`encoded_of_sweptOff` / `advance_of_sweptOff` が周期性なしで予測と前進を出す |
| shift 相 | witness は**生き延びる**（`sweptOff_shift` / `sweptOff_shiftOne`、`Offset` は period tape と `broken` だけを要求する）。座標は生き延びない |
| ラウンド**境界** | 原点の再アンカーは**不可約**。古い原点の `SweptOff` は予測を `2h` 左の index で述べ、`period_window` は 1 段だけ橋渡しする。ラウンド `m` には `m` 段必要で、それはまさに `rounds_origin` が `CompareRounds` 上で回している帰納 |

### 新規（`CloseoutRoundSeg`）

```
def RoundSeg (w) (s s' : GalilVM) : Prop :=
  ∀ wch wch', s.chain = .watch wch → s'.chain = .watch wch' →
    periodLength wch' = periodLength wch ∧
    CompareRounds (periodLength wch) (toOnly s wch) 1 (toOnly s' wch')

theorem originAt_next_of_roundSeg (hO : OriginAt w s) (hR : RoundSeg w s s')
    (hch) (hch') : ∃ C R, RoundScan w C R (periodLength wch') 0 s' wch' ∧
                            ReadsInv w C R (periodLength wch') 0 wch'

theorem originAt_of_roundSeg … : OriginAt w s'
```

**両半分が同じ座標で同時に出る** — `roundScan_entry` が round datum を、
`readsInv_of_entry` が sweep witness を。

また `sweptOff_shiftOne`（`chainShiftOne` は `period`/`forward`/`broken` を保ち
3 カウンタを減らす ＝ `Offset` 1 段）を証明。

### `hSP` の残差（確定、2 点）

| 義務 | 正本 | 内容 |
|---|---|---|
| `RoundSeg` | `GalilScaffoldTopRoundS.round_next` | 1 ラウンドの射影。`ScanSeg` ＋ 終端比較 ＋ shift から |
| `H_freshShift` / `H_fresh` | `GalilScaffoldTopFirstRound.first_round` | **最初の**ラウンド（前提約 25 個） |

どちらも**同種の作業**（制御 run の区間を `ReadOrigin` に組み上げる）で、
`hor` の `hfound`/`hfoundBg`/`hfoundReplay` と同じ系統。

**最上位は変わらず 4 前提**（`hSP` `hor` `hC` `hpack`）。計画書 §10.5 は未達。

---

## 2026-09-19 `SweptOff` はラウンド内で `ReadsInv` を完全に代替する、周期補題を窓全体に一般化

**全体 build 成功（EXIT=0、エラー 0、sorryAx 0）・標準公理のみ・無条件 PAL は未完。**

### ラウンド内では `SweptOff` だけで足りる

ラウンド内では witness の `n` が**そのまま**ラウンドの `used` で、
`RoundScan.fresh` が `used < 2h` を与えるので `origin_prediction_index`
（非巻き戻し版）が直接使える。周期性は不要。

| 名前 | 内容 |
|---|---|
| `encoded_of_sweptOff` | `SweptOff` ＋ `n < 2h` ＋ unbroken から `symbol = (encoded raw)[C+R+2−2h+n]?` |
| `advance_of_sweptOff` | **`H_advance` の結論を `SweptOff` から**（`sweptOff_consume` ＋ 非 terminal） |

つまり `ReadsInv` は `SweptOff` に完全に置き換えられる（`sweptOff_of_readsInv` は
片方向だが、`SweptOff` 側が真に弱く、かつ shift 相を生き延びる）。

### 周期補題を窓全体に一般化

`CloseoutAdvanceT.period_at_next`（`j = C+R+2` 固定）を任意の `j` に：

```
theorem period_window (hpal : PalAt x (C+h) (R+h)) (hnext : PalAt x (C+2h) (R+1))
    (hs : 2h ≤ R) (hp : 0 < h) (hroom : R+2 ≤ C)
    (hj1 : C + 2h − R ≤ j) (hj2 : j ≤ C + R + 2h) :
    x[j − 2h]? = x[j]?
```

`C+2h` について鏡映 → `C+h` について鏡映。`hj1` は `C+2h−R−1` ではなく
`C+2h−R` でないと 2 回目の鏡映が半径を 1 超える（omega が正しく拒否した）。
利用域は `2h ≤ R` より `j = C+R+2` も `C+R+3` も内側。

### 残差の形（測定確定）

ラウンド**内**は閉じた。ラウンド**境界**では witness は `sweptOff_shift` で運ばれるが
座標 `(C,R) → (C+h,R+h)` の再アンカーが要る。`ShiftInv` は座標側を既に持っており
（`roundScan_of_shiftInv` が新ラウンドの `pred` を `ShiftInv.pred` から出す）、
`period_window` が符号語側の周期を与える。残るのは両者を噛み合わせる配線と、
**最初のラウンド**（`H_freshShift` / `H_fresh` = `first_round` の組み上げ、前提約 25 個）。

**最上位は変わらず 4 前提**（`hSP` `hor` `hC` `hpack`）。計画書 §10.5 は未達。

---

## 2026-09-19 `SweptOff` — sweep witness を `Offset` 形にして shift 相を生き延びさせた

**全体 build 成功（EXIT=0、エラー 0、sorryAx 0）・標準公理のみ・無条件 PAL は未完。**

### 前エントリの結論を訂正（良い方向に）

前エントリで「原点はラウンド単位で運ばれる。per-tick の束に per-round の step を
接ぐ配線が必要で、粒度が違う。これが `hSP` の残り本体」と書いた。
**ラウンド単位の再構築は不要だった。**

`ReadsInv` が壊れるのは witness を**等式**で述べているせい。ところが
「period tape と `broken` は同じ、カウンタは定数差」という関係は開発側に既にあり
（`ReadOrigin.Offset`）、その代数も揃っている：

| 補題 | 場所 | 内容 |
|---|---|---|
| `Offset.of_eq` | `GalilScaffoldChainReadOrigin:28` | 等式は `Offset 0` |
| `Offset.consume` | `:32` | 両側 1 consume で `k` 不変 |
| `Offset.run` | `:46` | 継続全体で `k` 不変 |
| `Offset.trans` | `:53` | offset は加法的 |
| `Offset.shift` | `:60` | `n` 歩の `ChainShiftRun` は `k` を `n` ずらす |

### 新規（`CloseoutSweptOff`）

```
def SweptOff (raw) (C R h n : ℕ) (w : State) : Prop :=
  ∃ (o : ReadOrigin raw) (extra : List (Fin 3)) (k : ℤ),
    o.center = C ∧ o.radius = R ∧ o.interior.length + 1 = h ∧ extra.length = n ∧
    Offset k w.machine.control
      (run (ready o.token o.interior o.boundary) (o.pre ++ extra))
```

| 名前 | 内容 |
|---|---|
| `sweptOff_of_readsInv` | `ReadsInv` から（`Offset.of_eq` + `Offset.shift o.shiftRun o.offset` + `Offset.run` + `Offset.trans`） |
| `sweptOff_consume` | consume で `n ↦ n+1`（`Offset.consume`） |
| `sweptOff_shift` | **shift 相を生き延びる**（`Offset.shift`、`n` は不変） |
| `symbol_of_sweptOff` | 予測は参照 run から読める（`Offset.prediction` は `period` の等式そのもの） |
| `bounce_of_sweptOff` | 予測の `bounce` index、**長さの上界なし**（`successful_prediction`） |

すべて標準 3 公理のみ。

### これが `H_readsShift` を消す

witness をラウンド境界で作り直す必要がなくなり、**運ばれる**。
`ReadsRound` を `SweptOff` 基底に置き換えれば `H_readsShift` は消える。
`H_advance` / `H_advanceT` も `bounce_of_sweptOff` + `origin_prediction_index`
（非巻き戻し）／mod 形（巻き戻し）から出る — どちらも既に証明済みの部品。

### `hSP` の残差（更新）

| 義務 | 状態 |
|---|---|
| `H_freshShift` / `H_fresh` | `OPEN`。**同じ義務**。内容は `GalilScaffoldTopFirstRound.first_round`（前提約 25 個）。最初のラウンドの原点構成 |
| `H_readsShift` | `REFORMULATED`（`SweptOff` 基底へ）。配線待ち |

**最上位は変わらず 4 前提**（`hSP` `hor` `hC` `hpack`）。計画書 §10.5 は未達。

---

## 2026-09-19 `H_readsShift` の構造的原因を特定 — 原点は tick でなく**ラウンド**単位で運ばれる

**全体 build 成功（EXIT=0、エラー 0、sorryAx 0）・標準公理のみ・無条件 PAL は未完。**

### 測定

`CloseoutPackRun37.ReadsInv` は sweep witness を**等式**で述べている：

```
w0.machine.control = GalilScaffoldChainSweep.run o.shifted.machine.control extra
```

ところが `chainShiftOne`（`GalilScaffoldChainInputSupply:1481`）は
`distance`/`boundary`/`last` を減らすので、**shift 相でこの等式は壊れる**。
残るのは弱い `Offset`（period tape と `broken` は同じ、カウンタは定数差）だけで、
それがまさに `ReadOrigin.offset` が記録しているもの。これが `H_readsShift` の
構造的原因。

### 正しい担い手は既に一段上にある

| 補題 | 場所 | 内容 |
|---|---|---|
| `Entry raw o s` | `GalilScaffoldChainReadOrigin:976` | ラウンド開始での原点データ。`machine : s.watch.machine = o.shifted.machine` を含む |
| `rounds_origin` | `:1010` | `Entry raw o s → CompareRounds h s m s' → ∃ o', Entry raw o' s' ∧ o'.center = o.center + m*h ∧ o'.radius = o.radius + m*h` |
| `roundScan_entry` | `GalilRoundPeriod:327` | `Entry → RoundScan raw o.center o.radius h 0` |
| `rounds_lift` | `GalilScaffoldTopRounds:65` | 制御側の `Rounds` が `CompareRounds` に射影される |

**原点は tick 単位でなくラウンド単位で運ばれる**。`m = 1` で `rounds_origin` は
ちょうど次ラウンドの座標 `(C + h, R + h)` に着く — `roundScan_of_shiftInv` が
数値的に作る対と同じ。per-tick の不変量（`ChainRound`/`ShiftRound`）が数値を運び、
`Entry` が原点を運び、両者はラウンド境界で結ばれる。

### 新規（`CloseoutOriginAt`）

| 名前 | 内容 |
|---|---|
| `OriginAt w s` | 「watch している chain は必ずある read origin のラウンド開始にいる」を単一状態の場に |
| `readsInv_of_entry` | `Entry.machine` から `ReadsInv w o.center o.radius h 0 wch`（`extra = []`） |
| `round_of_originAt` | `OriginAt` から `RoundScan` と `ReadsInv` を**同じ `(C,R)` で**同時に |
| `originAt_next` | ラウンド境界の step（`rounds_origin` を `m = 1` で） |

### 残る作業の形（測定確定）

束を `ReadsRound` から `OriginAt` へ再基底化すれば `H_readsShift` は消える。
ラウンド境界の step は `originAt_next`（証明済み）。**残るのは最初のラウンドだけ**
（`H_freshShift` / `H_fresh`、内容は `GalilScaffoldTopFirstRound.first_round`、
前提約 25 個）。

再基底化には `CompareRounds h _ 1 _` をラウンド完了時に供給する必要があり、
これは `round_next`/`rounds_lift`（制御側の 1 ラウンド分の Steps から射影）。
つまり per-tick の束に per-round の step を接ぐ配線が必要で、粒度が違う。
これが `hSP` の残り本体。

**最上位は変わらず 4 前提**（`hSP` `hor` `hC` `hpack`）。計画書 §10.5 は未達。

---

## 2026-09-19 `RoundBundle` — `hSP` の生産経路を組み上げて残差をコンパイラに検証させた

**全体 build 成功（EXIT=0、エラー 0、sorryAx 0）・標準公理のみ・無条件 PAL は未完。**

ここまで「残差は N 個」と書いてきたのは**主張**であって検証ではなかった。
5 つの場を 1 つの構造体にまとめ、tick を組み上げて型チェックさせた。

```
structure RoundBundle (w) (c : Control) (s : GalilVM) : Prop where
  chainRound : ChainRound w c s
  readsRound : ReadsRound w c s
  shiftRound : ShiftRound w c s
  periodShape : PeriodShape s
  noReplay   : NoReplayWatch c s

theorem roundBundle_tick (hB : RoundBundle w c s) (hinv : ChainPosInv2 w c s)
    (hci : CopyIdle s) (hSh : H_readsShift w c s) (hF : H_freshShift w s t)
    (h : Tick … ⟨c,s⟩ ⟨c',t⟩) : RoundBundle w c' t

theorem shiftPal_of_roundBundle (hm) (hr) (hB : RoundBundle w c s)
    (hcan : canRight s.right)
    (hfresh : s.periodOnly = false → ShiftPal …) : ShiftPal …

theorem roundBundle_steps …   -- run 版
```

**`H_shiftDone` は入力でない** — 束自身の `ShiftRound` から
`h_shiftDone_of_shiftRound` で出る。これが組み上げて初めて確認できたこと。

### `hSP` の残差（コンパイラが検証した形）

| 義務 | 状態 |
|---|---|
| `H_readsShift` | `OPEN`。`ReadsInv` を shift 相を通す（`ShiftInv` に sweep witness を足す） |
| `H_freshShift` | `OPEN`。fresh chain の初回 shift |
| `H_fresh` | `OPEN`。`H_freshShift` と**同じ義務**（`shiftPal_of_readOrigin` の `periodOnly = false` 分岐） |
| `ChainPosInv2` | 主経路が既に運んでいる（`ChainPack.inv`） |
| `CopyIdle` | 既存の `LPackM` 系 tick 補題が既に `c.mode = Mode.shift → CopyIdle s` として threaded。新規ではない |
| `canRight s.right` | `ChainPack` から出る（`repR` + `scanBound` + `canRight_of_position_bound`） |

### `H_freshShift` / `H_fresh` の正本を測定

内容は `GalilScaffoldTopFirstRound.first_round`（登録済み・証明済み）。これは
found 探索から最初の shift までを通して

```
(∃ k, Steps … ⟨c0,v0⟩ ⟨…, e⟩) ∧ e.chain = .watch v ∧ zero v.lag = true ∧
  e.periodOnly = true ∧ ∃ o' : ReadOrigin raw, Entry raw o' (toOnly e v) ∧
    o'.interior.length+1 = h ∧ o'.center = position cen ∧ o'.shifts = 0 ∧ …
```

を与える。ただし前提が約 25 個（found 探索 `SafeQuanta`、DP の `Result`/`Candidate`、
watch 区間 `WatchSeg`、終端比較、shift の `ChainShiftRun`、prep の credit 履歴）。
`ShiftInv` への対応は座標 `C = o.center − h`、`R = o.radius − h` で合う
（`pal` が found 中心の palindrome、`origin` が found 中心の不一致、
`pred` が `origin_prediction_index` の `extra = []`）。

**これは `hor` の `hfound`/`hfoundBg`/`hfoundReplay` と同族の「found 経路の組み上げ」**
であり、残る最大の作業。前提を run から放電する配線が本体。

**最上位は変わらず 4 前提**（`hSP` `hor` `hC` `hpack`）。計画書 §10.5 は未達。

---

## 2026-09-19 `H_advanceT` を再切り出して配線 — `ShiftRound` の tick 残差は `H_freshShift` 1 つ

**全体 build 成功（EXIT=0、エラー 0、sorryAx 0）・標準公理のみ・無条件 PAL は未完。**

### 再切り出し（`ShiftPal` と同じ形）

`CloseoutPackRun37.H_advanceT` は `Good w0` 相当のデータを持たず、consume が失敗すると
period tape が動かないので偽だった。消費者（`shiftRound_tick` の `scan_shift` 分岐、
唯一の使用箇所）が持っているデータを定義に入れた：

```
def H_advanceT (w : List (Fin 2)) (c : Control) (s : GalilVM) : Prop :=
  c.mode = Mode.scan → c.replaying = false → s.periodOnly = true →
  ∀ C R used w0, RoundScan w C R (periodLength w0) used s w0 →
    singlePositive s.cycle = true →
    canRight s.right →
    symbol w0.machine.control.period.focus = read (right s.right) →
    symbol (immediate w0).machine.control.period.focus = (encoded w)[C + R + 2]?
```

`canRight s.right` は tick の `hav`（`:353`）、guard の予測は `hpred`（`:420`）で、
どちらも呼び出し点（`:430`）のスコープ内。モード前提は `ReadsRound` と同形にするため
（Run37 は `CloseoutRoundReads` を import できない — 逆向きの依存がある）。

### `Good` の第 2 成分は `RoundScan` + `canRight right` から出る

`sym_of_guard`: `GalilRoundPeriod.RoundScan.break_of_match` の手順をそのまま使う。
`canRight v.right` が scan の右ヘッドを bound し、`CaughtScan.aligned` がその bound を
verifier へ運び（`canRight_of_bound`）、2 つの表現が同じ記号を読む。予測が `some a` で
あることは `hI.pred` を terminal の index `C+R+1` に落として `getElem?_eq_getElem`。

**`canRight w0.machine.verifier` は新しい義務ではなかった** — `RoundScan` と
`canRight v.right` から導ける。

### 新規（`CloseoutAdvanceT`）

| 名前 | 内容 |
|---|---|
| `sym_of_guard` | guard での consume 成功（`Good` の第 2 成分） |
| `advanceT_of_guard` | `H_advanceT` の結論。`terminal_palindrome` が `palNext` を、`sym_of_guard` が consume を供給 |
| `h_advanceT_of_readsRound` | **`H_advanceT` は運ばれた `ReadsRound` から出る定理** |
| `shiftRound_tick_A` | `shiftRound_tick` の `H_advanceT` を除去。残差は `H_freshShift` だけ |

`H_advanceT`: `REFORMULATED` ＋ `INTEGRATED`（`ReadsRound` から供給、
`shiftRound_tick_A` で利用、`shiftRound_tick` の入力から消えた）。

### `hSP` の残差（現在）

| 義務 | 状態 |
|---|---|
| `H_freshShift`（fresh chain の初回 shift、`periodOnly = false`） | `OPEN`。内容は `GalilScaffoldTopFreshEntry` |
| `H_fresh`（`shiftPal_of_readOrigin` の `periodOnly = false` 分岐） | `OPEN`。同じく `GalilScaffoldTopFreshEntry` |
| `H_readsShift`（`ReadsInv` を shift 相を通す） | `OPEN`。`ShiftInv` に sweep witness を足せば出る |
| `CopyIdle`（`shiftRound_tick` の入力） | 未評価 |

運ぶ場（`ChainRound`・`ReadsRound`・`ShiftRound`・`PeriodShape`・`NoReplayWatch`）のうち
`PeriodShape`/`NoReplayWatch` は tick 保存済み、`ChainRound`/`ReadsRound`/`ShiftRound` の
tick はそれぞれ `H_shiftDone`（← `ShiftRound`）／`H_readsShift`／`H_freshShift` 1 つずつ。

**最上位は変わらず 4 前提**（`hSP` `hor` `hC` `hpack`）。計画書 §10.5 は未達。

---

## 2026-09-19 `H_advanceT` の数学的内容を証明（最重量と測定した葉）

**全体 build 成功（EXIT=0、エラー 0、sorryAx 0）・標準公理のみ・無条件 PAL は未完。**

### 前エントリの測定を訂正

前エントリで「`H_advanceT` は符号語が index `C+R+2` まで周期 `2h` を持つことを要求し、
原点の不一致 `C+R+1` の窓の外」と書いた。**窓の見積もりが誤りだった。**
`ShiftInv` は palindrome を **2 つ**持つ：`pal : PalAt x (C+h) (R+h)`（ラウンドの
caught scan）と `palNext : PalAt x (C+2h) (R+1)`（`terminal_palindrome`）。
`C+R+2` をまず `C+2h` について鏡映し、次に `C+h` について鏡映すると

```
C+R+2  ↦  2(C+2h) − (C+R+2) = C+4h−R−2  ↦  2(C+h) − (C+4h−R−2) = C+R+2−2h
```

で `C+R+2−2h` に着く。どちらの鏡映も `2h ≤ R` より半径の内側。

### tape 側：巻き戻しは障害ではなく本質

`GalilScaffoldChainPrediction.continued_prediction` は予測を
`bounce[(pre.length + extra.length) % (2*(xs.length+1))]?` として与え、
**`extra.length` に上界を課さない**。必要な `SamePrediction` は
`ReadOrigin` が `Offset.shift org.shiftRun org.offset` で持っている。
よって `extra.length = 2h` の予測は `extra.length = 0` の予測に等しく、
後者は `origin_prediction_index` が `x[C+R+2−2h]` に変換できる。

### 新規（`CloseoutAdvanceT`）

| 名前 | 内容 |
|---|---|
| `origin_prediction_bounce` | 長さの上界なしの `bounce` 形（`continued_prediction` に `ReadOrigin` の `Offset` を食わせる） |
| `origin_prediction_wrap` | `extra.length = 2h` で `x[org.center + org.radius + 2 − 2h]` |
| `period_at_next` | `x[C+R+2−2h] = x[C+R+2]`（鏡映 2 回） |
| `advanceT_of_readsInv` | `H_advanceT` の結論。入力は `RoundScan` + `ReadsInv` + `Good w0` + terminal + `palNext` |

すべて標準 3 公理のみ。

### `H_advanceT` は再切り出しが必要（測定結果）

`CloseoutPackRun37.H_advanceT`（`:148`）は `Good w0` を premise に持たない。
ところが consume が失敗すると `broken := true` になって period tape は**動かない**ので、
予測は `x[C+R+1]` のままになる。よって現在の形は**偽の疑いが強い**。

`Good w0`（`GalilScaffoldChainWatch:13`）= `canRight verifier ∧ ∃ a, symbol period.focus = some a
∧ read (right verifier) = some a`。shift 入口では shift guard が
`symbol wch.period.focus = read s'.right` を与え、`CaughtScan.aligned` が
`position verifier = position right` を与えるので第 2 成分は出る。第 1 成分
`canRight verifier` は `ChainPack.repVmid` 系から。

**対処方針**: `ShiftPal` と同じく、消費者（`shiftRound_tick` の `scan_shift` 分岐、
guard が手元にある）が持っているデータを `H_advanceT` の定義に入れる。
これは `REFORMULATED` で、前提数は増えない。

`H_advanceT`: `PROVED`（内容は `advanceT_of_readsInv`）＋ `REFORMULATED` 待ち（配線）。

---

## 2026-09-19 `hSP` の tick 機構が完成、残差は shift 相の受け渡し 1 点に

**全体 build 成功（EXIT=0、エラー 0、sorryAx 0）・標準公理のみ・無条件 PAL は未完。**

### `NoReplayWatch`: watch ＋ `periodOnly` なら replay 中ではない

**論証（コードを書く前）**: `replaying` が `true` に*上がる*のは fallback 出口と
`replayStart` だけで、どちらも `chain := .idle`。idle から watch に戻るには誕生が必要で
誕生は `periodOnly := false`。`periodOnly` を再び立てるのは `beginShiftVM` だけで、
それを発火する `scan_shift` tick は `hr : c.replaying = false` を持つ
（`GalilScaffoldTop:123`）。よって「`periodOnly = true` ∧ chain が watch ⇒
`replaying = false`」は tick 不変量。

`noReplayWatch_tick` を **23 形すべて、sorry なし**で証明した。

### `H_birthR` と `H_readsBirth` は空虚

`replay_false_of_tick`（同じ 23 形の場合分けで結論を `c` 側にしたもの）から
`h_birthR_vacuous` / `h_readsBirth_vacuous` が各 3 行。**`chainRound_tick` の
コピーは不要だった** — 空虚性を独立定理にして `hB` の位置に渡すだけで済む。

### `ReadsRound` の tick

`roundScan_unique`（`count` が `used` を、`rightPos`/`leftPos` が `C+R` と `C−R` を
決める。減算は `size`/`room` で安全）を使って `readsRound_tick` を証明。
watch を scan かつ `periodOnly` で着地させられる形は 3 つだけで、
`scan_wait`/`scan_count` は `internal_of_zero` で watch 状態が不変、
`scan_match` は `readsInv_immediate`、`shift_done` が `H_readsShift`。

### 到達点

```
theorem chainRound_tick_S (hCR : ChainRound) (hRR : ReadsRound) (hps : PeriodShape)
    (hn : NoReplayWatch) (hinv : ChainPosInv2) (hS : H_shiftDone) (h : Tick …)
    : ChainRound w c' t

theorem readsRound_tick_S (hCR) (hRR) (hps) (hn) (hinv)
    (hSh : H_readsShift) (h : Tick …) : ReadsRound w c' t

theorem shiftPal_of_readOrigin (hm) (hr) (hCR : ChainRound w c s)
    (hcan : canRight s.right) (H_fresh : periodOnly = false → ShiftPal …) : ShiftPal …
```

運ぶ場 5 つのうち **`PeriodShape` と `NoReplayWatch` は tick 保存済み**、
`ChainPosInv2` は主経路が既に運んでいる。`canRight` は `ChainPack` から出る。

### `hSP` の残差（この 3 ターンでの推移）

| 開始時 | 現在 |
|---|---|
| `ChainRound`, `WatchShift`（**偽**）, `H_matched`, `H_born`, `H_advance`, `BlockInv`, `H_birth`, `H_shiftDone`, `H_fresh` | `H_shiftDone` / `H_readsShift`（どちらも shift 相の受け渡し 1 点）, `H_fresh` |

`H_shiftDone` ← `h_shiftDone_of_shiftRound` ← `ShiftRound`（単一状態）。
その tick は `shiftRound_tick`、残り `H_advanceT`・`H_freshShift`。
`H_readsShift` は同じ受け渡しの `ReadsInv` 版で、`ShiftInv` に sweep witness を
足せば同時に出る。

**最上位は変わらず 4 前提**（`hSP` `hor` `hC` `hpack`）。計画書 §10.5 は未達。

---

## 2026-09-19 `H_birth` の「誕生」半分は `periodOnly` と両立しない — `ChainRound` の tick 残差が 2 つに

**全体 build 成功（EXIT=0、エラー 0、sorryAx 0）・標準公理のみ・無条件 PAL は未完。**

### 論証（コードを書く前に立てた見込み）

`H_birth` の第 2 の選択肢「source の chain は watch でないのに target はそう」は
`ChainStep` の構成子を読むと **`backDone` からしか**生じない
（`chainAt_false_watch`/`chainAt_true_watch` の `hnot` 分岐に残るのはその 1 つだけ）。
つまり source の chain は `.back`。ところが：

| 事実 | 出典 |
|---|---|
| `beginShiftVM` が `periodOnly := true` の唯一の writer、かつ `shiftGuardVM` ⇒ chain は `.watch` | `CloseoutPeriodOnlyRegression.shift_sets_periodOnly`、`GalilScaffoldTopGuards:24` |
| `.copy` への唯一の経路は誕生 `chainStart`、`afterBirth` は `periodOnly := false` | `GalilScaffoldTopSearch:78` |
| `.back` への唯一の経路は `.copy` からの `copyEnd` | `GalilScaffoldTopChainVM:59` |

よって「`periodOnly = true` → chain は `idle`/`watch`/`broken`」は tick 不変量で、
`.back` は排除される。

### 新規

| 名前 | ファイル | 内容 |
|---|---|---|
| `WatchLike` / `PeriodShape` | `CloseoutPeriodShape` | 上の不変量 |
| `watchLike_chainStep`/`chainMatched`/`chainTick`/`chainAt` | 同 | `ChainStep` の 7 構成子で `copy`/`back` の source が `False` になるので `cases h <;> first | exact hx | exact hx.elim | trivial` |
| `periodShape_tick` | 同 | **23 形すべて、sorry なし**。非 scan の相 tick は `fppLens`/`shiftLens`/`rewindLens` 越しなので `chain`/`periodOnly` を触らず `rfl`（`phase_case`）。`shift_one` は `chainShiftOne` で watch のまま、`shift_done` は VM 不変 |
| `periodShape_steps` | 同 | run 版 |
| `chainAt_false_back` / `chainAt_true_back` | `CloseoutBirthFree` | 誕生した watch の source は `.back`、ゆえに `¬ WatchLike` |
| `H_birthR` | 同 | `H_birth` の replaying 半分だけ |
| `chainRound_tick_B` / `chainRound_tick_BF` | 同 | `chainRound_tick_RR` を逐語コピーし、`hB` を消費する **4 行**だけ差し替え（3 つは誕生分岐で矛盾、1 つは `H_birthR`） |

`H_birth` の誕生半分: `PROVED`（空虚）。`BlockInv`: `INTEGRATED`（`ChainPosInv2` から）。

### `ChainRound` の tick 残差

```
theorem chainRound_tick_BF (hCR : ChainRound) (hRR : ReadsRound) (hps : PeriodShape)
    (hinv : ChainPosInv2) (hS : H_shiftDone) (hB : H_birthR) (h : Tick …) :
    ChainRound w y.ctl y.vm
```

運ぶ場 4 つ（`ChainRound`・`ReadsRound`・`PeriodShape`・`ChainPosInv2`）のうち
`PeriodShape` は tick 保存済み、`ChainPosInv2` は主経路が既に運んでいる。
残る意味的義務は **`H_shiftDone`**（→ `ShiftRound`、残り `H_advanceT`・`H_freshShift`）と
**`H_birthR`**（replay 終了時のラウンド datum）、および `ReadsRound` の tick 保存。

---

## 2026-09-19 `WatchShift` は 1 節しか使われていなかった、`BlockInv` は run に乗っていた

**全体 build 成功（EXIT=0、エラー 0、sorryAx 0）・標準公理のみ・無条件 PAL は未完。**

### `hws : WatchShift` → `hcan : canRight s.right`

`shiftPal_of_chainRound` は `CloseoutPackRun24.WatchShift` を取っていたが、
証明中の使用は **1 箇所** だけで、読んでいたのは

```
have hcan : canRight s.right := (hws hni s' hcmp wch hchain).2.1
```

つまり 6 節あるうちの `canRight x.vm.right` 1 節のみ。しかも `WatchShift` は
`WatchShiftG` と同じ理由で**偽**（`ChainStep.backDone` の生まれたての watch は
`distance = reset` なので、guard なしの target では `4·periodLength ≤ distance` を破る）。
偽の命題に依存していたことになる。

`hws` を `hcan : canRight s.right`（単一状態）に置換。`shiftPal_of_readOrigin` も同様。

`WatchShift` への依存: 主経路から**消滅**（`shiftPal_of_*` は唯一の利用者だった）。

### `BlockInv` は義務ではなかった

`chainRound_tick` の第 5 入力 `GalilBranchInvariants.BlockInv x.vm.chain` は
`CloseoutPackRun40.Coupled'` の場（`:79`）で、それは `CloseoutPackRun41.ChainPosInv2`
の `coupled` 場。主経路が既に運んでいる。`blockInv_of_chainPosInv2` は 1 行。

また `BlockInv` 自体は `GalilBranchInvariants` で完全に閉じている
（`blockInv_step` / `blockInv_matched` / `blockInv_tick` / `blockInv_steps`、
`BlockInv .idle = True`）。

### 結果

```
theorem shiftPal_of_readOrigin (hm : c.mode = Mode.scan) (hr : c.replaying = false)
    (hCR : ChainRound w c s) (hcan : canRight s.right)
    (H_fresh : s.periodOnly = false → ShiftPal centre place entry q first w s) :
    ShiftPal centre place entry q first w s

theorem chainRound_tick_free (hCR : ChainRound w x.ctl x.vm) (hRR : ReadsRound w x.ctl x.vm)
    (hinv : ChainPosInv2 w x.ctl x.vm)
    (hS : H_shiftDone …) (hB : H_birth w x.ctl x.vm y.vm)
    (h : Tick …) : ChainRound w y.ctl y.vm
```

### `hSP` の残差（更新）

| 義務 | 状態 |
|---|---|
| `ChainRound`（単一状態） | `OPEN`。tick は `chainRound_tick_free`、残り `H_shiftDone`・`H_birth` のみ |
| `ReadsRound`（単一状態） | `OPEN`。材料は `readsInv_immediate`（scan_match）と lag ゼロの `Internal.idle`（background） |
| `canRight s.right`（scan 時） | `ChainPack` から出る（`repR` + `scanBound` + `canRight_of_position_bound`） |
| `H_shiftDone` | `h_shiftDone_of_shiftRound` ← `ShiftRound`（単一状態）。tick は `shiftRound_tick`、残り `H_advanceT`・`H_freshShift` |
| `H_birth` | `OPEN` |
| `H_fresh` | `OPEN`。内容は `GalilScaffoldTopFreshEntry` |

`H_advanceT` の測定: 端末 consume の予測は period tape が巻き戻るので
`origin_prediction_index`（非巻き戻し版）が使えない。`continued_prediction` の mod 形
（`GalilScaffoldChainPrediction`）を使うと `bounce[(pre.length + 2h) % 2h] = bounce[pre.length % 2h]`
になり、結局 `(encoded raw)[C+R+2-2h]? = (encoded raw)[C+R+2]?`、つまり
**符号語が index `C+R+2` まで周期 `2h` を持つこと**を要求する。ところが原点の不一致は
`C+R+1` にあるので、その窓の外。`H_advanceT` は `hSP` 系で最も重い葉であり、
新しい周期の議論（新ラウンドの原点 `(C+h, R+h)` に対する周期）が必要。

---

## 2026-09-19 `H_advance` は既に解けていた — `CloseoutPackRun37` の在庫を読み落としていた

**全体 build 成功（EXIT=0、エラー 0、sorryAx 0）・標準公理のみ・無条件 PAL は未完。**

### 訂正: `hSP` の残差を過大に見積もっていた

前エントリで「`ChainRound` の tick 残差は `H_advance`/`H_shiftDone`/`H_birth` + `BlockInv`」
と書いたが、`CloseoutPackRun37`（登録済み・build 済み）を読むと **`H_advance` と
`H_shiftDone` はどちらも producer を持っていた**。

| 残差 | producer | 場所 |
|---|---|---|
| `H_advance` | `h_advance_of_readsInv`（`GalilGoodLag.origin_prediction_index` を 1 つ長い継続で適用） | `CloseoutPackRun37:483` |
| ↑の入力 `ReadsInv` の step | `readsInv_immediate` | `CloseoutPackRun37:517` |
| `H_shiftDone` | `h_shiftDone_of_shiftRound`（`ShiftInv` を shift 相を通して運ぶ） | `CloseoutPackRun37:130` |

これは「`hor` は producer ゼロ」と誤断した時と同じ失敗（型名だけを grep して、
その義務を解決するモジュールのヘッダを読まなかった）。**`Closeout*` の残差を評価する
前に、同族ファイルのヘッダ（`/-! ... -/`）を読むこと。**

### 新規

| 名前 | ファイル | 内容 |
|---|---|---|
| `ReadsRun` / `ReadsRound` | `CloseoutRoundReads` | `ReadsInv` をその状態の全ラウンドについて閉じた単一状態の場。`ReadsRound` は `ChainRound` と同じ前提（scan・非 replay・`periodOnly`）を持つ |
| `h_advance_of_readsRun` | `CloseoutRoundReads` | `H_advance` を `ReadsRun` から（1 行） |
| `chainRound_tick_RR` | `CloseoutRoundReads` | `chainRound_tick` の 200 行を逐語コピーし、`hA` を消費する **1 行だけ** を `h_advance_of_readsInv hI (hRR hm hrep hpo w0 hw0 C R used hI) hg hend` に差し替え |

`H_advance`: `INTEGRATED`（`ReadsRound` から供給、`chainRound_tick_RR` で利用、
`chainRound_tick` の入力から消えた）。数学（`origin_prediction_index`）は既に閉じていて、
欠けていたのは `ReadsInv` が言及する `(C, R, used)` を `H_advance` の量化と噛み合わせる
帳簿だけだった。

### `hSP` の残差（更新）

| 義務 | 状態 |
|---|---|
| `ChainRound`（単一状態、`CloseoutPackRun31:183`） | `OPEN`。tick は `chainRound_tick_RR` が 20 形を閉じ、残り `H_shiftDone`（→ `ShiftRound`）、`H_birth`、`BlockInv` |
| `ReadsRound`（単一状態） | `OPEN`。tick 保存の材料は `readsInv_immediate`（scan_match）と lag ゼロでの `Internal.idle`（background） |
| `ShiftRound`（単一状態、`CloseoutPackRun37:88`） | `OPEN`。tick は `shiftRound_tick`、残り `H_advanceT`（巻き戻し点の予測。材料は `GalilScaffoldChainPrediction.continued_prediction` の mod 形）と `H_freshShift` |
| `WatchShift`（単一状態、`CloseoutPackRun24:45`） | `OPEN` |
| `H_fresh`（`periodOnly = false` の初回 shift） | `OPEN`。内容は `GalilScaffoldTopFreshEntry` |

---

## 2026-09-19 `ShiftPal` は過剰量化だった — `shiftPal_of_chainRound` の名前付き分岐が 2 → 0

**全体 build 成功（EXIT=0、エラー 0、sorryAx 0）・標準公理のみ・無条件 PAL は未完。**
`pal_in_peg_final37` は **4 前提**（実測: `#check` で 4 引数、`#print axioms` は標準 3 公理）。

### 何が起きていたか

`CloseoutPackRun29.ShiftPal` は比較先 `s'` を「`compare s s'` かつ `s'.chain = .watch wch`
かつ `shiftGuardVM s'`」で量化していたが、**`¬ matched s'` を落としていた**。
一方 `Tick.scan_shift`（`GalilScaffoldTop`）は `hmt : ¬ matched s'` を要求するので、
matched な `s'` で guard が立つ場合はフレームが一切使わない。
`ShiftPal` の唯一の消費者 `shiftEntry_of_guard`（`CloseoutPackRun29:108`、grep で確認：
適用箇所は全体で 1 箇所のみ）も `hmt` を持っている。

つまり `ShiftPal` は消費者が必要としない強さを要求しており、その差分がそのまま
`shiftPal_of_chainRound` の名前付き分岐 `H_matched` になっていた。

### 対処

`ShiftPal` の定義に `¬ (galilFrameS …).matched s' →` を追加（`CloseoutPackRun29:82`、
**定義を直接編集**）。`ShiftPal` は 44 箇所で言及されるが、ほとんどは
`hSP : ScanNR x → ShiftPal … x.vm` を素通しするだけなので、修正が必要だったのは
消費者 1 箇所（`hSP _ hcmp hmt wch …`）と産出側 2 箇所だけ。全体 build で確認。

`H_matched` は `a = true` 分岐で `matched s'` を構成していたので、そのまま `absurd … hmt`。

### `H_born` も空虚だった

`H_born`（比較中に誕生した chain）は `ChainStep.backDone` の生まれたての watch で、
**phase = 0**（`CloseoutPackRun37.chainAt_false_born`）。ところが `shiftGuardVM`
（`GalilScaffoldTopGuards:24`）は **phase = 4** を要求する。よって guard を通れない。
`CloseoutPackRun37` は `CloseoutPackRun31` を import するので循環を避けて Run31 内に
`chainAt_false_born` を複製した（証明は `chainAt_false_watch` と同構造）。

これは `hws`/`hsl` を**反証**したのと同じ「生まれたての watch」の観察だが、今回は
逆向きに効いて分岐を**空虚化**した。

### 結果

```
theorem shiftPal_of_chainRound (hm : c.mode = Mode.scan) (hr : c.replaying = false)
    (hpo : s.periodOnly = true) (hCR : ChainRound w c s)
    (hws : WatchShift centre place entry q first w ⟨c, s⟩) :
    ShiftPal centre place entry q first w s
```

名前付き分岐**ゼロ**。`shiftPal_of_readOrigin` も `H_fresh` 1 つだけになった。

`ShiftPal`: `REFORMULATED`（消費者が持つ `¬ matched` を定義に入れた。弱化なので
利用側は全て無修正で通る — 全体 build で確認）。
`H_matched` / `H_born`: `PROVED`（どちらも空虚）。

### `hSP` の残差（更新）

| 義務 | 場所 | 状態 |
|---|---|---|
| `ChainRound`（単一状態） | `CloseoutPackRun31:183` | `OPEN`。tick 保存は `chainRound_tick` が 20 形を閉じ、残り `H_advance`/`H_shiftDone`/`H_birth` + `BlockInv` |
| `WatchShift`（単一状態） | `CloseoutPackRun24:45` | `OPEN` |
| `H_fresh`（`periodOnly = false` の初回 shift） | `CloseoutPackRun31` | `OPEN`。内容は `GalilScaffoldTopFreshEntry` |

**注意**: これらを `ChainPack` の場に移すだけなら台帳規約どおり `OPEN` のまま。
最上位の前提数は 4 → 3 になるが、証明義務は減らない。

---

## 2026-09-19 `hme` は `hpack` の中にあった — **4 前提**

**全体 build 成功（EXIT=0、エラー 0、sorryAx 0）・標準公理のみ・無条件 PAL は未完。**
`pal_in_peg_final37`（`CloseoutFinalW4`）は **4 前提**（`hSP`, `hor`, `hC`, `hpack`）。

### まず、自分の誤りの訂正（`INTEGRATED` ではなく設計誤認）

直前に「`BigPack2MG7W''` に 5 場（`cpack`/`wpack`/`lenNonneg`/`walkerPin`/`walkerOrigin`）
を足して `bigPack2MG7W''_tick` で保存すれば 4 前提になる」と書いた。**この配線は前提を
減らさない。** 設計して測った結果：

- `CloseoutPackRun17.wpack_tick` は着地の `hwin : c'.mode = .copy → WindowInOrigin t` を
  **毎 tick 入力として要求する**（:147）。よって `WPack` を run に沿って運ぶには
  run レベルの `hwin` が必要で、これは `hme` と同じ 1 前提。
- `hwin` を場にして tick で保存する道は**閉じている**。`scan → copy` は `scan_fallback`
  一択で、着地の `fpp.walker` は `beginFallbackVM p s1 s2` の `walker := p`
  （`GalilScaffoldChainFallback:404`）。`sharedC` は `bf` に `beginFallbackVM'`
  （`= ∃ p, beginFallbackVM p`、`GalilScaffoldTopGuards:38`）を入れるので `p` は
  **存在量化されたまま**で、`Tick` は `p` を一切縛らない。これは CLAUDE.md §2 の
  モデル欠陥 (e)「`beginFallbackVM'`（着地場所）が非関数的」そのもの。

つまり `hme` は「`Fair` を足す」か「モデルを変える」以外では**単独では**落ちない。

### 正しい道：`hme` の内容は既に `hpack` が配っていた

`hme` の使用箇所は `packRunR_MW` の中の **2 箇所だけ**で、どちらも産物は `MarksInv'`。

| 箇所 | 用途 |
|---|---|
| `CloseoutOracleW:170` | `marksInv'_of_run … hme` — run 起点の `MarksInv'` |
| `CloseoutOracleW:205` | `bigPack2MG7W''_tick … hme` — 1 tick 先の `MarksInv'` |

そして `MarksInv' first c s` は **`ChainPack` の場**（`CloseoutChainPack:281` `marks`）で、
`hpack` が `ChainPosInv2` を満たす全状態で配っている。前提 `ChainPosInv2` は：

- 起点：`InvLPC` は chain idle を強制（`CloseoutShiftLocalFree.chainIdle_of_invS`）→
  `CloseoutPackRun41.chainPosInv2_of_idle`。
- run 上：`CloseoutShiftS2.chainPosInv2_steps` が運ぶ。必要な 4 供給
  `H_bgP2`/`H_matchP2`/`H_shiftEntry2`/`H_shiftDoneRad2` は **`final36` が既に `hpack` から
  導出している**（`h_bgP2_of_chainPack`, `h_matchP2_of_target`, `h_shiftEntry2_of_target`,
  `h_shiftDoneRad2_of_chainPack`）。

よって `hme` の代わりに現れるものは**ない**。

### 新規

| 名前 | ファイル | 内容 |
|---|---|---|
| `bigPack2MG7W''_tick_M` | `CloseoutMarksPack` | `bigPack2MG7W''_tick` の `hme` を着地の `MarksInv'` 入力に置換（残り 60 行は逐語） |
| `packRunR_MWP` | `CloseoutMarksPack` | `packRunR_MW` の `hme` を 4 供給 + `hpk` に置換、`MarksInv'` は全部 `ChainPack.marks` |
| `pal_in_peg_final37` | `CloseoutFinalW4` | 4 前提 |

`hme`: `INTEGRATED`（`hpack` から供給、主経路で `hme` は消滅）。

### 残り 4 前提

| 前提 | 内容 | 状態 |
|---|---|---|
| `hSP` | scan 状態の `ShiftPal`（周期と `PalAt`、Galil の move 補題） | `OPEN` |
| `hor` | `CycleOracleMC3`（`h_oracle_of_leaves''` の 13〜14 葉、最大は `hfound`/`hfoundBg`/`hfoundReplay`） | `OPEN` |
| `hC` | `H_realizeLIMW'`（局所機械の実現） | `OPEN` |
| `hpack` | `ChainPosInv2 → ChainPack`。残差は `ChainSide`（`CloseoutChainPack:241`）。`lagCan`/`backLag` は `CloseoutLagAll.LagAll` で閉、`walkerPin` はモデル欠陥 (e) により `Fair` 必須、残りは `repV`/`repVmid`/`scanBound` | `OPEN` |

計画書 §10.5（前提ゼロ）は**未達**。

---

## 2026-09-19 `Fair` 依存は 2 箇所とも「1 つの pin」だった

**全体 build 成功（EXIT=0、エラー 0、sorryAx 0）・標準公理のみ・無条件 PAL は未完。**
`pal_in_peg_final36` は **5 前提**（`hSP`, `hme`, `hor`, `hC`, `hpack`）。

`hme` 除去の最後のブロッカーは「`hwin`（`WindowInOrigin` at copy）の producer が
`FairSteps` を要求する」ことだった。実際に読むと、`Fair` を使う 2 つの tick
補題はどちらも **1 箇所でしか** `Fair` を参照せず、その中身は
状態対についての等式ひとつだけだった。

| 補題 | `Fair` 参照 | 中身 | pin 版 |
|---|---|---|---|
| `CloseoutPackRun25.windowInOrigin_tick`（:80） | `fallbackPlace` 1 箇所（`scan_fallback` 分岐） | `y.vm.fpp.walker = y.vm.walker` | `CloseoutWinTick.windowInOrigin_tick_pin` |
| `CloseoutPackRun28.walkerInv_tick`（:308） | `keepsSearchCursor` 1 箇所（`init` 分岐） | `t.walker = s.walker` | `CloseoutWalkerTick.walkerInv_tick_pin` |

どちらも `Fair entry delay ⟨c,s⟩ ⟨c',t⟩` を、その 1 つの等式を述べる仮説に
置き換えるだけで通った（196 行の場合分けはそのまま）。

**これで `WindowInOrigin` / `WalkerInOrigin` の連鎖が `Fair` から完全に独立した。**

### `hme` 除去の材料（すべて揃った）

| `marks_steps` の入力 | 状態 |
|---|---|
| `h4 : first ≠ 4` | `first` 具体化で `decide`（`centreC`/`placeC` は `first` に依存しない） |
| `hfl : 0 ≤ value length` | **証明済み**（`CloseoutSpanTick.lenNonneg_of_span_radius`） |
| `hwin : WindowInOrigin at copy` | **分解済み**（`WalkerPin` ＋ `WalkerInOrigin`）＋ tick 保存が `Fair` 不要 |
| `CPack` / `WPack` / `MarksInv'` | `ChainPack` の場（`cpack_of_entry` / `wpack_of_mode` で起点は無料） |
| `MarksEntry'` の供給 | `marksEntry'_of_layout (chooseLayout_of_wpack h4 hW hm hs)` — `WPack` から |

**残る作業**: `BigPack2MG7W''` に `cpack` / `wpack` / `lenNonneg` / `walkerPin` /
`walkerOrigin` を場として足し、`bigPack2MG7W''_tick` で `cpack_tick` /
`wpack_tick` / `windowInOrigin_tick_pin` / `walkerInv_tick_pin` により保存する。
それで `hme` が落ちて **4 前提**になる。

### 教訓（`Fair` について）

「producer が `Fair` を要求する」を見て「`Fair` を run に通す構造変更が必要」と
判断したのは早すぎた。**`Fair` の 3 clause はそれぞれ状態対についての等式で、
補題が実際に使うのはそのうち 1 つだけ**という場合がある。`Fair` を仮説から
外すには、使用箇所を数えてその clause だけを取り出せばよい。

## 2026-09-19 ⚠️ 重大な訂正 — `hor` は「producer ゼロ」ではない。13〜14 葉に分解済み

**全体 build 成功・標準公理のみ・無条件 PAL は未完。**

本セッションで繰り返し「`hor`（`CycleOracleMC3`）は producer がリポジトリに
1 つも無く、束への畳み込みでは原理的に届かない」と述べた。**これは誤り。**

### 実際の状況

`GalilOracleMC3.h_oracle_of_leaves''`（:335）が **14 葉**から `H_oracle` を出す:

`hpres`, `hshape`, `hbudget`, `hstage`, `hrs`, `hends`, `hended`,
`hlastMatch`, `hlastMismatch`, `hmismatch`, `hfound`, `hfoundBg`,
`hfoundReplay`, `hstr`

そして **14 葉すべてに関連ファイルが存在する**:

| 葉 | ファイル |
|---|---|
| `hbudget` / `hrs` | `CloseoutRestartShape`（本セッション wave 5 で作成） |
| `hends` | `GalilLeafEnds` |
| `hended` / `hlastMatch` | `GalilLeafReport` |
| `hpres` | `CloseoutOracle7` |
| `hshape` | `GalilReplaySpan` |
| `hstage` / `hmismatch` | `CloseoutOracleI2` |
| `hlastMismatch` | `CloseoutOracle5` |
| `hfound` / `hfoundBg` | `CloseoutFoundBackground` |
| `hfoundReplay` | `CloseoutFoundReplay`（`foundInReplayRouteMC3_of_leaf` は **MC3** 用） |

### さらに: ビルド可能なのに未登録のファイルがあった

`CloseoutOracle7.h_oracle_of_leaves6` は **13 葉**版（`hends`/`hstr` が消え
`hreadyB`/`hpresRepAt` に置き換わっている）で、**単体ビルドが通るのに
`PalPeg.lean` に未登録**だった。`CloseoutOracle6` も同様。両方登録した。

未登録のまま眠っていた `Closeout*`（ビルド可否を実測）:

| ファイル | 状態 |
|---|---|
| `CloseoutOracle6` / `CloseoutOracle7` | **ビルド可能** → 登録した |
| `CloseoutFoundRoute1` | エラー 3 |
| `CloseoutPackRun49` | エラー 5（既報） |
| `CloseoutPackRun50` | エラー 5 |
| `CloseoutRealize1` | エラー 3 |
| `CloseoutCoreEnc25` / `CloseoutWatchRound52` / `CloseoutWatchRound53` | 未測定 |

### 教訓

「producer がゼロ」の判定を `grep -c "theorem.*: <型名>"` だけでやったのが誤り。
producer は**別名で**存在し（`h_oracle_of_leaves''` の結論は `H_oracle`）、
葉に分解された形で各ファイルに散っている。**CLAUDE.md の §3 に
「閉: `hex`, `hsearch`, `hsegmentM`, `hends`, `hbudget`, `hrs`, `hended`,
`hlastMatch`, `hstr`」と書いてあったのを読まずに「ゼロ」と結論した。**

前提の到達可能性を判定するときは、(1) 型名の grep だけで済ませない、
(2) CLAUDE.md / 台帳の既存記録を読む、(3) 未登録ファイルの有無を確認する。

## 2026-09-19 `hme` の 3 入力すべてに道がついた（`hwin` → `WalkerPin` ＋ `WalkerInOrigin`）

**全体 build 成功（EXIT=0、エラー 0、sorryAx 0）・標準公理のみ・無条件 PAL は未完。**
`pal_in_peg_final36` は **5 前提**（`hSP`, `hme`, `hor`, `hC`, `hpack`）。

`hme`（`H_marksEntry'`）の除去は `CloseoutPackRun17.marks_steps`
（`H_marksEntry'` を**使わない** run 版）を使う。その 3 側入力の現状:

| 入力 | 状態 |
|---|---|
| `h4 : first ≠ 4` | `first` を具体値に固定すれば `decide`。`centreC`/`placeC` は `first` に依存しない |
| `hfl : 0 ≤ value length` | **証明済み**（`CloseoutSpanTick.lenNonneg_of_span_radius`） |
| `hwin : WindowInOrigin at copy` | **分解済み**（本項） |

### `hwin` の分解

`WindowInOrigin s := (stream s.fpp.walker).length ≤ position s.right` と
`WalkerInOrigin s := (stream s.walker).length ≤ position s.right` は
**同じ境界を 2 つの別の walker に課したもの**。

`CloseoutPackRun25.windowInOrigin_of_fair` が両者を `scan → copy` 着地で
橋渡しするが、そこで使う `Fair.fallbackPlace` の内容は
`GalilTickFair.Fair` を読むと

```
fallbackPlace : x.ctl.mode = Mode.scan → y.ctl.mode = Mode.copy →
  y.vm.fpp.walker = y.vm.walker
```

すなわち **「着地状態で 2 つの walker が一致する」だけ**。これは着地状態
単独の性質なので、`Fair` を仮定に取る必要がない。

`CloseoutWinOrigin`:
- `WalkerPin s := s.fpp.walker = s.walker`（名前を付けた）
- `windowInOrigin_of_pin : WalkerPin s → WalkerInOrigin s → WindowInOrigin s`
- `pin_of_fair` — 旧橋がこれを経由することの確認

`ChainPack` の `winOrigin` 場を `walkerPin` / `walkerOrigin` の 2 場に置き換え、
`marksInputs_of_chainPack` が `windowInOrigin_of_pin` で組み直す。

### `SpanRep` による `hfl` の決着（`CloseoutSpanTick`）

`hfl` については 3 度訂正した。最終的な形:

- `lenPos_of_spanRep : SpanRep s → 0 ≤ value s.radius → 0 < value s.length`
- `radiusNonneg_of_radiusRep : RadiusRep r Rad → 0 ≤ value r`
- `lenNonneg_of_span_radius` — 2 つを合わせた `hfl` の形

`GalilSpanCounter` に `SpanRep` の遷移補題が全形状分あり
（`spanRepS_shiftTick` を含む）、`length` が減ることと `SpanRep` が保たれることは
両立する（`radius` も同時に減る）。

### 残る作業

`packRunR_MW` の `hme` 使用 2 箇所（`CloseoutOracleW:170`, `CloseoutPackW:156`）を
`ChainPack.marks` / `marksInputs_of_chainPack` に差し替える配線。
`packRunR_MW` に各状態の `ChainPack` を届ける必要があり、それには
`ChainPosInv2` を run に通す（`chainPosInv2_steps` は run 版を持っている）。

## 2026-09-19 ⚠️ 運用ミス — main への直コミットを 2 回やった

**全体 build 成功（EXIT=0、エラー 0、sorryAx 0）・標準公理のみ・無条件 PAL は未完。**

プロジェクト規定は「PR → merge」だが、本セッションで **2 回** main に直接
コミット／push した:

1. `a22b166`（`pal_in_peg_final31`、実体コード）— PR #70 とコンフリクトを生み、
   PR ブランチに main をマージして解消する手間が発生
2. `2411c49`（台帳の `SpanRep` 訂正）— main には台帳だけがあり
   `final36` の実体（`CloseoutFinalW3` 等）は作業ブランチにあるという
   **ねじれた状態**を作った。`git checkout main` した瞬間に
   `CloseoutFinalW3.lean` が消えて混乱した

どちらも作業ブランチに main をマージして復旧（台帳は両側のエントリを保持）。

**規則**: `lean-pal/` への変更は、台帳だけの変更であっても必ず作業ブランチに
置き、PR 経由で main に入れる。`git checkout main` の前に作業ブランチが
push 済みか確認する。

## 2026-09-19 訂正 — `SpanRep` の tick 保存は**既存**（`hfl` の真の証明経路）

**全体 build 成功・標準公理のみ・無条件 PAL は未完。**
`pal_in_peg_final36` は **5 前提**（`hSP`, `hme`, `hor`, `hC`, `hpack`）。

### 3 度目の訂正

`hfl`（`0 ≤ value length`）について:

1. 最初「`length` は減らない」→ 誤り（`shiftTick` が `dec (dec length)`）
2. 次「tick 不変量としては閉じない」→ **これも誤り**

`GalilSpanCounter` に `SpanRep`（`value length = 2·value radius + 1`）の
遷移補題が**全形状分ある**:

| 補題 | 対象 |
|---|---|
| `spanRep_afterCompare` | 比較 |
| `spanRep_replayDec` | replay 減算 |
| `spanRep_background` | background |
| `spanRep_watchSegE` / `spanRep_watchSeg` / `spanRep_scanSeg` | 区間 |
| **`spanRepS_shiftTick`** | **`shiftTick`**（`length` と `radius` が同時に減るので関係は保たれる） |
| `spanRepS_shiftRun` / `spanRep_shift` / `spanRep_rounds` | shift 相 |
| `spanRep_restart` / `spanRep_of_init` | restart / init |

つまり **`length` が減ることと `SpanRep` が保たれることは両立する** — ウチが
「`length` が減るから `hfl` は tick 不変量にならない」と結論したのは、
`radius` も同時に減ることを見落としていたため。

`SpanRep` は `InvLP` からも出る（`CloseoutWatchPhase.spanRep_of_invLP`）。
`radius` の非負性（`RadiusRep` の `value = Rad : ℕ`）と合わせて
`value length = 2·Rad + 1 ≥ 1`（`CloseoutLenNonneg.lenPos_of_entryCounters`、
**証明済み**）。

### `hme` 除去の残り

`ChainPack` に marks 経路の必要物すべて（`cpack` / `wpack` / `marks` /
`winOrigin` / `lenNonneg`）が場として入った。2 つの `hme` 使用箇所
（`CloseoutOracleW:170` の `marksInv'_of_run`、`CloseoutPackW:156` の
`marksInv'_tick`）はどちらも `MarksInv'` を作るためなので、`ChainPack.marks`
で置き換えられる。

**残る作業**: `packRunR_MW` に `ChainPosInv2` を通して各状態で `ChainPack` を
取れるようにする（現在 `packRunR_MW` は `IPackMW` しか運んでいない）。
`chainPosInv2_steps` が run に沿った `ChainPosInv2` を出すので、起点の
`ChainPosInv2` を入力に足せば届く。
## 2026-09-19 `ChainPack` に marks 3 pack を追加＋全体 build を壊して復旧（教訓）

**全体 build 成功（EXIT=0、エラー 0、sorryAx 0）・標準公理のみ・無条件 PAL は未完。**
`pal_in_peg_final36` は **5 前提**のまま（`hSP`, `hme`, `hor`, `hC`, `hpack`）。

### `hme` 除去の材料が揃った

`ChainPack` に `CPack` / `WPack` / `MarksInv'` を場として追加した。これで
`CloseoutPackRun17.marks_steps`（`H_marksEntry'` を**使わない** run 版）の
必要物がすべて束の中に入る:

| `marks_steps` の入力 | 供給元 |
|---|---|
| `h4 : first ≠ 4` | `first` を具体値に固定すれば `decide`。`centreC`/`placeC` は `first` に依存しない |
| `hfl : 0 ≤ value length` | `ChainPack.lenNonneg`（証明は `lenNonneg_of_entryCounters`） |
| `hwin : WindowInOrigin at copy` | `ChainPack.winOrigin` |
| `CPack` / `WPack` / `MarksInv'` | `ChainPack.cpack` / `.wpack` / `.marks` |

`cpack_of_entry`（`InvS` ＋ `EntryCounters` → `CPack`、`GalilCentreLive:670`）と
`wpack_of_mode`（`CloseoutPackRun17:107`）があるので、これらは run の起点では
無料。**配線は未了。**

### ⚠️ 教訓: `structure` の引数を変えると下流が静かに壊れる

`ChainPack` に `CPack q c s` / `WPack q first c s` を足した結果、`q` と `first`
が structure の引数に昇格し、`ChainPack w c s` が `ChainPack q first w c s` に
なった。**単体ビルド（`lake build PalPeg.CloseoutChainPack`）は通ったが、
全体 build が エラー 11 / sorryAx 5 で落ちた**（`CloseoutWatchSupply`,
`CloseoutFinalPack`, `CloseoutFinalW3` の 3 ファイル）。

これは CLAUDE.md の「`lake build --quiet PalPeg` が通ったことと、そのファイルが
ビルドされたことは別」の**裏返し**の事例:
**単体が通ったことと、下流が壊れていないことも別。**

対処: 3 ファイルで `ChainPack w …` → `ChainPack q first w …` に統一して復旧。

**規則**: `structure` / `def` の引数（section 変数の捕捉を含む）を変えたら、
単体ビルドで満足せず必ず全体 build を回す。

## 2026-09-19 `LagAll` — chain 進化の全体で閉じた lag 不変量

**全体 build 成功・標準公理のみ・無条件 PAL は未完。**

`ChainSide`（`hpack` の chain 側残差）の 12 場のうち、`lagCan` と `backLag` を
**tick 不変量として閉じた**。

### なぜ 2 場を組にする必要があったか

`CloseoutPackRun48.lagCan_step` は `LagCan`（`watch` 形状の lag）を
`ChainStep` で保存するが、**`back` 形状の lag を入力に取る**（`hback`）。
`ChainStep.backDone` が `back` の lag をそのまま新しい watch に installするため。

`ChainStep` の構成子（`GalilScaffoldTopChainVM:50`）を読むと:

| 構成子 | `lag` |
|---|---|
| `copyBit` | 不変 |
| `copyEnd`（`.copy → .back`） | 不変 |
| `backStep` | 不変 |
| `backDone`（`.back → .watch`） | 不変（`back` の lag が watch に入る） |
| `watchStep` | **ここだけ動く**（`Internal` 経由） |

よって「全形状の lag が canonical かつ非負」は `ChainStep` で閉じ、
`watch` の場合だけ `lagCan_step` が処理する。`hback` の側入力が消える。

### `LagAll`（`CloseoutLagAll`、標準公理のみ）

```lean
def LagAll (z : ChainVM) : Prop :=
  (∀ wch, z = .watch wch → Canonical wch.lag ∧ 0 ≤ value wch.lag) ∧
  (∀ v h lag margin ver, z = .back v h lag margin ver → Canonical lag ∧ 0 ≤ value lag) ∧
  (∀ t h p v lag margin ver, z = .copy t h p v lag margin ver → Canonical lag ∧ 0 ≤ value lag)
```

- `lagAll_idle` / `lagAll_broken` — 自明
- **`lagAll_step`** — `ChainStep` で閉じる
- **`lagAll_matched`** — `ChainMatched` で閉じる。全構成子が `lag` を保つか `inc` し、
  `inc` は両半分を保つ（`inc_canonical` と `nonneg_inc`）
- `lagAll_lagCan` / `lagAll_back` — Run48 の 2 入力を読み戻す

**chain の進化は `ChainStep` と `ChainMatched` のみ**なので、`LagAll` は
chain 進化の全体で閉じている。

### 現状

`pal_in_peg_final36` は **5 前提**（`hSP`, `hme`, `hor`, `hC`, `hpack`）。
`LagAll` は `hpack` の 12 場残差のうち 2 場を落とす材料で、**まだ配線していない**
（配線しても数は減らず、`ChainSide` が小さくなるだけ）。

前提数を実際に減らすには `ChainSide` を**丸ごと**閉じる必要がある。残る主要な壁:

| 場 | 状態 |
|---|---|
| `repV` / `repVmid` | `VerRep` の tick 保存。`verRep_next`（1 `right` の運搬）はあるが全形状は未 |
| `scanBound` | checkpoint の位置予算。run 文脈が要る（wave 7 の `front` 経路） |
| `centreCanR` / `centreLedgerPos` / `scanCentre` | `CentreLedger` と `ScanInvariant` の帰結の見込み |
| `replayPay` / `radNext` / `startLedger` | 未調査 |

## 2026-09-19 `ChainPack` を run pack と `ChainSide` に分解（前提数は 5 のまま）

**全体 build 成功（EXIT=0、エラー 0、sorryAx 0）・標準公理のみ・無条件 PAL は未完。**

`hpack`（`ChainPack`）の 18 場のうち、run 上に既にあるものを切り出した。

| `ChainPack` の場 | 出所（run 上で無料） |
|---|---|
| `repR` | `LPackM.scanGeom`（非 replaying）/ `LPackM2.scanGeomR`（replaying）の `ScanInvariant.rightRep` / `rightPresent` |
| `saneR` | `SanePack.saneR` |
| `centreSane` | `SanePack.saneC` |

`LPackM2` は `IPackMW` の成分として `packRunR_MW` が run 全体で運ぶ。
`SanePack` は `CloseoutLPack6.sanePack_pt` が `PreTrace` ＋ `LeftLive` だけから
trace 上で確立する（**追加入力なし**）。

`chainPack_of_lpackM2 : ChainPosInv2 → LPackM2 → SanePack → ChainSide → ChainPack`。

### 正直な評価

**前提数は 5 のまま**（`hpack` → `hside` の置き換え）。中身は 3 場小さくなったが、
数は減っていない。これは言い換えに近い。

`ChainSide` に残る 12 場: `repV`, `repVmid`, `lagCan`, `backLag`, `replayPay`,
`radNext`, `startLedger`, `centreCanR`, `centreLedgerPos`, `scanRad`,
`scanCentre`, `scanBound`, `shiftCanR`, `shiftRad`。

このうち `scanRad` / `scanCentre` / `centreLedgerPos` / `shiftRad` は
`ScanInvariant` と `CentreLedger` と `ShiftGeom` の帰結なので、次に落とせる見込み。
`repV` / `repVmid` / `lagCan` / `backLag` が chain 機械の本体。

## 2026-09-19 訂正 — 「見込みなし」は誤り。`hbudget` 除去（`final36`、5 前提）

**全体 build 成功・標準公理のみ・無条件 PAL は未完。**

直前の項で `hbudget` と `hme` を「見込みなし」と書いた。**両方とも誤り。**

### `hbudget` は `ChainPack` の場だった（5 分で落ちた）

「`ChainPosInv2` は単一状態の述語なので run 文脈がなく位置上界が出ない」と
書いたが、**位置上界も単一状態の性質**であり、`ChainPack` は run に沿って
確立される束なので、そこに畳めばよかっただけ。

`ChainPack` に `scanBound` 場を追加し、`scanBudget_of_chainPack` で読み戻す。
`hbudget` は `hpack`（既存前提）に吸収され、**`pal_in_peg_final36` は 5 前提**:
`hSP`, `hme`, `hor`, `hC`, `hpack`。

### `hme` も道がある

`CloseoutPackRun17.marks_steps`（:406）は `CPack`/`WPack`/`MarksInv'` を run に
沿って運び、**`H_marksEntry'` を使わない** — `marksInv'_tick` に
`marksEntry'_of_layout (chooseLayout_of_wpack h4 hW hm hs)` を渡す形で、
レイアウトを `WPack` から読む。

その 3 入力の現状:

| 入力 | 状態 |
|---|---|
| `h4 : first ≠ 4` | `first` 具体化時の側条件 |
| `hfl : … → 0 ≤ value length` | **証明済み**（`lenNonneg_of_entryCounters`） |
| `hwin : … → copy → WindowInOrigin z.vm` | 単一状態の性質（`(stream s.fpp.walker).length ≤ position s.right`）。`ChainPack` と同じく束の場にできる |

`CloseoutMarksFree.MarksRun`（`WindowInOrigin` at copy ＋ `EntryCounters` at
scan）と `marksInv'_of_marksRun` を置いた。`hfl` は `MarksRun` の第 2 成分から
自動で出る。

**教訓**: 「単一状態の述語だから run 文脈が要る」は逆だった。単一状態の性質こそ
run に沿って運ぶ束の場に置けばよい。`hav`/`hstart`/`hbudget` の 3 つが同じ形で
落ちた。「見込みなし」と書く前に、その述語が単一状態のものか run のものかを
見分けること。

## 2026-09-19 `hav`/`hstart` 除去と `hfl` の証明（`pal_in_peg_final35`、6 前提）

**全体 build 成功（EXIT=0、エラー 0、sorryAx 0）・標準公理のみ・無条件 PAL は未完。**

**トップダウンに徹し、書く前に「減る見込み」を論証する**方式に変えた。
前回は分解＝言い換えで前提が増えていた（8 → 9 → 10）。

### 純減 2 件

| 除去 | 事前の論証 | 結果 |
|---|---|---|
| `hav`（`ConsumeAvail`） | `watchShiftS_of_chainPosInv2` の `ConsumeAvail` 使用は `chainPos_step P.chainPos hav hstep` の **1 箇所だけ**で、`CloseoutPackRun48.chainPos_step_of_supply` が同じ材料（`Represents` 対 / verifier 対 / `LagCan` / `ChainPos` — すべて `ChainPack` の場）で代替する | 8 → 7 |
| `hstart`（`BgStartP2`） | `CloseoutPackRun47.bgStartP2_of_centre` が**既存**で、その 3 入力（`canRight s.right` / radius 台帳 / `CentreLedger`）はすべて `ChainPack` の場（第 1 は位置上界経由） | 7 → 6 |

`hav` の置き換えで mode 前提を入れずに済んだのは、`ShiftLocalS` の全場が
`ScanNR x` を前提に持つので mode が場の内側から取れるため
（`shiftLocalS_of_chainPack`）。

### `hfl`（`0 ≤ value length`）を証明した — 前回の訂正の訂正

tick 不変量としては偽（`shiftTick` が `dec (dec length)`）だが、
**不変量そのものが事実を含んでいた**:

`GalilGlueBLeaves.EntryCounters`（:74）は
`∃ Rad : ℕ, ScanInvariant … Rad … ∧ RadiusRep r.radius Rad ∧ SpanRep r ∧ Canonical r.length`。
`RadiusRep c n := Canonical c ∧ value c = n`（`n : ℕ`）と
`SpanRep r := value r.length = 2 * value r.radius + 1` から
`value length = 2·Rad + 1 ≥ 1`。`lenPos_of_entryCounters`。

前回「`CPack.canon` では出ない」と判断したのは正しかったが、
**`EntryCounters` を見落としていた。**

### `ScanBudget` の縮小

第 1 連言（`0 < left.length`）は `ChainPack.repR` と
`CloseoutLPack3.present_iff_left` から出るので落とした。残るは位置上界のみ。

### ⚠️ 残り 6 前提の到達可能性（見込みが立たないもの）

| 前提 | 状態 |
|---|---|
| `hbudget`（位置上界） | **見込みなし**: 使用 3 箇所すべて文脈が `ChainPosInv2` だけ。`ChainPosInv2` は**単一状態の述語**なので run 文脈がなく、wave 7 の `front` ポテンシャル経路（run の出口上界が必要）が刺さらない。`ScanBudget` を run 文脈付きに変える構造変更が要る |
| `hme` | **見込みなし**: `marksInv'_of_run'` の残り 2 入力のうち `hwin`（`WindowInOrigin`）の producer（`CloseoutPackRun25:124`）が **`FairSteps` を要求**する。`FairSteps → Steps` の一方向しかなく、逆には各 tick の `Fair` が要る。run pack を `FairSteps` に上げる構造変更とセット。`h4 : first ≠ 4` は `first` 具体化時の側条件 |
| `hSP` | 周期と `PalAt` の実質的主張（Galil の move 補題圏） |
| `hor` | `CycleOracleMC3` の producer はゼロ。最大の残り |
| `hC` | 局所機械の実現 |
| `hpack`（`ChainPack`） | `ChainPosInv2` の各場を run に沿って確立する層。`repR`/`repV` は `Represents` の運搬（`right_word`/`right_present`）があるが、tick 全形状の保存は未着手 |

**計画書 §10.5 の完成条件（追加引数なしの `RecognizedByTotalPEG PAL`）は未達。**

## 2026-09-19 `ChainPack` 束ね＋偽の `hni` 除去（`pal_in_peg_final33`）

**全体 build 成功（EXIT=0、エラー 0、sorryAx 0）・標準公理のみ・無条件 PAL は未完。**

### トップダウンに切り替えた

それまで葉から積むボトムアップで、前提の**言い換え**を作っていた
（`final30` 8 → `final31` 9 → `final32` 10 と増えた）。最終定理から降りて
各前提の producer と入力を測る形に変えた。

### `chainPosInv2_tick` の 4 分岐は `ChainPack` 1 つに束ねられる

`CloseoutPackRun48` の 4 producer の入力は**同じ形**をしている:

```
∀ c s, c.mode = Mode.scan → ChainPosInv2 w c s → <s についての局所事実>
```

局所事実は `RRep`（右ヘッド）、`VerRep`（verifier ヘッド）、`LagCan`（lag）、
shift 相の `canRight s.right` と radius 台帳。これを `ChainPosInv2` に畳んだのが
`ChainPack`（`CloseoutChainPack`）。

さらに **`H_matchRes2` と `H_shiftRes2` は同一の `MatchRes2` pack を要求する**
（一方は matching 比較の source、他方は mismatching guarded 比較）ので
`matchRes2_of_chainPack` 1 本で両方が落ちる。

### ⚠️ `hni`（scan 状態の chain は非 idle）は **偽**

`initVM` は `t.chain = .idle`（`GalilScaffoldTopReplay:24`）を出し、
`invLPC_init`（`GalilFinalAssembly4:85`）はその着地を `mode := .scan` に置く。
**scan かつ chain idle な状態が実在する。**

`MatchRes2` はこれを必要としない — `repV` は `.watch` で guard され
`startLedger` は `.idle` で guard される — ので、`canR` を
`canRight_of_position_bound`（wave 5）で位置上界から出す形に直して除去した。
`hnr`（scan 状態で非 replaying）も同時に不要になった。

### 前提数の推移

`final30` 8 → `final31` 9 → `final32` 10 → **`final33` 8**。

`final32 → final33` の 2 減は言い換えではなく、**偽の前提 1 つの除去**と
それに連動した 1 つの不要化。

### `final33` の 8 前提

`hSP`, `hme`, `hor`, `hC`, `hpack`（`ChainPack`）, `hbudget`（`ScanBudget`）,
`hstart`（`BgStartP2`）, `hav`（`ConsumeAvail`）。

**`hav` にも偽の疑いがある**: `∀ w st i, ConsumeAvail (st i).vm.chain` は
verifier が入力末尾にいる状態で `canRight (right verifier)` を主張する。
`consumeAvail_of_verRep`（`CloseoutVerRep`）が位置予算への還元を持っているので、
次はそこを配線して全称形を落とす。

### 副産物

- `CloseoutVerRep`: `VerRep`（verifier ヘッドの `Represents` 対）、
  `verRep_next`（1 `right` の運搬、`right_word`/`right_present`）、
  `consumeAvail_of_verRep`。
- **`CloseoutPackRun49` は `PalPeg.lean` に未登録で、単体ビルドでエラー 5 件。**
  `MatchRest` を材料にしようとして import した瞬間に露出した。CLAUDE.md の
  「build が通ったこととそのファイルがビルドされたことは別」の実例。

## 2026-09-19 `H_fourOther` 除去 — `ChainPosInv2` 経路へ（`pal_in_peg_final31`）

**全体 build 成功（EXIT=0、エラー 0、sorryAx 0）・標準公理のみ・無条件 PAL は未完。**

`CloseoutPackRun41` と `CloseoutPackRun48` は Run34 より**先に進んでいた**のに
run に繋がれていなかった。繋いだ。

### `ChainPosInv2` が `H_fourOther` を要らなくする

`CloseoutPackRun41.ChainPosInv2` は chain 半分を `ChainStep` / `ChainMatched` の
下で**自己完結**させる（`chainPos_step` / `chainPos_matched`）。よって Run38 の
「1 tick 先読み」が消え、`watchShiftS_of_chainPosInv2` は
**`H_fourOther` を取らない** — target の verifier 対は `chainPos_step` から出る
（unmatched な比較の chain 効果は素の `ChainStep`）。

`H_fourOther` は `guard_budget` が `h ≤ R + 1` しか出さない難所だったので、
これが不要になるのは大きい。

### Run48 が 4 分岐すべてを処理済み

| `chainPosInv2_tick` の仮説 | Run48 の producer |
|---|---|
| `H_bgP2` | `h_bgP2_of_supply`（:163） |
| `H_matchP2` | `h_matchP2_of_target`（:243） |
| `H_shiftEntry2` | `h_shiftEntry2_of_target`（:374） |
| `H_shiftDoneRad2` | `h_shiftDoneRad2_of_supply`（:446） |

`shift_one` は `chainPosInv2_tick` で**無条件に閉じる**（`shiftTick` は centre/left
しか動かさず、`chainShiftOne` は verifier と lag を固定し、`right` は
`shiftLens` の成分でないので `t.right = s.right`）。

### `ConsumeAvail` も位置予算に還元

`CloseoutPackRun47.consumeAvail_of_next_supply` は `ConsumeAvail` を
**次の右ヘッドセル**についての 4 事実（`Represents` / `focus ≠ none` /
`canRight` / `position R' = position R + 1`）＋ `LagNonneg` ＋ `ChainPos` に
落とす。後ろ 2 つは `ChainPosInv2` の中、`canRight` は wave 5 の
`canRight_next_of_bound` が位置上界から出す。`consumeAvail_of_bound`
（`CloseoutConsumeAvail`）。残る入力は **verifier ヘッドの `Represents`** 1 点。

### 前提の推移（正直に）

`final30`（8）→ `final31`（9）。**数は 1 増えた。**

| 消えた | 入った |
|---|---|
| `hfour`（`H_fourOther`） | `hentry`（`H_shiftEntry2`） |
| `hbgP` → `H_bgP2`（より弱い） | `hav`（`ConsumeAvail`） |
| `hmatchP` → `H_matchP2` | |
| `hsdP` → `H_shiftDoneRad2`（より弱い） | |

本質的な前進は「1 tick 先読みの消滅」と「`H_fourOther` の不要化」。
`hav` は `consumeAvail_of_bound` で verifier の `Represents` 1 点に絞れている。

### 新規（全て標準公理のみ）

`CloseoutShiftS2`（`chainPosInv2_steps`, `shiftLocalS_of_chainPosInv2`,
`shiftLocalS_of_run2`）、`CloseoutTrailS2`（`radPack_ptS2`, `trailF_ptS2`,
`needIMW'_le_W2`）、`CloseoutFinalS2`（`pal_in_peg_final5MW2`,
`consumeAvail_idle`, **`pal_in_peg_final31`**）、
`CloseoutConsumeAvail`（`consumeAvail_of_bound`）。
## 2026-09-19 3 分岐仮説を Run38 の残差へ（`CloseoutBranchRes`）

**全体 build 成功・標準公理のみ・無条件 PAL は未完。**

`CloseoutPackRun38` が Run34 の 3 分岐仮説**すべての分解を既に持っていた**。
run に繋がれていなかったので繋いだ。

| Run34 仮説 | Run38 producer | 残差 |
|---|---|---|
| `H_bgP` | `posPayload_background`（:157） | `H_bgRes` |
| `H_matchP` | `posPayload_match`（:220） | `H_matchRes` |
| `H_shiftDoneP` | `posPayload_shiftDone`（:314） | `H_shiftDoneRes`（恒等） |

### `H_bgRes` / `H_matchRes` は実質的な前進

`BgRes`（`Run38:140`）は payload を 3 つに割る:

- `src : SrcPos s` — chain 側の台帳（live watch の verifier が `Sane`、
  `back` 相は既に `lag` 分後ろにいる）。**`step_pos`（`Run38:76`）が
  1 `ChainStep` を越えて `position verifier + lag` を運ぶ。**
- `start` — chain が idle のときの `canRight` と radius 台帳
- `verNext` — 1 chain tick 先の verifier の `canRight ∧ Sane`

### `H_shiftDoneRes` は恒等（Run38 が明記）

Run38 は「`ChainPosInv` は `shift` mode を越えて何も届かない」と記録しており、
`posPayload_shiftDone := hres` は恒等。その**真の分解**は本セッションの
`CloseoutShiftDoneP`:

- `canR` ← `ShiftGeom.RRep` ＋ 位置上界（`canRight_of_position_bound`、wave 5）
- `radLe` ← `ScanInvariant.rightPos` と `ShiftGeom` の位置関係（`rem = 0`）
- 残り 2 場 → `ChainSideAt`（verifier の位置台帳と 1 tick 先の健全性）

### 新規（`CloseoutBranchRes`、標準公理のみ）

`chainPosInv_steps_res`, `shiftLocalS_of_run_res` — `shiftLocalS_of_run` 以上が
Run34 の仮説ではなく **Run38 の残差**に依存するようになった。

**次**: `SrcPos` を run に沿って確立する（`step_pos` が 1 step 分を持っている）。
`verNext` は `GalilArriveChain.caught_arrive` / `immediate_arrive` が近い。

## 2026-09-19 `H_shiftDoneP` の分解（`CloseoutShiftDoneP`）

**全体 build 成功・標準公理のみ・無条件 PAL は未完。**

`chainPosInv_tick`（`CloseoutPackRun34:411`）は 23 tick 形状のうち 20 を閉じ、
3 つを named hypothesis として残す。使用箇所は各 1 箇所:

| 仮説 | 使用 tick |
|---|---|
| `H_bgP` | `scan_wait`（:17）, `scan_count`（:20） |
| `H_matchP` | `scan_match`（:23） |
| `H_shiftDoneP` | `shift_done`（:26） |

`shift_done` は **VM が不変**（制御だけ `shift → scan`）なので 3 つの中で最も軽い。

### 分解結果

`PosPayload` の 4 場のうち **2 つは scan 幾何から無料**:

- `canR : canRight s.right` ← `ShiftGeom`（`CloseoutPackRun23:86`）の
  `RRep w s`（`Represents s.right.head w ∧ focus ≠ none`）と位置上界から
  `canRight_of_position_bound`（wave 5）で出る。`canR_of_shiftGeom`。
- `radLe` は `ScanInvariant.rightPos` と `ShiftGeom` の
  `position s.right = position s.center + rem + r` を突き合わせる。
  `shift_done` は `¬ remainingPos s` なので `rem = 0`。`radEq_of_shiftGeom_done`。

残り 2 場は chain 側で、`ShiftGeom` は何も言わない:

```lean
def ChainSideAt (w : List (Fin 2)) (s : GalilVM) : Prop :=
  (∀ wch, s.chain = .watch wch →
      (position wch.machine.verifier : ℤ) + value wch.lag = position s.right) ∧
  (∀ a z wch, ChainTick a s.chain z → z = .watch wch →
      canRight wch.machine.verifier ∧ Sane wch.machine.verifier)
```

`posPayload_of_shiftGeom` がこの 2 つを組み合わせて `PosPayload` を出す。
すべて標準公理のみ。

**残る義務**: `ChainSideAt`（verifier の位置台帳と 1 chain tick 先の健全性）。
これは chain machine の不変量で、`Coupled'.sum : SumRel`
（`.watch w` で `distance + lag = radius`）が `pos` 場の素材。
`verNext` は `GalilArriveChain` の `caught_arrive` / `immediate_arrive`
（`canRight` を前提に取る形）が近い。

## 2026-09-19 訂正 — `hfl`（`0 ≤ value length`）は単純な tick 不変量では**ない**

**全体 build 成功・標準公理のみ・無条件 PAL は未完。**

`hme` 除去のために `CloseoutPackRun17.marksInv'_of_run'` の入力
`hfl : ∀ m z, Steps … → z.ctl.mode = scan → 0 ≤ value z.vm.length`
を閉じようとした。

**誤った見立て**: `length := …` の代入箇所を grep すると `reset` / `ofNat _` /
`inc` しか出てこない（`GalilBootVM:45`, `GalilScaffoldTopRewind:56,178`,
`CloseoutWatchRound30:209`, `CloseoutWatchRound33:312`, `CloseoutPackRun50:54`,
`GalilLeafQuiet:121`）。よって「`length` は減らない」と判断した。

**これは間違い。** `shiftTick`（`GalilScaffoldChainInputSupply:1445`）は

```
def shiftTick (s : ShiftState) : ShiftState :=
  ⟨right s.center, right (right s.left), dec s.remaining, dec s.radius,
    dec (dec s.length)⟩
```

で **`length` を 2 回 `dec`** する。`shift_one` は `shiftLens.set s (shiftLens.get t)`
経由なので、可視の `length := dec …` として grep に出てこない。
`GalilScaffoldTopShift:11` の docstring は最初から「`length -= 2`」と書いていた。

**教訓**: 代入箇所の構文的 grep はレコード更新をすり抜ける。フィールドの
振る舞いは、そのフィールドを含むレンズ／レコードの更新関数
（ここでは `shiftTick`）まで追う必要がある。

### `hfl` の真の義務

`shift_one` が撃てるのは `remainingPos s`（`positive s.shift.remaining = true`）の
間だけで、`ShiftGeom`（`CloseoutPackRun23:86`）が `remaining` と
ヘッド位置を結びつけている。`CPack.span : value s.length ≤ 2 * position s.right + 1`
と合わせて `shift` phase の下界を出すのが本筋。

### 残したもの（`CloseoutLenNonneg`、標準公理のみ）

`value_reset`, `value_ofNat`, `nonneg_ofNat`, `nonneg_inc`, `value_inc`,
`nonneg_reset` — カウンタの基礎補題。これらは正しく、`hfl` の本証明でも使える。

## 2026-09-19 wave 10 — `ShiftLocalG` も消えた: **8 前提・反証済みゼロ**（`pal_in_peg_final30`）

**全体 build 成功・標準公理のみ・無条件 PAL は未完。**

`pal_in_peg_final30`（`CloseoutFinalW`）— 標準公理のみ。
**`WatchShiftG` も `ShiftLocalG` もコードに現れない。**

### `hsl` も偽だった

wave 9 の `final29` は `hsl : ∀ w y, ShiftLocalG … w y` を持っていたが、これも
`WatchShiftG` と同じ反例で偽。`ShiftLocalG` の全場の前提は
`beginShiftVM' s'' t''` で、`beginShiftVM h w s t := s.chain = .watch w ∧ t = …`
（`GalilScaffoldTopShiftCycle:23`）は **`shiftGuardVM` を含まない**。よって
`ChainStep.backDone` で生まれたばかりの watch（`distance = reset`）が前提を
満たしつつ `4 * periodLength ≤ distance` を破る。

### 弱化ではなく削除

`CloseoutShiftS`（wave 8）が trail 橋を `ChainPosInv` に載せ替えた結果、
**`IPackMG.shift` を読む者は誰もいなくなった**（唯一の読者
`halfBound_of_ipackMG` / `shiftVerSane_ptMG` は両方置換済み）。
よって場ごと削除できる。

`CloseoutPackRun30.IPackMG` から直接落とすと旧鎖 `final17 → … → final25` が
壊れる（実測: 全体 build で `final18` が `sorryAx`、ロールバック済み）ので、
`CloseoutStageCheck` と同じ**非破壊複製**で層を作った:

| ファイル | 内容 |
|---|---|
| `CloseoutPackW` | `IPackMW := LPackM ∧ LPackM2`（`IPackMG2` から `shift` を落としたもの）、`BigPack2MG7W`/`BigPack2MG7W''`、`lticksN_of_lpackM2_W`、`ipackMW_tick`、`bigPack2MG7W''_tick` |
| `CloseoutCheckW` | `StepsIMW`/`ReachAtIMW`/`CycleOutIMW`/`CycleOracleIMW`/`checkpoints_costIMW_upto1`/`PreTraceIMW`/`preTraceIMW_exists` |
| `CloseoutOracleW` | `PackRunRMW`、**`packRunR_MW`（shift 仮説ゼロ）**、`ipackMW_of_invLPC`、`h_bootIMW_of_bootIPack`、`h_oracleIMW_of_MC3_W`、`needIMW'_le_W` |
| `CloseoutFinalW` | `H_realizeLIMW'`、`pal_in_peg_final5MW`、**`pal_in_peg_final30`** |

`lticksN_of_lpackM2_pt7` は `shift` 場を一度も使っていなかったので、W 化は
`hx.ipackM.base.pack` → `hx.ipackM.pack` の置換のみ。

### `hC` の型

`H_realizeLIMG2'` は `PreTraceIMG2` を仮定に取るが、その結論
（`SAccepts ↔ LatchTrue …`）は run pack に一切触れず `stLG' τF w st (Tc w.length)`
だけを読む。よって自然な領域は `PreTraceB` で、`H_realizeLIMW'` はそれを取る。
`IPackMW` がその `base` を供給する。

### `final30` の 8 前提（すべて未反証）

| 前提 | 状態 |
|---|---|
| `hSP` | 実質的義務（周期と `PalAt`）。`BigPack2MG7W` 上に再基底化 |
| `hme` | 真の見込み（`marksInv'_of_run'` が既存、`Fair` 配線が必要） |
| `hor` | producer ゼロ。最大の残り |
| `hC`（`H_realizeLIMW'`） | 局所機械の実現 |
| `hfour`, `hbgP`, `hmatchP`, `hsdP` | Run34 の 4 guarded 分岐仮説。`chainPosInv_tick` が 23 形状中 20 を閉じており、残りは 3 形状分 |

**wave 6 からの推移**: 8（`hsc` 偽）→ 7 → 5（`hws` 偽）→ 9（`hsl` 偽）→ **8（反証済みゼロ）**。
数の増減より「偽の前提が残っているか」が判定基準。

## 2026-09-19 wave 9 — 偽の `hws` が最上位から消えた（`pal_in_peg_final29`）

**全体 build 成功・標準公理のみ・無条件 PAL は未完。**

`pal_in_peg_final29`（`CloseoutWeakFinal`）— 標準公理のみ。
**`WatchShiftG` はもう現れない。** 前提は 9 個で `final27`（5 個）より多いが、
**偽の前提がゼロ**になった。これが本質。数より正しさ。

### `hws` を消した 2 つの弱化

1. **trail 側**（wave 8）: `pal_in_peg_final5MG2T` は trail 橋の全体を
   `ChainPosInv` の上で走らせる。`radPack` → `trailF` → `needL'` の鎖から
   `WatchShiftG` が消えた。
2. **pack 側**（本 wave）: `packRunR_MG27P` は `hws` を **1 箇所でしか使わない** —
   `ipackMG2_tick_pt7` の

   ```
   have hsh : ShiftLocalG … w y := by
     by_cases hi : y.vm.chain = ChainVM.idle
     · exact shiftLocalG_of_chainIdle … hi
     · exact shiftLocalG_of_watchShiftG … hi (hws y)
   ```

   つまり pack が実際に必要とするのは `ShiftLocalG` であり、`WatchShiftG` は
   それを**含意するだけ**（`shiftLocalG_of_watchShiftG`, `Run26:237`）。
   `ShiftLocalG` を直接取れば**厳密に弱い前提**になり、`WatchShiftG` の
   第 5 連言も idle 場合分けも落ちる。`packRunR_MG27L`（`CloseoutShiftWeak`）。

### `final29` の 9 前提

| 前提 | 状態 |
|---|---|
| `hSP` | 実質的義務（周期と `PalAt`） |
| **`hsl`**（`∀ w y, ShiftLocalG`） | `hws` の代替。4 場のうち `move` は wave 7 の `Extra7` で**すでに無料**。残り `guard`/`coupled`/`ver` |
| `hme` | 真の見込み（`marksInv'_of_run'` が既存、`Fair` 配線が必要） |
| `hor` | producer ゼロ。最大の残り |
| `hC` | 局所機械の実現 |
| `hfour`, `hbgP`, `hmatchP`, `hsdP` | Run34 の 4 guarded 分岐仮説。すべて `shiftGuardVM` 付き・unmatched 限定で Run32 の反例には当たらない |

### 次

`hsl` の 3 場（`guard`/`coupled`/`ver`）は `ShiftLocalS`（guarded）なら
`ChainPosInv` から出る（`shiftLocalS_of_run`、wave 8）。`ShiftLocalG` を
`ShiftLocalS` に落とすには `IPackMG.shift` 場の弱化が必要で、それは
Run30 §1 / Run36 §2 の非破壊 `S` 複製（`CloseoutStageCheck` と同じ機械変換）。
そこまで行けば `hsl` も `hfour`/`hbgP`/`hmatchP`/`hsdP` に吸収され、
最上位は `hSP`, `hme`, `hor`, `hC` + 4 分岐仮説の **8 前提・すべて未反証**になる。

### 新規（`CloseoutShiftWeak` / `CloseoutWeakFinal`、標準公理のみ）

`ipackMG2_tick_pt7L`, `bigPack2MG7''_tickL`, `packRunR_MG27L`,
**`pal_in_peg_final29`**。

## 2026-09-19 wave 8 完 — trail 橋が `WatchShiftG` から外れた（`pal_in_peg_final5MG2T`）

**全体 build 成功（EXIT=0、エラー 0）・標準公理のみ・無条件 PAL は未完。**

`hws`（偽）の **2 役割のうち 1 つを完全に除去**した。

### 到達点: `pal_in_peg_final5MG2T`（`CloseoutShiftFinal`）

`WatchShiftG` を**一切取らない**。trail 橋の全体が `ChainPosInv` の上で動く:

```
ChainPosInv
  → shiftLocalS_of_run        （guarded な ShiftLocalS、run の各点）
  → radPack_ptS               （halfBound_of_shiftLocalS / saneVer_of_shiftLocalS 経由）
  → trailF_ptS
  → needIMG2'_le_S
  → pal_in_peg_final5MG2T
```

boot の `ChainPosInv` は無料（`boot w` の chain は idle、`chainPosInv_of_idle`）。
`hws` の代わりに入るのは `CloseoutPackRun34` の 4 **guarded** 分岐仮説
（`H_fourOther`, `H_bgP`, `H_matchP`, `H_shiftDoneP`）で、いずれも
`shiftGuardVM` 付き・unmatched なターゲットに限定されており、Run32 の反例
（誕生直後 `distance = reset`）には当たらない。

### 残る `hws` の役割と、試して退けた手

残るのは**逆方向** — `packRunR_MG27P` の中で `ipackMG2_tick_pt7` の
`hsh : ShiftLocalG y`（`CloseoutPackRun46:160`）として `IPackMG.shift`
（`Run30:83`）を**埋める**側。

trail 橋が外れた今、この場は**誰も読まない**。よって

```
shift : x.vm.chain = ChainVM.idle → ShiftLocalG centre place entry q first w x
```

に弱めれば `shiftLocalG_of_chainIdle` で無料になり、`hws` は完全に消える。

**この編集は実際に試し、ロールバックした。** 理由: `IPackMG` は
`final17 → 18 → 19 → 20 → 21 → 22 → 23 → 24 → 25 → 26 → 27` の**一本道**を
支えており（`CloseoutPackRun33/35/36/42/43/45/46/50/51` + `Preload36/40` +
`Realize1` + `StageFinal` + `ExtraFinal`）、場を弱めると旧リンクが壊れる。
実測: Run30 単体は通ったが全体 build で `final18` が `sorryAx` になった。
**ロールバック後、既存ファイルの差分ゼロ・全体 build EXIT=0 を確認済み。**

非破壊の経路は Run30 §1 と Run36 §2 の **`S` 複製**（弱めた場を持つ
`IPackMGS` / `IPackMG2S`）— `CloseoutStageCheck` と同じ機械変換。**次 wave の主題。**

### 新規（`CloseoutShiftS` / `CloseoutShiftFinal`、全て標準公理のみ）

`shiftLocalS_of_chainPosInv`, `chainPosInv_steps`, `shiftLocalS_of_run`,
`saneVer_of_shiftLocalS`, `shiftReaders_of_run`, `saneTickS`, `verSane_ptS`,
`shiftOrd_ptS`, `radPack_ptS`, `trailF_ptS`, `needIMG2'_le_S`,
`boot_chain_idle`, `pal_in_peg_final5MG2T`。

## 2026-09-19 wave 8 続き — `trailF_ptS` まで到達、`hws` 除去の最後の一手の設計

**全体 build 成功・標準公理のみ・無条件 PAL は未完。**

`radPack_ptS` に続いて **`trailF_ptS`**（`CloseoutShiftS`）も標準公理で通った。
`trailF_ptMG`（`CloseoutPackRun30:626`）が `WatchShiftG` に触れるのは
`radPack_ptMG` 経由**のみ**で、他の材料（`LeftLive`/`SanePack`/`ScanT`/
`ChainBudget`/`VerF`）は無改造で通る。

### `hws` が残る理由（正確に）

`pal_in_peg_final27` の `hws` は **2 つの役割**を持つ:

1. **pack の場を埋める**: `packRunR_MG27P` → `ipackMG2_tick_pt7` の
   `hsh : ShiftLocalG y`（`CloseoutPackRun46:160`）。`IPackMG.shift` 場
   （`Run30:83`）の中身。
2. **pack の場を読む**: `trailF_ptMG` → `radPack_ptMG` → `halfBound_of_ipackMG` /
   `shiftVerSane_ptMG`。

**(2) は解決済み**（`radPack_ptS` / `trailF_ptS`）。残るは (1)。

### 試して退けた手: `ShiftLocalG` の定義に guard を足す

`CloseoutPackRun26` の `ShiftLocalG` に `¬matched ∧ shiftGuardVM` を足すと、
逆変換 `shiftLocal_of_shiftLocalG`（:231）が通らなくなる。これは
`h_shiftLocalC_of_G`（:322）→ `H_shiftLocalC` → `ipack_of_invLPC'`
（`CloseoutOracleI2:140`）という **pack の根本**に効いており、`ShiftLocal`
（guard なし）を要求する。波及が大きすぎるので**編集をロールバックした**
（既存ファイルは無傷、差分ゼロを確認）。

### 残る一手（次 wave の主題）

`IPackMG` の `shift` 場は **`trailF_ptMG` でしか読まれない**。
`pal_in_peg_final5MG2S` の中の `needIMG2'_le`（`Run36:474`、`h_trailI_MG2` 経由で
`trailF_ptMG` を使う）を `trailF_ptS` に差し替えれば、**その場は誰からも
読まれなくなる**。そうなれば `IPackMG` から `shift` 場を落とせ、(1) も消える。

必要な作業:
1. `needIMG2'_le` の S 版（`trailF_ptS` を使う）。入力に `ChainPosInv` 入口・
   `hreach`・`LPackM`・`LeftLive` が要る — いずれも `PreTraceIMG2` の
   `packs`（`IPackMG2`）から出るはず。
2. `pal_in_peg_final5MG2S` をその S 版に差し替え。
3. `IPackMG` から `shift` 場を落とす（`Run30/36/43/45/46` の再ビルド）。

これで `hws` は `H_fourOther` / `H_bgP` / `H_matchP` / `H_shiftDoneP` と
入口 `ChainPosInv` に置き換わる。4 分岐仮説はすべて `shiftGuardVM` 付きの
文脈なので、Run32 の反例（誕生直後 `distance = reset`）には当たらない。

## 2026-09-19 wave 8 — `hws` を通さない `RadPack` 経路（`CloseoutShiftS`）

**全体 build 成功・標準公理のみ・無条件 PAL は未完。**

前項で `hws`（`∀ y, WatchShiftG … y`）が偽だと記録した。本項はその**除去経路を
実際に配線した**もの。`CloseoutPackRun34` が guarded 版（`WatchShiftS` /
`ShiftLocalS` / `ChainPosInv` / `watchShiftS_of_chainPosInv` / `chainPosInv_tick`）を
用意していたが run に繋がれていなかった。`CloseoutShiftS` がその配線。

### なぜ小さく済んだか

`IPackMG.shift`（= `ShiftLocalG`）の**射影は 4 箇所しかない**
（`CloseoutPackRun30:535, 538, 540, 562`）。その 2 読者が全て:

| 読者 | guarded 版 |
|---|---|
| `halfBound_of_ipackMG`（Run30:523） | `halfBound_of_shiftLocalS`（Run34:165、**既存**） |
| `shiftVerSane_ptMG`（Run30:558） | `saneVer_of_shiftLocalS`（本 wave） |

さらに trace 側の 2 つも guard を足すだけで通った。いずれも entry 仮説を
`scan_shift` 分岐の 1 箇所でしか呼ばず、そこは `hmt`/`hg` を持つ:

| trace 読者 | guarded 版 |
|---|---|
| `shiftOrd_ptG`（Run30:567）＋`shiftOrd_tickG` | `shiftOrd_ptS`（本 wave）＋`shiftOrd_tickS`（Run34:197、**既存**） |
| `verSane_ptG`（Run30:591）＋`saneTickG`（Run26:444） | `verSane_ptS`＋`saneTickS`（本 wave） |

### 成果（`CloseoutShiftS`、全て標準公理のみ）

| 定理 | 内容 |
|---|---|
| `shiftLocalS_of_chainPosInv` | idle 分岐は無料、watch 分岐は guarded な `WatchShiftS` 経由 |
| `chainPosInv_steps` | `chainPosInv_tick` の run 帰納 |
| `shiftLocalS_of_run` | run の各状態で `ShiftLocalS` |
| `saneVer_of_shiftLocalS` | Run30:558 読者の guarded 版 |
| `shiftReaders_of_run` | 両読者を `ChainPosInv` から直接 |
| `saneTickS` / `verSane_ptS` | trace 側 `SaneVer` |
| `shiftOrd_ptS` | trace 側 `ShiftOrd` |
| **`radPack_ptS`** | **`hws` を一切通さない `RadPack`** |

### 残差

`radPack_ptS` の入力は `H_fourOther`, `H_bgP`, `H_matchP`, `H_shiftDoneP`
（`CloseoutPackRun34` の 4 分岐仮説）と入口の `ChainPosInv`、それに
`LPackM` / `LeftLive` / `PreTrace` / `Steps`（いずれも pack から）。
4 分岐仮説はすべて `shiftGuardVM` 付きの文脈なので、Run32 の反例
（誕生直後 `distance = reset`）には当たらない。

**次**: `radPack_ptS` を `trailF_ptMG` → `H_trailF` → 最上位へ繋ぎ、
`pal_in_peg_final27` の `hws` を 4 分岐仮説に差し替える。

## 2026-09-19 ⚠️ `hws`（`WatchShiftG` の全称形）は **偽** — `final27` の扱いに注意

**全体 build 成功・標準公理のみ・無条件 PAL は未完。**

`pal_in_peg_final27` の 5 前提のうち `hws : ∀ w y, WatchShiftG centreC placeC entry q first w y`
は、リポジトリ内の既存解析によれば **成立しない**。したがって `final27` は
「偽かもしれない前提からの含意」であり、**この前提が残る限り定理は無内容になりうる**。
wave 6/7 の「8 → 7 → 5」という数え方は、この事実を併記せずに述べてはならない。

### 根拠（`CloseoutPackRun32` 冒頭の caveat、`CloseoutPackRun34` §2）

`WatchShiftG` は **unguarded** な比較ターゲット `s''` について主張する。
`ChainStep.backDone` で生まれたばかりの watch は `watchControl` の
`distance = reset`（値 `0`）を持つので、誕生直後の scan 比較では
`4 * periodLength wch ≤ value wch.machine.control.distance` が
`periodLength ≥ 1` のとき破れる。よって
「`∀ y, WatchShiftG … y` はそれらの状態で真であるいかなる不変量からも産出できない」
（Run32:33–40）。

`ShiftLocalG`（`CloseoutPackRun26:198`）も同じ弱点を持つ。全場の前提は
`beginShiftVM' s'' t''` だが、`beginShiftVM h w s t := s.chain = .watch w ∧ t = …`
（`GalilScaffoldTopShiftCycle:23`）であって **`shiftGuardVM` を含まない**。
Run34 §2 は「`shiftLocalG_of_watchShiftS` は as stated では **not provable**」と明記する。

**注**: Run32/Run34 の記述は「design, not proved here」であり、Lean による反証は
まだ書かれていない。反例の形は具体的に特定されているが、`compareFound` の
witness 構成が未着手。**反証を Lean で確定させることが先決**（`CloseoutCandOrient` で
`H_candOrient` を反証したのと同じ形）。

### 修理経路（`CloseoutPackRun34` に既存、未配線）

| 提供物 | 内容 |
|---|---|
| `WatchShiftS`（:67） | `WatchShiftG` の payload を `¬ matched s'' ∧ shiftGuardVM s''` の下に制限 |
| `ShiftLocalS`（:89） | 同じく guard 付きの `ShiftLocalG` |
| `shiftLocalS_of_watchShiftS`（:128）, `shiftLocalS_of_chainIdle`（:122） | 産出 |
| `halfBound_of_shiftLocalS`（:165）, `shiftOrd_tickS`（:197） | **消費側の再配線済み** |
| `ChainPosInv`（:322）, `watchShiftS_of_chainPosInv`（:353） | `Coupled.sum`（`SumRel` = `distance + lag = radius`）＋位置 payload から guarded 版を出す |
| `chainPosInv_tick`（:411） | 23 tick 形状のうち **20 を閉じる** |

残差は 4 つの分岐仮説: `H_fourOther`（post-shift `Other` 半分）、
`H_bgP`（`scan_wait`/`scan_count`）、`H_matchP`（`scan_match`）、`H_shiftDoneP`（`shift_done`）。

### 次 wave（wave 8）の主題

`IPackMG` の `ShiftLocalG` 場を `ShiftLocalS` へ落とす再配線。
`ShiftLocalG` の出現は 10 ファイル 17 箇所（`CloseoutPackRun26/30/34/36/43/45/46/51`,
`CloseoutShiftLocalFree`, `CloseoutExtraFree`）。
`shiftLocalS_of_shiftLocalG` は一方向なので、pack の場を弱める向きの変更になる。
wave 7 で作った `extra7_of_front_steps_pack` は `ShiftLocalS.move`
（`ScanNR x` の下で `canRight x.vm.right`）をそのまま埋める。

## 2026-09-19 wave 7 後の偵察 — 残り 5 前提の構造

**全体 build 成功・標準公理のみ・無条件 PAL は未完。**
`pal_in_peg_final27`（5 前提）は main にマージ済み（PR #66）。

wave 7 完了後、残り 5 つ（`hSP`, `hws`, `hme`, `hor`, `hC`）の到達可能性を調べた。
**新しい定理は作っていない。以下は次 wave のための設計情報。**

### `hme`（`H_marksEntry'`）— 経路は存在するが `Fair` が必要

`CloseoutPackRun17` に **`H_marksEntry'` を一切使わない** run 版が既にある:

- `marksEntry'_of_layout`（`Run16:176`）は `ChooseLayout → MarksEntry'` を**副条件なし**で出す。
- `chooseLayout_of_wpack`（`Run17:118`）は `WPack` から `ChooseLayout` を出す。
- `marks_steps`（`Run17:406`）は `CPack`/`WPack`/`MarksInv'` を run に沿って同時に運ぶ。
- `marksInv'_of_run'`（`Run17:430`）が結論。

残る入力は 3 つ:
1. `h4 : first ≠ 4` — `first` の選択に関する側条件（`Fin 9` の 9 通り中 8 通りで成立）。
2. `hfl : ∀ m z, Steps … → z.ctl.mode = scan → 0 ≤ value z.vm.length`。
   **`CPack.canon : Canonical s.length` では出ない**（`Canonical` と `0 ≤ value` は
   リポジトリ内でも常に別々の条件として並記される、例 `CloseoutPackRun49:85`）。
3. `hwin : ∀ m z, … → z.ctl.mode = copy → WindowInOrigin z.vm`。
   `WindowInOrigin s := (stream s.fpp.walker).length ≤ position s.right`（FPP walker、
   `WalkerInOrigin` の**主 walker とは別**）。producer は `CloseoutPackRun25:124` だが
   **`FairSteps` を要求する**（`windowInOrigin_of_fair` が `Fair` の `fallbackPlace` を使う）。

**したがって `hme` の除去は `PackRunRMG2P` の run を `Steps` から `FairSteps` へ
上げる作業とセットになる。** `Fair` 自体は `GalilTickFair` で完成しており
（`Tick ∧ Fair` は全状態で一意）、構成側の witness が `Fair` を満たすことの確認が
別途必要。これが次 wave の主題。

### `hws`（`WatchShiftG`）— 5 連言のうち 1 つは wave 7 で無料に

`WatchShiftG`（`CloseoutPackRun26`）は `ScanNR x → x.vm.chain ≠ idle → compare x.vm s'' →
s''.chain = .watch wch →` の下で 5 つを主張する:

1. `canRight x.vm.right` — **wave 7 の `extra7_of_front_steps_pack` で出る**（`ScanNR` は
   `Extra7` の発火条件と同一）。
2. `4 * periodLength wch ≤ value wch.machine.control.distance`
3. `∀ rad, ScanInvariant … → value wch.machine.control.distance ≤ 2 * rad`
   — 素材は `Coupled'.sum : SumRel s.chain (value s.radius)`、
   `SumRel (.watch w) R = (broken = false → distance + lag = R)`（`GalilChainCoupling`）。
   `lag` の非負性と radius の一致（`RadiusRep`）が要る。
4. `canRight wch.machine.verifier`
5. `Sane wch.machine.verifier`

`Coupled'.block : BlockInv s.chain` は `.watch w` で `WatchBlock w = OnBlock w.machine.control.period`
のみ。**4 と 5（chain の verifier ヘッドの健全性）は既存の不変量に無い。** 新規に要る。

### `hSP`（`ShiftPal`）— 空虚ではない

`ShiftPalAt w s s'`（`CloseoutPackRun31`）は `s'.chain = .watch wch → shiftGuardVM s' →
∀ r₀, ScanInvariant … → 1 ≤ periodLength wch ∧ periodLength wch ≤ r₀ + 1 ∧
PalAt (encoded w) (center + periodLength wch) (r₀ + 1 - periodLength wch)`。
`ShiftLocalG` を空虚にした「`InvLPC` の chain は idle」の手は使えない
（run 途中では chain は動いている）。実質的な周期・回文の主張で、
Galil の move 補題（`GalilMoveLemma`）圏の内容。

### `hor` / `hC`

`hor`（`CycleOracleMC3`）: producer はゼロのまま（6 consume, 0 produce）。最大の残り。
`hC`（`H_realizeLIMG2'`）: `h_realizeLIMG'_of_G2`（`Run36:499`）で `H_realizeLIMG'` に
還元される。局所機械の実現。

## 2026-09-19 wave 7 — `hee`/`het` を **無条件化**: 最上位は **5 前提**

**`pal_in_peg_final27`（`CloseoutExtraFinal`）— 標準公理のみ・5 前提。**
残り: `hSP`, `hws`, `hme`, `hor`, `hC`。

`hee`（`H_extraEntry7`）と `het`（`Extra7` の tick 保存）は、どちらも
`packRunR_MG27` の `hprefix`（`CloseoutPackRun46:229`）を作るためだけに存在した。
`hprefix` は「`InvLPC` 起点の run の各点で `Extra7`」、すなわち scan かつ
非 replaying な各状態で `canRight`。

wave 5 の `CloseoutCanRightBound.extra7_of_bound` は位置上界からこれを出すが、
`PackRunRMG2` に位置上界が無かった。**上界は front ポテンシャルに乗って伝わる。**

- `GalilRunTrace.front s = position s.right + value s.replay`（`:39`）は
  `CentreLive` run 上で単調（`GalilFrontMono.front_stepsAll_mono`、**既存**）。
- `FrontPack.rest` は `ReplayRest`、すなわち `c.replaying = false → s.replay = reset`。
  よって**非 replaying 状態では `front s = position s.right`**（`front_eq_position`）。
- ゆえに run の出口 `y` が非 replaying かつ cycle の上界を持てば、
  `position x.right = front x ≤ front y = position y.right ≤ 2m-1`。

右ヘッド自身の単調性（34 ケースの `Tick` 解析）は**一切不要**。

`extra7_of_bound` の残り 2 入力（`Represents … w`, `focus ≠ none`）は
`LPackM.scanGeom`（`CloseoutPackRun10:139`）の `ScanInvariant` から出る。
`scanGeom` の発火条件は `mode = scan ∧ replaying = false` で、
**`Extra7` が語る条件と完全に一致**する（`rrep_of_lpackM`）。

帰納の循環（`Extra7 (g (n+1))` が構築中の pack を要求）は
`bigPack2MG7''_tickE` が `Extra7` を**その pack の関数として**受け取ることで解消。

呼び出し側は全て上界を持っている:
- 進行分岐: `CycleOutMC3` の定義に `position sT.right ≤ 2m-1`（`GalilInvPlus3:213`）、
  非 replaying は `InvLPS` から `invS_mode`。
- checkpoint 分岐: `ReportPointAt`（`GalilReportPrefix`）の場が
  `notReplaying`, `atPlace : position = 2m-1`, `pos : 1 ≤ m`, `le : m ≤ w.length`。

| 新規ファイル | 内容 | 公理 |
|---|---|---|
| `CloseoutFrontExtra` | `front_eq_position`, `position_le_of_front_steps`, `rrep_of_lpackM`, `extra7_of_front_steps_pack` | 標準 |
| `CloseoutExtraFree` | `steps_to_end_of_trace`, `bigPack2MG7''_tickE`, **`packRunR_MG27P`**（`Extra7` 入力ゼロ） | 標準 |
| `CloseoutExtraOracle` | `reachAtIMG2S_of_reachAtC3R_P`, `cycleOutIMG2S_of_cycleOutMC3R_P`, `h_oracleIMG2S_of_MC3_P` | 標準 |
| `CloseoutExtraFinal` | **`pal_in_peg_final27`（5 前提）** | 標準 |

**台帳判定**: `hee` → **PROVED**、`het` → **PROVED**。
wave 5 の「`hee`/`het` の残差は偽の疑いが強い」という記録は**誤り**だった。
偽なのは「任意の状態で `canRight`」であって、run 文脈では真。訂正する。

**全体 build 成功・標準公理のみ・無条件 PAL は未完。**

## 2026-09-19 wave 6 — `hsc`（`H_stageScan`）を **完全除去**: 最上位は **7 前提**

**`pal_in_peg_final26`（`CloseoutStageFinal`）— 標準公理のみ・7 前提。**
残り: `hSP`, `hws`, `hee`, `het`, `hme`, `hor`, `hC`。

`hsc` は wave 5 で **REFUTED**（`InvScan` の 11 場は `s.radius` に触れないのに
`ReplayStage` は `Canonical radius` を要求）。今回の結論は、**再切り出しすら要らず
そのまま消える**というもの。

根拠の連鎖:

1. `hsc` の主経路上の消費者は `cycleOracleIMG2_of_cycleOracleMC3R`
   （`CloseoutPackRun36:673`）ただ 1 つ。そこで `hstage_of_scanBranch` を呼び、
   `InvLPC` を `CycleOracleMC3` の要求する `InvLPS` に持ち上げている。
2. その `hstage_of_scanBranch`（`CloseoutOracleI2:179`）は
   `rcases hIC.1.1.1.1 with h | ⟨k, h⟩` で分岐し、**`Inv` 側は
   `replayStage_of_inv h` で無条件に閉じている**。`hsc` が要るのは `InvScan` 側だけ。
3. ところが `CycleOutMC3` は **両方の出口で `InvLPS` を返している**
   （`ReachAtC3` の継続 `GalilInvPlus3:193`、進行分岐 `:212`）。
   `reachAtC2_of_3` と `cycleOutIMG2_of_cycleOutMC3R` が `hIS.1` で捨てていただけ。
4. boot も `Inv` 分岐に着地する: `GalilFinalAssembly4.invLPC_init:94` が
   `hI : Inv (a :: rest) … t` を作ってから、どちらの選言だったかを忘れている。

すなわち **stage は、必要とされるすべての地点ですでに産出されている**。
Run36 §2 のチェックポイント再帰を `InvLPC` ではなく `InvLPS` の上で走らせれば、
`hstage_of_scanBranch` は一度も呼ばれない。

| 新規ファイル | 内容 | 公理 |
|---|---|---|
| `CloseoutStageRecur` | `reachIMG2_fuel_stageFree`（`InvLPS` を運ぶ再帰）, `cycleOracleIMG2_stageFree` | 標準 |
| `CloseoutStageCheck` | Run36 §2 を `InvLPS` 上で再走: `ReachAtIMG2S`/`CycleOutIMG2S`/`CycleOracleIMG2S`/`checkpoints_costIMG2S_upto1`/`preTraceIMG2S_exists` | 標準 |
| `CloseoutStageBoot` | `invLPS_init` — `invLPC_init` に `replayStage_of_inv hI` を足しただけ | 標準 |
| `CloseoutStageOracle` | `h_bootIMG2S_of_bootIPack`, `h_oracleIMG2S_of_MC3`（**`hsc` 引数なし**） | 標準 |
| `CloseoutStageFinal` | `pal_in_peg_final5MG2S`, **`pal_in_peg_final26`（7 前提）** | 標準 |

**ドロップイン性の要点**: `preTraceIMG2S_exists` の結論 `PreTraceIMG2` は
Run36 の同名 structure **そのもの**（StageCheck 側の複製定義は削除済み）。
よって下流（`h_trailI_MG2` / `needIMG2'_le` / `pal_in_peg_of_latch'`）は無改造。

**台帳判定**: `hsc` → **REMOVED**（REFUTED のまま、置換も不要）。
wave 5 で書いた `InvScanS` / `InvLPCS` 再切り出し（`CloseoutStageSupply`,
`CloseoutStageFree`, `CloseoutStageLanding`, `CloseoutStageScan1`）は
**この経路では不要**になった。`CycleOracleMC3` を無条件に作る段（`hor`）で
replay 着地の stage を供給するときに再利用できるので残す。

**全体 build 成功・標準公理のみ・無条件 PAL は未完。**

## 0. 最上位

`pal_in_peg_final25` — `PalPeg/CloseoutPackRun51.lean`（`final24` + `hbs`/`hls`/`hsl` 供給）。状態 `OPEN`（下記 **8** 前提が未供給）。

前提: `hSP`, `hws`, `hee`, `het`, `hme`, `hsc`, `hor`, `hC`。
`hbs`/`hls`/`hsl` は §2 の通り、木の中の定理で供給済み（`final24` の 11 前提 → 8）。

> 注意: `final13 → final24` の番号の増加は、**義務の減少を意味しない**。多くは
> 同じ義務の再定式化であり、実際に主経路から消えた義務は §2 に列挙したものだけ。

### 8 前提の素性（2026-09-19 の調査で全部割れた）

| 前提 | 種類 | 残り |
|---|---|---|
| `hee` / `het` | **道具あり・検証済み** | `CloseoutClockFront.extra7_of_run` が `CloseoutPackRun46.extra7_steps` を置換して同時に消える |
| `hsc` | `H_stageScan`（`CloseoutOracleI2:173`） | 最上位引数 | **REFUTED**（§4）。**2026-09-19: 連鎖が全段つながった（標準公理のみ、`final25` への配線は未了）**。突破口は `ReplayStage`（`GalilFoundStage:98`）が着地状態に `Restarted` を要求せず、**`Restarted` な祖先から `WatchSegE` で到達したこと**だけを言う点。着地でこれは真。(a) 消費側 `CloseoutStageSupply.invLPS_of_invLPCS` が `hstage_of_scanBranch` の `hsc` 無し版。(b) 橋 `CloseoutStageFree.cycleOracleIMG2_stageFree` で `hsc` が `hup : InvLPC → InvLPCS` に置換。(c) 産出側 restart 枝は `invLPCS_of_inv`、replay 枝は `CloseoutStageLanding.invLPCS_of_replayLanding`（`ReplayLanding` の `rest : Restarted raw s 0 reset` と `clock : c.clock = 2048`、`replay_after_fallback` が返す `hseg` の 3 つがそのまま `invLPCS_of_seg` の入力）。残るのは `invLPC_after_replayLanding` の結論に `InvLPCS` を通す編集と、`final25` の引数列からの除去。 | `pal_in_peg_final25` |
| `hme` | **道具あり・検証済み** | `hcan`・`hplace` は定理化済み。残りは走行の各 tick が `Fair` を満たすことの監査のみ（`tick_fair_unique` は `GalilTickFair:437` で証明済み） |
| `hSP` | 残差絞り込み済み | `ChainRound` 経由 |
| `hws` | `WatchShiftG`（chain–scan 結合） | 最上位引数 | `ChainPosInv2`（`CloseoutPackRun41:215`）+ `Coupled'`（`PackRun40:77`） → `MatchRes2`（`PackRun48:208`）。**`matchRes2_of_lpackM3`（`PackRun49:420`）は完成済み**で、残差は `MatchRest`（`PackRun49:405`）の 4 場 `repV`/`repVmid`/`replayPay`/`canRNext`。**そのうち `canRNext` は位置上界から出る**（`CloseoutCanRightBound.canRight_next_of_bound`、2026-09-19 証明）。 | `pal_in_peg_final25` |
| `hor` | **別種** | 葉 15 個。閉 9、進行中 3、未着手 3（`hfound`/`hfoundBg`/`hfoundReplay` の found 経路構成） |
| `hC` | **別種** | `H_realizeLIMG2'` は局所機械の**存在証明**（`∃ Q' Γ' … L, ∀ w, SAccepts ↔ LatchTrue`）。仮定を減らす対象でなく機械を作る対象 |

---

## 1. OPEN（主経路に残る意味的義務）

| ID | 意味 | 現在の宣言 | 供給元 | 利用側 |
|---|---|---|---|---|
| `hSP` | scan 状態での `ShiftPal`（shift 入口の回文性） | `CloseoutPackRun36:712` の引数 | `ChainRound`（`CloseoutPackRun31:183`）→ 残 `H_shiftDone`(閉)/`H_advance`/`H_birth`/`H_fresh`/`H_matched` | `lTickLeaves2_of_shiftPalG` |
| `hws` | `WatchShiftG`（chain–scan 結合） | 同上 | `ChainPosInv2`（`CloseoutPackRun41:215`）+ `Coupled'`（`PackRun40:77`） → 残 `MatchRes2` の `repVmid`/`replayPay`、新規場 `CentreLedger`、`LagCan` | `rShiftNextMG_of_watchShiftG` |
| `hee` | `Extra7` 入口（`mode = scan ∧ ¬replaying → canRight right`） | `CloseoutPackRun46:284` | 残差は **1 つ**: `∀ c r, InvLPC w c r → position r.right ≠ 2*w.length`（`extraEntry7_of_end`）。**真偽が未確定で、偽の疑いが強い**: `Inv`（`GalilRunInv:29-49`）の 10 場のうち右ヘッドに触れるのは `input : Represents r.right.head raw` だけで、これは内容を縛るが**位置を縛らない**。入力を食い切った状態（`Tick.scan_wait` が回る状態）でも全場が成立しうる。攻め口は (a) `w = []` で `2*w.length = 0` と初期位置 `0` が一致する反例、(b) `InvLPC` への右ヘッド余裕場の追加（`hsc` と同じ再切り出し）。 | `bigPack2MG7''_tick` |
| `het` | `Extra7` tick | `CloseoutPackRun46:296` | 残差は **1 つ**: `(mode ≠ scan ∨ clock = 1) → y.mode = scan → ¬y.replaying → canRight y.vm.right` | 同上 |
| `hme` | `H_marksEntry'`（rewind 角） | `CloseoutPackRun16:165` | `h_marksEntry'_of_layout` → `marksEntry'_of_run`（`PackRun17:387`）。4 入力のうち **`hcan` は定理化済み**（`CloseoutReplayCanRight.hcan_of_cpack`）、**`hplace` も制限版が出た**（`CloseoutPlaceBound.hplace_of_order`、`GalilTrailOrder.Order.cr` から）。残るのは量化のずれ 1 点: `hwin` の産出元 `wpack_of_fair`（`PackRun25:121`）は `FairSteps` 上だが `marksEntry'_of_run` は `Steps` 上。原因は `windowInOrigin_tick`（`PackRun25:80`）が `Fair` を取ること。**`Fair` の一意性 `tick_fair_unique` は `GalilTickFair:437` で証明済み（sorry なし）**なので、残りは最上位走行の各 tick が `Fair` を満たすことの監査のみ。 | `pal_in_peg_final25` |
| `hsc` | `H_stageScan`（`CloseoutOracleI2:173`） | 最上位引数 | **REFUTED**（§4）。再切り出しの配線図: 消費側は `hstage_of_scanBranch`（`CloseoutOracleI2:179`）**ただ 1 つ**で、`InvS`（`GalilOracleDischarge:79`）の replay 枝から `InvScan` を取り出して `hsc` を当てている。よって `InvS` の replay 枝を `InvScan ∧ ReplayStage` に差し替えれば `hsc` は消える。産出側の第 1 段は証明済み（`CloseoutStageScan1.replayStage_of_replay_after_fallback`）。`InvS` の出現は 45 箇所で、そのうち replay 枝を作る産出点だけが `ReplayStage` の供給を要する。 | `pal_in_peg_final25` |
| `hor` | `CycleOracleMC3`（`GalilInvPlus3:216`） | 最上位引数 | **重要な訂正（2026-09-19）**: `h_oracle_of_leaves5`（`CloseoutOracle6:323`）の 15 葉は**旧系統 `H_oracle` 向け**で、`final25` が要求する `CycleOracleMC3` への橋は**存在しない**（`MC3` を産出する定理が repo に無く、消費する定理だけがある）。つまり `hor` は葉を潰す前に「`MC3` を出す定理を書く」段階がある。その日に向けて閉じた材料: **`hrs`（`RestartShape`）と `hbudget`（`ReplayBudgetR`）は無条件で証明済み**（`CloseoutRestartShape.restartShape_PofC` / `replayBudgetR_PofC`、後者は `decodesC` だけ）。`hended` も `GalilLeafReport.hended_C` で閉（残差 `EntryRefreshed` 1 つ）。`hshape`（`StartShape`）は `canRight s.center` を要求し `GalilWatchOkInst:61` が「導出不能」と明記。`EntryRefreshed` は出力の**完全性**（`IsPal → output = true`）を要するが `OutputRel` は健全性のみ。 | `pal_in_peg_final25` |
| `hbirth` | `M-periodOnly` の副産物。`afterBirth` が `S.onLetter`/`S.leftFirst`/`S.replayExhausted` を変えないこと。`Shared` の 3 場は抽象関数なので一般には偽 | `LocalTick1.tickL1_abs` / `LocalReplayParked.tickL1_abs''_nonreplay` の引数 | 具体 `PofC` で放電可能（`afterBirth` は `periodOnly` と `cycle` しか触らず、`replayExhausted = zero ∘ replay`）。未供給 |
| `hC` | `H_realizeLIMG2'`（局所実現） | `CloseoutPackRun36:488` | 局所側（`LocalSysConcrete`/`LocalRealizes*`）、`Fair` 依存 | `pal_in_peg_final5MG2` |

---

## 2. INTEGRATED（主経路から実際に消えた義務）

| ID | 何が起きたか | 根拠 |
|---|---|---|
| `Extra.failed` | **削除**。監査の結果どの消費側も読んでいなかった（`Extra'` の読み手は `scanAvail`/`rewindMargin` のみ；DP の実消費は `MismatchDp` が自前経路で `StageFailed` に到達） | `CloseoutPackRun42` §2 監査、`CloseoutPackRun43` |
| `Extra.cand` | **削除**（同上）。裸の向き変換 `H_candOrient` は反例あり（§4） | `CloseoutPackRun43`、`CloseoutCandOrient` |
| `Extra.ready` | **削除**。どのモードでも読まれていなかった | `CloseoutPackRun45` §0 監査、`CloseoutPackRun46` |
| `hsl` (`H_shiftLocalG`) | **定理化**。`InvLPC` のどの状態も chain は idle（`Inv.rest` → `Restarted` 第 1 連言、または `InvScan.chainIdle`）なので `ShiftLocalG` は空虚（`shiftLocalG_of_chainIdle`） | `CloseoutShiftLocalFree.chainIdle_of_invS` / `h_shiftLocalG`、`CloseoutPackRun51` で供給 |
| `rInitPackM` | 無条件で証明（pack は `AuxPack.front.notInit` により `init` に居ない） | `CloseoutPackRun21:88` |
| `WatchPrefixC` | 無条件の定理（`WatchSeg` の構成子族は排他、段は関数的） | `CloseoutWatchRound20:172` |
| `ShiftPeriodC` | 葉ですらなかった（`ShiftRoundDataL` の 2 場から導出）→ 削除 | `CloseoutWatchRound45:81` |
| `WindowEndC` | 仮定ゼロで閉（`LandingData.ScanInvariant` の `Represents` から） | `CloseoutWatchRound50:86` |
| `H_fourOther` | `Coupled'`（sharp `5h`）の下で定理に | `CloseoutPackRun40:306`、`coupled'_tick` は無仮定 |
| `hshift`（readiness） | 放電（`scan_shift` は比較量子を 1 つ消費し clock を 2048 に） | `CloseoutPreload38:51` |
| `hact`（readiness） | 形を slack 0 の節に直して消滅 | `CloseoutPreload39:57` |
| `hrot`（core） | `RTQueue.Inv` から導出、仮定でなくなった | `CloseoutCoreEnc22:180` |
| `near ≠ []`（core） | 消滅 | `CloseoutCoreEnc22` |
| `hbs`（`H_bootShift`） | **既に木の中の定理**。`initVM0` が `chain := .idle` にし、`shiftLocal_of_chainIdle` が `ShiftLocal` の全 5 場を潰す（`beginShiftVM'` は `chain = .watch` を要るが `chainAt_idle_ne_watch` が禁じる） | `CloseoutPackRun6:184`、供給は `CloseoutPackRun51.pal_in_peg_final25` |
| `hls`（`H_landShift`） | 同上。`initial` からの唯一の tick は `Tick.init` で chain は idle のまま（`GalilTrailFront.init_tick_inv`） | `CloseoutPackRun6:190`、同上 |
| `hsc` の再切り出し第 1 段 | `ReplayStage` は fallback replay の着地で**実際に構成できる**（`Restarted raw t 0 reset` と `c.clock = 2048` は呼び出し側に既にある）。`replay_after_fallback` が捨てていた `stage` フィールドを拾い直した。`H_stageScan` 自体は §4 の通り偽のままで、`InvScanS` への差し替えが残り | `CloseoutStageScan1.replayStage_of_seg` / `replayStage_of_replay_after_fallback` |
| `hpresT`（oracle） | `SegReachedW` が `HpresRepAt` の入力 2 つ（`StepsAll … SoundScanNR` と `mode = scan`）をそのまま持っていた | `CloseoutOracle7.hpresT_of_hpresRepAt`、oracle の前提が 15→14 |

---

## 3. `CycleOracleMC3` の葉（`hor` の内訳）

閉: `hex`, `hsearch`, `hends`, `hbudget`, `hrs`, `hended`, `hlastMatch`, `hstr`, `hfb`。

| 葉 | 状態 | 備考 |
|---|---|---|
| `hpres` | `REFORMULATED` | 普遍形は `GalilLeafPres.hpres_false_at` が反証。scan 側は `HpresAt` で放電（`CloseoutOracle5:64`）。replay 側 `hpresRep` は `GalilReplaySpan` に制限形を受ける版を追加する編集が必要（進行中） |
| `hstage` | `OPEN` | `ReplayStageInv`、mid-replay restart の `3·radius ≤ 5·last` |
| `hshape` | `REFORMULATED` | `StartShape` は偽 → `StartShape'`（`GalilReplaySpan.startShape'_of_decodes`） |
| `hlastMismatch` | `OPEN` | 最終文字分岐 + `EntryRefreshed` |
| `hmismatch` | `OPEN` | `hdp` → `MismatchDp`+`StageBudgetAt`、`hpos` → 区間予算 |
| `hfound`/`hfoundBg` | `OPEN` | 着地不変量に `Restarted`/`StageEntry` + found tick からの経路構成。**最大の未着手** |
| `hfoundReplay` | `OPEN` | 未着手 |
| `hreadyB` | `OPEN` | 着地での `RunEntriesAll` |

---

## 4. REFUTED（反例があり、修正対象）

| ID | 反例／理由 | 現在の扱い |
|---|---|---|
| `H_candOrient` | `W = [0,0,0,0,0,1]`, `n=5`, `lower=0`, `h=1`。接頭辞 3/5 は回文、`W.drop 3 = [0,0,1]` は非回文。Lean で確認（`CloseoutCandOrient.unrestricted_transport_false`、標準公理のみ） | 主経路から削除済み。正しい橋は `GalilDpSuffix.candidate_iff`（同一窓＋反転） |
| `Extra.scanMargin` | 1 文字語で反証（`ScanMargin2.margin_false_witness`） | 削除済み |
| `ShiftLocal`（無ガード） | 全 `scan→shift` 着地で偽（`shiftLocal_false_at_landing`、`Internal.idle` が有効） | `ShiftLocalG`（scan ガード付き）へ |
| `ReplayNoBusyC` | replay 中も found 量子で chain は始まる（Scala も同じ） | `ReplayRunW`（3 分岐）へ |
| `LandingFreshC` | `h` が普遍量化で `periodLength w' = 0` と `= 1` を同時要求 | `LandingFreshC'` + `ShiftPeriodC` へ分割 |
| `MismatchLandingLagZeroC` | lag 1 の `take` が guard を通る（`budget_counterexample`） | 着地限定 `MismatchLandingLagZeroL` へ |
| `WatchFreshC` | 全 watch 区間量化、`WatchSegE.stop` は任意 clock で成立 | 着地限定へ。ただし下記の通り着地版は空虚 |
| `WatchFreshAtC`（着地版） | **前提が充足不能 = 空虚**。着地の chain は `copy`（`chainStart` は `ChainVM.copy`、`ChainMatched` は構成子を保つ）であり `watch` ではない（`CloseoutWatchRound52.landing_chain_copy:120`、`landing_not_watch:135`、`watchFreshAtC_vacuous:148`）。**n72 の「文脈だけで閉じた」は誤り**で、`watchFreshAtC_of_ctx` は内容を持たない | 誕生時刻版 `WatchBirthFreshC`（watch 誕生は着地の `2h+3` prep tick 後、そこでの clock は `MatchClock.run 2048 2048 avPrep` で fresh でない）へ。`OPEN` |
| `ChainWatchPhaseC`（`n ≤ 2047`） | chain 周期は非有界なので copy/back 相は 1 クロック窓に収まらない | 相跨ぎ `ChainWatchReachM` へ |
| `LagPos`（`0 < lag`） | `Outer.immediate` は `zero lag` がガード | `LagCan`（`0 ≤ value lag`、自己保存）へ |
| `ScanRealized` | `ScanSupplyInv` と矛盾（`scanRealized_absurd`） | `PostRunPh`/`PostRunF`（到達可能接頭辞）へ |
| `hplace`（∀ 全状態の place 境界） | `placeC u = ⟨lettersOf u.center.head, u.center.gap⟩` は中心ヘッドしか読まず、`position u.right` は右ヘッドしか読まない。両者を結ぶ場が型に無いので、中心を 1 文字進めて右ヘッドを原点に置けば破れる | `CloseoutPlaceBound.hplace_false`。到達可能状態（`position center ≤ position right`）へ制限が必要 |
| `hpres`/`hpresRep`（普遍形） | `hpres_false_at` | `HpresAt`/`HpresRepAt` へ |
| `Extra3.failed`（全 scan 状態） | restart が DP を入口に reset | 削除（§2） |
| `hsc`（`H_stageScan`） | `InvScan`（`GalilReplaySegment:317-341`）の 11 場は**どれも `s.radius` に言及せん**が、結論の `ReplayStage` は `Restarted` 経由で `RadiusRep r.radius Rad`＝`Canonical r.radius` を要求する。`Counter = ⟨pos neg : List Unit⟩` で `⟨[()],[()]⟩` は値 0 の非 canonical な合法値なので、任意の `InvScan` 住人の `radius` だけをこれに差し替えれば 11 場は全部生き残り `ReplayStage` だけが壊れる（`s.length`/`s.cycle`/`s.periodOnly` でも同じ）。紙の議論であり Lean 項ではない | 再切り出し `InvScanS := InvScan ∧ ReplayStage`（`InvScan→InvScanO`、`SearchReady→SearchReadyB` と同じ型）。最初の一歩は `replayStage_of_replay_after_fallback` |

---

## 5. モデルの欠陥（修正単位）

| ID | 内容 | 状態 |
|---|---|---|
| `M-periodOnly` | Scala `ScaffoldChain.start()` は `periodOnly = false` **かつ** `cycle.reset()` を行うが、Lean のモデルはどちらも落としていた。修正: `chainBorn (found) (x : ChainVM) := x.isIdle && found`（誕生条件は「その遷移で新しい chain が実際に始まること」であって `found = true` ではない）と `afterBirth born s`（`GalilScaffoldTopSearch:70,77`）。`compareFound`/`backgroundS` の遷移先をこれで包んだ。 | **修正済み・検証中**。抽象側の破損は 2 モジュールのみ（`GalilScaffoldTopSegmentHeads.watchSegE_heads` は単調形 `t.periodOnly = true → s.periodOnly = true` に弱めた）。局所側は `LocalTick1` に `birthL`/`abs_birthL`/`inv_birthL`/`stepLocal_birthL` を入れ、`bgState` に誕生元 chain を渡し、局所歩数 `c₁` を 66 → 67 に上げて `tickL1_local`/`tickL1_inv`/`tickL1_abs` を再証明（sorry なし）。`tickL1_abs` は新たに側条件 `hbirth`（`onLetter`/`leftFirst`/`replayExhausted` が `afterBirth` 不変）を取る。`Shared` の 3 場は抽象関数なので一般には示せず、具体 `PofC` での放電が **OPEN**。回帰テスト `CloseoutPeriodOnlyRegression.birth_resets` が修正前は失敗し修正後は通る。 |

---

## 5b. 合成の方針: `canRight` 一本化

`hee`・`het`・`MatchRes2.canR`/`canRNext`・`walkerInOrigin_of_run` の `hcan` は**すべて同じ義務**
「その状態で右ヘッドがまだ動ける（入力が尽きていない）」に帰着する。個別に潰すのではなく 1 本の
走行補題で倒す。

1. 右ヘッドが進むのは比較のときだけで、1 回につき `position` はちょうど +1
   （`GalilScaffoldChainInputSupply.right_position`:500）。
2. 比較は `clock = 1` でのみ起き、その tick で clock は `delay` に戻る。よって比較は `delay` tick に
   1 回以下。
3. したがって `n` tick の走行で `position y.right ≤ position x.right + (n / delay + 1)`。
4. 入力枯渇は `position = 2 * w.length`（`GalilEndOfInput.not_canRight_iff`）。最上位の走行は
   `delay * w.length` tick なので `position ≤ w.length + 1 < 2 * w.length`（`1 < w.length`）。

**材料はすべて既存。**
* `front s := position s.right + value s.replay`（`GalilRunTrace:39`）は `front_tick_mono`
  （`GalilFrontMono:175`）で 23 構成子すべてについて単調が証明済み。増えるのは比較のときだけ。
* `Tick` の 23 構成子のうち clock を触るのは 5 つだけ（`GalilScaffoldTop:110-173` を実読）。
  `scan_count` が `clock - 1`、`scan_match`/`scan_shift`/`scan_fallback`/`replayStart`/`restart` が
  `clock := delay`、残り 17 は不変。よって**どの tick も clock を 1 より多く減らさない**。
* ポテンシャル `Ψ (c, s) := delay * front s - c.clock` は tick 毎に高々 +1。比較は
  `front` +1（`delay` 増）と clock `1 → delay`（`delay - 1` 減）で差し引き +1、非比較は
  `front` 不変で clock 減 ≤ 1。

**`PalPeg/CloseoutClockFront.lean` に一式を書き、`lean` で検証した（標準 3 公理のみ）。**

| 定理 | 内容 |
|---|---|
| `clock_drop_one` | どの tick も clock を 1 より多く減らさない（23 構成子） |
| `clock_le_delay` / `_steps` | clock は `delay` を超えない |
| `front_clock_tick` | **核心**。front 不変、または比較（front +1 かつ `clock = 1`、`clock' = delay`）。23 構成子のうち `Or.inr` は 3 つ（`scan_match` の非 replay、`scan_shift`、`scan_fallback`）だけ |
| `pot_tick` | `Ψ := delay·front − clock` は tick 毎に高々 +1 |
| `pot_steps` | `n` tick で `Ψ ≤ Ψ₀ + n` |
| `front_le_of_run` | 初期状態（`front = 0`, `clock = delay`）から `delay·front ≤ n` |
| `canRight_of_run` | `n < delay·(2·w.length)` なら右ヘッドは動ける |
| `extra7_of_run` | `Extra7` を走行から直接供給 |

**検証結果（2026-09-19）**: `clock_drop_one`, `clock_le_delay`, `clock_le_delay_steps`,
`front_clock_tick`, `pot_tick`, `pot_steps`, `front_le_of_run`, `canRight_of_run`,
`extra7_of_run` の 9 本すべてが `[propext, Classical.choice, Quot.sound]` のみで通った。
`front_clock_tick` の 23 構成子のうち比較枝（`Or.inr`）は 3 つだけであることも確認。

**接続点と残る障害（2026-09-19 の調査）**: `Extra7` は `BigPack2MG7''` の第 5 場で、
`packRunR_MG27`（`CloseoutPackRun46:223`）が走行の各点 `g i` で要求する。`hreach` が
`Steps … (j+i) ⟨c,r⟩ (g i)` を与えるので `extra7_of_run` の形には合う。

**ただし `extra7_of_run` は走行長の上界 `n < delay * (2 * w.length)` を要求し、
`PackRunRMG2`（`CloseoutPackRun36:588`）の `∀ (j : ℕ)` にはその上界がない。** これは
当初の見立ての誤りで、配線は 1 行では済まない。

**正しい route を実装した（`PalPeg/CloseoutCanRightBound.lean`、標準 3 公理のみで検証済み）**:
`CycleOracleIMG2`（`CloseoutPackRun36:256`）と `CycleOutIMG2`（:247）は**始点と終点の両方で
`position r.right ≤ 2 * m - 1` を保つ**設計で、`1 ≤ m ≤ w.length` なので
`position right ≤ 2*w.length - 1 < 2*w.length`。入力枯渇は `position = 2*w.length`
（`GalilEndOfInput.not_canRight_iff`）なので、これがそのまま `canRight` を与える
（`canRight_of_position_bound`）。

さらに `CostedRun.right_mono`（`GalilTraceCost:80`、右ヘッドは単調非減少）により、
出口の上界が走行の各中間点にも及ぶ（`canRight_of_costedRun`）。走行長の議論は不要。

残る作業は `packRunR_MG27` の `hprefix` をこの経路に差し替えること。

**この位置上界は 3 箇所に効く**（教訓: 同じ義務が名前を変えて複数箇所に出る）:
`hee`/`het`（`extra7_of_bound`）、`MatchRest.canRNext`（`canRight_next_of_bound`）、
`hor` の `hended`（既に `GalilLeafReport.hended_C` が同じ上界を使って閉じている）。

---

## 6. 運用規則

- 再定式化・改名でも同じ義務 ID を引き継ぐ。
- 「一つの仮定」に問題を詰め直して数を減らさない。
- 進捗率は報告しない。今回何が `INTEGRATED` になったかを報告する。
- 同じ義務が名前を変えて再登場したら、別名へ分解する前に、初期状態・遷移・量化範囲・供給元へ戻って監査する。
