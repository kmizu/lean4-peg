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
## 2026-09-19 n195: `ReadyPacedS` は過剰量化だった（測定済み）——インターフェイスを切り出した

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 3。
無条件 PAL は未完、§10.5 は未達。**

### 測定（n194 の宿題）

`CloseoutReadyStage` 全域で `ReadyPacedS` の使い方を数えた。
`watchSegE_constructS` / `segment_of_invLPCS` / `readyPacedS_watchSegE` /
`reachAtC3_of_crossS` / `reachAtC3_of_target_matchS` ——**全部**が次の 4 本だけを通る:

| 補題 | 何をする |
|---|---|
| `readyPacedS_ready` | `SearchReady` を取り出す（証人は `List.replicate n false` 1 本） |
| `readyPacedS_mono` | 添字を弱める |
| `readyPacedS_effect_false` | **背景量子 1 手**に沿って運ぶ |
| `readyPacedS_effect_true` | **比較量子 1 手**に沿って運ぶ |

**任意のリストに具体化している箇所は 1 つも無い。**
`ready` は固定の証人 1 本、`effect_*` は 1 要素の前置だけ。よって

    ReadyPacedS v n k := ∀ as, n ≤ as.length → PacedL 2048 k as → SearchReadyS v as

の `∀ as` は**消費者に対して過剰量化**（CLAUDE.md の 8 例と同じ型）。
これが効くのは `ReadyPacedS` が `CloseoutContracts.StageEntryC.fuel` だからで、
run 基底の readiness 線（`CloseoutPreload28/35/36`）は
**機械が取らないリストへの量化を原理的に出せない**（`CloseoutPreload36` の
「What this is and is not」）。

### 切り出したもの

`PalPeg/ReadyInterface.lean`（新規、1 構造体 ＋ 1 定理、標準 3 公理）:

    structure ReadyIface (P : Shared) (Φ : SearchVM → ℕ → ℕ → Prop) : Prop where
      ready      : Φ v n k → SearchReady v
      mono       : n ≤ n' → k' ≤ k → Φ v n k → Φ v n' k'
      background : k' ≤ k+1 → s.chain = idle → Φ (get s) (n+1) k →
                     searchEffect P false s v → Φ v n k'
      comparison : 2048 ≤ k+1 → s.chain = idle → Φ (get s) (n+1) k →
                     searchEffect P true s v → Φ v n 0

    theorem readyIface_readyPacedS (P) : ReadyIface P ReadyPacedS

4 場は既存 4 補題そのまま。**これが測定の形式的な記録**——
インターフェイスは `CloseoutReadyStage` が証明する内容より弱くなく、
`CloseoutReadyStage` が使う内容より強くない。

### まだ何も外れていない（正直な状態）

`watchSegE_constructS` とその 4 消費者を抽象 `Φ` に対して**再証明していない**。
機械的（4 つの補題呼び出しを 4 つの場に置き換えるだけ）だが長い。
それが済むまでこのファイルは何も落とさない。

### 次

1. `watchSegE_constructS` を `Φ` ＋ `ReadyIface P Φ` で再証明
2. `segment_of_invLPCS` / `readyPacedS_watchSegE` / `reachAtC3_of_crossS` を追従
3. `StageEntryC.fuel` を `∃ Φ, ReadyIface P Φ ∧ Φ …` に切り直す
4. run 線（`Preload28/35/36`）が run 添字の `Φ` を供給する

## 2026-09-19 n194: **n189 の書き方を訂正**＋2 本の線の食い違いが本当の壁

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 3。
無条件 PAL は未完、§10.5 は未達。コードは変更していない（訂正と診断のみ）。**

### 訂正（自分の誇張）

n189 で「準備相を歩きから切り離した／段境界を越える状態局所の背骨を作った」と書いたが、
**`CloseoutPreload28/35/36` の線はもともと状態局所だった。** 一次情報:

    CloseoutPreload35.dpSafe_of_stagePrepD_slack
      (hp : PrepAt k m v) … (hq : StagePrepS k m D slack v x (a :: as)) …

`StagePrepS _ _ _ _ w v as := ∃ bs, ReachP w bs v ∧ …` の基点 `w` が
**`PrepAt` 状態そのもの**（段の `begin` ではない）。段境界では
`prepAt_of_double_exit` が `PrepAt` を再成立させるので、この `ReachP` は往復で切れない。

`StageLocalPrep`（n189）が実際に足したのは 2 つだけ:
* 包装（`PrepPhase` = `PrepAt` ＋ `PrepTrace` ＋ 非 `.run`）
* `preloadAt_of_prepPhase` ——較正仮説
  `((stream s.walker).take (span+1)).length = stageWindow1 k` を落とした
  （消費者が読むのは `W.length ≤ m + 1` だけで、これは `List.length_take` でタダ）

**診断そのもの（`PostRun` / `NoReturn` がなぜ落ちないか）は有効。** 誇張したのは
「新しく作った」の部分。

### 本当の壁: 2 本の線が噛み合っていない

| 線 | `ReachP` の基点 | 状態 | 出せるもの |
|---|---|---|---|
| 旧（`Preload6/8/11/37`） | 段の `begin` ／ restart からの `ReachL` | `NoReturn` は偽、`PostRun` は producer なし | `ReadyPacedS`（**状態量化**）を `readyField2_entry_of_datum` で |
| 新（`Preload28/35/36`） | `PrepAt` 状態（境界で再成立） | **証明できる**（n190〜n193 で算術も詰めた） | run に沿った `DpSafeStage` のみ |

`CloseoutPreload36` 自身が「What this is and is not」でこう書いている——
run 帰納は機械自身の状態しか届かないので `PostRunPh` / `PostRunC` は作れない。

**食い違いの場所は `CloseoutContracts.StageEntryC.fuel : ReadyPacedS`。**
`ReadyPacedS v n k := ∀ as, n ≤ as.length → PacedL 2048 k as → SearchReadyS v as` は
**任意のペース付きリスト**に量化していて、新しい線は原理的にこれを出せない。

### 次にやること（公理への最短路）

`ReadyPacedS` が消費者に対して過剰量化していないかを測る
（CLAUDE.md の過剰量化 8 例と同じ検査）。消費者は
`CloseoutReadyStage.segment_of_invLPCS` / `readyPacedS_watchSegE` /
`reachAtC3_of_crossS` で、どれも **run に沿った watched segment** を作るために使う。
run 形に切り直せるなら、新しい線が `StageEntryC` を直接埋める。
切り直せないなら、旧線の `PostRun` を倒すしかない。**まずこれを測る。**

## 2026-09-19 n193: 算術の穴 2 は「boot 段だけ」に落ちた——しかも boot は slack 0

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 3。
無条件 PAL は未完、§10.5 は未達。**

`PalPeg/StageBudgetShift.lean` §2 に 1 本追加（標準 3 公理）:

    boot_windows_covered (hj : 1 ≤ j) : 16 ≤ 8 * 2 ^ j

### 筋が通った

boot では `lower = 0` で `grow` に入るので第 1 段の窓は `mw₀ = 8 * max 0 1 = 8`、
以降は倍々（`8, 16, 32, …`）。n192 のしきい値 `16` で
**第 2 段以降は全部覆われる**。残るのは boot 段 1 つだけ。

そしてその boot 段は **slack 0**——一次情報
`GalilScaffoldController.initial delay = ⟨.init, delay, false, false, false, false⟩`
（`GalilScaffoldController.lean:109`）で `clock = 2048`、slack `= 2048 - clock = 0`。
slack 0 の需要は `CloseoutPreload28.dpDemand`（`+2047` が無い方）で、その balance
`bal_of_paced_slack` が要るのは **`8 ≤ mw` だけ**。`mw₀ = 8` はちょうど満たす。

| 段 | 窓 | slack | 使う balance | しきい値 | 状態 |
|---|---|---|---|---|---|
| 第 1（boot） | 8 | **0** | `CloseoutPreload28.bal_of_paced_slack` | `8 ≤ mw` | 材料あり |
| 第 2 以降 | 16, 32, … | 任意 | `CloseoutPreload35.bal_of_paced_slack_S` | `16 ≤ mw`（n192） | **覆われた** |

**まだ組んでいない**: boot 段を `CloseoutPreload28` 経路で通し、第 2 段で
`CloseoutPreload36.postRunC_galil_of_boot` に接続する配線。
`CloseoutPreload36` §4 の **boot datum**（第 1 `.run` 入口の `EntryDatum`）も未証明。

### 算術の穴の現況（更新）

| # | 穴 | 状態 |
|---|---|---|
| 1 | `depth_exceeds_prepLen` | **閉（n190）** |
| 2 | slack 2047 の 2 単位 | **boot 段のみ、かつ boot は slack 0 で経路あり（n191〜n193）** |
| 3 | 段境界のイベント供給（`StageLegs` の `hlen`） | 未着手 |

## 2026-09-19 n192: しきい値 `32 → 16` を本線に入れた——`postRunF_step` の残差は `k ≤ 1` の**第 1 段だけ**

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 3。
無条件 PAL は未完、§10.5 は未達。**

n191 の `16 ≤ mw` を複製で持つのをやめ、`CloseoutPreload35.bal_of_paced_slack_S`
**そのもの**のしきい値を下げた（証明は同じ＋`16 ≤ mw < 20` の 4 窓を
`interval_cases`。`omega` は 2 つの `/2048` を含む tight な系で不完全）。
下流の `postRunF_round_trip_S` / `postRunF_round_trip_galil_S` / `postRunF_step` と
`CloseoutPreload36`（10 箇所）も `16 ≤ mw` に緩めた。

### 効き方

`CloseoutPreload35` §7 は `hmw : 32 ≤ mw` を
**「機械の run とモード註釈の外にある唯一の仮説」**と書いていた。
`postRunF_step` は較正 `8 * max k 1 ≤ mw` を持つので:

| しきい値 | 覆われる段 | 残差 |
|---|---|---|
| `32`（旧） | `k ≥ 4` | `k ≤ 3` |
| **`16`（新）** | **`k ≥ 2`** | **`k ≤ 1`** |

さらに `mw0 = 8 * max k 1` で窓は倍々になるので、`k ≤ 1` でも
**第 1 段（窓 8）だけ**が残る——第 2 段は窓 16 で覆われる。

`PalPeg/StageBudgetShift.lean` §2 は複製を消して、この残差の記録だけにした:

    window_covered_of_k (hcal : 8 * max k 1 ≤ mw) (hk : 2 ≤ k) : 16 ≤ mw
    window_residual    (hcal : 8 * max k 1 ≤ mw) (hmw : mw < 16) : k ≤ 1 ∧ 8 ≤ mw

### `D ≤ prepLen k` は 2 箇所で意味が違う（n190 の補足）

* `CloseoutPreload6.runEntriesS_of_namedG` の `D`: **restart から**測るので
  grow 相の `max k 1` ティックと `prepare` dispatch を含む → `prepLen k` を超える
  （`depth_exceeds_prepLen`）。n190 の `budget_adv_shift` がここを直す
* `CloseoutPreload35.dpSafe_of_stagePrepD_slack` の `D`: **`PrepAt` 入口から**
  測るので準備相のティックだけ → `prepLen k` で正しい。**ここは直す必要がない**

## 2026-09-19 n191: 2 つめの算術の穴を `32 ≤ mw` → `16 ≤ mw` に縮めた（残りは `k ≤ 3`）

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 3。
無条件 PAL は未完、§10.5 は未達。**

`PalPeg/StageBudgetShift.lean` §2（3 定理追加、標準 3 公理のみ）:

    bal_of_paced_slack_S16 … (hmw : 16 ≤ mw) … :
      4 * dpDemandS k (2*mw) + 4 * (bs ++ [a]).count true ≤ mw
    window_covered_of_k (hcal : 8 * max k 1 ≤ 2*mw) (hk : 4 ≤ k) : 16 ≤ mw
    window_residual (hcal : …) (hmw : mw < 16) : k ≤ 3 ∧ 4 ≤ mw

### 記録が両端とも間違っていた

`CloseoutPreload35` §3 は残差を「4 窓 `8 ≤ mw < 32`」と記録していたが、
**同じ入力**（`prepLen_le` / `dpEvents_win_le` / 窓全体のペーシング）で
`16 ≤ mw` から成立する。`32` は保守的な当て推量だった。
`mw ≤ 3` は `8 * max k 1 ≤ 2*mw` が `4 ≤ mw` を強制するので空虚。
**真の残差は `4 ≤ mw ≤ 15`、較正 `4 * max k 1 ≤ mw` で言い換えると `k ≤ 3`。**

`16` はこの入力に対して sharp: `mw = 15` では最悪の
`(prepLen k, dpEvents (2mw+1), count)` が balance `16 > 15` を与える。
余裕が 2 以下なのは `mw ∈ {16,17,18,20,21,22}` だけ（`mw=16` と `mw=20` で 0）。

証明は `mw < 20` / `mw ≥ 20` で分割。前者は `4 * max k 1 ≤ mw ≤ 19` から
`max k 1 ≤ 4` が出るので `interval_cases mw` で 4 ケース。
後者は `omega` が直接通る（`16 ≤ mw` のままでは `omega` が
2 つの `/2048` を含む tight な系で落ちる——反例は無い、不完全性）。

### 算術の穴の現況

| # | 穴 | 状態 |
|---|---|---|
| 1 | `depth_exceeds_prepLen`（`D ≤ prepLen k` が満たせない） | **閉（n190）** |
| 2 | slack 2047 の 2 単位（`CloseoutPreload35` §3） | **`k ≤ 3` に縮小（n191）** |
| 3 | 段境界のイベント供給 | 未着手 |

## 2026-09-19 n190: 記録済みの否定的結果（`depth_exceeds_prepLen`）を予算の緩和で閉じた

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 3。
無条件 PAL は未完、§10.5 は未達。**

`PalPeg/StageBudgetShift.lean`（新規、3 定理、標準 3 公理のみ）:

    budget_adv_nat_shift {k Rad adv m} (hstage : 3 * Rad ≤ 5 * k)
      (hadv : 2048 * adv ≤ prepLen k + max k 1 + 1)      -- ← 緩めた
      (hm   : 2048 * m ≤ prepLen k + dpEvents (stageWindow1 k) + 2048) :
      adv + m + Rad ≤ 2 * max k 1
    budget_adv_shift      -- ℤ 版（結論は stageDebt Rad k）
    budget_adv_of_shift   -- 旧 budget_adv を含むことの確認

### 何が閉じたか

`CloseoutPreload7.depth_exceeds_prepLen`（機械検査済み）は
**`CloseoutPreload6.runEntriesS_of_namedG` の側条件 `D ≤ prepLen k` が
満たせない**ことを言っていた: 実際の入口深さは
`max k 1 + 2 + (prepLen k - 1) = prepLen k + max k 1 + 1`
（`depth_le_prepLen_shifted`）で、`prepLen k` より真に大きい。
grow 相の `max k 1` ティックと `prepare` dispatch を数え落としていた。

`D ≤ prepLen k` の唯一の使い道は `budget_adv` の `2048 * adv ≤ prepLen k` なので、
そこを**実際の深さちょうど**に緩めた。結論は不変。

### 両側とも tight

* `k ≥ 9`: 緩い上界（`prepLen_le` / `dpEvents_stage_le`）で足りる——
  `3·2048·(adv+m+Rad) ≤ 11548k + 6429 ≤ 12288k` は `k ≥ 9` と同値
* `k ≤ 8`: 9 個の具体ケース。`k = 1, 2, 3, 5, 6` では**余裕がちょうど 0**

（数値確認: `k = 0..5000` と `10^5, 10^6, 10^7` で成立。余裕は `k=9,10` で 1、
`k=20` で 2、`k=100` で 13、`k=10^6` で 120809。）

### 読み方

これは readiness 連鎖の**算術の穴 3 つのうち 1 つ**。残り 2 つ:
`CloseoutPreload35` §3（`8 ≤ mw < 32` の 4 窓、slack 2047 で 2 単位吸収できない）と、
段境界でのイベント供給。**公理は減っていない**（穴は公理の下にある）。

## 2026-09-19 n189: 準備相を「歩き」から切り離した——段境界を越える状態局所の背骨

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 3。
無条件 PAL は未完、§10.5 は未達。**

`PalPeg/StageLocalPrep.lean`（新規、4 定理、**全部 `[propext, Quot.sound]` のみ**）:

| 定理 | 内容 |
|---|---|
| `prepPhase_start` | `PrepAt k m v → PrepPhase k m 0 v` |
| `prepPhase_step` | `.run` に入らない 1 手で保存（`k`/`m` 不変、`n` だけ増える） |
| **`prepPhase_of_double_exit`** | **段境界で再成立**（`.double` 出口だけから） |
| `preloadAt_of_prepPhase` | dispatch で DP の preload、窓は `w.length ≤ m + 1` |

    def PrepPhase (k m n : ℕ) (v : SearchVM) : Prop :=
      (∃ e, PrepAt k m e ∧ PrepTrace e n v) ∧ v.search.mode ≠ Mode.run

### なぜこれが要るか（n187〜n189 の診断の決着）

`PostRun`（`CloseoutPreload8:253`）と `NoReturn`（`CloseoutPreload5:599`）は
**同じ欠陥**で、どちらも producer が無い:

* `NoReturn u := ∀ bs v, ReachL u bs v → v.mode ≠ .run → ReachP u bs v`
  ——`run → wait → double → prepare` の往復を通った歩きは `ReachP` ではないので**偽**
* `PostRun := ∀ v as, v.mode = .run → DpSafeStage v as → RunEntriesS as v`
  ——`.run` 入口で台帳を丸ごと作り直せと言っている

両方の根は `StagePrep2`（`CloseoutPreload11:293`）の第 1 節
`ReachP w bs v`——**その段の `begin` からの歩き**。機械は最初の `.run` 入口で
そこを永久に離れるので、次の段では再成立しない。

**しかし消費者が実際に使うのは状態局所の事実だけ**（`CloseoutPreload2.preloadAt_of_prepRun`
が要るのは「新鮮な `.lower` 入口 `e`」と「`PrepTrace e n v`」の 2 つ）。
`CloseoutPreload10.PrepAt k m` がその新鮮な入口で、
`prepAt_of_double_exit` が**段境界でそれを再成立させる**（歩き不要）。
だから `PrepPhase` は往復を越えられる。

### 副産物: 較正仮説が 1 つ消えた

`preloadAtEntry_of_trace` は
`((stream s.walker).take (span+1)).length = stageWindow1 k` を要求していたが、
消費者 `CloseoutPreload11.dpSafe_entry_km` が読むのは `W.length ≤ m + 1` だけ。
これは `List.length_take` でタダ。`preloadAt_of_prepPhase` は較正を取らない。

### 残り（ここには入れていない）

段境界での**リスト側の帳簿**——ペーシング、イベント供給
（`dpEvents (m+1) ≤ as.length`）、負債。これが `CloseoutPreload35` §3 の
`8 ≤ mw < 32` の 4 窓の算術と同じ場所。

## 2026-09-19 n188: `.run` 相で `RunEntriesS` が縮む原子を作った（`PostRun` 整礎化の第一歩）

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 3。
無条件 PAL は未完、§10.5 は未達。**

`PalPeg/PostRunInduction.lean`（新規、1 定理、標準 3 公理のみ）:

    runEntriesS_cons_of_run (hm : v.search.mode = Mode.run)
      (hnext : ∀ center v', searchStep center a v v' → RunEntriesS as v') :
      RunEntriesS (a :: as) v

`RunEntryS center a v v' as` の第 2 仮説が**源の mode が `.run` でない**ことを要求するので、
源が `.run` なら空虚。残るのは行き先の `RunEntriesS as v'` だけ。

**これが `PostRun` を整礎帰納に置き換えるための原子。** `runEntriesS_of_stageInv2`
（`CloseoutPreload11:296`）が `PostRun` を必要とするのは `as` への帰納が `.run` 入口で
**縮まない**からで（`hpost v' as hr hsafe` を同じ `as` に使っている）、
`.run` 相でもイベントは消費されるのでこの補題で縮む。

### 既にある材料（n187/n188 で確認）

| 部品 | 場所 |
|---|---|
| `.run` 相のトレース | `CloseoutPreload13.RunTrace:79` |
| `.run` 相の 1 手の中身 | `CloseoutPreload13.run_step_quanta:85` |
| `.run` 出口のデータ（債務・`ExitMode`・次相の span/work） | `CloseoutPreload13.run_exit_frame:146` |
| 次の `.run` 入口の datum | `CloseoutPreload35.postRunF_next_entry`（§5） |
| 1 入口 → 次入口 | `CloseoutPreload35.postRunF_step`（§6） |
| **`.run` 相で `as` が縮む** | **`PostRunInduction.runEntriesS_cons_of_run`（n188）** |

### 残り

* 整礎帰納の組み立て（`as.length` で測る）
* **per-stage の供給条件**（各 stage 入口で残りイベントが `dpEvents (m+1)` 以上）——
  これは run に沿ってしか言えないので、`PostRun` を trace/run 形に切り直す必要がある（n187）
* `8 ≤ mw < 32` の 4 窓の算術（n186）

## 2026-09-19 n187: **`PostRun` に producer が無い理由が割れた**（落とした供給条件）

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 3。
無条件 PAL は未完、§10.5 は未達。**

コウタの指摘「**producer がないときは確実に形式化ミス**」を当てはめた。

    PostRun := ∀ v as, v.search.mode = .run → DpSafeStage v as → RunEntriesS as v

**`∀ v as` が run にも供給条件にも縛られていない。** 消費者が持っているのに
文が落としているものが 2 つ:

| 消費者（`StagePrep2` / `runEntriesS_of_restartS2`） | `PostRun` |
|---|---|
| `PacedL 2048 0 (bs ++ as)` | **無い** |
| `D + dpEvents (m+1) ≤ bs.length + as.length`（列が十分長い） | **無い** |

**短さで落ちることは既に機械検査済み**: `CloseoutPreload3.not_runEntriesS_eight`
（節タイトル「`RestartEntryS` is false: **the paced list may be too short**」）。
8 番目のイベントで `.run` に入ると残りが `[]` になり `DpSafeStage (w p8) []` の
課金プレフィックスが空 → `dpSafeStage_pre_ne_nil`。
**同じ証人が `PostRun` も落とす。**（`REFUTED` とはまだ書かない）

### なぜ帰納が止まっていたか

    StageInv2 k m D w v as := StagePrep2 k m D w v as ∨ RunEntriesS as v

`runEntriesS_of_stageInv2` は `as` に帰納するが、`.run` 入口で `hpost v' as hr hsafe` を
使うので **`as` が縮まない**。`.run` 相でもイベントは消費されるので本来は
`as.length` の整礎帰納で閉じられるはずだが、**各 stage 入口で「残りが十分長い」が要る**。
それが落とした供給条件で、**run に沿ってしか言えない**。

→ **`PostRun` は trace/run 形に切り直す。** CLAUDE.md の「global 形は原理的に落ちない」
がそのまま当てはまる（`hav` / `hpack` / `hpres` / `RunEntriesAtBegin` に続く 5 例目）。

### 次

1. `PostRun` の反証を書く（`not_runEntriesS_eight` の証人を流用）
2. run 形 `PostRunAlongRun` に切り直す
3. `runEntriesS_of_stageInv2` を整礎帰納で書き直し `hpost` を外す

## 2026-09-19 n186: `PostRunF` 帰納の**具体的な穴**が出た（`8 ≤ mw < 32` の窓）

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 3。
無条件 PAL は未完、§10.5 は未達。**

`CloseoutPreload35` の冒頭（一次情報）が穴を明記していた:

> §3 the `.double` exit satisfies `StageInvS` when `32 ≤ mw`
> (`bal_of_paced_slack_S`, `stageInvS_of_double_exit`); **the four windows
> `8 ≤ mw < 32` do not absorb the two extra units at slack `2047`**

帰納段 `postRunF_step`（§6）と次入口の構成 `postRunF_next_entry`（§5）は**ある**。

### 穴の大きさ

窓は restart で `mw = 8 * max k 1`、`.double` で倍々。だから
`8 ≤ mw < 32 ⟺ k ≤ 3` の初期 stage だけ。`k ≥ 4` なら `8k ≥ 32` で §3 が閉じる。
**境界ケースは 4 つ**。

### もう 1 つの穴: 帰納の基底

`postRunF_step` は帰納段で、**基底（boot / restart 後の最初の `.run` 入口の datum）を
出す定理は見つかっていない**。`CloseoutPreload.run_entry_preload:130` は
`.run` 入口の DP 機械の同定という局所事実で、基底ではない。

### 次（優先順、`PROOF_STACK.md` に記録）

1. `8 ≤ mw < 32` の 4 窓を `dpDemandS` の算術で詰める
2. 基底を探す/作る（restart 直後の最初の `.run` 入口）
3. 1 ＋ 2 ＋ `postRunF_step` で `PostRunF` の帰納を閉じ `PostRun` へ

**これが `shiftPalResiduesAlongRun` と `cycleOracle` の共通の底の最後。**

## 2026-09-19 n185: `PostRun` / `RestartS2` の地図（`readiness` 部分系、最深部）

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 3。
無条件 PAL は未完、§10.5 は未達。**

n184 で `StageEntryC` を修理したので、次の底は `RdPaced` の producer
`CloseoutPreload11.readyClosure_S2` が取る `PostRun` ＋ `RestartS2`。探した結果:

* `PostRun`（`CloseoutPreload8:253`）の変種の鎖は揃っている
  （`postRunP_of_postRun` / `postRunC_of_postRunP` / `postRunPh_of_postRunP` /
  `postRunC_of_postRunPh` / `postRunC'_of_double_leg`）が、**全部「変種 → 変種」**
* 帰納段 `CloseoutPreload35.postRunF_step` と脚のデータ `CloseoutPreload36.StageLegs` はある
* **基底が無い**（`PostRun*` を仮説なしで出す定理は 1 本も無い）
* `RestartS2`（`CloseoutPreload11:320`）も **producer 無し**
* `CloseoutPreload` は 1〜41 の 41 ファイル。**プロジェクト最深部**

`CloseoutPreload41` の冒頭は replay 半分の所見で、まだ基底に到達していない。

**次**: `postRunF_step` ＋ `StageLegs` の帰納が何で止まっているかを
`CloseoutPreload35` / `36` の冒頭で確認する。

### いまの全体像（公理 3 本）

| 公理 | 底 | 状態 |
|---|---|---|
| `obligation_shiftPalResiduesAlongRun` | found 経路 → `StageEntryC`（**修理済み n184**）→ `RdPaced` → `PostRun` ＋ `RestartS2` | 基底待ち |
| `obligation_cycleOracle` | 同上（底を共有、n176） | 同上 |
| `obligation_localRealization` | run 機構が fairness を捨てている（n174）。`Fair` の実質 2 場には witness あり（n172）／`keepsSearchCursor` は定理で無償化（n173） | 別系統 |

## 2026-09-19 n184: **`StageEntryC` の偽の場を修理した**（置換先は既に存在していた）

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 3。
無条件 PAL は未完、§10.5 は未達。**

n181 で反証した `StageEntryC.fuel` を差し替えた:

    -  fuel : ReadyFuel   (searchLens.get r) (headRank r.right * 2048 + c.clock) (headRank r.right)
    +  fuel : ReadyPacedS (searchLens.get r) (headRank r.right * 2048 + c.clock) (2048 - c.clock)

そして `reachAtC3_of_crossF_C` の中身を
`CloseoutReportCase.reachAtC3_of_crossF` から
**`CloseoutReadyStage.reachAtC3_of_crossS`** に向け直した。

### 新しい定理はゼロ本（4 回連続）

`reachAtC3_of_crossS`（`CloseoutReadyStage:945`）と `reachAtC3_of_target_matchS`（`:841`）は
**既に書かれていた**。`CloseoutReadyStage` の冒頭 docstring が
「§5–§6 re-prove … `reachAtC3_of_crossF` on `ReadyPacedS`」と書いていて、
**それは計画ではなく完了報告だった**（宣言の存在を `grep "^theorem"` で確認済み）。

`.fuel` の消費者は `CloseoutContracts:90` の **1 箇所だけ**だったので、
差し替えは 3 行（場の型・呼び先・import）で済んだ。

### スタック管理の効果（コウタの「stackで管理はよかったんかも」への答え）

| n | 出来事 | 新規に書いた定理 |
|---|---|---|
| n175 | **公理 4 → 3** | **0** |
| n177 | `ReplayStage` が捨てられていたのを発見・修理 | 0 |
| n181 | `StageEntryC.fuel` を反証 | 0（証人は全部既存） |
| n184 | `reachAtC3_of_crossS` が既にあった | 0 |

その前（n148〜n164）は **44 本書いて計器は 1 本も動かなかった**。
`PROOF_STACK.md` に「**書く前に探す**」を規律として書いたのが転換点。

**ただし「終わりが見えた」とはまだ書かない。** 見えてきたのは残り作業の形であって、
計器は 3 本のまま。

### 残り

| 公理 | 底 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` ＋ `obligation_cycleOracle` | found 経路の入口 `StageEntryC` が**修理できた**ので、次は `RdPaced`/`ReadyPacedS` の producer。`CloseoutPreload11.readyClosure_S2` の底は `PostRun` ＋ `RestartS2` |
| `obligation_localRealization` | run 機構が fairness を捨てている（n174）。`Fair` の実質 2 場には witness あり（n172） |

## 2026-09-19 n183: `ReadyFuel` の API 全体に `ReadyPacedS` の双子がある（切り直しは機械的）

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 3。
無条件 PAL は未完、§10.5 は未達。**

n182 の置換表を一次情報で確認したら、`CloseoutReadyStage` に対応物が**全部**そろっていた
（`_ready` `_mono` `_effect_false` `_effect_true` `_restarted` `_watchSegE`）。

### なぜ `ReadyPacedS` は反証されないか（本質）

    ReadyFuel   v n K := ∀ as, n ≤ as.length → as.count true ≤ K → SearchReadyB v as
    ReadyPacedS v n k := ∀ as, n ≤ as.length → PacedL 2048 k as  → SearchReadyS v as

* 第 2 指標が **マッチ予算 `K`（`headRank`＝入力長に比例）** から
  **クロック由来の slack `k`（`2048 ≤ c.clock + k`）** に変わった
* 結論が `SearchReadyB`（`DpSafeRem`＝残り全部）から
  `SearchReadyS`（`DpSafeStage`＝**stage で切った**）に変わった

**「債務 2 で入力長ぶんのマッチを払え」という要求が消えている。**
これが n181 の反証を受け付けない理由であり、
`CloseoutPreload11.readyClosure_S2` が実際に producer を出せている理由。

### 切り直しの残り作業（完全に特定済み、`PROOF_STACK.md` に手順）

1. `StageEntryC.fuel` → `RdPaced c r`（`StageEntryS`）
2. `CloseoutReportCase` の 2 定理を置換表で再証明
   （`readyPacedS_watchSegE` の結論は `∃ k'` で 1 段包んであるので `obtain` を 1 つ挟む）
3. `reachAtC3_of_crossF_C` と found 経路の入口を追従
4. producer は `readyClosure_S2`（底は `PostRun` ＋ `RestartS2`）

## 2026-09-19 n182: 切り直しの設計が確定（`ReadyFuel` → `ReadyClosure`、置換は 1:1）

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 3。
無条件 PAL は未完、§10.5 は未達。**

n181 で `StageEntryC.fuel`（＝`ReadyFuel`）を反証したので、消費者が**実際に何を使って
いるか**を読んだ（`CloseoutReportCase:380-390`）:

    readyFuel_mono → readyFuel_watchSegE → readyFuel_ready → SearchReady (searchLens.get s1)

**取り出しているのは `SearchReady` だけ。** `ReadyFuel` は「区間に沿って `SearchReady` を
運ぶ乗り物」で、その乗り物が偽だった。**正しい乗り物は既にある**——
`GalilReplaySpan.ReadyClosure:5621`:

    ready   : ∀ c s, Rd c s → SearchReady (searchLens.get s)
    seg     : ∀ es c c' s t, WatchSegE … → t.chain = .idle → Rd c s → Rd c' t
    restart : ∀ c u Rad last, … → Restarted … → StageEntry … → Rd c u

`readyFuel_watchSegE`（`CloseoutReportCase:87`）と `ReadyClosure.seg` は**仮説の形が
そのまま同じ**（`WatchSegE` ＋ `t.chain = idle`）。置換は 1:1 で、`ReadyClosure` 側は
燃料の算術が無いぶん**簡単**。

| 旧（偽） | 新 |
|---|---|
| `ReadyFuel … (headRank …)` | `Rd c r` |
| `readyFuel_watchSegE` / `_ready` / `_restarted` | `hcl.seg` / `hcl.ready` / `hcl.restart` |
| `readyFuel_mono` | **不要** |

### 手順（`PROOF_STACK.md` に記録）

1. `StageEntryC` → `StageEntryS := InvLPS ∧ Rd c r`
2. `CloseoutReportCase` の 2 定理を新通貨で再証明
3. `reachAtC3_of_crossF_C` を追従
4. found 経路の入口の `StageEntryC` を差し替え
5. `Rd := RdPaced` なら `CloseoutPreload11.readyClosure_S2` が producer。
   その底は `PostRun` ＋ `RestartS2`（次の的）

**これは (A)（弱化）ではなく偽の契約の修理。** `StageEntryC` を要求していた定理は
全部「空虚に真」なだけで使えない状態だった。

## 2026-09-19 n181: **`ReadyFuel` を機械検査で反証した** — `StageEntryC` は切り直しが要る

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 3。
無条件 PAL は未完、§10.5 は未達。**

`PalPeg/ReadyFuelRefute.lean`（新規、1 定理、標準 3 公理のみ）:

    not_readyFuel_v0 (n : ℕ) (hn : n ≤ paced.length) :
      ¬ GalilSegmentConstructB.ReadyFuel v0 n (paced.count true)

`v0` は restart 直後の探索（`search = begin reset reset`、`Canonical`・`0 ≤ value`・
`StageEntry 0 reset` がすべて成立）。`paced` は `CloseoutRunEntriesPaced` の
`advances 2048 2048 (av.map (·, true))`。

**証人は 1 つも新規に作っていない。** `CloseoutRunEntriesPaced` の
`v0` / `paced_shape` / `step1`〜`step8` / `p7_not_run` / `p8_run` / `p8_debt` / `rest_count` を
そのまま使った。`K` を `paced` 自身のマッチ数に取ったので数え上げも不要（`le_rfl`）。

### 帰結: `StageEntryC.fuel` は偽（もう「疑い」ではない）

    StageEntryC.fuel : ReadyFuel (searchLens.get r) (headRank r.right * 2048 + c.clock)
                                 (headRank r.right)

`readyFuel_mono` は `K' ≤ K` で弱くなる向きなので、`paced.count true`（= 3）以上の `K` では
**すべて偽**。`headRank p = 2 * (p.head.right.length + p.head.incoming.length) + …`
（`GalilLeafEnds:66`）は入力長に比例するので、数文字の入力で 3 を超える。

**`StageEntryC` を要求する found 経路の入口
（`CloseoutPrepInputs3.prepInputs3_of_found_or_later`）は、この契約では閉じない。**

### 切り直しの形（一次情報が指している先）

正しい通貨は `CloseoutReadyStage.RunEntriesS`（`RunEntryS` が `DpSafeRem` ではなく
**`DpSafeStage`**——stage の終わりで切った版を使う、`:318`）。
`CloseoutPreload11.runEntriesS_of_restartS2:327` が既にそれを出している
（`Restarted` ＋ `StageEntry` ＋ `CentreLongAt` ＋ `DepthAt` ＋ `PostRun` から、
条件は `D + dpEvents(…) ≤ as.length` ＋ `PacedL 2048 0 as`）。

### 今日の「形式化のミスを疑う」の 4 件目

| # | 場所 | 中身 |
|---|---|---|
| 1 | `localRealization` | `Trace`/`Steps`/`StepsAll` が fairness を捨てている（n174） |
| 2 | `PackRunRMW` | `ReplayStage` を `hI.1` で捨てていた（n177、**直した**） |
| 3 | `ReadyFuel` の素朴形 | 2 つとも既に反証済みだった（n178） |
| 4 | `StageEntryC.fuel` | **反証した**（n181） |

## 2026-09-19 n180: **`StageEntryC.fuel` は偽の疑いが濃い**（`REFUTED` とは書かない）

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 3。
無条件 PAL は未完、§10.5 は未達。**

`ReadyFuel` を一次情報で展開した:

    ReadyFuel v n K   := ∀ as, n ≤ as.length → as.count true ≤ K → SearchReadyB v as
    SearchReadyB v as := ReadyRem v as ∧ RunEntriesAll as v
    RunEntry … as     := … → v'.mode = .run → DpSafeRem v' as
    DpSafeRem v as    := ∃ … s0 bs, … ∧ ((bs ++ as).count true : ℤ) ≤ value s0.debt ∧ …

**`.run` 入口の債務が以後のマッチを全部払えと要求している。**
`StageEntryC.fuel`（`CloseoutContracts:68`）の `K` は `headRank r.right`（右ヘッドの残り段数）。
一方 `CloseoutRunEntriesPaced` の監査が確定させた `.run` 入口の債務は **2**
（`initialDebt reset = reset` ＋ grow tick 1 回の `+2`）。

**`headRank ≥ 3` になる入力で `StageEntryC.fuel` は成り立たないはず。**
`RunEntriesAtBegin` / `RunEntriesPaced 2048` が偽である理由と同型で、両方とも機械検査済み。

**`REFUTED` とは書かない**——`StageEntryC.fuel` について `False` を導く機械検査済みの
定理はまだ無い。

### n176 の見立てを訂正する

n176 で「残る差は `ReadyFuel` 1 つ」と書いたが、**埋めるべき穴ではなく偽の契約である
可能性が高い**。found 経路の入口 `prepInputs3_of_found_or_later` が `StageEntryC` を取って
いる以上、そこも切り直しが要る。

正しい通貨は `RunEntriesS`（`CloseoutReadyStage:444`、`DpSafeStage` で**stage で切った**版）で、
`CloseoutPreload11.runEntriesS_of_restartS2` が既にそれを出している。

### ついでの発見

`GalilLeafPres.RunEntriesAll` と `GalilReplaySpan.RunEntriesAllD` は**同じ定義の重複**。
`ReadyFuelD` の docstring も「`GalilSegmentConstructB.ReadyFuel`, restated」。
通貨は実質 2 つ（`…All` 系と `…S` 系）。

## 2026-09-19 n178: `ReadyFuel` の素朴な形は 2 つとも機械検査で偽（探して助かった）

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 3。
無条件 PAL は未完、§10.5 は未達。**

n177 で `StageEntryC = InvLPS ＋ ReadyFuel` の `InvLPS` 側を無償にしたので、
残る `ReadyFuel` を攻めようとした。**書く前に producer を探したら、両方偽だった。**

| 候補 | 状態 |
|---|---|
| `GalilReplaySpan.RunEntriesAtBegin` | **偽**（`CloseoutReadinessAudit.not_runEntriesAtBegin`） |
| `GalilReplaySpan.RunEntriesPaced 2048` | **偽**（`CloseoutRunEntriesPaced`） |

`readyFuel_of_stage`（`GalilReplaySpan:3764`）は `ReplayStage` ＋ `RunEntriesAtBegin` から
任意の `n K` で `ReadyFuelD` を出すが、第 2 入力が偽なので使えない。

理由（一次情報）: `RunEntriesAllD` は `.run` 入口で残り全部に `DpSafeRem` を要求し、
`DpSafeRem v as → as.count true ≤ value v.debt`。**固定の債務でいくらでも長い tail を
払え**と言っている。pacing は比較の頻度を縛るが回数は縛らない。

**正しい形**は同ファイルが明記している `RunEntriesPacedS`——
イベント列を stage の終わりで切り、`count true ≤ stageDebt Rad` を側条件に足す。
`stageDebt Rad k = 2 * max k 1 - Rad`（`CloseoutPreload11:109`）で、
`CloseoutPreload11` が `stageDebt` ＋ `stageCredit` の会計を展開している。

**これが `hpres` の正体で、残り 3 本のうち 2 本が共有する底の最後の 1 つ。**

### この session の (C)/(A) の記録

| n | 操作 | 効果 |
|---|---|---|
| n145 | 6 → 4 に戻した | 本数 |
| n175 | trace 形を run 形から導出 | **4 → 3**（新規定理ゼロ） |
| n177 | `PackRunRMW` を `InvLPS` に上げた | 公理の文が弱くなった（`ReplayStage` は捨てられていた） |
| n178 | `ReadyFuel` の偽の形 2 つを確認 | **無駄な証明を回避** |

## 2026-09-19 n177: `obligation_shiftPalResiduesAlongRun` の仮説を `InvLPC` → `InvLPS` に強めた（公理は弱くなる）

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 3。
無条件 PAL は未完、§10.5 は未達。**

### 見つけたもの: `ReplayStage` は欠けていたのではなく**捨てられていた**

`CloseoutOracleW.h_oracleIMW_of_MC3_W:148` は `hI : InvLPS` を持っているのに
**`hI.1`（`InvLPC` の部分）だけ**を `PackRunRMW` に渡していた。
`InvLPS = InvLPC ∧ ReplayStage`（`GalilInvPlus3:86`）なので、
**`ReplayStage` はその場で無償**だった。CLAUDE.md §3 が `hstage` を「残り葉」として
挙げていたが、この経路では既に手元にある。

### やったこと（(A) の操作）

`PackRunRMW` の origin 仮説を `InvLPC` → `InvLPS` に上げ、下流に伝播:

| ファイル | 変更 |
|---|---|
| `CloseoutOracleW` | `PackRunRMW` の def、`reachAtIMW_of_reachAtC3R_W`、`cycleOutIMW_of_cycleOutMC3R_W`、`h_oracleIMW_of_MC3_W`（`hI.1` → `hI`）、`packRunR_MW` の本体 |
| `CloseoutMarksPack` | 2 つの producer の本体（`hIC := hInvLPS.1`）＋ `packRunR_MW_marksFree` の `hShiftPalAlongRun` 仮説 |
| `CloseoutFinalBranch` | `given_scanLandingObligations` の `hShiftPalAlongRun` 仮説 |
| `PalInPegUnconditional` | 公理と定理の仮説 |

trace 形の導出（n175）も `st 1` で `InvLPS` が要るようになったが、
**`CloseoutFoundRoutes.replayStage_of_inv` が `Inv` から無条件で `ReplayStage` を出す**ので
`inv_of_boot_tick` の `hInv` からタダ。

### なぜこれが前進か

`StageEntryC = InvLPS ＋ ReadyFuel`（`CloseoutContracts:65`）。
found 経路の入口（`prepInputs3_of_found_or_later`）は `StageEntryC` を要求する。
**`InvLPS` が手に入ったので、残る差は `ReadyFuel` 1 つだけ**になった。
`SegReachedW` の方は `GalilInvPlus.segment_of_invLP` ＋ 既に閉じている `hlive`/`hends` で出る。

公理は 3 本のまま（本数は動かないが、`obligation_shiftPalResiduesAlongRun` の文は
**弱くなった**——より強い仮説を取るようになった）。

## 2026-09-19 n175: **計器が動いた。公理 4 → 3。**

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット更新。
公理は 3。無条件 PAL は未完、§10.5 は未達。**

    'PalPeg.PalInPeg.unconditional' depends on axioms: [propext,
     Classical.choice,
     Quot.sound,
     PalPeg.PalInPeg.obligation_cycleOracle,
     PalPeg.PalInPeg.obligation_localRealization,
     PalPeg.PalInPeg.obligation_shiftPalResiduesAlongRun]

### 何をしたか: **trace 形を run 形から導いた**

`obligation_shiftPalResiduesAlongRun`（`InvLPC` 起点の `Steps` 上）と
`obligation_shiftPalResiduesAlongTrace`（`PreTraceIMW` の trace 上、`1 ≤ j ≤ Tc`）は
**中身が同じ 3 残差**だった。trace は `st 0 = boot w` から始まるので、
**`st 1` で `InvLPC` が立てば trace 形は run 形の特殊化**になる。

`st 1` の `InvLPC` は**既存部品だけ**で組めた（`BranchSupply.cpack_alongTrace` と同じ recipe）:

| 部品 | 役割 |
|---|---|
| `GalilTrailFront.inv_of_boot_tick` | **与えられた** boot tick の着地で `Inv` ＋ `SpanRep`（存在形の `invLPC_init` ではなく、trace 自身の `st 1` について言う） |
| `PreTrace.trace.good 1` | `OutputRel` |
| `GalilOracleDischarge.invS_of_inv` ＋ 上 | `InvL` |
| `GalilGlueBLeaves.entryCounters_of_inv` | `EntryCounters` |
| `GalilOracleMC2.invLPC_of_boot` | `InvLP2` ＋ `CentreRep` → `InvLPC` |
| `Inv.rest` ＋ `GalilInvPlus2.centreRep_of_restarted` | `CentreRep` |
| `GalilTrailFront.steps_between` | `st 1` から `st j` への `Steps`（`1 ≤ j ≤ Tc`） |

`w = []` のときは `Tc 0 = 0`（`PreTrace.tc0`）なので 3 つとも空虚。

### 新しい定理はゼロ

**1 本も新規に書いていない。**`PalInPegUnconditional.lean` の中で既存部品を繋いだだけ
（約 40 行）。コウタの「定理ふえすぎてへん？」の直後にこれが出たのは偶然ではなく、
**既存部品を探す姿勢に切り替えたから**見つかった。

### 残り 3 本

| 公理 | 内容 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | `H_readsShift` ＋ `H_freshShiftAtShiftEntry` ＋ `FreshShiftLedger`（run 形。**trace 形はこれに吸収された**） |
| `obligation_cycleOracle` | `CycleOracleMC3` |
| `obligation_localRealization` | `H_realizeLIMW'`（局所実現。壁は n174 の「run 機構が fairness を捨てている」） |

## 2026-09-19 n174: **壁の正体 — run 機構が全階層で fairness を捨てている**

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。**

コウタの「壁にあたったら、形式化のミスを疑う」に従って `localRealization` の壁を掘った。

### 壁

    structure Trace (F) (delay) (Q) (st) (e) : Prop where     -- GalilCheckpoints:46
      tick : ∀ i, i < e → Tick F delay (st i) (st (i+1))
      good : ∀ i, i ≤ e → Q (st i)

**`Tick` しか記録しない。`Fair` は 1 場もない。** `Steps` / `StepsAll` も同じ。
`PreTrace.trace` はこの `Trace` なので、trace は非決定的な tick の列でしかない。

一方 `LocalSysConcrete.Realizes` は「局所 step **関数** `f` が trace の次状態に着地する」
を要求する。**決定的な関数に、非決定的な trace と一致せよと言っている。**
だから producer が原理的に作れない。コウタの見立て通り、これは形式化のミス。

### 直すのに要るもの（3 択、blast radius 付き）

| 案 | 内容 | 影響 |
|---|---|---|
| **(1) run 機構を装飾** | `Trace` / `Steps` / `StepsAll` に fair 版を足し、`checkpoints_cost_upto1` を fair 版にする | `Trace` 220 箇所・`Steps` は更に多い。**最大** |
| **(2) 公理を上げる** | `obligation_cycleOracle` を「fair な pre-trace が存在する」形に差し替える | `CycleOracleMC3` は `h_oracleIMW_of_MC3_W` でも使うので、そちらが別に必要になり**本数が増える恐れ** |
| **(3) `PreTraceB` に `fair` 場を足し、`preTraceB_exists` と `checkpoints_cost_upto1` だけを fair 化** | 中間。`stepsAll_fn`（`GalilCheckpoints:51`）の fair 版が要る | `PreTraceB` の producer は 3〜4 箇所（実測済み）。**最小** |

**推奨は (3)。** 理由: `Trace` は 2 場の単純な構造体で、fair 版は
`∀ i, i < e → Fair entry delay (st i) (st (i+1))` を並べるだけ。
`stepsAll_fn` は `StepsAll → ∃ g, Trace` なので、fair 版 `StepsAll` から fair 版 `Trace` へ
同じ帰納法で通る。`checkpoints_cost_upto1` は区間を貼り合わせるだけなので
fairness は連言で運べる。

### ただし (3) でも 4 → 3 にはならない（正直に）

`Fair` が閉じるのは `Realizes` の**決定性の半分**。
**局所 step の構成**（`H_scanLoc` / `H_initLoc` / `H_replayStartLoc`）は別の仕事で、
`LocalTick2.commitReplay` の `LocalTick1.Inv` 保存補題が起点
（`LocalTick2.lean` には `Inv` に関する補題が**1 本もない**——実測）。

### この session でやったこと（計器は 4 のまま）

* 公理 6 → 4 に戻した（n145）。以後増やしていない
* `PalPeg/RoundHistory.lean` 35 宣言で `H_readsShift` を run 全点で出す機械を完成
  （44 まで増やして 9 本削った——うち 4 本は既存の再発明）
* `Fair` の 3 場の内訳を割り、第 3 場が `Tick` からタダであることを**定理で**証明（n173）
* CLAUDE.md の古い記述を 1 箇所訂正（`initVM`/`replayStartVM` の `periodOnly`/`walker`）
* 自分の嘘 2 件を訂正、`sorry` を書きかけて止めたのを記録

## 2026-09-19 n173: `Fair` の第 3 場が `Tick` からタダであることを**定理で**示した

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。**

`GalilTickFair.keepsSearchCursor_of_tick`（標準 3 公理のみ）:

    Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay ⟨c, s⟩ y →
    (c.mode = Mode.init ∨ c.mode = Mode.replayStart) →
      y.vm.periodOnly = s.periodOnly ∧ y.vm.walker = s.walker

`initVM`（`GalilScaffoldTopReplay:20`）と `replayStartVM`（`:33`）の定義そのものの
15 連言の最後 2 つが `t.periodOnly = s.periodOnly ∧ t.walker = s.walker` なので、
`tick_init_cases` / `tick_replayStart_cases` で取り出すだけ。

**CLAUDE.md §2 の記述を散文でなく定理で直した。**
`Fair` の実質は 2 場（`restartFirst` ＋ `fallbackPlace`）で、どちらも witness がある
（`fair_restart` / `fallbackAt_walker_self`）。

**4 → 3 の道で「強めたオラクルが供給すべきもの」は 3 場から 2 場に減った。**
公理は 4 本のまま。

## 2026-09-19 n172: `Fair` は 3 場すべて witness がある——公理を強める根拠が立った

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。**

`GalilTickFair` に 3 場ぶんの witness が**既に揃っている**（一次情報で確認）:

| `Fair` の場 | witness | 側条件 |
|---|---|---|
| `keepsSearchCursor` | `initVM_keeps_cursor:474` / `replayStartVM_keeps_cursor:486`。**さらに定義自体に入っている**ので `Tick` からタダ | なし |
| `fallbackPlace` | **`fallbackAt_walker_self:466`**——search 自身の walker に着地する fallback が満たす（`FppControl.beginFallback` の `walker := p`、`GalilScaffoldChainFallback:410`） | `(stream s.walker).length ≤ position s.right` |
| `restartFirst` | `fair_restart:454` | なし（guard 下で restart が存在する） |

**帰結: fair な run は存在し、`tick_fair_unique` でそれは一意。**
だから `obligation_cycleOracle` の文に「run は `Fair`」を入れるのは
**モデルの忠実性の要求**であって、無根拠な強化ではない。

### ただし 4 → 3 にはまだ足りない（正直に）

`Fair` が閉じるのは `Realizes` の**決定性の半分**（`H_scanDet` / `H_initFun` / `H_rsFun`）。
**局所側の構成**（`H_scanLoc` / `H_initLoc` / `H_replayStartLoc` ＋ `H_rewindWF` /
`H_chooseWF` ＋ fpp の 1 量子）は残る。`LocalRealizesScan` の冒頭が
「`LocalReplayParked.commitReplayParked` が `H_replayStartLoc` の意図された witness だが
`LocalTick2.commitReplay` に `LocalTick1.Inv` 保存の補題がまだ無い」と書いている。

**つまり `localRealization` を外すには局所 step の構成作業が必要で、
それは `Fair` とは別の仕事。** 公理は 4 本のまま。

### 2 本の筋の残りを並べる（両方とも「配線／構成」で、新しい数学ではない）

| 筋 | 残り | 規模の手がかり |
|---|---|---|
| `H_readsShift`（第 1 残差） | `first_round` の 30+ 仮説を run から供給 | CLAUDE.md §3 の found 経路（`hfound`/`hfoundBg`/`hfoundReplay`、「未着手、最大の残り」） |
| `obligation_localRealization` | `Fair` を trace に通す ＋ 局所 step 3 本の構成 | `LocalTick2.commitReplay` の `Inv` 保存補題が起点 |

## 2026-09-19 n171: **`Fair` の 3 場の内訳を割った——1 場はタダ、1 場は形式化のミス**

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。**

`Fair`（`GalilTickFair:195`）は 3 場。4 → 3 の道でこれを供給しないといけないので、
1 場ずつ一次情報で測った。

| 場 | 状態 |
|---|---|
| `keepsSearchCursor` | **タダ**。`initVM`（`GalilScaffoldTopReplay:20`）と `replayStartVM`（`:33`）の定義の 15 連言の最後 2 つが `t.periodOnly = s.periodOnly ∧ t.walker = s.walker`。`tick_init_cases` / `tick_replayStart_cases` で取り出すだけ |
| `fallbackPlace` | `beginFallbackVM'`（`GalilScaffoldTopGuards:45`）が place `p` を「`(stream p).length ≤ position s.right`」だけで縛っている。**実機は search の walker から一意に計算する** → `t.fpp.walker = t.walker` を定義に足せば消える。**形式化のミス** |
| `restartFirst` | `restartGuardVM`（`GalilSharedFunctional:146`）が `chain = .broken w` を要求するので、**broken chain のない区間では空虚**。Scala は restart 優先（`ScaffoldGalil`） |

### CLAUDE.md を訂正した

§2 の「(e) `beginFallbackVM'`（着地場所）、`initVM`/`replayStartVM`（`periodOnly`, `walker`
自由）が非関数的」は**古い**。`initVM`/`replayStartVM` は既に両方を固定している。
**この誤った記述を信じて「fair を供給するのは 3 場ぶん」と見積もっていた。**

### 帰結（4 → 3 の道の見積もり改訂）

供給すべきは実質 2 場、しかもうち 1 場（`fallbackPlace`）は
**`beginFallbackVM'` の定義に 1 連言足せば消える**。
残るのは `restartFirst` だけで、それは broken chain のある区間に限られる。

**「Fair を通すのは大工事」という見積もりは過大だった。**

## 2026-09-19 n170: **コウタの「定理ふえすぎてへん？」に答えて 44 → 35 に削った**

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。**

### 答え: 増えすぎていた。9 本は要らなかった

44 宣言足して**計器は 1 本も動いていない**。プロジェクトの基準ではこれは足場を積んだだけ。
使用箇所を実測して 9 本削った。

**参照ゼロ（5 本）**:

| 消したもの | 理由 |
|---|---|
| `watch_eq_of_mismatch_lagZero` | `ChainStep` 版に置き換わったのに両方残していた |
| `outer_eq_of_false` | 上の唯一の消費者が死んで連鎖 |
| `chain_shift_period_focus` | 「`hprediction` に要るかも」で**推測で**足したが要らなかった |
| `h_readsShift_of_run` | `shiftPhaseHistory_readsShift` に置き換わった |
| `chainShiftRun_of_steps` | carrier が tick ごとに運ぶ方式にしたので不要 |

**既存の再発明（4 本）**——これが一番痛い:

| 消した自作 | 既にあったもの |
|---|---|
| `positive_false_of_zero` | `GalilMismatchCaught.positive_false_of_zero:67`（**文言まで同一**） |
| `internal_eq_of_lagZero` | `CloseoutWatchRound4.internal_eq_of_zero:240` |
| `chainStep_watch_eq_of_lagZero` | `CloseoutMismatchCompare.chainStep_watch_of_lagZero:91` |
| `chainTick_false_watch_eq_of_lagZero` | `CloseoutMismatchCompare.chainTick_false_idle:46` |

### さらに: `CloseoutMismatchCompare` を先に読むべきだった

あのファイルは**不一致比較の構成を全部持っている**:

    chainTick_false_idle / compare_mismatch_of_lagZero / compare_mismatch_of_round
    chainStep_watch_of_lagZero / compare_chain_of_mismatch / beginShift_of_guard
    shiftAtMismatchM_of_round

とくに `compare_chain_of_mismatch:99` は「lag ゼロの不一致比較で
`vs.chain = .watch w` ∧ `vs.left = left s.left` ∧ `vs.right = right s.right`」を
**まとめて**出す——ウチが `shiftPhaseHistory_of_scanShift` で苦労して導いた 3 事実そのもの。
**CLAUDE.md の「既にあるものを探す」を守れていなかった。**

### 教訓（`PROOF_STACK.md` に追記）

新しい補題を書く前に、**扱う概念の名前で `grep -n "^theorem"` を関連ファイルに掛ける**。
とくに `Closeout*` は同じ問題を既に扱っている可能性が高い。
今回は `CloseoutMismatchCompare` / `CloseoutWatchRound4` / `GalilMismatchCaught` の 3 本を
先に読めば 4 本書かずに済んだ。

## 2026-09-19 n169: `Fair` が閉じるのは「決定性の半分」——残るのは局所側の構成

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。計器はまだ動いていない。**

n168 の段取り 4 を一次情報で検証した。`LocalRealizesScan` の残り義務:

| mode | 決定性の半分 | 局所の半分 |
|---|---|---|
| `rewind` / `choose` | **閉**（`tick_det_rewind` / `tick_det_choose`） | `H_rewindWF` / `H_chooseWF` |
| `init` | `H_initFun` | `H_initLoc` |
| `replayStart` | `H_rsFun` | `H_replayStartLoc` |
| `scan` | **`H_scanDet`** | **`H_scanLoc`** |

`PalPeg/GalilTickFair.lean` に**そのまま合う 3 本が証明済み**:

    tick_fair_scan_unique        (:308)
    tick_fair_init_unique        (:381)
    tick_fair_replayStart_unique (:400)

どれも `hm : c.mode = …` ＋ 両 tick の `Fair` から `y₁ = y₂` を出す。

**結論: `Fair` は決定性の半分を閉じる。そこが「原理的に作れない」部分だった。**
残るのは局所側の**構成**（`H_scanLoc` / `H_initLoc` / `H_replayStartLoc` ＋
`H_rewindWF` / `H_chooseWF` ＋ fpp の 1 量子）で、不可能ではない。

`scan` の非決定性の原因も特定済み: `Tick.restart` が 5 つの scan 構成子と競合すること
（`Fair.restartFirst` が潰す）と `SafeQuanta` / `chainAt` が関係であること
（`GalilTickDet.safeQuanta_unique` / `chainAt_unique` が潰す）。**どちらも `Fair` 側で済んでいる。**

### この session の総括（計器は動いていない）

* 公理 **4 本**（n132 で 6 に増やしたのを n145 で 4 に戻した。以後増やしていない）
* 新規 `PalPeg/RoundHistory.lean` **44 宣言**——`H_readsShift` を run 全点で出す機械が完成
  （残りは `first_round` の配線＝ found 経路）
* `obligation_localRealization` の診断: `PreTrace` が `Fair` を記録していないので
  決定的な局所 step に非決定的な trace と一致せよと要求していた。
  `Fair` は証明済みだが `Local*` で未使用
* trace の出どころは `obligation_cycleOracle` なので、その文に `Fair` を入れれば
  決定性の半分が閉じる（**4 → 3 の道**）
* 自分の嘘 2 件を訂正（「残差化で弱くなった」は嘘 / build 通知の誤読）
* `sorry` を書きかけて実行前に止めた

## 2026-09-19 n168: **trace の出どころは `obligation_cycleOracle` — 4 → 3 の道が見えた**

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。計器はまだ動いていない。**

`preTraceB_exists`（`GalilFinalBaseNeed:193`）を一次情報で読んだ。trace は

    hor : CycleOracleMC (PofC centre place entry w) q first w
    → checkpoints_cost_upto1 … hor …
    → ⟨st, Tc, …⟩

で作られている。**trace の tick 列は `obligation_cycleOracle`（4 本のうちの 1 本）が
供給する run そのもの。**

### 帰結: 1 本の文を強めて 1 本を丸ごと消せる

| 操作 | 効果 |
|---|---|
| `obligation_cycleOracle` の文に「run の各 tick は `Fair`」を入れる | 1 本の中身が強くなる |
| `obligation_localRealization` が**公理から外れる** | **本数 4 → 3** |

**これは (C)（本数が減る操作）。** 強める側は妥当: `Fair` は Scala の優先順位と固定値を
表すもの（CLAUDE.md §2）なので、**実機の run は定義上 `Fair`**。
オラクルの仕事は run を提示することなので、提示する run が fair であることは
モデルの忠実性の要求そのもの。

### 段取り（`PROOF_STACK.md` に記録）

1. `PreTraceB` に `fair` 場を足す
2. `preTraceB_exists` の `hor` を `Fair` 版オラクルに差し替え、`checkpoints_cost_upto1` から運ぶ
3. `obligation_cycleOracle` の文に `Fair` を追加
4. `Realizes` の scan / init / replayStart を `tick_fair_unique` で閉じる
5. `H_realizeLIMW'` の `∃ … L` を構成して `obligation_localRealization` を**外す**

**未検証**: 4 が本当に閉じるか。CLAUDE.md §1 は「phase 側は閉、scan/init/replayStart が
非決定性で閉じない」と書いているので `Fair` を入れれば閉じる見込みだが、実証はまだ。

## 2026-09-19 n167: `localRealization` に producer がいない理由の診断

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。計器は動いていない。**

コウタの指摘「localRealization も一見難しく見えてるだけ。producer がいないってことは
モデル化を何か間違ってる」を追った。

### 確認できた事実（一次情報）

1. `Realizes`（`LocalSysConcrete:285`）は「mode の局所 step **関数** `f` が
   trace の次状態に着地する」を要求する
2. trace `stOf` は `PreTrace` の `trace` 場（`Tick (st i) (st (i+1))`）でしか縛られていない。
   **`Tick` は非決定的**（`GalilTickDet`、CLAUDE.md §2 に 5 分岐）
3. `Fair` を足すと一意: **`GalilTickFair.tick_fair_unique`（`:429`）は証明済み**、
   docstring は「with no reachability pack at all」
4. **`Fair` は `PalPeg/Local*.lean` のどこでも使われていない**
   （`grep -rln "Fair" PalPeg/Local*.lean` が空）

### 推論（未検証・機械検査した反証は無い）

`Realizes` は「決定的な関数に、非決定的な trace と一致せよ」と要求していることになり、
producer が原理的に作れない。**直し方の候補**: `PreTrace`（または `PreTraceB` / `InvC`）に
`Fair` の場を足す。`PreTraceIMW` は上位で**仮説**として現れるので、
場を足すと義務は**弱くなる**（(A) の操作）。

構成側（実 run から trace を作るところ）が `Fair` を供給できるかは別途確認が必要。
CLAUDE.md §2 自身が「構成側の witness と局所 step が `Fair` を満たすことを別途確認」と
書いている——つまり**この作業は当初から予定されていて、未着手のまま**だった。

### 2 本の筋の比較（どちらも未着手部分がある）

| 筋 | 状態 |
|---|---|
| `H_readsShift`（第 1 残差） | **部品は全部揃った**（`RoundHistory` 44 宣言）。残りは `first_round` の 30+ 仮説を run から供給する配線＝ CLAUDE.md §3 の found 経路（「未着手、最大の残り」） |
| `obligation_localRealization` | 診断は付いた（上）。`PreTrace` に `Fair` を足す構造変更＋構成側の `Fair` 供給 |

## 2026-09-19 n166: **自分が撒いた過剰量化を直した**（`roundCarrier_tick` の側条件）

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。計器はまだ動いていない。**

n164 で書いた `roundCarrier_tick` の側条件が**過剰量化していた**。
CLAUDE.md の「消費者がその分岐で何を要求しているかを読む」を自分のコードで破っていた。

| 側条件 | 旧（過剰） | 新（使う分岐だけ） |
|---|---|---|
| `singlePositive cycle = false` | 全 scan 点 | scan → **scan** の枝だけ |
| `canRight right` | 全 scan 点 | scan → **shift** の枝だけ |
| chain が watch | 全 target scan 点 | scan → **scan** の枝だけ |
| `replaying = false` | 全点 | **scan** 点だけ |
| `CopyIdle` | 全点 | **shift** 点だけ |

とくに 1 行目は**ラウンド終端で偽**になる: `shiftGuardVM` は `periodOnly` のとき
`singlePositive cycle = true` を要求するので、shift に入る点では周期が終端。
旧の形は「全 scan 点で周期が終端でない」と言っていたので、
**ラウンド境界を含む区間には適用できなかった**。

run 沿いの `hSide` も `∀ m z z', Steps … m x z → Tick … z z' → …` の形にして、
遷移先の mode で場合分けできるようにした。

**これは (A)（guard を狭める）の操作で、本物の弱化。** 公理はまだ 4 本。

## 2026-09-19 n165: 基底の橋（`first_round` の `Entry` → `OriginAt`）

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。計器はまだ動いていない。**

`PalPeg/RoundHistory.lean` は **44 宣言**（全部標準 3 公理以内、3 本は公理ゼロ）。

* `periodLength_after_shift` — shift 後の watch の周期は shift の歩数。3 段:
  `chain_shift_periodLength`（公理ゼロ）→ `GalilChainCoupling.periodLength_consume`
  （`immediate` 1 手、側条件 `WatchBlock`）→
  **`CloseoutWatchRound45.period_of_beginShift`**（既存。`beginShiftVM h w` と
  `beginShiftVM'` の `h` が一致する）
* `originAt_of_firstShiftEntry` — `first_round` の `Entry` を `OriginAt` にする
  （`CloseoutOriginRounds.originAt_of_entry` ＋ 上の周期一致）

**これで `H_readsShift` の鎖は基底から run 全点まで部品が揃った。**

### 計器を動かすために残っていること（正直に）

`first_round` は仮説が 30 個以上ある（found 経路の全部）。それを run から供給するのが
CLAUDE.md §3 の `hfound` / `hfoundBg` / `hfoundReplay`——「**未着手、最大の残り**」と
自分で書いていた項目そのもの。`h_readsShift_alongSteps` の側条件も既存 pack から
出る見込みだが**未検証**。

**つまり `H_readsShift` は「部品は全部ある・配線が残っている」状態。**
公理はまだ 4 本。

## 2026-09-19 n164: **`H_readsShift` を run の全点で組めた**（`RoundHistory` 42 宣言）

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。計器はまだ動いていない。**

`PROOF_STACK.md` 手順 1〜11 が全部繋がった:

    scanShift_parts / shiftDone_parts  — Tick の場合分けをデータ抽出に閉じ込める
    roundCarrier_tick                  — 4 遷移を振り分けて carrier を 1 tick 運ぶ
    roundCarrier_of_steps              — run に沿って運ぶ
    h_readsShift_alongSteps            — run の全点で H_readsShift

`scanShift_parts` / `shiftDone_parts` は「scan→shift の tick は `scan_shift` だけ」
「shift→scan の tick は `shift_done` だけ」を 23 構成子の照合で示したもの。
行き先の control を一次情報（`GalilScaffoldTop:110-172`）で全部確認した:

| 構成子 | 行き先 mode |
|---|---|
| `scan_wait` / `scan_count` / `scan_match` / `restart` | source と同じ（scan） |
| `scan_shift` | `.shift` |
| `scan_fallback` | `.copy` |
| `shift_one` | source と同じ（shift） |
| `shift_done` | `.scan`（VM は不変） |

### 計器を動かすために残っていること

`h_readsShift_alongSteps` の 2 つの入力:

1. **起点の `RoundCarrier`** — scan 相なら `RoundHistory`（起点の `OriginAt` が要る）。
   chain 誕生直後は `OriginAt` がまだ無く、最初の shift で
   `GalilScaffoldTopFirstRound.first_round`（**無条件**）が `Entry` を出す。
   **ここが基底。**
2. **側条件** — 区間の全点が scan / shift 相 ∧ 非 replay ∧ `CopyIdle`、
   scan 点では周期が終端でない・右ヘッドが読める・chain が watch。
   これは既存の pack（`Extra7` / `AuxPack` / `LPackM`）から出る見込み（未検証）

## 2026-09-19 n163: 結合 carrier `RoundCarrier` と `H_readsShift` の取り出し

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。計器はまだ動いていない。**

`PalPeg/RoundHistory.lean` は **37 宣言**（全部標準 3 公理以内、3 本は公理ゼロ）。

    RoundCarrier P q first delay w c s :=
      (c.mode = Mode.scan  → RoundHistory P q first delay w c s) ∧
      (c.mode = Mode.shift → ShiftPhaseHistory w s)

    h_readsShift_of_roundCarrier   : RoundCarrier … → H_readsShift w c s
    originShift_of_roundCarrier    : RoundCarrier … → OriginShift w c s

**これが目標の形**: `RoundCarrier` を run / trace の全点で持てれば
`obligation_shiftPalResidues*` の第 1 残差（`H_readsShift`）が公理から外れる。

### 途中で `sorry` を書きかけて止めた（記録）

tick 振り分けを書こうとして `| _ => sorry` を含むスクリプトを組み立てたが、
実行前に気づいて破棄した（スクリプトは `skip` を出力してファイルを書いていない）。
原因は `RoundHistory` の射影を `obtain ⟨wch, hwch⟩` で取ろうとしたこと——
実際は 12 成分の存在命題で、`onlyMatchedRun_of_roundHistory` を通さないといけない。
**急いで通すために `sorry` を置くのは禁止。** 確定できる分だけ入れた。

### 残り

1. `roundCarrier_tick` — 4 遷移を `Tick` の構成子で振り分ける。
   `scan_wait` / `scan_count` / `scan_match` は `roundHistory_tick`、
   `scan_shift` は `shiftPhaseHistory_of_scanShift`、
   `shift_one` は `shiftPhaseHistory_tick`、`shift_done` は `roundHistory_of_shiftDone`。
   各構成子の**行き先の control** を一次情報で確認してから書く（mode の判定に要る）
2. 基底 — `scan_fallback` / `restart` では carrier は原理的に保たれない。
   新しいラウンドの `OriginAt` は `first_round`（無条件）が出す

## 2026-09-19 n162: **ラウンドの 4 つの相遷移が全部揃った**（`RoundHistory` 34 宣言）

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。計器はまだ動いていない。**

| 遷移 | 定理 |
|---|---|
| scan → scan | `roundHistory_tick` |
| scan → shift（`scan_shift`） | **`shiftPhaseHistory_of_scanShift`（n162）** |
| shift → shift（`shift_one`） | `shiftPhaseHistory_tick` |
| shift → scan（`shift_done`） | `roundHistory_of_shiftDone` |

`scan_shift` 遷移の内訳（全部一次情報から）:

* `s'.chain = .watch wch` ← `ChainTick false x z` は `ChainStep x z`
  （`GalilScaffoldTopChainVM:92`）で `.watch` から出る構成子は `watchStep` だけ（`:66`）。
  lag ゼロなら `Internal` は恒等（`chainTick_false_watch_eq_of_lagZero`、n162）
* `singlePositive s1.cycle = true` ← guard の `if periodOnly then singlePositive cycle = true`
  節。`afterMismatch` は `cycle` / `periodOnly` を触らない（`afterMismatch_cycle` /
  `afterMismatch_periodOnly` はどちらも `rfl`）
* `hPredict` ← guard の `symbol …period.focus = read s'.right` ＋ `afterMismatch_right`
* `beginShiftVM (periodLength wch) wch …` ← `beginShiftVM'` の定義から（`w = wch` は chain で一意）
* 基底の `ChainShiftRun … 0 …` は `.stop`、frame は `(shiftLens.set_get s2).symm`

ついでに `MatchedRunSnoc.compare_mismatched_parts` の結論に
`vs.left` / `vs.right` / `ChainTick false t.chain vs.chain` を足した
（消費者がいなかったので破壊的変更なし）。

### 残り: 結合 carrier と run 沿いの帰納

    RoundCarrier P q first delay w c s :=
      (c.mode = Mode.scan  → RoundHistory P q first delay w c s) ∧
      (c.mode = Mode.shift → ShiftPhaseHistory w s)

* tick 保存は上の 4 遷移を `Tick` の構成子で振り分けるだけ
* **`H_readsShift` は scan 相では空虚**（guard が `mode = shift`）、
  shift 相で `remaining` が尽きた点は `shiftPhaseHistory_readsShift`
* **基底が残る**: `scan_fallback` で copy 相に落ちると chain が作り直されるので
  carrier は保たれない。そこは `GalilScaffoldTopFirstRound.first_round`（無条件）が
  新しい `OriginAt` を出す点。**ここが最後**

## 2026-09-19 n161: `shift_done` 遷移（`ShiftPhaseHistory` → `RoundHistory`）

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。計器はまだ動いていない。**

`PalPeg/RoundHistory.lean` は **31 宣言**。

`roundHistory_of_shiftDone`: shift 相が終わると次のラウンドの `RoundHistory` が立つ。
`shift_done` は VM を変えない（`GalilScaffoldTop:136`）のでこの状態がそのまま次の起点。
7 つの場の出どころ:

| 場 | 出どころ |
|---|---|
| `OriginAt w s` | `shiftPhaseHistory_originAt` |
| `s.periodOnly = true` | `beginShiftVM` が置いた値。`shiftLens` の外なので shift 相で不変 |
| `s.chain = .watch v` | `ShiftPhaseHistory` |
| `zero v.lag = true` | `chain_shift_lag`（`immediate` は lag を変えない） |
| `WatchBlock v` | `chain_shift_period` ＋ `onBlock_verifier_consume` |
| `Canonical s.radius` / `Canonical s.length` | `shift_run_canonical` |

そのために `RoundHistory` に `WatchBlock w₀` を、`ShiftPhaseHistory` に
`zero wch.lag = true` / `s2.periodOnly = true` / `Canonical s1.radius` を足した。

### 残り 1 個: `scan_shift` 遷移（`RoundHistory` → `ShiftPhaseHistory`）

tick が与えるもの（`GalilScaffoldTop:123`）: `hm` / `h`（available）/ `hc : clock = 1` /
`hcmp` / `hmt`（不一致）/ `hr : replaying = false` / `hg : P.shiftGuard s'` /
`hb : P.beginShift s' s''`。

`PofC` では `P.shiftGuard = shiftGuardVM`、`P.beginShift = beginShiftVM'`。
比較の分解は `MatchedRunSnoc.compare_mismatched_parts`。
必要な場はすべて `RoundHistory` の射影（`onlyMatchedRun_of_roundHistory`）と
guard から出る見込み。**これが繋がれば `H_readsShift` が run 全点で出る。**

## 2026-09-19 n160: shift 相の carrier（`ShiftPhaseHistory`）とその tick 保存

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。計器はまだ動いていない。**

`PalPeg/RoundHistory.lean` は **30 宣言**（全部標準 3 公理以内、3 本は公理ゼロ）。

* `ShiftPhaseHistory w s` — `roundSeg_of_run` の仮説を束ねた shift 相の履歴
* `shiftPhaseHistory_originAt` — `remaining` が尽きた点で `OriginAt`（次ラウンドの起点）
* `shiftPhaseHistory_readsShift` — 同じ点で **`H_readsShift`**
* `shiftPhaseHistory_tick` — shift 相の 1 tick で伸びる

`RoundHistory` は `ScanSeg` を持つので scan 相しか覆わない。ラウンドは
scan 相 ＋ shift 相なので、**2 つの carrier の選言**を run に沿って運ぶ形になる。

### 残り（相の遷移 2 つ ＋ 結合 carrier）

| 遷移 | 要るもの |
|---|---|
| `scan_shift`（`RoundHistory` → `ShiftPhaseHistory`） | `hTerminal`（`scanSeg_only` の `periodOnly` ＋ guard）／`hCanRight`（`Extra7`）／`hPredict`（guard ＋ `watch_eq_of_mismatch_lagZero`）／`hLengthCanonical`（**済**）／`hRight`・`hLeft`（比較）／`hBeginShift`（`beginShiftVM'`）／**`WatchBlock w₀`（`RoundHistory` に足す必要がある）** |
| `shift_done`（`ShiftPhaseHistory` → `RoundHistory`） | `shiftPhaseHistory_originAt`（**済**）＋ `roundHistory_start` |

**`RoundHistory` に `WatchBlock w₀` を足すのが次の一手。**

## 2026-09-19 n159: **`H_readsShift` がラウンド起点の `OriginAt` から出る鎖が繋がった**

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。計器はまだ動いていない。**

`PalPeg/RoundHistory.lean` は 24 宣言。`PROOF_STACK.md` 手順 8・9・11 が済んだ。

    roundSeg_of_run        : RoundSeg w s₀ sEnd
    originAt_next_of_run   : OriginAt w sEnd          （手順 9）
    h_readsShift_of_run    : H_readsShift w c sEnd    （手順 11）

つまり **ラウンド起点の `OriginAt` ＋ そのラウンドの run の材料**から
`H_readsShift` が出る。全部標準 3 公理のみ。

`roundSeg_of_run` の第 1 節（`periodLength v = periodLength w₀`）は 3 段の合成:

* scan 相 → `periodLength_onlyMatchedRun`
* `immediate` 1 手 → `GalilChainCoupling.periodLength_consume`
  （側条件 `WatchBlock` も `periodLength_onlyMatchedRun` が返す）
* shift 相 → `chain_shift_periodLength`（公理ゼロ）

### 計器を動かすために残っていること

`H_readsShift` を **trace / run の全点で**得るには、`RoundHistory`（＝ラウンド起点の
`OriginAt`）を run に沿って引き継ぐ帰納が要る:

* 基底: chain 誕生時の `OriginAt` ← `GalilScaffoldTopFirstRound.first_round`（**無条件**）
* 帰納: `originAt_next_of_run`（**済**）でラウンドごとに引き継ぐ
* ラウンド境界の検出: run のどこが `scan_shift` かを特定する（`RoundHistory` の
  `hScanWatchAll` 側条件と `shift` 相の `hShiftAll` 側条件をどう供給するか）

**これが最後の壁。** 計器（`#print axioms`）はまだ 4 本。

## 2026-09-19 n158: **ラウンド 1 周を run から組めた**（`compareRounds_one_of_run`）

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。計器は動いていない。**

`PROOF_STACK.md` 手順 7 が済んだ。`PalPeg/RoundHistory.lean` は 21 宣言。

    compareRounds_one_of_run :
      OnlyMatchedRun (toOnly s₀ w₀) n (toOnly s1 wch) →
      singlePositive s1.cycle = true → canRight s1.right →
      read (right s1.right) = symbol wch…period.focus →
      Canonical s1.length →
      vs.right = right s1.right → vs.left = left s1.left →
      beginShiftVM (periodLength wch) wch (afterMismatch s1 vs vq) s2 →
      ChainShiftRun (shiftLens.get s2).shift (immediate wch) (shiftLens.get s2).cycle k
        (shiftLens.get sEnd).shift v (shiftLens.get sEnd).cycle →
      positive (shiftLens.get sEnd).shift.remaining = false →
      sEnd = shiftLens.set s2 (shiftLens.get sEnd) →
      sEnd.chain = ChainVM.watch v →
      CompareRounds (periodLength wch) (toOnly s₀ w₀) 1 (toOnly sEnd v)

**フレーム（`P` / `q` / `first` / `delay`）に依らない。** run から取り出した材料だけで閉じる。
`CompareRounds.next` の `lengthCounter` は `inc (inc s1.length)` に決まり、
`hlen` は `inc_canonical` 2 回、`hrun : ShiftRun` は `shiftRun_of_chain` でタダ、
手数 `k = periodLength wch` は `chainShiftRun_length_eq`、
末尾の射影の形は `toOnly_shiftEnd_eq`。

### 残り（`PROOF_STACK.md` 手順 8〜11）

8. `RoundSeg w s₀ sEnd` にする（第 1 節 `periodLength v = periodLength w₀` は
   `periodLength_onlyMatchedRun` ＋ `periodLength_consume` ＋ `chain_shift_periodLength` の合成）
9. `CloseoutRoundSeg.originAt_of_roundSeg` → 次のラウンド起点の `OriginAt`
10. `roundHistory_start` で次のラウンドの `RoundHistory`
11. `CloseoutReadsOrigin.originShift_of_roundSeg` → `OriginShift`
    → `h_readsShift_of_originShift` → **`H_readsShift`**

## 2026-09-19 n157: shift 末尾の射影の形も確定（`RoundHistory` 20 宣言）

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。計器は動いていない。**

`toOnly_shiftEnd_eq`（一発で通った）。`CompareRounds.next` の `rest` の始点は
`⟨t'.center, t'.left, right t.right, v, cycle, t'.radius⟩` という明示の組
（`GalilScaffoldChainReadOrigin:1008`）で、run から作るには `toOnly sEnd v` が
これに一致しないといけない。

一致の根拠（一次情報）:

* `toOnly s w = ⟨s.center, s.left, s.right, w, s.cycle, s.radius⟩`（`GalilScaffoldTopOnly:20`）
* `shiftLens.get` は `⟨⟨center, left, remaining, radius, length⟩, chain, cycle⟩` なので
  center / left / radius / cycle は `shiftLens` の中、**`right` は外**
* `right` は shift 相で不変（`shiftLens_frame_steps`）、shift 入口の値は
  比較の `vs.right = right s1.right`

**これで `PROOF_STACK.md` 手順 11 段の部品はすべて揃った（20 宣言）。**

## 2026-09-19 n156: `shift` の手数が初期値で決まることを証明（`RoundHistory` 19 宣言）

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。計器は動いていない。**

`chainShiftRun_length_eq`:

    a.remaining = ofNat h → ChainShiftRun a w cycle k b v finish →
    positive b.remaining = false → k = h

`CompareRounds.next` は shift 相をちょうど `h` 手として要求するのに、run からは
「shift mode に留まった手数 `k`」しか分からないので `k = h` が要る。
`GalilScaffoldTopInvariant.shift_run_remaining` は「ちょうど `h` 手なら尽きる」の向きだけで
**逆向きが無かった**ので作った。`shiftTick` は `remaining := dec s.remaining`
（`GalilScaffoldChainInputSupply:1442`）で、`ChainShiftRun.next` は
`positive s.remaining = true` を要求するから手数は初期値で一意。

### `PalPeg/RoundHistory.lean` の 19 宣言（全部標準 3 公理以内、うち 3 本は公理ゼロ）

| 群 | 宣言 |
|---|---|
| ラウンド履歴 | `RoundHistory` / `roundHistory_start` / `roundHistory_tick` / `roundHistory_of_steps` / `onlyMatchedRun_of_roundHistory` |
| shift 相の収集 | `chainShiftRun_snoc` / `chainShiftRun_snoc_shiftOne` / `chainShiftRun_tick` / `chainShiftRun_of_steps` / `chainShiftRun_length_eq` |
| period テープ | `chain_shift_period` / `chain_shift_periodLength` / `chain_shift_period_focus` / `periodLength_onlyMatchedRun` |
| 比較の watch | `positive_false_of_zero` / `internal_eq_of_lagZero` / `outer_eq_of_false` / `watch_eq_of_mismatch_lagZero` |
| 形の一致 | `shiftEntry_shape` / `shiftLens_frame_tick` / `shiftLens_frame_steps` |

**`PROOF_STACK.md` の手順 11 段に必要な部品は全部そろった。残るのは組み立てだけ。**

## 2026-09-19 n155: shift 入口の形が `round_next` の要求とぴったり一致することを確定

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。計器は動いていない。**

`shiftEntry_shape`（`PalPeg/RoundHistory.lean`、18 宣言目）。一発で通った。

`round_next` と `CompareRounds.next` は shift 相の起点を
`⟨s1.center, left s1.left, ofNat h, inc s1.radius, inc (inc s1.length)⟩` という
**明示の形**で要求する。これが run の実状態と一致することを一次情報で照合した:

* `ScanVM` は `left` / `right` / `chain` の 3 場だけ（`GalilScaffoldTopScan:26`）なので
  `scanLens.set` は center / radius / length を触らない
* `afterMismatch s vs vq = {searchLens.set (scanLens.set s vs) vq with radius := radiusAfter s}`
  （`GalilScaffoldTopSearch:52`）、`radiusAfter s = inc s.radius`（無条件）
* `beginShiftVM h w s t` は `remaining := ofNat h` / `length := inc (inc s.length)` /
  `chain := .watch (immediate w)` / `cycle := reset` を置く（`GalilScaffoldTopShiftCycle:23`）

**必要な側条件は比較の `vs.left = left s1.left` だけ。**
ついでに `(shiftLens.get s2).chain = .watch (immediate wch)` と
`(shiftLens.get s2).cycle = reset` も出るので、`chainShiftRun_of_steps` の基底
（`.stop`）がそのまま立つ。

## 2026-09-19 n154: 組み立てに足りない部品がゼロになった

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。計器は動いていない。**

`shiftLens_frame_tick` / `shiftLens_frame_steps` を追加。
`shiftOne` は `Lens.rel`（`GalilScaffoldTopLens:28`：
`R (L.get s) (L.get t) ∧ t = L.set s (L.get t)`）なので、第 2 成分がちょうど
「lens の場以外は変わらない」。これを `Lens.set_set` で `Steps` に沿って合成した。
これが `round_next` の結論の形（`shiftLens.set s2 ⟨t', .watch v, cycle⟩`）に
run の状態を合わせるのに要る最後の部品だった。

**`PalPeg/RoundHistory.lean` は 17 宣言。全部標準 3 公理以内（3 本は公理ゼロ）。
`PROOF_STACK.md` の `roundSeg_of_run` 手順 11 段のうち、部品が無いものはもう無い。**

### この session でここまでに積んだ足場（全部標準公理のみ、全体 build 緑）

| 部品 | 役割 |
|---|---|
| `RoundHistory` ＋ `roundHistory_start` / `_tick` / `_of_steps` | ラウンドの履歴（`ScanSeg` ＋ 起点の `OriginAt` ＋ `Canonical`）を run に沿って運ぶ |
| `onlyMatchedRun_of_roundHistory` | 履歴から `CompareRounds.next` の第 1 引数と末尾の `Canonical` を取り出す |
| `chainShiftRun_snoc` / `_snoc_shiftOne` / `_tick` / `_of_steps` | shift 相を run から集める（`round_next` の `hchain`） |
| `chain_shift_period` / `_periodLength` / `_period_focus` | period テープは shift を通して不変 |
| `periodLength_onlyMatchedRun` | period テープの長さは scan 相のラウンドで不変 |
| `positive_false_of_zero` / `internal_eq_of_lagZero` / `outer_eq_of_false` / `watch_eq_of_mismatch_lagZero` | lag ゼロの不一致比較で watch は不変（`hpred` の橋） |
| `shiftLens_frame_tick` / `_steps` | shift 相では `shiftLens` の外は不変 |

**計器（`#print axioms`）はまだ 4 本のまま。** 上は全部 (C)（公理を減らす操作）の前段。

## 2026-09-19 n153: `round_next` の入力 15 個すべての出どころが確定した

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。計器は動いていない。**

最後に残っていた `hlen : Canonical s1.length` の出どころは
`GalilScaffoldTopSegmentHeads.scanSeg_counters`
（`ScanSeg → (Canonical s.radius → Canonical t.radius) ∧ (Canonical s.length → Canonical t.length)`）。
`RoundHistory` に `Canonical s₀.radius ∧ Canonical s₀.length` を足して起点で持たせ、
`onlyMatchedRun_of_roundHistory` が末尾の `Canonical` も返すようにした。

**`PROOF_STACK.md` に `roundSeg_of_run` の組み立て手順を 11 段すべて書いた。**
足りない小補題は **1 個だけ**:

> shift 末尾の状態 `y` について `y.vm = shiftLens.set s2 (shiftLens.get y.vm)`
> （`round_next` の結論の形に合わせるため）。`shiftOne` は `Lens.rel` なので
> 第 2 成分が `t = L.set s (L.get t)`＝「lens の場以外は変わらない」。
> これを `Steps` に沿って合成するだけ。

## 2026-09-19 n152: ラウンド境界の入力があと 1 個（`hlen`）になった

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。計器は動いていない。**

`PalPeg/RoundHistory.lean` が 15 宣言に。追加 5 本:

### `periodLength_onlyMatchedRun` — scan 相のラウンドは period テープの長さを変えない

`periodLength_consume`（`GalilChainCoupling:210`）は**無条件ではなく** `OnBlock` を側条件に
取るが、`OnBlock` は `consume` で保たれる（`GalilBranchInvariants.onBlock_verifier_consume`）
ので**起点 1 点だけ**あればよい。起点の `WatchBlock` は
`CloseoutRoundReads.blockInv_of_chainPosInv2` から出る。

これで `RoundSeg` の第 1 節 `periodLength wch' = periodLength wch` の材料が全部そろった
（shift 相は n149 の `chain_shift_periodLength`、公理ゼロ）。

### `watch_eq_of_mismatch_lagZero` — `hpred` の橋

`round_next` の `hpred` は**compare 前**の watch について言うのに、shift guard は
`afterMismatch s1 vs vq` 上で評価されるので**compare 後**の watch を見る。
この差は lag ゼロなら消える:

* `Internal` の `take` は `positive lag = true` を要求 → lag ゼロなら `idle` のみ
* 不一致比較の事象は `b = false`、`Outer s false t` は `idle` のみ
  （`queued` と `immediate` はどちらも `b = true`）

補助: `positive_false_of_zero` / `internal_eq_of_lagZero` / `outer_eq_of_false`。

### 入力表の現状（`PROOF_STACK.md`）

`GalilScaffoldTopRoundS.round_next` の入力 15 個のうち **14 個が確認済み**。
**残る未確認は `hlen : Canonical s1.length` の 1 個だけ**（`LPackM2` / `RadLedger` 側）。

## 2026-09-19 n151: ラウンド境界に無かった `ChainShiftRun` の収集を作った

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。計器は動いていない。**

### 新規 2 本（`PalPeg/RoundHistory.lean`、これで同ファイル 10 宣言）

* `chainShiftRun_tick` — shift 相の 1 tick で `ChainShiftRun` が伸びる。
  shift mode の `Tick` は `shift_one` と `shift_done` だけで、残り 21 構成子は
  mode guard で落ちる。行き先も shift mode なら `shift_done` も落ちる
  （`GalilScaffoldTop:136` が mode を `.scan` に戻す）。
  `CopyIdle` が要るのは合併フレームの `remainingPos` が `H ∨ B` だから
* `chainShiftRun_of_steps` — run に沿って伸ばす（`roundHistory_of_steps` と同じ形）

**これで n149 の入力表の `✗`（存在しない）が埋まった。**
`GalilScaffoldTopRoundS.round_next` の入力 15 個のうち **14 個が出どころ確認済み**、
未確認は 2 個（`hpred` の `afterMismatch` の right、`hlen : Canonical s1.length`）。

### 次にやること（`PROOF_STACK.md` に記録）

`round_next` を run から呼ぶ組み立て（`roundSeg_of_run`）。
その第 1 節 `periodLength wch' = periodLength wch` には「ラウンド内で `periodLength` が
保たれる」が要る:

* shift 相は `chain_shift_periodLength`（**済・公理ゼロ**）
* scan 相は `periodLength_consume` を使うが、**これは無条件ではなく block 側条件を取る**
  （`CloseoutRoundUnique:221` の使い方で確認）。側条件は
  `CloseoutRoundReads.blockInv_of_chainPosInv2` 経由で出る見込み（**未検証**）

## 2026-09-19 n150: `ChainShiftRun` を後ろから伸ばす（ラウンド境界の残り 1 個の半分）

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。計器は動いていない。**

### 新規 2 本（`PalPeg/RoundHistory.lean`）

* `chainShiftRun_snoc` — `ChainShiftRun s w cycle n t v finish` ＋ 1 手の許可条件 →
  `ChainShiftRun s w cycle (n+1) (shiftTick t) (chainShiftOne v) (inc (inc finish))`。**公理ゼロ**
* `chainShiftRun_snoc_shiftOne` — `(galilFrameS P q first).shiftOne u t` 1 手を吸収

`ChainShiftRun` は `next` で前から積む inductive なので run を歩きながら積むには
後ろから伸ばせないといけない——`OnlyMatchedRun` と同じ問題で、
`MatchedRunSnoc.onlyMatchedRun_snoc` と同じ形で解いた。

### 一次情報で確認した形（`PROOF_STACK.md` に転記）

* `shiftOne`（`GalilScaffoldTopShift:42`）は **`ChainShiftRun.next` の 1 手そのもの**
* `beginShiftVM h w s t`（`GalilScaffoldTopShiftCycle:23`）は
  `chain := .watch (immediate w)` / `remaining := ofNat h` / `cycle := reset` を置くので、
  **shift 入口の `ChainShiftRun … 0 …` は `.stop` でタダ**
* 合併フレームの `remainingPos` は `H ∨ B`（`GalilScaffoldTopMerge:65`）なので
  copy 側を殺すのに `CopyIdle` が要る
* 終端判定は `chain_shift_exhausts`（`GalilScaffoldTopInvariant:46`）

### 設計判断

`Tick` の 23 構成子の場合分けを**この補題では書かなかった**。消費者側でどうせ
場合分けするから（`ShiftPhaseDeterminism.tick_shift_det:54` がその形で全部書いている）。
CLAUDE.md「変によく考えず定理ふやすのやめよ」に従って、shift 1 手の中身だけを扱う。

### 残り

`ShiftHistory` の tick 保存（shift mode の `Tick` 23 構成子の場合分け。21 個は
mode guard で落ち、`shift_done` は行き先 mode で落ちる）。それができたら
`round_next` の入力 15 個が全部そろって `RoundSeg` が run から出る。

## 2026-09-19 n149: period テープは shift を通して不変（＋ラウンド境界の残りは 1 個に特定）

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。計器は動いていない。**

### 新規 3 本（`PalPeg/RoundHistory.lean` 内）

* `chain_shift_period : ChainShiftRun s w cycle n t v finish → v.machine.control.period = w.machine.control.period` — **公理ゼロ**
* `chain_shift_periodLength : … → periodLength v = periodLength w` — **公理ゼロ**
* `chain_shift_period_focus : … → symbol v…period.focus = symbol w…period.focus`

理由は一次情報で確認: `chainShiftOne`（`GalilScaffoldChainInputSupply:1478`）が変えるのは
`distance` / `boundary` / `last` / `margin` **だけ**で period テープに触らない。
`chain_shift_lag`（`GalilScaffoldTopRounds:19`）と同じ帰納法。

### ラウンド境界の残りは `ChainShiftRun` の収集 1 個（入力表は `PROOF_STACK.md`）

`GalilScaffoldTopRoundS.round_next` の入力を run からそろえる作業を 1 つずつ照合した。
15 個のうち **13 個は出どころが確認済み**（`RoundHistory` / `scan_shift` tick 構成子 /
`shiftGuardVM` / `Extra7.scanAvail` / `AuxPack` / `shift_done`）、
2 個が未確認（`hpred` の `afterMismatch` の right、`hlen : Canonical s1.length`）、
**1 個が存在しない**:

    hchain : ChainShiftRun ⟨s1.center, left s1.left, ofNat h, inc s1.radius,
                            inc (inc s1.length)⟩ (immediate w) reset h t' v cycle

これは shift 相（`shift_one` × h ＋ `shift_done`）を run から集める carrier が要る。
**found 経路の `CloseoutWatchRound33` / `37` も `ChainShiftRun` を仮説として取っている**
（`ShiftRoundInvCL` / `ShiftOriginRestCL` は open な `def`）ので、ここは共通の穴。
設計 `ShiftHistory` を `PROOF_STACK.md` に記録した。

## 2026-09-19 n148: `RoundHistory` — ラウンドの履歴を運ぶ不変量（公理は 4 本のまま）

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。計器は動いていない**（これは (C) の前段の足場）。

### 新規 `PalPeg/RoundHistory.lean`（5 宣言、標準 3 公理のみ）

    RoundHistory P q first delay w c s :=
      ∃ n c₀ s₀ w₀, ScanSeg P q first delay n c₀ s₀ c s ∧
        OriginAt w s₀ ∧ s₀.periodOnly = true ∧
        s₀.chain = ChainVM.watch w₀ ∧ zero w₀.lag = true

* `roundHistory_start` — ラウンド起点そのもの（`ScanSeg.stop`）
* `roundHistory_tick` — scan 相の 1 tick で伸びる（`MatchedRunSnoc.scanSeg_snoc_tick`）
* `roundHistory_of_steps` — run に沿って伸びる（側条件は `hScanWatchAll`）
* `onlyMatchedRun_of_roundHistory` — 下層の射影を取り出す（`CompareRounds.next` の第 1 引数）

**区間抽出（`CloseoutSegment.ScanToScan`）は使っていない。**

### なぜこれが要るか（測定済みの negative）

ラウンド境界（`scan_shift`）で read origin を貼り替えるには
`CompareRounds h (toOnly s w₀) 1 (toOnly s' v)`——**ラウンド 1 周ぶんの履歴**が要る
（`CloseoutRoundSeg.originAt_next_of_roundSeg`）。1 手の `Tick` からは作れないので、
**状態局所な不変量では閉じない**。だから履歴（`ScanSeg`）を持ち歩く。

### 次の小ブロック（特定済み・未着手）

`CompareRounds.next` の残り入力のうち、**`periodLength` が shift を通って保存される**
という補題が**存在しない**:

    chain_shift_period : ChainShiftRun s w cycle n t v finish → periodLength v = periodLength w

`chain_shift_lag`（`GalilScaffoldTopRounds:19`）と `chain_shift_phase`
（`GalilScaffoldChainReadOrigin:451`）が同じ帰納法で書かれているので、
`chainShiftOne` が period テープの `left.length + right.length` を変えないことを
示せば同型に通る。`periodLength (immediate w) = periodLength w` は既に 5 箇所で使われている。

### 今回やった honest な訂正

`lake build` を `(… ; echo BUILD=$?)` で包んでいたのでサブシェルの終了コードは
`echo` の 0 になる。**background task の通知の「exit code 0」を build 成功と読んで
一度間違えた**（実際は `BUILD=1`、docstring 直後に `set_option … in` を置いた構文エラー）。
以後 `BUILD=` の行を必ず読む。

## 2026-09-19 n147: **訂正** — 「中身は strictly weaker」は嘘やった

**全体 build 成功（EXIT=0、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。**

### 何を間違えたか

n145 と n146 で「公理の本数は 4 のまま、**中身は元より弱い**」と書いた。
`ShiftPal` 公理については**これは嘘**。

* 旧: `obligation_shiftPalAlongTrace` — 結論 `ShiftPal` そのもの
* 新: `obligation_shiftPalResiduesAlongTrace` — 残差 3 つ
* 定理は `残差 3 つ → ShiftPal`。**つまり残差は `ShiftPal` を含意する = 論理的には強い。**
  逆向き（`ShiftPal → 残差`）は無い。

「結論を前提に置き換えたら弱くなる」は成り立たない。**弱くなるのは guard を
狭めたときだけ。** 自分の言葉を検査せずに 2 回書いた。

### 弱くなった部分（こっちは本物）

| 変更 | 弱くなったか | 理由 |
|---|---|---|
| `obligation_shiftPalAlongRun` → `…AtWatchAlongRun` | **○ 本物** | chain が watch の点だけに guard を狭めた。非 watch は `shiftPal_of_chainNotWatch` で定理 |
| `…AtWatchAlongRun` に `canRight z.vm.right` を追加 | **○ 本物** | 消費者が持っている場を仮説に入れた（過剰量化の解消） |
| `ShiftPal` → 残差 3 つ（run 形・trace 形とも） | **× 逆に強い** | 残差が `ShiftPal` を含意する |

### では残差化は前進なのか

**前進ではあるが、「弱くなった」という理由ではない。** 正しい理由は 3 つ:

1. **`ShiftPal` は global 形では偽の疑いが濃く producer が無かった**（n112）。
   残差 3 つはどれも **producer が特定済み**（`readsShift_at_actual` /
   `first_round` / `candidate_palAt`）
2. 残差は**機械レベルの事実**で、入力語についての回文の主張を含まない方向に動いている
   （n147 で `FreshShiftLedger` の 2 回文は `candidate_palAt` で消える見込み）
3. **本数は増えていない**（4 のまま）

### 公理の操作で許される 3 種類（以後これで判定する）

| 操作 | 弱くなるか | 本数 |
|---|---|---|
| (A) guard を消費者が供給する場まで狭める | **弱くなる** | 変わらず |
| (B) 結論を「十分な primary な前提」に置き換える | **弱くならない**（強い） | 変わらず。前進は「証明可能性」 |
| (C) サブ前提を定理として証明して公理から外す | **弱くなる** | **減る**（これが本命） |

n145/n146 は (A) と (B) を混ぜて (B) も「弱い」と書いた。これが誤り。

## 2026-09-19 n146: run 形 `ShiftPal` も残差 3 つに（公理は 4 本のまま、中身はさらに弱い）

**全体 build 成功（EXIT=0、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。**

### やったこと

`obligation_shiftPalAtWatchAlongRun`（watch 点での `ShiftPal` そのもの）を
`obligation_shiftPalResiduesAlongRun`（残差 3 つ）に置き換えた。**本数は増えていない。**

**n147 訂正**: この置き換えは**弱化ではない**（残差は `ShiftPal` を含意する）。
弱くなったのは `canRight` を仮説に入れた部分だけ。

    [propext, Classical.choice, Quot.sound,
     obligation_cycleOracle,
     obligation_localRealization,
     obligation_shiftPalResiduesAlongRun,     -- ← 今回弱めた
     obligation_shiftPalResiduesAlongTrace]

**これで 2 本の `ShiftPal` 公理は完全に同内容**（量化の形だけが run / trace で違う）:

| 残差 | 中身 | producer 候補 |
|---|---|---|
| `H_readsShift` | shift 相のラウンド読み出し | `RoundSegFromRun.readsShift_at_actual`（構成 run / 実 run の対 ＋ `OriginAt` が要る） |
| `H_freshShiftAtShiftEntry` | shift 入口の最初のラウンド | `GalilScaffoldTopFirstRound.first_round`（`Entry` 形なので橋が要る） |
| `FreshShiftLedger` | 準備直後の watch の台帳 | n141〜n144 で 3 種類まで還元済み |

### 新しい定理 `ShiftPalAlongTrace.shiftPal_alongRun`

`CloseoutBundleRun.shiftPal_of_run_B` の適用。**run 形で新たに要る入力はゼロ**だった:

| 入力 | 出どころ |
|---|---|
| chain が idle | `CloseoutShiftLocalFree.chainIdle_of_invS`（`InvLPC` の `InvS`） |
| `AuxPack` | `CloseoutPackRun2.auxPack_steps` ＋ `InvLPC` の 3 場（`coupled`/`front`/`copyPack_of_invLPC`）＋ `GalilOracleLeaves2.hlive_of_invLPC` |
| `canRight right` | **消費者が持っていた**（下記） |

### `canRight` は過剰量化だった（CLAUDE.md の兆候そのもの）

`hShiftPalAlongRun` の唯一の消費者 `CloseoutMarksPack.packRunR_MW_marksFree` は
帰納段で `hn : BigPack2MG7W'' … (g n)` を持っており、その
`extra : Extra7` の `scanAvail` が scan・非 replay 点でちょうど
`canRight (g n).vm.right` を与える。**前の形はそれを捨てていた。**
`packRunR_MW_marksFree` と `CloseoutFinalBranch.given_scanLandingObligations` の
`hShiftPalAlongRun` 仮説に `canRight z.vm.right →` を足しただけで、
call site は `(hn.extra.scanAvail hs.1 hs.2)` で無償。

### 次の当たり（未検証）

`H_readsShift` と `CloseoutRoundReads.ReadsRound` は**mode guard だけが違う**:

    ReadsRound    : mode = scan  → replaying = false → periodOnly = true → …
    H_readsShift  : mode = shift → replaying = false → periodOnly = true →
                    positive remaining = false → …（結論は同一の `ReadsInv`）

しかも `CloseoutRoundReads.ReadsRun`（mode guard なしの形）が既にあって
`readsRound_of_readsRun` で `ReadsRound` を無償で出す。**`ReadsRun` を
`RoundBundle` の場にできれば `H_readsShift` も無償になる**——CLAUDE.md の
「guard を狭く切ると義務が増える」の同型 9 例目の可能性。次はこれを検査する。

## 2026-09-19 n145: **公理を 4 本に戻した**（n132 の原子化は後退だった）

**全体 build 成功（EXIT=0、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。**

### コウタの指摘（受けた）

* 「え？なんでいつのまにか前提ふやしてるの」「4 つに減らしたやろ」
* 「前提を増やしてどうするねん。せっかく機械的に進捗示すためにこっちが指示したのに」
* 「前提が難しいなら、その前提のサブ前提を証明せなあかん」

n132 で `obligation_shiftPalAlongTrace` を 3 原子に割って **4 → 6 にした**。
CLAUDE.md の「公理は 1 場ずつの原子に分解する」を根拠にしたが、
**計器の読みは本数**なので、これは数字を悪くしただけ。さらにそれを
「後退ではなく割れた状態」と書いて正当化した——そこが甘かった。

### 規律（これ以降）

1. **公理の本数は増やさない。** 4 が上限で、減らす方向にしか動かさない。
2. **前提が難しいときは、その前提のサブ前提を定理として証明する。**
   新しい公理にはしない。**公理の文が弱くなるだけ**にする。
3. 「原子に割ったから後退ではない」式の正当化をしない。

### 現在の 4 本（実測）

    [propext, Classical.choice, Quot.sound,
     obligation_cycleOracle,                    -- CycleOracleMC3（found 経路）
     obligation_localRealization,               -- H_realizeLIMW'（局所実現）
     obligation_shiftPalAtWatchAlongRun,        -- watch 点で ShiftPal（run 形）
     obligation_shiftPalResiduesAlongTrace]     -- trace 形の残差 3 つを束ねたもの

**元の 4 本と中身が違う**（n147 で訂正: 下の 2 つ目は**弱くなっていない**）:

* `obligation_shiftPalAlongRun` → `…AtWatchAlongRun`（chain が watch の点だけ。
  非 watch は `shiftPal_of_chainNotWatch` で空虚）
* `obligation_shiftPalAlongTrace`（`ShiftPal` 丸ごと）→ `…ResiduesAlongTrace`
  （`H_readsShift` ＋ `H_freshShiftAtShiftEntry` ＋ `FreshShiftLedger` の 3 残差）。
  とくに 3 つ目は `ShiftPal` 丸ごとから「period テープの中身／半径と周期の大小／
  period テープの位相」の 3 種類まで還元済み（n141〜n144、下に
  `shiftPal_of_freshShiftLedger` → `shiftPalAt_fresh_of_candidate` →
  `reshift_of_palAt_pair` → `periodOn_*` の鎖が全部入っている）

**これが「サブ前提を証明して公理の文を弱める」の実例。**

## 2026-09-19 n144: `hCaught` の正体 — chain の予測証明書（回文からは出ない）

**全体 build 成功（EXIT=0、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 6。
無条件 PAL は未完。§10.5 は未達。**

### `hCaught` を展開すると

`shiftPalAt_fresh_of_candidate` の中で導いた 2 つを並べる:

* `hsym'`（**ガードから出る**）: `symbol wch…period.focus = (encoded w)[pos + r₀ + 1]?`
  （`shiftGuardVM` の予測節 ＋ `right_read_index` ＋ `ScanInvariant.rightPos`）
* `hCaught`（**残差**）: `(encoded w)[pos + r₀ + 1 − 2h]? = symbol wch…period.focus`

合わせると `(encoded w)[pos + r₀ + 1 − 2h]? = (encoded w)[pos + r₀ + 1]?`。

**`pos + r₀ + 1` は現在の回文の右端 `pos + r₀` の 1 つ外**。だから
`periodOn_right_of_palAt_pair` が出す `PeriodOn (encoded w) (2h) pos (pos + r₀)` では
**原理的に届かない**（`j + 2h ≤ pos + r₀` までしか主張しない）。
`reshift_from_right` が `hright` の最後の 1 添字を別に要求するのはそのため。

### したがって `hCaught` は「chain の予測証明書」

意味は「period テープの焦点（＝chain が次に来ると予測している記号）が、
入力の `2h` 手前の記号と一致する」——**period テープが入力と `2h` ずれて整合している**こと。

* `periodOnly = true` 側ではこれが `RoundScan.pred`
  （`symbol focus = (encoded raw)[C + R + 2 + used − 2h]?`、終端で添字が `C + R + 1`
  ＝ `pos + r₀ + 1 − 2h` に一致。n142 の測定どおり）
* `periodOnly = false` 側は `RoundScan` が使えない（n143: `cycle` 凍結）ので、
  **準備直後の period テープの整合を運ぶ場**が要る

**回文からは出ない**（新しく読んだ記号についての主張なので）。
DP の `Candidate` は period テープの**中身**を保証するが、
「いまどの位相を指しているか」は chain の台帳の話。

### 残差 5 本の性格が確定した

| 残差 | 性格 | 出どころ |
|---|---|---|
| `hIn` / `hOut` | period テープの**中身**（DP の `Candidate`） | `prep_watch_start_least` ＋ `palAt_pair_of_candidate` |
| `hLo` / `hHi` | 半径と周期の**大小** | `found_radius_le_two_period` ＋ 伸び |
| `hCaught` | period テープの**位相** | 準備直後の整合を運ぶ場（`RoundScan.pred` の `periodOnly = false` 版） |

3 種類に分かれた。**`hCaught` だけが新しい場**で、残り 4 つは既存の定理からの配線。

## 2026-09-19 n143: **訂正** — `RoundScan` は `periodOnly = false` では偽。`ChainRound` のガードは必要だった

**全体 build 成功（EXIT=0、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 6。
無条件 PAL は未完。§10.5 は未達。**

### n142 の推測は間違いだった（一次情報で潰した）

n142 で「`RoundScan` に `periodOnly` の場が無いので `ChainRound` の
`periodOnly = true` ガードは**定義上の選択**」と書いた。**これは誤り。**

一次情報:

* `GalilScaffoldTopSearch:77` — `afterBirth true s = {s with periodOnly := false, cycle := reset}`
  （誕生で `cycle` が 0 になる）
* `GalilScaffoldTopSearch:41` — `cycleAfter s = if s.periodOnly then dec s.cycle else s.cycle`
  （**cycle は `periodOnly = true` のときだけ減る**）

したがって **`periodOnly = false` の間、`value cycle` は誕生時の `0` に凍結**される。
`RoundScan.count : value v.cycle = (2h : ℤ) − used` に `0` を入れると `used = 2h` で、
`RoundScan.fresh : used < 2 * h` と**矛盾**する。

**`RoundScan` は `periodOnly = false` の状態では常に偽。**
`ChainRound` の `s.periodOnly = true →` ガードは**必要**だった。

### 帰結: `periodOnly = false` 側には別の進行カウンタが要る

`cycle` が凍結しているので、最初の shift における「周期境界にいること」は
**watch 自身の `distance` / `boundary` / `last` / `phase`** で追う必要がある。
これが n138 で言った「`RoundScan` の `periodOnly = false` 版」の実体。

**`shiftPalAt_fresh_of_candidate`（n141）の 5 残差が正しいインタフェースである根拠**:
`hIn` / `hOut` / `hLo` / `hHi` / `hCaught` は **`cycle` に一切触れていない**。
`hCaught` は `symbol period.focus = (encoded w)[…]?` という watch 側の事実だけ。
だから `cycle` が凍結していても成立し得る。

### 次に測るべきこと

`GalilScaffoldChainConsume.consume` の
`phase := if boundaryEvent then advancePhase s.phase else s.phase` と
`boundary := if boundaryEvent then distance else s.boundary` /
`last := if boundaryEvent then s.boundary else s.last` の更新から、
`phase = 4` が「period テープを 4 回の境界イベント分たどった」ことを言う。
そこから `hCaught`（焦点が入力の `2h` 手前を指す）が出るか。

**`cycle` を使う道は閉じた**（凍結しているので情報を持たない）。
`distance`/`boundary`/`last`/`phase` の 4 つが唯一の進行情報。

## 2026-09-19 n142: `hCaught` は終端での `RoundScan.pred` と同じ添字（`RoundScan` に `periodOnly` の場は無い）

**全体 build 成功（EXIT=0、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 6。
無条件 PAL は未完。§10.5 は未達。**

### 測定 1: 添字が一致する

`GalilRoundPeriod.RoundScan` の
`pred : symbol w.machine.control.period.focus = (encoded raw)[C + R + 2 + used − 2h]?`
は、`position s.center = C + h`・`r₀ = R + h` を入れると
`shiftPalAt_fresh_of_candidate` の `hCaught` の添字
`position s.center + r₀ + 1 − 2h` = **`C + R + 1`** と一致する
（終端 `used = 2h − 1` のとき。`terminal_palindrome` も同じ書き換えをしている）。

**つまり `hCaught` は新しい場ではなく、`RoundScan.pred` の終端形。**

### 測定 2: `RoundScan` に `periodOnly` の場は無い

`RoundScan` の全 12 場（`chain` / `caught` / `canon` / `count` / `fresh` / `size` /
`posH` / `pal` / `room` / `origin` / `pred`）は幾何と台帳だけで、
**`periodOnly` に触れる場は 1 つも無い**。

`CloseoutPackRun31.ChainRound` の `s.periodOnly = true →` ガードは
**定義上の選択**であって `RoundScan` が要求しているものではない。

### 残る本当の差（`periodOnly = false` 側）

`shiftPal_of_chainRound` は `hend : singlePositive s.cycle = true`（ガードの
`periodOnly = true` 枝）から `terminal_iff` 経由で `used = 2h − 1` を得ている。
`periodOnly = false` 枝のガードは `negative wch.margin = false` で、**`used` を固定しない**。

Scala 正本（CLAUDE.md の記録: `ScaffoldGalil.scala:254`）でも `canShift` は
`periodOnly` のとき `singlePositive cycle` を要求し、そうでないときは margin を見る。
したがって最初の shift では `used` は cycle では固定されず、
**`phase = 4`（4 回の boundary event）が進行の指標**になる。

**次に測るべきはここ**: `phase = 4` ＋ `negative margin = false` から
`used` の位置（＝周期境界にいること）が出るか。`GalilScaffoldChainConsume.consume` の
`phase := if boundaryEvent then advancePhase s.phase else s.phase` と
`distance`/`boundary`/`last` の更新が一次情報。

### 今日の到達点（まとめ）

* 反証済み `hpack` 節 4 / 節 7 を found 経路から**除去**（`(hwatch : PrepLandingWatchC …)` は 0 本）
* 過剰仮定の弱化 6 件（`split4/3_of_prefix` / `fallbackLanding_of_pack` /
  `fallbackTick_of_watchTick` / `reshift_from_right` / `WatchMismatchNoShiftC` の guard）
* 公理の原子化（`shiftPalAlongTrace` → 3 原子）と狭化（run/trace 両方を **watch 点**に）
* fresh 側 `ShiftPal` の数学の芯完成（`periodOn_mirror'` / `periodOn_of_palAt_pair` /
  `periodOn_right_of_palAt_pair` / `reshift_of_palAt_pair` / `shiftPalAt_fresh_of_candidate`）
* 過去の自分の記述の訂正 6 件（`first_round`／`fresh_shift_entry`／`PalInPegUnconditional`
  の docstring／`LagPos` 不要／`shiftPal_of_readOrigin` の docstring／「found 半径正」の需要 3→2）

## 2026-09-19 n141: fresh 側 `ShiftPal` の**数学的な芯が完成**（4 段、全部標準公理）

**全体 build 成功（EXIT=0、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 6。
無条件 PAL は未完。§10.5 は未達。**

### 完成した芯

    PalPeg.reshift_of_palAt_pair (word : List (Fin 3)) (C h r : ℕ)
      (hin   : Manacher.PalAt word (C − h) h)          -- DP の Candidate（内側）
      (hout  : Manacher.PalAt word (C − 2h) (2h))      -- DP の Candidate（外側）
      (hcur  : Manacher.PalAt word C r)                -- ShiftPal の hScanInv.palindrome
      (hstep : 0 < h) (hsmall : 2h ≤ r) (hle : r ≤ 4h)
      (hend  : C + r + 1 < word.length)
      (hpred : word[C+r+1]? = word[C+r+1−2h]?)         -- shiftGuardVM の予測節
      : Manacher.PalAt word (C + h) (r + 1 − h)        -- ShiftPal の結論の第 3 節そのもの

### 4 段（今日の作業、すべて `PalPeg.GalilPeriodUnion` / `GalilScaffoldChainInputSupply`）

| 段 | 定理 | 効いた気づき |
|---|---|---|
| 0 | `reshift_from_right` の弱化（n139） | `hold` は半径 `radius` ではなく `step` 分で足りた（本体での使用は 2 行だけ） |
| 1 | `periodOn_mirror'` | 既存 `periodOn_mirror` は右→左。要るのは左→右で、証明は対称 |
| 2 | `periodOn_of_palAt_pair` | 中心が `d` ずれた 2 回文の鏡映が `2C − 4d − i` で一致 |
| 3 | `periodOn_right_of_palAt_pair` | `PeriodOn.mono`（`r ≤ 4d`）＋ 段 1 |
| 4 | `reshift_of_palAt_pair` | 末尾 1 添字（`j + 2h = C+r+1`）を予測で埋めて `reshift_from_right` へ |

**新しい数学はもう無い。** 残るのは配線 3 本:

1. `hin` / `hout` — この watch の周期テープが DP の `Candidate` から来たという**履歴**。
   材料は `GalilPrepLeast.prep_watch_start_least`（`watchStart ver c ys b credits` ＋
   `Candidate w lower h` ＋ `ys.length + 1 = h`）と
   `CloseoutWatchPhase3.palAt_pair_of_candidate`。
2. `hpred` — `shiftGuardVM` の最終節 `symbol w.machine.control.period.focus = read s.right`
   を添字形 `word[C+r+1]? = word[C+r+1−2h]?` へ。
   `periodOnly = true` 側は `hI.pred` がこの形を持っている（`CloseoutPackRun31:190` 付近）。
3. `2h ≤ r ≤ 4h` — found 時の `found_radius_le_two_period`（`radius ≤ 2h`）＋
   その後の一致比較ぶんの伸びを run に沿って運ぶ台帳。

## 2026-09-19 n140: fresh 側 `hright` の材料を全部特定した（`periodOn_*` と `found_radius_le_two_period`）

**全体 build 成功（EXIT=0、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 6。
無条件 PAL は未完。§10.5 は未達。**

### `hright` の正体

`reshift_from_right` の `hright` は、`GalilPeriodUnion.PeriodOn` と**同じ形**:

    PeriodOn x p a b := ∀ i, a ≤ i → i + p ≤ b → x[i]? = x[i + p]?

fresh 側で要るのは `PeriodOn (encoded w) (2h) (position s.center) (position s.center + r₀ + 1)`
——**現在の中心より右**で周期 `2h`。

### 既にある部品（一次情報で確認）

| 定理 | 内容 |
|---|---|
| `GalilPeriodUnion.periodOn_mirror (hpal : PalAt x C k) (hp : p ≤ k) (h : PeriodOn x p C (C+k)) : PeriodOn x p (C−k) C` | **右→左**。要るのは逆向き（左→右）だが証明は対称 |
| `GalilPeriodUnion.periodOn_union` | 重なる 2 区間の周期を合併 |
| `GalilPeriodUnion.encoded_periodOn_even` | `encoded` 上の偶数周期 |
| `CloseoutWatchPhase3.palAt_pair_of_candidate` | `Candidate` → `PalAt (pos−h) h` ∧ `PalAt (pos−2h) (2h)` |
| **`GalilReplayBudgetProof.found_radius_le_two_period`** | **found 時に `value sF.radius ≤ 2*h`**（＋`Candidate`＋最小性＋`1 ≤ h`）を**無条件で**出す |

### 効くこと

`found_radius_le_two_period` の `r₀ ≤ 2h` が、**「周期が回文全体を覆う」ための境界**。
`Candidate` が保証するのは place stream の接頭辞 `take (4h+1)` の回文性で、
`r₀ ≤ 2h` ならその範囲が現在の回文を覆う。つまり n139 で「未特定」とした
`hsmall : 2h ≤ r₀` と合わせると **found 時点では `r₀ = 2h`**。

ただし `ShiftPal` が評価されるのは found より**後**（誕生した chain の最初の shift）で、
そこまでに一致比較のぶん `r₀` が伸びている。したがって必要なのは

    found 時の r₀ = 2h  ＋  その後の一致比較ぶんの伸び

を run に沿って運ぶ台帳。これが fresh 側 `ShiftPal` の最後の芯。

### 次の具体手順

1. `periodOn_mirror` の左→右版（証明は対称、`Manacher.mirror_getElem?` を使う）
2. `palAt_pair_of_candidate` の 2 回文 → `PeriodOn (encoded w) (2h) (pos−2h) pos`
   （`periodOn_union` ＋ `encoded_periodOn_even`）
3. 1 を当てて `PeriodOn (encoded w) (2h) pos (pos+r₀)`、末尾 +1 は予測（`shiftGuardVM` の
   最終節 `symbol period.focus = read s.right`）
4. `reshift_from_right` に流して `PalAt (encoded w) (pos + h) (r₀ + 1 − h)`

**新しい数学はない。既存の `periodOn_*` 層と `found_radius_le_two_period` の配線。**

## 2026-09-19 n139: `reshift_from_right` の `hold` は半径 `step` 分で足りた（fresh 側の origin が DP から出る）

**全体 build 成功（EXIT=0、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 6。
無条件 PAL は未完。§10.5 は未達。**

### 弱化（一次情報で測って実施）

`GalilScaffoldChainInputSupply.reshift_from_right` は
`hold : Manacher.PalAt word center radius` を取っていたが、
本体での使用は **2 行だけ**（`:1153`/`:1155`）で、`PalAt word center step` を
作るためにしか使っていなかった。仮定をそこまで弱め、呼び出し側 3 箇所
（`CloseoutPackRun31:178`、`GalilScaffoldChainReadOrigin:657`、
`GalilScaffoldChainInputSupply:2748`）を inline の縮小で通した。全体 build 緑。

**意味**: 「origin の回文」は半径 `radius` 分は要らず、**周期長 `h` 分だけあれば足りる**。
そして `GalilDpCorrect.Candidate w lower h` の第 3 節
`(w.take (2h+1)).reverse = w.take (2h+1)` はまさに中心 `h`・半径 `h` の回文。
`CloseoutWatchPhase3.palAt_pair_of_candidate` がそれを
`PalAt (encoded raw) (pos − h) h` の形で出す。

**`periodOnly = true` 側は `RoundScan` が前ラウンドの origin を運んでいたが、
fresh 側は DP の `Candidate` が直接 origin をくれる——運ぶ必要がなかった。**

### fresh 側 `ShiftPal` の残差（`reshift_from_right` の引数ごとに測った）

| 引数 | fresh 側の出どころ | 状態 |
|---|---|---|
| `hold : PalAt word (pos−h) h` | `palAt_pair_of_candidate` 第 1 成分 | **揃った**（今回） |
| `hcurrent : PalAt word pos r₀` | `ShiftPal` の仮説 `hScanInv.palindrome` | **揃っている** |
| `hstep : 0 < h` | `Candidate` の `lower < h` | **揃っている** |
| `hsmall : h ≤ r₀ − h`（＝ `2h ≤ r₀`） | 未特定 | **要る**（台帳 1 本） |
| `hend : pos + r₀ + 1 < length` | 入力長の台帳 | 要る |
| `hright : 右側で周期 `2h`` | `Candidate` の 2 回文（半径 `h` と `2h`、`palAt_pair_of_candidate` が両方出す）の重なり | **材料あり** |

**`hright` が本体。** `periodOnly = true` 側は `hI.pal`（前ラウンド origin、半径 `R`）の
鏡映（`Manacher.mirror_getElem?`）＋ `hI.pred` で出していた。fresh 側は
`Candidate` が中心を `h` ずらした 2 つの回文をくれるので、**重なりから周期 `2h` が出る**——
純粋な語の組合せ論で、`GalilPeriodUnion.periodOn_union`（重なりが p 個以上ある
2 つの周期区間の合併）が既にある層。

**残りは「2 回文 → 周期 2h → 右側の周期性」1 本と `2h ≤ r₀` の台帳 1 本。**

## 2026-09-19 n138: 残る `ShiftPal` 2 本の中身を特定した（chain 台帳の 1 場）

**全体 build 成功（EXIT=0、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 6。
無条件 PAL は未完。§10.5 は未達。**

### 一次情報で測ったこと

| 定理 | 結論 | `ShiftPal` に使えるか |
|---|---|---|
| `CloseoutPackRun31.terminal_palindrome` | `PalAt (encoded w) (C + 2h) (R + 1)` | **使える**（`periodOnly = true` 側で実際に使われている） |
| `GalilScaffoldTopFreshEntry.fresh_shift_entry` | `∃ o, Entry … ∧ …`（origin 台帳） | **使えない**——`PalAt` ではない |
| `CloseoutWatchPhase3.palAt_pair_of_candidate` | `PalAt … (pos − h) h ∧ PalAt … (pos − 2h) (2h)` | 座標が中心の**左側**で、`ShiftPal` は `pos + h` を要求 |

**訂正**: `shiftPal_of_readOrigin` の docstring は `periodOnly = false` 分岐の内容を
「`GalilScaffoldTopFreshEntry`」と書いていたが、そのファイルの 2 定理
（`fresh_shift_entry` / `found_shift_entry`）はどちらも `Entry`（origin 台帳）を結論とし、
`PalAt` を出さない。**shift 入口の台帳の話で、`ShiftPal` ではなかった。**
（過去の自分の docstring を一次情報にしない——今日 5 回目）

### `terminal_palindrome` の構造から分かる、必要な材料

`terminal_palindrome` は `RoundScan` の場から組み立てている:

* `hI.caught.scan.palindrome` — **現在の回文** `PalAt (encoded w) (C + h) (R + h)`
* 終端条件（`terminal_iff` ← `singlePositive s.cycle`）
* 予測（`symbol period.focus = read (right s.right)`）

このうち**現在の回文は `ShiftPal` 自身の仮説 `hScanInv : ScanInvariant w (position s.center) r₀
s.left s.right` が持っている**。終端条件は `periodOnly = false` 側では
`negative wch.margin = false` に置き換わる。

### したがって残る内容は 1 場だけ

**「run に沿って、watch している chain の周期テープ長 `periodLength wch` は
その中心における入力の本物の周期である」**

これは `Candidate`（DP の結論、`GalilDpCorrect` で無条件証明済み）＋
「この watch の周期テープはその `Candidate` から作られた」という**履歴の事実**。
`periodOnly = true` 側では `RoundScan` がその履歴を運んでいる。
`periodOnly = false` 側（誕生後の最初の shift）にはそれを運ぶ場がまだない。

**次の仕事**: `RoundScan` の `periodOnly = false` 版（margin 基準・準備直後）を
chain 台帳の 1 場として立て、`GalilPrepLeast.prep_watch_start_least`
（`watchStart ver c ys b credits` ＋ `Candidate w lower h` ＋ `ys.length + 1 = h`）から
run に載せる。**新しい数学ではなく、履歴を運ぶ場を 1 つ足す仕事。**

## 2026-09-19 n137: run 形も watch 点に狭めた（同じ 1 定理で 2 本）

**全体 build 成功（EXIT=0、エラー 0、`sorry` ゼロ）。ラチェット更新済み・緑。公理は 6。
無条件 PAL は未完。§10.5 は未達。**

`ShiftPalAlongTrace.shiftPal_of_chainNotWatch`（n136）を `obligation_shiftPalAlongRun` にも
当てた。**同じ 1 つの定理が run 形と trace 形の両方を狭めた。**

| 旧 | 新（狭まった公理） |
|---|---|
| `obligation_shiftPalAlongRun` | `obligation_shiftPalAtWatchAlongRun`（`∀ wv, z.vm.chain = .watch wv →` を追加） |
| `obligation_shiftPalAtFreshChainAlongTrace` | `obligation_shiftPalAtFreshWatchAlongTrace`（同型） |

どちらも旧版は**定理になった**（`by_cases` で watch / 非 watch に割って、非 watch 側は空虚）。

### 現在の 6 本（実測）

    [propext, Classical.choice, Quot.sound,
     obligation_cycleOracle,                       -- CycleOracleMC3（found 経路）
     obligation_freshShiftAtShiftEntryAlongTrace,  -- trace 各 tick で H_freshShiftAtShiftEntry
     obligation_localRealization,                  -- H_realizeLIMW'（局所実現）
     obligation_readsShiftAlongTrace,              -- trace 各点で H_readsShift
     obligation_shiftPalAtFreshWatchAlongTrace,    -- watch 点で ShiftPal（trace 形）
     obligation_shiftPalAtWatchAlongRun]           -- watch 点で ShiftPal（run 形）

### 残る `ShiftPal` 2 本の中身（測定済み）

`periodOnly = true` 側は `CloseoutPackRun31.shiftPal_of_chainRound` が
`ChainRound`（`:204`、`periodOnly = true` を guard に持つ）から閉じている。
残るのは **`periodOnly = false` ＋ watch** の場合で、そこでは `shiftGuardVM` の分岐が
`singlePositive s.cycle = true` ではなく **`negative wch.margin = false`** になる。

到達可能性の確認: 誕生 watch は `phase = 0` だが、4 回の boundary event で `phase = 4` に
達し得る。その間 `periodOnly` は `beginShift` まで `false` のままなので、
**「新しく準備した chain の最初の shift」がこの場合**。空虚ではなく実質がある。

内容は「DP が見つけた周期が入力の本物の周期である」——n114 で探索側（`GalilDpCorrect`）は
無条件に証明済みと測定してあるので、新しい数学ではなく `margin` 側の `RoundScan` 相当を
立てる層の配線。**`ChainRound` の `periodOnly = false` 版（margin 基準）が次の仕事。**

## 2026-09-19 n136: `ShiftPal` は chain が watch でない限り**空虚**（lag も「found 半径正」も不要）

**全体 build 成功（EXIT=0、エラー 0、`sorry` ゼロ）。ラチェット更新済み・緑。公理は 6。
無条件 PAL は未完。§10.5 は未達。**

### 主定理（標準公理、`sorry` ゼロ）

    ShiftPalAlongTrace.shiftPal_of_chainNotWatch
      (hNotWatch : ∀ wv, s.chain ≠ ChainVM.watch wv) : ShiftPal centre place entry q first w s

**`CopyOrBack` も `CopyInv` も `LagPos` も「found 時の半径が正」も要らない。**

### なぜ lag が関係なかったか（n134/n135 の見立ての訂正）

`shiftGuardVM` は `w.machine.control.phase = 4` を要求する。
`GalilScaffoldChainConsume.State` のフィールド順は
`period, distance, boundary, last, phase, forward, broken`（`:15`）で、
`ChainStep.backDone` が置く `watchControl v = ⟨moveRight v, reset, reset, reset, 0, true, false⟩`
の **5 番目 `0` が `phase`**。つまり誕生 watch は `phase = 0`。

1 tick 後も 4 にならない:

* `Outer.queued` は machine を触らない → phase 0
* `Outer.immediate` は `consume` を通すが
  `phase := if boundaryEvent then advancePhase s.phase else s.phase` で
  `advancePhase 0 = ⟨min 4 1, _⟩ = 1`、不一致枝は `broken := true` で phase 不変
  （`CopyPhaseNoShift.consume_phase_ne_four`）
* `ChainMatched.breaks` の行き先は `.broken` で watch でない

`.idle` からは誕生しても `chainStart = .copy`、`.broken` からは `.broken`、
`.copy` からは `.copy`/`.back`——**どれも watch でない**。
支えは `CopyPhaseNoShift.tick_watch_phase_ne_four_of_notWatch`（構成子の形だけ）。

**n134 で `LagPos` を、n135 で「found 半径正」を要求すると測ったが、どちらも不要だった。**
一次情報（`watchControl` のフィールド順）を見て初めて分かった。
「壁に当たったら形式化のミスを疑う」がそのまま効いた。

### 公理の狭まり

`obligation_shiftPalAtFreshChainAlongTrace`（定理になった）
→ `obligation_shiftPalAtFreshWatchAlongTrace`（公理、**追加条件つき**）:

    ∀ wv : GalilScaffoldChainWatch.State, (st j).vm.chain = ChainVM.watch wv → ShiftPal …

本数は 6 のままだが、**中身は「chain が既に watch の点」だけに縮んだ**。
残るのは「準備し終えた周期が入力の本物の周期」という DP 正当性の帰結（n114 で
探索側は無条件に証明済みと測定）。

### 副産物: 「found 時の半径が正」の需要が 3 → 2 に減った

n135 で「1 本潰すと 3 箇所に効く」と書いた側条件のうち、
**`LagPos` 経由の 1 箇所は消えた**（`phase` で落ちるので lag が不要）。
残るのは `reachesWatchPhase_or_segEnd_at_foundBirth_canonical` と
`first_round` / `chain_life` の既存仮定。

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

# 現行の組み立て方針

更新: 2026-09-14。無条件の `PAL ∈ PEG` はまだ未完成。

**最新（2026-09-15、続き）：fresh shift → 任意回の再 shift → 終端 restart → 次 tick を実状態上で一気通貫。** `GalilScaffoldChainReadOrigin.lean` に追加：`shift_run_unique`/`chain_shift_unique`（決定性）、`Entry`（起点の再開入口不変量：OnlyScan/OnlyCredit/RadiusRep/machine=shifted/left=resumeLeft/center head 表現と位置）、`CompareRounds h s m s'`（一致周期 `OnlyMatchedRun` → cycleEnd＋右予測一致 → h 回の `ShiftRun`/`ChainShiftRun` 実行、の m ラウンド）、`rounds_origin`（Entry が保存され center/radius が m·h 進み shifts が m 増える帰納）、`rounds_restart`（末尾の左右一致・予測失敗枝で `Search.start` 入口条件）、`entry_of_only`（fresh `OnlyOrigin` ＋ shift 結果 ⇒ Entry）、`fresh_rounds_restart`（`scan_prediction_shift` の全前提から、ShiftRun/ChainShiftRun と「任意の m ラウンド＋終端一致 ⇒ center = 開始位置+(m+1)h、radius' = radius+1+m·h−h での restart 条件」）、`ReadOrigin.dispatch_match`、`read_terminal_dispatch_next_tick`（phase 前提・steps 前提なし版）、`rounds_dispatch_next_tick`（m ラウンド後の終端一致 → `dispatchOnlyMatch` → `restartInputTick` → 次 tick の scan/idle/restarts+1/clock/program/grow）。`scan_prediction_shift` の結論に `origin.center = position s.verifier`、`origin.radius = radius`、`4h ≤ distance (immediate t)` を輸出追加。全て標準公理のみ、`lake build PalPeg.GalilScaffoldChainReadOrigin` 8658 jobs 成功。未接続：周期途中の不一致（fallback 枝）、cycleEnd で左右不一致かつ予測不一致の枝、`CompareRounds` の各ラウンドの guard（右可用性・予測一致・length counter 正規性）を実 controller の tick から供給すること、実 restart の program.reset/lower alias/clock、物理 refinement、出力/締切、無条件 PAL。

### 分岐網羅（tick の全域性・決定性）の義務（2026-09-16、Opus 調査）

scan モードの `Tick` 構成子は `scan_wait`／`scan_count`／`scan_match`／`scan_shift`／`scan_fallback`／`restart`（`GalilScaffoldTop.lean:108–173`）。ガードの網羅は古典的に可能だが **`c.clock = 0` の scan 状態には構成子がない**（不変量 `1 ≤ clock` が必要；`tick_bounded` は上界のみ）。`compare_progress`（`TopBranches.lean:17`）／`compare_progress_concrete`（`TopGuards.lean:49`）は `galilFrame` 用で、`galilFrameS`（`compareFound`）版はない。

`backgroundS` の存在補題は無い。必要なもの：
- (a) `searchStep` の全域性：`idle/found/missed/wait/grow/double` は関数で全域；`lower/lowerHome/copy/home` は `PrepareControl.Tick`（`GalilScaffoldPrepareControl.lean:26–50`）が **`lowerHome`／`home` で左端に達すると tick が無い** ⇒ 到達可能状態の不変量「`(tapes 10).focus ≠ 4 → (tapes 10).left ≠ []`（tape 7 も同様）」が要る；`run` は `SafeQuanta`（`GalilScaffoldSearchRun.lean:138`）＝DP 命令の 64 個の実行が安全であること ⇒ `quantum64_safe`／`dp_quanta_safe`（l.109／221）は preload 初期機械からの走行にしか無いので「到達可能な DP 構成は preload 走行の接尾辞」の不変量が要る。
- (b) `ChainStep` の全域性（`TopChainVM.lean:49`）：`.watch` は `watch_tick_false`／`watch_tick_exists`（`TopWatch.lean:32/17`、`Good` 仮定）；`.copy`／`.back` には存在補題が無い ⇒ answer テープ不変量「copy 中は focus ∈ {8,4}、focus=8 → left ≠ [] ∧ read (left p) ≠ none、focus=4 → positive h ∧ period focus が `.plain`」が要る。
- 決定性：部品の一意性補題は揃っている（`searchStep_unique`、`chainTick_unique`、`watch_tick_unique`、`shift_run_unique`、`safe_quanta_unique`、`Prep.tick_unique` …）が **`Tick` レベルの決定性は無い**。障害：`Tick.restart` は scan 状態から `F.restart s s'` だけで発火し、`scan_wait`／`scan_count` と重なる（chain が broken でも background は成立）⇒ 副条件「chain が restart 条件を満たす broken でない」か、restart ガードの強化が要る；`beginShiftVM'`／`beginFallbackVM'`（`TopGuards.lean:36/39`）は `w`／`p` の存在量化で一意でない ⇒ `p` を固定した形が要る。
- 提案：`scan_tick_exists`（`hclk : 1 ≤ c.clock`、`hchain : ∀ a, ∃ z, chainAt a … s.chain z`、`hsearch : ∀ a, ∃ v, searchEffect P a s v` を仮定）を `backgroundS_exists`／`compare_progress_S`／`beginShift_exists`／`beginFallback_exists` から組む。

### 完全性（中心不変量）の証明計画（2026-09-16）

不変量（checkpoint＝scan・非 replay 状態で）：(1) `Leftmost raw (position right) (position center)`（`GalilLiveCentre.lean`）、(2) `SpanRep`（`length = 2·radius+1`、`GalilSpanCounter.lean`）、(3) **短周期なし** `∀ δ, 0 < δ → δ ≤ value lower → ¬ HasPeriod span (2δ)`（span = `(encoded raw)[C−k .. C+k]`）。

**修正（2026-09-16 深夜）：不変量 (3) の正しい形。** 「span に lower 以下の周期なし」を shift 直後の短い span（半径 k−h）に要求すると反例がある（例：周期 6 の回文 `abacab|abacaba` の末尾 7 文字 `abacaba` は周期 4 を持つ）。正しい不変量は **round の終端比較時（半径 k ≥ 2h、`Entry.size`）に「現在の chain の 2h 未満の周期が span に無い」（`NoBelow raw C k h`）**。
- 最初の終端比較：DP の最小性（`no_candidate_of_result`）＋Fine–Wilf（`no_short_period_of_minimal`）＋前史の「2·lower 以下の周期なし」で成立。
- 次の終端比較（同じ chain、中心 C+h、半径 k1 ≥ 2h）：S1 は周期 2h（検証済み）で長さ ≥ 4h+1、S1 の周期 p=2δ<2h があれば FW で周期 2g（g=gcd(δ,h)∣h）、S0 の末尾窓（長さ ≥ 2h）に制限され、2g∣2h なので S0 全体が周期 2g ⇒ S0 の最小性に矛盾（純粋補題 V：`noBelow_next`）。
- restart（周期の破れ、外側一致）：lower := h0。次の chain の span は破れ位置を含むので周期 2h0 を持たず、2h0 未満は旧 span の最小性で排除 ⇒ 「2·lower 以下の周期なし」が成立し、新 h1 > lower の最小性へ接続。

保存：
- 一致比較・idle 区間：`leftmost_match`／`leftmost_scanEvents`（サブエージェント A）。
- fallback：`leftmost_fallback`＋`span_covers`＋窓長＝`position (right R)`（サブエージェント B）；lower := 0 なので (3) は自明。
- chain shift（round の終端比較で C → C+h）：(a) 右半分 `[C+1, n+1]` の周期 2h は `watch_input_period`（検証器は `startBefore : position start ≤ center`、`endPosition = center+radius+1`）と予測一致 `hpred`；(b) 中心付近 `[C−4h, C]` の周期 2h は DP 候補（`Candidate`：反転 span の回文接頭辞 2h+1・4h+1 ⇒ `hasPeriod_of_isPal_take` で周期 2h）；(c) 回文の鏡映で左半分も周期 2h；(d) 重なり ≥ 2h の周期区間の和集合は周期 2h（要補題 `hasPeriod_union`）⇒ span 全体＋n+1 が周期 2h；(e) `palAt_shift_of_period`（サブエージェント C）で C+h は半径 k+1−h で生存；(f) (C, C+h) に生存中心なし：`no_centre_below_period`（C）＋最小周期性＝`GalilDpCorrect.Result` の「first 以上で最小の Candidate」＋不変量 (3)＋符号化語の周期は偶数（要補題 `encoded_period_even`：偶数添字は gap=2、奇数添字は文字）；(g) shift 後の (3)：新 span は旧 span の長さ ≥ 2·(2h) の回文接尾辞なので `Words.hasPeriod_minimal_of_suffix`（群補題）で短周期なしを継承。
- restart（周期の破れ、外側一致）：lower := h0；新 span は旧 span を含むので旧 span の周期性を制限で継承、2h0 は破れで除外 ⇒ (3) が lower = h0 で成立。
- 報告点：`leftmost_report`（`IsPal (raw.take k) ↔ C = k`）と `scan_output_complete`（C = k, r = k−1 ⇒ L が位置 1）で output=true。

### 実時間台帳の紙スケッチ（2026-09-16、Scala 経路で無条件に到達するために必要な証明義務）

正本は `docs/palindromes-in-peg/GALIL_CLOCK.md`（派生：q=64 で stage factor 10、match interval 256、predictability 3169、FIFO service 6338）と `SCA_GALIL.md`。Lean 側の較正は `GalilScaffoldTimingCost.delay_calibration`（K=63、M=2048）で、定数は粗いが同じ構造。無条件の `StructuredMachine`（固定 B）に落とすには次の義務を全部 Lean で閉じる必要がある。

1. **stage 締切**：第 1 stage の費用 ≤ max(r,1)+2r+2m+7+⌈(327m+224)/q⌉、後続 stage は ell/2 で置換、係数 K、M ≥ 24K。入口半径 ≤ 5r/3（Lean では仮定 `3·Rad ≤ 5·k` として上層に露出済み）。
2. **DP 発見と検証器の追いつき**：発見は半径 2h 以前、半周期複写 2h+2、M ≥ 8 で半径 4h 以前に追いつく（Lean：chain の一生は `credit/lag/margin` で会計、未接続部分あり）。
3. **Galil の move 不等式**：nonchain 不一致で C が δ 進むとき旧半径 k ≤ 4δ。`SCA_GALIL.md` 自身が「この実装のすべての fallback に適用できるなら」と留保。**Lean には存在しない**（`fallback_restarted` の最大性 `PalAt` はあるが δ の下界は未証明）。最大のリスク。
4. **fallback 費用**：copy/home/marker/rewind ≤ 5m+6、marked FPP ≤ ⌈(296m+190)/q⌉（`FPP_COST.md` の有限命令表の資源台帳）。Lean：`fpp_then_markEnd_S` 等は tick 数を陽に持つ（n+1+(|w|-1+1) など）ので、費用式への接続は可能だが未実施。
5. **replay**：1 place あたり ≤ 2M、FPP が選んだ回文の内側では不一致しない（Lean：`fallback_replay`／`replay_scan` で構造は証明済み、tick 数の上界は未接続）。
6. **中心不変量（完全性の核）**：報告時の暫定中心 C_i より左に未報告の回文中心はない、中心は単調非減少、予測利得 ≥ δ−2。**Lean 未着手**（出力の完全性そのもの）。
7. **telescoping**：busy 区間 j..i で Σd ≤ 2c(i−j)+c、FIFO rate 2c。純粋な算術で Lean 化は容易だが 1〜6 が前提。
8. **SCA ラッパー**：buffer/dispatcher を有限局所場として表現（`GalilVM` → 有限テープ機械への具体化＝旧経路の「差し込み」と同種の作業）。

`REALTIME_BUDGET = 2048`（`recognize`）は派生 service 6338 を下回るので、派生議論は 2048 を保証しない（`RealtimeGalil` は 6338 を使う）。予算実測プローブは `RealtimeGalil`（6338）で実行。

### 到達点の要約（2026-09-16、上層 `GalilScaffoldTop*`）

統合 VM `GalilVM` と関係フレーム `galilFrameS`（Scala `transition` の 1 tick：scan の background＝探索 step＋chain 効果、compare＝`compareFound`（探索 step・chain start・shift／fallback 入口）、他モードは各相の pull frame）の上で、次が標準公理のみで証明済み：
- **chain の一生**：`found_life`（found tick → 準備 → watch → 最初の shift → m 周の再 shift → 破れ比較 → restart 条件）、`life_restarted`（＋restart tick ⇒ `Restarted`）。
- **探索共走過程**：`searchStep`（grow／prepare／run／wait／double）、`search_first_stage`（`begin lower radius` からの実走行が第 1 stage で exit・DP `Result`）、`stage_prefix_mode`、`idle_segment_found_first`（found tick＝第 1 stage の終端か、区間内の非 found exit）。
- **主ループ**：`restarted_next_found`（restart 後 → 次の found 状態 `FoundReady`）、`found_to_found`（found → found の一周）。
- **fallback**：`scan_fallback_cycle_S`（不一致 → fallback → replayStart → scan）、`fallback_restarted`（`Restarted raw t 0 reset`、`PalAt`・窓内最大性）、`fallback_next_found`。
- **init**：`init_restarted`、`segment_mismatch_ready`。
仮定として残るもの：`Decodes P`（中心の復号）、`delay = 2048`、`3·Rad ≤ 5·k`（restart 半径と lower の関係）、found 時の半径正、fallback 窓長の偶数性。未対応：replay 中の found、探索の後段 stage（wait／double）・missed、空語、分岐網羅（各状態で次 tick の存在）と主ループの帰納、出力の完全性（中心の正しさ）、実時間入力供給、`StructuredMachine` 化と `SAccepts ↔ PAL`。

追記（2026-09-16 午前、並列バッチ 6）：`GalilRoundsLeftmost`（`rounds_leftmost`）、`GalilNoBelowFirst`、`GalilPrepLeast`。外注中 CC `life_minv`。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（2026-09-16 午前、並列バッチ 5）：`GalilPeriodNext`（`noBelow_next`）、`GalilPeriodSpan`、`GalilReadOriginPeriod`、`GalilCandidateWindow`、`GalilOriginPeriod`（`origin_periodOn_right`）。外注中：AA `rounds_leftmost`、BB `noBelow_first`。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（2026-09-16 深夜、並列バッチ 4）：`GalilScaffoldTopProgressS`（`scan_tick_exists`）、`GalilMinimalPeriod`（`no_short_period_of_minimal`、`result_least`）。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（2026-09-16 深夜、並列バッチ 3）：`GalilLiveCentreCycle`（`cycle_fallback_minv`）、`GalilLiveCentreSegs`、`GalilFallbackCost`（`fallback_ticks_le` ≤ 1588(ℓ+1)+836）。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（2026-09-16、並列バッチ 2）：`GalilLiveCentreMismatch`、`GalilSegmentCount`、`GalilShortPeriod`、`GalilCandidatePeriod`、`GalilLiveCentreShift`（`leftmost_shift`）。外注中：L／Q／N／S／T。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（2026-09-16、`Live` の厳密化と周期区間の和集合）：`Live` に左端 ≥ 1 を追加、`GalilPeriodUnion`（Opus D）。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（2026-09-16、完全性の機械側）：`GalilLiveCentreSeg`／`GalilLiveCentreFallback`／`GalilPeriodCentre`（Opus 並列）、`GalilSpanCounter`、`GalilLiveCentreReplay`（`MInv`）。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（2026-09-16、完全性の核＝最左の生存中心）：新モジュール `GalilLiveCentre.lean`（`Live`、`Leftmost`、`leftmost_match`、`leftmost_fallback`、`leftmost_report`：台帳義務 6 の数学側）。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（2026-09-16、予算プローブの実測結果）：`RealtimeGalil`（service 6338）で 42 語・長さ最大 201・全接頭辞で見逃し 0。有限テストであり任意長の証明ではない。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（2026-09-16、予測可能性 ⇒ 実時間の抽象定理）：新モジュール `GalilPredictability.lean`（`backlog`、`work`、`backlog_zero_of_bounds`、`work_bound_of_centres`、`realtime_of_predictable`、`wrapper_exact`：台帳義務 7 の Lean 化）。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（2026-09-16、Galil の move 補題の組合せ論部分）：新モジュール `GalilMoveLemma.lean`（`hasPeriod_of_isPal_take`、`window_hasPeriod_of_chosen`、`isPal_take_of_hasPeriod`、`chosenRadius_ge_of_period`：台帳義務 3 の数学側半分と、fallback が周期の半分を超えて中心を進めないこと；`fallback_window_period`、`galil_move_of_contract`：探索契約「半径の半分以下の周期なし」の下で k ≤ 4δ）。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（2026-09-16、経路比較・要判断）：旧経路（直接 SCA、`pal_SAccepts_iff_embed` は HEAD に存在、実時間予算の数学は証明済み、具体 Prog の差し込みが未完）と現行経路（Scala 忠実、soundness は主ループ 2 周まで、実時間台帳は仕様側でも未検証）のどちらで無条件を狙うかは要判断。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（2026-09-16、主ループ 2 周の全状態で出力健全）：新モジュール `GalilScaffoldTopOutputCycle.lean`（`cycle_found_stepsAll`、`cycle_fallback_stepsAll`：Restarted → Restarted の 2 周で全状態 `SoundScanNR`）。soundness 側は分岐網羅を除いて閉じた。**実時間の注意**：Scala 正本 `SCA_GALIL.md` は自身を「certified real-time recognizer ではない」「仕事量の台帳は未検証」と明記。固定 B の `StructuredMachine` に落とすには仕事量上界の証明が必要で、これは仕様側でも未確立。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: 予算 2048 の実測結果を見て経路判断、出力完全性、分岐網羅）。

追記（2026-09-16、init と restart tick の健全性）：新モジュール `GalilScaffoldTopOutputInit.lean`（`init_stepsAll`、`stepsAll_keep_tick`、`outputRel_position_one`）。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: 主ループ 1 周の合成と帰納）。

追記（2026-09-16、fallback 一周の全状態で出力健全）：新モジュール `GalilScaffoldTopFallbackRestartAll.lean`（`SoundScanNR`、`fallback_restarted_All`、`fallback_restarted_soundNR`）。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: init tick の健全性、chain 一生と restart tick の `SoundScanNR` 化、主ループの `StepsAll` 接続）。

追記（2026-09-16、fallback 一周を状態述語つき走行に）：新モジュール `GalilScaffoldTopFallbackAll.lean`（`NoScan`、`stepsAll_transfer_*`、`fallback_to_scan_All`、`scan_fallback_cycle_All`：不一致比較から scan 再入まで任意の述語 Q を運ぶ、r=0 の refresh 節輸出）。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: replaying=false 条件つき `SoundScanNR` で fallback→Restarted の終端 Q を `fallback_restarted` の不変量から供給、init、主ループ接続）。

追記（2026-09-16、chain の一生の全状態で出力健全）：新モジュール `GalilScaffoldTopOutputLifeAll.lean`（`first_shift_stepsAll`、`life_stepsAll`：found tick から破れ比較まで全状態で `SoundScan`）。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: fallback 一周と init の `StepsAll`、主ループ接続、フロンティア基準の出力関係、出力完全性、実時間、`StructuredMachine`、`SAccepts ↔ PAL`）。

追記（2026-09-16、再 shift 周回の全状態で出力健全）：新モジュール `GalilScaffoldTopOutputRound.lean`（`SoundScan`、`stepsAll_transfer_generic`、`shift_phase_stepsAll_S`、`round_stepsAll`、`rounds_stepsAll`）。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: found tick → 準備 → watch → 最初の shift → 周回 → 破れ比較 → restart の全状態版 `life_stepsAll`、fallback 一周、init）。

追記（2026-09-16、refresh 点と全状態の出力健全性）：新モジュール `GalilScaffoldTopOutputLife.lean`（`rounds_output`、`outputRel_matched_refresh`、`entry_scanInvariant`）と `GalilScaffoldTopOutputTrace.lean`（`StepsAll`、`SoundOut`、`watchSegE_stepsAll`／`scanSeg_stepsAll`／`watchSeg_stepsAll`：区間の全状態で出力健全）。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: chain の一生・fallback 一周・init を `StepsAll` で接続、フロンティア基準の出力関係、出力完全性、分岐網羅、実時間、`StructuredMachine`、`SAccepts ↔ PAL`）。

追記（2026-09-16、出力の健全性）：新モジュール `GalilScaffoldTopOutputSound.lean`（`OutputRel`、`watchSegE_output`／`scanSeg_output`／`watchSeg_output`：区間に沿った出力健全性の保存、`report_sound`）。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: 区間外 refresh 点の供給、出力完全性、分岐網羅、実時間、`StructuredMachine`、`SAccepts ↔ PAL`）。

追記（2026-09-16、init と不一致前提の供給）：新モジュール `GalilScaffoldTopInitRestart.lean`（`watchSegE_remaining`、`initialHead`、`init_restarted`：init tick 後は `Restarted (a :: rest) t 0 reset`、`segment_mismatch_ready`）。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: 分岐網羅と主ループの帰納、出力完全性、実時間、`StructuredMachine`、`SAccepts ↔ PAL`）。

追記（2026-09-16、不一致 → 次の found）：新モジュール `GalilScaffoldTopFallbackFound.lean`（`fallback_next_found`：不一致→fallback 一周→chain idle 区間→found 比較で `FoundReady`）。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: init からの接続）。

追記（2026-09-16、fallback → restart 状態）：`Restarted` 緩和、`restarted_next_found`／`found_to_found` に found 時半径正の仮定、新モジュール `GalilScaffoldTopFallbackRestart.lean`（`fallback_restarted`：不一致→fallback 一周後の状態は `Restarted raw t 0 reset`、中心は右ヘッドの r 個下、`PalAt` と窓内最大性）。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: fallback→found の合成、init 初期不変量）。

追記（同日、replay 中の tick と区間の一般化）：`replayDec`、`scan_match_S'`／`scan_match_idle_S'`、`WatchSegE.countR`／`matchIdleR` と各補題の更新。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: fallback 後の replay 区間と `ScanInvariant` 再構成、init 初期不変量；replay 中の found は未対応）。

追記（同日、chain idle の不一致 → fallback 一周）：新モジュール `GalilScaffoldTopFallbackCycleS.lean`（`scan_fallback_cycle_S`：不一致比較→fallback→replayStart→scan を `galilFrameS` で）。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: replay 区間、init 初期不変量、fallback 後の `ScanInvariant` と replay の一致保証）。

追記（同日、fallback 経路の `galilFrameS` 化）：新モジュール `GalilScaffoldTopFallbackS.lean`（`steps_transfer_*_S`、`copy_home_start_S`…`fallback_to_scan_S`）。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: `scan_fallback_S`、replay 区間、init からの走査不変量）。

追記（同日、replay の減算＝忠実性修正）：`galilFrame.matchedPlace` に replay の減算を反映。全体 build 成功・標準公理のみ・無条件 PAL は未完。未解決の下層前提：`3·Rad ≤ 5·k`、found 時の半径 `0 < r0`（replay 後の半径 0）。

追記（同日、主ループの一周）：新モジュール `GalilScaffoldTopFoundLoop.lean`（`found_to_found`：found 状態から次の found 状態まで `Steps` ∧ `FoundReady` 再成立）。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: init／replay から最初の found へ、後段 stage、missed／fallback、出力完全性、実時間、`StructuredMachine`、`SAccepts ↔ PAL`）。

追記（同日、chain の一生 → restart 直後）：新モジュール `GalilScaffoldTopLifeRestart.lean`（`watchSeg_counters`、`life_restarted`：found 状態から restart 直後まで `Steps` ∧ `Restarted`）。`life_restarted`＋`restarted_next_found` で found→次の found（第 1 stage）が閉じた。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: 一周の合成、init／replay から最初の found へ、他枝、出力完全性、実時間、`StructuredMachine`、`SAccepts ↔ PAL`）。

追記（同日、restart 後 → 次の found 状態）：新モジュール `GalilScaffoldTopReadyFound.lean`（`Decodes`、`FoundReady`、`Restarted`、`restarted_next_found`）。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: `life_restarted`（found_life＋restart tick ⇒ `Restarted`）と一周の合成）。

追記（同日、中心・ヘッド・counter の輸送）：`chain_life`／`found_life` に `Entry` を輸出、新モジュール `GalilScaffoldTopCentre.lean`（`represents_decompose`、`rounds_centerRep`）、`GalilScaffoldTopSegmentHeads.lean`（`watchSegE_heads`、`scanSeg_counters`）、`GalilScaffoldTopRoundsCounters.lean`（`rounds_counters`）。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: `FoundReady` 不変量と found→found の一周定理；`3*rad ≤ 5*k` は未証明の前提）。

追記（同日、found tick の特定）：新モジュール `GalilScaffoldTopIdleFound.lean`（`idle_segment_found_first`：chain idle 区間の次の tick で found なら、それが第 1 stage の終端（DP `Result`・直前 run・Candidate）か、第 1 stage が区間内で非 found の exit で終わっていたか）。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: restart tick 出口との接続、`found_life` への合成、後段 stage、missed/fallback）。

追記（同日、chain idle の比較 tick と区間の事実）：`scan_match_idle_S`、`WatchSegE.matchIdle`、`watchSegE_steps`、新モジュール `GalilScaffoldTopSegmentFacts.lean`（`watchSegE_center`／`clock`、`searchRun_pad`、`watchSegE_search_not_found`）。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: restart 出口→found tick 特定→`found_life` 接続）。

追記（同日、第 1 stage の構造化と接頭辞）：`search_first_stage` を各相の `SearchRun` を輸出する形に構造化。新モジュール `GalilScaffoldTopStagePrefix.lean`（`searchRun_unique` 等）と `GalilScaffoldTopFirstStagePrefix.lean`（`stage_prefix_mode`：stage の真の接頭辞の後は found でない、最後の直前は run）。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: restart 出口→found tick の特定→`found_life` 接続）。

追記（同日、restart 後の第 1 stage の実走行）：新モジュール `GalilScaffoldTopFirstStage.lean`（`search_first_stage`：`begin lower radius` からの実走行が `used` の終端で exit mode・DP `Result`・found なら Candidate）。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: restart tick の出口から前提供給、found tick での chain start と `found_life` の接続）。

追記（同日、探索段階の同一視）：新モジュール `GalilScaffoldTopSearchStage.lean`（`searchRun_growing`／`searchRun_paced`／`searchRun_prepared`／`searchRun_quanta`：実走行 `SearchRun` が下層の `PacedGrowing`／`PacedPrepared`／`SafeQuanta` を辿る）。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: `first_stage_chain_run` との合成による restart 後第 1 stage の上層定理）。

追記（同日、background での chain start）：`backgroundS` の chain 効果を `chainAt false` に（idle かつ found なら任意の scan tick で `chainStart`）、`backgroundS_chainTick`／`backgroundS_idle`、`watchSeg(E)_events` に非 idle 前提。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（同日、chain idle 区間の探索の駆動）：新モジュール `GalilScaffoldTopSearchRun.lean`（`SearchRun`、`watchSegE_searchRun`、`watchSegE_advances`）。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: `SearchRun` と下層の段階 run の同一視、restart→found の一本化）。

追記（同日、探索共走過程の上層統合）：`searchStep`（mode 別の探索 1 step＋advance）、`searchEffect`（chain idle のときだけ探索が進む）、`backgroundS` を定義し `galilFrameS` の compare／background に組み込み。下流の仮定を差し替え。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: chain idle 区間の探索段階を `searchStep` 列から復元して `first_stage_chain_run`／`restart_first_stage` に接続、restart→found の一本化）。

追記（同日、init／replay／fallback の忠実性修正）：`initVM entry`／`replayStartVM entry`／`beginFallbackVM` に chain idle・search 再始動（`begin`）・`dp` reset・search idle を追加、`galilShared … entry`。全体 build 成功・標準公理のみ・無条件 PAL は未完。残りの主要作業：探索共走過程の上層統合（`searchTick` を mode 別に `PrepareControl.Tick`／`PacedGrowing`／`Double.Run`／`WaitInterrupt.Run`／run quantum に対応づけ）、restart→`SearchSeg`→found／missed／fallback、init／replay 後の `ScanInv`、出力の完全性、実時間入力供給、`StructuredMachine` 化と `SAccepts ↔ PAL`。

追記（同日、found tick からの一本化）：新モジュール `GalilScaffoldTopFoundLife.lean`（`found_life`：found 状態から準備期間・watch 期間・最初の shift・m ラウンド・破れ比較まで `galilFrameS` の `Steps` と restart 条件）。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: restart 以降、探索 idle 期間、found 前の `ScanInv` 確立、実時間供給、`StructuredMachine` 化、`SAccepts ↔ PAL`）。

追記（同日、単一フレームへの統合）：`galilFrameS.compare := compareFound`（chain start 込み）、`galilFrameF` 廃止、`centre`/`place` を `Shared` のフィールドに。S 系補題は「chain が idle でない」前提つき。found tick から `chain_life` まで同一フレームの `Steps`。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（同日、chain start と準備期間、忠実性修正）：`compareFound`／`found_start_match` の answer tape を quantum 後の `vq.dp` に修正（Scala は quantum 後に `chain.start()`）。`found_shift_entry`／`first_round`／`chain_life` の h・ys・b を ∀ 入力に変更。新モジュール `GalilScaffoldTopWatchSegE.lean`（`WatchSegE`、`watchSegE_append`／`trans`／`events`、`prep_watch_start`：start tick 後の準備期間 `bs ++ dm :: cs` の終端で chain は `watchStart`）。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: found tick→準備→`chain_life` の一本化、初期条件供給、restart 以降、実時間供給、`StructuredMachine` 化、`SAccepts ↔ PAL`）。

追記（同日、chain 一生分の合成）：新モジュール `GalilScaffoldTopChainLife.lean`（ルート import 済み）：`chain_life`（`first_round`＋`rounds_lift`＋`rounds_break` の合成：found 直後から broken 状態までの `Steps` と、`restartVM` の前提となる restart 条件）。文中の `let` は「unknown free variable」を起こすので展開して書く。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: chain start の上層供給、restart 以降、実時間供給、`StructuredMachine` 化、`SAccepts ↔ PAL`）。

追記（同日、最初の一周）：新モジュール `GalilScaffoldTopWatchSeg.lean`（`WatchSeg`、`watchSeg_steps`、`watchSeg_events`）と `GalilScaffoldTopFirstRound.lean`（`terminal_shift_steps`、`first_round`：found 側前提＋watch 期間＋終端不一致＋shift ⇒ `Steps` ∧ 終状態 watching・lag 零・periodOnly ∧ `Entry`）。両方ルート import 済み。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: `first_round`→`rounds_lift`→`rounds_break` の合成、chain start の上層供給、restart 後、実時間供給、`StructuredMachine` 化、`SAccepts ↔ PAL`）。

追記（同日、found からの `Entry`）：`GalilScaffoldTopFreshEntry.lean` に `found_shift_entry`（`found_rounds_restart` の前提＋実機の `ChainShiftRun` ⇒ shift 後状態に `Entry raw o`、`o.interior.length+1 = h`、`o.shifts = 0`）。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（同日、最初の shift の `Entry`）：新モジュール `GalilScaffoldTopFreshEntry.lean`（ルート import 済み）：`fresh_shift_entry`（`scan_prediction_shift` の前提＋実機の `ChainShiftRun` ⇒ shift 後状態に `Entry raw o`、`o.interior.length+1 = xs.length+1`、`o.shifts = 0`）。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: 上層状態から前提を供給する「最初の一周」補題、restart 後の探索と found tick 供給、実時間供給、`StructuredMachine` 化、`SAccepts ↔ PAL`）。

追記（同日、破れ枝）：新モジュール `GalilScaffoldTopRoundBreak.lean`（ルート import 済み）：`chainTick_true_broken`、`afterCompare_only'`、`rounds_break`（`Rounds m`＋区間＋破れる終端比較 ⇒ `Steps` ∧ 下層 `rounds_restart` の結論が実状態で成立＝`restartVM` の前提）。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: `Entry` の初期成立、restart 後の探索と found tick 供給、実時間供給、`StructuredMachine` 化、`SAccepts ↔ PAL`）。

追記（同日、m ラウンドの連結）：shift 出口の output を `refresh` 仮定つきの明示 `o` に変更（`shift_steps_S`／`shift_phase_S`／`round_next`）。新モジュール `GalilScaffoldTopRounds.lean`（ルート import 済み）：`chain_shift_lag`、`compareRounds_append`、`Rounds`（m 回の一周）、`rounds_lift`（`Steps` ∧ `CompareRounds h … m …`、終状態も watching・lag 零・periodOnly）。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: `Entry` の初期成立、破れ枝 `rounds_restart`、found tick 供給、実時間供給、`StructuredMachine` 化、`SAccepts ↔ PAL`）。

追記（同日、一周＝`CompareRounds` の 1 段）：`beginShiftVM` の radius 二重加算を除去。新モジュール `GalilScaffoldTopRoundS.lean`（ルート import 済み）：`shift_phase_S`、`round_next`（コントローラの一周 ⇒ `galilFrameS` の `Steps` ∧ `CompareRounds h … 1 …`）。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: m ラウンド連結と `Entry` 保存、破れ枝、found tick 供給、実時間供給、`StructuredMachine` 化、`SAccepts ↔ PAL`）。

追記（同日、消費のタイミングの修正）：`scanFrame.compare` の chain 効果を一致ビットで `ChainTick (decide …)` に、`beginShiftVM` で `immediate`、guard は `singlePositive cycle`。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（同日、比較結果の分岐と二重計上の修正）：`afterCompare`（一致：radius+1・cycle−1（periodOnly）・length+2）と `afterMismatch`（radius+1）に分岐、`shiftGuardVM` の periodOnly 側は減算後 `zero cycle`、`beginShiftVM` の二重 `immediate` を除去（`CompareRounds.next` の `hchain` と同形に）。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（同日、一致比較列と走査区間）：新モジュール `GalilScaffoldTopMatchedSeq.lean`・`GalilScaffoldTopScanSeg.lean`（ルート import 済み）：`MatchedSeq`/`matchedSeq_only`、`ScanSeg`/`scanSeg_steps`/`scanSeg_only`（コントローラの走査区間 ⇒ `Steps` と `OnlyMatchedRun`）。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: `CompareRounds.next` への対応づけと `Entry` の保存）。

追記（同日、only-compare 射影）：新モジュール `GalilScaffoldTopOnly.lean`（ルート import 済み）：`toOnly`、`chainTick_true_immediate`、`chainTick_false_idle`、`afterCompare_only`（一致比較＝`onlyCompareNext`）。`MatchedSeq`/`matchedSeq_only` はドラフト中。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（同日、periodOnly と cycle の反映）：`GalilVM.periodOnly`、`cycleAfter`、`shiftGuardVM` の Scala 準拠化、`beginShiftVM` の `periodOnly := true`。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: 走査＋shift 一周を `CompareRounds.next` に対応づけ `rounds_origin` で `Entry` を一周保存）。

追記（同日、一致比較での不変条件保存）：`radiusAfter s := inc s.radius` に修正（`advanceMatch` も radius を増やす）。新モジュール `GalilScaffoldTopInvStep.lean`（ルート import 済み）：`afterCompare`、`scanInv_compare_matched`。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（同日、比較 tick の radius 更新）：`compareVM`/`compareFound` に `radiusAfter s`（search 活性∧chain idle なら不変、さもなくば inc）を追加。全体 build 成功・標準公理のみ・無条件 PAL は未完。設計メモ：`ScanInv.radius` は search 活性中の一致で崩れるので、「radius ＋ search 開始以降の一致数 ＝ 走査半径」型の不変条件に改める（search の debt/span 対応を要確認）。

追記（同日、shift 一周の接続）：新モジュール `GalilScaffoldTopShiftRound.lean`（ルート import 済み）：`shift_round`（下層の `ChainShiftRun` から scan→shift→scan 一周）。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: 比較 tick の radius 更新の追加と `ScanInv` の保存）。

追記（同日、scan モード不変条件と shift の消尽）：新モジュール `GalilScaffoldTopInvariant.lean`（ルート import 済み）：`ScanInv`、`shift_run_remaining`、`chain_shift_exhausts`。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（同日、入口の具体化）：新モジュール `GalilScaffoldTopGuards.lean`（ルート import 済み）：`shiftGuardVM`、`periodLength`、`beginShiftVM'`、`beginFallbackVM'`、`compare_progress_concrete`。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（同日、watch 期間から shift guard）：新モジュール `GalilScaffoldTopWatchGuard.lean`（ルート import 済み）：`watch_run_unique`、`watch_period_guard`（watch 期間の `GRun` → `freshShiftGuard`・距離・`ScanInvariant`）。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（同日、watch 期間の供給）：新モジュール `GalilScaffoldTopWatchSupply.lean`（ルート import 済み）：`watch_grun_supply`（watch 期間の `GRun` → ws・`Watch.Run`・`VerifyRun`・lag・`ScanEvents`）。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（同日、watch 期間の chain tick と検証器実行）：新モジュール `GalilScaffoldTopWatchRun.lean`（ルート import 済み）：`broken_stays`、`chainTicks_watch_run`、`verify_run_append`、`watch_run_verify`（`Watch.Run` → `VerifyRun.Run … (watchConsumes bs lag)`、lag は `watchLag`）。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: watch 期間の `GRun` を `watch_shift_supply` に接続）。

追記（同日、prep 期間の連結）：新モジュール `GalilScaffoldTopPrep.lean`（ルート import 済み）：`prep_to_watch`（found 後の `GRun` のイベント列が `bs ++ dm :: cs` なら chain は `watchStart …` に到達）。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: watch 期間の `GRun` → `watch_shift_supply` 接続、guard の具体化、大域不変条件、実時間供給、`StructuredMachine` 化、`SAccepts ↔ PAL`）。

追記（同日、chain tick の決定性）：新モジュール `GalilScaffoldTopChainUnique.lean`（ルート import 済み）：`chainStep_unique`、`chainMatched_unique`、`chainTick_unique`、`chainTicks_unique`（破れと `Outer true` の排他性を含む）。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（同日、一般走査実行のイベント抽出）：新モジュール `GalilScaffoldTopGeneralEvents.lean`（ルート import 済み）：`grun_events`（`GRun` → `ScanEvents` ∧ `ChainTicks`）。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（同日、任意の chain での走査実行）：新モジュール `GalilScaffoldTopGeneralRun.lean`（ルート import 済み）：`GScan`/`GTick`/`GRun`（`JointTick` の `ChainVM` 一般化）、`grun_lift`。イベントは tick 単位（`ScanEvents`/`prepEvents` と同じ粒度）。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（同日、found → chain.start の比較）：新モジュール `GalilScaffoldTopFound.lean`（ルート import 済み）：`chainAt`、`compareFound`、`galilFrameF`、`found_start_match`。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（同日、Broken 後の restart tick）：新モジュール `GalilScaffoldTopRestart.lean`（ルート import 済み）：`restartVM entry`、`restart_tick`。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（同日、統合 VM の chain 載せ替え）：`GalilVM`/`ScanVM`/`ShiftVM` の `watch` を `chain : ChainVM` に置換（定義は新モジュール `GalilScaffoldTopChainVM.lean`、`chainTick_of_watch_*`/`chainTick_of_break` で `Watch.Tick`/破れと一致）。`Top.Tick` に `restart` 構成子と `Frame.restart`/`Shared.restart` を追加し全モジュール更新。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: `restartVM` の tick、found → `chainStart` の background 組み込み、大域不変条件、実時間供給、一本化、`SAccepts ↔ PAL`）。

追記（同日、chain 入口＝`watchStart`）：新モジュール `GalilScaffoldTopChainEntry.lean`（ルート import 済み）：`run_lag_ofNat`、`found_to_watchStart`（found → 開始 credit sm → copy bs → 終端 credit dm → back cs で `watchStart ver c ys b (run (start radius) (prepEvents sm dm bs cs))` に到達）。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: `ChainVM` の `GalilVM` 載せ替え、破れ後 restart、大域不変条件、実時間供給、一本化、`SAccepts ↔ PAL`）。

追記（同日、prep 中の走査クレジット）：`ChainStep.watchStep` を `Internal` に、`ChainMatched.watch` を `Outer true` に分離。新モジュール `GalilScaffoldTopChainCredits.lean`（ルート import 済み）：`ChainTick`/`ChainTicks`、`creditsOf`、`step_copy`/`step_idle`、`copy_ticks`・`back_ticks`（`prepEvents` の copy/back 成分が `ChainVM` の tick 列に対応）。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: `found_to_watchStart`（`GalilScaffoldTopChainEntry.lean` ドラフト中、未 import）、`ChainVM` の `GalilVM` への載せ替え、restart、大域不変条件、実時間供給、一本化、`SAccepts ↔ PAL`）。

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

追記（同日、破れ枝）：`GalilScaffoldChainFallback.lean` に統合 tick の「破れ」枝 `JointBreak`（clock=1・右ヘッド可・走査側一致・lag 零・検証器 consume で不一致）、`joint_break_facts`、`credits_margin_canonical`、`joint_break_restart`（`joint_shift_supply` + `shift_ready` の freshShiftGuard から、破れ直後の restart 条件〈broken・lag 零・margin 非負・last 正・last canonical・成長〉）を sorry なしで証明。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: 出力完全性、`Main.pal_in_peg_of_structured` への最終合成）。

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

最新：OnlyOrigin.reshift_after_matchesで入口→継続実行→cycleEndから回数/実半径R+h/Credit/再shift後PalAtを導出。全体build9121 jobs成功/exit 0・標準公理のみ。実再shift構成/次起点/全PALは未完。

最新：OnlyOrigin.reshift_palindromeで実終端比較/連結Traceから右周期・終点を内部導出し再shift後PalAt(c+2h,R+1)を証明。全体build9121 jobs成功/exit 0・標準公理のみ。現在scan同期/実再shift/新起点/全PALは未完。

最新：OnlyOrigin.joined_input_periodで旧centerから現在verifierまでの実入力2h周期をshift前後の同じ成功履歴から導出。全体build9121 jobs成功/exit 0・標準公理のみ。再shift座標/PalAt接続・新起点/全PALは未完。

最新：OnlyOrigin.joined_readsでshift前後の実read列を連結し元readyの成功列へ戻す。全体build9121 jobs成功/exit 0・標準公理のみ。列周期→入力右周期→再shift回文性/全PALは未完。

最新：reshift_from_rightで旧回文から短回文を継承し再shift後PalAt(c+2h,R+1)を導出。新DP Candidate不要。全体build9121 jobs成功/exit 0・標準公理のみ。実履歴から右周期/現在座標の供給・全PALは未完。

最新：OnlyOrigin.reshift_compareが最後の実記号を含むTrace/LeftMovesと長さ2hを内部構成。全体build9121 jobs成功/exit 0・標準公理のみ。再shift新PalAt/周期窓/OnlyOrigin更新・全PALは未完。

最新：OnlyOrigin.reshift_compareでcycleEnd＋実右予測一致から実左右不一致/Good/合法consume/brokenfalseを同じ履歴で導出。全体build9121 jobs成功/exit 0・標準公理のみ。再shift後scan/周期/guard全体/全PALは未完。

最新：reshift_only_creditでcycleEnd時のmatched.inc→cycle reset→同じ再shiftからOnlyCreditを保存。比較前fresh margin非負は不要。全体build9121 jobs成功/exit 0・標準公理のみ。再shiftのscan/周期/起点更新・全PALは未完。

最新：terminal_dispatch_restartをterminal_dispatch_next_tickへ置換し、終端一致→次tick到着/restart/時計を合成。全体build9121 jobs成功/exit 0・標準公理のみ。全mode/出力/到達性/他分岐/全PALは未完。

最新：restartInputTickでOption到着→到着後headからScala可用性計算→restart→同tick時計を統合、restart_input_tickでscan/検索状態保存を検証。全体build9121 jobs成功/exit 0・標準公理のみ。全mode/出力/全head/他分岐/全PALは未完。

最新：restartScanTick/restart_scan_tickでbackground restart後の同tick scan時計を接続。delay>1なら比較なし、可用ならdelay−1・不可ならdelay。全体build9121 jobs成功/exit 0・標準公理のみ。実availability/到着込み統合/全controller/全PALは未完。

最新：OnlyRestartReady.arrival/restart_after_arrivalで次tick入力到着による全保持head更新と拡張raw上scan/restart成功を接続。全体build9121 jobs成功/exit 0・標準公理のみ。背景/時計/全controller/他分岐/全PALは未完。

最新：terminal_dispatch_restartで固定起点/履歴→guard付き終端一致dispatch→restart成功とscan/検索更新を一括合成。全体build9121 jobs成功/exit 0・標準公理のみ。次tick到着/背景時計interleave・到達性・他分岐・全PALは未完。

最新：dispatchOnlyMatchでcaught only一致枝guardを実検査、dispatch_only_matchで固定起点の履歴からcheckPair/lag/cycle条件を供給。全体build9121 jobs成功/exit 0・標準公理のみ。全背景tick/他分岐/到達性/全PALは未完。

最新：matchedRestartState/restart_after_matchで同じ比較後brokenからchainModeを計算してrestartへ接続。全体build9121 jobs成功/exit 0・標準公理のみ。有効枝dispatch/背景tick到着・時計/全controller/全PALは未完。

最新：RestartState/restart/restart_readyでOnlyRestartReady＋chain broken→検索start/Idle/restarts++/clock resetを局所射影上で統合。全体build9121 jobs成功/exit 0・標準公理のみ。全controllerのmode対応/背景tick/後続検索/他分岐/全PALは未完。

最新：history_terminal_canonicalをrestart契約へ合成し、start_searchのlast Canonical独立前提を削除。全体build9121 jobs成功/exit 0・標準公理のみ。外側restart統合/到達性/他分岐/全PALは未完。

最新：OnlyRestartReady.start_searchで終端last/radius→検索reset/start更新を接続。lower非負にはlast Canonicalを明示要求（履歴からの供給が次）。全体build9121 jobs成功/exit 0・標準公理のみ。外側restart/全PALは未完。

最新：SearchState/startSearch/startSearch_positiveでraw program reset・lower・既存scheduler beginを統合し、空テープ対応/heap保存/grow/work/debt条件を検証。全体build9121 jobs成功/exit 0・標準公理のみ。OnlyRestartReady→外側restart更新/physical alias/全controller/全PALは未完。

最新：RawTick.reset/reset_represents/reset_heapでprogram.resetを共有heap保存・private roots破棄・pc開始/done=trueとしてモデル化し空テープ対応を証明。全体build9121 jobs成功/exit 0・標準公理のみ。検索begin/lower alias/chain Idle/clockとの実restart合成とcircuit refinement、全PALは未完。

最新：scan_prediction_shiftの入口収支/正規形を直接仮定せず、同じ準備Credits.run終点のlag/margin等式から内部導出。全体build9121 jobs成功/exit 0・標準公理のみ。準備イベント/controller対応と成功watch等の到達性、全PALは未完。

最新：scan_prediction_shiftの比較時margin正規形/非負を入口CanonicalStateと準備balance=4hから同じRunで導出。全体build9121 jobs成功/exit 0・標準公理のみ。準備終点との同一性/成功watch/他分岐/実restart/全PALは未完。

最新：scan_prediction_shiftの独立半径下界hsizeを比較前phase4へ置換し、同じwatch収支から内部導出。restart継続契約の追加phase条件も不要化。全体build9121 jobs成功/exit 0・標準公理のみ。入口到達性/他分岐/実restart/全PALは未完。

最新：watch_phase_distanceでready成功watchのphase4→distance≥4hを証明。scan_prediction_shiftのrestart継続契約の距離仮定をphase guardへ置換。全体build9121 jobs成功/exit 0・標準公理のみ。入口到達性/実restart/他分岐/全PALは未完。

最新：scan_prediction_shiftが同じ生成入口からのOnlyMatchedRun→終端一致→OnlyRestartReady契約も返す。only_matched_restartへ直接合成済み。全体build9121 jobs成功/exit 0・標準公理のみ。距離guard/入口到達性/他分岐/実restart/全PALは未完。

最新：scan_prediction_shiftが実左右不一致を受け同じwatch/shift終点のOnlyOriginを構成するよう更新。入口不変条件とoriginの同一性を同時に返す。全体build9121 jobs成功/exit 0・標準公理のみ。only_matched_restart直接合成、全controller前提供給、全PALは未完。

最新：scan_prediction_shiftを強化（署名変更）。counter正規形・fresh margin条件から、予測比較→同じshift→OnlyScan/Credit/RadiusRep/空履歴/center存在まで返す。全体build9121 jobs成功/exit 0・標準公理のみ。OnlyOrigin/restart集約、全controllerからの前提供給、全PALは未完。

最新：shift_to_only_initializedで終了scanを独立前提にせずshift生成から供給し、比較入口一式を構成。全体build9121 jobs成功/exit 0・標準公理のみ。新PalAt/caught watch等は前提で、予測比較起点との合成・全PALは未完。

最新：shift_only_entryで同じshift終了実状態にOnlyScan/Credit/RadiusRep/空Trace/LeftMoves/center.readを一括初期化。全体build9121 jobs成功/exit 0・標準公理のみ。終了scan等は前提で、shift生成からの供給とOnlyOrigin/restartへの合成、全PALは未完。

最新：only_matched_restartで終端checkPairも同じ起点/履歴から内部導出。継続一致列→終端一致→restart入口の集約定理に独立checkPair仮定なし。全体build9121 jobs成功/exit 0・標準公理のみ。入口構成/実restart/再shift/fallback/全PALは未完。

最新：OnlyOrigin/OnlyMatchedRun/only_matched_checkedで各比較のcheckPairを独立前提から除去。固定shift起点と更新履歴から導出しOnlyCompareRunへlift。全体build9121 jobs成功/exit 0・標準公理のみ。終端checkPairの内部合成と入口到達性、実restart、全PALは未完。

最新：only_compare_restartで同じwatch/shift起点→n回継続一致→終端一致のrestart入口条件を合成。center.read保存と実radius非負も含む。全体build9121 jobs成功/exit 0・標準公理のみ。各step guard供給、実restart更新、全controller/全PALは未完。

最新：OnlyCompareRun/only_compare_historyで非終端only一致のn回帰納、center不変、Trace/LeftMoves/OnlyScan/OnlyCredit/RadiusRepを同時保存。全体build9121 jobs成功/exit 0・標準公理のみ。各stepのguardは前提で、固定shift入口からの供給と終端dispatch/実restartへの接続は未完。

最新再開：`only_terminal_radius`で終端一致にも実radius.incの表現と非負guardを接続。全体build9121 jobs成功/exit 0、標準公理のみ。center保存・実restart更新・全比較区間帰納は未完。CLAUDE_RESUME冒頭の再開追記を優先。

引き継ぎ：repo直下`CLAUDE_RESUME.md`の「Resume checkpoint — 2026-09-14」を最優先する。今回は文書だけ更新。次は終端一致の実radius.inc保存→center不変を含むSearch.start guard→固定入口からの比較区間帰納。全controller・物理refinement・無条件定理は未完。直前build成功の記録と、今回の現物確認を同文書で区別している。

最新：RadiusRep/shift_radius_rep/radius_rep_incで実半径counterとscan半径を接続。only_history_matchedが同じinc後のRadiusRepも返す（署名変更）。全体build9121 jobs成功/exit 0、標準公理のみ。終端一致counter/center不変/Search.start全guard・全PALは未完。

最新：shift_run_center/shift_search_guardsで同じshift終了centerの表現/focus/座標とread存在、radius非負判定を導出（初期正規形/n≤radius値）。全体build9121 jobs成功/exit 0、標準公理のみ。その後の実radius counter更新/実restart/全PALは未完。

最新：SearchFinish.begin/ begin_positiveでSearch.startの既存スケジューラ状態を定義。終端restart条件に同じlast→begin.work一致を合成。全体build9121 jobs成功/exit 0、標準公理のみ。program.reset/lower alias/center・radius guard/chain idle/clock/全PALは未完。

最新：history_terminal_last→only_terminal_restart_conditionsで同じ最終immediate状態のscan保存/broken/非負margin/正last/lagzeroを一括導出。全体build9121 jobs成功/exit 0、標準公理のみ。Search.start(last)/idle/clockの実restart更新、入口guard/再shift/全PALは未完。

最新：only_history_matchedでOnlyCreditも同じ履歴更新に保存、only_scan_terminal_matchで同じ終端margin.negative=falseを追加（署名変更）。全体build9121 jobs成功/exit 0、標準公理のみ。last正値の終端合成/実restart/再shift収支/全PALは未完。

最新：OnlyCreditでmargin+cycle≥0を追跡。shift_only_creditでfresh非負marginから初期化、only_credit_stepでimmediate/cycle.dec保存、only_credit_terminalで最後のmargin非負判定。全体build9121 jobs成功/exit 0、標準公理のみ。履歴/終端lastと同時合成・再shift収支/全PALは未完。

最新：watch_last_lowerでready成功watch/distance≥4h→last≥3h。watch_shift_last_positiveで同じh回shift後の任意追加consume（失敗含む）last正値。順序/正規形はTraceから供給。全体build9121 jobs成功/exit 0、標準公理のみ。phase4逆方向/margin収支/restart同期/全PALは未完。

最新：chain_shift_order/control_canonical/future_lastで境界順序・正規形をshift後へ保存し、入口last>hなら任意追加consume（失敗含む）後last正値。全体build9121 jobs成功/exit 0、標準公理のみ。入口下界・margin累積・restart同期/全PALは未完。

最新：only_scan_terminal_matchでcycleEnd/checkPair/実一致→scan半径+1・broken=true・lagzero・cycle.dec.zero・margin+1。全体build9121 jobs成功/exit 0、標準公理のみ。restartのmargin≥0/last>0と同一履歴への接続、全PALは未完。

最新：caught_scan_terminal_matchで最後の左≠予測・左右一致ならscan半径+1と合法consume/broken=trueを証明。Scalaは左右一致優先で、この枝はshift/fallbackではなく後続restartへ。全体build9121 jobs成功/exit 0、標準公理のみ。cycle/margin/lastのrestart同期、全PALは未完。

最新：only_history_matchedの独立hprediction/hremainを削除。checkPair同値とcycleEnd=falseから内部導出し、同じTrace/LeftMoves/OnlyScanを延長。全体build9121 jobs成功/exit 0、標準公理のみ。二定理の固定入口での帰納/最後dispatch/fallback/全PALは未完。

最新：only_history_check_pairで同じTrace/LeftMoves/OnlyScanからcycle正値と（実左read=実token↔cycleEnd=false）。成功extra/左座標は履歴から内部導出。全体build9121 jobs成功/exit 0、標準公理のみ。継続一致/最後dispatch/fallbackの同一実行、入口の実guard/全PALは未完。

最新：only_history_matchedで同じ一致比較の実読出しaを使いTrace(extra++[a])/LeftMoves/OnlyScanを同時延長。全体build9121 jobs成功/exit 0、標準公理のみ。checkPair/dispatchから予測・残数前提供給、accepted分岐帰納/全PALは未完。

最新：scan_prediction_shiftを更新。比較後radius/length countersを受け、最後の予測tick→新PalAt→同じShiftRun/ChainShiftRun/終了counter値/OnlyScan入口を一括で返す。verifier表現/右位置/lagzero/brokenfalseは追加tickから内部導出。全体build9121 jobs成功/exit 0、標準公理のみ。成功watch等の実guard供給・only継続帰納・全PALは未完。

最新：shift_to_onlyで旧scan/新PalAt/比較後counter/caught watchから、同じShiftRun・ChainShiftRun・終了counter値・OnlyScan入口を一括構成。終了scan/cycle値は内部供給。全体build9121 jobs成功/exit 0、標準公理のみ。最後予測tickとの入口同期/accepted帰納/全PALは未完。

最新：shift_only_scanでreset cycleからの同じChainShiftRun終点t.center/t.leftのScanInvariantとverifier条件→OnlyScan(period=2n,used=0)。全体build9121 jobs成功/exit 0、標準公理のみ。終了scanの一括供給・accepted履歴帰納・mode/時計/全PALは未完。

最新：OnlyScan/only_scan_dispatch/only_scan_matchedでCaughtScanとcycle正規形・period−used値を統合。一致比較の同じ一歩でcycle.dec、cycleEnd↔残り1。全体build9121 jobs成功/exit 0、標準公理のみ。mode/時計・予測供給の帰納・最後dispatch/全PALは未完。

最新：CaughtScanでscan/右verifier同位置/lagzero/brokenfalseを統合。caught_scan_matchedで一致比較後保存、shift_caught_scanで同じshift後へ入口を転送。全体build9121 jobs成功/exit 0、標準公理のみ。cycle/onlyとcheckPair供給の同一帰納、全PALは未完。

最新：matched_left_predictionで左read=予測＋実左右一致からGood/合法consume1-step/broken保存。予測some/Goodを独立前提にしない。全体build9121 jobs成功/exit 0、標準公理のみ。同位置等は前提、checkPairと同一only状態への合成/帰納/全PALは未完。

最新：LeftMoves/left_moves_position/bounded_left_moves/left_moves_readで番兵までの合法左移動と座標/readを接続。shifted_check_pairは現在left座標前提を除き、shift終了ScanInvariant＋LeftMovesから導出（署名変更）。全体build9121 jobs成功/exit 0、標準公理のみ。同一tick右消費/cycle/継続成功/全PALは未完。

最新：shifted_check_pairで同じwatch/shift/成功extraと旧scan不一致から、現在実左read=実token↔extra.length+1<2h。旧右窓対応は内部供給、番兵も対応。全体build9121 jobs成功/exit 0、標準公理のみ。現在左座標/継続成功/cycle・only・lag同期は前提、全PALは未完。

最新：continued_prediction→chain_shift_continued_prediction→shifted_prediction_window。成功watch/同じshift/成功追加語から、各次token=旧右窓end−2h+extra.length+1を導出（extra.length<2h）。全体build9121 jobs成功/exit 0、標準公理のみ。成功追加語と実only比較・左head/cycle同期、全PALは未完。

最新：run_same_brokenとchain_shift_future_successで同じ語の成功をshift前後へ転送。chain_shift_supplied_runで元の合法Readsと成功からshift後の実VerifyRun.Run/同じ終了head/broken=false。全体build9121 jobs成功/exit 0、propext/Quot.soundのみ。追加語の成功/Readsは前提、実only時系列/全PALは未完。

最新：SamePrediction/consume_same_prediction/run_same_predictionでperiod/forward一致を任意consume語へ保存。chain_shift_future_predictionでshift前後のcounter差を跨ぎ同じ追加語後の実token一致。全体build9121 jobs成功/exit 0、propext/Quot.soundのみ。実only語の同一性/成功性と各k窓対応・guard・全PALは未完。

最新：successful_next/successful_predictionで実period次token=bounceの消費長mod添字。watch_prediction_windowで同じ成功watch終了token=旧右窓end−2h+1。全体build9121 jobs成功/exit 0、標準公理のみ。shift後counter変更を跨ぐperiod/forward射影、各継続k/only/全PALは未完。

最新：watch_input_cycleで同じ実読出し=bounceのmod添字。watch_previous_windowで終了変位n≥2hから次の周期語予測kと旧右窓end−2h+kの一致を導出。全体build9121 jobs成功/exit 0、標準公理のみ。実period tokenとの一致、終了位置と最後の比較同期、only/guard/全PALは未完。

最新：represented_signed_read/left_signed_readで実readと番兵つき座標を接続。scan_radius_lt/scan_failed_signedからscan_continuation_pairへ合成し、旧PalAt/R<c/旧語不一致を実scanから供給。全体build9121 jobs成功/exit 0、標準公理のみ。予測窓対応・継続head/cycle/only同一run・全PALは未完。

最新：signedReadはi≤0をnoneとし、synthetic gapの0番と実head番兵の差を明示。continuation_pair_signedで旧左不一致が座標0の番兵でも継続比較一致↔k<2hを証明（R<c/予測対応など前提）。全体build9121 jobs成功/exit 0、propext/Quot.soundのみ。実head.read対応・予測/only/cycle接続、全PALは未完。

最新：continuation_pairで旧PalAt/旧境界不一致/予測と旧右窓の対応から、shift後左比較がk<2hなら一致、k=2hなら不一致と証明。全体build9121 jobs成功/exit 0、propext/Quot.soundのみ。予測対応は前提、左番兵枝と実cycle/head/only時系列は未接続。checkPair全体・全PALは未完。

最新：Counter.singlePositive_iffでcycleEnd相当判定↔値1。chain_shift_reset_cycleでresetからh>0回shift後cycle=2h/positive=true/cycleEnd=false。同じRunのcycle正規形保存も証明。全体build9121 jobs成功/exit 0。次の核心はonly継続checkPairの文字列不変条件（cycleEndまで一致、最後で不一致）。mode/output/実guard/全PALは未完。

最新：chainShiftOne/ChainShiftRunで外側shiftTickと既存Watch.Stateの私有counter減算/cycle加算を同期。shift_run_chainで同じ外側Runを持ち上げ、chain_shift_valuesで各counter−n/cycle+2n/verifier・period・lag不変。全体build9121 jobs成功/exit 0、標準公理のみ。beginShift/only/cycle終了判定/mode/output/実guardと全PALは未完。

最新：shift_run_canonical / shift_run_values / shift_run_exitで任意の同じShiftRunの外側counter正規形保存、値収支、初期remaining値=nからn回後zero=true/positive=falseを導出。全体build9121 jobs成功/exit 0、標準公理のみ。Run存在・chain内部・mode/output/全PALは未完。

最新：ShiftState/shiftTick/ShiftRunで外側remaining・radius・lengthとheadの同一tickをモデル化。shift_heads_countersでh回後remaining=0/radius−h/length−2h、shift_scan_countersで比較後radius=R+1から終了値R+1−hとScanInvariantを合成。全体build9121 jobs成功/exit 0、標準公理のみ。chain.shiftOne/cycle/mode/output/実到達性は未完。

最新の継続：ShiftHeads / reads_shift_headsで各反復のcenter.right→left.right×2を全guardつきで同期。shift_scan_resume / scan_prediction_shiftの結論へ追加。全体build9121 jobs成功/exit 0、標準公理のみ。counter/chain.shiftOne/remaining/lengthと実center配置、成功watchのguard導出、全PALは未完。

再開用の現在地・残る前提・Scala制御順序・検証状態は `../CLAUDE_RESUME.md` の「現在地の要約」を優先する。この下は追記履歴で、古い「次は」を再実装しない。今回の保存依頼では証明コードは変更していない。

最新：shift_scan_resumeで合法center/left移動→終了ScanInvariant。scan_prediction_shiftへ一括合成。
全体build成功9121 jobs、標準公理のみ。比較前scan→予測→新PalAt→decoded移動→再開。
実同tick/center配置/counter/cycle/only/guard/全PALは未完。

最新：bounded_right_movesで終点範囲から合法Readsを構成。shifted_left_movesは比較後sentinelからの復帰も対応。
全体build成功9121 jobs、標準公理のみ。次は新PalAtとcenter/left移動を合わせ終了ScanInvariantへ。
同tick/counter/only/全controller/全PALは未完。

最新：scan_prediction_shiftで比較前ScanInvariant→最後の予測比較→新中心/半径PalAtを一括合成。
全体build成功9121 jobs、標準公理のみ。次は実shift移動と終了ScanInvariant。
移動guard/sentinel/phase半径/イベント同期/only再shift/全PALは未完。

最新：caught_scan_predictionでScanInvariant＋lagzero収支→同位置→予測Good/末尾true追加Runを合成。
全体build成功9121 jobs、標準公理のみ。次はwatch_shift_palindromeへ一括接続、実shift再開。
半径イベント/予測token/実guard/全PALは未完。

最新：aligned_prediction_goodで同位置の外側read予測一致→verifier Good。append_caught_tickで成功Run末尾へ追加。
全体build成功9121 jobs、標準公理のみ。次はlagzero/実右head位置から同位置を導きshift先PalAtへ合成。
cycle/only/実guard/全PALは未完。

最新：prepared_radius_alignmentで同じ準備/watchイベントのacceptedRadius更新値=verifier変位（lagzero）。
全体build成功9121 jobs、標準公理のみ。acceptedRadiusは受理比較区間の射影で実guard対応は未証明。
最後のshift比較・減算/reset・全PALは未完。

最新：prepared_caught_positionで準備Credits.run→watch終点の収支を合成。start/done含む全matched数を使用。
全体build成功9121 jobs、標準公理のみ。次は同じ外側radius更新との同期。
back終端ready-consume/全online/全PALは未完。

最新：watch_progress/caught_positionでlagzero＋同じmatched収支→実verifier終点。
watch_shift_palindromeの到達距離前提を除去。全体build成功9121 jobs、標準公理のみ。
半径とmatched数の実controller同期、実shift/全PALは未完。

最新：watch_shift_palindromeで実DP候補＋同じ成功watch→shift先PalAt。短回文/周期/入力右端範囲を内部導出。
全体build成功9121 jobs、標準公理のみ。終了verifier≥新右端は前提。次はlagzero/比較収支から導出。
実半径範囲/shift実行/全PALは未完。

最新：candidate_short_palindromeで実DP Candidate＋同じ左窓→PalAt(center−h,h)、letter/gap共通。
全体build成功9121 jobs、標準公理のみ。次はshift_from_rightへ合成しwatch終点/lagzero/最後の比較を同期。
実半径範囲/成功時系列/only再shift/全PALは未完。

最新：period_from_rightで短い左PalAtと右側周期→中心継ぎ目/左半分の周期を導出、shift_from_rightへ合成。
全体build成功9121 jobs、標準公理のみ。次は短いPalAtをDP窓へ、右側終端をlagzero/最後の比較へ接続。
実guard/only再shift/全PALは未完。

最新：watch_periodで同じTraceのHasPeriod(actual,2h)、watch_input_periodで同じ実入力右側の周期添字一致。
全体build成功9121 jobs、標準公理のみ。次はPalAtによる左側反映・中心継ぎ目・最後の比較との同期。
lagzero右端一致/全online成功性/全PALは未完。

最新：ChainPrediction.watch_cyclesで同じ成功watchの読出し列が任意長の往復語反復prefixと一致。
全体build成功9121 jobs、標準公理のみ。次は周期添字一致→実入力区間→shift先PalAt。
全online成功性・最後の比較同期・全PALは未完。

最新：shift_after_predictionで旧PalAt(c,R)+新右端までの周期2h→PalAt(c+h,R+1−h)。
全体build成功9121 jobs、標準公理のみ。周期は前提で、実watchからの導出は未完。
次はDP/予測/lagzeroから周期供給、shift終了不変条件へ。全PAL未完。

最新：reads_position→watch_displacementで同じwatchの実verifier変位=distance差。
shift_geometryでcenter+h/left+2h/radius−hの端点整合（実Reads前提）。全体build成功9121 jobs。
shift先のPalAt・移動guard/半径範囲・watch lag同期・全PALは未完。

最新：ScanInvariantで左右head/端点/PalAtを集約。scan_first初期化、scan_arrival、scan_matched保存を証明。
全体build成功9121 jobs、標準公理のみ。固定中心の成功走査射影。
次は中心shift/fallbackと窓/Chain/clock同期。全PAL未完。

最新：comparison_extendsで比較前の表現/端点→実左右移動→read一致→PalAt半径+1・表現保存を合成。
移動後focus/端点と半径<centerは内部導出。全体build成功9121 jobs、標準公理のみ。
次は到着保存と同じ到達不変条件へ。初期化/shift/fallback/窓/時計/全PALは未完。

最新：right_position/left_positionからcomparison_positionsを証明。実比較移動で端点center±radius→center±(radius+1)。
全体build成功9121 jobs、標準公理のみ。次は移動後Represents/focusとmatched_extendsを合成。
先頭sentinel・初期化/shift/窓同期/全PALは未完。

最新：represented_readで実head.readと入力添字を対応づけ、matched_extendsで成功比較→PalAt(radius+1)。
右端範囲は内部導出。移動後position=center±(radius+1)と左端範囲は前提。全体build成功9121 jobs。
次は実left/right移動の座標更新。中心shift/窓/時計/全PALは未完。

最新：palindrome_arrivalで同じInputTrace.append後のReachと既知PalAt保存を証明。
encoded入力の古い末尾gapは保持される。全体build成功9121 jobs、標準公理のみ。
次は実比較による半径拡張/中心移動と窓同期。到達不変条件全体・全PALは未完。

最新：reachable/window/found_mirrored安全性をgap:Boolで共通化（foundの名称はfound_window_safe）。
同じfound→copy/back→ready安全Runをletter/gap両中心へ。全体build成功9121 jobs、標準公理のみ。
次は実到達PalAt/窓不変条件・watch/時計同期。内部catch全域/期限/物理回路/全PALは未完。

最新：candidate_gap_window_layoutでgap左窓→同じ拡張入力の左添字一致。範囲条件はDP候補から導出。
全体build成功9121 jobs、標準公理のみ。次はgap右供給と合成しletter/gap共通のfound安全性へ。
PalAt/窓の実時系列・内部catch全域・全PALは未完。

最新：reachable_gap_supplyでgap=true開始の実Readsと右添字2Lの一致を導出。末尾gap/n=0も対応。
全体build成功9121 jobs、標準公理のみ。次はgap左配置/鏡映安全性を合成してletter/gapを統一。
実PalAt/時計/内部catch全域/全PALは未完。

最新：found_window_safeで同じfound結果→Copy→Back→そのperiodのreadyから安全verifier Runを合成。
左右配置/予測head形を内部導出。全体build成功9121 jobs、標準公理のみ。
Reach・窓とstreamの一致・PalAtは前提。実時系列/credits/時計との同期、gap開始、内部catch全域、全PALは未完。

最新：candidate_window_layoutでw=左stream.take spanとDP候補から左添字配置等式を導出。
左streamと拡張prefix反転の末尾gap差を明示。全体build成功9121 jobs、標準公理のみ。
次は同じReach/layoutとの合成・実Search窓コピー接続とPalAt実到達。全PAL未完。

最新：reachable_mirrored_safeで同じReachからの右Readsを鏡映安全性へ合成。末尾gapにも対応。
独立した供給長はPalAtから導出し、右配置/Reads前提を除去。全体build成功9121 jobs、標準公理のみ。
左DP配置・PalAt実到達・gap開始・全online/全PALは未完。次は左stream座標接続。

最新：ChainInputSupply.reachable_coordinate_supplyでReachから正確にn回の実Readsと、同じencoded raw上のrightReads配置を一括導出。
letter座標2L−1、suffix開始2Lの対応を証明。供給長条件あり。全体build成功9121 jobs、標準公理のみ。
次は鏡映安全性への合成と左DP配置/PalAt実到達。gap開始/末尾gap・全online/全PALは未完。

再開用の現在地・未解決点・次の座標補題案は `../CLAUDE_RESUME.md` の「再開チェックポイント」に保存。
今回の引き継ぎでは証明追加なし。最終検証記録は9121 jobs成功（今回build再実行なし）。
以下は新しい順の履歴で、古い項目の「次」は現在の着手指示ではない。

最新：ChainInputSupplyで右stack→FIFO混合読出し、Reachから同じwordのunread suffix/prefix Readsを構成。
各右移動と全Readsでword表現を保存。全体build成功9121 jobs。
letter位置のみ。次は拡張Fin3入力添字とrightReads/左DP streamの座標対応、PalAt実到達。全PAL未完。

最新：ChainMirrorで同じ入力のPalAt→左右読出し一致→DP予測を実verifierのn回Runへ（n≤radius,4h）。
headRightは既存InputTrace.moveRightへ統一。全体build成功9120 jobs。
配置等式/PalAt/Readsの実到達導出が次。内部catch全域/早期不一致/restart/shift/時計/期限/全PALは未完。

最新：ChainPalindrome.candidate_wordで実DPの二回文条件からtake(4h+1)=center::二往復語を証明。
candidate_prefix_safeは既知語の任意n≤4hでbrokenfalse。全体build成功9119 jobs。
左向きDP窓と右向きverifier既知履歴の対応は未接続。次は内部catch/早期不一致排除。全PAL未完。

最新：failed_after_watchで同じ成功Watch.Run（距離≥4h−1/lagzero）→実verifier右移動の不一致→restart3条件。
一往復済み/last正とmargin≥−1を内部導出。全体build成功9118 jobs。
早期/内部catch不一致排除、token/canRight実配置、次Search.start/clock/shift/期限/物理回路/全PALは未完。

最新：ChainRestartでlast≤boundary≤distance/Canonical保存、一往復後last正の永続性。
lagzero・margin≥−1でouter consume不一致→同じ結果のrestart assertion3条件を証明。全体build成功9118 jobs。
実到達の一往復/margin条件、内部catch不一致排除、Search.start接続は未完。全PAL/期限/物理回路も未完。

最新：margin_exactから初期負marginを成功比較で返済。clock_shift_readyはmargin前提なしでready/balance4h→不足≤4hを導出。
8192h availableと2k+2成功有効tick（初期lag≤k）、matched=同じcompareでshiftへ。全体build成功9117 jobs。
実成功区間/比較対応・失敗restart・供給期限/shift実行/物理回路/全PALは未完。

最新：ChainPrediction.watch_phaseで成功prefixを一意性から自動導出。clock_shiftで同じRunの時計→lagzero→距離/phase4→shiftを合成。
全体build成功9117 jobs。成功有効watch、ready/balance4h、初期margin非負、実compare対応は前提。
次は負margin/失敗restartと実online到達、shift/only=true。期限/物理回路/全PALは未完。

最新：WatchTrace.run_traceで同じWatch.Runの実consume列/距離増分/broken保存を抽出。
二往復prefixなら同じ終了phase4/距離≥4hを導きshift_from_traceで収支へ接続。全体build成功9116 jobs。
prefix形の自動導出とclock_catches合成が次。実clock/失敗restart/期限/物理回路/全PALは未完。

最新：ChainLag.run_lagで初期lag−非matched tick数の上界。clock_catchesはdelay2048で初期lag≤k→2k+2有効成功tickでzero。
同じ比較時計/available列のcompare数上界を使用。全体build成功9115 jobs。
成功watch継続・matched/compare対応は前提。次は同じRunのconsume列/phase、実clock対応/失敗出口。全PAL未完。

最新：ChainWatchでInternal catch→Outer matchedを同tick化（一tick二consumeも含む）。
同じRunでdistance+lag−margin保存/Canonical保存、準備から値4h、終了lagzero・距離≥4hならmargin非負→shift判定。
全体build成功9114 jobs。成功fresh watch射影で、時計/失敗restart/phase距離供給/期限/物理回路/全PALは未完。

最新：prepared_marginでmargin=lag−4h、prepared_shift_afterでlag=4h+suffix長を同じCatchで消費。
phase4保存と成功suffixから終了lag0、margin=suffix長非負を導出しfreshShiftGuardへ。全体build成功9113 jobs。
Reads/全成功/初期lag一致・outer matchedなしは前提。次は実online供給/時計/interleaving・restart。全PAL未完。

最新：ChainCatchで同じverifier成功Run nにpositive lag/decを同期し、n+k→k。
四境界catch→phase4、k=0/非負marginからfresh watch・only=falseのshift判定を導出。全体build成功9113 jobs。
初期lag/marginと準備収支の接続、外側matched/時計/中断は未完。全controller/期限/物理回路/全PALも未完。

最新：ChainVerifyRun.four_boundariesで同じ合法verifier右移動/読出し→phase4へ接続。
stack_supply/queue_supplyは格納prefixからReadsを構成、個別read/移動guardを導出。全体build成功9112 jobs。
次は予測列との一致、lag/時計のconsume有効化・marginを同期。実FIFO/中断/期限/全PALは未完。

最新：ChainSweep.round_tripを任意counter/phaseへ一般化、four_boundariesで二往復→距離/境界4h・last3h・phase4。
同じrunのperiod復元/向き/broken保存まで保証。全体build成功9111 jobs。
次は実verifier/lag/marginからcanShift条件へ。成功予測列の制御射影で、全入力認識/期限/物理回路は未完。

最新：ChainSweep.first_round_tripで成功往復後period復元、distance/boundary=2h、last=h、phase2。
逆向きplain走査→FIRST折返しを同じ状態で接続。全体build成功9111 jobs。
次は任意counter/phaseへの一般化とphase4、実verifier・不一致restart。期限/物理回路/全PALは未完。

最新：ChainSweep.first_boundaryで任意hの最初の一致走査→距離/境界h・phase1・左折を証明。
first_turn_legalはFIRST残存からLAST左移動guardを導出。全体build成功9111 jobs。
未来の一致は仮定せず、成功列の制御実行。次は逆向き走査/複数境界と実verifier・不一致/restartの接続。

最新：ChainVerifierで右stack/FIFO→PlaceHead右移動→同じreadをconsumeへ接続。
一致で距離+1、不一致broken、実letter→gapの一致を証明。全体build成功9110 jobs。
canRight/論理FIFOは前提層。次はcenter配置・回文候補からの文字一致・period移動合法性、watch反復。

最新：ChainConsumeでplain/FIRST/LAST/不一致更新、fresh watchのouter matched lagゼロ分岐を実装・証明。
h=1は最初からLASTで左折/境界1。lagゼロconsumeではlag増加なし、marginは増加。
全体build成功9109 jobs。seenはverifier右移動後という入力条件で移動との接続は未完。次は実verifier/一致保証とback終端合成。

最新：ChainReady.found_preparedで同じfound結果からcenter/assertion付きPacedCopy→PacedBack/収支を集約。
正radiusは条件付き。Scala replay_startはradiusをresetするため普遍的正性を仮定しない。
PacedBack.doneはmatched時のみlag非zeroを要求、pace_back_quietはゼロlagも対応。全体build成功9108 jobs。
次は終端matched/lagゼロでのwatch.consume分岐、実event対応/中断/期限/物理回路。

最新：prepare_pacedでstart/copy/done/backのmatched列と中間credit状態を統一。
prep_valueはstart/doneも含むmargin=radius−4h+M/lag=radius+M。全体build成功9107 jobs。
次はfound_start_backからの一括接続と実radius正条件、watch/consume。実guard/中断/期限/物理回路は未完。

最新：PacedCopy/pace_copy_balanceで実copyと同じmatched列のcounter収支を同期。
PacedBack/pace_backは同じback実行の最後のwatch移行でlag非zeroガードを証明。全体build成功9107 jobs。
次はstart/done各tickのouter matchedも含めcopy→backを合成し、実radius正条件へ接続。

最新：found_start_backでcenter.read/初期化から同じcopy・backを集約。ChainCreditsで準備margin/lag収支と正radius時lag非zero。
全体build成功9107 jobs。back最後はwatch化後に外側matchedがconsumeし得るため、出口はその直前。
次は実radius条件・同じイベント列への同期・watch/consume。全PAL/期限/物理回路は未完。

最新：ChainPeriod.copy_then_backで同じcopyのperiod書込み/末尾plainからLAST化後n+1回backへ接続。
11種Tokenのdecoded Tape、FIRSTの一つ右へ戻る。全体build成功9106 jobs、標準公理のみ。
次は実center start条件、margin/lagと外側matchedのinterleaving、watch入口。物理回路/期限は未完。

最新：ChainAnswer.found_copy_walkで同じfound実行からOUTPUT/h/walkerの同期copyを構成。
候補長からread有効性を導出し、読出し列と終了streamを確定。全体build成功9105 jobs。
窓とcenter streamの配置一致は前提。次は11記号periodの書込み/rewind、margin/lagと期限。

最新：ChainAnswer.answer_copy_exact/doneでOUTPUT/h射影のh回moveLeft/incを構成し、LEFT到達とcounter.positiveを証明。
全体build成功9105 jobs、標準公理のみ。次はwalker/periodを同じ実行へ加える。Chain全体・正例期限は未完。

最新：DpCorrect/DpSuffix.Result成功枝にOUTPUT pos11=hを追加。ChainAnswer.found_outputでfocus8/left非空まで接続。
全体build成功9105 jobs。次はChain.copyの全h読出し/Counter構成、walker/period/期限。

最新：quanta_window_resultで同じDP終了の最小suffix候補/単項OUTPUTとterminal modeを接続。
実center配置とchain入口/正例期限への接続は未完。

最新：quanta_found_result/quanta_missed_resultで同じDP結果の候補有無とterminal modeを同値化。
stage出口契約への組込み、event/clock反復、PAL/chainへの意味接続が次。

最新：quanta_exit_modeでrun出口4種、prepared_exitでterminal/idle fallback/NextStageへ統合。
found/missedの同じDP結果との対応、stage存在契約/clock引継ぎは次。

最新：next_stage_safeがNextStageの同じcontroller状態からDouble.Run→準備→安全DP停止を構成。
イベント列/clock対応と各出口分類を含む反復契約は未完。

最新：prepared_wait_nextがstage→wait prefixからidle中断または全NextStage入口条件を返す。
wait開始clock/供給は引数。NextStage→後続実行と直接double/terminal分岐の反復契約が次。

最新：first_stage_safe/later_stage_safeが終了Canonical/非負を返すよう強化。wait入口条件を導出可能。
WaitInterrupt.double_resetでwait経由のspan reset/quarter0も保証。次は反復契約へ合成。

最新：prepared_wait_double_workで準備→run→wait→doubleの次work=準備入口spanを証明。
全stage戻り値の強化/反復とwait終了reset/quarterの集約が次。

最新：WaitInterrupt.supplied_exitがdebt=k/2048(k+1) availableから安全なidle-or-double離脱を構成。
run_debtで同じ比較数の収支。stage終了→wait→離脱の接続とfallback全体は次。

最新：WaitInterrupt.run_prefixで最初のwait離脱までの安全Run/残り列/Outcomeを構成。run_clockで同じprefix時計と一致。
十分availableから待機継続枝を排除する停止上界とstage/fallback全体の接続は次。

最新：WaitInterrupt.safe_tickでwaitStep→advance→fallback idleの三分岐安全性を証明。
scan/chain idle/非replayのSearch射影のみ。イベント列への反復とfallback全状態更新は未接続。

最新：idle_scan_wait_guardsでscan/chain idle中のwait enabled/advanceをScala式へ対応。
fallbackは同tick後段でsearchをidleにする。無条件wait継続は禁止、中断/再開を含むモデルが次。

最新：clock_sequence_doubleでwait→doubleの次availabilityを同じevents[n]に固定、範囲内も証明。
全eligible/有効dispatchは仮定。オンライン制御対応とstage間接続は未完。

最新：clock_prefix_doubleでwait prefix終了clockを用いてdouble入口work/span/quarter/debt/clock条件を合成。
次tickイベントは別引数。同じオンライン列との対応とpause refinementは未接続。

最新：clock_prefix_zeroで元available列take nのwait実行と、その同じprefix終了clockを取得。
次は終了clockからwait→double境界へ接続。実eligible/供給は未証明。

最新：advances_appendで区間位相を接続、eligible_supply→Wait.clock_reaches_zeroで2048k availableからzero到達。
実eligible/available供給と停止prefix時計への接続は未完。

最新：GalilScaffoldWait.reaches_zeroが十分advanceからassertion込みwait prefixのzero到達を構成。span/Canonical保存。
実clock位相とadvance供給時間、次のdouble dispatchへの接続は次。

最新：double_stage_next_sizeで実double→準備→run→doubleから次work=2n/StageSizeを導出。
double_reset_of_quantaで終了span reset/quarter0も保証。clock/debt条件の同じtraceへの合成とwait反復が次。

最新：prepared_span→prepared_double_workで次work=準備入口span。StageSize初回成立/倍増保存を実traceへ接続。
前doubleからspan=2nを得る全stage合成とwait経由反復、全境界条件の集約は次。

最新：safe_quanta_frameでfinalStageとstageSpan（double時はwork）保存。double_work_of_quantaで次work=旧span。
準備側span保存とstage数値不変条件への接続は次。

最新：Double.enter_boundaryでzero→double後advanceのdebt/clock選言を導出。wait非zero時のadvance非負性も証明。
stage終了から境界へ、境界から後続stageへの全状態不変条件の合成は次。

最新：later_stage_safeで後続double→prepare→安全DP停止を合成。入口debt≥0、またはdebt≥−1/clock resetを許す。
run/wait→double同tickのadvance境界を落とさない条件。実到達不変条件/event guard/初期radiusは未接続。

最新：double_then_prepareでdouble→DP入口を同じ状態から構成、quarter0/Canonical/debt収支を保証。
later_stage_ticks追加。次は後続clock上界とSafeQuantaの合成。

最新：GalilScaffoldDoubleで実quarter更新順のadvance込み完走、span+2n/debt+n/4-count（quarter0・4倍数）を証明。
次はdouble終了→prepare→runと後続clock予算の合成。

最新：StagePrepare.first_stage_safeで初回grow→prepare→SafeQuanta停止/Result/収支を合成。
run入口debt予算とstage時間上界は内部導出。実イベント列対応・初期radius契約・後続stageは未接続。

最新：calibrated_quanta_safeで時計の切上げrunBudgetを直接使用。first_stage_ticksでgrow+prepare+runBudget≤63span。
次は準備終了状態とrun入口の接続、全stage advance予算の分配。実guard/初期radiusは未接続。

最新：SearchRun.dp_quanta_safeが実DPからadvance込みSafeQuantaの存在/停止/Result/収支を構成。
予算列のprefixで停止、run終了後は実行しない。入口debt予算・準備状態対応・全stage時計への接続は次。

最新：SearchRun.quanta_safeで64呼出し→外側advance単位の安全性/Canonical/収支を証明。
RunQuanta存在・停止とclock予算・共有準備Stateの接続は次。非run移行後のtickは含めない。

最新：StagePrepare.first_prepared_safeで初回準備終了debtの非負性を時計上界から導出。
終了Canonicalも初期状態から保存。実イベント対応・初期radius・tick長は前提、run区間のadvance安全性は次。

最新：StagePrepare.paced_grow_then_prepareで共有grow→prepareのadvance込み実行を合成。
正確なDP入口とdebt=初期値+2g-全advance数を同時保証。次はAdvanceClock/実guard/run区間との接続。

最新：PreparePaced.prepared_interleaveでprepare開始dispatchを含む全n tickへadvanceを挿入できた。
終了状態はdebtのみspendへ差替え。次は共有Growingのcredit/advance収支との合成。実イベントguardは未接続。

引き継ぎ確定：全体build成功（9101 jobs、exit 0）、diff check成功。起動build終了済み。
現在の到達点・未証明・次の具体作業は `../CLAUDE_RESUME.md` の「引き継ぎ確定版」を優先する。
次はprepare初期dispatchも含むadvance挿入と、共有Growingのcredit/advance収支を合成しAdvanceClockへ接続。
実guard・初期radius・runStep非負性は未接続。以下は逆時系列の履歴であり、古い「次」は現行TODOではない。

最新：PreparePaced.interleaveで共有準備Runへ任意外側advance列を挿入。終了状態はdebtだけ差替え、他全field不変。
実advance生成条件・grow credit・runStep assertionとの接続は未完。

最新：StagePrepare.grow_then_prepareで共有Stateのgrow positive/zero guardからprepare完走へ接続。
g tick＋2r+2m+7 tick、span+8g/debt+2g。外側advance割込みは未実装。

最新：PrepareControl.prepare_completeで初期reset/walker/work/LOWER設定を含め2r+2m+7 tickの準備完走。
grow/doubleの呼出し境界・advance割込み・heap実現は未接続。

最新：PrepareControl.prepared_runでlower入口から2r+2m+6有効tickの共有Run完走を証明。
正確なDP初期config/run/done=false/debt保存/finalStageを同時保証。初期prepare/grow/advanceは未接続。

最新：PrepareControl.source_copy/source_homeでCopy/Rewindを共有Runへliftしpc320/done=false/runへ接続。
4区間lift完了、通し合成とphase-specific frameは次。

最新：PrepareControl.lower_load/lower_homeで既存Load/Rewindを同じ有効tick数の共有Runへlift。
copy入口のLOWER/SOURCE/workを保証。次はCopyとSOURCE Homeのlift・全区間合成。

最新：PrepareControlに共有Stateと準備4モードTick/Runを定義し、debt/他テープ保存を証明。
既存Load/Copy/RewindのこのRunへのliftと完走は未実装。定義追加をcontroller完成扱いしない。

最新：SourceReady.prepare_program/prepare_then_dpでwalker準備の全12テープ状態をDP初期状態へ一致させ、有効tick予算付きResultへ接続。
基本操作数とcontroller tick数は別。mode/debt/heap/FIFO全体は未完。

最新：SourceReady.place_program_opsで同じwalkerコピー/homeを12テープLoading.Runへlift。
SOURCE以外とPCを保存。3m+2は基本操作数。LOWER/setup/reset/startとの合成は次。

最新：SourceReady.input_readyでPlace/InputHead walkerの同じ実行をSOURCE Rewind/preloadへ接続。
incoming保存・左移動guard含む。全12テープ/mode合成と物理FIFOは未完。

最新：ScaffoldLower.source_readyでCounter.Copy m+1＋Rewind m+2 tickと正確なSOURCE preload/finalStageを接続。
stream引数とPlace/InputHead walker、全状態/modeの合成は未完。

最新：ScaffoldLower.lower_readyでCounter駆動書込みr+1 tick＋実LEFT検査home r+2 tickを証明。
正確なDP単項LOWER preloadへ接続。SOURCE/mode全体/heap評価は未完。

最新：ScaffoldGrow.paced_stageでgrow後のadvance列も含むdebt収支を証明。
後続work=0はgrow禁止の射影。実prepareのworkコピーと同一視せず、modeからdebt射影を接続する必要あり。

最新：AdvanceClockで初回radius+advance≤2*max(r,1)、後続advance≤span/8をdelay2048で証明。
実stage長/radius/収支は条件のまま。first_stage_debtはそれらからnegative禁止を導出。

最新：AdvanceClockがclock由来advance列を生成しadvance数*delay≤available数を証明。
grow_before_first_compareでreset後最初の比較までのdebt収支へ接続。全stage非負性は未完。

最新：ScaffoldGrow.paced_valuesはgrow後のadvance減算を任意Bool prefix列で計上。
debt=初期値+2*grow数-advance数。実compare条件とのイベント対応は未接続。

最新：ScaffoldGrow.grow_exactで二スタックCounterのg回更新＋終了判定、span+8g/debt+2gを証明。
負の初期debtも許す。外側advanceMatchの割込みとprepare操作は未接続。

最新：PrepareClock.preparation_ticksでdecoded準備モードのg+2r+2m+7 tick収支を証明。
具体Counter/tape/walkerとのrefinementは未完。copy長mとspanを同一視しない。

最新：buildOnlineはGalilClock.deriveのdelayを使う。固定既定256との混同を訂正。
TimingCostで新DP上界のstage係数63・delay候補2048の数値不等式を証明。
実stage制御tick数への対応・Scala数値更新・debt収支はまだ未実施。

最新：SearchRun.quantum64_safeは入口debtのCanonical/非負を仮定し、Scala assertion込みの有界呼出し列を保証。
online全体の入口非負性や外側advanceMatchの収支は未証明。この仮定を解消した扱いにしない。

最新：SearchRun.quantum64_exitsで有界Callsのdone＋run退出＋Resultを統合。
calls_stoppedで非run後の残余runStep呼出しは不変。非runの外側tick処理とは別。

最新：ScaffoldSearchRun.realize_callsでGuardedRunをmode.run guard＋finish更新の呼出し列へ接続。
run iff not-doneを維持。debt requireと外側tick入口running/非run dispatchは未接続。

最新：ScaffoldDpCost.GuardedRun/guard_runでdone後のslot抑制を証明。
quantum64_correctは64*(50*N+27)要求slotで正しいDP終了を保証。実Search mode/tick対応は未完。

最新：ScaffoldDpCost.scheduled_correctが具体preloadから3186*N+1683有効tickで正しいdoneを保証。
実Search.tickのenabled列がこの予算を満たす証明は未完。次はquantum/modeと進捗の対応。

最新：GalilDpCost.initial_correct_costで同一実行のResultと3186*N+1683上界を統合。
read-key一意性からCompleted終了状態の決定性を証明。次はScaffold Searchの実schedule/正例期限へ。

最新：GalilDpCost.initial_terminated_costでDP全体の停止実行を3186*N+1683命令以内と証明。
空/短入力と任意lowerも含む。次は既存Resultと同一実行への接続、続いてGalil期限。

最新：GalilDpPreparedCost.prepared_costがPC372までの全状態契約＋3168*N+1661命令上界を保証。
次はStartのlong/short分岐で既存Loop.terminates/short_nextの上界を保持し全DPコストへ接続。

最新：GalilFppMarkedCost.marked_fpp_exact_costで9テープmarked FPP全体を1584*N+830命令以内と証明。
正確なmarks/SOURCE/head終状態も保持。次はDpPreparedへ2倍変換とdispatch1命令を合成する。

最新：GenerationCost.initial_completed_costでFPP全体の実行を390*N+4命令以内と証明。
初期化・生成・失敗探索・border出力・halt・空入力を含む。次はmarked FPP/DPとGalil期限への接続。
旧132*N+12とは異なる保守的な上界。以下のFPP全体未完という記述は履歴。

最新：GenerationCost.input_step_costで失敗探索と両終端分岐を合成した。
入力一文字の固定費366＋BACK/S/failure potential差分まで証明済み。
次はadvance_input/process_prefixへ持ち上げ、初期化・Chain出力込みの全体時間上界。
下の「失敗探索との合成前」は保存時点の過去記録。

引き継ぎの最新状態・未実装の次手・検証記録は `../CLAUDE_RESUME.md` 冒頭の
「再開時にまず読む最新スナップショット」を参照。以下は累積履歴で、古い「次は」は更新済みの場合がある。
現在は両終端分岐のコスト証明まで完了し、失敗探索との合成前で停止。
Execute/Stepsの重み付きヘッド移動上界を使う案は未実装。今回の保存で証明コードの変更はない。

GenerationCost.zero_miss_supply_costは8命令＋BACKへの2ビット追加を計上し、
一致側と同じ固定費18＋BACK/S差分の形へそろえた。失敗探索とinput_stepの合成は未完。

`GalilFppGenerationCost.hit_ready_cost` で一致比較からReady復元までコストを接続。
delta(p)を終了S-開始Sへ変換し、BACKとS位置の償却形にした。失敗探索・zero_missとの合成は未完。

`GalilFppSupplyCost` で候補scanと一致enqueue分岐を償却コストへ接続。
一致分岐は命令数+5*終了BACK高さ≤11*delta(p)+16+5*開始BACK高さ。
次はGenerationとfallback差・C/S移動の全実行償却。全体上界は未完成。

`GalilFppReadCost` でdequeue償却上界を全read instanceとLazyForward scanへ持ち上げた。
scanは命令数+5*終了BACK高さ≤11*d+8+5*開始BACK高さ。単体検査成功。
次はSupply/Generationへ持ち上げ、enqueue増加とfailure差/delta和を合算する。

FPP全体時間へ戻り、Materialize.dequeue_costを追加：命令数+5*終了BACK高さ≤7+5*開始BACK高さ。
旧dequeueは互換wrapper。ReadInstances/LazyForward/Supplyへpotential付きコストの持ち上げが次。

`GalilScaffoldMatchClock` はreset間のavailable tick数に対するcompare回数を正確に挟む。
debt上界にはadvanceSearchとの対応と処理時間上界・restart境界の接続がなお必要。

debtはstart時に-radiusとなるため、全時点での非負性は成立しない。SearchFinishの収支補題で
debt+radiusを追跡し、finished/wait境界のradius≤creditsへ必要条件を整理。
その境界上界自体は未証明で、Galil.advanceSearchと実処理時間への接続が必要。

`GalilScaffoldSearchFinish` でprogram.step後のfound/missed/double/wait分岐をDP Resultへ接続。
doubleのcounterコピー/resetを含む。finalStage/debtのonline不変条件と実heap/circuitへの対応は未完。

RawScheduleの `realize_block` で単一ノードの連続instruction slotsを用いる実行と
controller suffixセル保存を合成。Search.tickの実enabled/mode更新・controller操作は未接続。

RawScheduleの `realize_run` は同長/Nodup/初期未使用の事前固定Address列でControl.Runを実現。
`block` は同一ノードのinstruction prefix slotsを具体化。実instructionIndex/quantum・
controller suffixとの干渉・複数ノードへの接続は残る。

RawTickの `realize_run` / `scheduled_completed` で任意pause列と停止traceを合成し、
十分な有効tickからheap側done=trueと最終テープ解釈を保証。割当は存在証明で実固定scheduleは未接続。

`GalilScaffoldRawTick.realize_tick` はheap上のdecoded enabled/done/halt/nextPC/tape操作を
既存Control.Tickの全分岐へ接続。fresh Address/WellFormedが前提、bit回路評価・実割当は未接続。

NextPcの `targetEvent_iff` はtarget別イベントOR集約をlookup計算と同値化。
`target_unique` で有効targetの一意性。decode済み値の層であり、Value/Exprのbit評価・done更新は未完。

`GalilScaffoldNextPc.realize_next` は入口focus/read表から次PCを計算しraw tape loopへ接続。
実DP全命令のread記号Nodupを `dp_wellFormed` で検証。Scala nextPc集約・done更新・
bit回路との対応は未証明。

`GalilScaffoldRawTapes` で各テープwrite→left→rightの実順序foldを合成。
`realize_loop` は次PCを命令意味論から与えた場合のProgram対応。nextPc計算・done更新・
bit回路・field decodingはまだ未接続。

`GalilScaffoldWriteGuards` はwriteイベントのtape/symbol一致、全テープwrite foldの単一操作化、
inactive/非write時の無変更を扱う。moveとの実順序合成・nextPc/done・bit回路への接続は残る。

MoveGuardsの具体的 `keys n`（全テープ×左/右）のNodupと被覆を証明し、`concrete_loop_move`
から列の前提を除去。`inactive_loop` / `nonmove_loop` は非実行・非move時の不変性。
write群・PC/done更新・bit回路評価との合成は残る。

MoveGuardsの `eventLoop_once` は入口PCのmoveイベントを逐次foldし、選択された一回の操作へ
簡約する。キー列Nodup/被覆は引数で、実列・inactive等の分岐・bit回路snapshotへの対応は未完。

`GalilScaffoldMoveGuards` はraw命令のtape/direction別イベントが高々一つ有効であることと、
排他的な共有Address書き込みの対応を証明。具体的PCのdecodeが前提で、bit回路評価・
全ループ・instructionIndex/quantum・controller領域との接続は未完。

`GalilScaffoldHeapProgram.realize_completed` は有限heapから任意のList Program停止traceを
同じPC列・最終解釈で実現。新規ノードのslot0を順に使う存在証明であり、実Scalaの固定割当・
時間スケジュールとの一致は未証明。

`GalilScaffoldHeapProgram.realize_step` は共有heap上の全テープ構成で、既存Programの
任意read/write/左右moveを実現する。他テープの内容を保存。fresh Addressは引数で、
全traceの割当と実Circuitへの接続は未完。

`GalilScaffoldHeapTape` のheap lookup/push/popによる左右移動・reset・writeを既存List tapeへ接続。
fresh allocation下で他の共有rootを保存。Program全体と実Circuit field decodingへの合成は残る。

Heapの `Allocator/Bounded` から未使用slotのfreshnessを導出し、追加割当・次ノード・disabledの
保存を証明した。Scalaの実slot非衝突/guard排他性とfield decodingへの接続は依然として残る。

`GalilScaffoldHeap` でノード×有限slotの共有heapをListへ解釈し、fresh pushによる全既存root保存、
pop、空判定を証明。実allocateのfreshness・回路field decoding・各List部品への合成は未証明。

`GalilScaffoldInputTrace.reachable_represents` はresetから任意の入力到着・左右移動を通じて
入力全体=`xs.reverse ++ rs ++ incoming`とhead配置を保存する。`reachable_copy`は
その到達状態からstack版copyを開始できる。Queueは論理FIFO、物理セルとの対応は未証明。

`GalilScaffoldInputHead.realize_copy` はPlace版copy全体を明示的focus・左右Listスタックへ
持ち上げる。左移動時の非空guardを導出し、incoming Queueを保存する。
物理Ref/StackPoolと、初期化・右移動・入力追加によるlayout保存はまだ未証明。

`GalilScaffoldPlace` はScala PlaceHeadのletter/gap読み取りと左移動を論理射影でモデル化。
`runs` / `copy_sound` でそのcopyループを既存stream版へ、`copy_counter` / `copy_ops` で
Counter版と原始テープ操作へ接続。物理Ref・入力Queueからこの射影への不変条件は未証明。

最新: `GalilScaffoldCounter` をrootへ追加し、全体build成功（9070 jobs）。
Scala Counterのpos/negをListで解釈し、inc/decの整数値・Canonical保存・正負零判定を証明。
`realize_copy` / `copy_exact` でNat版copyを二スタックcounter版へ接続した。
物理StackPool・online walker・predicated制御は未接続。詳細と再開位置は引き継ぎ文書参照。

引き継ぎ: ユーザー依頼で現在状態を [CLAUDE_RESUME.md](../CLAUDE_RESUME.md) に保存した。
継続作業で`GalilScaffoldLoad.lean`の`home_exact`の型エラーを修正した。
`load` / `load_source` / `load_lower`はleaf検査成功、root importに追加。
マーカー駆動の巻き戻しでreset後のテープからbounded配置を作る。原始操作数は
payload長nに対して3n+4（controller tickやresetコストではない）。
オンラインwalker・counter・状態選択回路からの供給は未接続。再開文書も更新した。
`GalilScaffoldLoading.load_program` は原始ロードを全テープ構成へ持ち上げ、任意の旧状態の
論理reset後にLOWER→SOURCEの順で具体的DP初期配置を構成する。操作数は3*(lower+n)+8。
`load_then_dp` はstartと任意pause付きDP実行・最小性へ接続する。費用は原始write/moveのみで、
controller guard/counter/walker/reset、物理StackPoolのコストや実装対応は含まない。
`GalilScaffoldCopy.copy_exact` は論理的な左向き文字列streamと残量counterのcopyループで、
take(work)のコピー・drop(work)の残り・残量・END書き込みを正確に同定する。
`final_iff` は入力長≤workのときだけfinalStage=trueであることを保証する（同時終端を含む）。
`copy_ops` はこのguarded loopを既存の原始write/right列へ落とし、`copy_home` は
マーカー駆動の巻き戻しでbounded配置へ接続する。実walker・物理counter・predicated回路の
表現対応は未証明で、論理streamを実入力ポインタへ接続する必要がある。

### 最新の接続点（以下の段階別記録より優先）

`GalilFppGeneration.input_step` は、実入力テープと `Ready w (failure w N)`、
処理済みprefixの `Supply` から、比較再試行入口→探索→一致/左端不一致→
生成・必要なlazy scan→PC38の実命令列が存在し、次のprefixの `Ready` と
`Supply`、入力テープ不変を回復することを証明する。一致側はA/B/T保存と
C停止位置のmaterializationを走査証明から取り出し、`cache_tape` でC全prefixの
物理的δ表現を復元する。不一致側の10追加も参照δ値から正当化する。
`referenceStream` を区切り位置から構成し、`reference_encoded` が全prefixでの
`Encoded` を証明する。`initial` はScalaの実preloadであり、非空入力の
`initial_start` は開始PC227の1命令からPC38へ到達し、初期 `Ready`/`Supply` と
入力テープ・B位置・生成済み長を保証する。`advance_input` はPC38→37→retryの
実2命令と不変条件保存を証明した。B位置保存をfallback・検索・1文字処理へ
通し、`process_prefix` が任意の非空prefixについて初期状態からPC38までの
実行を帰納法で証明する。`process_all` は全入力後のB送りと右端記号の分岐も
含め、border列出力入口PC1へ到達する。`empty_completed` は空入力の実2命令
（開始分岐とhalt）による停止・出力なしを証明する。
`GalilFppChain` は出力側の非enqueue fallbackを実命令で証明し、`emit_next` が
現在のborderを1つ出力して次のproper borderへ戻る。`completed` は出力ループが
入場時の出力列へ `borderValues` を正確に追加し、25p+2命令以下で停止することを
示す。`initial_completed` は前半の `process_all` と接続し、空入力を含む任意入力で
実FPPカーネル全体が停止することを証明した。`generation_output` は実コードの
閉じた出力領域（PC0..36）と唯一のemit（PC36）の検査から、生成領域へ到達する
実行は出力を変えないと証明する。`process_all` に出力空を接続し、
`initial_completed` は全出力が `borderValues w (failure w w.length)` と等しい
ことまで保証する。`mem_initial_output` はその列の要素が正の真のborder長と
同値であることを証明する。`GalilFppMarked.prepared_kernel_exact` はScalaの
準備語 `w ++ [#] ++ reverse w` に実カーネルを適用し、出力集合が元の入力の
正の回文prefix長と過不足なく一致することを証明する。separatorの唯一性から
すべての真のborderが元入力長以下であることも証明済み。
`ExportMarkedCode.scala` でScalaの `buildMarkedProgram("abs")` の321命令を出力し、
`GalilFppMarkedCode` に取り込んだ（開始PC320）。`GalilFppWide` はテープ数を
パラメータ化した同じ局所命令意味論で、observer用emitは持たない。
`GalilFppMarkTransform.all_kernel_rows` は元の228命令すべてについてScalaの
変換を検査する。A移動に追加されたMARKS移動は実2命令でヘッド同期を保ち、
emitの置換は実1命令で出力長の集合に対応するMARKSセルを1にすることを証明。
`GalilFppMarkSimulation.Related` は最初の7テープの内容・位置・PCとMARKSの
ヘッド・内容の対応を定義する。`steps` / `completed` は任意のカーネル実行を
実9テープ命令列へ持ち上げ、命令数が最大2倍で対応と停止を保存すると証明する。
`prepared_marks` は準備済み入口のRelatedを前提に、実9テーププログラムの停止と
正確な回文prefixマークを保証する。`GalilFppPreparation` は任意長のSOURCE列に
対する前向きコピー（正確に8n命令）と逆向きコピー（6n命令）の実行・全テープ内容・
ヘッド位置を証明する。右端でMARKS終端と私有separatorを書いて反転する7命令、
左端でA/B終端を書いてrewindへ入る3命令も証明済み。
`GalilFppPrepareCopy.copy_run` は実bounded SOURCEから全読み取り前提を導き、
空入力も含めたコピー全体を14n+10命令で合成する。`copied_ab` / `copied_marks`
は全書き込み列を同定する。`GalilFppPrepareRewind.rewind_all` は3本のrewindと
最後のB送りを合成し、テープ内容を保ってA=0、B=1、MARKS=0、PC227へ到達する。
`GalilFppPrepareCells` はfillの範囲内・範囲外の各セルを証明し、コピー後の実テープ
からrewindの全文字条件を導く。`copy_rewind` は初期頭位置1・左マーカー・実SOURCE
のみを前提にコピーからカーネル開始PC227までを合成し、正確に24n+24命令で
A=0、B=1、MARKS=0、SOURCE=0へ到達する。`GalilFppPrepareInit.boot_step` は
開始PC320からの実18命令を証明し、`boot_eq` は空白の作業テープからC=010・
左マーカー・コピー用頭位置ができることを全セルについて同定する。
`fresh_prepare` はSOURCEだけを与えるScalaの実初期状態からPC227までの準備全体を
24n+42命令で合成し、全ヘッド位置とコピー後の全テープ関数を保証する。
`GalilFppPrepareLayout.fill_input` はその連続書き込みをbounded入力テープへ同定し、
`prepared_related` が準備後の全テープ・全ヘッドからRelatedを導く。
`marked_fpp` は準備済み入口の仮定を外し、任意のabs入力についてSOURCE以外が
空白の実初期状態から、Scalaの実321命令のプログラムが停止して正確な回文prefix
マークを生成することを証明する。これはmarked FPP単体の正しさであり、DPに
必要な終了時の呼び出し契約も強めた。7テープ出力ループから停止PC0・A頭0を
取り出し、`marked_fpp` は停止PC0・MARKS頭0・SOURCE頭0とSOURCE全内容の保存を
保証する。`GalilFppMarkedFrames` は元の228命令と追加13移動の閉じた領域を検査し、
その任意の停止実行でSOURCE頭・テープが保存されることを証明する。
`GalilFppMarkedLayout.marked_fpp_exact` はMARKSの全セルを同定する。左端は^、
1..nは回文prefixなら1・それ以外0、n+1は$、以後は空白であり、SOURCEだけを
与えた実初期状態からこの配置・停止PC0・SOURCE/MARKS頭0までを保証する。
`ExportDpCode.scala` で実 `DpFinite.buildDpProgram("abs")` の373命令を出力し、
`GalilDpCode` に取り込んだ。`GalilDpTransform.all_marked_rows` は元の321命令を
全検査し、MARKS移動・書き込みのSECONDへの複製とhaltの検索入口への置換を確認する。
`duplicate_write` / `duplicate_move` は実2命令での複製書き込み・左右移動について
両テープの内容一致・頭位置同期をそれぞれ保存すると証明する。これらは局所変換の
証明であり、複製書き込みはそれ以外の全テープ保存も保証する。
`other_move_code` / `other_write_code` / `read_code` は残る命令の正確な持ち上げを
取り出す。`dispatch` は元のhalt地点でSOURCE左端を読む実1命令からPC372へ進み、
全テープと全頭を保存する。
`GalilDpSimulation.step` / `steps` / `completed` は任意のmarked FPP実行を
DP実命令列へ持ち上げる。元の9テープ全体とPC、SECONDの内容一致・頭同期を保ち、
変換後の命令数は元の高々2倍。haltそのものは実行せず、呼び出し側がdispatchする。
`GalilDpPrepared.prepared` はScalaのSOURCEとunary LOWERのみを与えた実初期状態から
検索入口PC372への到達を証明する。SOURCE保存、SOURCE/MARKS/SECOND頭0、
MARKS/SECOND全セルが正確な回文prefix配置であることを保証する。
`GalilDpFrames.before_search` は検索領域PC346以上の閉性と準備領域の全命令検査から、
FPP領域で終了する任意の実行prefixがLOWER/OUTPUTの全内容・頭位置を保存すると証明する。
`prepared` に接続済みで、検索入口ではLOWERは元のunary下限・頭0、OUTPUTは全空白・頭0。
`GalilDpSearch.candidate_found` は下限END・両マーク1からの実3読み取りと成功halt、
`skip_lower` は下限1からLOWERのみを進める実2命令、`end_guard` はSECOND終端での
失敗haltを証明する。これらは局所分岐で、最小h検索の全ループの正しさは未完成。
`GalilDpAdvance` はnext-hの6個のguard/moveペアを実命令表で検査する。
`guard_end` は各guardでENDなら頭を動かさず失敗停止することを保証する。
`next_run` は出力1追加とMARKS+2・SECOND+4を正確に14命令で合成し、全ヘッドと
全テープへの効果を同定する。`marked_next` は次候補が入力内なら正確なマーク配置から
6セル分の読み取り前提を導く。`next_candidate` は最後のSECOND検査も含めて
次候補入口PC348へ15命令で戻る。
`GalilDpExhaustion.exhausted` は有効な正の候補hから次候補が範囲外になる4通りを
実行列で合成し、最大16命令で失敗PC347へ停止すると証明する。
`exhausted_of_room` はMARKSの2セル分の余地だけを前提とする一般化で、長さ2以上の
h=0初回経路にも適用できる。`GalilDpSearch.skip_second` / `skip_first` は下限消化後、
SECONDが0、またはSECONDが1でMARKSが0の候補を実2/3読み取りで更新入口PC363へ送る。
`GalilDpLoop.State` は両マークテープと頭位置、LOWER内容とその頭が1..lower+1に
あることを保持する。`branch` は全読み取り条件をこの配置から導き、成功または
Stateを保存した更新入口への実行を返す。`next_state` は次候補でStateを回復する。
`terminates` は有効な正の候補入口から成功/失敗haltまでの全ループを帰納法で合成し、
検索部分の命令数≤18*(入力長-h)+19を証明する。これは出力の正確さ・最小性の証明ではない。
`GalilDpStart.start_run` は検索入口PC372からの実6命令を合成し、`start_state` が
MARKS/SECOND頭1とLOWER頭1を含むh=0のStateを導く。`long_terminates` は長さ5以上で
次候補h=1への15命令と検索ループを接続する。`short_next` は長さ0/1の早期guard停止と
長さ2..4の一般化した終端経路を合成する。`initial_terminates` は空入力を含む任意入力・
任意unary下限について、Scalaの実初期状態から実12テープDP全体が成功または失敗haltへ
到達することを証明した。
`GalilDpCounters.Tracked` は出力の全セル（^、h個の1、その後は空白）・頭hと、
LOWER頭=min(cursor,lower+1)を追う。bootstrap・候補スキップ・next-hのすべてで保存する。
`GalilDpCorrect.Candidate` はh>lower、4h+1≤入力長、長さ2h+1と4h+1の両prefixが
回文であること。`accepts_candidate` / `rejects_candidate` は実分岐とこの条件を接続する。
`correct_loop` は最小の有効候補をunary出力するか、有効候補が存在しない場合に失敗する
ことを全ループで証明する。`initial_correct` は準備・初回検索・短い入力を接続し、
任意の実初期入力と下限について同じ正しさ・最小性を証明した。これでオフラインDP単体の
意味的正しさは接続済み。FPPを含む全体線形時間上界と、オンラインGalilへの実装接続・
再利用/cleanup・FIFO/PEGへの接続は未完成。
`ScaffoldCircuitSearch.step` のcopyはwalkerを左へ進め、最大span+1文字をSOURCEへ書く。
`GalilDpSuffix.reverse_prefix_pal` / `candidate_iff` は逆順のprefix条件を元窓のsuffix条件へ
同定する。`initial_correct` は逆順preloadについて、最小のdouble-palindromic suffix候補
または不存在という実DP結果を証明する。`window_correct` は実際のcopy長に合わせた
`w.reverse.take (span+1)` を入力とし、対応するsuffix窓で同じ契約を保証する。
これは入力方向と窓切り出しの意味的接続であり、オンラインcopy/resetがこのpreloadを
実現すること、有限scaffold命令への持ち上げ、時間上界を証明したものではない。
`GalilScaffoldTape` は `ScaffoldCircuitStructs.Tape` の左右スタックとfocusをリストで
解釈する層を追加した。`right_denote` / `left_denote` は全セル保存、対応するhead定理は
±1の移動、`focus_eq` はreadセル、`write_denote` は注目位置だけの更新を証明する。
`reset_blank` / `reset_head` は両スタックclearとblank focusが全空白・頭0を表すことを
証明する。右スタック空でのblank生成と左移動の非空条件も扱う。これはリスト層の
テープ対応であり、物理StackPool・共有セル・命令選択回路のrefinementは未完了。
`GalilScaffoldProgram` は任意本数のリスト式2スタックテープとPCを持つ命令意味論を
追加する。`realize_step` / `realize_completed` は既存の有限テープ実行を同じ命令列・
同じ最終テープ解釈で持ち上げ、`execute_sound` / `completed_sound` は逆方向を証明する。
移動・書き込み・readのfocus一致と左移動の合法性を含む。命令数は変わらない。
これは同じ命令表を実行する論理スタック層の対応であり、predicated circuitの選択、
doneフラグ、物理StackPoolへの実装対応はまだ含まない。
`GalilScaffoldControl` は論理スタック層へenabled/done制御を追加した。
`completed_run` はhaltでdoneを立て、`done_run` / `completed_padded` は停止後の
余分な有効/無効呼び出しが状態を変えないことを保証する。`scheduled_completed` は
実行途中の任意の一時停止も含め、有効tick数≥命令数なら同じ結果へ到達すると証明する。
`dp_scheduled` は実DPの正しさ・最小性をこの制御へ接続する。ただし初期スタック表現の
一致を明示的な前提とする。doneプロトコルの意味論は接続済みだが、Scalaのpredicated
回路がこのプロトコルを実装すること、物理loading/StackPoolと期限保証は未証明。
`GalilScaffoldPreload.initial` はSOURCEとunary LOWERの具体的な左右スタック・focus、
他の全空白テープを構成する。`initial_denote` が全セル・全ヘッド・PCを実DP初期状態へ
同定し、`scheduled_correct` は初期表現一致の前提なしにDPの正しさと任意pause付き
スケジュールでの実行を返す。これは具体的配置からの定理であり、オンラインloaderが
その配置を生成する命令列、物理StackPoolのrefinement、期限保証はまだ未証明。
DPラッパーへの全体接続、
全体資源上界・Galil source/FIFO/PEGへの接続は未完成であり、本定理はそれらを
証明したものではない。以下は各段階時点の記録で、未接続の記述も当時の状態。

## 現在の主経路：Scala の online Galil → FIFO → PEG

`GalilFppMaterialize` は実コードの最初の deltaRead について、キャッシュ済みCの
1命令読み出し、FRONTからの5命令の消去・pop・C書き込み、およびBACKからFRONTへ
1ビットを移す5命令のrefillを証明した。さらに `StackAt` を用い、任意長のBACK列を
反転してFRONTへ積み、BACKを空にしてFRONT readerへ戻る `refill` を実命令から証明。
所要命令数は厳密に5n+1。`from_back` は空FRONTからCへの書き込みまで5n+7命令で
接続し、元のCヘッド位置と残余列を保証する。`QueueAt` の抽象列を
FRONT ++ reverse BACK と定め、`dequeue` は非空キューの先頭をCへ書き、
残余キューが正確にtailになることを両経路について証明する。
数学的δ列と実C/FIFOの対応は未証明であり、
この命令証明だけでは全体の正しさを主張しない。

`GalilFppEnqueue` はScala実コードのBACK push全7箇所について、2命令で
抽象FIFOの末尾へ指定ビットを追加し、Cの内容とヘッドを保存することを証明。
`failed_left` は実PC66から38までの4命令がブロック10を末尾追加することを示す。
一致時0・fallback距離分の1・左端失敗時10が数学的δ値の符号化になるための
照合状態・fallbackの意味論はまだ未接続。

`GalilFppDelta.encoded` はδ値を1^δ0として展開する。`fallback_bit_prefix` は
逆向きビット走査の任意の途中でS/Tの消費が元のgap以下であり、次の同種ビットが
残るなら対応カウンタが正であることを証明。`fallback_bit_result` は全消費後に
Sが次のproper-border gap、Tが0になることを示す。全prefixの符号長は2n以下。
これは参照符号列の保証であり、実Cがこの符号列を保持する不変条件は未接続。

`GalilFppCache.CacheAt` は実Cの保存済みprefixと、その後がすべて空白であることを
表す。`read_correct` は最初のdeltaRead実命令について、prefix内ならFIFOを
消費せず、境界ならFIFOの次の参照ビットを1個だけ書き込んでprefixを伸ばす。
dequeueの契約をCテープ全体の関数更新等式へ強め、他セル保存を証明に使用。
全7enqueue箇所もCacheAtを保存する。境界でFIFO先頭が参照列の次ビットであること、
Cヘッドがprefixを飛び越さないことは前提であり、全FPPの生成・移動命令から
それを導く証明、および参照列をδ列へ同定する証明は未完了。

`GalilFppFrontier` は全228命令のblank制御証明書を検査し、Cが空白の状態で
右移動PC40/60に到達できないことを不変条件にする。任意の成功実行prefixについて、
非空白prefix＋空白suffixの形、prefix長の単調性、C head ≤ prefix長を証明。
`from_initial` はScala初期C=010・head=0からこの境界を導き、最終headの境界を
前提として要求しない。これは停止性や参照δビット値の一致をまだ保証しない。

`GalilFppWriteOnce` は全6deltaReadの補充領域がC空白テストからのみ入れることを
全命令で検査し、到達可能なC writeは必ず空白セルへの書き込みであると証明。
`reachable_write_frontier` は初期C=010・head=0・startから、書き込み先が正確に
非空白prefixの直後であることを導く。`reachable_cell_immutable` は到達状態で
非空白だった任意のCセルが、その後の任意長の成功実行でも変わらないことを示す。
値の生成がδ列と一致すること、未定義read/左端越えが起きないこと、停止性は未完了。

`GalilFppFailure` はfailureを最大proper borderへ接続し、fallbackが成功候補を
飛ばさないことを証明。比較→failureリンク→左端失敗の参照算法 `seek` は
次の最長照合長を返す。`emitted_delta` は一致で0個・fallback距離分・左端失敗で
1個の1を出す参照分岐について、総数が厳密にδ(n)であることを示す（n>0）。
これは実テープfallbackが正しいfailure位置へ移動することをまだ仮定せず証明した
参照算法の仕様であり、実命令との精密化は別途未完了。初期1文字は初期化側の義務。

`GalilFppFallbackBits` はappend-distance付きfallback全4箇所の実命令を証明。
キャッシュ済み1は5命令でSをpopしCを左移動、0は7命令でFIFOへ1を追加し
Aを左移動してTをpopする。`ones_steps` は任意長の連続1について5n命令の実行、
S/Cヘッドの正確な差分、C内容・FIFO保存を保証する。まだcallerがCの対象ビット列と
十分なカウンタ長を与える。0をまたぐループ、copyからの接続、proper-border値との
同定までを合わせたfallback全体の仕様は未完了。

`GalilFppFallbackLoop.loop` はappend-distance付き全4箇所で、コピー済みTから
空Tを検出して抜けるまでの任意回の実ループを構成する。k個の区切りと合計Σd個の
1を横切り、命令数5Σd+9k+1、Aの左移動k、Sの減少Σd、Cの左移動Σd+k、
FIFOへの1の追加k、C内容保存、T空を保証する。終端実行の存在を前提としない。
ただし `Blocks` がC上の対象列を与え、S/Aの十分な長さとコピー済みTを前提とする。
copyからの接続と、Blocksを実δ列の不変条件から導くことは未完了。

`GalilFppCopyInstances.copy_restore_all` をS/T以外の全ヘッド・テープ保存まで強化。
`GalilFppFallbackLoop.fallback` は空Tのcopy開始からループ終了までを接続し、
コピー済みTという前提を除去した。命令数は5Σd+15k+5、Aはk、SはΣd、CはΣd+k
減り、FIFOへk個の1を追加する。全4append-distance箇所を扱う。
Sの正しい単項形状、CのBlocks、Σd≤kの前提を到達状態のδ不変条件から導くことは残る。

`GalilFppDeltaTape` はCを先頭0＋各1^δ0ブロックとし、区切り位置n+Σδを定義。
`tape_blocks` がこの物理テープ仕様から実ループのBlocksを導き、`fallback_failure`
が全4箇所のcopy開始から終了まで、A=failure(p)、S=次のgap、C=その区切り位置、
FIFOへのgap個の1追加を証明する。命令数≤20gap+5。Blocksとδ和の安全性を別途
callerに要求しなくなった。`initial_tape` はScala初期010とこの表現の一致を示す。
ただし到達状態でS形状とCのTape仕様が保たれる全FPP不変条件は未証明。

fallbackの出力契約をさらに強化した。`Unary` は左端記号、連続した1、直後の空白を
含み、各popから任意長のループ、copyを含むfallback全体まで保存を証明。
`fallback_failure` は出力Sが再びUnaryであり、Cが次のfailure位置までTape仕様を
満たすことも返す。従ってfallback単体の後でS形状を再仮定する必要はない。
一致後の前向き走査・遅延δ供給・比較分岐を含む全体の不変条件は引き続き未完了。

`GalilFppForward.matched` は保存済みδブロックについて、一致PC62からFIFOへ0追加、
C前向き走査、次入力へ進むPC38までを実命令で接続する。Sは次のgap、Cは次の
区切り位置となり、命令数5δ+5。`FullUnary` はS未使用suffix全体の空白を含む。
既存Unaryの「直後1セルが空白」だけでは繰り返しpushを正当化できないため、
ここではFullUnaryを明示的に要求する。fallbackのFullUnary保存と、C空白時の
FIFO materializationを含む前向き走査、全体の到達不変条件は未完了。

S形状の条件を統一した。`GalilFppFallbackBits.Unary` 自体を未使用suffix全体が
空白である仕様へ強化し、`FullUnary` はその別名に変更。単発pop、任意回fallback、
copyを含むfallback、数学的failureへの接続、前向きpush/scanが同じ形状を保存する。
fallbackの入力側もsuffix全体の空白を明示的に要求する。旧い「直後1セルのみ」から
強い保存性を推論してはいない。全体ビルドで全依存先の証明を再確認済み。
C空白時の前向きFIFO補充と全体の到達不変条件は依然として未完了。

`GalilFppReadInstances` は補充の実行PC範囲を元証明に追加し、命令対応証明書から
全6deltaReadへ証明を移す。`dequeue_all` はFIFO先頭取り出し、Cの1セル更新、
A/B/S/Tの全ヘッド・テープ保存を保証。`forward_blank` はPC39のaliasから補充を
経て実継続PC38/42へ戻る。前向きreaderの空白分岐自体は接続済みとなった。
保存済み・未保存が混在するδブロック全体の前向き反復とFIFO供給不変条件は未完了。

`GalilFppLazyForward.Supply` は参照ビット列に対するCの保存済みprefixとFIFO残余を
一体化する。`scan` は保存済みセルと空白セルが混在する任意長の1^d0を、実命令で
最後の0まで読み切る。S/Cはd進み、Sの全suffix空白とSupplyを保存し、
保存済み長＋FIFO長も保存する。前向き走査中の補充経路はこれで接続済み。
十分なビットが供給済みであることと、その参照列が正しいδ列であることを
全FPPの入力処理・比較・生成から導く不変条件、ならびに時間上界は未完了。

`GalilFppSupply.enqueue_supply` は実enqueue全7箇所で、次の参照ビットを追加すると
Supplyが保たれ、供給範囲が1伸びることを証明。`failure_scan_available` は候補
p≤failure(N)、N>0なら、pのδ走査に必要な最後の0まで既に処理済みNの符号範囲に
入ると示す。`scan_candidate` はこれを混在走査へ接続し、候補ごとの供給十分性を
処理済みprefixの供給量から導き、次のS gap/C区切りまで実行を構成する。
処理済みprefix全体が正しく供給されているという到達不変条件の生成側証明は未完了。

`GalilFppCompare` は全4比較箇所のretry→比較を実命令で証明。一致ならPC62へ進み、
不一致ならAを元の位置へ正確に戻し、左端記号ならPC66、通常文字なら対応する
copy開始PC97/137/177/217へ進む。全コードを検査し、任意長の実行で入力コピー
A/Bのテープ内容が不変であることも証明。比較と既存macroの再帰的な組立て、
処理済み入力prefixの供給不変条件、全FPPの停止性・時間上界は未完了。

`GalilFppRetry.miss_retry` は非左端での不一致比較から、Aの復元、copy、実fallbackを
経て同じretry PCへ戻るまでを接続する。`Ready`（A候補、空T、S gapと全suffix空白、
C区切りとδテープ仕様）をfailure(p)で再び返し、候補の狭義減少と入力A/B内容保存を
保証する。所要命令数≤20gap+9、FIFOにはgap個の1を追加。比較文字の読み出し条件は
まだ入力表現から与える前提であり、全比較列の組立てとSupply保存は未完了。

`GalilFppRetry.search` は候補の強い帰納法で任意回の実不一致retryを構成し、
候補r=0または次文字が一致するretry状態へ到達する。Readyを保存し、FIFO追加は
正確にp-r個の1、命令数≤29(p-r)。終了実行を前提にしていない。
入力文字の有限アルファベット条件は最初に与え、A内容保存で途中へ引き継ぐ。
終端比較の一致/左端失敗から入力処理完了への接続とSupply保存、全FPPの時間上界は残る。

`GalilFppRetry.zero_miss` は候補0での不一致比較から左端分岐と2回のBACK pushまで
8命令で接続し、PC38（Bを進める直前）へ到達する。Ready(0)、入力A/B内容を保存し、
FIFOへ正確に10を追加する。探索の終端分岐のうち左端失敗が閉じた。
全探索の終端選択・一致分岐との統合、供給不変条件、全体時間上界は未完了。

`GalilFppRetry.search_dispatch` は任意回の不一致探索と終端比較を統合した。
一致ならAを進めたPC62と候補rのS/C/T条件、左端不一致ならReady(0)を保つPC38を返す。
どちらも正確なFIFO残余を返し、命令数≤29(p-r)+8。終了側をcallerに選ばせない。
一致PC62からのlazy前向き走査との統合、生成ビットがδ列となるSupplyの維持、
全FPPの入力反復・出力・時間上界は未完了。

`GalilFppSupply.matched_lazy` は一致PC62の実0追加からC右移動、混在cache/FIFO走査、
PC38までを接続する。Cを全ブロック保存済みと仮定しない。S/Cは次のgap/区切り位置と
なりSupplyを保存、供給総量は正確に1増える。現在Cが区切り0であることからcache内を
導き、次C headの境界条件も導出する。追加する0が参照列の次ビットであることは
生成側の前提として残り、探索の出力Supplyと結合する全入力処理の不変条件は未完了。

`GalilFppSupply.generatedPosition` はN文字処理済みで候補pまで戻った時の生成位置を
定義する。`fallback_supply` は次のfailure長の候補上界から追加1列の参照一致を導き、
fallbackのC/FIFO効果からSupplyと生成位置更新を得る。`matched_generated` は
failure(N+1)=p+1から次ビット0を導出し、実一致処理後の供給量が正確に
position(N+1)+1であることを証明。「次ビットが0」という独立前提はここでは不要。
次failure長に関する意味論条件を実比較探索と接続すること、全入力反復・時間上界は残る。

`GalilFppRetry.search` が実際に失敗して飛ばした候補列 `Skipped` も返すよう強化。
`skipped_seek` はこの列が参照seekの結果を変えないことを証明し、`endpoint_failure`
が実探索終端rから「一致ならfailure(N+1)=r+1、左端失敗なら0」を導く。
入力テープの文字比較と参照wordの比較が一致することはまだ明示的な前提。
これを具体的入力テープ表現から導き、生成/Supply更新と一本にする接続は未完了。

`GalilFppInputWord.inputTape` はScalaの^word$＋空白をFin9テープとして定義する。
`compare_iff` は実文字テストと参照wordテストの一致を全位置で証明し、入力外の
右端記号・空白も通常文字に一致しないことを含む。`search_word` はこの具体的表現から
実探索の入力妥当性と比較一致を導き、終端が次のproper borderを計算することを証明。
比較一致を別途callerが仮定する必要はなくなった。Ready/Supplyの入力反復による維持と
生成更新との統合、全体時間上界・PALの最終接続は未完了。

`GalilFppGeneration.search_supply` は具体的入力上の任意回の実探索とSupplyを結合。
実探索が返す次border長から、追加した1列全体がδブロック内であることを導き、
各不一致の生成正しさを独立に仮定せず、探索後のSupplyと生成位置を証明する。
これに必要なC内容保存をmiss_retry/search/search_wordの出力へ追加した。
終端一致/左端失敗を含む入力1文字分の統合と反復、全体の時間上界は未完了。

ユーザーの指示により、主経路を `scala/pal/src/main/scala/pal/GenerateOnlinePeg.scala`
が実際に生成する構成へ変更する。以下に残る4スロット・ReplayLoopの記録は既存部品の
記録であり、完成までの必須工程ではない。特に全入力境界の zero lag を完成条件にしない。

実装の接続は `ScaffoldCircuitGalil.buildOnline` → `ScaffoldEventBuffer.bufferSource`
→ `packService` → 通常PEGの出力。ソースの中心移動・DP探索・周期鎖・FPP・再生を
任意入力について証明し、`GALIL_CLOCK.md` の時間契約を実ソースから導く。
予測可能性により肯定回答だけは締切に間に合い、未完了時は不受理としてよい。
否定回答の遅れは `GalilRealtimeSuite` に明示的な回帰例がある。

`GalilFifoDeadline` は worker 時刻のFIFO完了漸化式を定義し、
work(n)+c*k(n)≤2c+c*k(n+1) から finish(n)≤2cn+c*k(n) を証明する。
肯定回答時 k(n)=0 ならその締切内に完了し、未完了を false とする外部回答は
ソース回答と全時点で一致する。これは抽象スケジューリングの証明であり、
`move_predictability` は Scala の中心座標から k(n)=C(n)-n-1 を取り、中心の単調性と
work(n)≤alpha*(C(n+1)-C(n))+beta からその予測不等式を導出する。
`center_answer_eq` は肯定時 C(n)=n と合わせ、service=2*(alpha+beta) で回答一致を示す。
具体的 source の時間契約、局所FIFO実装との精密化、PALとの同値はまだ未接続。
Scala実装との対応を基準にこれらを閉じる。旧構成を保持するための追加義務は作らない。

`GalilSourceCost` は Scala の既定 quantum=64 に限定して、marked-FPP の命令上限
296*m+190 と m≤8*delta から実行バッチ数≤37*delta+3 を導出する。
copy/home/marker/rewind と replay の局所上限を加えて moveSlope=2125、
高々2回の move/shift と比較・dispatch を加えて intervalOverhead=1044 を得る。
`default_answers` が c=3169（service=6338）を既存のFIFO定理へ接続する。
局所資源上限・1出力間のmove回数・中心不変条件は引数であり、Scala有限命令・
実モード遷移からそれらを導出する作業は残る。定数の算術と実機契約を区別する。

`ExportFppCostCertificate` は Scala の `FppFinite.buildProgram("abs#")` を実行して、
228命令の全分岐先・charged判定・cutまでの順位を `GalilFppGraph` へ出力する。
Lean の `certified` は全分岐先の範囲内性、順位1〜4、charged命令の順位1、
noncharged命令からの全分岐での厳密な順位減少を `decide` で検証する。
これでグラフ係数4の有限検査をScalaの実命令表からLeanへ持ち込んだ。
ただしグラフ射影と実行意味論の接続、実行のcharged区間への分割、テープ移動量の
資源不変条件は別途必要。FPP全体の線形時間証明が閉じたとは扱わない。

`GalilFppTrace` は検証済み graph certificate を命題へ取り出し、charged命令で終わる
任意長のグラフ実行について instructions≤4*charges を帰納証明する。
未到達分岐も含む全経路を対象にし、有限テストの長さ上限は用いない。
`kernel_from_ledger` は charges≤33*N+3 を仮定として132*N+12へ接続する。
charged区間の会計は閉じたが、実テープ実行からTraceを構成する精密化と
33*N+3の資源不変条件は未完了。後者をこの定理の仮定に隠して完成扱いしない。

`ExportFppCode` が同じScalaビルダーから228命令の操作・テープ番号・記号・分岐先と
開始PCを出力する。`GalilFppCode.graph_projection` は実命令表の射影が既存の検証済み
グラフと完全一致することをLeanのdecideで検証する。`GalilFppInstruction` は7本の
テープ・9記号・非負ヘッド位置の参照実行規則を定義し、readは現在セルで分岐、writeは
1セル更新、moveは単位移動、emitはAの位置を記録する。未定義readと左端越えには
成功遷移を与えない。`GalilFppExecution.completed_trace` はこの規則で停止した任意の
実行を検証済みグラフのTraceへ写し、instructions≤4*chargesへ接続する。
これはScalaのVM規則を明示的に形式化したもので、Scala言語自体の検証ではない。
初期テープからの停止性・出力のFPP正当性・charges≤33*N+3は未完了で、
最終StructuredMachineの構成もまだこの参照実行とは別に必要。

`GalilFppInputScan.input_moves_le` はBテープの資源項 moves(B)≤N を実命令表から導く。
全228命令でBへの書込み・後退がないこと、BがEND上にあるときの制御領域が
PC≤37またはPC=227で閉じることを有限検査する。この領域からB移動は起きず、
B移動後のPC=37は領域内なので、初期PC=start、B位置1、セルN+1がENDから
全実行でB位置≤N+1を帰納証明する。移動回数と前進量の完全一致を合わせて
N以下を得る。停止実行を対象とするが、最終位置上限・総時間上限は仮定しない。
他のテープ資源項と停止性・FPP正当性は引き続き未完了。

`ExportFppCode` は命令グラフの A移動−B移動の重みから非負potentialを計算する。
正の重みの閉路があれば生成を拒否し、Lean側 `GalilFppCandidate.code_credit` が
全分岐の displacement+potential(next)≤potential(pc) を再検証する。
`step_credit` は実テープの単位移動へ接続し、初期A=0/B=1/PC=startから
`candidate_before_scan`（A<B）を停止実行について証明する。
既存のB終端不変条件と合わせ、`candidate_le_input` はA位置≤Nを導く。
これは候補位置の範囲保証であり、Aの総移動回数≤4Nや候補の文字列意味論とは区別する。

`GalilFppInstruction.Steps` は停止を要求しない有限実行prefixを表す。
`GalilFppPrefix.initial_bounds` は任意prefixで A<B≤N+1、B移動回数≤N、B内容不変を
証明する。従来のCompletedに依存した範囲・B資源項の停止仮定を外した。
`instruction_budget` は prefix命令数+rank(末尾PC)≤rank(開始PC)+4*charges を示し、
未完了charged区間も扱う。これらは停止性の証明へ循環なく使用可能だが、
残りテープの資源上限と、各到達状態で停止または次の正当な遷移が存在する証明は必要。

`GalilFppCopy.copy_restore` はScala Builder.copySToTの最初の実インスタンス
（PC28からPC2）を具体的read/write/move命令列で証明した。
Sが原点LEFT、1..sに単項1、s+1にblank、ヘッドsなら、6s+4命令で戻る。
S内容とヘッド位置sは保存され、Tはsセル前進し、新しい区間はすべて1になる。
Tの旧ヘッド以下のセルも保存する。引数sは証明用で、実行はセルのLEFT/blankを読む。
停止性・出力・命令数をこの小区間について実行から導出している。
他の生成インスタンスへの適用、呼出時に単項S不変条件が成立すること、全fallbackの
距離総和の上限はまだ必要で、FPP全体の停止・線形時間保証とは区別する。

`GalilFppCopyInstances.copy_restore_all` は実生成されたcopySToT全5個に適用する。
入口/復帰先は28/2、97/69、137/109、177/149、217/189。
全40命令のPC付替え一致を `instances_match` で有限検証し、命令の付替えが
実テープ操作とStepsを保存することを帰納証明する。元のcopy証明は実行したPCが
28..35の内部に限られることも返すよう強化し、範囲外の命令を誤って移送しない。
全呼出しで6s+4命令・S保存復元・Tへの単項s個追加を得る。
各呼出し時のS形状不変条件とfallback全体の距離会計は引き続き未完了。

`GalilFppDelta` は既存のmatchStateからprefixのproper-border長failureを定義し、
failure(n)≤n-1とfailure(n+1)≤failure(n)+1を導く。
δ(i)=1+failure(i)-failure(i+1) の区間和をtelescopingし、fallbackで横切る
1の数 + 次のgap = 旧gap を証明する。`partial_crossing_le` は途中の区間和も
旧gap以下、`pop_positive` は未処理の1があれば残カウンタが正であることを示す。
`total_ones_le` はδ列全体の1の総数≤prefix長を与える。
これらは任意wordの数学的δ列についての証明であり、実Cテープ/FIFOがこの列を
保持する精密化はまだ未完了。実行側のS非アンダーフローを証明したとは扱わない。

## 完成条件

`PalPeg/Main.lean` の `pal_in_peg_of_structured` に、次の二つを渡す。

- 有限制御・有限テープアルファベット・固定マイクロステップ数の具体的な `StructuredMachine`。
- 任意の入力 `w` に対する `M.SAccepts w ↔ w ∈ PAL` の証明。

全体を一本の `Prog` にする必要はない。有限個の継続を制御状態に保持でき、
`ProgLangBank.Bank` がその仕組みを既に与える。一本化のためだけの
PCテープと再開点復元を、新たな証明義務にしない。

## 再利用する核と残る接続

1. 語の組合せ論、GS分解・消費量、段分解の正しさは再利用する。
2. 実行系は `TextFeedPipelineControl` と、報告器を組み込んだ
   `TextFeedPipelineOutput.machine` を使う。実マクロ復帰後の読取りと
   入力1回の固定長実行は証明済み。`TextFeedPipelineOutputSound.frames_iff`
   は初期化済みのstreaming状態から、任意の非空入力接頭辞について実機の
   出力と末尾パターン出現の同値を証明済み。中断・待機・再入・実報告器を含む。
   `TextFeedPipelineInitial.prefix_snapshot` が実前処理完了から物理初期状態を構築し、
   `prefix_boot` が空の左パターンも含め、実入力割込みつきで最初のマクロへ接続する。
   起動時の方向テープ・SourceSafeは具体的seedから導出済み。
   準備から初回照合までの締切を全段の実入力供給と結ぶ証明はまだ閉じていない。
   `prefix_boot` の到達点は入力フレーム途中でもよい。`pending_frames` は残りworkerと
   通常フレームを一つのTraceへ結び、`OutputSound.trace_iff` は途中位相からの
   Traceでも実観測出力の同値を与える。起動前からの96-step出力機械の実行と
   このTraceの接続、および実起動時の残り位相・時間条件の導出は引き続き必要。
   `OutputInitial.prefix_boot` は観測付きstep/opStepからなる実到着スケジュール上で
   最初のservice macroへ接続済み（方向設定1呼び出し後、最大6呼び出し・3到着）。
   空の左パターンも扱い、観測状態を保持する。`OutputClock.boot_microsteps` が
   その起動を実外側microstepへ接続済み（最大678ステップ・最大3到着）。
   `finishAt_embed` は任意の前処理/prefix部分フレーム終了点で時計の同期を導く。
   `boot_any_phase` は入力境界でのcomplete_arrivalも統合し、任意の完了位相から
   最大775microsteps・4到着で初期creditつきmacroへ至る（明示的な数値条件の下）。
   段生成からこのstartup creditに対応する実入力スライスを供給する義務は残る。
   `OutputBirth.finishAt_safe` は固定初期制御から任意入力と部分フレーム終了点まで
   SourceSafeを導き、`seed_timed` のObservedReadyにも同じ証明を含める。
   `Direction.finishAt_dir` は全命令の方向ヘッド停留と観測・入力捕捉の保存から、
   任意の実入力と途中フレーム後の方向初期化条件を導出する。
   `OutputBirth.finishAt_dir` が具体的seedへ適用し、ObservedReadyは方向条件も含む。
   `OutputBoot.ready_boot` はObservedReadyから、同じ実機の最大775microstep・
   最大4到着で初期credit付きservice macroへ接続する。途中時計の同期を実行から
   導出し、実入力word++tailの対応から残り入力の添字を導出、空白同値を到達点まで保存。
   必要な後続入力4個の供給と全段のstreaming実行への接続は引き続き必要。
   `OutputTrace.realize` は任意のservice Trace（途中フレーム開始を含む）を
   外側実microstepへ展開し、`expand_inputs` は入力記号列の一致を保証する。
   `output_iff` は起動後の空白同値な実機にも適用でき、実受理bitとRawMatchesを同定。
   `OutputResume.resumed_iff` は現在位相から残りworker数を導出し、その96倍の
   実microstepに続く通常sRound列の実受理bitとRawMatchesを同定する。
   起動後のcreditをそのまま使い、出力・照合状態をリセットしない。
   `OutputResume.initial_semantic` は起動時pos=|u|・q=0・空比較区間とZDeadlineから
   ScanInv/ZInvを導き、`boot_resumed_iff` はSemanticを独立した前提にせず通常入力を扱う。
   `Parameters.decomp` は具体的prepRes（rate=8）からKSimple・右パターン非空・
   ZDeadlineを導出し、`conditions` は準備時Safeから全ての照合記号条件を供給する。
   `Parameters.stage_resumed_iff` は具体的prepResと固定workerRate 8を復帰定理へ適用し、
   GS・Semantic条件を独立した前提にせず、実受理bitと元のstagePat全体の末尾出現を同定。
   `Stage.prepared_running` はL≥32の具体的非パディングseedから、準備・prefix・起動・
   残りフレーム・通常sRound照合まで一本で接続した。Complete/Macro/GS/Semanticを
   呼出し側の前提にせず、実受理bitとstagePat全体の末尾出現の同値を返す。
   入力スライスの長さ・対応・後続4到着の供給は明示的な前提として残る。
   全段制御からこの供給を実現することと、小段処理・生成再利用はまだ未接続。
   `OutputBudget.setup_timed` はL≥32・rate≥2・前処理開始n≤L/8の下で、
   具体的前処理・prefix仕事量・4起動到着を含めたcreditを固定workerRateから導く。
   workerRateはservice側の速度条件も満たし、入力長を参照しない。
   段生成による開始nの上界、実入力スライスの選択・供給、小さい段の処理は未接続。
   `OutputBirth.seed_timed` は到着済みw.take Lからの具体的seed（padding=0）を使い、
   空FIFO・PrepPre・n=0を構成して上記締切へ接続する。未来長の空白paddingは証明用の
   代表テープだけに置き、任意の将来実行でも実テープと制御・観測出力が一致する。
   このseedを全段の生成・切替・再利用から実現する有限制御はまだ未接続。
   `BirthBuild.build_machine` は空白39本からseedを作る有限内部命令機械を実装し、
   初期化1回・到着記号ごとのコピー・凍結1回の|w|+2命令での完全一致を証明。
   `builtStart_eq` は出力テープとseed_timedの初期配置を同定する。
   `BirthInput.input_seed` は実到着を固定2microstepで直接コピーし、非空入力の
   読取り後に固定freeze動作1回で同じseedとなることを証明する。
   `input_start` は固定の前処理制御への引継ぎ後のstartとの完全一致を与える。
   begin/freezeの時点選択、全段への配線・再利用は未実装。
   `ProgramRecycle` は使用範囲mの任意形のテープ束を5m+4動作で同時消去する実部品。
   実行列から範囲上界を導出し、`TextFeedPipelineRecycle.future_output` は消去・seed
   再構築後の全将来出力が新品と一致すると証明。方向列の時間制御・解放窓への割当と、
   コピー元の実入力履歴の供給はまだ必要で、再利用の全体制御は未完成。
   `ProgramRecycleWindow.reset_phases` は相位14〜19を左1・右2・左3の等長相位へ割当て、
   使用範囲m<C*qの下で全テープの消去を証明。
   `ClockRecycleMachine` は時計8本と作業156本を固定C+2ステップで同一機械へ配線。
   `work_round` で更新前相位によるC回の消去、`clock_from_blank` で元時計の実行保存を証明。
   `ClockRecycleTrace.reset_window` は時刻16*qの時計配置から6*q実到着で当該39本の
   消去が終わると証明。作業テープは任意形・使用範囲m<C*qのみを仮定し、
   相位列・方向列は実時計から導出する。範囲上界・固定速度Cの全段評価はまだ必要。
   `HistoryConcat.machine` は実ソース2本から接頭辞と差分を読む有限制御の統合コピー。
   `concat_prefix` でh+2動作の完全コピー、`stable_done` で完了後の待機保存を証明。
   ソースのオンライン維持・開始位置への移動、到着中の保存、seedへの配線はまだ必要。
   `OutputPrepFinish.setup_finishes` は具体的な前処理を96-step出力機械上で
   完了させる（実capture・複数フレーム・最終部分フレーム込み）。
   `OutputPrefixSetup.setup_reaches` はその具体的前処理から、部分フレームの残り・
   入力待ち・必要なproductive framesを通じて、実出力機械のprefix Complete到達へ
   接続済み。開始PrepPreと入力列・締切条件を実段生成から供給する義務は残る。
3. 中央判定、段の生成・切替・再利用を全体機械へ接続し、空白の初期テープから
   各入力到着後までの不変条件を証明する。数学的な段の仕様と実機の実現を区別する。
   `ProgramBroadcast` と `TextFeedPipelineSlots.machine` は4スロット・156本の
   有限制御配線を実装。実入力を同時に各スロットへ渡し、任意の初期配置から各局所実行・
   観測bitが単独機械と一致することを証明した。マイクロステップ数は単独機械と同じ。
   これは配線であり、世代交代・有効段選択・再利用・最終PAL受理は未実装。
   配線機械自身のacceptingはfalseで、各スロット出力はoutputから取り出す。
   `SlotClock.machine` は2本・有限相位・固定2microstepの世代時計を実装。
   30相位のうち後半16相位で次の走査区間を書き、最後にテープ役割を交換する。
   `rollover` は任意長の成長途中テープからの実世代末遷移を証明し、
   `first_generation` は長さ1から16への最初の30ラウンドをkernelで検証する。
   `SlotClockStartup` で四段時計の空白からの初期テープ構築を実装・証明。
   32到着で区間長4/8/16/2・相位6/2/0/14へ達し、自動で通常時計へ切り替わる。
   `from_blank` は以後の任意長の各局所実行との一致を証明。
   `SlotClockTime.startup_phase_matches` で全時刻32+tの実相位とphaseAtの一致を証明。
   `startup_resident` は実有限制御からの常駐bitとactiveAtの一致を証明。
   `SlotClockEvents.machine` は各段2個のBoolで再起動パルスを実装。
   `run_project` で時計の実行保存、`pulse_matches` で全時刻n≥32のrsCanon一致を証明。
   パルスの照合器ライフサイクルへの接続、残差・成長長の全テープ表現との一致は未完。
   `SlotClockSweep` は任意長の通常左右走査と、相位29の全走査・成長・役割交換を証明。
   `SlotClockGeneration.generation` は30相位を合成し、任意長qが30*qラウンドで
   長さ16*qの次世代配置となることを両テープの等式として証明。
   `generations` / `interval_growth` で実機の任意世代反復と16^k倍成長も証明済み。
   `SlotClockPosition.phase_at_time` は世代内の任意時刻tの相位p+t/qを証明。
   `first_generation_from_blank` で初期相位が0でない段を含む四段の空白起動から
   最初の世代末までの全配置も接続済み。canonSlot全フィールドとの全時刻の一致、
   四段の照合器ライフサイクル接続はまだ必要。
   `grow_left` / `grow_right` で通常成長相位の全書込み列（相位14の左境界を含む）、
   `idle_left` / `idle_right` で前半の非活動テープ保存も証明済み。
4. 全体機械の受理同値を得たら `pal_in_peg_of_structured` で閉じる。

次の証明はこの接続の未解決条件を減らすものに絞る。中断・給送・再開の評価は、
同じ実行に対する不変条件と時間評価へ集約する。既存の局所補題を増やすこと自体を
完了基準にしない。

## 履歴供給の接続状況（2026-09-13）

`HistoryReadyInput.prepared` まで実機で接続済み。用意された非空白ソースu,vから、
コピー完了の自動検出・巻戻し・新着ログ保存を4本、固定C+1 microsteps/到着で行う。
実到着数nについてn*C≥2*(|u|+|v|)+5なら、統合済みソースと新着ログを得る。
宛先には空白番兵1セルが必要で、完了後の余分なworker tickは内容を変えない。

更新：後半を`HistoryRecover`へ置き換え、元ソース2本を消去・回収しながら統合先を
巻き戻す。同じ2h+5の予算で空き2本も得る。両元ソースの左番兵を[blank]と明示。
`prepared_padded`は全4本の開始状態をBlankEqで受け取り、回収で残った右空白を
実テープ上から削除せずに次の実行へつなげられる。

次の接続は全空白からの番兵初期化と、新着ログの凍結・役割回転・次回ソース化。
この定理だけでは初期ソースを供給できず、matcherのseedへの配線も未完。
履歴準備の線形評価を、実スロットの開始・締切と同じ実行上で満たす必要がある。

`HistoryRotation.frozen` まで追加接続済み。旧統合先・旧ログ・空き2本から、
[2,3,1,0]の物理配線で旧ログだけを巻き戻し、新着を回収済み0へ保存する。
|v|+2≤到着数*Cなら次のコピー開始のデータ前提が満たされる（全てBlankEq対応）。
残る制御接続は凍結完了→コピーの自動遷移と、クロック駆動での役割更新。
現在はこれらのフェーズ開始を外から指定する定理であり、全周期の実機ではない。

更新：`HistoryNext` と `HistoryNextInput` で凍結完了→コピーの自動遷移も接続。
`HistoryRotation.cycled` は1パス全体の実入力実行でLayoutの再生成を証明し、
2*(|u|+|v|)+|v|+8のworker予算を得た。パス内の外部切替は不要。
次に必要なのはパス間の有限ループ制御（役割を保持・更新）と実クロックによる起動。

更新：`HistoryLoop.block_layout`で起動bit付き実到着を受ける有限ループ制御も接続。
役割を保持・更新し、起動到着も新ログへ渡す。速度32でh≥32の履歴処理はfloor(h/8)
到着以内（`block_by_eighth`）。`SlotClockBirth.startNow_power`は実クロックの到着前
制御から既読長が2の冪のときだけ真となるbitを得る。まだ別機械なので、次は
startNowを同一到着でループへ渡す結合と両機械への射影を証明する。

更新：`ClockHistory`で12テープ・33microsteps/到着の結合を実装し、
`clock_round`/`history_round`で両射影を証明。`trigger_from_blank`は結合機械でも
既読長≥32の起動信号が2の冪と一致する。履歴の番兵初期化は未完のため、次は
最初の到着を有限制御に保持し、番兵を置いてから同じ到着を処理する初期化接続。

更新：`ClockHistoryStartup`で全空白初期化を実装。入力を有限制御に保持してから番兵を
置き、同じ入力を処理する。12テープ・34microsteps/到着、時計の到着数は不変。
`startup_layout`と`startup_role`で32文字の実入力後のLayoutと初期役割を証明した。
次はdyadic区間に起動信号が1回だけあることを使い、全周期のLayout帰納へ進む。

更新：`ClockHistoryPeriods`で実dyadic区間とHistoryLoopのブロックを接続し、
`ClockHistoryInvariant.actual_dyadic`で全周期Layoutを帰納証明した。
`actual_window`はN≥32の各2の冪についてN+N/8≤|w|≤2Nの間、全空白実行の
実テープがw.take Nを読取り可能なsourceとして持ち、w.drop Nをログに保つと保証。
履歴単独の期限供給は閉じた。次はこのsourceをmatcher seedへ実配線し、コピーに伴う
ヘッド変化と復元も含めて四段matcher・時間評価へ接続する。

更新：`TextFeedPipelineBirthSource.seed_from_history`はactual_windowが供給する実ソースを
読み、39本のOutputBirth.seedを生成する有限機械への接続を証明。コピーは|w|+2 tick、
実空白終端で終了する。`future_output`で既存pipeline出力との一致も証明済み。
全体への共有ヘッド配線・源ヘッド復元・同時到着保存・workspace回収条件と期限評価は残る。
history単独のN/8締切と、追加コピーを含むmatcher開始締切は区別して評価する。

## 退役した構成

追加検証: `TextFeedPipelineBirthRestore.copy_restore` は、実ソースからのコピー後、39 本の seed テープを保存したまま履歴ヘッドを復帰する往復を証明する。復帰は固定有限制御で長さを読まない。ここでのコピー→復帰の制御切替は証明側で明示しており、全体スケジューラへの自動接続・入力との並行実行・準備期限は未完了。直列復帰を準備期限内と仮定してはならない。

続く `TextFeedPipelineBirthCycle.ready_at` でコピー→復帰の手動切替は解消した。40 テープ、有限制御 `Fin 3 ⊕ Fin 3`、1 worker tick の機械がソース終端を検出して自動復帰し、`2*L+5` ticks 以降は seed と復帰履歴を保存して停止する。これは worker の局所上限であり、実入力との並行化・共有履歴への配線・段準備期限の証明は依然必要。

`TextFeedPipelineBirthInputCycle.prepared_padded` は実入力ごとに capture 1 tick と worker C ticks を動かす 41 テープ機械に接続した。コピー/復帰と同時に全到着入力を一度ずつ log に保存し、右空白 padding を持つ実テープからも seed・復帰履歴・log の契約を満たす。`prepared_by_eighth` は C=32、L≥32 でソースが既に利用可能になってから L/8 到着後の完了を証明する。履歴構築時間は含めないため、これを既存 history の L/8 上限に直列加算して段全体の L/8 期限を満たしたと主張してはならない。log を実際の照合器入力キューへ引き渡す接続と全体速度設計は残る。

`TextFeedPipelineBacklog` は物理 source の focus から既存 39 テープ共有入力レジスタへ文字を capture する 40 テープ reader を追加した。`read_round` は source を一文字進め、`empty_round` は終端で停止する。`first_from_source` / `next_from_source` はその実読取結果から既存 FIFO worker の Exec 契約へ接続し、両 FIFO の snoc・予約テープ保存・読取を含む 93/69 action 上限を証明する。これらは一文字の実行トレース契約であり、全 backlog を回す有限制御、worker の40テープへの配置、書込中 log からの読取 source 作成、queue を持つ状態から pipeline への handoff は未接続。既存 pipeline start は空 queue を仮定するため、単に nonempty queue を渡して旧 seed 定理を適用してはならない。

開始条件のずれを避ける主接続として `Program.TapeReplay` と `TextFeedPipelineReplay.from_seed` を追加した。空 queue の seed から pipeline 全体を起動し、物理 source の各文字について既存機械の B microsteps（最初だけ some、残り none）をそのまま実行する。`encoded_word` は任意保存語・任意後続 padding ticks で通常入力 fold と状態・全 target tapes が完全一致することを証明する。reader は有限位相 `Fin B` を持ち、word/length は runtime control に入れず、終端では停止する。pipeline 特化で B=`(R+1)*96+1`、40 テープの worker。これにより nonempty queue 初期状態への拡張は不要となるが、保存ログを forward source にする処理、到着し続ける入力との並行実行、再生遅延を解消する全体速度・期限・slot scheduler の証明は未完了。Backlog の FIFO 単独契約は補助として残し、先詰め方式を完成扱いしない。

`Program.ReplayArrival` は再生 worker と実入力 log を接続する。固定 C+1 microsteps/到着、t+2 テープで、old.length*B≤fresh.length*C なら worker は old の通常実行と一致し、新着 fresh は別ログへ一度ずつ保存される。`replayed_after` は既に past を実行済みの状態から past++old への接続を証明し、再生バッチ間で matcher を再初期化しない。`replayed_padded` は回収済み実テープの空白 padding も許す。fresh 自体はまだ未処理であり、この定理だけで現在位置への追いつきや現在入力の PAL 判定を主張してはならない。次段ログの巻戻し/役割交換の有限制御、および backlog 収縮・準備期限は未完了。

`ReplayBufferTurn.prepared_padded` は旧 consumed buffer と spare の消去、次 batch の巻戻し、新着 log の保存を並行化した。処理時間は max(old.length,batch.length)+2 worker ticks、復帰後は buffer0/1 free、2 readable、3 new log。`ReplayLoop.machine` は matcher t 本と4 buffersを持つ有限制御の自律ループを実装し、recovery 完了で replay、replay 終端で roles=[2,1,3,0] に交換して recovery を再開する。実入力は各 C+1 frame の最初にその時点の log role へ一度 capture する。`worker_preserves_matcher_during_recovery`、`replay_handoff`、`worker_preserves_current_log`、`capture_arrival` は局所遷移を検証済み。ループ全体の語順・buffer layout 不変条件、blank 初期状態から sentinel/seed を作る接続、追いつきの時間上限は未証明。accepting は内側 M の出力を転送しているだけで、catch-up 前の現在入力の認識を証明したものではない。

`ReplayLoopReplay.batch_handoff` は standalone replay を実際の ReplayLoop.worker へ接続した。任意の保存語 w から、w.length*B+1 ticks 以内に通常入力 fold と同じ matcher 状態・target tapes を得て、他 buffer を保存したまま roles を回して recovery に入る。`handoff` が最初の終端時刻を扱うため、呼出側へ「途中で終端にならない」仮定を残さない。この定理の tick 列には capture は入っておらず、実入力 frame が再生を横切る場合の不変条件、recovery 側の同様の接続、全 cycle の追いつき時間証明は依然必要。

`ReplayLoopCapture.capture_lift` は実 frame の capture が log role 3 のみを更新し、source role 2 と matcher 全体を保存することを証明した。`capture_then_replay` でその後の連続 replay と接続し、`frame` は任意制御状態からの実入力 sRound が capture 一回＋C worker ticks と完全一致することを証明する。`frame` 自体は内部 handoff を禁止しない。replay 限定の射影定理には区間内で replay が続く条件が残るため、handoff をまたぐ入力列全体の buffer/layout 不変条件と backlog 収縮時間の証明は引き続き必要。

`ReplayLoopRecovery` で recovery 側も実 worker に接続した。`tick_lift`/`run_lift` は HistoryRecover と同じ動作を証明し、`handoff` は最初の完了時刻から自動で replay へ進むことを証明する。`buffers_handoff` は consumed/frozen frontier から max(old.length,batch.length)+3 ticks 以内に replay に入り、buffer0/1 free、buffer2 forward source の BlankEq 契約を得る。matcher と log は保存する。`capture_lift` により recovery 中の実 capture も log のみに作用する。再生・回収両分岐の局所/区間対応は揃ったが、capture と handoff を任意回横切る全体不変条件、および backlog 収縮による catch-up 期限の証明は未完了。

`ReplayLoopRotation.cycle` で worker の回収→再生→役割交換の一周を接続した。前回消費語長 a、今回保存語長 b なら max(a,b)+b*B+4 ticks 以内に、matcher は保存語を通常順序で実行済み、旧 free buffer は次 log、旧 log は次 recovery の frozen buffer となる。回収で生じる padding は `source_lift_blankEq` / `padded_batch_to_recovery` で保持し、次状態は実テープの BlankEq 契約として得る。`recovery_to_replay` / `replay_to_recovery` は両 handoff の物理配置が一致することを証明済み。この cycle は capture を挟まない worker tick 列であり、継続的到着下の全周期語順・catch-up 時間はまだ未証明。

`ReplayLoopEvents.actual_word` は任意の実入力列を capture/tick の証明用 event 列へ完全に対応させる（runtime 入力 alphabet を変更しない）。`arrivals_events` で capture の抽出列は元入力と一致する。`recovery_interleaved` と `replay_interleaved` は各 phase 内で任意回 arrival を挟んでも、worker は tick 数だけ進み、新着 log は元の順序で増えることを証明する。`appendLog_frontier` / `appendBuffers_log` が実 log テープの文字順を与える。phase 区間内でまだ handoff しない条件は残るので、最初の handoff event で分解する全周期不変条件と catch-up 時間の証明は未完了。

`ReplayLoopEventCut.recovery_handoff` / `replay_handoff` は任意 interleaved event 列から最初の完了 tick を取り出し、そこまでの全 arrival を保存したまま次 phase と残り event 列へ接続する。呼出側に「完了前の全 tick が active」という仮定を残さず、既知の完了上限 n と work(es)>n から切替を得る。再生終了側は rotated recovery layout まで接続済み。`cut_accounting` は切替 tick の除去で arrival 列が pre++post の順序のまま残ること、`work_events` は実入力 w の worker 予算が |w|*C であること、`remaining_budget` は次 phase の残予算を証明する。任意回の cycle の全体不変条件・初期化・catch-up 期限の最終統合はまだ未完了。

`ReplayLoopEventPadding.run_blankEq` は任意 event 列（arrival、recovery、replay、rotation を含む）で実テープの右空白 padding の対応が保たれることを証明した。`compose` / `segments` は区間末尾の BlankEq 契約から次の区間へ進み、任意個の検証済み区間をテープの初期化なしで合成する。各区間の契約と分割自体は引数であり、自律機械の全周期不変条件をこの定理だけで完了扱いしない。残りは具体的 phase 契約の再帰的構成、到着率からの catch-up 上限、および PAL 全体への統合。

`ReplayArrivalRate.segment_budget` は実入力 trace の任意連続区間 seg で arrival_count(seg)*C≤work(seg)+C を証明する。区間は frame 途中で始まり/終わってよく、切替で分割した event 列にも適用可能。prefix の上下界を実際の events 構造から帰納証明し、外部から到着率を仮定しない。これで次 batch の長さを処理時間から評価できるが、具体的 cycle の時間上限との結合・backlog 収縮・最終 catch-up はまだ未証明。

`ReplayContraction.segment_shrink` は C=8*(B+5) と一周の worker 上限 max(a,b)+b*B+4 を組み合わせ、新着量≤max(a,b)/8+2 を示す。到着率は実 events の任意区間から導出するが、一周の時間上限はここでは条件のまま。`two_batches` / `strict_decrease` / `eventually_small` はこの漸化式から2周ごとの減少と有限回後の pair maximum≤3 を証明する。これは zero lag や具体的な準備期限を証明しない。実 interleaved cycle の時間上限を全周で満たす不変条件、総時間上限、残った少量 backlog の排出と現在時刻の受理の整合性は未完了。

`ReplayCyclePadded.cycle` は一周の開始条件を3本すべて BlankEq に緩め、前周の回収で残った空白を除去せず、同じ max(a,b)+b*B+4 worker 上限と次 recovery 配置を得る。これは capture を挟まない一周の再利用条件を閉じるもので、interleaved 全 cycle の上限を自動的に導くものではない。新着入力付きの一周契約とその再帰的適用は引き続き必要。

`ReplayPaddedHandoff.recovery` / `replay` は実テープと canonical 配置の BlankEq から、新着入力を挟む最初の切替を移送する。`cycle` は両切替を合成し、回収完了上限 n と回収済み source の再生完了上限 m、および work(es)≥n+m+2 から、次の rotated recovery までの実 event 区間を抽出する。その worker 数は n+m+2 以下で、両区間の全 arrival は log に保持される。完了上限はまだ引数であり、具体的 batch 長からの導出・次周不変条件・zero lag はこの定理の結論ではない。

`ReplayPaddedHandoff.phase_bounds` は具体的 frontier 配置から回収完了を max(old.length,w.length)+2 tick、再生完了を w.length*B tick で導出し、再生後の matcher 全配置が w.foldl M.sRound x と BlankEq であることも示す。`batch_cycle` はこれを interleaved 一周へ適用し、phase 完了仮定を呼出側から除去した。実初期配置には canonical 配置との BlankEq を許し、次周までの区間の worker 上限は max(old.length,w.length)+w.length*B+4。回収後の free buffer 2本も結論に保持する。次の課題は出力の nextBuffers と蓄積 log を次周の frontier 契約へ整形して帰納適用すること、実 trace の到着率との結合、zero lag と全体期限・PAL 受理の統合。

`ReplayPaddedHandoff.next_layout` は回収後の free 2本と再生結果の BlankEq を次周の canonical frontier 配置へ戻す。次 batch は pending++arrivals(recovery)++arrivals(replay)、新 log と spare は空、matcher は今回の batch 処理後。`boundary` にこの開始配置をまとめ、`boundary_cycle` は具体的一周上限の予算がある任意 event 列を seg++post に分け、work(seg)≥2 と既知上限を保ち、残り post を同じ boundary（roles 回転、old=batch.map enc、batch=pending++arrivals(seg)、pending=[]）から実行した結果との BlankEq を証明した。これで次周へ同じ契約を適用できる。一方、任意回の帰納適用・実到着率による総時間と zero lag の保証・PAL 全体の統合はまだ残る。

`ReplayDrain.drain` は work(es) に関する強帰納で、予算内に完了する一周を繰り返し適用する。残り suffix の worker 数が次周の worst-case cost 未満になる分解を得て、batch++pending++arrivals(pre)=done++batch'++pending' と、matcher が done.foldl M.sRound x であることを保持する。残り suffix 内の部分周は実行したまま結論に残すため、zero lag は主張しない。`trace_cycle` は実入力 events(speed B) の任意 suffix に boundary_cycle と segment_shrink を直接適用し、次 batch 長≤pending.length+max(old.length,batch.length)/8+2 を証明した。既に phase 完了・一周時間の仮定はなく、boundary 配置と残 worker 予算だけを要求する。実 trace 上の連続周での定量的総時間上限、小さい backlog の排出、全体スケジュール・PAL 受理の統合は未完了。

旧 `FullMachineProg` と `StageLifecycleProg`、旧計画書は
[`archive/single-prog/`](archive/single-prog/README.md) に退避した。
これらは現役の `PalPeg` モジュールとビルド対象から外れている。
`FullMachineTapes` などの数学的な仕様や、現行コードが参照する補題は残している。
