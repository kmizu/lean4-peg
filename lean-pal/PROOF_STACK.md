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

## 現在のスタック（上が浅い）

```
[0] GOAL  PalPeg.PalInPeg.unconditional : RecognizedByTotalPEG PAL
          計器 = #print axioms。標準 3 公理だけになったら §10.5 達成
          **いま 3 本（2026-09-19 n175 で 4 → 3）**:
            obligation_cycleOracle
            obligation_localRealization
            obligation_shiftPalResiduesAlongRun

[済] obligation_shiftPalResiduesAlongTrace — **公理から外れた（n175）**
          trace は st 0 = boot w から始まるので st 1 で InvLPC が立ち、
          trace 形は run 形の特殊化になる。既存部品だけで繋がった:
            GalilTrailFront.inv_of_boot_tick / GalilOracleDischarge.invS_of_inv /
            GalilGlueBLeaves.entryCounters_of_inv / GalilOracleMC2.invLPC_of_boot /
            GalilInvPlus2.centreRep_of_restarted / GalilTrailFront.steps_between
          recipe は BranchSupply.cpack_alongTrace にそのまま書いてあった。
          **新しい定理は 1 本も書いていない。**

[1] obligation_shiftPalResiduesAlongRun（← 次の的）
          ∀ w c r, InvLPC w c r → ∀ Steps から届く z について
            (a) H_readsShift w z.ctl z.vm
            (b) H_freshShiftAtShiftEntry …（tick 形）
            (c) FreshShiftLedger w z.vm s'（periodOnly = false 点）
          (a) の機械は PalPeg/RoundHistory.lean（35 宣言）で完成。
          残りは first_round の 30+ 仮説を run から供給する配線（found 経路）。
          **その前に (b)(c) の producer を探す**——n175 の教訓（書く前に探す）。

[2] obligation_cycleOracle    — CycleOracleMC3。葉は CLAUDE.md §3 に 11 個
[3] obligation_localRealization — H_realizeLIMW'。壁は n174（run 機構が fairness を捨てている）
```

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

**全体 build 成功・標準公理のみ・無条件 PAL は未完（公理 4 本）。**
