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
