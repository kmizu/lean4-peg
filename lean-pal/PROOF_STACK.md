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
* `REFUTED` は `False` を導く機械検査済みの定理があるときだけ

---

## 現在のスタック（上が浅い）

```
[0] GOAL  PalPeg.PalInPeg.unconditional : RecognizedByTotalPEG PAL
          計器 = #print axioms。標準 3 公理だけになったら §10.5 達成
          いま 4 本:
            obligation_cycleOracle
            obligation_localRealization
            obligation_shiftPalResiduesAlongRun
            obligation_shiftPalResiduesAlongTrace

[1] obligation_shiftPalResiduesAlongTrace ＋ …AlongRun
          ※ 2 本あるが **中身は同内容**（量化が trace 形／run 形の違いだけ）。
            どちらも残差は次の 3 つ:
              (a) H_readsShift
              (b) H_freshShiftAtShiftEntry
              (c) FreshShiftLedger
            → (a)(b)(c) を潰せば公理 2 本が同時に落ちる。だからここを先に攻める

[2] (c) ShiftPalAlongTrace.FreshShiftLedger
          n141〜n144 で `periodOnly = false` ＋ watch の ShiftPal をこの 1 場に還元済み。
          中身は 7 連言で、3 種類:
            ① period テープの中身   : PalAt (encoded w) (pos−h) h ／ PalAt (encoded w) (pos−2h) (2h)
            ② 半径と周期の大小      : 0 < h ／ 2h ≤ r₀ ／ r₀ ≤ 4h ／ pos+r₀+1 < length
            ③ period テープの位相   : (encoded w)[pos+r₀+1−2h]? = symbol wch…period.focus

[3] ① の橋 — **済（pop）**
          `GalilScaffoldChainInputSupply.candidate_palAt`（`PalPeg/GalilCandidatePeriod.lean:45`）が
          **もう証明している**（標準 3 公理のみ）:

            (hc : GalilDpCorrect.Candidate ((stream ⟨a::ls,gap⟩).take (span+1)) lower h) :
              let C := position (represent ⟨a::ls,gap⟩ (rs.map some) q)
              PalAt (encoded ((a::ls).reverse ++ rs ++ q)) (C − h) h ∧
              PalAt (encoded ((a::ls).reverse ++ rs ++ q)) (C − 2h) (2h)

          ついでに `candidate_periodOn` が `PeriodOn (encoded …) (2h) (C−4h) C` も出す。
          **`first_round` の文脈で全部そろう**（`hcand` / `hcen0 : v0.center = cen` /
          `hcen : cen = represent …` / `hys : ys.length+1 = h`）。
          → CLAUDE.md「既にあるものを探す」の通りやった。新しい数学は要らんかった。

[4] `FreshShiftLedger` を **1 個の named fact に絞る**（← いまここ）
          ① が定理になったので、残差は「この状態の watch の周期が、この中心での
          DP の `Candidate` 由来である」という 1 場に絞れる。仮に `PeriodFromCandidate`:

            ∀ wch, s'.chain = .watch wch →
              ∃ a ls rs q gap span lower,
                w = (a::ls).reverse ++ rs ++ q ∧
                position s.center = position (represent ⟨a::ls,gap⟩ (rs.map some) q) ∧
                GalilDpCorrect.Candidate ((stream ⟨a::ls,gap⟩).take (span+1)) lower (periodLength wch)

          これがあれば ① は `candidate_palAt` で無償、② の `0 < h` は `Candidate` の
          `lower < h`（`lower` が 0 のときは別途）、`r₀ ≤ 4h` は Galil の move 不等式
          （`GalilMoveLemma.galil_move_of_contract`、CLAUDE.md 記載）、
          `2h ≤ r₀` は shift guard、`pos+r₀+1 < length` は `ScanInvariant` 側。
          残るのは ③（period テープの位相）。

          **既存の担い手候補**（未検証、次に読む）:
          * `CloseoutPackRun42.Extra4.cand` — `mode = shift` guard 付きで
            `∃ n lower h, Candidate ((stream (P.place x.vm)).take n) lower h`。
            ただし `h` を `periodLength wch` に縛っていない
          * `CloseoutFoundCompare:86,96` / `CloseoutFoundBackground:77,164` —
            found 経路で `Candidate` を出している。`periodLength` との結びつきを確認する
          * `CloseoutWatchRound5:452` / `CloseoutWatchRound10:333`
```

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
* その次: `scan_shift` tick から `CompareRounds h … 1 …` を組む
  （`GalilScaffoldTopRoundS.round_next` の入力をそろえる）→ `RoundSeg` →
  `originAt_of_roundSeg` で起点を貼り替え → `originShift_of_roundSeg` → `H_readsShift`

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
