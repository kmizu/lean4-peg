# 証明スタック（今どこにいるか）

**運用（コウタの指示 2026-09-19）**: 追っている前提を push（このファイルに書く）、
そこからサブ定理に潜るときも push、解けたら pop。**これで自分がどこにいるか忘れない。**

規律（CLAUDE.md より、ここでも効く）:
* **公理の本数は増やさない。** 難しいときはサブ前提を定理として証明し、公理の文を弱める
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

[3] ① の橋（← いまここ）
          DP の GalilDpCorrect.Candidate は **stream の take/reverse 形**:
            Candidate v lower h := lower < h ∧ 4h+1 ≤ v.length ∧
              (v.take (2h+1)).reverse = v.take (2h+1) ∧ (v.take (4h+1)).reverse = v.take (4h+1)
          欲しいのは Manacher.PalAt (encoded raw) 形。**同型の前例がある**:
            GalilFallbackLanding:63 / GalilInvPlus:159 / GalilLeafFb:353 …
            は chosenRadius について
              Manacher.PalAt (encoded raw) (position (right s.right) − chosenRadius (…take (ℓ+1)))
                             (chosenRadius (…take (ℓ+1)))
            を実際に出している（producer は GalilScaffoldChainFallback.fallback_replay）。
          → **同じ道具で Candidate の 2 回文も PalAt に写せるはず。** 次の一手はここ。
```

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
