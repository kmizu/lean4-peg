## 2026-09-19: Fable 5 向け引き継ぎ・inline 撤去後の checkpoint

ユーザー指示で未完成・未検証の cycle inline proof を撤去し、既存の2公理による
最終定理へ戻した。`CanonicalChainMinimal` の shift 最小性、search/chain readiness、
fallback/replay、および周期境界の証明は保持。cycle と local realization は未解消。

**次の作業で要確認:** Scala/Python は broken chain で search を restart するが、
Lean の `GalilTickFair.Canonical.noRestart` は禁止する。Python 正本の broken-restart
分岐だけを省いた実行で、入力 prefix `abaaaaababaaabaaaaabaaaaabaaaaabaaaa`、
centre=45、radius=25、fallback move=6、chain=broken を観測した。
従って、この実行では `radius ≤ 4*move` は不成立。これは Python 診断であって
Lean の packed-run 到達可能性の証明ではなく、cycle 公理そのものの反証とも断定しない。
この条件の相違を解決せず、残差を単なる接続作業と扱わないこと。

再現コマンド（Python のみ。Lean の証明ではない）:

```sh
python3 docs/palindromes-in-peg/diagnose_no_restart_fallback.py
```

Fable 5 への最初の確認事項:

- canonical/no-restart と broken restart の相違を精査し、`hmove` producer の
  仮定をそのまま証明する方針が妥当か判断する。上の観測だけで Lean の命題が
  偽だと断定しない。標準モデルの正しさとも混同しない。
- search/chain readiness、shift 最小性、fallback/replay の既存証明を再利用し、
  未検証の inline draft は復活させない。
- `obligation_localRealization` は具体的な有限局所機械・符号化が未構成。
  一意性や条件付き `realizes_canonical` を完成扱いしない。
- ユーザーの指示は、サブエージェントなし・不要な探索と補題追加なし。
  残りの証明はまず既存義務内へ直接書き、完成後に必要な補題を抽出する。


既存の `move_of_live_sem_packed` / `move_of_preShift_packed` の
`∀ h, MoveMinimal … h → rad ≤ 4*h` は一般には使えない強すぎる仮定。
`MoveMinimal … 0` は空虚に真なので、この全称仮定は `rad = 0` を強制する。
必要なのは実際に保持された周期の証人に結びついた bound / boundary-break の証明。

検証: checkpoint build / 公理監査は実行中。

> 追記（Codex、n264）: fallbackのコピー元の記述にも誤りがあった。
> Scalaは `walker.copyFrom(right)`。canonical条件とfallback葉は現在
> `u.fpp.walker = GalilTickFair.rightPlace u`。旧search cursorのpinとは違う。
> `fallback_right_not_searchPin` で両者の不一致をLean検査したが、これはPAL全体の反証ではない。

> 追記（Codex、n263）: oracleのoriginはbootから到達済みの状態に限定した。
> `CanonicalPeriod.packed_lower_zero` をoracle本体で使い、周期葉に `lower = reset` を供給。
> 下限以下の周期排除はゼロゆえ不要。DP Resultとwatchの接続・反復shift等は未解決。
> 2公理は残っており、originの制限による義務の弱化と、公理の証明は区別する。

> 追記（Codex、n262）: §3 の「非決定的な trace 全部との一致は原理的に不可能」という
> 診断は撤回。実現条件は **受理結果** の一致であり、状態列の一致ではない。
> `CloseoutFinalFour.latch_iff_pal_of_preTrace` で、`PreTraceB` と消費者の lookahead 条件から
> canonical 性なしに latch ↔ PAL を証明し、最終の組み立てに実際に使用した。
> 旧 `PreTraceB` だけの条件が真だと証明したわけではない。残る2公理は未解消。

> 追記（Codex、n261）: `tick_canonical_unique` は実装済み。新規
> `CanonicalLocalRealizes.lean` に `canonical_trunc` と `realizes_canonical` を追加。
> 残り2公理は未解消。検証の確定結果と残差は `PROOF_STACK.md` 先頭を参照。

# Codex への引き継ぎ（2026-09-19 夕方、Claude Fable 5.1 から）

対象: `lean-pal/`（`PAL ∈ PEG` の Lean 4 証明、v4.31.0 + Mathlib）。
branch: `feat/lean-pal-consume-avail`（main には PR で merge 済みのものが順次入っている）。

## 0. 一番大事なこと（3 行）

- **進捗の計器は `#print axioms PalPeg.PalInPeg.unconditional`**（`PalPeg/PalInPegUnconditional.lean`、guard は `PalPeg/Axioms.lean`）。標準 3 公理（`propext`／`Classical.choice`／`Quot.sound`）以外に **2 個の `axiom`** が残っている: `obligation_cycleOracleOnPackedRun` と `obligation_localRealization`。これが 0 になったら完了。
- **残りを「義務の切り方と配線だけ」と断定しない。** `hminv` の過剰量化や `hfallback` の量化子順序には修正があるが、`localRealization` が非決定性ゆえ不可能という診断は受理同値と状態一致の混同だった（n262で訂正）。具体的な局所機械・符号化と、oracleの4葉は依然として未構成。
- **やってはいけないこと**: `git reset --hard`／`git clean`、`lake build` の並列実行（メモリ kill）、公理を増やす、参照ゼロの定理やコピペ証明を残す、「REFUTED」を機械検査なしに書く。

## 1. 現在の状態（このファイル執筆時点）

| 項目 | 状態 |
|---|---|
| 最終定理 | `PalPeg.PalInPeg.unconditional : RecognizedByTotalPEG PAL`（閉じた項。witness は `given_scanLandingObligations 0 1 0 …`、`q = 1`） |
| 残る公理 | `obligation_cycleOracleOnPackedRun`（run 形の cycle oracle）／`obligation_localRealization`（局所実現） |
| 直近 commit（全体 build 済み） | `96c091f` n259（`hchain` の切り直し） |
| n260（canonical run の導入、§3） | `PackedRun`〜`PalInPegUnconditional` まで module 単位の build 成功、`#print axioms unconditional` は標準 3 公理＋上の 2 公理。全体 build の結果は PROOF_STACK.md の n260 を見よ |

`lean-pal/PROOF_STACK.md`／`lean-pal/ASSEMBLY_PLAN.md`／`CLAUDE_RESUME.md` の先頭に n252〜n259 のノートがある（新しい順）。各ノートは「公理への進捗」表と「全体 build 成功・標準公理のみ・無条件 PAL は未完」を書く決まり。

## 2. 公理 1: `obligation_cycleOracleOnPackedRun`

型（`PalInPegUnconditional.lean`）:
```
∀ w, 0 < w.length →
  CloseoutCheckW.CycleOracleOn centreC placeC entry q first
    (ScanOnPackedRunFromInvLPS centreC placeC entry q first) (GalilTickFair.Canonical entry 2048) w
```
意味: 運ぶ述語 `I := ScanOnPackedRunFromInvLPS`（`InvLPS` 起点からの packed run 上の非 replay な scan 状態、`Refreshed`、`MInv`、shaped run）を満たす状態から、次の報告点（`position right = 2m−1`）までの 1 cycle を `CostedRun` の台帳つきで構成し、着地でまた `I` を返す。

**producer**: `PalPeg.OracleReady.cycleOracleOn_of_readyLeaves`（標準公理のみ）。葉は 4 つ:

| 葉 | 文（要旨） | 帰着先 |
|---|---|---|
| `hfresh` | fresh restart（`Restarted w r Rad last ∧ StageEntry Rad last`、scan、clock = 2048）で `∃ n, CloseoutPreload39.ReadyFieldP3 n ⟨c, r⟩` | DP の較正。`CloseoutReadyStage.readyPacedS_restarted` で `RunEntriesS` に帰着。既存の入口定理 `readyField3_entry_of_datum` は `NoReturn`（1 stage 越えで偽）を取るので、stage ごとの帰納（`CloseoutPreload36.postRunC_galil_of_boot`／`StageChain`）に切り替える必要 |
| `hchain` | `InvLPS … c₀ r₀ → StepsIMWC … k ⟨c₀,r₀⟩ y → y.ctl.mode = .scan → ChainReady y.vm.chain` | `BranchSupply.chainVerifierSupply_alongTrace`（trace の scan 点で `VerRep ∧ LagCan`）と同型。`ChainReady` の 4 条件: `BlockInv`（`IPackMW.win.coupled.block` で無償）、copy の `∃ n, CopyInv`（誕生時 decode: `AnswerAheadDecode.copyInv_of_found` ＋ `copyInv_step`）、verifier の `canRight`（供給: `VerRep`/`LagCan`）、`Internal → canRight`（同じ供給） |
| `hshiftPeriodMinimal` | shift 入口（guard 立ち・不一致）で watch chain の周期 `periodLength wg` が `Span w C (n−C)` の最小周期: `∀ p, 0 < p → p < 2·periodLength wg → ¬ HasPeriod … p` | 誕生時 decode（`GalilMinimalPeriod.result_least`／`GalilSearchResult.search_result_at_tick`）を period テープに沿って運ぶ chain 不変量。`hchain` の copy 相と同じ起点データなので 1 本の不変量にまとめる |
| `hfallback` | 不一致・guard 下がりの源から `∃ u, beginFallback s1 u ∧ u.fpp.walker = GalilTickFair.rightPlace u ∧ ∃ c' s' kk r fb replay, StepsAllR … (Canonical) (fb+replay) … ∧ ShapedSteps … ∧ scan ∧ ¬replaying ∧ Refreshed ∧ MInv ∧ right+1 ∧ r ≤ kk ∧ centre + (kk+1−r) ∧ fb ≤ 12704·(kk+1−r)+4012 ∧ replay ≤ 8·2048·(kk+1−r)` | 本物の fallback 構成 `scan_fallback_cycle_All`／`fallback_restarted_soundNR`（右ヘッドから decode した非空 place を自分で選ぶ。側条件 `ShiftIdle`／`Canonical length`／`heven`／`0 < q`／`first ≠ 7, 8`）＋ replay 区間。`replay_segment_construct`／`match_round` は偽の `hpres`／`hquiet` を取るので `ReadyFieldP3` 版に切り直す。`minv_after_fallback`／`leftmost_after_fallback` で `MInv` |

oracle の本体: `PalPeg/OracleRun.lean`（`scanBackground_run`／`scanCompare_cases`／`scanCycle_of_leaves`／`cycleOracleOn_of_leaves`／`shiftUnits_S`／`shiftExit_S`／`shiftLeaf`／`cycleOracleOn_of_fourLeaves`）、`PalPeg/OracleReady.lean`（`hready` を `hfresh` から定理化）、`PalPeg/ReadyTransport.lean`、`PalPeg/ShapedRun.lean`。

## 3. 公理 2: `obligation_localRealization`（n260 で切り直し中）

旧: `CloseoutFinalW.H_realizeLIMW'` = `∃ 局所機械 M, ∀ w st Tc, PreTraceB → (M.SAccepts w ↔ LatchTrue st …)`。これは**受理結果**の一致であり、`Tick` の非決定性だけでは反証できない。n262 の `latch_iff_pal_of_preTrace` は `PreTraceB` に実際の消費者の lookahead 条件を加えると canonical 性なしに latch ↔ PAL を証明する。ただし旧条件には lookahead が明記されていないため、そのまま真だと証明したわけでもない。

新（n260）: `CloseoutFinalW.H_realizeCanonical` = 同じ ∃ だが `∀ st Tc, PreTraceIMW → CanonTrace entry w st Tc → (…)`。`CanonTrace` は各 tick が `GalilTickFair.Canonical entry 2048`（**restart しない**／fallback の place は右ヘッドをdecodeした `rightPlace`（n264で修正）／`init`・`replayStart` でカーソル保持）。`Tick ∧ Fair` が関数的（`tick_fair_unique`）なのと同様に `Tick ∧ Canonical` も関数的（restartを除外し、fallbackのコピー元を右ヘッドに固定。`tick_fair_scan_unique` の `hnr` 分岐がそのまま使える——**この一意性定理 `tick_canonical_unique` は n261 で証明済み**。`tick_scan_noRestart_unique` を共通核とし、`canonical_trunc` と `realizes_canonical` まで接続した）。

そのために oracle の run に tick 述語を載せた:
- `PalPeg/PackedRun.lean`: `StepsAllR F delay Q R`（`StepsAll` ＋ tick 述語）、`PackedRunR … R`、`stepsAllR_fn`／`canon_concat`／`PackedRunR.trans`／`toPacked`／`ofPacked`／`forget`／`pack_last`。
- `PalPeg/CloseoutCheckW.lean`: 汎用層（`ReachAtOn`／`CycleOutOn`／`CycleOracleOn`／`H_bootOn`／`checkpoints_costOn_upto1`／`preTraceOn_exists`）が `R` を取る。`StepsIMWR R`、`StepsIMWC := StepsIMWR (Canonical entry 2048)`、`CanonTrace`。旧 `InvLPS` インスタンス（`ReachAtIMW` 等）は `R := True` に固定して arity 不変。`preTraceOnPackedRun_exists` は `PreTraceIMW ∧ CanonTrace` を返す。
- `PalPeg/CloseoutMarksPack.lean`: `PackRunRMWR R`／`packRunR_MWR_marksFree`（tick 述語つき）。旧 `packRunR_MW_marksFree` はその `R := True` 系。
- `PalPeg/CloseoutOracleW.lean`: boot tick が canonical（`canonical_of_init`）。
- `PalPeg/OracleRun.lean`／`OracleReady.lean`: 全 run を `StepsAllR … (Canonical entry 2048)` に。各 tick の canonical 性は `canonical_of_scan_nonCopy`（restart でない＝`ShapedRun` の `hnr` から）／`canonical_of_scan_copy`（fallback 入口: 葉の `u.fpp.walker = GalilTickFair.rightPlace u`）／`canonical_of_offScan`（shift 相）。
- `PalPeg/CloseoutFinalFour.lean`: `given_preTraceIMW_on P`（trace 述語 `P` で一般化。旧 `given_preTraceIMW` は `P := True` の系）。`CloseoutFinalBranch.given_scanLandingObligations` は `P := CanonTrace entry`、`hC : H_realizeCanonical`。

**producer の残差**: `realizes_canonical` は局所 successor が canonical な抽象 tick を実現すると仮定して trace の successor との一致を示す。実際の局所 step、物理不変量、word-independent な有限テープ符号化を構成する必要は残る。`LocalLatchRealize.pal_in_peg_of_local_core` の `L0` / `enc_tick` / `enc_feed` は引数であり、完成済みの具体的機械ではない。また、この exact-tracking 経路だけが局所実現の証明方法とは限らない（n262）。

## 4. 使い方

```sh
cd lean-pal && . ~/.elan/env
lake build --quiet PalPeg > /tmp/b.log 2>&1; echo "BUILD=$?" >> /tmp/b.log   # 全体（10〜20 分）
lake build --quiet PalPeg.OracleRun                                          # 1 module（依存も build）
lake env lean PalPeg/X.lean                                                  # 既存 olean で 1 file だけ
# 公理チェック
cat > /tmp/ax.lean <<'EOF'
import PalPeg.PalInPegUnconditional
#print axioms PalPeg.PalInPeg.unconditional
EOF
lake env lean /tmp/ax.lean
```
- 新 module は `PalPeg/Workbench.lean` に import を足す（`sed -i "/^import PalPeg.OracleReady$/a import PalPeg.X"`）。ルート `PalPeg.lean` は触らない。
- 長い編集は python スクリプト（`sub1` で出現回数を assert）で。`Edit` の連打より事故が少ない。
- `BUILD=` 行だけを信じる。task の exit code や「通ったはず」は信じない。

## 5. 設計上の教訓（今日 3 回踏んだ）

**run 上でしか要らない事実を到達可能な全状態へ全称量化すると偽になる。** `hminv`（run 全点の `MInv`）は fallback 入口で偽（`CloseoutPackRun4.minv_false_at_mismatch` が核、`CloseoutLPack5.MInvG` で一度直した穴の再発）。直し方は「運ぶ述語 `I` の場にする」（`Refreshed`／`MInv` がそう）か「packed run の scan 状態だけ」に絞る（`hchain`）。葉を書く前に **消費者のその分岐で scope に何があるか**を読む。

**量化子の向き**: `hfallback` の旧形は `scanCompare_cases` が `beginFallback_exists`（空 place `⟨[], false⟩`）で選んだ任意の着地から完走せよ、だった。構成する側が選ぶものは `∃`。

**定数**: fallback 構成は `0 < q` を要る。最終 witness は `q = 1`（`first = 0`）。

**`Fair` と canonical**: Scala 正本は broken chain で即 restart するが、Lean の oracle は restart せず broken のまま次の fallback まで走る。これは機械の正当な実行（`ShapedRun` の docstring）。`Canonical` はその方針を tick 述語にしたもの。`Fair`（restart 優先）を要求すると readiness の `hrestart` 葉が復活するので選ばなかった。

## 6. 参照

- 正本の仕様: `scala/pal/src/main/scala/pal/ScaffoldGalil.scala`／`ScaffoldChain.scala`。
- 名前の索引（カーネル検査）: `PalPeg/Canonical.lean`。
- 反証済み・偽の疑いの記録: `CLAUDE.md`（lean-pal の節）と `PROOF_STACK.md`。
