import PalPeg.CloseoutFinalW
import PalPeg.CloseoutPackRun49
import PalPeg.CloseoutBundleRun
import PalPeg.CloseoutReadsOrigin
import PalPeg.CloseoutPackRefute
import PalPeg.CloseoutWatchShiftAudit
import PalPeg.CloseoutBudgetFree
import PalPeg.CloseoutRealize1
import PalPeg.CloseoutMarksFree
import PalPeg.PackedRun
import PalPeg.WatchOkRefute
import PalPeg.ChainStepGap
import PalPeg.CloseoutFinalFour
import PalPeg.ConsumeAvailRefute
import PalPeg.BranchSupply
import PalPeg.AuxPackNotAtBoot

/-!
# Canonical — 意味のある名前で正本部品を再輸出する

## なぜこのファイルがあるか

`PalPeg/` は 1142 ファイル・33 万行あり、定理名の多くが **`final24` … `final37`、
`PackRun49`、`WatchRound53`、`Oracle8`、`Preload41` のように「いつ書いたか」を
符号化していて「何であるか」を符号化していない**。そのため必要な部品を意味から
引けず、番号を覚えているかどうかに依存する。実際に取り落とした：

- `CloseoutPackRun49`（`LPackM3`: 中心台帳を run に沿って運ぶ）は未登録のまま放置され、
  「中心台帳は `ChainPack` にしか無い」という誤った記述を書いた。
- `CloseoutWatchRound53` はエラー 0・sorryAx 0 で無傷なのに 1 本も使われていなかった。
- `CloseoutTerminalN.roundStepC_of_alignN` / `CloseoutMarksFree.marks_steps_free` は
  既に存在したのに「配線が必要」と書いた。

`PART_INDEX.md` も作ったが、**markdown の索引は黙って腐る**（今日それで失敗した）。
このファイルは**カーネルが検査する索引**である：名前が動けば build が壊れる。

## 命名方針

- 番号を名前に入れない。**何であるか**を書く。
- 正本（canonical）とは「反証済みの前提を含まない経路」のこと。
- 反証済みのものは `refuted_` を前置して、使ってはいけないことを名前で示す。

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

namespace PalPeg.Canonical

/-! ## 1. 最上位

**正本の最上位は `given_globalScanLandings`（`CloseoutFinalFour`）で Prop 引数 7 本**
（`hSP` `hme` `hor` `hC` `hbgP` `hmatchP` `hsdP`）。`final30` の 8 本から
`hfour : ∀ w, H_FourSemiperiodsLeDistance …` が**何も足さずに**落ちたもの（`CloseoutPackRun40.ChainPositionInvariantExactCoupling`
＝ `Coupled` を `Coupled'` に強めた構造が `four_of_other'` を直接使えるため。
`ShiftLocalRun` が run に載せている）。反証済みの前提は含まない。

`hfour` を落とした既存の 3 版はどれも代わりに**偽の前提**を取っていた:
`final31` は `hav`（`ConsumeAvailRefute.hav_false`）、`final36`/`final37` は `hpack`
（`CloseoutPackRefute.hpack_false`）。型を見ずに前提数だけ比べてはならない。

**「8 が最小」とは主張しない。** `pal_in_peg_final*` は 47 本あり、全部の型を見ていない。
また Prop 引数の本数は前提の本数ではない（`∀ w, H_x w` は 1 本に見えて族、instance は
自動放電される）。数えるべきは **producer が無い前提**であり、それは型を見て初めて決まる。

計画書 §10.5（前提ゼロ）は未達。 -/

/-! **無条件の最終定理 `pal_in_peg : RecognizedByTotalPEG PAL` はまだ存在しない。**
`pal_in_peg` という名前はそれ専用に予約する。前提を取るものは
`given_<残差>` と名付け、名前だけで「何を仮定すれば到達するか」が読めるように
する（コウタ 2026-09-19:「本来の定理は pal_in_peg やん。その到達のための partial な
ものなら適切な名前がある」）。

現時点で前提が最少かつ反証済みを含まないのは
`PalPeg.CloseoutFinalFour.given_globalScanLandings`
（`hSP` `hme` `hor` `hC` ＋ global な `H_BackgroundLandingPayload` / `H_MatchLandingPayload` / `H_ShiftExitPayload`）。
一代前は `PalPeg.CloseoutFinalW.given_globalScanLandings_and_fourOther`。
本数で別名を付けるのはやめた（「7」「8」は名前から意味が引けない）。 -/

/-- **最上位の組み立ての共通部分**（旧名 `given_needBound`）。`needL'` の上界を
外から取る 45 行で、`final5MW` / `5MW2` / `5MW3` / `5MW4` はこれの instantiation。 -/
alias top_assembly_from_need_bound := PalPeg.CloseoutFinalFour.given_needBound

/-- **`needL'` の上界は run 沿いの `ShiftLocalS` だけから出る**
（旧名 `needBound_of_shiftLocalS_alongTrace`）。`RadPack` → `TrailF` → `needL'` の 3 段を
4 回書いていたコピペ（S / S3 / S4）の共通部分。 -/
alias need_bound_from_shiftLocal_run := PalPeg.ShiftLocalRun.needBound_of_shiftLocalS_alongTrace

/-- **`hfour` 抜きで run 沿いに `ShiftLocalS`**（旧名 `shiftLocalS_alongRun_of_chainPosInvCoupled'`）。
分岐前提は `H_BackgroundLandingPayload` / `H_MatchLandingPayload` / `H_ShiftExitPayload` の 3 本のみ。 -/
alias shiftLocal_along_run_without_four := PalPeg.ShiftLocalRun.shiftLocalS_alongRun_of_chainPosInvCoupled'

/-- **4 分岐義務の状態局所版**（旧名 `CloseoutPackRun41.chainPosInv2_tick_of_landingObligationsAt`）。
`H_BackgroundLandingChainLedger` / `H_MatchLandingChainLedger` / `H_ShiftEntryChainLedger` / `H_ShiftExitRadiusLedger` は
`chainPosInv2_tick` の中で**その `(c, s)` でしか使われない**ので、束 `LandingObligationsAt` に
局所化できる。これが run 形化の入り口。 -/
alias chainPosInv2_tick_local := PalPeg.CloseoutPackRun41.chainPosInv2_tick_of_landingObligationsAt

/-- **4 分岐義務の run 形**（旧名 `BranchSupply.chainPosInv2_alongRun`）。
`∀ c s` の形では放電できない（材料の `LPackM2.shiftGeom`・chain 側台帳 `ChainPositionLedger`・
入力供給はいずれも run に沿ってしか存在しない）。global → run 形は一方向
（`BranchSupply.landingObligationsAlongRun_of_globalHypotheses`）。 -/
alias chainPosInv2_along_run := PalPeg.BranchSupply.chainPosInv2_alongRun

/-- **`needL'` の上界を run 形の義務から**（旧名 `BranchSupply.needBound_of_landingObligationsAlongRun`）。 -/
alias need_bound_from_branch_run := PalPeg.BranchSupply.needBound_of_landingObligationsAlongRun

/-- **`shiftDone` 義務の半径台帳はタダ**（旧名 `BranchSupply.radiusLe_of_radLedger`）。
`RadLedger.le`（`position center + value radius ≤ position right`）と
`ScanInvariant.rightPos` だけ。`RadLedger` は `CloseoutLPack6.radLedger_pt` が
`PreTrace` ＋ `LeftLive` だけで trace の全点に与える。 -/
alias radius_ledger_is_free := PalPeg.BranchSupply.radiusLe_of_radLedger

/-- **`init` へ戻る `Tick` 構成子は無い**（旧名 `BranchSupply.tick_target_mode_ne_init`）。
`Tick`（`GalilScaffoldTop:109`）の全構成子の行き先 mode は scan/shift/copy/home/fpp/
markEnd/choose/rewind/replayStart か「変えない」。だから trace は 1 手目以降 `init` に
戻らず、`GalilTrailRad.frontPack_trace` が trace の各点で使える。 -/
alias tick_never_enters_init := PalPeg.BranchSupply.tick_target_mode_ne_init

/-- **右ヘッドは trace 全域で `2|w| − 1` 以下**（旧名 `BranchSupply.rightHeadPos_le_alongTrace`）。
終端の報告点（`ReportPointAt.atPrefix`）から front ポテンシャルの単調性で後ろ向きに
伝播する。これが `canRight` の源。 -/
alias right_head_bounded_along_trace := PalPeg.BranchSupply.rightHeadPos_le_alongTrace

/-- **shift 相の `canRight` はタダ**（旧名 `BranchSupply.shiftRightHeadCanRight_alongTrace`）。
trace 予算 ＋ `LPackM2.shiftGeom` の `RRep`。新規入力ゼロ。 -/
alias shift_canRight_is_free := PalPeg.BranchSupply.shiftRightHeadCanRight_alongTrace

/-- **`canRight` は trace の 1 手目以降タダ**（旧名 `BranchSupply.rightHeadCanRight_alongTrace`）。
右ヘッドが入力を表現していればよい。scan 相版は `scanRightHeadCanRight_alongTrace` で、
これは `CloseoutPackRun46.Extra7.scanAvail`（＝ `hee` / `het` の中身）そのもの。 -/
alias canRight_is_free_along_trace := PalPeg.BranchSupply.rightHeadCanRight_alongTrace

/-- **scan 相の `canRight`（`Extra7.scanAvail`）はタダ**
（旧名 `BranchSupply.scanRightHeadCanRight_alongTrace`）。 -/
alias scan_canRight_is_free := PalPeg.BranchSupply.scanRightHeadCanRight_alongTrace

/-! ## 2. 反証済み — 使ってはいけない

`hpack : ∀ w c s, ChainPositionInvariantWithShiftPhase w c s → ChainPack q first w c s` は**偽**。
`ChainPack` は run に沿って確立される束を一状態述語として書いており、3 場しかない
`ChainPositionInvariantWithShiftPhase` からは出ない。詳細は `REFUTATION_AUDIT.md`。 -/

/-- **`hpack` は偽**（無条件、証人構成込み）。 -/
alias refuted_chainPack_from_chainPosInv2 := PalPeg.CloseoutPackRefute.hpack_false

/-- **`ScanBudget` は偽**（同じ証人）。 -/
alias refuted_scanBudget := PalPeg.CloseoutPackRefute.scanBudget_false

/-- **`WatchShiftG` は偽**（`backDone` 着地で `periodLength = 0` と `≥ 1` を同時に要求）。 -/
alias refuted_watchShiftG := PalPeg.CloseoutWatchShiftAudit.watchShiftG_false_at_backDone

/-- **`WatchOk` は偽**（無条件）。`born` が任意 lag で `Ok` を与え、`good` がその正 lag で
period と入力の一致を強制するが、`born` の仮説は両者を関係づけない。
**帰結**: `ChainTickable` を `ChainOk`＋`WatchOk` 上に載せ替える道は閉じた。`hready` を
消すには `ChainOk` を `.copy`/`.back` で lag/margin を縛る形に再設計する必要がある。 -/
alias refuted_watchOk := PalPeg.WatchOkRefute.watchOk_false

/-- **`ConsumeAvail` を全状態に量化した前提は偽**（`final31` の `hav`）。
`hav : ∀ w st i, ConsumeAvail (st i).vm.chain` は `st` が無制約関数なので
`∀ z : ChainVM, ConsumeAvail z` と同値で、`gap = false` かつ右も incoming も空な
verifier を持つ watch 状態で破れる。**帰結**: `given_consumeAvailEverywhere_FALSE_HYP` は無価値。
正しい形は `CloseoutVerSide.VerRun`（run 形）。 -/
alias refuted_consumeAvail_universal := PalPeg.ConsumeAvailRefute.hav_false

/-- **`AuxPack` は boot では偽**（旧名 `AuxPackNotAtBoot.not_auxPack_at_boot`）。
`AuxPack.front.notInit : c.mode ≠ Mode.init` と `initial delay` の mode が衝突する。
**帰結**: `CloseoutPackRun49.lpackM3_steps` は全点の `AuxPack` を要求するので
**boot 根の trace には適用できない**（`hLv 0` が充足不能）。`LPackM3` を運ぶなら
添字を `1 ≤ i` に制限するか、cycle 起点（`InvLPC` の scan 状態）から運ぶ。 -/
alias auxPack_is_false_at_boot := PalPeg.AuxPackNotAtBoot.not_auxPack_at_boot

/-- **モデル欠陥 `M-watchBreak`**（`WatchOk` が偽である根本原因）。
Scala 正本の `ScaffoldChain.step()` は `Mode.Watch` かつ正 lag で `consume()` を呼び、
不一致なら `Mode.Broken` に落とす。Lean の `ChainStep` には `.watch → .broken` の
構成子が無く（`ChainMatched.breaks` は `BreakStep` が `zero lag` を要求するので
lag ゼロ経路のみ）、その結果**正 lag ＋ 不一致の watch に後続状態が存在しない**。
だから正 lag の背景遷移は `Internal.take`（`Good` 必須）しかなく、`WatchOk.good` が
「予測は常に当たる」と主張することになっていた。 -/
alias model_gap_watchBreak_closed := PalPeg.ChainStepGap.chainStep_exists_at_positive_lag_mismatch

/-! ## 3. run に沿って運ばれる左パック（偽の `ChainPack` の代替）

`LPackM3 = LPackM2 ∧ (scan → CentreLedger) ∧ LagCan`。boot で成立し、tick で保存され、
`MatchRes2` と `CentreLedger` を与える。 -/

/-- **左パックは boot で成立する。** -/
alias leftPack_holds_at_boot := PalPeg.CloseoutPackRun49.lpackM3_boot

/-- **左パックは 1 tick 保存される。** -/
alias leftPack_survives_tick := PalPeg.CloseoutPackRun49.lpackM3_tick

/-- **左パックは run に沿って運ばれる。** -/
alias leftPack_along_run := PalPeg.CloseoutPackRun49.lpackM3_steps

/-- **中心台帳は左パックの場**（「`ChainPack` にしか無い」は誤りだった）。 -/
alias centreLedger_from_leftPack := PalPeg.CloseoutPackRun49.centreLedger_of_lpackM3

/-- **`MatchRes2` を偽の `ChainPack` 経由でなく出す。** -/
alias matchRes2_from_leftPack := PalPeg.CloseoutPackRun49.matchRes2_of_lpackM3

/-! ## 4. `hSP`（`ShiftPal`）の鎖 -/

/-- **ラウンド束は idle chain で成立する**（cycle の `InvLPC` 起点）。 -/
alias roundBundle_holds_at_idle := PalPeg.CloseoutBundleRun.roundBundle_of_idle

/-- **ラウンド束は run に沿って運ばれる**（`ChainPositionInvariantWithShiftPhase` は不要、`AuxPack` で足りる）。 -/
alias roundBundle_along_run := PalPeg.CloseoutBundleRun.roundBundle_steps_B

/-- **`ShiftPal` を run から出す**（残差は `H_readsShift` / `H_freshShift` / fresh 分岐）。 -/
alias shiftPal_from_run := PalPeg.CloseoutBundleRun.shiftPal_of_run_B

/-- **`CopyIdle` は `AuxPack` の場**（shift 相では copy 機構が idle）。 -/
alias copyIdle_at_shift_from_auxPack := PalPeg.CloseoutBundleRun.copyIdle_shift_of_auxPack

/-- **`H_readsShift` は read origin から出る。** -/
alias readsShift_from_readOrigin := PalPeg.CloseoutReadsOrigin.h_readsShift_of_originAt

/-- **`H_readsShift` の供給経路**（controller `Rounds` ＋ 第 1 ラウンドの `Entry`）。 -/
alias readsShift_from_rounds := PalPeg.CloseoutReadsOrigin.h_readsShift_of_rounds

/-! ## 5. ラウンド 1 周の部品（Round 30 の piece 1〜4）

n250 で削除。round 塔（`CloseoutWatchRound*`／`CloseoutMismatchCompare`／`CloseoutTickFalse`／
`CloseoutLandingRound`）はモデル欠陥 `M-watchBreak` の上でだけ真だった補題（`WatchClosedC` 等）を
含み、`unconditional` の閉包外なので build から外した。 -/


/-! ## 7. `ScanBudget` の producer（偽だった場に本物の供給元） -/

/-- **run の出口上界を遡らせて区間予算を出す**（`Extra7` から `hee`/`het` を消したのと同じ機構）。 -/
alias scanBudget_from_run := PalPeg.CloseoutBudgetFree.scanBudget_of_front_run

/-! ## 8. `hme`（marks）と `hC`（局所実現） -/

/-- **`H_marksEntry'` は不要**: marks は run に沿って運ばれる（残差は `WindowInOrigin`）。 -/
alias marks_along_run_without_entry := PalPeg.CloseoutMarksFree.marks_steps_free

/-- **`hC` の `LocalStep` 証人は付随的**: 任意の厳密実時間 `StructuredMachine` で足りる。 -/
alias realize_is_machine_generic := PalPeg.CloseoutRealize1.h_realizeSMG2'_of_LIMG2'

/-! ## 9. 括り出した汎用部品

pack を各点で運ぶ有限 run。`StepsI` / `StepsIM` / `StepsIMW` / `StepsIMG` /
`StepsIMG2` / `StepsIO` の共通形で、`*_trans` 6 本と `*_of_*` 3 本の共通部分を
ここに集約した（`PalPeg/PackedRun.lean`、`GalilCheckpoints` だけに依存、σ 一般）。
**pack の変種を新しく作るとき、連結と弱化を書き直さない。** -/

/-- **pack を各点で運ぶ有限 run**（`Steps*` 族の共通形）。 -/
alias packed_run := PalPeg.PackedRun

/-- **pack つき run は連結できる。** -/
alias packed_run_trans := PalPeg.PackedRun.trans

/-- **pack は弱めてよい。** -/
alias packed_run_weaken := PalPeg.PackedRun.mono

end PalPeg.Canonical
