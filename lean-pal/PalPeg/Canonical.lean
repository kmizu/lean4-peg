import PalPeg.CloseoutFinalW
import PalPeg.CloseoutPackRun49
import PalPeg.CloseoutBundleRun
import PalPeg.CloseoutMismatchCompare
import PalPeg.CloseoutShiftRun
import PalPeg.CloseoutLandingRound
import PalPeg.CloseoutReadsOrigin
import PalPeg.CloseoutPackRefute
import PalPeg.CloseoutWatchShiftAudit
import PalPeg.CloseoutBudgetFree
import PalPeg.CloseoutRealize1
import PalPeg.CloseoutMarksFree
import PalPeg.CloseoutTickFalse
import PalPeg.PackedRun

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

`pal_in_peg_final30` は Prop 引数 8 本（`hSP` `hme` `hor` `hC` `hfour` `hbgP`
`hmatchP` `hsdP`）で、そのどれも反証されていない（確認したのは `final30` `final31`
`final33` `final36` `final37` の 5 本）。

**「8 が最小」とは主張しない。** `pal_in_peg_final*` は 47 本あり、全部の型を見ていない。
また Prop 引数の本数は前提の本数ではない（`∀ w, H_x w` は 1 本に見えて族、instance は
自動放電される）。数えるべきは **producer が無い前提**であり、それは型を見て初めて決まる。

計画書 §10.5（前提ゼロ）は未達。 -/

/-- **現時点の正本の最上位定理**（旧名 `pal_in_peg_final30`）。
Prop 引数 8 本、反証済みの前提を含まない。最小性は未検証。 -/
alias pal_in_peg_of_eight_leaves := PalPeg.CloseoutFinalW.pal_in_peg_final30

/-! ## 2. 反証済み — 使ってはいけない

`hpack : ∀ w c s, ChainPosInv2 w c s → ChainPack q first w c s` は**偽**。
`ChainPack` は run に沿って確立される束を一状態述語として書いており、3 場しかない
`ChainPosInv2` からは出ない。詳細は `REFUTATION_AUDIT.md`。 -/

/-- **`hpack` は偽**（無条件、証人構成込み）。 -/
alias refuted_chainPack_from_chainPosInv2 := PalPeg.CloseoutPackRefute.hpack_false

/-- **`ScanBudget` は偽**（同じ証人）。 -/
alias refuted_scanBudget := PalPeg.CloseoutPackRefute.scanBudget_false

/-- **`WatchShiftG` は偽**（`backDone` 着地で `periodLength = 0` と `≥ 1` を同時に要求）。 -/
alias refuted_watchShiftG := PalPeg.CloseoutWatchShiftAudit.watchShiftG_false_at_backDone

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

/-- **ラウンド束は run に沿って運ばれる**（`ChainPosInv2` は不要、`AuxPack` で足りる）。 -/
alias roundBundle_along_run := PalPeg.CloseoutBundleRun.roundBundle_steps_B

/-- **`ShiftPal` を run から出す**（残差は `H_readsShift` / `H_freshShift` / fresh 分岐）。 -/
alias shiftPal_from_run := PalPeg.CloseoutBundleRun.shiftPal_of_run_B

/-- **`CopyIdle` は `AuxPack` の場**（shift 相では copy 機構が idle）。 -/
alias copyIdle_at_shift_from_auxPack := PalPeg.CloseoutBundleRun.copyIdle_shift_of_auxPack

/-- **`H_readsShift` は read origin から出る。** -/
alias readsShift_from_readOrigin := PalPeg.CloseoutReadsOrigin.h_readsShift_of_originAt

/-- **`H_readsShift` の供給経路**（controller `Rounds` ＋ 第 1 ラウンドの `Entry`）。 -/
alias readsShift_from_rounds := PalPeg.CloseoutReadsOrigin.h_readsShift_of_rounds

/-! ## 5. ラウンド 1 周の部品（Round 30 の piece 1〜4） -/

/-- **piece 1**: 不一致比較は watch を保つ（終端では lag ゼロ）。 -/
alias mismatchCompare_keeps_watch := PalPeg.CloseoutMismatchCompare.compare_chain_of_mismatch

/-- **piece 1'**: その不一致比較を構成する。 -/
alias mismatchCompare_exists := PalPeg.CloseoutMismatchCompare.compare_mismatch_of_round

/-- **piece 2**: shift 入口を構成する。 -/
alias shiftEntry_exists := PalPeg.CloseoutMismatchCompare.beginShift_of_guard

/-- **piece 3**: `CopyIdle` は FPP 成分だけを読む。 -/
alias copyIdle_congr := PalPeg.CloseoutMismatchCompare.copyIdle_congr

/-- **piece 4**: `h` 単位の `ShiftRun` はラウンドから存在する。 -/
alias shiftRun_exists_from_round := PalPeg.CloseoutShiftRun.shiftRun_exists_round

/-- **`ShiftAtMismatchM` を運ばれる不変量だけから証明**。 -/
alias shiftAtMismatch_from_round := PalPeg.CloseoutMismatchCompare.shiftAtMismatchM_of_round

/-- **`WatchClosedC`**: 背景 tick は watch を watch に保つ。 -/
alias backgroundTick_keeps_watch := PalPeg.CloseoutMismatchCompare.watchClosedC_proved

/-- **背景 tick は lag ゼロなら恒等**（`WatchOk` 不要）。 -/
alias backgroundTick_is_identity_at_lagZero :=
  PalPeg.CloseoutMismatchCompare.chainTick_false_idle

/-- **`ChainOk` な chain から `.broken` への `ChainStep` は無い。** -/
alias step_never_breaks := PalPeg.CloseoutTickFalse.step_ne_broken

/-! ## 6. `LandingReadyC`（`hland`） -/

/-- **`LandingReadyC` を運ばれる事実から出す。** -/
alias landingReady_from_parts := PalPeg.CloseoutLandingRound.landingReadyC_of_parts

/-- **`ChainReady` はラウンドから出る。** -/
alias chainReady_from_round := PalPeg.CloseoutLandingRound.chainReady_of_round

/-- **`distance = radius`**（`SumRel` ＋ lag ゼロ ＋ unbroken）。 -/
alias distance_eq_radius := PalPeg.CloseoutLandingRound.distance_eq_radius_of_round

/-- **半径の非負性**は中心台帳 ＋ 走査不変量から。 -/
alias radius_nonneg := PalPeg.CloseoutLandingRound.radius_nonneg_of_ledger

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
