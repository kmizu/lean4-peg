import PalPeg.PalInPeg
import PalPeg.BranchSupply
import PalPeg.ShiftPalAlongTrace

/-!
# `PalInPeg.unconditional` — 目標そのもの。穴は `axiom` で明示する

**これが目標の形**: `RecognizedByTotalPEG PAL` を**前提ゼロ**で（＝閉じた項として）持つ。
いま足りない 8 個の原子的な義務を `axiom` として明示し、`#print axioms unconditional` を
そのまま TODO リストにする。

```
#print axioms PalPeg.PalInPeg.unconditional
-- 標準 3 公理（propext / Classical.choice / Quot.sound）だけになったら証明完了
```

`PalPeg/Axioms.lean` に `#guard_msgs in #print axioms unconditional` を置いてあるので、
**1 個外すたびに guard が壊れて更新を強制される**（ラチェット）。逆に、うっかり
新しい穴を開けても guard が壊れるので気づける。

コウタの指示（2026-09-19）:
* 「unconditional はつくっておいて、前提の and でうめりゃいいのでは。その前提を
  いったん axiom にしといて外していく」
* 「トップダウンにまずそれを書いておいてビルド通すために前提をいったん axiom に
  しておく。で、検証したい前提ごとに axiom をはずして全部外せたら証明完了」

## 4 個の原子的義務と、それぞれの経路

**この表は `axiom` 宣言（`:85` / `:96` / `:104` / `:109`）と一致していなければならない。**
2026-09-19（n126）に**この docstring が腐っていた**のを直した——表は 9 行あったが
`axiom` 宣言は 4 本で、`obligation_verifierRunAlongRun` / `matchLanding_alongTrace` /
`shiftEntryLanding_alongTrace` / `chainBackLag_alongTrace` / `shiftExitLedger_alongTrace` /
`rewindMargin_alongTrace` の 6 行は既に存在しない公理を載せたままだった。
CLAUDE.md（`4 個`）と `#print axioms` は一致していたので、**ズレていたのはここだけ**。
CLAUDE.md の「ファイル自身の docstring も一次情報ではない」に自分で引っかかった。
**数えるときは `grep "^axiom " PalPeg/PalInPegUnconditional.lean` か `#print axioms`。**

| axiom | 内容 | 経路と残り |
|---|---|---|
| `obligation_shiftPalAlongRun` / `obligation_shiftPalAlongTrace` | scan 状態で `ShiftPal`（run 形／trace 形） | `ShiftPalAlongTrace.shiftPal_alongTrace` と `CloseoutBundleRun.shiftPal_of_run_B`。残差はどちらも `H_readsShift`（←`RoundSegFromRun.readsShift_at_actual`）＋ `H_freshShiftAtShiftEntry`（←`first_round`）＋ `periodOnly = false` 分岐 |
| `obligation_cycleOracle` | `CycleOracleMC3` | `CloseoutOracleBridge.hor_of_H_oracle` ＋ `CloseoutOracle8.h_oracle_of_leaves7`。11 葉（CLAUDE.md §3） |
| `obligation_localRealization` | `H_realizeLIMW'`（局所実現） | **producer なし**（5 機械の鎖の 2→3 段）。難易度は宣言しない——`LagCan` / `CentreRep` と同じ「切り方の誤り」の可能性が高い |

### 公理としては消えた 6 本（経路メモは残す）

`#print axioms` にはもう出てこない。下は当時の経路メモで、**現状の義務ではない**。

| 旧 axiom | 内容 | 当時の経路メモ |
|---|---|---|
| `obligation_verifierRunAlongRun` | `VerRun`（verifier が入力を表現、lag 正規） | `chainPos_step_of_supply` が要求する 4 局所事実の残り 2 つ。`ConsumeAvail` の全状態版は偽（`ConsumeAvailRefute.hav_false`） |
| `obligation_matchLanding_alongTrace` | `scan_match` 着地 | `CloseoutPackRun49.matchRes2_of_lpackM3`（`LPackM3` は §5e で運べる）＋ `h_matchP2_of_target`。残差は `MatchRest` の 3 場: `repV`（←`VerRun`）/ `repVmid`（verifier 1 歩先、`right_word` で出るはず）/ `replayPay`（replaying 時の payload）。`canRNext` は**反証済みで削除**（`MatchRestRefute`） |
| `obligation_shiftEntryLanding_alongTrace` | `scan_shift` 入口 | `beginShiftVM'` は `immediate`（1 consume）を当てる。`ShiftPhaseChainLedger` の確立 |
| `obligation_chainBackLag_alongTrace` | chain `.back` 相の lag 形状 | **producer なし**。`LagCan` は `.watch` 相のみ。`.back` は `ChainStep.copyEnd` が `.copy` の lag を持ち込むところで確立される。`CloseoutChainPack` / `CloseoutChainSideR` に同名の場があるのでその証明を参照 |
| `obligation_shiftExitLedger_alongTrace` | `shift_done` での `CentreLedger` | 3 節のうち `canRight center` / `Sane center` は §5b でタダ。残るは等式 `radiusExact`。scan 状態では `LPackM3` からタダなので、**shift 相へ運ぶ**のが仕事: `beginShiftVM` は center/radius/right を触らず（§5d）、`shiftTick` は center +1・radius −1・right 不変で保存する。side condition は `canRight s.center`（shift 相では `CentreRep` が無いので要調達）と `0 < value s.radius`（`RadLedger.shiftBud` ＋ `remainingPos` から出る） |
| `obligation_rewindMargin_alongTrace` | rewind 相の `2 ≤ position left` | **producer なし**。`LPackM2.centreOrder` は `position left ≤ position center`（上界）なので別物。CLAUDE.md は「`CentreMargin` 1 葉に集約」と記録 |

### 放電済み（この近傍のタダ飯）

`bg` 場（`scan_wait`/`scan_count` 着地）、`shift_done` の半径上界と `canRight`、
`Extra7.scanAvail`（＝`hee`/`het`）、`AuxPack`（1 手目以降）、`LPackM3` の運搬、
`LTickLeaves3.initLedger` / `.replayLedger`、`CentreLedger` の `canRight`/`Sane` 2 節、
`CentreLive`、`FrontPack`、`Coupled`、`CopyPack`。

**無条件 PAL は未完。計画書 §10.5（前提ゼロ）は未達。**
-/

set_option autoImplicit false

namespace PalPeg.PalInPeg

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply PegSeparation
open PalPeg.GalilFinalAssembly2 PalPeg.GalilRunSkeleton PalPeg.GalilInvPlus3
open PalPeg.CloseoutPackW PalPeg.CloseoutPackRun26 PalPeg.CloseoutPackRun29
open PalPeg.CloseoutPackRun16 PalPeg.CloseoutFinalW PalPeg.CloseoutPackRun34
open PalPeg.GalilFinalAssembly (boot)

/-! ## 未証明の義務（外すべき `axiom`）-/

/-! **2026-09-19（n112）: 旧 `obligation_shiftPalAtScanStates` は偽の疑いが濃かったので
差し替えた。**

旧版は一状態述語の形

    ∀ w x, BigPack2MG7W … w x → ScanNR x → ShiftPal … w x.vm

で、`ShiftPal` の結論「chain の周期が入力語 `w` の本物の周期である」という**履歴の
事実**を要求していた。`BigPack2MG7W` の場を一次情報で全部展開すると、chain の周期
テープの中身と `w` を結びつける場が 1 つも無い（`w` に触れる場はヘッド、chain に
触れる場はカウンタ）。`hpack` が偽だったのと同じ欠陥。**機械検査した反証はまだ無いので
`REFUTED` とは書かない**が、そのままにはできないので run 形／trace 形の 2 つに割った。

どちらも履歴が run で固定されるので、この欠陥は無い。放電器も用意してある:
`ShiftPalAlongTrace.shiftPal_alongTrace`（trace 形）と
`CloseoutBundleRun.shiftPal_of_run_B`（run 形）で、残差はどちらも
`H_readsShift` ＋ `H_freshShiftAtShiftEntry` ＋ `periodOnly = false` 分岐の 3 つ。
`H_readsShift` は `RoundSegFromRun.readsShift_at_actual` が実状態で出す。

**数は 1 → 2 に増えた。偽の疑いが濃い前提を 1 個持つより、真であろう前提を 2 個持つ方を
採った**（CLAUDE.md「偽の前提で数字を作らない」）。 -/

/-- **(OBLIGATION)** `InvLPC` 起点から到達する scan 状態で `ShiftPal`（run 形）。 -/
axiom obligation_shiftPalAlongRun (entry q : ℕ) (first : Fin 9) :
    ∀ (w : List (Fin 2)) (c : GalilScaffoldController.Control) (r : GalilVM),
      PalPeg.GalilInvPlus2.InvLPC w c r →
      ∀ (m : ℕ) (z : GalilScaffoldTop.State GalilVM),
        Steps (galilFrameS (PofC centreC placeC entry w) q first) 2048 m ⟨c, r⟩ z →
        ScanNR z → ShiftPal centreC placeC entry q first w z.vm

/-! ### trace 形 `ShiftPal` の 3 原子（n132 で `obligation_shiftPalAlongTrace` を割った）

`PreTraceIMW` を仮説に入れるのは必須。入れないと `st` が無制約関数になって
`∀ z, … → ShiftPal z.vm` と同値に潰れる（`hav` が偽になったのと同じ形）。 -/

/-- **(OBLIGATION)** trace の各点で `H_readsShift`（shift 相のラウンド読み出し）。
`obligation_shiftPalAlongTrace` を原子に割った 1 本目。
producer の候補は `RoundSegFromRun.readsShift_at_actual`。 -/
axiom obligation_readsShiftAlongTrace (entry q : ℕ) (first : Fin 9) :
    ∀ (w : List (Fin 2)) (st : ℕ → GalilScaffoldTop.State GalilVM) (Tc : ℕ → ℕ),
      PalPeg.CloseoutCheckW.PreTraceIMW centreC placeC entry q first w st Tc →
      ∀ j, 1 ≤ j → j ≤ Tc w.length →
        PalPeg.CloseoutRoundUnique.H_readsShift w (st j).ctl (st j).vm

/-- **(OBLIGATION)** trace の各 tick で `H_freshShiftAtShiftEntry`（shift 入口の最初のラウンド）。
原子 2 本目。producer の候補は `GalilScaffoldTopFirstRound.first_round`。 -/
axiom obligation_freshShiftAtShiftEntryAlongTrace (entry q : ℕ) (first : Fin 9) :
    ∀ (w : List (Fin 2)) (st : ℕ → GalilScaffoldTop.State GalilVM) (Tc : ℕ → ℕ),
      PalPeg.CloseoutCheckW.PreTraceIMW centreC placeC entry q first w st Tc →
      ∀ j, 1 ≤ j → j < Tc w.length →
        PalPeg.CloseoutPackRun37.H_freshShiftAtShiftEntry centreC placeC entry q first w
          (st j).ctl (st j).vm (st (j+1)).vm

/-- **(OBLIGATION)** `periodOnly = false`（＝chain 誕生後まだ shift していない）点での
`ShiftPal`。原子 3 本目。`periodOnly = true` 側は `shiftPal_of_chainRound` が閉じている
ので、残るのはこの分岐だけ。 -/
axiom obligation_shiftPalAtFreshWatchAlongTrace (entry q : ℕ) (first : Fin 9) :
    ∀ (w : List (Fin 2)) (st : ℕ → GalilScaffoldTop.State GalilVM) (Tc : ℕ → ℕ),
      PalPeg.CloseoutCheckW.PreTraceIMW centreC placeC entry q first w st Tc →
      ∀ j, 1 ≤ j → j ≤ Tc w.length → (st j).vm.periodOnly = false →
      ∀ wv : GalilScaffoldChainWatch.State, (st j).vm.chain = ChainVM.watch wv →
        ShiftPal centreC placeC entry q first w (st j).vm

/-- **もう公理ではない。**  chain が watch でない点では `ShiftPal` は空虚
（`ShiftPalAlongTrace.shiftPal_of_chainNotWatch`——`shiftGuardVM` が `phase = 4` を要求するが
copy/back/idle/broken から 1 手で生まれる watch は `phase ≤ 1`）。
**`CopyOrBack` も `CopyInv` も lag も「found 時の半径が正」も要らない。** -/
theorem obligation_shiftPalAtFreshChainAlongTrace (entry q : ℕ) (first : Fin 9) :
    ∀ (w : List (Fin 2)) (st : ℕ → GalilScaffoldTop.State GalilVM) (Tc : ℕ → ℕ),
      PalPeg.CloseoutCheckW.PreTraceIMW centreC placeC entry q first w st Tc →
      ∀ j, 1 ≤ j → j ≤ Tc w.length → (st j).vm.periodOnly = false →
        ShiftPal centreC placeC entry q first w (st j).vm := by
  classical
  intro w st Tc hPre j hj1 hjle hpo
  by_cases hW : ∃ wv : GalilScaffoldChainWatch.State, (st j).vm.chain = ChainVM.watch wv
  · obtain ⟨wv, hwv⟩ := hW
    exact obligation_shiftPalAtFreshWatchAlongTrace entry q first w st Tc hPre j hj1 hjle hpo wv hwv
  · exact PalPeg.ShiftPalAlongTrace.shiftPal_of_chainNotWatch centreC placeC entry q first
      (fun wv hEq => hW ⟨wv, hEq⟩)

/-- **もう公理ではない。**  `ShiftPalAlongTrace.shiftPal_alongTrace` の適用で、
上の 3 原子に割れた。2 つの側条件（`0 < w.length` と `1 ≤ Tc w.length`）は文脈から出る:
`w = []` なら `Tc 0 = 0`（`PreTrace.tc0`）で結論が空虚、
`1 ≤ Tc w.length` は `PreTraceB.tc1`（`Tc 1 = 1`）＋ `PreTrace.mono`。 -/
theorem obligation_shiftPalAlongTrace (entry q : ℕ) (first : Fin 9) :
    ∀ (w : List (Fin 2)) (st : ℕ → GalilScaffoldTop.State GalilVM) (Tc : ℕ → ℕ),
      PalPeg.CloseoutCheckW.PreTraceIMW centreC placeC entry q first w st Tc →
      ∀ j, 1 ≤ j → j ≤ Tc w.length →
        (st j).ctl.mode = GalilScaffoldController.Mode.scan → (st j).ctl.replaying = false →
        ShiftPal centreC placeC entry q first w (st j).vm := by
  intro w st Tc hPre j hj1 hjle hm hr
  have hw : 0 < w.length := by
    rcases Nat.eq_zero_or_pos w.length with h0 | hpos
    · exfalso; rw [h0, hPre.base.pre.tc0] at hjle; omega
    · exact hpos
  have hTcPos : 1 ≤ Tc w.length := by
    have hmono := hPre.base.pre.mono 1 w.length hw (le_refl _)
    rw [hPre.base.tc1] at hmono
    exact hmono
  exact PalPeg.ShiftPalAlongTrace.shiftPal_alongTrace centreC placeC entry q first hw hPre hTcPos
    (fun j' h1 h2 => obligation_readsShiftAlongTrace entry q first w st Tc hPre j' h1 h2)
    (fun j' h1 h2 =>
      obligation_freshShiftAtShiftEntryAlongTrace entry q first w st Tc hPre j' h1 h2)
    (fun j' h1 h2 h3 =>
      obligation_shiftPalAtFreshChainAlongTrace entry q first w st Tc hPre j' h1 h2 h3)
    j hj1 hjle hm hr

/-- **(OBLIGATION)** `CycleOracleMC3`。 -/
axiom obligation_cycleOracle (entry q : ℕ) (first : Fin 9) :
    ∀ w : List (Fin 2), 0 < w.length →
      CycleOracleMC3 (PofC centreC placeC entry w) q first w

/-- **(OBLIGATION)** 局所実現 `H_realizeLIMW'`。producer が無い。 -/
axiom obligation_localRealization (entry q : ℕ) (first : Fin 9) :
    H_realizeLIMW' centreC placeC entry q first

/-! ### scan landing 義務 — 原子に分解した 5 つ（すべて trace 形）

束ねると「公理を 1 個外す」が測れなくなるので 1 場ずつに分けた。
**すべて trace 形**（`PreTraceIMW` を取り `st j` で述べる）である点が本質:
状態全体に量化した global 形は、放電の材料（`LPackM2`・chain 側台帳・入力供給）が
run に沿ってしか存在しないので**原理的に落ちない**。`hpack` / `hav` が偽だったのと
同じ病。

`bg` 場（`scan_wait` / `scan_count` 着地）は放電済みなのでここに無い。 -/

/-! `MatchRes2` の残差 `MatchRest` は**放電済み**
（`BranchSupply.matchRest_alongTrace`、新規入力は `CentreMargin` だけ）。

4 場すべてが消えた経緯:

| 場 | 決着 |
|---|---|
| `canRNext` | **偽**（`MatchRestRefute.matchRest_alongTrace_false`）。着地側の 1 歩分に切り直し |
| `repV` | `CloseoutVerSide.VerRun` の第 1 成分そのもの |
| `replayPay` | `ChainPositionInvariantWithShiftPhase.payload` の guard を `ScanNR` から `mode = scan` へ広げたら源で両 replay 分岐が出た |
| `repVmid` | `ChainVerifierRepresents`（chain の verifier が 3 相すべてで入力を表現）を 1 手進めるだけ |

`ChainVerifierRepresents` の側条件はゼロ。`right` は入力端で no-op なので
（`representsAfterRight_free`）`canRight` の供給が一切要らず、誕生の
`Represents s.center.head w` だけが外部入力で、それは `HeadsRepresent.centre`。 -/

/-! rewind 相の左ヘッド余裕（旧 `obligation_centreMargin_alongTrace`）は**放電済み**
（`BranchSupply.rewindMarginAt_alongTrace`、新規入力ゼロ）。

`CloseoutPackRun16.MarksInv'` の第 2 成分が
`position left + r + pairOff c ≤ position center`（`RCouple` が持っていない向き）で、
第 1 成分 ＋ `¬ atFirst` から `2 ≤ position left`（`two_le_left_of_marksInv'`）。
`Tick.rewind_one` / `rewind_pair` は `¬ atFirst` を**構成子として持つ**ので、
`rewindLeft` / `Extra8.rewindMargin` / `RewindMarginAt` をその guard で再定式化すれば
`MarksInv'`（`BranchSupply.marksInv_alongTrace_ofPreTrace`、無償）だけで閉じる。

**`CentreMargin` は `+1` 分だけ強すぎた**（guard なしでは
`one_le_left_of_marksInv'` の `1 ≤ position left` しか出ない）。
n96 の「`rewindMargin` を `CentreMargin` 1 葉に縮めた」は数だけの削減で、
内容は強化だった——**過剰量化の 11 例目、自分で撒いた 4 例目**。 -/

/-! chain の verifier 側供給（旧 `obligation_verifierRunAlongRun`）は**放電済み**
（`BranchSupply.chainVerifierSupply_alongTrace`、新規入力は `CentreMargin` だけ）。

`VerRun` は `Steps` で到達可能な**任意の**状態に量化していたので trace からは出なかった
（`Tick` は決定的でない）。trace の点で述べた `ChainVerifierSupplyAlongTrace` に
切り直すと、`VerRep` は `ChainVerifierRepresents` の `.watch` 場、
`LagCan` は `ChainLagCanonical` の `.watch` 場で、どちらも搬送済み。

**過剰量化の 10 例目。run 形と trace 形は別物で、trace 形のほうが真に弱い。** -/

/-! `H_marksEntry'`（旧 `obligation_marksEntry`）は**放電済み**
（`CloseoutMarksPack.packRunR_MW_marksFree`、新規入力は側条件 `first ≠ 4` だけ）。

`hme` の消費者は `CloseoutOracleW.packRunR_MW` の 2 箇所だけで、どちらも
`MarksInv'` を作るためだけにあった。`CloseoutPackRun17.marksInv'_of_run'` は
**`H_marksEntry'` なしで** run の全点に `MarksInv'` を与えるもので、その 4 入力が
`InvLPC` の origin ではすべて無償だった:

| 入力 | 出どころ |
|---|---|
| `first ≠ 4` | 側条件（`first = 0` なので `by decide`） |
| `hfl`（scan 状態で `0 ≤ value length`） | `GalilInvPlus2.hfloor_of_invLP2`（`InvLPC.1` がそのまま `InvLP2`） |
| `hwin`（copy 状態で `WindowInOrigin`） | `CloseoutPackRun25.windowInOrigin_alongRun`。origin は scan なので origin 側の前提が空虚 |
| `CPack q c r` | `GalilCentreLive.cpack_of_entry` ＋ `CloseoutMarksFree.entryCounters_of_invLPC` |

`windowInOrigin_alongRun` が `Fair` なしで通るようになったのは、モデル欠陥
`M-fallbackPlace` を直して `beginFallbackVM'` が fallback 先の窓長を
`position right` で抑えるようにしたから（n107）。

**つまり `hme` は最初から独立した義務ではなかった。** `CloseoutMarksPack` の
冒頭は「`hme` は `hpack` の中にある」と書いていたが、正しくは
**`hme` は run の中にある**。 -/

/-! ## 目標 -/

/-- **目標**: `PAL ∈ PEG` を前提ゼロで。いまは上の 4 個の `axiom` に依存している。
`#print axioms unconditional` が標準 3 公理だけになったら証明完了。 -/
theorem unconditional : RecognizedByTotalPEG PAL :=
  given_scanLandingObligations 0 0 0
    (obligation_shiftPalAlongRun 0 0 0)
    (by decide)
    (obligation_cycleOracle 0 0 0)
    (obligation_localRealization 0 0 0)
    (fun w st Tc hPreTraceIMW =>
      PalPeg.BranchSupply.scanLandingObligations_alongTrace_of_matchRest centreC placeC 0 0 0
        hPreTraceIMW
        (obligation_shiftPalAlongTrace 0 0 0 w st Tc hPreTraceIMW)
        (PalPeg.BranchSupply.shiftExitLedgerAt_alongTrace centreC placeC 0 0 0
          hPreTraceIMW (PalPeg.BranchSupply.marksInv_alongTrace_ofPreTrace centreC placeC 0 0 0 (by decide)
            hPreTraceIMW.base.pre))
        (PalPeg.BranchSupply.marksInv_alongTrace_ofPreTrace centreC placeC 0 0 0 (by decide)
          hPreTraceIMW.base.pre)
        (PalPeg.BranchSupply.matchRest_alongTrace centreC placeC 0 0 0 hPreTraceIMW
          (PalPeg.BranchSupply.marksInv_alongTrace_ofPreTrace centreC placeC 0 0 0 (by decide)
            hPreTraceIMW.base.pre)))
    (fun w st Tc hw hPreTraceIMW =>
      PalPeg.BranchSupply.chainVerifierSupply_alongTrace centreC placeC 0 0 0 hw hPreTraceIMW
        (PalPeg.BranchSupply.marksInv_alongTrace_ofPreTrace centreC placeC 0 0 0 (by decide)
          hPreTraceIMW.base.pre)
        (hPreTraceIMW.base.tc1 ▸ hPreTraceIMW.base.pre.mono 1 w.length hw le_rfl))

#print axioms unconditional

end PalPeg.PalInPeg
