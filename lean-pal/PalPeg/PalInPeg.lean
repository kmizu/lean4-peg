import PalPeg.CloseoutFinalFour
import PalPeg.CloseoutFinalBranch
import PalPeg.CloseoutFinalVer
import PalPeg.CloseoutFinalS2
import PalPeg.CloseoutFinalW3
import PalPeg.CloseoutFinalW4
import PalPeg.CloseoutFinalW5
import PalPeg.CloseoutFinalPack

/-!
# `PalInPeg` — 目標定理と、そこへ至る部分結果を 1 つの名前空間に集める

**目標は無条件の `PalInPeg.unconditional : RecognizedByTotalPEG PAL`。2026-09-24 に証明済み**
（`PalPeg/PalInPegFinal.lean`、標準3公理のみ。Scala の window-pal と同じ SCA 経路）。

前提を取るものは全部「部分結果」であり、`PalInPeg.given_<残差>` という名前にする。
名前だけで「**何を仮定すれば `PAL ∈ PEG` に到達するか**」が読めるのが条件。
番号（旧 `pal_in_peg_final30` / `final39` / `final43` …）は「いつ書いたか」でしかなく、
意味から引けないので廃止した。

コウタの指示（2026-09-19）:
* 「本来の定理は `pal_in_peg` やん。その到達のための partial なものなら適切な名前がある」
* 「あるいは `PalInPeg` をモジュールにしてその下に関係する前提を集めるとかね。
  そしたら theorem 名がやたら長くならずにもすむ」

## 前提が最少で、反証済みの前提を含まないもの

**`PalInPeg.given_globalScanLandings`**（`hSP` `hme` `hor` `hC` ＋ global な
`H_BackgroundLandingPayload` / `H_MatchLandingPayload` / `H_ShiftExitPayload`）。

## 偽の前提を取っているもの（`_FALSE_HYP`）

前提の本数だけ見ると少ないが、**名前に出ている前提が偽**なので前進として数えない。
`consumeAvailEverywhere` は `ConsumeAvailRefute.hav_false`、
`chainPackAtAnyState` は `CloseoutPackRefute.hpack_false` で機械検査済み。
（どちらも「run に沿う事実を状態全体に量化した」という同じ病。名前にそれが出るようにした。）

**全体 build 成功・標準公理のみ・無条件 PAL は未完。計画書 §10.5（前提ゼロ）は未達。**
-/

set_option autoImplicit false

namespace PalPeg.PalInPeg

/-! ## 1. 前提が最少で健全なもの -/

/-- **`hSP` `hme` `hor` `hC` ＋ global な 3 つの scan landing 義務**があれば `PAL ∈ PEG`。
global 形の landing 義務は原理的に放電できない（材料が run に沿ってしか存在しない）ので、
実際に詰めるのは §2 の trace 形の方。 -/
alias given_globalScanLandings :=
  PalPeg.CloseoutFinalFour.given_globalScanLandings

/-- 一代前。`H_FourSemiperiodsLeDistance` を余分に取る。`H_FourSemiperiodsLeDistance` は
`CloseoutPackRun40.four_of_other'` で消えた（`ChainPositionInvariantExactCoupling` に載せ替えるだけ）。 -/
alias given_globalScanLandings_and_fourOther :=
  PalPeg.CloseoutFinalW.given_globalScanLandings_and_fourOther

/-! ## 2. trace 形（放電可能な形）-/

/-- **`hSP` `hme` `hor` `hC` ＋ trace の各点での scan landing 義務 3 場 ＋ `VerRun`**。
`shiftDone` 義務は完全に放電済み（半径台帳は `RadLedger`、`canRight` は trace 予算）。 -/
alias given_scanLandingObligations :=
  PalPeg.CloseoutFinalBranch.given_scanLandingObligations

/-- 同上、`shiftDone` の半径台帳だけを放電した段階。 -/
alias given_landingObligationsSansRadiusLedger :=
  PalPeg.CloseoutFinalBranch.given_landingObligationsSansRadiusLedger

/-- 4 場をまとめて run 形にした段階（放電はまだ）。 -/
alias given_landingObligationsAlongRun :=
  PalPeg.CloseoutFinalBranch.given_landingObligationsAlongRun

/-- global な Run41 版 4 義務 ＋ `VerRun`。`CloseoutPackRun48` の放電器が効く経路。 -/
alias given_globalRun41Landings_and_verifierRun :=
  PalPeg.CloseoutFinalVer.given_globalRun41Landings_and_verifierRun

/-! ## 3. 組み立ての共通部分 -/

/-- `needL'` の上界を外から取る 45 行の組み立て。`given_*` の各版はこれの instantiation。 -/
alias given_needBound := PalPeg.CloseoutFinalFour.given_needBound

/-! ## 4. 偽の前提を取っているもの — 使ってはいけない -/

/-- **偽**: `consumeAvailEverywhere`（`ConsumeAvail` を全状態に量化）。 -/
alias given_consumeAvailEverywhere_FALSE_HYP :=
  PalPeg.CloseoutFinalS2.given_consumeAvailEverywhere_FALSE_HYP

/-- **偽**: `chainPackAtAnyState`（`ChainPositionInvariantWithShiftPhase → ChainPack` を任意状態で）。 -/
alias given_chainPackAtAnyState_FALSE_HYP :=
  PalPeg.CloseoutFinalW4.given_chainPackAtAnyState_FALSE_HYP

/-- **偽**: 同じ `chainPackAtAnyState`。前提数は 5。 -/
alias given_chainPackAtAnyState_andMore_FALSE_HYP :=
  PalPeg.CloseoutFinalW3.given_chainPackAtAnyState_andMore_FALSE_HYP

#print axioms given_globalScanLandings
#print axioms given_scanLandingObligations
#print axioms given_needBound

end PalPeg.PalInPeg
