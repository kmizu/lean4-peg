import PalPeg.CloseoutVerSide
import PalPeg.CloseoutPackRun49
import PalPeg.CloseoutPackRun13
import PalPeg.ShiftLocalRun

/-!
# `LandingObligationsAlongRun` — `ChainPositionInvariantWithShiftPhase` の 4 分岐義務を run 形にする

## なぜ run 形でなければならないか

`H_BackgroundLandingChainLedger` / `H_MatchLandingChainLedger` / `H_ShiftEntryChainLedger` / `H_ShiftExitRadiusLedger` は
`∀ (c : Control) (s : GalilVM), …` で**任意の状態**を量化している。ところが
それらを放電する材料は run に沿ってしか存在しない：

* `LPackM2.shiftGeom`（`CloseoutPackRun23:103`）— `H_ShiftExitRadiusLedger` の `canRight`/
  半径上界はここから出る（`CloseoutShiftDoneP.canR_of_shiftGeom` /
  `radEq_of_shiftGeom_done`）。`LPackM2` は run の各点に `IPackMW.m2` としてある。
* chain 側台帳 `ChainPositionLedger`（Run41、Run38 の `SrcPos` を吸収）— `chainPos_step` /
  `chainPos_matched` で run を運ばれる。
* 入力供給（verifier が入力を表現する）— `CloseoutVerSide.VerRun` が run 形で束ねている。

任意の状態にこれらは無い。だから `∀ c s` の形のままでは放電できない。
同じ誤りの反証が `ConsumeAvailRefute.hav_false`（`∀ st` と書いて run の制約が
ゼロになった例）。

## このファイル

`CloseoutPackRun41.LandingObligationsAt`（状態局所の束、`chainPosInv2_tick_of_landingObligationsAt` が消費する）を
run に沿って量化した `LandingObligationsAlongRun` を定義し、`ChainPositionInvariantWithShiftPhase` を run に沿って運ぶ。
`landingObligationsAlongRun_of_globalHypotheses` があるので、global 4 本を持っている呼び出し側はそのまま乗る
（**逆は無い** — run 形のほうが真に弱い）。

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.BranchSupply

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
open PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton PalPeg.GalilFrontMono PalPeg.GalilChainCoupling
open PalPeg.CloseoutLPack5 PalPeg.CloseoutPackRun6 PalPeg.CloseoutPackRun10
open PalPeg.CloseoutPackRun26 PalPeg.CloseoutPackRun34 PalPeg.CloseoutPackRun40
open PalPeg.CloseoutPackRun41 PalPeg.CloseoutPackRun48 PalPeg.CloseoutVerRep
open PalPeg.CloseoutWatchSupply
open PalPeg.CloseoutShiftS2
open PalPeg.CloseoutRadPack2 PalPeg.CloseoutRadPack4
open PalPeg.CloseoutPackRun30 PalPeg.CloseoutPackRun32 PalPeg.CloseoutPackRun38
open PalPeg.GalilBranchInvariants PalPeg.CloseoutCheckW
open PalPeg.GalilFinalAssembly
open PalPeg.GalilTrailRad
open PalPeg.CloseoutLPack
open PalPeg.CloseoutShiftS
open PalPeg.CloseoutLPack6
open PalPeg.GalilTrailAssembly
open PalPeg.GalilTrailScan
open PalPeg.GalilTrailProof
  PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton PalPeg.GalilFrontMono
open PalPeg.CloseoutPackRun26 PalPeg.CloseoutPackRun34 PalPeg.CloseoutPackRun41
open PalPeg.CloseoutPackRun44 PalPeg.CloseoutPackRun47 PalPeg.CloseoutPackRun48
open PalPeg.CloseoutPackRun41 PalPeg.CloseoutShiftS2
open PalPeg.CloseoutVerSide PalPeg.CloseoutVerRep PalPeg.ShiftLocalRun
open PalPeg.GalilRunTrace PalPeg.CloseoutFrontExtra PalPeg.CloseoutCanRightBound
open PalPeg.CloseoutPackRun23 PalPeg.GalilLedgerAssembly
open PalPeg.CloseoutPackRun49 PalPeg.CloseoutPackW PalPeg.CloseoutPackRun36
open PalPeg.CloseoutPackRun47 PalPeg.CloseoutPackRun29 PalPeg.CloseoutPackRun46
open PalPeg.GalilScaffoldChainPeriod (Tape)

section
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-! ## 1. run 形の 4 分岐義務 -/

/-- **(NAMED, run 形) 4 分岐義務**: run が到達する各状態で `LandingObligationsAt`。 -/
def LandingObligationsAlongRun (w : List (Fin 2)) (x : State GalilVM) : Prop :=
  ∀ (m : ℕ) (z : State GalilVM),
    Steps (galilFrameS (PofC centre place entry w) q first) 2048 m x z →
    LandingObligationsAt centre place entry q first w z.ctl z.vm

/-- global 4 本は run 形を含意する（**逆は無い** — run 形のほうが真に弱い）。 -/
theorem landingObligationsAlongRun_of_globalHypotheses {w : List (Fin 2)}
    (hbg : H_BackgroundLandingChainLedger centre place entry q first w) (hmatch : H_MatchLandingChainLedger centre place entry q first w)
    (hentry : H_ShiftEntryChainLedger centre place entry q first w)
    (hsd : H_ShiftExitRadiusLedger centre place entry q first w) (x : State GalilVM) :
    LandingObligationsAlongRun centre place entry q first w x :=
  fun _ z _ => landingObligationsAt_of_globalHypotheses centre place entry q first hbg hmatch hentry hsd z.ctl z.vm

/-- **`ChainPositionInvariantWithShiftPhase` を run に沿って運ぶ（run 形の義務で）。**  再指標化は
`Steps.succ ht`（`CloseoutBundleRun.roundBundle_steps_run` と同じ形）。 -/
theorem chainPosInv2_alongRun {w : List (Fin 2)} :
    ∀ {n : ℕ} {x y : State GalilVM},
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 n x y →
      ChainPositionInvariantWithShiftPhase w x.ctl x.vm →
      LandingObligationsAlongRun centre place entry q first w x →
      ChainPositionInvariantWithShiftPhase w y.ctl y.vm := by
  intro n x y h
  induction h with
  | zero x => intro hx _; exact hx
  | @succ n x z y ht _ ih =>
    intro hx hLandingObligations
    refine ih (chainPosInv2_tick_of_landingObligationsAt centre place entry q first (hLandingObligations 0 x (.zero x)) hx ht) ?_
    intro m z' hz'
    exact hLandingObligations (m + 1) z' (.succ ht hz')

/-! ## 2. `ShiftLocalS` と `needL'` を run 形の義務から -/

/-- **`ShiftLocalS` along the run**: `CloseoutVerSide.shiftLocalS_of_verRun` の
4 つの global 義務を `LandingObligationsAlongRun` に置き換えたもの。 -/
theorem shiftLocalS_of_landingObligationsAlongRun {w : List (Fin 2)}
    {n : ℕ} {x y : State GalilVM} (hx : ChainPositionInvariantWithShiftPhase w x.ctl x.vm)
    (h : Steps (galilFrameS (PofC centre place entry w) q first) 2048 n x y)
    (hLandingObligations : LandingObligationsAlongRun centre place entry q first w x)
    (hVerRun : VerRun centre place entry q first w x)
    (hLPackM2AtTarget : PalPeg.CloseoutPackRun23.LPackM2 w y.ctl y.vm) :
    ShiftLocalS centre place entry q first w y := by
  refine shiftLocalS_of_parts centre place entry q first
    (chainPosInv2_alongRun centre place entry q first h hx hLandingObligations)
    (fun hm => ?_) (fun hm => (hVerRun n y h hm).1) (fun hm => (hVerRun n y h hm).2)
  cases hr : y.ctl.replaying with
  | false =>
    obtain ⟨rad, hIndexLeTc⟩ := hLPackM2AtTarget.packM.scanGeom hm hr
    exact ⟨hIndexLeTc.rightRep, hIndexLeTc.rightPresent⟩
  | true =>
    obtain ⟨rad, hIndexLeTc⟩ := hLPackM2AtTarget.scanGeomR hm hr
    exact ⟨hIndexLeTc.rightRep, hIndexLeTc.rightPresent⟩

/-- **`needL'` の上界を run 形の義務から。**  `CloseoutVerSide.needIMW'_le_W4` の
global 4 本を `LandingObligationsAlongRun` に置き換え、3 段の本体は
`ShiftLocalRun.needBound_of_shiftLocalS_alongTrace`（S / S3 / S4 共通部分）に載せた。 -/
theorem needBound_of_landingObligationsAlongRun {w : List (Fin 2)} (hw : 0 < w.length)
    {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hPreTrace : PalPeg.CloseoutCheckW.PreTraceIMW centre place entry q first w st Tc)
    (hChainPosInv2AtOrigin : ChainPositionInvariantWithShiftPhase w (st 0).ctl (st 0).vm)
    (hLandingObligations : LandingObligationsAlongRun centre place entry q first w (st 0))
    (hVerRun : VerRun centre place entry q first w (st 0)) :
    ∀ m, m < w.length → ∀ i, i ≤ Tc (m+1) →
      PalPeg.GalilLookRefined.needL' w st i ≤ m + 1 :=
  needBound_of_shiftLocalS_alongTrace centre place entry q first hw hPreTrace
    (fun i hIndexLeTc => shiftLocalS_of_landingObligationsAlongRun centre place entry q first hChainPosInv2AtOrigin
      (PalPeg.CloseoutPackRun2.steps_of_trace hPreTrace.base.pre.trace i hIndexLeTc) hLandingObligations hVerRun (hPreTrace.packs i hIndexLeTc).m2)

/-! ## 3. `shiftDone` 場の半径台帳はタダ

`LandingObligationsAt.shiftDone` は `canRight s.right` と半径台帳の連言。後者は
**`CloseoutRadPack.RadLedger.le`（`position center + value radius ≤ position right`）と
`ScanInvariant.rightPos`（`position right = position center + rad`）だけで出る**。
`RadLedger` は `CloseoutLPack6.radLedger_pt` が `PreTrace` ＋ `LeftLive` だけから
run の全点に与える（新規入力ゼロ）。 -/

/-- **半径台帳は `RadLedger` から出る。** -/
theorem radiusLe_of_radLedger {w : List (Fin 2)} {c : Control} {s : GalilVM}
    (hRadLedger : PalPeg.CloseoutRadPack.RadLedger c s) :
    ∀ rad : ℕ, ScanInvariant w (position s.center) rad s.left s.right →
      value s.radius ≤ (rad : ℤ) := by
  intro rad hsi
  have hIndexPos : (position s.center : ℤ) + value s.radius ≤ (position s.right : ℤ) := hRadLedger.le
  have h2 : position s.right = position s.center + rad := hsi.rightPos
  rw [h2] at hIndexPos
  push_cast at hIndexPos
  omega

/-- **`shiftDone` 場は `canRight` 1 つに落ちる。** -/
theorem shiftExitObligation_of_radLedger {w : List (Fin 2)} {c : Control} {s : GalilVM}
    (hRadLedger : PalPeg.CloseoutRadPack.RadLedger c s)
    (hcan : c.mode = Mode.shift →
      ¬ (galilFrameS (PofC centre place entry w) q first).remainingPos s →
      GalilScaffoldChainVerifier.canRight s.right) :
    c.mode = Mode.shift →
      ¬ (galilFrameS (PofC centre place entry w) q first).remainingPos s →
      ChainPositionInvariantWithShiftPhase w c s → s.chain ≠ ChainVM.idle →
      GalilScaffoldChainVerifier.canRight s.right ∧
        ∀ rad : ℕ, ScanInvariant w (position s.center) rad s.left s.right →
          value s.radius ≤ (rad : ℤ) :=
  fun hm hp _ _ => ⟨hcan hm hp, radiusLe_of_radLedger (w := w) hRadLedger⟩

#print axioms radiusLe_of_radLedger
#print axioms shiftExitObligation_of_radLedger

/-! ## 4. trace 指標版 — 供給の形に合わせる

`LandingObligationsAlongRun` は `Steps` で到達する**すべての**状態を量化するが、`Tick` は関係なので
trace の外の状態も含む。一方、放電の材料（`RadLedger`、`LPackM2`）は
`radLedger_pt` / `PreTraceIMW.packs` が **trace の点 `st i`** で与える。
そこで trace 指標の版を置く。`chainPosInv2_alongRun` を使う経路は `steps_of_trace` で
trace の鎖しか渡さないので、これで十分。 -/

/-- **(NAMED, trace 形) 4 分岐義務の残り**: `shiftDone` の半径台帳は `RadLedger` から
出るので（§3）、残るのは `canRight` だけ。 -/
structure LandingObligationsAtSansRadiusLedger (w : List (Fin 2)) (c : Control) (s : GalilVM) : Prop where
  bg : ∀ t : GalilVM, c.mode = Mode.scan → ChainPositionInvariantWithShiftPhase w c s →
    (galilFrameS (PofC centre place entry w) q first).background s t →
    ScanNR ⟨c, t⟩ → t.chain ≠ ChainVM.idle → ScanPositionPayloadWithChainLedger w t
  matchLand : ∀ (s' t : GalilVM) (o b : Bool), c.mode = Mode.scan → ChainPositionInvariantWithShiftPhase w c s →
    (galilFrameS (PofC centre place entry w) q first).compare s s' →
    (galilFrameS (PofC centre place entry w) q first).matched s' →
    (galilFrameS (PofC centre place entry w) q first).matchedPlace c.replaying s' t →
    ScanNR ⟨{c with clock := 2048, output := o, replaying := c.replaying && b}, t⟩ →
    t.chain ≠ ChainVM.idle → ScanPositionPayloadWithChainLedger w t
  entryLand : ∀ s' t : GalilVM, c.mode = Mode.scan → ChainPositionInvariantWithShiftPhase w c s →
    (galilFrameS (PofC centre place entry w) q first).compare s s' →
    ¬ (galilFrameS (PofC centre place entry w) q first).matched s' →
    shiftGuardVM s' → beginShiftVM' s' t → ShiftPhaseChainLedger t
  shiftCan : c.mode = Mode.shift →
    ¬ (galilFrameS (PofC centre place entry w) q first).remainingPos s →
    GalilScaffoldChainVerifier.canRight s.right

/-- **`LandingObligationsAt` from `LandingObligationsAtSansRadiusLedger` plus the free radius ledger.** -/
theorem landingObligationsAt_of_sansRadiusLedger {w : List (Fin 2)} {c : Control} {s : GalilVM}
    (hRadLedger : PalPeg.CloseoutRadPack.RadLedger c s)
    (hres : LandingObligationsAtSansRadiusLedger centre place entry q first w c s) :
    LandingObligationsAt centre place entry q first w c s :=
  ⟨hres.bg, hres.matchLand, hres.entryLand,
    shiftExitObligation_of_radLedger centre place entry q first hRadLedger hres.shiftCan⟩

/-- **`ChainPositionInvariantWithShiftPhase` along the trace** (induction on the index, the shape
`CloseoutPackRun49.lpackM3_steps` uses). -/
theorem chainPosInv2_alongTrace {w : List (Fin 2)} {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hPreTrace : PreTrace centre place entry q first w st Tc)
    (hLandingObligations : ∀ i, i ≤ Tc w.length → LandingObligationsAt centre place entry q first w (st i).ctl (st i).vm)
    (hx : ChainPositionInvariantWithShiftPhase w (st 0).ctl (st 0).vm) :
    ∀ i, i ≤ Tc w.length → ChainPositionInvariantWithShiftPhase w (st i).ctl (st i).vm := by
  intro i
  induction i with
  | zero => intro _; exact hx
  | succ n ih =>
    intro hIndexLeTc
    exact chainPosInv2_tick_of_landingObligationsAt centre place entry q first (hLandingObligations n (by omega)) (ih (by omega))
      (hPreTrace.trace.tick n (by omega))

/-- **(NAMED, trace 形) 残りの 3 場 ＋ `canRight`**, at every point of the trace. -/
def LandingObligationsAlongTraceSansRadiusLedger (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ) : Prop :=
  ∀ i, i ≤ Tc w.length → LandingObligationsAtSansRadiusLedger centre place entry q first w (st i).ctl (st i).vm

/-- **`needL'` の上界を trace 形の残差から。**  半径台帳（`RadLedger`）は
`CloseoutLPack6.radLedger_pt` が `PreTrace` ＋ `LeftLive` だけで与えるので
**新規入力ゼロ**で内部調達する。 -/
theorem needBound_of_landingObligationsSansRadiusLedger {w : List (Fin 2)} (hw : 0 < w.length)
    {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hPreTrace : PalPeg.CloseoutCheckW.PreTraceIMW centre place entry q first w st Tc)
    (hChainPosInv2AtOrigin : ChainPositionInvariantWithShiftPhase w (st 0).ctl (st 0).vm)
    (hres : LandingObligationsAlongTraceSansRadiusLedger centre place entry q first w st Tc)
    (hVerRun : VerRun centre place entry q first w (st 0)) :
    ∀ m, m < w.length → ∀ i, i ≤ Tc (m+1) →
      PalPeg.GalilLookRefined.needL' w st i ≤ m + 1 := by
  have hLPackM2AtTarget : ∀ i, i ≤ Tc w.length →
      PalPeg.CloseoutPackRun10.LPackM w (st i).ctl (st i).vm :=
    fun i hIndexLeTc => (hPreTrace.packs i hIndexLeTc).pack
  have hll : ∀ i, i ≤ Tc w.length →
      PalPeg.GalilTrailSane.LeftLive (st i).ctl (st i).vm :=
    fun i hIndexLeTc => leftLive_of_lpackM (hLPackM2AtTarget i hIndexLeTc)
  have hRadLedger := radLedger_pt centre place entry q first hw hPreTrace.base.pre hll
  have hLandingObligations : ∀ i, i ≤ Tc w.length →
      LandingObligationsAt centre place entry q first w (st i).ctl (st i).vm :=
    fun i hIndexLeTc => landingObligationsAt_of_sansRadiusLedger centre place entry q first (hRadLedger i hIndexLeTc) (hres i hIndexLeTc)
  have hinv := chainPosInv2_alongTrace centre place entry q first hPreTrace.base.pre hLandingObligations hChainPosInv2AtOrigin
  refine needBound_of_shiftLocalS_alongTrace centre place entry q first hw hPreTrace (fun i hIndexLeTc => ?_)
  refine shiftLocalS_of_parts centre place entry q first (hinv i hIndexLeTc) (fun hm => ?_)
    (fun hm => (hVerRun i (st i)
      (PalPeg.CloseoutPackRun2.steps_of_trace hPreTrace.base.pre.trace i hIndexLeTc) hm).1)
    (fun hm => (hVerRun i (st i)
      (PalPeg.CloseoutPackRun2.steps_of_trace hPreTrace.base.pre.trace i hIndexLeTc) hm).2)
  cases hr : (st i).ctl.replaying with
  | false =>
    obtain ⟨rad, hi'⟩ := (hPreTrace.packs i hIndexLeTc).m2.packM.scanGeom hm hr
    exact ⟨hi'.rightRep, hi'.rightPresent⟩
  | true =>
    obtain ⟨rad, hi'⟩ := (hPreTrace.packs i hIndexLeTc).m2.scanGeomR hm hr
    exact ⟨hi'.rightRep, hi'.rightPresent⟩

/-! ## 5. `shiftCan` — 右ヘッドが動けることは trace の予算から出る

`LandingObligationsAtSansRadiusLedger.shiftCan` は `canRight s.right`。`CloseoutCanRightBound.canRight_of_position_bound`
は `position p ≤ 2m − 1`（`1 ≤ m ≤ |w|`）から `canRight p` を出す。`m = |w|` を取れば
必要なのは **`position (st i).vm.right ≤ 2|w| − 1`**。

これは trace の終端の報告点から**後ろ向き**に出る：
`PreTrace.report` の `ReportPointAt.atPrefix` が終端で `position right = 2|w| − 1` を与え、
front ポテンシャル（`front = position + replay`）は tick で単調（`front_tick_mono`）、
かつ `position right ≤ front`（`FrontPack` だけから）。よって

```
position (st i).right ≤ front (st i) ≤ front (st (Tc |w|)) = position (st (Tc |w|)).right = 2|w| − 1
```

`Steps` 版（`CloseoutFrontExtra.position_le_of_front_steps`）ではなく **trace 指標**で
書く必要がある: 中間状態の `CentreLive` は `centreLive_trace` が trace の点でしか
与えないのに対し、`Steps` 版は任意の到達状態を量化するから。 -/

/-- `position right ≤ front`（`FrontPack` だけから）。 -/
theorem rightHeadPos_le_front {c : Control} {s : GalilVM} (hPreTrace : FrontPack c s) :
    (position s.right : ℤ) ≤ front s := by
  unfold front
  cases hr : c.replaying with
  | true =>
    obtain ⟨m, hm⟩ := hPreTrace.replayPos hr
    rw [hm, GalilScaffoldCounter.ofNat_value]
    omega
  | false =>
    rw [hPreTrace.rest (Or.inl hr)]
    simp [GalilScaffoldCounter.value, GalilScaffoldCounter.reset]

/-- **front は trace に沿って単調。** -/
theorem front_mono_alongTrace {w : List (Fin 2)} {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hPreTrace : PreTrace centre place entry q first w st Tc)
    (hFrontPack : ∀ j, 1 ≤ j → j ≤ Tc w.length → FrontPack (st j).ctl (st j).vm) :
    ∀ i k, 1 ≤ i → i + k ≤ Tc w.length → front (st i).vm ≤ front (st (i + k)).vm := by
  intro i k
  induction k with
  | zero => intro _ _; exact le_rfl
  | succ n ih =>
    intro hIndexPos hk
    refine le_trans (ih hIndexPos (by omega)) ?_
    have ht := hPreTrace.trace.tick (i + n) (by omega)
    have hm := front_tick_mono (onLetterVM w) leftFirstVM centre place entry q first 2048
      (hFrontPack (i + n) (by omega) (by omega)) ht
    have he : i + (n + 1) = i + n + 1 := by omega
    rw [he]
    exact hm

/-- **右ヘッドは trace 全域で `2|w| − 1` 以下。** -/
theorem rightHeadPos_le_alongTrace {w : List (Fin 2)} (hw : 0 < w.length)
    {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hPreTrace : PreTrace centre place entry q first w st Tc)
    (hFrontPack : ∀ j, 1 ≤ j → j ≤ Tc w.length → FrontPack (st j).ctl (st j).vm)
    (hTcPos : 1 ≤ Tc w.length) :
    ∀ i, 1 ≤ i → i ≤ Tc w.length → position (st i).vm.right ≤ 2 * w.length - 1 := by
  intro i hIndexPos hIndexLeTc
  have hrp := hPreTrace.report w.length hw le_rfl
  have hfe : front (st (Tc w.length)).vm = ((position (st (Tc w.length)).vm.right : ℕ) : ℤ) :=
    front_eq_position (hFrontPack _ hTcPos le_rfl) hrp.notReplaying
  have hmono := front_mono_alongTrace centre place entry q first hPreTrace hFrontPack i (Tc w.length - i) hIndexPos (by omega)
  rw [show i + (Tc w.length - i) = Tc w.length by omega] at hmono
  have hple := rightHeadPos_le_front (hFrontPack i hIndexPos hIndexLeTc)
  rw [hfe, hrp.atPrefix] at hmono
  have : ((position (st i).vm.right : ℕ) : ℤ) ≤ ((2 * w.length - 1 : ℕ) : ℤ) :=
    le_trans hple hmono
  exact_mod_cast this

/-- **`mode := .init` にする `Tick` 構成子は存在しない。**  `Tick`（`GalilScaffoldTop:109`）の
24 構成子の行き先の mode は scan / shift / copy / home / fpp / markEnd / choose / rewind /
replayStart か「変えない」のいずれかで、`init` は源の mode としてしか現れない。 -/
theorem tick_target_mode_ne_init {σ : Type} {F : Frame σ} {delay : ℕ} {x y : State σ}
    (h : Tick F delay x y) : y.ctl.mode ≠ Mode.init := by
  cases h <;> simp_all

/-- **trace は 1 手目以降 `init` に戻らない。** -/
theorem mode_ne_init_alongTrace_afterFirstStep {w : List (Fin 2)} {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hPreTrace : PreTrace centre place entry q first w st Tc) :
    ∀ j, 1 ≤ j → j ≤ Tc w.length → (st j).ctl.mode ≠ Mode.init := by
  intro j hj1 hj
  obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
  exact tick_target_mode_ne_init (hPreTrace.trace.tick n (by omega))

/-- **右ヘッドが入力を表現している trace 点では `canRight` はタダ。**
`rightHeadPos_le_alongTrace` ＋ `CloseoutCanRightBound.canRight_of_position_bound`（`m = |w|`）。
`i = 0` は boot（`mode = init`）なので除く。これは `Extra7.scanAvail`（＝`hee`/`het` の
中身）と shift 相の `canRight` を同時に与える。 -/
theorem rightHeadCanRight_alongTrace {w : List (Fin 2)} (hw : 0 < w.length)
    {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hPreTrace : PreTrace centre place entry q first w st Tc)
    (hFrontPack : ∀ j, 1 ≤ j → j ≤ Tc w.length → FrontPack (st j).ctl (st j).vm)
    (hTcPos : 1 ≤ Tc w.length)
    {i : ℕ} (hIndexPos : 1 ≤ i) (hIndexLeTc : i ≤ Tc w.length)
    (hrep : GalilScaffoldInputTrace.Represents (st i).vm.right.head w)
    (hpres : (st i).vm.right.head.focus ≠ none) :
    GalilScaffoldChainVerifier.canRight (st i).vm.right :=
  canRight_of_position_bound hrep hpres (m := w.length) hw le_rfl
    (rightHeadPos_le_alongTrace centre place entry q first hw hPreTrace hFrontPack hTcPos i hIndexPos hIndexLeTc)

/-- **`FrontPack` は trace の 1 手目以降タダ。** -/
theorem frontPack_alongTrace {w : List (Fin 2)} (hw : 0 < w.length)
    {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hPreTrace : PreTrace centre place entry q first w st Tc) :
    ∀ j, 1 ≤ j → j ≤ Tc w.length → FrontPack (st j).ctl (st j).vm :=
  fun j hj1 hj => frontPack_trace centre place entry q first w hw st Tc hPreTrace j hj
    (mode_ne_init_alongTrace_afterFirstStep centre place entry q first hPreTrace j hj1 hj)

/-- **scan 相の `canRight`（＝`Extra7.scanAvail`）もタダ。**  右ヘッドの
`Represents`/`focus ≠ none` は `LPackM2` の scan 幾何から出る。 -/
theorem scanRightHeadCanRight_alongTrace {w : List (Fin 2)} (hw : 0 < w.length)
    {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hPreTrace : PreTrace centre place entry q first w st Tc)
    (hLPackM2 : ∀ j, j ≤ Tc w.length →
      PalPeg.CloseoutPackRun23.LPackM2 w (st j).ctl (st j).vm)
    (hTcPos : 1 ≤ Tc w.length) :
    ∀ i, i ≤ Tc w.length → (st i).ctl.mode = Mode.scan →
      GalilScaffoldChainVerifier.canRight (st i).vm.right := by
  intro i hIndexLeTc hMode
  have hIndexPos : 1 ≤ i := by
    rcases Nat.eq_zero_or_pos i with rfl | h; swap; · exact h
    exfalso
    rw [hPreTrace.start] at hMode
    exact Mode.noConfusion hMode
  have hrp : GalilScaffoldInputTrace.Represents (st i).vm.right.head w ∧
      (st i).vm.right.head.focus ≠ none := by
    cases hr : (st i).ctl.replaying with
    | false =>
      obtain ⟨rad, hi'⟩ := (hLPackM2 i hIndexLeTc).packM.scanGeom hMode hr
      exact ⟨hi'.rightRep, hi'.rightPresent⟩
    | true =>
      obtain ⟨rad, hi'⟩ := (hLPackM2 i hIndexLeTc).scanGeomR hMode hr
      exact ⟨hi'.rightRep, hi'.rightPresent⟩
  exact rightHeadCanRight_alongTrace centre place entry q first hw hPreTrace
    (frontPack_alongTrace centre place entry q first hw hPreTrace) hTcPos hIndexPos hIndexLeTc hrp.1 hrp.2

/-- **`shiftCan` は trace 予算と `LPackM2.shiftGeom` から出る — 新規入力ゼロ。**
shift 相では `ShiftGeom` の `RRep` が右ヘッドの `Represents` と `focus ≠ none` を持ち、
`FrontPack` は `GalilTrailRad.frontPack_trace` が `mode ≠ init`（1 手目以降は定理）
のもとで trace の各点に与える。 -/
theorem shiftRightHeadCanRight_alongTrace {w : List (Fin 2)} (hw : 0 < w.length)
    {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hPreTrace : PreTrace centre place entry q first w st Tc)
    (hLPackM2 : ∀ j, j ≤ Tc w.length →
      PalPeg.CloseoutPackRun23.LPackM2 w (st j).ctl (st j).vm) :
    ∀ i, i ≤ Tc w.length → (st i).ctl.mode = Mode.shift →
      GalilScaffoldChainVerifier.canRight (st i).vm.right := by
  have hFrontPack : ∀ j, 1 ≤ j → j ≤ Tc w.length → FrontPack (st j).ctl (st j).vm :=
    fun j hj1 hj => frontPack_trace centre place entry q first w hw st Tc hPreTrace j hj
      (mode_ne_init_alongTrace_afterFirstStep centre place entry q first hPreTrace j hj1 hj)
  intro i hIndexLeTc hMode
  have hIndexPos : 1 ≤ i := by
    rcases Nat.eq_zero_or_pos i with rfl | h; swap; · exact h
    exfalso
    rw [hPreTrace.start] at hMode
    exact Mode.noConfusion hMode
  obtain ⟨rem, r, -, -, ⟨hrep, hpres⟩, -, -, -, -, -, -⟩ := (hLPackM2 i hIndexLeTc).shiftGeom hMode
  exact canRight_of_position_bound hrep hpres (m := w.length) hw le_rfl
    (rightHeadPos_le_alongTrace centre place entry q first hw hPreTrace hFrontPack (by omega) i hIndexPos hIndexLeTc)

#print axioms rightHeadPos_le_front
#print axioms front_mono_alongTrace
#print axioms rightHeadPos_le_alongTrace
#print axioms rightHeadCanRight_alongTrace
#print axioms frontPack_alongTrace
#print axioms scanRightHeadCanRight_alongTrace
#print axioms tick_target_mode_ne_init
#print axioms mode_ne_init_alongTrace_afterFirstStep
#print axioms shiftRightHeadCanRight_alongTrace

#print axioms landingObligationsAt_of_sansRadiusLedger
#print axioms chainPosInv2_alongTrace
#print axioms needBound_of_landingObligationsSansRadiusLedger

/-! ## 5a. `AuxPack` は 1 手目以降タダ

`AuxPack = ⟨Coupled, FrontPack, CopyPack⟩`（`CloseoutPackRun2:103`）。

* `Coupled` — boot で `coupled_of_idle`（chain は idle）、tick で `coupled_tick`
  （**側条件なし**）→ trace 全域でタダ
* `CopyPack` — boot で `copyPack_boot`、tick で `copyPack_tick`（**側条件なし**）
  → trace 全域でタダ
* `FrontPack` — boot では**偽**（`FrontPack.notInit : mode ≠ init`）。1 手目以降は
  `frontPack_alongTrace` でタダ

よって **`AuxPack` は `1 ≤ i` でタダ**。`AuxPackNotAtBoot.not_auxPack_at_boot` が
示す通り `i = 0` では偽なので、`1 ≤ i` の制限は落とせない。 -/

/-- `Coupled` は trace 全域でタダ（boot は idle chain、tick は側条件なし）。 -/
theorem coupled_alongTrace {w : List (Fin 2)} {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hPreTrace : PreTrace centre place entry q first w st Tc) :
    ∀ i, i ≤ Tc w.length → Coupled (st i).ctl (st i).vm := by
  intro i
  induction i with
  | zero =>
    intro _
    rw [hPreTrace.start]
    exact coupled_of_idle (by rfl)
  | succ n ih =>
    intro hIndexLeTc
    exact coupled_tick (onLetterVM w) leftFirstVM centre place entry q first 2048
      (ih (by omega)) (hPreTrace.trace.tick n (by omega))

/-- `CopyPack` は trace 全域でタダ（`copyPack_boot` ＋ 側条件なしの tick）。 -/
theorem copyPack_alongTrace {w : List (Fin 2)} {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hPreTrace : PreTrace centre place entry q first w st Tc) :
    ∀ i, i ≤ Tc w.length → CopyPack (st i).ctl (st i).vm := by
  intro i
  induction i with
  | zero => intro _; rw [hPreTrace.start]; exact copyPack_boot 2048 w
  | succ n ih =>
    intro hIndexLeTc
    exact copyPack_tick (onLetterVM w) leftFirstVM centre place entry q first 2048
      (ih (by omega)) (hPreTrace.trace.tick n (by omega))

/-- **`AuxPack` は 1 手目以降タダ。** -/
theorem auxPack_alongTrace_afterFirstStep {w : List (Fin 2)} (hw : 0 < w.length)
    {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hPreTrace : PreTrace centre place entry q first w st Tc) :
    ∀ i, 1 ≤ i → i ≤ Tc w.length →
      PalPeg.CloseoutPackRun2.AuxPack (st i).ctl (st i).vm :=
  fun i hIndexPos hIndexLeTc =>
    ⟨coupled_alongTrace centre place entry q first hPreTrace i hIndexLeTc,
     frontPack_alongTrace centre place entry q first hw hPreTrace i hIndexPos hIndexLeTc,
     copyPack_alongTrace centre place entry q first hPreTrace i hIndexLeTc⟩

#print axioms coupled_alongTrace
#print axioms copyPack_alongTrace
#print axioms auxPack_alongTrace_afterFirstStep

/-! ## 5b. 中心ヘッドも動ける — `CentreLedger` の 2/3 はタダ

`CloseoutPackRun47.CentreLedger s := canRight s.center ∧ Sane s.center ∧
(position s.center : ℤ) + value s.radius = position s.right`。

* `Sane s.center` ← `GalilTrailSane.SanePack.saneC`（`CloseoutLPack6.sanePack_pt` が
  `PreTrace` ＋ `LeftLive` だけで trace 全点に与える）— **タダ**
* `canRight s.center` ← `position s.center ≤ position s.right`（`RadLedger.le` ＋ `.nonneg`）
  ＋ `rightHeadPos_le_alongTrace` ＋ `CentreRep`（`LPackM2.centreRep`）— **タダ**
* 残るのは**等式** `position center + value radius = position right` のみ。 -/

/-- **中心ヘッドの `canRight` はタダ。** -/
theorem centreHeadCanRight_alongTrace {w : List (Fin 2)} (hw : 0 < w.length)
    {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hPreTrace : PreTrace centre place entry q first w st Tc)
    (hRadLedger : ∀ j, j ≤ Tc w.length → PalPeg.CloseoutRadPack.RadLedger (st j).ctl (st j).vm)
    (hTcPos : 1 ≤ Tc w.length)
    {i : ℕ} (hIndexPos : 1 ≤ i) (hIndexLeTc : i ≤ Tc w.length)
    (hCentreRep : PalPeg.GalilInvPlus2.CentreRep w (st i).vm) :
    GalilScaffoldChainVerifier.canRight (st i).vm.center := by
  have hle : (position (st i).vm.center : ℤ) ≤ (position (st i).vm.right : ℤ) := by
    have h := (hRadLedger i hIndexLeTc).le
    have hn := (hRadLedger i hIndexLeTc).nonneg
    omega
  have hrb := rightHeadPos_le_alongTrace centre place entry q first hw hPreTrace
    (frontPack_alongTrace centre place entry q first hw hPreTrace) hTcPos i hIndexPos hIndexLeTc
  refine canRight_of_position_bound hCentreRep.1 hCentreRep.2 (m := w.length) hw le_rfl ?_
  have : (position (st i).vm.center : ℤ) ≤ ((2 * w.length - 1 : ℕ) : ℤ) := by
    have : ((position (st i).vm.right : ℕ) : ℤ) ≤ ((2 * w.length - 1 : ℕ) : ℤ) := by
      exact_mod_cast hrb
    omega
  exact_mod_cast this

/-- **`LTickLeaves3.replayLedger` はタダ。**  `replayStart` 相では `LPackM2.centreRep` が
`CentreRep` を持ち、`Sane s.center` は `SanePack.saneC`。 -/
theorem replayStartLedger_alongTrace {w : List (Fin 2)} (hw : 0 < w.length)
    {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hPreTrace : PreTrace centre place entry q first w st Tc)
    (hRadLedger : ∀ j, j ≤ Tc w.length → PalPeg.CloseoutRadPack.RadLedger (st j).ctl (st j).vm)
    (hLPackM2 : ∀ j, j ≤ Tc w.length →
      PalPeg.CloseoutPackRun23.LPackM2 w (st j).ctl (st j).vm)
    (hSanePack : ∀ j, j ≤ Tc w.length → PalPeg.GalilTrailSane.SanePack (st j).ctl (st j).vm)
    (hTcPos : 1 ≤ Tc w.length) :
    ∀ i, i ≤ Tc w.length → (st i).ctl.mode = Mode.replayStart →
      GalilScaffoldChainVerifier.canRight (st i).vm.center ∧ Sane (st i).vm.center := by
  intro i hIndexLeTc hMode
  have hIndexPos : 1 ≤ i := by
    rcases Nat.eq_zero_or_pos i with rfl | h; swap; · exact h
    exfalso
    rw [hPreTrace.start] at hMode
    exact Mode.noConfusion hMode
  exact ⟨centreHeadCanRight_alongTrace centre place entry q first hw hPreTrace hRadLedger hTcPos hIndexPos hIndexLeTc
    ((hLPackM2 i hIndexLeTc).centreRep (Or.inr hMode)), (hSanePack i hIndexLeTc).saneC⟩

/-- **`CentreLedger` の等式は `EntryCounters` から出る。**
`GalilGlueBLeaves.EntryCounters w s := ∃ Rad, ScanInvariant w (position s.center) Rad …
∧ RadiusRep s.radius Rad ∧ …` で、`RadiusRep counter rad := Canonical counter ∧
value counter = rad`、`ScanInvariant.rightPos : position right = position center + Rad`。
差をとれば等式。

**これが `RadLedger.le`（`≤`）と等式の差**: `RadLedger` は半径カウンタが距離を
**超えない**ことしか言わない（探索が活性のあいだ右ヘッドだけ進む場合があるため）。
正確さは `RadiusRep` が担保する。 -/
theorem radiusExact_of_entryCounters {w : List (Fin 2)} {s : GalilVM}
    (hEntryCounters : PalPeg.GalilGlueBLeaves.EntryCounters w s) :
    (position s.center : ℤ) + value s.radius = position s.right := by
  obtain ⟨Rad, hIndexLeTc, hRR, -, -⟩ := hEntryCounters
  rw [hRR.2, hIndexLeTc.rightPos]
  push_cast
  omega

/-- **`CentreLedger` は等式だけに落ちる。** -/
theorem centreLedger_of_radiusExact {w : List (Fin 2)} (hw : 0 < w.length)
    {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hPreTrace : PreTrace centre place entry q first w st Tc)
    (hRadLedger : ∀ j, j ≤ Tc w.length → PalPeg.CloseoutRadPack.RadLedger (st j).ctl (st j).vm)
    (hSanePack : ∀ j, j ≤ Tc w.length → PalPeg.GalilTrailSane.SanePack (st j).ctl (st j).vm)
    (hTcPos : 1 ≤ Tc w.length)
    {i : ℕ} (hIndexPos : 1 ≤ i) (hIndexLeTc : i ≤ Tc w.length)
    (hCentreRep : PalPeg.GalilInvPlus2.CentreRep w (st i).vm)
    (heq : (position (st i).vm.center : ℤ) + value (st i).vm.radius
      = position (st i).vm.right) :
    PalPeg.CloseoutPackRun47.CentreLedger (st i).vm :=
  ⟨centreHeadCanRight_alongTrace centre place entry q first hw hPreTrace hRadLedger hTcPos hIndexPos hIndexLeTc hCentreRep,
    (hSanePack i hIndexLeTc).saneC, heq⟩

#print axioms centreHeadCanRight_alongTrace
#print axioms replayStartLedger_alongTrace
/-- **`CentreLedger` は `EntryCounters` ＋ `CentreRep` から完全に出る。** -/
theorem centreLedger_of_entryCounters {w : List (Fin 2)} (hw : 0 < w.length)
    {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hPreTrace : PreTrace centre place entry q first w st Tc)
    (hRadLedger : ∀ j, j ≤ Tc w.length → PalPeg.CloseoutRadPack.RadLedger (st j).ctl (st j).vm)
    (hSanePack : ∀ j, j ≤ Tc w.length → PalPeg.GalilTrailSane.SanePack (st j).ctl (st j).vm)
    (hTcPos : 1 ≤ Tc w.length)
    {i : ℕ} (hIndexPos : 1 ≤ i) (hIndexLeTc : i ≤ Tc w.length)
    (hCentreRep : PalPeg.GalilInvPlus2.CentreRep w (st i).vm)
    (hEntryCounters : PalPeg.GalilGlueBLeaves.EntryCounters w (st i).vm) :
    PalPeg.CloseoutPackRun47.CentreLedger (st i).vm :=
  centreLedger_of_radiusExact centre place entry q first hw hPreTrace hRadLedger hSanePack hTcPos hIndexPos hIndexLeTc hCentreRep
    (radiusExact_of_entryCounters hEntryCounters)

#print axioms radiusExact_of_entryCounters
#print axioms centreLedger_of_entryCounters
#print axioms centreLedger_of_radiusExact

/-! ## 5c. `LTickLeaves3.initLedger` はタダ

`initVM entry s t`（`GalilScaffoldTopReplay:20`）は
`t.right = right s.right`、`t.center = right s.right`、`t.radius = s.radius` を固定する。
つまり **`t.center = t.right`** なので等式は `value t.radius = 0` に落ち、それは
`RadLedger.initZero`（init 相で `value radius = 0`）。
`canRight t.center = canRight t.right` と `Sane t.center = Sane t.right` は
**次状態が scan 相**（`Tick.init` の行き先）なので §5 の無料補題で出る。

`t` は `initVM` で全成分が決まるわけではない（`periodOnly` などは自由）が、
`CentreLedger` が読むのは `center` / `radius` / `right` の 3 つだけで、
それらは `initVM` が固定するので trace 上の `st (i+1)` から移せる。 -/

/-- **`init` 相の tick は `initVM` で、行き先は `scan` 相。**  `Tick` の 24 構成子のうち
源の mode が `init` なのは `Tick.init` だけ。状態を変数に一般化してから `cases` する
必要がある（非変数の `st 0` / `st 1` に対しては dependent elimination が失敗する）。 -/
theorem init_tick_target_is_scan {w : List (Fin 2)} (x y : State GalilVM)
    (hTick : Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y)
    (hMode : x.ctl.mode = Mode.init) :
    (galilFrameS (PofC centre place entry w) q first).init x.vm y.vm ∧
      y.ctl.mode = Mode.scan := by
  cases hTick with
  | init c s s' hm' hinit => exact ⟨hinit, rfl⟩
  | _ => simp_all

/-- **`LTickLeaves3.initLedger` は trace 上でタダ。** -/
theorem initLedger_alongTrace {w : List (Fin 2)} (hw : 0 < w.length)
    {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hPreTrace : PreTrace centre place entry q first w st Tc)
    (hLPackM2 : ∀ j, j ≤ Tc w.length →
      PalPeg.CloseoutPackRun23.LPackM2 w (st j).ctl (st j).vm)
    (hSanePack : ∀ j, j ≤ Tc w.length → PalPeg.GalilTrailSane.SanePack (st j).ctl (st j).vm)
    (hRadLedger : ∀ j, j ≤ Tc w.length → PalPeg.CloseoutRadPack.RadLedger (st j).ctl (st j).vm)
    (hTcPos : 1 ≤ Tc w.length) :
    ∀ i, i ≤ Tc w.length → (st i).ctl.mode = Mode.init →
      ∀ t : GalilVM, (galilFrameS (PofC centre place entry w) q first).init (st i).vm t →
        PalPeg.CloseoutPackRun47.CentreLedger t := by
  intro i hIndexLeTc hMode t hit
  -- `init` 相は 0 手目だけ（`tick_target_mode_ne_init`）
  have h0 : i = 0 := by
    rcases Nat.eq_zero_or_pos i with h | h
    · exact h
    · exfalso
      obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
      exact tick_target_mode_ne_init (hPreTrace.trace.tick n (by omega)) hMode
  subst h0
  have hi1 : 1 ≤ Tc w.length := hTcPos
  -- trace の 1 手目は同じ `init` 遷移
  obtain ⟨hinit1, hmode1⟩ :=
    init_tick_target_is_scan centre place entry q first (st 0) (st 1)
      (hPreTrace.trace.tick 0 (by omega)) hMode
  obtain ⟨hr1, -, hc1, -, hrad1, -, -, -, -, -, -, -, -⟩ :
    initVM entry (st 0).vm (st 1).vm := hinit1
  obtain ⟨hrt, -, hct, -, hradt, -, -, -, -, -, -, -, -⟩ :
    initVM entry (st 0).vm t := hit
  -- `t` の 3 成分は `st 1` と一致
  have hcc : t.center = (st 1).vm.center := by rw [hct, hc1]
  have hrr : t.right = (st 1).vm.right := by rw [hrt, hr1]
  have hcr1 : (st 1).vm.center = (st 1).vm.right := by rw [hc1, hr1]
  refine ⟨?_, ?_, ?_⟩
  · rw [hcc, hcr1]
    exact scanRightHeadCanRight_alongTrace centre place entry q first hw hPreTrace hLPackM2 hTcPos 1 hi1 hmode1
  · rw [hcc, hcr1]
    exact (hSanePack 1 hi1).saneR
  · have hRadiusZero : value (st 0).vm.radius = 0 := (hRadLedger 0 (by omega)).initZero (by rw [hPreTrace.start]; rfl)
    have hvt : value t.radius = 0 := by rw [hradt]; exact hRadiusZero
    rw [hcc, hrr, hcr1, hvt]
    omega

#print axioms init_tick_target_is_scan
#print axioms initLedger_alongTrace

/-! ## 5d. `CentreEq` — 半径カウンタが中心から右ヘッドまでの距離を正確に測る

```
CentreEq s := (position s.center : ℤ) + value s.radius = position s.right
```

これが `CloseoutPackRun47.CentreLedger` の第 3 節で、`RadLedger.le`（`≤`）からは出ない
（`LPackM2` の 6 場に radius を縛るものは無い）。一次情報で遷移ごとの効果を確認した：

| 遷移 | center | radius | right |
|---|---|---|---|
| `backgroundS` | 不変 | 不変 | 不変 |
| `shiftTick`（`ChainInputSupply:1445`） | `right s.center`（+1） | `dec`（−1） | 不変 |
| `afterCompare` の `radiusAfter`（`TopSearch:37`） | 不変 | **無条件 `inc`** | +1 |
| `beginShiftVM`（`TopShiftCycle:23`） | 不変 | 不変 | 不変 |
| `beginFallbackVM`（`TopFallbackCycle:19`） | 不変 | 不変 | 不変 |
| `restartVM`（`TopRestart:19`） | 不変 | 不変 | 不変 |
| `initVM` / `replayStartVM`（`TopReplay:20,28`） | `= right` | 0 | — |
| fpp 相（`copyOne`/`copyEnd`/`fppStart`/`homeStep`/`fppSlice`/`fppDone`/`atEnd`/`markForward`） | 不変（`fppLens` は `s.fpp` だけを見る） | 不変 | 不変 |
| **rewind 相**（`markBack`/`rewindOne`/`rewindPair`、`rewindLens`） | **動く** | **動く** | **動く** |

`rewindLens.get s = ⟨s.fpp, s.left, s.center, s.right, s.length, s.radius⟩` なので
rewind 相だけが heads と radius を動かす。そこを mode guard で除外すれば
（`choose` / `rewind` / `replayStart`）、`replayStartVM` が出口で
`center = right`、`radius = 0` として**再確立**するので残差ゼロで運べる見込み。 -/

/-- 中心と右ヘッドが同じで半径が 0 なら成立。 -/
theorem radiusExact_of_centreAtRightAndRadiusZero {s : GalilVM} (hc : s.center = s.right)
    (hRadiusZero : value s.radius = 0) :
    (position s.center : ℤ) + value s.radius = position s.right := by
  rw [hc, hRadiusZero]; omega

/-- boot で成立。 -/
theorem radiusExact_at_boot (w : List (Fin 2)) :
    (position (boot w).vm.center : ℤ) + value (boot w).vm.radius
      = position (boot w).vm.right :=
  radiusExact_of_centreAtRightAndRadiusZero (by rfl) (by rfl)

/-- `beginShiftVM'` は center / radius / right を触らない。 -/
theorem radiusExact_after_beginShift {s t : GalilVM} (hb : beginShiftVM' s t)
    (h : (position s.center : ℤ) + value s.radius = position s.right) :
    (position t.center : ℤ) + value t.radius = position t.right := by
  obtain ⟨v, -, ht⟩ := hb
  rw [ht]; exact h

/-- `beginFallbackVM'` も触らない。 -/
theorem radiusExact_after_beginFallback {s t : GalilVM} (hb : beginFallbackVM' s t)
    (h : (position s.center : ℤ) + value s.radius = position s.right) :
    (position t.center : ℤ) + value t.radius = position t.right := by
  obtain ⟨p, ht⟩ := hb
  rw [ht]; exact h

/-- `restartVM` も触らない。 -/
theorem radiusExact_after_restart {s t : GalilVM} (hb : restartVM entry s t)
    (h : (position s.center : ℤ) + value s.radius = position s.right) :
    (position t.center : ℤ) + value t.radius = position t.right := by
  obtain ⟨v, -, -, -, -, ht⟩ := hb
  rw [ht]; exact h

/-- **`replayStartVM` は前提なしで `CentreEq` を再確立する**（`center = right`、
`radius = reset`）。rewind 相で壊れた等式がここで戻る。 -/
theorem radiusExact_after_replayStart {s t : GalilVM} (hb : replayStartVM entry s t) :
    (position t.center : ℤ) + value t.radius = position t.right := by
  obtain ⟨-, hr, -, hc, hrad, -, -, -, -, -, -, -, -⟩ := hb
  refine radiusExact_of_centreAtRightAndRadiusZero ?_ ?_
  · rw [hc, hr]
  · rw [hrad]; rfl

/-- `initVM` は `center = right` にし radius を保つので、init 相の `radius = 0`
（`RadLedger.initZero`）から成立。 -/
theorem radiusExact_after_initVM {s t : GalilVM} (hb : initVM entry s t)
    (hRadiusZero : value s.radius = 0) :
    (position t.center : ℤ) + value t.radius = position t.right := by
  obtain ⟨hr, -, hc, -, hrad, -, -, -, -, -, -, -, -⟩ := hb
  refine radiusExact_of_centreAtRightAndRadiusZero ?_ ?_
  · rw [hc, hr]
  · rw [hrad]; exact hRadiusZero

/-- `backgroundS` は center / radius / right を触らない。 -/
theorem radiusExact_after_background {w : List (Fin 2)} {s t : GalilVM}
    (hb : (galilFrameS (PofC centre place entry w) q first).background s t)
    (h : (position s.center : ℤ) + value s.radius = position s.right) :
    (position t.center : ℤ) + value t.radius = position t.right := by
  obtain ⟨-, hr, -, hcen, -, hrad, -⟩ :=
    backgroundS_fields (PofC centre place entry w) q first hb
  rw [hcen, hr, hrad]; exact h

/-- **`compare` は `radiusExact` を保つ**（一致・不一致とも）。
`compareFound` は `vs.right = right s.right` を無条件に与え、`afterCompare` /
`afterMismatch` は `center` 不変・`radius = inc s.radius`、`afterBirth` は 3 つとも不変。
右ヘッドが 1 進み半径が 1 増えるので等式が保たれる。 -/
theorem radiusExact_after_compare {w : List (Fin 2)} {s t : GalilVM}
    (hCompare : (galilFrameS (PofC centre place entry w) q first).compare s t)
    (hCanRight : GalilScaffoldChainVerifier.canRight s.right)
    (hLeftNonempty : 0 < s.right.head.left.length)
    (hRadiusExact : (position s.center : ℤ) + value s.radius = position s.right) :
    (position t.center : ℤ) + value t.radius = position t.right := by
  obtain ⟨vs, vq, a, -, hvr, -, -, -, hteq⟩ :
    compareFound (PofC centre place entry w) q first s t := hCompare
  have hstep : position (GalilScaffoldChainVerifier.right s.right) = position s.right + 1 :=
    right_position s.right hCanRight hLeftNonempty
  have hc : t.center = s.center := by
    rw [hteq]; cases a <;>
      simp [afterBirth_center, afterCompare_center, afterMismatch_center]
  have hr : t.right = GalilScaffoldChainVerifier.right s.right := by
    rw [hteq]; cases a <;>
      simp [afterBirth_right, afterCompare_right, afterMismatch_right, hvr]
  have hrad : t.radius = inc s.radius := by
    rw [hteq]; cases a <;>
      simp [afterBirth_radius, afterCompare_radius, afterMismatch_radius]
  rw [hc, hr, hrad, inc_value, hstep]
  push_cast
  omega

/-- **`matchedPlace` は `center` / `radius` / `right` を触らない**
（`t = if b then {s with replay := dec s.replay} else s`）。 -/
theorem radiusExact_after_matchedPlace {w : List (Fin 2)} {b : Bool} {s t : GalilVM}
    (hPlace : (galilFrameS (PofC centre place entry w) q first).matchedPlace b s t)
    (hRadiusExact : (position s.center : ℤ) + value s.radius = position s.right) :
    (position t.center : ℤ) + value t.radius = position t.right := by
  have h : t = (if b then {s with replay := dec s.replay} else s) := hPlace
  rw [h]; cases b <;> simpa using hRadiusExact

/-- **fpp 相の遷移は `center` / `radius` / `right` を触らない。**
`fppLens.get s = s.fpp` だけを見るので `t = fppLens.set s (fppLens.get t) = {s with fpp := t.fpp}`。
`copyOne` / `copyEnd` / `fppStart` / `homeStep` / `fppSlice` / `fppDone` / `atEnd` /
`markForward` の 8 遷移が該当する。 -/
theorem radiusExact_after_fppLensStep {s t : GalilVM}
    (hSet : t = fppLens.set s (fppLens.get t))
    (hRadiusExact : (position s.center : ℤ) + value s.radius = position s.right) :
    (position t.center : ℤ) + value t.radius = position t.right := by
  rw [hSet]; exact hRadiusExact

/-- **`shiftOne` は `radiusExact` を保つ。**  `shiftLens` は `right` を見ないので
右ヘッドは不変、`shiftTick` は `center := right s.center`（位置 +1）と
`radius := dec s.radius`（値 −1）。側条件は中心ヘッドが右へ進めること
（`canRight` ＋ 左スタック非空）と半径が正であること。 -/
theorem radiusExact_after_shiftOne {w : List (Fin 2)} {s t : GalilVM}
    (hShiftOne : (galilFrameS (PofC centre place entry w) q first).shiftOne s t)
    (hCanRightCentre : GalilScaffoldChainVerifier.canRight s.center)
    (hCentreLeftNonempty : 0 < s.center.head.left.length)
    (hRadiusPos : 1 ≤ value s.radius)
    (hRadiusExact : (position s.center : ℤ) + value s.radius = position s.right) :
    (position t.center : ℤ) + value t.radius = position t.right := by
  obtain ⟨-, -, -, wv, -, hGet⟩ := hShiftOne.1
  have hSet := hShiftOne.2
  rw [hGet] at hSet
  subst hSet
  have hstep : position (GalilScaffoldChainVerifier.right s.center) = position s.center + 1 :=
    right_position s.center hCanRightCentre hCentreLeftNonempty
  show (position (GalilScaffoldChainVerifier.right s.center) : ℤ) + value (dec s.radius)
    = position s.right
  rw [dec_value, hstep]
  push_cast
  omega

/-! ### mode で守った `radiusExact` の tick 保存

壊れるのは `rewindLens` の 3 遷移（`markBack` / `rewindOne` / `rewindPair`）だけで、
行き先はすべて `choose` / `rewind` / `replayStart`。そこを guard で除外すれば、
出口の `replayStartVM` が前提なしで再確立するので**追加の葉なしで閉じる**。 -/

/-- **mode で守った `radiusExact`。** rewind 相（`choose` / `rewind`）と `replayStart` を
除外する。 -/
def RadiusExactOffRewindPhase (c : Control) (s : GalilVM) : Prop :=
  c.mode ≠ Mode.choose → c.mode ≠ Mode.rewind → c.mode ≠ Mode.replayStart →
    (position s.center : ℤ) + value s.radius = position s.right

/-- **1 tick 保存。**  側入力は init 相の `radius = 0`、scan 相の右ヘッド供給、
shift 相の中心ヘッド供給だけ。 -/
theorem radiusExactOffRewindPhase_tick {w : List (Fin 2)} {x y : State GalilVM}
    (hTick : Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y)
    (hRadiusZeroAtInit : x.ctl.mode = Mode.init → value x.vm.radius = 0)
    (hScanSupply : x.ctl.mode = Mode.scan →
      GalilScaffoldChainVerifier.canRight x.vm.right ∧ 0 < x.vm.right.head.left.length)
    (hShiftSupply : x.ctl.mode = Mode.shift →
      GalilScaffoldChainVerifier.canRight x.vm.center ∧
        0 < x.vm.center.head.left.length ∧ 1 ≤ value x.vm.radius)
    (hPrev : RadiusExactOffRewindPhase x.ctl x.vm) :
    RadiusExactOffRewindPhase y.ctl y.vm := by
  cases hTick with
  | init c s s' hm hInit =>
    intro _ _ _
    exact radiusExact_after_initVM (entry := entry) hInit (hRadiusZeroAtInit hm)
  | scan_wait c s s' hm _ hBg =>
    intro _ _ _
    exact radiusExact_after_background centre place entry q first hBg
      (hPrev (by rw [hm]; decide) (by rw [hm]; decide) (by rw [hm]; decide))
  | scan_count c s s' hm _ _ hBg =>
    intro _ _ _
    exact radiusExact_after_background centre place entry q first hBg
      (hPrev (by rw [hm]; decide) (by rw [hm]; decide) (by rw [hm]; decide))
  | scan_match c s s' s'' o hm _ _ hCompare _ hPlace _ =>
    intro _ _ _
    obtain ⟨hCanRight, hLeftNonempty⟩ := hScanSupply hm
    exact radiusExact_after_matchedPlace centre place entry q first hPlace
      (radiusExact_after_compare centre place entry q first hCompare hCanRight hLeftNonempty
        (hPrev (by rw [hm]; decide) (by rw [hm]; decide) (by rw [hm]; decide)))
  | scan_shift c s s' s'' hm _ _ hCompare _ _ _ hBegin =>
    intro _ _ _
    obtain ⟨hCanRight, hLeftNonempty⟩ := hScanSupply hm
    exact radiusExact_after_beginShift hBegin
      (radiusExact_after_compare centre place entry q first hCompare hCanRight hLeftNonempty
        (hPrev (by rw [hm]; decide) (by rw [hm]; decide) (by rw [hm]; decide)))
  | scan_fallback c s s' s'' hm _ _ hCompare _ _ _ hBegin =>
    intro _ _ _
    obtain ⟨hCanRight, hLeftNonempty⟩ := hScanSupply hm
    exact radiusExact_after_beginFallback hBegin
      (radiusExact_after_compare centre place entry q first hCompare hCanRight hLeftNonempty
        (hPrev (by rw [hm]; decide) (by rw [hm]; decide) (by rw [hm]; decide)))
  | shift_one c s s' hm _ hOne =>
    intro _ _ _
    obtain ⟨hCanRightCentre, hCentreLeftNonempty, hRadiusPos⟩ := hShiftSupply hm
    exact radiusExact_after_shiftOne centre place entry q first hOne hCanRightCentre
      hCentreLeftNonempty hRadiusPos
      (hPrev (by rw [hm]; decide) (by rw [hm]; decide) (by rw [hm]; decide))
  | shift_done c s o hm _ _ =>
    intro _ _ _
    exact hPrev (by rw [hm]; decide) (by rw [hm]; decide) (by rw [hm]; decide)
  | replayStart c s s' o hm hRS _ _ =>
    intro _ _ _
    exact radiusExact_after_replayStart (entry := entry) hRS
  | restart c s s' hm hRestart =>
    intro _ _ _
    exact radiusExact_after_restart (entry := entry) hRestart
      (hPrev (by rw [hm]; decide) (by rw [hm]; decide) (by rw [hm]; decide))
  | copy_one c s s' hm _ h =>
    intro _ _ _
    exact radiusExact_after_fppLensStep h.2
      (hPrev (by rw [hm]; decide) (by rw [hm]; decide) (by rw [hm]; decide))
  | copy_done c s s' hm _ h =>
    intro _ _ _
    exact radiusExact_after_fppLensStep h.2
      (hPrev (by rw [hm]; decide) (by rw [hm]; decide) (by rw [hm]; decide))
  | home_start c s s' hm _ h =>
    intro _ _ _
    exact radiusExact_after_fppLensStep h.2
      (hPrev (by rw [hm]; decide) (by rw [hm]; decide) (by rw [hm]; decide))
  | home_step c s s' hm _ h =>
    intro _ _ _
    exact radiusExact_after_fppLensStep h.2
      (hPrev (by rw [hm]; decide) (by rw [hm]; decide) (by rw [hm]; decide))
  | fpp_slice c s s' hm h =>
    intro _ _ _
    exact radiusExact_after_fppLensStep h.2
      (hPrev (by rw [hm]; decide) (by rw [hm]; decide) (by rw [hm]; decide))
  | fpp_done c s s' hm h =>
    intro _ _ _
    exact radiusExact_after_fppLensStep h.2
      (hPrev (by rw [hm]; decide) (by rw [hm]; decide) (by rw [hm]; decide))
  | markEnd_step c s s' hm _ h =>
    intro _ _ _
    exact radiusExact_after_fppLensStep h.2
      (hPrev (by rw [hm]; decide) (by rw [hm]; decide) (by rw [hm]; decide))
  | markEnd_found c s s' hm _ h => intro hne _ _; exact absurd rfl hne
  | choose_select c s s' hm _ _ h => intro _ hne _; exact absurd rfl hne
  | choose_step c s s' hm _ h => intro hne _ _; exact absurd hm hne
  | rewind_done c s s' hm _ h => intro _ _ hne; exact absurd rfl hne
  | rewind_one c s s' hm _ _ h => intro _ hne _; exact absurd hm hne
  | rewind_pair c s s' hm _ _ h => intro _ hne _; exact absurd hm hne

#print axioms radiusExactOffRewindPhase_tick

/-! ### chain の lag は構成から正規 — `ChainBackLagAt` は人工的な残差だった

実機（`ScaffoldChain`）の lag は `chain.start()` で `radius` から作られ `inc` / `dec` で
しか動かない。だから `Canonical` と非負は**構成から自明**。
`CloseoutPackRun48.LagCan` が `.watch` 相だけに切られていたので `.back` 相が残差に
見えていた。全構成子に広げれば `ChainBackLagAt` は落ちる。

`ChainStep` は lag を**一切変更しない**（`backDone` が `.back` の lag を watch へ
持ち込むだけ）。`ChainMatched` は `inc` のみ。`Internal.take` は `dec` だが
`positive s.lag = true` を要求するので非負が保たれる。`Outer` は `idle`（不変）/
`queued`（`inc`）/`immediate`（不変）。`.broken` は誰も読まない。 -/

/-- **(chain 全体の lag 不変量)** `.copy` / `.back` / `.watch` の lag が正規かつ非負。 -/
structure ChainLagCanonical (z : ChainVM) : Prop where
  copyLag : ∀ (t : GalilScaffoldTape.Tape) (h : Counter) (p : GalilScaffoldPlace.Place)
      (v : Tape) (lag margin : Counter) (ver : PlaceHead),
      z = .copy t h p v lag margin ver → Canonical lag ∧ 0 ≤ value lag
  backLagField : ∀ (v : Tape) (h lag margin : Counter) (ver : PlaceHead),
      z = .back v h lag margin ver → Canonical lag ∧ 0 ≤ value lag
  watchLag : ∀ w : GalilScaffoldChainWatch.State,
      z = .watch w → Canonical w.lag ∧ 0 ≤ value w.lag

theorem chainLagCanonical_idle : ChainLagCanonical .idle :=
  ⟨(fun _ _ _ _ _ _ _ h => by cases h), (fun _ _ _ _ _ h => by cases h),
    (fun _ h => by cases h)⟩

theorem chainLagCanonical_broken (w : GalilScaffoldChainWatch.State) :
    ChainLagCanonical (.broken w) :=
  ⟨(fun _ _ _ _ _ _ _ h => by cases h), (fun _ _ _ _ _ h => by cases h),
    (fun _ h => by cases h)⟩

/-- **誕生時**: `chainStart` は `lag = radius` なので `RadLedger` の 2 場でタダ。 -/
theorem chainLagCanonical_chainStart (answer : GalilScaffoldTape.Tape) (c : Fin 3)
    (walker : GalilScaffoldPlace.Place) (verifier : PlaceHead) (radius : Counter)
    (hCanonical : Canonical radius) (hNonneg : 0 ≤ value radius) :
    ChainLagCanonical (chainStart answer c walker verifier radius) := by
  refine ⟨fun t h p v lag margin ver heq => ?_, (fun _ _ _ _ _ h => by cases h),
    (fun _ h => by cases h)⟩
  unfold chainStart at heq
  injection heq with _ _ _ _ h5 _ _
  subst h5
  exact ⟨hCanonical, hNonneg⟩

/-- **`ChainStep` は lag 不変量を保つ。** -/
theorem chainLagCanonical_step {x z : ChainVM} (hInv : ChainLagCanonical x)
    (hStep : ChainStep x z) : ChainLagCanonical z := by
  obtain ⟨hCopy, hBack, hWatch⟩ := hInv
  cases hStep with
  | idle => exact chainLagCanonical_idle
  | brokenIdle w => exact chainLagCanonical_broken w
  | copyBit t h p v lag margin ver a _ _ _ =>
    refine ⟨fun t' h' p' v' lag' margin' ver' heq => ?_,
      (fun _ _ _ _ _ heq => by cases heq), (fun _ heq => by cases heq)⟩
    injection heq with _ _ _ _ h5 _ _
    subst h5
    exact hCopy t h p v lag margin ver rfl
  | copyEnd t h p v lag margin ver b _ _ _ =>
    refine ⟨(fun _ _ _ _ _ _ _ heq => by cases heq), fun v' h' lag' margin' ver' heq => ?_,
      (fun _ heq => by cases heq)⟩
    injection heq with _ _ h3 _ _
    subst h3
    exact hCopy t h p v lag margin ver rfl
  | backStep v h lag margin ver _ =>
    refine ⟨(fun _ _ _ _ _ _ _ heq => by cases heq), fun v' h' lag' margin' ver' heq => ?_,
      (fun _ heq => by cases heq)⟩
    injection heq with _ _ h3 _ _
    subst h3
    exact hBack v h lag margin ver rfl
  | backDone v h lag margin ver _ =>
    refine ⟨(fun _ _ _ _ _ _ _ heq => by cases heq), (fun _ _ _ _ _ heq => by cases heq),
      fun w heq => ?_⟩
    injection heq with hw
    subst hw
    exact hBack v h lag margin ver rfl
  | watchStep w w' hInternal =>
    refine ⟨(fun _ _ _ _ _ _ _ heq => by cases heq), (fun _ _ _ _ _ heq => by cases heq),
      fun w'' heq => ?_⟩
    injection heq with hw
    subst hw
    obtain ⟨hCan, hNonneg⟩ := hWatch w rfl
    cases hInternal with
    | idle _ => exact ⟨hCan, hNonneg⟩
    | take hPositive _ =>
      have hpos : 0 < value w.lag := (positive_iff w.lag hCan).1 hPositive
      refine ⟨dec_canonical _ hCan, ?_⟩
      show (0 : ℤ) ≤ value (dec w.lag)
      rw [dec_value]
      omega

/-- **`ChainMatched` は lag 不変量を保つ。** -/
theorem chainLagCanonical_matched {x z : ChainVM} (hInv : ChainLagCanonical x)
    (hMatched : ChainMatched x z) : ChainLagCanonical z := by
  obtain ⟨hCopy, hBack, hWatch⟩ := hInv
  cases hMatched with
  | idle => exact chainLagCanonical_idle
  | copy t h p v lag margin ver =>
    refine ⟨fun _ _ _ _ _ _ _ heq => ?_, (fun _ _ _ _ _ heq => by cases heq),
      (fun _ heq => by cases heq)⟩
    injection heq with _ _ _ _ h5 _ _
    subst h5
    obtain ⟨hCan, hNonneg⟩ := hCopy t h p v lag margin ver rfl
    refine ⟨inc_canonical _ hCan, ?_⟩
    show (0 : ℤ) ≤ value (inc lag)
    rw [inc_value]
    omega
  | back v h lag margin ver =>
    refine ⟨(fun _ _ _ _ _ _ _ heq => by cases heq), fun _ _ _ _ _ heq => ?_,
      (fun _ heq => by cases heq)⟩
    injection heq with _ _ h3 _ _
    subst h3
    obtain ⟨hCan, hNonneg⟩ := hBack v h lag margin ver rfl
    refine ⟨inc_canonical _ hCan, ?_⟩
    show (0 : ℤ) ≤ value (inc lag)
    rw [inc_value]
    omega
  | watch w w' hOuter =>
    refine ⟨(fun _ _ _ _ _ _ _ heq => by cases heq), (fun _ _ _ _ _ heq => by cases heq),
      fun w'' heq => ?_⟩
    injection heq with hw
    subst hw
    obtain ⟨hCan, hNonneg⟩ := hWatch w rfl
    cases hOuter with
    | queued _ =>
      refine ⟨inc_canonical _ hCan, ?_⟩
      show (0 : ℤ) ≤ value (inc w.lag)
      rw [inc_value]
      omega
    | immediate _ _ => exact ⟨hCan, hNonneg⟩
  | breaks w w' _ => exact chainLagCanonical_broken w'

#print axioms chainLagCanonical_idle
#print axioms chainLagCanonical_chainStart
#print axioms chainLagCanonical_step
#print axioms chainLagCanonical_matched

/-- chain が変わらない遷移では不変量はそのまま。 -/
theorem chainLagCanonical_of_chainEq {s t : GalilVM} (hEq : t.chain = s.chain)
    (hInv : ChainLagCanonical s.chain) : ChainLagCanonical t.chain := by
  rw [hEq]; exact hInv

/-- `chainShiftOne` は lag を触らない。 -/
theorem chainLagCanonical_shiftOne {v : GalilScaffoldChainWatch.State}
    (hInv : ChainLagCanonical (ChainVM.watch v)) :
    ChainLagCanonical (ChainVM.watch (chainShiftOne v)) := by
  obtain ⟨hCan, hNonneg⟩ := hInv.watchLag v rfl
  refine ⟨(fun _ _ _ _ _ _ _ h => by cases h), (fun _ _ _ _ _ h => by cases h),
    fun w h => ?_⟩
  injection h with hw
  subst hw
  exact ⟨hCan, hNonneg⟩

/-- `immediate` は lag を触らない。 -/
theorem chainLagCanonical_immediate {v : GalilScaffoldChainWatch.State}
    (hInv : ChainLagCanonical (ChainVM.watch v)) :
    ChainLagCanonical (ChainVM.watch (GalilScaffoldChainWatch.immediate v)) := by
  obtain ⟨hCan, hNonneg⟩ := hInv.watchLag v rfl
  refine ⟨(fun _ _ _ _ _ _ _ h => by cases h), (fun _ _ _ _ _ h => by cases h),
    fun w h => ?_⟩
  injection h with hw
  subst hw
  exact ⟨hCan, hNonneg⟩

/-- **scan background を通した搬送。**  chain が誕生する場合は `chainStart` なので
`RadLedger` の 2 場でタダ、さもなくば `ChainStep`。 -/
theorem chainLagCanonical_background {w : List (Fin 2)} {s t : GalilVM}
    (hBg : (galilFrameS (PofC centre place entry w) q first).background s t)
    (hInv : ChainLagCanonical s.chain)
    (hRadiusCanonical : Canonical s.radius) (hRadiusNonneg : 0 ≤ value s.radius) :
    ChainLagCanonical t.chain := by
  by_cases hIdle : s.chain = ChainVM.idle
  · rcases backgroundS_idle (PofC centre place entry w) q first hBg hIdle with
      ⟨-, hz⟩ | ⟨-, hz⟩
    · rw [hz]; exact chainLagCanonical_idle
    · rw [hz]
      exact chainLagCanonical_chainStart _ _ _ _ _ hRadiusCanonical hRadiusNonneg
  · obtain ⟨y, hStep, hy⟩ :=
      backgroundS_chainTick (PofC centre place entry w) q first hBg hIdle
    simp only [Bool.false_eq_true, reduceIte] at hy
    rw [hy]
    exact chainLagCanonical_step hInv hStep

#print axioms chainLagCanonical_of_chainEq
#print axioms chainLagCanonical_shiftOne
#print axioms chainLagCanonical_immediate
/-! ### `chainAt` — tick の chain 効果の分類器（既にあった）

`compareFound` の 8 番目の成分は
`chainAt a found answer c walker ver radius s.chain vs.chain` で、これが
**tick の chain 効果の分類器そのもの**（`GalilScaffoldTopSearch:130`）:

```
chainAt a found … x z :=
  (x ≠ .idle ∧ ChainTick a x z) ∨
  (x = .idle ∧ found = false ∧ z = .idle) ∨
  (x = .idle ∧ found = true ∧ (if a then ChainMatched (chainStart …) z else z = chainStart …))
ChainTick a x z := ∃ y, ChainStep x y ∧ (if a then ChainMatched y z else z = y)
```

`lpackM3_tick` は `scan_match` / `scan_shift` の各ケースでこれを手で開いていた
（`Run49:162–290` の約 60 行）。**分類器に対する補題を 1 本書けば、chain の不変量は
すべてそれに乗る**（`LagCan` / `ChainPositionLedger` / `ChainLagCanonical` …）。 -/

/-- **`ChainTick` を通した搬送。** -/
theorem chainLagCanonical_chainTick {a : Bool} {x z : ChainVM}
    (hInv : ChainLagCanonical x) (hTick : ChainTick a x z) : ChainLagCanonical z := by
  obtain ⟨y, hStep, hAfter⟩ := hTick
  have hy := chainLagCanonical_step hInv hStep
  cases a with
  | true =>
    rw [if_pos rfl] at hAfter
    exact chainLagCanonical_matched hy hAfter
  | false =>
    rw [if_neg (by decide)] at hAfter
    rw [hAfter]
    exact hy

/-- **`chainAt` を通した搬送。**  誕生の場合の `chainStart` は `lag = radius` なので
`RadLedger` の 2 場でタダ。**これが tick の chain 効果に対する唯一の窓口。** -/
theorem chainLagCanonical_chainAt {a found : Bool} {ans : GalilScaffoldTape.Tape} {c : Fin 3}
    {wk : GalilScaffoldPlace.Place} {ver : PlaceHead} {rad : Counter} {x z : ChainVM}
    (hInv : ChainLagCanonical x) (hCanonical : Canonical rad) (hNonneg : 0 ≤ value rad)
    (hAt : chainAt a found ans c wk ver rad x z) : ChainLagCanonical z := by
  rcases hAt with ⟨-, hTick⟩ | ⟨-, -, hz⟩ | ⟨-, -, hStart⟩
  · exact chainLagCanonical_chainTick hInv hTick
  · rw [hz]; exact chainLagCanonical_idle
  · cases a with
    | true =>
      rw [if_pos rfl] at hStart
      exact chainLagCanonical_matched
        (chainLagCanonical_chainStart ans c wk ver rad hCanonical hNonneg) hStart
    | false =>
      rw [if_neg (by decide)] at hStart
      rw [hStart]
      exact chainLagCanonical_chainStart ans c wk ver rad hCanonical hNonneg

/-- **`compare` を通した搬送。**  `compareFound` の chain 成分は `chainAt`、
そして `afterBirth` は chain を `afterBirth_chain` で書き換えるだけ。 -/
theorem chainLagCanonical_compare {w : List (Fin 2)} {s t : GalilVM}
    (hCompare : (galilFrameS (PofC centre place entry w) q first).compare s t)
    (hInv : ChainLagCanonical s.chain)
    (hCanonical : Canonical s.radius) (hNonneg : 0 ≤ value s.radius) :
    ChainLagCanonical t.chain := by
  obtain ⟨vs, vq, a, -, -, -, -, hAt, hteq⟩ :
    compareFound (PofC centre place entry w) q first s t := hCompare
  have hchain : t.chain = vs.chain := by
    rw [hteq, afterBirth_chain]
    cases a <;> rfl
  rw [hchain]
  exact chainLagCanonical_chainAt hInv hCanonical hNonneg hAt

#print axioms chainLagCanonical_chainTick
#print axioms chainLagCanonical_chainAt
/-- **1 tick 搬送。**  側入力は `RadLedger` の 2 場（`Canonical radius` と非負）だけ。
chain が変わる遷移はすべて §上の分類器経由の補題で処理する。 -/
theorem chainLagCanonical_tick {w : List (Fin 2)} {x y : State GalilVM}
    (hTick : Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y)
    (hCanonical : Canonical x.vm.radius) (hNonneg : 0 ≤ value x.vm.radius)
    (hInv : ChainLagCanonical x.vm.chain) : ChainLagCanonical y.vm.chain := by
  cases hTick with
  | init c s s' hm hInit =>
    obtain ⟨-, -, -, -, -, -, -, -, -, hch, -⟩ : initVM entry s s' := hInit
    rw [show s'.chain = ChainVM.idle from hch]; exact chainLagCanonical_idle
  | scan_wait c s s' hm _ hBg =>
    exact chainLagCanonical_background centre place entry q first hBg hInv hCanonical hNonneg
  | scan_count c s s' hm _ _ hBg =>
    exact chainLagCanonical_background centre place entry q first hBg hInv hCanonical hNonneg
  | scan_match c s s' s'' o hm _ _ hCompare _ hPlace _ =>
    have hEq : s''.chain = s'.chain := by
      have h : s'' = (if c.replaying then {s' with replay := dec s'.replay} else s') := hPlace
      rw [h]; split <;> rfl
    rw [hEq]
    exact chainLagCanonical_compare centre place entry q first hCompare hInv hCanonical hNonneg
  | scan_shift c s s' s'' hm _ _ hCompare _ _ _ hBegin =>
    obtain ⟨v, hv⟩ := hBegin
    rw [show s''.chain = ChainVM.watch (GalilScaffoldChainWatch.immediate v) from by
      rw [hv.2]]
    refine chainLagCanonical_immediate ?_
    rw [show ChainVM.watch v = s'.chain from hv.1.symm]
    exact chainLagCanonical_compare centre place entry q first hCompare hInv hCanonical hNonneg
  | scan_fallback c s s' s'' hm _ _ hCompare _ _ _ hBegin =>
    obtain ⟨pl, hv⟩ := hBegin
    rw [show s''.chain = ChainVM.idle from by rw [hv]]
    exact chainLagCanonical_idle
  | shift_one c s s' hm _ hOne =>
    obtain ⟨-, -, -, wv, hw, hGet⟩ := hOne.1
    have hSet := hOne.2
    rw [hGet] at hSet
    subst hSet
    refine chainLagCanonical_shiftOne ?_
    rw [show ChainVM.watch wv = s.chain from hw.symm]
    exact hInv
  | shift_done c s o hm _ _ => exact hInv
  | replayStart c s s' o hm hRS _ _ =>
    obtain ⟨-, -, -, -, -, -, -, -, -, hch, -, -, -⟩ : replayStartVM entry s s' := hRS
    rw [show s'.chain = ChainVM.idle from hch]; exact chainLagCanonical_idle
  | restart c s s' hm hRestart =>
    obtain ⟨v, -, -, -, -, ht⟩ : restartVM entry s s' := hRestart
    rw [show s'.chain = ChainVM.idle from by rw [ht]]; exact chainLagCanonical_idle
  | copy_one c s s' hm _ h => exact chainLagCanonical_of_chainEq (by rw [h.2]; rfl) hInv
  | copy_done c s s' hm _ h => exact chainLagCanonical_of_chainEq (by rw [h.2]; rfl) hInv
  | home_start c s s' hm _ h => exact chainLagCanonical_of_chainEq (by rw [h.2]; rfl) hInv
  | home_step c s s' hm _ h => exact chainLagCanonical_of_chainEq (by rw [h.2]; rfl) hInv
  | fpp_slice c s s' hm h => exact chainLagCanonical_of_chainEq (by rw [h.2]; rfl) hInv
  | fpp_done c s s' hm h => exact chainLagCanonical_of_chainEq (by rw [h.2]; rfl) hInv
  | markEnd_step c s s' hm _ h => exact chainLagCanonical_of_chainEq (by rw [h.2]; rfl) hInv
  | markEnd_found c s s' hm _ h => exact chainLagCanonical_of_chainEq (by rw [h.2]; rfl) hInv
  | choose_select c s s' hm _ _ h => exact chainLagCanonical_of_chainEq (by rw [h.2]; rfl) hInv
  | choose_step c s s' hm _ h => exact chainLagCanonical_of_chainEq (by rw [h.2]; rfl) hInv
  | rewind_done c s s' hm _ h => exact chainLagCanonical_of_chainEq (by rw [h.2]; rfl) hInv
  | rewind_one c s s' hm _ _ h => exact chainLagCanonical_of_chainEq (by rw [h.2]; rfl) hInv
  | rewind_pair c s s' hm _ _ h => exact chainLagCanonical_of_chainEq (by rw [h.2]; rfl) hInv

/-- **trace 全域での搬送。**  新規入力ゼロ（`RadLedger` は `radLedger_pt` でタダ）。 -/
theorem chainLagCanonical_alongTrace {w : List (Fin 2)} (hw : 0 < w.length)
    {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hPreTraceIMW : PalPeg.CloseoutCheckW.PreTraceIMW centre place entry q first w st Tc) :
    ∀ i, i ≤ Tc w.length → ChainLagCanonical (st i).vm.chain := by
  have hPreTrace := hPreTraceIMW.base.pre
  have hRadLedger := radLedger_pt centre place entry q first hw hPreTrace
    (fun j hj => leftLive_of_lpackM (hPreTraceIMW.packs j hj).pack)
  intro i
  induction i with
  | zero =>
    intro _
    rw [hPreTrace.start]
    exact chainLagCanonical_idle
  | succ n ih =>
    intro hIndexLeTc
    exact chainLagCanonical_tick centre place entry q first
      (hPreTrace.trace.tick n (by omega))
      (hRadLedger n (by omega)).canon (hRadLedger n (by omega)).nonneg
      (ih (by omega))

#print axioms chainLagCanonical_tick
#print axioms chainLagCanonical_alongTrace

#print axioms chainLagCanonical_compare

#print axioms chainLagCanonical_background


#print axioms radiusExact_after_shiftOne

#print axioms radiusExact_after_compare
#print axioms radiusExact_after_matchedPlace
#print axioms radiusExact_after_fppLensStep

#print axioms radiusExact_after_background
#print axioms radiusExact_of_centreAtRightAndRadiusZero
#print axioms radiusExact_at_boot
#print axioms radiusExact_after_beginShift
#print axioms radiusExact_after_beginFallback
#print axioms radiusExact_after_restart
#print axioms radiusExact_after_replayStart
#print axioms radiusExact_after_initVM

/-! ## 5e. `LPackM3` を trace に運ぶ（1 手目から）

`LTickLeaves3` の 4 場のうち `initLedger`（§5c）と `replayLedger`（§5b）はタダになった。
残るのは `backLag`（`.back` 相の lag 形状）と `shiftExitLedger`（`shift_done` での
`CentreLedger`）の 2 場だけ。それを名前付きの残差として取り、`LPackM3` を trace に運ぶ。

`i = 0` から始められないのは `AuxPack` が boot で偽だから
（`AuxPackNotAtBoot.not_auxPack_at_boot`、機械検査済み）。`1 ≤ i` から始める。
`LPackM3 (st 1)` は `initLedger_alongTrace`（§5c）で作る。 -/

/-- **(NAMED, trace 形) まだ残っている 3 場。**

* `backLag` — chain の `.back` 相の lag 形状（`LTickLeaves3`）
* `shiftExitLedger` — `shift_done` での `CentreLedger`（`LTickLeaves3`）
* `rewindMargin` — rewind 相での左ヘッドの余裕（`Extra8`）

`LTickLeaves3` の他の 2 場（`initLedger` / `replayLedger`）と `Extra8.scanAvail` と
`CentreLive` はすべてタダになった。 -/
structure ChainBackLagAndShiftExitLedgerAt (w : List (Fin 2)) (c : Control) (s : GalilVM) :
    Prop where
  backLag : ∀ (v : Tape) (h lag margin : Counter) (ver : PlaceHead),
    s.chain = .back v h lag margin ver → Canonical lag ∧ 0 ≤ value lag
  shiftExitLedger : c.mode = Mode.shift →
    ¬ (galilFrameS (PofC centre place entry w) q first).remainingPos s → CentreLedger s
  rewindMargin : c.mode = Mode.rewind → 2 ≤ position s.left

/-- **`LTickLeaves3` は残り 2 場だけから trace 全域で出る。** -/
theorem lTickLeaves3_alongTrace {w : List (Fin 2)} (hw : 0 < w.length)
    {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hPreTrace : PreTrace centre place entry q first w st Tc)
    (hRadLedger : ∀ j, j ≤ Tc w.length →
      PalPeg.CloseoutRadPack.RadLedger (st j).ctl (st j).vm)
    (hLPackM2 : ∀ j, j ≤ Tc w.length → LPackM2 w (st j).ctl (st j).vm)
    (hSanePack : ∀ j, j ≤ Tc w.length → PalPeg.GalilTrailSane.SanePack (st j).ctl (st j).vm)
    (hTcPos : 1 ≤ Tc w.length)
    (hRes : ∀ j, j ≤ Tc w.length →
      ChainBackLagAndShiftExitLedgerAt centre place entry q first w (st j).ctl (st j).vm) :
    ∀ i, i ≤ Tc w.length → LTickLeaves3 centre place entry q first w (st i).ctl (st i).vm :=
  fun i hIndexLeTc =>
    { backLag := (hRes i hIndexLeTc).backLag
      initLedger := initLedger_alongTrace centre place entry q first hw hPreTrace hLPackM2
        hSanePack hRadLedger hTcPos i hIndexLeTc
      shiftDoneLedger := (hRes i hIndexLeTc).shiftExitLedger
      replayLedger := replayStartLedger_alongTrace centre place entry q first hw hPreTrace
        hRadLedger hLPackM2 hSanePack hTcPos i hIndexLeTc }

/-- **`LPackM3` を trace に運ぶ（1 手目から）。**  新規入力は `hSP`（`ShiftPal`）と
残り 2 場 `hRes` だけ。 -/
theorem lpackM3_alongTrace_afterFirstStep {w : List (Fin 2)} (hw : 0 < w.length)
    {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hPreTraceIMW : PalPeg.CloseoutCheckW.PreTraceIMW centre place entry q first w st Tc)
    (hTcPos : 1 ≤ Tc w.length)
    (hSP : ∀ x : State GalilVM, BigPack2MG7W centre place entry q first w x →
      ScanNR x → ShiftPal centre place entry q first w x.vm)
    (hRes : ∀ j, j ≤ Tc w.length →
      ChainBackLagAndShiftExitLedgerAt centre place entry q first w (st j).ctl (st j).vm) :
    ∀ i, 1 ≤ i → i ≤ Tc w.length → LPackM3 w (st i).ctl (st i).vm := by
  have hPreTrace := hPreTraceIMW.base.pre
  have hLPackM2 : ∀ j, j ≤ Tc w.length → LPackM2 w (st j).ctl (st j).vm :=
    fun j hj => (hPreTraceIMW.packs j hj).m2
  have hSanePack : ∀ j, j ≤ Tc w.length →
      PalPeg.GalilTrailSane.SanePack (st j).ctl (st j).vm :=
    PalPeg.CloseoutLPack6.sanePack_pt centre place entry q first hw hPreTrace
      (fun j hj => leftLive_of_lpackM (hPreTraceIMW.packs j hj).pack)
  have hRadLedger := radLedger_pt centre place entry q first hw hPreTrace
    (fun j hj => leftLive_of_lpackM (hPreTraceIMW.packs j hj).pack)
  have hAuxPack := auxPack_alongTrace_afterFirstStep centre place entry q first hw hPreTrace
  have hL3 := lTickLeaves3_alongTrace centre place entry q first hw hPreTrace hRadLedger
    hLPackM2 hSanePack hTcPos hRes
  -- 1 手目
  obtain ⟨hinit1, hMode1⟩ :=
    init_tick_target_is_scan centre place entry q first (st 0) (st 1)
      (hPreTrace.trace.tick 0 (by omega))
      (by rw [hPreTrace.start]; rfl)
  have hbase : LPackM3 w (st 1).ctl (st 1).vm := by
    refine ⟨hLPackM2 1 hTcPos, fun _ => ?_, ?_⟩
    · exact initLedger_alongTrace centre place entry q first hw hPreTrace hLPackM2 hSanePack
        hRadLedger hTcPos 0 (by omega) (by rw [hPreTrace.start]; rfl) (st 1).vm hinit1
    · obtain ⟨-, -, -, -, -, -, -, -, -, hch, -⟩ :
        initVM entry (st 0).vm (st 1).vm := hinit1
      rw [hch]; exact lagCan_idle
  intro i
  induction i with
  | zero => intro hIndexPos; exact absurd hIndexPos (by omega)
  | succ n ih =>
    intro _ hIndexLeTc
    rcases Nat.eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero n)) with h1 | h1
    · -- n + 1 = 1
      have : n = 0 := by omega
      subst this; exact hbase
    · have hn1 : 1 ≤ n := by omega
      have hPrev := ih hn1 (by omega)
      have hBig : BigPack2MG7W centre place entry q first w (st n) :=
        ⟨hPreTraceIMW.packs n (by omega), hAuxPack n hn1 (by omega),
         PalPeg.GalilTrailRad.centreLive_trace centre place entry q first w hw st Tc
           hPreTrace n (by omega),
         ⟨(hRes n (by omega)).rewindMargin,
          fun hm _ => scanRightHeadCanRight_alongTrace centre place entry q first hw
            hPreTrace hLPackM2 hTcPos n (by omega) hm⟩⟩
      have hLN := lticksN_of_lpackM2_W centre place entry q first hBig
        (hLPackM2 n (by omega))
      exact lpackM3_tick' centre place entry q first hPrev hLN
        (hAuxPack n hn1 (by omega))
        (lTickLeaves2_of_shiftPalG centre place entry q first (hLPackM2 n (by omega)) hLN
          (fun hs => hSP (st n) hBig hs))
        (hL3 n (by omega)) (hPreTrace.trace.tick n (by omega))

#print axioms lTickLeaves3_alongTrace
#print axioms lpackM3_alongTrace_afterFirstStep

/-! ## 6. 残差は 3 場 — `shiftDone` は完全に放電された

§3 で半径台帳（`RadLedger`）、§5 で `canRight`（trace 予算 ＋ `LPackM2.shiftGeom`）が
出たので、`LandingObligationsAt.shiftDone` は**新規入力ゼロで**得られる。残るのは
`bg` / `matchLand` / `entryLand` の 3 場。 -/

/-- **(NAMED, trace 形) 残り 3 場。** -/
structure ScanLandingObligationsAt (w : List (Fin 2)) (c : Control) (s : GalilVM) : Prop where
  bg : ∀ t : GalilVM, c.mode = Mode.scan → ChainPositionInvariantWithShiftPhase w c s →
    (galilFrameS (PofC centre place entry w) q first).background s t →
    ScanNR ⟨c, t⟩ → t.chain ≠ ChainVM.idle → ScanPositionPayloadWithChainLedger w t
  matchLand : ∀ (s' t : GalilVM) (o b : Bool), c.mode = Mode.scan → ChainPositionInvariantWithShiftPhase w c s →
    (galilFrameS (PofC centre place entry w) q first).compare s s' →
    (galilFrameS (PofC centre place entry w) q first).matched s' →
    (galilFrameS (PofC centre place entry w) q first).matchedPlace c.replaying s' t →
    ScanNR ⟨{c with clock := 2048, output := o, replaying := c.replaying && b}, t⟩ →
    t.chain ≠ ChainVM.idle → ScanPositionPayloadWithChainLedger w t
  entryLand : ∀ s' t : GalilVM, c.mode = Mode.scan → ChainPositionInvariantWithShiftPhase w c s →
    (galilFrameS (PofC centre place entry w) q first).compare s s' →
    ¬ (galilFrameS (PofC centre place entry w) q first).matched s' →
    shiftGuardVM s' → beginShiftVM' s' t → ShiftPhaseChainLedger t

/-- **(NAMED, trace 形) 残り 3 場を trace の各点で。** -/
def ScanLandingObligationsAlongTrace (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ) : Prop :=
  ∀ i, i ≤ Tc w.length → ScanLandingObligationsAt centre place entry q first w (st i).ctl (st i).vm

/-- **`needL'` の上界を残り 3 場だけから。**  `shiftDone` 場は内部で放電する
（半径台帳は `radLedger_pt`、`canRight` は `shiftRightHeadCanRight_alongTrace`、どちらも新規入力ゼロ）。 -/
theorem needBound_of_scanLandingObligations {w : List (Fin 2)} (hw : 0 < w.length)
    {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hPreTrace : PalPeg.CloseoutCheckW.PreTraceIMW centre place entry q first w st Tc)
    (hChainPosInv2AtOrigin : ChainPositionInvariantWithShiftPhase w (st 0).ctl (st 0).vm)
    (hres : ScanLandingObligationsAlongTrace centre place entry q first w st Tc)
    (hVerRun : VerRun centre place entry q first w (st 0)) :
    ∀ m, m < w.length → ∀ i, i ≤ Tc (m+1) →
      PalPeg.GalilLookRefined.needL' w st i ≤ m + 1 := by
  have hll : ∀ i, i ≤ Tc w.length →
      PalPeg.GalilTrailSane.LeftLive (st i).ctl (st i).vm :=
    fun i hIndexLeTc => leftLive_of_lpackM (hPreTrace.packs i hIndexLeTc).pack
  have hRadLedger := radLedger_pt centre place entry q first hw hPreTrace.base.pre hll
  have hcan := shiftRightHeadCanRight_alongTrace centre place entry q first hw hPreTrace.base.pre
    (fun j hj => (hPreTrace.packs j hj).m2)
  refine needBound_of_landingObligationsSansRadiusLedger centre place entry q first hw hPreTrace hChainPosInv2AtOrigin (fun i hIndexLeTc => ?_) hVerRun
  exact ⟨(hres i hIndexLeTc).bg, (hres i hIndexLeTc).matchLand, (hres i hIndexLeTc).entryLand,
    fun hMode _ => hcan i hIndexLeTc hMode⟩

#print axioms landingObligationsAt_of_sansRadiusLedger
#print axioms needBound_of_scanLandingObligations

/-! ## 7. `bg` 場 — 供給に分解する（状態局所版）

`CloseoutPackRun48.h_bgP2_of_supply` は `hRightHeadRep` / `hVerifierRep` / `hLagCan` / `hstart` の 4 入力を
**すべて源状態 `(c, s)` でだけ**使う（`Run48:186–192`）。global 形のままでは
`hVerifierRep` が任意の scan 状態で verifier の入力表現を要求するので偽の疑いが強い。
そこで状態局所版を置く。本体は Run48 の 18 行と同じ論法（`backgroundS_fields` で
`left`/`right`/`center`/`radius` が保存、`backgroundS_chainTick` で chain 効果が
素の `ChainStep`、`chainPos_step_of_supply` で `ChainPositionLedger` が運ばれる）。 -/

/-- **`ScanLandingObligationsAt.bg` を 4 つの局所供給に分解する。** -/
theorem backgroundLanding_of_supply {w : List (Fin 2)} {c : Control} {s : GalilVM}
    (hRightHeadRep : c.mode = Mode.scan → ChainPositionInvariantWithShiftPhase w c s →
      GalilScaffoldInputTrace.Represents s.right.head w ∧ s.right.head.focus ≠ none)
    (hVerifierRep : c.mode = Mode.scan → ChainPositionInvariantWithShiftPhase w c s → VerRep w s.chain)
    (hLagCan : c.mode = Mode.scan → ChainPositionInvariantWithShiftPhase w c s →
      PalPeg.CloseoutPackRun48.LagCan s.chain)
    (hstart : ∀ t : GalilVM, c.mode = Mode.scan → ChainPositionInvariantWithShiftPhase w c s →
      s.chain = ChainVM.idle →
      (galilFrameS (PofC centre place entry w) q first).background s t →
      ScanNR ⟨c, t⟩ → t.chain ≠ ChainVM.idle → ScanPositionPayloadWithChainLedger w t) :
    ∀ t : GalilVM, c.mode = Mode.scan → ChainPositionInvariantWithShiftPhase w c s →
      (galilFrameS (PofC centre place entry w) q first).background s t →
      ScanNR ⟨c, t⟩ → t.chain ≠ ChainVM.idle → ScanPositionPayloadWithChainLedger w t := by
  intro t hm hx hb hs hni
  by_cases hIndexLeTc : s.chain = ChainVM.idle
  · exact hstart t hm hx hIndexLeTc hb hs hni
  · have P : ScanPositionPayloadWithChainLedger w s := hx.payload hs hIndexLeTc
    obtain ⟨hl, hr, -, hcen, -, hrad, -⟩ :=
      backgroundS_fields (PofC centre place entry w) q first hb
    have hstep : ChainStep s.chain t.chain := by
      obtain ⟨y, hst, hy⟩ :=
        backgroundS_chainTick (PofC centre place entry w) q first hb hIndexLeTc
      simp only [Bool.false_eq_true, reduceIte] at hy
      rw [hy]; exact hst
    obtain ⟨hrr, hfr⟩ := hRightHeadRep hm hx
    refine ⟨?_, ?_, ?_⟩
    · rw [hr]; exact P.canR
    · rw [hcen, hl, hr, hrad]; exact P.radLe
    · rw [hr]
      exact chainPos_step_of_supply hrr hfr P.canR (hVerifierRep hm hx) (hLagCan hm hx) P.chainPos hstep

#print axioms backgroundLanding_of_supply

/-! ## 5f. `bg` 場を放電する

`CloseoutPackRun47.bgStartP2_of_centre` は 3 入力（`canRight s.right` / 半径上界 /
`CentreLedger`）を**すべて源状態 `(c, s)` でだけ**使う。局所版を置き、
`CentreLedger` は §5e の `LPackM3` から、他 2 つは §5 の無料補題から供給する。

`i = 0`（boot、mode = init）では 3 場とも `c.mode = Mode.scan` で守られているので**空虚**。
よって `1 ≤ i` を埋めれば trace 全域が埋まる。 -/

/-- **`BgStartP2` の状態局所版**（`bgStartP2_of_centre` の本体をそのまま局所化）。 -/
theorem bgStart_at_of_centreLedger {w : List (Fin 2)} {c : Control} {s : GalilVM}
    (hCanRight : GalilScaffoldChainVerifier.canRight s.right)
    (hRadBound : ∀ rad : ℕ, ScanInvariant w (position s.center) rad s.left s.right →
      value s.radius ≤ (rad : ℤ))
    (hCentreLedger : CentreLedger s) :
    ∀ t : GalilVM, c.mode = Mode.scan →
      ChainPositionInvariantWithShiftPhase w c s → s.chain = ChainVM.idle →
      (galilFrameS (PofC centre place entry w) q first).background s t →
      ScanNR ⟨c, t⟩ → t.chain ≠ ChainVM.idle →
      ScanPositionPayloadWithChainLedger w t := by
  intro t hMode hChainPosInv hIdle hBg hScanNR hNotIdle
  obtain ⟨hl, hr, -, hcenf, -, hradf, -⟩ :=
    backgroundS_fields (PofC centre place entry w) q first hBg
  obtain ⟨hc1, hc2, hc3⟩ := hCentreLedger
  refine ⟨?_, ?_, ?_⟩
  · rw [hr]; exact hCanRight
  · rw [hcenf, hl, hr, hradf]; exact hRadBound
  · rcases backgroundS_idle (PofC centre place entry w) q first hBg hIdle with ⟨-, hz⟩ | ⟨-, hz⟩
    · exact absurd hz hNotIdle
    · rw [hz, hr]
      refine ⟨(fun _ hwch => by cases hwch), (fun _ _ _ _ _ hbk => by cases hbk),
        fun _ _ _ _ _ _ _ hcp => ?_⟩
      unfold chainStart at hcp
      injection hcp with _ _ _ _ h5 _ h7
      subst h5; subst h7
      exact ⟨hc1, hc2, hc3⟩

/-- **`bg` 場は trace 全域で放電できる。**  新規入力は `hSP`（axiom）、`VerRun`（axiom）、
残り 3 場 `hRes` だけ。 -/
theorem backgroundLanding_alongTrace {w : List (Fin 2)} (hw : 0 < w.length)
    {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hPreTraceIMW : PalPeg.CloseoutCheckW.PreTraceIMW centre place entry q first w st Tc)
    (hTcPos : 1 ≤ Tc w.length)
    (hSP : ∀ x : State GalilVM, BigPack2MG7W centre place entry q first w x →
      ScanNR x → ShiftPal centre place entry q first w x.vm)
    (hVerRun : VerRun centre place entry q first w (st 0))
    (hRes : ∀ j, j ≤ Tc w.length →
      ChainBackLagAndShiftExitLedgerAt centre place entry q first w (st j).ctl (st j).vm) :
    ∀ i, i ≤ Tc w.length → ∀ t : GalilVM,
      (st i).ctl.mode = Mode.scan →
      ChainPositionInvariantWithShiftPhase w (st i).ctl (st i).vm →
      (galilFrameS (PofC centre place entry w) q first).background (st i).vm t →
      ScanNR ⟨(st i).ctl, t⟩ → t.chain ≠ ChainVM.idle →
      ScanPositionPayloadWithChainLedger w t := by
  have hPreTrace := hPreTraceIMW.base.pre
  have hLPackM2 : ∀ j, j ≤ Tc w.length → LPackM2 w (st j).ctl (st j).vm :=
    fun j hj => (hPreTraceIMW.packs j hj).m2
  have hRadLedger := radLedger_pt centre place entry q first hw hPreTrace
    (fun j hj => leftLive_of_lpackM (hPreTraceIMW.packs j hj).pack)
  have hPack3 := lpackM3_alongTrace_afterFirstStep centre place entry q first hw
    hPreTraceIMW hTcPos hSP hRes
  intro i hIndexLeTc t hMode hChainPosInv hBg hScanNR hNotIdle
  -- `i = 0` は boot（mode = init）なので scan guard で空虚
  have hIndexPos : 1 ≤ i := by
    rcases Nat.eq_zero_or_pos i with rfl | h; swap; · exact h
    exfalso; rw [hPreTrace.start] at hMode; exact Mode.noConfusion hMode
  by_cases hIdle : (st i).vm.chain = ChainVM.idle
  · exact bgStart_at_of_centreLedger centre place entry q first
      (scanRightHeadCanRight_alongTrace centre place entry q first hw hPreTrace hLPackM2
        hTcPos i hIndexLeTc hMode)
      (radiusLe_of_radLedger (w := w) (hRadLedger i hIndexLeTc))
      (centreLedger_of_lpackM3 (hPack3 i hIndexPos hIndexLeTc) hMode)
      t hMode hChainPosInv hIdle hBg hScanNR hNotIdle
  · exact backgroundLanding_of_supply centre place entry q first
      (fun hm hx => by
        cases hr : (st i).ctl.replaying with
        | false =>
          obtain ⟨rad, hsi⟩ := (hLPackM2 i hIndexLeTc).packM.scanGeom hm hr
          exact ⟨hsi.rightRep, hsi.rightPresent⟩
        | true =>
          obtain ⟨rad, hsi⟩ := (hLPackM2 i hIndexLeTc).scanGeomR hm hr
          exact ⟨hsi.rightRep, hsi.rightPresent⟩)
      (fun hm _ => (hVerRun i (st i)
        (PalPeg.CloseoutPackRun2.steps_of_trace hPreTrace.trace i hIndexLeTc) hm).1)
      (fun hm _ => (hVerRun i (st i)
        (PalPeg.CloseoutPackRun2.steps_of_trace hPreTrace.trace i hIndexLeTc) hm).2)
      (fun t' hm hx hidle hb hs hni => absurd hidle hIdle)
      t hMode hChainPosInv hBg hScanNR hNotIdle

#print axioms bgStart_at_of_centreLedger
#print axioms backgroundLanding_alongTrace

/-! ## 5g. 原子的な残差から `ScanLandingObligationsAlongTrace` を組み立てる

`bg` 場は §5f で放電できたので、残る義務は**原子的な 5 つ**（それぞれ 1 場の構造体に
分けた。束ねると「公理を 1 個外す」が測れなくなるため）:

| 原子 | 内容 |
|---|---|
| `MatchLandingAt` | `scan_match` 着地の位置台帳 |
| `ShiftEntryLandingAt` | `scan_shift` 入口の shift 相台帳 |
| `ChainBackLagAt` | chain の `.back` 相の lag 形状 |
| `ShiftExitLedgerAt` | `shift_done` での `CentreLedger` |
| `RewindMarginAt` | rewind 相での `2 ≤ position left` |

これに `hSP`（`ShiftPal`）と `hVerRun`（`VerRun`）を加えた 7 つが全入力。
`w = []` のときは `Tc 0 = 0` で `i = 0`（boot、mode = init）しか無く 3 場とも
scan guard で空虚なので自由。 -/

/-- **(ATOM)** `scan_match` 着地の位置台帳。 -/
structure MatchLandingAt (w : List (Fin 2)) (c : Control) (s : GalilVM) : Prop where
  matchLand : ∀ (s' t : GalilVM) (o b : Bool), c.mode = Mode.scan →
    ChainPositionInvariantWithShiftPhase w c s →
    (galilFrameS (PofC centre place entry w) q first).compare s s' →
    (galilFrameS (PofC centre place entry w) q first).matched s' →
    (galilFrameS (PofC centre place entry w) q first).matchedPlace c.replaying s' t →
    ScanNR ⟨{c with clock := 2048, output := o, replaying := c.replaying && b}, t⟩ →
    t.chain ≠ ChainVM.idle → ScanPositionPayloadWithChainLedger w t

/-- **(ATOM)** `scan_shift` 入口の shift 相台帳。 -/
structure ShiftEntryLandingAt (w : List (Fin 2)) (c : Control) (s : GalilVM) : Prop where
  entryLand : ∀ s' t : GalilVM, c.mode = Mode.scan →
    ChainPositionInvariantWithShiftPhase w c s →
    (galilFrameS (PofC centre place entry w) q first).compare s s' →
    ¬ (galilFrameS (PofC centre place entry w) q first).matched s' →
    shiftGuardVM s' → beginShiftVM' s' t → ShiftPhaseChainLedger t

/-- **(ATOM)** chain の `.back` 相の lag 形状。 -/
structure ChainBackLagAt (s : GalilVM) : Prop where
  backLag : ∀ (v : Tape) (h lag margin : Counter) (ver : PlaceHead),
    s.chain = .back v h lag margin ver → Canonical lag ∧ 0 ≤ value lag

/-- **(ATOM)** `shift_done` での `CentreLedger`。 -/
structure ShiftExitLedgerAt (w : List (Fin 2)) (c : Control) (s : GalilVM) : Prop where
  shiftExitLedger : c.mode = Mode.shift →
    ¬ (galilFrameS (PofC centre place entry w) q first).remainingPos s → CentreLedger s

/-- **(ATOM)** rewind 相での左ヘッドの余裕。 -/
structure RewindMarginAt (c : Control) (s : GalilVM) : Prop where
  rewindMargin : c.mode = Mode.rewind → 2 ≤ position s.left

/-- **原子的な残差から trace 形の scan landing 義務を組み立てる。** -/
theorem scanLandingObligations_alongTrace_of_atoms {w : List (Fin 2)}
    {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hPreTraceIMW : PalPeg.CloseoutCheckW.PreTraceIMW centre place entry q first w st Tc)
    (hSP : ∀ x : State GalilVM, BigPack2MG7W centre place entry q first w x →
      ScanNR x → ShiftPal centre place entry q first w x.vm)
    (hVerRun : VerRun centre place entry q first w (st 0))
    (hChainBackLag : ∀ j, j ≤ Tc w.length → ChainBackLagAt (st j).vm)
    (hShiftExitLedger : ∀ j, j ≤ Tc w.length →
      ShiftExitLedgerAt centre place entry q first w (st j).ctl (st j).vm)
    (hRewindMargin : ∀ j, j ≤ Tc w.length → RewindMarginAt (st j).ctl (st j).vm)
    (hMatchLanding : ∀ j, j ≤ Tc w.length →
      MatchLandingAt centre place entry q first w (st j).ctl (st j).vm)
    (hShiftEntryLanding : ∀ j, j ≤ Tc w.length →
      ShiftEntryLandingAt centre place entry q first w (st j).ctl (st j).vm) :
    ScanLandingObligationsAlongTrace centre place entry q first w st Tc := by
  intro i hIndexLeTc
  refine { bg := ?_, matchLand := (hMatchLanding i hIndexLeTc).matchLand,
           entryLand := (hShiftEntryLanding i hIndexLeTc).entryLand }
  rcases Nat.eq_zero_or_pos w.length with hlen | hw
  · intro t hMode _ _ _ _
    exfalso
    rw [hlen, hPreTraceIMW.base.pre.tc0] at hIndexLeTc
    have hzero : i = 0 := by omega
    subst hzero
    rw [hPreTraceIMW.base.pre.start] at hMode
    exact Mode.noConfusion hMode
  · have hTcPos : 1 ≤ Tc w.length :=
      hPreTraceIMW.base.tc1 ▸ hPreTraceIMW.base.pre.mono 1 w.length hw le_rfl
    exact backgroundLanding_alongTrace centre place entry q first hw hPreTraceIMW hTcPos hSP
      hVerRun
      (fun j hj => ⟨(hChainBackLag j hj).backLag,
        (hShiftExitLedger j hj).shiftExitLedger, (hRewindMargin j hj).rewindMargin⟩)
      i hIndexLeTc

#print axioms scanLandingObligations_alongTrace_of_atoms

/-! ## 5h. `ChainBackLagAt` は放電済み — 新規入力ゼロ

`ChainLagCanonical` は §5d の分類器補題（`chainLagCanonical_chainAt` ほか）で
trace 全域を運べる（`chainLagCanonical_alongTrace`、側入力は `RadLedger` だけで
それは `radLedger_pt` でタダ）。その `.back` 節が `ChainBackLagAt` そのもの。

`w = []` のときは `Tc 0 = 0` で `j = 0`（boot、chain は idle）しか無いので自由。 -/

/-- **`ChainBackLagAt` は trace 全域でタダ。** -/
theorem chainBackLagAt_alongTrace {w : List (Fin 2)}
    {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hPreTraceIMW : PalPeg.CloseoutCheckW.PreTraceIMW centre place entry q first w st Tc) :
    ∀ j, j ≤ Tc w.length → ChainBackLagAt (st j).vm := by
  intro j hIndexLeTc
  rcases Nat.eq_zero_or_pos w.length with hlen | hw
  · rw [hlen, hPreTraceIMW.base.pre.tc0] at hIndexLeTc
    have hzero : j = 0 := by omega
    subst hzero
    rw [hPreTraceIMW.base.pre.start]
    exact ⟨(chainLagCanonical_idle).backLagField⟩
  · exact ⟨(chainLagCanonical_alongTrace centre place entry q first hw hPreTraceIMW j
      hIndexLeTc).backLagField⟩

#print axioms chainBackLagAt_alongTrace

/-! ## 5i. `RewindMarginAt` は `CentreMargin` 1 葉に縮む — `RCouple` はタダ

`CloseoutPackRun13` に材料が揃っていた:

* `rcouple_of_run`（:213）— **葉なし**。rewind 以外の mode で始まる run の各点で
  `RCouple` が成り立つ。boot は `mode = init ≠ rewind` なので trace 全域でタダ
* `rewindMargin_of_centreMargin`（:234）— `RCouple` ＋ `CentreMargin` から
  `2 ≤ position s.left`

`CentreMargin c s := c.mode = Mode.rewind → ∀ r, s.radius = ofNat r →
r + pairOff c + 2 ≤ position s.center`（`Run13:227`）。

`position p = if p.gap then 2·|left| else 2·|left| − 1`（`ChainInputSupply:496`）なので
これは**リストの長さの算術**であって幾何ではない。 -/

/-- **`RCouple` は trace 全域でタダ**（`rcouple_of_run` は葉を取らない）。 -/
theorem rcouple_alongTrace {w : List (Fin 2)} {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hPreTrace : PreTrace centre place entry q first w st Tc) :
    ∀ i, i ≤ Tc w.length →
      PalPeg.CloseoutPackRun13.RCouple (st i).ctl (st i).vm :=
  fun i hIndexLeTc =>
    PalPeg.CloseoutPackRun13.rcouple_of_run (PofC centre place entry w) q first 2048
      (PalPeg.CloseoutPackRun2.steps_of_trace hPreTrace.trace i hIndexLeTc)
      (by decide : Mode.init ≠ Mode.rewind)
      (by rw [hPreTrace.start]; rfl)

/-- **`RewindMarginAt` は `CentreMargin` だけから出る。** -/
theorem rewindMarginAt_alongTrace {w : List (Fin 2)} {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hPreTrace : PreTrace centre place entry q first w st Tc)
    (hCentreMargin : ∀ i, i ≤ Tc w.length →
      PalPeg.CloseoutPackRun13.CentreMargin (st i).ctl (st i).vm) :
    ∀ i, i ≤ Tc w.length → RewindMarginAt (st i).ctl (st i).vm :=
  fun i hIndexLeTc =>
    ⟨fun hMode => PalPeg.CloseoutPackRun13.rewindMargin_of_centreMargin
      (rcouple_alongTrace centre place entry q first hPreTrace i hIndexLeTc)
      (hCentreMargin i hIndexLeTc) hMode⟩

#print axioms rcouple_alongTrace
#print axioms rewindMarginAt_alongTrace


#print axioms landingObligationsAlongRun_of_globalHypotheses
#print axioms chainPosInv2_alongRun
#print axioms shiftLocalS_of_landingObligationsAlongRun
#print axioms needBound_of_landingObligationsAlongRun

end

end PalPeg.BranchSupply
