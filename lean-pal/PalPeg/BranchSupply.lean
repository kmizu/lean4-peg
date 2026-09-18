import PalPeg.CloseoutVerSide
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
  have init_tick_target_is_scan : ∀ x y : State GalilVM,
      Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y →
      x.ctl.mode = Mode.init →
      (galilFrameS (PofC centre place entry w) q first).init x.vm y.vm ∧
        y.ctl.mode = Mode.scan := by
    intro x y h hm
    cases h with
    | init c s s' hm' hinit => exact ⟨hinit, rfl⟩
    | _ => simp_all
  obtain ⟨hinit1, hmode1⟩ := init_tick_target_is_scan (st 0) (st 1) (hPreTrace.trace.tick 0 (by omega)) hMode
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

#print axioms radiusExact_after_background
#print axioms radiusExact_of_centreAtRightAndRadiusZero
#print axioms radiusExact_at_boot
#print axioms radiusExact_after_beginShift
#print axioms radiusExact_after_beginFallback
#print axioms radiusExact_after_restart
#print axioms radiusExact_after_replayStart
#print axioms radiusExact_after_initVM

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

#print axioms landingObligationsAlongRun_of_globalHypotheses
#print axioms chainPosInv2_alongRun
#print axioms shiftLocalS_of_landingObligationsAlongRun
#print axioms needBound_of_landingObligationsAlongRun

end

end PalPeg.BranchSupply
