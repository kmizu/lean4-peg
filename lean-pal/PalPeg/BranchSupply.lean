import PalPeg.CloseoutVerSide
import PalPeg.ShiftLocalRun

/-!
# `BranchRun` — `ChainPosInv2` の 4 分岐義務を run 形にする

## なぜ run 形でなければならないか

`H_bgP2` / `H_matchP2` / `H_shiftEntry2` / `H_shiftDoneRad2` は
`∀ (c : Control) (s : GalilVM), …` で**任意の状態**を量化している。ところが
それらを放電する材料は run に沿ってしか存在しない：

* `LPackM2.shiftGeom`（`CloseoutPackRun23:103`）— `H_shiftDoneRad2` の `canRight`/
  半径上界はここから出る（`CloseoutShiftDoneP.canR_of_shiftGeom` /
  `radEq_of_shiftGeom_done`）。`LPackM2` は run の各点に `IPackMW.m2` としてある。
* chain 側台帳 `ChainPos`（Run41、Run38 の `SrcPos` を吸収）— `chainPos_step` /
  `chainPos_matched` で run を運ばれる。
* 入力供給（verifier が入力を表現する）— `CloseoutVerSide.VerRun` が run 形で束ねている。

任意の状態にこれらは無い。だから `∀ c s` の形のままでは放電できない。
同じ誤りの反証が `ConsumeAvailRefute.hav_false`（`∀ st` と書いて run の制約が
ゼロになった例）。

## このファイル

`CloseoutPackRun41.BranchAt`（状態局所の束、`chainPosInv2_tick_at` が消費する）を
run に沿って量化した `BranchRun` を定義し、`ChainPosInv2` を run に沿って運ぶ。
`branchRun_of_global` があるので、global 4 本を持っている呼び出し側はそのまま乗る
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

/-- **(NAMED, run 形) 4 分岐義務**: run が到達する各状態で `BranchAt`。 -/
def BranchRun (w : List (Fin 2)) (x : State GalilVM) : Prop :=
  ∀ (m : ℕ) (z : State GalilVM),
    Steps (galilFrameS (PofC centre place entry w) q first) 2048 m x z →
    BranchAt centre place entry q first w z.ctl z.vm

/-- global 4 本は run 形を含意する（**逆は無い** — run 形のほうが真に弱い）。 -/
theorem branchRun_of_global {w : List (Fin 2)}
    (hbg : H_bgP2 centre place entry q first w) (hmatch : H_matchP2 centre place entry q first w)
    (hentry : H_shiftEntry2 centre place entry q first w)
    (hsd : H_shiftDoneRad2 centre place entry q first w) (x : State GalilVM) :
    BranchRun centre place entry q first w x :=
  fun _ z _ => branchAt_of_global centre place entry q first hbg hmatch hentry hsd z.ctl z.vm

/-- **`ChainPosInv2` を run に沿って運ぶ（run 形の義務で）。**  再指標化は
`Steps.succ ht`（`CloseoutBundleRun.roundBundle_steps_run` と同じ形）。 -/
theorem chainPosInv2_steps_run {w : List (Fin 2)} :
    ∀ {n : ℕ} {x y : State GalilVM},
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 n x y →
      ChainPosInv2 w x.ctl x.vm →
      BranchRun centre place entry q first w x →
      ChainPosInv2 w y.ctl y.vm := by
  intro n x y h
  induction h with
  | zero x => intro hx _; exact hx
  | @succ n x z y ht _ ih =>
    intro hx hB
    refine ih (chainPosInv2_tick_at centre place entry q first (hB 0 x (.zero x)) hx ht) ?_
    intro m z' hz'
    exact hB (m + 1) z' (.succ ht hz')

/-! ## 2. `ShiftLocalS` と `needL'` を run 形の義務から -/

/-- **`ShiftLocalS` along the run**: `CloseoutVerSide.shiftLocalS_of_verRun` の
4 つの global 義務を `BranchRun` に置き換えたもの。 -/
theorem shiftLocalS_of_branchRun {w : List (Fin 2)}
    {n : ℕ} {x y : State GalilVM} (hx : ChainPosInv2 w x.ctl x.vm)
    (h : Steps (galilFrameS (PofC centre place entry w) q first) 2048 n x y)
    (hB : BranchRun centre place entry q first w x)
    (hV : VerRun centre place entry q first w x)
    (hLP : PalPeg.CloseoutPackRun23.LPackM2 w y.ctl y.vm) :
    ShiftLocalS centre place entry q first w y := by
  refine shiftLocalS_of_parts centre place entry q first
    (chainPosInv2_steps_run centre place entry q first h hx hB)
    (fun hm => ?_) (fun hm => (hV n y h hm).1) (fun hm => (hV n y h hm).2)
  cases hr : y.ctl.replaying with
  | false =>
    obtain ⟨rad, hi⟩ := hLP.packM.scanGeom hm hr
    exact ⟨hi.rightRep, hi.rightPresent⟩
  | true =>
    obtain ⟨rad, hi⟩ := hLP.scanGeomR hm hr
    exact ⟨hi.rightRep, hi.rightPresent⟩

/-- **`needL'` の上界を run 形の義務から。**  `CloseoutVerSide.needIMW'_le_W4` の
global 4 本を `BranchRun` に置き換え、3 段の本体は
`ShiftLocalRun.needIMW'_le_of_shiftLocal`（S / S3 / S4 共通部分）に載せた。 -/
theorem needIMW'_le_B {w : List (Fin 2)} (hw : 0 < w.length)
    {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hP : PalPeg.CloseoutCheckW.PreTraceIMW centre place entry q first w st Tc)
    (hpos0 : ChainPosInv2 w (st 0).ctl (st 0).vm)
    (hB : BranchRun centre place entry q first w (st 0))
    (hV : VerRun centre place entry q first w (st 0)) :
    ∀ m, m < w.length → ∀ i, i ≤ Tc (m+1) →
      PalPeg.GalilLookRefined.needL' w st i ≤ m + 1 :=
  needIMW'_le_of_shiftLocal centre place entry q first hw hP
    (fun i hi => shiftLocalS_of_branchRun centre place entry q first hpos0
      (PalPeg.CloseoutPackRun2.steps_of_trace hP.base.pre.trace i hi) hB hV (hP.packs i hi).m2)

/-! ## 3. `shiftDone` 場の半径台帳はタダ

`BranchAt.shiftDone` は `canRight s.right` と半径台帳の連言。後者は
**`CloseoutRadPack.RadLedger.le`（`position center + value radius ≤ position right`）と
`ScanInvariant.rightPos`（`position right = position center + rad`）だけで出る**。
`RadLedger` は `CloseoutLPack6.radLedger_pt` が `PreTrace` ＋ `LeftLive` だけから
run の全点に与える（新規入力ゼロ）。 -/

/-- **半径台帳は `RadLedger` から出る。** -/
theorem radLe_of_radLedger {w : List (Fin 2)} {c : Control} {s : GalilVM}
    (hR : PalPeg.CloseoutRadPack.RadLedger c s) :
    ∀ rad : ℕ, ScanInvariant w (position s.center) rad s.left s.right →
      value s.radius ≤ (rad : ℤ) := by
  intro rad hsi
  have h1 : (position s.center : ℤ) + value s.radius ≤ (position s.right : ℤ) := hR.le
  have h2 : position s.right = position s.center + rad := hsi.rightPos
  rw [h2] at h1
  push_cast at h1
  omega

/-- **`shiftDone` 場は `canRight` 1 つに落ちる。** -/
theorem shiftDone_of_radLedger {w : List (Fin 2)} {c : Control} {s : GalilVM}
    (hR : PalPeg.CloseoutRadPack.RadLedger c s)
    (hcan : c.mode = Mode.shift →
      ¬ (galilFrameS (PofC centre place entry w) q first).remainingPos s →
      GalilScaffoldChainVerifier.canRight s.right) :
    c.mode = Mode.shift →
      ¬ (galilFrameS (PofC centre place entry w) q first).remainingPos s →
      ChainPosInv2 w c s → s.chain ≠ ChainVM.idle →
      GalilScaffoldChainVerifier.canRight s.right ∧
        ∀ rad : ℕ, ScanInvariant w (position s.center) rad s.left s.right →
          value s.radius ≤ (rad : ℤ) :=
  fun hm hp _ _ => ⟨hcan hm hp, radLe_of_radLedger (w := w) hR⟩

#print axioms radLe_of_radLedger
#print axioms shiftDone_of_radLedger

/-! ## 4. trace 指標版 — 供給の形に合わせる

`BranchRun` は `Steps` で到達する**すべての**状態を量化するが、`Tick` は関係なので
trace の外の状態も含む。一方、放電の材料（`RadLedger`、`LPackM2`）は
`radLedger_pt` / `PreTraceIMW.packs` が **trace の点 `st i`** で与える。
そこで trace 指標の版を置く。`chainPosInv2_steps_run` を使う経路は `steps_of_trace` で
trace の鎖しか渡さないので、これで十分。 -/

/-- **(NAMED, trace 形) 4 分岐義務の残り**: `shiftDone` の半径台帳は `RadLedger` から
出るので（§3）、残るのは `canRight` だけ。 -/
structure BranchRes (w : List (Fin 2)) (c : Control) (s : GalilVM) : Prop where
  bg : ∀ t : GalilVM, c.mode = Mode.scan → ChainPosInv2 w c s →
    (galilFrameS (PofC centre place entry w) q first).background s t →
    ScanNR ⟨c, t⟩ → t.chain ≠ ChainVM.idle → PosPayload2 w t
  matchLand : ∀ (s' t : GalilVM) (o b : Bool), c.mode = Mode.scan → ChainPosInv2 w c s →
    (galilFrameS (PofC centre place entry w) q first).compare s s' →
    (galilFrameS (PofC centre place entry w) q first).matched s' →
    (galilFrameS (PofC centre place entry w) q first).matchedPlace c.replaying s' t →
    ScanNR ⟨{c with clock := 2048, output := o, replaying := c.replaying && b}, t⟩ →
    t.chain ≠ ChainVM.idle → PosPayload2 w t
  entryLand : ∀ s' t : GalilVM, c.mode = Mode.scan → ChainPosInv2 w c s →
    (galilFrameS (PofC centre place entry w) q first).compare s s' →
    ¬ (galilFrameS (PofC centre place entry w) q first).matched s' →
    shiftGuardVM s' → beginShiftVM' s' t → ShiftPos2 t
  shiftCan : c.mode = Mode.shift →
    ¬ (galilFrameS (PofC centre place entry w) q first).remainingPos s →
    GalilScaffoldChainVerifier.canRight s.right

/-- **`BranchAt` from `BranchRes` plus the free radius ledger.** -/
theorem branchAt_of_res {w : List (Fin 2)} {c : Control} {s : GalilVM}
    (hR : PalPeg.CloseoutRadPack.RadLedger c s)
    (hres : BranchRes centre place entry q first w c s) :
    BranchAt centre place entry q first w c s :=
  ⟨hres.bg, hres.matchLand, hres.entryLand,
    shiftDone_of_radLedger centre place entry q first hR hres.shiftCan⟩

/-- **`ChainPosInv2` along the trace** (induction on the index, the shape
`CloseoutPackRun49.lpackM3_steps` uses). -/
theorem chainPosInv2_trace {w : List (Fin 2)} {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hP : PreTrace centre place entry q first w st Tc)
    (hB : ∀ i, i ≤ Tc w.length → BranchAt centre place entry q first w (st i).ctl (st i).vm)
    (hx : ChainPosInv2 w (st 0).ctl (st 0).vm) :
    ∀ i, i ≤ Tc w.length → ChainPosInv2 w (st i).ctl (st i).vm := by
  intro i
  induction i with
  | zero => intro _; exact hx
  | succ n ih =>
    intro hi
    exact chainPosInv2_tick_at centre place entry q first (hB n (by omega)) (ih (by omega))
      (hP.trace.tick n (by omega))

/-- **(NAMED, trace 形) 残りの 3 場 ＋ `canRight`**, at every point of the trace. -/
def BranchResTrace (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ) : Prop :=
  ∀ i, i ≤ Tc w.length → BranchRes centre place entry q first w (st i).ctl (st i).vm

/-- **`needL'` の上界を trace 形の残差から。**  半径台帳（`RadLedger`）は
`CloseoutLPack6.radLedger_pt` が `PreTrace` ＋ `LeftLive` だけで与えるので
**新規入力ゼロ**で内部調達する。 -/
theorem needIMW'_le_R {w : List (Fin 2)} (hw : 0 < w.length)
    {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hP : PalPeg.CloseoutCheckW.PreTraceIMW centre place entry q first w st Tc)
    (hpos0 : ChainPosInv2 w (st 0).ctl (st 0).vm)
    (hres : BranchResTrace centre place entry q first w st Tc)
    (hV : VerRun centre place entry q first w (st 0)) :
    ∀ m, m < w.length → ∀ i, i ≤ Tc (m+1) →
      PalPeg.GalilLookRefined.needL' w st i ≤ m + 1 := by
  have hLP : ∀ i, i ≤ Tc w.length →
      PalPeg.CloseoutPackRun10.LPackM w (st i).ctl (st i).vm :=
    fun i hi => (hP.packs i hi).pack
  have hll : ∀ i, i ≤ Tc w.length →
      PalPeg.GalilTrailSane.LeftLive (st i).ctl (st i).vm :=
    fun i hi => leftLive_of_lpackM (hLP i hi)
  have hR := radLedger_pt centre place entry q first hw hP.base.pre hll
  have hB : ∀ i, i ≤ Tc w.length →
      BranchAt centre place entry q first w (st i).ctl (st i).vm :=
    fun i hi => branchAt_of_res centre place entry q first (hR i hi) (hres i hi)
  have hinv := chainPosInv2_trace centre place entry q first hP.base.pre hB hpos0
  refine needIMW'_le_of_shiftLocal centre place entry q first hw hP (fun i hi => ?_)
  refine shiftLocalS_of_parts centre place entry q first (hinv i hi) (fun hm => ?_)
    (fun hm => (hV i (st i)
      (PalPeg.CloseoutPackRun2.steps_of_trace hP.base.pre.trace i hi) hm).1)
    (fun hm => (hV i (st i)
      (PalPeg.CloseoutPackRun2.steps_of_trace hP.base.pre.trace i hi) hm).2)
  cases hr : (st i).ctl.replaying with
  | false =>
    obtain ⟨rad, hi'⟩ := (hP.packs i hi).m2.packM.scanGeom hm hr
    exact ⟨hi'.rightRep, hi'.rightPresent⟩
  | true =>
    obtain ⟨rad, hi'⟩ := (hP.packs i hi).m2.scanGeomR hm hr
    exact ⟨hi'.rightRep, hi'.rightPresent⟩

/-! ## 5. `shiftCan` — 右ヘッドが動けることは trace の予算から出る

`BranchRes.shiftCan` は `canRight s.right`。`CloseoutCanRightBound.canRight_of_position_bound`
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
theorem position_le_front {c : Control} {s : GalilVM} (hP : FrontPack c s) :
    (position s.right : ℤ) ≤ front s := by
  unfold front
  cases hr : c.replaying with
  | true =>
    obtain ⟨m, hm⟩ := hP.replayPos hr
    rw [hm, GalilScaffoldCounter.ofNat_value]
    omega
  | false =>
    rw [hP.rest (Or.inl hr)]
    simp [GalilScaffoldCounter.value, GalilScaffoldCounter.reset]

/-- **front は trace に沿って単調。** -/
theorem front_mono_trace {w : List (Fin 2)} {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hP : PreTrace centre place entry q first w st Tc)
    (hf : ∀ j, 1 ≤ j → j ≤ Tc w.length → FrontPack (st j).ctl (st j).vm) :
    ∀ i k, 1 ≤ i → i + k ≤ Tc w.length → front (st i).vm ≤ front (st (i + k)).vm := by
  intro i k
  induction k with
  | zero => intro _ _; exact le_rfl
  | succ n ih =>
    intro h1 hk
    refine le_trans (ih h1 (by omega)) ?_
    have ht := hP.trace.tick (i + n) (by omega)
    have hm := front_tick_mono (onLetterVM w) leftFirstVM centre place entry q first 2048
      (hf (i + n) (by omega) (by omega)) ht
    have he : i + (n + 1) = i + n + 1 := by omega
    rw [he]
    exact hm

/-- **右ヘッドは trace 全域で `2|w| − 1` 以下。** -/
theorem rightPos_le_trace {w : List (Fin 2)} (hw : 0 < w.length)
    {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hP : PreTrace centre place entry q first w st Tc)
    (hf : ∀ j, 1 ≤ j → j ≤ Tc w.length → FrontPack (st j).ctl (st j).vm)
    (htc : 1 ≤ Tc w.length) :
    ∀ i, 1 ≤ i → i ≤ Tc w.length → position (st i).vm.right ≤ 2 * w.length - 1 := by
  intro i h1 hi
  have hrp := hP.report w.length hw le_rfl
  have hfe : front (st (Tc w.length)).vm = ((position (st (Tc w.length)).vm.right : ℕ) : ℤ) :=
    front_eq_position (hf _ htc le_rfl) hrp.notReplaying
  have hmono := front_mono_trace centre place entry q first hP hf i (Tc w.length - i) h1 (by omega)
  rw [show i + (Tc w.length - i) = Tc w.length by omega] at hmono
  have hple := position_le_front (hf i h1 hi)
  rw [hfe, hrp.atPrefix] at hmono
  have : ((position (st i).vm.right : ℕ) : ℤ) ≤ ((2 * w.length - 1 : ℕ) : ℤ) :=
    le_trans hple hmono
  exact_mod_cast this

/-- **`mode := .init` にする `Tick` 構成子は存在しない。**  `Tick`（`GalilScaffoldTop:109`）の
24 構成子の行き先の mode は scan / shift / copy / home / fpp / markEnd / choose / rewind /
replayStart か「変えない」のいずれかで、`init` は源の mode としてしか現れない。 -/
theorem tick_mode_ne_init {σ : Type} {F : Frame σ} {delay : ℕ} {x y : State σ}
    (h : Tick F delay x y) : y.ctl.mode ≠ Mode.init := by
  cases h <;> simp_all

/-- **trace は 1 手目以降 `init` に戻らない。** -/
theorem mode_ne_init_of_trace {w : List (Fin 2)} {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hP : PreTrace centre place entry q first w st Tc) :
    ∀ j, 1 ≤ j → j ≤ Tc w.length → (st j).ctl.mode ≠ Mode.init := by
  intro j hj1 hj
  obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
  exact tick_mode_ne_init (hP.trace.tick n (by omega))

/-- **`shiftCan` は trace 予算と `LPackM2.shiftGeom` から出る — 新規入力ゼロ。**
shift 相では `ShiftGeom` の `RRep` が右ヘッドの `Represents` と `focus ≠ none` を持ち、
`FrontPack` は `GalilTrailRad.frontPack_trace` が `mode ≠ init`（1 手目以降は定理）
のもとで trace の各点に与える。 -/
theorem shiftCan_of_trace {w : List (Fin 2)} (hw : 0 < w.length)
    {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hP : PreTrace centre place entry q first w st Tc)
    (hm2 : ∀ j, j ≤ Tc w.length →
      PalPeg.CloseoutPackRun23.LPackM2 w (st j).ctl (st j).vm) :
    ∀ i, i ≤ Tc w.length → (st i).ctl.mode = Mode.shift →
      GalilScaffoldChainVerifier.canRight (st i).vm.right := by
  have hf : ∀ j, 1 ≤ j → j ≤ Tc w.length → FrontPack (st j).ctl (st j).vm :=
    fun j hj1 hj => frontPack_trace centre place entry q first w hw st Tc hP j hj
      (mode_ne_init_of_trace centre place entry q first hP j hj1 hj)
  intro i hi hmo
  have h1 : 1 ≤ i := by
    rcases Nat.eq_zero_or_pos i with rfl | h; swap; · exact h
    exfalso
    rw [hP.start] at hmo
    exact Mode.noConfusion hmo
  obtain ⟨rem, r, -, -, ⟨hrep, hpres⟩, -, -, -, -, -, -⟩ := (hm2 i hi).shiftGeom hmo
  exact canRight_of_position_bound hrep hpres (m := w.length) hw le_rfl
    (rightPos_le_trace centre place entry q first hw hP hf (by omega) i h1 hi)

#print axioms position_le_front
#print axioms front_mono_trace
#print axioms rightPos_le_trace
#print axioms tick_mode_ne_init
#print axioms mode_ne_init_of_trace
#print axioms shiftCan_of_trace

#print axioms branchAt_of_res
#print axioms chainPosInv2_trace
#print axioms needIMW'_le_R

/-! ## 6. 残差は 3 場 — `shiftDone` は完全に放電された

§3 で半径台帳（`RadLedger`）、§5 で `canRight`（trace 予算 ＋ `LPackM2.shiftGeom`）が
出たので、`BranchAt.shiftDone` は**新規入力ゼロで**得られる。残るのは
`bg` / `matchLand` / `entryLand` の 3 場。 -/

/-- **(NAMED, trace 形) 残り 3 場。** -/
structure BranchRes3 (w : List (Fin 2)) (c : Control) (s : GalilVM) : Prop where
  bg : ∀ t : GalilVM, c.mode = Mode.scan → ChainPosInv2 w c s →
    (galilFrameS (PofC centre place entry w) q first).background s t →
    ScanNR ⟨c, t⟩ → t.chain ≠ ChainVM.idle → PosPayload2 w t
  matchLand : ∀ (s' t : GalilVM) (o b : Bool), c.mode = Mode.scan → ChainPosInv2 w c s →
    (galilFrameS (PofC centre place entry w) q first).compare s s' →
    (galilFrameS (PofC centre place entry w) q first).matched s' →
    (galilFrameS (PofC centre place entry w) q first).matchedPlace c.replaying s' t →
    ScanNR ⟨{c with clock := 2048, output := o, replaying := c.replaying && b}, t⟩ →
    t.chain ≠ ChainVM.idle → PosPayload2 w t
  entryLand : ∀ s' t : GalilVM, c.mode = Mode.scan → ChainPosInv2 w c s →
    (galilFrameS (PofC centre place entry w) q first).compare s s' →
    ¬ (galilFrameS (PofC centre place entry w) q first).matched s' →
    shiftGuardVM s' → beginShiftVM' s' t → ShiftPos2 t

/-- **(NAMED, trace 形) 残り 3 場を trace の各点で。** -/
def BranchRes3Trace (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ) : Prop :=
  ∀ i, i ≤ Tc w.length → BranchRes3 centre place entry q first w (st i).ctl (st i).vm

/-- **`needL'` の上界を残り 3 場だけから。**  `shiftDone` 場は内部で放電する
（半径台帳は `radLedger_pt`、`canRight` は `shiftCan_of_trace`、どちらも新規入力ゼロ）。 -/
theorem needIMW'_le_R3 {w : List (Fin 2)} (hw : 0 < w.length)
    {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hP : PalPeg.CloseoutCheckW.PreTraceIMW centre place entry q first w st Tc)
    (hpos0 : ChainPosInv2 w (st 0).ctl (st 0).vm)
    (hres : BranchRes3Trace centre place entry q first w st Tc)
    (hV : VerRun centre place entry q first w (st 0)) :
    ∀ m, m < w.length → ∀ i, i ≤ Tc (m+1) →
      PalPeg.GalilLookRefined.needL' w st i ≤ m + 1 := by
  have hll : ∀ i, i ≤ Tc w.length →
      PalPeg.GalilTrailSane.LeftLive (st i).ctl (st i).vm :=
    fun i hi => leftLive_of_lpackM (hP.packs i hi).pack
  have hR := radLedger_pt centre place entry q first hw hP.base.pre hll
  have hcan := shiftCan_of_trace centre place entry q first hw hP.base.pre
    (fun j hj => (hP.packs j hj).m2)
  refine needIMW'_le_R centre place entry q first hw hP hpos0 (fun i hi => ?_) hV
  exact ⟨(hres i hi).bg, (hres i hi).matchLand, (hres i hi).entryLand,
    fun hmo _ => hcan i hi hmo⟩

#print axioms branchAt_of_res
#print axioms needIMW'_le_R3

#print axioms branchRun_of_global
#print axioms chainPosInv2_steps_run
#print axioms shiftLocalS_of_branchRun
#print axioms needIMW'_le_B

end

end PalPeg.BranchSupply
