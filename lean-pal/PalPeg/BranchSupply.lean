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

#print axioms branchRun_of_global
#print axioms chainPosInv2_steps_run
#print axioms shiftLocalS_of_branchRun
#print axioms needIMW'_le_B

end

end PalPeg.BranchSupply
