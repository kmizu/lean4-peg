import PalPeg.CloseoutWatchSupply
import PalPeg.CloseoutChainSideR

/-!
# `hpack`'s use in the top theorem is two chain-side facts, not a bundle

`CloseoutFinalW3.pal_in_peg_final5MW3` takes `hpk` (the refuted
`∀ w c s, ChainPosInv2 w c s → ChainPack q first w c s`) and uses it in exactly
one place: `CloseoutWatchSupply.needIMW'_le_W3` → `radPack_ptS3` →
`shiftLocalS_of_run3` → `shiftLocalS_of_chainPack`.  And that last lemma reads
**four** fields of the bundle:

```
hp.inv          -- ChainPosInv2, already a hypothesis of the caller
hp.repR  hs.1   -- the right head represents `w`
hp.repV  hs.1   -- the chain's verifier represents `w`
hp.lagCan hs.1  -- the chain's lag counters are canonical
```

Of those, `repR` is **already available along the run**: `needIMW'_le_W3`
computes `hLP : ∀ i ≤ Tc w.length, LPackM w (st i).ctl (st i).vm` from the
pre-trace, and `CloseoutChainPack.chainPack_of_lpackM2` shows `LPackM2`'s
`scanGeom` / `scanGeomR` give exactly `repR`.

So the whole of `hpk`'s contribution is `repV` and `lagCan` at the run's `scan`
states.  `shiftLocalS_of_parts` below is `shiftLocalS_of_chainPack` with the
four reads taken as arguments, and `VerRun` names the two residual facts **in
run form** — the shape that `chainPosInv2_of_idle` cannot refute, and the same
shape `CloseoutMarksFree.MarksRun` already uses for the marks side.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutVerSide

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

section
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **`ShiftLocalS` from the four facts `shiftLocalS_of_chainPack` reads.**
Verbatim that proof, with the bundle replaced by its four projections. -/
theorem shiftLocalS_of_parts {w : List (Fin 2)} {x : State GalilVM}
    (hinv : ChainPosInv2 w x.ctl x.vm)
    (hrep : x.ctl.mode = Mode.scan →
      GalilScaffoldInputTrace.Represents x.vm.right.head w ∧ x.vm.right.head.focus ≠ none)
    (hver : x.ctl.mode = Mode.scan → VerRep w x.vm.chain)
    (hlag : x.ctl.mode = Mode.scan → LagCan x.vm.chain) :
    ShiftLocalS centre place entry q first w x := by
  by_cases hi : x.vm.chain = ChainVM.idle
  · exact shiftLocalS_of_chainIdle centre place entry q first hi
  · refine
      { move := fun hs => ?_, guard := fun hs => ?_, coupled := fun hs => ?_,
        ver := fun hs => ?_ } <;>
    · obtain ⟨hrr, hfr⟩ := hrep hs.1
      exact (shiftLocalS_of_watchShiftS centre place entry q first hi
        (watchShiftS_of_supply centre place entry q first hinv hrr hfr
          (hver hs.1) (hlag hs.1)) |> fun H => by
        first
          | exact H.move hs | exact H.guard hs | exact H.coupled hs | exact H.ver hs)

/-- **(NAMED, run form) the two chain-side facts.**  The chain's verifier
represents the input and its lag counters are canonical, at every `scan` state
the run reaches.  Unlike `hpack` this is not free at an arbitrary idle-chain
state, so `chainPosInv2_of_idle` gives no counterexample. -/
def VerRun (w : List (Fin 2)) (x : State GalilVM) : Prop :=
  ∀ (m : ℕ) (z : State GalilVM),
    Steps (galilFrameS (PofC centre place entry w) q first) 2048 m x z →
    z.ctl.mode = Mode.scan → VerRep w z.vm.chain ∧ LagCan z.vm.chain

/-- **`ShiftLocalS` along the run from `VerRun`.**  `shiftLocalS_of_run3` with
the bundle replaced: `ChainPosInv2` still travels on the four supplies, `repR`
comes from the run's own `LPackM`, and only `VerRun` is assumed. -/
theorem shiftLocalS_of_verRun {w : List (Fin 2)}
    (hbg : H_bgP2 centre place entry q first w) (hmatch : H_matchP2 centre place entry q first w)
    (hentry : H_shiftEntry2 centre place entry q first w)
    (hsd : H_shiftDoneRad2 centre place entry q first w)
    {n : ℕ} {x y : State GalilVM} (hx : ChainPosInv2 w x.ctl x.vm)
    (h : Steps (galilFrameS (PofC centre place entry w) q first) 2048 n x y)
    (hV : VerRun centre place entry q first w x)
    (hLP : PalPeg.CloseoutPackRun23.LPackM2 w y.ctl y.vm) :
    ShiftLocalS centre place entry q first w y := by
  refine shiftLocalS_of_parts centre place entry q first
    (chainPosInv2_steps centre place entry q first hbg hmatch hentry hsd hx h)
    (fun hm => ?_) (fun hm => (hV n y h hm).1) (fun hm => (hV n y h hm).2)
  cases hr : y.ctl.replaying with
  | false =>
    obtain ⟨rad, hi⟩ := hLP.packM.scanGeom hm hr
    exact ⟨hi.rightRep, hi.rightPresent⟩
  | true =>
    obtain ⟨rad, hi⟩ := hLP.scanGeomR hm hr
    exact ⟨hi.rightRep, hi.rightPresent⟩

/-- **The refuted hypothesis implies the run form.**  So replacing `hpk` by
`VerRun` loses nothing and drops the contradiction. -/
theorem verRun_of_hpack {w : List (Fin 2)} {x : State GalilVM}
    (hp : ∀ (c : Control) (s : GalilVM),
      ChainPosInv2 w c s → PalPeg.CloseoutChainPack.ChainPack q first w c s)
    (hbg : H_bgP2 centre place entry q first w) (hmatch : H_matchP2 centre place entry q first w)
    (hentry : H_shiftEntry2 centre place entry q first w)
    (hsd : H_shiftDoneRad2 centre place entry q first w)
    (hx : ChainPosInv2 w x.ctl x.vm) :
    VerRun centre place entry q first w x := by
  intro m z hz hm
  have hP := hp z.ctl z.vm
    (chainPosInv2_steps centre place entry q first hbg hmatch hentry hsd hx hz)
  exact ⟨hP.repV hm, hP.lagCan hm⟩

/-! ## Up to the top: `hpk` replaced by `VerRun` -/

/-- `radPack_ptS3` with `hpk` replaced by `VerRun` and the run's own `LPackM2`. -/
theorem radPack_ptS4 {w : List (Fin 2)} (hw : 0 < w.length) {st : ℕ → State GalilVM}
    {Tc : ℕ → ℕ} (hP : PreTrace centre place entry q first w st Tc)
    (hbg : H_bgP2 centre place entry q first w) (hmatch : H_matchP2 centre place entry q first w)
    (hentry : H_shiftEntry2 centre place entry q first w)
    (hsd : H_shiftDoneRad2 centre place entry q first w)
    (hpos0 : ChainPosInv2 w (st 0).ctl (st 0).vm)
    (hreach : ∀ i, i ≤ Tc w.length →
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 i (st 0) (st i))
    (hLP : ∀ i, i ≤ Tc w.length → PalPeg.CloseoutPackRun10.LPackM w (st i).ctl (st i).vm)
    (hLP2 : ∀ i, i ≤ Tc w.length → PalPeg.CloseoutPackRun23.LPackM2 w (st i).ctl (st i).vm)
    (hll : ∀ i, i ≤ Tc w.length → PalPeg.GalilTrailSane.LeftLive (st i).ctl (st i).vm)
    (hV : VerRun centre place entry q first w (st 0)) :
    ∀ i, i ≤ Tc w.length → RadPack (st i).ctl (st i).vm := by
  have hsh : ∀ i, i ≤ Tc w.length → ShiftLocalS centre place entry q first w (st i) := fun i hi =>
    shiftLocalS_of_verRun centre place entry q first hbg hmatch hentry hsd hpos0
      (hreach i hi) hV (hLP2 i hi)
  have hen : ∀ i, i ≤ Tc w.length → ScanNR (st i) → ∀ s'' t'' : GalilVM,
      (galilFrameS (PofC centre place entry w) q first).compare (st i).vm s'' →
      ¬ (galilFrameS (PofC centre place entry w) q first).matched s'' →
      shiftGuardVM s'' → beginShiftVM' s'' t'' → ShiftBud t'' := by
    intro i hi hs s'' t'' hcmp hmt hg hb
    obtain ⟨rad, hscan, hcan, hh⟩ :=
      halfBound_of_shiftLocalS centre place entry q first (hLP i hi) (hsh i hi) hs hcmp hmt hg hb
    exact shiftBud_of_scanInv (onLetterVM w) leftFirstVM centre place entry q first
      hscan hcan hcmp hb hh
  have hsv : ∀ i, i ≤ Tc w.length → ScanNR (st i) → ∀ s'' t'' : GalilVM,
      (galilFrameS (PofC centre place entry w) q first).compare (st i).vm s'' →
      ¬ (galilFrameS (PofC centre place entry w) q first).matched s'' →
      shiftGuardVM s'' → beginShiftVM' s'' t'' → SaneVer t''.chain := fun i hi hs s'' t'' =>
    saneVer_of_shiftLocalS centre place entry q first (hsh i hi) hs
  have hL := radLedger_pt centre place entry q first hw hP hll
  have hS := shiftOrd_ptS centre place entry q first hw hP hll hen
  have hVs := verSane_ptS centre place entry q first hw hP hll hsv
  exact fun i hi => radPack_of_parts (hL i hi) (hS i hi) (hll i hi) (hVs i hi)

/-- `trailF_ptS3` over `radPack_ptS4`. -/
theorem trailF_ptS4 {w : List (Fin 2)} (hw : 0 < w.length) {st : ℕ → State GalilVM}
    {Tc : ℕ → ℕ} (hP : PreTrace centre place entry q first w st Tc)
    (hbg : H_bgP2 centre place entry q first w) (hmatch : H_matchP2 centre place entry q first w)
    (hentry : H_shiftEntry2 centre place entry q first w)
    (hsd : H_shiftDoneRad2 centre place entry q first w)
    (hpos0 : ChainPosInv2 w (st 0).ctl (st 0).vm)
    (hreach : ∀ i, i ≤ Tc w.length →
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 i (st 0) (st i))
    (hLP : ∀ i, i ≤ Tc w.length → PalPeg.CloseoutPackRun10.LPackM w (st i).ctl (st i).vm)
    (hLP2 : ∀ i, i ≤ Tc w.length → PalPeg.CloseoutPackRun23.LPackM2 w (st i).ctl (st i).vm)
    (hll : ∀ i, i ≤ Tc w.length → PalPeg.GalilTrailSane.LeftLive (st i).ctl (st i).vm)
    (hV : VerRun centre place entry q first w (st 0))
    {m : ℕ} (hm : m < w.length) :
    ∀ i, i ≤ Tc (m+1) → TrailF w m (st i) := by
  have hsane := sanePack_pt centre place entry q first hw hP hll
  have hrad := radPack_ptS4 centre place entry q first hw hP hbg hmatch hentry hsd hpos0
    hreach hLP hLP2 hll hV
  have hscan := scanT_pt centre place entry q first hw hP hrad hsane hm
  have hB := chainBudget_pt centre place entry q first hw hP hrad hsane hm
  have hVf := verF_trace centre place entry q first hP hm hscan hB
  exact fun i hi => trailF_of_scanT (hscan i hi) (hVf i hi).ver (hVf i hi).lagPos

/-- **`needIMW'_le_W3` with `hpk` gone.**  `LPackM` and `LPackM2` both come off
the pre-trace's own packs, so the only new input is `VerRun`. -/
theorem needIMW'_le_W4 {w : List (Fin 2)} (hw : 0 < w.length)
    {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hP : PalPeg.CloseoutCheckW.PreTraceIMW centre place entry q first w st Tc)
    (hbg : H_bgP2 centre place entry q first w) (hmatch : H_matchP2 centre place entry q first w)
    (hentry : H_shiftEntry2 centre place entry q first w)
    (hsd : H_shiftDoneRad2 centre place entry q first w)
    (hpos0 : ChainPosInv2 w (st 0).ctl (st 0).vm)
    (hV : VerRun centre place entry q first w (st 0)) :
    ∀ m, m < w.length → ∀ i, i ≤ Tc (m+1) →
      PalPeg.GalilLookRefined.needL' w st i ≤ m + 1 := by
  have hbase := hP.base.pre
  have hreach : ∀ i, i ≤ Tc w.length →
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 i (st 0) (st i) := by
    intro i hi
    exact PalPeg.CloseoutPackRun2.steps_of_trace hbase.trace i hi
  have hLP : ∀ i, i ≤ Tc w.length →
      PalPeg.CloseoutPackRun10.LPackM w (st i).ctl (st i).vm :=
    fun i hi => (hP.packs i hi).pack
  have hLP2 : ∀ i, i ≤ Tc w.length →
      PalPeg.CloseoutPackRun23.LPackM2 w (st i).ctl (st i).vm :=
    fun i hi => (hP.packs i hi).m2
  have hll : ∀ i, i ≤ Tc w.length →
      PalPeg.GalilTrailSane.LeftLive (st i).ctl (st i).vm :=
    fun i hi => leftLive_of_lpackM (hLP i hi)
  intro m hm i hi
  exact needL'_le_of_trailF w st m i
    (trailF_ptS4 centre place entry q first hw hbase hbg hmatch hentry hsd hpos0
      hreach hLP hLP2 hll hV hm i hi)

end

#print axioms shiftLocalS_of_parts
#print axioms shiftLocalS_of_verRun
#print axioms verRun_of_hpack
#print axioms radPack_ptS4
#print axioms trailF_ptS4
#print axioms needIMW'_le_W4

end PalPeg.CloseoutVerSide
