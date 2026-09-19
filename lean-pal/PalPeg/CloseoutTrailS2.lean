import PalPeg.CloseoutShiftS2
import PalPeg.CloseoutOracleW

/-!
# The trail bridge over `ChainPositionInvariantWithShiftPhase`: `H_FourSemiperiodsLeDistance` gone

`CloseoutShiftS`'s chain (`radPack_ptS` → `trailF_ptS`) runs on
`CloseoutPackRun34.ChainPositionInvariant` and therefore carries `H_FourSemiperiodsLeDistance`.
`CloseoutShiftS2.shiftLocalS_of_run2` produces the same `ShiftLocalS` from
`CloseoutPackRun41.ChainPositionInvariantWithShiftPhase`, whose `watchShiftS_of_chainPosInv2` needs
**no** `H_FourSemiperiodsLeDistance` — the target's verifier pair comes from `chainPos_step`.

Its branch hypotheses (`H_BackgroundLandingChainLedger`, `H_MatchLandingChainLedger`, `H_ShiftEntryChainLedger`,
`H_ShiftExitRadiusLedger`) are all discharged in `CloseoutPackRun48`, modulo
`ConsumeAvail` — a `take`/`immediate` consume moves the verifier, and `canRight`
of the *moved* verifier is an input-supply fact, not a consequence of the source
(`CloseoutPackRun41` §2).

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutTrailS2

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton PalPeg.GalilFrontMono PalPeg.GalilChainCoupling
open PalPeg.CloseoutLPack5 PalPeg.CloseoutPackRun6 PalPeg.CloseoutPackRun10
open PalPeg.CloseoutRadPack2 PalPeg.CloseoutRadPack4
open PalPeg.CloseoutPackRun26 PalPeg.CloseoutPackRun30 PalPeg.CloseoutPackRun32
open PalPeg.CloseoutPackRun26 PalPeg.CloseoutPackRun34 PalPeg.CloseoutFrontExtra
open PalPeg.CloseoutLPack PalPeg.CloseoutPackRun10 PalPeg.CloseoutPackRun30
open PalPeg.CloseoutLPack5 PalPeg.CloseoutLPack6 PalPeg.CloseoutPackRun12
open PalPeg.GalilTrailSane PalPeg.GalilChainCoupling PalPeg.GalilBranchInvariants
open PalPeg.CloseoutPackRun11 PalPeg.CloseoutPackRun9 PalPeg.CloseoutPackRun8
open PalPeg.GalilTrailChain PalPeg.GalilFinalAssembly PalPeg.GalilThrottledRun
open PalPeg.CloseoutRadPack PalPeg.CloseoutRadPack2 PalPeg.CloseoutRadPack3 PalPeg.CloseoutRadPack4
open PalPeg.GalilTrailRad PalPeg.GalilTrailProof PalPeg.GalilTrailAssembly
open PalPeg.GalilTrailScan PalPeg.GalilTrailBudget PalPeg.GalilTrailFront
open PalPeg.CloseoutPackRun41 PalPeg.CloseoutPackRun44 PalPeg.CloseoutPackRun47
open PalPeg.CloseoutPackRun48 PalPeg.CloseoutShiftS2 PalPeg.CloseoutOracleW
open PalPeg.CloseoutCheckW PalPeg.CloseoutShiftS

section
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

theorem radPack_ptS2 {w : List (Fin 2)} (hw : 0 < w.length) {st : ℕ → State GalilVM}
    {Tc : ℕ → ℕ} (hP : PreTrace centre place entry q first w st Tc)
    (hbg : H_BackgroundLandingChainLedger centre place entry q first w) (hmatch : H_MatchLandingChainLedger centre place entry q first w)
    (hentry : H_ShiftEntryChainLedger centre place entry q first w)
    (hsd : H_ShiftExitRadiusLedger centre place entry q first w)
    (hpos0 : ChainPositionInvariantWithShiftPhase w (st 0).ctl (st 0).vm)
    (hreach : ∀ i, i ≤ Tc w.length →
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 i (st 0) (st i))
    (hLP : ∀ i, i ≤ Tc w.length → PalPeg.CloseoutPackRun10.LPackM w (st i).ctl (st i).vm)
    (hll : ∀ i, i ≤ Tc w.length → PalPeg.GalilTrailSane.LeftLive (st i).ctl (st i).vm)
    (hav : ∀ i, i ≤ Tc w.length → ConsumeAvail (st i).vm.chain)
    (hCanRightAlongRun : ∀ (j : ℕ) (z : State GalilVM),
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 j (st 0) z →
      z.ctl.mode = Mode.scan ∨ z.ctl.mode = Mode.shift →
      GalilScaffoldChainVerifier.canRight z.vm.right) :
    ∀ i, i ≤ Tc w.length → RadPack (st i).ctl (st i).vm := by
  have hsh : ∀ i, i ≤ Tc w.length → ShiftLocalS centre place entry q first w (st i) := fun i hi =>
    shiftLocalS_of_run2 centre place entry q first hbg hmatch hentry hsd hCanRightAlongRun hpos0
      (hreach i hi) (hav i hi)
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
  have hV := verSane_ptS centre place entry q first hw hP hll hsv
  exact fun i hi => radPack_of_parts (hL i hi) (hS i hi) (hll i hi) (hV i hi)


theorem trailF_ptS2 {w : List (Fin 2)} (hw : 0 < w.length) {st : ℕ → State GalilVM}
    {Tc : ℕ → ℕ} (hP : PreTrace centre place entry q first w st Tc)
    (hbg : H_BackgroundLandingChainLedger centre place entry q first w) (hmatch : H_MatchLandingChainLedger centre place entry q first w)
    (hentry : H_ShiftEntryChainLedger centre place entry q first w)
    (hsd : H_ShiftExitRadiusLedger centre place entry q first w)
    (hpos0 : ChainPositionInvariantWithShiftPhase w (st 0).ctl (st 0).vm)
    (hreach : ∀ i, i ≤ Tc w.length →
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 i (st 0) (st i))
    (hLP : ∀ i, i ≤ Tc w.length → PalPeg.CloseoutPackRun10.LPackM w (st i).ctl (st i).vm)
    (hll : ∀ i, i ≤ Tc w.length → PalPeg.GalilTrailSane.LeftLive (st i).ctl (st i).vm)
    (hav : ∀ i, i ≤ Tc w.length → ConsumeAvail (st i).vm.chain)
    (hCanRightAlongRun : ∀ (j : ℕ) (z : State GalilVM),
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 j (st 0) z →
      z.ctl.mode = Mode.scan ∨ z.ctl.mode = Mode.shift →
      GalilScaffoldChainVerifier.canRight z.vm.right)
    {m : ℕ} (hm : m < w.length) :
    ∀ i, i ≤ Tc (m+1) → TrailF w m (st i) := by
  have hsane := sanePack_pt centre place entry q first hw hP hll
  have hrad := radPack_ptS2 centre place entry q first hw hP hbg hmatch hentry hsd hpos0
    hreach hLP hll hav hCanRightAlongRun
  have hscan := scanT_pt centre place entry q first hw hP hrad hsane hm
  have hB := chainBudget_pt centre place entry q first hw hP hrad hsane hm
  have hV := verF_trace centre place entry q first hP hm hscan hB
  exact fun i hi => trailF_of_scanT (hscan i hi) (hV i hi).ver (hV i hi).lagPos


theorem needIMW'_le_W2 {w : List (Fin 2)} (hw : 0 < w.length)
    {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hP : PalPeg.CloseoutCheckW.PreTraceIMW centre place entry q first w st Tc)
    (hbg : H_BackgroundLandingChainLedger centre place entry q first w) (hmatch : H_MatchLandingChainLedger centre place entry q first w)
    (hentry : H_ShiftEntryChainLedger centre place entry q first w)
    (hsd : H_ShiftExitRadiusLedger centre place entry q first w)
    (hpos0 : ChainPositionInvariantWithShiftPhase w (st 0).ctl (st 0).vm)
    (hav : ∀ i, i ≤ Tc w.length → ConsumeAvail (st i).vm.chain)
    (hCanRightAtAnyScanOrShiftState : ∀ z : State GalilVM,
      z.ctl.mode = Mode.scan ∨ z.ctl.mode = Mode.shift →
      GalilScaffoldChainVerifier.canRight z.vm.right)
    :
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
  have hll : ∀ i, i ≤ Tc w.length →
      PalPeg.GalilTrailSane.LeftLive (st i).ctl (st i).vm :=
    fun i hi => leftLive_of_lpackM (hLP i hi)
  intro m hm i hi
  exact needL'_le_of_trailF w st m i
    (trailF_ptS2 centre place entry q first hw hbase hbg hmatch hentry hsd hpos0
      hreach hLP hll hav (fun _ z' _ => hCanRightAtAnyScanOrShiftState z') hm i hi)



#print axioms radPack_ptS2
#print axioms trailF_ptS2
#print axioms needIMW'_le_W2

end

end PalPeg.CloseoutTrailS2
