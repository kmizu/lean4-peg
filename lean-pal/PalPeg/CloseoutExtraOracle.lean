import PalPeg.CloseoutExtraFree
import PalPeg.CloseoutStageOracle

/-!
# `hee` and `het` discharged: the run pack needs no `Extra7` input

`CloseoutExtraFree.packRunR_MG27P` builds the run pack from the cycle's own exit
bound instead of from `hprefix`.  Every caller has that bound already:

* the **progress** exit of `CycleOutMC3` carries `position sT.right ≤ 2*m-1` by
  definition (`GalilInvPlus3:213`) and `InvLPS` gives `c.replaying = false`
  through `invS_mode`;
* the **checkpoint** exit carries `ReportPointAt w m y`
  (`GalilReportPrefix`), whose fields are literally `notReplaying`,
  `atPlace : position y.vm.right = 2*m-1`, `pos : 1 ≤ m` and `le : m ≤ w.length`.

So the `Extra7` obligations never leave the run.  Both `hee` and `het` go.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutExtraOracle

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilTickArrive PalPeg.GalilLatchTracking PalPeg.GalilArriveChain
open PalPeg.GalilThrottledRun PalPeg.GalilThrottledRunGen PalPeg.GalilLedgerQ64
open PalPeg.GalilRunSkeleton PalPeg.GalilCheckpoints PalPeg.GalilTraceCost
open PalPeg.GalilOracleDischarge PalPeg.GalilOracleLocal PalPeg.GalilLexMeasure
open PalPeg.GalilInvPlus PalPeg.GalilInvPlus2 PalPeg.GalilOracleMC PalPeg.GalilOracleMC2
open PalPeg.GalilGlueBLeaves PalPeg.GalilBranchInvariants2 PalPeg.GalilSegmentConstruct
open PalPeg.GalilTruncTick PalPeg.GalilFinalAssembly PalPeg.GalilFinalAssembly2
open PalPeg.GalilFinalBaseNeed PalPeg.GalilFinalAssembly3 PalPeg.GalilOracleLeaves2
open PalPeg.GalilFinalAssembly4 PalPeg.GalilInvPlus3 PalPeg.CloseoutOracleI2
open PalPeg.CloseoutPackRun36 PalPeg.CloseoutStageCheck PalPeg.CloseoutStageBoot
open PalPeg.CloseoutPackRun PalPeg.CloseoutPackRun2 PalPeg.CloseoutPackRun3
open PalPeg.CloseoutPackRun5 PalPeg.CloseoutPackRun7 PalPeg.CloseoutPackRun8
open PalPeg.CloseoutPackRun9 PalPeg.CloseoutPackRun10 PalPeg.CloseoutPackRun11
open PalPeg.CloseoutPackRun12 PalPeg.CloseoutPackRun16 PalPeg.CloseoutPackRun18
open PalPeg.CloseoutPackRun19 PalPeg.CloseoutPackRun20 PalPeg.CloseoutPackRun21
open PalPeg.CloseoutPackRun23 PalPeg.CloseoutPackRun24 PalPeg.CloseoutPackRun29
open PalPeg.CloseoutPackRun30 PalPeg.CloseoutPackRun33 PalPeg.CloseoutPackRun35
open PalPeg.CloseoutPackRun26 PalPeg.CloseoutStageSupply
open PalPeg.CloseoutLPack PalPeg.CloseoutLPack2 PalPeg.CloseoutLPack3
open PalPeg.CloseoutLPack4 PalPeg.CloseoutLPack5 PalPeg.CloseoutLPack6
open PalPeg.CloseoutStageOracle PalPeg.CloseoutExtraFree PalPeg.CloseoutFrontExtra

variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- `CloseoutStageOracle.reachAtIMG2S_of_reachAtC3R` over `PackRunRMG2P`.  The
bounds the pack now asks for are read off `ReportPointAt` and `InvLPS`. -/
theorem reachAtIMG2S_of_reachAtC3R_P {w : List (Fin 2)}
    (hpr : PackRunRMG2P centre place entry q first w)
    {m : ℕ} {c : Control} {r : GalilVM} (hIC : InvLPC w c r)
    (hx : IPackMG2 centre place entry q first w ⟨c, r⟩)
    (h : ReachAtC3 (PofC centre place entry w) q first w m c r) :
    ReachAtIMG2S centre place entry q first w m c r := by
  obtain ⟨y, k, L, hst, hcr, hrp, hfr, hcont⟩ := h
  have hstI : StepsIMG2 centre place entry q first w k ⟨c, r⟩ y :=
    hpr c r hIC m hrp.pos hrp.le 0 ⟨c, r⟩ (.zero _) k y hx hst
      hrp.notReplaying (le_of_eq hrp.atPlace)
  refine ⟨y, k, L, hstI, hcr, hrp, hfr, fun hlt => ?_⟩
  obtain ⟨c', r', k', L', hst', hcr', hIS, hp⟩ := hcont hlt
  exact ⟨c', r', k', L',
    hpr c r hIC (m + 1) (by omega) (by omega) k y (stepsAll_steps hst) k' ⟨c', r'⟩
      (ipackMG2_last_of_stepsIMG2 centre place entry q first hstI) hst'
      (invS_mode hIS.1.1.1.1.1).2 hp,
    hcr', hIS, hp⟩

/-- `CloseoutStageOracle.cycleOutIMG2S_of_cycleOutMC3R` over `PackRunRMG2P`. -/
theorem cycleOutIMG2S_of_cycleOutMC3R_P {w : List (Fin 2)}
    (hpr : PackRunRMG2P centre place entry q first w)
    {m : ℕ} (hm1 : 1 ≤ m) (hmle : m ≤ w.length)
    {c : Control} {r : GalilVM} (hIC : InvLPC w c r)
    (hx : IPackMG2 centre place entry q first w ⟨c, r⟩)
    (h : CycleOutMC3 (PofC centre place entry w) q first w m c r) :
    CycleOutIMG2S centre place entry q first w m c r := by
  rcases h with hdone | ⟨cT, sT, k, L, hst, hcr, hIT, hlt, hpos⟩
  · exact Or.inl (reachAtIMG2S_of_reachAtC3R_P centre place entry q first hpr hIC hx hdone)
  · exact Or.inr ⟨cT, sT, k, L,
      hpr c r hIC m hm1 hmle 0 ⟨c, r⟩ (.zero _) k ⟨cT, sT⟩ hx hst
        (invS_mode hIT.1.1.1.1.1).2 hpos,
      hcr, hIT, hlt, hpos⟩

/-- **`H_oracleIMG2S` with no `Extra7` input.** -/
theorem h_oracleIMG2S_of_MC3_P
    (hpr : ∀ w : List (Fin 2), PackRunRMG2P centre place entry q first w)
    (hsl : ∀ w : List (Fin 2), H_shiftLocalG centre place entry q first w)
    (hor : ∀ w : List (Fin 2), 0 < w.length →
      CycleOracleMC3 (PofC centre place entry w) q first w) :
    H_oracleIMG2S centre place entry q first := by
  intro w hw m c r hm1 hmle hI hp
  exact cycleOutIMG2S_of_cycleOutMC3R_P centre place entry q first (hpr w) hm1 hmle hI.1
    (ipackMG2_of_invLPC centre place entry q first (hsl w) hI.1)
    (hor w hw m c r hm1 hmle hI hp)

#print axioms reachAtIMG2S_of_reachAtC3R_P
#print axioms cycleOutIMG2S_of_cycleOutMC3R_P
#print axioms h_oracleIMG2S_of_MC3_P

end PalPeg.CloseoutExtraOracle
