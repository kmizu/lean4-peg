import PalPeg.CloseoutStageBoot

/-!
# `H_stageScan` removed from the main path

The three pieces are in place:

* `CloseoutStageCheck` runs Run36 §2's checkpoint recursion over `InvLPS`
  (`checkpoints_costIMG2S_upto1`, `preTraceIMG2S_exists`), whose conclusion
  `PreTraceIMG2` is *identical* to the old one — so this is a drop-in.
* `CloseoutStageBoot.invLPS_init` shows the boot landing carries the stage:
  `GalilFinalAssembly4.invLPC_init` already builds it from `hI : Inv`, and
  `replayStage_of_inv` closes that disjunct for free.
* `CycleOutMC3`'s own exits (`GalilInvPlus3:193, :212`) hand back `InvLPS`.

So the stage is *produced* everywhere it is *consumed*, and
`hstage_of_scanBranch` — the one consumer of `H_stageScan` on the main path — is
never called.  This file supplies `H_bootIMG2S` and `H_oracleIMG2S`.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutStageOracle

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

variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- `CloseoutPackRun36.reachAtIMG2_of_reachAtC3R` (:640) keeping the stage: the
continuation of `ReachAtC3` is already `InvLPS`, and the old proof drops it with
`hIS.1`. -/
theorem reachAtIMG2S_of_reachAtC3R {w : List (Fin 2)}
    (hpr : PackRunRMG2 centre place entry q first w)
    {m : ℕ} {c : Control} {r : GalilVM} (hIC : InvLPC w c r)
    (hx : IPackMG2 centre place entry q first w ⟨c, r⟩)
    (h : ReachAtC3 (PofC centre place entry w) q first w m c r) :
    ReachAtIMG2S centre place entry q first w m c r := by
  obtain ⟨y, k, L, hst, hcr, hrp, hfr, hcont⟩ := h
  have hstI : StepsIMG2 centre place entry q first w k ⟨c, r⟩ y :=
    hpr c r hIC 0 ⟨c, r⟩ (.zero _) k y hx hst
  refine ⟨y, k, L, hstI, hcr, hrp, hfr, fun hlt => ?_⟩
  obtain ⟨c', r', k', L', hst', hcr', hIS, hp⟩ := hcont hlt
  exact ⟨c', r', k', L',
    hpr c r hIC k y (stepsAll_steps hst) k' ⟨c', r'⟩
      (ipackMG2_last_of_stepsIMG2 centre place entry q first hstI) hst',
    hcr', hIS, hp⟩

/-- `cycleOutIMG2_of_cycleOutMC3R` (:660) keeping the stage. -/
theorem cycleOutIMG2S_of_cycleOutMC3R {w : List (Fin 2)}
    (hpr : PackRunRMG2 centre place entry q first w)
    {m : ℕ} {c : Control} {r : GalilVM} (hIC : InvLPC w c r)
    (hx : IPackMG2 centre place entry q first w ⟨c, r⟩)
    (h : CycleOutMC3 (PofC centre place entry w) q first w m c r) :
    CycleOutIMG2S centre place entry q first w m c r := by
  rcases h with hdone | ⟨cT, sT, k, L, hst, hcr, hIT, hlt, hpos⟩
  · exact Or.inl (reachAtIMG2S_of_reachAtC3R centre place entry q first hpr hIC hx hdone)
  · exact Or.inr ⟨cT, sT, k, L, hpr c r hIC 0 ⟨c, r⟩ (.zero _) k ⟨cT, sT⟩ hx hst,
      hcr, hIT, hlt, hpos⟩

/-- **`H_oracleIMG2S` from `CycleOracleMC3`, with no `H_stageScan`.**  Compare
`cycleOracleIMG2_of_cycleOracleMC3R` (:673), whose extra argument `hsc` feeds
`hstage_of_scanBranch`; here the entry invariant is already `InvLPS`. -/
theorem h_oracleIMG2S_of_MC3
    (hpr : ∀ w : List (Fin 2), PackRunRMG2 centre place entry q first w)
    (hsl : ∀ w : List (Fin 2), H_shiftLocalG centre place entry q first w)
    (hor : ∀ w : List (Fin 2), 0 < w.length →
      CycleOracleMC3 (PofC centre place entry w) q first w) :
    H_oracleIMG2S centre place entry q first := by
  intro w hw m c r hm1 hmle hI hp
  exact cycleOutIMG2S_of_cycleOutMC3R centre place entry q first (hpr w) hI.1
    (ipackMG2_of_invLPC centre place entry q first (hsl w) hI.1)
    (hor w hw m c r hm1 hmle hI hp)

/-- **`H_bootIMG2S` from `BootIPack`.**  Every step of the boot chain
(`h_bootIO_of_h_bootI`, `h_bootIM_of_h_bootIO`, `h_bootIMG_of_h_bootIM`,
`h_bootIMG2_of_h_bootIMG`) only strengthens the run pack and passes the landing
invariant through untouched, so the whole chain runs over `invLPS_init` the same
way it runs over `invLPC_init`. -/
theorem h_bootIMG2S_of_bootIPack
    (hsl : ∀ w : List (Fin 2), H_shiftLocalG centre place entry q first w)
    (hb : BootIPack centre place entry q first) :
    H_bootIMG2S centre place entry q first := by
  intro a rest
  obtain ⟨c1, t, hsteps, hI, hpos, -⟩ := invLPS_init centre place entry q first a rest
  obtain ⟨hp0, hp1⟩ := hb a rest
  obtain ⟨g, hg0, hg1, htr⟩ := stepsAll_fn hsteps
  have hstI : StepsI centre place entry q first (a :: rest) 1
      ⟨GalilScaffoldController.initial 2048, GalilBootVM.initVM0 (a :: rest)⟩ ⟨c1, t⟩ := by
    refine ⟨g, hg0, hg1, htr, ?_⟩
    intro i hi
    interval_cases i
    · rw [hg0]; exact hp0
    · rw [hg1]; exact hp1 c1 t hsteps hI.1
  have hstG := stepsIMG_of_stepsIM centre place entry q first
    (stepsIM_of_stepsIO centre place entry q first
      (stepsIO_of_stepsI centre place entry q first hstI))
  obtain ⟨g2, hg20, hg21, htr2, hp2⟩ := hstG
  refine ⟨c1, t, ⟨g2, hg20, hg21, htr2, fun i hi => ⟨hp2 i hi, ?_⟩⟩, hI, hpos⟩
  cases i with
  | zero => rw [hg20]; exact lpackM2_boot (a :: rest)
  | succ n =>
    cases n with
    | zero =>
      rw [hg21]
      exact lpackM2_of_invLPC centre place entry q first (hsl _) hI.1
    | succ n => omega

#print axioms reachAtIMG2S_of_reachAtC3R
#print axioms cycleOutIMG2S_of_cycleOutMC3R
#print axioms h_oracleIMG2S_of_MC3
#print axioms h_bootIMG2S_of_bootIPack

end PalPeg.CloseoutStageOracle
