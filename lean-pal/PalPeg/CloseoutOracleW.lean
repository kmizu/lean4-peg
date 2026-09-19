import PalPeg.CloseoutCheckW
import PalPeg.CloseoutExtraOracle
import PalPeg.CloseoutShiftS

/-!
# The oracle and boot over `IPackMW`

`CloseoutExtraOracle` wired the `Extra7`-free run pack to `CycleOracleMC3`;
this is the same wiring over `IPackMW`, so no `ShiftLocalG` is needed to fill
the pack.

`PackRunRMW` is `CloseoutExtraFree.PackRunRMG2P` with `IPackMG2` replaced by
`IPackMW`, and `packRunR_MW` builds it with **no** shift hypothesis at all:
the `Extra7` comes from the run (`CloseoutFrontExtra`) and the dropped `shift`
field needs nothing.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutOracleW

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open PalPeg.GalilThrottledRun PalPeg.GalilTrailProof PalPeg.GalilFinalAssembly
open PalPeg.GalilRunSkeleton PalPeg.GalilCheckpoints PalPeg.GalilTraceCost
open PalPeg.GalilOracleDischarge PalPeg.GalilOracleLocal
open PalPeg.GalilInvPlus PalPeg.GalilInvPlus2 PalPeg.GalilOracleMC PalPeg.GalilOracleMC2
open PalPeg.GalilFinalAssembly2 PalPeg.GalilFinalAssembly4
open PalPeg.CloseoutOracleI PalPeg.CloseoutOracleI2 PalPeg.GalilInvPlus3
open PalPeg.CloseoutPackRun PalPeg.CloseoutPackRun2 PalPeg.CloseoutPackRun3
open PalPeg.CloseoutPackRun5 PalPeg.CloseoutPackRun7 PalPeg.CloseoutPackRun8
open PalPeg.CloseoutPackRun9 PalPeg.CloseoutPackRun10 PalPeg.CloseoutPackRun11
open PalPeg.CloseoutPackRun12 PalPeg.CloseoutPackRun16 PalPeg.CloseoutPackRun18
open PalPeg.CloseoutPackRun19 PalPeg.CloseoutPackRun20 PalPeg.CloseoutPackRun21
open PalPeg.CloseoutPackRun23 PalPeg.CloseoutPackRun24 PalPeg.CloseoutPackRun26
open PalPeg.CloseoutPackRun29 PalPeg.CloseoutPackRun30 PalPeg.CloseoutPackRun33
open PalPeg.CloseoutPackRun35 PalPeg.CloseoutPackRun36 PalPeg.CloseoutPackRun43
open PalPeg.CloseoutPreload37 PalPeg.CloseoutPackRun22 PalPeg.CloseoutPackRun45
open PalPeg.CloseoutLPack PalPeg.CloseoutLPack2 PalPeg.CloseoutLPack3
open PalPeg.CloseoutLPack4 PalPeg.CloseoutLPack5 PalPeg.CloseoutLPack6
open GalilScaffoldInputHead GalilScaffoldCounter GalilScaffoldChainVerifier
open PalPeg.CloseoutPackRun46 PalPeg.CloseoutFrontExtra
open PalPeg.CloseoutExtraFree
open PalPeg.CloseoutShiftWeak
open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open PalPeg.GalilThrottledRun PalPeg.GalilTrailProof PalPeg.GalilFinalAssembly
open PalPeg.CloseoutRadPack PalPeg.CloseoutRadPack2 PalPeg.CloseoutRadPack3
open PalPeg.CloseoutRadPack4 PalPeg.CloseoutLPack PalPeg.CloseoutLPack2
open PalPeg.CloseoutLPack3 PalPeg.CloseoutLPack4 PalPeg.CloseoutLPack5
open PalPeg.CloseoutLPack6
open PalPeg.GalilRunSkeleton PalPeg.GalilCheckpoints PalPeg.GalilTraceCost
open PalPeg.GalilOracleDischarge PalPeg.GalilOracleLocal PalPeg.GalilLexMeasure
open PalPeg.GalilInvPlus PalPeg.GalilInvPlus2 PalPeg.GalilOracleMC PalPeg.GalilOracleMC2
open PalPeg.GalilLookRefined PalPeg.GalilFinalBaseNeed PalPeg.GalilFinalAssembly2
open PalPeg.GalilLedgerQ64 PalPeg.GalilLedgerAssembly PalPeg.GalilIntervalCost
open PalPeg.GalilLatchTracking PalPeg.GalilArriveChain PalPeg.GalilTickArrive
open PalPeg.GalilTruncTick PalPeg.GalilFinalAssembly4
open PalPeg.GalilTrailScan PalPeg.GalilTrailBudget PalPeg.GalilTrailChain
open PalPeg.GalilTrailAssembly PalPeg.GalilTrailRad PalPeg.GalilFrontMono
open PalPeg.CloseoutOracleI PalPeg.CloseoutOracleI2 PalPeg.GalilInvPlus3
open PalPeg.CloseoutPackRun PalPeg.CloseoutPackRun2 PalPeg.CloseoutPackRun3
open PalPeg.CloseoutPackRun5 PalPeg.CloseoutPackRun7 PalPeg.CloseoutPackRun8
open PalPeg.CloseoutPackRun9 PalPeg.CloseoutPackRun10 PalPeg.CloseoutPackRun11
open PalPeg.CloseoutPackRun12 PalPeg.CloseoutPackRun16 PalPeg.CloseoutPackRun18
open PalPeg.CloseoutPackRun19 PalPeg.CloseoutPackRun20 PalPeg.CloseoutPackRun21
open PalPeg.CloseoutPackRun23 PalPeg.CloseoutPackRun24 PalPeg.CloseoutPackRun26
open PalPeg.CloseoutPackRun29 PalPeg.CloseoutPackRun30 PalPeg.CloseoutPackRun33
open PalPeg.CloseoutPackRun35
open GalilScaffoldInputHead GalilScaffoldCounter GalilScaffoldChainVerifier
open PalPeg.CloseoutPackRun36 PalPeg.CloseoutPackW PalPeg.CloseoutStageCheck
open PalPeg.CloseoutCheckW PalPeg.CloseoutExtraOracle PalPeg.CloseoutExtraFree
open PalPeg.CloseoutFrontExtra PalPeg.CloseoutStageOracle PalPeg.CloseoutStageBoot
open PalPeg.CloseoutShiftS PalPeg.CloseoutPackRun34 PalPeg.GalilLookRefined

section
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- `CloseoutExtraFree.PackRunRMG2P` over `IPackMW`. -/
def PackRunRMW (w : List (Fin 2)) : Prop :=
  ∀ (c : Control) (r : GalilVM),
    PalPeg.GalilInvPlus3.InvLPS (PofC centre place entry w) q first w c r →
    ∀ (M : ℕ), 1 ≤ M → M ≤ w.length →
    ∀ (j : ℕ) (x : State GalilVM),
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 j ⟨c, r⟩ x →
      ∀ (k : ℕ) (y : State GalilVM), IPackMW centre place entry q first w x →
        StepsAll (galilFrameS (PofC centre place entry w) q first) 2048 (SoundScanNR w) k x y →
        y.ctl.replaying = false → position y.vm.right ≤ 2 * M - 1 →
        StepsIMW centre place entry q first w k x y

/-- `IPackMW` at an `InvLPC` origin, by forgetting the `shift` field of
`CloseoutPackRun36.ipackMG2_of_invLPC`. -/
theorem ipackMW_of_invLPC {w : List (Fin 2)}
    (hsl : PalPeg.CloseoutPackRun26.H_shiftLocalG centre place entry q first w)
    {c : Control} {r : GalilVM} (hIC : InvLPC w c r) :
    IPackMW centre place entry q first w ⟨c, r⟩ :=
  ipackMW_of_ipackMG2 centre place entry q first
    (PalPeg.CloseoutPackRun36.ipackMG2_of_invLPC centre place entry q first hsl hIC)
    (fun _ => PalPeg.WindowPack.windowRunPack_of_invLPC hIC)

/-- `CloseoutStageOracle.reachAtIMG2S_of_reachAtC3R` over `PackRunRMW`.  The
bounds the pack now asks for are read off `ReportPointAt` and `InvLPS`. -/
theorem reachAtIMW_of_reachAtC3R_W {w : List (Fin 2)}
    (hpr : PackRunRMW centre place entry q first w)
    {m : ℕ} {c : Control} {r : GalilVM}
    (hIC : PalPeg.GalilInvPlus3.InvLPS (PofC centre place entry w) q first w c r)
    (hx : IPackMW centre place entry q first w ⟨c, r⟩)
    (h : ReachAtC3 (PofC centre place entry w) q first w m c r) :
    ReachAtIMW centre place entry q first w m c r := by
  obtain ⟨y, k, L, hst, hcr, hrp, hfr, hcont⟩ := h
  have hstI : StepsIMW centre place entry q first w k ⟨c, r⟩ y :=
    hpr c r hIC m hrp.pos hrp.le 0 ⟨c, r⟩ (.zero _) k y hx hst
      hrp.notReplaying (le_of_eq hrp.atPlace)
  refine ⟨y, k, L, hstI, hcr, hrp, hfr, fun hlt => ?_⟩
  obtain ⟨c', r', k', L', hst', hcr', hIS, hp⟩ := hcont hlt
  exact ⟨c', r', k', L',
    hpr c r hIC (m + 1) (by omega) (by omega) k y (stepsAll_steps hst) k' ⟨c', r'⟩
      (ipackMW_last_of_stepsIMW centre place entry q first hstI) hst'
      (invS_mode hIS.1.1.1.1.1).2 hp,
    hcr', hIS, hp⟩

/-- `CloseoutStageOracle.cycleOutIMG2S_of_cycleOutMC3R` over `PackRunRMW`. -/
theorem cycleOutIMW_of_cycleOutMC3R_W {w : List (Fin 2)}
    (hpr : PackRunRMW centre place entry q first w)
    {m : ℕ} (hm1 : 1 ≤ m) (hmle : m ≤ w.length)
    {c : Control} {r : GalilVM}
    (hIC : PalPeg.GalilInvPlus3.InvLPS (PofC centre place entry w) q first w c r)
    (hx : IPackMW centre place entry q first w ⟨c, r⟩)
    (h : CycleOutMC3 (PofC centre place entry w) q first w m c r) :
    CycleOutIMW centre place entry q first w m c r := by
  rcases h with hdone | ⟨cT, sT, k, L, hst, hcr, hIT, hlt, hpos⟩
  · exact Or.inl (reachAtIMW_of_reachAtC3R_W centre place entry q first hpr hIC hx hdone)
  · exact Or.inr ⟨cT, sT, k, L,
      hpr c r hIC m hm1 hmle 0 ⟨c, r⟩ (.zero _) k ⟨cT, sT⟩ hx hst
        (invS_mode hIT.1.1.1.1.1).2 hpos,
      hcr, hIT, hlt, hpos⟩

/-- **`H_oracleIMW` with no `Extra7` input.** -/
theorem h_oracleIMW_of_MC3_W
    (hpr : ∀ w : List (Fin 2), PackRunRMW centre place entry q first w)
    (hsl : ∀ w : List (Fin 2), H_shiftLocalG centre place entry q first w)
    (hor : ∀ w : List (Fin 2), 0 < w.length →
      CycleOracleMC3 (PofC centre place entry w) q first w) :
    H_oracleIMW centre place entry q first := by
  intro w hw m c r hm1 hmle hI hp
  exact cycleOutIMW_of_cycleOutMC3R_W centre place entry q first (hpr w) hm1 hmle hI
    (ipackMW_of_invLPC centre place entry q first (hsl w) hI.1)
    (hor w hw m c r hm1 hmle hI hp)


/-- **`PackRunRMW` with no shift hypothesis at all.** -/
theorem packRunR_MW {w : List (Fin 2)}
    (hSP : ∀ x : State GalilVM, BigPack2MG7W centre place entry q first w x →
      ScanNR x → ShiftPal centre place entry q first w x.vm)
    (hme : H_marksEntry' (PofC centre place entry w) q first)
    :
    PackRunRMW centre place entry q first w := by
  intro c r hInvLPS M hm1 hmle j x hjx k y hx h hry hyb
  have hIC : InvLPC w c r := hInvLPS.1
  have hlv0 : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 m ⟨c, r⟩ z →
      CentreLive z.ctl z.vm :=
    PalPeg.GalilOracleLeaves2.hlive_of_invLPC centre place entry q first hIC
  have haux0 : AuxPack c r :=
    ⟨coupled_of_invLPC hIC, front_of_invLPC hIC, copyPack_of_invLPC hIC⟩
  have hauxx : AuxPack x.ctl x.vm :=
    auxPack_steps centre place entry q first (x := ⟨c, r⟩) hlv0 haux0 hjx
  have hmx : MarksInv' first x.ctl x.vm :=
    marksInv'_of_run (PofC centre place entry w) q first 2048 hme (x := ⟨c, r⟩) hjx
      (m := Mode.scan) (by decide) (invS_mode hIC.1.1.1.1).1
  obtain ⟨g, hg0, hgk, htr⟩ := stepsAll_fn h
  have hreach : ∀ i, i ≤ k →
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 (j + i) ⟨c, r⟩ (g i) := by
    intro i hi
    have := steps_of_trace htr i hi
    rw [hg0] at this
    exact steps_trans hjx this
  have hauxi : ∀ i, i ≤ k → AuxPack (g i).ctl (g i).vm := fun i hi =>
    auxPack_steps centre place entry q first (x := ⟨c, r⟩) hlv0 haux0 (hreach i hi)
  have hgy : g k = y := hgk
  subst hgy
  have hextra : ∀ i, i ≤ k → IPackMW centre place entry q first w (g i) → Extra7 (g i) := by
    intro i hi hip
    refine extra7_of_front_steps_pack (m := M) (w := w)
      (steps_to_end_of_trace htr (k - i) i (by omega)) ?_ (hauxi i hi).front ?_ ?_ ?_ hm1 hmle ?_
    · intro d z hz
      exact hlv0 (j + i + d) z (steps_trans (hreach i hi) hz)
    · exact (hauxi k le_rfl).front
    · exact hry
    · exact hip.pack
    · exact hyb
  have hexx : Extra7 x := by
    have := hextra 0 (Nat.zero_le _) (by rw [hg0]; exact hx)
    rw [hg0] at this; exact this
  have hbx : BigPack2MG7W'' centre place entry q first w x :=
    ⟨hx, hauxx, hlv0 j x hjx, hmx, hexx⟩
  have hbig : ∀ i, i ≤ k → BigPack2MG7W'' centre place entry q first w (g i) := by
    intro i
    induction i with
    | zero => intro _; rw [hg0]; exact hbx
    | succ n ih =>
      intro hi
      have hn := ih (by omega)
      exact bigPack2MG7W''_tick centre place entry q first hme hn
        (fun hip => hextra (n+1) hi hip)
        (fun hs => hSP (g n) (bigPack2MG7W_of_W'' centre place entry q first hn
          (fun hm => absurd (hs.1.symm.trans hm) (by decide))) hs)
        (htr.tick n (by omega)) (htr.good (n+1) hi)
        (hlv0 (j + (n+1)) (g (n+1)) (hreach (n+1) hi))
  exact ⟨g, hg0, hgk, htr, fun i hi => (hbig i hi).ipackM⟩


/-- **`H_bootIMW` from `BootIPack`.** -/
theorem h_bootIMW_of_bootIPack
    (hsl : ∀ w : List (Fin 2), H_shiftLocalG centre place entry q first w)
    (hb : BootIPack centre place entry q first) :
    H_bootIMW centre place entry q first := by
  intro a rest
  obtain ⟨c1, t, hsteps, hI, hpos⟩ := invLPS_init centre place entry q first a rest
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
  refine ⟨c1, t, ⟨g2, hg20, hg21, htr2, fun i hi => ⟨(hp2 i hi).pack, ?_, ?_⟩⟩, hI, hpos⟩
  · cases i with
    | zero => rw [hg20]; exact lpackM2_boot (a :: rest)
    | succ n =>
      cases n with
      | zero =>
        rw [hg21]
        exact lpackM2_of_invLPC centre place entry q first (hsl _) hI.1
      | succ n => omega
  · cases i with
    | zero => rw [hg20]; exact fun _ => PalPeg.WindowPack.windowRunPack_boot (a :: rest)
    | succ n =>
      cases n with
      | zero => rw [hg21]; exact fun _ => PalPeg.WindowPack.windowRunPack_of_invLPC hI.1
      | succ n => omega


/-- **`needL'` over `PreTraceIMW`.** -/
theorem needIMW'_le_W {w : List (Fin 2)} (hw : 0 < w.length)
    {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hP : PalPeg.CloseoutCheckW.PreTraceIMW centre place entry q first w st Tc)
    (hfour : H_FourSemiperiodsLeDistance centre place entry q first w)
    (hbg : H_BackgroundLandingPayload centre place entry q first w) (hmatch : H_MatchLandingPayload centre place entry q first w)
    (hsd : H_ShiftExitPayload centre place entry q first w)
    (hpos0 : ChainPositionInvariant w (st 0).ctl (st 0).vm) :
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
    (trailF_ptS centre place entry q first hw hbase hfour hbg hmatch hsd hpos0
      hreach hLP hll hm i hi)


#print axioms needIMW'_le_W
#print axioms h_bootIMW_of_bootIPack
#print axioms packRunR_MW
#print axioms reachAtIMW_of_reachAtC3R_W
#print axioms cycleOutIMW_of_cycleOutMC3R_W
#print axioms h_oracleIMW_of_MC3_W

end

end PalPeg.CloseoutOracleW
