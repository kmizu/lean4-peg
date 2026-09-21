import PalPeg.PackedRun
import PalPeg.CloseoutPackW
import PalPeg.CloseoutStageCheck
import PalPeg.ShapedRun

/-!
# The checkpoint layer over `IPackMW`: no `ShiftLocalG` anywhere

`CloseoutStageCheck` runs Run36 §2's checkpoint recursion over `InvLPS`;
this file runs the same recursion over `IPackMW` — the pack with the refuted
`shift` field dropped (`CloseoutPackW`).  The conclusion `PreTraceIMW` is the
`IPackMW` analogue of `PreTraceIMG2`.

Nothing here mentions `WatchShiftG` or `ShiftLocalG`.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutCheckW

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

section
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

def StepsIMW (w : List (Fin 2)) (k : ℕ) (x y : State GalilVM) : Prop :=
  PackedRun (galilFrameS (PofC centre place entry w) q first) 2048 (SoundScanNR w)
    (IPackMW centre place entry q first w) k x y

theorem stepsIMW_trans {w : List (Fin 2)} {k1 k2 : ℕ} {x y z : State GalilVM}
    (h1 : StepsIMW centre place entry q first w k1 x y)
    (h2 : StepsIMW centre place entry q first w k2 y z) :
    StepsIMW centre place entry q first w (k1 + k2) x z :=
  PalPeg.PackedRun.trans h1 h2

theorem ipackMW_last_of_stepsIMW {w : List (Fin 2)} {k : ℕ} {x y : State GalilVM}
    (h : StepsIMW centre place entry q first w k x y) :
    IPackMW centre place entry q first w y := by
  obtain ⟨g, -, hgk, -, hp⟩ := h
  rw [← hgk]; exact hp k le_rfl


/-- `CloseoutPackRun30.PreTraceIMG` over `IPackMW`. -/
structure PreTraceIMW (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9) (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ) :
    Prop where
  base : PreTraceB centre place entry q first w st Tc
  packs : ∀ i, i ≤ Tc w.length → IPackMW centre place entry q first w (st i)

section
variable (I : List (Fin 2) → Control → GalilVM → Prop)
variable (R : List (Fin 2) → State GalilVM → State GalilVM → Prop)
-- What the oracle says, in addition, about the state of a report point (for instance that it
-- is a scan state).  The older lineage says nothing (`fun _ _ => True`).
variable (Y : List (Fin 2) → State GalilVM → Prop)

/-- `StepsIMW` with a tick predicate `R` (`PackedRunR`). -/
def StepsIMWR (w : List (Fin 2)) (k : ℕ) (x y : State GalilVM) : Prop :=
  PackedRunR (galilFrameS (PofC centre place entry w) q first) 2048 (SoundScanNR w)
    (IPackMW centre place entry q first w) (R w) k x y

theorem stepsIMWR_trans {w : List (Fin 2)} {k1 k2 : ℕ} {x y z : State GalilVM}
    (h1 : StepsIMWR centre place entry q first R w k1 x y)
    (h2 : StepsIMWR centre place entry q first R w k2 y z) :
    StepsIMWR centre place entry q first R w (k1 + k2) x z :=
  PalPeg.PackedRunR.trans h1 h2

theorem ipackMW_last_of_stepsIMWR {w : List (Fin 2)} {k : ℕ} {x y : State GalilVM}
    (h : StepsIMWR centre place entry q first R w k x y) :
    IPackMW centre place entry q first w y :=
  PalPeg.PackedRunR.pack_last h

/-- The instance at `R := True` is the old `StepsIMW`. -/
theorem stepsIMWR_true_of_stepsIMW {w : List (Fin 2)} {k : ℕ} {x y : State GalilVM}
    (h : StepsIMW centre place entry q first w k x y) :
    StepsIMWR centre place entry q first (fun _ _ _ => True) w k x y :=
  PalPeg.PackedRunR.ofPacked h

theorem stepsIMWR_true_of_stepsIMWR {w : List (Fin 2)} {k : ℕ} {x y : State GalilVM}
    (h : StepsIMWR centre place entry q first R w k x y) :
    StepsIMWR centre place entry q first (fun _ _ _ => True) w k x y :=
  PalPeg.PackedRunR.forget h

def ReachAtOn (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) : Prop :=
  ∃ (y : State GalilVM) (k : ℕ) (L : List Piece),
    StepsIMWR centre place entry q first R w k ⟨c, r⟩ y ∧
    CostedRun r y.vm k L ∧
    PalPeg.GalilReportPrefix.ReportPointAt w m y ∧
    Refreshed (PofC centre place entry w) q first y ∧
    Y w y ∧
    (m < w.length → ∃ (c' : Control) (r' : GalilVM) (k' : ℕ) (L' : List Piece),
      StepsIMWR centre place entry q first R w k' y ⟨c', r'⟩ ∧
      CostedRun y.vm r' k' L' ∧
      I w c' r' ∧ position r'.right ≤ 2 * (m+1) - 1)

/-- `CloseoutPackRun30.CycleOutIMG` over `StepsIMW`. -/
def CycleOutOn (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) : Prop :=
  ReachAtOn centre place entry q first I R Y w m c r ∨
    ∃ (cT : Control) (sT : GalilVM) (k : ℕ) (L : List Piece),
      StepsIMWR centre place entry q first R w k ⟨c, r⟩ ⟨cT, sT⟩ ∧
      CostedRun r sT k L ∧
      I w cT sT ∧ mu w sT < mu w r ∧
      position sT.right ≤ 2 * m - 1

/-- `CloseoutPackRun30.CycleOracleIMG` over `StepsIMW`. -/
def CycleOracleOn (w : List (Fin 2)) : Prop :=
  ∀ (m : ℕ) (c : Control) (r : GalilVM), 1 ≤ m → m ≤ w.length → I w c r →
    position r.right ≤ 2 * m - 1 → CycleOutOn centre place entry q first I R Y w m c r

theorem reachOn_fuel (w : List (Fin 2)) (hor : CycleOracleOn centre place entry q first I R Y w)
    (m : ℕ) (hm1 : 1 ≤ m) (hmle : m ≤ w.length) :
    ∀ (n : ℕ) (c : Control) (r : GalilVM), mu w r ≤ n → I w c r →
      position r.right ≤ 2 * m - 1 → ReachAtOn centre place entry q first I R Y w m c r := by
  intro n
  induction n with
  | zero =>
    intro c r hn hI hp
    rcases hor m c r hm1 hmle hI hp with hdone | ⟨cT, sT, k, L, _, _, _, hlt, _⟩
    · exact hdone
    · omega
  | succ n ih =>
    intro c r hn hI hp
    rcases hor m c r hm1 hmle hI hp with hdone | ⟨cT, sT, k, L, hst, hcr, hIT, hlt, hpT⟩
    · exact hdone
    · obtain ⟨y, k', L', hst', hcr', hrp, hfr, hreportFact, hcont⟩ := ih cT sT (by omega) hIT hpT
      exact ⟨y, k + k', L ++ L',
        stepsIMWR_trans centre place entry q first R hst hst',
        costedRun_trans hcr hcr', hrp, hfr, hreportFact, hcont⟩

theorem reachOn_from (w : List (Fin 2))
    (hor : CycleOracleOn centre place entry q first I R Y w)
    {m : ℕ} (hm1 : 1 ≤ m) (hmle : m ≤ w.length) {c : Control} {r : GalilVM}
    (hI : I w c r) (hp : position r.right ≤ 2 * m - 1) :
    ReachAtOn centre place entry q first I R Y w m c r :=
  reachOn_fuel centre place entry q first I R Y w hor m hm1 hmle _ c r le_rfl hI hp

/-- `CloseoutPackRun30.checkpoints_costIMG_upto1` over `IPackMG2` (verbatim). -/
theorem checkpoints_costOn_upto1 (w : List (Fin 2))
    (hor : CycleOracleOn centre place entry q first I R Y w)
    {x0 : State GalilVM} {k0 : ℕ} {c : Control} {r : GalilVM}
    (hpre : StepsIMWR centre place entry q first R w k0 x0 ⟨c, r⟩)
    (hI : I w c r) (hpos : position r.right = 1) :
    ∀ M, M ≤ w.length →
    ∃ (st : ℕ → State GalilVM) (Tc : ℕ → ℕ) (e : ℕ),
      st 0 = x0 ∧ Tc 0 = 0 ∧
      Trace (galilFrameS (PofC centre place entry w) q first) 2048 (SoundScanNR w) st e ∧
      (∀ i, i < e → R w (st i) (st (i+1))) ∧
      (∀ m, m < M → Tc m ≤ Tc (m+1)) ∧ Tc M ≤ e ∧
      (∀ m, 1 ≤ m → m ≤ M →
        PalPeg.GalilReportPrefix.ReportPointAt w m (st (Tc m)) ∧
        Refreshed (PofC centre place entry w) q first (st (Tc m)) ∧
        Y w (st (Tc m))) ∧
      (∀ m, 1 ≤ m → m < M →
        Tc (m+1) - Tc m ≤ alpha' 2048 * (Cw w (m+1) - Cw w m) + beta' 2048) ∧
      (M < w.length → ∃ (c' : Control) (r' : GalilVM),
        st e = ⟨c', r'⟩ ∧ I w c' r' ∧ position r'.right ≤ 2 * (M+1) - 1 ∧
        (1 ≤ M → ∃ L : List Piece, CostedRun (st (Tc M)).vm r' (e - Tc M) L)) ∧
      (M = 0 → e = k0 ∧ st e = ⟨c, r⟩) ∧
      (1 ≤ M → Tc 1 = k0) ∧
      (∀ i, i ≤ e → IPackMW centre place entry q first w (st i)) := by
  intro M
  induction M with
  | zero =>
    intro _
    obtain ⟨g, hg0, hgn, htr, hR, hgp⟩ := hpre
    refine ⟨g, fun _ => 0, k0, hg0, rfl, htr, hR, fun m hm => absurd hm (Nat.not_lt_zero _),
      Nat.zero_le _, fun m h1 h2 => absurd h1 (by omega), fun m h1 h2 => absurd h2 (by omega),
      fun _ => ⟨c, r, hgn, hI, by omega, fun h => absurd h (by omega)⟩,
      fun _ => ⟨rfl, hgn⟩, fun h => absurd h (by omega), hgp⟩
  | succ M ih =>
    intro hM
    obtain ⟨st, Tc, e, hst0, hTc0, htr, hcan, hmono, hTcM, hchk, hcost, hres, hzero, hone, hpk⟩ :=
      ih (by omega)
    obtain ⟨c', r', hste, hI', hp', hpend⟩ := hres (by omega)
    obtain ⟨y, k, L2, hrun, hcr, hrp, hfr, hreportFact, hcont⟩ :=
      reachOn_from centre place entry q first I R Y w hor (m := M+1) (by omega) hM hI' hp'
    have hk0 : M = 0 → k = 0 ∧ e = k0 := by
      intro hM0
      subst hM0
      obtain ⟨he, hse⟩ := hzero rfl
      have hrr : r' = r := by
        have := hste.symm.trans hse
        exact (GalilScaffoldTop.State.mk.injEq _ _ _ _ ▸ this).2
      subst hrr
      have hyp := hrp.atPlace
      exact ⟨costedRun_zero hcr (by rw [hyp, hpos]), he⟩
    obtain ⟨g1, hg10, hg1k, htr1, hR1, hpg1⟩ := hrun
    have hj1 : st e = g1 0 := by rw [hste, hg10]
    set st1 := concat st g1 e with hst1
    have htr1' : Trace (galilFrameS (PofC centre place entry w) q first) 2048
        (SoundScanNR w) st1 (e + k) :=
      trace_concat htr htr1 hj1
    have hst1y : st1 (e + k) = y := by rw [hst1, concat_end st g1 hj1, hg1k]
    have hcan1 : ∀ i, i < e + k → R w (st1 i) (st1 (i+1)) := canon_concat hj1 hcan hR1
    have hpk1 : ∀ i, i ≤ e + k → IPackMW centre place entry q first w (st1 i) :=
      pack_concat hj1 hpk hpg1
    obtain ⟨st2, e2, htr2, hcan2, hagree, hle2, hres2, hpk2⟩ :
        ∃ (st2 : ℕ → State GalilVM) (e2 : ℕ),
          Trace (galilFrameS (PofC centre place entry w) q first) 2048 (SoundScanNR w) st2 e2 ∧
          (∀ i, i < e2 → R w (st2 i) (st2 (i+1))) ∧
          (∀ i, i ≤ e + k → st2 i = st1 i) ∧ e + k ≤ e2 ∧
          (M + 1 < w.length → ∃ (c'' : Control) (r'' : GalilVM),
            st2 e2 = ⟨c'', r''⟩ ∧ I w c'' r'' ∧
            position r''.right ≤ 2 * (M+1+1) - 1 ∧
            ∃ L : List Piece, CostedRun y.vm r'' (e2 - (e + k)) L) ∧
          (∀ i, i ≤ e2 → IPackMW centre place entry q first w (st2 i)) := by
      by_cases hlt : M + 1 < w.length
      · obtain ⟨c'', r'', k', L', hrun2, hcr2, hI2, hp2⟩ := hcont hlt
        obtain ⟨g2, hg20, hg2k, htr2, hR2, hpg2⟩ := hrun2
        have hj2 : st1 (e + k) = g2 0 := by rw [hst1y, hg20]
        refine ⟨concat st1 g2 (e + k), e + k + k', trace_concat htr1' htr2 hj2,
          canon_concat hj2 hcan1 hR2,
          fun i hi => concat_le st1 g2 hi, by omega, fun _ => ⟨c'', r'', ?_, hI2, hp2, L', ?_⟩,
          pack_concat hj2 hpk1 hpg2⟩
        · rw [concat_end st1 g2 hj2, hg2k]
        · rw [show e + k + k' - (e + k) = k' by omega]; exact hcr2
      · exact ⟨st1, e + k, htr1', hcan1, fun _ _ => rfl, le_rfl, fun h => absurd h hlt, hpk1⟩
    have hTcle : ∀ m, m ≤ M → Tc m ≤ e := fun m hm =>
      le_trans (mono_of_step Tc M hmono m M hm le_rfl) hTcM
    have hst2old : ∀ m, m ≤ M → st2 (Tc m) = st (Tc m) := by
      intro m hm
      rw [hagree _ (by have := hTcle m hm; omega), hst1, concat_le st g1 (hTcle m hm)]
    have hst2y : st2 (e + k) = y := by rw [hagree _ le_rfl, hst1y]
    refine ⟨st2, fun m => if m ≤ M then Tc m else e + k, e2, ?_, ?_, htr2, hcan2, ?_, ?_, ?_, ?_, ?_,
      fun h => absurd h (by omega), ?_, hpk2⟩
    · rw [hagree 0 (by omega), hst1, concat_le st g1 (Nat.zero_le _), hst0]
    · simp [hTc0]
    · intro m hm
      by_cases hm' : m + 1 ≤ M
      · simp only [hm', show m ≤ M by omega, if_true]; exact hmono m (by omega)
      · have hmM : m = M := by omega
        subst hmM
        simp only [le_refl, if_true, hm', if_false]
        exact le_trans hTcM (Nat.le_add_right _ _)
    · simp only [show ¬ M + 1 ≤ M by omega, if_false]; exact hle2
    · intro m h1 h2
      by_cases hm' : m ≤ M
      · simp only [hm', if_true]
        rw [hst2old m hm']
        exact hchk m h1 hm'
      · have hmM : m = M + 1 := by omega
        subst hmM
        simp only [hm', if_false]
        rw [hst2y]
        exact ⟨hrp, hfr, hreportFact⟩
    · intro m h1 h2
      by_cases hm' : m + 1 ≤ M
      · simp only [hm', show m ≤ M by omega, if_true]
        exact hcost m h1 (by omega)
      · have hmM : m = M := by omega
        subst hmM
        simp only [le_refl, if_true, hm', if_false]
        obtain ⟨L1, hcr1⟩ := hpend h1
        have hall := costedRun_trans hcr1 hcr
        have hTm := hTcle m le_rfl
        obtain ⟨hrp0, hfr0, _⟩ := hchk m h1 le_rfl
        have hc' : CostedRun (st (Tc m)).vm y.vm (e + k - Tc m) (L1 ++ L2) := by
          rw [show e + k - Tc m = e - Tc m + k by omega]; exact hall
        exact interval_cost_of_costedRun h1 hrp0 hfr0 hrp hfr hc'
    · intro hlt
      obtain ⟨c'', r'', h1, h2, h3, L, h4⟩ := hres2 hlt
      refine ⟨c'', r'', h1, h2, h3, fun _ => ⟨L, ?_⟩⟩
      simp only [show ¬ M + 1 ≤ M by omega, if_false]
      rw [hst2y]
      exact h4
    · intro _
      by_cases hM0 : M = 0
      · subst hM0
        obtain ⟨hk, he⟩ := hk0 rfl
        simp only [show ¬ (1 ≤ 0) by omega, if_false]
        omega
      · simp only [show 1 ≤ M by omega, if_true]
        exact hone (by omega)

/-- `H_bootIMW` with the carried predicate `I` at the boot landing. -/
def H_bootOn : Prop :=
  ∀ (a : Fin 2) (rest : List (Fin 2)),
    ∃ (c1 : Control) (t : GalilVM),
      StepsIMWR centre place entry q first R (a :: rest) 1
        ⟨GalilScaffoldController.initial 2048, GalilBootVM.initVM0 (a :: rest)⟩ ⟨c1, t⟩ ∧
      I (a :: rest) c1 t ∧ position t.right = 1

theorem preTraceOn_exists (hboot : H_bootOn centre place entry q first I R)
    (hor : ∀ w : List (Fin 2), 0 < w.length → CycleOracleOn centre place entry q first I R Y w) (w : List (Fin 2)) (hw : 0 < w.length) :
    ∃ st Tc, PreTraceIMW centre place entry q first w st Tc ∧
      (∀ i, i < Tc w.length → R w (st i) (st (i+1))) ∧
      ∀ m, 1 ≤ m → m ≤ w.length → Y w (st (Tc m)) := by
  rcases w with _ | ⟨a, rest⟩
  · simp at hw
  · obtain ⟨c1, t, hst, hI, hpos⟩ := hboot a rest
    obtain ⟨st, Tc, e, hst0, hTc0, htr, hcan, hmono, hTcM, hchk, hcost, -, -, hone, hpk⟩ :=
      checkpoints_costOn_upto1 centre place entry q first I R Y (a :: rest) (hor (a :: rest) hw)
        hst hI hpos (a :: rest).length le_rfl
    refine ⟨st, Tc, ⟨⟨⟨hst0, hTc0, trace_le htr hTcM, mono_of_step Tc _ hmono, ?_, hcost⟩,
      hone (by simp)⟩, fun i hi => hpk i (le_trans hi hTcM)⟩,
      fun i hi => hcan i (lt_of_lt_of_le hi hTcM), fun m h1 h2 => (hchk m h1 h2).2.2⟩
    intro m h1 h2
    exact ledgerAt_of_prefix (hchk m h1 h2).1 (hchk m h1 h2).2.1



end

/-! ## The `InvLPS` instance (the names the older closeout lineage uses) -/

def ReachAtIMW (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) : Prop :=
  ReachAtOn centre place entry q first
    (fun w c r => InvLPS (PofC centre place entry w) q first w c r) (fun _ _ _ => True)
    (fun _ _ => True) w m c r

def CycleOutIMW (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) : Prop :=
  CycleOutOn centre place entry q first
    (fun w c r => InvLPS (PofC centre place entry w) q first w c r) (fun _ _ _ => True)
    (fun _ _ => True) w m c r

def CycleOracleIMW (w : List (Fin 2)) : Prop :=
  CycleOracleOn centre place entry q first
    (fun w c r => InvLPS (PofC centre place entry w) q first w c r) (fun _ _ _ => True)
    (fun _ _ => True) w

/-- `CloseoutPackRun30.H_bootIMG` over `StepsIMW`. -/
def H_bootIMW : Prop :=
  H_bootOn centre place entry q first
    (fun w c r => InvLPS (PofC centre place entry w) q first w c r) (fun _ _ _ => True)

/-- `CloseoutPackRun30.H_oracleIMG` over `StepsIMW`. -/
def H_oracleIMW : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → CycleOracleIMW centre place entry q first w

theorem preTraceIMW_exists (hboot : H_bootIMW centre place entry q first)
    (hor : H_oracleIMW centre place entry q first) (w : List (Fin 2)) (hw : 0 < w.length) :
    ∃ st Tc, PreTraceIMW centre place entry q first w st Tc := by
  obtain ⟨st, Tc, h, -, -⟩ := preTraceOn_exists centre place entry q first
    (fun w c r => InvLPS (PofC centre place entry w) q first w c r) (fun _ _ _ => True)
    (fun _ _ => True) hboot hor w hw
  exact ⟨st, Tc, h⟩

/-! ## The run-shaped instance: scan states on a packed run out of an `InvLPS` origin

`InvLPS` (a restart state, or a replay scan state) has an *idle* chain.  The chain goes idle
only at a fallback or at a restart out of a broken chain (`ScaffoldGalil.scala:233,320`), so on
an input such as `aaaa…` the chain born at the first found comparison lives across every later
report point and no `InvLPS` state recurs.  An oracle whose report continuation lands in
`InvLPS` before the next report point (`ReachAtIMW`) therefore cannot be met there.  The
carried predicate below keeps the origin and lets the state itself be any non-replaying scan
state of the packed run out of it. -/

/-- **The oracle's runs are canonical** (`GalilTickFair.Canonical`): a broken chain whose guard
is up is restarted first, the fallback place is the right head, the cursor is kept at
`init`／`replayStart`.  `Tick ∧ Canonical` is functional, so a canonical pre-loaded trace is
*the* trace of the deterministic machine.  The packed path also records where a fresh search
re-enters (`ShapedRun.OracleTick`). -/
abbrev StepsIMWC (w : List (Fin 2)) (k : ℕ) (x y : State GalilVM) : Prop :=
  StepsIMWR centre place entry q first (PalPeg.ShapedRun.OracleTick entry) w k x y

theorem stepsIMWC_trans {w : List (Fin 2)} {k1 k2 : ℕ} {x y z : State GalilVM}
    (h1 : StepsIMWC centre place entry q first w k1 x y)
    (h2 : StepsIMWC centre place entry q first w k2 y z) :
    StepsIMWC centre place entry q first w (k1 + k2) x z :=
  stepsIMWR_trans centre place entry q first _ h1 h2

theorem ipackMW_last_of_stepsIMWC {w : List (Fin 2)} {k : ℕ} {x y : State GalilVM}
    (h : StepsIMWC centre place entry q first w k x y) :
    IPackMW centre place entry q first w y :=
  ipackMW_last_of_stepsIMWR centre place entry q first _ h

/-- A canonical trace: every tick up to the last report point is `Canonical`. -/
abbrev CanonTrace (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ) : Prop :=
  ∀ i, i < Tc w.length → PalPeg.GalilTickFair.Canonical entry 2048 (st i) (st (i+1))

/-- A finite canonical packed prefix from the actual boot state. -/
def PackedFromBoot (w : List (Fin 2)) (x : State GalilVM) : Prop :=
  ∃ k, StepsIMWC centre place entry q first w k (boot w) x

/-- A non-replaying scan state on a packed sound run out of an `InvLPS` origin
that is itself reached from boot.  The final consumer needs no arbitrary origin. -/
def ScanOnPackedRunFromInvLPS (w : List (Fin 2)) (c : Control) (r : GalilVM) : Prop :=
  ScanNR ⟨c, r⟩ ∧ Refreshed (PofC centre place entry w) q first ⟨c, r⟩ ∧
  PalPeg.GalilScaffoldChainInputSupply.MInv w c r ∧
  ¬ PalPeg.GalilScaffoldChainInputSupply.restartGuardVM r ∧
  ∃ (c₀ : Control) (r₀ : GalilVM) (j : ℕ),
    InvLPS (PofC centre place entry w) q first w c₀ r₀ ∧
    PackedFromBoot centre place entry q first w ⟨c₀, r₀⟩ ∧
    StepsIMWC centre place entry q first w j ⟨c₀, r₀⟩ ⟨c, r⟩ ∧
    ∃ j' : ℕ, PalPeg.ShapedRun.ShapedSteps centre place entry q first w j' ⟨c₀, r₀⟩ ⟨c, r⟩

/-- **What the oracle says about a report point**: it is a scan state, and it carries the
invariant of the packed run itself.  The consumer of the last report point runs on from it
(the ticks after the last letter), so the invariant is handed out at every report point, not
only below the last one. -/
def ReportOnPackedRun (w : List (Fin 2)) (y : State GalilVM) : Prop :=
  y.ctl.mode = Mode.scan ∧ ScanOnPackedRunFromInvLPS centre place entry q first w y.ctl y.vm

/-- An `InvLPS` state carrying its pack is on the packed run out of itself. -/
theorem scanOnPackedRunFromInvLPS_of_invLPS {w : List (Fin 2)} {c : Control} {r : GalilVM}
    (hI : InvLPS (PofC centre place entry w) q first w c r)
    (hf : Refreshed (PofC centre place entry w) q first ⟨c, r⟩)
    (hp : IPackMW centre place entry q first w ⟨c, r⟩)
    (hBoot : PackedFromBoot centre place entry q first w ⟨c, r⟩) :
    ScanOnPackedRunFromInvLPS centre place entry q first w c r := by
  have hmode := invS_mode hI.1.1.1.1.1
  have hminv : PalPeg.GalilScaffoldChainInputSupply.MInv w c r := by
    rcases hI.1.1.1.1.1 with h | ⟨k, h⟩ <;> exact h.minv
  have hidle : r.chain = .idle := by
    rcases hI.1.1.1.1.1 with h | ⟨k, h⟩
    · obtain ⟨Rad', last, hR⟩ := h.rest
      exact hR.1
    · exact h.chainIdle
  have hng : ¬ PalPeg.GalilScaffoldChainInputSupply.restartGuardVM r := by
    rintro ⟨w', hw', -⟩
    rw [hidle] at hw'; cases hw'
  refine ⟨⟨hmode.1, hmode.2⟩, hf, hminv, hng, c, r, 0, hI, hBoot, ⟨fun _ => ⟨c, r⟩, rfl, rfl, ?_,
    fun i hi => absurd hi (Nat.not_lt_zero _), fun _ _ => hp⟩, 0, .zero _⟩
  exact ⟨fun i hi => absurd hi (Nat.not_lt_zero _), fun _ _ _ _ => hI.1.1.1.1.2⟩

/-- The boot landing as `CloseoutOracleW` produces it: an `InvLPS` state whose output was
just refreshed by the `init` tick. -/
def H_bootRefreshedIMW : Prop :=
  H_bootOn centre place entry q first
    (fun w c r => InvLPS (PofC centre place entry w) q first w c r ∧
      Refreshed (PofC centre place entry w) q first ⟨c, r⟩)
    (PalPeg.ShapedRun.OracleTick entry)

/-- **The pre-loaded trace from the run-shaped oracle.** -/
theorem preTraceOnPackedRun_exists (hboot : H_bootRefreshedIMW centre place entry q first)
    (hor : ∀ w : List (Fin 2), 0 < w.length →
      CycleOracleOn centre place entry q first (ScanOnPackedRunFromInvLPS centre place entry q first)
        (PalPeg.ShapedRun.OracleTick entry) (ReportOnPackedRun centre place entry q first) w)
    (w : List (Fin 2)) (hw : 0 < w.length) :
    ∃ st Tc, PreTraceIMW centre place entry q first w st Tc ∧ CanonTrace entry w st Tc ∧
      (∀ m, 1 ≤ m → m ≤ w.length → (st (Tc m)).ctl.mode = Mode.scan) ∧
      ∀ m, 1 ≤ m → m ≤ w.length →
        ScanOnPackedRunFromInvLPS centre place entry q first w (st (Tc m)).ctl (st (Tc m)).vm := by
  obtain ⟨st, Tc, hpre, hticks, hscan⟩ := preTraceOn_exists centre place entry q first _ _ _
    (fun a rest => by
      obtain ⟨c1, t, hst, ⟨hI, hf⟩, hpos⟩ := hboot a rest
      exact ⟨c1, t, hst, scanOnPackedRunFromInvLPS_of_invLPS centre place entry q first hI hf
        (ipackMW_last_of_stepsIMWC centre place entry q first hst) ⟨1, hst⟩, hpos⟩)
    hor w hw
  exact ⟨st, Tc, hpre, fun i hi => (hticks i hi).canonical,
    fun m hm1 hmle => (hscan m hm1 hmle).1, fun m hm1 hmle => (hscan m hm1 hmle).2⟩

#print axioms checkpoints_costOn_upto1
#print axioms preTraceOnPackedRun_exists
#print axioms preTraceIMW_exists
#print axioms preTraceOnPackedRun_exists

end

end PalPeg.CloseoutCheckW
