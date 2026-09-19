import PalPeg.PackedRun
import PalPeg.CloseoutPackW
import PalPeg.CloseoutStageCheck

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

def ReachAtOn (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) : Prop :=
  ∃ (y : State GalilVM) (k : ℕ) (L : List Piece),
    StepsIMW centre place entry q first w k ⟨c, r⟩ y ∧
    CostedRun r y.vm k L ∧
    PalPeg.GalilReportPrefix.ReportPointAt w m y ∧
    Refreshed (PofC centre place entry w) q first y ∧
    (m < w.length → ∃ (c' : Control) (r' : GalilVM) (k' : ℕ) (L' : List Piece),
      StepsIMW centre place entry q first w k' y ⟨c', r'⟩ ∧
      CostedRun y.vm r' k' L' ∧
      I w c' r' ∧ position r'.right ≤ 2 * (m+1) - 1)

/-- `CloseoutPackRun30.CycleOutIMG` over `StepsIMW`. -/
def CycleOutOn (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) : Prop :=
  ReachAtOn centre place entry q first I w m c r ∨
    ∃ (cT : Control) (sT : GalilVM) (k : ℕ) (L : List Piece),
      StepsIMW centre place entry q first w k ⟨c, r⟩ ⟨cT, sT⟩ ∧
      CostedRun r sT k L ∧
      I w cT sT ∧ mu w sT < mu w r ∧
      position sT.right ≤ 2 * m - 1

/-- `CloseoutPackRun30.CycleOracleIMG` over `StepsIMW`. -/
def CycleOracleOn (w : List (Fin 2)) : Prop :=
  ∀ (m : ℕ) (c : Control) (r : GalilVM), 1 ≤ m → m ≤ w.length → I w c r →
    position r.right ≤ 2 * m - 1 → CycleOutOn centre place entry q first I w m c r

theorem reachOn_fuel (w : List (Fin 2)) (hor : CycleOracleOn centre place entry q first I w)
    (m : ℕ) (hm1 : 1 ≤ m) (hmle : m ≤ w.length) :
    ∀ (n : ℕ) (c : Control) (r : GalilVM), mu w r ≤ n → I w c r →
      position r.right ≤ 2 * m - 1 → ReachAtOn centre place entry q first I w m c r := by
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
    · obtain ⟨y, k', L', hst', hcr', hrp, hfr, hcont⟩ := ih cT sT (by omega) hIT hpT
      exact ⟨y, k + k', L ++ L',
        stepsIMW_trans centre place entry q first hst hst',
        costedRun_trans hcr hcr', hrp, hfr, hcont⟩

theorem reachOn_from (w : List (Fin 2))
    (hor : CycleOracleOn centre place entry q first I w)
    {m : ℕ} (hm1 : 1 ≤ m) (hmle : m ≤ w.length) {c : Control} {r : GalilVM}
    (hI : I w c r) (hp : position r.right ≤ 2 * m - 1) :
    ReachAtOn centre place entry q first I w m c r :=
  reachOn_fuel centre place entry q first I w hor m hm1 hmle _ c r le_rfl hI hp

/-- `CloseoutPackRun30.checkpoints_costIMG_upto1` over `IPackMG2` (verbatim). -/
theorem checkpoints_costOn_upto1 (w : List (Fin 2))
    (hor : CycleOracleOn centre place entry q first I w)
    {x0 : State GalilVM} {k0 : ℕ} {c : Control} {r : GalilVM}
    (hpre : StepsIMW centre place entry q first w k0 x0 ⟨c, r⟩)
    (hI : I w c r) (hpos : position r.right = 1) :
    ∀ M, M ≤ w.length →
    ∃ (st : ℕ → State GalilVM) (Tc : ℕ → ℕ) (e : ℕ),
      st 0 = x0 ∧ Tc 0 = 0 ∧
      Trace (galilFrameS (PofC centre place entry w) q first) 2048 (SoundScanNR w) st e ∧
      (∀ m, m < M → Tc m ≤ Tc (m+1)) ∧ Tc M ≤ e ∧
      (∀ m, 1 ≤ m → m ≤ M →
        PalPeg.GalilReportPrefix.ReportPointAt w m (st (Tc m)) ∧
        Refreshed (PofC centre place entry w) q first (st (Tc m))) ∧
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
    obtain ⟨g, hg0, hgn, htr, hgp⟩ := hpre
    refine ⟨g, fun _ => 0, k0, hg0, rfl, htr, fun m hm => absurd hm (Nat.not_lt_zero _),
      Nat.zero_le _, fun m h1 h2 => absurd h1 (by omega), fun m h1 h2 => absurd h2 (by omega),
      fun _ => ⟨c, r, hgn, hI, by omega, fun h => absurd h (by omega)⟩,
      fun _ => ⟨rfl, hgn⟩, fun h => absurd h (by omega), hgp⟩
  | succ M ih =>
    intro hM
    obtain ⟨st, Tc, e, hst0, hTc0, htr, hmono, hTcM, hchk, hcost, hres, hzero, hone, hpk⟩ :=
      ih (by omega)
    obtain ⟨c', r', hste, hI', hp', hpend⟩ := hres (by omega)
    obtain ⟨y, k, L2, hrun, hcr, hrp, hfr, hcont⟩ :=
      reachOn_from centre place entry q first I w hor (m := M+1) (by omega) hM hI' hp'
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
    obtain ⟨g1, hg10, hg1k, htr1, hpg1⟩ := hrun
    have hj1 : st e = g1 0 := by rw [hste, hg10]
    set st1 := concat st g1 e with hst1
    have htr1' : Trace (galilFrameS (PofC centre place entry w) q first) 2048
        (SoundScanNR w) st1 (e + k) :=
      trace_concat htr htr1 hj1
    have hst1y : st1 (e + k) = y := by rw [hst1, concat_end st g1 hj1, hg1k]
    have hpk1 : ∀ i, i ≤ e + k → IPackMW centre place entry q first w (st1 i) :=
      pack_concat hj1 hpk hpg1
    obtain ⟨st2, e2, htr2, hagree, hle2, hres2, hpk2⟩ :
        ∃ (st2 : ℕ → State GalilVM) (e2 : ℕ),
          Trace (galilFrameS (PofC centre place entry w) q first) 2048 (SoundScanNR w) st2 e2 ∧
          (∀ i, i ≤ e + k → st2 i = st1 i) ∧ e + k ≤ e2 ∧
          (M + 1 < w.length → ∃ (c'' : Control) (r'' : GalilVM),
            st2 e2 = ⟨c'', r''⟩ ∧ I w c'' r'' ∧
            position r''.right ≤ 2 * (M+1+1) - 1 ∧
            ∃ L : List Piece, CostedRun y.vm r'' (e2 - (e + k)) L) ∧
          (∀ i, i ≤ e2 → IPackMW centre place entry q first w (st2 i)) := by
      by_cases hlt : M + 1 < w.length
      · obtain ⟨c'', r'', k', L', hrun2, hcr2, hI2, hp2⟩ := hcont hlt
        obtain ⟨g2, hg20, hg2k, htr2, hpg2⟩ := hrun2
        have hj2 : st1 (e + k) = g2 0 := by rw [hst1y, hg20]
        refine ⟨concat st1 g2 (e + k), e + k + k', trace_concat htr1' htr2 hj2,
          fun i hi => concat_le st1 g2 hi, by omega, fun _ => ⟨c'', r'', ?_, hI2, hp2, L', ?_⟩,
          pack_concat hj2 hpk1 hpg2⟩
        · rw [concat_end st1 g2 hj2, hg2k]
        · rw [show e + k + k' - (e + k) = k' by omega]; exact hcr2
      · exact ⟨st1, e + k, htr1', fun _ _ => rfl, le_rfl, fun h => absurd h hlt, hpk1⟩
    have hTcle : ∀ m, m ≤ M → Tc m ≤ e := fun m hm =>
      le_trans (mono_of_step Tc M hmono m M hm le_rfl) hTcM
    have hst2old : ∀ m, m ≤ M → st2 (Tc m) = st (Tc m) := by
      intro m hm
      rw [hagree _ (by have := hTcle m hm; omega), hst1, concat_le st g1 (hTcle m hm)]
    have hst2y : st2 (e + k) = y := by rw [hagree _ le_rfl, hst1y]
    refine ⟨st2, fun m => if m ≤ M then Tc m else e + k, e2, ?_, ?_, htr2, ?_, ?_, ?_, ?_, ?_,
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
        exact ⟨hrp, hfr⟩
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
        obtain ⟨hrp0, hfr0⟩ := hchk m h1 le_rfl
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
      StepsIMW centre place entry q first (a :: rest) 1
        ⟨GalilScaffoldController.initial 2048, GalilBootVM.initVM0 (a :: rest)⟩ ⟨c1, t⟩ ∧
      I (a :: rest) c1 t ∧ position t.right = 1

theorem preTraceOn_exists (hboot : H_bootOn centre place entry q first I)
    (hor : ∀ w : List (Fin 2), 0 < w.length → CycleOracleOn centre place entry q first I w) (w : List (Fin 2)) (hw : 0 < w.length) :
    ∃ st Tc, PreTraceIMW centre place entry q first w st Tc := by
  rcases w with _ | ⟨a, rest⟩
  · simp at hw
  · obtain ⟨c1, t, hst, hI, hpos⟩ := hboot a rest
    obtain ⟨st, Tc, e, hst0, hTc0, htr, hmono, hTcM, hchk, hcost, -, -, hone, hpk⟩ :=
      checkpoints_costOn_upto1 centre place entry q first I (a :: rest) (hor (a :: rest) hw)
        hst hI hpos (a :: rest).length le_rfl
    refine ⟨st, Tc, ⟨⟨⟨hst0, hTc0, trace_le htr hTcM, mono_of_step Tc _ hmono, ?_, hcost⟩,
      hone (by simp)⟩, fun i hi => hpk i (le_trans hi hTcM)⟩⟩
    intro m h1 h2
    exact ledgerAt_of_prefix (hchk m h1 h2).1 (hchk m h1 h2).2



end

/-! ## The `InvLPS` instance (the names the older closeout lineage uses) -/

def ReachAtIMW (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) : Prop :=
  ReachAtOn centre place entry q first
    (fun w c r => InvLPS (PofC centre place entry w) q first w c r) w m c r

def CycleOutIMW (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) : Prop :=
  CycleOutOn centre place entry q first
    (fun w c r => InvLPS (PofC centre place entry w) q first w c r) w m c r

def CycleOracleIMW (w : List (Fin 2)) : Prop :=
  CycleOracleOn centre place entry q first
    (fun w c r => InvLPS (PofC centre place entry w) q first w c r) w

/-- `CloseoutPackRun30.H_bootIMG` over `StepsIMW`. -/
def H_bootIMW : Prop :=
  H_bootOn centre place entry q first
    (fun w c r => InvLPS (PofC centre place entry w) q first w c r)

/-- `CloseoutPackRun30.H_oracleIMG` over `StepsIMW`. -/
def H_oracleIMW : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → CycleOracleIMW centre place entry q first w

theorem preTraceIMW_exists (hboot : H_bootIMW centre place entry q first)
    (hor : H_oracleIMW centre place entry q first) (w : List (Fin 2)) (hw : 0 < w.length) :
    ∃ st Tc, PreTraceIMW centre place entry q first w st Tc :=
  preTraceOn_exists centre place entry q first _ hboot hor w hw

/-! ## The run-shaped instance: scan states on a packed run out of an `InvLPS` origin

`InvLPS` (a restart state, or a replay scan state) has an *idle* chain.  The chain goes idle
only at a fallback or at a restart out of a broken chain (`ScaffoldGalil.scala:233,320`), so on
an input such as `aaaa…` the chain born at the first found comparison lives across every later
report point and no `InvLPS` state recurs.  An oracle whose report continuation lands in
`InvLPS` before the next report point (`ReachAtIMW`) therefore cannot be met there.  The
carried predicate below keeps the origin and lets the state itself be any non-replaying scan
state of the packed run out of it. -/

/-- A non-replaying scan state on a packed sound run out of an `InvLPS` origin. -/
def ScanOnPackedRunFromInvLPS (w : List (Fin 2)) (c : Control) (r : GalilVM) : Prop :=
  ScanNR ⟨c, r⟩ ∧ ∃ (c₀ : Control) (r₀ : GalilVM) (j : ℕ),
    InvLPS (PofC centre place entry w) q first w c₀ r₀ ∧
    StepsIMW centre place entry q first w j ⟨c₀, r₀⟩ ⟨c, r⟩

/-- An `InvLPS` state carrying its pack is on the packed run out of itself. -/
theorem scanOnPackedRunFromInvLPS_of_invLPS {w : List (Fin 2)} {c : Control} {r : GalilVM}
    (hI : InvLPS (PofC centre place entry w) q first w c r)
    (hp : IPackMW centre place entry q first w ⟨c, r⟩) :
    ScanOnPackedRunFromInvLPS centre place entry q first w c r := by
  have hmode := invS_mode hI.1.1.1.1.1
  refine ⟨⟨hmode.1, hmode.2⟩, c, r, 0, hI, fun _ => ⟨c, r⟩, rfl, rfl, ?_, fun _ _ => hp⟩
  exact ⟨fun i hi => absurd hi (Nat.not_lt_zero _), fun _ _ _ _ => hI.1.1.1.1.2⟩

/-- **The pre-loaded trace from the run-shaped oracle**, with the boot landing supplied
exactly as before (`H_bootIMW`). -/
theorem preTraceOnPackedRun_exists (hboot : H_bootIMW centre place entry q first)
    (hor : ∀ w : List (Fin 2), 0 < w.length →
      CycleOracleOn centre place entry q first (ScanOnPackedRunFromInvLPS centre place entry q first) w)
    (w : List (Fin 2)) (hw : 0 < w.length) :
    ∃ st Tc, PreTraceIMW centre place entry q first w st Tc :=
  preTraceOn_exists centre place entry q first _
    (fun a rest => by
      obtain ⟨c1, t, hst, hI, hpos⟩ := hboot a rest
      exact ⟨c1, t, hst, scanOnPackedRunFromInvLPS_of_invLPS centre place entry q first hI
        (ipackMW_last_of_stepsIMW centre place entry q first hst), hpos⟩)
    hor w hw

#print axioms checkpoints_costOn_upto1
#print axioms preTraceIMW_exists
#print axioms preTraceOnPackedRun_exists

end

end PalPeg.CloseoutCheckW
