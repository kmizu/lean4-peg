import PalPeg.CloseoutPackRun8

/-!
# `CloseoutPackRun9`: the `StepsI` family re-cut over `IPackO`, and `pal_in_peg_final12`

`CloseoutPackRun8` proved `packRunR_O` (a `PackRunR` producing runs packed with
`CloseoutPackRun7.IPackO`, i.e. the pack with the centre invariant deleted) and
recorded the obstruction to `pal_in_peg_final12`: every intermediate definition
between the oracle and the trail bridge mentions `CloseoutLPack5.IPack`
*positively*, so weakening the producer forces a re-cut of the whole family.

This file performs that re-cut.  `StepsIO` already exists in `CloseoutPackRun8`;
here come `ReachAtIO`, `CycleOutIO`, `CycleOracleIO`, `PreTraceIO`, `H_bootIO`,
`H_oracleIO`, `preTraceIO_exists` and `pal_in_peg_final5O`, each a transcript of
its `CloseoutLPack5` original with `IPack`/`StepsI` replaced throughout.  Nothing
in those scripts reads a pack field: the pack is only ever *carried* (through
`CloseoutLPack5.pack_concat`, which is already generic in the payload) and handed
to the trail bridge at the end — and there `CloseoutPackRun7.h_trailI_O` is
already stated over `IPackO` and **proved**, so the re-cut version of
`pal_in_peg_final5` loses the `H_trailI` hypothesis altogether.

§7 re-runs `CloseoutPackRun2`'s oracle bridge over `PackRunRO`, and §8 assembles
`pal_in_peg_final12`: `CloseoutPackRun5.pal_in_peg_final11` with `BigResid5G`
replaced by `CloseoutPackRun8.BigResid5O` (six contracts instead of seven, the
`MInv` halves of `rInitPack`/`rReplayPack` and the whole `rShiftDoneMinv` gone).

Standard axioms only.  Unconditional `PAL ∈ PEG` remains open: the residual is
the six `BigResid5O` contracts, the two `Extra` obligations, `H_shiftLocalC`,
`H_stageScan`, `CycleOracleMC3`, `H_bootShift`, `H_landShift` and
`H_realizeLI'`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPackRun9

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
open PalPeg.CloseoutOracleI PalPeg.CloseoutOracleI2 PalPeg.GalilInvPlus3
open PalPeg.CloseoutPackRun PalPeg.CloseoutPackRun2 PalPeg.CloseoutPackRun3
open PalPeg.CloseoutPackRun5 PalPeg.CloseoutPackRun7 PalPeg.CloseoutPackRun8
open GalilScaffoldInputHead GalilScaffoldCounter GalilScaffoldChainVerifier

/-! ## 1. `StepsIO` transport -/

section Trans
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- `CloseoutLPack5.stepsI_trans` over the `MInv`-free payload. -/
theorem stepsIO_trans {w : List (Fin 2)} {k1 k2 : ℕ} {x y z : State GalilVM}
    (h1 : StepsIO centre place entry q first w k1 x y)
    (h2 : StepsIO centre place entry q first w k2 y z) :
    StepsIO centre place entry q first w (k1 + k2) x z := by
  obtain ⟨g1, hg10, hg1k, htr1, hp1⟩ := h1
  obtain ⟨g2, hg20, hg2k, htr2, hp2⟩ := h2
  have hj : g1 k1 = g2 0 := by rw [hg1k, hg20]
  refine ⟨concat g1 g2 k1, ?_, ?_, trace_concat htr1 htr2 hj,
    pack_concat hj hp1 hp2⟩
  · rw [concat_le g1 g2 (Nat.zero_le _)]; exact hg10
  · rw [concat_end g1 g2 hj]; exact hg2k

/-- `CloseoutOracleI2.ipack_last_of_stepsI` over the `MInv`-free payload. -/
theorem ipackO_last_of_stepsIO {w : List (Fin 2)} {k : ℕ} {x y : State GalilVM}
    (h : StepsIO centre place entry q first w k x y) :
    IPackO centre place entry q first w y := by
  obtain ⟨g, -, hgk, -, hp⟩ := h
  rw [← hgk]; exact hp k le_rfl

end Trans

#print axioms stepsIO_trans
#print axioms ipackO_last_of_stepsIO

/-! ## 2. `ReachAtIO`, `CycleOutIO`, `CycleOracleIO` -/

section Recursion
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- `CloseoutLPack5.ReachAtI` over `StepsIO`. -/
def ReachAtIO (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) : Prop :=
  ∃ (y : State GalilVM) (k : ℕ) (L : List Piece),
    StepsIO centre place entry q first w k ⟨c, r⟩ y ∧
    CostedRun r y.vm k L ∧
    PalPeg.GalilReportPrefix.ReportPointAt w m y ∧
    Refreshed (PofC centre place entry w) q first y ∧
    (m < w.length → ∃ (c' : Control) (r' : GalilVM) (k' : ℕ) (L' : List Piece),
      StepsIO centre place entry q first w k' y ⟨c', r'⟩ ∧
      CostedRun y.vm r' k' L' ∧
      InvLPC w c' r' ∧ position r'.right ≤ 2 * (m+1) - 1)

/-- `CloseoutLPack5.CycleOutI` over `StepsIO`. -/
def CycleOutIO (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) : Prop :=
  ReachAtIO centre place entry q first w m c r ∨
    ∃ (cT : Control) (sT : GalilVM) (k : ℕ) (L : List Piece),
      StepsIO centre place entry q first w k ⟨c, r⟩ ⟨cT, sT⟩ ∧
      CostedRun r sT k L ∧
      InvLPC w cT sT ∧ mu w sT < mu w r ∧
      position sT.right ≤ 2 * m - 1

/-- `CloseoutLPack5.CycleOracleI` over `StepsIO`. -/
def CycleOracleIO (w : List (Fin 2)) : Prop :=
  ∀ (m : ℕ) (c : Control) (r : GalilVM), 1 ≤ m → m ≤ w.length → InvLPC w c r →
    position r.right ≤ 2 * m - 1 → CycleOutIO centre place entry q first w m c r

/-- `CloseoutLPack5.reachI_fuel` over `StepsIO`. -/
theorem reachIO_fuel (w : List (Fin 2)) (hor : CycleOracleIO centre place entry q first w)
    (m : ℕ) (hm1 : 1 ≤ m) (hmle : m ≤ w.length) :
    ∀ (n : ℕ) (c : Control) (r : GalilVM), mu w r ≤ n → InvLPC w c r →
      position r.right ≤ 2 * m - 1 → ReachAtIO centre place entry q first w m c r := by
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
        stepsIO_trans centre place entry q first hst hst',
        costedRun_trans hcr hcr', hrp, hfr, hcont⟩

theorem reachIO_from_invLPC (w : List (Fin 2))
    (hor : CycleOracleIO centre place entry q first w)
    {m : ℕ} (hm1 : 1 ≤ m) (hmle : m ≤ w.length) {c : Control} {r : GalilVM}
    (hI : InvLPC w c r) (hp : position r.right ≤ 2 * m - 1) :
    ReachAtIO centre place entry q first w m c r :=
  reachIO_fuel centre place entry q first w hor m hm1 hmle _ c r le_rfl hI hp

end Recursion

#print axioms reachIO_fuel
#print axioms reachIO_from_invLPC

/-! ## 3. The checkpoint construction over `StepsIO` -/

section Construct
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- `CloseoutLPack5.checkpoints_costI_upto1` over the `MInv`-free payload. -/
theorem checkpoints_costIO_upto1 (w : List (Fin 2))
    (hor : CycleOracleIO centre place entry q first w)
    {x0 : State GalilVM} {k0 : ℕ} {c : Control} {r : GalilVM}
    (hpre : StepsIO centre place entry q first w k0 x0 ⟨c, r⟩)
    (hI : InvLPC w c r) (hpos : position r.right = 1) :
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
        st e = ⟨c', r'⟩ ∧ InvLPC w c' r' ∧ position r'.right ≤ 2 * (M+1) - 1 ∧
        (1 ≤ M → ∃ L : List Piece, CostedRun (st (Tc M)).vm r' (e - Tc M) L)) ∧
      (M = 0 → e = k0 ∧ st e = ⟨c, r⟩) ∧
      (1 ≤ M → Tc 1 = k0) ∧
      (∀ i, i ≤ e → IPackO centre place entry q first w (st i)) := by
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
      reachIO_from_invLPC centre place entry q first w hor (m := M+1) (by omega) hM hI' hp'
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
    have hpk1 : ∀ i, i ≤ e + k → IPackO centre place entry q first w (st1 i) :=
      pack_concat hj1 hpk hpg1
    obtain ⟨st2, e2, htr2, hagree, hle2, hres2, hpk2⟩ :
        ∃ (st2 : ℕ → State GalilVM) (e2 : ℕ),
          Trace (galilFrameS (PofC centre place entry w) q first) 2048 (SoundScanNR w) st2 e2 ∧
          (∀ i, i ≤ e + k → st2 i = st1 i) ∧ e + k ≤ e2 ∧
          (M + 1 < w.length → ∃ (c'' : Control) (r'' : GalilVM),
            st2 e2 = ⟨c'', r''⟩ ∧ InvLPC w c'' r'' ∧
            position r''.right ≤ 2 * (M+1+1) - 1 ∧
            ∃ L : List Piece, CostedRun y.vm r'' (e2 - (e + k)) L) ∧
          (∀ i, i ≤ e2 → IPackO centre place entry q first w (st2 i)) := by
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

end Construct

#print axioms checkpoints_costIO_upto1

/-! ## 4. `PreTraceIO` -/

section Pre
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- `CloseoutLPack5.PreTraceI` over the `MInv`-free payload. -/
structure PreTraceIO (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ) : Prop where
  base : PreTraceB centre place entry q first w st Tc
  packs : ∀ i, i ≤ Tc w.length → IPackO centre place entry q first w (st i)

/-- `CloseoutLPack5.H_bootI` over `StepsIO`. -/
def H_bootIO : Prop :=
  ∀ (a : Fin 2) (rest : List (Fin 2)),
    ∃ (c1 : Control) (t : GalilVM),
      StepsIO centre place entry q first (a :: rest) 1
        ⟨GalilScaffoldController.initial 2048, GalilBootVM.initVM0 (a :: rest)⟩ ⟨c1, t⟩ ∧
      InvLPC (a :: rest) c1 t ∧ position t.right = 1

/-- The boot prefix weakens: `H_bootI` is *stronger*, since `StepsI` occurs
positively in both. -/
theorem h_bootIO_of_h_bootI (h : H_bootI centre place entry q first) :
    H_bootIO centre place entry q first := by
  intro a rest
  obtain ⟨c1, t, hst, hI, hp⟩ := h a rest
  exact ⟨c1, t, stepsIO_of_stepsI centre place entry q first hst, hI, hp⟩

/-- `CloseoutLPack5.H_oracleI` over `StepsIO`. -/
def H_oracleIO : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → CycleOracleIO centre place entry q first w

/-- `CloseoutLPack5.preTraceI_exists` over the `MInv`-free payload. -/
theorem preTraceIO_exists (hboot : H_bootIO centre place entry q first)
    (hor : H_oracleIO centre place entry q first) (w : List (Fin 2)) (hw : 0 < w.length) :
    ∃ st Tc, PreTraceIO centre place entry q first w st Tc := by
  rcases w with _ | ⟨a, rest⟩
  · simp at hw
  · obtain ⟨c1, t, hst, hI, hpos⟩ := hboot a rest
    obtain ⟨st, Tc, e, hst0, hTc0, htr, hmono, hTcM, hchk, hcost, -, -, hone, hpk⟩ :=
      checkpoints_costIO_upto1 centre place entry q first (a :: rest) (hor (a :: rest) hw)
        hst hI hpos (a :: rest).length le_rfl
    refine ⟨st, Tc, ⟨⟨⟨hst0, hTc0, trace_le htr hTcM, mono_of_step Tc _ hmono, ?_, hcost⟩,
      hone (by simp)⟩, fun i hi => hpk i (le_trans hi hTcM)⟩⟩
    intro m h1 h2
    exact ledgerAt_of_prefix (hchk m h1 h2).1 (hchk m h1 h2).2

end Pre

#print axioms h_bootIO_of_h_bootI
#print axioms preTraceIO_exists

/-! ## 5. The need bound, with the trail bridge already proved -/

section Need
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- The refined need bound on a `PreTraceIO`.  Unlike `CloseoutLPack5.needI'_le`
this takes **no** trail hypothesis: `CloseoutPackRun7.h_trailI_O` is a theorem. -/
theorem needIO'_le {w : List (Fin 2)}
    (hw : 0 < w.length) {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hP : PreTraceIO centre place entry q first w st Tc) :
    ∀ m, m < w.length → ∀ i, i ≤ Tc (m+1) → needL' w st i ≤ m + 1 :=
  fun m hm i hi =>
    needL'_le_of_trailF w st m i
      (h_trailI_O centre place entry q first w hw st Tc hP.base.pre hP.packs m hm i hi)

end Need

#print axioms needIO'_le

/-! ## 6. `pal_in_peg_final5O` -/

/-- (C) over `PreTraceIO`. -/
def H_realizeLIO' (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9) : Prop :=
  ∃ (Q' Γ' : Type) (_ : Fintype Q') (_ : DecidableEq Q') (_ : Fintype Γ') (_ : DecidableEq Γ')
    (t K : ℕ) (L : PalPeg.Local.LocalStep (Fin 2) Q' Γ' t K) (blank : Γ') (initQ : Q')
    (outQ : Q' → Bool) (n : ℕ) (htape : 0 < t) (hn : 0 < n),
    ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTraceIO centre place entry q first w st Tc →
      ((L.realize blank initQ (GalilEmptyWord.accept' initQ outQ) n htape hn).SAccepts w ↔
        LatchTrue (PofC centre place entry w) q first w (stLG' τF w st (Tc w.length))
          ((w.length + 1) * τF))

/-- **`CloseoutLPack5.pal_in_peg_final5` over the `MInv`-free payload.**  The
`H_trailI` hypothesis is gone: `CloseoutPackRun7.h_trailI_O` discharges it. -/
theorem pal_in_peg_final5O (entry q : ℕ) (first : Fin 9)
    (hboot : H_bootIO centreC placeC entry q first)
    (hA : H_oracleIO centreC placeC entry q first)
    (hC : H_realizeLIO' centreC placeC entry q first) :
    RecognizedByTotalPEG PAL := by
  classical
  obtain ⟨Q', Γ', iQ, dQ, iΓ, dΓ, t, K, L, blank, initQ, outQ, n, htape, hn, hreal⟩ := hC
  have key : ∀ w : List (Fin 2), ∃ (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      0 < w.length → PreTraceIO centreC placeC entry q first w st Tc := by
    intro w
    by_cases hw : 0 < w.length
    · obtain ⟨st, Tc, h⟩ := preTraceIO_exists centreC placeC entry q first hboot hA w hw
      exact ⟨st, Tc, fun _ => h⟩
    · exact ⟨fun _ => boot w, fun _ => 0, fun h => absurd h hw⟩
  choose stP TcP hP using key
  let M := L.realize blank initQ (GalilEmptyWord.accept' initQ outQ) n htape hn
  have hpre : ∀ w : List (Fin 2), 0 < w.length → PreloadL' w (stP w) (TcP w) := by
    intro w hw
    have h := hP w hw
    exact ⟨h.base.pre.tc0, fun m hm => h.base.pre.mono m (m+1) (by omega) hm,
      needL'_boot w (stP w) h.base.pre.start,
      needLe_of_pointwise' w (stP w) (TcP w) (needIO'_le centreC placeC entry q first hw h)⟩
  refine pal_in_peg_of_latch' (Nat.mul_pos hn (PalPeg.Local.cnt_pos K)) M
    (PofC centreC placeC entry) (fun _ => q) (fun _ => first) 2048
    (fun w => PofC_onLetter centreC placeC entry w)
    (fun w => PofC_leftFirst centreC placeC entry w)
    (fun w => stLG' τF w (stP w) (TcP w w.length))
    (fun w => arrLG' τF w (stP w) (TcP w w.length))
    (fun w => (w.length + 1) * τF) ?_ ?_ ?_ ?_
  · intro w hw
    have h := hP w hw
    exact abstractRun_throttledL'_2p18 w (stP w) (TcP w w.length)
      (PofC centreC placeC entry w) q first 2048
      (fun j => sharedC_trunc_vm w j centreC placeC entry (fun s => (centrePlaceC w j s).1)
        (fun s => (centrePlaceC w j s).2))
      (sharedC_suf w _ _ centreC placeC entry)
      (by rw [h.base.pre.start]; rfl) (needL'_boot w (stP w) h.base.pre.start)
      (by rw [h.base.pre.start]; exact sufVM_boot w) h.base.pre.trace.tick
  · intro w hw
    exact hreal w hw _ _ (hP w hw)
  · exact ledger_throttledL'_2p18 (PofC centreC placeC entry) (fun _ => q) (fun _ => first)
      stP TcP hpre (fun w hw => (hP w hw).base.pre.report w.length (by omega) le_rfl)
      (fun w hw => base_of_preTraceB (hP w hw).base)
      (fun w hw => (hP w hw).base.pre.cost)
  · exact GalilEmptyWord.realize_accept'_nil L blank initQ outQ n htape hn

#print axioms pal_in_peg_final5O

/-! ## 7. The oracle bridge over `PackRunRO` -/

section Bridge
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- `CloseoutPackRun2.reachAtI_of_reachAtC3R` over `PackRunRO`. -/
theorem reachAtIO_of_reachAtC3R {w : List (Fin 2)}
    (hpr : PackRunRO centre place entry q first w)
    {m : ℕ} {c : Control} {r : GalilVM} (hIC : InvLPC w c r)
    (hx : IPackO centre place entry q first w ⟨c, r⟩)
    (h : ReachAtC3 (PofC centre place entry w) q first w m c r) :
    ReachAtIO centre place entry q first w m c r := by
  obtain ⟨y, k, L, hst, hcr, hrp, hfr, hcont⟩ := h
  have hstI : StepsIO centre place entry q first w k ⟨c, r⟩ y :=
    hpr c r hIC 0 ⟨c, r⟩ (.zero _) k y hx hst
  refine ⟨y, k, L, hstI, hcr, hrp, hfr, fun hlt => ?_⟩
  obtain ⟨c', r', k', L', hst', hcr', hIS, hp⟩ := hcont hlt
  exact ⟨c', r', k', L',
    hpr c r hIC k y (stepsAll_steps hst) k' ⟨c', r'⟩
      (ipackO_last_of_stepsIO centre place entry q first hstI) hst',
    hcr', hIS.1, hp⟩

/-- `CloseoutPackRun2.cycleOutI_of_cycleOutMC3R` over `PackRunRO`. -/
theorem cycleOutIO_of_cycleOutMC3R {w : List (Fin 2)}
    (hpr : PackRunRO centre place entry q first w)
    {m : ℕ} {c : Control} {r : GalilVM} (hIC : InvLPC w c r)
    (hx : IPackO centre place entry q first w ⟨c, r⟩)
    (h : CycleOutMC3 (PofC centre place entry w) q first w m c r) :
    CycleOutIO centre place entry q first w m c r := by
  rcases h with hdone | ⟨cT, sT, k, L, hst, hcr, hIT, hlt, hpos⟩
  · exact Or.inl (reachAtIO_of_reachAtC3R centre place entry q first hpr hIC hx hdone)
  · exact Or.inr ⟨cT, sT, k, L, hpr c r hIC 0 ⟨c, r⟩ (.zero _) k ⟨cT, sT⟩ hx hst,
      hcr, hIT.1, hlt, hpos⟩

/-- `CloseoutPackRun2.cycleOracleI_of_cycleOracleMC3R` over `PackRunRO`. -/
theorem cycleOracleIO_of_cycleOracleMC3R {w : List (Fin 2)}
    (hpr : PackRunRO centre place entry q first w)
    (hsl : H_shiftLocalC centre place entry q first w)
    (hsc : H_stageScan centre place entry q first w)
    (hor : CycleOracleMC3 (PofC centre place entry w) q first w) :
    CycleOracleIO centre place entry q first w := by
  intro m c r hm1 hmle hIC hp
  exact cycleOutIO_of_cycleOutMC3R centre place entry q first hpr hIC
    (ipackO_of_ipack centre place entry q first
      (ipack_of_invLPC' centre place entry q first hsl (x := ⟨c, r⟩) hIC))
    (hor m c r hm1 hmle (hstage_of_scanBranch centre place entry q first hsc c r hIC) hp)

end Bridge

#print axioms reachAtIO_of_reachAtC3R
#print axioms cycleOutIO_of_cycleOutMC3R
#print axioms cycleOracleIO_of_cycleOracleMC3R

/-! ## 8. `pal_in_peg_final12` -/

/-- **`CloseoutPackRun5.pal_in_peg_final11` over the `MInv`-free residual.**
Seven contracts become six: `rShiftDoneMinv` is gone, and `rInitPack` /
`rReplayPack` keep only their head halves.  The boot prefix still comes from
`CloseoutOracleI.bootIPack_of_parts` (which produces the *stronger* `IPack` at
those two states) and is weakened by `h_bootIO_of_h_bootI`; the oracle comes from
`CloseoutPackRun8.packRunR_O` through §7; the trail bridge is discharged
outright inside `pal_in_peg_final5O`. -/
theorem pal_in_peg_final12 (entry q : ℕ) (first : Fin 9)
    (hr : ∀ w : List (Fin 2), BigResid5O centreC placeC entry q first w)
    (hee : ∀ w : List (Fin 2), H_extraEntry centreC placeC entry w)
    (het : ∀ w : List (Fin 2), H_extraTick centreC placeC entry q first w)
    (hsl : ∀ w : List (Fin 2), H_shiftLocalC centreC placeC entry q first w)
    (hsc : ∀ w : List (Fin 2), H_stageScan centreC placeC entry q first w)
    (hor : ∀ w : List (Fin 2), 0 < w.length →
      CycleOracleMC3 (PofC centreC placeC entry w) q first w)
    (hbs : H_bootShift centreC placeC entry q first)
    (hls : H_landShift centreC placeC entry q first)
    (hC : H_realizeLIO' centreC placeC entry q first) :
    RecognizedByTotalPEG PAL :=
  pal_in_peg_final5O entry q first
    (h_bootIO_of_h_bootI centreC placeC entry q first
      (h_bootI_of_bootIPack centreC placeC entry q first
        (bootIPack_of_parts centreC placeC entry q first h_lrepC hbs hls)))
    (fun w hw => cycleOracleIO_of_cycleOracleMC3R centreC placeC entry q first
      (packRunR_O centreC placeC entry q first (hr w) (hee w) (het w)) (hsl w) (hsc w)
      (hor w hw))
    hC

#print axioms pal_in_peg_final12

end PalPeg.CloseoutPackRun9
