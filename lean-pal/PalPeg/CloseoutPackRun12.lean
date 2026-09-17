import PalPeg.CloseoutPackRun9
import PalPeg.CloseoutPackRun11

/-!
# `CloseoutPackRun12`: the `StepsI` family over `IPackM`, and `pal_in_peg_final13`

`CloseoutPackRun11` closed the two defects that `CloseoutPackRun10` isolated —
the `scan_match` origin corner (`LTickLeavesN` has no `scanLeft`) and the
refuted `Extra.scanMargin` (`Extra'` has five fields) — and packaged them as
`BigResid6` / `bigPack2M_tick` over the mode-guarded pack
`CloseoutPackRun10.LPackM` / `IPackM`.  It stopped short of the final theorem
for exactly the reason `CloseoutPackRun8.§4` recorded: `CloseoutPackRun9`'s
whole `StepsIO` family mentions `IPackO` **positively**, so weakening the
producer to `IPackM` forces one more transcript.

This file is that transcript.  Every definition and script of
`CloseoutPackRun9` is repeated with

* `CloseoutPackRun8.StepsIO` → `StepsIM` (the same run predicate carrying
  `CloseoutPackRun10.IPackM`),
* `CloseoutPackRun7.IPackO` → `CloseoutPackRun10.IPackM`,
* `CloseoutPackRun8.BigResid5O` → `CloseoutPackRun11.BigResid6`,
* `CloseoutPackRun3.Extra` → `CloseoutPackRun11.Extra'`, and hence
  `H_extraEntry` / `H_extraTick` → `H_extraEntry'` / `H_extraTick'`.

Two places need more than a rename.

* §5 transcribes `CloseoutPackRun7.§5` (the trail bridge) over `IPackM`.  It
  goes through unchanged: `halfBound_of_ipackO` reads only `IPackO.shift` and
  the pack's `scanGeom`, both of which `IPackM` still has verbatim, and the
  `LeftLive` input is `CloseoutPackRun10.leftLive_ptM` in place of
  `leftLive_ptO`.  So `h_trailI_M` is a theorem and `needIM'_le` — like
  `CloseoutPackRun9.needIO'_le` — takes no trail hypothesis.
* §7 replaces `CloseoutPackRun8.packRunR_O` by `packRunR_M`, built from
  `CloseoutPackRun11.bigPack2M_tick` and the `Extra'` transport `extra'_steps`.

## Honest status

Standard axioms only.  Unconditional `PAL ∈ PEG` remains **open**:
`pal_in_peg_final13` is `CloseoutPackRun9.pal_in_peg_final12` with a strictly
smaller residual — the refuted `scanMargin` field and the unguarded `scanLeft`
leaf are gone — but the residual is still

`BigResid6` (six contracts: `rInitPackM`, `rScanInvR`, `rShiftDoneScan`,
`rChoosePackL`, `rReplayPackM`, `rShiftNext`), `H_extraEntry'`, `H_extraTick'`
(whose `Extra'.rewindMargin` is the surviving corner), `H_shiftLocalC`,
`H_stageScan`, `CycleOracleMC3`, `H_bootShift`, `H_landShift`, `H_realizeLIM'`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPackRun12

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
open GalilScaffoldInputHead GalilScaffoldCounter GalilScaffoldChainVerifier

/-! ## 0. `StepsIM` -/

section RunM
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- `CloseoutPackRun8.StepsIO` carrying `IPackM` instead of `IPackO`. -/
def StepsIM (w : List (Fin 2)) (k : ℕ) (x y : State GalilVM) : Prop :=
  ∃ g : ℕ → State GalilVM, g 0 = x ∧ g k = y ∧
    Trace (galilFrameS (PofC centre place entry w) q first) 2048 (SoundScanNR w) g k ∧
    ∀ i, i ≤ k → IPackM centre place entry q first w (g i)

/-- An `MInv`-free packed run is a mode-guarded packed run. -/
theorem stepsIM_of_stepsIO {w : List (Fin 2)} {k : ℕ} {x y : State GalilVM}
    (h : StepsIO centre place entry q first w k x y) :
    StepsIM centre place entry q first w k x y := by
  obtain ⟨g, h0, hk, htr, hp⟩ := h
  exact ⟨g, h0, hk, htr, fun i hi => ipackM_of_ipackO centre place entry q first (hp i hi)⟩

end RunM

#print axioms stepsIM_of_stepsIO

/-! ## 1. `StepsIM` transport -/

section Trans
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- `CloseoutPackRun9.stepsIO_trans` over the guarded payload. -/
theorem stepsIM_trans {w : List (Fin 2)} {k1 k2 : ℕ} {x y z : State GalilVM}
    (h1 : StepsIM centre place entry q first w k1 x y)
    (h2 : StepsIM centre place entry q first w k2 y z) :
    StepsIM centre place entry q first w (k1 + k2) x z := by
  obtain ⟨g1, hg10, hg1k, htr1, hp1⟩ := h1
  obtain ⟨g2, hg20, hg2k, htr2, hp2⟩ := h2
  have hj : g1 k1 = g2 0 := by rw [hg1k, hg20]
  refine ⟨concat g1 g2 k1, ?_, ?_, trace_concat htr1 htr2 hj,
    pack_concat hj hp1 hp2⟩
  · rw [concat_le g1 g2 (Nat.zero_le _)]; exact hg10
  · rw [concat_end g1 g2 hj]; exact hg2k

/-- `CloseoutPackRun9.ipackO_last_of_stepsIO` over the guarded payload. -/
theorem ipackM_last_of_stepsIM {w : List (Fin 2)} {k : ℕ} {x y : State GalilVM}
    (h : StepsIM centre place entry q first w k x y) :
    IPackM centre place entry q first w y := by
  obtain ⟨g, -, hgk, -, hp⟩ := h
  rw [← hgk]; exact hp k le_rfl

end Trans

#print axioms stepsIM_trans
#print axioms ipackM_last_of_stepsIM

/-! ## 2. `ReachAtIM`, `CycleOutIM`, `CycleOracleIM` -/

section Recursion
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- `CloseoutPackRun9.ReachAtIO` over `StepsIM`. -/
def ReachAtIM (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) : Prop :=
  ∃ (y : State GalilVM) (k : ℕ) (L : List Piece),
    StepsIM centre place entry q first w k ⟨c, r⟩ y ∧
    CostedRun r y.vm k L ∧
    PalPeg.GalilReportPrefix.ReportPointAt w m y ∧
    Refreshed (PofC centre place entry w) q first y ∧
    (m < w.length → ∃ (c' : Control) (r' : GalilVM) (k' : ℕ) (L' : List Piece),
      StepsIM centre place entry q first w k' y ⟨c', r'⟩ ∧
      CostedRun y.vm r' k' L' ∧
      InvLPC w c' r' ∧ position r'.right ≤ 2 * (m+1) - 1)

/-- `CloseoutPackRun9.CycleOutIO` over `StepsIM`. -/
def CycleOutIM (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) : Prop :=
  ReachAtIM centre place entry q first w m c r ∨
    ∃ (cT : Control) (sT : GalilVM) (k : ℕ) (L : List Piece),
      StepsIM centre place entry q first w k ⟨c, r⟩ ⟨cT, sT⟩ ∧
      CostedRun r sT k L ∧
      InvLPC w cT sT ∧ mu w sT < mu w r ∧
      position sT.right ≤ 2 * m - 1

/-- `CloseoutPackRun9.CycleOracleIO` over `StepsIM`. -/
def CycleOracleIM (w : List (Fin 2)) : Prop :=
  ∀ (m : ℕ) (c : Control) (r : GalilVM), 1 ≤ m → m ≤ w.length → InvLPC w c r →
    position r.right ≤ 2 * m - 1 → CycleOutIM centre place entry q first w m c r

/-- `CloseoutPackRun9.reachIO_fuel` over `StepsIM`. -/
theorem reachIM_fuel (w : List (Fin 2)) (hor : CycleOracleIM centre place entry q first w)
    (m : ℕ) (hm1 : 1 ≤ m) (hmle : m ≤ w.length) :
    ∀ (n : ℕ) (c : Control) (r : GalilVM), mu w r ≤ n → InvLPC w c r →
      position r.right ≤ 2 * m - 1 → ReachAtIM centre place entry q first w m c r := by
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
        stepsIM_trans centre place entry q first hst hst',
        costedRun_trans hcr hcr', hrp, hfr, hcont⟩

theorem reachIM_from_invLPC (w : List (Fin 2))
    (hor : CycleOracleIM centre place entry q first w)
    {m : ℕ} (hm1 : 1 ≤ m) (hmle : m ≤ w.length) {c : Control} {r : GalilVM}
    (hI : InvLPC w c r) (hp : position r.right ≤ 2 * m - 1) :
    ReachAtIM centre place entry q first w m c r :=
  reachIM_fuel centre place entry q first w hor m hm1 hmle _ c r le_rfl hI hp

end Recursion

#print axioms reachIM_fuel
#print axioms reachIM_from_invLPC

/-! ## 3. The checkpoint construction over `StepsIM` -/

section Construct
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- `CloseoutPackRun9.checkpoints_costIO_upto1` over the guarded payload. -/
theorem checkpoints_costIM_upto1 (w : List (Fin 2))
    (hor : CycleOracleIM centre place entry q first w)
    {x0 : State GalilVM} {k0 : ℕ} {c : Control} {r : GalilVM}
    (hpre : StepsIM centre place entry q first w k0 x0 ⟨c, r⟩)
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
      (∀ i, i ≤ e → IPackM centre place entry q first w (st i)) := by
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
      reachIM_from_invLPC centre place entry q first w hor (m := M+1) (by omega) hM hI' hp'
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
    have hpk1 : ∀ i, i ≤ e + k → IPackM centre place entry q first w (st1 i) :=
      pack_concat hj1 hpk hpg1
    obtain ⟨st2, e2, htr2, hagree, hle2, hres2, hpk2⟩ :
        ∃ (st2 : ℕ → State GalilVM) (e2 : ℕ),
          Trace (galilFrameS (PofC centre place entry w) q first) 2048 (SoundScanNR w) st2 e2 ∧
          (∀ i, i ≤ e + k → st2 i = st1 i) ∧ e + k ≤ e2 ∧
          (M + 1 < w.length → ∃ (c'' : Control) (r'' : GalilVM),
            st2 e2 = ⟨c'', r''⟩ ∧ InvLPC w c'' r'' ∧
            position r''.right ≤ 2 * (M+1+1) - 1 ∧
            ∃ L : List Piece, CostedRun y.vm r'' (e2 - (e + k)) L) ∧
          (∀ i, i ≤ e2 → IPackM centre place entry q first w (st2 i)) := by
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

#print axioms checkpoints_costIM_upto1

/-! ## 4. `PreTraceIM` -/

section Pre
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- `CloseoutPackRun9.PreTraceIO` over the guarded payload. -/
structure PreTraceIM (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ) : Prop where
  base : PreTraceB centre place entry q first w st Tc
  packs : ∀ i, i ≤ Tc w.length → IPackM centre place entry q first w (st i)

/-- `CloseoutPackRun9.H_bootIO` over `StepsIM`. -/
def H_bootIM : Prop :=
  ∀ (a : Fin 2) (rest : List (Fin 2)),
    ∃ (c1 : Control) (t : GalilVM),
      StepsIM centre place entry q first (a :: rest) 1
        ⟨GalilScaffoldController.initial 2048, GalilBootVM.initVM0 (a :: rest)⟩ ⟨c1, t⟩ ∧
      InvLPC (a :: rest) c1 t ∧ position t.right = 1

/-- The boot prefix weakens once more. -/
theorem h_bootIM_of_h_bootIO (h : H_bootIO centre place entry q first) :
    H_bootIM centre place entry q first := by
  intro a rest
  obtain ⟨c1, t, hst, hI, hp⟩ := h a rest
  exact ⟨c1, t, stepsIM_of_stepsIO centre place entry q first hst, hI, hp⟩

/-- `CloseoutPackRun9.H_oracleIO` over `StepsIM`. -/
def H_oracleIM : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → CycleOracleIM centre place entry q first w

/-- `CloseoutPackRun9.preTraceIO_exists` over the guarded payload. -/
theorem preTraceIM_exists (hboot : H_bootIM centre place entry q first)
    (hor : H_oracleIM centre place entry q first) (w : List (Fin 2)) (hw : 0 < w.length) :
    ∃ st Tc, PreTraceIM centre place entry q first w st Tc := by
  rcases w with _ | ⟨a, rest⟩
  · simp at hw
  · obtain ⟨c1, t, hst, hI, hpos⟩ := hboot a rest
    obtain ⟨st, Tc, e, hst0, hTc0, htr, hmono, hTcM, hchk, hcost, -, -, hone, hpk⟩ :=
      checkpoints_costIM_upto1 centre place entry q first (a :: rest) (hor (a :: rest) hw)
        hst hI hpos (a :: rest).length le_rfl
    refine ⟨st, Tc, ⟨⟨⟨hst0, hTc0, trace_le htr hTcM, mono_of_step Tc _ hmono, ?_, hcost⟩,
      hone (by simp)⟩, fun i hi => hpk i (le_trans hi hTcM)⟩⟩
    intro m h1 h2
    exact ledgerAt_of_prefix (hchk m h1 h2).1 (hchk m h1 h2).2

end Pre

#print axioms h_bootIM_of_h_bootIO
#print axioms preTraceIM_exists

/-! ## 5. The trail bridge over `IPackM` -/

section TrailM
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- `CloseoutPackRun7.halfBound_of_ipackO` over `IPackM`: it reads only
`IPackM.shift` and `LPackM.scanGeom`, both unchanged by the mode guard. -/
theorem halfBound_of_ipackM {w : List (Fin 2)} {x : State GalilVM}
    (hx : IPackM centre place entry q first w x) {s'' t'' : GalilVM}
    (hcmp : (galilFrameS (PofC centre place entry w) q first).compare x.vm s'')
    (hb : beginShiftVM' s'' t'') :
    ∃ rad : ℕ,
      ScanInvariant w (position x.vm.center) rad x.vm.left x.vm.right ∧
      GalilScaffoldChainVerifier.canRight x.vm.right ∧
      ∀ wch : GalilScaffoldChainWatch.State, s''.chain = .watch wch →
        2 * periodLength wch ≤ rad := by
  obtain ⟨hmode, hrep⟩ := hx.shift.mode s'' t'' hcmp hb
  obtain ⟨rad, hscan⟩ := hx.pack.scanGeom hmode hrep
  refine ⟨rad, hscan, hx.shift.move s'' t'' hcmp hb, fun wch hch => ?_⟩
  have h4 : 4 * (periodLength wch : ℤ) ≤
      GalilScaffoldCounter.value wch.machine.control.distance :=
    hx.shift.guard s'' t'' hcmp hb wch hch
  have h2 : GalilScaffoldCounter.value wch.machine.control.distance ≤ 2 * (rad : ℤ) :=
    hx.shift.coupled s'' t'' hcmp hb wch hch rad hscan
  omega

/-- `CloseoutPackRun7.shiftEntry_ptO` over `IPackM`. -/
theorem shiftEntry_ptM {w : List (Fin 2)} {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hIP : ∀ i, i ≤ Tc w.length → IPackM centre place entry q first w (st i)) :
    ∀ i, i ≤ Tc w.length → ∀ s'' t'' : GalilVM,
      (galilFrameS (PofC centre place entry w) q first).compare (st i).vm s'' →
      beginShiftVM' s'' t'' → ShiftBud t'' := by
  intro i hi s'' t'' hcmp hb
  obtain ⟨rad, hscan, hcan, hh⟩ :=
    halfBound_of_ipackM centre place entry q first (hIP i hi) hcmp hb
  exact shiftBud_of_scanInv (onLetterVM w) leftFirstVM centre place entry q first
    hscan hcan hcmp hb hh

/-- `CloseoutPackRun7.shiftVerSane_ptO` over `IPackM`. -/
theorem shiftVerSane_ptM {w : List (Fin 2)} {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hIP : ∀ i, i ≤ Tc w.length → IPackM centre place entry q first w (st i)) :
    ∀ i, i ≤ Tc w.length → ∀ s'' t'' : GalilVM,
      (galilFrameS (PofC centre place entry w) q first).compare (st i).vm s'' →
      beginShiftVM' s'' t'' → SaneVer t''.chain :=
  fun i hi s'' t'' hcmp hb =>
    saneVer_beginShift hb ((hIP i hi).shift.ver s'' t'' hcmp hb)

/-- `CloseoutPackRun7.radPack_ptO` over `IPackM`. -/
theorem radPack_ptM {w : List (Fin 2)} (hw : 0 < w.length) {st : ℕ → State GalilVM}
    {Tc : ℕ → ℕ} (hP : PreTrace centre place entry q first w st Tc)
    (hIP : ∀ i, i ≤ Tc w.length → IPackM centre place entry q first w (st i)) :
    ∀ i, i ≤ Tc w.length → RadPack (st i).ctl (st i).vm := by
  have hll := leftLive_ptM centre place entry q first hIP
  have hen := shiftEntry_ptM centre place entry q first hIP
  have hsv := shiftVerSane_ptM centre place entry q first hIP
  have hL := radLedger_pt centre place entry q first hw hP hll
  have hS := shiftOrd_pt centre place entry q first hw hP hll hen
  have hV := verSane_pt centre place entry q first hw hP hll hsv
  exact fun i hi => radPack_of_parts (hL i hi) (hS i hi) (hll i hi) (hV i hi)

/-- `CloseoutPackRun7.trailF_ptO` over `IPackM`. -/
theorem trailF_ptM {w : List (Fin 2)} (hw : 0 < w.length) {st : ℕ → State GalilVM}
    {Tc : ℕ → ℕ} (hP : PreTrace centre place entry q first w st Tc)
    (hIP : ∀ i, i ≤ Tc w.length → IPackM centre place entry q first w (st i))
    {m : ℕ} (hm : m < w.length) :
    ∀ i, i ≤ Tc (m+1) → TrailF w m (st i) := by
  have hll := leftLive_ptM centre place entry q first hIP
  have hsane := sanePack_pt centre place entry q first hw hP hll
  have hrad := radPack_ptM centre place entry q first hw hP hIP
  have hscan := scanT_pt centre place entry q first hw hP hrad hsane hm
  have hB := chainBudget_pt centre place entry q first hw hP hrad hsane hm
  have hV := verF_trace centre place entry q first hP hm hscan hB
  exact fun i hi => trailF_of_scanT (hscan i hi) (hV i hi).ver (hV i hi).lagPos

/-- **(NAMED-FREE) `CloseoutPackRun7.H_trailI_O` over the guarded payload.** -/
def H_trailI_M : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTrace centre place entry q first w st Tc →
    (∀ i, i ≤ Tc w.length → IPackM centre place entry q first w (st i)) →
    ∀ m, m < w.length → ∀ i, i ≤ Tc (m+1) → TrailF w m (st i)

/-- **(KEY) the trail bridge does not read the mode-unguarded strictness
either.**  `CloseoutPackRun7.h_trailI_O` over `IPackM`. -/
theorem h_trailI_M : H_trailI_M centre place entry q first :=
  fun _ hw _ _ hP hIP _ hm i hi =>
    trailF_ptM centre place entry q first hw hP hIP hm i hi

/-- The refined need bound on a `PreTraceIM`; like `CloseoutPackRun9.needIO'_le`
it takes **no** trail hypothesis. -/
theorem needIM'_le {w : List (Fin 2)}
    (hw : 0 < w.length) {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hP : PreTraceIM centre place entry q first w st Tc) :
    ∀ m, m < w.length → ∀ i, i ≤ Tc (m+1) → needL' w st i ≤ m + 1 :=
  fun m hm i hi =>
    needL'_le_of_trailF w st m i
      (h_trailI_M centre place entry q first w hw st Tc hP.base.pre hP.packs m hm i hi)

end TrailM

#print axioms halfBound_of_ipackM
#print axioms radPack_ptM
#print axioms h_trailI_M
#print axioms needIM'_le

/-! ## 6. `pal_in_peg_final5M` -/

/-- (C) over `PreTraceIM`. -/
def H_realizeLIM' (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9) : Prop :=
  ∃ (Q' Γ' : Type) (_ : Fintype Q') (_ : DecidableEq Q') (_ : Fintype Γ') (_ : DecidableEq Γ')
    (t K : ℕ) (L : PalPeg.Local.LocalStep (Fin 2) Q' Γ' t K) (blank : Γ') (initQ : Q')
    (outQ : Q' → Bool) (n : ℕ) (htape : 0 < t) (hn : 0 < n),
    ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTraceIM centre place entry q first w st Tc →
      ((L.realize blank initQ (GalilEmptyWord.accept' initQ outQ) n htape hn).SAccepts w ↔
        LatchTrue (PofC centre place entry w) q first w (stLG' τF w st (Tc w.length))
          ((w.length + 1) * τF))

/-- **`CloseoutPackRun9.pal_in_peg_final5O` over the guarded payload.** -/
theorem pal_in_peg_final5M (entry q : ℕ) (first : Fin 9)
    (hboot : H_bootIM centreC placeC entry q first)
    (hA : H_oracleIM centreC placeC entry q first)
    (hC : H_realizeLIM' centreC placeC entry q first) :
    RecognizedByTotalPEG PAL := by
  classical
  obtain ⟨Q', Γ', iQ, dQ, iΓ, dΓ, t, K, L, blank, initQ, outQ, n, htape, hn, hreal⟩ := hC
  have key : ∀ w : List (Fin 2), ∃ (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      0 < w.length → PreTraceIM centreC placeC entry q first w st Tc := by
    intro w
    by_cases hw : 0 < w.length
    · obtain ⟨st, Tc, h⟩ := preTraceIM_exists centreC placeC entry q first hboot hA w hw
      exact ⟨st, Tc, fun _ => h⟩
    · exact ⟨fun _ => boot w, fun _ => 0, fun h => absurd h hw⟩
  choose stP TcP hP using key
  let M := L.realize blank initQ (GalilEmptyWord.accept' initQ outQ) n htape hn
  have hpre : ∀ w : List (Fin 2), 0 < w.length → PreloadL' w (stP w) (TcP w) := by
    intro w hw
    have h := hP w hw
    exact ⟨h.base.pre.tc0, fun m hm => h.base.pre.mono m (m+1) (by omega) hm,
      needL'_boot w (stP w) h.base.pre.start,
      needLe_of_pointwise' w (stP w) (TcP w) (needIM'_le centreC placeC entry q first hw h)⟩
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

#print axioms pal_in_peg_final5M

/-! ## 7. `packRunR_M` and the oracle bridge -/

section BridgeM
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- `CloseoutPackRun3.extra_steps` over `Extra'`. -/
theorem extra'_steps {w : List (Fin 2)} (het : H_extraTick' centre place entry q first w)
    {n : ℕ} {x y : State GalilVM} (he : Extra' centre place entry w x)
    (h : Steps (galilFrameS (PofC centre place entry w) q first) 2048 n x y) :
    Extra' centre place entry w y := by
  induction h with
  | zero z => exact he
  | @succ m a b z h hr ih => exact ih (het a b he h)

/-- `CloseoutPackRun8.PackRunRO` over `StepsIM`. -/
def PackRunRM (w : List (Fin 2)) : Prop :=
  ∀ (c : Control) (r : GalilVM), InvLPC w c r →
    ∀ (j : ℕ) (x : State GalilVM),
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 j ⟨c, r⟩ x →
      ∀ (k : ℕ) (y : State GalilVM), IPackM centre place entry q first w x →
        StepsAll (galilFrameS (PofC centre place entry w) q first) 2048 (SoundScanNR w) k x y →
        StepsIM centre place entry q first w k x y

/-- **(KEY) `PackRunRM` from the six `BigResid6` contracts plus the two `Extra'`
obligations.**  `CloseoutPackRun8.packRunR_O` over the guarded pack. -/
theorem packRunR_M {w : List (Fin 2)}
    (hr : BigResid6 centre place entry q first w)
    (hee : H_extraEntry' centre place entry w)
    (het : H_extraTick' centre place entry q first w) :
    PackRunRM centre place entry q first w := by
  intro c r hIC j x hjx k y hx h
  have hlv0 : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 m ⟨c, r⟩ z →
      CentreLive z.ctl z.vm :=
    PalPeg.GalilOracleLeaves2.hlive_of_invLPC centre place entry q first hIC
  have haux0 : AuxPack c r :=
    ⟨coupled_of_invLPC hIC, front_of_invLPC hIC, copyPack_of_invLPC hIC⟩
  have hauxx : AuxPack x.ctl x.vm :=
    auxPack_steps centre place entry q first (x := ⟨c, r⟩) hlv0 haux0 hjx
  have hexx : Extra' centre place entry w x :=
    extra'_steps centre place entry q first het (x := ⟨c, r⟩) (hee c r hIC) hjx
  have hbx : BigPack2M centre place entry q first w x :=
    ⟨hx, hauxx, hlv0 j x hjx, hexx⟩
  obtain ⟨g, hg0, hgk, htr⟩ := stepsAll_fn h
  have hreach : ∀ i, i ≤ k →
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 (j + i) ⟨c, r⟩ (g i) := by
    intro i hi
    have := steps_of_trace htr i hi
    rw [hg0] at this
    exact steps_trans hjx this
  have hbig : ∀ i, i ≤ k → BigPack2M centre place entry q first w (g i) := by
    intro i
    induction i with
    | zero => intro _; rw [hg0]; exact hbx
    | succ n ih =>
      intro hi
      exact bigPack2M_tick centre place entry q first hr het (ih (by omega))
        (htr.tick n (by omega)) (htr.good (n+1) hi)
        (hlv0 (j + (n+1)) (g (n+1)) (hreach (n+1) hi))
  exact ⟨g, hg0, hgk, htr, fun i hi => (hbig i hi).ipackM⟩

/-- `CloseoutPackRun9.reachAtIO_of_reachAtC3R` over `PackRunRM`. -/
theorem reachAtIM_of_reachAtC3R {w : List (Fin 2)}
    (hpr : PackRunRM centre place entry q first w)
    {m : ℕ} {c : Control} {r : GalilVM} (hIC : InvLPC w c r)
    (hx : IPackM centre place entry q first w ⟨c, r⟩)
    (h : ReachAtC3 (PofC centre place entry w) q first w m c r) :
    ReachAtIM centre place entry q first w m c r := by
  obtain ⟨y, k, L, hst, hcr, hrp, hfr, hcont⟩ := h
  have hstI : StepsIM centre place entry q first w k ⟨c, r⟩ y :=
    hpr c r hIC 0 ⟨c, r⟩ (.zero _) k y hx hst
  refine ⟨y, k, L, hstI, hcr, hrp, hfr, fun hlt => ?_⟩
  obtain ⟨c', r', k', L', hst', hcr', hIS, hp⟩ := hcont hlt
  exact ⟨c', r', k', L',
    hpr c r hIC k y (stepsAll_steps hst) k' ⟨c', r'⟩
      (ipackM_last_of_stepsIM centre place entry q first hstI) hst',
    hcr', hIS.1, hp⟩

/-- `CloseoutPackRun9.cycleOutIO_of_cycleOutMC3R` over `PackRunRM`. -/
theorem cycleOutIM_of_cycleOutMC3R {w : List (Fin 2)}
    (hpr : PackRunRM centre place entry q first w)
    {m : ℕ} {c : Control} {r : GalilVM} (hIC : InvLPC w c r)
    (hx : IPackM centre place entry q first w ⟨c, r⟩)
    (h : CycleOutMC3 (PofC centre place entry w) q first w m c r) :
    CycleOutIM centre place entry q first w m c r := by
  rcases h with hdone | ⟨cT, sT, k, L, hst, hcr, hIT, hlt, hpos⟩
  · exact Or.inl (reachAtIM_of_reachAtC3R centre place entry q first hpr hIC hx hdone)
  · exact Or.inr ⟨cT, sT, k, L, hpr c r hIC 0 ⟨c, r⟩ (.zero _) k ⟨cT, sT⟩ hx hst,
      hcr, hIT.1, hlt, hpos⟩

/-- `CloseoutPackRun9.cycleOracleIO_of_cycleOracleMC3R` over `PackRunRM`. -/
theorem cycleOracleIM_of_cycleOracleMC3R {w : List (Fin 2)}
    (hpr : PackRunRM centre place entry q first w)
    (hsl : H_shiftLocalC centre place entry q first w)
    (hsc : H_stageScan centre place entry q first w)
    (hor : CycleOracleMC3 (PofC centre place entry w) q first w) :
    CycleOracleIM centre place entry q first w := by
  intro m c r hm1 hmle hIC hp
  exact cycleOutIM_of_cycleOutMC3R centre place entry q first hpr hIC
    (ipackM_of_ipackO centre place entry q first
      (ipackO_of_ipack centre place entry q first
        (ipack_of_invLPC' centre place entry q first hsl (x := ⟨c, r⟩) hIC)))
    (hor m c r hm1 hmle (hstage_of_scanBranch centre place entry q first hsc c r hIC) hp)

end BridgeM

#print axioms extra'_steps
#print axioms packRunR_M
#print axioms reachAtIM_of_reachAtC3R
#print axioms cycleOutIM_of_cycleOutMC3R
#print axioms cycleOracleIM_of_cycleOracleMC3R

/-! ## 8. `pal_in_peg_final13` -/

/-- **`CloseoutPackRun9.pal_in_peg_final12` over the mode-guarded residual.**
`BigResid5O` becomes `CloseoutPackRun11.BigResid6` (the `LPackO` conclusions of
`rInitPackO` / `rReplayPackO` weaken to `LPackM`, and every contract is handed
the weaker hypothesis `BigPack2M`), and `Extra` becomes `Extra'` — five fields,
the refuted `scanMargin` deleted — so the two enlargement obligations are
`H_extraEntry'` / `H_extraTick'`.  The boot prefix still comes from
`CloseoutOracleI.bootIPack_of_parts` and is weakened twice
(`h_bootIO_of_h_bootI`, then `h_bootIM_of_h_bootIO`); the oracle comes from
`packRunR_M` through §7; the trail bridge is discharged outright by
`h_trailI_M` inside `pal_in_peg_final5M`. -/
theorem pal_in_peg_final13 (entry q : ℕ) (first : Fin 9)
    (hr : ∀ w : List (Fin 2), BigResid6 centreC placeC entry q first w)
    (hee : ∀ w : List (Fin 2), H_extraEntry' centreC placeC entry w)
    (het : ∀ w : List (Fin 2), H_extraTick' centreC placeC entry q first w)
    (hsl : ∀ w : List (Fin 2), H_shiftLocalC centreC placeC entry q first w)
    (hsc : ∀ w : List (Fin 2), H_stageScan centreC placeC entry q first w)
    (hor : ∀ w : List (Fin 2), 0 < w.length →
      CycleOracleMC3 (PofC centreC placeC entry w) q first w)
    (hbs : H_bootShift centreC placeC entry q first)
    (hls : H_landShift centreC placeC entry q first)
    (hC : H_realizeLIM' centreC placeC entry q first) :
    RecognizedByTotalPEG PAL :=
  pal_in_peg_final5M entry q first
    (h_bootIM_of_h_bootIO centreC placeC entry q first
      (h_bootIO_of_h_bootI centreC placeC entry q first
        (h_bootI_of_bootIPack centreC placeC entry q first
          (bootIPack_of_parts centreC placeC entry q first h_lrepC hbs hls))))
    (fun w hw => cycleOracleIM_of_cycleOracleMC3R centreC placeC entry q first
      (packRunR_M centreC placeC entry q first (hr w) (hee w) (het w)) (hsl w) (hsc w)
      (hor w hw))
    hC

#print axioms pal_in_peg_final13

end PalPeg.CloseoutPackRun12
