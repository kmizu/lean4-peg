import PalPeg.GalilInvPlus2
import PalPeg.GalilNoShiftDischarge
import PalPeg.GalilFoundStage
import PalPeg.GalilFinalAssembly3

/-!
# The cycle oracle over the strengthened landing invariant

`GalilTraceCost.checkpoints_cost` runs the recursion over `InvL`, so its
continuation clause (`ReachAtC`) only hands the next cycle an `InvL` state.
The strengthened leaves of `GalilInvPlus2` (`foundRouteMC_noshift''`,
`invLPC_of_fallbackRouteP`, `invLPC_of_foundRouteLP`) all *need* `InvLPC`
(`InvLP` + the copy pack + the centre head) at the entry and all *produce* it at
the landing, so the whole recursion can be carried over `InvLPC` instead.

* `ReachAtC2` — `ReachAtC` whose continuation carries `InvLPC`.
* `CycleOutMC2C` / `CycleOracleMC2C` — `GalilInvPlus2.CycleOutMC2` /
  `CycleOracleMC2` with `InvLPC` in place of `InvLP2` and `ReachAtC2` in place
  of `ReachAtC`.
* `reachC2_from_invLPC` — the recursion on `mu`.
* `checkpoints_cost2` — `checkpoints_cost` over the strengthened oracle, with
  the entry state only required to be `InvLPC`.  No `hstr` anywhere.
* `cycleOracleMC_of_MC2C` — the bridge back to `GalilTraceCost.CycleOracleMC`
  (hence to `GalilFinalAssembly.H_oracle`); this one *does* need the residue
  `hstr : InvL → InvLPC`, because `CycleOracleMC` quantifies over every `InvL`
  state, boot-reachable or not.  Its copy-pack half is free from the boot
  (`invLP2_of_boot`), which is what `checkpoints_cost2` exploits.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.GalilOracleMC2

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton PalPeg.GalilOracleDischarge PalPeg.GalilOracleLocal
open PalPeg.GalilCheckpoints PalPeg.GalilTraceCost PalPeg.GalilLexMeasure
open PalPeg.GalilInvPlus PalPeg.GalilInvPlus2 PalPeg.GalilOracleMC
open PalPeg.GalilIntervalCost PalPeg.GalilLedgerQ64 PalPeg.GalilLedgerAssembly
open PalPeg.GalilGlueBLeaves PalPeg.GalilBranchInvariants2 PalPeg.GalilSegmentConstruct
open PalPeg.GalilNoShiftDischarge PalPeg.GalilOracleM

/-! ## 1. `ReachAtC2`: the continuation over `InvLPC` -/

theorem invLPC_invL {raw : List (Fin 2)} {c : Control} {s : GalilVM} (h : InvLPC raw c s) :
    InvL raw c s := h.1.1.1

theorem invLPC_invLP {raw : List (Fin 2)} {c : Control} {s : GalilVM} (h : InvLPC raw c s) :
    InvLP raw c s := h.1.1

/-- `GalilTraceCost.ReachAtC` with the resume continuation carrying `InvLPC`. -/
def ReachAtC2 (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ)
    (c : Control) (r : GalilVM) : Prop :=
  ∃ (y : State GalilVM) (k : ℕ) (L : List Piece),
    StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ y ∧
    CostedRun r y.vm k L ∧
    PalPeg.GalilReportPrefix.ReportPointAt raw m y ∧ Refreshed P q first y ∧
    (m < raw.length → ∃ (c' : Control) (r' : GalilVM) (k' : ℕ) (L' : List Piece),
      StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k' y ⟨c', r'⟩ ∧
      CostedRun y.vm r' k' L' ∧
      InvLPC raw c' r' ∧ position r'.right ≤ 2 * (m+1) - 1)

/-- Forgetting the strengthening of the continuation. -/
theorem reachAtC_of_2 {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)} {m : ℕ}
    {c : Control} {r : GalilVM} (h : ReachAtC2 P q first raw m c r) :
    ReachAtC P q first raw m c r := by
  obtain ⟨y, k, L, hst, hcr, hrp, hfr, hcont⟩ := h
  refine ⟨y, k, L, hst, hcr, hrp, hfr, fun hlt => ?_⟩
  obtain ⟨c', r', k', L', hst', hcr', hI, hp⟩ := hcont hlt
  exact ⟨c', r', k', L', hst', hcr', invLPC_invL hI, hp⟩

/-- `GalilInvPlus2.CycleOutMC2` over `InvLPC`. -/
def CycleOutMC2C (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ)
    (c : Control) (r : GalilVM) : Prop :=
  ReachAtC2 P q first raw m c r ∨
    ∃ (cT : Control) (sT : GalilVM) (k : ℕ) (L : List Piece),
      StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩ ∧
      CostedRun r sT k L ∧
      InvLPC raw cT sT ∧ mu raw sT < mu raw r ∧
      position sT.right ≤ 2 * m - 1

/-- `GalilInvPlus2.CycleOracleMC2` over `InvLPC`. -/
def CycleOracleMC2C (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) : Prop :=
  ∀ (m : ℕ) (c : Control) (r : GalilVM), 1 ≤ m → m ≤ raw.length → InvLPC raw c r →
    position r.right ≤ 2 * m - 1 → CycleOutMC2C P q first raw m c r

/-- The centre-progress exit. -/
theorem cycleOutMC2C_of_centre {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)} {m : ℕ}
    {c : Control} {r : GalilVM} {cT : Control} {sT : GalilVM} {k : ℕ} {L : List Piece}
    (hI : InvLPC raw c r)
    (hst : StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩)
    (hcr : CostedRun r sT k L) (hIT : InvLPC raw cT sT)
    (hlt : position r.center < position sT.center) (hp : position sT.right ≤ 2 * m - 1) :
    CycleOutMC2C P q first raw m c r :=
  Or.inr ⟨cT, sT, k, L, hst, hcr, hIT,
    mu_lt_of_centre (invS_center_le (invLPC_invL hI).1) (invLPC_invL hIT) hlt, hp⟩

/-- The no-shift exit (centre kept, right head strictly up). -/
theorem cycleOutMC2C_of_noshift {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)} {m : ℕ}
    {c : Control} {r : GalilVM} {cT : Control} {sT : GalilVM} {k : ℕ} {L : List Piece}
    (hst : StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩)
    (hcr : CostedRun r sT k L) (hIT : InvLPC raw cT sT)
    (hc : position sT.center = position r.center) (hlt : position r.right < position sT.right)
    (hp : position sT.right ≤ 2 * m - 1) : CycleOutMC2C P q first raw m c r :=
  Or.inr ⟨cT, sT, k, L, hst, hcr, hIT, mu_lt_of_right (invLPC_invL hIT) hc hlt, hp⟩

/-! ## 2. The recursion on `mu` over `InvLPC` -/

theorem reachC2_fuel (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (hor : CycleOracleMC2C P q first raw) (m : ℕ) (hm1 : 1 ≤ m) (hmle : m ≤ raw.length) :
    ∀ (n : ℕ) (c : Control) (r : GalilVM), mu raw r ≤ n → InvLPC raw c r →
      position r.right ≤ 2 * m - 1 → ReachAtC2 P q first raw m c r := by
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
      exact ⟨y, k + k', L ++ L', stepsAll_trans hst hst', costedRun_trans hcr hcr', hrp, hfr, hcont⟩

theorem reachC2_from_invLPC (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (hor : CycleOracleMC2C P q first raw) {m : ℕ} (hm1 : 1 ≤ m) (hmle : m ≤ raw.length)
    {c : Control} {r : GalilVM} (hI : InvLPC raw c r) (hp : position r.right ≤ 2 * m - 1) :
    ReachAtC2 P q first raw m c r :=
  reachC2_fuel P q first raw hor m hm1 hmle _ c r le_rfl hI hp

/-- **The bridge back to `GalilTraceCost.CycleOracleMC`.**  `hstr` is the whole
residue: every admissible `InvL` state carries the entering counters, the copy
pack and the centre head. -/
theorem cycleOracleMC_of_MC2C {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    (hor : CycleOracleMC2C P q first raw)
    (hstr : ∀ (c : Control) (r : GalilVM), InvL raw c r → InvLPC raw c r) :
    CycleOracleMC P q first raw :=
  fun _ c r hm1 hmle hI hp =>
    Or.inl (reachAtC_of_2 (reachC2_from_invLPC P q first raw hor hm1 hmle (hstr c r hI) hp))


/-! ## 3. The checkpoint trace, over `InvLPC` -/

theorem checkpoints_cost2_upto (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (hor : CycleOracleMC2C P q first raw)
    {x0 : State GalilVM} {k0 : ℕ} {c : Control} {r : GalilVM}
    (hpre : StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k0 x0 ⟨c, r⟩)
    (hI : InvLPC raw c r) (hpos : position r.right ≤ 1) :
    ∀ M, M ≤ raw.length →
    ∃ (st : ℕ → State GalilVM) (Tc : ℕ → ℕ) (e : ℕ),
      st 0 = x0 ∧ Tc 0 = 0 ∧ Trace (galilFrameS P q first) 2048 (SoundScanNR raw) st e ∧
      (∀ m, m < M → Tc m ≤ Tc (m+1)) ∧ Tc M ≤ e ∧
      (∀ m, 1 ≤ m → m ≤ M →
        PalPeg.GalilReportPrefix.ReportPointAt raw m (st (Tc m)) ∧
        Refreshed P q first (st (Tc m))) ∧
      (∀ m, 1 ≤ m → m < M →
        Tc (m+1) - Tc m ≤ alpha' 2048 * (Cw raw (m+1) - Cw raw m) + beta' 2048) ∧
      (M < raw.length → ∃ (c' : Control) (r' : GalilVM),
        st e = ⟨c', r'⟩ ∧ InvLPC raw c' r' ∧ position r'.right ≤ 2 * (M+1) - 1 ∧
        (1 ≤ M → ∃ L : List Piece, CostedRun (st (Tc M)).vm r' (e - Tc M) L)) := by
  intro M
  induction M with
  | zero =>
    intro _
    obtain ⟨g, hg0, hgn, htr⟩ := stepsAll_fn hpre
    refine ⟨g, fun _ => 0, k0, hg0, rfl, htr, fun m hm => absurd hm (Nat.not_lt_zero _),
      Nat.zero_le _, fun m h1 h2 => absurd h1 (by omega), fun m h1 h2 => absurd h2 (by omega),
      fun _ => ⟨c, r, hgn, hI, by omega, fun h => absurd h (by omega)⟩⟩
  | succ M ih =>
    intro hM
    obtain ⟨st, Tc, e, hst0, hTc0, htr, hmono, hTcM, hchk, hcost, hres⟩ := ih (by omega)
    obtain ⟨c', r', hste, hI', hp', hpend⟩ := hres (by omega)
    obtain ⟨y, k, L2, hrun, hcr, hrp, hfr, hcont⟩ :=
      reachC2_from_invLPC P q first raw hor (m := M+1) (by omega) hM hI' hp'
    obtain ⟨g1, hg10, hg1k, htr1⟩ := stepsAll_fn hrun
    have hj1 : st e = g1 0 := by rw [hste, hg10]
    set st1 := concat st g1 e with hst1
    have htr1' : Trace (galilFrameS P q first) 2048 (SoundScanNR raw) st1 (e + k) :=
      trace_concat htr htr1 hj1
    have hst1y : st1 (e + k) = y := by rw [hst1, concat_end st g1 hj1, hg1k]
    obtain ⟨st2, e2, htr2, hagree, hle2, hres2⟩ :
        ∃ (st2 : ℕ → State GalilVM) (e2 : ℕ),
          Trace (galilFrameS P q first) 2048 (SoundScanNR raw) st2 e2 ∧
          (∀ i, i ≤ e + k → st2 i = st1 i) ∧ e + k ≤ e2 ∧
          (M + 1 < raw.length → ∃ (c'' : Control) (r'' : GalilVM),
            st2 e2 = ⟨c'', r''⟩ ∧ InvLPC raw c'' r'' ∧ position r''.right ≤ 2 * (M+1+1) - 1 ∧
            ∃ L : List Piece, CostedRun y.vm r'' (e2 - (e + k)) L) := by
      by_cases hlt : M + 1 < raw.length
      · obtain ⟨c'', r'', k', L', hrun2, hcr2, hI2, hp2⟩ := hcont hlt
        obtain ⟨g2, hg20, hg2k, htr2⟩ := stepsAll_fn hrun2
        have hj2 : st1 (e + k) = g2 0 := by rw [hst1y, hg20]
        refine ⟨concat st1 g2 (e + k), e + k + k', trace_concat htr1' htr2 hj2,
          fun i hi => concat_le st1 g2 hi, by omega, fun _ => ⟨c'', r'', ?_, hI2, hp2, L', ?_⟩⟩
        · rw [concat_end st1 g2 hj2, hg2k]
        · rw [show e + k + k' - (e + k) = k' by omega]; exact hcr2
      · exact ⟨st1, e + k, htr1', fun _ _ => rfl, le_rfl, fun h => absurd h hlt⟩
    have hTcle : ∀ m, m ≤ M → Tc m ≤ e := fun m hm =>
      le_trans (mono_of_step Tc M hmono m M hm le_rfl) hTcM
    have hst2old : ∀ m, m ≤ M → st2 (Tc m) = st (Tc m) := by
      intro m hm
      rw [hagree _ (by have := hTcle m hm; omega), hst1, concat_le st g1 (hTcle m hm)]
    have hst2y : st2 (e + k) = y := by rw [hagree _ le_rfl, hst1y]
    refine ⟨st2, fun m => if m ≤ M then Tc m else e + k, e2, ?_, ?_, htr2, ?_, ?_, ?_, ?_, ?_⟩
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

/-- **`checkpoints_cost2`.**  `GalilTraceCost.checkpoints_cost` over the
strengthened oracle.  The entry state is only required to be `InvLPC`; there is
no `hstr : InvL → InvLPC` anywhere, because the recursion never leaves `InvLPC`. -/
theorem checkpoints_cost2 (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (hor : CycleOracleMC2C P q first raw)
    {x0 : State GalilVM} {k0 : ℕ} {c : Control} {r : GalilVM}
    (hpre : StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k0 x0 ⟨c, r⟩)
    (hI : InvLPC raw c r) (hpos : position r.right ≤ 1) :
    ∃ (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      st 0 = x0 ∧ Tc 0 = 0 ∧
      Trace (galilFrameS P q first) 2048 (SoundScanNR raw) st (Tc raw.length) ∧
      (∀ m m', m ≤ m' → m' ≤ raw.length → Tc m ≤ Tc m') ∧
      (∀ m, 1 ≤ m → m ≤ raw.length →
        PalPeg.GalilLedgerAssembly.ReportPointAt P q first raw m (st (Tc m))) ∧
      (∀ m, 1 ≤ m → m < raw.length →
        Tc (m+1) - Tc m ≤ alpha' 2048 * (Cw raw (m+1) - Cw raw m) + beta' 2048) := by
  obtain ⟨st, Tc, e, hst0, hTc0, htr, hmono, hTcM, hchk, hcost, -⟩ :=
    checkpoints_cost2_upto P q first raw hor hpre hI hpos raw.length le_rfl
  exact ⟨st, Tc, hst0, hTc0, trace_le htr hTcM, mono_of_step Tc raw.length hmono,
    fun m h1 h2 => ledgerAt_of_prefix (hchk m h1 h2).1 (hchk m h1 h2).2, hcost⟩

/-- **The copy-pack half of the entry is free from the boot.**  An `InvLP`
state reached from the boot state that carries the centre head is `InvLPC`. -/
theorem invLPC_of_boot (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9) (d : ℕ)
    {raw : List (Fin 2)} {n : ℕ} {c : Control} {r : GalilVM}
    (h : Steps (galilFrameS (PofC centre place entry raw) q first) 2048 n
      ⟨GalilScaffoldController.initial d, GalilBootVM.initVM0 raw⟩ ⟨c, r⟩)
    (hI : InvLP raw c r) (hc : CentreRep raw r) : InvLPC raw c r :=
  ⟨invLP2_of_boot centre place entry q first d h hI, hc⟩


/-! ## 4. The routes over `InvLPC` -/

/-- `GalilOracleMC.FallbackRouteMC` with the two landings carrying `SpanRep`
(as `GalilInvPlus.FallbackRouteP` does) and the report exit strengthened to
`ReachAtC2`. -/
inductive FallbackRouteMC2 (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ)
    (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM) : Prop
  | report (h : ReachAtC2 P q first raw m c r)
  | landed (fb : ℕ) (cT : Control) (sT : GalilVM)
      (hst : StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) (1 + fb) ⟨c', t⟩ ⟨cT, sT⟩)
      (hD : FppData raw t fb 0)
      (hland : position sT.center = position (right t.right) - 0) (hCR : sT.center = sT.right)
      (hI : Inv raw cT sT) (hSpan : SpanRep sT) (hprog : position t.center < position sT.center)
      (hpos : position (right t.right) ≤ 2 * m - 1)
  | replaying (fb R : ℕ) (cT : Control) (sT : GalilVM)
      (hst : StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) (1 + fb) ⟨c', t⟩ ⟨cT, sT⟩)
      (hD : FppData raw t fb R) (hL : ReplayLanding raw cT sT R) (hSpan : SpanRep sT)
      (hland : position sT.center = position (right t.right) - R) (hCR : sT.center = sT.right)
      (hprog : position t.center < position sT.center)
      (hpos : position (right t.right) ≤ 2 * m - 1)

/-- **The mismatch exit over `InvLPC`.**  `GalilOracleMC.cycleOutMC_of_fallback`
with the landing strengthened: the radius-`0` landing is an `Inv` state with
`SpanRep` (`invLPC_of_landed`), and the replayed landing gets its entering
counters from `entryCounters_of_invScan` and its centre head from
`invScanC_of_restart`, exactly as in `GalilInvPlus2.invLPC_after_replayLanding`. -/
theorem cycleOutMC2C_of_fallback (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m : ℕ)
    (hex : ∀ s, (PofC centre place entry raw).replayExhausted s = zero s.replay)
    (hsearch : ∀ s : GalilVM, SearchReady (searchLens.get s) →
      ∀ a : Bool, ∃ v, searchEffect (PofC centre place entry raw) a s v)
    (hpres : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s) →
      searchEffect (PofC centre place entry raw) a s v → SearchReady v)
    (hquiet : PalPeg.GalilReplaySegment.SearchQuiet (PofC centre place entry raw))
    (hout : ∀ (c' : Control) (t' : GalilVM) (k : ℕ),
      PalPeg.GalilReplaySegment.InvScan 2048 raw c' t' k → SoundScanNR raw ⟨c', t'⟩)
    {c c' : Control} {r t : GalilVM} {es : List Bool}
    (hIC : InvLPC raw c r)
    (hw : WatchSegE (PofC centre place entry raw) q first 2048 es c r c' t)
    (hcen : t.center = r.center) (hc1 : c'.clock = 1) (hav : canRight t.right)
    (h : FallbackRouteMC2 (PofC centre place entry raw) q first raw m c r c' t) :
    CycleOutMC2C (PofC centre place entry raw) q first raw m c r := by
  have hI : InvL raw c r := invLPC_invL hIC
  obtain ⟨⟨R0, hi0⟩, hc0, -⟩ := invL_entry hI
  have hrun0 := seg_run centre place entry q first raw hI hw
  cases h with
  | report h => exact Or.inl h
  | landed fb cT sT hst hD hland hCR hIT hSpan hprog hpos =>
      obtain ⟨Rad, ℓ, a, xs, rs', q', a₀, ls₀, rs₀, q₀, gap₀, lower, span, y, hi, hRR, hSt, hv, hkC,
        hdec, hraw, hraw₀, hC₀, hspan, hres, hidle, hlow, hR, hfb⟩ := hD
      obtain ⟨L, w, hw', e, hcr, -, -, -, -, -, hr'⟩ :=
        GalilCostedFallback.costedRun_fallback_zero raw (PofC centre place entry raw) q first hw hi0
          hc0 hc1 (t := sT) hi hav hRR hSt ℓ hv hkC a xs rs' q' hdec hraw a₀ ls₀ rs₀ q₀ gap₀ hraw₀
          hC₀ hspan hres hidle hlow fb hR hfb hland hCR
      have hall := stepsAll_trans hrun0 hst
      rw [show es.length + (1 + fb) = es.length + 1 + fb by omega] at hall
      exact cycleOutMC2C_of_centre hIC hall hcr
        (invLPC_of_landed centre place entry q first hIC.1.2 hall hIT hSpan)
        (by rw [← hcen]; exact hprog) (by rw [hr']; exact hpos)
  | replaying fb R cT sT hst hD hL hSpan hland hCR hprog hpos =>
      obtain ⟨Rad, ℓ, a, xs, rs', q', a₀, ls₀, rs₀, q₀, gap₀, lower, span, y, hi, hRR, hSt, hv, hkC,
        hdec, hraw, hraw₀, hC₀, hspan, hres, hidle, hlow, hR, hfb⟩ := hD
      obtain ⟨esR, c'', t'', hseg, hstR, hlen, hcnt, hrr, hcc, hIS⟩ :=
        PalPeg.GalilReplaySegment.replay_after_fallback raw (PofC centre place entry raw) q first
          2048 hex (by norm_num) hsearch hpres hquiet R hL.pos cT sT hL.mode hL.clock hL.replaying
          hL.rest hL.replay hL.minv hL.frontier hL.shiftIdle
      obtain ⟨L, w, hw', e, hcr, -, -, -, -, -, hr'⟩ :=
        GalilCostedFallback.costedRun_fallback_replay raw (PofC centre place entry raw) q first hw
          hi0 hc0 hc1 (t := sT) (t' := t'') hi hav hRR hSt ℓ hv hkC a xs rs' q' hdec hraw a₀ ls₀
          rs₀ q₀ gap₀ hraw₀ hC₀ hspan hres hidle hlow fb esR R hR hfb hlen hland hCR hrr hcc
      have hall := stepsAll_trans (stepsAll_trans hrun0 hst) (hstR (hout c'' t'' R hIS))
      rw [show es.length + (1 + fb) + esR.length = es.length + 1 + fb + esR.length by omega] at hall
      have hRRt : RadiusRep t''.radius R := by
        have h0 := radiusRep_watchSegE _ q first 2048 hseg hL.rest.2.2.2.2.1
        rw [hcnt, Nat.zero_add] at h0
        exact h0
      have hE : EntryCounters raw t'' :=
        entryCounters_of_invScan hIS hRRt (spanRep_watchSegE _ q first 2048 hseg hSpan)
          (canonical_length_watchSegE _ q first 2048 hseg hL.rest.2.2.2.2.2.1)
      have hIL : InvLP raw c'' t'' := ⟨invL_of_run hall (Or.inr ⟨R, hIS⟩), hE⟩
      exact cycleOutMC2C_of_centre hIC hall hcr
        ⟨invLP2_of_stepsAll centre place entry q first hIC.1.2 hall hIL,
          (invScanC_of_restart hL.rest hcc hIS).2⟩
        (by rw [hcc, ← hcen]; exact hprog) (by rw [hr']; exact hpos)


/-- `GalilOracleMC.FoundRouteMC` with the landings carrying `SpanRep` (as
`GalilInvPlus.FoundRouteLP` does), the report exit strengthened to `ReachAtC2`,
and one extra exit `broke`: the found cycle that breaks *before* any shift
(`GalilInvPlus2.foundRouteMC_noshift''` / `GalilNoShiftDischarge`), which keeps
the centre and advances the right head, so it is admissible only for `mu`. -/
inductive FoundRouteMC2 (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ)
    (c : Control) (r : GalilVM) (c0 : Control) (s0 : GalilVM) : Prop
  | report (h : ReachAtC2 P q first raw m c r)
  | shift (cT : Control) (sT : GalilVM) (hcost : FoundCost P q first raw c0 s0 cT sT)
      (hM : MInv raw cT sT) (hR : ∃ (Rad : ℕ) (last : Counter), Restarted raw sT Rad last)
      (hres : FoundResidual raw cT sT) (hSpan : SpanRep sT)
      (hprog : position s0.center < position sT.center)
      (hpos : position sT.right ≤ 2 * m - 1)
  | noShift (cT : Control) (sT : GalilVM) (hcost : FoundCost P q first raw c0 s0 cT sT)
      (hM : MInv raw cT sT) (hR : ∃ (Rad : ℕ) (last : Counter), Restarted raw sT Rad last)
      (hres : FoundResidual raw cT sT) (hSpan : SpanRep sT)
      (hprog : position s0.center < position sT.center)
      (hpos : position sT.right ≤ 2 * m - 1)
  | broke (cT : Control) (sT : GalilVM) (k : ℕ) (L : List Piece)
      (hst : StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩)
      (hcr : CostedRun r sT k L) (hIT : InvLP2 raw cT sT) (hcenT : CentreRep raw sT)
      (hc : position sT.center = position r.center)
      (hlt : position r.right < position sT.right)
      (hpos : position sT.right ≤ 2 * m - 1)

/-- **The found exit over `InvLPC`**, the found route started at the segment end. -/
theorem cycleOutMC2C_of_found (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m : ℕ) {c c' : Control} {r t : GalilVM} {es : List Bool}
    (hIC : InvLPC raw c r)
    (hw : WatchSegE (PofC centre place entry raw) q first 2048 es c r c' t)
    (hcen : t.center = r.center) (hav : canRight t.right)
    (h : FoundRouteMC2 (PofC centre place entry raw) q first raw m c r c' t) :
    CycleOutMC2C (PofC centre place entry raw) q first raw m c r := by
  have hI : InvL raw c r := invLPC_invL hIC
  obtain ⟨⟨R, hi⟩, hc0, -⟩ := invL_entry hI
  have hrun0 := seg_run centre place entry q first raw hI hw
  obtain ⟨Ls, k', w1, hcrS, he, hw1, -, -, -, -⟩ :=
    GalilCostedFallback.costedRun_watchSegE raw (PofC centre place entry raw) q first hw hi hc0 hav
  have fin : ∀ (cT : Control) (sT : GalilVM),
      FoundCost (PofC centre place entry raw) q first raw c' t cT sT →
      Inv raw cT sT → SpanRep sT → position t.center < position sT.center →
      position sT.right ≤ 2 * m - 1 →
      CycleOutMC2C (PofC centre place entry raw) q first raw m c r := by
    intro cT sT hcost hIT hSpan hprog hpos
    obtain ⟨k, L, hst, hcr⟩ := hcost w1 hw1
    have hall := stepsAll_trans hrun0 hst
    have hcr' := costedRun_trans hcrS hcr
    rw [show k' + (k + w1) = es.length + k by omega] at hcr'
    exact cycleOutMC2C_of_centre hIC hall hcr'
      (invLPC_of_landed centre place entry q first hIC.1.2 hall hIT hSpan)
      (by rw [← hcen]; exact hprog) hpos
  cases h with
  | report h => exact Or.inl h
  | shift cT sT hcost hM hR hres hSpan hprog hpos =>
      exact fin cT sT hcost (inv_of_residual hM hR hres) hSpan hprog hpos
  | noShift cT sT hcost hM hR hres hSpan hprog hpos =>
      exact fin cT sT hcost (inv_of_residual hM hR hres) hSpan hprog hpos
  | broke cT sT k L hst hcr hIT hcenT hc hlt hpos =>
      exact cycleOutMC2C_of_noshift hst hcr ⟨hIT, hcenT⟩ hc hlt hpos

/-- **The background-found exit over `InvLPC`**, the found route started at the
cycle start. -/
theorem cycleOutMC2C_of_foundBg (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m : ℕ) {c : Control} {r : GalilVM}
    (hIC : InvLPC raw c r)
    (h : FoundRouteMC2 (PofC centre place entry raw) q first raw m c r c r) :
    CycleOutMC2C (PofC centre place entry raw) q first raw m c r := by
  have hI : InvL raw c r := invLPC_invL hIC
  obtain ⟨-, hc0, -⟩ := invL_entry hI
  have fin : ∀ (cT : Control) (sT : GalilVM),
      FoundCost (PofC centre place entry raw) q first raw c r cT sT →
      Inv raw cT sT → SpanRep sT → position r.center < position sT.center →
      position sT.right ≤ 2 * m - 1 →
      CycleOutMC2C (PofC centre place entry raw) q first raw m c r := by
    intro cT sT hcost hIT hSpan hprog hpos
    obtain ⟨k, L, hst, hcr⟩ := hcost 0 (by omega)
    exact cycleOutMC2C_of_centre hIC hst hcr
      (invLPC_of_landed centre place entry q first hIC.1.2 hst hIT hSpan) hprog hpos
  cases h with
  | report h => exact Or.inl h
  | shift cT sT hcost hM hR hres hSpan hprog hpos =>
      exact fin cT sT hcost (inv_of_residual hM hR hres) hSpan hprog hpos
  | noShift cT sT hcost hM hR hres hSpan hprog hpos =>
      exact fin cT sT hcost (inv_of_residual hM hR hres) hSpan hprog hpos
  | broke cT sT k L hst hcr hIT hcenT hc hlt hpos =>
      exact cycleOutMC2C_of_noshift hst hcr ⟨hIT, hcenT⟩ hc hlt hpos


/-- **The matched, not-found comparison onto `2m-1`, over `InvLPC`.**
`GalilOracleMC.reachAtC_of_target_match` with the resume continuation
strengthened: the entering counters travel along the idle segment
(`scanInvariant_watchSegE`, `radiusRep_watchSegE`, `spanRep_watchSegE`,
`canonical_length_watchSegE`) and across the report comparison
(`matched_invariant'`, `radius_rep_inc`, `spanRep_afterCompare`,
`inc_canonical`); the copy pack travels along the run itself; the centre head is
the one the cycle started with (the segment and `afterCompare` keep the centre). -/
theorem reachAtC2_of_target_match (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m : ℕ) (hm1 : 1 ≤ m) (hmle : m ≤ raw.length)
    (hpres : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s) →
      searchEffect (PofC centre place entry raw) a s v → SearchReady v)
    (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM) (hIC : InvLPC raw c r)
    (hsW : SegReachedW centre place entry q first raw c r c' t)
    (hT : AtTarget m c' t)
    (hmt : read (left t.left) = read (right t.right))
    (vq : SearchVM) (hq : searchEffect (PofC centre place entry raw) true t vq)
    (hnf : vq.search.mode ≠ .found) :
    ReachAtC2 (PofC centre place entry raw) q first raw m c r := by
  classical
  set P : Shared := PofC centre place entry raw with hP
  have hI : InvL raw c r := invLPC_invL hIC
  obtain ⟨hs, es, hw⟩ := hsW
  obtain ⟨hnr, hc1, hav, hpos, hrep⟩ := hT
  obtain ⟨⟨R0, hi0⟩, hc0, -⟩ := invL_entry hI
  have hrun0 := seg_run centre place entry q first raw hI hw
  obtain ⟨R, hi⟩ := hs.scan
  -- the entering counters, transported along the idle segment
  obtain ⟨RadE, hiE, hRRE, hSE, hLE⟩ := hIC.1.1.2
  have hiT : ScanInvariant raw (position r.center) (RadE + es.count true) t.left t.right :=
    scanInvariant_watchSegE P q first 2048 hw hiE
  have hRRT : RadiusRep t.radius (RadE + es.count true) :=
    radiusRep_watchSegE P q first 2048 hw hRRE
  have hST : SpanRep t := spanRep_watchSegE P q first 2048 hw hSE
  have hLT : Canonical t.length := canonical_length_watchSegE P q first 2048 hw hLE
  set vs : ScanVM := ⟨left t.left, right t.right, ChainVM.idle⟩ with hvs
  have hmt0 : (galilFrame P q first).matched (scanLens.set t vs) := hmt
  have hborn : chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) t.chain
      = false := by
    have hd : decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found) = false := by
      simp [hnf]
    unfold chainBorn
    rw [hd]
    exact Bool.and_false _
  have hcmp : (galilFrameS P q first).compare t (afterCompare t vs vq) :=
    ⟨vs, vq, true, rfl, rfl, ⟨fun _ => hmt0, fun _ => rfl⟩, hq,
      Or.inr (Or.inl ⟨hs.idle, by simp [hnf], rfl⟩), by rw [hborn]; rfl⟩
  have hmt1 : (galilFrameS P q first).matched (afterCompare t vs vq) := hmt
  set u : GalilVM := afterCompare t vs vq with hu
  set o : Bool := if P.onLetter u then decide (P.leftFirst u) else c'.output with ho'
  have ho : refresh (galilFrameS P q first) u c'.output o := by
    refine ⟨fun hl => ?_, fun hl => ?_⟩
    · have hl' : P.onLetter u := hl
      show (if P.onLetter u then decide (P.leftFirst u) else c'.output) = true ↔ P.leftFirst u
      rw [if_pos hl']; exact decide_eq_true_iff
    · have hl' : ¬ P.onLetter u := hl
      show (if P.onLetter u then decide (P.leftFirst u) else c'.output) = c'.output
      rw [if_neg hl']
  have hsrc : SoundScanNR raw ⟨c', t⟩ := stepsAll_last hrun0
  obtain ⟨⟨k1, hrun1⟩, hrp, hfr⟩ :=
    PalPeg.GalilReportPrefix.reportAt_of_match raw P rfl rfl q first 2048 hsrc hs.mode hc1 hnr
      hav hs.minv hi hpos hm1 hmle vs vq o false rfl rfl hcmp hmt1 ho
  have hsound := stepsAll_last hrun1
  have hpl : (galilFrameS P q first).matchedPlace c'.replaying u u := by
    show u = (if c'.replaying then _ else u)
    rw [hnr]; simp
  have htick : Tick (galilFrameS P q first) 2048 ⟨c', t⟩
      ⟨{c' with clock := 2048, output := o, replaying := false}, u⟩ := by
    have h := Tick.scan_match (F := galilFrameS P q first) (delay := 2048) c' t u u o hs.mode
      (Or.inr hav) hc1 hcmp hmt1 hpl ho
    rw [hnr] at h
    simpa using h
  have hall := stepsAll_trans hrun0 (.succ hsrc htick (.zero _ hsound))
  obtain ⟨L, w, hw', hcr, -, -⟩ :=
    GalilCostedFallback.costedRun_target_match raw P q first hw hi0 hc0 hc1 hav m hm1 hpos vq
  -- the counters and the centre head at the landing of the comparison
  have hcu : u.center = r.center := by rw [hu, afterCompare_center, hs.center]
  have hEu : EntryCounters raw u := by
    refine ⟨RadE + es.count true + 1, ?_, ?_, ?_, ?_⟩
    · rw [hcu]; exact matched_invariant' raw vq (vs := vs) rfl rfl hmt hav hiT
    · rw [hu, afterCompare_radius]; exact radius_rep_inc hRRT
    · rw [hu]; exact spanRep_afterCompare hST
    · rw [hu, afterCompare_length]; exact inc_canonical _ (inc_canonical _ hLT)
  refine ⟨_, es.length + (0 + 1), L ++ [GalilCostedFallback.cmpPiece (2 * m - 1) w hw'], hall,
    hcr, hrp, hfr, fun _ => ⟨_, u, 0, [], .zero _ (stepsAll_last hall), costedRun_nil u, ?_, ?_⟩⟩
  · have hIS : PalPeg.GalilReplaySegment.InvScan 2048 raw
        {c' with clock := 2048, output := o, replaying := false} u (R + 1) := by
      refine PalPeg.GalilReplaySegment.inv_after_replay 2048 raw _ u (R + 1) hs.mode rfl rfl
        (by rw [hu, afterCompare_chain]) ?_ hrp.centre ?_ ?_ ?_
      · exact matched_invariant' raw vq (vs := vs) rfl rfl hmt hav hi
      · exact hpres t true vq hs.search hq
      · rw [hu, afterCompare_replay]; exact hrep
      · exact PalPeg.GalilReplaySegment.shiftIdle_congr
          (PalPeg.GalilReplaySegment.afterCompare_remaining t vs vq) hs.shiftIdle
    have hIL : InvLP raw {c' with clock := 2048, output := o, replaying := false} u :=
      ⟨invL_of_run hall (Or.inr ⟨R + 1, hIS⟩), hEu⟩
    exact ⟨invLP2_of_stepsAll centre place entry q first hIC.1.2 hall hIL,
      centreRep_congr hcu hIC.2⟩
  · have h1 : position u.right = 2 * m - 1 := hrp.atPlace
    omega


/-! ## 5. The general replay, over `ReplayBudgetR` -/

/-- `GalilInvPlus2.invScanC_of_replay_general` over
`GalilFoundStage.replay_after_fallback_general'''`: the raw `ReplayBudget` leaf
is replaced by `ReplayBudgetR` (the budget restricted to the found ticks
reachable inside a replay) together with `ReplayStageInv`. -/
theorem invScanC_of_replay_generalR (raw : List (Fin 2)) (P : Shared)
    (hP : P.onLetter = onLetterVM raw) (hP' : P.leftFirst = leftFirstVM) (q : ℕ) (first : Fin 9)
    (delay : ℕ) (hex : ∀ s, P.replayExhausted s = zero s.replay) (hd : 1 ≤ delay)
    (hsearch : ∀ s : GalilVM, SearchReady (searchLens.get s) →
      ∀ a : Bool, ∃ v, searchEffect P a s v)
    (hpres : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s) → searchEffect P a s v → SearchReady v)
    (hshape : PalPeg.GalilWatchOkInst.StartShape P)
    (hbudget : PalPeg.GalilFoundStage.ReplayBudgetR raw P q first delay)
    (hinv : PalPeg.GalilFoundStage.ReplayStageInv raw P q first)
    (hrs : PalPeg.GalilReplaySpan.RestartShape P)
    (r : ℕ) (hr0 : 0 < r) (c : Control) (t : GalilVM)
    (hm : c.mode = Mode.scan) (hc : c.clock = delay) (hrpl : c.replaying = true)
    (hR : Restarted raw t 0 reset) (hrep : t.replay = ofNat r)
    (hM : MInv raw c t) (hfr : Frontier t) (hsi : ShiftIdle t) :
    (∃ (es : List Bool) (c' : Control) (t' : GalilVM),
      WatchSegE P q first delay es c t c' t' ∧
      (SoundScanNR raw ⟨c', t'⟩ →
        StepsAll (galilFrameS P q first) delay (SoundScanNR raw) es.length ⟨c, t⟩ ⟨c', t'⟩) ∧
      es.length = r * delay ∧ es.count true = r ∧
      position t'.right = position t.right + r ∧ t'.center = t.center ∧
      InvScanC delay raw c' t' r) ∨
    PalPeg.GalilReplaySpan.ChainEnd raw P q first delay (position t.right + r) c t 0 r ∨
    (PalPeg.GalilReplaySpan.BrokeAndRestarted raw P q first delay c t ∧
      ∃ (n : ℕ) (c' : Control) (t' : GalilVM),
        (SoundScanNR raw ⟨c', t'⟩ →
          StepsAll (galilFrameS P q first) delay (SoundScanNR raw) n ⟨c, t⟩ ⟨c', t'⟩) ∧
        position t'.right = position t.right + r ∧ t'.center = t.center ∧
        InvScanC delay raw c' t' r) := by
  rcases PalPeg.GalilFoundStage.replay_after_fallback_general''' raw P hP hP' q first delay hex hd
      hsearch hpres hshape hbudget hinv hrs r hr0 c t hm hc hrpl hR hrep hM hfr hsi with
    ⟨es, c', t', hseg, hst, hlen, hcnt, hpos, hC, hIS⟩ | hEnd | ⟨hw, n, c', t', hst, hpos, hC, hIS⟩
  · exact Or.inl ⟨es, c', t', hseg, hst, hlen, hcnt, hpos, hC, invScanC_of_restart hR hC hIS⟩
  · exact Or.inr (Or.inl hEnd)
  · exact Or.inr (Or.inr ⟨hw, n, c', t', hst, hpos, hC, invScanC_of_restart hR hC hIS⟩)

/-! ## 6. The oracle over `InvLPC`, assembled -/

/-- **`GalilOracleMC.cycleOracleMC_of_pieces` over `InvLPC`.**  Same case split
(target reached / mismatch / found / background found / report exits), with every
entry state an `InvLPC` state and every exit landing back in `InvLPC`. -/
theorem cycleOracleMC2C_of_pieces (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2))
    (hex : ∀ s, (PofC centre place entry raw).replayExhausted s = zero s.replay)
    (hsearch : ∀ s : GalilVM, SearchReady (searchLens.get s) →
      ∀ a : Bool, ∃ v, searchEffect (PofC centre place entry raw) a s v)
    (hpres : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s) →
      searchEffect (PofC centre place entry raw) a s v → SearchReady v)
    (hquiet : PalPeg.GalilReplaySegment.SearchQuiet (PofC centre place entry raw))
    (houtReplay : ∀ (c' : Control) (t' : GalilVM) (k : ℕ),
      PalPeg.GalilReplaySegment.InvScan 2048 raw c' t' k → SoundScanNR raw ⟨c', t'⟩)
    (hsegmentM : ∀ (m : ℕ) (c : Control) (r : GalilVM), 1 ≤ m → m ≤ raw.length →
      InvLPC raw c r → position r.right ≤ 2 * m - 1 →
      ∃ (c' : Control) (t : GalilVM),
        SegReachedW centre place entry q first raw c r c' t ∧
        (AtTarget m c' t ∨ SegEnd (PofC centre place entry raw) c' t))
    (hended : ∀ (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ raw.length → InvLPC raw c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centre place entry q first raw c r c' t → ¬ canRight t.right →
      ReachAtC2 (PofC centre place entry raw) q first raw m c r)
    (hlastMatch : ∀ (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ raw.length → InvLPC raw c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centre place entry q first raw c r c' t →
      c'.clock = 1 → canRight t.right → PopsIncoming t.right →
      (∃ a : Fin 2, t.right.head.incoming = [a]) →
      read (left t.left) = read (right t.right) →
      ReachAtC2 (PofC centre place entry raw) q first raw m c r)
    (hlastMismatch : ∀ (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ raw.length → InvLPC raw c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centre place entry q first raw c r c' t →
      c'.clock = 1 → canRight t.right → PopsIncoming t.right →
      (∃ a : Fin 2, t.right.head.incoming = [a]) →
      read (left t.left) ≠ read (right t.right) →
      ReachAtC2 (PofC centre place entry raw) q first raw m c r)
    (hmismatch : ∀ (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ raw.length → InvLPC raw c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centre place entry q first raw c r c' t →
      c'.replaying = false → c'.clock = 1 → canRight t.right →
      read (left t.left) ≠ read (right t.right) →
      FallbackRouteMC2 (PofC centre place entry raw) q first raw m c r c' t)
    (hfound : ∀ (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ raw.length → InvLPC raw c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centre place entry q first raw c r c' t →
      c'.clock = 1 → canRight t.right →
      read (left t.left) = read (right t.right) →
      (∃ vq, searchEffect (PofC centre place entry raw) true t vq ∧ vq.search.mode = .found) →
      FoundRouteMC2 (PofC centre place entry raw) q first raw m c r c' t)
    (hfoundBg : ∀ (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ raw.length → InvLPC raw c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centre place entry q first raw c r c' t → 1 ≤ c'.clock →
      (∃ vq, searchEffect (PofC centre place entry raw) false t vq ∧ vq.search.mode = .found) →
      FoundRouteMC2 (PofC centre place entry raw) q first raw m c r c r) :
    CycleOracleMC2C (PofC centre place entry raw) q first raw := by
  intro m c r hm1 hmle hIC hp
  obtain ⟨c', t, hsW, hend⟩ := hsegmentM m c r hm1 hmle hIC hp
  obtain ⟨hs, es, hw⟩ := id hsW
  rcases hend with hT | hend
  · obtain ⟨hnr, hc1, hav, -, -⟩ := id hT
    by_cases hmt : read (left t.left) = read (right t.right)
    · obtain ⟨vq, hq⟩ := hsearch t hs.search true
      by_cases hf : vq.search.mode = .found
      · exact cycleOutMC2C_of_found centre place entry q first raw m hIC hw hs.center hav
          (hfound m c r c' t hm1 hmle hIC hp hsW hc1 hav hmt ⟨vq, hq, hf⟩)
      · exact Or.inl (reachAtC2_of_target_match centre place entry q first raw m hm1 hmle hpres
          c r c' t hIC hsW hT hmt vq hq hf)
    · exact cycleOutMC2C_of_fallback centre place entry q first raw m hex hsearch hpres hquiet
        houtReplay hIC hw hs.center hc1 hav
        (hmismatch m c r c' t hm1 hmle hIC hp hsW hnr hc1 hav hmt)
  · cases hend with
    | ended hn => exact Or.inl (hended m c r c' t hm1 hmle hIC hp hsW hn)
    | mismatch hr hc hav hne =>
        exact cycleOutMC2C_of_fallback centre place entry q first raw m hex hsearch hpres hquiet
          houtReplay hIC hw hs.center hc hav
          (hmismatch m c r c' t hm1 hmle hIC hp hsW hr hc hav hne)
    | found hc hav hmt hq =>
        exact cycleOutMC2C_of_found centre place entry q first raw m hIC hw hs.center hav
          (hfound m c r c' t hm1 hmle hIC hp hsW hc hav hmt hq)
    | foundBackground hc hq =>
        exact cycleOutMC2C_of_foundBg centre place entry q first raw m hIC
          (hfoundBg m c r c' t hm1 hmle hIC hp hsW hc hq)
    | lastLetter hc hav hpop hinc =>
        by_cases hmt : read (left t.left) = read (right t.right)
        · exact Or.inl (hlastMatch m c r c' t hm1 hmle hIC hp hsW hc hav hpop hinc hmt)
        · exact Or.inl (hlastMismatch m c r c' t hm1 hmle hIC hp hsW hc hav hpop hinc hmt)


/-! ## 7. `H_oracle` from the leaves -/

open PalPeg.GalilFinalAssembly PalPeg.GalilFinalAssembly2 in
/-- **`H_oracle` from the remaining leaves.**  Every hypothesis here is a leaf of
the `InvLPC` recursion, quantified over the input word; `hstr` is the one residue
of the bridge back to `GalilTraceCost.CycleOracleMC` (see `checkpoints_cost2`
for the boot-side route that avoids it). -/
theorem h_oracle_of_leaves (entry q : ℕ) (first : Fin 9)
    (hex : ∀ (w : List (Fin 2)) (s : GalilVM),
      (PofC centreC placeC entry w).replayExhausted s = zero s.replay)
    (hsearch : ∀ (w : List (Fin 2)) (s : GalilVM), SearchReady (searchLens.get s) →
      ∀ a : Bool, ∃ v, searchEffect (PofC centreC placeC entry w) a s v)
    (hpres : ∀ (w : List (Fin 2)) (s : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s) →
      searchEffect (PofC centreC placeC entry w) a s v → SearchReady v)
    (hquiet : ∀ w : List (Fin 2),
      PalPeg.GalilReplaySegment.SearchQuiet (PofC centreC placeC entry w))
    (houtReplay : ∀ (w : List (Fin 2)) (c' : Control) (t' : GalilVM) (k : ℕ),
      PalPeg.GalilReplaySegment.InvScan 2048 w c' t' k → SoundScanNR w ⟨c', t'⟩)
    (hsegmentM : ∀ (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM), 1 ≤ m → m ≤ w.length →
      InvLPC w c r → position r.right ≤ 2 * m - 1 →
      ∃ (c' : Control) (t : GalilVM),
        SegReachedW centreC placeC entry q first w c r c' t ∧
        (AtTarget m c' t ∨ SegEnd (PofC centreC placeC entry w) c' t))
    (hended : ∀ (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ w.length → InvLPC w c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centreC placeC entry q first w c r c' t → ¬ canRight t.right →
      ReachAtC2 (PofC centreC placeC entry w) q first w m c r)
    (hlastMatch : ∀ (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) (c' : Control)
      (t : GalilVM), 1 ≤ m → m ≤ w.length → InvLPC w c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centreC placeC entry q first w c r c' t →
      c'.clock = 1 → canRight t.right → PopsIncoming t.right →
      (∃ a : Fin 2, t.right.head.incoming = [a]) →
      read (left t.left) = read (right t.right) →
      ReachAtC2 (PofC centreC placeC entry w) q first w m c r)
    (hlastMismatch : ∀ (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) (c' : Control)
      (t : GalilVM), 1 ≤ m → m ≤ w.length → InvLPC w c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centreC placeC entry q first w c r c' t →
      c'.clock = 1 → canRight t.right → PopsIncoming t.right →
      (∃ a : Fin 2, t.right.head.incoming = [a]) →
      read (left t.left) ≠ read (right t.right) →
      ReachAtC2 (PofC centreC placeC entry w) q first w m c r)
    (hmismatch : ∀ (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) (c' : Control)
      (t : GalilVM), 1 ≤ m → m ≤ w.length → InvLPC w c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centreC placeC entry q first w c r c' t →
      c'.replaying = false → c'.clock = 1 → canRight t.right →
      read (left t.left) ≠ read (right t.right) →
      FallbackRouteMC2 (PofC centreC placeC entry w) q first w m c r c' t)
    (hfound : ∀ (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) (c' : Control)
      (t : GalilVM), 1 ≤ m → m ≤ w.length → InvLPC w c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centreC placeC entry q first w c r c' t →
      c'.clock = 1 → canRight t.right →
      read (left t.left) = read (right t.right) →
      (∃ vq, searchEffect (PofC centreC placeC entry w) true t vq ∧ vq.search.mode = .found) →
      FoundRouteMC2 (PofC centreC placeC entry w) q first w m c r c' t)
    (hfoundBg : ∀ (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) (c' : Control)
      (t : GalilVM), 1 ≤ m → m ≤ w.length → InvLPC w c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centreC placeC entry q first w c r c' t → 1 ≤ c'.clock →
      (∃ vq, searchEffect (PofC centreC placeC entry w) false t vq ∧ vq.search.mode = .found) →
      FoundRouteMC2 (PofC centreC placeC entry w) q first w m c r c r)
    (hstr : ∀ (w : List (Fin 2)) (c : Control) (r : GalilVM), InvL w c r → InvLPC w c r) :
    H_oracle centreC placeC entry q first :=
  fun w _ => cycleOracleMC_of_MC2C
    (cycleOracleMC2C_of_pieces centreC placeC entry q first w (hex w) (hsearch w) (hpres w)
      (hquiet w) (houtReplay w) (hsegmentM w) (hended w) (hlastMatch w) (hlastMismatch w)
      (hmismatch w) (hfound w) (hfoundBg w)) (hstr w)


/-! ## 6b. The no-shift break leaf over `InvLPC` -/

/-- **`GalilNoShiftDischarge.foundRouteMC_noshift_d` over `InvLPC`.**  Same
wrapper (the preparation landing and the two palindromes are discharged from the
DP candidate and the copy/back data), but built on
`GalilInvPlus2.foundRouteMC_noshift''`, so `hcenS` is gone (the centre head comes
from `InvLPC`) and the landing is `InvLP2`.  This is the producer of the `broke`
constructor of `FoundRouteMC2`; only `CentreRep raw sT` at the landing is left
over, since `foundRouteMC_noshift''` does not export the fact that its landing is
a restart. -/
theorem foundRouteMC_noshift_dC (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2))
    (hex : ∀ s, (PofC centre place entry raw).replayExhausted s = zero s.replay)
    {c0 : Control} {r : GalilVM} (hI : InvLPC raw c0 r)
    (hlive : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (PofC centre place entry raw) qq first) 2048 m ⟨c0, r⟩ z →
      CentreLive z.ctl z.vm)
    (a : Fin 2) (ls rs q : List (Fin 2)) (gap : Bool)
    (hraw : raw = (a :: ls).reverse ++ rs ++ q)
    {es0 : List Bool} {cF : Control} {sF : GalilVM}
    (hseg0 : WatchSegE (PofC centre place entry raw) qq first 2048 es0 c0 r cF sF)
    (hmF : cF.mode = .scan) (hrF : cF.replaying = false)
    (hcF : cF.clock = 1) (havF : canRight sF.right) (hidle : sF.chain = .idle)
    (hCen : sF.center = represent ⟨a :: ls,gap⟩ (rs.map some) q)
    (vq : SearchVM) (hq : searchEffect (PofC centre place entry raw) true sF vq)
    (hfound : vq.search.mode = .found)
    (hmt : read (left sF.left) = read (right sF.right))
    (span lower h : ℕ) (cen : Fin 3) (p q' : GalilScaffoldPlace.Place)
    (u : GalilScaffoldTape.Tape) (ys : List (Fin 3)) (b : Fin 3)
    (hc : GalilDpCorrect.Candidate
      ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (span+1)) lower h)
    (hlen : ys.length + 1 = h)
    (hcopy : GalilScaffoldChainPeriod.Copy (vq.dp.config.tapes 11) reset p
      (GalilScaffoldChainPeriod.start cen) h u (ofNat h) q'
      (GalilScaffoldChainPeriod.fill (GalilScaffoldChainPeriod.start cen) (ys ++ [b])))
    (hu : u.focus = 4) (hpos : positive (ofNat h) = true)
    (hfocus : (GalilScaffoldChainPeriod.fill (GalilScaffoldChainPeriod.start cen)
      (ys ++ [b])).focus = .plain b)
    (hback : GalilScaffoldChainPeriod.Back (GalilScaffoldChainPeriod.write
      (GalilScaffoldChainPeriod.fill (GalilScaffoldChainPeriod.start cen) (ys ++ [b])) (.last b))
      (h+1) (GalilScaffoldChainPeriod.moveRight ⟨[], .first cen,
        ys.map GalilScaffoldChainPeriod.Token.plain ++ [.last b]⟩))
    (hh : 2*h+2 < 2048)
    (ch : ChainVM)
    (hch : ChainMatched (chainStart (vq.dp.config.tapes 11) cen p sF.center sF.radius) ch)
    (hch' : ChainMatched (chainStart (vq.dp.config.tapes 11)
      ((PofC centre place entry raw).centre sF)
      ((PofC centre place entry raw).place sF) sF.center sF.radius) ch)
    (hchne : ch ≠ .idle) (oF : Bool)
    (hoF : refresh (galilFrame (PofC centre place entry raw) qq first)
      (afterBirth true (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq)) cF.output oF)
    (hcont : ∀ (c2 : Control) (s2 : GalilVM),
      WatchSegE (PofC centre place entry raw) qq first 2048 (List.replicate (2*h+2) false)
        {cF with clock := 2048, output := oF, replaying := false}
        (afterBirth true (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq)) c2 s2 →
      s2.chain = .watch (GalilNoShiftStage.freshWatch sF.center cen ys b sF.radius) →
      c2.mode = .scan → c2.replaying = false → c2.output = oF →
      2048 - (2*h+2) ≤ c2.clock → c2.clock ≤ 2048 →
      s2.left = (afterBirth true (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq)).left →
      s2.right = (afterBirth true (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq)).right →
      s2.center = (afterBirth true (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq)).center →
      s2.radius = (afterBirth true (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq)).radius →
      ∃ (c3 : Control) (s3 : GalilVM) (w3 : GalilScaffoldChainWatch.State) (vs3 : ScanVM)
        (vq3 : SearchVM) (o3 : Bool) (w3' : GalilScaffoldChainWatch.State),
        WatchSeg (PofC centre place entry raw) qq first 2048 c2 s2 c3 s3 ∧
        c3.mode = .scan ∧ c3.replaying = false ∧ c3.clock = 1 ∧
        s3.chain = .watch w3 ∧ GalilScaffoldCounter.zero w3.lag = true ∧ canRight s3.right ∧
        (galilFrame (PofC centre place entry raw) qq first).compare s3 (scanLens.set s3 vs3) ∧
        (galilFrame (PofC centre place entry raw) qq first).matched (scanLens.set s3 vs3) ∧
        searchEffect (PofC centre place entry raw) true s3 vq3 ∧
        refresh (galilFrame (PofC centre place entry raw) qq first)
          (afterCompare s3 vs3 vq3) c3.output o3 ∧
        (afterCompare s3 vs3 vq3).chain = .broken w3' ∧
        negative w3'.margin = false) :
    ∃ (cT : Control) (sT : GalilVM) (k : ℕ) (L : List Piece),
      StepsAll (galilFrameS (PofC centre place entry raw) qq first) 2048 (SoundScanNR raw) k
        ⟨c0, r⟩ ⟨cT, sT⟩ ∧
      CostedRun r sT k L ∧ InvLP2 raw cT sT ∧
      position sT.center = position r.center ∧ position r.right < position sT.right ∧
      ∃ (s3 : GalilVM) (vs3 : ScanVM) (vq3 : SearchVM),
        sT.right = (afterCompare s3 vs3 vq3).right := by
  classical
  have hchain : (afterBirth true (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq)).chain = ch :=
    by rw [afterBirth_chain]; exact afterCompare_chain _ _ _
  obtain ⟨c2, s2, hseg2, hchz, hm2, hr2, ho2, hlo, hhi, hl2, hr2', hc2, hrad2, -, -, -, -⟩ :=
    prep_segment_construct_bg (PofC centre place entry raw) qq first 2048 (vq.dp.config.tapes 11)
      cen p q' sF.center sF.radius u h ys b hcopy hu hpos hfocus hback ch hch
      {cF with clock := 2048, output := oF, replaying := false}
      (afterBirth true (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq)) hmF rfl rfl hchain hh
  have hwatch2 : s2.chain = .watch (GalilNoShiftStage.freshWatch sF.center cen ys b sF.radius) := by
    rw [hchz, GalilNoShiftStage.freshWatch_eq _ _ _ _ _ h hlen]
  obtain ⟨c3, s3, w3, vs3, vq3, o3, w3', hseg, hm3, hr3, hc3, hs3, hz3, hav3, hcmp3, hmt3, hq3, ho3,
      hbroken, hmargin⟩ :=
    hcont c2 s2 hseg2 hwatch2 hm2 hr2 ho2 hlo hhi hl2 hr2' hc2 hrad2
  have hpal := pal_of_candidate a ls rs q gap span lower h hraw hc hCen
  have hcen0 : sF.center = r.center := watchSegE_center _ _ _ _ hseg0
  rw [hcen0, ← hlen] at hpal
  obtain ⟨cT, sT, k, L, hst, hcr, hIT, hcenT, hlt, hright⟩ :=
    foundRouteMC_noshift'' centre place entry qq first raw hex hI hlive hseg0 hmF hrF hcF
      havF hidle vq hq hfound hmt ch hch' hchne oF hoF hseg2 cen ys b hwatch2
      (List.count_eq_zero.2 (by simp))
      hpal.1 hpal.2 hseg hm3 hr3 hc3 w3 hs3 hz3 hav3 vs3 vq3 hcmp3 hmt3 hq3 o3 ho3 w3' hbroken hmargin
  exact ⟨cT, sT, k, L, hst, hcr, hIT, hcenT, hlt, s3, vs3, vq3, hright⟩

#print axioms reachAtC_of_2
#print axioms reachC2_from_invLPC
#print axioms cycleOracleMC_of_MC2C
#print axioms checkpoints_cost2
#print axioms invLPC_of_boot
#print axioms cycleOutMC2C_of_fallback
#print axioms cycleOutMC2C_of_found
#print axioms cycleOutMC2C_of_foundBg
#print axioms reachAtC2_of_target_match
#print axioms invScanC_of_replay_generalR
#print axioms cycleOracleMC2C_of_pieces
#print axioms foundRouteMC_noshift_dC
#print axioms h_oracle_of_leaves

end PalPeg.GalilOracleMC2
