import PalPeg.GalilOracleLocal
import PalPeg.GalilReportPrefix
import PalPeg.GalilLedgerAssembly
import PalPeg.GalilLatchTracking

/-!
# Checkpoints at every prefix along one run

`PalPeg.GalilOracleLocal.run_from_invL` drives the scaffold from an `InvL`
state to the report point of the *whole* word.  The ledger
(`PalPeg.GalilLedgerAssembly.ledgerObligation_of_oracles`, hypothesis
`O_check`) needs a refreshed report point for *every* prefix length `m`, all on
one run, at monotone times.

* `CycleOracleM` — the per-target oracle: at an `InvL` state whose right head
  has not passed the target cell `2m-1`, either reach a refreshed prefix report
  point (`ReachAt`, which also hands back an `InvL` state from which the next
  target `m+1` resumes), or run one cycle to an `InvL` state with centre
  progress and the right head still not past `2m-1`.
* `reach_from_invL` — the per-target recursion (fuel = centre measure).
* `checkpoints_upto` / `checkpoints_from_invL` — the recursion over targets,
  concatenating the segments into one trace `st : ℕ → State GalilVM`.
* `checkpoints_monotone` — checkpoint times of distinct positive prefixes are
  strictly increasing (the right head differs), with no further hypothesis.
* `O_check_of_oracleM` — the `O_check` shape of the ledger assembly.
* `O_check_of_oracleM_boot` — the same, booted at `initVM0` via the `init` tick.

Arrival throttling is **not** modelled here: the whole word is pre-loaded.
-/

set_option autoImplicit false

namespace PalPeg.GalilCheckpoints

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier
open GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton
open PalPeg.GalilOracleDischarge
open PalPeg.GalilOracleLocal

/-! ## Traces -/

/-- A concrete run of `e` ticks, as a function of time, all states satisfying `Q`. -/
structure Trace {σ : Type} (F : Frame σ) (delay : ℕ) (Q : State σ → Prop)
    (st : ℕ → State σ) (e : ℕ) : Prop where
  tick : ∀ i, i < e → Tick F delay (st i) (st (i+1))
  good : ∀ i, i ≤ e → Q (st i)

theorem stepsAll_fn {σ : Type} {F : Frame σ} {delay : ℕ} {Q : State σ → Prop} {n : ℕ}
    {x y : State σ} (h : StepsAll F delay Q n x y) :
    ∃ g : ℕ → State σ, g 0 = x ∧ g n = y ∧ Trace F delay Q g n := by
  induction h with
  | zero x hx =>
    exact ⟨fun _ => x, rfl, rfl, ⟨fun i hi => absurd hi (Nat.not_lt_zero _), fun _ _ => hx⟩⟩
  | @succ n x y z hx h _ ih =>
    obtain ⟨g, hg0, hgn, htr⟩ := ih
    refine ⟨fun i => if i = 0 then x else g (i-1), by simp, by simpa using hgn, ⟨?_, ?_⟩⟩
    · intro i hi
      rcases i with _ | i
      · simpa [hg0] using h
      · simpa using htr.tick i (by omega)
    · intro i hi
      rcases i with _ | i
      · simpa using hx
      · simpa using htr.good i (by omega)

theorem trace_le {σ : Type} {F : Frame σ} {delay : ℕ} {Q : State σ → Prop}
    {st : ℕ → State σ} {e e' : ℕ} (h : Trace F delay Q st e) (hle : e' ≤ e) :
    Trace F delay Q st e' :=
  ⟨fun i hi => h.tick i (by omega), fun i hi => h.good i (by omega)⟩

/-- Concatenation of two traces meeting at `f e = g 0`. -/
def concat {σ : Type} (f g : ℕ → State σ) (e : ℕ) : ℕ → State σ :=
  fun i => if i ≤ e then f i else g (i - e)

theorem concat_le {σ : Type} (f g : ℕ → State σ) {e i : ℕ} (hi : i ≤ e) :
    concat f g e i = f i := by
  simp [concat, hi]

theorem concat_end {σ : Type} (f g : ℕ → State σ) {e n : ℕ} (hfg : f e = g 0) :
    concat f g e (e + n) = g n := by
  by_cases hn : n = 0
  · subst hn; simp [concat, hfg]
  · have h1 : ¬ e + n ≤ e := by omega
    simp [concat, h1]

theorem trace_concat {σ : Type} {F : Frame σ} {delay : ℕ} {Q : State σ → Prop}
    {f g : ℕ → State σ} {e n : ℕ}
    (hf : Trace F delay Q f e) (hg : Trace F delay Q g n) (hfg : f e = g 0) :
    Trace F delay Q (concat f g e) (e + n) := by
  constructor
  · intro i hi
    by_cases h1 : i + 1 ≤ e
    · rw [concat_le f g h1, concat_le f g (by omega : i ≤ e)]
      exact hf.tick i h1
    · by_cases h2 : i ≤ e
      · have hie : i = e := by omega
        subst hie
        rw [concat_le f g h2, hfg]
        have h3 : concat f g i (i + 1) = g 1 := concat_end f g hfg
        rw [h3]
        exact hg.tick 0 (by omega)
      · have e1 : concat f g e i = g (i - e) := by simp [concat, h2]
        have e2 : concat f g e (i + 1) = g ((i - e) + 1) := by
          simp only [concat, h1, if_false]
          congr 1
          omega
        rw [e1, e2]
        exact hg.tick (i - e) (by omega)
  · intro i hi
    by_cases h2 : i ≤ e
    · rw [concat_le f g h2]; exact hf.good i h2
    · have e1 : concat f g e i = g (i - e) := by simp [concat, h2]
      rw [e1]; exact hg.good (i - e) (by omega)

/-! ## The per-target oracle -/

/-- Reaching the refreshed report point of the prefix `m` from `⟨c, r⟩`; if a longer
prefix remains, the run continues to an `InvL` state from which the target `m+1`
resumes (right head not past `2(m+1)-1`). -/
def ReachAt (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ)
    (c : Control) (r : GalilVM) : Prop :=
  ∃ (y : State GalilVM) (k : ℕ),
    StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ y ∧
    PalPeg.GalilReportPrefix.ReportPointAt raw m y ∧ Refreshed P q first y ∧
    (m < raw.length → ∃ (c' : Control) (r' : GalilVM) (k' : ℕ),
      StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k' y ⟨c', r'⟩ ∧
      InvL raw c' r' ∧ position r'.right ≤ 2 * (m+1) - 1)

/-- One turn toward the target `m`. -/
def CycleOutM (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ)
    (c : Control) (r : GalilVM) : Prop :=
  ReachAt P q first raw m c r ∨
    ∃ (cT : Control) (sT : GalilVM) (k : ℕ),
      StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩ ∧
      InvL raw cT sT ∧ position r.center < position sT.center ∧
      position sT.right ≤ 2 * m - 1

/-- **The per-target cycle oracle.** -/
def CycleOracleM (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) : Prop :=
  ∀ (m : ℕ) (c : Control) (r : GalilVM), 1 ≤ m → m ≤ raw.length → InvL raw c r →
    position r.right ≤ 2 * m - 1 → CycleOutM P q first raw m c r

theorem reach_fuel (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (hor : CycleOracleM P q first raw) (m : ℕ) (hm1 : 1 ≤ m) (hmle : m ≤ raw.length) :
    ∀ (n : ℕ) (c : Control) (r : GalilVM), 2 * raw.length - position r.center ≤ n →
      InvL raw c r → position r.right ≤ 2 * m - 1 → ReachAt P q first raw m c r := by
  intro n
  induction n with
  | zero =>
    intro c r hn hI hp
    rcases hor m c r hm1 hmle hI hp with hdone | ⟨cT, sT, k, _, hIT, hlt, _⟩
    · exact hdone
    · exact absurd (invS_center_le hIT.1) (by have := invS_center_le hI.1; omega)
  | succ n ih =>
    intro c r hn hI hp
    rcases hor m c r hm1 hmle hI hp with hdone | ⟨cT, sT, k, hst, hIT, hlt, hpT⟩
    · exact hdone
    · obtain ⟨y, k', hst', hrp, hfr, hcont⟩ :=
        ih cT sT (by have := invS_center_le hIT.1; omega) hIT hpT
      exact ⟨y, k + k', stepsAll_trans hst hst', hrp, hfr, hcont⟩

theorem reach_from_invL (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (hor : CycleOracleM P q first raw) {m : ℕ} (hm1 : 1 ≤ m) (hmle : m ≤ raw.length)
    {c : Control} {r : GalilVM} (hI : InvL raw c r) (hp : position r.right ≤ 2 * m - 1) :
    ReachAt P q first raw m c r :=
  reach_fuel P q first raw hor m hm1 hmle _ c r le_rfl hI hp

/-! ## The recursion over targets -/

theorem mono_of_step (Tc : ℕ → ℕ) (M : ℕ) (h : ∀ m, m < M → Tc m ≤ Tc (m+1)) :
    ∀ m m', m ≤ m' → m' ≤ M → Tc m ≤ Tc m' := by
  intro m m' hle hM
  induction m' with
  | zero => have : m = 0 := by omega
            subst this; exact le_rfl
  | succ j ih =>
    by_cases hj : m ≤ j
    · exact le_trans (ih hj (by omega)) (h j (by omega))
    · have : m = j + 1 := by omega
      subst this; exact le_rfl

theorem checkpoints_upto (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (hor : CycleOracleM P q first raw)
    {x0 : State GalilVM} {k0 : ℕ} {c : Control} {r : GalilVM}
    (hpre : StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k0 x0 ⟨c, r⟩)
    (hI : InvL raw c r) (hpos : position r.right ≤ 1) :
    ∀ M, M ≤ raw.length →
    ∃ (st : ℕ → State GalilVM) (Tc : ℕ → ℕ) (e : ℕ),
      st 0 = x0 ∧ Tc 0 = 0 ∧ Trace (galilFrameS P q first) 2048 (SoundScanNR raw) st e ∧
      (∀ m, m < M → Tc m ≤ Tc (m+1)) ∧ Tc M ≤ e ∧
      (∀ m, 1 ≤ m → m ≤ M →
        PalPeg.GalilReportPrefix.ReportPointAt raw m (st (Tc m)) ∧
        Refreshed P q first (st (Tc m))) ∧
      (M < raw.length → ∃ (c' : Control) (r' : GalilVM),
        st e = ⟨c', r'⟩ ∧ InvL raw c' r' ∧ position r'.right ≤ 2 * (M+1) - 1) := by
  intro M
  induction M with
  | zero =>
    intro _
    obtain ⟨g, hg0, hgn, htr⟩ := stepsAll_fn hpre
    refine ⟨g, fun _ => 0, k0, hg0, rfl, htr, fun m hm => absurd hm (Nat.not_lt_zero _),
      Nat.zero_le _, fun m h1 h2 => absurd h1 (by omega), fun _ => ⟨c, r, hgn, hI, by omega⟩⟩
  | succ M ih =>
    intro hM
    obtain ⟨st, Tc, e, hst0, hTc0, htr, hmono, hTcM, hchk, hres⟩ := ih (by omega)
    obtain ⟨c', r', hste, hI', hp'⟩ := hres (by omega)
    obtain ⟨y, k, hrun, hrp, hfr, hcont⟩ :=
      reach_from_invL P q first raw hor (m := M+1) (by omega) hM hI' hp'
    obtain ⟨g1, hg10, hg1k, htr1⟩ := stepsAll_fn hrun
    have hj1 : st e = g1 0 := by rw [hste, hg10]
    set st1 := concat st g1 e with hst1
    have htr1' : Trace (galilFrameS P q first) 2048 (SoundScanNR raw) st1 (e + k) :=
      trace_concat htr htr1 hj1
    have hst1y : st1 (e + k) = y := by rw [hst1, concat_end st g1 hj1, hg1k]
    -- optional continuation to the next resume state
    obtain ⟨st2, e2, htr2, hagree, hle2, hres2⟩ :
        ∃ (st2 : ℕ → State GalilVM) (e2 : ℕ),
          Trace (galilFrameS P q first) 2048 (SoundScanNR raw) st2 e2 ∧
          (∀ i, i ≤ e + k → st2 i = st1 i) ∧ e + k ≤ e2 ∧
          (M + 1 < raw.length → ∃ (c'' : Control) (r'' : GalilVM),
            st2 e2 = ⟨c'', r''⟩ ∧ InvL raw c'' r'' ∧ position r''.right ≤ 2 * (M+1+1) - 1) := by
      by_cases hlt : M + 1 < raw.length
      · obtain ⟨c'', r'', k', hrun2, hI2, hp2⟩ := hcont hlt
        obtain ⟨g2, hg20, hg2k, htr2⟩ := stepsAll_fn hrun2
        have hj2 : st1 (e + k) = g2 0 := by rw [hst1y, hg20]
        refine ⟨concat st1 g2 (e + k), e + k + k', trace_concat htr1' htr2 hj2,
          fun i hi => concat_le st1 g2 hi, by omega, fun _ => ⟨c'', r'', ?_, hI2, hp2⟩⟩
        rw [concat_end st1 g2 hj2, hg2k]
      · exact ⟨st1, e + k, htr1', fun _ _ => rfl, le_rfl, fun h => absurd h hlt⟩
    have hTcle : ∀ m, m ≤ M → Tc m ≤ e := fun m hm =>
      le_trans (mono_of_step Tc M hmono m M hm le_rfl) hTcM
    refine ⟨st2, fun m => if m ≤ M then Tc m else e + k, e2, ?_, ?_, htr2, ?_, ?_, ?_, hres2⟩
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
        have ht := hTcle m hm'
        rw [hagree _ (by omega), hst1, concat_le st g1 ht]
        exact hchk m h1 hm'
      · have hmM : m = M + 1 := by omega
        subst hmM
        simp only [hm', if_false]
        rw [hagree _ le_rfl, hst1y]
        exact ⟨hrp, hfr⟩

/-- **Checkpoints along one run.** From a sound prefix run `x0 ⇝ ⟨c, r⟩` into an
`InvL` state whose right head is at most on the first letter cell, the per-target
oracle yields one trace `st` starting at `x0` and monotone times `Tc` with
`Tc 0 = 0` and a refreshed prefix report point at `st (Tc m)` for every
`1 ≤ m ≤ |raw|`; the trace ticks soundly up to `Tc |raw|`. -/
theorem checkpoints_from_invL (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (hor : CycleOracleM P q first raw)
    {x0 : State GalilVM} {k0 : ℕ} {c : Control} {r : GalilVM}
    (hpre : StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k0 x0 ⟨c, r⟩)
    (hI : InvL raw c r) (hpos : position r.right ≤ 1) :
    ∃ (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      st 0 = x0 ∧ Tc 0 = 0 ∧
      Trace (galilFrameS P q first) 2048 (SoundScanNR raw) st (Tc raw.length) ∧
      (∀ m m', m ≤ m' → m' ≤ raw.length → Tc m ≤ Tc m') ∧
      (∀ m, 1 ≤ m → m ≤ raw.length →
        PalPeg.GalilReportPrefix.ReportPointAt raw m (st (Tc m)) ∧
        Refreshed P q first (st (Tc m))) := by
  obtain ⟨st, Tc, e, hst0, hTc0, htr, hmono, hTcM, hchk, -⟩ :=
    checkpoints_upto P q first raw hor hpre hI hpos raw.length le_rfl
  exact ⟨st, Tc, hst0, hTc0, trace_le htr hTcM, mono_of_step Tc raw.length hmono, hchk⟩

/-- **Strict monotonicity, hypothesis-free.** Checkpoints of consecutive positive
prefixes lie at distinct times: the right head sits on `2m-1` versus `2m+1`. -/
theorem checkpoints_monotone (raw : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ)
    (N : ℕ) (hmono : ∀ m m', m ≤ m' → m' ≤ N → Tc m ≤ Tc m')
    (hchk : ∀ m, 1 ≤ m → m ≤ N → PalPeg.GalilReportPrefix.ReportPointAt raw m (st (Tc m))) :
    ∀ m m', 1 ≤ m → m < m' → m' ≤ N → Tc m < Tc m' := by
  intro m m' h1 hlt hle
  rcases lt_or_eq_of_le (hmono m m' hlt.le hle) with h | h
  · exact h
  · have ha := (hchk m h1 (by omega)).atPlace
    have hb := (hchk m' (by omega) hle).atPlace
    rw [h] at ha
    omega

/-! ## The `O_check` shape of the ledger assembly -/

theorem ledgerAt_of_prefix {P : Shared} {q : ℕ} {first : Fin 9} {w : List (Fin 2)} {m : ℕ}
    {st : State GalilVM} (h : PalPeg.GalilReportPrefix.ReportPointAt w m st)
    (hfr : Refreshed P q first st) :
    PalPeg.GalilLedgerAssembly.ReportPointAt P q first w m st :=
  ⟨h.notReplaying, h.scanInv, h.centre, h.atPlace, hfr⟩

/-- **`O_check` from the per-target oracle.** Given for each nonempty `w` a sound
prefix run from an initial controller into a start state, the checkpoint
construction supplies `stOf`, `Tc` with exactly the `O_check` hypothesis of
`ledgerObligation_of_oracles`, together with the trace facts. -/
theorem O_check_of_oracleM (Pof : List (Fin 2) → Shared) (qof : List (Fin 2) → ℕ)
    (firstOf : List (Fin 2) → Fin 9)
    (hstart : ∀ w : List (Fin 2), 0 < w.length →
      ∃ (x0 : State GalilVM) (k0 : ℕ) (c : Control) (r : GalilVM),
        x0.ctl = GalilScaffoldController.initial 2048 ∧
        StepsAll (galilFrameS (Pof w) (qof w) (firstOf w)) 2048 (SoundScanNR w) k0 x0 ⟨c, r⟩ ∧
        InvL w c r ∧ position r.right ≤ 1)
    (hor : ∀ w : List (Fin 2), 0 < w.length → CycleOracleM (Pof w) (qof w) (firstOf w) w) :
    ∃ (stOf : List (Fin 2) → ℕ → State GalilVM) (Tc : List (Fin 2) → ℕ → ℕ),
      (∀ w : List (Fin 2), 0 < w.length →
        (stOf w 0).ctl = GalilScaffoldController.initial 2048 ∧
        Trace (galilFrameS (Pof w) (qof w) (firstOf w)) 2048 (SoundScanNR w) (stOf w)
          (Tc w w.length) ∧
        ∀ m m', m ≤ m' → m' ≤ w.length → Tc w m ≤ Tc w m') ∧
      (∀ w : List (Fin 2), 0 < w.length →
        Tc w 0 = 0 ∧ ∀ m, 1 ≤ m → m ≤ w.length →
          PalPeg.GalilLedgerAssembly.ReportPointAt (Pof w) (qof w) (firstOf w) w m
            (stOf w (Tc w m))) := by
  obtain ⟨xd, -⟩ := hstart [0] (by simp)
  have key : ∀ w : List (Fin 2), ∃ (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      0 < w.length →
        ((st 0).ctl = GalilScaffoldController.initial 2048 ∧
          Trace (galilFrameS (Pof w) (qof w) (firstOf w)) 2048 (SoundScanNR w) st
            (Tc w.length) ∧
          ∀ m m', m ≤ m' → m' ≤ w.length → Tc m ≤ Tc m') ∧
        (Tc 0 = 0 ∧ ∀ m, 1 ≤ m → m ≤ w.length →
          PalPeg.GalilLedgerAssembly.ReportPointAt (Pof w) (qof w) (firstOf w) w m
            (st (Tc m))) := by
    intro w
    by_cases hw : 0 < w.length
    · obtain ⟨x0, k0, c, r, hx0, hpre, hI, hpos⟩ := hstart w hw
      obtain ⟨st, Tc, hst0, hTc0, htr, hmono, hchk⟩ :=
        checkpoints_from_invL (Pof w) (qof w) (firstOf w) w (hor w hw) hpre hI hpos
      refine ⟨st, Tc, fun _ => ⟨⟨by rw [hst0]; exact hx0, htr, hmono⟩, hTc0, ?_⟩⟩
      intro m h1 h2
      obtain ⟨hrp, hfr⟩ := hchk m h1 h2
      exact ledgerAt_of_prefix hrp hfr
    · exact ⟨fun _ => xd, fun _ => 0, fun h => absurd h hw⟩
  choose stOf Tc hkey using key
  exact ⟨stOf, Tc, fun w hw => (hkey w hw).1, fun w hw => (hkey w hw).2⟩

/-! ## Booted at `initVM0` -/

/-- `inv_init` with the right head position of the landing exposed (`= 1`). -/
theorem inv_init_pos (onLetter leftFirst : GalilVM → Prop) (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (s0 : GalilVM) (a : Fin 2) (rest : List (Fin 2))
    (h0 : s0.right = initialHead (a :: rest))
    (hrad : s0.radius = reset) (hlen : s0.length = reset)
    (hrepl : s0.replay = reset) (hsi : ShiftIdle s0) :
    ∃ (c1 : Control) (t : GalilVM),
      StepsAll (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) 2048
        (SoundScanNR (a :: rest)) 1 ⟨initial 2048, s0⟩ ⟨c1, t⟩ ∧
      Inv (a :: rest) c1 t ∧ position t.right = 1 := by
  obtain ⟨t, hst, hR, hpos, -, hRt, hrem, hrp⟩ :=
    init_stepsAll onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' (restartVM entry)
      centre place entry q first 2048 (initial 2048) rfl s0 a rest h0 hrad hlen
  have hMt : MInv (a :: rest) {(initial 2048) with mode := .scan, output := true} t := by
    refine minv_of_leftmost ?_ rfl
    rw [hRt, hpos]
    exact leftmost_one a rest
  have htrp : t.replay = reset := by rw [hrp, hrepl]
  refine ⟨_, t, hst, inv_of_parts hR hMt ⟨rfl, rfl, rfl⟩ (frontier_of_reset htrp)
    (replayRest_of_reset htrp) ?_, by rw [hRt, hpos]⟩
  rw [shiftIdle_iff, hrem]
  exact (shiftIdle_iff s0).1 hsi

/-- **`O_check` for the concrete scaffold**, booted at `initVM0` through the `init`
tick, from the per-target oracle alone. -/
theorem O_check_of_oracleM_boot (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (hor : ∀ w : List (Fin 2), 0 < w.length →
      CycleOracleM (PofC centre place entry w) q first w) :
    ∃ (stOf : List (Fin 2) → ℕ → State GalilVM) (Tc : List (Fin 2) → ℕ → ℕ),
      (∀ w : List (Fin 2), 0 < w.length →
        (stOf w 0).ctl = GalilScaffoldController.initial 2048 ∧
        Trace (galilFrameS (PofC centre place entry w) q first) 2048 (SoundScanNR w) (stOf w)
          (Tc w w.length) ∧
        ∀ m m', m ≤ m' → m' ≤ w.length → Tc w m ≤ Tc w m') ∧
      (∀ w : List (Fin 2), 0 < w.length →
        Tc w 0 = 0 ∧ ∀ m, 1 ≤ m → m ≤ w.length →
          PalPeg.GalilLedgerAssembly.ReportPointAt (PofC centre place entry w) q first w m
            (stOf w (Tc w m))) := by
  refine O_check_of_oracleM (PofC centre place entry) (fun _ => q) (fun _ => first) ?_ hor
  intro w hw
  rcases w with _ | ⟨a, rest⟩
  · simp at hw
  · obtain ⟨c1, t, hst, hI, hpos⟩ :=
      inv_init_pos (onLetterVM (a :: rest)) leftFirstVM centre place entry q first
        (PalPeg.GalilBootVM.initVM0 (a :: rest)) a rest
        (PalPeg.GalilBootVM.initVM0_right _) (PalPeg.GalilBootVM.initVM0_radius _)
        (PalPeg.GalilBootVM.initVM0_length _) (PalPeg.GalilBootVM.initVM0_replay _)
        (PalPeg.GalilBootVM.initVM0_shiftIdle _)
    exact ⟨_, 1, c1, t, rfl, hst, invL_of_run hst (invS_of_inv hI), by omega⟩

#print axioms stepsAll_fn
#print axioms trace_le
#print axioms concat_le
#print axioms concat_end
#print axioms trace_concat
#print axioms reach_fuel
#print axioms reach_from_invL
#print axioms mono_of_step
#print axioms checkpoints_upto
#print axioms checkpoints_from_invL
#print axioms checkpoints_monotone
#print axioms ledgerAt_of_prefix
#print axioms O_check_of_oracleM
#print axioms inv_init_pos
#print axioms O_check_of_oracleM_boot

end PalPeg.GalilCheckpoints
