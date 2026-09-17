import PalPeg.CloseoutPreload23

/-!
# `PostRun` in the machine's own clock phase

`CloseoutPreload17` §3 (1) records why `CloseoutPreload17.PostRunP` cannot be fed
by its own consumers: the pacing premise `PacedL 2048 slack as` is handed the
slack `(bs ++ [a]).length`, while every budget lemma
(`CloseoutPreload16.runP_exit_debt_at_exit_take`) wants `slack ≤ 2047`.  The
list-level `PacedL` cannot be sharpened; the true local slack is the machine's
*clock phase*, and `CloseoutPreload18.PrefixPhase` is its list shadow.
`CloseoutPreload21` / `CloseoutPreload23` supply exactly that shadow from the
controller itself (`prefixPhase_of_scan_inv`: a scan leg entered in phase and
under an input-supply invariant has a phase-bounded event list).

* §1 `PostRunC` — `PostRunP` with the pacing premise replaced by the machine
  datum: the events charged to the stage's preparation form a `ScanTrace`
  (`CloseoutPreload21`) of a frame carrying a `ScanSupplyInv`
  (`CloseoutPreload23`), entered at a clock satisfying
  `CloseoutPreload22.ClockInv 2048`.  `postRunC_of_postRunP` shows it is weaker,
  and §1 re-exports the whole consumption chain of `CloseoutPreload17` §1 on
  `PostRunC` — `runEntriesS_of_stageInv2C` / `runEntriesS_of_restartS2C` /
  `readyClosure_S2C` / `replay_final_of_decodes_S2C` /
  `runEntriesS_of_stageInvPPC` / `runEntriesS_of_double_exitC` — so the
  substitution `PostRunP ↝ PostRunC` costs the consumers nothing beyond the
  realizability clause `ScanRealized` (a `StagePrep2` preparation prefix really
  is a scan leg; the constructors of `CloseoutPreload21.ScanTrace` are the three
  `.scan` `Tick` branches, so this is a statement about `GalilScaffoldTopScan`,
  not about `PacedL`).
* §2 the machine composition: `runP_exit_debt_at_exit_scan` discharges the
  `slack ≤ 2047` side condition of `CloseoutPreload16` from the clock phase —
  residue 1 of `CloseoutPreload17` §3, closed — and `round_trip_entries` chains
  `CloseoutPreload14.wait_exit_double` → `CloseoutPreload17.double_spends` →
  `CloseoutPreload18.double_exit_debt_bound` into the next stage's
  `RunEntriesS`, on `PostRunC`.
* §3 records what `postRunC_of_machine` still needs.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPreload24

open PalPeg PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController
open PalPeg.GalilScaffoldSearchFinish (Mode)
open PalPeg.GalilScaffoldCounter (Counter Canonical value ofNat positive reset zero zero_iff)
open PalPeg.CloseoutReadyStage (DpSafeStage PacedL RunEntriesS)
open PalPeg.CloseoutPreload (RdPaced rdPaced_ready rdPaced_seg rdPaced_restart)
open PalPeg.CloseoutDebtAudit (dpEvents stageWindow1)
open PalPeg.CloseoutPreload5 (append_cons_eq)
open PalPeg.CloseoutPreload6 (prepLen)
open PalPeg.CloseoutPreload8 (BeginAt CentreLongAt DepthAt beginAt_of_restarted)
open PalPeg.CloseoutPreload10 (PrepAt prepAt_of_double_exit)
open PalPeg.CloseoutPreload11 (StagePrep2 StageInv2 stagePrep_next2 stageCredit
  dpSafe_of_stagePrep2 RestartS2 stageStart_of_double_exit)
open PalPeg.CloseoutPreload12 (dpSafe_of_stagePrepP)
open PalPeg.CloseoutPreload13 (RunTrace)
open PalPeg.CloseoutPreload14 (WaitTrace wait_step_cases wait_exit_double)
open PalPeg.CloseoutPreload16 (runP_exit_debt_at_exit_take)
open PalPeg.CloseoutPreload17 (PostRunP DoubleTrace double_spends double_exit_canonical)
open PalPeg.CloseoutPreload18 (PrefixPhase pacedL_suffix_2047 double_exit_debt_bound)
open PalPeg.CloseoutPreload21 (ScanTrace)
open PalPeg.CloseoutPreload22 (ClockInv)
open PalPeg.CloseoutPreload23 (ScanSupplyInv prefixPhase_of_scan_inv)
open PalPeg.GalilReplaySpan (stageDebt)

/-! ## 1. `PostRun` with the clock phase as its premise -/

/-- **NAMED — the clock-phase post-run contract.**  `CloseoutPreload17.PostRunP`
with the pacing premise `PacedL 2048 slack as` replaced by the machine datum it
is supposed to abbreviate: the preparation prefix `bs` of the stage is the event
list of a scan leg of the controller (`CloseoutPreload21.ScanTrace`), run under
an input-supply invariant (`CloseoutPreload23.ScanSupplyInv`) and entered at a
clock in phase (`CloseoutPreload22.ClockInv 2048`), and the whole stream
`bs ++ as` is paced from phase `0`.  Unlike `PostRunP` this carries the *clock*,
so the slack of the suffix is `≤ 2047` by `CloseoutPreload18.pacedL_suffix_2047`
rather than `bs.length` — residue 1 of `CloseoutPreload17` §3. -/
def PostRunC : Prop :=
  ∀ {σ : Type} {F : Frame σ} {I : State σ → Prop}, ScanSupplyInv F 2048 I →
    ∀ {ts bs : List Bool} {p q : State σ}, ScanTrace F 2048 ts bs p q → I p →
      ClockInv 2048 p.ctl →
      ∀ (v : SearchVM) (as : List Bool), v.search.mode = Mode.run →
        DpSafeStage v as → PacedL 2048 0 (bs ++ as) → RunEntriesS as v

/-- `PostRunP` is stronger: it accepts any slack, in particular `2047`. -/
theorem postRunC_of_postRunP (h : PostRunP) : PostRunC :=
  fun {_ _ _} hsup {_ _ _ _} hsc hp hcl v as hm hsafe hpaced =>
    h v as 2047 hm hsafe
      (pacedL_suffix_2047 hpaced (prefixPhase_of_scan_inv hsup hsc hp hcl.1 hcl.2))

#print axioms postRunC_of_postRunP

section Consumers

variable {σ : Type} {F : Frame σ} {I : State σ → Prop}

/-- **NAMED — the realizability clause.**  Every preparation prefix a
`StagePrep2` stage walks is the event list of a scan leg of the controller,
entered in phase and under the supply invariant.  This is the one interface
obligation the substitution `PostRunP ↝ PostRunC` adds; it is a statement about
`GalilScaffoldTopScan` (the coupling between `searchStep`'s boolean and the
`Tick` branch taken), listed as open in `CloseoutPreload21` §4. -/
def ScanRealized (F : Frame σ) (I : State σ → Prop) : Prop :=
  ∀ bs : List Bool, ∃ (ts : List Bool) (p q : State σ),
    ScanTrace F 2048 ts bs p q ∧ I p ∧ ClockInv 2048 p.ctl

/-- `CloseoutPreload17.runEntriesS_of_stageInv2P`, on `PostRunC`. -/
theorem runEntriesS_of_stageInv2C {u : GalilVM} {w : SearchVM} {k m Rad D : ℕ}
    (hb : BeginAt k Rad w) (hm : m = 8 * max k 1) (hstage : 3 * Rad ≤ 5 * k)
    (hcl : CentreLongAt w k) (hdep : DepthAt w D) (hD : D ≤ prepLen k)
    (hsup : ScanSupplyInv F 2048 I) (hreal : ScanRealized F I) (hpost : PostRunC) :
    ∀ (as : List Bool) (v : SearchVM), StageInv2 k m D w v as → RunEntriesS as v := by
  intro as
  induction as with
  | nil => intro v _; trivial
  | cons a as ih =>
    intro v hq
    rcases hq with hq | hq
    · intro c v' hstep
      by_cases hr : v'.search.mode = Mode.run
      · have hsafe := dpSafe_of_stagePrep2 (u := u) hb hm hstage hcl hdep hD hq hstep hr
        obtain ⟨bs, -, -, hpaced⟩ := hq
        have hpaced' : PacedL 2048 0 ((bs ++ [a]) ++ as) := by
          rw [← append_cons_eq]; exact hpaced
        obtain ⟨ts, p, q, hsc, hp, hclk⟩ := hreal (bs ++ [a])
        exact ⟨fun _ _ _ => hsafe, hpost hsup hsc hp hclk v' as hr hsafe hpaced'⟩
      · exact ⟨fun _ _ h => absurd h hr,
          ih v' (Or.inl (stagePrep_next2 hq hstep hr))⟩
    · exact hq

#print axioms runEntriesS_of_stageInv2C

/-- `CloseoutPreload17.runEntriesS_of_restartS2P`, on `PostRunC`. -/
theorem runEntriesS_of_restartS2C {raw : List (Fin 2)} {u : GalilVM} {Rad D : ℕ}
    {last : Counter} (hR : Restarted raw u Rad last) (hSE : StageEntry Rad last)
    (hcl : CentreLongAt (searchLens.get u) (value last).toNat)
    (hdep : DepthAt (searchLens.get u) D) (hD : D ≤ prepLen (value last).toNat)
    (hsup : ScanSupplyInv F 2048 I) (hreal : ScanRealized F I) (hpost : PostRunC) :
    ∀ (as : List Bool),
      D + dpEvents (8 * max (value last).toNat 1 + 1) ≤ as.length → PacedL 2048 0 as →
      RunEntriesS as (searchLens.get u) := by
  have hval : value last = ((value last).toNat : ℤ) :=
    (Int.toNat_of_nonneg hR.2.2.2.2.2.2.2.2.2).symm
  have hstage : 3 * Rad ≤ 5 * (value last).toNat := hSE _ hval
  intro as hlen hpaced
  refine runEntriesS_of_stageInv2C (u := u) (beginAt_of_restarted hR) rfl hstage hcl hdep hD
    hsup hreal hpost as _ (Or.inl ⟨[], .nil _ ?_, by simpa using hlen, by simpa using hpaced⟩)
  rw [(PalPeg.CloseoutPreload5.restart_facts hR).1]
  decide

#print axioms runEntriesS_of_restartS2C

/-- **`GalilReplaySpan.ReadyClosure` for `RdPaced`, on `PostRunC`.** -/
theorem readyClosure_S2C (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9)
    (hsup : ScanSupplyInv F 2048 I) (hreal : ScanRealized F I) (hpost : PostRunC)
    (h : RestartS2 raw) :
    PalPeg.GalilReplaySpan.ReadyClosure raw P q first 2048 RdPaced where
  ready := fun c s hs => rdPaced_ready c s hs
  seg := fun es c c' s t hseg hidle hs => rdPaced_seg P q first es c c' s t hseg hidle hs
  restart := fun c u Rad last _ hclk hR hSE => by
    obtain ⟨D, hD, hcl, hdep⟩ := h u Rad last hR hSE
    exact rdPaced_restart c u Rad last
      (D + dpEvents (8 * max (value last).toNat 1 + 1)) hclk hR
      (fun m as hlen hp =>
        runEntriesS_of_restartS2C hR hSE hcl hdep hD hsup hreal hpost as (by omega) hp)

#print axioms readyClosure_S2C

/-- The final replay theorem, on `PostRunC`. -/
def replay_final_of_decodes_S2C (raw : List (Fin 2)) (P : Shared)
    (hP : P.onLetter = onLetterVM raw) (hP' : P.leftFirst = leftFirstVM)
    (q : ℕ) (first : Fin 9)
    (hex : ∀ s, P.replayExhausted s = GalilScaffoldCounter.zero s.replay)
    (hsearch : ∀ s : GalilVM, PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get s) →
      ∀ a : Bool, ∃ v, searchEffect P a s v)
    (hsup : ScanSupplyInv F 2048 I) (hreal : ScanRealized F I) (hpost : PostRunC)
    (hS : RestartS2 raw)
    (hdec : Decodes P)
    (hbudget : PalPeg.GalilReplaySpan.ReplayBudgetRD raw P q first 2048)
    (hrs : PalPeg.GalilReplaySpan.RestartShapeL P)
    (r : ℕ) (hr0 : 0 < r) (c : Control) (t : GalilVM)
    (hm : c.mode = Mode.scan) (hc : c.clock = 2048) (hrpl : c.replaying = true)
    (hR : Restarted raw t 0 GalilScaffoldCounter.reset) (hrep : t.replay = ofNat r)
    (hM : MInv raw c t) (hfr : Frontier t) (hsi : ShiftIdle t) :=
  PalPeg.GalilReplaySpan.replay_after_fallback_general''_R_of_decodes
    raw P hP hP' q first hex hsearch (readyClosure_S2C raw P q first hsup hreal hpost hS)
    hdec hbudget hrs r hr0 c t hm hc hrpl hR hrep hM hfr hsi

#print axioms replay_final_of_decodes_S2C

/-- `CloseoutPreload17.runEntriesS_of_stageInvPP`, on `PostRunC`. -/
theorem runEntriesS_of_stageInvPPC {k m Rad D : ℕ} {v : SearchVM}
    (hp : PrepAt k m v) (hstage : 3 * Rad ≤ 5 * k) (hcal : 8 * max k 1 ≤ m)
    (hE : stageDebt Rad (k : ℤ) + (stageCredit k m : ℤ) ≤ value v.search.debt)
    (hdep : DepthAt v D) (hD : D ≤ prepLen k)
    (hsup : ScanSupplyInv F 2048 I) (hreal : ScanRealized F I) (hpost : PostRunC) :
    ∀ (as : List Bool) (x : SearchVM), StageInv2 k m D v x as → RunEntriesS as x := by
  intro as
  induction as with
  | nil => intro x _; trivial
  | cons a as ih =>
    intro x hq
    rcases hq with hq | hq
    · intro c x' hstep
      by_cases hr : x'.search.mode = Mode.run
      · have hsafe := dpSafe_of_stagePrepP hp hstage hcal hE hdep hD hq hstep hr
        obtain ⟨bs, -, -, hpaced⟩ := hq
        have hpaced' : PacedL 2048 0 ((bs ++ [a]) ++ as) := by
          rw [← append_cons_eq]; exact hpaced
        obtain ⟨ts, p, q', hsc, hp', hclk⟩ := hreal (bs ++ [a])
        exact ⟨fun _ _ _ => hsafe, hpost hsup hsc hp' hclk x' as hr hsafe hpaced'⟩
      · exact ⟨fun _ _ h => absurd h hr, ih x' (Or.inl (stagePrep_next2 hq hstep hr))⟩
    · exact hq

#print axioms runEntriesS_of_stageInvPPC

/-- `CloseoutPreload17.runEntriesS_of_double_exitP`, on `PostRunC`. -/
theorem runEntriesS_of_double_exitC {c : GalilScaffoldPlace.Place} {t t' : SearchVM}
    {a : Bool} {k m Rad D : ℕ}
    (htm : t.search.mode = Mode.double)
    (htw : positive t.search.work = false)
    (hsp : t.search.span = ofNat m) (hlow : t.lower = ofNat k)
    (hcal : 8 * max k 1 ≤ m) (hc : Canonical t.search.debt)
    (hstage : 3 * Rad ≤ 5 * k)
    (hE : stageDebt Rad (k : ℤ) + (stageCredit k m : ℤ) + 1 ≤ value t.search.debt)
    (hs : searchStep c a t t')
    (hdep : DepthAt t' D) (hD : D ≤ prepLen k)
    (hsup : ScanSupplyInv F 2048 I) (hreal : ScanRealized F I) (hpost : PostRunC) :
    ∀ (as : List Bool),
      D + dpEvents (m + 1) ≤ as.length → PacedL 2048 0 as → RunEntriesS as t' := by
  have hst := stageStart_of_double_exit (E := stageDebt Rad (k : ℤ) + (stageCredit k m : ℤ))
    htm htw hsp hlow hcal hc hE hs
  obtain ⟨hprep, -, -⟩ := prepAt_of_double_exit htm htw hsp hlow hc hs
  intro as hlen hpaced
  refine runEntriesS_of_stageInvPPC hprep hstage hcal hst.debt hdep hD hsup hreal hpost as _
    (Or.inl ⟨[], .nil _ ?_, by simpa using hlen, by simpa using hpaced⟩)
  rw [hprep.mode]; decide

#print axioms runEntriesS_of_double_exitC

/-! ## 2. The machine composition -/

/-- **NAMED — the slack normalisation, from the clock.**  Residue 1 of
`CloseoutPreload17` §3: `CloseoutPreload16.runP_exit_debt_at_exit_take` asks for
`slack ≤ 2047`; the scan leg of the controller supplies exactly that, because its
event list is phase-bounded (`CloseoutPreload23.prefixPhase_of_scan_inv`) and
`CloseoutPreload18.pacedL_suffix_2047` rounds the suffix's slack to `2047`.  No
appeal to `PacedL` alone is made. -/
theorem runP_exit_debt_at_exit_scan {Rad k m : ℕ} {as as0 bs rest ts : List Bool}
    {p q : State σ} {v t t' : SearchVM} {c : GalilScaffoldPlace.Place} {a : Bool}
    {w : List (Fin 3)} {lower : ℕ}
    (hsup : ScanSupplyInv F 2048 I) (hsc : ScanTrace F 2048 ts bs p q) (hp : I p)
    (hclk : ClockInv 2048 p.ctl)
    (hdp : v.dp = ⟨GalilScaffoldPreload.initial w lower, false⟩)
    (hm : v.search.mode = Mode.run)
    (hw : w.length ≤ stageWindow1 k)
    (hsupply : dpEvents (stageWindow1 k) ≤ as0.length)
    (hc : Canonical v.search.debt)
    (hpaced : PacedL 2048 0 (bs ++ as0))
    (hdebt : (((2047 + dpEvents (stageWindow1 k)) / 2048 + 1 : ℕ) : ℤ)
      ≤ value v.search.debt)
    (hr : RunTrace as v t) (hmt : t.search.mode = Mode.run)
    (hpref : as ++ rest = as0)
    (hs : searchStep c a t t')
    (hpa : PacedL 2048 2047 (as ++ [a]))
    (hstage : 3 * Rad ≤ 5 * k)
    (hE : 2 * stageDebt Rad (k : ℤ) + (stageCredit k (2 * m) : ℤ) + 1
      ≤ value v.search.debt) :
    stageDebt Rad (k : ℤ) + (stageCredit k (2 * m) : ℤ) + 1 ≤ value t'.search.debt :=
  runP_exit_debt_at_exit_take (m := m) (by omega) hdp hm hw hsupply hc
    (pacedL_suffix_2047 hpaced (prefixPhase_of_scan_inv hsup hsc hp hclk.1 hclk.2))
    hdebt hr hmt hpref hs hpa hstage hE

#print axioms runP_exit_debt_at_exit_scan

end Consumers

/-- **NAMED — the `.wait` exit leaves the debt at zero.**  `wait_step_cases`
enters `.double` only when the debt has already fired (`zero debt = true`), and
the entering tick is a background tick, so no further unit is spent. -/
theorem wait_exit_debt_zero {c : GalilScaffoldPlace.Place} {v v' : SearchVM}
    (hm : v.search.mode = Mode.wait) (hz : zero v.search.debt = true)
    (hcan : Canonical v.search.debt) (hs : searchStep c false v v') :
    value v'.search.debt = 0 := by
  obtain ⟨-, -, hd, -⟩ := wait_step_cases hm hs
  rw [hd, (zero_iff _ hcan).mp hz]
  simp

#print axioms wait_exit_debt_zero

section RoundTrip

variable {σ : Type} {F : Frame σ} {I : State σ → Prop}

/-- **NAMED — `CloseoutPreload18.double_leg_entries_window`, on `PostRunC`. -/
theorem double_leg_entries_windowC {c' : GalilScaffoldPlace.Place} {k Rad D mw : ℕ}
    {a : Bool} {bs : List Bool} {v t t' : SearchVM}
    (hr : DoubleTrace bs v t)
    (hv0 : value v.search.debt = 0) (hq : v.search.quarter = 0)
    (hvc : Canonical v.search.debt)
    (htm : t.search.mode = Mode.double) (htw : positive t.search.work = false)
    (hts : t.search.span = ofNat (2 * mw)) (htl : t.lower = ofNat k)
    (hcal : 8 * max k 1 ≤ 2 * mw) (hstage : 3 * Rad ≤ 5 * k)
    (hlen : 4 * (stageDebt Rad (k : ℤ) + (stageCredit k (2 * mw) : ℤ) + 1)
        + 4 * ((bs.count true : ℕ) : ℤ) + 3 ≤ ((bs.length : ℕ) : ℤ))
    (hs : searchStep c' a t t') (hdep : DepthAt t' D) (hD : D ≤ prepLen k)
    (hsup : ScanSupplyInv F 2048 I) (hreal : ScanRealized F I) (hpost : PostRunC) :
    ∀ (as : List Bool),
      D + dpEvents (2 * mw + 1) ≤ as.length → PacedL 2048 0 as → RunEntriesS as t' :=
  runEntriesS_of_double_exitC htm htw hts htl hcal
    (double_exit_canonical hr htm htw hvc) hstage
    (double_exit_debt_bound (E := stageDebt Rad (k : ℤ) + (stageCredit k (2 * mw) : ℤ))
      hr htm htw hv0 hq hlen)
    hs hdep hD hsup hreal hpost

#print axioms double_leg_entries_windowC

/-- **NAMED — the `.run` → `.wait` → `.double` → `prepare` round trip, on
`PostRunC`.**  The `.wait` leg exits into `.double` carrying its window
(`CloseoutPreload14.wait_exit_double`) with the debt spent
(`wait_exit_debt_zero`); the `.double` leg then runs `work` down to zero in
exactly `mw` ticks with the doubled window in `span`
(`CloseoutPreload17.double_spends`); and the state it leaves dispatches into the
next `(k, 2 * mw)` stage, whose every later `.run` entry carries a `DpSafeStage`
witness.  The only numeric input is the `.double` leg's own length inequality,
which `CloseoutPreload18.double_exit_debt_bound` converts into the exit debt. -/
theorem round_trip_entries {cw : GalilScaffoldPlace.Place} {k mw : ℕ}
    {es bs : List Bool} {v t t0 : SearchVM}
    (hsp : v.search.span = ofNat mw) (hlow : v.lower = ofNat k)
    (hw : WaitTrace es v t) (hmt : t.search.mode = Mode.wait)
    (hz : zero t.search.debt = true) (hcan : Canonical t.search.debt)
    (hs : searchStep cw false t t0) (hne : t0.search.mode ≠ Mode.wait)
    (hcan0 : Canonical t0.search.debt) (hq0 : t0.search.quarter = 0)
    (hblen : bs.length = mw)
    (hsup : ScanSupplyInv F 2048 I) (hreal : ScanRealized F I) (hpost : PostRunC) :
    ∃ t1 : SearchVM, DoubleTrace bs t0 t1 ∧ t1.search.mode = Mode.double ∧
      positive t1.search.work = false ∧ t1.search.span = ofNat (2 * mw) ∧
      t1.lower = ofNat k ∧
      ∀ (Rad D : ℕ) (c' : GalilScaffoldPlace.Place) (a : Bool) (t' : SearchVM),
        8 * max k 1 ≤ 2 * mw → 3 * Rad ≤ 5 * k →
        4 * (stageDebt Rad (k : ℤ) + (stageCredit k (2 * mw) : ℤ) + 1)
            + 4 * ((bs.count true : ℕ) : ℤ) + 3 ≤ ((bs.length : ℕ) : ℤ) →
        searchStep c' a t1 t' → DepthAt t' D → D ≤ prepLen k →
        ∀ as : List Bool,
          D + dpEvents (2 * mw + 1) ≤ as.length → PacedL 2048 0 as → RunEntriesS as t' := by
  obtain ⟨hdm, hdw, hdsp, -, hdl, -⟩ := wait_exit_double hsp hw hmt hs hne
  have hd0 : value t0.search.debt = 0 := wait_exit_debt_zero hmt hz hcan hs
  obtain ⟨t1, hr, h1m, h1w, h1s, h1l, -, -⟩ :=
    double_spends cw hdm hdw hdsp hblen
  refine ⟨t1, hr, h1m, h1w, h1s, by rw [h1l, hdl, hlow], ?_⟩
  intro Rad D c' a t' hcal hstage hlen hstep hdep hD
  exact double_leg_entries_windowC hr hd0 hq0 hcan0 h1m h1w h1s
    (by rw [h1l, hdl, hlow]) hcal hstage hlen hstep hdep hD hsup hreal hpost

#print axioms round_trip_entries

end RoundTrip

/-!
## 3. What is left

Closed here:

* **§1 — the `PostRunP ↝ PostRunC` substitution.**  The whole consumption chain
  of `CloseoutPreload17` §1 goes through with the pacing premise replaced by the
  controller datum (`ScanTrace` + `ScanSupplyInv` + `ClockInv 2048`), at the
  price of the realizability clause `ScanRealized` — which is exactly the
  interface obligation `CloseoutPreload21` §4 already lists (the coupling
  between `searchStep`'s boolean and the `Tick` branch, in
  `GalilScaffoldTopScan`).  `postRunC_of_postRunP` shows `PostRunC` is the
  weaker contract, so proving *it* is strictly easier than proving `PostRunP`.
* **residue 1 of `CloseoutPreload17` §3, closed.**
  `runP_exit_debt_at_exit_scan` discharges the `slack ≤ 2047` side condition of
  `CloseoutPreload16.runP_exit_debt_at_exit_take` from the machine's clock phase
  alone: `prefixPhase_of_scan_inv` gives `PrefixPhase bs` for the preparation
  prefix of a scan leg, and `pacedL_suffix_2047` rounds the suffix's slack.  The
  `PacedL`-only route (`CloseoutPreload5.pacedL_suffix`, slack `bs.length`) is
  no longer used anywhere in this chain.
* **the round trip.**  `round_trip_entries` chains `wait_exit_double` →
  `wait_exit_debt_zero` → `double_spends` → `double_exit_debt_bound` →
  `runEntriesS_of_double_exitC`, so a `.wait` leg that fires reaches the next
  `(k, 2 * mw)` stage with its `RunEntriesS` ledger, on `PostRunC`.

**NOT closed — `postRunC_of_machine` is not proved here.**  §2 gives every leg
of one round trip, but `PostRunC` asserts the ledger for *all* later `.run`
entries, i.e. for the whole tail of stages, so its proof is an induction on the
event list whose step is §2.  Three inputs are still missing for that induction:

1. **The `.double` leg's length inequality** (`hlen` of
   `double_leg_entries_windowC`, `4 * (stageDebt + stageCredit + 1) + 4 * count
   + 3 ≤ mw`).  `double_spends` fixes the leg's length at exactly `mw`, and the
   pacing bounds `bs.count true` by `mw / 2048 + 1`, so this is a purely numeric
   obligation on `stageCredit k (2 * mw)` against the calibration
   `8 * max k 1 ≤ 2 * mw` — but it is not discharged here.
2. **The `.wait` leg's budget.**  `CloseoutPreload23.wait_leg_length_le_of_scan_inv`
   now bounds the leg by `2048 * (debt + 1)` ticks — residue 2 of
   `CloseoutPreload17` §3, available at last — but nothing yet converts that
   bound into the *next* stage's `DepthAt` / event-supply clause, which is what
   the induction's step needs to re-enter §1.
3. **`ScanRealized` itself**, for the concrete frame: on `galilFrameS` the
   supply invariant is `CloseoutPreload23.bigPack2_scanSupply`, but the leg
   construction (that a stage's preparation prefix *is* a `ScanTrace`) is still
   the `GalilScaffoldTopScan` coupling.

**無条件 PAL ∈ PEG は未完.**
-/

end PalPeg.CloseoutPreload24
