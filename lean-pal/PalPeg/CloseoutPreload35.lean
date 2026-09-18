import PalPeg.CloseoutPreload34

/-!
# From the dispatch to the next `.run` entry — `postRunF_next_entry`, `postRunF_step`

`CloseoutPreload34.postRunF_round_trip_galil'` ends at the dispatch tick into
`prepare` with `PrepAt k (2mw) ∧ StageInvD k (2mw)` on the search projection.
`CloseoutPreload31` §3 lists what is missing before the next `.run` entry: the
preparation walk `CloseoutPreload28.dpSafe_of_stagePrepD` measures its pacing
from the `prepare` entry at slack `0`, while only slack `≤ 2047` is available
there; and the next entry needs the `PostRunF` datum again.

* §1 pacing at a slack: `pacedL_prefix_count_slack`, `pacedL_suffix_slack'`,
  `pacedL_prefix_of_append`.
* §2 **`dpSafe_of_stagePrepD_slack`** — `dpSafe_of_stagePrepD` restated with the
  preparation stream paced at any slack `≤ 2047`.  The demand grows by at most
  two units (`dpDemandS k m := (prepLen k + 2047)/2048 +
  (prepLen k + 2047 + dpEvents (m+1))/2048 + 1`, invariant `StageInvS`).
* §3 the `.double` exit satisfies `StageInvS` when `16 ≤ mw`
  (`bal_of_paced_slack_S`, `stageInvS_of_double_exit`); the windows
  `4 ≤ mw ≤ 15` do not absorb the two extra units at slack `2047`.
* §4 `postRunF_round_trip_S` / `postRunF_round_trip_galil_S` — the round trip
  of `CloseoutPreload31`/`34` with `StageInvS` at the dispatch.
* §5 **`postRunF_next_entry`** — from the dispatch state, through an idle
  preparation leg and the entry tick, the `PostRunF` datum at the next `.run`
  entry: `span = ofNat m`, `lower = ofNat k`, calibration, `Canonical`,
  `DpSafeStage`, and the `ScanTrace` over the extended stream.
* §6 **`postRunF_step`** — the datum at one `.run` entry gives the datum at the
  next, on `galilFrameS`, the `.double` leg and the dispatch also read off the
  machine run (`idleLeg_doubleTrace`, `doubleTrace_det`).

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPreload35

open PalPeg PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController
open PalPeg.GalilScaffoldSearchFinish (Mode)
open PalPeg.GalilScaffoldCounter (Canonical value ofNat positive zero reset)
open PalPeg.CloseoutReadyStage (DpSafeStage PacedL RunEntriesS)
open PalPeg.CloseoutDebtAudit (dpEvents)
open PalPeg.CloseoutPreload (run_entry_preload)
open PalPeg.CloseoutPreload5 (ReachP reachP_ne_run append_cons_eq ofPrep_span afterAdvance_span
  toPrep_span)
open PalPeg.CloseoutPreload6 (prepLen prepLen_le)
open PalPeg.CloseoutPreload8 (DepthAt)
open PalPeg.CloseoutPreload9 (dpEvents_mono)
open PalPeg.CloseoutPreload10 (PrepAt prepAt_of_double_exit dpSafeStage_entry_real)
open PalPeg.CloseoutPreload11 (dpEvents_win_le)
open PalPeg.CloseoutPreload12 (entry_preload_at_prep entry_debt_at_prep phase_reach_at_prep
  phaseP_mode4)
open PalPeg.CloseoutPreload13 (RunTrace run_exit_frame)
open PalPeg.CloseoutPreload14 (WaitTrace wait_step_cases wait_exit_double)
open PalPeg.CloseoutPreload17 (DoubleTrace double_spends double_exit_canonical double_step_pos)
open PalPeg.CloseoutPreload18 (pacedL_suffix_2047 double_exit_debt_ge)
open PalPeg.CloseoutPreload21 (ScanTrace)
open PalPeg.CloseoutPreload22 (ClockInv)
open PalPeg.CloseoutPreload23 (ScanSupplyInv prefixPhase_of_scan_inv)
open PalPeg.CloseoutPreload24 (wait_exit_debt_zero)
open PalPeg.CloseoutPreload28 (dpDemand StageInvD)
open PalPeg.CloseoutPreload32 (canonical_runTrace canonical_run_step canonical_wait_step
  canonical_waitTrace)
open PalPeg.CloseoutPreload33 (RestartOnBroken IdleLeg scanTrace_single_searchStep
  idleLeg_runTrace idleLeg_waitTrace scanTrace_append idleLeg_scanTrace
  scanTrace_single_false_of_clock legsCoupled_galil)
open PalPeg.CloseoutPreload34 (exitNotFire_of_wait)

/-! ## 1. Pacing at a slack -/

theorem pacedL_prefix_count_slack {d slack : ℕ} {bs as : List Bool}
    (h : PacedL d slack (bs ++ as)) : d * bs.count true ≤ bs.length + slack := by
  have h2 := h bs.length
  rw [List.take_left] at h2
  exact h2

theorem pacedL_suffix_slack' {d slack : ℕ} {bs as : List Bool}
    (h : PacedL d slack (bs ++ as)) : PacedL d (bs.length + slack) as := by
  intro n
  have h2 := h (bs.length + n)
  rw [List.take_length_add_append, List.count_append] at h2
  have : d * (bs.count true + (as.take n).count true)
      = d * (bs.count true) + d * ((as.take n).count true) := by ring
  omega

theorem pacedL_prefix_of_append {d : ℕ} {xs ys : List Bool}
    (h : PacedL d 0 (xs ++ ys)) : PacedL d 0 xs := by
  intro n
  by_cases hn : n ≤ xs.length
  · have h2 := h n
    rw [List.take_append_of_le_length hn] at h2
    exact h2
  · have h2 := h xs.length
    rw [List.take_left] at h2
    rw [List.take_of_length_le (by omega)]
    omega

#print axioms pacedL_prefix_of_append

/-! ## 2. The preparation walk at slack `≤ 2047` -/

/-- The DP demand of a `(k, m)` stage when the preparation stream is paced at
a slack of up to `2047` (the clock phase at the `prepare` entry). -/
def dpDemandS (k m : ℕ) : ℕ :=
  (prepLen k + 2047) / 2048 + (prepLen k + 2047 + dpEvents (m + 1)) / 2048 + 1

/-- `StageInvD` with the slack-`2047` demand. -/
def StageInvS (k m : ℕ) (v : SearchVM) : Prop :=
  (dpDemandS k m : ℤ) ≤ value v.search.debt

theorem dpDemand_le_dpDemandS (k m : ℕ) : dpDemand k m ≤ dpDemandS k m := by
  unfold dpDemand dpDemandS
  omega

theorem stageInvD_of_stageInvS {k m : ℕ} {v : SearchVM} (h : StageInvS k m v) :
    StageInvD k m v := by
  have hz : (dpDemand k m : ℤ) ≤ (dpDemandS k m : ℤ) := by
    exact_mod_cast dpDemand_le_dpDemandS k m
  unfold StageInvD
  unfold StageInvS at h
  omega

/-- `CloseoutPreload11.StagePrep2` with the pacing at a slack. -/
def StagePrepS (_k m D slack : ℕ) (w v : SearchVM) (as : List Bool) : Prop :=
  ∃ bs : List Bool, ReachP w bs v ∧ D + dpEvents (m + 1) ≤ bs.length + as.length ∧
    PacedL 2048 slack (bs ++ as)

theorem stagePrepS_next {k m D slack : ℕ} {w v v' : SearchVM} {c : GalilScaffoldPlace.Place}
    {a : Bool} {as : List Bool} (hq : StagePrepS k m D slack w v (a :: as))
    (hs : searchStep c a v v') (hne : v'.search.mode ≠ Mode.run) :
    StagePrepS k m D slack w v' as := by
  obtain ⟨bs, hreach, hlen, hpaced⟩ := hq
  refine ⟨bs ++ [a], .snoc _ _ _ _ _ c hreach hs hne, ?_, ?_⟩
  · simp only [List.length_append, List.length_singleton]
    simp only [List.length_cons] at hlen
    omega
  · rw [← append_cons_eq]; exact hpaced

/-- **NAMED — `CloseoutPreload28.dpSafe_of_stagePrepD` at slack `≤ 2047`.**  The
preparation stream is paced from the clock phase at the `prepare` entry, not
from phase `0`; the stage invariant is `StageInvS`. -/
theorem dpSafe_of_stagePrepD_slack {k m D slack : ℕ} {v : SearchVM}
    (hp : PrepAt k m v) (hE : StageInvS k m v)
    (hdep : DepthAt v D) (hD : D ≤ prepLen k) (hslack : slack ≤ 2047)
    {x x' : SearchVM} {c : GalilScaffoldPlace.Place} {a : Bool} {as : List Bool}
    (hq : StagePrepS k m D slack v x (a :: as)) (hs : searchStep c a x x')
    (hrun : x'.search.mode = Mode.run) :
    DpSafeStage x' as := by
  obtain ⟨bs, hreach, hlen, hpaced⟩ := hq
  have hne := reachP_ne_run hreach
  have hdlen := hdep bs x x' c a hreach hs hrun
  obtain ⟨W, lower, hW, hpreload⟩ := entry_preload_at_prep hp hreach hs hrun
  obtain ⟨hcan, hdv⟩ := entry_debt_at_prep hp hreach hs hrun
  have hpaced' : PacedL 2048 slack ((bs ++ [a]) ++ as) := by
    rw [← append_cons_eq]; exact hpaced
  have hlenpref : (bs ++ [a]).length ≤ D := by
    simp only [List.length_append, List.length_singleton]; omega
  have hadv : 2048 * ((bs ++ [a]).count true) ≤ prepLen k + 2047 :=
    le_trans (pacedL_prefix_count_slack hpaced') (by omega)
  have hmono : dpEvents W.length ≤ dpEvents (m + 1) := dpEvents_mono hW
  have hsuf := pacedL_suffix_slack' hpaced'
  refine dpSafeStage_entry_real x' W lower ((bs ++ [a]).length + slack) as
    (run_entry_preload hs hne hrun hpreload) hrun hcan ?_ ?_ hsuf
  · have hneed : ((bs ++ [a]).length + slack + dpEvents W.length) / 2048 + 1
        + (bs ++ [a]).count true ≤ dpDemandS k m := by
      unfold dpDemandS
      omega
    have hneedz : ((((bs ++ [a]).length + slack + dpEvents W.length) / 2048 + 1 : ℕ) : ℤ)
        + (((bs ++ [a]).count true : ℕ) : ℤ) ≤ (dpDemandS k m : ℤ) := by
      exact_mod_cast hneed
    unfold StageInvS at hE
    rw [hdv]
    omega
  · have hlen' : D + dpEvents (m + 1) ≤ bs.length + (as.length + 1) := hlen
    omega

#print axioms dpSafe_of_stagePrepD_slack

/-! ## 3. The `.double` exit satisfies `StageInvS` (for `16 ≤ mw`) -/

/-- **NAMED — the balance for the slack-`2047` demand.**  The two extra units
of `dpDemandS` cost `8` in the balance; the windows `4 ≤ mw ≤ 15` do not
absorb them at an arbitrary clock phase.  `16` is sharp for these inputs
(`prepLen_le`, `dpEvents_win_le`, the pacing at the full window): at `mw = 15`
the worst admissible triple gives a balance of `16 > 15`, and the margin is
`0` at `mw = 16` and `mw = 20`.  `mw ≤ 3` is vacuous, since `hcal` forces
`4 ≤ mw`. -/
theorem bal_of_paced_slack_S {k mw slack : ℕ} {bs : List Bool} {a : Bool}
    (hcal : 8 * max k 1 ≤ 2 * mw) (hblen : bs.length = mw) (hmw : 16 ≤ mw)
    (hslack : slack ≤ 2047) (hp : PacedL 2048 slack (bs ++ [a])) :
    4 * dpDemandS k (2 * mw) + 4 * (bs ++ [a]).count true ≤ mw := by
  have hc : 2048 * (bs ++ [a]).count true ≤ (bs ++ [a]).length + slack := by
    have h := hp (bs ++ [a]).length
    rwa [List.take_length] at h
  have hl : (bs ++ [a]).length = mw + 1 := by simp [hblen]
  rw [hl] at hc
  have h1 := prepLen_le k
  have h2 := dpEvents_win_le (2 * mw)
  have h3 : k ≤ max k 1 := le_max_left _ _
  have h4 : 1 ≤ max k 1 := le_max_right _ _
  have hM : 4 * max k 1 ≤ mw := by omega
  unfold dpDemandS
  -- `omega` is incomplete on the tight system with two `/2048` quotients at
  -- `16 ≤ mw`; the four windows `16 ≤ mw < 20` are closed by `interval_cases`.
  rcases Nat.lt_or_ge mw 20 with hlt | hge
  · have hk : max k 1 ≤ 4 := by omega
    interval_cases mw <;> omega
  · omega

#print axioms bal_of_paced_slack_S

/-- `CloseoutPreload28.stageInvD_of_double_exit` on `StageInvS`. -/
theorem stageInvS_of_double_exit {c' : GalilScaffoldPlace.Place} {k mw : ℕ} {a : Bool}
    {bs : List Bool} {v t t' : SearchVM}
    (hr : DoubleTrace bs v t)
    (hv0 : value v.search.debt = 0) (hq : v.search.quarter = 0)
    (hvc : Canonical v.search.debt)
    (htm : t.search.mode = Mode.double) (htw : positive t.search.work = false)
    (hts : t.search.span = ofNat (2 * mw)) (htl : t.lower = ofNat k)
    (hblen : bs.length = mw)
    (hbal : 4 * dpDemandS k (2 * mw) + 4 * (bs ++ [a]).count true ≤ mw)
    (hs : searchStep c' a t t') :
    PrepAt k (2 * mw) t' ∧ StageInvS k (2 * mw) t' := by
  have hc := double_exit_canonical hr htm htw hvc
  obtain ⟨hprep, -, hdv⟩ := prepAt_of_double_exit htm htw hts htl hc hs
  refine ⟨hprep, ?_⟩
  have hge := double_exit_debt_ge hr htm htw hv0 hq
  rw [hblen] at hge
  have hcnt : (bs ++ [a]).count true = bs.count true + (if a then 1 else 0) := by
    cases a <;> simp
  rw [hcnt] at hbal
  unfold StageInvS
  rw [hdv]
  cases a
  · simp only [Bool.false_eq_true, if_false, add_zero, sub_zero] at hbal ⊢
    have hbalz : (4 * dpDemandS k (2 * mw) : ℤ) + 4 * ((bs.count true : ℕ) : ℤ) ≤ (mw : ℤ) := by
      exact_mod_cast hbal
    omega
  · simp only [if_true] at hbal ⊢
    have hbalz : (4 * dpDemandS k (2 * mw) : ℤ) + 4 * ((bs.count true : ℕ) : ℤ) + 4
        ≤ (mw : ℤ) := by
      have h : 4 * dpDemandS k (2 * mw) + 4 * bs.count true + 4 ≤ mw := by omega
      exact_mod_cast h
    omega

#print axioms stageInvS_of_double_exit

/-! ## 4. The round trip with `StageInvS` at the dispatch -/

section RoundTrip

variable {σ : Type} {F : Frame σ} {I : State σ → Prop}

/-- `CloseoutPreload31.postRunF_round_trip` with `StageInvS` at the dispatch;
the one extra premise is `16 ≤ mw`. -/
theorem postRunF_round_trip_S {k mw : ℕ} {ts pre rs ws bs : List Bool} {a1 a3 : Bool}
    {cr cw : GalilScaffoldPlace.Place} {v t0 w0 w1 u0 : SearchVM} {p q0 : State σ}
    (hsup : ScanSupplyInv F 2048 I)
    (hm : v.search.mode = Mode.run) (hsp : v.search.span = ofNat mw)
    (hlow : v.lower = ofNat k) (hcal : 8 * max k 1 ≤ mw)
    (hrun : RunTrace rs v t0) (ht0 : t0.search.mode = Mode.run)
    (hs1 : searchStep cr a1 t0 w0) (hw0 : w0.search.mode = Mode.wait)
    (hwait : WaitTrace ws w0 w1) (hw1 : w1.search.mode = Mode.wait)
    (hcan1 : Canonical w1.search.debt)
    (hs2 : searchStep cw false w1 u0) (hne : u0.search.mode ≠ Mode.wait)
    (hcan0 : Canonical u0.search.debt)
    (hsc : ScanTrace F 2048 ts (pre ++ (rs ++ a1 :: (ws ++ [false]))) p q0)
    (hp : I p) (hclk : ClockInv 2048 p.ctl)
    (hblen : bs.length = mw) (hmw : 16 ≤ mw)
    (hpaced : PacedL 2048 0 ((pre ++ (rs ++ a1 :: (ws ++ [false]))) ++ (bs ++ [a3]))) :
    ∃ t1 : SearchVM, DoubleTrace bs u0 t1 ∧ t1.search.mode = Mode.double ∧
      positive t1.search.work = false ∧ t1.search.span = ofNat (2 * mw) ∧
      t1.lower = ofNat k ∧
      ∀ (c' : GalilScaffoldPlace.Place) (t' : SearchVM), searchStep c' a3 t1 t' →
        PrepAt k (2 * mw) t' ∧ StageInvS k (2 * mw) t' ∧ t'.walker = c' ∧
          8 * max k 1 ≤ 2 * mw := by
  have hne0 : w0.search.mode ≠ Mode.run := by rw [hw0]; decide
  obtain ⟨hl0, -, -, -, -, hwsp, -⟩ := run_exit_frame hm hsp hlow hrun ht0 hs1 hne0
  have hsp0 : w0.search.span = ofNat mw := hwsp hw0
  obtain ⟨hdm, hdw, hdsp, hq0, hdl, -⟩ := wait_exit_double hsp0 hwait hw1 hs2 hne
  have hz : zero w1.search.debt = true := by
    obtain ⟨-, -, -, hc | hc⟩ := wait_step_cases hw1 hs2
    · exact absurd hc.2.1 hne
    · exact hc.1
  have hd0 : value u0.search.debt = 0 := wait_exit_debt_zero hw1 hz hcan1 hs2
  obtain ⟨t1, hr, h1m, h1w, h1s, h1l, -, -⟩ := double_spends cw hdm hdw hdsp hblen
  have h1l' : t1.lower = ofNat k := by rw [h1l, hdl, hl0]
  refine ⟨t1, hr, h1m, h1w, h1s, h1l', ?_⟩
  intro c' t' hs3
  have hph := prefixPhase_of_scan_inv hsup hsc hp hclk.1 hclk.2
  have hpa : PacedL 2048 2047 (bs ++ [a3]) := pacedL_suffix_2047 hpaced hph
  have hcal' : 8 * max k 1 ≤ 2 * mw := by omega
  have hbal := bal_of_paced_slack_S hcal' hblen hmw le_rfl hpa
  obtain ⟨hprep, hinv⟩ :=
    stageInvS_of_double_exit hr hd0 hq0 hcan0 h1m h1w h1s h1l' hblen hbal hs3
  have hc1 := double_exit_canonical hr h1m h1w hcan0
  obtain ⟨-, hwk, -⟩ := prepAt_of_double_exit h1m h1w h1s h1l' hc1 hs3
  exact ⟨hprep, hinv, hwk, hcal'⟩

#print axioms postRunF_round_trip_S

end RoundTrip

variable (P : Shared) (q : ℕ) (first : Fin 9)

/-- `CloseoutPreload34.postRunF_round_trip_galil'` with `StageInvS` at the
dispatch; the one extra premise is `16 ≤ mw`. -/
theorem postRunF_round_trip_galil_S {I : State GalilVM → Prop} {k mw : ℕ}
    {ts0 pre rs ws bs : List Bool} {t1 t2 a1 a2 a3 : Bool}
    {p p0 p1 p2 p3 p4 : State GalilVM}
    (hres : RestartOnBroken P)
    (hsup : ScanSupplyInv (galilFrameS P q first) 2048 I)
    (hm : p0.vm.search.mode = Mode.run) (hsp : p0.vm.search.span = ofNat mw)
    (hlow : p0.vm.lower = ofNat k) (hcal : 8 * max k 1 ≤ mw)
    (hcan : Canonical p0.vm.search.debt)
    (hpre : ScanTrace (galilFrameS P q first) 2048 ts0 pre p p0)
    (hrunL : IdleLeg P q first (fun s => s.search.mode = Mode.run) rs p0 p1)
    (ht0 : p1.vm.search.mode = Mode.run) (hidle1 : p1.vm.chain = ChainVM.idle)
    (hex1 : ScanTrace (galilFrameS P q first) 2048 [t1] [a1] p1 p2)
    (hw0 : p2.vm.search.mode = Mode.wait)
    (hwaitL : IdleLeg P q first (fun s => s.search.mode = Mode.wait) ws p2 p3)
    (hw1 : p3.vm.search.mode = Mode.wait) (hidle3 : p3.vm.chain = ChainVM.idle)
    (hex2 : ScanTrace (galilFrameS P q first) 2048 [t2] [a2] p3 p4)
    (hne : p4.vm.search.mode ≠ Mode.wait)
    (hp : I p) (hclk : ClockInv 2048 p.ctl)
    (hblen : bs.length = mw) (hmw : 16 ≤ mw)
    (hpaced : PacedL 2048 0 ((pre ++ (rs ++ a1 :: (ws ++ [false]))) ++ (bs ++ [a3]))) :
    ∃ t1 : SearchVM, DoubleTrace bs (searchLens.get p4.vm) t1 ∧ t1.search.mode = Mode.double ∧
      positive t1.search.work = false ∧ t1.search.span = ofNat (2 * mw) ∧
      t1.lower = ofNat k ∧
      ∀ (c' : GalilScaffoldPlace.Place) (t' : SearchVM), searchStep c' a3 t1 t' →
        PrepAt k (2 * mw) t' ∧ StageInvS k (2 * mw) t' ∧ t'.walker = c' ∧
          8 * max k 1 ≤ 2 * mw := by
  have hrun := idleLeg_runTrace P q first hres hrunL
  have hwait := idleLeg_waitTrace P q first hres hwaitL
  have hs1 := scanTrace_single_searchStep P q first hres hex1 hidle1
  have hs2 := scanTrace_single_searchStep P q first hres hex2 hidle3
  have hnf := exitNotFire_of_wait P q first hres hcan hrunL ht0 hidle1 hex1 hw0 hwaitL hw1
    hidle3 hex2 hne
  obtain ⟨ha2, ts', q', hsc⟩ := legsCoupled_galil P q first hpre hrunL hex1 hwaitL hex2 hnf
  subst ha2
  have hct0 : Canonical (searchLens.get p1.vm).search.debt := canonical_runTrace hrun hcan
  have hcw0 := canonical_run_step ht0 hs1 hct0
  have hcan1 := canonical_waitTrace hwait hcw0
  have hcan0 := canonical_wait_step hw1 hs2 hcan1
  exact postRunF_round_trip_S (v := searchLens.get p0.vm) (t0 := searchLens.get p1.vm)
    (w0 := searchLens.get p2.vm) (w1 := searchLens.get p3.vm) (u0 := searchLens.get p4.vm)
    hsup hm hsp hlow hcal hrun ht0 hs1 hw0 hwait hw1 hcan1 hs2 hne hcan0 hsc hp hclk hblen
    hmw hpaced

#print axioms postRunF_round_trip_galil_S

/-! ## 5. The preparation leg on the machine, and the next `.run` entry -/

/-- A preparation tick keeps the span. -/
theorem prepTick_span {x y : GalilScaffoldPrepareControl.State} {b : Bool}
    (ht : GalilScaffoldPrepareControl.Tick b x y) : y.span = x.span := by
  cases ht <;> rfl

/-- Along the pre-entry reachability from a `.lower` entry, `span` and `lower`
are the stage's. -/
theorem reachP_frame_of_prepAt {k m : ℕ} {v : SearchVM} (hp : PrepAt k m v) :
    ∀ {bs : List Bool} {x : SearchVM}, ReachP v bs x →
      x.search.span = ofNat m ∧ x.lower = ofNat k := by
  intro bs x h
  induction h with
  | nil hne => exact ⟨hp.span, hp.low⟩
  | snoc x x' bs a c hr hs hne ih =>
      have h4 := phaseP_mode4 hp.mode (phase_reach_at_prep hp hr)
      unfold searchStep at hs
      have hstep : ∃ y, GalilScaffoldPrepareControl.Tick true x.toPrep y ∧
          x' = SearchVM.ofPrep (GalilScaffoldPreparePaced.afterAdvance a y)
            x.search.quarter x.lower := by
        rcases h4 with h4 | h4 | h4 | h4 <;> rw [h4] at hs <;> exact hs
      obtain ⟨y, hy, hx'⟩ := hstep
      refine ⟨?_, ?_⟩
      · rw [hx', ofPrep_span, afterAdvance_span, prepTick_span hy, toPrep_span, ih.1]
      · rw [hx', ofPrep_lower, ih.2]

#print axioms reachP_frame_of_prepAt

/-- The `.run` entry tick keeps `span` and `lower`. -/
theorem run_entry_frame {c : GalilScaffoldPlace.Place} {a : Bool} {x x' : SearchVM}
    (hs : searchStep c a x x') (hne : x.search.mode ≠ Mode.run)
    (hr : x'.search.mode = Mode.run) :
    x'.search.span = x.search.span ∧ x'.lower = x.lower := by
  obtain ⟨-, -, he⟩ := PalPeg.CloseoutRunEntriesS.run_entry_startRun hs hne hr
  refine ⟨?_, ?_⟩
  · rw [he, ofPrep_span, afterAdvance_span]; rfl
  · rw [he, ofPrep_lower]

theorem idleLeg_first {M : GalilVM → Prop} {as : List Bool} {p r : State GalilVM}
    (h : IdleLeg P q first M as p r) (hM : M r.vm) : M p.vm := by
  cases h with
  | nil p => exact hM
  | cons t a as p p' r hidle hM' h1 hr => exact hM'

/-- **NAMED — an idle leg outside `.run` is a `ReachP` on the search
projection, with the same booleans.** -/
theorem idleLeg_reachP (hres : RestartOnBroken P) {as : List Bool} {p r : State GalilVM}
    (h : IdleLeg P q first (fun s => s.search.mode ≠ Mode.run) as p r) :
    r.vm.search.mode ≠ Mode.run →
    ∀ {bs0 : List Bool} {v : SearchVM}, ReachP v bs0 (searchLens.get p.vm) →
      ReachP v (bs0 ++ as) (searchLens.get r.vm) := by
  induction h with
  | nil p => intro _ bs0 v h0; simpa using h0
  | cons t a as p p' r hidle hM h1 hr ih =>
      intro hne bs0 v h0
      have hne' : p'.vm.search.mode ≠ Mode.run := idleLeg_first P q first hr hne
      have hs := scanTrace_single_searchStep P q first hres h1 hidle
      have h1' : ReachP v (bs0 ++ [a]) (searchLens.get p'.vm) :=
        .snoc _ _ _ _ _ _ h0 hs hne'
      rw [append_cons_eq]
      exact ih hne h1'

#print axioms idleLeg_reachP

/-- **NAMED — the next `.run` entry re-establishes the `PostRunF` datum.**
From the dispatch state `p5` (`PrepAt k m ∧ StageInvS k m` on the search
projection, entered at the end of the scan leg `pre5` from `p`), through an
idle preparation leg `ps` and the entry tick `a`, the next `.run` entry `p7`
carries `span = ofNat m`, `lower = ofNat k`, the calibration, `Canonical` debt,
`DpSafeStage` over the rest `as`, and is the end of the scan leg
`pre5 ++ ps ++ [a]` from `p`.  The pacing is of the whole stream from `p`;
the slack at `prepare` is `≤ 2047` by the clock phase. -/
theorem postRunF_next_entry (hres : RestartOnBroken P) {I : State GalilVM → Prop}
    {k m D : ℕ} {ts5 pre5 ps as : List Bool} {t a : Bool} {p p5 p6 p7 : State GalilVM}
    (hsup : ScanSupplyInv (galilFrameS P q first) 2048 I)
    (hp5 : PrepAt k m (searchLens.get p5.vm)) (hE : StageInvS k m (searchLens.get p5.vm))
    (hcal : 8 * max k 1 ≤ m)
    (hdep : DepthAt (searchLens.get p5.vm) D) (hD : D ≤ prepLen k)
    (hsc5 : ScanTrace (galilFrameS P q first) 2048 ts5 pre5 p p5)
    (hp : I p) (hclk : ClockInv 2048 p.ctl)
    (hprepL : IdleLeg P q first (fun s => s.search.mode ≠ Mode.run) ps p5 p6)
    (hne6 : p6.vm.search.mode ≠ Mode.run) (hidle6 : p6.vm.chain = ChainVM.idle)
    (hex : ScanTrace (galilFrameS P q first) 2048 [t] [a] p6 p7)
    (hrun7 : p7.vm.search.mode = Mode.run)
    (hlen : D + dpEvents (m + 1) ≤ ps.length + (as.length + 1))
    (hpaced : PacedL 2048 0 (pre5 ++ (ps ++ a :: as))) :
    p7.vm.search.mode = Mode.run ∧ p7.vm.search.span = ofNat m ∧ p7.vm.lower = ofNat k ∧
      8 * max k 1 ≤ m ∧ Canonical p7.vm.search.debt ∧
      DpSafeStage (searchLens.get p7.vm) as ∧
      ∃ ts7 : List Bool,
        ScanTrace (galilFrameS P q first) 2048 ts7 (pre5 ++ (ps ++ [a])) p p7 := by
  have hs := scanTrace_single_searchStep P q first hres hex hidle6
  have hreach : ReachP (searchLens.get p5.vm) ps (searchLens.get p6.vm) := by
    have h0 : ReachP (searchLens.get p5.vm) [] (searchLens.get p5.vm) :=
      .nil _ (by rw [hp5.mode]; decide)
    simpa using idleLeg_reachP P q first hres hprepL hne6 h0
  have hph := prefixPhase_of_scan_inv hsup hsc5 hp hclk.1 hclk.2
  have hpa : PacedL 2048 2047 (ps ++ a :: as) := pacedL_suffix_2047 hpaced hph
  have hq : StagePrepS k m D 2047 (searchLens.get p5.vm) (searchLens.get p6.vm) (a :: as) :=
    ⟨ps, hreach, by simpa using hlen, hpa⟩
  have hsafe := dpSafe_of_stagePrepD_slack hp5 hE hdep hD le_rfl hq hs hrun7
  obtain ⟨hsp6, hlow6⟩ := reachP_frame_of_prepAt hp5 hreach
  obtain ⟨hsp7, hlow7⟩ := run_entry_frame hs hne6 hrun7
  obtain ⟨hcan7, -⟩ := entry_debt_at_prep hp5 hreach hs hrun7
  refine ⟨hrun7, ?_, ?_, hcal, hcan7, hsafe, ?_⟩
  · show (searchLens.get p7.vm).search.span = ofNat m
    exact hsp7.trans hsp6
  · show (searchLens.get p7.vm).lower = ofNat k
    exact hlow7.trans hlow6
  · obtain ⟨tsp, hp6⟩ := idleLeg_scanTrace P q first hprepL
    refine ⟨ts5 ++ (tsp ++ [t]), ?_⟩
    have h := scanTrace_append hsc5 (scanTrace_append hp6 hex)
    simpa using h

#print axioms postRunF_next_entry

/-! ## 6. The `.double` leg on the machine, and the step -/

/-- The search projection of an idle `.double` leg (work positive at every
tick) is a `DoubleTrace` with the same booleans. -/
theorem idleLeg_doubleTrace (hres : RestartOnBroken P) {as : List Bool}
    {p r : State GalilVM}
    (h : IdleLeg P q first
      (fun s => s.search.mode = Mode.double ∧ positive s.search.work = true) as p r) :
    DoubleTrace as (searchLens.get p.vm) (searchLens.get r.vm) := by
  induction h with
  | nil p => exact .nil _
  | cons t a as p p' r hidle hM h1 hr ih =>
      exact .cons (P.place p.vm) a as _ _ _ hM.1 hM.2
        (scanTrace_single_searchStep P q first hres h1 hidle) ih

/-- A `.double` leg is deterministic in its booleans. -/
theorem doubleTrace_det {as : List Bool} {v t t' : SearchVM}
    (h : DoubleTrace as v t) (h' : DoubleTrace as v t') : t = t' := by
  induction h generalizing t' with
  | nil v => cases h'; rfl
  | cons c a as v v' t hm hp hs hr ih =>
      cases h' with
      | cons c' _ _ _ v'' _ hm' hp' hs' hr' =>
          have e1 := double_step_pos hm hp hs
          have e2 := double_step_pos hm' hp' hs'
          have hv : v' = v'' := by rw [e1, e2]
          subst hv
          exact ih hr'

#print axioms doubleTrace_det

/-- **NAMED — `PostRunF`'s datum at one `.run` entry gives it at the next.**
Inputs: the datum at `p0` (frame, `Canonical`, the scan leg `pre` from `p`
under `I p ∧ ClockInv`), the machine legs `.run` (`rs`) / exit `a1` / `.wait`
(`ws`) / exit `a2` / `.double` (`bs`) / dispatch `a3` / preparation (`ps`) /
entry `a`, each an `IdleLeg` with its mode annotation and the chain idle at the
exit ticks, the pacing of the whole stream from `p`, the input-length clause
for the next stage, the depth `D ≤ prepLen k` of the preparation, and
`16 ≤ mw`.  Output: the datum at `p8` with `span = ofNat (2mw)`. -/
theorem postRunF_step (hres : RestartOnBroken P) {I : State GalilVM → Prop} {k mw D : ℕ}
    {ts0 pre rs ws bs ps as : List Bool} {t1 t2 t3 t4 a1 a2 a3 a4 : Bool}
    {p p0 p1 p2 p3 p4 p5 p6 p7 p8 : State GalilVM}
    (hsup : ScanSupplyInv (galilFrameS P q first) 2048 I)
    (hm : p0.vm.search.mode = Mode.run) (hsp : p0.vm.search.span = ofNat mw)
    (hlow : p0.vm.lower = ofNat k) (hcal : 8 * max k 1 ≤ mw)
    (hcan : Canonical p0.vm.search.debt)
    (hpre : ScanTrace (galilFrameS P q first) 2048 ts0 pre p p0)
    (hp : I p) (hclk : ClockInv 2048 p.ctl)
    (hrunL : IdleLeg P q first (fun s => s.search.mode = Mode.run) rs p0 p1)
    (ht0 : p1.vm.search.mode = Mode.run) (hidle1 : p1.vm.chain = ChainVM.idle)
    (hex1 : ScanTrace (galilFrameS P q first) 2048 [t1] [a1] p1 p2)
    (hw0 : p2.vm.search.mode = Mode.wait)
    (hwaitL : IdleLeg P q first (fun s => s.search.mode = Mode.wait) ws p2 p3)
    (hw1 : p3.vm.search.mode = Mode.wait) (hidle3 : p3.vm.chain = ChainVM.idle)
    (hex2 : ScanTrace (galilFrameS P q first) 2048 [t2] [a2] p3 p4)
    (hne : p4.vm.search.mode ≠ Mode.wait)
    (hdblL : IdleLeg P q first
      (fun s => s.search.mode = Mode.double ∧ positive s.search.work = true) bs p4 p5)
    (hidle5 : p5.vm.chain = ChainVM.idle)
    (hex3 : ScanTrace (galilFrameS P q first) 2048 [t3] [a3] p5 p6)
    (hdep : DepthAt (searchLens.get p6.vm) D) (hD : D ≤ prepLen k)
    (hprepL : IdleLeg P q first (fun s => s.search.mode ≠ Mode.run) ps p6 p7)
    (hne7 : p7.vm.search.mode ≠ Mode.run) (hidle7 : p7.vm.chain = ChainVM.idle)
    (hex4 : ScanTrace (galilFrameS P q first) 2048 [t4] [a4] p7 p8)
    (hrun8 : p8.vm.search.mode = Mode.run)
    (hblen : bs.length = mw) (hmw : 16 ≤ mw)
    (hlen : D + dpEvents (2 * mw + 1) ≤ ps.length + (as.length + 1))
    (hpaced : PacedL 2048 0
      (pre ++ (rs ++ a1 :: (ws ++ [false])) ++ (bs ++ a3 :: (ps ++ a4 :: as)))) :
    p8.vm.search.mode = Mode.run ∧ p8.vm.search.span = ofNat (2 * mw) ∧
      p8.vm.lower = ofNat k ∧ 8 * max k 1 ≤ 2 * mw ∧ Canonical p8.vm.search.debt ∧
      DpSafeStage (searchLens.get p8.vm) as ∧
      ∃ ts8 : List Bool, ScanTrace (galilFrameS P q first) 2048 ts8
        (pre ++ (rs ++ a1 :: (ws ++ [false])) ++ (bs ++ a3 :: (ps ++ [a4]))) p p8 := by
  -- the stream split at the dispatch
  have e : pre ++ (rs ++ a1 :: (ws ++ [false])) ++ (bs ++ a3 :: (ps ++ a4 :: as))
      = (pre ++ (rs ++ a1 :: (ws ++ [false])) ++ (bs ++ [a3])) ++ (ps ++ a4 :: as) := by
    simp
  rw [e] at hpaced
  have hpaced1 := pacedL_prefix_of_append hpaced
  -- the round trip to the dispatch
  obtain ⟨t1', hdt, -, -, -, -, hnext⟩ := postRunF_round_trip_galil_S P q first hres hsup hm hsp
    hlow hcal hcan hpre hrunL ht0 hidle1 hex1 hw0 hwaitL hw1 hidle3 hex2 hne hp hclk hblen hmw
    hpaced1
  have hdt' := idleLeg_doubleTrace P q first hres hdblL
  have ht1 : t1' = searchLens.get p5.vm := doubleTrace_det hdt hdt'
  subst ht1
  have hs3 := scanTrace_single_searchStep P q first hres hex3 hidle5
  obtain ⟨hp6, hE6, -, hcal'⟩ := hnext _ _ hs3
  -- the scan leg up to the dispatch
  have hnf := exitNotFire_of_wait P q first hres hcan hrunL ht0 hidle1 hex1 hw0 hwaitL hw1
    hidle3 hex2 hne
  have ha2 : a2 = false := scanTrace_single_false_of_clock hex2 hnf
  subst ha2
  obtain ⟨tsr, hr⟩ := idleLeg_scanTrace P q first hrunL
  obtain ⟨tsw, hw⟩ := idleLeg_scanTrace P q first hwaitL
  obtain ⟨tsd, hd⟩ := idleLeg_scanTrace P q first hdblL
  have hsc6 : ScanTrace (galilFrameS P q first) 2048
      (ts0 ++ (tsr ++ [t1] ++ (tsw ++ [t2])) ++ (tsd ++ [t3]))
      (pre ++ (rs ++ a1 :: (ws ++ [false])) ++ (bs ++ [a3])) p p6 := by
    have h := scanTrace_append
      (scanTrace_append hpre
        (scanTrace_append (scanTrace_append hr hex1) (scanTrace_append hw hex2)))
      (scanTrace_append hd hex3)
    simpa using h
  -- the next entry
  obtain ⟨h1, h2, h3, h4, h5, h6, ts8, h7⟩ := postRunF_next_entry P q first hres hsup hp6 hE6
    hcal' hdep hD hsc6 hp hclk hprepL hne7 hidle7 hex4 hrun8 hlen hpaced
  refine ⟨h1, h2, h3, h4, h5, h6, ts8, ?_⟩
  simpa using h7

#print axioms postRunF_step

/-!
## 7. What is left

Closed: `dpSafe_of_stagePrepD_slack` (§2) — the preparation walk at slack
`≤ 2047`; `postRunF_next_entry` (§5) — the `PostRunF` datum at the next `.run`
entry from the dispatch state, every machine fact read off the run; and
`postRunF_step` (§6) — the datum at one `.run` entry gives it at the next.

**The one hypothesis** outside the machine run and the mode/idle annotations:
`hmw : 16 ≤ mw` — the slack-`2047` demand `dpDemandS` costs two more units than
`dpDemand`, and `bal_of_paced_slack_S` needs `mw ≥ 16` to absorb them at an
arbitrary clock phase (`CloseoutPreload28.bal_of_paced_slack` needs only
`mw ≥ 8`).  Since `postRunF_step` carries `hcal : 8 * max k 1 ≤ mw`, a stage
with `2 ≤ k` has `mw ≥ 16` and is covered unconditionally; **the residue is
`k ≤ 1`**, i.e. `8 ≤ mw ≤ 15`, where the phase of the `.double` leg or a
sharper demand is needed.  `DepthAt _ D` / `D ≤ prepLen k` and the input-length clause remain
the supply-side premises they were in `CloseoutPreload28`.

**Not assembled here:** `RunEntriesS` through the `.wait` / `.double` /
preparation legs (every entry there is outside `.run`, so each `RunEntryS` is
vacuous except at the final entry tick, where `postRunF_next_entry`'s
`DpSafeStage` is its content), and the induction over all later `.run` entries
(`PostRunC` modulo the boot datum) — `postRunF_step` is its step.

**無条件 PAL ∈ PEG は未完.**
-/

end PalPeg.CloseoutPreload35
