import PalPeg.CloseoutPreload27

/-!
# `StageInvD` — the post-double stage invariant in Scala's shape

`CloseoutPreload25`–`27` showed that the `.double` exit clause of
`CloseoutPreload24.round_trip_entries` — the radius-shaped stage bound
`stageDebt Rad k + stageCredit k (2 * mw) + 1 ≤ debt` re-established after a
`.double` leg of length `mw` — is false for every credit divisor
(`CloseoutPreload27.double_len_false_any`).  The root cause is that the
radius-shaped bound is the *first-run* (post-`prep`) invariant, while a
post-double `.run` leg starts from whatever the `.double` leg earned
(`CloseoutPreload18.double_exit_debt_ge`, ≈ `mw / 4`) with a doubled window.

The Scala spec (`ScaffoldSearch.scala`) asserts only `debt ≥ 0` (`stepRun`
239–240, `stepWait` 256–257) and never re-establishes a radius-shaped budget at
the `.double` exit.  This file follows it.

* §1 `dpDemand k m` — the number of comparison units the DP of a window `m`
  can be charged before it halts: the preparation's own advances
  (`prepLen k / 2048`) plus the clock-paced comparisons over the preparation
  and the DP run (`(prepLen k + dpEvents (m + 1)) / 2048 + 1`).  `StageInvD k m v`
  is `dpDemand k m ≤ debt v` — no radius, no credit.
* §2 `dpSafe_of_stagePrepD` — the DP entry from `StageInvD`.  It goes straight
  to `CloseoutPreload10.dpSafeStage_entry_real`, skipping
  `CloseoutPreload11.budget_adv2`: the radius/credit shape was only ever used
  to *derive* the bound `dpSafeStage_entry_real` asks for.
  `runEntriesS_of_stageInvD` is the stage induction on it, on `PostRunC`.
* §3 `stageInvD_of_double_exit` — the `.double` exit satisfies `StageInvD`
  when the leg's earnings cover the doubled window's demand
  (`hbal : 4 * dpDemand k (2 * mw) + 4 * count ≤ mw`), and
  `runEntriesS_of_double_exitD` — the analogue of
  `CloseoutPreload24.runEntriesS_of_double_exitC` on `StageInvD`.
* §4 the discharge of `hbal`: `bal_of_paced` (a leg paced in phase from its
  own entry, unconditional in `mw`) and `bal_of_paced_slack` (an arbitrary
  clock phase, for `mw ≥ 8`).

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPreload28

open PalPeg PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController
open PalPeg.GalilScaffoldSearchFinish (Mode)
open PalPeg.GalilScaffoldCounter (Canonical value ofNat positive)
open PalPeg.CloseoutReadyStage (DpSafeStage PacedL RunEntriesS)
open PalPeg.CloseoutDebtAudit (dpEvents)
open PalPeg.CloseoutPreload (run_entry_preload)
open PalPeg.CloseoutPreload5 (reachP_ne_run pacedL_prefix_count pacedL_suffix append_cons_eq)
open PalPeg.CloseoutPreload6 (prepLen prepLen_le)
open PalPeg.CloseoutPreload8 (DepthAt)
open PalPeg.CloseoutPreload9 (dpEvents_mono)
open PalPeg.CloseoutPreload10 (PrepAt prepAt_of_double_exit dpSafeStage_entry_real)
open PalPeg.CloseoutPreload11 (StagePrep2 StageInv2 stagePrep_next2 dpEvents_win_le)
open PalPeg.CloseoutPreload12 (entry_preload_at_prep entry_debt_at_prep)
open PalPeg.CloseoutPreload17 (DoubleTrace double_exit_canonical)
open PalPeg.CloseoutPreload18 (double_exit_debt_ge)
open PalPeg.CloseoutPreload21 (ScanTrace)
open PalPeg.CloseoutPreload22 (ClockInv)
open PalPeg.CloseoutPreload23 (ScanSupplyInv)
open PalPeg.CloseoutPreload24 (PostRunC ScanRealized)
open PalPeg.CloseoutPreload25 (count_le_of_paced)

/-! ## 1. The demand of a window, and the invariant -/

/-- **The DP demand of a `(k, m)` stage, in comparison units.**  The
preparation advances at most `prepLen k / 2048` times
(`CloseoutPreload5.pacedL_prefix_count`), and the DP run of the window `m + 1`
sees at most `(slack + dpEvents (m + 1)) / 2048 + 1` comparisons at a slack of
at most `prepLen k` (`CloseoutPreload10.dpSafeStage_entry_real`). -/
def dpDemand (k m : ℕ) : ℕ :=
  prepLen k / 2048 + (prepLen k + dpEvents (m + 1)) / 2048 + 1

/-- **NAMED — the post-double stage invariant, in Scala's shape.**  The debt at
the stage entry covers the demand of the window.  Compare the first-run
invariant `stageDebt Rad k + stageCredit k m ≤ debt` of
`CloseoutPreload12.dpSafe_of_stagePrepP`: no radius and no credit appear,
because Scala's `debt := 2·max(k,1) − rad` is installed only at `prepare` after
a restart, not at the `.double` exit. -/
def StageInvD (k m : ℕ) (v : SearchVM) : Prop :=
  (dpDemand k m : ℤ) ≤ value v.search.debt

/-! ## 2. The DP entry and the stage induction from `StageInvD` -/

/-- **NAMED — `CloseoutPreload12.dpSafe_of_stagePrepP` from `StageInvD`.**  The
radius-shaped premises `hstage` / `hcal` / `hE` are replaced by `StageInvD`;
`CloseoutPreload11.budget_adv2` is not used — the bound
`dpSafeStage_entry_real` asks for is `dpDemand` minus the advances spent. -/
theorem dpSafe_of_stagePrepD {k m D : ℕ} {v : SearchVM}
    (hp : PrepAt k m v) (hE : StageInvD k m v)
    (hdep : DepthAt v D) (hD : D ≤ prepLen k)
    {x x' : SearchVM} {c : GalilScaffoldPlace.Place} {a : Bool} {as : List Bool}
    (hq : StagePrep2 k m D v x (a :: as)) (hs : searchStep c a x x')
    (hrun : x'.search.mode = Mode.run) :
    DpSafeStage x' as := by
  obtain ⟨bs, hreach, hlen, hpaced⟩ := hq
  have hne := reachP_ne_run hreach
  have hdlen := hdep bs x x' c a hreach hs hrun
  obtain ⟨W, lower, hW, hpreload⟩ := entry_preload_at_prep hp hreach hs hrun
  obtain ⟨hcan, hdv⟩ := entry_debt_at_prep hp hreach hs hrun
  have hpaced' : PacedL 2048 0 ((bs ++ [a]) ++ as) := by
    rw [← append_cons_eq]; exact hpaced
  have hlenpref : (bs ++ [a]).length ≤ D := by
    simp only [List.length_append, List.length_singleton]; omega
  have hadv : 2048 * ((bs ++ [a]).count true) ≤ prepLen k :=
    le_trans (pacedL_prefix_count hpaced') (by omega)
  have hmono : dpEvents W.length ≤ dpEvents (m + 1) := dpEvents_mono hW
  refine dpSafeStage_entry_real x' W lower (bs ++ [a]).length as
    (run_entry_preload hs hne hrun hpreload) hrun hcan ?_ ?_ (pacedL_suffix hpaced')
  · have hneed : ((bs ++ [a]).length + dpEvents W.length) / 2048 + 1
        + (bs ++ [a]).count true ≤ dpDemand k m := by
      unfold dpDemand
      omega
    have hneedz : ((((bs ++ [a]).length + dpEvents W.length) / 2048 + 1 : ℕ) : ℤ)
        + (((bs ++ [a]).count true : ℕ) : ℤ) ≤ (dpDemand k m : ℤ) := by
      exact_mod_cast hneed
    unfold StageInvD at hE
    rw [hdv]
    omega
  · have hlen' : D + dpEvents (m + 1) ≤ bs.length + (as.length + 1) := hlen
    omega

#print axioms dpSafe_of_stagePrepD

section Consumers

variable {σ : Type} {F : Frame σ} {I : State σ → Prop}

/-- **NAMED — `CloseoutPreload24.runEntriesS_of_stageInvPPC` from `StageInvD`.** -/
theorem runEntriesS_of_stageInvD {k m D : ℕ} {v : SearchVM}
    (hp : PrepAt k m v) (hE : StageInvD k m v)
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
      · have hsafe := dpSafe_of_stagePrepD hp hE hdep hD hq hstep hr
        obtain ⟨bs, -, -, hpaced⟩ := hq
        have hpaced' : PacedL 2048 0 ((bs ++ [a]) ++ as) := by
          rw [← append_cons_eq]; exact hpaced
        obtain ⟨ts, p, q', hsc, hp', hclk⟩ := hreal (bs ++ [a])
        exact ⟨fun _ _ _ => hsafe, hpost hsup hsc hp' hclk x' as hr hsafe hpaced'⟩
      · exact ⟨fun _ _ h => absurd h hr, ih x' (Or.inl (stagePrep_next2 hq hstep hr))⟩
    · exact hq

#print axioms runEntriesS_of_stageInvD

/-! ## 3. The `.double` exit satisfies `StageInvD` -/

/-- **NAMED — the `.double` exit is a `StageInvD` stage entry.**  The leg of
length `mw` earns `≥ (mw - 4 * count - 3) / 4` units
(`CloseoutPreload18.double_exit_debt_ge`); the dispatch tick spends at most one
(`CloseoutPreload10.prepAt_of_double_exit`).  Under `hbal` — the earnings cover
the doubled window's demand — the exit state satisfies `StageInvD k (2 * mw)`.
No radius-shaped clause is asked. -/
theorem stageInvD_of_double_exit {c' : GalilScaffoldPlace.Place} {k mw : ℕ} {a : Bool}
    {bs : List Bool} {v t t' : SearchVM}
    (hr : DoubleTrace bs v t)
    (hv0 : value v.search.debt = 0) (hq : v.search.quarter = 0)
    (hvc : Canonical v.search.debt)
    (htm : t.search.mode = Mode.double) (htw : positive t.search.work = false)
    (hts : t.search.span = ofNat (2 * mw)) (htl : t.lower = ofNat k)
    (hblen : bs.length = mw)
    (hbal : 4 * dpDemand k (2 * mw) + 4 * (bs ++ [a]).count true ≤ mw)
    (hs : searchStep c' a t t') :
    PrepAt k (2 * mw) t' ∧ StageInvD k (2 * mw) t' := by
  have hc := double_exit_canonical hr htm htw hvc
  obtain ⟨hprep, -, hdv⟩ := prepAt_of_double_exit htm htw hts htl hc hs
  refine ⟨hprep, ?_⟩
  have hge := double_exit_debt_ge hr htm htw hv0 hq
  rw [hblen] at hge
  have hcnt : (bs ++ [a]).count true = bs.count true + (if a then 1 else 0) := by
    cases a <;> simp
  rw [hcnt] at hbal
  unfold StageInvD
  rw [hdv]
  cases a
  · simp only [Bool.false_eq_true, if_false, add_zero, sub_zero] at hbal ⊢
    have hbalz : (4 * dpDemand k (2 * mw) : ℤ) + 4 * ((bs.count true : ℕ) : ℤ) ≤ (mw : ℤ) := by
      exact_mod_cast hbal
    omega
  · simp only [if_true] at hbal ⊢
    have hbalz : (4 * dpDemand k (2 * mw) : ℤ) + 4 * ((bs.count true : ℕ) : ℤ) + 4
        ≤ (mw : ℤ) := by
      have h : 4 * dpDemand k (2 * mw) + 4 * bs.count true + 4 ≤ mw := by omega
      exact_mod_cast h
    omega

#print axioms stageInvD_of_double_exit

/-- **NAMED — `CloseoutPreload24.runEntriesS_of_double_exitC` on `StageInvD`.**
The hypotheses `hstage : 3 * Rad ≤ 5 * k`, `hcal`, and the radius-shaped exit
debt `hE` are replaced by the leg data (`DoubleTrace`, entered with debt `0`
and `quarter = 0` as `CloseoutPreload24.wait_exit_debt_zero` /
`CloseoutPreload14.wait_exit_double` deliver, of length exactly `mw` as
`CloseoutPreload17.double_spends` delivers) and the single balance `hbal`.  The
conclusion is the one `PostRunC`'s consumers need. -/
theorem runEntriesS_of_double_exitD {c' : GalilScaffoldPlace.Place} {k mw D : ℕ}
    {a : Bool} {bs : List Bool} {v t t' : SearchVM}
    (hr : DoubleTrace bs v t)
    (hv0 : value v.search.debt = 0) (hq : v.search.quarter = 0)
    (hvc : Canonical v.search.debt)
    (htm : t.search.mode = Mode.double) (htw : positive t.search.work = false)
    (hts : t.search.span = ofNat (2 * mw)) (htl : t.lower = ofNat k)
    (hblen : bs.length = mw)
    (hbal : 4 * dpDemand k (2 * mw) + 4 * (bs ++ [a]).count true ≤ mw)
    (hs : searchStep c' a t t') (hdep : DepthAt t' D) (hD : D ≤ prepLen k)
    (hsup : ScanSupplyInv F 2048 I) (hreal : ScanRealized F I) (hpost : PostRunC) :
    ∀ (as : List Bool),
      D + dpEvents (2 * mw + 1) ≤ as.length → PacedL 2048 0 as → RunEntriesS as t' := by
  obtain ⟨hprep, hinv⟩ :=
    stageInvD_of_double_exit hr hv0 hq hvc htm htw hts htl hblen hbal hs
  intro as hlen hpaced
  refine runEntriesS_of_stageInvD hprep hinv hdep hD hsup hreal hpost as _
    (Or.inl ⟨[], .nil _ ?_, by simpa using hlen, by simpa using hpaced⟩)
  rw [hprep.mode]; decide

#print axioms runEntriesS_of_double_exitD

end Consumers

/-! ## 4. Discharging `hbal` -/

/-- **NAMED — the balance holds for a leg paced in phase from its own entry,
unconditionally in `mw`.**  With `2048 * count ≤ mw + 1` and the calibration
`8 * max k 1 ≤ 2 * mw`, the demand `dpDemand k (2 * mw) ≈ mw / 20` plus the
comparisons met fits under `mw / 4` at every `mw ≥ 4 * max k 1`. -/
theorem bal_of_paced {k mw : ℕ} {bs : List Bool} {a : Bool}
    (hcal : 8 * max k 1 ≤ 2 * mw) (hblen : bs.length = mw)
    (hp : PacedL 2048 0 (bs ++ [a])) :
    4 * dpDemand k (2 * mw) + 4 * (bs ++ [a]).count true ≤ mw := by
  have hc := count_le_of_paced hp
  have hl : (bs ++ [a]).length = mw + 1 := by simp [hblen]
  rw [hl] at hc
  have h1 := prepLen_le k
  have h2 := dpEvents_win_le (2 * mw)
  have h3 : k ≤ max k 1 := le_max_left _ _
  have h4 : 1 ≤ max k 1 := le_max_right _ _
  unfold dpDemand
  omega

#print axioms bal_of_paced

/-- **NAMED — the balance at an arbitrary clock phase, for `mw ≥ 8`.**  A
suffix of a paced stream carries slack `≤ 2047`
(`CloseoutPreload18.pacedL_suffix_2047`); one extra comparison may then land in
the leg, which the four smallest windows (`mw ∈ {4, …, 7}`) cannot absorb. -/
theorem bal_of_paced_slack {k mw slack : ℕ} {bs : List Bool} {a : Bool}
    (hcal : 8 * max k 1 ≤ 2 * mw) (hblen : bs.length = mw) (hmw : 8 ≤ mw)
    (hslack : slack ≤ 2047) (hp : PacedL 2048 slack (bs ++ [a])) :
    4 * dpDemand k (2 * mw) + 4 * (bs ++ [a]).count true ≤ mw := by
  have hc : 2048 * (bs ++ [a]).count true ≤ (bs ++ [a]).length + slack := by
    have h := hp (bs ++ [a]).length
    rwa [List.take_length] at h
  have hl : (bs ++ [a]).length = mw + 1 := by simp [hblen]
  rw [hl] at hc
  have h1 := prepLen_le k
  have h2 := dpEvents_win_le (2 * mw)
  have h3 : k ≤ max k 1 := le_max_left _ _
  have h4 : 1 ≤ max k 1 := le_max_right _ _
  unfold dpDemand
  omega

#print axioms bal_of_paced_slack

/-!
## 5. What is left

Closed here: `StageInvD` (§1); `dpSafe_of_stagePrepD` / `runEntriesS_of_stageInvD`
(§2); `stageInvD_of_double_exit` / `runEntriesS_of_double_exitD` (§3) — the
`.double` exit clause of the round trip on the Scala-shaped invariant, replacing
the false radius-shaped clause of `CloseoutPreload24`; `bal_of_paced` /
`bal_of_paced_slack` (§4).

**The one hypothesis:** `hbal : 4 * dpDemand k (2 * mw) + 4 * count ≤ mw`, the
`.double` leg's earnings against the doubled window's demand.  Its Scala
counterpart is the ledger `debt ≥ 0` in `stepRun` (`ScaffoldSearch.scala`
239–240) holding through the first `.run` leg after `doubleWindow`: the leg
credits one unit per four ticks and the DP of the doubled window consumes at
most `dpDemand` units.  §4 discharges it from pacing: in phase from the leg's
entry for every `mw`, or at any phase for `mw ≥ 8`.

**NOT closed:** `postRunC_of_machine` (the induction over all later `.run`
entries), `ScanRealized` on `galilFrameS`, and the phase of the `.double` leg
at the four smallest windows.

**無条件 PAL ∈ PEG は未完.**
-/

end PalPeg.CloseoutPreload28
