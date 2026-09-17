import PalPeg.CloseoutPreload11

/-!
# The preparation phase from a `.lower` entry

`CloseoutPreload11` closed naming exactly one gap: `CloseoutPreload5.Phase` —
and with it `entry_shape_at` / `entry_debt_at` — is proved only from a `.grow`
`BeginAt`, so the doubling exit (`CloseoutPreload10.PrepAt k m`, which *is* the
`.lower` entry of a preparation) could not use the stage chain.

This file supplies that.  From `PrepAt k m v` there is **no grow phase at all**:
the state is already the freshly prepared `.lower` state, `work = lower = ofNat k`,
`span = ofNat m`, and the whole pre-entry reachability is one preparation trace.
So the invariant collapses to three clauses (§1 `PhaseP`), the entry shape is the
window the preparation copies — of length `≤ m + 1` with no calibration lemma at
all, since `List.take` truncates (§2), and the entry debt is the starting debt
minus the advances (§3).

* §1 `PhaseP`, `phase_reach_at_prep` — the invariant along `ReachP`.
* §2 `entry_preload_at_prep` — `∃ W lower, W.length ≤ m + 1 ∧ PreloadAt`.
* §3 `entry_debt_at_prep`.
* §4 `dpSafe_of_stagePrepP` — `CloseoutPreload11.dpSafe_of_stagePrep2` at a
  doubling entry, through `dpSafe_entry_km`.
* §5 `runEntriesS_of_stageInvP`, `runEntriesS_of_double_exit` — the stage
  induction and its composition with `CloseoutPreload11.stageStart_of_double_exit`.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPreload12

open PalPeg PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController
open PalPeg.GalilScaffoldPrepareControl (State)
open PalPeg.GalilScaffoldCounter (Counter Canonical value ofNat positive)
open PalPeg.CloseoutReadyStage (DpSafeStage PacedL RunEntriesS)
open PalPeg.CloseoutPreload (PreloadAt run_entry_preload)
open PalPeg.CloseoutDebtAudit (dpEvents)
open PalPeg.CloseoutPreload2 (PrepTrace preloadAt_of_prepRun)
open PalPeg.CloseoutPreload5 (ReachP reachP_ne_run pacedL_prefix_count pacedL_suffix
  append_cons_eq prepMode_four prepTrace_snoc prepStep_debt)
open PalPeg.CloseoutPreload6 (prepLen)
open PalPeg.CloseoutPreload8 (DepthAt PostRun)
open PalPeg.CloseoutPreload10 (PrepAt prepAt_of_double_exit)
open PalPeg.CloseoutPreload11 (StagePrep2 StageInv2 stagePrep_next2 stageCredit
  dpSafe_entry_km stageStart_of_double_exit)
open PalPeg.GalilReplaySpan (stageDebt)

/-! ## 1. The phase invariant from a `.lower` entry -/

/-- **NAMED — the preparation invariant, from a `.lower` entry.**  There is no
grow branch: every pre-entry state is on the preparation trace out of `v`, and
the debt is the starting debt minus one per advance. -/
def PhaseP (v : SearchVM) (bs : List Bool) (x : SearchVM) : Prop :=
  PrepTrace v bs.length x ∧ x.search.mode ≠ GalilScaffoldSearchFinish.Mode.run ∧
    value x.search.debt = value v.search.debt - (bs.count true : ℤ) ∧
    Canonical x.search.debt

/-- The four tick modes at a state on the trace. -/
theorem phaseP_mode4 {v : SearchVM} {bs : List Bool} {x : SearchVM}
    (hm : v.search.mode = GalilScaffoldSearchFinish.Mode.lower) (h : PhaseP v bs x) :
    x.search.mode = GalilScaffoldSearchFinish.Mode.lower ∨
      x.search.mode = GalilScaffoldSearchFinish.Mode.lowerHome ∨
      x.search.mode = GalilScaffoldSearchFinish.Mode.copy ∨
      x.search.mode = GalilScaffoldSearchFinish.Mode.home :=
  prepMode_four (PalPeg.CloseoutPreload4.prepTrace_mode h.1 (Or.inl hm)) h.2.1

/-- **NAMED — the invariant holds all along the pre-entry reachability.**  This is
`CloseoutPreload5.phase_reach` / `CloseoutPreload8.phase_reach_at` at a `.lower`
entry.  `CentreLongAt` is *not* needed: it was only ever used at the `prepare`
dispatch that ends the grow phase, and there is no grow phase here. -/
theorem phase_reach_at_prep {k m : ℕ} {v : SearchVM} (hp : PrepAt k m v) :
    ∀ {bs : List Bool} {x : SearchVM}, ReachP v bs x → PhaseP v bs x := by
  intro bs x h
  induction h with
  | nil hne =>
    exact ⟨by simpa using PrepTrace.nil _, hne, by simp, hp.can⟩
  | snoc x x' bs a c hr hs hne ih =>
    have h4 := phaseP_mode4 hp.mode ih
    have hlen : (bs ++ [a]).length = bs.length + 1 := by simp
    have hcount : ((bs ++ [a]).count true : ℤ)
        = (bs.count true : ℤ) + (if a then 1 else 0) := by cases a <;> simp
    refine ⟨by rw [hlen]; exact prepTrace_snoc ih.1 h4 ⟨c, a, hs⟩, hne, ?_, ?_⟩
    · rw [prepStep_debt h4 hs, hcount]
      cases a <;> simp [GalilScaffoldCounter.dec_value, ih.2.2.1] <;> omega
    · rw [prepStep_debt h4 hs]
      cases a
      · exact ih.2.2.2
      · exact GalilScaffoldCounter.dec_canonical _ ih.2.2.2

#print axioms phase_reach_at_prep

/-! ## 2. The entry shape at a `.lower` entry -/

/-- **NAMED — the preload witness at a doubling entry.**  `entry_shape_at`'s
payload, at `(k, m)`: the window the preparation copied is
`(stream v.walker).take (m + 1)`, whose length is `≤ m + 1` outright — no
calibration hypothesis, because `List.take` truncates rather than pads.  This is
precisely the clause `CloseoutPreload11.dpSafe_entry_km` consumes. -/
theorem entry_preload_at_prep {k m : ℕ} {v : SearchVM} (hp : PrepAt k m v)
    {bs : List Bool} {x x' : SearchVM} {c : GalilScaffoldPlace.Place} {a : Bool}
    (hr : ReachP v bs x) (hs : searchStep c a x x')
    (hrun : x'.search.mode = GalilScaffoldSearchFinish.Mode.run) :
    ∃ (W : List (Fin 3)) (lower : ℕ), W.length ≤ m + 1 ∧ PreloadAt x.toPrep W lower := by
  have hph := phase_reach_at_prep hp hr
  refine ⟨(GalilScaffoldPlace.stream v.toPrep.walker).take (m + 1), k, ?_, ?_⟩
  · rw [List.length_take]; omega
  · refine preloadAt_of_prepRun v.toPrep k m bs.length hp.mode hp.work hp.span
      hp.ten (hp.other 7 (by decide)) (fun i _ hi => hp.other i hi)
      ⟨v, rfl, hph.1⟩ hs (reachP_ne_run hr) hrun

#print axioms entry_preload_at_prep

/-! ## 3. The entry debt at a `.lower` entry -/

/-- **NAMED — the entry debt, from a `.lower` entry.**  `entry_debt_at` with the
starting debt left symbolic: a doubling entry does not install `-Rad`, it
inherits whatever the previous stage left (`stageStart_of_double_exit`). -/
theorem entry_debt_at_prep {k m : ℕ} {v : SearchVM} (hp : PrepAt k m v)
    {bs : List Bool} {x x' : SearchVM} {c : GalilScaffoldPlace.Place} {a : Bool}
    (hr : ReachP v bs x) (hs : searchStep c a x x')
    (hrun : x'.search.mode = GalilScaffoldSearchFinish.Mode.run) :
    Canonical x'.search.debt ∧
      value x'.search.debt = value v.search.debt - (((bs ++ [a]).count true : ℕ) : ℤ) := by
  have hph := phase_reach_at_prep hp hr
  have hdebt := PalPeg.CloseoutRunEntriesS.run_entry_debt hs (reachP_ne_run hr) hrun
  have hcount : (((bs ++ [a]).count true : ℕ) : ℤ)
      = ((bs.count true : ℕ) : ℤ) + (if a then 1 else 0) := by cases a <;> simp
  refine ⟨?_, ?_⟩
  · rw [hdebt]; cases a
    · exact hph.2.2.2
    · exact GalilScaffoldCounter.dec_canonical _ hph.2.2.2
  · rw [hdebt, hcount]; cases a
    · simp only [Bool.false_eq_true, if_false]; rw [hph.2.2.1]; ring
    · simp only [if_true]; rw [GalilScaffoldCounter.dec_value, hph.2.2.1]; ring

#print axioms entry_debt_at_prep

/-! ## 4. The DP entry at a doubling stage -/

/-- **NAMED — `CloseoutPreload11.dpSafe_of_stagePrep2` at a doubling entry.**
The `.grow` version needed `BeginAt`, `CentreLongAt` and `m = 8 * max k 1`; this
one needs only `PrepAt k m`, the calibration inequality `8 * max k 1 ≤ m`, and a
starting debt at least `stageDebt Rad k + stageCredit k m` — which is exactly
what `stageStart_of_double_exit` delivers. -/
theorem dpSafe_of_stagePrepP {k m Rad D : ℕ} {v : SearchVM}
    (hp : PrepAt k m v) (hstage : 3 * Rad ≤ 5 * k) (hcal : 8 * max k 1 ≤ m)
    (hE : stageDebt Rad (k : ℤ) + (stageCredit k m : ℤ) ≤ value v.search.debt)
    (hdep : DepthAt v D) (hD : D ≤ prepLen k)
    {x x' : SearchVM} {c : GalilScaffoldPlace.Place} {a : Bool} {as : List Bool}
    (hq : StagePrep2 k m D v x (a :: as)) (hs : searchStep c a x x')
    (hrun : x'.search.mode = GalilScaffoldSearchFinish.Mode.run) :
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
  refine dpSafe_entry_km (Rad := Rad) (k := k) (m := m) (L := (bs ++ [a]).length)
    (adv := (bs ++ [a]).count true) (lower := lower) hstage hcal hW hadv (by omega)
    (run_entry_preload hs hne hrun hpreload) hrun hcan ?_ ?_ (pacedL_suffix hpaced')
  · rw [hdv]; omega
  · have hlen' : D + dpEvents (m + 1) ≤ bs.length + (as.length + 1) := hlen
    omega

#print axioms dpSafe_of_stagePrepP

/-! ## 5. The stage induction, and the doubling exit -/

/-- `CloseoutPreload11.runEntriesS_of_stageInv2`, from a `.lower` entry. -/
theorem runEntriesS_of_stageInvP {k m Rad D : ℕ} {v : SearchVM}
    (hp : PrepAt k m v) (hstage : 3 * Rad ≤ 5 * k) (hcal : 8 * max k 1 ≤ m)
    (hE : stageDebt Rad (k : ℤ) + (stageCredit k m : ℤ) ≤ value v.search.debt)
    (hdep : DepthAt v D) (hD : D ≤ prepLen k) (hpost : PostRun) :
    ∀ (as : List Bool) (x : SearchVM), StageInv2 k m D v x as → RunEntriesS as x := by
  intro as
  induction as with
  | nil => intro x _; trivial
  | cons a as ih =>
    intro x hq
    rcases hq with hq | hq
    · intro c x' hstep
      by_cases hr : x'.search.mode = GalilScaffoldSearchFinish.Mode.run
      · have hsafe := dpSafe_of_stagePrepP hp hstage hcal hE hdep hD hq hstep hr
        exact ⟨fun _ _ _ => hsafe, hpost x' as hr hsafe⟩
      · exact ⟨fun _ _ h => absurd h hr, ih x' (Or.inl (stagePrep_next2 hq hstep hr))⟩
    · exact hq

#print axioms runEntriesS_of_stageInvP

/-- **NAMED — the doubling exit runs the next stage.**  Composition of
`CloseoutPreload11.stageStart_of_double_exit` with §4: a spent `.double` phase at
span `m` and lower bound `k`, whose debt still covers
`stageDebt Rad k + stageCredit k m + 1`, dispatches into a stage whose every
`.run` entry is DP-safe. -/
theorem runEntriesS_of_double_exit {c : GalilScaffoldPlace.Place} {t t' : SearchVM}
    {a : Bool} {k m Rad D : ℕ}
    (htm : t.search.mode = GalilScaffoldSearchFinish.Mode.double)
    (htw : positive t.search.work = false)
    (hsp : t.search.span = ofNat m) (hlow : t.lower = ofNat k)
    (hcal : 8 * max k 1 ≤ m) (hc : Canonical t.search.debt)
    (hstage : 3 * Rad ≤ 5 * k)
    (hE : stageDebt Rad (k : ℤ) + (stageCredit k m : ℤ) + 1 ≤ value t.search.debt)
    (hs : searchStep c a t t')
    (hdep : DepthAt t' D) (hD : D ≤ prepLen k) (hpost : PostRun) :
    ∀ (as : List Bool),
      D + dpEvents (m + 1) ≤ as.length → PacedL 2048 0 as → RunEntriesS as t' := by
  have hst := stageStart_of_double_exit (E := stageDebt Rad (k : ℤ) + (stageCredit k m : ℤ))
    htm htw hsp hlow hcal hc hE hs
  obtain ⟨hprep, -, -⟩ := prepAt_of_double_exit htm htw hsp hlow hc hs
  intro as hlen hpaced
  refine runEntriesS_of_stageInvP hprep hstage hcal hst.debt hdep hD hpost as _
    (Or.inl ⟨[], .nil _ ?_, by simpa using hlen, by simpa using hpaced⟩)
  rw [hprep.mode]; decide

#print axioms runEntriesS_of_double_exit

/-!
## Note — what is closed, and what is left

Closed here: the fact `CloseoutPreload11` named.  `CloseoutPreload5.Phase` is now
available from a `.lower` entry (§1), and with it the entry shape (§2) and the
entry debt (§3), so the `(k, m)` stage chain of `CloseoutPreload11` runs at a
doubling entry exactly as it does at a restart (§4, §5) — and, unlike the `.grow`
case, without any `CentreLongAt` premise and without a calibration lemma for the
window, because the copied window is a `List.take` and `dpSafe_entry_km` asks
only for `≤ m + 1`.

`readyClosure_S2` / `replay_final_of_decodes_S2` are **not** thereby made
unconditional.  Their remaining hypothesis is `PostRun`, and `PostRun` is a
statement about the **run** phase, not the preparation phase:

> once the DP has been handed a safe stage, every later `.run` entry on the same
> event list is safe — i.e. the `.run` → `.wait`/`.double` → `prepare` round trip
> preserves the ledger.

§5 supplies the *last leg* of that round trip (the `.double` exit re-enters a
safe stage, `runEntriesS_of_double_exit`).  The one machine fact still missing is
the leg before it:

> a `.run` phase entered DP-safe at window `m` exits into `.wait`/`.double` with
> `span = ofNat m`, the same `lower = ofNat k`, and debt still at least
> `stageDebt Rad k + stageCredit k (2 * m) + 1` — the doubled-window budget,
> which `CloseoutPreload11.credit_double` shows the `.double` phase's own
> quarter-credit pays for.

**無条件 PAL ∈ PEG は未完.**
-/

end PalPeg.CloseoutPreload12
