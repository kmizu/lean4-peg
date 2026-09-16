import PalPeg.CloseoutPreload

/-!
# `PreloadAtEntry` from the restart trace

`CloseoutPreload` left one residual named:

  `PreloadAtEntry : ∀ v v' center a k, searchStep center a v v' →
      v.search.mode ≠ .run → v'.search.mode = .run →
      ∃ w lower, w.length = stageWindow1 k ∧ PreloadAt v.toPrep w lower`

As a statement about *arbitrary* `v` it is false: nothing in a single
`searchStep` forces the tapes of a `.home` state to be in preload shape.  The
correct premise is the one the machine actually supplies — the entry sits at the
end of a preparation phase started by `prepare` at the restart.  This file
proves it in that form, by **determinism** rather than by rebuilding the tape
invariant:

* §1 `tick_true_det` / `run_true_det` — a `true` preparation tick is a partial
  function, and `.run` is a dead end for `true` ticks (`no_tick_of_run`).
  Hence any two `true`-runs out of the same state that both stop in `.run`
  agree, length included (`run_run_unique`).

* §2 `dErase` — the debt is the only field the paced wrapper
  (`GalilScaffoldPreparePaced.afterAdvance`) touches, and no `Tick` reads or
  writes it.  Erasing it turns a `searchStep` chain through the preparation
  modes into a genuine `GalilScaffoldPrepareControl.Run` (`prepTrace_run`).

* §3 `preloadAt_of_prepRun` — the payoff.  `CloseoutPreload.prep_run_preload`
  builds *one* run from the freshly prepared `.lower` state to `.run`; §1 says
  the trace in hand is that run; so the state entering `.run` carries
  `GalilScaffoldPreload.initial w lower`, and since `startRun` only bumps the
  `pc` (`run_entry_startRun`), the predecessor's tapes are already in preload
  shape: `PreloadAt v.toPrep w lower` with
  `w = (GalilScaffoldPlace.stream s.walker).take (span+1)`.

* §4 `preloadAtEntry_of_trace` — `PreloadAtEntry` in the form
  `CloseoutPreload.EntryPreload` consumes, and `runEntriesS_of_prepInv`, which
  feeds `CloseoutPreload.runEntriesS_of_preloadInv` from a trace-carrying
  invariant.

* §5 `readyClosure_paced` — the `GalilReplaySpan.ReadyClosure` structure for
  `RdPaced`, assembled from `rdPaced_ready`, `rdPaced_seg`, `rdPaced_restart`.

## What is still named

Two things, both calibration rather than shape:

`StageCalibration : ((GalilScaffoldPlace.stream s.walker).take (span+1)).length
    = PalPeg.CloseoutDebtAudit.stageWindow k`

— that the span counter at the restart of stage `k` really is `stageWindow k - 1`
and that the place stream is long enough for the window not to be truncated; and

`RestartEntryS'` (§5) — the length-guarded entry datum that `rdPaced_restart`
consumes; §4 reduces it to the trace premise of §3 plus the two debt facts of
`CloseoutRunEntriesPaced`.  (The *unguarded* `RestartEntryS` is refuted in
`CloseoutPreload3` §2, and `StageCalibration` is settled there too: the window
is `stageWindow1 k = 8 * max k 1 + 1`, which is what this file now uses.)
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace PalPeg.CloseoutPreload2

open PalPeg PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController
open PalPeg.GalilScaffoldPrepareControl (State Tick Run)
open PalPeg.GalilScaffoldCounter (Counter Canonical value)
open PalPeg.CloseoutReadyStage
open PalPeg.CloseoutRunEntriesS
open PalPeg.CloseoutPreload
open PalPeg.CloseoutDebtAudit (dpEvents stageWindow stageWindow1 dpEntry)

/-! ## 1. Determinism of the preparation ticks -/

/-- `.run` is a dead end: no `true` preparation tick leaves it. -/
theorem no_tick_of_run {x y : State} (hm : x.mode = .run) : ¬ Tick true x y := by
  intro ht
  cases ht with
  | lowerBit x hmx hp => rw [hm] at hmx; exact absurd hmx (by decide)
  | lowerEnd x hmx hp => rw [hm] at hmx; exact absurd hmx (by decide)
  | lowerLeft x hmx hf hl => rw [hm] at hmx; exact absurd hmx (by decide)
  | beginCopy x hmx hf => rw [hm] at hmx; exact absurd hmx (by decide)
  | copyBit x a hmx ha hw => rw [hm] at hmx; exact absurd hmx (by decide)
  | copyEnd x hmx he => rw [hm] at hmx; exact absurd hmx (by decide)
  | sourceLeft x hmx hf hl => rw [hm] at hmx; exact absurd hmx (by decide)
  | startRun x hmx hf => rw [hm] at hmx; exact absurd hmx (by decide)

#print axioms no_tick_of_run

/-- **A `true` preparation tick is a partial function.**  The guards of the eight
constructors are pairwise exclusive: the mode separates the four phases, and
inside each phase the counter/head test separates the two branches. -/
theorem tick_true_det {x y z : State} (h1 : Tick true x y) (h2 : Tick true x z) :
    y = z := by
  cases h1 <;> cases h2 <;> simp_all

#print axioms tick_true_det

/-- Determinism along an all-`true` run of a fixed length. -/
theorem run_true_det : ∀ (n : ℕ) {x y z : State},
    Run x (List.replicate n true) y → Run x (List.replicate n true) z → y = z := by
  intro n
  induction n with
  | zero =>
    intro x y z h1 h2
    cases h1; cases h2; rfl
  | succ n ih =>
    intro x y z h1 h2
    rw [List.replicate_succ] at h1 h2
    cases h1 with
    | cons _ u _ _ _ ht1 hr1 =>
      cases h2 with
      | cons _ u' _ _ _ ht2 hr2 =>
        cases tick_true_det ht1 ht2
        exact ih hr1 hr2

#print axioms run_true_det

/-- An all-`true` run out of a `.run` state is empty. -/
theorem run_of_run_mode {x y : State} {n : ℕ} (hm : x.mode = .run)
    (hr : Run x (List.replicate n true) y) : n = 0 ∧ y = x := by
  cases n with
  | zero => cases hr; exact ⟨rfl, rfl⟩
  | succ n =>
    rw [List.replicate_succ] at hr
    cases hr with
    | cons _ u _ _ _ ht _ => exact absurd ht (no_tick_of_run hm)

#print axioms run_of_run_mode

/-- Splitting a run at a concatenation of event lists. -/
theorem run_split_append : ∀ {bs : List Bool} {cs : List Bool} {x z : State},
    Run x (bs ++ cs) z → ∃ y, Run x bs y ∧ Run y cs z := by
  intro bs
  induction bs with
  | nil => intro cs x z hr; exact ⟨x, .nil x, hr⟩
  | cons b bs ih =>
    intro cs x z hr
    rw [List.cons_append] at hr
    cases hr with
    | cons _ u _ _ _ ht hr =>
      obtain ⟨y, h1, h2⟩ := ih hr
      exact ⟨y, .cons _ u _ _ _ ht h1, h2⟩

#print axioms run_split_append

/-- **Two all-`true` runs out of the same state that both stop in `.run` agree.**
Determinism plus the dead-end property of `.run`. -/
theorem run_run_unique {x y z : State} {n m : ℕ}
    (h1 : Run x (List.replicate n true) y) (h2 : Run x (List.replicate m true) z)
    (hy : y.mode = .run) (hz : z.mode = .run) : y = z := by
  rcases Nat.le_total n m with hle | hle
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
    subst hd
    rw [List.replicate_add] at h2
    obtain ⟨w, hw1, hw2⟩ := run_split_append h2
    cases run_true_det n h1 hw1
    exact ((run_of_run_mode hy hw2).2).symm
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
    subst hd
    rw [List.replicate_add] at h1
    obtain ⟨w, hw1, hw2⟩ := run_split_append h1
    cases run_true_det m h2 hw1
    exact (run_of_run_mode hz hw2).2

#print axioms run_run_unique

/-! ## 2. Erasing the debt: a `searchStep` chain is a preparation `Run` -/

/-- The debt is the only field the paced wrapper touches, and no `Tick` reads it.
`dErase` normalises it away. -/
def dErase (x : State) : State := { x with debt := GalilScaffoldCounter.ofNat 0 }

@[simp] theorem dErase_mode (x : State) : (dErase x).mode = x.mode := rfl
@[simp] theorem dErase_program (x : State) : (dErase x).program = x.program := rfl
@[simp] theorem dErase_walker (x : State) : (dErase x).walker = x.walker := rfl
@[simp] theorem dErase_work (x : State) : (dErase x).work = x.work := rfl
@[simp] theorem dErase_span (x : State) : (dErase x).span = x.span := rfl

theorem dErase_afterAdvance (a : Bool) (x : State) :
    dErase (GalilScaffoldPreparePaced.afterAdvance a x) = dErase x := by
  cases a <;> rfl

/-- Ticks do not see the debt. -/
theorem tick_dErase {x y : State} {b : Bool} (ht : Tick b x y) :
    Tick b (dErase x) (dErase y) := by
  cases ht with
  | idle x => exact .idle _
  | lowerBit x hm hp => exact .lowerBit _ hm hp
  | lowerEnd x hm hp => exact .lowerEnd _ hm hp
  | lowerLeft x hm hf hl => exact .lowerLeft _ hm hf hl
  | beginCopy x hm hf => exact .beginCopy _ hm hf
  | copyBit x a hm ha hw => exact .copyBit _ a hm ha hw
  | copyEnd x hm he => exact .copyEnd _ hm he
  | sourceLeft x hm hf hl => exact .sourceLeft _ hm hf hl
  | startRun x hm hf => exact .startRun _ hm hf

#print axioms tick_dErase

/-- A chain of `searchStep`s all taken in the four preparation modes. -/
inductive PrepTrace : SearchVM → ℕ → SearchVM → Prop
  | nil (v : SearchVM) : PrepTrace v 0 v
  | cons (v v' w : SearchVM) (n : ℕ)
      (hm : v.search.mode = .lower ∨ v.search.mode = .lowerHome ∨
        v.search.mode = .copy ∨ v.search.mode = .home)
      (hs : ∃ (center : GalilScaffoldPlace.Place) (a : Bool), searchStep center a v v')
      (hr : PrepTrace v' n w) :
      PrepTrace v (n + 1) w

/-- A preparation `searchStep` *is* a preparation tick, up to the debt. -/
theorem prepStep_tick {center : GalilScaffoldPlace.Place} {a : Bool} {v v' : SearchVM}
    (hm : v.search.mode = .lower ∨ v.search.mode = .lowerHome ∨
      v.search.mode = .copy ∨ v.search.mode = .home)
    (hs : searchStep center a v v') :
    Tick true (dErase v.toPrep) (dErase v'.toPrep) := by
  unfold searchStep at hs
  have hstep : ∃ y, Tick true v.toPrep y ∧
      v' = SearchVM.ofPrep (GalilScaffoldPreparePaced.afterAdvance a y)
        v.search.quarter v.lower := by
    rcases hm with hm | hm | hm | hm <;> rw [hm] at hs <;> exact hs
  obtain ⟨y, hy, hv'⟩ := hstep
  have : dErase v'.toPrep = dErase y := by
    rw [hv', toPrep_ofPrep, dErase_afterAdvance]
  rw [this]
  exact tick_dErase hy

#print axioms prepStep_tick

/-- **A preparation trace is a preparation `Run`.** -/
theorem prepTrace_run {v w : SearchVM} {n : ℕ} (h : PrepTrace v n w) :
    Run (dErase v.toPrep) (List.replicate n true) (dErase w.toPrep) := by
  induction h with
  | nil v => exact .nil _
  | cons v v' w n hm hs hr ih =>
    rw [List.replicate_succ]
    obtain ⟨center, a, hs⟩ := hs
    exact .cons _ _ _ _ _ (prepStep_tick hm hs) ih

#print axioms prepTrace_run

/-! ## 3. `PreloadAt` at the entry, from the restart trace -/

/-- **The payoff.**  If the state `v` at a `.run` entry is reachable from the
freshly prepared `.lower` state `s` by a preparation trace, then its tapes are in
preload shape for the window the preparation copied.  No tape invariant is
rebuilt: `prep_run_preload` supplies *one* run to `.run`, and §1 says the trace
in hand ends at the same state. -/
theorem preloadAt_of_prepRun {center : GalilScaffoldPlace.Place} {a : Bool}
    {v v' : SearchVM} (s : State) (lower span n : ℕ)
    (hm : s.mode = .lower) (hw : s.work = GalilScaffoldCounter.ofNat lower)
    (hspan : s.span = GalilScaffoldCounter.ofNat span)
    (h10 : s.program.config.tapes 10 =
      GalilScaffoldTape.moveRight (GalilScaffoldTape.write GalilScaffoldTape.reset 4))
    (h7 : s.program.config.tapes 7 = GalilScaffoldTape.reset)
    (hother : ∀ i : Fin 12, i ≠ 7 → i ≠ 10 →
      s.program.config.tapes i = GalilScaffoldTape.reset)
    (htr : ∃ v0 : SearchVM, v0.toPrep = s ∧ PrepTrace v0 n v)
    (hs : searchStep center a v v') (hne : v.search.mode ≠ .run)
    (hr : v'.search.mode = .run) :
    PreloadAt v.toPrep ((GalilScaffoldPlace.stream s.walker).take (span + 1)) lower := by
  classical
  obtain ⟨v0, hv0, htrace⟩ := htr
  -- the run supplied by the preparation phase, on the debt-erased state
  obtain ⟨t, hrunt, htm, htprog, -⟩ :=
    prep_run_preload (dErase s) lower span hm hw hspan h10 h7 hother
  -- the trace in hand, extended by the entry tick
  obtain ⟨hmode, hfocus, -⟩ := run_entry_startRun hs hne hr
  have hu : Tick true (dErase v.toPrep) (dErase v'.toPrep) :=
    prepStep_tick (Or.inr (Or.inr (Or.inr hmode))) hs
  have hrun0 : Run (dErase s) (List.replicate n true) (dErase v.toPrep) := by
    rw [← hv0]; exact prepTrace_run htrace
  have hrun1 : Run (dErase s) (List.replicate (n + 1) true) (dErase v'.toPrep) := by
    rw [List.replicate_succ']
    exact GalilScaffoldPrepareControl.run_append hrun0 (.cons _ _ _ _ _ hu (.nil _))
  have hr' : (dErase v'.toPrep).mode = GalilScaffoldSearchFinish.Mode.run := hr
  -- both stop in `.run`, hence at the same state
  have heq := run_run_unique hrun1 hrunt hr' htm
  have hprog : GalilScaffoldControl.start 320 v.toPrep.program =
      (⟨GalilScaffoldPreload.initial
        ((GalilScaffoldPlace.stream s.walker).take (span + 1)) lower, false⟩ :
        GalilScaffoldControl.Machine 12) := by
    have h1 : v'.toPrep.program = GalilScaffoldControl.start 320 v.toPrep.program :=
      run_entry_dp hs hne hr
    have h2 : (dErase v'.toPrep).program = t.program := by rw [heq]
    rw [← h1]
    exact h2.trans htprog
  have htapes : ∀ i : Fin 12, v.toPrep.program.config.tapes i =
      (GalilScaffoldPreload.initial
        ((GalilScaffoldPlace.stream s.walker).take (span + 1)) lower).tapes i := by
    intro i
    have := congrArg (fun m : GalilScaffoldControl.Machine 12 => m.config.tapes i) hprog
    simpa [GalilScaffoldControl.start] using this
  refine ⟨?_, ?_, ?_⟩
  · rw [htapes 7]; rfl
  · rw [htapes 10]; rfl
  · intro i hi7 hi10
    rw [htapes i]
    simp [GalilScaffoldPreload.initial, hi7, hi10]

#print axioms preloadAt_of_prepRun

/-! ## 4. Packaging: `PreloadAtEntry` and `RunEntriesS` from a trace invariant -/

/-- **`PreloadAtEntry` in the form `EntryPreload` consumes.**  The window length
is the one named residual (`StageCalibration`). -/
theorem preloadAtEntry_of_trace {center : GalilScaffoldPlace.Place} {a : Bool}
    {v v' : SearchVM} (s : State) (lower span n k : ℕ)
    (hm : s.mode = .lower) (hw : s.work = GalilScaffoldCounter.ofNat lower)
    (hspan : s.span = GalilScaffoldCounter.ofNat span)
    (h10 : s.program.config.tapes 10 =
      GalilScaffoldTape.moveRight (GalilScaffoldTape.write GalilScaffoldTape.reset 4))
    (h7 : s.program.config.tapes 7 = GalilScaffoldTape.reset)
    (hother : ∀ i : Fin 12, i ≠ 7 → i ≠ 10 →
      s.program.config.tapes i = GalilScaffoldTape.reset)
    (hcal : ((GalilScaffoldPlace.stream s.walker).take (span + 1)).length = stageWindow1 k)
    (htr : ∃ v0 : SearchVM, v0.toPrep = s ∧ PrepTrace v0 n v)
    (hs : searchStep center a v v') (hne : v.search.mode ≠ .run)
    (hr : v'.search.mode = .run) :
    ∃ (w : List (Fin 3)) (l : ℕ), w.length = stageWindow1 k ∧ PreloadAt v.toPrep w l :=
  ⟨(GalilScaffoldPlace.stream s.walker).take (span + 1), lower, hcal,
    preloadAt_of_prepRun s lower span n hm hw hspan h10 h7 hother htr hs hne hr⟩

#print axioms preloadAtEntry_of_trace

/-- The restart data an invariant has to carry for §3 to fire at every entry. -/
def TracePreload (Q : SearchVM → List Bool → Prop) (k : ℕ) : Prop :=
  ∀ (v : SearchVM) (as : List Bool), Q v as →
    ∃ (s : State) (lower span n : ℕ) (v0 : SearchVM),
      s.mode = .lower ∧ s.work = GalilScaffoldCounter.ofNat lower ∧
      s.span = GalilScaffoldCounter.ofNat span ∧
      s.program.config.tapes 10 =
        GalilScaffoldTape.moveRight (GalilScaffoldTape.write GalilScaffoldTape.reset 4) ∧
      s.program.config.tapes 7 = GalilScaffoldTape.reset ∧
      (∀ i : Fin 12, i ≠ 7 → i ≠ 10 →
        s.program.config.tapes i = GalilScaffoldTape.reset) ∧
      ((GalilScaffoldPlace.stream s.walker).take (span + 1)).length = stageWindow1 k ∧
      v0.toPrep = s ∧ PrepTrace v0 n v

/-- **`EntryPreload` from a trace-carrying invariant.**  The preload half is §3;
the debt and pacing halves stay as hypotheses (they are the data
`CloseoutRunEntriesPaced` supplies at the restart). -/
theorem entryPreload_of_trace {Q : SearchVM → List Bool → Prop} {Rad k slack : ℕ}
    (htr : TracePreload Q k)
    (hnext : ∀ (v v' : SearchVM) (c : GalilScaffoldPlace.Place) (a : Bool) (as : List Bool),
      Q v (a :: as) → searchStep c a v v' → Q v' as)
    (hcan : ∀ (v v' : SearchVM) (c : GalilScaffoldPlace.Place) (a : Bool) (as : List Bool),
      Q v (a :: as) → searchStep c a v v' → v.search.mode ≠ .run →
        v'.search.mode = .run → Canonical v'.search.debt)
    (hdebt : ∀ (v v' : SearchVM) (c : GalilScaffoldPlace.Place) (a : Bool) (as : List Bool),
      Q v (a :: as) → searchStep c a v v' → v.search.mode ≠ .run →
        v'.search.mode = .run →
          PalPeg.GalilReplaySpan.stageDebt Rad (k : ℤ) ≤ value v'.search.debt)
    (hlen : ∀ (v v' : SearchVM) (c : GalilScaffoldPlace.Place) (a : Bool) (as : List Bool),
      Q v (a :: as) → searchStep c a v v' → v.search.mode ≠ .run →
        v'.search.mode = .run → dpEvents (stageWindow1 k) ≤ as.length)
    (hpaced : ∀ (v v' : SearchVM) (c : GalilScaffoldPlace.Place) (a : Bool) (as : List Bool),
      Q v (a :: as) → searchStep c a v v' → v.search.mode ≠ .run →
        v'.search.mode = .run → PacedL 2048 slack as) :
    EntryPreload Q Rad k slack := by
  intro v v' c a as hq hstep
  refine ⟨fun hne hr => ⟨?_, hcan v v' c a as hq hstep hne hr,
    hdebt v v' c a as hq hstep hne hr, hlen v v' c a as hq hstep hne hr,
    hpaced v v' c a as hq hstep hne hr⟩,
    hnext v v' c a as hq hstep⟩
  obtain ⟨s, lower, span, n, v0, hm, hw, hspan, h10, h7, hother, hcal, hv0, htrace⟩ :=
    htr v (a :: as) hq
  exact preloadAtEntry_of_trace s lower span n k hm hw hspan h10 h7 hother hcal
    ⟨v0, hv0, htrace⟩ hstep hne hr

#print axioms entryPreload_of_trace

/-- **`RunEntriesS` for every event list, from the restart trace.**  §3 + §4 +
`CloseoutPreload.runEntriesS_of_preloadInv`. -/
theorem runEntriesS_of_trace {Q : SearchVM → List Bool → Prop} {Rad k slack : ℕ}
    (hstage : 3 * Rad ≤ 5 * k) (hslack : slack ≤ 2047)
    (htr : TracePreload Q k)
    (hnext : ∀ (v v' : SearchVM) (c : GalilScaffoldPlace.Place) (a : Bool) (as : List Bool),
      Q v (a :: as) → searchStep c a v v' → Q v' as)
    (hcan : ∀ (v v' : SearchVM) (c : GalilScaffoldPlace.Place) (a : Bool) (as : List Bool),
      Q v (a :: as) → searchStep c a v v' → v.search.mode ≠ .run →
        v'.search.mode = .run → Canonical v'.search.debt)
    (hdebt : ∀ (v v' : SearchVM) (c : GalilScaffoldPlace.Place) (a : Bool) (as : List Bool),
      Q v (a :: as) → searchStep c a v v' → v.search.mode ≠ .run →
        v'.search.mode = .run →
          PalPeg.GalilReplaySpan.stageDebt Rad (k : ℤ) ≤ value v'.search.debt)
    (hlen : ∀ (v v' : SearchVM) (c : GalilScaffoldPlace.Place) (a : Bool) (as : List Bool),
      Q v (a :: as) → searchStep c a v v' → v.search.mode ≠ .run →
        v'.search.mode = .run → dpEvents (stageWindow1 k) ≤ as.length)
    (hpaced : ∀ (v v' : SearchVM) (c : GalilScaffoldPlace.Place) (a : Bool) (as : List Bool),
      Q v (a :: as) → searchStep c a v v' → v.search.mode ≠ .run →
        v'.search.mode = .run → PacedL 2048 slack as) :
    ∀ (as : List Bool) (v : SearchVM), Q v as → RunEntriesS as v :=
  runEntriesS_of_preloadInv hstage hslack
    (entryPreload_of_trace htr hnext hcan hdebt hlen hpaced)

#print axioms runEntriesS_of_trace

/-! ## 5. The ledger closure, assembled -/

/-- **The entry datum, length-guarded.**  The refutation of
`CloseoutPreload3.not_restartEntryS_ofSearch` is that the unguarded form asks the
entry datum of *every* paced list, including ones shorter than the stage's own
DP run.  The true shape carries the entry length `dpEntry k = 8 + dpEvents
(stageWindow1 k)` — the eight preparation events plus the charged prefix of the
stage — as a lower bound on the event list. -/
def RestartEntryS' (raw : List (Fin 2)) : Prop :=
  ∀ (u : GalilVM) (Rad : ℕ) (last : Counter),
    Restarted raw u Rad last → StageEntry Rad last →
    ∀ (m : ℕ) (as : List Bool),
      dpEntry (value last).toNat + m ≤ as.length → PacedL 2048 0 as →
      RunEntriesS as (searchLens.get u)

/-- **`GalilReplaySpan.ReadyClosure` for `RdPaced`.**  The three fields are
`CloseoutPreload.rdPaced_ready`, `rdPaced_seg`, `rdPaced_restart`; the last one
consumes the length-guarded `RestartEntryS'`, which §4 reduces to the trace
premise of §3. -/
theorem readyClosure_paced (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9)
    (hE : RestartEntryS' raw) :
    PalPeg.GalilReplaySpan.ReadyClosure raw P q first 2048 RdPaced where
  ready := fun c s h => rdPaced_ready c s h
  seg := fun es c c' s t hseg hidle h => rdPaced_seg P q first es c c' s t hseg hidle h
  restart := fun c u Rad last _ hclk hR hSE =>
    rdPaced_restart c u Rad last (dpEntry (value last).toNat) hclk hR (hE u Rad last hR hSE)

#print axioms readyClosure_paced

end PalPeg.CloseoutPreload2
