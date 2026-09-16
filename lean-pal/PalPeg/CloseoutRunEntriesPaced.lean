import PalPeg.CloseoutReadinessAudit
import PalPeg.GalilScaffoldAdvanceClock

/-!
# Audit of `GalilReplaySpan.RunEntriesPaced`

`GalilReplaySpan` (section `Paced`) replaces the refuted all-lists hypothesis
`RunEntriesAtBegin` (`CloseoutReadinessAudit.not_runEntriesAtBegin`) by the
clock-paced one

```
RunEntriesPaced delay : ∀ v last radius Rad,
  v.search = begin last radius → Canonical last → 0 ≤ value last →
  Canonical radius → value radius = Rad → StageEntry Rad last →
  ∀ av, RunEntriesAllD (advances delay delay (av.map (·, true))) v
```

This file settles it: **`RunEntriesPaced 2048` is false as stated**, refuted by a
finite trace.

## Why pacing is not enough

Pacing bounds the *rate* of comparisons (one per `delay` ticks) but not their
*number*, while `RunEntriesAllD` demands `DpSafeRem` at the entry into `.run` for
the whole remaining suffix, and `DpSafeRem v as → as.count true ≤ value v.debt`
(`CloseoutReadinessAudit.dpSafeRem_count_le`).  So the hypothesis asks a *fixed*
debt to pay for an *unboundedly long* paced tail.

The stage budget does not repair this.  `StageEntry Rad last` is
`∀ k, value last = k → 3 * Rad ≤ 5 * k`, which is free at `Rad = 0`
(`stageEntry_zero`) — and `Rad = 0` is exactly the restart the fallback and init
cycles produce (`restart_stage_bound_fallback`, `restart_stage_bound_init`).  Nor
does `ReadyRem`: its `DpSafeRem` clause is guarded by `mode = .run`, which is
false at `begin` (the search sits in `.grow`, `searchReady_begin`), so it says
nothing about the entry that is at issue.  The debt actually installed along the
way is small and explicit: `initialDebt reset = reset`, and the single grow tick
`begin` dispatches adds `2` (`growStep`), so the search enters `.run` with debt
`2` — while the paced tail of a long enough `av` still holds `3` comparisons.

Unlike `RunEntriesAtBegin`, the trace here must respect `0 ≤ value last`, so it
cannot use the audit's negative lower bound: with `last = reset` the work counter
`begin` installs is `inc reset`, positive, so the trace spends one `growStep`
before `prepare` and reaches `.run` in **eight** events rather than seven.  The
first eight entries of the paced list are `false`, which is what makes the trace
run.

## The correct restatement

The event list must be cut at the end of the stage instead of running on forever:
keep the pacing and add the budget side condition the debt actually supports,

```
RunEntriesPacedS delay : ∀ v last radius Rad, … → StageEntry Rad last →
  ∀ av : List Bool,
    (advances delay delay (av.map (·, true))).count true ≤ stageDebt Rad →
    RunEntriesAllD (advances delay delay (av.map (·, true))) v
```

where `stageDebt Rad` is the debt at the `.run` entry of that stage (`2` at
`Rad = 0`, by `p8_debt` below; in general `value (initialDebt radius)` plus `2`
per grow tick `begin` dispatches).  Equivalently, keep `∀ av` and bound the
availability stream by one stage, `av.length < delay * (stageDebt Rad + 1)`.  The
refutation below says precisely that no such side condition may be dropped: the
counterexample is a paced list that is merely *too long*.
-/

set_option autoImplicit false

namespace PalPeg.CloseoutRunEntriesPaced

open PalPeg PalPeg.GalilReplaySpan PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilSearchReadyInv PalPeg.GalilBranchInvariants2
open PalPeg.GalilScaffoldPrepareControl (State Tick prepare tape)
open PalPeg.GalilScaffoldAdvanceClock (advances)

local notation "value" => GalilScaffoldCounter.value
local notation "Cnt" => GalilScaffoldCounter.Counter

/-! ## 1. The paced list of an all-available stream -/

theorem adv_cons_ne (d clock : ℕ) (h : clock ≠ 1) (es : List (Bool × Bool)) :
    advances d clock ((true, true) :: es) = false :: advances d (clock - 1) es := by
  simp [advances, h]

theorem adv_cons_one (d : ℕ) (es : List (Bool × Bool)) :
    advances d 1 ((true, true) :: es) = true :: advances d d es := by
  simp [advances]

/-- One background tick peeled off a paced all-available stream, in the numeral
form the trace below rewrites with. -/
theorem peel (d clock c' m n : ℕ) (h : clock ≠ 1) (hc : c' = clock - 1) (hm : m = n + 1) :
    advances d clock (List.replicate m (true, true)) =
      false :: advances d c' (List.replicate n (true, true)) := by
  subst hm; subst hc
  rw [List.replicate_succ, adv_cons_ne d clock h]

/-- **A paced tail holds as many comparisons as it has room for.**  With the
clock at `clock` and `clock + k * d` ticks still available, at least `k + 1`
comparisons are still ahead. -/
theorem adv_count_ge (d : ℕ) (hd : 1 ≤ d) :
    ∀ (n k clock : ℕ), 1 ≤ clock → clock + k * d ≤ n →
      k + 1 ≤ (advances d clock (List.replicate n (true, true))).count true := by
  intro n
  induction n with
  | zero => intro k clock h1 h2; omega
  | succ n ih =>
    intro k clock h1 h2
    rw [List.replicate_succ]
    by_cases hc : clock = 1
    · subst hc
      rw [adv_cons_one]
      have hcount :
          (true :: advances d d (List.replicate n (true, true))).count true =
            (advances d d (List.replicate n (true, true))).count true + 1 := by
        simp
      cases k with
      | zero => omega
      | succ k =>
        have hle : d + k * d ≤ n := by
          have hk : (k + 1) * d ≤ n := by
            have h3 : 1 + (k + 1) * d ≤ n + 1 := h2
            omega
          calc d + k * d = (k + 1) * d := by ring
            _ ≤ n := hk
        have := ih k d hd hle
        omega
    · rw [adv_cons_ne d clock hc]
      have := ih k (clock - 1) (by omega) (by omega)
      simpa [List.count_cons] using this

/-! ## 2. A restarted search the paced hypothesis admits -/

/-- The centre place the walker is loaded from: empty, so `copyEnd` fires. -/
def ctr : GalilScaffoldPlace.Place := ⟨[], false⟩

def mach0 : GalilScaffoldControl.Machine 12 := ⟨⟨0, fun _ => GalilScaffoldTape.reset⟩, false⟩

/-- A restarted search whose lower bound and radius are `reset`: `Canonical`,
`0 ≤ value`, and `StageEntry 0 reset` is free, so `RunEntriesPaced` applies. -/
def v0 : SearchVM :=
  ⟨GalilScaffoldSearchFinish.begin GalilScaffoldCounter.reset GalilScaffoldCounter.reset,
    mach0, GalilScaffoldCounter.reset, ctr⟩

theorem v0_search :
    v0.search =
      GalilScaffoldSearchFinish.begin GalilScaffoldCounter.reset GalilScaffoldCounter.reset := rfl

/-- The grow tick `begin` dispatches, because `work = inc reset` is positive. -/
def p1 : State := GalilScaffoldStagePrepare.growStep v0.toPrep
def p2 : State := prepare p1 GalilScaffoldCounter.reset ctr
def p3 : State := {p2 with program := tape p2 10 (fun t => GalilScaffoldTape.write t 5), mode := .lowerHome}
def p4 : State := {p3 with program := tape p3 10 GalilScaffoldTape.moveLeft}
def p5 : State := {p4 with program := tape p4 7 (fun t => GalilScaffoldTape.moveRight (GalilScaffoldTape.write t 4)), work := GalilScaffoldCounter.inc p4.span, mode := .copy}
def p6 : State := {p5 with program := tape p5 7 (fun t => GalilScaffoldTape.write t 5), mode := .home, finalStage := (GalilScaffoldPlace.read p5.walker).isNone}
def p7 : State := {p6 with program := tape p6 7 GalilScaffoldTape.moveLeft}
def p8 : State := {p7 with program := GalilScaffoldControl.start 320 p7.program, mode := .run}

def w (p : State) : SearchVM := SearchVM.ofPrep p 0 GalilScaffoldCounter.reset

theorem step1 : searchStep ctr false v0 (w p1) := rfl

theorem step2 : searchStep ctr false (w p1) (w p2) := rfl

theorem step_tick {p y : State} (hm : p.mode = .lower ∨ p.mode = .lowerHome ∨
    p.mode = .copy ∨ p.mode = .home) (ht : Tick true p y) :
    searchStep ctr false (w p) (w y) := by
  have hmode : (w p).search.mode = p.mode := rfl
  unfold searchStep
  rw [hmode]
  rcases hm with h | h | h | h <;> rw [h] <;>
    exact ⟨y, ht, rfl⟩

theorem step3 : searchStep ctr false (w p2) (w p3) := by
  unfold p3
  exact step_tick (Or.inl rfl) (Tick.lowerEnd p2 rfl (by decide))

theorem step4 : searchStep ctr false (w p3) (w p4) := by
  unfold p4
  exact step_tick (Or.inr (Or.inl rfl)) (Tick.lowerLeft p3 rfl (by decide) (by decide))

theorem step5 : searchStep ctr false (w p4) (w p5) := by
  unfold p5
  exact step_tick (Or.inr (Or.inl rfl)) (Tick.beginCopy p4 rfl (by decide))

theorem step6 : searchStep ctr false (w p5) (w p6) := by
  unfold p6
  exact step_tick (Or.inr (Or.inr (Or.inl rfl))) (Tick.copyEnd p5 rfl (Or.inl (by decide)))

theorem step7 : searchStep ctr false (w p6) (w p7) := by
  unfold p7
  exact step_tick (Or.inr (Or.inr (Or.inr rfl))) (Tick.sourceLeft p6 rfl (by decide) (by decide))

theorem step8 : searchStep ctr false (w p7) (w p8) := by
  unfold p8
  exact step_tick (Or.inr (Or.inr (Or.inr rfl))) (Tick.startRun p7 rfl (by decide))

theorem p7_not_run : (w p7).search.mode ≠ .run := by decide

theorem p8_run : (w p8).search.mode = .run := rfl

/-- The whole debt the stage has at the entry into `.run`: `initialDebt reset`
plus the `2` of the single grow tick. -/
theorem p8_debt : value (w p8).search.debt = 2 := by decide

/-! ## 3. The paced event list of the trace -/

/-- The availability stream: `6144 = 3 * 2048` ticks, all available and
eligible — three comparisons at this pacing, one more than the debt. -/
def av : List Bool := List.replicate 6144 true

/-- What is left of the paced list once the trace has entered `.run`. -/
def rest : List Bool := advances 2048 2040 (List.replicate 6136 (true, true))

theorem paced_shape :
    advances 2048 2048 (av.map (fun b => (b, true))) =
      false :: false :: false :: false :: false :: false :: false :: false :: rest := by
  rw [av, List.map_replicate]
  rw [peel 2048 2048 2047 6144 6143 (by decide) rfl rfl,
    peel 2048 2047 2046 6143 6142 (by decide) rfl rfl,
    peel 2048 2046 2045 6142 6141 (by decide) rfl rfl,
    peel 2048 2045 2044 6141 6140 (by decide) rfl rfl,
    peel 2048 2044 2043 6140 6139 (by decide) rfl rfl,
    peel 2048 2043 2042 6139 6138 (by decide) rfl rfl,
    peel 2048 2042 2041 6138 6137 (by decide) rfl rfl,
    peel 2048 2041 2040 6137 6136 (by decide) rfl rfl]
  rfl

theorem rest_count : 3 ≤ rest.count true :=
  adv_count_ge 2048 (by decide) 6136 2 2040 (by decide) (by decide)

/-! ## 4. The refutation -/

/-- **`RunEntriesPaced 2048` is false.**  The restarted search `v0` — lower bound
and radius `reset`, so `Canonical`, `0 ≤ value`, and `StageEntry 0 reset` free —
walks into `.run` on the eight leading background ticks of the paced list of `av`
with debt `2`, and the closure then demands `DpSafeRem (w p8) rest` while `rest`
still carries three comparisons: `3 ≤ 2`. -/
theorem not_runEntriesPaced : ¬ RunEntriesPaced 2048 := by
  intro h
  have h0 :
      RunEntriesAllD (advances 2048 2048 (av.map (fun b => (b, true)))) v0 :=
    h v0 GalilScaffoldCounter.reset GalilScaffoldCounter.reset 0 v0_search
      (Or.inl rfl) (by decide) (Or.inl rfl) (by decide) (fun k _ => by omega) av
  rw [paced_shape] at h0
  have h1 := (h0 ctr (w p1) step1).2
  have h2 := (h1 ctr (w p2) step2).2
  have h3 := (h2 ctr (w p3) step3).2
  have h4 := (h3 ctr (w p4) step4).2
  have h5 := (h4 ctr (w p5) step5).2
  have h6 := (h5 ctr (w p6) step6).2
  have h7 := (h6 ctr (w p7) step7).2
  have h8 := (h7 ctr (w p8) step8).1
  have hdp : DpSafeRem (w p8) rest := h8 step8 p7_not_run p8_run
  have hcnt := CloseoutReadinessAudit.dpSafeRem_count_le hdp
  rw [p8_debt] at hcnt
  have := rest_count
  omega

#print axioms adv_count_ge
#print axioms paced_shape
#print axioms p8_debt
#print axioms not_runEntriesPaced

end PalPeg.CloseoutRunEntriesPaced
