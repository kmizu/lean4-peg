import PalPeg.GalilReplaySpan
import PalPeg.GalilLeafPres

/-!
# Audit of `GalilReplaySpan.RunEntriesAtBegin`

`GalilReplaySpan` (section `Fuel`) closes the segment construction under the
single named hypothesis

```
RunEntriesAtBegin : ∀ (v : SearchVM) (last radius : Counter),
  v.search = GalilScaffoldSearchFinish.begin last radius → ∀ as, RunEntriesAllD as v
```

i.e. the *all-lists* `.run`-entry closure at every restarted search.  This file
settles it: **`RunEntriesAtBegin` is false**, refuted by a finite trace.

## Why the quantifier ranges are fatal

`RunEntriesAllD` is quantified over *every* event list `as` and, at each step,
over *every* centre and *every* successor the relation `searchStep` admits.
`GalilSegmentConstructB`'s own preamble already records that the all-lists
closure "is false at any `.run` state (an all-`true` budget would demand
unbounded debt)"; `RunEntriesAtBegin` reinstates exactly that closure one
restart earlier, and `begin` reaches a `.run` entry in seven `searchStep`s.

Concretely `RunEntry` at the entry into `.run` demands `DpSafeRem v' as` for the
*remaining* list `as`, and `DpSafeRem v' as → as.count true ≤ value v'.debt`
(`dpSafeRem_count_le`, §1).  At a restart the debt is `initialDebt radius`, so
with `radius = reset` it is `0`, while `as` may be `[true]`.

The trace (§2), all seven events `false` so that no debt is paid:
`begin` is `.grow` with `work = lower`; choosing `lower` non-zero and
non-positive the grow tick dispatches `prepare` (→ `.lower`, `work := v.lower =
reset`), then `lowerEnd` → `.lowerHome`, `lowerLeft` (tape 10 is
`GalilScaffoldTape.moveRight (write reset 4)`, so its `left` is `[4]`) → focus `4`, `beginCopy` →
`.copy`, `copyEnd` (the centre place is `⟨[], false⟩`, so `read walker = none`)
→ `.home`, `sourceLeft` → focus `4`, `startRun` → `.run`.
-/

set_option autoImplicit false

namespace PalPeg.CloseoutReadinessAudit

open PalPeg PalPeg.GalilReplaySpan PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilSearchReadyInv PalPeg.GalilBranchInvariants2
open PalPeg.GalilScaffoldPrepareControl (State Tick prepare tape)

local notation "value" => GalilScaffoldCounter.value
local notation "Cnt" => GalilScaffoldCounter.Counter


/-! ## 1. What `DpSafeRem` costs -/

/-- **The budget clause of `DpSafeRem`, read at the current configuration.**
Every remaining `true` event must be paid for out of the debt that is there
now. -/
theorem dpSafeRem_count_le {v : SearchVM} {as : List Bool} (h : DpSafeRem v as) :
    ((as.count true : ℤ)) ≤ value v.search.debt := by
  obtain ⟨w, lower, s0, bs, hbud, hs0, hc, hb, hreach⟩ := h
  have hd : value v.search.debt = value s0.debt - (bs.count true : ℤ) :=
    _root_.PalPeg.GalilLeafPres.safeQuanta_value hreach
  have hsplit : ((bs ++ as).count true : ℤ) = (bs.count true : ℤ) + (as.count true : ℤ) := by
    simp [List.count_append]
  omega

/-! ## 2. A restarted search that reaches `.run` in seven steps -/

/-- Non-zero, non-positive: `begin`'s grow tick dispatches `prepare` at once. -/
def lowVal : Cnt := ⟨[], [()]⟩

/-- The centre place the walker is loaded from: empty, so `copyEnd` fires. -/
def ctr : GalilScaffoldPlace.Place := ⟨[], false⟩

def mach0 : GalilScaffoldControl.Machine 12 := ⟨⟨0, fun _ => GalilScaffoldTape.reset⟩, false⟩

/-- A restarted search state. -/
def v0 : SearchVM :=
  ⟨GalilScaffoldSearchFinish.begin lowVal GalilScaffoldCounter.reset, mach0,
    GalilScaffoldCounter.reset, ctr⟩

theorem v0_search : v0.search = GalilScaffoldSearchFinish.begin lowVal GalilScaffoldCounter.reset :=
  rfl

/-- `SearchVM.toPrep` is a left inverse of `SearchVM.ofPrep`. -/
theorem toPrep_ofPrep (p : State) (q : Fin 4) (l : Cnt) :
    (SearchVM.ofPrep p q l).toPrep = p := rfl

def p1 : State := prepare v0.toPrep GalilScaffoldCounter.reset ctr
def p2 : State := {p1 with program := tape p1 10 (fun t => GalilScaffoldTape.write t 5), mode := .lowerHome}
def p3 : State := {p2 with program := tape p2 10 GalilScaffoldTape.moveLeft}
def p4 : State := {p3 with program := tape p3 7 (fun t => GalilScaffoldTape.moveRight (GalilScaffoldTape.write t 4)), work := GalilScaffoldCounter.inc p3.span, mode := .copy}
def p5 : State := {p4 with program := tape p4 7 (fun t => GalilScaffoldTape.write t 5), mode := .home, finalStage := (GalilScaffoldPlace.read p4.walker).isNone}
def p6 : State := {p5 with program := tape p5 7 GalilScaffoldTape.moveLeft}
def p7 : State := {p6 with program := GalilScaffoldControl.start 320 p6.program, mode := .run}

def w (p : State) : SearchVM := SearchVM.ofPrep p 0 GalilScaffoldCounter.reset

theorem step1 : searchStep ctr false v0 (w p1) := rfl

theorem step_tick {p y : State} (hm : p.mode = .lower ∨ p.mode = .lowerHome ∨
    p.mode = .copy ∨ p.mode = .home) (ht : Tick true p y) :
    searchStep ctr false (w p) (w y) := by
  have hmode : (w p).search.mode = p.mode := rfl
  unfold searchStep
  rw [hmode]
  rcases hm with h | h | h | h <;> rw [h] <;>
    exact ⟨y, ht, rfl⟩

theorem step2 : searchStep ctr false (w p1) (w p2) := by
  unfold p2
  exact step_tick (Or.inl rfl) (Tick.lowerEnd p1 rfl (by decide))

theorem step3 : searchStep ctr false (w p2) (w p3) := by
  unfold p3
  exact step_tick (Or.inr (Or.inl rfl)) (Tick.lowerLeft p2 rfl (by decide) (by decide))

theorem step4 : searchStep ctr false (w p3) (w p4) := by
  unfold p4
  exact step_tick (Or.inr (Or.inl rfl)) (Tick.beginCopy p3 rfl (by decide))

theorem step5 : searchStep ctr false (w p4) (w p5) := by
  unfold p5
  exact step_tick (Or.inr (Or.inr (Or.inl rfl))) (Tick.copyEnd p4 rfl (Or.inl (by decide)))

theorem step6 : searchStep ctr false (w p5) (w p6) := by
  unfold p6
  exact step_tick (Or.inr (Or.inr (Or.inr rfl))) (Tick.sourceLeft p5 rfl (by decide) (by decide))

theorem step7 : searchStep ctr false (w p6) (w p7) := by
  unfold p7
  exact step_tick (Or.inr (Or.inr (Or.inr rfl))) (Tick.startRun p6 rfl (by decide))

theorem p6_not_run : (w p6).search.mode ≠ .run := by decide

theorem p7_run : (w p7).search.mode = .run := rfl

theorem p7_debt_zero : value (w p7).search.debt = 0 := by decide

/-! ## 3. The refutation -/

/-- The event list the trace spends: seven background ticks (no debt paid) and
one comparison still ahead at the entry into `.run`. -/
def evs : List Bool := [false, false, false, false, false, false, false, true]

/-- **`RunEntriesAtBegin` is false.**  Not merely unproved: the restarted search
`v0` walks into `.run` on seven `false` events with debt `0`, and the closure
then demands `DpSafeRem` for the remaining `[true]`, i.e. `1 ≤ 0`. -/
theorem not_runEntriesAtBegin : ¬ RunEntriesAtBegin := by
  intro h
  have h0 : RunEntriesAllD evs v0 := h v0 _ _ v0_search evs
  have h1 := (h0 ctr (w p1) step1).2
  have h2 := (h1 ctr (w p2) step2).2
  have h3 := (h2 ctr (w p3) step3).2
  have h4 := (h3 ctr (w p4) step4).2
  have h5 := (h4 ctr (w p5) step5).2
  have h6 := (h5 ctr (w p6) step6).2
  have h7 := (h6 ctr (w p7) step7).1
  have hdp : DpSafeRem (w p7) [true] := h7 step7 p6_not_run p7_run
  have hcnt := dpSafeRem_count_le hdp
  rw [p7_debt_zero] at hcnt
  simp at hcnt

#print axioms dpSafeRem_count_le
#print axioms not_runEntriesAtBegin

end PalPeg.CloseoutReadinessAudit
