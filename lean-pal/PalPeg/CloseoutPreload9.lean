import PalPeg.CloseoutPreload8

/-!
# The stage boundary: the `.double` phase terminates, and the doubled stage's
# parameters survive

`CloseoutPreload8` left exactly one residual, `PostRun`, and its note named the
two pieces that were genuinely absent.  This file supplies both halves that are
*arithmetic or counter* facts, leaving a single machine fact behind.

* §1 `DoubleReach`, `doubleReach_step`, `doubleS_complete` — the `.double`
  phase **terminates**.  `GalilScaffoldDouble.complete` proves this for the
  finish-state counter; here it is lifted to `searchStep` on `SearchVM`, driven
  by an arbitrary event list instead of a chosen one: from a `.double` state
  with `work = ofNat n`, the first `n` events of *any* long enough list reach a
  state with `positive work = false`, `span = ofNat (sp + 2*n)`, and the lower
  bound, walker and DP untouched.  At that state `CloseoutPreload8.step_double_dispatch`
  fires and the next stage's `prepare` is dispatched.
* §2 `stage_span_double`, `stage_bound_double`, `dpEvents_double` — the doubled
  stage's parameters.  The span exported by §1 is `2 * k` (the `.double` entry
  loads `work := span`, and `span` gains `2` per tick), so `k' = 2 * k`; the
  entry inequality `3 * Rad' ≤ 5 * k'` is then free for any `Rad' ≤ 2 * Rad`,
  and the DP event demand at most doubles (`+1` for the flooring).
* §3 the residual, recorded honestly: the supply clause
  `dpEvents (stageWindow1 k') ≤ as.length` is **not** removed by a short input
  (`dpSafeStage_entry_min`'s window relaxation shrinks the *window*, not the
  event count demanded, which is computed from `k` alone), and the one missing
  machine fact is named in `StageBoundary`.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPreload9

open PalPeg PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController
open PalPeg.GalilScaffoldCounter (Counter Canonical value ofNat positive)
open PalPeg.CloseoutDebtAudit (dpEvents stageWindow1)
open PalPeg.CloseoutPreload8 (BeginAt)

/-! ## 1. The `.double` phase terminates -/

/-- The `.double` phase as a chain of `searchStep`s: positive ticks only, ending
where the work counter is spent (which is where `prepare` is dispatched). -/
inductive DoubleReach (c : GalilScaffoldPlace.Place) : SearchVM → List Bool → SearchVM → Prop
  | stop (v : SearchVM) (hm : v.search.mode = GalilScaffoldSearchFinish.Mode.double)
      (hz : positive v.search.work = false) : DoubleReach c v [] v
  | next (v t : SearchVM) (a : Bool) (as : List Bool)
      (hm : v.search.mode = GalilScaffoldSearchFinish.Mode.double)
      (hp : positive v.search.work = true)
      (hr : DoubleReach c
        {v with search := GalilScaffoldSearchRun.advance a (GalilScaffoldDouble.step v.search)}
        as t) : DoubleReach c v (a :: as) t

/-- Every `DoubleReach` tick really is a `searchStep`. -/
theorem doubleReach_step {c : GalilScaffoldPlace.Place} {v t : SearchVM} {a : Bool}
    {as : List Bool} (h : DoubleReach c v (a :: as) t) :
    ∃ v', searchStep c a v v' ∧ DoubleReach c v' as t := by
  cases h with
  | next v t a as hm hp hr =>
    refine ⟨_, ?_, hr⟩
    unfold searchStep
    rw [hm]
    simp only [hp, if_true]

/-- **NAMED — the doubling phase halts.**  The lift of
`GalilScaffoldDouble.complete` to `searchStep`, driven by a given event list. -/
theorem doubleS_complete (c : GalilScaffoldPlace.Place) :
    ∀ (n sp : ℕ) (v : SearchVM) (as : List Bool),
      v.search.mode = GalilScaffoldSearchFinish.Mode.double →
      v.search.work = ofNat n → v.search.span = ofNat sp → n ≤ as.length →
      ∃ t, DoubleReach c v (as.take n) t ∧
        t.search.mode = GalilScaffoldSearchFinish.Mode.double ∧
        positive t.search.work = false ∧ t.search.span = ofNat (sp + 2 * n) ∧
        t.lower = v.lower ∧ t.walker = v.walker ∧ t.dp = v.dp := by
  intro n
  induction n with
  | zero =>
    intro sp v as hm hw hs _
    refine ⟨v, ?_, hm, ?_, by simpa using hs, rfl, rfl, rfl⟩
    · simpa using DoubleReach.stop (c := c) v hm (by simp [hw, positive, ofNat])
    · simp [hw, positive, ofNat]
  | succ n ih =>
    intro sp v as hm hw hs hlen
    match as, hlen with
    | a :: as', hlen =>
      have hlen' : n ≤ as'.length := by simpa using hlen
      set v1 : SearchVM :=
        {v with search := GalilScaffoldSearchRun.advance a (GalilScaffoldDouble.step v.search)}
        with hv1
      have hm1 : v1.search.mode = GalilScaffoldSearchFinish.Mode.double := by
        cases a <;>
          simpa [hv1, GalilScaffoldSearchRun.advance, GalilScaffoldDouble.step] using hm
      have hw1 : v1.search.work = ofNat n := by
        cases a <;>
          simp [hv1, GalilScaffoldSearchRun.advance, GalilScaffoldDouble.step, hw,
            GalilScaffoldCounter.dec_ofNat_succ]
      have hs1 : v1.search.span = ofNat (sp + 2) := by
        cases a <;>
          simp [hv1, GalilScaffoldSearchRun.advance, GalilScaffoldDouble.step, hs,
            GalilScaffoldCounter.inc_ofNat, Nat.add_assoc]
      obtain ⟨t, hr, htm, htw, hts, htl, htwk, htdp⟩ := ih (sp + 2) v1 as' hm1 hw1 hs1 hlen'
      refine ⟨t, ?_, htm, htw, ?_, ?_, ?_, ?_⟩
      · have : (a :: as').take (n + 1) = a :: as'.take n := by simp
        rw [this]
        exact DoubleReach.next (c := c) v t a (as'.take n) hm
          (by simp [hw, positive, ofNat, List.replicate_succ]) hr
      · rw [hts]; congr 1; omega
      · exact htl
      · exact htwk
      · exact htdp

#print axioms doubleReach_step
#print axioms doubleS_complete

/-- At the end of the phase the `prepare` dispatch of `CloseoutPreload8` fires. -/
theorem double_exit_dispatch {c : GalilScaffoldPlace.Place} {t t' : SearchVM}
    (htm : t.search.mode = GalilScaffoldSearchFinish.Mode.double)
    (htw : positive t.search.work = false) {a : Bool} (hs : searchStep c a t t') :
    t' = SearchVM.ofPrep (GalilScaffoldPreparePaced.afterAdvance a
      (GalilScaffoldPrepareControl.prepare t.toPrep t.lower c)) t.search.quarter t.lower :=
  PalPeg.CloseoutPreload8.step_double_dispatch htm htw hs

#print axioms double_exit_dispatch

/-! ## 2. The doubled stage's parameters -/

/-- The `.double` entry loads `work := span` and resets `span`
(`GalilScaffoldDouble.enter`), so §1's exported span at the dispatch is exactly
twice the stage's lower bound: `k' = 2 * k`. -/
theorem stage_span_double {c : GalilScaffoldPlace.Place} (k : ℕ) (v : SearchVM)
    (as : List Bool) (hm : v.search.mode = GalilScaffoldSearchFinish.Mode.double)
    (hw : v.search.work = ofNat k) (hs : v.search.span = ofNat 0) (hlen : k ≤ as.length) :
    ∃ t, DoubleReach c v (as.take k) t ∧
      t.search.mode = GalilScaffoldSearchFinish.Mode.double ∧
      positive t.search.work = false ∧ t.search.span = ofNat (2 * k) ∧
      t.lower = v.lower ∧ t.walker = v.walker ∧ t.dp = v.dp := by
  obtain ⟨t, hr, htm, htw, hts, htl, htwk, htdp⟩ := doubleS_complete c k 0 v as hm hw hs hlen
  exact ⟨t, hr, htm, htw, by simpa using hts, htl, htwk, htdp⟩

#print axioms stage_span_double

/-- **The entry inequality survives doubling.**  `StageEntry`'s clause
`3 * Rad ≤ 5 * k` is monotone in the direction the stage moves: the lower bound
doubles while the radius at worst doubles. -/
theorem stage_bound_double {k Rad k' Rad' : ℕ} (hstage : 3 * Rad ≤ 5 * k)
    (hk : k' = 2 * k) (hR : Rad' ≤ 2 * Rad) : 3 * Rad' ≤ 5 * k' := by omega

#print axioms stage_bound_double

/-- **The DP demand at most doubles.**  `dpEvents ∘ stageWindow1` is affine in
`max k 1` up to the flooring, so the doubled stage asks for at most twice the
events of the current one, plus the one event lost to the floor. -/
theorem dpEvents_double (k : ℕ) :
    dpEvents (stageWindow1 (2 * k)) ≤ 2 * dpEvents (stageWindow1 k) + 1 := by
  unfold dpEvents stageWindow1
  have h1 : max (2 * k) 1 ≤ 2 * max k 1 := by omega
  omega

#print axioms dpEvents_double

/-- `dpEvents` is monotone, so a window shorter than the calibrated one demands
no more events. -/
theorem dpEvents_mono {w w' : ℕ} (h : w ≤ w') : dpEvents w ≤ dpEvents w' := by
  unfold dpEvents; omega

#print axioms dpEvents_mono

/-! ## 3. The residual -/

/-- **NAMED — the stage boundary.**  This is `CloseoutPreload8.PostRun` with §1
and §2 already spent: what is left is purely the claim that the `prepare`
dispatched at the end of the doubling phase lands in a state satisfying the
*begin* shape of the doubled stage — i.e. that `CloseoutPreload8.BeginAt`'s
data (`work = ofNat (max k' 1)`, `span = ofNat 0`, `debt = -(Rad' : ℤ)`,
`lower = ofNat k'`), together with `CentreLongAt` and `DepthAt` at `k'`, is
re-established.  Everything else in the boundary is now discharged:
termination by `doubleS_complete`, `k' = 2 * k` by `stage_span_double`,
`3 * Rad' ≤ 5 * k'` by `stage_bound_double`, and the demand growth by
`dpEvents_double`. -/
def StageBoundary : Prop :=
  ∀ (c : GalilScaffoldPlace.Place) (t t' : SearchVM) (a : Bool) (k Rad : ℕ),
    t.search.mode = GalilScaffoldSearchFinish.Mode.double →
    positive t.search.work = false →
    t.search.span = ofNat (2 * k) → t.lower = ofNat k →
    value t.search.debt = -(Rad : ℤ) → Canonical t.search.debt →
    searchStep c a t t' →
    ∃ Rad' : ℕ, Rad' ≤ 2 * Rad ∧ BeginAt (2 * k) Rad' t'

/-!
## Note — what is *not* fixed by short inputs

`CloseoutPreload8.dpSafeStage_entry_min` relaxed the **window** clause to
`w.length ≤ stageWindow1 k`, which is what a short input really produces.  Its
remaining hypothesis `dpEvents (stageWindow1 k) ≤ as.length` is a different
quantity: it is computed from `k` alone, not from the window actually copied,
so a short input does **not** discharge it — the DP still has to be given the
events its *calibrated* budget asks for.  Removing it would mean restating the
entry at `dpEvents w.length` (legitimate by `dpEvents_mono`, but
`DpSafeStage`'s own entry condition is phrased at the calibrated window), or
adding a final-stage escape for the case where the input runs out first.  That
is the single remaining input-length assumption of the chain, and it is
orthogonal to `StageBoundary`.
-/

end PalPeg.CloseoutPreload9
