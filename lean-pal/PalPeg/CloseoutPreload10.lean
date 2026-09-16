import PalPeg.CloseoutPreload9

/-!
# The stage boundary, computed — and why `BeginAt` is the wrong target

`CloseoutPreload9.StageBoundary` asked the `prepare` dispatched at the end of
the doubling phase to re-establish `CloseoutPreload8.BeginAt (2*k) Rad'`.  This
file computes every field of that dispatch from the definitions
(`GalilScaffoldPrepareControl.prepare`, `GalilScaffoldPreparePaced.afterAdvance`,
`SearchVM.ofPrep`, `GalilScaffoldStagePrepare.runState`) and finds that
**`StageBoundary` is false as stated**, in three independent fields:

| field | `BeginAt (2*k) Rad'` asks | the dispatch delivers |
|---|---|---|
| `search.mode` | `.grow` | `.lower` |
| `search.span` | `ofNat 0` | `t.search.span` (unchanged, `= ofNat (2*k)`) |
| `search.work` | `ofNat (max (2*k) 1)` | `t.lower` |
| `lower` | `ofNat (2*k)` | `t.lower` (never doubled) |

Only the `debt` clause is of the shape `CloseoutPreload9` anticipated (`-Rad'`
with `Rad' ≤ Rad + 1`), so weakening `BeginAt` to `BeginAtGe` does **not**
repair the statement: `mode` alone already refutes it (§2).

* §1 `double_exit_mode/work/span/debt/lower/walker/dp/final` — the dispatch,
  field by field.  All are definitional.
* §2 `not_beginAt_of_double_exit`, `not_stageBoundary` — `StageBoundary` and
  every `debt`-weakened variant of it are false.
* §3 `PrepAt`, `prepAt_of_double_exit` — what the dispatch **does** establish:
  the `.lower` entry of the preparation, at the *same* lower bound `k` and the
  *doubled* span.  This is `CloseoutPreload5.Phase`'s prep branch minus its
  `span = 8 * max k 1` clause, which is exactly the clause that breaks: the
  window doubles while `lower` does not, so the stage's window index and its
  `lower` counter part company after the first doubling.
* §4 `dpSafeStage_entry_real` — the short-input half, successful: the entry is
  restated at the **real** window `w.length`, removing the calibrated
  input-length hypothesis `dpEvents (stageWindow1 k) ≤ as.length` of
  `CloseoutPreload8.dpSafeStage_entry_min`.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPreload10

open PalPeg PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController
open PalPeg.GalilScaffoldPrepareControl (State prepare)
open PalPeg.GalilScaffoldCounter (Counter Canonical value ofNat positive dec)
open PalPeg.CloseoutDebtAudit (dpEvents stageWindow1)
open PalPeg.CloseoutReadyStage (DpSafeStage PacedL dpSafeStage_entry dpEvents_budget)
open PalPeg.CloseoutPreload8 (BeginAt)

/-- The state dispatched at the end of the doubling phase. -/
def exitState (c : GalilScaffoldPlace.Place) (a : Bool) (t : SearchVM) : SearchVM :=
  SearchVM.ofPrep (GalilScaffoldPreparePaced.afterAdvance a
    (prepare t.toPrep t.lower c)) t.search.quarter t.lower

theorem exit_eq {c : GalilScaffoldPlace.Place} {t t' : SearchVM} {a : Bool}
    (htm : t.search.mode = GalilScaffoldSearchFinish.Mode.double)
    (htw : positive t.search.work = false) (hs : searchStep c a t t') :
    t' = exitState c a t :=
  PalPeg.CloseoutPreload8.step_double_dispatch htm htw hs

#print axioms exit_eq

/-! ## 1. The dispatch, field by field -/

section Fields
variable (c : GalilScaffoldPlace.Place) (a : Bool) (t : SearchVM)

theorem double_exit_mode :
    (exitState c a t).search.mode = GalilScaffoldSearchFinish.Mode.lower := by
  cases a <;> rfl

theorem double_exit_work : (exitState c a t).search.work = t.lower := by
  cases a <;> rfl

theorem double_exit_span : (exitState c a t).search.span = t.search.span := by
  cases a <;> rfl

theorem double_exit_lower : (exitState c a t).lower = t.lower := by
  cases a <;> rfl

theorem double_exit_walker : (exitState c a t).walker = c := by
  cases a <;> rfl

theorem double_exit_final : (exitState c a t).search.finalStage = false := by
  cases a <;> rfl

theorem double_exit_debt :
    (exitState c a t).search.debt = (if a then dec t.search.debt else t.search.debt) := by
  cases a <;> rfl

theorem double_exit_debt_value :
    value (exitState c a t).search.debt
      = value t.search.debt - (if a then 1 else 0) := by
  cases a
  · show value t.search.debt = value t.search.debt - (0 : ℤ)
    simp
  · show value (dec t.search.debt) = _
    rw [GalilScaffoldCounter.dec_value]; simp

theorem double_exit_canonical (hc : Canonical t.search.debt) :
    Canonical (exitState c a t).search.debt := by
  cases a
  · exact hc
  · exact GalilScaffoldCounter.dec_canonical _ hc

end Fields

#print axioms double_exit_mode
#print axioms double_exit_work
#print axioms double_exit_span
#print axioms double_exit_lower
#print axioms double_exit_debt_value
#print axioms double_exit_canonical

/-! ## 2. `StageBoundary` is false -/

/-- **NAMED — the mode refutation.**  The dispatch lands in `.lower`, the first
mode of the preparation, never in `.grow`: the `.grow` phase is entered only by
`GalilScaffoldSearchFinish.begin` at a restart, and the doubling phase bypasses
it (it has already computed the new span itself).  So no `BeginAt`, and no
weakening of `BeginAt` in the `debt` or `work` clauses, can hold here. -/
theorem not_beginAt_of_double_exit (c : GalilScaffoldPlace.Place) (a : Bool)
    (t : SearchVM) (k' Rad' : ℕ) : ¬ BeginAt k' Rad' (exitState c a t) := by
  intro hb
  have h := hb.mode
  rw [double_exit_mode] at h
  exact absurd h (by decide)

#print axioms not_beginAt_of_double_exit

/-- `CloseoutPreload9.StageBoundary` is refutable: instantiate it at any state
whose doubling phase has genuinely ended.  (The witness only has to satisfy the
hypotheses; `searchStep` at a spent `.double` state is a definitional equation,
so `exitState` itself is the successor.) -/
theorem not_stageBoundary (c : GalilScaffoldPlace.Place)
    (P : GalilScaffoldControl.Machine 12) : ¬ PalPeg.CloseoutPreload9.StageBoundary := by
  intro h
  -- a concrete spent-`.double` state with `k = 0`, `Rad = 0`
  set t : SearchVM :=
    ⟨⟨GalilScaffoldSearchFinish.Mode.double, false, ofNat 0, ofNat 0,
      GalilScaffoldCounter.reset, 0⟩, P, ofNat 0, c⟩ with ht
  have hm : t.search.mode = GalilScaffoldSearchFinish.Mode.double := rfl
  have hw : positive t.search.work = false := by
    show positive (ofNat 0) = false
    simp [positive, ofNat]
  have hsp : t.search.span = ofNat (2 * 0) := by simp [ht]
  have hlow : t.lower = ofNat 0 := rfl
  have hdv : value t.search.debt = -((0 : ℕ) : ℤ) := by
    show value GalilScaffoldCounter.reset = _
    simp [GalilScaffoldCounter.value, GalilScaffoldCounter.reset]
  have hcan : Canonical t.search.debt := Or.inl rfl
  have hstep : searchStep c false t (exitState c false t) := by
    unfold searchStep
    rw [hm]
    simp only [hw, Bool.false_eq_true, if_false]
    rfl
  obtain ⟨Rad', -, hb⟩ :=
    h c t (exitState c false t) false 0 0 hm hw hsp hlow hdv hcan hstep
  exact not_beginAt_of_double_exit c false t (2 * 0) Rad' hb

#print axioms not_stageBoundary

/-! ## 3. What the dispatch does establish -/

/-- The `.lower` entry of a preparation: the shape
`CloseoutPreload5.Phase`'s prep branch asks for, **without** the clause
`span = 8 * max k 1` that ties the window to the lower bound.  `k` is the
persistent lower counter (`work = lower = ofNat k`) and `m` is the span the
window will be copied from — after the first doubling these two are no longer
related by the stage calibration. -/
structure PrepAt (k m : ℕ) (v : SearchVM) : Prop where
  mode : v.search.mode = GalilScaffoldSearchFinish.Mode.lower
  work : v.search.work = ofNat k
  span : v.search.span = ofNat m
  low : v.lower = ofNat k
  final : v.search.finalStage = false
  ten : v.dp.config.tapes 10 =
    GalilScaffoldTape.moveRight (GalilScaffoldTape.write GalilScaffoldTape.reset 4)
  other : ∀ i : Fin 12, i ≠ 10 → v.dp.config.tapes i = GalilScaffoldTape.reset
  can : Canonical v.search.debt

/-- **NAMED — the stage boundary, correctly stated.**  The `prepare` dispatched
at the end of the doubling phase re-establishes the *preparation* entry at the
same lower bound `k` and the doubled span `m`, with the debt paid down by at
most one. -/
theorem prepAt_of_double_exit {c : GalilScaffoldPlace.Place} {t t' : SearchVM}
    {a : Bool} {k m : ℕ}
    (htm : t.search.mode = GalilScaffoldSearchFinish.Mode.double)
    (htw : positive t.search.work = false)
    (hsp : t.search.span = ofNat m) (hlow : t.lower = ofNat k)
    (hc : Canonical t.search.debt) (hs : searchStep c a t t') :
    PrepAt k m t' ∧ t'.walker = c ∧
      value t'.search.debt = value t.search.debt - (if a then 1 else 0) := by
  have he : t' = exitState c a t := exit_eq htm htw hs
  subst he
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, double_exit_walker c a t,
    double_exit_debt_value c a t⟩
  · exact double_exit_mode c a t
  · rw [double_exit_work]; exact hlow
  · rw [double_exit_span]; exact hsp
  · rw [double_exit_lower]; exact hlow
  · exact double_exit_final c a t
  · show (exitState c a t).dp.config.tapes 10 = _
    cases a <;>
      simp [exitState, SearchVM.ofPrep, GalilScaffoldPreparePaced.afterAdvance, prepare,
        GalilScaffoldLoading.put, GalilScaffoldControl.reset]
  · intro i hi
    show (exitState c a t).dp.config.tapes i = _
    cases a <;>
      simp [exitState, SearchVM.ofPrep, GalilScaffoldPreparePaced.afterAdvance, prepare,
        GalilScaffoldLoading.put, GalilScaffoldControl.reset, hi]
  · exact double_exit_canonical c a t hc

#print axioms prepAt_of_double_exit

/-! ## 4. The short-input half: the entry at the real window -/

/-- **NAMED — the entry at the real window.**  `CloseoutPreload8.dpSafeStage_entry_min`
still demanded `dpEvents (stageWindow1 k) ≤ as.length`, a quantity computed from
the *calibrated* window even when the preparation copied a shorter one.  Here
the whole entry is restated at `w.length`, the window actually loaded, so the
remaining input-length hypothesis is about the real window.  By
`CloseoutPreload9.dpEvents_mono` any calibrated bound implies this one. -/
theorem dpSafeStage_entry_real (v : SearchVM) (w : List (Fin 3)) (lower slack : ℕ)
    (as : List Bool)
    (hdp : v.dp = ⟨GalilScaffoldPreload.initial w lower, false⟩)
    (hmode : v.search.mode = .run)
    (hc : Canonical v.search.debt)
    (hb : (((slack + dpEvents w.length) / 2048 + 1 : ℕ) : ℤ) ≤ value v.search.debt)
    (hlen : dpEvents w.length ≤ as.length)
    (hpaced : PacedL 2048 slack as) :
    DpSafeStage v as := by
  set N : ℕ := dpEvents w.length with hN
  refine dpSafeStage_entry v w lower as (as.take N) (as.drop N) hdp hmode
    (by rw [List.take_append_drop]) ?_ hc ?_
  · have hlenpre : (as.take N).length = N := by rw [List.length_take]; omega
    have hbud := dpEvents_budget w.length
    rw [hlenpre, hN]
    omega
  · have h1 : (as.take N).count true ≤ (slack + N) / 2048 + 1 :=
      PalPeg.CloseoutPreload6.pacedL_count_take_gen hpaced
    have h3 : (((as.take N).count true : ℕ) : ℤ) ≤ (((slack + N) / 2048 + 1 : ℕ) : ℤ) :=
      Int.ofNat_le.mpr h1
    omega

#print axioms dpSafeStage_entry_real

/-- The calibrated entry is a special case: a window no longer than the
calibrated one needs no more events. -/
theorem dpSafeStage_entry_real_of_calibrated (v : SearchVM) (w : List (Fin 3))
    (lower k slack : ℕ) (as : List Bool)
    (hw : w.length ≤ stageWindow1 k)
    (hdp : v.dp = ⟨GalilScaffoldPreload.initial w lower, false⟩)
    (hmode : v.search.mode = .run)
    (hc : Canonical v.search.debt)
    (hb : (((slack + dpEvents (stageWindow1 k)) / 2048 + 1 : ℕ) : ℤ)
      ≤ value v.search.debt)
    (hlen : dpEvents (stageWindow1 k) ≤ as.length)
    (hpaced : PacedL 2048 slack as) :
    DpSafeStage v as := by
  have hmono := PalPeg.CloseoutPreload9.dpEvents_mono hw
  refine dpSafeStage_entry_real v w lower slack as hdp hmode hc ?_ (by omega) hpaced
  have : (slack + dpEvents w.length) / 2048 ≤ (slack + dpEvents (stageWindow1 k)) / 2048 :=
    Nat.div_le_div_right (by omega)
  have h2 : (((slack + dpEvents w.length) / 2048 + 1 : ℕ) : ℤ)
      ≤ (((slack + dpEvents (stageWindow1 k)) / 2048 + 1 : ℕ) : ℤ) :=
    Int.ofNat_le.mpr (by omega)
  omega

#print axioms dpSafeStage_entry_real_of_calibrated

/-!
## Note — the one missing fact, restated

With §1–§3 the stage boundary is no longer a machine unknown but a
**calibration** problem: the dispatch is fully computed, and what fails is the
*indexing*.  `CloseoutPreload8`'s chain reads a stage through one number `k`,
used twice — as the lower bound (`work = lower = ofNat k`, and in the debt
budget `3 * Rad ≤ 5 * k`) and as the window (`stageWindow1 k = 8 * max k 1 + 1`).
At a restart the two agree, because the `.grow` phase builds the span from the
lower bound (`span = 8 * max k 1`).  After a doubling they do not: the span
doubles (`CloseoutPreload9.stage_span_double`) and `lower` is untouched — it is
written only by `GalilScaffoldTopRestart`'s `lower := w.machine.control.last`.

So the genuinely missing fact is *not* `StageBoundary` but:

> `CloseoutPreload5.Phase` / `CloseoutPreload8.entry_shape_at`, `dpSafe_of_stagePrep`
> and `dpSafeStage_entry_min`, re-indexed on **two** parameters `(k, m)` — the
> lower bound and the span — instead of one, with the window clause at `m + 1`
> and the debt clause at `3 * Rad ≤ 5 * k`, so that `PrepAt k m` can serve as
> the entry of the doubled stage with `m' = 2 * m`.

§4 is the part of that re-indexing which is already done: the DP entry now
reads the real window length rather than the calibrated one.
-/

end PalPeg.CloseoutPreload10
