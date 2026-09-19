import PalPeg.CanonicalSearchBudget
import PalPeg.CanonicalSearchProgram

/-!
# The stage history of the paced search

While the chain is idle the search runs the DP in stages of doubling span.  A fallback can come
at any moment of a stage, when the DP tapes of the current stage say nothing yet.  What holds at
every moment is the history: some window of the centre's place stream has no candidate above the
lower bound (the last failed stage, or a window too short to hold one), and the scan radius is
inside it.  The radius is tied to the stage by the debt counter: a match pays one unit of debt,
and a stage of span `S` starts with `S/4` units above the radius.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.SearchStageHistory

open PalPeg GalilScaffoldChainInputSupply GalilScaffoldCounter
open GalilScaffoldSearchRun GalilBranchInvariants2 CanonicalSearchProgram CanonicalSearchBudget

/-- The search modes in which the scheduler still moves. -/
def Active (m : GalilScaffoldSearchFinish.Mode) : Prop :=
  m ≠ .idle ∧ m ≠ .found ∧ m ≠ .missed

/-- No candidate above `lower` in the first `H + 1` places of the stream of `p`. -/
def NoCandidate (p : GalilScaffoldPlace.Place) (lower H : ℕ) : Prop :=
  ∀ h, ¬ GalilDpCorrect.Candidate ((GalilScaffoldPlace.stream p).take (H+1)) lower h

/-- How far the current stage may run against the candidate-free window `H`. -/
def WindowBound (s : GalilScaffoldSearchFinish.State) (H : ℕ) : Prop :=
  match s.mode with
  | .wait => value s.span ≤ (H : ℤ)
  | .double => value s.span + 2 * value s.work ≤ 2 * (H : ℤ)
  | .grow => value s.span + 8 * value s.work ≤ 4 * (H : ℤ)
  | _ => value s.span ≤ 4 * (H : ℤ)

/-- The debt balance against the scan radius `R`, and the candidate-free window. -/
structure StageHistory (p : GalilScaffoldPlace.Place) (lower : ℕ) (R : ℤ) (v : SearchVM) :
    Prop where
  balance : Active v.search.mode →
    4 * (value v.search.debt + R) +
        (if v.search.mode = .double then (v.search.quarter.val : ℤ) else 0)
      = value v.search.span + (if v.search.mode = .double then value v.search.work else 0)
  waitDebt : v.search.mode = .wait → 0 ≤ value v.search.debt
  window : Active v.search.mode → ∃ H, NoCandidate p lower H ∧ WindowBound v.search H

/-- A window of `4·lower + 4` places is too short to hold a candidate above `lower`. -/
theorem noCandidate_short (p : GalilScaffoldPlace.Place) (lower : ℕ) :
    NoCandidate p lower (4 * lower + 3) := by
  intro h hcandidate
  obtain ⟨hlower, hlength, -⟩ := hcandidate
  rw [List.length_take] at hlength
  omega

theorem value_initialDebt (radius : Counter) :
    value (GalilScaffoldSearchFinish.initialDebt radius) = - value radius := by
  simp [GalilScaffoldSearchFinish.initialDebt, value]

/-- A fresh search: the debt starts at minus the radius, the span at zero. -/
theorem stageHistory_begin (p : GalilScaffoldPlace.Place) (lower : ℕ) (radius : Counter)
    {v : SearchVM} (hsearch : v.search = GalilScaffoldSearchFinish.begin (ofNat lower) radius) :
    StageHistory p lower (value radius) v := by
  have hmode : v.search.mode = .grow := by rw [hsearch]; rfl
  have hspan : value v.search.span = 0 := by rw [hsearch]; rfl
  have hdebt : value v.search.debt = - value radius := by
    rw [hsearch]; exact value_initialDebt radius
  have hwork : value v.search.work = (max lower 1 : ℕ) := by
    rw [hsearch]
    cases lower with
    | zero => rfl
    | succ n =>
      show value (if zero (ofNat (n+1)) then inc (ofNat (n+1)) else ofNat (n+1)) = _
      have hz : zero (ofNat (n+1)) = false := by simp [zero, ofNat, List.replicate_succ]
      rw [hz]
      simp [ofNat_value]
  refine ⟨fun _ => ?_, fun hwait => (by rw [hmode] at hwait; cases hwait), fun _ => ?_⟩
  · simp only [hmode, reduceCtorEq, if_false]
    rw [hspan, hdebt]
    ring
  · refine ⟨4 * lower + 3, noCandidate_short p lower, ?_⟩
    simp only [WindowBound, hmode]
    rw [hspan, hwork]
    push_cast
    omega

/-! ## Targets by mode -/

/-- The modes in which the span is fixed and the balance has no correction term. -/
def Steady (m : GalilScaffoldSearchFinish.Mode) : Prop :=
  m = .lower ∨ m = .lowerHome ∨ m = .copy ∨ m = .home ∨ m = .run

theorem stageHistory_of_steady {p : GalilScaffoldPlace.Place} {lower : ℕ} {R : ℤ} {v : SearchVM}
    (hsteady : Steady v.search.mode)
    (hbalance : 4 * (value v.search.debt + R) = value v.search.span)
    (hwindow : ∃ H : ℕ, NoCandidate p lower H ∧ value v.search.span ≤ 4 * (H : ℤ)) :
    StageHistory p lower R v := by
  obtain ⟨H, hnone, hbound⟩ := hwindow
  refine ⟨fun _ => ?_, fun hwait => ?_, fun _ => ⟨H, hnone, ?_⟩⟩
  · rcases hsteady with h | h | h | h | h <;> simp only [h, reduceCtorEq, if_false] <;> linarith
  · rcases hsteady with h | h | h | h | h <;> rw [h] at hwait <;> cases hwait
  · rcases hsteady with h | h | h | h | h <;> simp only [WindowBound, h] <;> exact hbound

theorem stageHistory_of_grow {p : GalilScaffoldPlace.Place} {lower : ℕ} {R : ℤ} {v : SearchVM}
    (hmode : v.search.mode = .grow)
    (hbalance : 4 * (value v.search.debt + R) = value v.search.span)
    (hwindow : ∃ H : ℕ, NoCandidate p lower H ∧
      value v.search.span + 8 * value v.search.work ≤ 4 * (H : ℤ)) :
    StageHistory p lower R v := by
  obtain ⟨H, hnone, hbound⟩ := hwindow
  refine ⟨fun _ => ?_, fun hwait => ?_, fun _ => ⟨H, hnone, ?_⟩⟩
  · simp only [hmode, reduceCtorEq, if_false]; linarith
  · rw [hmode] at hwait; cases hwait
  · simp only [WindowBound, hmode]; exact hbound

theorem stageHistory_of_double {p : GalilScaffoldPlace.Place} {lower : ℕ} {R : ℤ} {v : SearchVM}
    (hmode : v.search.mode = .double)
    (hbalance : 4 * (value v.search.debt + R) + (v.search.quarter.val : ℤ)
      = value v.search.span + value v.search.work)
    (hwindow : ∃ H : ℕ, NoCandidate p lower H ∧
      value v.search.span + 2 * value v.search.work ≤ 2 * (H : ℤ)) :
    StageHistory p lower R v := by
  obtain ⟨H, hnone, hbound⟩ := hwindow
  refine ⟨fun _ => ?_, fun hwait => ?_, fun _ => ⟨H, hnone, ?_⟩⟩
  · simp only [hmode, if_true]; exact hbalance
  · rw [hmode] at hwait; cases hwait
  · simp only [WindowBound, hmode]; exact hbound

theorem stageHistory_of_wait {p : GalilScaffoldPlace.Place} {lower : ℕ} {R : ℤ} {v : SearchVM}
    (hmode : v.search.mode = .wait)
    (hbalance : 4 * (value v.search.debt + R) = value v.search.span)
    (hdebt : 0 ≤ value v.search.debt)
    (hwindow : ∃ H : ℕ, NoCandidate p lower H ∧ value v.search.span ≤ (H : ℤ)) :
    StageHistory p lower R v := by
  obtain ⟨H, hnone, hbound⟩ := hwindow
  refine ⟨fun _ => ?_, fun _ => hdebt, fun _ => ⟨H, hnone, ?_⟩⟩
  · simp only [hmode, reduceCtorEq, if_false]; linarith
  · simp only [WindowBound, hmode]; exact hbound

theorem stageHistory_of_inactive {p : GalilScaffoldPlace.Place} {lower : ℕ} {R : ℤ} {v : SearchVM}
    (hinactive : ¬ Active v.search.mode) (hnotWait : v.search.mode ≠ .wait) :
    StageHistory p lower R v :=
  ⟨fun h => absurd h hinactive, fun h => absurd h hnotWait, fun h => absurd h hinactive⟩

/-! ## The fields of the search after a prepare-side step -/

section ofPrep
variable (a : Bool) (y : GalilScaffoldPrepareControl.State) (quarter : Fin 4) (lower : Counter)

theorem ofPrep_mode : (SearchVM.ofPrep (GalilScaffoldPreparePaced.afterAdvance a y) quarter
    lower).search.mode = y.mode := by
  cases a <;> rfl

theorem ofPrep_span : (SearchVM.ofPrep (GalilScaffoldPreparePaced.afterAdvance a y) quarter
    lower).search.span = y.span := by
  cases a <;> rfl

theorem ofPrep_work : (SearchVM.ofPrep (GalilScaffoldPreparePaced.afterAdvance a y) quarter
    lower).search.work = y.work := by
  cases a <;> rfl

theorem ofPrep_debt : value (SearchVM.ofPrep (GalilScaffoldPreparePaced.afterAdvance a y) quarter
    lower).search.debt = value y.debt - (if a then 1 else 0) := by
  cases a
  · simp [SearchVM.ofPrep, GalilScaffoldStagePrepare.runState,
      GalilScaffoldPreparePaced.afterAdvance]
  · simp [SearchVM.ofPrep, GalilScaffoldStagePrepare.runState,
      GalilScaffoldPreparePaced.afterAdvance, dec_value]

end ofPrep

theorem prepTick_span {x y : GalilScaffoldPrepareControl.State} {b : Bool}
    (htick : GalilScaffoldPrepareControl.Tick b x y) : y.span = x.span := by
  cases htick <;> rfl

theorem prepTick_steady {x y : GalilScaffoldPrepareControl.State}
    (htick : GalilScaffoldPrepareControl.Tick true x y) (hprep : Preparing x.mode) :
    Steady y.mode := by
  cases htick <;> simp_all [Steady, Preparing]

/-! ## The fields of the search after an advance -/

section advance
variable (a : Bool) (s : GalilScaffoldSearchFinish.State)

theorem advance_mode : (advance a s).mode = s.mode := by cases a <;> rfl
theorem advance_span : (advance a s).span = s.span := by cases a <;> rfl
theorem advance_work : (advance a s).work = s.work := by cases a <;> rfl
theorem advance_quarter : (advance a s).quarter = s.quarter := by cases a <;> rfl
theorem advance_debt : value (advance a s).debt = value s.debt - (if a then 1 else 0) := by
  cases a
  · simp [advance]
  · simp [advance, dec_value]

end advance

/-- A counter that stands for a natural number and is not positive is zero. -/
theorem value_zero_of_not_positive {c : Counter} {n : ℕ} (hc : c = ofNat n)
    (hpositive : ¬ positive c = true) : value c = 0 := by
  have hn : n = 0 := by
    simp [hc, positive_ofNat] at hpositive
    omega
  rw [hc, hn]
  rfl

/-- One search event away from `run`: the balance and the window follow the scheduler. -/
theorem stageHistory_step_offRun {p : GalilScaffoldPlace.Place} {lower clock : ℕ} {R : ℤ}
    {a : Bool} {v v' : SearchVM}
    (hbudget : BudgetInv p lower clock v) (hhistory : StageHistory p lower R v)
    (hnotRun : v.search.mode ≠ .run) (hstep : searchStep p a v v') :
    StageHistory p lower (R + if a then 1 else 0) v' := by
  cases hm : v.search.mode with
  | run => exact absurd hm hnotRun
  | idle | found | missed =>
    simp only [searchStep, hm] at hstep
    subst v'
    exact stageHistory_of_inactive (by simp [Active, hm]) (by simp [hm])
  | lower | lowerHome | copy | home =>
    simp only [searchStep, hm] at hstep
    obtain ⟨y, htick, rfl⟩ := hstep
    have hactive : Active v.search.mode := by simp [Active, hm]
    have hbalance := hhistory.balance hactive
    simp only [hm, reduceCtorEq, if_false] at hbalance
    obtain ⟨H, hnone, hbound⟩ := hhistory.window hactive
    simp only [WindowBound, hm] at hbound
    apply stageHistory_of_steady
    · rw [ofPrep_mode]
      exact prepTick_steady htick (by simp [Preparing, SearchVM.toPrep, hm])
    · rw [ofPrep_debt, ofPrep_span, prepTick_span htick,
        GalilScaffoldPrepareControl.tick_debt htick]
      change 4 * (value v.search.debt - _ + (R + _)) = value v.search.span
      linarith
    · refine ⟨H, hnone, ?_⟩
      rw [ofPrep_span, prepTick_span htick]
      exact hbound
  | grow =>
    have hactive : Active v.search.mode := by simp [Active, hm]
    have hbalance := hhistory.balance hactive
    simp only [hm, reduceCtorEq, if_false] at hbalance
    obtain ⟨H, hnone, hbound⟩ := hhistory.window hactive
    simp only [WindowBound, hm] at hbound
    simp only [searchStep, hm] at hstep
    by_cases hpositive : positive v.search.work = true
    · simp only [hpositive, if_true] at hstep
      subst v'
      apply stageHistory_of_grow
      · rw [ofPrep_mode]; exact hm
      · rw [ofPrep_debt, ofPrep_span]
        change 4 * (value (GalilScaffoldGrow.add 2 v.search.debt) - _ + (R + _))
          = value (GalilScaffoldGrow.add 8 v.search.span)
        rw [GalilScaffoldGrow.add_value, GalilScaffoldGrow.add_value]
        push_cast
        linarith
      · refine ⟨H, hnone, ?_⟩
        rw [ofPrep_span, ofPrep_work]
        change value (GalilScaffoldGrow.add 8 v.search.span) + 8 * value (dec v.search.work) ≤ _
        rw [GalilScaffoldGrow.add_value, dec_value]
        push_cast
        linarith
    · simp only [hpositive, Bool.false_eq_true, if_false] at hstep
      subst v'
      obtain ⟨work, hwork⟩ := hbudget.work_nat (Or.inl hm)
      have hworkZero := value_zero_of_not_positive hwork hpositive
      apply stageHistory_of_steady
      · rw [ofPrep_mode]; exact Or.inl rfl
      · rw [ofPrep_debt, ofPrep_span]
        change 4 * (value v.search.debt - _ + (R + _)) = value v.search.span
        linarith
      · refine ⟨H, hnone, ?_⟩
        rw [ofPrep_span]
        change value v.search.span ≤ _
        linarith
  | wait =>
    have hactive : Active v.search.mode := by simp [Active, hm]
    have hbalance := hhistory.balance hactive
    simp only [hm, reduceCtorEq, if_false] at hbalance
    obtain ⟨H, hnone, hbound⟩ := hhistory.window hactive
    simp only [WindowBound, hm] at hbound
    have hdebt := hhistory.waitDebt hm
    simp only [searchStep, hm] at hstep
    subst v'
    by_cases hzero : zero v.search.debt = true
    · have hentered : GalilScaffoldDouble.waitStep true v.search
          = GalilScaffoldDouble.enter v.search := GalilScaffoldDouble.wait_enter _ hm hzero
      apply stageHistory_of_double
      · show (advance a (GalilScaffoldDouble.waitStep true v.search)).mode = .double
        rw [advance_mode, hentered]; rfl
      · show 4 * (value (advance a (GalilScaffoldDouble.waitStep true v.search)).debt + _)
          + (((advance a (GalilScaffoldDouble.waitStep true v.search)).quarter.val : ℕ) : ℤ)
          = value (advance a (GalilScaffoldDouble.waitStep true v.search)).span
            + value (advance a (GalilScaffoldDouble.waitStep true v.search)).work
        rw [advance_debt, advance_quarter, advance_span, advance_work, hentered]
        change 4 * (value v.search.debt - _ + (R + _)) + ((0 : ℕ) : ℤ)
          = value reset + value v.search.span
        have hreset : value reset = 0 := rfl
        rw [hreset]
        push_cast
        linarith
      · refine ⟨H, hnone, ?_⟩
        show value (advance a (GalilScaffoldDouble.waitStep true v.search)).span
          + 2 * value (advance a (GalilScaffoldDouble.waitStep true v.search)).work ≤ _
        rw [advance_span, advance_work, hentered]
        change value reset + 2 * value v.search.span ≤ _
        have hreset : value reset = 0 := rfl
        rw [hreset]
        linarith
    · have hstays : GalilScaffoldDouble.waitStep true v.search = v.search := by
        simp [GalilScaffoldDouble.waitStep, hm, hzero]
      have hdebtPos : 1 ≤ value v.search.debt := by
        have hne : value v.search.debt ≠ 0 := fun h =>
          hzero ((zero_iff _ hbudget.debt_canonical).mpr h)
        omega
      apply stageHistory_of_wait
      · show (advance a (GalilScaffoldDouble.waitStep true v.search)).mode = .wait
        rw [advance_mode, hstays]; exact hm
      · show 4 * (value (advance a (GalilScaffoldDouble.waitStep true v.search)).debt + _)
          = value (advance a (GalilScaffoldDouble.waitStep true v.search)).span
        rw [advance_debt, advance_span, hstays]
        linarith
      · show 0 ≤ value (advance a (GalilScaffoldDouble.waitStep true v.search)).debt
        rw [advance_debt, hstays]
        cases a <;> simp <;> omega
      · refine ⟨H, hnone, ?_⟩
        show value (advance a (GalilScaffoldDouble.waitStep true v.search)).span ≤ _
        rw [advance_span, hstays]
        exact hbound
  | double =>
    have hactive : Active v.search.mode := by simp [Active, hm]
    have hbalance := hhistory.balance hactive
    simp only [hm, if_true] at hbalance
    obtain ⟨H, hnone, hbound⟩ := hhistory.window hactive
    simp only [WindowBound, hm] at hbound
    simp only [searchStep, hm] at hstep
    by_cases hpositive : positive v.search.work = true
    · simp only [hpositive, if_true] at hstep
      subst v'
      have hstepBalance := GalilScaffoldDouble.step_balance v.search
      apply stageHistory_of_double
      · show (advance a (GalilScaffoldDouble.step v.search)).mode = .double
        rw [advance_mode]; exact hm
      · show 4 * (value (advance a (GalilScaffoldDouble.step v.search)).debt + _)
          + (((advance a (GalilScaffoldDouble.step v.search)).quarter.val : ℕ) : ℤ)
          = value (advance a (GalilScaffoldDouble.step v.search)).span
            + value (advance a (GalilScaffoldDouble.step v.search)).work
        rw [advance_debt, advance_quarter, advance_span, advance_work]
        change _ = value (inc (inc v.search.span)) + value (dec v.search.work)
        rw [inc_value, inc_value, dec_value]
        linarith
      · refine ⟨H, hnone, ?_⟩
        show value (advance a (GalilScaffoldDouble.step v.search)).span
          + 2 * value (advance a (GalilScaffoldDouble.step v.search)).work ≤ _
        rw [advance_span, advance_work]
        change value (inc (inc v.search.span)) + 2 * value (dec v.search.work) ≤ _
        rw [inc_value, inc_value, dec_value]
        linarith
    · simp only [hpositive, Bool.false_eq_true, if_false] at hstep
      subst v'
      obtain ⟨span, hspan⟩ := hbudget.span_nat
      obtain ⟨work, hwork⟩ := hbudget.work_nat (Or.inr hm)
      have hworkZero := value_zero_of_not_positive hwork hpositive
      have hw0 : work = 0 := by
        rw [hwork, ofNat_value] at hworkZero
        exact_mod_cast hworkZero
      have hsize := hbudget.double_size hm
      simp only [hspan, hwork, ofNat_value] at hsize
      norm_cast at hsize
      have hquarter : v.search.quarter.val = 0 :=
        double_end_quarter hw0 v.search.quarter.isLt hsize.2.1 hsize.2.2
      rw [hquarter, hworkZero] at hbalance
      apply stageHistory_of_steady
      · rw [ofPrep_mode]; exact Or.inl rfl
      · rw [ofPrep_debt, ofPrep_span]
        change 4 * (value v.search.debt - _ + (R + _)) = value v.search.span
        push_cast at hbalance
        linarith
      · refine ⟨H, hnone, ?_⟩
        rw [ofPrep_span]
        change value v.search.span ≤ _
        have hH : (0 : ℤ) ≤ (H : ℤ) := Int.natCast_nonneg H
        linarith

end PalPeg.SearchStageHistory
