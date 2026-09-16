import PalPeg.GalilDpCost

set_option autoImplicit false
namespace PalPeg.GalilScaffoldTimingCost

/-- Ceiling of the proved DP instruction budget on at most span+1 symbols,
at quantum 64. This is a numeric budget, not yet a Search schedule theorem. -/
def runBudget (span : ℕ) : ℕ := (3186*(span+1)+1683+63)/64

theorem runBudget_sufficient (span : ℕ) :
    3186*(span+1)+1683 ≤ 64*runBudget span := by
  unfold runBudget
  omega

/-- First-stage calibration corresponding to GalilClock.derive's 19/8
control factor and ten fixed ticks. Actual control-cost correspondence is separate. -/
theorem first_stage (span : ℕ) (hs : 8 ≤ span) :
    19*span/8 + 10 + runBudget span ≤ 63*span := by
  unfold runBudget
  omega

theorem later_stage (span : ℕ) (hs : 16 ≤ span) :
    11*span/4 + 10 + runBudget span ≤ 63*span := by
  unfold runBudget
  omega

/-- Actual grow and preparation costs, followed by the calibrated run budget. -/
theorem first_stage_ticks (r m : ℕ) (hm : m ≤ 8*max r 1+1) :
    max r 1+2*r+2*m+7+runBudget (8*max r 1) ≤ 63*(8*max r 1) := by
  have h := first_stage (8*max r 1) (by omega)
  have hr : r ≤ max r 1 := le_max_left _ _
  omega

theorem delay_calibration : 24*63 ≤ (2048 : ℕ) ∧ (1024 : ℕ) < 24*63 := by decide

theorem later_stage_ticks (n lower m : ℕ) (hn : 8 ≤ n)
    (hl : 4*lower ≤ n) (hm : m ≤ 2*n+1) :
    n+2*lower+2*m+7+runBudget (2*n) ≤ 63*(2*n) := by
  have h := later_stage (2*n) (by omega)
  omega

#print axioms first_stage
#print axioms first_stage_ticks
#print axioms later_stage_ticks
#print axioms later_stage
end PalPeg.GalilScaffoldTimingCost
