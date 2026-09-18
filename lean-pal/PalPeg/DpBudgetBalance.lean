import PalPeg.StageBudgetShift

/-!
# The readiness budget, as arithmetic

`CloseoutReadyStage.ReadyIface` asks a predicate `Φ v n k` for two transport
steps, and their guards fix the accounting completely:

| field | guard | DP events still needed | slack `k` | debt |
|---|---|---|---|---|
| `background` | — | `-1` | `≤ k + 1` | unchanged |
| `comparison` | `2048 ≤ k + 1` | `-1` | `→ 0` | one comparison spent |

So along a background tick the pair `(need, k)` keeps its sum, and along a
comparison — which the guard only permits at `k = 2047` — that sum drops by
exactly `2048` while one unit of debt is spent.  The quantity

```
spent + ⌈(need + k) / 2048⌉ ≤ debt
```

is therefore **exactly balanced**: neither tick can break it, and neither has
slack to spare.  That is the reason the constant `2048` appears on both sides of
the machine, and it is why `ReadyIface.comparison` carrying `2048 ≤ k + 1` is
not a technicality: it is what stops a schedule from spending several
comparisons in a row against one stage's debt.

`CloseoutReadyStage.ReadyPacedS` obtains the same bound from
`PacedL 2048 k as` over an arbitrary continuation.  That hypothesis is weaker
than the clock: `PacedL` bounds the comparison count *cumulatively from the
start of the list*, so a list may save its budget over a long background stretch
and then spend it in a burst (`replicate (2048 * m) false ++ replicate m true`
is `PacedL 2048 0`), which the machine cannot do.  The arithmetic here is stated
against the current slack instead, so no such schedule is admitted.

**Not done here.**  This file is the accounting only; nothing connects it to
`DpReached`, to `SearchVM` or to `ReadyIface` yet, so no hypothesis is removed.
-/

set_option autoImplicit false

namespace PalPeg.DpBudgetBalance

/-- **The budget at a running DP.**  `need` is the number of events the DP still
has to be given, `spent` the comparisons charged to this stage so far, `debt`
the stage debt it started with, and `k` the current clock slack. -/
def DpBudget (need spent debt k : ℕ) : Prop :=
  spent + (need + k + 2047) / 2048 ≤ debt

/-- **What the budget gives the `ready` field.**  The comparisons already
charged are within the debt, which is what `GalilBranchInvariants2.DpSafeHere`
asks for once its existential continuation is taken all-background. -/
theorem dpBudget_spent {need spent debt k : ℕ} (h : DpBudget need spent debt k) :
    spent ≤ debt := by
  unfold DpBudget at h; omega

/-- **The `mono` field.**  A smaller slack is a weaker claim. -/
theorem dpBudget_mono {need spent debt k k' : ℕ} (hk : k' ≤ k)
    (h : DpBudget need spent debt k) : DpBudget need spent debt k' := by
  unfold DpBudget at h ⊢
  have : (need + k' + 2047) / 2048 ≤ (need + k + 2047) / 2048 :=
    Nat.div_le_div_right (by omega)
  omega
/-- **The `background` field.**  One event of the DP's need is met and the slack
grows by at most one, so the sum `need + k` does not grow. -/
theorem dpBudget_background {need spent debt k k' : ℕ} (hneed : 1 ≤ need)
    (hk : k' ≤ k + 1) (h : DpBudget need spent debt k) :
    DpBudget (need - 1) spent debt k' := by
  unfold DpBudget at h ⊢
  have : (need - 1 + k' + 2047) / 2048 ≤ (need + k + 2047) / 2048 :=
    Nat.div_le_div_right (by omega)
  omega

/-- **The `comparison` field.**  The guard `2048 ≤ k + 1` forces `k = 2047`, so
resetting the slack to `0` while meeting one more event of the need drops
`need + k` by exactly `2048` — one whole unit of the ceiling, which is what pays
for the comparison. -/
theorem dpBudget_comparison {need spent debt k : ℕ} (hneed : 1 ≤ need)
    (hk : 2048 ≤ k + 1) (h : DpBudget need spent debt k) :
    DpBudget (need - 1) (spent + 1) debt 0 := by
  unfold DpBudget at h ⊢
  have hstep : (need - 1 + 0 + 2047) / 2048 + 1 ≤ (need + k + 2047) / 2048 := by
    have hle : (need - 1 + 2047) / 2048 + 1 = (need - 1 + 2047 + 2048) / 2048 := by
      omega
    have hmono : (need - 1 + 2047 + 2048) / 2048 ≤ (need + k + 2047) / 2048 :=
      Nat.div_le_div_right (by omega)
    omega
  omega

/-- **The guard `2048 ≤ k + 1` is sharp.**  One unit less of slack already
breaks the step: `need = 2`, `spent = 0`, `debt = 1` satisfies the budget at
`k = 2046`, and the comparison would have to leave `DpBudget 1 1 1 0`, which it
does not.  So `ReadyIface.comparison` cannot be weakened to `2047 ≤ k + 1`. -/
theorem dpBudget_comparison_needs_full_slack :
    DpBudget 2 0 1 2046 ∧ ¬ DpBudget (2 - 1) (0 + 1) 1 0 := by
  constructor <;> · unfold DpBudget; omega

#print axioms dpBudget_spent
#print axioms dpBudget_mono
#print axioms dpBudget_background
#print axioms dpBudget_comparison
#print axioms dpBudget_comparison_needs_full_slack

end PalPeg.DpBudgetBalance
