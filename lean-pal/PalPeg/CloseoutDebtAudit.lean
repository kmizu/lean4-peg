import PalPeg.GalilReplaySpan
import PalPeg.GalilRestartStage

/-!
# Audit of the search debt ledger against the comparison budget

Three questions, answered here.

## (1) `GalilReplaySpan.ReplayFitsStage` is false

`ReplayFitsStage raw` says that at *every* restart the replay counter `m`
satisfies `(m : ℤ) ≤ stageDebt Rad (value last) = 2 * max (value last) 1 - Rad`.
Both restarts the machine actually performs — the fallback
(`GalilRestartStage.restart_stage_bound_fallback`) and the init
(`restart_stage_bound_init`) — end in `Restarted raw t 0 reset`, i.e. `Rad = 0`
and `value last = 0`, where `stageDebt = 2` (`stageDebt_zero_reset`).  So
`ReplayFitsStage` asserts that a fallback never has more than **two** positions
left to replay.  `Restarted` does not constrain `r.replay` at all (see
`GalilScaffoldTopReadyFound.Restarted`: the fields mentioned are `chain`,
`center`, `left`, `right`, `radius`, `length`, `search`, `lower`), so any
restart whatsoever refutes it after retargeting the replay counter:
`not_replayFitsStage_of_restarted`.  This is not a subtle trace argument — the
replay of a fallback re-reads the whole look-ahead block, whose length is
`Θ(n)` (`GalilReplayBudgetProof`'s clause 3 is essentially `k ≤ 4n-1`), so the
bound `2` is off by an unbounded factor.

## (2) Where the debt clause really bites (the Scala ledger)

`scala/pal/src/main/scala/pal/ScaffoldSearch.scala`: `debt` starts at `-radius`
(`begin`), gains `2` per unit of `max(lower,1)` in `stepGrow`, loses one per
`advanceMatch()`, and is *checked only at the DP halt* — `stepRun` throws
"match passed the DP stage deadline" when `debt.sign < 0` at `program.done`,
and `stepWait` deliberately drains the debt to exactly `0` before
`doubleWindow`.  The debt is therefore a **rolling** counter, never reset
between stages (`prepareWindow` touches `lower/work/span`, not `debt`;
`stepDouble` refills it by one per four consumed span cells).

So the machine's obligation is *local*: the comparisons that occur between the
`.run` entry and the halt of that stage's DP fit the debt at the entry.  The
obligation is discharged at `.found`/`.missed`/`.wait`/`.double`, exactly as
`GalilSearchReadyInv.ReadyRem` guards `DpSafeRem` by `mode = .run`.  But
`DpSafeRem v as` charges *the whole remaining list* `as` against the entry debt
(`CloseoutReadinessAudit.dpSafeRem_count_le`), and `as` is the rest of the
threaded segment, not the rest of the DP run.  That over-charge is precisely
what already refuted `RunEntriesAtBegin` and `RunEntriesPaced`
(`CloseoutReadinessAudit`, `CloseoutRunEntriesPaced`), and it is why
`ReadyFuel v n (headRank r.right)` of `GalilSegmentConstructB` cannot be had at
a debt of `≈ 2k`: `ReadyFuel` bounds the comparisons by `headRank r.right`,
which is the *input* head rank, not a stage-local quantity.

## (3) The invariant that is true, and its arithmetic

The correct per-stage statement is the cut one: only the events up to the DP
halt are charged.  The DP halt is reachable within `3186*|w|+1683` instructions
at `64` per event (`DpSafeRem`'s own entry side condition
`3186*w.length+1683 ≤ 64*(bs ++ as).length`), and the calibrated window of a
stage with lower bound `k` is `|w| = 8 * max k 1`
(`GalilRestartStage.value_reset`'s comment).  With the clock pacing `delay =
2048` a run of `n` events holds at most `n / 2048 + 1` comparisons, so the
comparisons charged to the stage satisfy

    8192 * c ≤ 1593 * k + 9894   (i.e. 131072 * c ≤ 25488 * (k+1) + 1746 + 131072),

and `stage_fits` shows that this is `≤ stageDebt Rad k` for every `Rad` allowed
by `StageEntry` (`3 * Rad ≤ 5 * k`) — for every `k`, with no side condition
(`stage_fits`, `paced_bound`, `stage_budget_closes`).  So the local invariant
is provable stage by stage; it is only the unbounded suffix in `DpSafeRem` and
the unbounded replay counter in `ReplayFitsStage` that are not.
-/

set_option autoImplicit false

namespace PalPeg.CloseoutDebtAudit

open PalPeg PalPeg.GalilReplaySpan PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilScaffoldCounter (value reset ofNat ofNat_value)

/-! ## 1. The stage debt of the restarts the machine performs -/

/-- Both real restarts (`Rad = 0`, `last = reset`) have stage debt `2`. -/
theorem stageDebt_zero_reset : stageDebt 0 (value reset) = 2 := by
  rw [PalPeg.GalilScaffoldChainInputSupply.value_reset]
  norm_num [stageDebt]

/-- `ReplayFitsStage` forces every fallback/init restart to have at most two
positions left to replay. -/
theorem replayFitsStage_bound {raw : List (Fin 2)} (h : ReplayFitsStage raw)
    {r : GalilVM} {m : ℕ} (hR : Restarted raw r 0 reset) (hm : r.replay = ofNat m) :
    m ≤ 2 := by
  have := h r 0 reset m hR (stageEntry_zero reset) hm
  rw [stageDebt_zero_reset] at this
  exact_mod_cast this

/-- **`ReplayFitsStage` is false.**  `Restarted` says nothing about `replay`, so
retargeting the replay counter of any restart to `3` refutes it. -/
theorem not_replayFitsStage_of_restarted {raw : List (Fin 2)} {r : GalilVM}
    (hR : Restarted raw r 0 reset) : ¬ ReplayFitsStage raw := by
  intro h
  have hR' : Restarted raw { r with replay := ofNat 3 } 0 reset := hR
  have : (3 : ℕ) ≤ 2 := replayFitsStage_bound h hR' rfl
  omega

/-! ## 2. The rolling ledger: the charge is local to the DP run -/

/-- The events a stage with window `w` needs before its DP halts, at the `64`
instructions per event of `DpSafeRem`'s entry condition. -/
def dpEvents (w : ℕ) : ℕ := (3186 * w + 1683 + 63) / 64

/-- The calibrated window of a stage with lower bound `k`. -/
def stageWindow (k : ℕ) : ℕ := 8 * max k 1

/-- The comparisons a clock-paced run of `n` events can hold. -/
def pacedComparisons (delay n : ℕ) : ℕ := n / delay + 1

/-! ## 3. The local budget closes, unconditionally -/

/-- **The true stage budget.**  Any comparison count that fits the clock-paced
DP run of the calibrated window of a stage with lower bound `k` fits that
stage's debt, for every radius `StageEntry Rad last` permits.  `131072 =
64 * 2048` is `DpSafeRem`'s instructions-per-event times the clock pacing. -/
theorem stage_fits {k Rad c : ℕ} (hstage : 3 * Rad ≤ 5 * k)
    (hc : 8192 * c ≤ 1593 * k + 9894) :
    (c : ℤ) ≤ stageDebt Rad (k : ℤ) := by
  have hnat : c + Rad ≤ 2 * max k 1 := by omega
  have hcast : (c : ℤ) + (Rad : ℤ) ≤ 2 * max (k : ℤ) 1 := by
    have h := (Nat.cast_le (α := ℤ)).mpr hnat
    push_cast at h
    exact h
  rw [stageDebt]
  omega

/-- The paced comparison count of one stage really is bounded the way
`stage_fits` assumes. -/
theorem paced_bound (k : ℕ) :
    8192 * pacedComparisons 2048 (dpEvents (stageWindow k)) ≤ 1593 * k + 9894 := by
  unfold pacedComparisons dpEvents stageWindow
  have harg : 3186 * (8 * max k 1) + 1683 + 63 = 25488 * max k 1 + 1746 := by ring
  rw [harg, Nat.div_div_eq_div_mul]
  have h2 : (25488 * max k 1 + 1746) / (64 * 2048) * (64 * 2048)
      ≤ 25488 * max k 1 + 1746 := Nat.div_mul_le_self _ _
  have hM : max k 1 ≤ k + 1 := by omega
  omega

/-- Combined: the stage-local charge never exceeds the stage debt. -/
theorem stage_budget_closes {k Rad : ℕ} (hstage : 3 * Rad ≤ 5 * k) :
    ((pacedComparisons 2048 (dpEvents (stageWindow k)) : ℕ) : ℤ) ≤ stageDebt Rad (k : ℤ) :=
  stage_fits hstage (paced_bound k)

/-! ## 4. The *true* window: one cell more (`CloseoutPreload3` §1) -/

/-- **The window the preparation really copies.**  The span handed to `prepare`
is `8 * max k 1` (`CloseoutPreload3.grow_span_calibration`), and the copy takes
`span + 1` cells of the place stream, so the calibrated window of a stage with
lower bound `k` is `stageWindow k + 1`.  `stageWindow` itself stays as it was —
`CloseoutRunEntriesS.stageWindow_restart` reads `stageWindow 0 = 8` off it — but
every *window-length* clause downstream uses `stageWindow1`. -/
def stageWindow1 (k : ℕ) : ℕ := 8 * max k 1 + 1

theorem stageWindow1_eq (k : ℕ) : stageWindow1 k = stageWindow k + 1 := rfl

/-- **The stage budget still closes for the true window.**  The extra cell costs
`3186` instructions, i.e. less than one comparison at `64 * 2048` ticks each. -/
theorem paced_bound1 (k : ℕ) :
    8192 * pacedComparisons 2048 (dpEvents (stageWindow1 k)) ≤ 1593 * k + 9894 := by
  unfold pacedComparisons dpEvents stageWindow1
  have harg : 3186 * (8 * max k 1 + 1) + 1683 + 63 = 25488 * max k 1 + 4932 := by ring
  rw [harg, Nat.div_div_eq_div_mul]
  have h2 : (25488 * max k 1 + 4932) / (64 * 2048) * (64 * 2048)
      ≤ 25488 * max k 1 + 4932 := Nat.div_mul_le_self _ _
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    norm_num at h2 ⊢
  · have hM : max k 1 = k := by omega
    rw [hM] at h2 ⊢
    omega

/-- `stage_budget_closes` for the true window. -/
theorem stage_budget_closes1 {k Rad : ℕ} (hstage : 3 * Rad ≤ 5 * k) :
    ((pacedComparisons 2048 (dpEvents (stageWindow1 k)) : ℕ) : ℤ) ≤ stageDebt Rad (k : ℤ) :=
  stage_fits hstage (paced_bound1 k)

/-- **The entry length of a stage**: the eight preparation events of the
`.run` entry plus the charged prefix of the stage's DP run.  This is the lower
bound the readiness ledger has to carry (`CloseoutPreload.RdPaced`). -/
def dpEntry (k : ℕ) : ℕ := 8 + dpEvents (stageWindow1 k)

theorem dpEvents_le_dpEntry (k : ℕ) : dpEvents (stageWindow1 k) ≤ dpEntry k := by
  unfold dpEntry; omega

end PalPeg.CloseoutDebtAudit

#print axioms PalPeg.CloseoutDebtAudit.stageDebt_zero_reset
#print axioms PalPeg.CloseoutDebtAudit.replayFitsStage_bound
#print axioms PalPeg.CloseoutDebtAudit.not_replayFitsStage_of_restarted
#print axioms PalPeg.CloseoutDebtAudit.stage_fits
#print axioms PalPeg.CloseoutDebtAudit.paced_bound
#print axioms PalPeg.CloseoutDebtAudit.stage_budget_closes
#print axioms PalPeg.CloseoutDebtAudit.paced_bound1
#print axioms PalPeg.CloseoutDebtAudit.stage_budget_closes1
#print axioms PalPeg.CloseoutDebtAudit.dpEvents_le_dpEntry
