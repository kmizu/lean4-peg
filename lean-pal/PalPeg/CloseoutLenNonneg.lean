import PalPeg.CloseoutPackRun17
import PalPeg.CloseoutRadPack
import PalPeg.GalilCentreLive

/-!
# The `length` counter is never negative

`CloseoutPackRun17.marksInv'_of_run'` — the `H_marksEntry'`-free reader — asks
for `0 ≤ value z.vm.length` at every `scan` state of the run.  That is not in
`CPack`: its `canon` field is only `Canonical s.length`, and
`Canonical c := c.pos = [] ∨ c.neg = []` (`GalilScaffoldCounter:14`) allows the
negative side.

But the machine never decrements `length`.  Every assignment to the field in the
whole development is `reset`, `ofNat _`, or `inc` (`GalilBootVM:45`,
`GalilScaffoldTopRewind:56,178`, `CloseoutWatchRound30:209`,
`CloseoutWatchRound33:312`, `CloseoutPackRun50:54`, `GalilLeafQuiet:121`) — there
is no `length := dec …` anywhere.  So non-negativity is a plain tick invariant
once the three counter facts below are in hand.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false

namespace PalPeg.CloseoutLenNonneg

open GalilScaffoldCounter

/-- `reset` has value `0`. -/
theorem value_reset : value reset = 0 := by simp [value, reset]

/-- `ofNat n` has value `n`. -/
theorem value_ofNat (n : ℕ) : value (ofNat n) = (n : ℤ) := by
  simp [value, ofNat]

/-- `0 ≤ value (ofNat n)`. -/
theorem nonneg_ofNat (n : ℕ) : 0 ≤ value (ofNat n) := by
  rw [value_ofNat]; exact Int.ofNat_nonneg n

/-- **`inc` preserves non-negativity.**  `inc ⟨pos, neg⟩` either drops a unit
from `neg` (raising the value by one) or pushes onto `pos` (the same). -/
theorem nonneg_inc {c : Counter} (h : 0 ≤ value c) : 0 ≤ value (inc c) := by
  unfold inc
  cases hn : c.neg with
  | nil => simp [value, hn] at h ⊢; omega
  | cons a ns => simp [value, hn] at h ⊢; omega

/-- `inc` raises the value by exactly one. -/
theorem value_inc (c : Counter) : value (inc c) = value c + 1 := by
  unfold inc value
  cases hn : c.neg with
  | nil => simp [hn]
  | cons a ns => simp [hn]; omega

/-- `0 ≤ value reset`. -/
theorem nonneg_reset : 0 ≤ value reset := by rw [value_reset]

#print axioms value_reset
#print axioms nonneg_ofNat
#print axioms nonneg_inc
#print axioms value_inc

/-! ## Why the tick invariant does **not** follow from these

`shiftTick` (`GalilScaffoldChainInputSupply:1445`) sets

```
length := dec (dec s.length)
```

so `length` *does* decrease, twice per `shift_one` tick.  The claim
"`length` is never decremented" — which an assignment-site grep suggests, since
every syntactic `length := …` is `reset`, `ofNat _` or `inc` — is **wrong**:
the `shift` phase goes through `shiftLens.set` and `shiftTick`, where the field
is updated inside a `ShiftState` record rather than by a visible
`length := dec …`.

So `0 ≤ value s.length` at `scan` states (`CloseoutPackRun17.marksInv'_of_run'`'s
`hfl`) needs the shift phase's own budget: `shift_one` fires only while
`remainingPos s`, and `ShiftGeom` (`CloseoutPackRun23:86`) ties `remaining` to
the head positions.  That is the real obligation, recorded in
`CLOSEOUT_LEDGER.md`.
-/

end PalPeg.CloseoutLenNonneg
