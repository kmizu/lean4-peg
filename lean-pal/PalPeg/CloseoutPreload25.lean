import PalPeg.CloseoutPreload24

/-!
# The three inputs `CloseoutPreload24` §3 lists for `postRunC_of_machine`

`CloseoutPreload24` §2 supplies every leg of one `.run` → `.wait` → `.double` →
`prepare` round trip on `PostRunC`, and §3 names three inputs still missing
before the induction on the event list can be run.  This file settles the two
that are arithmetic / plumbing, and reports the exact obstruction in the first.

* §1 **the `.double` leg's length inequality is false as posed.**  The
  obligation `hlen` of `CloseoutPreload24.double_leg_entries_windowC` is
  `4 * (stageDebt Rad k + stageCredit k (2 * mw) + 1) + 4 * count + 3 ≤ bs.length`
  and `CloseoutPreload17.double_spends` fixes `bs.length = mw`.  But
  `4 * stageCredit k (2 * mw) ≈ 2 * mw - 8 * max k 1` and
  `4 * stageDebt Rad k = 8 * max k 1 - 4 * Rad`, so the left side is
  `≈ 2 * mw - 4 * Rad + 4 * count + 4`: the leg must pay for the *doubled*
  window while running only the old one.  `double_len_of_leg` gives the exact
  sufficient threshold (`2 * mw + 4 * count + 7 ≤ leg length`, unconditional in
  `Rad`), `double_len_needs` the matching necessary condition, and
  `double_len_forces_small_window` / `double_len_false_of_rad_zero` show that at
  `bs.length = mw` the obligation forces `3 * mw + 12 * count + 12 ≤ 20 * k` and
  is outright refutable at `Rad = 0`.  **Fix: the `.double` leg has to run
  `2 * mw + 4 * count + 7` ticks (the doubled span), not `mw`.**
* §2 **the `.wait` leg's budget, converted.**  `depth_supply_of_wait_leg` turns
  `CloseoutPreload23.wait_leg_length_le_of_scan_inv` (`len ≤ 2048 * (debt + 1)`)
  into the next stage's supply clause `D + dpEvents w ≤ rest.length`, against a
  stage budget `N` — residue 2 of `CloseoutPreload24` §3, closed.
* §3 **`ScanRealized`** is only repackaged (`scanRealized_mono`,
  `scanRealized_of_legs`); the leg construction on `galilFrameS` remains the
  `GalilScaffoldTopScan` coupling and is **not** proved here.

**`postRunC_of_machine : CloseoutPreload24.PostRunC` is NOT proved here** — §4.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPreload25

open PalPeg
open PalPeg.GalilScaffoldTop (Frame State)
open PalPeg.GalilScaffoldChainInputSupply (SearchVM)
open PalPeg.GalilScaffoldSearchFinish (Mode)
open PalPeg.GalilScaffoldCounter (Canonical value zero)
open PalPeg.CloseoutReadyStage (PacedL)
open PalPeg.CloseoutDebtAudit (dpEvents)
open PalPeg.CloseoutPreload11 (stageCredit)
open PalPeg.CloseoutPreload14 (WaitTrace)
open PalPeg.CloseoutPreload22 (ClockInv)
open PalPeg.CloseoutPreload21 (ScanTrace)
open PalPeg.CloseoutPreload23 (ScanSupplyInv wait_leg_length_le_of_scan_inv)
open PalPeg.CloseoutPreload24 (ScanRealized)
open PalPeg.GalilReplaySpan (stageDebt)

/-! ## 1. The `.double` leg's length inequality -/

/-- The stage's obligation, as a standalone numeric predicate: the left side of
`hlen` in `CloseoutPreload24.double_leg_entries_windowC`, against a leg of
length `L` with `c` firing ticks. -/
def DoubleLen (Rad k mw c L : ℕ) : Prop :=
  4 * (stageDebt Rad (k : ℤ) + (stageCredit k (2 * mw) : ℤ) + 1) + 4 * (c : ℤ) + 3 ≤ (L : ℤ)

private theorem cast_max (k : ℕ) : ((max k 1 : ℕ) : ℤ) = max (k : ℤ) 1 := by
  push_cast; rfl

/-- The credit is `(2 * mw - 8 * max k 1) / 4`, so `4 * credit` sits within `3`
of `2 * mw - 8 * max k 1`. -/
private theorem credit_bounds {k mw : ℕ} (_hcal : 8 * max k 1 ≤ 2 * mw) :
    4 * stageCredit k (2 * mw) ≤ 2 * mw - 8 * max k 1 ∧
      2 * mw - 8 * max k 1 ≤ 4 * stageCredit k (2 * mw) + 3 := by
  unfold stageCredit
  omega

/-- **NAMED — the sufficient threshold, unconditional in `Rad`.**  A `.double`
leg of length `2 * mw + 4 * count + 7` discharges the obligation for every
`Rad`.  This is the number `CloseoutPreload17.double_spends` would have to
deliver; it delivers `mw`. -/
theorem double_len_of_leg {Rad k mw c L : ℕ} (hcal : 8 * max k 1 ≤ 2 * mw)
    (hL : 2 * mw + 4 * c + 7 ≤ L) : DoubleLen Rad k mw c L := by
  obtain ⟨hc1, -⟩ := credit_bounds (k := k) (mw := mw) hcal
  have hm := cast_max k
  have hd : stageDebt Rad (k : ℤ) = 2 * max (k : ℤ) 1 - (Rad : ℤ) := rfl
  unfold DoubleLen
  rw [hd, ← hm]
  have h1 : (4 * stageCredit k (2 * mw) : ℤ) ≤ ((2 * mw - 8 * max k 1 : ℕ) : ℤ) := by
    exact_mod_cast Nat.cast_le.mpr hc1
  have h2 : ((2 * mw - 8 * max k 1 : ℕ) : ℤ) = 2 * (mw : ℤ) - 8 * ((max k 1 : ℕ) : ℤ) := by
    have : (8 * max k 1 : ℕ) ≤ 2 * mw := hcal
    push_cast [Nat.cast_sub this]
    ring
  have h3 : (0 : ℤ) ≤ (Rad : ℤ) := Int.natCast_nonneg Rad
  have h4 : (2 * mw + 4 * c + 7 : ℤ) ≤ (L : ℤ) := by exact_mod_cast hL
  push_cast at h1 h2 h4 ⊢
  omega

#print axioms double_len_of_leg

/-- **NAMED — the matching necessary condition.**  Any leg discharging the
obligation has length `≥ 2 * mw + 4 * count + 4 - 4 * Rad`. -/
theorem double_len_needs {Rad k mw c L : ℕ} (hcal : 8 * max k 1 ≤ 2 * mw)
    (h : DoubleLen Rad k mw c L) : 2 * mw + 4 * c + 4 ≤ L + 4 * Rad := by
  obtain ⟨-, hc2⟩ := credit_bounds (k := k) (mw := mw) hcal
  have hm := cast_max k
  have hd : stageDebt Rad (k : ℤ) = 2 * max (k : ℤ) 1 - (Rad : ℤ) := rfl
  unfold DoubleLen at h
  rw [hd, ← hm] at h
  have h1 : ((2 * mw - 8 * max k 1 : ℕ) : ℤ) ≤ (4 * stageCredit k (2 * mw) : ℤ) + 3 := by
    exact_mod_cast Nat.cast_le.mpr hc2
  have h2 : ((2 * mw - 8 * max k 1 : ℕ) : ℤ) = 2 * (mw : ℤ) - 8 * ((max k 1 : ℕ) : ℤ) := by
    have : (8 * max k 1 : ℕ) ≤ 2 * mw := hcal
    push_cast [Nat.cast_sub this]
    ring
  have : (2 * mw + 4 * c + 4 : ℤ) ≤ (L : ℤ) + 4 * (Rad : ℤ) := by
    push_cast at h h1 h2 ⊢; omega
  exact_mod_cast this

#print axioms double_len_needs

/-- **NAMED — at the leg length `double_spends` actually delivers the obligation
forces the window to stay below `20 * k / 3`.**  With `bs.length = mw` and the
stage bound `3 * Rad ≤ 5 * k`, the obligation implies
`3 * mw + 12 * count + 12 ≤ 20 * k`; since the calibration already gives
`4 * k ≤ mw`, it fails at every doubling past `mw ≈ 6.7 * k`. -/
theorem double_len_forces_small_window {Rad k mw c : ℕ} (hcal : 8 * max k 1 ≤ 2 * mw)
    (hstage : 3 * Rad ≤ 5 * k) (h : DoubleLen Rad k mw c mw) :
    3 * mw + 12 * c + 12 ≤ 20 * k := by
  have := double_len_needs hcal h
  omega

#print axioms double_len_forces_small_window

/-- **NAMED — the obligation is outright false at `Rad = 0`.**  A stage entered
with radius `0` never discharges `hlen` on a leg of length `mw`, whatever the
calibration.  So the `.double` leg length is a genuine gap, not a bookkeeping
slip. -/
theorem double_len_false_of_rad_zero {k mw c : ℕ} (hcal : 8 * max k 1 ≤ 2 * mw) :
    ¬ DoubleLen 0 k mw c mw := by
  intro h
  have := double_len_needs hcal h
  omega

#print axioms double_len_false_of_rad_zero

/-- Pacing bounds the firing count of a leg by its length over the delay. -/
theorem count_le_of_paced {as : List Bool} (h : PacedL 2048 0 as) :
    2048 * as.count true ≤ as.length := by
  have := h as.length
  simpa using this

#print axioms count_le_of_paced

/-- **NAMED — the threshold in closed form, with the count eliminated.**  A
paced `.double` leg of length `L` with `512 * (2 * mw + 7) ≤ 511 * L`
discharges the obligation: the doubled window plus a `1/511` margin. -/
theorem double_len_of_paced {Rad k mw : ℕ} {bs : List Bool}
    (hcal : 8 * max k 1 ≤ 2 * mw) (hp : PacedL 2048 0 bs)
    (hL : 512 * (2 * mw + 7) ≤ 511 * bs.length) :
    DoubleLen Rad k mw (bs.count true) bs.length := by
  have hc := count_le_of_paced hp
  exact double_len_of_leg hcal (by omega)

#print axioms double_len_of_paced

/-! ## 2. The `.wait` leg's budget, converted to the supply clause -/

section Supply

variable {σ : Type} {F : Frame σ} {I : State σ → Prop}

/-- **NAMED — residue 2 of `CloseoutPreload24` §3, closed.**
`CloseoutPreload23.wait_leg_length_le_of_scan_inv` bounds the `.wait` leg by
`2048 * (debt + 1)` ticks; against a stage budget `N` for the whole stream
`as ++ rest` that becomes exactly the supply clause
`D + dpEvents w ≤ rest.length` the next stage's `DepthAt` obligation
(`CloseoutPreload24.double_leg_entries_windowC`, `runEntriesS_of_double_exitC`)
asks for.  No pacing is used: only the clock phase carried by the scan leg. -/
theorem depth_supply_of_wait_leg (hsup : ScanSupplyInv F 2048 I)
    {ts as rest : List Bool} {p q : State σ} {v t : SearchVM} {debt D w N : ℕ}
    (hr : WaitTrace as v t) (hmt : t.search.mode = Mode.wait)
    (hz : zero t.search.debt = true) (hc : Canonical t.search.debt)
    (hdv : value v.search.debt = (debt : ℤ))
    (hsc : ScanTrace F 2048 ts as p q) (hp : I p) (hcl : ClockInv 2048 p.ctl)
    (hN : (as ++ rest).length = N)
    (hbudget : D + dpEvents w + 2048 * (debt + 1) ≤ N) :
    D + dpEvents w ≤ rest.length := by
  have hlen := wait_leg_length_le_of_scan_inv hsup hr hmt hz hc hdv hsc hp hcl.1 hcl.2
  rw [List.length_append] at hN
  omega

#print axioms depth_supply_of_wait_leg

/-- The same, in the form the stage induction consumes: the remainder of the
stage's stream after a `.wait` leg still carries the next stage's events. -/
theorem stage_supply_after_wait (hsup : ScanSupplyInv F 2048 I)
    {ts as rest : List Bool} {p q : State σ} {v t : SearchVM} {debt D mw N : ℕ}
    (hr : WaitTrace as v t) (hmt : t.search.mode = Mode.wait)
    (hz : zero t.search.debt = true) (hc : Canonical t.search.debt)
    (hdv : value v.search.debt = (debt : ℤ))
    (hsc : ScanTrace F 2048 ts as p q) (hp : I p) (hcl : ClockInv 2048 p.ctl)
    (hN : (as ++ rest).length = N)
    (hbudget : D + dpEvents (2 * mw + 1) + 2048 * (debt + 1) ≤ N) :
    D + dpEvents (2 * mw + 1) ≤ rest.length :=
  depth_supply_of_wait_leg hsup hr hmt hz hc hdv hsc hp hcl hN hbudget

#print axioms stage_supply_after_wait

end Supply

/-! ## 3. `ScanRealized`, repackaged -/

section Realized

variable {σ : Type} {F : Frame σ}

/-- `ScanRealized` only weakens as the invariant weakens. -/
theorem scanRealized_mono {I J : State σ → Prop} (hIJ : ∀ x, I x → J x)
    (h : ScanRealized F I) : ScanRealized F J := by
  intro bs
  obtain ⟨ts, p, q, hsc, hp, hcl⟩ := h bs
  exact ⟨ts, p, q, hsc, hIJ p hp, hcl⟩

#print axioms scanRealized_mono

/-- **NAMED — the shape of the remaining obligation.**  `ScanRealized F I` is
exactly the leg-construction clause: for every event list there is a scan leg of
the controller producing it, entered under `I` and in phase.  Nothing here
proves it; on `galilFrameS` the invariant is
`CloseoutPreload23.bigPack2_scanSupply`'s `BigPack2` and the construction is the
`GalilScaffoldTopScan` coupling. -/
theorem scanRealized_of_legs {I : State σ → Prop}
    (h : ∀ bs : List Bool, ∃ (ts : List Bool) (p q : State σ),
      ScanTrace F 2048 ts bs p q ∧ I p ∧ ClockInv 2048 p.ctl) :
    ScanRealized F I := h

#print axioms scanRealized_of_legs

end Realized

/-!
## 4. What is left

Closed here:

* **residue 2 of `CloseoutPreload24` §3** — `depth_supply_of_wait_leg` /
  `stage_supply_after_wait` convert the `.wait` leg's tick bound into the next
  stage's supply clause.
* **the exact threshold of residue 1** — `double_len_of_leg` (sufficient),
  `double_len_needs` (necessary), `double_len_of_paced` (count eliminated).

**NOT closed — `postRunC_of_machine : CloseoutPreload24.PostRunC` is not proved
here.**

**Missing (one line):** the induction cannot be closed because the `.double`
leg as built by `CloseoutPreload17.double_spends` is `mw` ticks long while
`double_len_needs` shows the obligation requires `2 * mw + 4 * count + 4 - 4 *
Rad` (unconditionally `2 * mw + 4 * count + 7`, `double_len_of_leg`) — so the
`.double` phase must be re-paced over the doubled span before the step of §2 can
be iterated — and `ScanRealized` on `galilFrameS` still awaits the
`GalilScaffoldTopScan` leg construction (§3).

**無条件 PAL ∈ PEG は未完.**
-/

end PalPeg.CloseoutPreload25
