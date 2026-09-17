import PalPeg.CloseoutPreload25

/-!
# `PostRunC'` — the `.double` exit with a carried debt

`CloseoutPreload25` §1 shows the `.double` exit clause of the round trip
(`CloseoutPreload24.round_trip_entries`, `hlen`) is false at the leg length the
machine actually spends (`CloseoutPreload17.double_spends`: exactly `mw` ticks).
The machine is right and the obligation is mis-stated: the doubling phase earns
one unit of debt per four ticks (`GalilScaffoldDouble.step`), i.e. `≈ mw / 4`,
and the Scala spec (`ScaffoldSearch.scala`, `doubleWindow` → `Mode.Double` →
`prepareWindow`) amortises the doubled window in the following `.run` leg.

* §1 `doubleCarry` / `PostRunC'` — the carried-debt contract.  `PostRunC'` keeps
  the `.run`-entry clause of `CloseoutPreload24.PostRunC` verbatim and replaces
  the `.double` exit clause: the exit may be short of the stage budget
  `stageDebt Rad k + stageCredit k (2 * mw) + 1` by `doubleCarry mw count`, and
  that shortfall is charged into the next stage's `stageDebt` accounting as an
  enlarged radius `Rad + doubleCarry mw count` (`stageDebt (Rad + c) k =
  stageDebt Rad k - c`, definitionally), so every downstream consumer
  (`stageStart_of_double_exit` → `runEntriesS_of_stageInvPPC` →
  `dpSafe_of_stagePrepP`) sees the ordinary budget shape.  The match-clock
  conservation and `runP_exit_debt_at_exit_scan` are untouched: no pacing or
  clock premise changes, only the exit-debt number.
* §2 `postRunC'_of_double_leg` — a `.double` leg of length exactly `mw`
  (`double_exit_debt_ge`) satisfies the carried clause, and the exit dispatches
  into the `(k, 2 * mw)` stage's `RunEntriesS`, on `PostRunC`.

**The one hypothesis left** is the discharge clause inside `PostRunC'`:
`3 * (Rad + doubleCarry mw count) ≤ 5 * k`.  It is exactly the stage bound
`3 * Rad' ≤ 5 * k` at the enlarged radius, and since `doubleCarry mw c ≈ mw / 4`
it caps the window at `mw ≲ 20 * k / 3` — the same cap
`CloseoutPreload25.double_len_forces_small_window` found.  So the carried debt
is *not* absorbed by the existing `stageDebt + stageCredit` accounting for
large windows; that accounting credits `stageCredit k (2 * mw) ≈ mw / 2` while
the leg earns `mw / 4` (the `.wait` exit resets the debt to `0`,
`CloseoutPreload24.wait_exit_debt_zero`, so credits do not accumulate across
doublings).  The real fix is to halve `stageCredit` (`(m - 8 * max k 1) / 8`)
and re-run `CloseoutPreload11.budget_adv2_nat`, which still closes since the DP
demand is `≈ m / 41`; that is a change to `CloseoutPreload11` and is not made
here.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPreload26

open PalPeg PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController
open PalPeg.GalilScaffoldSearchFinish (Mode)
open PalPeg.GalilScaffoldCounter (Canonical value ofNat positive)
open PalPeg.CloseoutReadyStage (DpSafeStage PacedL RunEntriesS)
open PalPeg.CloseoutDebtAudit (dpEvents)
open PalPeg.CloseoutPreload6 (prepLen)
open PalPeg.CloseoutPreload8 (DepthAt)
open PalPeg.CloseoutPreload11 (stageCredit)
open PalPeg.CloseoutPreload17 (DoubleTrace double_spends double_exit_canonical)
open PalPeg.CloseoutPreload18 (double_exit_debt_ge)
open PalPeg.CloseoutPreload21 (ScanTrace)
open PalPeg.CloseoutPreload22 (ClockInv)
open PalPeg.CloseoutPreload23 (ScanSupplyInv)
open PalPeg.CloseoutPreload24 (PostRunC ScanRealized runEntriesS_of_double_exitC)
open PalPeg.GalilReplaySpan (stageDebt)

/-! ## 1. The carried debt and `PostRunC'` -/

/-- **The carried debt of a `.double` leg** of length `mw` with `c` firing ticks:
the amount by which the exit debt `≈ (mw - 4 * c) / 4` falls short of the stage
budget `≈ 2 * mw / 4`, rounded up. -/
def doubleCarry (mw c : ℕ) : ℕ := (mw + 4 * c + 10) / 4

/-- **NAMED — `PostRunC` with the `.double` exit clause carried.**  The first
conjunct is `CloseoutPreload24.PostRunC` verbatim (the `.run`-entry clause).  The
second replaces the round trip's `.double` exit clause
(`CloseoutPreload24.round_trip_entries`, `hlen`): the leg has length exactly `mw`
(`bs.length = mw`, as `double_spends` delivers) and the shortfall
`doubleCarry mw (bs.count true)` is charged to the next stage as an enlarged
radius — the stage bound `3 * Rad ≤ 5 * k` is asked at `Rad + doubleCarry`, which
is the one hypothesis §2 cannot discharge. -/
def PostRunC' (carry : ℕ → ℕ → ℕ) : Prop :=
  PostRunC ∧
  ∀ {σ : Type} {F : Frame σ} {I : State σ → Prop},
    ScanSupplyInv F 2048 I → ScanRealized F I →
    ∀ {c' : GalilScaffoldPlace.Place} {k Rad D mw : ℕ} {a : Bool} {bs : List Bool}
      {v t t' : SearchVM},
      DoubleTrace bs v t → value v.search.debt = 0 → v.search.quarter = 0 →
      Canonical v.search.debt →
      t.search.mode = Mode.double → positive t.search.work = false →
      t.search.span = ofNat (2 * mw) → t.lower = ofNat k → bs.length = mw →
      8 * max k 1 ≤ 2 * mw →
      3 * (Rad + carry mw (bs.count true)) ≤ 5 * k →
      searchStep c' a t t' → DepthAt t' D → D ≤ prepLen k →
      ∀ as : List Bool,
        D + dpEvents (2 * mw + 1) ≤ as.length → PacedL 2048 0 as → RunEntriesS as t'

/-! ## 2. The `.double` leg of length `mw` satisfies the carried clause -/

private theorem cast_max (k : ℕ) : ((max k 1 : ℕ) : ℤ) = max (k : ℤ) 1 := by
  push_cast; rfl

/-- **The exit debt of a `.double` leg of length `mw` meets the stage budget at
the enlarged radius `Rad + doubleCarry mw count`.**  Pure arithmetic on
`CloseoutPreload18.double_exit_debt_ge` and `stageCredit`. -/
theorem double_exit_debt_carry {Rad k mw : ℕ} {bs : List Bool} {v t : SearchVM}
    (hr : DoubleTrace bs v t) (htm : t.search.mode = Mode.double)
    (htw : positive t.search.work = false)
    (hv0 : value v.search.debt = 0) (hq : v.search.quarter = 0)
    (hblen : bs.length = mw) (hcal : 8 * max k 1 ≤ 2 * mw) :
    stageDebt (Rad + doubleCarry mw (bs.count true)) (k : ℤ)
        + (stageCredit k (2 * mw) : ℤ) + 1 ≤ value t.search.debt := by
  have hge := double_exit_debt_ge hr htm htw hv0 hq
  rw [hblen] at hge
  have hcred : 4 * stageCredit k (2 * mw) ≤ 2 * mw - 8 * max k 1 := by
    unfold stageCredit; omega
  have hcarry : mw + 4 * bs.count true + 7 ≤ 4 * doubleCarry mw (bs.count true) := by
    unfold doubleCarry; omega
  have hd : stageDebt (Rad + doubleCarry mw (bs.count true)) (k : ℤ)
      = 2 * max (k : ℤ) 1 - ((Rad + doubleCarry mw (bs.count true) : ℕ) : ℤ) := rfl
  rw [hd, ← cast_max k]
  have h1 : (4 * stageCredit k (2 * mw) : ℤ) ≤ ((2 * mw - 8 * max k 1 : ℕ) : ℤ) := by
    exact_mod_cast Nat.cast_le.mpr hcred
  have h2 : ((2 * mw - 8 * max k 1 : ℕ) : ℤ) = 2 * (mw : ℤ) - 8 * ((max k 1 : ℕ) : ℤ) := by
    have : (8 * max k 1 : ℕ) ≤ 2 * mw := hcal
    push_cast [Nat.cast_sub this]
    ring
  have h3 : ((mw + 4 * bs.count true + 7 : ℕ) : ℤ)
      ≤ ((4 * doubleCarry mw (bs.count true) : ℕ) : ℤ) := by exact_mod_cast hcarry
  push_cast at h1 h2 h3 hge ⊢
  omega

#print axioms double_exit_debt_carry

/-- **NAMED — `PostRunC'` holds at `doubleCarry`, on `PostRunC`.**  The `.double`
leg of length exactly `mw` (the shape `CloseoutPreload17.double_spends` builds)
meets the carried exit clause by `double_exit_debt_carry`, and the exit
dispatches into the `(k, 2 * mw)` stage through
`CloseoutPreload24.runEntriesS_of_double_exitC` at the enlarged radius.  The only
input beyond `PostRunC` is the discharge clause `3 * (Rad + doubleCarry mw
count) ≤ 5 * k`, which is a premise of the clause itself. -/
theorem postRunC'_of_double_leg (hpost : PostRunC) : PostRunC' doubleCarry := by
  refine ⟨hpost, ?_⟩
  intro σ F I hsup hreal c' k Rad D mw a bs v t t' hr hv0 hq hvc htm htw hts htl hblen
    hcal hdis hs hdep hD
  exact runEntriesS_of_double_exitC (Rad := Rad + doubleCarry mw (bs.count true))
    htm htw hts htl hcal (double_exit_canonical hr htm htw hvc) hdis
    (double_exit_debt_carry hr htm htw hv0 hq hblen hcal) hs hdep hD hsup hreal hpost

#print axioms postRunC'_of_double_leg

/-- The same, entered from the `.double` state `double_spends` produces: the leg
is *built*, not assumed. -/
theorem postRunC'_double_spends {c : GalilScaffoldPlace.Place} {k mw : ℕ} {bs : List Bool}
    {v : SearchVM}
    (hm : v.search.mode = Mode.double) (hw : v.search.work = ofNat mw)
    (hsp : v.search.span = GalilScaffoldCounter.reset) (hlow : v.lower = ofNat k)
    (hblen : bs.length = mw) (hcal : 8 * max k 1 ≤ 2 * mw)
    (hv0 : value v.search.debt = 0) (hq : v.search.quarter = 0) :
    ∃ t : SearchVM, DoubleTrace bs v t ∧ t.search.mode = Mode.double ∧
      positive t.search.work = false ∧ t.search.span = ofNat (2 * mw) ∧
      t.lower = ofNat k ∧
      ∀ Rad : ℕ,
        stageDebt (Rad + doubleCarry mw (bs.count true)) (k : ℤ)
          + (stageCredit k (2 * mw) : ℤ) + 1 ≤ value t.search.debt := by
  obtain ⟨t, hr, htm, htw, hts, htl, -, -⟩ := double_spends c hm hw hsp hblen
  exact ⟨t, hr, htm, htw, hts, by rw [htl, hlow], fun Rad =>
    double_exit_debt_carry hr htm htw hv0 hq hblen hcal⟩

#print axioms postRunC'_double_spends

/-!
## 3. What is left

Closed here: `PostRunC' doubleCarry` on `PostRunC` (`postRunC'_of_double_leg`),
with the `.double` leg at its true length `mw` (`postRunC'_double_spends`).

**NOT closed:** the discharge clause `3 * (Rad + doubleCarry mw count) ≤ 5 * k`
is a premise, not a theorem, and it fails for `mw > 20 * k / 3`: the carried
debt cannot be absorbed by the `stageDebt Rad k + stageCredit k (2 * mw)`
accounting, whose credit is twice what the leg earns.  `postRunC_of_machine`
(`PostRunC` itself) is likewise still open.

**無条件 PAL ∈ PEG は未完.**
-/

end PalPeg.CloseoutPreload26
