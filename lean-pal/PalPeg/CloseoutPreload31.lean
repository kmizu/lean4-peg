import PalPeg.CloseoutPreload30

/-!
# `PostRunF` — the framed post-run contract, and the round trip to `prepare`

`CloseoutPreload30` §4 lists why the `.wait → .double → prepare` leg of the
`PostRunC` induction does not compose from `PostRunC`'s own premises: the stage
datum `DpSafeStage v as` carries no frame, and the pacing at the `.double` exit
is a suffix (slack `≤ 2047`, not `0`).  This file

* §1 defines `PostRunF F I` — `CloseoutPreload30.PostRunPh` whose stage datum
  carries the frame of the `.run` entry (`span = ofNat mw`, `lower = ofNat k`,
  the window-doubling calibration `8 * max k 1 ≤ mw`, `Canonical` debt; the DP
  preload is the `DpReached` witness inside `DpSafeStage`) and whose phase
  clause is `PrefixPhase` of the *reachable* preparation prefix, given as the
  `ScanTrace F 2048 ts pre p q` datum of `CloseoutPreload29.PostRunD`'s
  `.double` clause (entered under `I p ∧ ClockInv 2048 p.ctl`), **not** as
  `ScanRealized` (refuted by `CloseoutPreload30.scanRealized_absurd`).
* §2 proves `postRunF_round_trip`: from the framed `.run` entry, through the
  `.run` leg (`run_exit_frame`), the `.wait` leg (`wait_exit_double`,
  `wait_exit_debt_zero`), the `.double` leg (`double_spends`) and the dispatch
  tick (`prepAt_of_double_exit`), the next stage's entry satisfies
  `PrepAt k (2 * mw) ∧ StageInvD k (2 * mw)` with the doubled calibration.  The
  balance `hbal` is *derived*: `prefixPhase_of_scan_inv` on the reachable
  prefix up to the `.double` entry, `pacedL_suffix_2047`, `eight_le_of_cal`,
  `bal_of_paced_slack`.  `runEntriesS_of_double_exitD` is **not** used — it
  takes `ScanRealized`, so any use of it is vacuous.
* §3 says what is not closed.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPreload31

open PalPeg PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController
open PalPeg.GalilScaffoldSearchFinish (Mode)
open PalPeg.GalilScaffoldCounter (Canonical value ofNat positive zero)
open PalPeg.CloseoutReadyStage (DpSafeStage PacedL RunEntriesS)
open PalPeg.CloseoutPreload10 (PrepAt prepAt_of_double_exit)
open PalPeg.CloseoutPreload13 (RunTrace run_exit_frame)
open PalPeg.CloseoutPreload14 (WaitTrace wait_step_cases wait_exit_double)
open PalPeg.CloseoutPreload17 (DoubleTrace double_spends double_exit_canonical)
open PalPeg.CloseoutPreload18 (PrefixPhase pacedL_suffix_2047)
open PalPeg.CloseoutPreload21 (ScanTrace)
open PalPeg.CloseoutPreload22 (ClockInv)
open PalPeg.CloseoutPreload23 (ScanSupplyInv prefixPhase_of_scan_inv)
open PalPeg.CloseoutPreload24 (wait_exit_debt_zero)
open PalPeg.CloseoutPreload28 (StageInvD stageInvD_of_double_exit bal_of_paced_slack)
open PalPeg.CloseoutPreload29 (eight_le_of_cal)
open PalPeg.CloseoutPreload30 (PostRunPh)

/-! ## 1. The framed contract -/

/-- **NAMED — the framed, reachable-prefix post-run contract.**  `PostRunPh`
with (a) the frame of the `.run` entry (`span`, `lower`, calibration,
`Canonical` debt; the DP preload is inside `DpSafeStage`) and (b) the phase
clause replaced by the machine datum: the preparation prefix `pre` is a scan
leg `ScanTrace F 2048 ts pre p q` entered under `I p` and in phase
(`ClockInv 2048 p.ctl`), from which `PrefixPhase pre` follows by
`prefixPhase_of_scan_inv` under `ScanSupplyInv`.  No `ScanRealized`. -/
def PostRunF {σ : Type} (F : Frame σ) (I : State σ → Prop) : Prop :=
  ∀ {k mw : ℕ} {ts pre : List Bool} {p q : State σ} (v : SearchVM) (as : List Bool),
    ScanTrace F 2048 ts pre p q → I p → ClockInv 2048 p.ctl →
    v.search.mode = Mode.run → v.search.span = ofNat mw → v.lower = ofNat k →
    8 * max k 1 ≤ mw → Canonical v.search.debt →
    DpSafeStage v as → PacedL 2048 0 (pre ++ as) → RunEntriesS as v

/-- `PostRunF` is weaker than `PostRunPh`: the frame is dropped and the phase
clause is derived from the scan leg. -/
theorem postRunF_of_postRunPh {σ : Type} {F : Frame σ} {I : State σ → Prop}
    (hsup : ScanSupplyInv F 2048 I) (h : PostRunPh) : PostRunF F I :=
  fun {_ _ _ _ _ _} v as hsc hp hclk hm _ _ _ _ hsafe hpaced =>
    h v as _ hm hsafe (prefixPhase_of_scan_inv hsup hsc hp hclk.1 hclk.2) hpaced

#print axioms postRunF_of_postRunPh

/-! ## 2. The round trip from the framed datum -/

section RoundTrip

variable {σ : Type} {F : Frame σ} {I : State σ → Prop}

/-- **NAMED — the `.run → .wait → .double → prepare` round trip from the framed
`.run` entry.**  Hypotheses that are neither the frame of `PostRunF` nor the
leg traces themselves:

* `hsc` — **machine fact (clock).**  The reachable prefix up to the `.double`
  entry, `pre ++ (rs ++ a1 :: (ws ++ [false]))`, is one scan leg from `p`.
  Relative to `PostRunF`'s datum over `pre` alone, this is the extension of the
  `ScanTrace` over the `.run` and `.wait` legs.
* `hs2 : searchStep cw false w1 u0` — **frame fact.**  The `.wait` exit tick is
  a background tick (as in `CloseoutPreload24.round_trip_entries`); a
  comparison on the exit tick would drive the zero debt negative.
* `hcan1`, `hcan0` — **frame fact.**  `Canonical` debt at the `.wait` exit and
  at the `.double` entry (no `Canonical` preservation lemma along `RunTrace` /
  `WaitTrace` is in the tree; `dec_canonical` would give it).

Everything else is derived: the `.wait` entry's span from `run_exit_frame`, the
`.double` entry's shape from `wait_exit_double`, `zero debt = true` at the
`.wait` exit from `wait_step_cases`, `debt = 0` from `wait_exit_debt_zero`,
the spent `.double` state from `double_spends`, and the balance from the
clock (`prefixPhase_of_scan_inv` → `pacedL_suffix_2047` → `eight_le_of_cal` →
`bal_of_paced_slack`). -/
theorem postRunF_round_trip {k mw : ℕ} {ts pre rs ws bs : List Bool} {a1 a3 : Bool}
    {cr cw : GalilScaffoldPlace.Place} {v t0 w0 w1 u0 : SearchVM} {p q : State σ}
    (hsup : ScanSupplyInv F 2048 I)
    (hm : v.search.mode = Mode.run) (hsp : v.search.span = ofNat mw)
    (hlow : v.lower = ofNat k) (hcal : 8 * max k 1 ≤ mw)
    (hrun : RunTrace rs v t0) (ht0 : t0.search.mode = Mode.run)
    (hs1 : searchStep cr a1 t0 w0) (hw0 : w0.search.mode = Mode.wait)
    (hwait : WaitTrace ws w0 w1) (hw1 : w1.search.mode = Mode.wait)
    (hcan1 : Canonical w1.search.debt)
    (hs2 : searchStep cw false w1 u0) (hne : u0.search.mode ≠ Mode.wait)
    (hcan0 : Canonical u0.search.debt)
    (hsc : ScanTrace F 2048 ts (pre ++ (rs ++ a1 :: (ws ++ [false]))) p q)
    (hp : I p) (hclk : ClockInv 2048 p.ctl)
    (hblen : bs.length = mw)
    (hpaced : PacedL 2048 0 ((pre ++ (rs ++ a1 :: (ws ++ [false]))) ++ (bs ++ [a3]))) :
    ∃ t1 : SearchVM, DoubleTrace bs u0 t1 ∧ t1.search.mode = Mode.double ∧
      positive t1.search.work = false ∧ t1.search.span = ofNat (2 * mw) ∧
      t1.lower = ofNat k ∧
      ∀ (c' : GalilScaffoldPlace.Place) (t' : SearchVM), searchStep c' a3 t1 t' →
        PrepAt k (2 * mw) t' ∧ StageInvD k (2 * mw) t' ∧ t'.walker = c' ∧
          8 * max k 1 ≤ 2 * mw := by
  have hne0 : w0.search.mode ≠ Mode.run := by rw [hw0]; decide
  obtain ⟨hl0, -, -, -, -, hwsp, -⟩ := run_exit_frame hm hsp hlow hrun ht0 hs1 hne0
  have hsp0 : w0.search.span = ofNat mw := hwsp hw0
  obtain ⟨hdm, hdw, hdsp, hq0, hdl, -⟩ := wait_exit_double hsp0 hwait hw1 hs2 hne
  have hz : zero w1.search.debt = true := by
    obtain ⟨-, -, -, hc | hc⟩ := wait_step_cases hw1 hs2
    · exact absurd hc.2.1 hne
    · exact hc.1
  have hd0 : value u0.search.debt = 0 := wait_exit_debt_zero hw1 hz hcan1 hs2
  obtain ⟨t1, hr, h1m, h1w, h1s, h1l, -, -⟩ := double_spends cw hdm hdw hdsp hblen
  have h1l' : t1.lower = ofNat k := by rw [h1l, hdl, hl0]
  refine ⟨t1, hr, h1m, h1w, h1s, h1l', ?_⟩
  intro c' t' hs3
  have hph := prefixPhase_of_scan_inv hsup hsc hp hclk.1 hclk.2
  have hpa : PacedL 2048 2047 (bs ++ [a3]) := pacedL_suffix_2047 hpaced hph
  have hmw : 8 ≤ mw := eight_le_of_cal hcal
  have hcal' : 8 * max k 1 ≤ 2 * mw := by omega
  have hbal := bal_of_paced_slack hcal' hblen hmw le_rfl hpa
  obtain ⟨hprep, hinv⟩ :=
    stageInvD_of_double_exit hr hd0 hq0 hcan0 h1m h1w h1s h1l' hblen hbal hs3
  have hc1 := double_exit_canonical hr h1m h1w hcan0
  obtain ⟨-, hwk, -⟩ := prepAt_of_double_exit h1m h1w h1s h1l' hc1 hs3
  exact ⟨hprep, hinv, hwk, hcal'⟩

#print axioms postRunF_round_trip

end RoundTrip

/-!
## 3. What is left

Closed here: `PostRunF` (§1), `postRunF_of_postRunPh`, and
`postRunF_round_trip` (§2) — the round trip to the next stage's `prepare`
entry with `PrepAt ∧ StageInvD` and the doubled calibration, the balance
derived from the clock, no `ScanRealized`.

**`postRunC_of_postRunF` does not go through** and is not stated: `PostRunC`'s
`.run` state carries no frame (`span`, `lower`, calibration, `Canonical`), so
`PostRunF` cannot be instantiated from `PostRunC`'s premises — the
implication goes the other way (`postRunF_of_postRunPh`).

**NOT closed — the continuation from `prepare` to the next `.run` entry.**
`CloseoutPreload28.runEntriesS_of_stageInvD` walks the preparation with
`StagePrep2`, whose pacing clause is `PacedL 2048 0` measured *from the
`prepare` entry*; at the exit of `postRunF_round_trip` the stream is a suffix
of the paced stream from `p`, so only slack `≤ 2047` is available
(`CloseoutPreload30` §4 (2)).  Either `StagePrep2` / `dpDemand` /
`dpSafe_of_stagePrepD` are restated at slack `2047` (`prepLen k + 2047` in the
advance budget), or the induction carries the `ScanTrace` of the entire stream
and the clock phase at `prepare`.  Second, the next `.run` entry needs the
`PostRunF` datum again: the `ScanTrace` over `pre ++ legs ++ prep prefix` —
the same machine fact as `hsc`, one stage further.  Third, `RunEntriesS`
through the `.wait` / `.double` legs themselves (every `RunEntryS` there is
vacuous by `wait_not_to_run` and the `.double` phase never enters `.run`) is
not assembled here.

**無条件 PAL ∈ PEG は未完.**
-/

end PalPeg.CloseoutPreload31
