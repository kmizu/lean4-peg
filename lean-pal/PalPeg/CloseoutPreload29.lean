import PalPeg.CloseoutPreload28

/-!
# `PostRunD` — the round trip with the `.double` clause in Scala's shape

`CloseoutPreload26.PostRunC'` packages `CloseoutPreload24.PostRunC` together with
the round-trip `.double` clause of `round_trip_entries`, whose numeric input is
the radius-shaped exit debt — false for every credit divisor
(`CloseoutPreload27.double_len_false_any`).  `CloseoutPreload28` replaced that
clause by `runEntriesS_of_double_exitD`, whose only numeric input is the balance
`hbal : 4 * dpDemand k (2 * mw) + 4 * count ≤ mw`, and discharged `hbal` from
pacing (`bal_of_paced_slack`, any clock phase, `8 ≤ mw`).

* §1 `PostRunD F I` — `PostRunC ∧` the `.double` clause of
  `runEntriesS_of_double_exitD`, with `hbal` replaced by the machine datum that
  produces it: the `.double` leg `bs ++ [a]` is the suffix of a stream
  `pre ++ (bs ++ [a])` paced from phase `0`, whose prefix `pre` is a scan leg of
  the controller (`CloseoutPreload21.ScanTrace`) run under
  `CloseoutPreload23.ScanSupplyInv` and entered at `CloseoutPreload22.ClockInv 2048`.
  This is exactly the shape `CloseoutPreload24.runP_exit_debt_at_exit_scan` uses
  to normalise a suffix's slack to `2047`.
  The calibration is stated in the **window-doubling** form `8 * max k 1 ≤ mw`
  (the span *entering* `.double`), not the doubled form `8 * max k 1 ≤ 2 * mw`
  of `round_trip_entries`: in `ScaffoldSearch.scala` `stepGrow` writes eight
  span cells per unit of `max(r, 1)` (`CloseoutPreload8.BeginAt.work`), so the
  first window is `8 * max k 1` (`stageWindow1 k - 1`), and `doubleWindow`
  only doubles; hence every `.double` entry has `mw ≥ 8 * max k 1 ≥ 8`.  The
  small-window phase `8 ≤ mw` of `bal_of_paced_slack` is therefore *derived*,
  not assumed.
* §2 `postRunD_of_machine` — `PostRunD F I` from `ScanSupplyInv`,
  `ScanRealized`, and `PostRunC`: the prefix's phase
  (`prefixPhase_of_scan_inv`) rounds the leg's slack to `2047`
  (`pacedL_suffix_2047`), `bal_of_paced_slack` yields `hbal`, and
  `runEntriesS_of_double_exitD` closes the clause.
  `postRunD_of_machine_galil` is the instance on `galilFrameS` with the supply
  invariant `bigPack2_scanSupply`.
* §3 the residues.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPreload29

open PalPeg PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController
open PalPeg.GalilScaffoldSearchFinish (Mode)
open PalPeg.GalilScaffoldCounter (Canonical value ofNat positive)
open PalPeg.CloseoutReadyStage (PacedL RunEntriesS)
open PalPeg.CloseoutDebtAudit (dpEvents)
open PalPeg.CloseoutPreload6 (prepLen)
open PalPeg.CloseoutPreload8 (DepthAt)
open PalPeg.CloseoutPreload17 (DoubleTrace)
open PalPeg.CloseoutPreload18 (pacedL_suffix_2047)
open PalPeg.CloseoutPreload21 (ScanTrace)
open PalPeg.CloseoutPreload22 (ClockInv)
open PalPeg.CloseoutPreload23 (ScanSupplyInv prefixPhase_of_scan_inv bigPack2_scanSupply)
open PalPeg.CloseoutPreload24 (PostRunC ScanRealized)
open PalPeg.CloseoutPreload28 (dpDemand runEntriesS_of_double_exitD bal_of_paced_slack)
open PalPeg.GalilRunSkeleton (PofC)
open PalPeg.CloseoutPackRun3 (BigPack2 H_extraTick BigResid5)

/-! ## 1. The contract -/

/-- **NAMED — `PostRunC` with the round-trip `.double` clause in `StageInvD`'s
shape.**  Compare `CloseoutPreload26.PostRunC'`: the radius `Rad`, the carry,
the discharge clause `3 * (Rad + carry) ≤ 5 * k`, and the radius-shaped exit
debt are gone.  In their place is the machine datum for the leg's pacing — the
leg `bs ++ [a]` (of length exactly `mw`, plus the dispatch tick) is the suffix
of a stream paced from phase `0` whose prefix `pre` is a scan leg of the
controller entered in phase — and the calibration `8 * max k 1 ≤ mw` on the
span entering `.double` (the window-doubling invariant, see the header). -/
def PostRunD {σ : Type} (F : Frame σ) (I : State σ → Prop) : Prop :=
  PostRunC ∧
  ∀ {c' : GalilScaffoldPlace.Place} {k D mw : ℕ} {a : Bool} {bs pre ts : List Bool}
    {v t t' : SearchVM} {p q : State σ},
    DoubleTrace bs v t → value v.search.debt = 0 → v.search.quarter = 0 →
    Canonical v.search.debt →
    t.search.mode = Mode.double → positive t.search.work = false →
    t.search.span = ofNat (2 * mw) → t.lower = ofNat k → bs.length = mw →
    8 * max k 1 ≤ mw →
    ScanTrace F 2048 ts pre p q → I p → ClockInv 2048 p.ctl →
    PacedL 2048 0 (pre ++ (bs ++ [a])) →
    searchStep c' a t t' → DepthAt t' D → D ≤ prepLen k →
    ∀ as : List Bool,
      D + dpEvents (2 * mw + 1) ≤ as.length → PacedL 2048 0 as → RunEntriesS as t'

/-! ## 2. The contract from the machine facts -/

/-- The small-window phase is not a residue: the span entering `.double` is at
least the first window `8 * max k 1`. -/
theorem eight_le_of_cal {k mw : ℕ} (hcal : 8 * max k 1 ≤ mw) : 8 ≤ mw := by
  have := le_max_right k 1
  omega

#print axioms eight_le_of_cal

/-- **NAMED — `PostRunD` from the machine facts.**  Hypotheses: the supply
invariant `hsup`, the realizability clause `H_scanRealized`, and the post-run
contract `H_postRunC` (`postRunC_of_machine` is not in the tree).  Everything
else is derived: the prefix's phase (`prefixPhase_of_scan_inv`) rounds the
`.double` leg's slack to `2047` (`pacedL_suffix_2047`), `8 ≤ mw` comes from the
window-doubling calibration (`eight_le_of_cal`), `bal_of_paced_slack` yields
`hbal`, and `runEntriesS_of_double_exitD` closes the clause. -/
theorem postRunD_of_machine {σ : Type} {F : Frame σ} {I : State σ → Prop}
    (hsup : ScanSupplyInv F 2048 I)
    (H_scanRealized : ScanRealized F I)
    (H_postRunC : PostRunC) :
    PostRunD F I := by
  refine ⟨H_postRunC, ?_⟩
  intro c' k D mw a bs pre ts v t t' p q hr hv0 hq hvc htm htw hts htl hblen hcal
    hsc hp hclk hpaced hs hdep hD
  have hph := prefixPhase_of_scan_inv hsup hsc hp hclk.1 hclk.2
  have hpa : PacedL 2048 2047 (bs ++ [a]) := pacedL_suffix_2047 hpaced hph
  have hmw : 8 ≤ mw := eight_le_of_cal hcal
  have hcal' : 8 * max k 1 ≤ 2 * mw := by omega
  have hbal : 4 * dpDemand k (2 * mw) + 4 * (bs ++ [a]).count true ≤ mw :=
    bal_of_paced_slack hcal' hblen hmw le_rfl hpa
  exact runEntriesS_of_double_exitD hr hv0 hq hvc htm htw hts htl hblen hbal hs hdep hD
    hsup H_scanRealized H_postRunC

#print axioms postRunD_of_machine

/-- **The instance on `galilFrameS`.**  The supply invariant is
`CloseoutPreload23.bigPack2_scanSupply` (under its own residues `BigResid5` /
`H_extraTick` / the per-tick side condition); the realizability clause on the
concrete frame is the named residue `H_scanRealized`. -/
theorem postRunD_of_machine_galil
    (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9) {w : List (Fin 2)}
    (hr : BigResid5 centre place entry q first w)
    (het : H_extraTick centre place entry q first w)
    (hside : ∀ x y : State GalilVM,
      Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y →
      BigPack2 centre place entry q first w x →
      PalPeg.GalilScaffoldChainInputSupply.SoundScanNR w y ∧
        PalPeg.GalilScaffoldChainInputSupply.CentreLive y.ctl y.vm)
    (H_scanRealized : ScanRealized (galilFrameS (PofC centre place entry w) q first)
      (BigPack2 centre place entry q first w))
    (H_postRunC : PostRunC) :
    PostRunD (galilFrameS (PofC centre place entry w) q first)
      (BigPack2 centre place entry q first w) :=
  postRunD_of_machine (bigPack2_scanSupply centre place entry q first hr het hside)
    H_scanRealized H_postRunC

#print axioms postRunD_of_machine_galil

/-!
## 3. What is left

Closed here: `PostRunD` (§1) — the round trip's `.double` clause in Scala's
shape, with the leg's pacing carried as the controller datum and the
calibration in window-doubling form; `postRunD_of_machine` (§2) — the clause
from `ScanSupplyInv`, `ScanRealized`, `PostRunC`; the small-window phase
`8 ≤ mw` is derived (`eight_le_of_cal`), not assumed.

**Hypotheses of `postRunD_of_machine`:** `hsup : ScanSupplyInv F 2048 I`,
`H_scanRealized : ScanRealized F I`, `H_postRunC : PostRunC`.  On
`galilFrameS` (`postRunD_of_machine_galil`) `hsup` is discharged by
`bigPack2_scanSupply` at the price of its residues `BigResid5` / `H_extraTick` /
`hside`.

**NOT closed:** `ScanRealized` on `galilFrameS` (the `GalilScaffoldTopScan`
leg construction, `CloseoutPreload21` §4); `postRunC_of_machine : PostRunC`
(the induction over all later `.run` entries — `PostRunD` is its step, not its
proof); and the placement of the `.double` leg inside a scan leg's stream
(that the events `pre ++ (bs ++ [a])` of a `.wait` → `.double` round trip really
are the tail of one paced `ScanTrace`), which `PostRunD` carries as a premise.

**無条件 PAL ∈ PEG は未完.**
-/

end PalPeg.CloseoutPreload29
