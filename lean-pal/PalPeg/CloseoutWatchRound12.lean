import PalPeg.CloseoutWatchRound11
import PalPeg.CloseoutWatchRun
import PalPeg.GalilCostedFound
import PalPeg.GalilLiveCentreSegs

/-!
# Round 12: the crossing case at the *watch* phase

`CloseoutWatchRound11` closes the post-shift round against the checkpoint cell
`2m-1` in two branches, and names one gap: when the crossing segment belongs to
the **watch phase** (`s.chain = ChainVM.watch w`, a `ScanSeg`), the report route
`CloseoutReportCase.reachAtC3_of_crossF` does not apply, because it consumes a
`SegReachedW`, i.e. a `WatchSegE` out of an *idle*-chain landing.

This file supplies the live-chain crossing route.  Two observations make it
possible without the idle machinery.

* `GalilReportPrefix.ReportPointAt` does **not** mention the chain: it asks for
  `replaying = false`, a scan invariant, `MInv`, and the right head exactly on
  `2m-1`.  All four are transported along a `ScanSeg`
  (`GalilLiveCentreSegs.minv_scanSeg`, `GalilScaffoldTopCentre.scanSeg_center`,
  `CloseoutWatchRound11.scanSeg_right_position`).
* A `ScanSeg` is indexed by its number of comparisons, and each comparison moves
  the right head by exactly one, so — unlike the `WatchSegE` route, which splits
  the event list at the `(2m-2)`-th `true` and then performs the report
  comparison by hand — the crossing state here is simply the landing of the
  `j`-th comparison, `j = 2m-1 - position r.right`.  It lands *on* the cell, and
  it lands right after a comparison, so its clock is fresh and its output is
  refreshed by the segment's own `refresh` field.

## What is proved here (unconditionally, no `sorry`)

1. `scanSeg_split` — the `split_nth_true` analogue for `ScanSeg`, on the index
   instead of on an event list: a segment of `n` comparisons splits at any
   `j ≤ n` into a `j`-segment and an `(n-j)`-segment, and for `j ≥ 1` the split
   point is the landing of a comparison, hence `replaying = false`,
   `clock = delay`, and `Refreshed`.
2. `reportPointAt_of_scanSeg` — the crossing state of a `ScanSeg` is a prefix
   report point for `m`.
3. `reachAtC3_of_crossW` — **the live-chain `reachAtC3_of_crossF`.**  From a
   cycle entry `InvLPS` below the cell and a watch-phase `ScanSeg` that crosses
   it, the cycle routes to `.report`.  The run and its cost come from
   `GalilCostedFound.watchSeg_costed` on `watchSeg_of_scanSeg` (the split point
   has `clock = 2048`, so no pending ticks remain and the tick count of the run
   equals the tick count of the costed run, which is what `ReachAtC3` demands);
   the continuation is the empty run at the crossing state itself, exactly as in
   `GalilInvPlus3.reachAtC3_of_target_match`, since `2m-1 ≤ 2(m+1)-1`.

## Still open, NAMED with exact type

* **One fact**, the hypothesis `hland` of `reachAtC3_of_crossW`:

  ```
  ∀ (c1 : Control) (s1 : GalilVM),
    ScanSeg (PofC centre place entry raw) q first 2048 (2*m-1 - position r.right) c r c1 s1 →
    position s1.right = 2*m-1 → c1.replaying = false → c1.clock = 2048 →
    InvLPS (PofC centre place entry raw) q first raw c1 s1
  ```

  i.e. the landing of the crossing comparison is again a cycle-entry state.
  `GalilInvPlus3.reachAtC3_of_target_match` proves its idle-chain analogue with
  `GalilReplaySegment.inv_after_replay`, whose `chain` field is
  `ChainVM.idle`; at a watch landing `afterCompare_chain` gives
  `ChainVM.watch w'` (the `hwatch` field of `ScanSeg.match`), so that route is
  unavailable and the watch remainder must supply it instead
  (`CloseoutWatchRun.watchRun_of_distance` to a terminal live landing, then the
  `landed` / `broke` exits of `CloseoutContracts.FoundExit`).  Nothing in the
  tree currently carries a live-chain landing back into `InvLPS`.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

namespace PalPeg.CloseoutWatchRound12

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton PalPeg.GalilOracleDischarge PalPeg.GalilOracleLocal
open PalPeg.GalilCheckpoints PalPeg.GalilInvPlus PalPeg.GalilInvPlus2
open PalPeg.GalilOracleMC PalPeg.GalilOracleMC2 PalPeg.GalilOracleMC3
open PalPeg.GalilLeafPos PalPeg.GalilLeafReport PalPeg.GalilOneFallback
open PalPeg.GalilInvPlus3 PalPeg.GalilTraceCost PalPeg.GalilCostedFound
open PalPeg.CloseoutWatchRound11

/-! ## 1. Splitting a scan segment at a comparison -/

/-- **Derived — the `ScanSeg` analogue of `split_nth_true`.**  A scan segment of
`n` comparisons splits at any `j ≤ n`; for `j ≥ 1` the split point is the
landing of the `j`-th comparison, so its control is fresh (`clock = delay`, not
replaying) and its output has just been refreshed. -/
theorem scanSeg_split (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) {n : ℕ}
    {c c' : Control} {s t : GalilVM} (h : ScanSeg P q first delay n c s c' t) :
    ∀ j : ℕ, j ≤ n → ∃ (c1 : Control) (s1 : GalilVM),
      ScanSeg P q first delay j c s c1 s1 ∧ ScanSeg P q first delay (n - j) c1 s1 c' t ∧
      (1 ≤ j → Refreshed P q first ⟨c1, s1⟩ ∧ c1.replaying = false ∧ c1.clock = delay) := by
  induction h with
  | stop c s =>
    intro j hj
    obtain rfl : j = 0 := Nat.le_zero.mp hj
    exact ⟨c, s, .stop _ _, .stop _ _, by omega⟩
  | wait c s s' hm hr hn hb rest ih =>
    intro j hj
    match j with
    | 0 => exact ⟨c, s, .stop _ _, by simpa using ScanSeg.wait c s s' hm hr hn hb rest, by omega⟩
    | (j+1) =>
      obtain ⟨c1, s1, h1, h2, href⟩ := ih (j+1) hj
      exact ⟨c1, s1, .wait c s s' hm hr hn hb h1, h2, href⟩
  | count c s s' hm hr ha hc hb rest ih =>
    intro j hj
    match j with
    | 0 => exact ⟨c, s, .stop _ _, by simpa using ScanSeg.count c s s' hm hr ha hc hb rest, by omega⟩
    | (j+1) =>
      obtain ⟨c1, s1, h1, h2, href⟩ := ih (j+1) hj
      exact ⟨c1, s1, .count c s s' hm hr ha hc hb h1, h2, href⟩
  | @«match» c s vs vq o n c' t hm hr ha hc hcont hcmp hmt hwatch hq ho rest ih =>
    intro j hj
    match j with
    | 0 =>
      exact ⟨c, s, .stop _ _,
        by simpa using ScanSeg.match c s vs vq o hm hr ha hc hcont hcmp hmt hwatch hq ho rest,
        by omega⟩
    | 1 =>
      refine ⟨_, _, .match c s vs vq o hm hr ha hc hcont hcmp hmt hwatch hq ho (.stop _ _),
        by simpa using rest, fun _ => ⟨⟨c.output, ho⟩, rfl, rfl⟩⟩
    | (j+2) =>
      obtain ⟨c1, s1, h1, h2, href⟩ := ih (j+1) (by omega)
      refine ⟨c1, s1, .match c s vs vq o hm hr ha hc hcont hcmp hmt hwatch hq ho h1, ?_,
        fun _ => href (by omega)⟩
      simpa using h2

/-! ## 2. The crossing state is a prefix report point -/

/-- **Derived.**  A scan segment of `j` comparisons out of a state whose right
head is `2m-1-j` lands on the checkpoint cell, and that landing is a prefix
report point — `ReportPointAt` never inspects the chain, so the live-chain case
is no different from the idle one. -/
theorem reportPointAt_of_scanSeg (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9)
    (m j : ℕ) (hm1 : 1 ≤ m) (hmle : m ≤ raw.length)
    {c c1 : Control} {r s1 : GalilVM} {R0 : ℕ}
    (h : ScanSeg P q first 2048 j c r c1 s1)
    (hi0 : ScanInvariant raw (position r.center) R0 r.left r.right)
    (hM : MInv raw c r) (hnr : c1.replaying = false)
    (hpos : position r.right + j = 2 * m - 1) :
    PalPeg.GalilReportPrefix.ReportPointAt raw m ⟨c1, s1⟩ := by
  obtain ⟨hi1, hp1⟩ := scanSeg_right_position raw P q first 2048 h hi0
  have hcen : s1.center = r.center := scanSeg_center P q first 2048 h
  refine ⟨hnr, ⟨R0 + j, by rw [hcen]; exact hi1⟩, minv_scanSeg raw P q first 2048 h R0 hi0 hM,
    by rw [hp1]; omega, hm1, hmle⟩

/-! ## 3. The report route of the watch phase -/

/-- **Derived — the live-chain `CloseoutReportCase.reachAtC3_of_crossF`.**  A
watch-phase scan segment out of the cycle entry that crosses the checkpoint cell
routes the cycle to `.report`.  The only hypothesis that is not a fact of the
segment is `hland`, the landing invariant at the crossing comparison, named in
the header. -/
theorem reachAtC3_of_crossW (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m n : ℕ) (hm1 : 1 ≤ m) (hmle : m ≤ raw.length)
    {c c' : Control} {r t : GalilVM}
    (hIN : InvLPS (PofC centre place entry raw) q first raw c r)
    (hseg : ScanSeg (PofC centre place entry raw) q first 2048 n c r c' t)
    (hlt : position r.right < 2 * m - 1) (hge : 2 * m - 1 ≤ position t.right)
    (hland : ∀ (c1 : Control) (s1 : GalilVM),
      ScanSeg (PofC centre place entry raw) q first 2048 (2 * m - 1 - position r.right) c r c1 s1 →
      position s1.right = 2 * m - 1 → c1.replaying = false → c1.clock = 2048 →
      InvLPS (PofC centre place entry raw) q first raw c1 s1) :
    ReachAtC3 (PofC centre place entry raw) q first raw m c r := by
  classical
  set P : Shared := PofC centre place entry raw with hP
  have hI : InvL raw c r := invLPS_invL hIN
  obtain ⟨-, -, -, -, hMC, R0, hi0, -, -, -⟩ := invS_entry_data hI.1
  obtain ⟨-, hc0, ho0⟩ := invL_entry hI
  -- the comparison count of the crossing prefix
  set j : ℕ := 2 * m - 1 - position r.right with hj
  have hposT : position t.right = position r.right + n :=
    (scanSeg_right_position raw P q first 2048 hseg hi0).2
  have hjn : j ≤ n := by omega
  have hj1 : 1 ≤ j := by omega
  obtain ⟨c1, s1, h1, -, href⟩ := scanSeg_split P q first 2048 hseg j hjn
  obtain ⟨hfr, hnr1, hclk1⟩ := href hj1
  obtain ⟨hi1, hp1⟩ := scanSeg_right_position raw P q first 2048 h1 hi0
  have hpos1 : position s1.right = 2 * m - 1 := by rw [hp1]; omega
  have hrp : PalPeg.GalilReportPrefix.ReportPointAt raw m ⟨c1, s1⟩ :=
    reportPointAt_of_scanSeg raw P q first m j hm1 hmle h1 hi0 hMC hnr1 (by omega)
  -- the run and its cost: the split point has a fresh clock, so nothing is pending
  obtain ⟨k, kc, p', r', L, hstOut, hk, hp', hcr, -, -, -⟩ :=
    watchSeg_costed raw P rfl rfl q first 2048 le_rfl
      (watchSeg_of_scanSeg P q first 2048 h1) (position r.center) R0 0 hi0 ho0 (by omega)
      (by omega)
  have hkc : kc = k := by omega
  have hst : StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨c1, s1⟩ :=
    stepsAll_mono (fun st h0 _ _ => h0) hstOut
  have hIS : InvLPS P q first raw c1 s1 := hland c1 s1 h1 hpos1 hnr1 hclk1
  exact ⟨⟨c1, s1⟩, k, L, hst, by rw [← hkc] at *; exact hcr, hrp, hfr,
    fun _ => ⟨c1, s1, 0, [], .zero _ (stepsAll_last hst), costedRun_nil s1, hIS, by omega⟩⟩

#print axioms scanSeg_split
#print axioms reportPointAt_of_scanSeg
#print axioms reachAtC3_of_crossW

end PalPeg.CloseoutWatchRound12
