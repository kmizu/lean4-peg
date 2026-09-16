import PalPeg.CloseoutWatchRound9
import PalPeg.CloseoutReportCase

/-!
# Round 11: the checkpoint split for the post-shift round

`CloseoutWatchRound9` builds the post-shift round run (`ScanSeg` + `Rounds`) out
of `ShiftAtMismatchC`, and closes with one named gap: the terminal right-head
bound `position (afterCompare s3 vs3 vq3).right ≤ 2*m - 1` of
`CloseoutWatchRound7.ShiftRoundData` is produced by no run-level lemma.

That bound is a *checkpoint* statement, and the checkpoint discipline already
exists one layer up: `GalilOracleMC4.cycleOracleMC2C_of_pieces''` splits the
cycle at the cell `2m-1` **before** the exit analysis, so that every leaf it
feeds (`hmismatch`, `hfound`, `hfoundBg`, `hlastMatch`, `hlastMismatch`) gets
`position t.right ≤ 2*m - 2`, while the two other branches go to the report
route (`reachAtC2_of_entry` when the segment *starts* at or past the cell,
`reachAtC2_of_cross` / `CloseoutReportCase.reachAtC3_of_crossF` when it crosses
it).  This file makes that same split explicit for the post-shift round, by
counting the right-head advance of a `ScanSeg`.

## What is proved here (unconditionally, no `sorry`)

1. `scanSeg_eventsC` — `scanSeg_heads` refined: the event list of a `ScanSeg` of
   length `n` has exactly `n` matched events (`es.count true = n`).  Waits and
   counts emit `false`, a comparison emits `true`.
2. `scanSeg_right_position` — hence the right head of a `ScanSeg` advances by
   exactly the number of comparisons: `position t.right = position s.right + n`,
   and the scan invariant lands at radius `k + n`.
3. `compareRight_position` — one matched comparison at the end moves the right
   head one further: `position (afterCompare s vs vq).right = position s.right + 1`
   for a `canRight` head represented in `raw`.
4. `terminalBound_of_scanSeg` — 1–3 combined: **the terminal right-head bound of
   `ShiftRoundData` is exactly the statement that the round's comparisons all
   happen strictly before the checkpoint**, i.e. it follows from
   `position s'.right + n ≤ 2*m - 2` on the round entry `s'` and its comparison
   count `n`.  This is the "手前で起きる" branch.
5. `reachAtC3_or_belowCheckpoint` — the "越える" branch, at the watch phase:
   for a found-route `SegReachedW c r c' t` entering strictly below the cell,
   either the segment stays below (`position t.right ≤ 2*m - 2`, which is what
   `cycleOracleMC2C_of_pieces''` hands its leaves) or it crosses the cell and the
   route is `.report`, by `CloseoutReportCase.reachAtC3_of_crossF`.
6. `watchPhase_or_report` — 4 and 5 composed over the link `position t.right =
   position s'.right` (the shift block does not move the right head — supplied as
   an argument, since `beginShiftVM`/`ShiftRun` are about the centre, copy and
   counter tapes): from a found-route watch phase and a post-shift round whose
   comparisons fit under the checkpoint, either the cycle routes to `.report`, or
   the terminal bound of `ShiftRoundData` holds.

## Still open, NAMED with exact type

* **One fact.**  The fit hypothesis `hfit : position s'.right + n ≤ 2*m - 2` of
  items 4 and 6 is *not* dischargeable inside this layer: when the post-shift
  round's own comparisons cross the cell `2m-1`, the crossing segment is a
  `ScanSeg`, and `CloseoutReportCase.reachAtC3_of_crossF` (like
  `GalilLeafReport.reachAtC2_of_cross`) accepts only a `SegReachedW`, i.e. a
  `WatchSegE` prefix out of an *idle*-chain landing; the missing fact is the
  transport `ScanSeg P q first 2048 n c' s' c3 s3 → position s'.right < 2*m-1 →
  2*m-1 ≤ position s3.right → SegReachedW centre place entry q first raw c' s' _ _`
  at the crossing comparison, which no lemma in the tree provides (a post-shift
  landing has `s'.chain = ChainVM.watch w`, so `SegReachedW.idle` fails outright).

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

namespace PalPeg.CloseoutWatchRound11

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton PalPeg.GalilOracleDischarge PalPeg.GalilOracleLocal
open PalPeg.GalilCheckpoints PalPeg.GalilInvPlus PalPeg.GalilInvPlus2
open PalPeg.GalilOracleMC PalPeg.GalilOracleMC2 PalPeg.GalilOracleMC3
open PalPeg.GalilLeafPos PalPeg.GalilLeafReport PalPeg.GalilOneFallback
open PalPeg.GalilInvPlus3 PalPeg.GalilReadyFuelUses PalPeg.GalilSegmentConstructB PalPeg.GalilLeafEnds

/-! ## 1. Counting the comparisons of a scan segment -/

/-- **Derived — `GalilLiveCentreSeg.scanSeg_heads` with the count.**  The scan
events of a `ScanSeg` of length `n` contain exactly `n` matched events: `wait`
and `count` run a background tick, which leaves both heads alone and emits
`false`; `match` emits `true` and steps the right head. -/
theorem scanSeg_eventsC (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) {n : ℕ}
    {c c' : Control} {s t : GalilVM} (h : ScanSeg P q first delay n c s c' t) :
    ∃ es : List Bool, es.count true = n ∧
      ∀ (raw : List (Fin 2)) (c0 r : ℕ),
        ScanEvents raw c0 r s.left s.right es t.left t.right := by
  induction h with
  | stop c s => exact ⟨[], rfl, fun _ _ _ => .stop _ _ _⟩
  | wait c s s' _ _ _ hb _ ih =>
    obtain ⟨es, hcnt, hsc⟩ := ih
    obtain ⟨hl, hr, _⟩ := background_frame P q first hb
    refine ⟨false :: es, by simpa using hcnt, fun raw c0 r => ?_⟩
    have hev := hsc raw c0 r
    rw [hl, hr] at hev
    exact .skip _ _ _ hev
  | count c s s' _ _ _ _ hb _ ih =>
    obtain ⟨es, hcnt, hsc⟩ := ih
    obtain ⟨hl, hr, _⟩ := background_frame P q first hb
    refine ⟨false :: es, by simpa using hcnt, fun raw c0 r => ?_⟩
    have hev := hsc raw c0 r
    rw [hl, hr] at hev
    exact .skip _ _ _ hev
  | «match» c s vs vq o _ _ ha _ _ hcmp hmt _ _ _ _ ih =>
    obtain ⟨es, hcnt, hsc⟩ := ih
    have hmatch : read (left s.left) = read (right s.right) := by
      obtain ⟨⟨hl0, hr0, _⟩, _⟩ := hcmp
      rw [scanLens.get_set] at hl0 hr0
      have hp := matched_parts P q first hmt
      rw [hl0, hr0] at hp; exact hp
    obtain ⟨hl, hr, _⟩ := compare_parts P q first hcmp hmatch
    refine ⟨true :: es, by simpa using hcnt, fun raw c0 r => ?_⟩
    have hev := hsc raw c0 (r+1)
    rw [afterCompare_left, afterCompare_right, hl, hr] at hev
    exact .matched _ _ _ ha hmatch hev

/-- **Derived — the right-head advance of a scan segment.**  Same shape as
`GalilOneFallback.watchSegE_right_position`, with the comparison count read off
the `ScanSeg` index instead of an event list. -/
theorem scanSeg_right_position (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9)
    (delay : ℕ) {n : ℕ} {c c' : Control} {s t : GalilVM}
    (h : ScanSeg P q first delay n c s c' t) {C k : ℕ}
    (hi : ScanInvariant raw C k s.left s.right) :
    ScanInvariant raw C (k + n) t.left t.right ∧
      position t.right = position s.right + n := by
  obtain ⟨es, hcnt, hsc⟩ := scanSeg_eventsC P q first delay h
  have hi' := scan_events_invariant (hsc raw C k) hi
  rw [hcnt] at hi'
  refine ⟨hi', ?_⟩
  rw [hi'.rightPos, hi.rightPos]; omega

/-! ## 2. The terminal comparison -/

/-- **Derived.**  A matched comparison at the end of the round moves the right
head exactly one place further. -/
theorem compareRight_position (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9)
    {C k : ℕ} (s : GalilVM) (vs : ScanVM) (vq : SearchVM) (hav : canRight s.right)
    (hcmp : (galilFrame P q first).compare s (scanLens.set s vs))
    (hmt : (galilFrame P q first).matched (scanLens.set s vs))
    (hi : ScanInvariant raw C k s.left s.right) :
    position (afterCompare s vs vq).right = position s.right + 1 := by
  have hmatch : read (left s.left) = read (right s.right) := by
    obtain ⟨⟨hl0, hr0, _⟩, _⟩ := hcmp
    rw [scanLens.get_set] at hl0 hr0
    have hp := matched_parts P q first hmt
    rw [hl0, hr0] at hp; exact hp
  obtain ⟨-, hr, -⟩ := compare_parts P q first hcmp hmatch
  rw [afterCompare_right, hr]
  exact right_position s.right hav
    (represented_position _ raw hi.rightRep hi.rightPresent).1

/-! ## 3. The "all comparisons before the checkpoint" branch -/

/-- **Derived — the terminal right-head bound of `ShiftRoundData`.**  It *is* the
statement that the whole post-shift round happens strictly below the checkpoint
cell `2m-1`: the entry place plus the round's comparison count plus the terminal
comparison must not pass `2m-1`. -/
theorem terminalBound_of_scanSeg (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9)
    (m n : ℕ) (hm1 : 1 ≤ m) {c' c3 : Control} {s' s3 : GalilVM} {C k : ℕ}
    (hseg : ScanSeg P q first 2048 n c' s' c3 s3)
    (hi : ScanInvariant raw C k s'.left s'.right)
    (hav3 : canRight s3.right)
    (hfit : position s'.right + n ≤ 2 * m - 2)
    (vs3 : ScanVM) (vq3 : SearchVM)
    (hcmp3 : (galilFrame P q first).compare s3 (scanLens.set s3 vs3))
    (hmt3 : (galilFrame P q first).matched (scanLens.set s3 vs3)) :
    position (afterCompare s3 vs3 vq3).right ≤ 2 * m - 1 := by
  obtain ⟨hi3, hpos3⟩ := scanSeg_right_position raw P q first 2048 hseg hi
  have h1 : position (afterCompare s3 vs3 vq3).right = position s3.right + 1 :=
    compareRight_position raw P q first s3 vs3 vq3 hav3 hcmp3 hmt3 hi3
  omega

/-! ## 4. The crossing branch, at the watch phase -/

/-- **Derived — the checkpoint split of `cycleOracleMC2C_of_pieces''`, isolated.**
For a found-route watch phase entering strictly below the checkpoint cell, either
it stays below — which is exactly the `position t.right ≤ 2m-2` that
`GalilOracleMC4.cycleOracleMC2C_of_pieces''` hands to each of its exit leaves —
or it crosses the cell, and then the cycle routes to `.report`, by
`CloseoutReportCase.reachAtC3_of_crossF`. -/
theorem reachAtC3_or_belowCheckpoint (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m : ℕ) (hm1 : 1 ≤ m) (hmle : m ≤ raw.length)
    {c c' : Control} {r t : GalilVM}
    (hIN : InvLPS (PofC centre place entry raw) q first raw c r)
    (hready : ReadyFuel (searchLens.get r) (headRank r.right * 2048 + c.clock)
      (headRank r.right))
    (hsW : SegReachedW centre place entry q first raw c r c' t)
    (hlt : position r.right < 2 * m - 1) :
    ReachAtC3 (PofC centre place entry raw) q first raw m c r ∨
      position t.right ≤ 2 * m - 2 := by
  rcases Nat.lt_or_ge (position t.right) (2 * m - 1) with h2 | h2
  · exact Or.inr (by omega)
  · exact Or.inl (PalPeg.CloseoutReportCase.reachAtC3_of_crossF centre place entry q first raw m
      hm1 hmle hIN hready hsW hlt h2)

/-! ## 5. The two branches composed -/

/-- **Derived — the checkpoint discipline for the post-shift round.**  From a
found-route watch phase entering below the cell and a post-shift round whose
entry place is the watch phase's landing place (`hlink`: the shift block moves
the centre, copy and counter tapes, not the right head), either the cycle routes
to `.report` (the watch phase crossed the cell), or the terminal right-head bound
of `CloseoutWatchRound7.ShiftRoundData` holds — provided the round's own
comparisons fit under the cell (`hfit`, the one open fact named in the header). -/
theorem watchPhase_or_report (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m n : ℕ) (hm1 : 1 ≤ m) (hmle : m ≤ raw.length)
    {c c'' : Control} {r t : GalilVM}
    (hIN : InvLPS (PofC centre place entry raw) q first raw c r)
    (hready : ReadyFuel (searchLens.get r) (headRank r.right * 2048 + c.clock)
      (headRank r.right))
    (hsW : SegReachedW centre place entry q first raw c r c'' t)
    (hlt : position r.right < 2 * m - 1)
    {c' c3 : Control} {s' s3 : GalilVM} {C k : ℕ}
    (hseg : ScanSeg (PofC centre place entry raw) q first 2048 n c' s' c3 s3)
    (hi : ScanInvariant raw C k s'.left s'.right)
    (hav3 : canRight s3.right)
    (hlink : position s'.right = position t.right)
    (hfit : position s'.right + n ≤ 2 * m - 2)
    (vs3 : ScanVM) (vq3 : SearchVM)
    (hcmp3 : (galilFrame (PofC centre place entry raw) q first).compare s3
      (scanLens.set s3 vs3))
    (hmt3 : (galilFrame (PofC centre place entry raw) q first).matched
      (scanLens.set s3 vs3)) :
    ReachAtC3 (PofC centre place entry raw) q first raw m c r ∨
      position (afterCompare s3 vs3 vq3).right ≤ 2 * m - 1 := by
  rcases reachAtC3_or_belowCheckpoint centre place entry q first raw m hm1 hmle hIN hready
    hsW hlt with hrep | hbelow
  · exact Or.inl hrep
  · exact Or.inr (terminalBound_of_scanSeg raw (PofC centre place entry raw) q first m n
      hm1 hseg hi hav3 hfit vs3 vq3 hcmp3 hmt3)

#print axioms scanSeg_eventsC
#print axioms scanSeg_right_position
#print axioms compareRight_position
#print axioms terminalBound_of_scanSeg
#print axioms reachAtC3_or_belowCheckpoint
#print axioms watchPhase_or_report

end PalPeg.CloseoutWatchRound11
