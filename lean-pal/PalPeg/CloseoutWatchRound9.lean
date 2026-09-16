import PalPeg.CloseoutWatchRound7
import PalPeg.GalilSegmentConstruct3

/-!
# Round 9: the round run for a **shift-done** chain (`ScanSeg` / `Rounds`)

`CloseoutWatchRun.watchRun_of_distance` and `CloseoutWatchRound.roundStepC_of_data`
build the watch phase as a fuel-driven run of `WatchSeg` rounds.  After a centre
shift (`Tick.shift_one`×h, `shift_done`, `GalilScaffoldTopShift*`) the machine is
back in scan mode with a *shifted* chain, and the run that must be built there is
not a `WatchSeg` run but a `ScanSeg` / `Rounds` run: this is exactly the shape
`CloseoutWatchRound7.ShiftRoundData` asks for
(`Rounds … mm … ∧ ScanSeg … n c' s' c3 s3` with a terminal break).

`ScanSeg` differs from `WatchSeg` in two premises at a matched comparison —
`singlePositive s.cycle = false` (the cycle is not at its end) and
`∃ w', vs.chain = .watch w'` (the chain is still watching after the tick) — and it
*counts* the comparisons.  Nothing in the tree constructs a `ScanSeg`:
`GalilSegmentConstruct3.rounds_construct_of_measure` iterates rounds but takes each
round, segment included, as an oracle.  This file supplies the missing segment
construction and re-runs the `CloseoutWatchRun` fuel argument on it.

## What is proved here (unconditionally, no `sorry`)

1. `scanSeg_countdown` — the idle interval of a post-shift round as a `ScanSeg`
   of length `0` (`ScanSeg.count` does not count).  Same proof shape as
   `CloseoutWatchRound.watchSeg_countdown`, with the chain-shape invariant `Q`
   carried so the landing stays a watch landing.
2. `scanSeg_matchStep` — one matched comparison at clock `1`, mid-cycle, as a
   `ScanSeg` of length `1`: the compare relation, the `matched` flag, the watch
   shape of the tick and the output refresh are all *constructed*.
3. `ScanRoundStepC`, `scanRun_construct`, `scanRun_of_distance` — the fuel
   induction in its `ScanSeg` form: the same `CloseoutWatchRun.roundFuel h`
   (the chain's catch-up `distance` against the shift guard's threshold `4*h`),
   so a post-shift landing reaches a terminal landing in at most `4*h + 1`
   comparisons, all of it one `ScanSeg`.
4. `SegEndS`, `scanRoundStepC_of_data` — the per-comparison step, from **the same
   data** `CloseoutWatchRound.RoundDataC` that the watch-phase round uses.  The
   extra `ScanSeg` premise `∃ w', vs.chain = .watch w'` is *derived* from that
   data (`afterCompare_chain` plus the post-state `LiveScanWatch`), so the
   shift-done run costs no new obligation.  The terminal is the disjunction
   "fuel spent / input exhausted / cycle end / mismatch" — the four ways a
   post-shift segment can stop.
5. `segRun_terminal` — items 1–4 composed: from a live post-shift landing, one
   `ScanSeg` reaches a `SegEndS` landing.
6. `roundOne_of_segRun` — **one `Rounds` step built from the run.**  At a landing
   whose segment run ends in a *mismatch* that carries the shift data
   (`ShiftAtMismatchC`), `GalilSegmentConstruct3.roundStep_of_shiftRun` turns the
   constructed `ScanSeg` into `Rounds … 1`.  Hence `rounds_construct_of_measure`
   applies, which is `roundsRun_to_end`: `Rounds … mm` to a `RoundEnd`, whose
   `BreakEnd` branch is precisely the terminal `ScanSeg` + breaking comparison of
   `ShiftRoundData`.

## Still open, NAMED with exact types

* `CloseoutWatchRound.RoundDataC P q first h c s` — unchanged from round 8's
  ledger: the matched chain tick, the search effect and the fuel drop.
* `ShiftAtMismatchC P q first h c1 s1` (below) — the shift block at the
  mismatching landing: `singlePositive s1.cycle = true`, the chain's prediction
  agreeing with the right symbol, `Canonical s1.length`, the guard, the
  `beginShiftVM h w` entry with `CopyIdle`, and a `ShiftRun` of exactly `h` units.
  All of it is input-dependent (whether the outer symbols agree is input data),
  so it stays an obligation about the run.
* The remaining distance to `CloseoutWatchRound7.ShiftRoundData` is **one fact**:
  the terminal right-head bound `position (afterCompare s3 vs3 vq3).right ≤ 2*m - 1`
  is not produced by any run-level lemma (`rounds_break` gives the three counter
  conjuncts `negative w3'.margin = false`, `positive …last = true`,
  `zero w3'.lag = true` from `Entry`, but no head bound).

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutWatchRound9

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.CloseoutContracts
open PalPeg.GalilRunSkeleton
open PalPeg.GalilTickFun (ChainReady)
open PalPeg.CloseoutWatchRun (LiveScanWatch roundFuel)
open PalPeg.CloseoutWatchRound (RoundDataC WatchClosedC)

/-! ## 1. The idle interval of a post-shift round -/

/-- **Derived.**  The countdown to the next comparison as a `ScanSeg`.  `ScanSeg`
counts only comparisons, so the whole interval has length `0`.  `Q` is any
chain-shape invariant closed under `ChainTick false`; at "is a `watch`" it keeps
the landing a watch landing. -/
theorem scanSeg_countdown (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    (hready : PalPeg.GalilReplayChainSeg.ChainTickable)
    (Q : ChainVM → Prop)
    (hQ : ∀ (x z : ChainVM), Q x → ChainTick false x z → Q z) :
    ∀ (k : ℕ) (c : Control) (s : GalilVM), c.mode = .scan → c.replaying = false →
      c.clock = k + 1 → canRight s.right → s.chain ≠ ChainVM.idle → ChainReady s.chain →
      Q s.chain →
      ∃ s' : GalilVM,
        ScanSeg P q first delay 0 c s {c with clock := 1} s' ∧
        s'.chain ≠ ChainVM.idle ∧ ChainReady s'.chain ∧ Q s'.chain ∧
        s'.left = s.left ∧ s'.right = s.right ∧ s'.center = s.center ∧
        s'.replay = s.replay := by
  intro k
  induction k with
  | zero =>
    intro c s hm hr hclk hav hne hrd hQs
    have h1 : c.clock = 1 := by omega
    have hc : ({c with clock := 1} : Control) = c := by rw [← h1]
    refine ⟨s, ?_, hne, hrd, hQs, rfl, rfl, rfl, rfl⟩
    rw [hc]; exact .stop _ _
  | succ k ih =>
    intro c s hm hr hclk hav hne hrd hQs
    obtain ⟨z, htz, hrz⟩ := hready false s.chain hrd hne
    have hstep : ChainStep s.chain z := by
      obtain ⟨y, hst, hy⟩ := htz
      have hzy : z = y := hy
      rw [hzy]; exact hst
    obtain ⟨s1, hb, hch1, hl1, hr1, hC1, hrep1⟩ :=
      PalPeg.GalilReplayChainSeg.active_background_exists P q first s hne hstep
    have hne1 : s1.chain ≠ ChainVM.idle := by
      rw [hch1]; exact chainTick_ne_idle' htz hne
    have hrd1 : ChainReady s1.chain := by rw [hch1]; exact hrz
    have hQ1 : Q s1.chain := by rw [hch1]; exact hQ _ _ hQs htz
    have hav1 : canRight s1.right := by rw [hr1]; exact hav
    obtain ⟨s2, hseg, hne2, hrd2, hQ2, hl2, hr2, hC2, hrep2⟩ :=
      ih {c with clock := c.clock - 1} s1 hm hr (by simp; omega) hav1 hne1 hrd1 hQ1
    refine ⟨s2, ?_, hne2, hrd2, hQ2, by rw [hl2, hl1], by rw [hr2, hr1],
      by rw [hC2, hC1], by rw [hrep2, hrep1]⟩
    have hseg' : ScanSeg P q first delay 0 {c with clock := c.clock - 1} s1
        {c with clock := 1} s2 := by
      have he : ({({c with clock := c.clock - 1} : Control) with clock := 1} : Control)
          = {c with clock := 1} := rfl
      rw [he] at hseg; exact hseg
    exact .count c s s1 hm hr hav (by omega) hb hseg'

/-! ## 2. The comparison, on a match, mid-cycle -/

/-- **Derived.**  One matched outer comparison at clock `1`, mid-cycle, with the
chain still watching after the tick: a `ScanSeg` of length `1`.  The compare
relation, the `matched` flag and the output refresh are constructed. -/
theorem scanSeg_matchStep (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    (c : Control) (s : GalilVM) (hm : c.mode = .scan) (hr : c.replaying = false)
    (hc1 : c.clock = 1) (hav : canRight s.right)
    (hcont : singlePositive s.cycle = false)
    (z : ChainVM) (htick : ChainTick true s.chain z)
    (hw : ∃ w' : GalilScaffoldChainWatch.State, z = ChainVM.watch w')
    (hmatch : read (left s.left) = read (right s.right))
    (vq : SearchVM) (hq : searchEffect P true s vq) :
    ∃ o : Bool,
      ScanSeg P q first delay 1 c s
        {c with clock := delay, output := o, replaying := false}
        (afterCompare s ⟨left s.left, right s.right, z⟩ vq) := by
  classical
  set vs : ScanVM := ⟨left s.left, right s.right, z⟩ with hvs
  have hcmp : (galilFrame P q first).compare s (scanLens.set s vs) := by
    refine ⟨⟨rfl, rfl, ?_⟩, ?_⟩
    · show ChainTick (decide (read (left s.left) = read (right s.right))) s.chain z
      rw [decide_eq_true hmatch]
      exact htick
    · rfl
  have hmt : (galilFrame P q first).matched (scanLens.set s vs) := hmatch
  set u : GalilVM := afterCompare s vs vq with hu
  refine ⟨if P.onLetter u then decide (P.leftFirst u) else c.output, ?_⟩
  have ho : refresh (galilFrame P q first) u c.output
      (if P.onLetter u then decide (P.leftFirst u) else c.output) := by
    refine ⟨fun hl => ?_, fun hl => ?_⟩
    · have hl' : P.onLetter u := hl
      show (if P.onLetter u then decide (P.leftFirst u) else c.output) = true ↔ P.leftFirst u
      rw [if_pos hl']; exact decide_eq_true_iff
    · have hl' : ¬ P.onLetter u := hl
      show (if P.onLetter u then decide (P.leftFirst u) else c.output) = c.output
      rw [if_neg hl']
  have hwatch : ∃ w' : GalilScaffoldChainWatch.State, vs.chain = ChainVM.watch w' := hw
  exact .match c s vs vq _ hm hr hav hc1 hcont hcmp hmt hwatch hq ho (.stop _ _)

/-! ## 3. The fuel induction, in `ScanSeg` form -/

/-- **NAMED (open), per instance.**  One post-shift comparison: at a live scan
landing, either the landing is terminal, or the machine performs a `ScanSeg`
reaching the next live scan landing with a strictly smaller measure.  This is the
`ScanSeg` analogue of `CloseoutWatchRun.RoundStepC`. -/
def ScanRoundStepC (P : Shared) (q : ℕ) (first : Fin 9) (meas : GalilVM → ℕ)
    (Term : Control → GalilVM → Prop) (c : Control) (s : GalilVM) : Prop :=
  Term c s ∨
    ∃ (n : ℕ) (c' : Control) (s' : GalilVM),
      ScanSeg P q first 2048 n c s c' s' ∧ LiveScanWatch c' s' ∧ meas s' < meas s

/-- **Derived — the post-shift segment as a run.**  From a live scan landing with
measure at most `n0`, the per-comparison contract reaches a terminal live landing
by a single `ScanSeg`.  Induction on the fuel; each comparison contributes one
`ScanSeg`, composed by `GalilSegmentConstruct3.scanSeg_append`. -/
theorem scanRun_construct (P : Shared) (q : ℕ) (first : Fin 9) (meas : GalilVM → ℕ)
    (Term : Control → GalilVM → Prop)
    (hstep : ∀ (c : Control) (s : GalilVM), LiveScanWatch c s →
      ScanRoundStepC P q first meas Term c s) :
    ∀ (n0 : ℕ) (c : Control) (s : GalilVM), meas s ≤ n0 → LiveScanWatch c s →
      ∃ (n : ℕ) (c' : Control) (s' : GalilVM),
        ScanSeg P q first 2048 n c s c' s' ∧ LiveScanWatch c' s' ∧ Term c' s' := by
  intro n0
  induction n0 with
  | zero =>
    intro c s hfuel hL
    rcases hstep c s hL with ht | ⟨n, c', s', hseg, hL', hlt⟩
    · exact ⟨0, c, s, .stop _ _, hL, ht⟩
    · omega
  | succ n0 ih =>
    intro c s hfuel hL
    rcases hstep c s hL with ht | ⟨n, c', s', hseg, hL', hlt⟩
    · exact ⟨0, c, s, .stop _ _, hL, ht⟩
    · obtain ⟨n', c'', s'', hseg2, hL'', ht⟩ := ih c' s' (by omega) hL'
      exact ⟨n + n', c'', s'', scanSeg_append P q first 2048 hseg hseg2, hL'', ht⟩

/-- **Derived.**  The post-shift segment with the concrete fuel: at most
`4*h + 1` comparisons, the same ledger as `CloseoutWatchRun.watchRun_of_distance`. -/
theorem scanRun_of_distance (P : Shared) (q : ℕ) (first : Fin 9) (h : ℕ)
    (Term : Control → GalilVM → Prop)
    (hstep : ∀ (c : Control) (s : GalilVM), LiveScanWatch c s →
      ScanRoundStepC P q first (roundFuel h) Term c s)
    (c : Control) (s : GalilVM) (hL : LiveScanWatch c s) :
    ∃ (n : ℕ) (c' : Control) (s' : GalilVM),
      ScanSeg P q first 2048 n c s c' s' ∧ LiveScanWatch c' s' ∧ Term c' s' := by
  refine scanRun_construct P q first (roundFuel h) Term hstep (4 * h + 1) c s ?_ hL
  cases hch : s.chain <;> simp [roundFuel, hch]

/-! ## 4. The per-comparison step, from the watch-phase data -/

/-- **The terminal landing of a post-shift segment.**  A live watch landing at
which one of the four exits fires: the fuel is spent (`distance` has reached the
shift guard's threshold `4*h`), the right head is exhausted, or the segment
reaches a clock-`1` landing at which the cycle ends (`singlePositive = true`, the
`Rounds.next` / break shape) or the outer symbols disagree (the mismatch that
starts the next shift). -/
def SegEndS (P : Shared) (q : ℕ) (first : Fin 9) (h : ℕ) (c : Control)
    (s : GalilVM) : Prop :=
  LiveScanWatch c s ∧
    (roundFuel h s = 0 ∨ ¬ canRight s.right ∨
      ∃ (n : ℕ) (c1 : Control) (s1 : GalilVM),
        ScanSeg P q first 2048 n c s c1 s1 ∧ c1.clock = 1 ∧ LiveScanWatch c1 s1 ∧
          s1.left = s.left ∧ s1.right = s.right ∧ ChainReady s1.chain ∧
          (singlePositive s1.cycle = true ∨
            read (left s1.left) ≠ read (right s1.right)))

/-- **Derived — one post-shift comparison, from the round-8 data.**  The extra
`ScanSeg` premise `∃ w', vs.chain = .watch w'` is *derived* from
`RoundDataC`'s post-state `LiveScanWatch` via
`GalilScaffoldTopRoundBreak.afterCompare_chain`, so the shift-done run needs no
obligation beyond the watch-phase one.  The `singlePositive` split is classical:
whether the cycle ends at this comparison is state data. -/
theorem scanRoundStepC_of_data (P : Shared) (q : ℕ) (first : Fin 9) (h : ℕ)
    (hready : PalPeg.GalilReplayChainSeg.ChainTickable)
    (hclosed : WatchClosedC)
    (hdata : ∀ (c : Control) (s : GalilVM), LiveScanWatch c s →
      RoundDataC P q first h c s)
    (c : Control) (s : GalilVM) (hL : LiveScanWatch c s) :
    ScanRoundStepC P q first (roundFuel h) (SegEndS P q first h) c s := by
  classical
  obtain ⟨hm, hr, hclk, w, hw⟩ := hL
  have hL' : LiveScanWatch c s := ⟨hm, hr, hclk, w, hw⟩
  obtain ⟨hav, hrd, hcmpdata⟩ := hdata c s hL'
  have hne : s.chain ≠ ChainVM.idle := by rw [hw]; intro h0; cases h0
  obtain ⟨k, hk⟩ : ∃ k, c.clock = k + 1 := ⟨c.clock - 1, by omega⟩
  obtain ⟨s1, hseg1, hne1, hrd1, hQ1, hl1, hr1, hC1, hrep1⟩ :=
    scanSeg_countdown P q first 2048 hready
      (fun x => ∃ w' : GalilScaffoldChainWatch.State, x = ChainVM.watch w')
      (fun x z hx ht => by
        obtain ⟨w', rfl⟩ := hx
        exact hclosed w' z ht)
      k c s hm hr hk hav hne hrd ⟨w, hw⟩
  have hL1 : LiveScanWatch {c with clock := 1} s1 := ⟨hm, hr, by simp, hQ1⟩
  by_cases hcyc : singlePositive s1.cycle = true
  · exact Or.inl ⟨hL', Or.inr (Or.inr ⟨0, {c with clock := 1}, s1, hseg1, rfl, hL1,
      hl1, hr1, hrd1, Or.inl hcyc⟩)⟩
  by_cases hmm : read (left s1.left) = read (right s1.right)
  · -- a mid-cycle match: one full comparison
    obtain ⟨z, vq, htick, hq, hpost⟩ := hcmpdata s1 hl1 hr1 hL1 hrd1 hmm
    have hcont : singlePositive s1.cycle = false := by
      cases hsp : singlePositive s1.cycle
      · rfl
      · exact absurd hsp hcyc
    have hwz : ∃ w' : GalilScaffoldChainWatch.State, z = ChainVM.watch w' := by
      obtain ⟨-, -, -, w', hw'⟩ := (hpost false).1
      rw [PalPeg.GalilScaffoldChainInputSupply.afterCompare_chain] at hw'
      exact ⟨w', hw'⟩
    obtain ⟨o, hseg2⟩ :=
      scanSeg_matchStep P q first 2048 ({c with clock := 1} : Control) s1 hm hr rfl
        (by rw [hr1]; exact hav) hcont z htick hwz hmm vq hq
    refine Or.inr ⟨0 + 1, {c with clock := 2048, output := o, replaying := false},
      afterCompare s1 ⟨left s1.left, right s1.right, z⟩ vq, ?_, (hpost o).1, (hpost o).2⟩
    revert hseg2
    cases c with
    | mk mode clock output replaying odd pair =>
      intro hseg2
      exact scanSeg_append P q first 2048 hseg1 hseg2
  · -- a mismatch: the landing is terminal, and the next shift starts here
    exact Or.inl ⟨hL', Or.inr (Or.inr ⟨0, {c with clock := 1}, s1, hseg1, rfl, hL1,
      hl1, hr1, hrd1, Or.inr hmm⟩)⟩

/-- **Derived — the post-shift segment, end to end.**  From a live landing, at
most `4*h+1` comparisons reach a `SegEndS` landing, all of it one `ScanSeg`. -/
theorem segRun_terminal (P : Shared) (q : ℕ) (first : Fin 9) (h : ℕ)
    (hready : PalPeg.GalilReplayChainSeg.ChainTickable)
    (hclosed : WatchClosedC)
    (hdata : ∀ (c : Control) (s : GalilVM), LiveScanWatch c s →
      RoundDataC P q first h c s)
    (c : Control) (s : GalilVM) (hL : LiveScanWatch c s) :
    ∃ (n : ℕ) (c' : Control) (s' : GalilVM),
      ScanSeg P q first 2048 n c s c' s' ∧ LiveScanWatch c' s' ∧
        SegEndS P q first h c' s' :=
  scanRun_of_distance P q first h (SegEndS P q first h)
    (scanRoundStepC_of_data P q first h hready hclosed hdata) c s hL

/-! ## 5. One `Rounds` step built from the segment run -/

/-- **NAMED (open), per landing.**  The shift block at a mismatching clock-`1`
landing: the cycle ends there, the chain's prediction agrees with the right
symbol, the length is canonical, the guard holds, the shift entry is
`beginShiftVM h w` with `CopyIdle`, and the head/counter state performs a
`ShiftRun` of exactly `h` units.  These are the premises of `Rounds.next` that
`GalilSegmentConstruct3.roundStep_of_shiftRun` does not supply itself. -/
def ShiftAtMismatchC (P : Shared) (q : ℕ) (first : Fin 9) (h : ℕ) (c1 : Control)
    (s1 : GalilVM) : Prop :=
  ∀ w : GalilScaffoldChainWatch.State, s1.chain = ChainVM.watch w →
    read (left s1.left) ≠ read (right s1.right) →
    ∃ (vs : ScanVM) (vq : SearchVM) (s2 : GalilVM) (t' : ShiftState),
      (galilFrame P q first).compare s1 (scanLens.set s1 vs) ∧
      ¬ (galilFrame P q first).matched (scanLens.set s1 vs) ∧
      searchEffect P false s1 vq ∧
      singlePositive s1.cycle = true ∧
      read (right s1.right) =
        GalilScaffoldChainConsume.symbol w.machine.control.period.focus ∧
      Canonical s1.length ∧
      P.shiftGuard (afterMismatch s1 vs vq) ∧
      P.beginShift (afterMismatch s1 vs vq) s2 ∧
      beginShiftVM h w (afterMismatch s1 vs vq) s2 ∧ CopyIdle s2 ∧
      ShiftRun ⟨s1.center, left s1.left, ofNat h, inc s1.radius, inc (inc s1.length)⟩ h t'

/-- **Derived — one complete round.**  The segment run of §4 reaches a terminal
landing; on the *mismatch* exit the shift block turns it into a `Rounds … 1` step
by `roundStep_of_shiftRun`.  The other three exits (fuel spent, input exhausted,
cycle end) are returned unchanged: they are the terminals of the whole rounds
phase, not of one round. -/
theorem roundOne_of_segRun (P : Shared) (q : ℕ) (first : Fin 9) (h : ℕ)
    (hready : PalPeg.GalilReplayChainSeg.ChainTickable)
    (hclosed : WatchClosedC)
    (hdata : ∀ (c : Control) (s : GalilVM), LiveScanWatch c s →
      RoundDataC P q first h c s)
    (hshift : ∀ (c1 : Control) (s1 : GalilVM), LiveScanWatch c1 s1 →
      ShiftAtMismatchC P q first h c1 s1)
    (c : Control) (s : GalilVM) (hL : LiveScanWatch c s) :
    (∃ (n : ℕ) (c' : Control) (s' : GalilVM),
        ScanSeg P q first 2048 n c s c' s' ∧ LiveScanWatch c' s' ∧
        (roundFuel h s' = 0 ∨ ¬ canRight s'.right ∨
          ∃ (n1 : ℕ) (c1 : Control) (s1 : GalilVM),
            ScanSeg P q first 2048 n1 c' s' c1 s1 ∧ c1.clock = 1 ∧
              LiveScanWatch c1 s1 ∧ singlePositive s1.cycle = true)) ∨
      ∃ (c' : Control) (s' : GalilVM),
        Rounds P q first 2048 h 1 c s c' s' := by
  classical
  obtain ⟨n, cT, sT, hseg, hLT, hterm⟩ := segRun_terminal P q first h hready hclosed hdata c s hL
  obtain ⟨-, hexit⟩ := hterm
  rcases hexit with h0 | hnr | ⟨n1, c1, s1, hseg1, hc1, hL1, hl1, hr1, hrd1, hcase⟩
  · exact Or.inl ⟨n, cT, sT, hseg, hLT, Or.inl h0⟩
  · exact Or.inl ⟨n, cT, sT, hseg, hLT, Or.inr (Or.inl hnr)⟩
  rcases hcase with hcyc | hmm
  · exact Or.inl ⟨n, cT, sT, hseg, hLT, Or.inr (Or.inr ⟨n1, c1, s1, hseg1, hc1, hL1, hcyc⟩)⟩
  -- the mismatch: one round
  obtain ⟨hm1, hr1', hclk1, w1, hw1⟩ := hL1
  obtain ⟨vs, vq, s2, t', hcmp, hmis, hq, hend, hpred, hlen, hg, hb, hs2, hi2, hrun⟩ :=
    hshift c1 s1 ⟨hm1, hr1', hclk1, w1, hw1⟩ w1 hw1 hmm
  have hav1 : canRight s1.right := by
    obtain ⟨hav, -, -⟩ := hdata cT sT hLT
    rw [hr1]; exact hav
  obtain ⟨v, cycle, o, hround⟩ :=
    roundStep_of_shiftRun P q first 2048 h
      (scanSeg_append P q first 2048 hseg hseg1)
      hm1 hr1' hc1 w1 hw1 hav1 vs vq hcmp hmis hq hend hpred hlen hg s2 hb hs2 hi2 hrun
  exact Or.inr ⟨_, _, hround⟩

#print axioms scanSeg_countdown
#print axioms scanSeg_matchStep
#print axioms scanRun_construct
#print axioms scanRun_of_distance
#print axioms scanRoundStepC_of_data
#print axioms segRun_terminal
#print axioms roundOne_of_segRun

end PalPeg.CloseoutWatchRound9
