import PalPeg.CloseoutWatchRun
import PalPeg.GalilReplayChainSeg

/-!
# One watch round, constructed

`PalPeg.CloseoutWatchRun` reduced the whole watch phase to a per-round
contract

```
CloseoutWatchRun.RoundStepC P q first (CloseoutWatchRun.roundFuel h) Term c s
  : Prop
  := Term c s ∨ ∃ c' s', WatchSeg P q first 2048 c s c' s' ∧
       CloseoutWatchRun.LiveScanWatch c' s' ∧
       CloseoutWatchRun.roundFuel h s' < CloseoutWatchRun.roundFuel h s
```

and left it NAMED.  This file *builds* the round and thereby discharges
`RoundStepC` at a concrete terminal predicate `TerminalC`, from data that is
genuinely local: a tickable chain, one comparison's search effect, and the
fuel bookkeeping of a matched outer tick.

## What is proved here (unconditionally, no `sorry`)

1. `watchSeg_countdown` — the idle interval of a round.  In scan mode with
   `replaying = false`, an available right head and a **live** chain, the clock
   counts down from `k+1` to `1` by `WatchSeg.count`, the chain ticking on
   `false` all the way (`GalilReplayChainSeg.active_background_exists` supplies
   the background, `ChainTickable` the tick).  A chain-shape invariant `Q`
   closed under `ChainTick false` is carried along, which is how the landing
   stays a *watch* landing.  (`CloseoutReadyStage.watchSegE_constructS` is the
   chain-**idle** analogue; `GalilReplayChainSeg.replayChainSeg_countdown` the
   `replaying = true` one.  The scan-mode live-chain countdown had none.)
2. `watchSeg_matchStep` — the comparison itself, on a match: one
   `WatchSeg.match` from clock `1` to the reloaded control, with the compare
   relation and the refreshed output built here (no hypothesis about them).
3. `roundStepC_of_data` — **the round**: countdown, then `by_cases` on the
   outer comparison `read (left s₁.left) = read (right s₁.right)`, which is
   input data and therefore decided classically: a match gives the full round
   (`watchSeg_append` from `CloseoutWatchRun`), a mismatch makes the landing
   terminal via `BreakEndC` (the `ChainMatched.breaks` side).  Together with
   `CloseoutWatchRun.watchRun_of_distance` this turns the watch phase into a
   single `WatchSeg` ending at a `TerminalC` landing (`watchRun_terminal`).
4. `watchRouteLPraw_of_run` — the wiring to `CloseoutWatchPhase3`: modulo the
   NAMED terminal-to-tails contract, the cycle has the disjunctive raw route.

## Still open, NAMED with exact types

* `RoundDataC P q first h c s` (below) — the per-round comparison data at the
  clock-`1` landing: a `ChainTick true`, a `searchEffect P true`, and the fuel
  bookkeeping `CloseoutWatchRun.roundFuel h (afterCompare …) <
  CloseoutWatchRun.roundFuel h s` (i.e. `distance` really rises by one at a
  matched outer tick — `GalilCatchUpDistance.distance_at_terminal`), together
  with the watch shape of the landing.
* `WatchClosedC : Prop` — `∀ (w : GalilScaffoldChainWatch.State) (z : ChainVM),
  ChainTick false (ChainVM.watch w) z → ∃ w', z = ChainVM.watch w'`: a
  background tick of a watching chain keeps it watching.
* `PrepInvC Prep` — `∀ c s, CloseoutWatchRun.LiveScanWatch c s → Prep c s`: the
  preparation data (`es.count true` accumulated over the rounds, the DP
  `Candidate`, the `freshWatch` lag shape) survives a round.  This is the
  round-indexed generalisation of `GalilNoShiftStage.fresh_break_ledger`.
* `TerminalTailsC …` — the terminal landing is one of the two tails
  (`CloseoutWatchPhase2.ShiftTailC` via `shiftGuardVM` and `Tick.scan_shift`,
  `CloseoutWatchPhase3.NoShiftTailC0` via the break ledger).

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutWatchRound

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.CloseoutContracts
open PalPeg.GalilRunSkeleton
open PalPeg.GalilTickFun (ChainReady)
open PalPeg.CloseoutWatchRun (LiveScanWatch RoundStepC roundFuel watchSeg_append)
open PalPeg.CloseoutWatchPhase2 (ShiftTailC)
open PalPeg.CloseoutWatchPhase3 (NoShiftTailC0 WatchRouteLPraw)

/-! ## 1. The idle interval of a round -/

/-- **Derived.**  The countdown to the next comparison in *scan* mode with a
live chain.  `Q` is any chain-shape invariant closed under `ChainTick false`;
instantiated at "is a `watch`" it keeps the landing a watch landing. -/
theorem watchSeg_countdown (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    (hready : PalPeg.GalilReplayChainSeg.ChainTickable)
    (Q : ChainVM → Prop)
    (hQ : ∀ (x z : ChainVM), Q x → ChainTick false x z → Q z) :
    ∀ (k : ℕ) (c : Control) (s : GalilVM), c.mode = .scan → c.replaying = false →
      c.clock = k + 1 → canRight s.right → s.chain ≠ ChainVM.idle → ChainReady s.chain →
      Q s.chain →
      ∃ s' : GalilVM,
        WatchSeg P q first delay c s {c with clock := 1} s' ∧
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
    have hseg' : WatchSeg P q first delay {c with clock := c.clock - 1} s1
        {c with clock := 1} s2 := by
      have he : ({({c with clock := c.clock - 1} : Control) with clock := 1} : Control)
          = {c with clock := 1} := rfl
      rw [he] at hseg; exact hseg
    exact .count c s s1 hm hr hav (by omega) hb hseg'

/-! ## 2. The comparison, on a match -/

/-- **Derived.**  One matched outer comparison at clock `1` with a live chain:
the compare relation and the output refresh are *constructed*, not assumed. -/
theorem watchSeg_matchStep (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    (c : Control) (s : GalilVM) (hm : c.mode = .scan) (hr : c.replaying = false)
    (hc1 : c.clock = 1) (hav : canRight s.right) (hne : s.chain ≠ ChainVM.idle)
    (z : ChainVM) (htick : ChainTick true s.chain z)
    (hmatch : read (left s.left) = read (right s.right))
    (vq : SearchVM) (hq : searchEffect P true s vq) :
    ∃ o : Bool,
      WatchSeg P q first delay c s
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
  exact .match c s vs vq _ hm hr hav hc1 hne hcmp hmt hq ho (.stop _ _)

/-! ## 3. The terminal predicate and the round -/

/-- A round that ends in a **break**: the idle interval runs to clock `1` and
the outer comparison there disagrees, so the chain's `ChainTick` is the
`ChainMatched.breaks` side and the watch phase is over. -/
def BreakEndC (P : Shared) (q : ℕ) (first : Fin 9) (c : Control) (s : GalilVM) : Prop :=
  ∃ (c1 : Control) (s1 : GalilVM),
    WatchSeg P q first 2048 c s c1 s1 ∧ c1.clock = 1 ∧ LiveScanWatch c1 s1 ∧
      read (left s1.left) ≠ read (right s1.right)

/-- **The terminal landing of the watch phase.**  A live watch landing carrying
the preparation data `Prep` (the accumulated `es.count true`, the DP candidate,
the `freshWatch` lag shape) at which one of the four exits fires: the fuel is
spent (`distance` has reached `4*h`, the shift guard's threshold), the shift
guard itself holds, the right head is exhausted, or the round breaks. -/
def TerminalC (P : Shared) (q : ℕ) (first : Fin 9) (h : ℕ)
    (Prep : Control → GalilVM → Prop) (c : Control) (s : GalilVM) : Prop :=
  LiveScanWatch c s ∧ Prep c s ∧
    (roundFuel h s = 0 ∨ shiftGuardVM s ∨ ¬ canRight s.right ∨ BreakEndC P q first c s)

/-- **NAMED (open).**  A background tick of a watching chain keeps it watching. -/
def WatchClosedC : Prop :=
  ∀ (w : GalilScaffoldChainWatch.State) (z : ChainVM),
    ChainTick false (ChainVM.watch w) z → ∃ w' : GalilScaffoldChainWatch.State,
      z = ChainVM.watch w'

/-- **NAMED (open), per landing.**  The comparison data of one round, at the
clock-`1` landing `s1` reached from `s`: a matched chain tick, the search
effect, and the fuel bookkeeping (`distance` rises by one, so `roundFuel`
falls). -/
def RoundDataC (P : Shared) (q : ℕ) (first : Fin 9) (h : ℕ) (c : Control)
    (s : GalilVM) : Prop :=
  canRight s.right ∧ ChainReady s.chain ∧
    ∀ s1 : GalilVM, s1.left = s.left → s1.right = s.right →
      LiveScanWatch {c with clock := 1} s1 → ChainReady s1.chain →
      read (left s1.left) = read (right s1.right) →
      ∃ (z : ChainVM) (vq : SearchVM),
        ChainTick true s1.chain z ∧ searchEffect P true s1 vq ∧
        ∀ o : Bool,
          LiveScanWatch {c with clock := 2048, output := o, replaying := false}
              (afterCompare s1 ⟨left s1.left, right s1.right, z⟩ vq) ∧
            roundFuel h (afterCompare s1 ⟨left s1.left, right s1.right, z⟩ vq)
              < roundFuel h s

/-- **NAMED (open).**  The preparation data holds at every live landing — the
round-indexed generalisation of `GalilNoShiftStage.fresh_break_ledger`. -/
def PrepInvC (Prep : Control → GalilVM → Prop) : Prop :=
  ∀ (c : Control) (s : GalilVM), LiveScanWatch c s → Prep c s

/-- **Derived — one watch round.**  At a live watch landing, either the landing
is terminal, or the machine performs exactly one round (idle interval plus a
matched comparison) to a live watch landing with strictly less fuel.  This is
`CloseoutWatchRun.RoundStepC`, so `CloseoutWatchRun.watchRun_of_distance`
applies. -/
theorem roundStepC_of_data (P : Shared) (q : ℕ) (first : Fin 9) (h : ℕ)
    (Prep : Control → GalilVM → Prop)
    (hready : PalPeg.GalilReplayChainSeg.ChainTickable)
    (hclosed : WatchClosedC) (hprep : PrepInvC Prep)
    (hdata : ∀ (c : Control) (s : GalilVM), LiveScanWatch c s →
      RoundDataC P q first h c s)
    (c : Control) (s : GalilVM) (hL : LiveScanWatch c s) :
    RoundStepC P q first (roundFuel h) (TerminalC P q first h Prep) c s := by
  classical
  obtain ⟨hm, hr, hclk, w, hw⟩ := hL
  have hL' : LiveScanWatch c s := ⟨hm, hr, hclk, w, hw⟩
  obtain ⟨hav, hrd, hcmpdata⟩ := hdata c s hL'
  have hne : s.chain ≠ ChainVM.idle := by rw [hw]; intro h0; cases h0
  -- the idle interval
  obtain ⟨k, hk⟩ : ∃ k, c.clock = k + 1 := ⟨c.clock - 1, by omega⟩
  obtain ⟨s1, hseg1, hne1, hrd1, hQ1, hl1, hr1, hC1, hrep1⟩ :=
    watchSeg_countdown P q first 2048 hready
      (fun x => ∃ w' : GalilScaffoldChainWatch.State, x = ChainVM.watch w')
      (fun x z hx ht => by
        obtain ⟨w', rfl⟩ := hx
        exact hclosed w' z ht)
      k c s hm hr hk hav hne hrd ⟨w, hw⟩
  have hL1 : LiveScanWatch {c with clock := 1} s1 := ⟨hm, hr, by simp, hQ1⟩
  by_cases hmm : read (left s1.left) = read (right s1.right)
  · -- match: the full round
    obtain ⟨z, vq, htick, hq, hpost⟩ := hcmpdata s1 hl1 hr1 hL1 hrd1 hmm
    obtain ⟨o, hseg2⟩ :=
      watchSeg_matchStep P q first 2048 ({c with clock := 1} : Control) s1 hm hr rfl
        (by rw [hr1]; exact hav) hne1 z htick hmm vq hq
    refine Or.inr ⟨{c with clock := 2048, output := o, replaying := false},
      afterCompare s1 ⟨left s1.left, right s1.right, z⟩ vq, ?_, (hpost o).1, (hpost o).2⟩
    revert hseg2
    cases c with
    | mk mode clock output replaying odd pair =>
      intro hseg2
      exact watchSeg_append hseg1 hseg2
  · -- mismatch: the landing is terminal on the break side
    exact Or.inl ⟨hL', hprep c s hL',
      Or.inr (Or.inr (Or.inr ⟨{c with clock := 1}, s1, hseg1, rfl, hL1, hmm⟩))⟩

/-- **Derived — the watch phase, end to end.**  From a live watch landing, at
most `4*h+1` rounds reach a terminal landing, all of it one `WatchSeg`. -/
theorem watchRun_terminal (P : Shared) (q : ℕ) (first : Fin 9) (h : ℕ)
    (Prep : Control → GalilVM → Prop)
    (hready : PalPeg.GalilReplayChainSeg.ChainTickable)
    (hclosed : WatchClosedC) (hprep : PrepInvC Prep)
    (hdata : ∀ (c : Control) (s : GalilVM), LiveScanWatch c s →
      RoundDataC P q first h c s)
    (c : Control) (s : GalilVM) (hL : LiveScanWatch c s) :
    ∃ (c' : Control) (s' : GalilVM),
      WatchSeg P q first 2048 c s c' s' ∧ LiveScanWatch c' s' ∧
        TerminalC P q first h Prep c' s' :=
  PalPeg.CloseoutWatchRun.watchRun_of_distance P q first h (TerminalC P q first h Prep)
    (roundStepC_of_data P q first h Prep hready hclosed hprep hdata) c s hL

/-! ## 4. Wiring to the tails -/

/-- **NAMED (open).**  The terminal landing is one of the two tails: the shift
tail (`shiftGuardVM` plus `Tick.scan_shift`) or the reduced break tail (the
break ledger of `GalilNoShiftStage.fresh_break_ledger`, generalised to keep
`es.count true` across rounds). -/
def TerminalTailsC (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m h : ℕ) (Prep : Control → GalilVM → Prop)
    (c0 : Control) (r : GalilVM) : Prop :=
  ∀ (cP : Control) (sP : GalilVM),
    TerminalC (PofC centre place entry raw) qq first h Prep cP sP →
      ShiftTailC centre place entry qq first raw m c0 r cP sP ∨
        NoShiftTailC0 centre place entry qq first raw m c0 r cP sP

/-- **Derived.**  Modulo the NAMED contracts, the watch phase run out of a
stage entry gives the disjunctive raw route of `CloseoutWatchPhase3`. -/
theorem watchRouteLPraw_of_run (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m h : ℕ) (Prep : Control → GalilVM → Prop)
    (hex : ∀ s, (PofC centre place entry raw).replayExhausted s = zero s.replay)
    (hready : PalPeg.GalilReplayChainSeg.ChainTickable)
    (hclosed : WatchClosedC) (hprep : PrepInvC Prep)
    (hdata : ∀ (c : Control) (s : GalilVM), LiveScanWatch c s →
      RoundDataC (PofC centre place entry raw) qq first h c s)
    {c0 : Control} {r : GalilVM}
    (hE : StageEntryC (PofC centre place entry raw) qq first raw c0 r)
    (htails : TerminalTailsC centre place entry qq first raw m h Prep c0 r)
    (hL : LiveScanWatch c0 r) :
    ∃ (cP : Control) (sP : GalilVM),
      WatchSeg (PofC centre place entry raw) qq first 2048 c0 r cP sP ∧
        WatchRouteLPraw (PofC centre place entry raw) qq first raw m c0 r cP sP := by
  obtain ⟨cP, sP, hseg, hLP, hterm⟩ :=
    watchRun_terminal (PofC centre place entry raw) qq first h Prep hready hclosed hprep
      hdata c0 r hL
  exact ⟨cP, sP, hseg,
    PalPeg.CloseoutWatchRun.watchRouteLPraw_of_terminal centre place entry qq first raw m
      hex hE (htails cP sP hterm)⟩

end PalPeg.CloseoutWatchRound

#print axioms PalPeg.CloseoutWatchRound.watchSeg_countdown
#print axioms PalPeg.CloseoutWatchRound.watchSeg_matchStep
#print axioms PalPeg.CloseoutWatchRound.roundStepC_of_data
#print axioms PalPeg.CloseoutWatchRound.watchRun_terminal
#print axioms PalPeg.CloseoutWatchRound.watchRouteLPraw_of_run
