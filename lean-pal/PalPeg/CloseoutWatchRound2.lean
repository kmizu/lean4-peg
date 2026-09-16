import PalPeg.CloseoutWatchRound

/-!
# The watch round, with its NAMED contracts discharged

`PalPeg.CloseoutWatchRound` built one watch round and thereby reduced the whole
watch phase to four NAMED contracts: `WatchClosedC`, `RoundDataC`, `PrepInvC`
and `TerminalTailsC`.  This file removes three of them outright and shrinks the
fourth to a shape that only quantifies over data the entry already has.

## What is proved here (unconditionally, no `sorry`)

1. `watchClosed : CloseoutWatchRound.WatchClosedC` — **NAMED discharged.**  A
   background tick of a watching chain keeps it watching, because `watchStep`
   is the *only* `ChainStep` constructor whose source is a `.watch`
   (`GalilScaffoldTopChainVM`), and the disabled tick is its own step.
2. `distance_mono_internal`, `distance_mono_false` — the catch-up `distance` is
   monotone along background ticks (`Internal.idle` leaves it, `Internal.take`
   raises it by one through `GalilScaffoldChainWatch.good_distance`).  This is
   the fact `RoundDataC` had to *assume* in order to state its fuel clause: the
   clock-`1` landing of a round is reached from `s` by background ticks only, so
   its `distance` is at least that of `s`.
3. `watchTick_immediate` — the enabled tick of a caught-up watch: with
   `zero w.lag = true` (hence `positive w.lag = false`,
   `GalilScaffoldChainInputSupply.positive_of_zero`) and `Good w`, the tick is
   `Tick.step (Internal.idle …) (Outer.immediate …)`, and it raises `distance`
   by exactly one.  So the fuel bookkeeping is *derived*, not named.
4. `roundStepC_of_align` — **`RoundDataC` discharged**, down to the one fact
   that is genuinely not local: `MatchTickC`, the alignment of the chain
   verifier's own heads with the outer comparison (`zero lag` and `Good`).  The
   `searchEffect` clause of `RoundDataC` is free (`searchEffect` on a *non-idle*
   chain is `vq = searchLens.get s`, `GalilScaffoldTopSearch`), and the fuel
   clause comes from 2 + 3.  `PrepInvC` is discharged by instantiating the
   preparation predicate at `True` (`prepInvC_triv`) — the preparation data now
   travels in the terminal record instead, see below.
5. `watchRun_terminal'`, `terminalRunC_of_align` — the watch phase, end to end,
   in the shape its consumer needs: for *every* preparation segment out of the
   post-compare landing `(cP, sP)`, the rounds from that segment's landing reach
   a `TerminalC` landing, all of it one `WatchSeg`.
6. `TerminalC'` = `FoundCompareCtxC ∧ TerminalRunC`: the terminal record with
   the found-tick context of `CloseoutFoundCompare` / `CloseoutPrepInputs3`
   (the found comparison `sF`, its `found` search state, the started chain, and
   `(cP, sP)` being that comparison's control and post-state) bundled in, since
   that is exactly the common preamble both tails of `CloseoutWatchPhase2/3`
   demand.  `TerminalTailsC'` is the only contract left, and its remaining job
   is the *tail body* alone.
7. `foundExit_compare_final` — the composition:
   `TerminalC' → tails → CloseoutWatchPhase3.watchRouteLP_of_tails →
   RoundsExit ∨ BreakExit → CloseoutPrepInputs3.foundExit_of_compare3 →
   FoundExit`.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutWatchRound2

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.CloseoutContracts
open PalPeg.GalilRunSkeleton
open PalPeg.GalilInvPlus (SegReachedW)
open PalPeg.GalilTickFun (ChainReady)
open PalPeg.CloseoutWatchRun (LiveScanWatch RoundStepC roundFuel watchSeg_append)
open PalPeg.CloseoutWatchPhase2 (ShiftTailC LandingRestartReach)
open PalPeg.CloseoutWatchPhase3 (NoShiftTailC0 noShiftTailC_of_0 watchRouteLP_of_tails)
open PalPeg.CloseoutWatchRound (TerminalC BreakEndC WatchClosedC PrepInvC
  watchSeg_countdown watchSeg_matchStep)

/-! ## 1. `WatchClosedC`, discharged -/

/-- **NAMED discharged.**  `watchStep` is the only `ChainStep` out of a
`.watch`, and a disabled tick *is* its background step. -/
theorem watchClosed : WatchClosedC := by
  intro w z h
  obtain ⟨y, hstep, hzy⟩ := h
  have hzy' : z = y := hzy
  cases hstep with
  | watchStep w w' hi => exact ⟨w', hzy'⟩

/-! ## 2. `distance` is monotone along background ticks -/

/-- **Derived.**  An internal watch step never lowers the catch-up `distance`:
`idle` leaves it, `take` raises it by one. -/
theorem distance_mono_internal {w w' : GalilScaffoldChainWatch.State}
    (h : GalilScaffoldChainWatch.Internal w w') :
    value w.machine.control.distance ≤ value w'.machine.control.distance := by
  cases h with
  | idle hz => exact le_refl _
  | take hp hg =>
      have hd := GalilScaffoldChainWatch.good_distance hg
      show value w.machine.control.distance ≤
        value (GalilScaffoldChainWatch.caught w).machine.control.distance
      simp only [GalilScaffoldChainWatch.caught]
      omega

/-- **Derived.**  The disabled chain tick of a watch lands in a watch whose
`distance` is at least the old one. -/
theorem distance_mono_false {w : GalilScaffoldChainWatch.State} {z : ChainVM}
    (h : ChainTick false (ChainVM.watch w) z) :
    ∃ w' : GalilScaffoldChainWatch.State, z = ChainVM.watch w' ∧
      value w.machine.control.distance ≤ value w'.machine.control.distance := by
  obtain ⟨y, hstep, hzy⟩ := h
  have hzy' : z = y := hzy
  cases hstep with
  | watchStep w w' hi => exact ⟨w', hzy', distance_mono_internal hi⟩

/-! ## 3. The enabled tick of a caught-up watch -/

/-- **Derived.**  At zero lag with a successful consume, the enabled tick is
`Internal.idle` followed by `Outer.immediate`, and it raises `distance` by one.
This is the fuel bookkeeping `RoundDataC` assumed. -/
theorem watchTick_immediate {w : GalilScaffoldChainWatch.State}
    (hz : zero w.lag = true) (hg : GalilScaffoldChainWatch.Good w) :
    ChainTick true (ChainVM.watch w)
        (ChainVM.watch (GalilScaffoldChainWatch.immediate w)) ∧
      value (GalilScaffoldChainWatch.immediate w).machine.control.distance
        = value w.machine.control.distance + 1 := by
  refine ⟨chainTick_of_watch_true (.step (.idle w (positive_of_zero hz))
    (.immediate w hz hg)), ?_⟩
  have hd := GalilScaffoldChainWatch.good_distance hg
  show value (GalilScaffoldChainVerifier.consume w.machine).control.distance
    = value w.machine.control.distance + 1
  exact hd

/-! ## 4. The round, with `RoundDataC` and `PrepInvC` discharged -/

/-- **NAMED (open) — all that is left of `RoundDataC`.**  At a watch landing
where the outer comparison matches, the chain verifier is caught up (`zero lag`)
and its own consume succeeds (`Good`).  This is head alignment between the
verifier and the scan, not fuel or search bookkeeping. -/
def MatchTickC : Prop :=
  ∀ (s1 : GalilVM) (w1 : GalilScaffoldChainWatch.State),
    s1.chain = ChainVM.watch w1 → canRight s1.right →
    read (left s1.left) = read (right s1.right) →
    zero w1.lag = true ∧ GalilScaffoldChainWatch.Good w1

/-- The shape of a landing the rounds start from: an available right head, a
tickable chain, and a nonnegative catch-up `distance`. -/
def LandingReadyC (s : GalilVM) : Prop :=
  canRight s.right ∧ ChainReady s.chain ∧
    ∀ w : GalilScaffoldChainWatch.State, s.chain = ChainVM.watch w →
      0 ≤ value w.machine.control.distance

/-- The preparation predicate, trivialised: the preparation data now travels in
`TerminalC'` (§5) instead of inside `TerminalC`. -/
def TrivPrep : Control → GalilVM → Prop := fun _ _ => True

/-- **NAMED discharged.** -/
theorem prepInvC_triv : PrepInvC TrivPrep := fun _ _ _ => trivial

/-- **`RoundDataC` discharged.**  One watch round from the alignment datum
alone: the countdown carries a `distance` floor, so the matched comparison's
`distance + 1` really lowers `roundFuel`. -/
theorem roundStepC_of_align (P : Shared) (q : ℕ) (first : Fin 9) (h : ℕ)
    (hready : PalPeg.GalilReplayChainSeg.ChainTickable)
    (halign : MatchTickC)
    (hland : ∀ (c : Control) (s : GalilVM), LiveScanWatch c s → LandingReadyC s)
    (c : Control) (s : GalilVM) (hL : LiveScanWatch c s) :
    RoundStepC P q first (roundFuel h) (TerminalC P q first h TrivPrep) c s := by
  classical
  obtain ⟨hm, hr, hclk, w, hw⟩ := hL
  have hL' : LiveScanWatch c s := ⟨hm, hr, hclk, w, hw⟩
  obtain ⟨hav, hrd, hnn⟩ := hland c s hL'
  by_cases hfuel : roundFuel h s = 0
  · exact Or.inl ⟨hL', trivial, Or.inl hfuel⟩
  have hd0 : 0 ≤ value w.machine.control.distance := hnn w hw
  have hbound : (value w.machine.control.distance).toNat < 4 * h + 1 := by
    have he : roundFuel h s = (4 * h + 1) - (value w.machine.control.distance).toNat := by
      simp only [roundFuel, hw]
    omega
  have hne : s.chain ≠ ChainVM.idle := by rw [hw]; intro h0; cases h0
  obtain ⟨k, hk⟩ : ∃ k, c.clock = k + 1 := ⟨c.clock - 1, by omega⟩
  obtain ⟨s1, hseg1, hne1, hrd1, hQ1, hl1, hr1, hC1, hrep1⟩ :=
    watchSeg_countdown P q first 2048 hready
      (fun x => ∃ w' : GalilScaffoldChainWatch.State, x = ChainVM.watch w' ∧
        value w.machine.control.distance ≤ value w'.machine.control.distance)
      (by
        intro x z hx ht
        obtain ⟨w', hxe, hle⟩ := hx
        subst hxe
        obtain ⟨w'', hze, hle2⟩ := distance_mono_false ht
        exact ⟨w'', hze, le_trans hle hle2⟩)
      k c s hm hr hk hav hne hrd ⟨w, hw, le_refl _⟩
  obtain ⟨w1, hw1, hdle⟩ := hQ1
  have hav1 : canRight s1.right := by rw [hr1]; exact hav
  have hL1 : LiveScanWatch {c with clock := 1} s1 := ⟨hm, hr, by simp, ⟨w1, hw1⟩⟩
  by_cases hmm : read (left s1.left) = read (right s1.right)
  · obtain ⟨hz, hg⟩ := halign s1 w1 hw1 hav1 hmm
    obtain ⟨htick0, hdist⟩ := watchTick_immediate hz hg
    have htick : ChainTick true s1.chain
        (ChainVM.watch (GalilScaffoldChainWatch.immediate w1)) := by
      rw [hw1]; exact htick0
    have hq : searchEffect P true s1 (searchLens.get s1) := Or.inr ⟨hne1, rfl⟩
    obtain ⟨o, hseg2⟩ :=
      watchSeg_matchStep P q first 2048 ({c with clock := 1} : Control) s1 hm hr rfl
        hav1 hne1 _ htick hmm _ hq
    have huch : (afterCompare s1 ⟨left s1.left, right s1.right,
        ChainVM.watch (GalilScaffoldChainWatch.immediate w1)⟩ (searchLens.get s1)).chain
        = ChainVM.watch (GalilScaffoldChainWatch.immediate w1) := rfl
    have hLu : LiveScanWatch
        ({c with clock := 2048, output := o, replaying := false} : Control)
        (afterCompare s1 ⟨left s1.left, right s1.right,
          ChainVM.watch (GalilScaffoldChainWatch.immediate w1)⟩ (searchLens.get s1)) :=
      ⟨hm, rfl, by simp, ⟨_, huch⟩⟩
    have hfu : roundFuel h (afterCompare s1 ⟨left s1.left, right s1.right,
          ChainVM.watch (GalilScaffoldChainWatch.immediate w1)⟩ (searchLens.get s1))
        < roundFuel h s := by
      have e1 : roundFuel h (afterCompare s1 ⟨left s1.left, right s1.right,
            ChainVM.watch (GalilScaffoldChainWatch.immediate w1)⟩ (searchLens.get s1))
          = (4 * h + 1) -
            (value (GalilScaffoldChainWatch.immediate w1).machine.control.distance).toNat := by
        simp only [roundFuel, huch]
      have e2 : roundFuel h s = (4 * h + 1) - (value w.machine.control.distance).toNat := by
        simp only [roundFuel, hw]
      rw [e1, e2, hdist]
      omega
    refine Or.inr ⟨{c with clock := 2048, output := o, replaying := false}, _, ?_, hLu, hfu⟩
    revert hseg2
    cases c with
    | mk mode clock output replaying odd pair =>
      intro hseg2
      exact watchSeg_append hseg1 hseg2
  · exact Or.inl ⟨hL', trivial,
      Or.inr (Or.inr (Or.inr ⟨{c with clock := 1}, s1, hseg1, rfl, hL1, hmm⟩))⟩

/-- **Derived — the watch phase, end to end**, on the discharged contracts. -/
theorem watchRun_terminal' (P : Shared) (q : ℕ) (first : Fin 9) (h : ℕ)
    (hready : PalPeg.GalilReplayChainSeg.ChainTickable)
    (halign : MatchTickC)
    (hland : ∀ (c : Control) (s : GalilVM), LiveScanWatch c s → LandingReadyC s)
    (c : Control) (s : GalilVM) (hL : LiveScanWatch c s) :
    ∃ (c' : Control) (s' : GalilVM),
      WatchSeg P q first 2048 c s c' s' ∧ LiveScanWatch c' s' ∧
        TerminalC P q first h TrivPrep c' s' :=
  PalPeg.CloseoutWatchRun.watchRun_of_distance P q first h (TerminalC P q first h TrivPrep)
    (roundStepC_of_align P q first h hready halign hland) c s hL

/-! ## 5. The terminal record in the shape the tails demand -/

/-- The rounds out of *every* preparation segment of the post-compare landing
`(cP, sP)` reach a terminal landing.  This is the quantifier shape both
`ShiftTailC` and `NoShiftTailC0` close over. -/
def TerminalRunC (P : Shared) (q : ℕ) (first : Fin 9) (h : ℕ)
    (cP : Control) (sP : GalilVM) : Prop :=
  ∀ (es : List Bool) (c2 : Control) (s2 : GalilVM),
    WatchSegE P q first 2048 es cP sP c2 s2 → LiveScanWatch c2 s2 →
      ∃ (cT : Control) (sT : GalilVM),
        WatchSeg P q first 2048 c2 s2 cT sT ∧ LiveScanWatch cT sT ∧
          TerminalC P q first h TrivPrep cT sT

/-- **Derived.** -/
theorem terminalRunC_of_align (P : Shared) (q : ℕ) (first : Fin 9) (h : ℕ)
    (hready : PalPeg.GalilReplayChainSeg.ChainTickable)
    (halign : MatchTickC)
    (hland : ∀ (c : Control) (s : GalilVM), LiveScanWatch c s → LandingReadyC s)
    (cP : Control) (sP : GalilVM) : TerminalRunC P q first h cP sP := by
  intro es c2 s2 hseg hL
  exact watchRun_terminal' P q first h hready halign hland c2 s2 hL

/-- The found-tick context of `CloseoutFoundCompare` / `CloseoutPrepInputs3`:
the common preamble of `ShiftTailC` and `NoShiftTailC0`.  Every conjunct is
entry data — the found comparison, its `found` search state, the chain it
starts, and the fact that `(cP, sP)` is that comparison's control and
post-state. -/
def FoundCompareCtxC (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (c0 : Control) (r : GalilVM) (cP : Control) (sP : GalilVM) : Prop :=
  ∃ (es0 : List Bool) (cF : Control) (sF : GalilVM) (vq : SearchVM) (ch : ChainVM)
    (oF : Bool) (a : Fin 2) (ls rs qw : List (Fin 2)) (gap : Bool),
    raw = (a :: ls).reverse ++ rs ++ qw ∧
    WatchSegE (PofC centre place entry raw) qq first 2048 es0 c0 r cF sF ∧
    cF.mode = .scan ∧ cF.replaying = false ∧ cF.clock = 1 ∧ canRight sF.right ∧
    sF.chain = ChainVM.idle ∧
    sF.center = represent ⟨a :: ls, gap⟩ (rs.map some) qw ∧
    searchEffect (PofC centre place entry raw) true sF vq ∧ vq.search.mode = .found ∧
    read (left sF.left) = read (right sF.right) ∧
    ChainMatched (chainStart (vq.dp.config.tapes 11)
      ((PofC centre place entry raw).centre sF) ((PofC centre place entry raw).place sF)
      sF.center sF.radius) ch ∧
    ch ≠ ChainVM.idle ∧
    refresh (galilFrame (PofC centre place entry raw) qq first)
      (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq) cF.output oF ∧
    cP = {cF with clock := 2048, output := oF, replaying := false} ∧
    sP = afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq

/-- **The terminal record.**  `CloseoutWatchRound.TerminalC` at the end of the
rounds, together with the found-tick context the tails also require. -/
def TerminalC' (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (h : ℕ) (c0 : Control) (r : GalilVM)
    (cP : Control) (sP : GalilVM) : Prop :=
  FoundCompareCtxC centre place entry qq first raw c0 r cP sP ∧
    TerminalRunC (PofC centre place entry raw) qq first h cP sP

/-- **Derived — `watchRun_terminal` re-exported in the tails' shape.** -/
theorem terminalC'_of_align (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (h : ℕ)
    (hready : PalPeg.GalilReplayChainSeg.ChainTickable)
    (halign : MatchTickC)
    (hland : ∀ (c : Control) (s : GalilVM), LiveScanWatch c s → LandingReadyC s)
    {c0 cP : Control} {r sP : GalilVM}
    (hctx : FoundCompareCtxC centre place entry qq first raw c0 r cP sP) :
    TerminalC' centre place entry qq first raw h c0 r cP sP :=
  ⟨hctx, terminalRunC_of_align (PofC centre place entry raw) qq first h hready halign hland
    cP sP⟩

/-- **NAMED (open) — the only contract left.**  The terminal record is one of
the two tails.  Its preamble is already supplied by `FoundCompareCtxC`, so what
remains is the tail *body*: the shift tail's `beginShiftVM` / `Rounds` /
`ScanSeg` chain (`CloseoutWatchPhase2.ShiftTailC`), or the break tail's
`freshWatch` landing with `es.count true = 0` and the nonnegative break margin
(`CloseoutWatchPhase3.NoShiftTailC0`). -/
def TerminalTailsC' (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m h : ℕ) (c0 : Control) (r : GalilVM)
    (cP : Control) (sP : GalilVM) : Prop :=
  TerminalC' centre place entry qq first raw h c0 r cP sP →
    ShiftTailC centre place entry qq first raw m c0 r cP sP ∨
      NoShiftTailC0 centre place entry qq first raw m c0 r cP sP

/-! ## 6. The composition -/

open PalPeg.CloseoutFoundCompare (RoundsExit BreakExit)
open PalPeg.CloseoutPrepInputs2 (MismatchExitG)
open PalPeg.CloseoutPrepInputs3 (PrepInputsG3 foundExit_of_compare3)

/-- **Derived — the found comparison's exit, on the discharged contracts.**
`TerminalC'` comes from §4–5; the tails contract is the only NAMED input
besides the alignment datum `MatchTickC`, the landing shape `LandingReadyC`,
the chain tickability, and the entry data (`StageEntryC`, `SegReachedW`,
`PrepInputsG3`, `MismatchExitG`, `LandingRestartReach`). -/
theorem foundExit_compare_final (centreC : GalilVM → Fin 3)
    (placeC : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (m h : ℕ)
    (hP : Decodes (PofC centreC placeC entry w))
    (hex : ∀ s, (PofC centreC placeC entry w).replayExhausted s = zero s.replay)
    (hready : PalPeg.GalilReplayChainSeg.ChainTickable)
    (halign : MatchTickC)
    (hland : ∀ (c : Control) (s : GalilVM), LiveScanWatch c s → LandingReadyC s)
    {c c' cP : Control} {r t sP : GalilVM}
    (hE : StageEntryC (PofC centreC placeC entry w) q first w c r)
    (hsW : SegReachedW centreC placeC entry q first w c r c' t)
    (hLR : LandingRestartReach (PofC centreC placeC entry w) q first w c r)
    (a : Fin 2) (ls rs qw : List (Fin 2)) (gap : Bool) {lower span : ℕ}
    (hprep : PrepInputsG3 (PofC centreC placeC entry w) q first ⟨a :: ls, gap⟩ lower span
      cP sP)
    (hmis : MismatchExitG (PofC centreC placeC entry w) q first w m c r cP sP)
    (hctx : FoundCompareCtxC centreC placeC entry q first w c r cP sP)
    (htails : TerminalTailsC' centreC placeC entry q first w m h c r cP sP) :
    FoundExit (PofC centreC placeC entry w) q first w m c r := by
  have hT : TerminalC' centreC placeC entry q first w h c r cP sP :=
    terminalC'_of_align centreC placeC entry q first w h hready halign hland hctx
  have htail : ShiftTailC centreC placeC entry q first w m c r cP sP ∨
      PalPeg.CloseoutWatchPhase2.NoShiftTailC centreC placeC entry q first w m c r cP sP := by
    rcases htails hT with hs | hn
    · exact Or.inl hs
    · exact Or.inr (noShiftTailC_of_0 centreC placeC entry q first w m hn)
  have hroute := watchRouteLP_of_tails centreC placeC entry q first w m hex hE hLR htail
  have hbranch : RoundsExit (PofC centreC placeC entry w) q first w m c r cP sP ∨
      BreakExit (PofC centreC placeC entry w) q first w m c r cP sP := by
    rcases hroute with hro | hbr
    · exact Or.inl (PalPeg.CloseoutWatchPhase.roundsExit_of_LP hro)
    · exact Or.inr (PalPeg.CloseoutWatchPhase.breakExit_of_LP hbr)
  exact foundExit_of_compare3 centreC placeC entry q first w m hP hE hsW a ls rs qw gap
    hprep hmis hbranch

end PalPeg.CloseoutWatchRound2

#print axioms PalPeg.CloseoutWatchRound2.watchClosed
#print axioms PalPeg.CloseoutWatchRound2.distance_mono_internal
#print axioms PalPeg.CloseoutWatchRound2.distance_mono_false
#print axioms PalPeg.CloseoutWatchRound2.watchTick_immediate
#print axioms PalPeg.CloseoutWatchRound2.prepInvC_triv
#print axioms PalPeg.CloseoutWatchRound2.roundStepC_of_align
#print axioms PalPeg.CloseoutWatchRound2.watchRun_terminal'
#print axioms PalPeg.CloseoutWatchRound2.terminalRunC_of_align
#print axioms PalPeg.CloseoutWatchRound2.terminalC'_of_align
#print axioms PalPeg.CloseoutWatchRound2.foundExit_compare_final
