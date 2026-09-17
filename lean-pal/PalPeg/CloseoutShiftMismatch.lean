import PalPeg.CloseoutWatchRound9
import PalPeg.GalilRoundPeriod

/-!
# `ShiftAtMismatchC` over-asserts, and the missing exit is the fallback

`CloseoutWatchRound9.roundOne_of_segRun` builds one `Rounds` step out of
`ShiftAtMismatchC`.  Its own header calls that leaf "input-dependent", which is
right, but the statement does more than depend on the input — it **asserts**
part of it.  `SegEndS`'s third exit is a disjunction

```
singlePositive s1.cycle = true ∨ read (left s1.left) ≠ read (right s1.right)
```

and the consumer routes the first disjunct to the early exit, so in the branch
where `ShiftAtMismatchC` is applied the cycle's end is **unknown**.  Yet the
leaf's conclusion contains `singlePositive s1.cycle = true`.

That is the fifth instance of the same defect (`ShiftPal`, `H_advanceT`,
`MatchTickC`, `hpos`): a leaf quantified over states its sole consumer never
reaches.  And the machine agrees with the consumer, not the leaf —
`ScaffoldGalil.scala:254`:

```scala
if (left.read() == right.read())          matchedPlace()
else if (!replaying && chain.canShift && chain.prediction() == right.read())
                                          beginChainShift()
else                                      beginFallback()
```

`canShift` (`shiftGuardVM`) contains `if periodOnly then singlePositive cycle`,
so at a **mid-cycle** mismatch a `periodOnly` chain does not shift, it falls
back.  `shiftAtMismatchC_false_at_nonterminal` below is that contradiction,
machine-checked and grounded in a reachable configuration (a non-terminal
`RoundScan`, whose `terminal_iff` gives `singlePositive s.cycle = false`).

`ShiftAtMismatchN` is the reformulation — the cycle's end moves from the
conclusion to the premises — and `roundOne_of_segRun_N` is the consumer with
the branch the machine actually takes: the terminal exit of `SegEndS` now
distinguishes "cycle end" from "mid-cycle mismatch", and the latter is where
the oracle's `hmismatch` leaf (`FallbackRouteMC2`) already takes over.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutShiftMismatch

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton
open PalPeg.CloseoutWatchRun (LiveScanWatch roundFuel)
open PalPeg.CloseoutWatchRound (RoundDataC WatchClosedC)
open PalPeg.CloseoutWatchRound9
open PalPeg.GalilRoundPeriod

/-! ## 1. The refutation -/

/-- **`ShiftAtMismatchC` is false at a non-terminal mismatch.**  A `RoundScan`
that is not at its terminal has `singlePositive s.cycle = false`
(`RoundScan.terminal_iff`), while the leaf's conclusion asserts the opposite. -/
theorem shiftAtMismatchC_false_at_nonterminal {raw : List (Fin 2)} {C R h used : ℕ}
    {s : GalilVM} {w0 : GalilScaffoldChainWatch.State}
    (hI : RoundScan raw C R h used s w0)
    (hne : used + 1 ≠ 2 * h)
    (hmm : read (GalilScaffoldInputHead.left s.left) ≠ read (right s.right))
    {P : Shared} {q : ℕ} {first : Fin 9} {h' : ℕ} {c : Control}
    (hS : ShiftAtMismatchC P q first h' c s) : False := by
  have hmid : singlePositive s.cycle = false := by
    cases hq : singlePositive s.cycle with
    | false => rfl
    | true => exact absurd (hI.terminal_iff.mp hq) hne
  obtain ⟨vs, vq, s2, t', -, -, -, hend, -⟩ := hS w0 hI.chain hmm
  rw [hend] at hmid
  cases hmid

/-! ## 2. The reformulation -/

/-- **(NAMED, reformulated) the shift block at a *terminal* mismatch.**  The
cycle's end is a premise, which is what the machine's `canShift` requires and
what the consumer decides for itself. -/
def ShiftAtMismatchN (P : Shared) (q : ℕ) (first : Fin 9) (h : ℕ) (c1 : Control)
    (s1 : GalilVM) : Prop :=
  ∀ w : GalilScaffoldChainWatch.State, s1.chain = ChainVM.watch w →
    read (left s1.left) ≠ read (right s1.right) →
    singlePositive s1.cycle = true →
    ∃ (vs : ScanVM) (vq : SearchVM) (s2 : GalilVM) (t' : ShiftState),
      (galilFrame P q first).compare s1 (scanLens.set s1 vs) ∧
      ¬ (galilFrame P q first).matched (scanLens.set s1 vs) ∧
      searchEffect P false s1 vq ∧
      read (right s1.right) =
        GalilScaffoldChainConsume.symbol w.machine.control.period.focus ∧
      Canonical s1.length ∧
      P.shiftGuard (afterMismatch s1 vs vq) ∧
      P.beginShift (afterMismatch s1 vs vq) s2 ∧
      beginShiftVM h w (afterMismatch s1 vs vq) s2 ∧ CopyIdle s2 ∧
      ShiftRun ⟨s1.center, left s1.left, ofNat h, inc s1.radius, inc (inc s1.length)⟩ h t'

/-- `ShiftAtMismatchN` is strictly weaker than `ShiftAtMismatchC`. -/
theorem shiftAtMismatchN_of_C {P : Shared} {q : ℕ} {first : Fin 9} {h : ℕ}
    {c1 : Control} {s1 : GalilVM} (hS : ShiftAtMismatchC P q first h c1 s1) :
    ShiftAtMismatchN P q first h c1 s1 := by
  intro w hch hmm _
  obtain ⟨vs, vq, s2, t', h1, h2, h3, -, h5, h6, h7, h8, h9, h10, h11⟩ := hS w hch hmm
  exact ⟨vs, vq, s2, t', h1, h2, h3, h5, h6, h7, h8, h9, h10, h11⟩

/-! ## 3. The consumer, with the fallback exit -/

/-- **One complete round, or the fallback.**  `roundOne_of_segRun` with the
reformulated leaf: the terminal exit now says *which* of the two `SegEndS`
disjuncts stopped the segment, and only the cycle-end one is fed to the shift
block.  The new case — a mid-cycle mismatch — is the machine's `beginFallback`,
which is the oracle's `hmismatch` (`FallbackRouteMC2`) branch. -/
theorem roundOne_of_segRun_N (P : Shared) (q : ℕ) (first : Fin 9) (h : ℕ)
    (hready : PalPeg.GalilReplayChainSeg.ChainTickable)
    (hclosed : WatchClosedC)
    (hdata : ∀ (c : Control) (s : GalilVM), LiveScanWatch c s →
      RoundDataC P q first h c s)
    (hshift : ∀ (c1 : Control) (s1 : GalilVM), LiveScanWatch c1 s1 →
      ShiftAtMismatchN P q first h c1 s1)
    (c : Control) (s : GalilVM) (hL : LiveScanWatch c s) :
    (∃ (n : ℕ) (c' : Control) (s' : GalilVM),
        ScanSeg P q first 2048 n c s c' s' ∧ LiveScanWatch c' s' ∧
        (roundFuel h s' = 0 ∨ ¬ canRight s'.right ∨
          ∃ (n1 : ℕ) (c1 : Control) (s1 : GalilVM),
            ScanSeg P q first 2048 n1 c' s' c1 s1 ∧ c1.clock = 1 ∧
              LiveScanWatch c1 s1 ∧
              (singlePositive s1.cycle = true ∨
                (read (left s1.left) ≠ read (right s1.right) ∧
                  singlePositive s1.cycle = false)))) ∨
      ∃ (c' : Control) (s' : GalilVM),
        Rounds P q first 2048 h 1 c s c' s' := by
  classical
  obtain ⟨n, cT, sT, hseg, hLT, hterm⟩ := segRun_terminal P q first h hready hclosed hdata c s hL
  obtain ⟨-, hexit⟩ := hterm
  rcases hexit with h0 | hnr | ⟨n1, c1, s1, hseg1, hc1, hL1, hl1, hr1, hrd1, hcase⟩
  · exact Or.inl ⟨n, cT, sT, hseg, hLT, Or.inl h0⟩
  · exact Or.inl ⟨n, cT, sT, hseg, hLT, Or.inr (Or.inl hnr)⟩
  rcases hcase with hcyc | hmm
  · exact Or.inl ⟨n, cT, sT, hseg, hLT,
      Or.inr (Or.inr ⟨n1, c1, s1, hseg1, hc1, hL1, Or.inl hcyc⟩)⟩
  cases hcyc2 : singlePositive s1.cycle with
  | false =>
    exact Or.inl ⟨n, cT, sT, hseg, hLT,
      Or.inr (Or.inr ⟨n1, c1, s1, hseg1, hc1, hL1, Or.inr ⟨hmm, hcyc2⟩⟩)⟩
  | true =>
    obtain ⟨hm1, hr1', hclk1, w1, hw1⟩ := hL1
    obtain ⟨vs, vq, s2, t', hcmp, hmis, hq, hpred, hlen, hg, hb, hs2, hi2, hrun⟩ :=
      hshift c1 s1 ⟨hm1, hr1', hclk1, w1, hw1⟩ w1 hw1 hmm hcyc2
    have hav1 : canRight s1.right := by
      obtain ⟨hav, -, -⟩ := hdata cT sT hLT
      rw [hr1]; exact hav
    obtain ⟨v, cycle, o, hround⟩ :=
      roundStep_of_shiftRun P q first 2048 h
        (scanSeg_append P q first 2048 hseg hseg1)
        hm1 hr1' hc1 w1 hw1 hav1 vs vq hcmp hmis hq hcyc2 hpred hlen hg s2 hb hs2 hi2 hrun
    exact Or.inr ⟨_, _, hround⟩

/-! ## 4. `ShiftAtMismatchN` still over-asserts — the guard is input data too

Recording my own error: moving the cycle's end to the premises is not enough.
`ShiftAtMismatchN`'s conclusion still contains

```
read (right s1.right) = GalilScaffoldChainConsume.symbol w.machine.control.period.focus
```

and that equation *is* the machine's branch condition.  At a terminal
`RoundScan` the two sides are `(encoded raw)[C+R+2h+1]?` (the right head sits at
`C+R+1+used = C+R+2h`) and `(encoded raw)[C+R+1]?` (`RoundScan.pred` at
`used = 2h-1`), so the agreement is the input-dependent equation
`(encoded raw)[C+R+1]? = (encoded raw)[C+R+2h+1]?` — precisely the condition
under which Galil's shift continues.  When it fails the machine runs
`beginFallback()`; a leaf asserting it universally would make that branch dead
code.

`CloseoutWatchRound30` already has the right shape for this: its
`ShiftRoundAtC'` takes the post-compare guard `shiftGuardVM (afterMismatch s1 vs vq')`
as the **trigger**, not as a conclusion.  `ShiftTrigger` names that condition and
`ShiftAtMismatchM` premises it, leaving in the leaf only the *mechanical* pieces
(`beginShift`, `CopyIdle`, the `h`-unit `ShiftRun`, and the state invariant
`Canonical s1.length`).  The consumer decides the trigger classically, and the
negative branch is the machine's fallback. -/

/-- **The machine's `beginChainShift` condition** at a mismatching landing:
a frame compare that is not matched, the background search effect, and the
post-compare shift guard.  `¬ ShiftTrigger` is `beginFallback`. -/
def ShiftTrigger (P : Shared) (q : ℕ) (first : Fin 9) (s1 : GalilVM) : Prop :=
  ∃ (vs : ScanVM) (vq : SearchVM) (w : GalilScaffoldChainWatch.State),
    s1.chain = ChainVM.watch w ∧
    (galilFrame P q first).compare s1 (scanLens.set s1 vs) ∧
    ¬ (galilFrame P q first).matched (scanLens.set s1 vs) ∧
    searchEffect P false s1 vq ∧
    read (right s1.right) =
      GalilScaffoldChainConsume.symbol w.machine.control.period.focus ∧
    P.shiftGuard (afterMismatch s1 vs vq)

/-- **(NAMED, reformulated twice) the *mechanical* pieces of the shift.**  Both
input-dependent facts — the cycle's end and the guard — are premises now; what
remains is the machine's own bookkeeping. -/
def ShiftAtMismatchM (P : Shared) (q : ℕ) (first : Fin 9) (h : ℕ) (c1 : Control)
    (s1 : GalilVM) : Prop :=
  ∀ w : GalilScaffoldChainWatch.State, s1.chain = ChainVM.watch w →
    read (left s1.left) ≠ read (right s1.right) →
    singlePositive s1.cycle = true →
    ∀ (vs : ScanVM) (vq : SearchVM),
      (galilFrame P q first).compare s1 (scanLens.set s1 vs) →
      searchEffect P false s1 vq →
      P.shiftGuard (afterMismatch s1 vs vq) →
      ∃ (s2 : GalilVM) (t' : ShiftState),
        Canonical s1.length ∧
        P.beginShift (afterMismatch s1 vs vq) s2 ∧
        beginShiftVM h w (afterMismatch s1 vs vq) s2 ∧ CopyIdle s2 ∧
        ShiftRun ⟨s1.center, left s1.left, ofNat h, inc s1.radius, inc (inc s1.length)⟩ h t'

/-! `ShiftAtMismatchM` is not derived from `ShiftAtMismatchN` here: `N` returns
its block at an existential compare of its own, while `M` must return it at the
compare the consumer already fixed, so the implication does not hold in that
direction.  `M` is the statement to discharge; `N` is recorded only because it
was the first (still insufficient) reformulation. -/

/-- **One complete round, or the fallback.**  The terminal exit of `SegEndS` is
now split three ways: the cycle ends without a mismatch (the chain breaks —
`CloseoutTerminalBreak.terminal_match_breaks`), the cycle ends at a mismatch
whose trigger holds (the shift, one `Rounds` step), or neither (the machine's
`beginFallback`, which is the oracle's `hmismatch` branch). -/
theorem roundOne_of_segRun_M (P : Shared) (q : ℕ) (first : Fin 9) (h : ℕ)
    (hready : PalPeg.GalilReplayChainSeg.ChainTickable)
    (hclosed : WatchClosedC)
    (hdata : ∀ (c : Control) (s : GalilVM), LiveScanWatch c s →
      RoundDataC P q first h c s)
    (hshift : ∀ (c1 : Control) (s1 : GalilVM), LiveScanWatch c1 s1 →
      ShiftAtMismatchM P q first h c1 s1)
    (c : Control) (s : GalilVM) (hL : LiveScanWatch c s) :
    (∃ (n : ℕ) (c' : Control) (s' : GalilVM),
        ScanSeg P q first 2048 n c s c' s' ∧ LiveScanWatch c' s' ∧
        (roundFuel h s' = 0 ∨ ¬ canRight s'.right ∨
          ∃ (n1 : ℕ) (c1 : Control) (s1 : GalilVM),
            ScanSeg P q first 2048 n1 c' s' c1 s1 ∧ c1.clock = 1 ∧
              LiveScanWatch c1 s1 ∧
              (singlePositive s1.cycle = true ∨
                (read (left s1.left) ≠ read (right s1.right) ∧
                  (singlePositive s1.cycle = false ∨
                    ¬ ShiftTrigger P q first s1))))) ∨
      ∃ (c' : Control) (s' : GalilVM),
        Rounds P q first 2048 h 1 c s c' s' := by
  classical
  obtain ⟨n, cT, sT, hseg, hLT, hterm⟩ := segRun_terminal P q first h hready hclosed hdata c s hL
  obtain ⟨-, hexit⟩ := hterm
  rcases hexit with h0 | hnr | ⟨n1, c1, s1, hseg1, hc1, hL1, hl1, hr1, hrd1, hcase⟩
  · exact Or.inl ⟨n, cT, sT, hseg, hLT, Or.inl h0⟩
  · exact Or.inl ⟨n, cT, sT, hseg, hLT, Or.inr (Or.inl hnr)⟩
  rcases hcase with hcyc | hmm
  · exact Or.inl ⟨n, cT, sT, hseg, hLT,
      Or.inr (Or.inr ⟨n1, c1, s1, hseg1, hc1, hL1, Or.inl hcyc⟩)⟩
  cases hcyc2 : singlePositive s1.cycle with
  | false =>
    exact Or.inl ⟨n, cT, sT, hseg, hLT,
      Or.inr (Or.inr ⟨n1, c1, s1, hseg1, hc1, hL1,
        Or.inr ⟨hmm, Or.inl hcyc2⟩⟩)⟩
  | true =>
    by_cases hT : ShiftTrigger P q first s1
    · obtain ⟨vs, vq, w, hwc, hcmp, hmis, hq, hpred, hg⟩ := hT
      obtain ⟨hm1, hr1', hclk1, w1, hw1⟩ := hL1
      have hww : w = w1 := by rw [hw1] at hwc; cases hwc; rfl
      subst hww
      obtain ⟨s2, t', hlen, hb, hs2, hi2, hrun⟩ :=
        hshift c1 s1 ⟨hm1, hr1', hclk1, w, hw1⟩ w hw1 hmm hcyc2 vs vq hcmp hq hg
      have hav1 : canRight s1.right := by
        obtain ⟨hav, -, -⟩ := hdata cT sT hLT
        rw [hr1]; exact hav
      obtain ⟨v, cycle, o, hround⟩ :=
        roundStep_of_shiftRun P q first 2048 h
          (scanSeg_append P q first 2048 hseg hseg1)
          hm1 hr1' hc1 w hw1 hav1 vs vq hcmp hmis hq hcyc2 hpred hlen hg s2 hb hs2 hi2 hrun
      exact Or.inr ⟨_, _, hround⟩
    · exact Or.inl ⟨n, cT, sT, hseg, hLT,
        Or.inr (Or.inr ⟨n1, c1, s1, hseg1, hc1, hL1,
          Or.inr ⟨hmm, Or.inr hT⟩⟩)⟩

#print axioms shiftAtMismatchC_false_at_nonterminal
#print axioms shiftAtMismatchN_of_C
#print axioms roundOne_of_segRun_N
#print axioms ShiftTrigger
#print axioms roundOne_of_segRun_M

end PalPeg.CloseoutShiftMismatch
