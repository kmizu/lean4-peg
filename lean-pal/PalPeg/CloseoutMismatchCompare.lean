import PalPeg.CloseoutShiftRun
import PalPeg.CloseoutPackRun31

/-!
# The mismatching comparison at a round terminal, constructed

`CloseoutShiftMismatch.ShiftAtMismatchM` and `Rounds.next` both need, at a
terminal mismatching landing, a frame comparison `vs` whose chain is **still the
same watch**.  `CloseoutWatchRound30`'s header calls that "piece 1" and notes
that `ChainTick false (.watch w) (.watch w')` only gives some
`GalilScaffoldChainWatch.Internal w w'`, so the data seems to assert that the
disabled tick keeps the watch state.

At a *round terminal* it does not have to be assumed.  `RoundScan.caught.lagZero`
gives `zero w.lag = true`, and

* `Internal.idle w (positive_eq_false_of_zero hz) : Internal w w`;
* `ChainStep.watchStep w w · : ChainStep (.watch w) (.watch w)`;
* `ChainTick a x z := ∃ y, ChainStep x y ∧ (if a then ChainMatched y z else z = y)`,
  so at `a = false` the tick *is* the step.

And `galilFrame`'s `compare` is `Frame.pull scanLens (scanFrame …)`, i.e.

```
vs.left = left s.left ∧ vs.right = right s.right ∧
  ChainTick (decide (read (left s.left) = read (right s.right))) s.chain vs.chain
```

which a mismatch turns into `ChainTick false`.  So the whole comparison is
**constructible**: `compare_mismatch_of_lagZero` below.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutMismatchCompare

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton PalPeg.CloseoutPackRun31

/-- **A disabled chain tick at lag zero keeps the watch.** -/
theorem chainTick_false_idle {w : GalilScaffoldChainWatch.State} (hz : zero w.lag = true) :
    ChainTick false (ChainVM.watch w) (ChainVM.watch w) :=
  ⟨ChainVM.watch w,
    .watchStep w w (.idle w (positive_eq_false_of_zero hz)), rfl⟩

/-- **The mismatching comparison, constructed.**  At a watching chain with zero
lag and disagreeing outer symbols the frame's comparison exists, is not
`matched`, moves both heads one place, and leaves the chain exactly where it
was. -/
theorem compare_mismatch_of_lagZero (P : Shared) (q : ℕ) (first : Fin 9)
    {s : GalilVM} {w : GalilScaffoldChainWatch.State}
    (hch : s.chain = ChainVM.watch w) (hz : zero w.lag = true)
    (hmm : read (GalilScaffoldInputHead.left s.left) ≠ read (right s.right)) :
    ∃ vs : ScanVM,
      (galilFrame P q first).compare s (scanLens.set s vs) ∧
      ¬ (galilFrame P q first).matched (scanLens.set s vs) ∧
      vs.left = GalilScaffoldInputHead.left s.left ∧
      vs.right = right s.right ∧
      vs.chain = ChainVM.watch w := by
  refine ⟨⟨GalilScaffoldInputHead.left s.left, right s.right, ChainVM.watch w⟩, ⟨?_, ?_⟩, ?_,
    rfl, rfl, rfl⟩
  · refine ⟨rfl, rfl, ?_⟩
    show ChainTick (decide (read (GalilScaffoldInputHead.left s.left) = read (right s.right)))
      s.chain (ChainVM.watch w)
    rw [hch, decide_eq_false hmm]
    exact chainTick_false_idle hz
  · rfl
  · show ¬ (read (GalilScaffoldInputHead.left s.left) = read (right s.right))
    exact hmm

/-- **The same at a round terminal**, where `lagZero` is a `RoundScan` field. -/
theorem compare_mismatch_of_round (P : Shared) (q : ℕ) (first : Fin 9)
    {raw : List (Fin 2)} {C R h used : ℕ} {s : GalilVM}
    {w : GalilScaffoldChainWatch.State}
    (hI : PalPeg.GalilRoundPeriod.RoundScan raw C R h used s w)
    (hmm : read (GalilScaffoldInputHead.left s.left) ≠ read (right s.right)) :
    ∃ vs : ScanVM,
      (galilFrame P q first).compare s (scanLens.set s vs) ∧
      ¬ (galilFrame P q first).matched (scanLens.set s vs) ∧
      vs.left = GalilScaffoldInputHead.left s.left ∧
      vs.right = right s.right ∧
      vs.chain = ChainVM.watch w :=
  compare_mismatch_of_lagZero P q first hI.chain hI.caught.lagZero hmm

/-- **A chain step out of a zero-lag watch is the identity.** -/
theorem chainStep_watch_of_lagZero {w : GalilScaffoldChainWatch.State} {z : ChainVM}
    (hz : zero w.lag = true) (h : ChainStep (ChainVM.watch w) z) : z = ChainVM.watch w := by
  cases h with
  | watchStep w0 w' hi => rw [internal_of_zero hz hi]

/-- **So does the *given* mismatching comparison keep the watch.**  The dual of
`compare_mismatch_of_lagZero`: there the comparison is built, here an arbitrary
one is analysed. -/
theorem compare_chain_of_mismatch (P : Shared) (q : ℕ) (first : Fin 9)
    {s : GalilVM} {vs : ScanVM} {w : GalilScaffoldChainWatch.State}
    (hch : s.chain = ChainVM.watch w) (hz : zero w.lag = true)
    (hmm : read (GalilScaffoldInputHead.left s.left) ≠ read (right s.right))
    (hcmp : (galilFrame P q first).compare s (scanLens.set s vs)) :
    vs.chain = ChainVM.watch w ∧ vs.left = GalilScaffoldInputHead.left s.left ∧
      vs.right = right s.right := by
  obtain ⟨⟨hl, hr, htick⟩, -⟩ := hcmp
  have hl' : vs.left = GalilScaffoldInputHead.left s.left := hl
  have hr' : vs.right = right s.right := hr
  have ht : ChainTick (decide (read (GalilScaffoldInputHead.left s.left) = read (right s.right)))
      s.chain vs.chain := htick
  rw [decide_eq_false hmm, hch] at ht
  obtain ⟨y, hstep, hzy⟩ := ht
  have hy : y = ChainVM.watch w := chainStep_watch_of_lagZero hz hstep
  have : vs.chain = ChainVM.watch w := by
    show vs.chain = ChainVM.watch w
    rw [show vs.chain = y from hzy, hy]
  exact ⟨this, hl', hr'⟩

/-! ## The shift entry and the copy component -/

/-- **`CopyIdle` depends only on the FPP component.** -/
theorem copyIdle_congr {s t : GalilVM} (h : t.fpp = s.fpp) (hs : CopyIdle s) : CopyIdle t := by
  rw [copyIdle_iff] at hs ⊢
  rw [h]; exact hs

/-- **The shift entry, constructed.**  `beginShiftVM h w u t` pins `t` outright
and `beginShiftVM'` is its existential over the watch, so once the period length
matches there is nothing left to check. -/
theorem beginShift_of_guard {centre : GalilVM → Fin 3}
    {place : GalilVM → GalilScaffoldPlace.Place} {entry : ℕ} {w0 : List (Fin 2)}
    {u : GalilVM} {wch : GalilScaffoldChainWatch.State} {h : ℕ}
    (hch : u.chain = ChainVM.watch wch) (hper : periodLength wch = h) :
    ∃ t : GalilVM,
      (PofC centre place entry w0).beginShift u t ∧ beginShiftVM h wch u t ∧
      t.fpp = u.fpp := by
  subst hper
  exact ⟨_, ⟨wch, hch, rfl⟩, ⟨hch, rfl⟩, rfl⟩

/-! ## `ShiftAtMismatchM`, discharged at a round terminal -/

/-- **`CloseoutShiftMismatch.ShiftAtMismatchM` for the concrete shared `PofC`.**
Every conjunct is now a construction:

* the mismatching comparison leaves the chain where it was
  (`compare_chain_of_mismatch`, from `RoundScan.caught.lagZero`);
* the shift entry is pinned by `beginShiftVM` (`beginShift_of_guard`);
* `CopyIdle` only reads the FPP component, which neither `afterMismatch` nor the
  shift entry touches (`copyIdle_congr`);
* the `h`-unit `ShiftRun` exists (`CloseoutShiftRun.shiftRun_exists_round`).

What is left as hypotheses are the *carried* invariants: the round datum at the
terminal, `Canonical s1.length` (`CPack.canon`), `CopyIdle s1`
(`AuxPack.copyP`), and the centre head's representation (`CentreRep`) with the
carried centre invariant. -/
theorem shiftAtMismatchM_of_round {centre : GalilVM → Fin 3}
    {place : GalilVM → GalilScaffoldPlace.Place} {entry q : ℕ} {first : Fin 9}
    {w0 : List (Fin 2)} {C R h used : ℕ} {c1 : Control} {s1 : GalilVM}
    (hround : ∀ wch : GalilScaffoldChainWatch.State, s1.chain = ChainVM.watch wch →
      PalPeg.GalilRoundPeriod.RoundScan w0 C R h used s1 wch ∧ periodLength wch = h)
    (hterm : used + 1 = 2 * h)
    (hlen : GalilScaffoldCounter.Canonical s1.length)
    (hcopy : CopyIdle s1)
    (hcen : ∃ rad : ℕ, ScanInvariant w0 (position s1.center) rad s1.left s1.right)
    (hcr : GalilScaffoldInputTrace.Represents s1.center.head w0)
    (hcp : s1.center.head.focus ≠ none) :
    PalPeg.CloseoutShiftMismatch.ShiftAtMismatchM
      (PofC centre place entry w0) q first h c1 s1 := by
  intro wch hch hmm hcyc vs vq hcmp hq hg
  obtain ⟨hI, hper⟩ := hround wch hch
  obtain ⟨hvc, hvl, hvr⟩ :=
    compare_chain_of_mismatch (PofC centre place entry w0) q first hch hI.caught.lagZero hmm hcmp
  have hmc : (afterMismatch s1 vs vq).chain = ChainVM.watch wch := hvc
  obtain ⟨t, hb, hbv, hfpp⟩ := beginShift_of_guard (centre := centre) (place := place)
    (entry := entry) (w0 := w0) hmc hper
  obtain ⟨t', hrun⟩ :=
    PalPeg.CloseoutShiftRun.shiftRun_exists_round hI hterm hcen hcr hcp
  refine ⟨t, t', hlen, hb, hbv, ?_, hrun⟩
  exact copyIdle_congr (by rw [hfpp]; rfl) hcopy

/-- **`CloseoutWatchRound.WatchClosedC`, proved.**  `ChainTick false x z` is just
`ChainStep x z`, and the only `ChainStep` constructor whose source is a `.watch`
is `watchStep`, whose target is a `.watch` too.  (`ChainMatched.breaks` is what
turns a watch into a broken chain, and that only fires at `a = true`.) -/
theorem watchClosedC_proved : PalPeg.CloseoutWatchRound.WatchClosedC := by
  intro w z h
  obtain ⟨y, hstep, hzy⟩ := h
  cases hstep with
  | watchStep w0 w' ht => exact ⟨w', hzy⟩

#print axioms chainTick_false_idle
#print axioms compare_mismatch_of_lagZero
#print axioms compare_mismatch_of_round
#print axioms chainStep_watch_of_lagZero
#print axioms compare_chain_of_mismatch
#print axioms copyIdle_congr
#print axioms beginShift_of_guard
#print axioms shiftAtMismatchM_of_round
#print axioms watchClosedC_proved

end PalPeg.CloseoutMismatchCompare
