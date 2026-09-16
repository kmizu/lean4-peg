import PalPeg.GalilPrepLeast
import PalPeg.GalilReplayChainSeg

/-!
# The preparation period, stated against the chain trace

`prep_watch_start` (`PalPeg/GalilScaffoldTopWatchSegE.lean`),
`prep_watch_start_least` (`PalPeg/GalilPrepLeast.lean`) and `PreludeEnds`
(`PalPeg/GalilPreludeDone.lean`) are all stated against a `WatchSegE`, but
none of them uses anything of the segment except the `ChainTicks` trace it
induces: each concludes through `chainTicks_unique`.  That is an accidental
coupling — `PalPeg.GalilReplayChainSeg.ReplayChainSeg`, the replay segment
with a live chain, induces exactly the same trace (`replayChainSeg_chain`)
and so ought to be admissible in the same places.

This file removes the coupling, mechanically:

* `prep_watch_start_trace` / `prep_watch_start_least_trace` are the
  preparation lemmas with `WatchSegE P q first delay (bs ++ dm :: cs) c0 v0 c1 v1`
  and `v0.chain = ch` replaced by `ChainTicks (bs ++ dm :: cs) ch z`.  They
  mention neither `P`, `q`, `first`, `delay` nor `Control`/`GalilVM`.
* `watchSegE_chainTicks` and `replayChainSeg_chain` are the two feeders.
* `prep_watch_start_of_watchSegE` re-derives the original `prep_watch_start`
  from the trace form (so the restatement is faithful), and
  `prep_watch_start_of_replayChainSeg` is the new consumer.
* `PreludeEndsT` is the trace form of `PreludeEnds`;
  `preludeEnds_of_preludeEndsT` shows it is the stronger hypothesis, and
  `preludeEndsT_replayChainSeg` applies it to a replay segment.

Nothing here is new mathematics: every proof is `chainTicks_unique` or a
rewrite of the feeder's conclusion.
-/

set_option autoImplicit false

namespace PalPeg.GalilScaffoldChainInputSupply

open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-! ## The two feeders -/

/-- A `WatchSegE` with a live chain induces a `ChainTicks` trace on its own
event index.  This is the chain component of `watchSegE_events`, named so that
it pairs with `PalPeg.GalilReplayChainSeg.replayChainSeg_chain`. -/
theorem watchSegE_chainTicks (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) {es : List Bool}
    {c c' : Control} {s t : GalilVM} (h : WatchSegE P q first delay es c s c' t)
    (hne : s.chain ≠ .idle) : ChainTicks es s.chain t.chain :=
  (watchSegE_events P q first delay h hne).1

/-- A chain that a `ChainMatched` of a `chainStart` reaches is not idle. -/
theorem chainMatched_chainStart_ne_idle {answer : GalilScaffoldTape.Tape} {cc : Fin 3}
    {walker : GalilScaffoldPlace.Place} {ver : PlaceHead} {radius : Counter} {ch : ChainVM}
    (h : ChainMatched (chainStart answer cc walker ver radius) ch) : ch ≠ .idle := by
  intro h0
  rw [h0] at h
  cases h

/-! ## The preparation period against the trace -/

/-- **`prep_watch_start`, stated against the chain trace.**  After `h` copy
ticks, the done tick `dm` and `h+1` back ticks, *any* chain trace out of a
`ChainMatched` of the chain start lands on `watchStart`.  No segment, no
controller, no `P`/`q`/`first`/`delay`. -/
theorem prep_watch_start_trace
    {s t : GalilScaffoldSearchFinish.State} {x y : GalilScaffoldControl.Machine 12}
    {as : List Bool} {w : List (Fin 3)} {lower span : ℕ} (p : GalilScaffoldPlace.Place)
    (hw : w = (GalilScaffoldPlace.stream p).take (span+1))
    (hr : GalilScaffoldSearchRun.SafeQuanta s x as t y) (hs : s.mode = .run) (ht : t.mode = .found)
    (hv : GalilDpCorrect.Result w lower 0 (GalilScaffoldProgram.denote y.config))
    (ver : PlaceHead) (r0 : ℕ) (dm : Bool) :
    ∃ (h : ℕ) (c : Fin 3) (ys : List (Fin 3)) (b : Fin 3),
      GalilDpCorrect.Candidate w lower h ∧ GalilScaffoldPlace.read p = some c ∧ ys.length + 1 = h ∧
      ∀ (bs cs : List Bool), bs.length = h → cs.length = h+1 →
        ∀ (ch z : ChainVM), ChainMatched (chainStart (y.config.tapes 11) c p ver (ofNat (r0+1))) ch →
          ChainTicks (bs ++ dm :: cs) ch z →
            z = .watch (watchStart ver c ys b (GalilScaffoldChainCredits.run
              (GalilScaffoldChainCredits.start (ofNat (r0+1)))
              (GalilScaffoldChainCredits.prepEvents true dm bs cs))) := by
  obtain ⟨h, c, ys, b, hcand, hread, hlen, hrest⟩ := found_to_watchStart p hw hr hs ht hv ver r0 true dm
  refine ⟨h, c, ys, b, hcand, hread, hlen, ?_⟩
  intro bs cs hbs hcs ch z hch hticks
  obtain ⟨x1, hx1, hticks'⟩ := hrest bs cs hbs hcs
  simp only [ite_true] at hx1
  have hx : ch = x1 := chainMatched_unique hch hx1
  subst hx
  exact chainTicks_unique hticks hticks'

/-- **`prep_watch_start_least`, stated against the chain trace.**  Same
reduction, carrying the DP link (`pc = 346`, `pos 11 = h`) of
`PalPeg/GalilPrepLeast.lean`. -/
theorem prep_watch_start_least_trace
    {s t : GalilScaffoldSearchFinish.State} {x y : GalilScaffoldControl.Machine 12}
    {as : List Bool} {w : List (Fin 3)} {lower span : ℕ} (p : GalilScaffoldPlace.Place)
    (hw : w = (GalilScaffoldPlace.stream p).take (span+1))
    (hr : GalilScaffoldSearchRun.SafeQuanta s x as t y) (hs : s.mode = .run) (ht : t.mode = .found)
    (hv : GalilDpCorrect.Result w lower 0 (GalilScaffoldProgram.denote y.config))
    (ver : PlaceHead) (r0 : ℕ) (dm : Bool) :
    ∃ (h : ℕ) (c : Fin 3) (ys : List (Fin 3)) (b : Fin 3),
      GalilDpCorrect.Candidate w lower h ∧ GalilScaffoldPlace.read p = some c ∧ ys.length + 1 = h ∧
      (GalilScaffoldProgram.denote y.config).pc = 346 ∧
      (GalilScaffoldProgram.denote y.config).pos 11 = h ∧
      ∀ (bs cs : List Bool), bs.length = h → cs.length = h+1 →
        ∀ (ch z : ChainVM), ChainMatched (chainStart (y.config.tapes 11) c p ver (ofNat (r0+1))) ch →
          ChainTicks (bs ++ dm :: cs) ch z →
            z = .watch (watchStart ver c ys b (GalilScaffoldChainCredits.run
              (GalilScaffoldChainCredits.start (ofNat (r0+1)))
              (GalilScaffoldChainCredits.prepEvents true dm bs cs))) := by
  obtain ⟨h, c, ys, b, hcand, hread, hlen, hpc, hcur, hrest⟩ :=
    found_to_watchStart_least p hw hr hs ht hv ver r0 true dm
  refine ⟨h, c, ys, b, hcand, hread, hlen, hpc, hcur, ?_⟩
  intro bs cs hbs hcs ch z hch hticks
  obtain ⟨x1, hx1, hticks'⟩ := hrest bs cs hbs hcs
  simp only [ite_true] at hx1
  have hx : ch = x1 := chainMatched_unique hch hx1
  subst hx
  exact chainTicks_unique hticks hticks'

/-! ## The two consumers -/

/-- **`WatchSegE` feeds the trace form**: the original `prep_watch_start` is
recovered from `prep_watch_start_trace` through `watchSegE_chainTicks`. -/
theorem prep_watch_start_of_watchSegE (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    {s t : GalilScaffoldSearchFinish.State} {x y : GalilScaffoldControl.Machine 12}
    {as : List Bool} {w : List (Fin 3)} {lower span : ℕ} (p : GalilScaffoldPlace.Place)
    (hw : w = (GalilScaffoldPlace.stream p).take (span+1))
    (hr : GalilScaffoldSearchRun.SafeQuanta s x as t y) (hs : s.mode = .run) (ht : t.mode = .found)
    (hv : GalilDpCorrect.Result w lower 0 (GalilScaffoldProgram.denote y.config))
    (ver : PlaceHead) (r0 : ℕ) (dm : Bool) :
    ∃ (h : ℕ) (c : Fin 3) (ys : List (Fin 3)) (b : Fin 3),
      GalilDpCorrect.Candidate w lower h ∧ GalilScaffoldPlace.read p = some c ∧ ys.length + 1 = h ∧
      ∀ (bs cs : List Bool), bs.length = h → cs.length = h+1 →
        ∀ (ch : ChainVM), ChainMatched (chainStart (y.config.tapes 11) c p ver (ofNat (r0+1))) ch →
        ∀ {c0 c1 : Control} {v0 v1 : GalilVM},
          WatchSegE P q first delay (bs ++ dm :: cs) c0 v0 c1 v1 → v0.chain = ch →
          v1.chain = .watch (watchStart ver c ys b (GalilScaffoldChainCredits.run
            (GalilScaffoldChainCredits.start (ofNat (r0+1)))
            (GalilScaffoldChainCredits.prepEvents true dm bs cs))) := by
  obtain ⟨h, c, ys, b, hcand, hread, hlen, hrest⟩ := prep_watch_start_trace p hw hr hs ht hv ver r0 dm
  refine ⟨h, c, ys, b, hcand, hread, hlen, ?_⟩
  intro bs cs hbs hcs ch hch c0 c1 v0 v1 hseg hv0
  have hne : v0.chain ≠ .idle := by
    rw [hv0]; exact chainMatched_chainStart_ne_idle hch
  have hticks := watchSegE_chainTicks P q first delay hseg hne
  rw [hv0] at hticks
  exact hrest bs cs hbs hcs ch v1.chain hch hticks

/-- **`ReplayChainSeg` feeds the trace form too.**  The replay segment with a
live chain — which `WatchSegE` cannot express, since `countR`/`matchIdleR`
both carry `s.chain = .idle` — is now an admissible preparation segment. -/
theorem prep_watch_start_of_replayChainSeg (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    {s t : GalilScaffoldSearchFinish.State} {x y : GalilScaffoldControl.Machine 12}
    {as : List Bool} {w : List (Fin 3)} {lower span : ℕ} (p : GalilScaffoldPlace.Place)
    (hw : w = (GalilScaffoldPlace.stream p).take (span+1))
    (hr : GalilScaffoldSearchRun.SafeQuanta s x as t y) (hs : s.mode = .run) (ht : t.mode = .found)
    (hv : GalilDpCorrect.Result w lower 0 (GalilScaffoldProgram.denote y.config))
    (ver : PlaceHead) (r0 : ℕ) (dm : Bool) :
    ∃ (h : ℕ) (c : Fin 3) (ys : List (Fin 3)) (b : Fin 3),
      GalilDpCorrect.Candidate w lower h ∧ GalilScaffoldPlace.read p = some c ∧ ys.length + 1 = h ∧
      ∀ (bs cs : List Bool), bs.length = h → cs.length = h+1 →
        ∀ (ch : ChainVM), ChainMatched (chainStart (y.config.tapes 11) c p ver (ofNat (r0+1))) ch →
        ∀ {c0 c1 : Control} {v0 v1 : GalilVM},
          PalPeg.GalilReplayChainSeg.ReplayChainSeg P q first delay (bs ++ dm :: cs) c0 v0 c1 v1 →
          v0.chain = ch →
          v1.chain = .watch (watchStart ver c ys b (GalilScaffoldChainCredits.run
            (GalilScaffoldChainCredits.start (ofNat (r0+1)))
            (GalilScaffoldChainCredits.prepEvents true dm bs cs))) := by
  obtain ⟨h, c, ys, b, hcand, hread, hlen, hrest⟩ := prep_watch_start_trace p hw hr hs ht hv ver r0 dm
  refine ⟨h, c, ys, b, hcand, hread, hlen, ?_⟩
  intro bs cs hbs hcs ch hch c0 c1 v0 v1 hseg hv0
  have hne : v0.chain ≠ .idle := by
    rw [hv0]; exact chainMatched_chainStart_ne_idle hch
  have hticks := PalPeg.GalilReplayChainSeg.replayChainSeg_chain P q first delay hseg hne
  rw [hv0] at hticks
  exact hrest bs cs hbs hcs ch v1.chain hch hticks

/-- The `least` variant for replay segments. -/
theorem prep_watch_start_least_of_replayChainSeg (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    {s t : GalilScaffoldSearchFinish.State} {x y : GalilScaffoldControl.Machine 12}
    {as : List Bool} {w : List (Fin 3)} {lower span : ℕ} (p : GalilScaffoldPlace.Place)
    (hw : w = (GalilScaffoldPlace.stream p).take (span+1))
    (hr : GalilScaffoldSearchRun.SafeQuanta s x as t y) (hs : s.mode = .run) (ht : t.mode = .found)
    (hv : GalilDpCorrect.Result w lower 0 (GalilScaffoldProgram.denote y.config))
    (ver : PlaceHead) (r0 : ℕ) (dm : Bool) :
    ∃ (h : ℕ) (c : Fin 3) (ys : List (Fin 3)) (b : Fin 3),
      GalilDpCorrect.Candidate w lower h ∧ GalilScaffoldPlace.read p = some c ∧ ys.length + 1 = h ∧
      (GalilScaffoldProgram.denote y.config).pc = 346 ∧
      (GalilScaffoldProgram.denote y.config).pos 11 = h ∧
      ∀ (bs cs : List Bool), bs.length = h → cs.length = h+1 →
        ∀ (ch : ChainVM), ChainMatched (chainStart (y.config.tapes 11) c p ver (ofNat (r0+1))) ch →
        ∀ {c0 c1 : Control} {v0 v1 : GalilVM},
          PalPeg.GalilReplayChainSeg.ReplayChainSeg P q first delay (bs ++ dm :: cs) c0 v0 c1 v1 →
          v0.chain = ch →
          v1.chain = .watch (watchStart ver c ys b (GalilScaffoldChainCredits.run
            (GalilScaffoldChainCredits.start (ofNat (r0+1)))
            (GalilScaffoldChainCredits.prepEvents true dm bs cs))) := by
  obtain ⟨h, c, ys, b, hcand, hread, hlen, hpc, hcur, hrest⟩ :=
    prep_watch_start_least_trace p hw hr hs ht hv ver r0 dm
  refine ⟨h, c, ys, b, hcand, hread, hlen, hpc, hcur, ?_⟩
  intro bs cs hbs hcs ch hch c0 c1 v0 v1 hseg hv0
  have hne : v0.chain ≠ .idle := by
    rw [hv0]; exact chainMatched_chainStart_ne_idle hch
  have hticks := PalPeg.GalilReplayChainSeg.replayChainSeg_chain P q first delay hseg hne
  rw [hv0] at hticks
  exact hrest bs cs hbs hcs ch v1.chain hch hticks

/-! ## `PreludeEnds` against the trace -/

/-- **`PreludeEnds`, stated against the chain trace.**  `PreludeEnds` quantifies
over a `WatchSegE` and a clock bound, but uses only the induced `ChainTicks`
run of length `2*h + 2` out of the chain start (its suppliers — `copy_run_to_back`,
`back_exact`, `prep_watch_start` — are all trace facts).  This is that
hypothesis with the segment erased. -/
def PreludeEndsT (answer : GalilScaffoldTape.Tape) (cc : Fin 3)
    (walker : GalilScaffoldPlace.Place) (ver : PlaceHead) (radius : Counter) (h : ℕ) : Prop :=
  ∀ {es : List Bool} {x z : ChainVM}, es.length = 2 * h + 2 → ChainTicks es x z →
    x = chainStart answer cc walker ver radius →
    ∃ w : GalilScaffoldChainWatch.State,
      z = .watch w ∧ GalilScaffoldChainWatch.CanonicalState w ∧
        0 ≤ value w.lag ∧ value w.lag ≤ ((2 * h + 2 : ℕ) : ℤ)

/-- The trace form is the stronger hypothesis: it implies `PreludeEnds` for
every controller, clock and place, through `watchSegE_chainTicks`. -/
theorem preludeEnds_of_preludeEndsT (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    {answer : GalilScaffoldTape.Tape} {cc : Fin 3} {walker : GalilScaffoldPlace.Place}
    {ver : PlaceHead} {radius : Counter} {h : ℕ}
    (hT : PreludeEndsT answer cc walker ver radius h) :
    PalPeg.GalilPreludeDone.PreludeEnds P q first delay answer cc walker ver radius h := by
  intro es c0 c1 v0 v1 hlen _ hseg hstart
  have hne : v0.chain ≠ .idle := by rw [hstart]; intro h0; cases h0
  have hticks := watchSegE_chainTicks P q first delay hseg hne
  exact hT hlen hticks hstart

/-- And it applies to a replay segment, which `PreludeEnds` cannot reach. -/
theorem preludeEndsT_replayChainSeg (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    {answer : GalilScaffoldTape.Tape} {cc : Fin 3} {walker : GalilScaffoldPlace.Place}
    {ver : PlaceHead} {radius : Counter} {h : ℕ}
    (hT : PreludeEndsT answer cc walker ver radius h)
    {es : List Bool} {c0 c1 : Control} {v0 v1 : GalilVM} (hlen : es.length = 2 * h + 2)
    (hseg : PalPeg.GalilReplayChainSeg.ReplayChainSeg P q first delay es c0 v0 c1 v1)
    (hstart : v0.chain = chainStart answer cc walker ver radius) :
    ∃ w : GalilScaffoldChainWatch.State,
      v1.chain = .watch w ∧ GalilScaffoldChainWatch.CanonicalState w ∧
        0 ≤ value w.lag ∧ value w.lag ≤ ((2 * h + 2 : ℕ) : ℤ) := by
  have hne : v0.chain ≠ .idle := by rw [hstart]; intro h0; cases h0
  have hticks := PalPeg.GalilReplayChainSeg.replayChainSeg_chain P q first delay hseg hne
  exact hT hlen hticks hstart

#print axioms watchSegE_chainTicks
#print axioms chainMatched_chainStart_ne_idle
#print axioms prep_watch_start_trace
#print axioms prep_watch_start_least_trace
#print axioms prep_watch_start_of_watchSegE
#print axioms prep_watch_start_of_replayChainSeg
#print axioms prep_watch_start_least_of_replayChainSeg
#print axioms preludeEnds_of_preludeEndsT
#print axioms preludeEndsT_replayChainSeg

end PalPeg.GalilScaffoldChainInputSupply
