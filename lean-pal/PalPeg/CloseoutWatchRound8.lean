import PalPeg.CloseoutWatchRound7

/-!
# Round 8: the seven residues of `CloseoutWatchRound7`

Nothing new is *named* here: every statement is either a discharge of a
Round 7 residue, a refutation of one, or a machine fact that isolates exactly
what a residue still needs.

## Discharged (unconditionally, no `sorry`)

* `shiftReachC_holds` — **`CloseoutWatchRound7.ShiftReachC` is trivially true.**
  The predicate asks for *some* `WatchSeg`-reachable landing that is still live
  and still satisfies the exit disjunct; `WatchSeg.stop` at the given landing
  answers it.  So the entire content of §4 of Round 7 sits in `ShiftRoundAtC`.
* `foundRadiusCanonC_of_stage` — **`CloseoutWatchRound7.FoundRadiusCanonC` from
  `CloseoutWatchRound7.FoundStageEntryC`.**  `Restarted` carries
  `RadiusRep r.radius Rad`, whose first component is `Canonical r.radius`, and
  `GalilScaffoldChainInputSupply.watchSegE_heads` already exports
  `Canonical s.radius → Canonical t.radius` along a segment.  One of the seven
  is therefore not independent: it is a consequence of `FoundStageEntryC`.

## Machine facts about the chain along a segment (new, unconditional)

* `chainStep_broken`, `chainMatched_broken_elim` — a broken chain is a sink:
  the only background step out of `.broken w` is `brokenIdle`, and `ChainMatched`
  has **no** constructor at `.broken`, so a matched comparison out of a broken
  chain is impossible.
* `chainTick_false_watch` / `chainTick_watch_cases` — a *disabled* tick keeps a
  watching chain watching; an enabled one keeps it watching **or breaks it**
  (`ChainMatched.breaks`).  These two are the whole chain alphabet of a segment.
* `watchSegE_broken_persists`, `watchSegE_watch_or_broken` — hence from a
  watching chain **every** landing of a `WatchSegE` is watching or broken, and a
  broken one stays broken.
* `watchSegE_watch_of_noMatch` — and it is *watching* as soon as the landing's
  event list has no matched comparison (`es.count true = 0`): `match` and
  `matchIdle` are the only constructors that emit `true`, and the two replay
  constructors need `s.chain = .idle`.

## What that settles about the two "landing" residues

* `prepLandingWatchC_of_noMatch` — **`CloseoutWatchRound7.PrepLandingWatchC`
  follows from a watching start plus "no landing of the preparation segment
  contains a matched comparison"**, which is exactly the shape of
  `CloseoutPrepInputs2.NoCompareInPrepG`.
* `not_prepLandingWatchC_of_idle` — **the unrestricted `PrepLandingWatchC` is
  false** at any idle start: `WatchSegE.stop` is a landing with `es = []`.
  So the predicate silently contains the premise `∃ w, sP.chain = .watch w`,
  which no exit states.
* `prepLandingWatchC_watch_start` — that premise is in fact *equivalent* to the
  `es = []` instance, so `PrepLandingWatchC` = (start watching) + (no break
  before any landing), and by `watchSegE_watch_of_noMatch` the second half is
  implied by the no-comparison delay fit.  **Missing machine fact**: that the
  preparation segment of a found exit really has no matched comparison, i.e.
  that `NoCompareInPrepG` holds at *every* landing and not only at the branch-A
  landing `CloseoutPrepInputs3.prep_of_prepInputsG3` supplies.

* `breakLandingC_start`, `breakLandingC_noMatch`, `breakLandingC_watch_fixed` —
  the same dissection for `CloseoutWatchRound5.BreakLandingC`.  Its `es = []`
  instance pins the start to `GalilNoShiftStage.freshWatch sF.center cen ys b
  sF.radius` with `ys.length + 1 = h` (the `freshWatch_eq` shape), and its
  general instance demands the **same** watch state at every landing.  Since the
  background step at a watching chain is `ChainStep.watchStep`, i.e. an arbitrary
  `GalilScaffoldChainWatch.Internal`, that conjunct asserts that `Internal`
  *stutters* on `freshWatch` for the whole preparation segment.  **Missing
  machine fact (and the reason to doubt the statement as written)**: a stutter
  lemma `Internal (freshWatch …) w' → w' = freshWatch …`; the watch consumes its
  period tape as the scan advances, so `BreakLandingC` is very likely false in
  its present verbatim form and should be weakened to the ledger equations
  (`value lag = value sF.radius`, the `decFour` margin) that
  `GalilNoShiftStage.fresh_break_ledger` actually uses.

## Not settled here — the exact missing fact for each

* `CloseoutWatchRound7.FoundStageEntryC raw c0 r` — **unprovable as stated**, and
  not because of a gap: `r` is universally quantified, so the predicate claims
  every VM is a restart landing of a stage.  It is a *datum*, not a lemma; the
  missing machine fact is the propagation of `StageEntryC.stage`
  (`Restarted` + `StageEntry`) across `replayStage_trans` **to the exit's own**
  `(c0, r)`, which the exit record does not carry.  Any closing of the seven has
  to thread that witness through the exit, not prove it here.
* `CloseoutWatchRound7.FoundIndexAgreeC` — needs the DP's least-candidate indices
  to be the exit's.  `GalilSearchResult.idle_segment_found_quantum` fixes
  `k = value last` and `span = 8 * max k 1` on the first-stage branch and
  `CloseoutPrepInputs3.LaterQuantumC` on the later-stage branch; the
  `pos 11 = h` conjunct is `GalilReplayBudgetProof.answerAhead_eq_head`.  The
  missing machine fact is the **uniqueness** of the `Result` window: `Result
  (stream.take (span'+1)) k 0 dp → k = lower ∧ span' = span`, i.e. that the DP
  configuration determines `(k, span')`.  Nothing in the tree states that.
* `CloseoutWatchRound7.ShiftRoundAtC` — the whole shift round (mismatch, guard,
  `beginShift`, `ChainShiftRun`, `Entry`, `Rounds`, `ScanSeg`, terminal break).
  `CloseoutWatchRound5.shiftTick_of_roundData` only certifies the *tick*; the
  missing machine fact is the post-shift run itself, i.e. a `Rounds`/`ScanSeg`
  construction out of `shiftLens.set s2' ⟨t', .watch v, cycle⟩` — the analogue
  of `CloseoutWatchRun.watchRun_of_distance` for a shifted chain, which does not
  exist.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutWatchRound8

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.CloseoutContracts
open PalPeg.GalilRunSkeleton
open PalPeg.CloseoutWatchRun (LiveScanWatch roundFuel)
open PalPeg.CloseoutWatchRound7 (ShiftReachC FoundStageEntryC FoundRadiusCanonC
  PrepLandingWatchC)

/-! ## 1. `ShiftReachC` is trivially true -/

/-- **Discharged — `CloseoutWatchRound7.ShiftReachC`.**  It asks only for *a*
`WatchSeg`-reachable live landing that still satisfies the exit disjunct, and
`WatchSeg.stop` is one.  The reduction `shiftRoundC_of_parts` of Round 7 is
therefore a reduction of `ShiftRoundC` to `ShiftRoundAtC` alone. -/
theorem shiftReachC_holds (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (h : ℕ) :
    ShiftReachC centre place entry qq first raw h := by
  intro cT sT hL hexit
  exact ⟨cT, sT, .stop cT sT, hL, hexit⟩

#print axioms shiftReachC_holds

/-! ## 2. `FoundRadiusCanonC` is a consequence of `FoundStageEntryC` -/

open PalPeg.GalilScaffoldChainInputSupply (Restarted StageEntry watchSegE_heads)

/-- **Discharged — `CloseoutWatchRound7.FoundRadiusCanonC` from
`CloseoutWatchRound7.FoundStageEntryC`.**  `Restarted` carries
`RadiusRep r.radius Rad`, i.e. `Canonical r.radius`, and `watchSegE_heads`
propagates canonicity along the segment (the only radius moves are `inc`). -/
theorem foundRadiusCanonC_of_stage (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) {c0 : Control} {r : GalilVM}
    (hstage : FoundStageEntryC raw c0 r) :
    FoundRadiusCanonC centre place entry qq first raw c0 r := by
  intro es0 cF sF hseg
  obtain ⟨Rad, last, hR, hcl, hSt⟩ := hstage
  obtain ⟨-, -, -, -, ⟨hrc, -⟩, -⟩ := hR
  obtain ⟨-, -, -, hcan, -⟩ := watchSegE_heads (PofC centre place entry raw) qq first 2048 hseg
  exact hcan hrc

#print axioms foundRadiusCanonC_of_stage

/-! ## 3. The chain alphabet of a segment -/

/-- A broken chain is a background sink. -/
theorem chainStep_broken {w : GalilScaffoldChainWatch.State} {z : ChainVM}
    (h : ChainStep (.broken w) z) : z = .broken w := by
  cases h; rfl

/-- `ChainMatched` has no constructor at a broken chain. -/
theorem chainMatched_broken_elim {w : GalilScaffoldChainWatch.State} {z : ChainVM}
    (h : ChainMatched (.broken w) z) : False := by
  cases h

/-- A disabled tick keeps a watching chain watching. -/
theorem chainTick_false_watch {w : GalilScaffoldChainWatch.State} {z : ChainVM}
    (h : ChainTick false (.watch w) z) : ∃ w' : GalilScaffoldChainWatch.State, z = .watch w' := by
  obtain ⟨y, hstep, hz⟩ := h
  simp only [Bool.false_eq_true, if_false] at hz
  cases hstep with
  | watchStep w w' hi => exact ⟨w', hz⟩

/-- An enabled tick keeps a watching chain watching or breaks it. -/
theorem chainTick_watch_cases {a : Bool} {w : GalilScaffoldChainWatch.State} {z : ChainVM}
    (h : ChainTick a (.watch w) z) :
    (∃ w' : GalilScaffoldChainWatch.State, z = .watch w') ∨
      (∃ w' : GalilScaffoldChainWatch.State, z = .broken w') := by
  obtain ⟨y, hstep, hz⟩ := h
  cases hstep with
  | watchStep w w' hi =>
    cases a with
    | false =>
      simp only [Bool.false_eq_true, if_false] at hz
      exact Or.inl ⟨w', hz⟩
    | true =>
      simp only [if_true] at hz
      cases hz with
      | watch _ w'' ho => exact Or.inl ⟨w'', rfl⟩
      | breaks _ w'' hb => exact Or.inr ⟨w'', rfl⟩

/-- A disabled tick keeps a broken chain broken. -/
theorem chainTick_false_broken {w : GalilScaffoldChainWatch.State} {z : ChainVM}
    (h : ChainTick false (.broken w) z) : z = .broken w := by
  obtain ⟨y, hstep, hz⟩ := h
  simp only [Bool.false_eq_true, if_false] at hz
  rw [hz]; exact chainStep_broken hstep

/-- A broken chain cannot take a matched comparison. -/
theorem chainTick_true_broken_elim {w : GalilScaffoldChainWatch.State} {z : ChainVM}
    (h : ChainTick true (.broken w) z) : False := by
  obtain ⟨y, hstep, hz⟩ := h
  simp only [if_true] at hz
  rw [chainStep_broken hstep] at hz
  exact chainMatched_broken_elim hz

#print axioms chainTick_watch_cases
#print axioms chainTick_true_broken_elim

/-! ## 4. Landings of a segment out of a watching chain -/

/-- The matched-comparison event of the `match` constructor is a real match of
the heads; the private repetition of the two-line derivation used throughout
`GalilScaffoldTopSegmentHeads`. -/
theorem compare_heads_match (P : Shared) (q : ℕ) (first : Fin 9) {s : GalilVM} {vs : ScanVM}
    (hcmp : (galilFrame P q first).compare s (scanLens.set s vs))
    (hmt : (galilFrame P q first).matched (scanLens.set s vs)) :
    read (left s.left) = read (right s.right) := by
  obtain ⟨⟨hl0, hr0, -⟩, -⟩ := hcmp
  rw [scanLens.get_set] at hl0 hr0
  have h := matched_parts P q first hmt
  rw [hl0, hr0] at h
  exact h

/-- **A broken chain persists to every landing.** -/
theorem watchSegE_broken_persists (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    {es : List Bool} {c c' : Control} {s t : GalilVM}
    (hseg : WatchSegE P q first delay es c s c' t) :
    (∃ w : GalilScaffoldChainWatch.State, s.chain = .broken w) →
      ∃ w : GalilScaffoldChainWatch.State, t.chain = .broken w := by
  induction hseg with
  | stop c s => exact id
  | wait c s s' hm hr hn hb rest ih =>
      rintro ⟨w, hw⟩
      have hne : s.chain ≠ .idle := by rw [hw]; exact fun h => by cases h
      have ht := backgroundS_chainTick P q first hb hne
      rw [hw] at ht
      exact ih ⟨w, chainTick_false_broken ht⟩
  | count c s s' hm hr ha hc hb rest ih =>
      rintro ⟨w, hw⟩
      have hne : s.chain ≠ .idle := by rw [hw]; exact fun h => by cases h
      have ht := backgroundS_chainTick P q first hb hne
      rw [hw] at ht
      exact ih ⟨w, chainTick_false_broken ht⟩
  | «match» c s vs vq o hm hr ha hc hne hcmp hmt hq ho rest ih =>
      rintro ⟨w, hw⟩
      obtain ⟨-, -, htk⟩ := compare_parts P q first hcmp (compare_heads_match P q first hcmp hmt)
      rw [hw] at htk
      exact absurd htk (fun h => chainTick_true_broken_elim h)
  | matchIdle c s vs vq o hm hr ha hc hidle hl hrr hvs hmt hq hnf ho rest ih =>
      rintro ⟨w, hw⟩; rw [hidle] at hw; cases hw
  | countR c s s' hm hr hc hidle hb rest ih =>
      rintro ⟨w, hw⟩; rw [hidle] at hw; cases hw
  | matchIdleR c s vs vq o hm hr hc ha hidle hl hrr hvs hmt hq hnf ho rest ih =>
      rintro ⟨w, hw⟩; rw [hidle] at hw; cases hw

/-- **Every landing out of a watching chain is watching or broken.**  This is
the unconditional half of `PrepLandingWatchC`. -/
theorem watchSegE_watch_or_broken (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    {es : List Bool} {c c' : Control} {s t : GalilVM}
    (hseg : WatchSegE P q first delay es c s c' t) :
    (∃ w : GalilScaffoldChainWatch.State, s.chain = .watch w) →
      (∃ w : GalilScaffoldChainWatch.State, t.chain = .watch w) ∨
        (∃ w : GalilScaffoldChainWatch.State, t.chain = .broken w) := by
  induction hseg with
  | stop c s => exact Or.inl
  | wait c s s' hm hr hn hb rest ih =>
      rintro ⟨w, hw⟩
      have hne : s.chain ≠ .idle := by rw [hw]; exact fun h => by cases h
      have ht := backgroundS_chainTick P q first hb hne
      rw [hw] at ht
      exact ih (chainTick_false_watch ht)
  | count c s s' hm hr ha hc hb rest ih =>
      rintro ⟨w, hw⟩
      have hne : s.chain ≠ .idle := by rw [hw]; exact fun h => by cases h
      have ht := backgroundS_chainTick P q first hb hne
      rw [hw] at ht
      exact ih (chainTick_false_watch ht)
  | «match» c s vs vq o hm hr ha hc hne hcmp hmt hq ho rest ih =>
      rintro ⟨w, hw⟩
      obtain ⟨-, -, htk⟩ := compare_parts P q first hcmp (compare_heads_match P q first hcmp hmt)
      rw [hw] at htk
      have hch : (afterCompare s vs vq).chain = vs.chain := afterCompare_chain s vs vq
      rcases chainTick_watch_cases htk with ⟨w', hw'⟩ | ⟨w', hw'⟩
      · exact ih ⟨w', by rw [hch, hw']⟩
      · exact Or.inr (watchSegE_broken_persists P q first delay rest ⟨w', by rw [hch, hw']⟩)
  | matchIdle c s vs vq o hm hr ha hc hidle hl hrr hvs hmt hq hnf ho rest ih =>
      rintro ⟨w, hw⟩; rw [hidle] at hw; cases hw
  | countR c s s' hm hr hc hidle hb rest ih =>
      rintro ⟨w, hw⟩; rw [hidle] at hw; cases hw
  | matchIdleR c s vs vq o hm hr hc ha hidle hl hrr hvs hmt hq hnf ho rest ih =>
      rintro ⟨w, hw⟩; rw [hidle] at hw; cases hw

/-- **A landing whose event list has no matched comparison is watching.**  The
only constructors that emit `true` are `match`, `matchIdle` and `matchIdleR`,
and the last two need `s.chain = .idle`; so `es.count true = 0` rules out the
one constructor (`match`) that can break the chain. -/
theorem watchSegE_watch_of_noMatch (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    {es : List Bool} {c c' : Control} {s t : GalilVM}
    (hseg : WatchSegE P q first delay es c s c' t) :
    es.count true = 0 → (∃ w : GalilScaffoldChainWatch.State, s.chain = .watch w) →
      ∃ w : GalilScaffoldChainWatch.State, t.chain = .watch w := by
  induction hseg with
  | stop c s => intro _ h; exact h
  | wait c s s' hm hr hn hb rest ih =>
      rintro hz ⟨w, hw⟩
      have hne : s.chain ≠ .idle := by rw [hw]; exact fun h => by cases h
      have ht := backgroundS_chainTick P q first hb hne
      rw [hw] at ht
      refine ih ?_ (chainTick_false_watch ht)
      simp only [List.count_cons] at hz; omega
  | count c s s' hm hr ha hc hb rest ih =>
      rintro hz ⟨w, hw⟩
      have hne : s.chain ≠ .idle := by rw [hw]; exact fun h => by cases h
      have ht := backgroundS_chainTick P q first hb hne
      rw [hw] at ht
      refine ih ?_ (chainTick_false_watch ht)
      simp only [List.count_cons] at hz; omega
  | «match» c s vs vq o hm hr ha hc hne hcmp hmt hq ho rest ih =>
      intro hz _
      simp at hz
  | matchIdle c s vs vq o hm hr ha hc hidle hl hrr hvs hmt hq hnf ho rest ih =>
      rintro _ ⟨w, hw⟩; rw [hidle] at hw; cases hw
  | countR c s s' hm hr hc hidle hb rest ih =>
      rintro _ ⟨w, hw⟩; rw [hidle] at hw; cases hw
  | matchIdleR c s vs vq o hm hr hc ha hidle hl hrr hvs hmt hq hnf ho rest ih =>
      rintro _ ⟨w, hw⟩; rw [hidle] at hw; cases hw

#print axioms watchSegE_watch_or_broken
#print axioms watchSegE_watch_of_noMatch

/-! ## 5. `PrepLandingWatchC`: its exact content -/

/-- **`PrepLandingWatchC` forces a watching start.**  Its `es = []` instance
(`WatchSegE.stop`) *is* `∃ w, sP.chain = .watch w`. -/
theorem prepLandingWatchC_watch_start (P : Shared) (q : ℕ) (first : Fin 9)
    {cP : Control} {sP : GalilVM} (h : PrepLandingWatchC P q first cP sP) :
    ∃ w : GalilScaffoldChainWatch.State, sP.chain = .watch w :=
  h [] cP sP (.stop cP sP)

/-- **Refutation — the unrestricted `PrepLandingWatchC` is false at an idle
start.**  So the predicate carries an unstated premise. -/
theorem not_prepLandingWatchC_of_idle (P : Shared) (q : ℕ) (first : Fin 9)
    {cP : Control} {sP : GalilVM} (hidle : sP.chain = .idle) :
    ¬ PrepLandingWatchC P q first cP sP := by
  intro h
  obtain ⟨w, hw⟩ := prepLandingWatchC_watch_start P q first h
  rw [hidle] at hw
  cases hw

/-- **Discharged modulo the no-comparison fit — `PrepLandingWatchC`.**  The
second hypothesis is the universal form of `CloseoutPrepInputs2.NoCompareInPrepG`:
no landing of the preparation segment contains a matched comparison.  This is
the only machine fact `PrepLandingWatchC` still needs. -/
theorem prepLandingWatchC_of_noMatch (P : Shared) (q : ℕ) (first : Fin 9)
    {cP : Control} {sP : GalilVM}
    (hstart : ∃ w : GalilScaffoldChainWatch.State, sP.chain = .watch w)
    (hno : ∀ (es : List Bool) (c2 : Control) (s2 : GalilVM),
      WatchSegE P q first 2048 es cP sP c2 s2 → es.count true = 0) :
    PrepLandingWatchC P q first cP sP := by
  intro es c2 s2 hseg
  exact watchSegE_watch_of_noMatch P q first 2048 hseg (hno es c2 s2 hseg) hstart

#print axioms not_prepLandingWatchC_of_idle
#print axioms prepLandingWatchC_of_noMatch

/-! ## 6. `CloseoutWatchRound5.BreakLandingC`: its exact content -/

open PalPeg.CloseoutWatchRound5 (BreakLandingC)
open PalPeg.GalilNoShiftStage (freshWatch)

/-- **The `es = []` instance of `BreakLandingC` is the `freshWatch_eq` shape at
the start.** -/
theorem breakLandingC_start (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (h : ℕ) (sF : GalilVM) {cP : Control} {sP : GalilVM}
    (hB : BreakLandingC centre place entry qq first raw h sF cP sP) :
    ∃ (cen : Fin 3) (ys : List (Fin 3)) (b : Fin 3),
      ys.length + 1 = h ∧ sP.chain = ChainVM.watch (freshWatch sF.center cen ys b sF.radius) := by
  obtain ⟨cen, ys, b, hlen, hch, -⟩ := hB [] cP sP (.stop cP sP)
  exact ⟨cen, ys, b, hlen, hch⟩

/-- **`BreakLandingC` asserts that no landing contains a matched comparison.**
This half is exactly the `NoCompareInPrepG` delay fit, and by
`watchSegE_watch_of_noMatch` it already gives the *watching* conjunct. -/
theorem breakLandingC_noMatch (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (h : ℕ) (sF : GalilVM) {cP : Control} {sP : GalilVM}
    (hB : BreakLandingC centre place entry qq first raw h sF cP sP) :
    ∀ (es : List Bool) (c2 : Control) (s2 : GalilVM),
      WatchSegE (PofC centre place entry raw) qq first 2048 es cP sP c2 s2 → es.count true = 0 :=
  fun es c2 s2 hseg => by
    obtain ⟨cen, ys, b, -, -, hz⟩ := hB es c2 s2 hseg
    exact hz

/-- **The residual half of `BreakLandingC` is a stutter claim.**  Beyond the
start shape and the no-comparison fit, all it says is that the watch state at
every landing is *syntactically the same* `freshWatch …`.  Since the only
background move of a watching chain is `ChainStep.watchStep`, i.e. an arbitrary
`GalilScaffoldChainWatch.Internal`, this is the assertion that `Internal`
stutters on `freshWatch` for the whole preparation segment — a machine fact that
does not exist in the tree, and one the consuming watch makes doubtful. -/
theorem breakLandingC_watch_fixed (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (h : ℕ) (sF : GalilVM) {cP : Control} {sP : GalilVM}
    (hB : BreakLandingC centre place entry qq first raw h sF cP sP)
    {es : List Bool} {c2 : Control} {s2 : GalilVM}
    (hseg : WatchSegE (PofC centre place entry raw) qq first 2048 es cP sP c2 s2) :
    ∃ (cen : Fin 3) (ys : List (Fin 3)) (b : Fin 3),
      ys.length + 1 = h ∧
      s2.chain = ChainVM.watch (freshWatch sF.center cen ys b sF.radius) := by
  obtain ⟨cen, ys, b, hlen, hch, -⟩ := hB es c2 s2 hseg
  exact ⟨cen, ys, b, hlen, hch⟩

#print axioms breakLandingC_start
#print axioms breakLandingC_noMatch
#print axioms breakLandingC_watch_fixed

end PalPeg.CloseoutWatchRound8
