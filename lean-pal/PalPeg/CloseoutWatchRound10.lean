import PalPeg.CloseoutWatchRound8

/-!
# Round 10: the four missing facts named by `CloseoutWatchRound8`

Each section attacks one of the four residues the Round 8 docstring isolates.

## (a) `NoCompareInPrepG` at *every* landing

* `watchSegE_noCompare_of_short` — **unconditional**: a `WatchSegE` shorter than
  the controller's clock contains **no** matched comparison.  Every `true` event
  needs `c.clock = 1` (`match`, `matchIdle`, `matchIdleR`), `wait` leaves the
  clock alone and `count`/`countR` decrement it by one, so reaching a comparison
  costs at least `c.clock` events.
* `noCompareInPrepG_of_short` — hence `CloseoutPrepInputs2.NoCompareInPrepG` at
  a landing follows from a *length* bound on the landings, and at `clock = 2048`
  the intended instance `2*h+2 < 2048` is exactly that bound.
  **Missing machine fact**: that every landing of the preparation segment has
  `es.length ≤ 2*h+2` (branch A of `CloseoutPrepInputs3.prep_of_prepInputsG3`
  supplies one landing, not all of them).

## (b) `BreakLandingC` weakened to the ledger

* `margin_false_of_run` — `CloseoutWatchRound5.margin_false_of_fuel` with the
  verbatim landing `s2.chain = .watch (freshWatch …)` **replaced by the ledger
  datum** `s2.chain = .watch w2` together with *any* `Run (freshWatch …) es' w2`.
  `run_of_watchSeg` + `run_append` glue the two runs, and
  `fresh_margin_false_of_places` only ever needed the composite run.
* `BreakLandingLedgerC`, `breakLandingLedgerC_of_breakLandingC` — the weakened
  landing predicate and the (trivial) fact that the verbatim one implies it.
* **Re-exported** (this round): the family is now weakened from the top.
  `CloseoutWatchPhase3.NoShiftTailC0L` is `NoShiftTailC0` over the ledger
  landing, `CloseoutWatchPhase3.foundRouteMC_noshift_L` re-proves
  `GalilNoShiftStage.foundRouteMC_noshift'` over it (the two watch runs compose,
  and the extra background ticks carry no `true`, so `fresh_break_ledger`'s
  `distance = radius + 1 + #matched` and `distance = 4h + margin` are unchanged),
  and `breakRouteLPraw_of_tail0L` gives the raw break route.  Here
  `BreakExitTailLC` / `breakExitTailLC_of_parts` / `breakRouteLPraw_of_ledger_parts`
  rebuild `CloseoutWatchRound5.breakExitTailC_of_parts` over
  `BreakLandingLedgerC`, with `margin_false_of_run` in place of
  `margin_false_of_fuel`.  The stutter lemma `Internal (freshWatch …) w' → w' =
  freshWatch …` is **not** needed anywhere and is still believed false.

## (c) `FoundStageEntryC` replaced by a witness the exit does carry

* `foundDp_core_of_replayStage`, `foundDpShiftC_of_at`, `foundDpBreakC_of_at`,
  `foundRadiusCanonC_of_replayStage` — **`CloseoutWatchRound7.FoundStageEntryC`
  is not needed**: the weaker `GalilFoundStage.ReplayStage raw P qq first c0 r`,
  which *is* what `GalilFoundStageInv.replayStage_trans` propagates to the exit,
  suffices.  Its own stage entry `(c0', r')` sits before `(c0, r)` by a
  `WatchSegE`, and `watchSegE_trans` composes that prefix with the exit's
  segment, so `foundDp_core` applies at the genuine stage entry.  This closes
  the Round 8 residue "the exit record does not carry the witness": it carries
  `ReplayStage`, and `ReplayStage` is enough.

## (d) the DP window: what is and is not determined

* `result_pos_eq`, `result_index_unique`, `result_pc_cases`,
  `result_not_found_of_pc` — the *found index* of a `Result` is `y.pos 11`, so
  it is determined by the DP configuration alone, for **any** `w`, `lower`,
  `first`.  The two disjuncts are separated by `pc` (`346` vs `347`).
* `candidate_antitone` — **but the `lower` slot is not determined**:
  `Candidate w lower h` only asks `lower < h` of `lower`, so it survives every
  decrease of `lower`.  The uniqueness `Result (stream.take (span'+1)) k 0 dp →
  k = lower ∧ span' = span` demanded by `CloseoutWatchRound7.FoundIndexAgreeC`
  is therefore **not** a property of `Result`; only the minimality clause
  constrains `lower` at all, and nothing constrains `span'`.
* `FoundDpAtC`, `foundDpAtC_of_indexAgree`, `foundDpShiftC_of_at`,
  `foundDpBreakC_of_at` — the repair: state the DP record **at the exit's own
  indices** instead of proving uniqueness.  `FoundDpAtC` is implied by
  `FoundIndexAgreeC` (via the same `vq`, as Round 8 suggested) and discharges
  both `FoundDpShiftC` and `FoundDpBreakC` on its own, with `pc = 346` coming
  from `foundDp_core`.  No window uniqueness is used anywhere.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutWatchRound10

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.CloseoutContracts
open PalPeg.GalilRunSkeleton
open PalPeg.CloseoutWatchRun (LiveScanWatch roundFuel)
open PalPeg.GalilFoundStage (ReplayStage)
open PalPeg.GalilNoShiftStage (freshWatch)

/-! ## (a) No matched comparison inside a short segment -/

/-- **Unconditional — a segment shorter than the clock has no comparison.**
Every `true` event is emitted by `match`, `matchIdle` or `matchIdleR`, each of
which demands `c.clock = 1`; `wait` leaves the clock unchanged and
`count`/`countR` decrement it by exactly one.  So a matched comparison costs at
least `c.clock` events. -/
theorem watchSegE_noCompare_of_short (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    {es : List Bool} {c c' : Control} {s t : GalilVM}
    (h : WatchSegE P q first delay es c s c' t) :
    es.length < c.clock → es.count true = 0 := by
  induction h with
  | stop c s => intro _; simp
  | wait c s s' hm hr hn hb rest ih =>
      intro hlen
      simp only [List.length_cons] at hlen
      have hcount := ih (by omega)
      simpa [List.count_cons] using hcount
  | count c s s' hm hr ha hc hb rest ih =>
      intro hlen
      simp only [List.length_cons] at hlen
      have hcount := ih (by show _ < c.clock - 1; omega)
      simpa [List.count_cons] using hcount
  | «match» c s vs vq o hm hr ha hc hne hcmp hmt hq ho rest ih =>
      intro hlen
      simp only [List.length_cons] at hlen
      exfalso; omega
  | matchIdle c s vs vq o hm hr ha hc hidle hl hrr hvs hmt hq hnf ho rest ih =>
      intro hlen
      simp only [List.length_cons] at hlen
      exfalso; omega
  | countR c s s' hm hr hc hidle hb rest ih =>
      intro hlen
      simp only [List.length_cons] at hlen
      have hcount := ih (by show _ < c.clock - 1; omega)
      simpa [List.count_cons] using hcount
  | matchIdleR c s vs vq o hm hr hc ha hidle hl hrr hvs hmt hq hnf ho rest ih =>
      intro hlen
      simp only [List.length_cons] at hlen
      exfalso; omega

#print axioms watchSegE_noCompare_of_short

/-- **`CloseoutPrepInputs2.NoCompareInPrepG` from a landing-length bound.**  At
`cP.clock = 2048` the intended fit `2*h+2 < 2048` is exactly this bound. -/
theorem noCompareInPrepG_of_short (P : Shared) (q : ℕ) (first : Fin 9)
    {cP : Control} {sP : GalilVM}
    (hb : ∀ (es : List Bool) (c2 : Control) (s2 : GalilVM),
      WatchSegE P q first 2048 es cP sP c2 s2 → es.length < cP.clock) :
    PalPeg.CloseoutPrepInputs2.NoCompareInPrepG P q first cP sP := by
  intro es c2 s2 hseg
  exact watchSegE_noCompare_of_short P q first 2048 hseg (hb es c2 s2 hseg)

/-- The same bound therefore also gives Round 8's `PrepLandingWatchC` out of a
watching start. -/
theorem prepLandingWatchC_of_short (P : Shared) (q : ℕ) (first : Fin 9)
    {cP : Control} {sP : GalilVM}
    (hstart : ∃ w : GalilScaffoldChainWatch.State, sP.chain = ChainVM.watch w)
    (hb : ∀ (es : List Bool) (c2 : Control) (s2 : GalilVM),
      WatchSegE P q first 2048 es cP sP c2 s2 → es.length < cP.clock) :
    PalPeg.CloseoutWatchRound7.PrepLandingWatchC P q first cP sP :=
  PalPeg.CloseoutWatchRound8.prepLandingWatchC_of_noMatch P q first hstart
    (fun es c2 s2 hseg => watchSegE_noCompare_of_short P q first 2048 hseg (hb es c2 s2 hseg))

#print axioms noCompareInPrepG_of_short
#print axioms prepLandingWatchC_of_short

/-! ## (b) The break landing in ledger form -/

open PalPeg.CloseoutWatchRound3 (CompareKeepsWatchC DistanceNonnegC)
open PalPeg.CloseoutWatchRun (places_of_fuel_zero)
open PalPeg.CloseoutWatchRound5 (run_append run_of_watchSeg
  fresh_margin_false_of_places breakStep_at_terminal)

/-- **`margin_false_of_fuel` over the ledger landing.**  The verbatim landing
`s2.chain = .watch (freshWatch …)` is replaced by "the landing's watch state is
*reachable* from the fresh watch by some run", which is what
`GalilNoShiftStage.fresh_break_ledger` actually consumes. -/
theorem margin_false_of_run (P : Shared) (q : ℕ) (first : Fin 9)
    (hkeep : CompareKeepsWatchC P q first) (hnn : DistanceNonnegC)
    (ver : GalilScaffoldInputHead.PlaceHead) (cen : Fin 3) (ys : List (Fin 3)) (b : Fin 3)
    (radius : Counter) (hrc : Canonical radius)
    {c2 c3 : Control} {s2 s3 : GalilVM} {vs3 : ScanVM} {vq3 : SearchVM}
    {w2 w3 w3' : GalilScaffoldChainWatch.State} {es' : List Bool}
    (hlanding : s2.chain = ChainVM.watch w2)
    (hrun0 : GalilScaffoldChainWatch.Run (freshWatch ver cen ys b radius) es' w2)
    (hseg : WatchSeg P q first 2048 c2 s2 c3 s3)
    (hs3 : s3.chain = ChainVM.watch w3)
    (hz3 : GalilScaffoldCounter.zero w3.lag = true)
    (hcmp : (galilFrame P q first).compare s3 (scanLens.set s3 vs3))
    (hmt : (galilFrame P q first).matched (scanLens.set s3 vs3))
    (hbroken : (afterCompare s3 vs3 vq3).chain = ChainVM.broken w3')
    (hz : zero w3.lag = true)
    (hfuel : roundFuel (ys.length + 1) s3 = 0) :
    negative w3'.margin = false := by
  obtain ⟨es, w1, hend, hrun⟩ := run_of_watchSeg P q first hkeep hseg _ hlanding
  have hw1 : w1 = w3 := by
    rw [hs3] at hend
    injection hend with hinj
    exact hinj.symm
  subst hw1
  have hbr := breakStep_at_terminal P q first hs3 hz hcmp hmt hbroken
  have hplaces : 4 * ((ys.length : ℤ) + 1) ≤ value w1.machine.control.distance := by
    have hp := places_of_fuel_zero (ys.length + 1) hs3
      (hnn s3 w1 hs3) hfuel
    push_cast at hp ⊢; linarith
  exact fresh_margin_false_of_places ver cen ys b radius hrc (run_append hrun0 hrun) hbr hplaces

#print axioms margin_false_of_run

/-- **The ledger weakening of `CloseoutWatchRound5.BreakLandingC`.**  The
landing's watch state need only be *reachable* from the fresh watch, not equal
to it. -/
def BreakLandingLedgerC (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (h : ℕ) (sF : GalilVM) (cP : Control) (sP : GalilVM) : Prop :=
  ∀ (es : List Bool) (c2 : Control) (s2 : GalilVM),
    WatchSegE (PofC centre place entry raw) qq first 2048 es cP sP c2 s2 →
    (∃ wLive : GalilScaffoldChainWatch.State, s2.chain = ChainVM.watch wLive) →
      ∃ (cen : Fin 3) (ys : List (Fin 3)) (b : Fin 3)
        (w2 : GalilScaffoldChainWatch.State) (es' : List Bool),
        ys.length + 1 = h ∧ s2.chain = ChainVM.watch w2 ∧
        GalilScaffoldChainWatch.Run (freshWatch sF.center cen ys b sF.radius) es' w2 ∧
        es'.count true = 0 ∧
        es.count true = 0

/-- The verbatim landing implies the ledger landing (`Run.stop`). -/
theorem breakLandingLedgerC_of_breakLandingC (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (h : ℕ) (sF : GalilVM) {cP : Control} {sP : GalilVM}
    (hB : PalPeg.CloseoutWatchRound5.BreakLandingC centre place entry qq first raw h sF cP sP) :
    BreakLandingLedgerC centre place entry qq first raw h sF cP sP := by
  intro es c2 s2 hseg hwLanding
  obtain ⟨cen, ys, b, hys, hwatch, hes⟩ := hB es c2 s2 hseg hwLanding
  exact ⟨cen, ys, b, _, [], hys, hwatch, .stop _, by simp, hes⟩

#print axioms breakLandingLedgerC_of_breakLandingC


/-! ### (b′) The break tail over the ledger landing -/

open PalPeg.CloseoutWatchPhase3 (NoShiftTailC0L)
open PalPeg.CloseoutWatchRound2 (FoundCompareCtxC)
open PalPeg.CloseoutWatchRound3 (TerminalRunBreakC)
open PalPeg.CloseoutWatchRound5 (PrepLandingLiveC FoundDpBreakC BreakTerminalC)
open PalPeg.CloseoutWatchRun (watchSeg_append)

/-- **NAMED (open) — the break tail alone, over the ledger landing.**
`CloseoutWatchRound3.BreakExitTailC` with `CloseoutWatchPhase3.NoShiftTailC0`
replaced by the ledger form `NoShiftTailC0L`. -/
def BreakExitTailLC (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m h : ℕ) (c0 : Control) (r : GalilVM)
    (cP : Control) (sP : GalilVM) : Prop :=
  FoundCompareCtxC centre place entry qq first raw c0 r cP sP →
    TerminalRunBreakC (PofC centre place entry raw) qq first h cP sP →
      NoShiftTailC0L centre place entry qq first raw m c0 r cP sP

/-- **Derived — `CloseoutWatchRound5.breakExitTailC_of_parts` over the ledger.**
The verbatim landing `BreakLandingC` is replaced by `BreakLandingLedgerC`, and
the margin conjunct by `margin_false_of_run` instead of `margin_false_of_fuel`.
Nothing else changes: the preparation may consume its period tape. -/
theorem breakExitTailLC_of_parts (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m h lower span : ℕ) {c0 cP : Control} {r sP : GalilVM}
    (hkeep : CompareKeepsWatchC (PofC centre place entry raw) qq first)
    (hnn : DistanceNonnegC)
    (hdp : FoundDpBreakC centre place entry qq first raw lower span h c0 r)
    (hland : ∀ sF : GalilVM, BreakLandingLedgerC centre place entry qq first raw h sF cP sP)
    (hterm : BreakTerminalC centre place entry qq first raw m h) :
    BreakExitTailLC centre place entry qq first raw m h c0 r cP sP := by
  intro hctx hrun
  obtain ⟨es0, cF, sF, vq, ch, oF, a, ls, rs, qw, gap, hraw, hseg0, hmF, hrF, hcF, havF,
    hidle, hCen, hq, hfound, hmt, hch, hchne, hoF, hcPeq, hsPeq⟩ := hctx
  obtain ⟨hcand, hpr, hrc⟩ := hdp a ls rs qw gap es0 cF sF vq hseg0 hCen hq hfound
  refine ⟨es0, cF, sF, vq, ch, oF, a, ls, rs, qw, gap, span, lower, h, hraw, hCen, hpr, hcand,
    hseg0, hmF, hrF, hcF, havF, hidle, hq, hfound, hmt, hch, hchne, hoF, hcPeq, hsPeq, ?_⟩
  intro es c2 s2 hseg hwLanding
  obtain ⟨cen, ys, b, w2, es', hys, hwatch2, hrun0, hes', hes0⟩ := hland sF es c2 s2 hseg hwLanding
  obtain ⟨hmL, hrL, hcL⟩ := watchSegE_live_control (delay := 2048) (by omega) hseg
    (by rw [hcPeq]; exact hmF) (by rw [hcPeq]) (by simp [hcPeq])
  obtain ⟨cT, sT, hsegT, hLT, hexit⟩ :=
    hrun es c2 s2 hseg ⟨hmL, hrL, hcL, hwLanding⟩
  obtain ⟨c3, s3, w3, vs3, vq3, o3, w3', hsegR, hm3, hr3, hc3, hs3, hav3, hcmp3, hmt3, hq3,
    ho3, hbroken, hz3, hfuel, hbound⟩ := hterm cT sT hLT hexit
  have hmargin : negative w3'.margin = false :=
    margin_false_of_run (PofC centre place entry raw) qq first hkeep hnn sF.center cen ys b
      sF.radius hrc hwatch2 hrun0 (watchSeg_append hsegT hsegR) hs3 hcmp3 hmt3 hbroken hz3
      (by rw [hys]; exact hfuel)
  exact ⟨cen, ys, b, w2, es', c3, s3, w3, vs3, vq3, o3, w3', hys, hwatch2, hrun0, hes', hes0,
    watchSeg_append hsegT hsegR, hm3, hr3, hc3, hs3, hav3, hcmp3, hmt3, hq3, ho3, hbroken,
    hmargin, hbound⟩

/-- **Derived — the raw break route straight from the ledger parts.** -/
theorem breakRouteLPraw_of_ledger_parts (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m h lower span : ℕ)
    (hex : ∀ s, (PofC centre place entry raw).replayExhausted s = zero s.replay)
    {c0 cP : Control} {r sP : GalilVM}
    (hE : StageEntryC (PofC centre place entry raw) qq first raw c0 r)
    (hkeep : CompareKeepsWatchC (PofC centre place entry raw) qq first)
    (hnn : DistanceNonnegC)
    (hdp : FoundDpBreakC centre place entry qq first raw lower span h c0 r)
    (hland : ∀ sF : GalilVM, BreakLandingLedgerC centre place entry qq first raw h sF cP sP)
    (hterm : BreakTerminalC centre place entry qq first raw m h)
    (hctx : FoundCompareCtxC centre place entry qq first raw c0 r cP sP)
    (hrun : TerminalRunBreakC (PofC centre place entry raw) qq first h cP sP) :
    PalPeg.CloseoutWatchPhase2.BreakRouteLPraw (PofC centre place entry raw) qq first raw m
      c0 r cP sP :=
  PalPeg.CloseoutWatchPhase3.breakRouteLPraw_of_tail0L centre place entry qq first raw m hex hE
    (breakExitTailLC_of_parts centre place entry qq first raw m h lower span hkeep hnn hdp
      hland hterm hctx hrun)

#print axioms breakExitTailLC_of_parts
#print axioms breakRouteLPraw_of_ledger_parts

/-! ## (c) `ReplayStage` in place of `FoundStageEntryC` -/

open PalPeg.GalilScaffoldChainInputSupply (Decodes Restarted StageEntry watchSegE_heads)
open PalPeg.CloseoutWatchRound7 (FoundIndexAgreeC FoundRadiusCanonC foundDp_core)

/-- **`foundDp_core` over the witness the exit really carries.**  `ReplayStage`
places a genuine stage entry `(c0', r')` a `WatchSegE` before `(c0, r)`;
`watchSegE_trans` composes it with the exit's own segment. -/
theorem foundDp_core_of_replayStage (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (hP : Decodes (PofC centre place entry raw))
    (a : Fin 2) (ls rs qw : List (Fin 2)) (gap : Bool)
    {c0 : Control} {r : GalilVM}
    (hst : ReplayStage raw (PofC centre place entry raw) qq first c0 r)
    {es0 : List Bool} {cF : Control} {sF : GalilVM}
    (hseg : WatchSegE (PofC centre place entry raw) qq first 2048 es0 c0 r cF sF)
    (hidle : sF.chain = ChainVM.idle)
    (hcen : sF.center = represent ⟨a :: ls, gap⟩ (rs.map some) qw)
    (vq : SearchVM) (hq : searchEffect (PofC centre place entry raw) true sF vq)
    (hfound : vq.search.mode = .found) :
    ∃ k h span : ℕ,
      GalilDpCorrect.Result ((GalilScaffoldPlace.stream ⟨a :: ls, gap⟩).take (span+1)) k 0
        (GalilScaffoldProgram.denote vq.dp.config) ∧
      (GalilScaffoldProgram.denote vq.dp.config).pc = 346 ∧
      (GalilScaffoldProgram.denote vq.dp.config).pos 11 = h ∧
      GalilDpCorrect.Candidate ((GalilScaffoldPlace.stream ⟨a :: ls, gap⟩).take (span+1)) k h := by
  obtain ⟨r', Rad, last, esPre, c0', hR, hSt, hcl, hsegPre⟩ := hst
  exact foundDp_core centre place entry qq first raw hP a ls rs qw gap hR hcl hSt
    (watchSegE_trans (PofC centre place entry raw) qq first 2048 hsegPre hseg) hidle hcen
    vq hq hfound

#print axioms foundDp_core_of_replayStage

/-- **`FoundRadiusCanonC` from `ReplayStage`.** -/
theorem foundRadiusCanonC_of_replayStage (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) {c0 : Control} {r : GalilVM}
    (hst : ReplayStage raw (PofC centre place entry raw) qq first c0 r) :
    FoundRadiusCanonC centre place entry qq first raw c0 r := by
  intro es0 cF sF hseg
  obtain ⟨r', Rad, last, esPre, c0', hR, hSt, hcl, hsegPre⟩ := hst
  obtain ⟨-, -, -, -, ⟨hrc, -⟩, -⟩ := hR
  obtain ⟨-, -, -, hcan, -⟩ := watchSegE_heads (PofC centre place entry raw) qq first 2048
    (watchSegE_trans (PofC centre place entry raw) qq first 2048 hsegPre hseg)
  exact hcan hrc

#print axioms foundRadiusCanonC_of_replayStage

/-! ## (d) The DP window: what `Result` does and does not determine -/

open PalPeg.GalilFppWide (Config)

/-- The found index of a `Result` is the DP's own `pos 11` — so it is determined
by the configuration alone, for any `w`, `lower`, `first`. -/
theorem result_pos_eq {w : List (Fin 3)} {lower first : ℕ} {y : Config 12}
    (hr : GalilDpCorrect.Result w lower first y) (hpc : y.pc = 346) :
    GalilDpCorrect.Candidate w lower (y.pos 11) ∧ first ≤ y.pos 11 := by
  rcases hr with ⟨k, hk, hc, -, -, -, hpos⟩ | ⟨hpc', -⟩
  · rw [hpos]; exact ⟨hc, hk⟩
  · rw [hpc] at hpc'; exact absurd hpc' (by decide)

/-- Two `Result`s at the same configuration report the same index. -/
theorem result_index_unique {w w' : List (Fin 3)} {lower lower' first first' : ℕ} {y : Config 12}
    (hr : GalilDpCorrect.Result w lower first y) (hr' : GalilDpCorrect.Result w' lower' first' y)
    {k k' : ℕ} (hk : y.pos 11 = k) (hk' : y.pos 11 = k') : k = k' := by
  rw [← hk, ← hk']

/-- The two disjuncts of `Result` are separated by the program counter. -/
theorem result_pc_cases {w : List (Fin 3)} {lower first : ℕ} {y : Config 12}
    (hr : GalilDpCorrect.Result w lower first y) : y.pc = 346 ∨ y.pc = 347 := by
  rcases hr with ⟨k, -, -, -, hpc, -⟩ | ⟨hpc, -⟩
  · exact Or.inl hpc
  · exact Or.inr hpc

/-- At `pc = 347` a `Result` denies every candidate. -/
theorem result_not_found_of_pc {w : List (Fin 3)} {lower first : ℕ} {y : Config 12}
    (hr : GalilDpCorrect.Result w lower first y) (hpc : y.pc = 347) :
    ∀ k, first ≤ k → ¬ GalilDpCorrect.Candidate w lower k := by
  rcases hr with ⟨k, -, -, -, hpc', -⟩ | ⟨-, hnone⟩
  · rw [hpc] at hpc'; exact absurd hpc'.symm (by decide)
  · exact hnone

/-- **Why the `lower` slot of `Result` is not determined.**  `Candidate` asks
only `lower < h` of `lower`, so it is antitone in `lower`: the window's lower
bound cannot be read back off the DP configuration, and the uniqueness
`k = lower` that `FoundIndexAgreeC` demands is not a property of `Result`. -/
theorem candidate_antitone {w : List (Fin 3)} {lower lower' h : ℕ}
    (hc : GalilDpCorrect.Candidate w lower h) (hle : lower' ≤ lower) :
    GalilDpCorrect.Candidate w lower' h := by
  obtain ⟨hl, hn, hm, hs⟩ := hc
  exact ⟨by omega, hn, hm, hs⟩

#print axioms result_pos_eq
#print axioms result_pc_cases
#print axioms candidate_antitone

/-- **The repair of `FoundIndexAgreeC`: state the DP record at the exit's own
indices.**  No window uniqueness is needed. -/
def FoundDpAtC (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (lower span h : ℕ) (c0 : Control) (r : GalilVM) : Prop :=
  ∀ (a : Fin 2) (ls rs qw : List (Fin 2)) (gap : Bool) (es0 : List Bool) (cF : Control)
    (sF : GalilVM) (vq : SearchVM),
    WatchSegE (PofC centre place entry raw) qq first 2048 es0 c0 r cF sF →
    sF.center = represent ⟨a :: ls, gap⟩ (rs.map some) qw →
    searchEffect (PofC centre place entry raw) true sF vq → vq.search.mode = .found →
      sF.chain = ChainVM.idle ∧
      GalilDpCorrect.Result ((GalilScaffoldPlace.stream ⟨a :: ls, gap⟩).take (span+1)) lower 0
        (GalilScaffoldProgram.denote vq.dp.config) ∧
      GalilDpCorrect.Candidate ((GalilScaffoldPlace.stream ⟨a :: ls, gap⟩).take (span+1)) lower h

/-- `FoundIndexAgreeC` is stronger: it transports the DP's own record onto the
exit's indices, using the *same* `vq` (Round 8's "same quantum" reading). -/
theorem foundDpAtC_of_indexAgree (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (hP : Decodes (PofC centre place entry raw))
    (lower span h : ℕ) {c0 : Control} {r : GalilVM}
    (hst : ReplayStage raw (PofC centre place entry raw) qq first c0 r)
    (hidx : FoundIndexAgreeC centre place entry qq first raw lower span h c0 r) :
    FoundDpAtC centre place entry qq first raw lower span h c0 r := by
  intro a ls rs qw gap es0 cF sF vq hseg hcen hq hfound
  obtain ⟨hidle, hpos, hagree⟩ := hidx a ls rs qw gap es0 cF sF vq hseg hcen hq hfound
  obtain ⟨k, h', span', hres, hpc, hpos', hcand⟩ :=
    foundDp_core_of_replayStage centre place entry qq first raw hP a ls rs qw gap hst hseg
      hidle hcen vq hq hfound
  obtain ⟨hk, hs⟩ := hagree k span' hres
  subst hk; subst hs
  have hh : h' = h := by rw [← hpos', hpos]
  subst hh
  exact ⟨hidle, hres, hcand⟩

/-- **`CloseoutWatchRound5.FoundDpShiftC` from `FoundDpAtC` + `ReplayStage`.** -/
theorem foundDpShiftC_of_at (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (hP : Decodes (PofC centre place entry raw))
    (lower span h : ℕ) {c0 : Control} {r : GalilVM}
    (hst : ReplayStage raw (PofC centre place entry raw) qq first c0 r)
    (hat : FoundDpAtC centre place entry qq first raw lower span h c0 r) :
    PalPeg.CloseoutWatchRound5.FoundDpShiftC centre place entry qq first raw lower span c0 r := by
  intro a ls rs qw gap es0 cF sF vq hseg hcen hq hfound
  obtain ⟨hidle, hres, hcand⟩ := hat a ls rs qw gap es0 cF sF vq hseg hcen hq hfound
  obtain ⟨k, h', span', -, hpc, -, -⟩ :=
    foundDp_core_of_replayStage centre place entry qq first raw hP a ls rs qw gap hst hseg
      hidle hcen vq hq hfound
  exact ⟨hres, hpc⟩

/-- **`CloseoutWatchRound5.FoundDpBreakC` from `FoundDpAtC` + `ReplayStage`.** -/
theorem foundDpBreakC_of_at (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (hP : Decodes (PofC centre place entry raw))
    (lower span h : ℕ) {c0 : Control} {r : GalilVM}
    (hst : ReplayStage raw (PofC centre place entry raw) qq first c0 r)
    (hat : FoundDpAtC centre place entry qq first raw lower span h c0 r) :
    PalPeg.CloseoutWatchRound5.FoundDpBreakC centre place entry qq first raw lower span h c0 r := by
  intro a ls rs qw gap es0 cF sF vq hseg hcen hq hfound
  obtain ⟨hidle, hres, hcand⟩ := hat a ls rs qw gap es0 cF sF vq hseg hcen hq hfound
  refine ⟨hcand, ?_, foundRadiusCanonC_of_replayStage centre place entry qq first raw hst
    es0 cF sF hseg⟩
  rw [watchSegE_center (PofC centre place entry raw) qq first 2048 hseg]

#print axioms foundDpAtC_of_indexAgree
#print axioms foundDpShiftC_of_at
#print axioms foundDpBreakC_of_at

end PalPeg.CloseoutWatchRound10
