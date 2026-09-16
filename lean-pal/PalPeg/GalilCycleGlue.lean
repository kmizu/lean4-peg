import PalPeg.GalilSegmentConstruct
import PalPeg.GalilSegmentConstruct2
import PalPeg.GalilSegmentConstruct3
import PalPeg.GalilMainLoopMInv
import PalPeg.GalilShiftH
import PalPeg.GalilNoBelowFirst
import PalPeg.GalilScaffoldTopLifeRestart

/-!
# Gluing one main-loop cycle out of the segment constructions

`GalilMainLoopMInv` consumes the two premise bundles `FoundCycle` and
`FallbackCycle` — long existential conjunctions describing one whole turn of
the controller's main loop.  Until now they were only ever *assumed*.  This
module assembles them, *existentially*, from the constructive segment lemmas
of `GalilSegmentConstruct{,2,3}`, so that what is left assumed is only what no
local construction can produce.  Every such piece is a **named hypothesis with
a one-line meaning**; nothing is hidden in a `sorry`.

The two results are

* `fallbackCycle_of_constructions` — `watchSegE_construct` plus the
  `SegEnd.mismatch` exit.  Here almost everything *is* derivable: the scan and
  search effects of the mismatching comparison are total, and the shift guard
  fails outright because the chain is still idle.
* `foundCycle_of_constructions` — `watchSegE_construct` (`SegEnd.found`),
  `watchSegE_watchSeg_construct` (`WatchStop.mismatchWatch`),
  `shift_run_chain` for the shift phase and `rounds_construct_inv`
  (`RoundEnd = BreakEnd`) for the re-shift rounds.

## What is *not* derivable here (see each hypothesis)

Branch selection (`hfound`, `hwatch`, `hbreak`, `hmis`) is input-dependent: the
constructions are total and produce *some* exit, and which exit is taken is a
fact about `raw`.  The chain start (`hch`), the shift entry and its unit moves
(`hshift`), the DP result at the found tick (`hdpres`, the conclusion of
`search_result_at_tick`), the read origin and the semiperiod calibration
(`horg`, whose `h = pos 11` half is `shift_h_eq_pos11`), the period lower
bound (`hlow`, the input of `noBelow_first_of_result`), the round invariant at
the first shift (`hRI`), the terminal chain data (`hterm`) and the landing
`Restarted` (`hland`, from `life_restarted`) are all of the same kind.

`hland` deserves a note of its own: `life_restarted` needs the preparation
segment split as `bs ++ dm :: cs` with `|bs| = h` and `|cs| = h+1` (that is
what `prep_watch_start_least` pins down), while
`watchSegE_watchSeg_construct` produces the *empty* preparation segment.  So
the landing `Restarted` cannot be threaded through this construction as it
stands and travels as a hypothesis.
-/

set_option autoImplicit false
namespace PalPeg.GalilCycleGlue

open PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilSegmentConstruct
  PalPeg.GalilSegmentConstruct2 PalPeg.GalilBranchInvariants2
open Manacher GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter
  GalilScaffoldInputHead GalilScaffoldChainVerifier

/-! ## A totality helper -/

/-- The exit output of a comparison is total on `galilFrame`, exactly as it is
on `galilFrameS` (`GalilTickFun3.refresh_exists`). -/
theorem refresh_frame_exists (P : Shared) (q : ℕ) (first : Fin 9) (s : GalilVM) (old : Bool) :
    ∃ o, refresh (galilFrame P q first) s old o := by
  classical
  refine ⟨if P.onLetter s then decide (P.leftFirst s) else old, ?_, ?_⟩
  · intro hl
    have hl' : P.onLetter s := hl
    show (if P.onLetter s then decide (P.leftFirst s) else old) = true ↔ P.leftFirst s
    rw [if_pos hl']
    exact decide_eq_true_iff
  · intro hl
    have hl' : ¬ P.onLetter s := hl
    show (if P.onLetter s then decide (P.leftFirst s) else old) = old
    rw [if_neg hl']

/-! ## The fallback cycle -/

/-- **The fallback cycle, assembled.**  From a scan state with the chain idle,
`watchSegE_construct` builds the chain-idle segment; if that segment ends in
`SegEnd.mismatch` (`hmis`), the mismatching comparison's scan and search
effects are *total* (`hsearch`, and `chainAt`'s idle branch under `hbg`), and
the shift guard fails outright because the chain is still idle
(`shiftGuardVM` demands `chain = .watch w`).  So the whole of `FallbackCycle`
follows. -/
theorem fallbackCycle_of_constructions
    (raw : List (Fin 2)) (qq : ℕ) (first : Fin 9) (delay : ℕ)
    (onLetter leftFirst : GalilVM → Prop) (rsl : GalilVM → GalilVM → Prop)
    (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place) (entry : ℕ)
    (P : Shared)
    -- the concrete shared the fallback lemma is stated for
    (hPeq : P = galilShared onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM'
      rsl centre place entry)
    (honL : onLetter = onLetterVM raw) (hlF : leftFirst = leftFirstVM)
    (hex : ∀ s, P.replayExhausted s = zero s.replay)
    (hq0 : 0 < qq) (h7 : first ≠ 7) (h8 : first ≠ 8) (hd : 1 ≤ delay)
    -- the co-process hypotheses of `watchSegE_construct`
    (hsearch : ∀ s' : GalilVM, SearchReady (searchLens.get s') → ∀ a : Bool,
      ∃ v, searchEffect P a s' v)
    (hpres : ∀ (s' : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s') → searchEffect P a s' v → SearchReady v)
    -- GAP: a *background* event never lands the search in `found`, i.e. the chain
    -- is started only at a comparison.  (This used to be `watchSegE_construct`'s
    -- own `hbg`; the construction now has a `foundBackground` exit instead.)
    (hbg : ∀ (s' : GalilVM) (v : SearchVM), searchEffect P false s' v → v.search.mode ≠ .found)
    -- the state the cycle starts from
    (c0 : Control) (r : GalilVM) (R : ℕ)
    (hm0 : c0.mode = .scan) (hclk0 : 1 ≤ c0.clock) (hidle0 : r.chain = ChainVM.idle)
    (hsr0 : SearchReady (searchLens.get r)) (hM0 : MInv raw c0 r)
    (hinv0 : ScanInvariant raw (position r.center) R r.left r.right)
    (hI0 : ShiftIdle r) (hS0 : SpanRep r) (hout0 : OutputRel raw c0 r)
    (fuel : ℕ)
    -- GAP: the idle segment ends at a mismatching comparison (`SegEnd.mismatch`),
    -- not at the end of the input and not at a found comparison.
    (hmis : ∀ (es : List Bool) (c : Control) (t : GalilVM),
      WatchSegE P qq first delay es c0 r c t → t.chain = ChainVM.idle →
      c.replaying = false ∧ c.clock = 1 ∧ canRight t.right ∧
        read (left t.left) ≠ read (right t.right))
    -- GAP: the length counter is a natural number and the prepared stage window
    -- has even length at the mismatch (`heven` of `cycle_fallback_stepsAll`).
    (heven : ∀ t : GalilVM, ∃ l : ℕ, value t.length = l ∧
      ∀ (a : Fin 2) (xs rs' q' : List (Fin 2)),
        right t.right = represent ⟨a :: xs,(right t.right).gap⟩ (rs'.map some) q' →
        ((GalilScaffoldPlace.stream ⟨a :: xs,(right t.right).gap⟩).take (l+1)).length % 2 = 0) :
    FallbackCycle P qq first delay raw c0 r := by
  obtain ⟨es0, cF, sF, _r', hseg0, hmF, _hclkF, hidleF, hsrF, _hMF, _hinvF, _⟩ :=
    watchSegE_construct raw P hex qq first delay hd hsearch hpres fuel c0 r R hm0 hclk0 hidle0
      hsr0 hM0 hinv0
  obtain ⟨hrF, hcF, havF, hneF⟩ := hmis es0 cF sF hseg0 hidleF
  obtain ⟨vq, hq⟩ := hsearch sF hsrF false
  obtain ⟨l, hl, hev⟩ := heven sF
  refine ⟨onLetter, leftFirst, rsl, centre, place, entry, es0, cF, sF,
    ⟨left sF.left, right sF.right, ChainVM.idle⟩, vq, l,
    hPeq, hq0, h7, h8, honL, hlF, hI0, hS0, hout0, hseg0, hmF, hrF, hcF, havF, rfl, rfl, hneF, hq,
    Or.inr (Or.inl ⟨hidleF, decide_eq_false (hbg sF vq hq), rfl⟩), ?_, hl, hev⟩
  -- the shift guard cannot hold: the chain is still idle after the mismatch
  rintro ⟨w, hw, -⟩
  rw [afterMismatch_chain] at hw
  exact ChainVM.noConfusion hw

/-! ## The semiperiod calibration, as `shift_h_eq_pos11` supplies it -/

/-- The `h = pos 11` half of `horg` below, discharged by `shift_h_eq_pos11`:
the shift's semiperiod `h` equals the DP's OUTPUT cursor as soon as the answer
tape is exact and the walker is far enough ahead. -/
theorem h_eq_pos11_of_answerExact {cfg : GalilScaffoldProgram.Config 12} {n : ℕ}
    (hans : PalPeg.GalilShiftH.AnswerExact (cfg.tapes 11) n) (hn : 0 < n)
    (c : Fin 3) (walker : GalilScaffoldPlace.Place) (ver : PlaceHead) (radius : Counter)
    (hwalk : PalPeg.GalilBranchInvariants.PlaceAhead walker n)
    {ch : ChainVM} (hch : ChainMatched (chainStart (cfg.tapes 11) c walker ver radius) ch)
    {N : ℕ} {w : GalilScaffoldChainWatch.State} (hrun : ChainSteps N ch (.watch w))
    {h : ℕ} {s t : GalilVM} (hb : beginShiftVM h w s t) (hb' : beginShiftVM' s t) :
    h = (GalilScaffoldProgram.denote cfg).pos 11 :=
  PalPeg.GalilShiftH.shift_h_eq_pos11 hans hn c walker ver radius hwalk hch hrun hb hb'

/-! ## The found cycle -/

/-- **The found cycle, assembled.**  The four constructions are run in order —
the chain-idle segment (`watchSegE_construct`), the preparation and watch
segments (`watchSegE_watchSeg_construct`), the shift phase
(`shift_run_chain`) and the re-shift rounds (`rounds_construct_inv`) — and
their outputs are packed into `FoundCycle`.  The branch each construction
takes, and every input-dependent datum, is a named hypothesis; see the module
docstring. -/
theorem foundCycle_of_constructions
    (raw : List (Fin 2)) (qq : ℕ) (first : Fin 9) (delay : ℕ) (P : Shared)
    (a : Fin 2) (ls rs qs : List (Fin 2)) (gap : Bool) (entry h : ℕ)
    (hP : P.onLetter = onLetterVM raw) (hP' : P.leftFirst = leftFirstVM)
    (hex : ∀ s, P.replayExhausted s = zero s.replay)
    (hraw : raw = (a :: ls).reverse ++ rs ++ qs) (hd : 1 ≤ delay)
    -- the co-process hypotheses of `watchSegE_construct`
    (hsearch : ∀ s' : GalilVM, SearchReady (searchLens.get s') → ∀ b : Bool,
      ∃ v, searchEffect P b s' v)
    (hpres : ∀ (s' : GalilVM) (b : Bool) (v : SearchVM),
      SearchReady (searchLens.get s') → searchEffect P b s' v → SearchReady v)
    -- the hypothesis pack of the watch phase (`GalilSegmentConstruct2.Ctx`)
    (K : Ctx P qq first)
    -- the state the cycle starts from
    (c0 : Control) (r : GalilVM) (R : ℕ)
    (hm0 : c0.mode = .scan) (hclk0 : 1 ≤ c0.clock) (hidle0 : r.chain = ChainVM.idle)
    (hsr0 : SearchReady (searchLens.get r)) (hM0 : MInv raw c0 r)
    (hinv0 : ScanInvariant raw (position r.center) R r.left r.right)
    (hout0 : OutputRel raw c0 r)
    (hcen0 : r.center = represent ⟨a :: ls,gap⟩ (rs.map some) qs)
    (fuel fuel2 : ℕ)
    -- GAP: the idle segment ends at a *found* comparison (`SegEnd.found`), and the
    -- controller is not replaying there.
    (hfound : ∀ (es : List Bool) (c : Control) (t : GalilVM),
      WatchSegE P qq first delay es c0 r c t → t.chain = ChainVM.idle →
      c.replaying = false ∧ c.clock = 1 ∧ canRight t.right ∧
        read (left t.left) = read (right t.right) ∧
        ∃ vq, searchEffect P true t vq ∧ vq.search.mode = .found)
    -- GAP: the chain started at the found comparison is a real (non-idle) chain.
    (hch : ∀ (t : GalilVM) (vq : SearchVM),
      ∃ ch : ChainVM,
        ChainMatched (chainStart (vq.dp.config.tapes 11) (P.centre t) (P.place t) t.center t.radius)
          ch ∧ ch ≠ ChainVM.idle)
    -- GAP: the state the chain starts in satisfies the watch-phase invariant.
    (hKinv : ∀ (t : GalilVM) (vq : SearchVM) (ch : ChainVM), K.Inv (afterCompare t
      ⟨left t.left, right t.right, ch⟩ vq))
    -- GAP: the watch phase ends at a mismatch with the chain watching at lag zero
    -- (`WatchStop.mismatchWatch`), at clock one.
    (hwatch : ∀ (c : Control) (t : GalilVM), WatchStop P qq first c t →
      c.clock = 1 ∧ canRight t.right ∧
      ∃ w : GalilScaffoldChainWatch.State, t.chain = ChainVM.watch w ∧ zero w.lag = true ∧
      ∃ (vs : ScanVM) (vq : SearchVM),
        (galilFrame P qq first).compare t (scanLens.set t vs) ∧
        ¬ (galilFrame P qq first).matched (scanLens.set t vs) ∧
        searchEffect P false t vq)
    -- GAP: at that mismatch the shift guard holds, the shift entry fires with the
    -- semiperiod `h`, the copy is idle and the centre really moves `h` unit steps.
    (hshift : ∀ (t : GalilVM) (w : GalilScaffoldChainWatch.State) (vs : ScanVM) (vq : SearchVM),
      t.chain = ChainVM.watch w →
      ∃ (u : GalilVM) (t' : ShiftState),
        P.shiftGuard (afterMismatch t vs vq) ∧ P.beginShift (afterMismatch t vs vq) u ∧
        beginShiftVM h w (afterMismatch t vs vq) u ∧ CopyIdle u ∧
        ShiftRun ⟨t.center, left t.left, ofNat h, inc t.radius, inc (inc t.length)⟩ h t')
    -- GAP: the DP result at the found tick (the left disjunct of
    -- `search_result_at_tick`), with the OUTPUT cursor calibrated to `h`
    -- (`shift_h_eq_pos11`, i.e. `h_eq_pos11_of_answerExact` above).
    (hdpres : ∀ (t : GalilVM) (vq : SearchVM), searchEffect P true t vq →
      vq.search.mode = .found →
      ∃ lower span : ℕ,
        GalilDpCorrect.Result ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (span+1)) lower 0
          (GalilScaffoldProgram.denote vq.dp.config) ∧
        (GalilScaffoldProgram.denote vq.dp.config).pc = 346 ∧
        (GalilScaffoldProgram.denote vq.dp.config).pos 11 = h)
    -- GAP: the read origin of the shifted chain, of semiperiod `h`, sitting at the
    -- centre of the found comparison.
    (horg : ∀ (t u : GalilVM) (w : GalilScaffoldChainWatch.State),
      ∃ org : ReadOrigin raw, org.interior.length + 1 = h ∧ Entry raw org (toOnly u w) ∧
        org.center = position t.center)
    -- GAP: no period below the prepared stage (the `hlow` input of
    -- `noBelow_first_of_result`).
    (hlow : ∀ (org : ReadOrigin raw) (lower : ℕ), ∀ d, 0 < d → d ≤ lower →
      ¬ HasPeriod (Span raw org.center org.radius) (2*d))
    -- GAP: the round invariant holds at the state the first shift lands in.
    (hRI : ∀ (c : Control) (u : GalilVM) (t' : ShiftState)
      (v : GalilScaffoldChainWatch.State) (cyc : Counter) (o : Bool),
      RoundInv h raw {c with mode := .scan, clock := delay, output := o}
        (shiftLens.set u ⟨t', ChainVM.watch v, cyc⟩))
    -- the measure and the one-round oracle of `rounds_construct_inv`
    (mu : Control → GalilVM → ℕ)
    (hround : ∀ c s, RoundInv h raw c s → RoundEnd P qq first delay c s ∨
      ∃ (c' : Control) (s' : GalilVM),
        Rounds P qq first delay h 1 c s c' s' ∧ mu c' s' < mu c s)
    -- GAP: the rounds end at the breaking comparison, not at the end of the input
    -- and not at a failing shift guard.
    (hbreak : ∀ (c : Control) (s : GalilVM),
      RoundEnd P qq first delay c s → BreakEnd P qq first delay c s)
    -- GAP: the scan invariant and the broken chain's counters at the terminal.
    (hterm : ∀ (s3 : GalilVM) (vs3 : ScanVM) (vq3 : SearchVM)
      (w3' : GalilScaffoldChainWatch.State), vs3.chain = ChainVM.broken w3' →
      (∃ cen3 r3 : ℕ, ScanInvariant raw cen3 r3 (afterCompare s3 vs3 vq3).left
        (afterCompare s3 vs3 vq3).right) ∧
      negative w3'.margin = false ∧ positive w3'.machine.control.last = true ∧
      zero w3'.lag = true)
    (hrestart : ∀ s t, restartVM entry s t → P.restart s t)
    -- GAP: the state after the restart is `Restarted` — `life_restarted`, which
    -- this construction cannot feed (see the module docstring).
    (hland : ∀ (s3 : GalilVM) (vs3 : ScanVM) (vq3 : SearchVM)
      (w3' : GalilScaffoldChainWatch.State),
      ∃ Rad' : ℕ, Restarted raw {(afterCompare s3 vs3 vq3) with chain := .idle, lower := w3'.machine.control.last, search := GalilScaffoldSearchFinish.begin w3'.machine.control.last (afterCompare s3 vs3 vq3).radius, dp := GalilScaffoldControl.reset entry (afterCompare s3 vs3 vq3).dp} Rad' w3'.machine.control.last) :
    FoundCycle P qq first delay raw c0 r := by
  classical
  -- (1) the chain-idle segment, ending at the found comparison
  obtain ⟨es0, cF, sF, _r1, hseg0, hmF, _hclkF, hidleF, _hsrF, _hMF, _hinvF, _⟩ :=
    watchSegE_construct raw P hex qq first delay hd hsearch hpres fuel c0 r R hm0 hclk0 hidle0
      hsr0 hM0 hinv0
  obtain ⟨hrF, hcF, havF, hmt, vq, hq, hfnd⟩ := hfound es0 cF sF hseg0 hidleF
  have hcenF : sF.center = represent ⟨a :: ls,gap⟩ (rs.map some) qs := by
    rw [watchSegE_center P qq first delay hseg0]; exact hcen0
  -- (2) the chain start and the exit output of the found comparison
  obtain ⟨ch, hchm, hchne⟩ := hch sF vq
  obtain ⟨oF, hoF⟩ := refresh_frame_exists P qq first
    (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq) cF.output
  -- (3) the preparation and watch segments
  obtain ⟨cM, sM, hprepSeg, hseg, _hinvM, hmM, hrM, _hclkM, hstop⟩ :=
    watchSegE_watchSeg_construct P qq first delay hd K fuel2
      {cF with clock := delay, output := oF, replaying := false}
      (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq)
      (hKinv sF vq ch) hmF rfl hd
  obtain ⟨hcM, havM, w, hsM, hz, vs, vq', hcmp, hmis, hq'⟩ := hwatch cM sM hstop
  -- (4) the shift phase
  obtain ⟨s2', t', hg, hb, hs2', hi2, hrun⟩ := hshift sM w vs vq' hsM
  obtain ⟨v, cyc, hchain⟩ := shift_run_chain hrun (GalilScaffoldChainWatch.immediate w) reset
  obtain ⟨o, ho⟩ := PalPeg.GalilTickFun3.refresh_exists P qq first
    (shiftLens.set s2' ⟨t', ChainVM.watch v, cyc⟩) cM.output
  -- (5) the DP data and the read origin
  obtain ⟨lower, span, hres, hpc, hpos11⟩ := hdpres sF vq hq hfnd
  obtain ⟨org, hint, hEntry, hocen⟩ :=
    horg sF (shiftLens.set s2' ⟨t', ChainVM.watch v, cyc⟩) v
  -- (6) the re-shift rounds and their terminal
  obtain ⟨m, c', s', hrounds, _hRI', hend⟩ :=
    rounds_construct_inv P qq first delay h raw mu hround
      {cM with mode := .scan, clock := delay, output := o}
      (shiftLens.set s2' ⟨t', ChainVM.watch v, cyc⟩) (hRI cM s2' t' v cyc o)
  obtain ⟨n, c3, s3, hseg3, hm3, hr3, hc3, w3, hs3, hav3, vs3, vq3, hcmp3, hmt3, hq3, _hend3,
    w3', hbr3⟩ := hbreak _ _ hend
  obtain ⟨o3, ho3⟩ := refresh_frame_exists P qq first (afterCompare s3 vs3 vq3) c3.output
  obtain ⟨⟨cen3, r3, hinv3⟩, hmargin, hlast, hlag⟩ := hterm s3 vs3 vq3 w3' hbr3
  exact ⟨a, ls, rs, qs, gap, es0, cF, sF, vq, ch, oF, [],
    {cF with clock := delay, output := oF, replaying := false},
    afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq, cM, sM, h, w, vs, vq', s2', t', v, cyc,
    o, org, lower, span, m, c', s', n, c3, s3, w3, vs3, vq3, o3, cen3, r3, w3', entry,
    hP, hP', hex, hraw, hout0, hseg0, hmF, hrF, hcF, havF, hidleF, hcenF, hq, hfnd, hmt, hchm,
    hchne, hoF, hprepSeg, hseg, hmM, hrM, hcM, hsM, hz, havM, hcmp, hmis, hq', hg, hb, hs2', hi2,
    hchain, ho, hint, hEntry, hocen, hres, hpc, (by rw [hpos11] : _), hlow org lower, hrounds,
    hseg3, hm3, hr3, hc3, hs3, hav3, hcmp3, hmt3, hq3, ho3, hinv3, hbr3, hmargin, hlast, hlag,
    hrestart, hland s3 vs3 vq3 w3'⟩

#print axioms refresh_frame_exists
#print axioms fallbackCycle_of_constructions
#print axioms h_eq_pos11_of_answerExact
#print axioms foundCycle_of_constructions

end PalPeg.GalilCycleGlue
