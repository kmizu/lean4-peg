import PalPeg.CloseoutWatchRound32

/-!
# Closeout watch round 34 — pieces 5 and 6 of `shiftRoundAtC'_of_tick`

Round 30 produced `ShiftRoundAtC'` from six named pieces; Round 32 worked the
tick-local pieces 1–4.  This file works the two run-level pieces.

**Piece 6 (`ShiftBreakRunC`) — the missing iteration exists after all.**
Round 14 recorded the missing fact as "an iteration of
`GalilSegmentConstruct3.rounds_construct_of_measure` whose round invariant
carries the `Entry`/`Aligned` origin across rounds and whose `RoundEnd` is
restricted to the `BreakEnd` branch".  `GalilSegmentConstruct3` already has the
invariant (`RoundInv h raw`: read origin + `Entry`, `2h`-periodicity with
minimality, lag-zero `periodOnly` watch, `MInv`) and its preservation
(`roundInv_preserved`, from `rounds_leftmost`), and `rounds_construct_inv`
iterates it — but to the three-way `RoundEnd`.  `rounds_construct_break` below
is the same measure induction with the oracle restricted to `BreakEnd`, so
the terminal is the breaking matched comparison and the invariant is
re-established there.  From `BreakEnd` the conclusion of `ShiftBreakRunC`
follows: the output refresh is total, the broken chain is `afterCompare_chain`,
and the three counters (`negative margin = false`, `positive last`,
`zero lag`) are `GalilScaffoldTopRoundBreak.rounds_break` fed with the
origin's `Entry` at the round start and `read s'.center ≠ none` at the round
end (both from `RoundInv`, the latter via `Entry.centerPresent`).  What is
left, NAMED: the invariant at the post-shift state (`ShiftRoundInvC`), the
one-round oracle (`ShiftBreakOracleC`: at a `RoundInv` state, `BreakEnd` or
one more round with a smaller measure — this is where `InputEnd`/`GuardFail`
are excluded), and the head bound `≤ 2m-1` (`ShiftBreakFitC`, Round 11's
`hfit`).

**Piece 5 (`ShiftOriginC`) — partially transported.**  `org`,
`org.interior.length + 1 = h` and `Entry raw org` at the post-shift state are
the first three components of the same `RoundInv` (`ShiftRoundInvC`), so piece
5 shares its main hypothesis with piece 6.  The remaining four conjuncts are
**not transportable from the landing**: `org.center = position sF.center` and
`(denote vq.dp.config).pos 11 = h` speak about `sF`/`vq`, which `ShiftOriginC`
(like `ShiftRoundAtC'`) quantifies with no hypothesis tying them to the
landing `s1`; `Aligned org` needs the origin to be a fresh one
(`aligned_of_only`, `shifts = 0`), which `RoundInv`'s abstract `org` does not
record; the period lower bound is in the `HasPeriod (Span …)` form, not
`RoundInv`'s `PeriodOn` form.  They are the ONE hypothesis `ShiftOriginRestC`,
stated for the origin `RoundInv` supplies.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

namespace PalPeg.CloseoutWatchRound34

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.CloseoutContracts
open PalPeg.GalilRunSkeleton
open PalPeg.CloseoutWatchRun (LiveScanWatch)
open PalPeg.CloseoutWatchRound30 (ShiftOriginC ShiftBreakRunC)

/-! ## 1. The BreakEnd-only iteration (Round 14's missing iteration) -/

/-- **Derived — the iteration.**  `rounds_construct_of_measure` with the oracle
restricted to `BreakEnd`: the invariant is re-established at the break. -/
theorem rounds_construct_break (P : Shared) (q : ℕ) (first : Fin 9) (delay h : ℕ)
    (Inv : Control → GalilVM → Prop) (μ : Control → GalilVM → ℕ)
    (hround : ∀ c s, Inv c s → BreakEnd P q first delay c s ∨
      ∃ (c' : Control) (s' : GalilVM), Rounds P q first delay h 1 c s c' s' ∧ Inv c' s' ∧
        μ c' s' < μ c s) :
    ∀ (c : Control) (s : GalilVM), Inv c s →
      ∃ (m : ℕ) (c' : Control) (s' : GalilVM),
        Rounds P q first delay h m c s c' s' ∧ Inv c' s' ∧ BreakEnd P q first delay c' s' := by
  have key : ∀ (fuel : ℕ) (c : Control) (s : GalilVM), Inv c s → μ c s ≤ fuel →
      ∃ (m : ℕ) (c' : Control) (s' : GalilVM),
        Rounds P q first delay h m c s c' s' ∧ Inv c' s' ∧ BreakEnd P q first delay c' s' := by
    intro fuel
    induction fuel with
    | zero =>
      intro c s hI hμ
      rcases hround c s hI with hend | ⟨c1, s1, _, _, hlt⟩
      · exact ⟨0, c, s, .stop _ _, hI, hend⟩
      · omega
    | succ f ih =>
      intro c s hI hμ
      rcases hround c s hI with hend | ⟨c1, s1, hstep, hI1, hlt⟩
      · exact ⟨0, c, s, .stop _ _, hI, hend⟩
      · obtain ⟨m, c', s', hr, hI', hend⟩ := ih c1 s1 hI1 (by omega)
        exact ⟨1 + m, c', s', rounds_append P q first delay h hstep hr, hI', hend⟩
  intro c s hI
  exact key (μ c s) c s hI (le_refl _)

/-! ## 2. The named pieces -/

/-- The post-shift state of the shift round. -/
abbrev postShift (s2' : GalilVM) (t' : ShiftState) (v : GalilScaffoldChainWatch.State)
    (cycle : Counter) : GalilVM :=
  shiftLens.set s2' ⟨t', .watch v, cycle⟩

/-- **NAMED (open) — the round invariant at the post-shift state.**  Read
origin of semiperiod `h` with its `Entry`, the `2h`-periodicity of the span
and its minimality, the lag-zero watch, and `MInv`.  (`periodOnly`, the chain
shape and `replaying = false` are definitional here; the rest is not.) -/
def ShiftRoundInvC (raw : List (Fin 2)) (h : ℕ) : Prop :=
  ∀ (c1 : Control) (s1 : GalilVM) (vs : ScanVM) (vq' : SearchVM)
    (w : GalilScaffoldChainWatch.State) (s2' : GalilVM) (t' : ShiftState)
    (v : GalilScaffoldChainWatch.State) (cycle : Counter) (o : Bool),
    LiveScanWatch c1 s1 → c1.clock = 1 → s1.chain = ChainVM.watch w →
    beginShiftVM h w (afterMismatch s1 vs vq') s2' →
    ChainShiftRun ⟨s1.center, left s1.left, ofNat h, inc s1.radius, inc (inc s1.length)⟩
      (GalilScaffoldChainWatch.immediate w) reset h t' v cycle →
    RoundInv h raw {c1 with mode := .scan, clock := 2048, output := o}
      (postShift s2' t' v cycle)

/-- **NAMED (open) — the one-round oracle, break-only.**  At a `RoundInv`
state the controller either reaches the breaking matched comparison or
performs one more round with a smaller measure `μ`.  This is exactly where
`GalilSegmentConstruct3.RoundEnd`'s `InputEnd` and `GuardFail` branches must
be excluded. -/
def ShiftBreakOracleC (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (h : ℕ) (μ : Control → GalilVM → ℕ) : Prop :=
  ∀ (c : Control) (s : GalilVM), RoundInv h raw c s →
    BreakEnd (PofC centre place entry raw) qq first 2048 c s ∨
    ∃ (c' : Control) (s' : GalilVM),
      Rounds (PofC centre place entry raw) qq first 2048 h 1 c s c' s' ∧ μ c' s' < μ c s

/-- **NAMED (open) — the head bound at the break** (Round 11's `hfit`, in the
form the run produces: the breaking matched comparison after the rounds from
a `RoundInv` state stays under the checkpoint cell). -/
def ShiftBreakFitC (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m h : ℕ) : Prop :=
  ∀ (c0 : Control) (s0 : GalilVM) (mm : ℕ) (c' : Control) (s' : GalilVM) (n : ℕ)
    (c3 : Control) (s3 : GalilVM) (vs3 : ScanVM) (vq3 : SearchVM),
    RoundInv h raw c0 s0 →
    Rounds (PofC centre place entry raw) qq first 2048 h mm c0 s0 c' s' →
    ScanSeg (PofC centre place entry raw) qq first 2048 n c' s' c3 s3 →
    canRight s3.right →
    (galilFrame (PofC centre place entry raw) qq first).compare s3 (scanLens.set s3 vs3) →
    (galilFrame (PofC centre place entry raw) qq first).matched (scanLens.set s3 vs3) →
    position (afterCompare s3 vs3 vq3).right ≤ 2 * m - 1

/-- **NAMED (open) — the four origin conjuncts not transportable from the
landing**, for the origin `RoundInv` supplies. -/
def ShiftOriginRestC (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (h lower : ℕ) : Prop :=
  ∀ (sF : GalilVM) (vq : SearchVM) (c1 : Control) (s1 : GalilVM) (vs : ScanVM)
    (vq' : SearchVM) (w : GalilScaffoldChainWatch.State) (s2' : GalilVM)
    (t' : ShiftState) (v : GalilScaffoldChainWatch.State) (cycle : Counter)
    (org : ReadOrigin raw),
    LiveScanWatch c1 s1 → c1.clock = 1 → s1.chain = ChainVM.watch w →
    beginShiftVM h w (afterMismatch s1 vs vq') s2' →
    ChainShiftRun ⟨s1.center, left s1.left, ofNat h, inc s1.radius, inc (inc s1.length)⟩
      (GalilScaffoldChainWatch.immediate w) reset h t' v cycle →
    org.interior.length + 1 = h →
    Entry raw org (toOnly (postShift s2' t' v cycle) v) →
      org.center = position sF.center ∧
      PalPeg.GalilRadiusConsumed.Aligned org ∧
      (GalilScaffoldProgram.denote vq.dp.config).pos 11 = h ∧
      (∀ δ, 0 < δ → δ ≤ lower → ¬ HasPeriod (Span raw org.center org.radius) (2*δ))

/-! ## 3. Small helpers -/

/-- The output refresh on `galilFrame` is total (the `galilFrameS` proof,
`GalilTickFun3.refresh_exists`, verbatim). -/
theorem refresh_frame_exists' (P : Shared) (q : ℕ) (first : Fin 9) (s : GalilVM) (old : Bool) :
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

/-- The centre of a `RoundInv` state is readable (`Entry.centerPresent`). -/
theorem read_center_of_roundInv {raw : List (Fin 2)} {h : ℕ} {c : Control} {s : GalilVM}
    (hI : RoundInv h raw c s) : GalilScaffoldInputHead.read s.center ≠ none := by
  obtain ⟨org, w, -, -, -, -, he, -, -, -, -⟩ := hI
  have hpres : s.center.head.focus ≠ none := he.centerPresent
  intro hnone
  cases hf : s.center.head.focus with
  | none => exact hpres hf
  | some a => simp [GalilScaffoldInputHead.read, hf] at hnone

/-- The watch witness of `RoundInv` at a post-shift state is the shifted watch. -/
theorem roundInv_postShift_watch {raw : List (Fin 2)} {h : ℕ} {c : Control} {s2' : GalilVM}
    {t' : ShiftState} {v : GalilScaffoldChainWatch.State} {cycle : Counter}
    (hI : RoundInv h raw c (postShift s2' t' v cycle)) :
    ∃ org : ReadOrigin raw, org.interior.length + 1 = h ∧ zero v.lag = true ∧
      Entry raw org (toOnly (postShift s2' t' v cycle) v) := by
  obtain ⟨org, w, hint, hs, hz, -, he, -, -, -, -⟩ := hI
  have hwv : w = v := by
    have hs' : ChainVM.watch v = ChainVM.watch w := hs
    exact (ChainVM.watch.inj hs').symm
  subst hwv
  exact ⟨org, hint, hz, he⟩

/-! ## 4. Piece 6 -/

/-- **Derived — `ShiftBreakRunC` from the invariant, the break-only oracle and
the head bound.**  The iteration is `rounds_construct_break`; the terminal's
broken chain is `afterCompare_chain`; the three counters are `rounds_break`. -/
theorem shiftBreakRunC_of_tail (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (m h : ℕ) (μ : Control → GalilVM → ℕ)
    (hinv : ShiftRoundInvC raw h)
    (horacle : ShiftBreakOracleC centre place entry qq first raw h μ)
    (hfit : ShiftBreakFitC centre place entry qq first raw m h) :
    ShiftBreakRunC centre place entry qq first raw m h := by
  intro c1 s1 vs vq' w s2' t' v cycle o hL hclk hw hs2' hchain ho
  -- the invariant at the post-shift state
  have hI := hinv c1 s1 vs vq' w s2' t' v cycle o hL hclk hw hs2' hchain
  obtain ⟨org, hint, hzv, he⟩ := roundInv_postShift_watch hI
  -- the iteration
  have horacle' : ∀ c s, RoundInv h raw c s →
      BreakEnd (PofC centre place entry raw) qq first 2048 c s ∨
      ∃ (c' : Control) (s' : GalilVM),
        Rounds (PofC centre place entry raw) qq first 2048 h 1 c s c' s' ∧
        RoundInv h raw c' s' ∧ μ c' s' < μ c s := by
    intro c0 s0 h0
    rcases horacle c0 s0 h0 with hend | ⟨c', s', hstep, hlt⟩
    · exact Or.inl hend
    · exact Or.inr ⟨c', s', hstep,
        roundInv_preserved (PofC centre place entry raw) qq first 2048 h raw hstep h0, hlt⟩
  obtain ⟨mm, c', s', hrounds, hI', hend⟩ :=
    rounds_construct_break (PofC centre place entry raw) qq first 2048 h (RoundInv h raw) μ
      horacle' _ _ hI
  obtain ⟨n, c3, s3, hseg3, hm3, hr3, hc3, w3, hs3, hav3, vs3, vq3, hcmp3, hmt3, hq3, hsp3,
    w3', hbr3⟩ := hend
  -- the output refresh at the break
  obtain ⟨o3, ho3⟩ := refresh_frame_exists' (PofC centre place entry raw) qq first
    (afterCompare s3 vs3 vq3) c3.output
  -- the counters at the break
  have hp0 : (postShift s2' t' v cycle).periodOnly = true := by
    show s2'.periodOnly = true
    rw [hs2'.2]
  have hs0 : (postShift s2' t' v cycle).chain = ChainVM.watch v := rfl
  obtain ⟨-, -, hbroken, hres⟩ :=
    rounds_break (PofC centre place entry raw) qq first 2048 h hrounds v hp0 hs0 hzv hseg3
      hm3 hr3 hc3 w3 hs3 hav3 vs3 vq3 hcmp3 hmt3 hq3 hsp3 w3' hbr3 o3 ho3
  have hall := hres raw org hint he (read_center_of_roundInv hI')
  obtain ⟨-, -, hmargin, hlast, hlag, -, -, -, -, -⟩ := hall
  -- the head bound
  have hbound := hfit _ _ mm c' s' n c3 s3 vs3 vq3 hI hrounds hseg3 hav3 hcmp3 hmt3
  exact ⟨mm, c', s', n, c3, s3, w3, vs3, vq3, o3, w3', hrounds, hseg3, hm3, hr3, hc3, hs3, hav3,
    hcmp3, hmt3, hq3, ho3, hbroken, hmargin, hlast, hlag, hbound⟩

/-! ## 5. Piece 5 -/

/-- **Derived — `ShiftOriginC` from the invariant and the rest.**  The origin,
its semiperiod and its `Entry` at the post-shift state are `RoundInv`'s; the
four remaining conjuncts are `ShiftOriginRestC`. -/
theorem shiftOriginC_of_ctx (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (h lower : ℕ)
    (hinv : ShiftRoundInvC raw h)
    (hrest : ShiftOriginRestC centre place entry qq first raw h lower) :
    ShiftOriginC centre place entry qq first raw h lower := by
  intro sF vq c1 s1 vs vq' w s2' t' v cycle hL hclk hw hs2' hchain
  have hI := hinv c1 s1 vs vq' w s2' t' v cycle c1.output hL hclk hw hs2' hchain
  obtain ⟨org, hint, -, he⟩ := roundInv_postShift_watch hI
  obtain ⟨hoc, ha, hpos11, hlow⟩ :=
    hrest sF vq c1 s1 vs vq' w s2' t' v cycle org hL hclk hw hs2' hchain hint he
  exact ⟨org, hint, he, hoc, ha, hpos11, hlow⟩

end PalPeg.CloseoutWatchRound34

#print axioms PalPeg.CloseoutWatchRound34.rounds_construct_break
#print axioms PalPeg.CloseoutWatchRound34.refresh_frame_exists'
#print axioms PalPeg.CloseoutWatchRound34.read_center_of_roundInv
#print axioms PalPeg.CloseoutWatchRound34.roundInv_postShift_watch
#print axioms PalPeg.CloseoutWatchRound34.shiftBreakRunC_of_tail
#print axioms PalPeg.CloseoutWatchRound34.shiftOriginC_of_ctx
