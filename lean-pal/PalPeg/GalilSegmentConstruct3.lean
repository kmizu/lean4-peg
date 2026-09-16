import PalPeg.GalilGoodLag
import PalPeg.GalilScaffoldTopRoundBreak
import PalPeg.GalilSharedFunctional
import PalPeg.GalilTickFun3

/-!
# L7c — constructing the re-shift rounds and the final segment

`cycle_found_stepsAll` / `life_stepsAll` *consume* the data

* `hrounds : Rounds P qq first delay h m …`  (`GalilScaffoldTopRounds`),
* `hseg3 : ScanSeg P qq first delay n …`     (`GalilScaffoldTopScanSeg`),
* the terminal breaking comparison `hmt3` / `vs3.chain = .broken w3'`
  (`GalilScaffoldTopRoundBreak.rounds_break`),

as hypotheses.  This module builds them.

The shape of the construction is forced by `Rounds.next`, whose premises are
(i) a scan segment, (ii) a terminal *mismatching* comparison at clock one with
`singlePositive s1.cycle = true` and the chain's prediction agreeing with the
right symbol, (iii) the shift guard and the shift entry `beginShiftVM h w`,
(iv) a `ChainShiftRun` of exactly `h` units, (v) an output refresh.  Of these
only (iv) and (v) are *total*: `shift_run_chain` lifts any `ShiftRun` of the
head/counter state to a `ChainShiftRun` (no `Good` is needed — the verifier
does not move during a centre shift), and `GalilTickFun3.refresh_exists`
supplies the exit output.  `roundStep_of_shiftRun` packages exactly that.

Everything else is input-dependent and is exposed as the one-round oracle
`hround` of `rounds_construct`: at a state satisfying the round invariant the
controller either

* `BreakEnd` — reaches the breaking matched comparison (the `life`
  continuation, the premises of `rounds_break`), or
* `InputEnd` — runs out of input inside a segment (`¬ canRight`, i.e.
  `position = 2*|raw|` by `GalilEndOfInput.not_canRight_iff`), or
* `GuardFail` — reaches a mismatching terminal with `¬ shiftGuardVM`.  This
  branch *does* exist during rounds: `Tick.scan_fallback` fires on
  `Or.inr hg`, and `compare_progress_S` shows the tick is available, so the
  guard cannot be assumed true, or
* performs one more round (`Rounds … 1`).

`rounds_construct` iterates the oracle (fuel), `rounds_construct_of_measure`
replaces the fuel by a strictly decreasing measure, and
`roundInv_preserved` (from `rounds_leftmost`) shows the invariant used for the
iteration — read origin, `2h`-periodicity of the span with its minimality, and
the leftmost-live-centre invariant `MInv` — survives a round, so the oracle is
only ever asked about states where it has the facts it needs.

The span containment needed for `Good` at positive lag during a round's scan
(`hidx` of `good_of_periodOn`) is kept as the single named hypothesis `hidx`
of `roundInv_good`: the read index is `org.center + org.radius + 2`, which is
*two past* the right end of the span `rounds_leftmost` carries, so the period
must be known on a strictly larger interval.  That is the one genuine gap.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open Manacher GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter
  GalilScaffoldInputHead GalilScaffoldChainVerifier

variable (P : Shared) (q : ℕ) (first : Fin 9) (delay h : ℕ)

/-! ## Composition of segments and rounds -/

/-- Scan segments compose. -/
theorem scanSeg_append {n : ℕ} {c c1 : Control} {s s1 : GalilVM}
    (h1 : ScanSeg P q first delay n c s c1 s1) :
    ∀ {n' : ℕ} {c2 : Control} {s2 : GalilVM}, ScanSeg P q first delay n' c1 s1 c2 s2 →
      ScanSeg P q first delay (n+n') c s c2 s2 := by
  induction h1 with
  | stop c s => intro n' c2 s2 h2; simpa using h2
  | wait c s s' hm hr hn hb _ ih => intro n' c2 s2 h2; exact .wait c s s' hm hr hn hb (ih h2)
  | count c s s' hm hr ha hc hb _ ih =>
    intro n' c2 s2 h2; exact .count c s s' hm hr ha hc hb (ih h2)
  | «match» c s vs vq o hm hr ha hc hcont hcmp hmt hwatch hq ho _ ih =>
    intro n' c2 s2 h2
    rw [Nat.add_right_comm]
    exact .match c s vs vq o hm hr ha hc hcont hcmp hmt hwatch hq ho (ih h2)

/-- Chained rounds compose. -/
theorem rounds_append {m : ℕ} {c c1 : Control} {s s1 : GalilVM}
    (h1 : Rounds P q first delay h m c s c1 s1) :
    ∀ {m' : ℕ} {c2 : Control} {s2 : GalilVM}, Rounds P q first delay h m' c1 s1 c2 s2 →
      Rounds P q first delay h (m+m') c s c2 s2 := by
  induction h1 with
  | stop c s => intro m' c2 s2 h2; simpa using h2
  | next c s hseg hm1 hr1 hc1 w hs1 hav vs vq hcmp hmis hq hend hpred hlen hg s2 hb hs2 hi2
      hchain o ho _ ih =>
    intro m' c2 s2' h2
    rw [Nat.add_right_comm]
    exact .next c s hseg hm1 hr1 hc1 w hs1 hav vs vq hcmp hmis hq hend hpred hlen hg s2 hb hs2 hi2
      hchain o ho (ih h2)

/-! ## One round, built from the totality sources -/

/-- **One round exists once the segment, the mismatching terminal and the
`h` unit moves of the shift phase are given.**  The chain side of the shift
(`ChainShiftRun`) and the exit output are total: `shift_run_chain` and
`GalilTickFun3.refresh_exists`.  The shift *entry* is `beginShiftVM h w`,
which is an equation, so it is supplied by `hb`/`hs2` from the guard via
`beginShift_exists` at the call site. -/
theorem roundStep_of_shiftRun {n : ℕ} {c c1 : Control} {s s1 : GalilVM}
    (hseg : ScanSeg P q first delay n c s c1 s1)
    (hm1 : c1.mode = .scan) (hr1 : c1.replaying = false) (hc1 : c1.clock = 1)
    (w : GalilScaffoldChainWatch.State) (hs1 : s1.chain = .watch w)
    (hav : canRight s1.right) (vs : ScanVM) (vq : SearchVM)
    (hcmp : (galilFrame P q first).compare s1 (scanLens.set s1 vs))
    (hmis : ¬ (galilFrame P q first).matched (scanLens.set s1 vs))
    (hq : searchEffect P false s1 vq)
    (hend : singlePositive s1.cycle = true)
    (hpred : read (right s1.right) =
      GalilScaffoldChainConsume.symbol w.machine.control.period.focus)
    (hlen : Canonical s1.length)
    (hg : P.shiftGuard (afterMismatch s1 vs vq))
    (s2 : GalilVM) (hb : P.beginShift (afterMismatch s1 vs vq) s2)
    (hs2 : beginShiftVM h w (afterMismatch s1 vs vq) s2) (hi2 : CopyIdle s2)
    {t' : ShiftState}
    (hshift : ShiftRun ⟨s1.center, left s1.left, ofNat h, inc s1.radius, inc (inc s1.length)⟩
      h t') :
    ∃ (v : GalilScaffoldChainWatch.State) (cycle : Counter) (o : Bool),
      Rounds P q first delay h 1 c s
        {c1 with mode := .scan, clock := delay, output := o}
        (shiftLens.set s2 ⟨t', .watch v, cycle⟩) := by
  obtain ⟨v, cycle, hchain⟩ :=
    shift_run_chain hshift (GalilScaffoldChainWatch.immediate w) reset
  obtain ⟨o, ho⟩ := PalPeg.GalilTickFun3.refresh_exists P q first
    (shiftLens.set s2 ⟨t', .watch v, cycle⟩) c1.output
  refine ⟨v, cycle, o, ?_⟩
  have : Rounds P q first delay h (0+1) c s
      {c1 with mode := .scan, clock := delay, output := o}
      (shiftLens.set s2 ⟨t', .watch v, cycle⟩) :=
    .next c s hseg hm1 hr1 hc1 w hs1 hav vs vq hcmp hmis hq hend hpred hlen hg s2 hb hs2 hi2
      hchain o ho (.stop _ _)
  simpa using this

/-! ## The three ways a round can fail to be a round -/

/-- The `life` continuation: a final segment ending at a matched comparison
whose chain prediction fails, i.e. exactly the premises `hseg3`, `hmt3`,
`hbroken` of `rounds_break`. -/
def BreakEnd (c : Control) (s : GalilVM) : Prop :=
  ∃ (n : ℕ) (c3 : Control) (s3 : GalilVM), ScanSeg P q first delay n c s c3 s3 ∧
    c3.mode = .scan ∧ c3.replaying = false ∧ c3.clock = 1 ∧
    ∃ w3 : GalilScaffoldChainWatch.State, s3.chain = .watch w3 ∧ canRight s3.right ∧
      ∃ (vs3 : ScanVM) (vq3 : SearchVM),
        (galilFrame P q first).compare s3 (scanLens.set s3 vs3) ∧
        (galilFrame P q first).matched (scanLens.set s3 vs3) ∧
        searchEffect P true s3 vq3 ∧ singlePositive s3.cycle = true ∧
        ∃ w3' : GalilScaffoldChainWatch.State, vs3.chain = .broken w3'

/-- The input runs out inside a segment. -/
def InputEnd (c : Control) (s : GalilVM) : Prop :=
  ∃ (n : ℕ) (c3 : Control) (s3 : GalilVM),
    ScanSeg P q first delay n c s c3 s3 ∧ ¬ canRight s3.right

/-- A mismatching terminal at which the shift guard fails, so the controller
takes `Tick.scan_fallback` instead of a further round. -/
def GuardFail (c : Control) (s : GalilVM) : Prop :=
  ∃ (n : ℕ) (c1 : Control) (s1 : GalilVM), ScanSeg P q first delay n c s c1 s1 ∧
    c1.mode = .scan ∧ c1.replaying = false ∧ c1.clock = 1 ∧ canRight s1.right ∧
    ∃ (vs : ScanVM) (vq : SearchVM),
      (galilFrame P q first).compare s1 (scanLens.set s1 vs) ∧
      ¬ (galilFrame P q first).matched (scanLens.set s1 vs) ∧
      searchEffect P false s1 vq ∧ ¬ P.shiftGuard (afterMismatch s1 vs vq)

/-- The three terminal alternatives are stable under prefixing a segment-free
start, i.e. they are predicates of the state only; this is the form the
iteration produces. -/
def RoundEnd (c : Control) (s : GalilVM) : Prop :=
  BreakEnd P q first delay c s ∨ InputEnd P q first delay c s ∨ GuardFail P q first delay c s

/-! ## The iteration -/

/-- **L7c, fuel form.**  From a one-round oracle for an invariant `Inv`, the
controller performs `m ≤ fuel` rounds and then either ends (break / input /
guard) or still satisfies `Inv` with the fuel exhausted. -/
theorem rounds_construct (Inv : Control → GalilVM → Prop)
    (hround : ∀ c s, Inv c s → RoundEnd P q first delay c s ∨
      ∃ (c' : Control) (s' : GalilVM), Rounds P q first delay h 1 c s c' s' ∧ Inv c' s') :
    ∀ (fuel : ℕ) (c : Control) (s : GalilVM), Inv c s →
      ∃ (m : ℕ) (c' : Control) (s' : GalilVM), m ≤ fuel ∧
        Rounds P q first delay h m c s c' s' ∧
        (RoundEnd P q first delay c' s' ∨ (m = fuel ∧ Inv c' s')) := by
  intro fuel
  induction fuel with
  | zero => intro c s hI; exact ⟨0, c, s, le_refl _, .stop _ _, Or.inr ⟨rfl, hI⟩⟩
  | succ f ih =>
    intro c s hI
    rcases hround c s hI with hend | ⟨c1, s1, hstep, hI1⟩
    · exact ⟨0, c, s, Nat.zero_le _, .stop _ _, Or.inl hend⟩
    · obtain ⟨m, c', s', hm, hr, hres⟩ := ih c1 s1 hI1
      refine ⟨1 + m, c', s', by omega, rounds_append P q first delay h hstep hr, ?_⟩
      rcases hres with hend | ⟨hmf, hI'⟩
      · exact Or.inl hend
      · exact Or.inr ⟨by omega, hI'⟩

/-- **L7c, measure form.**  If each round strictly decreases a natural measure
(the controller's `2|raw| − position center` in the intended instance), the
fuel-exhausted case disappears: the rounds really do end in one of the three
alternatives. -/
theorem rounds_construct_of_measure (Inv : Control → GalilVM → Prop)
    (μ : Control → GalilVM → ℕ)
    (hround : ∀ c s, Inv c s → RoundEnd P q first delay c s ∨
      ∃ (c' : Control) (s' : GalilVM), Rounds P q first delay h 1 c s c' s' ∧ Inv c' s' ∧
        μ c' s' < μ c s) :
    ∀ (c : Control) (s : GalilVM), Inv c s →
      ∃ (m : ℕ) (c' : Control) (s' : GalilVM),
        Rounds P q first delay h m c s c' s' ∧ RoundEnd P q first delay c' s' := by
  have key : ∀ (fuel : ℕ) (c : Control) (s : GalilVM), Inv c s → μ c s ≤ fuel →
      ∃ (m : ℕ) (c' : Control) (s' : GalilVM),
        Rounds P q first delay h m c s c' s' ∧ RoundEnd P q first delay c' s' := by
    intro fuel
    induction fuel with
    | zero =>
      intro c s hI hμ
      rcases hround c s hI with hend | ⟨c1, s1, _, _, hlt⟩
      · exact ⟨0, c, s, .stop _ _, hend⟩
      · omega
    | succ f ih =>
      intro c s hI hμ
      rcases hround c s hI with hend | ⟨c1, s1, hstep, hI1, hlt⟩
      · exact ⟨0, c, s, .stop _ _, hend⟩
      · obtain ⟨m, c', s', hr, hend⟩ := ih c1 s1 hI1 (by omega)
        exact ⟨1 + m, c', s', rounds_append P q first delay h hstep hr, hend⟩
  intro c s hI
  exact key (μ c s) c s hI (le_refl _)


/-! ## The round invariant, and its preservation

`rounds_leftmost` already carries the whole package across `Rounds`; naming it
turns that theorem into the "the oracle is only ever asked at good states"
half of the iteration. -/

/-- The facts a re-shift round needs at its start: a read origin of semiperiod
`h` with its `Entry`, the `2h`-periodicity of the current span together with
its minimality, the watch at lag zero in `periodOnly`, and the leftmost live
centre invariant. -/
def RoundInv (raw : List (Fin 2)) (c : Control) (s : GalilVM) : Prop :=
  ∃ (org : ReadOrigin raw) (w : GalilScaffoldChainWatch.State),
    org.interior.length + 1 = h ∧ s.chain = .watch w ∧ zero w.lag = true ∧
    s.periodOnly = true ∧ Entry raw org (toOnly s w) ∧
    PeriodOn (encoded raw) (2*h) (org.center - org.radius) (org.center + org.radius) ∧
    (∀ p, 0 < p → p < 2*h →
      ¬ PeriodOn (encoded raw) p (org.center - org.radius) (org.center + org.radius)) ∧
    c.replaying = false ∧ MInv raw c s

/-- **The round invariant survives a round.**  Immediate from
`rounds_leftmost`, which is where all the mathematics sits (the shift of the
leftmost live centre, `periodOn_span_of_next`, `noBelow_next`). -/
theorem roundInv_preserved (raw : List (Fin 2)) {m : ℕ} {c c' : Control} {s s' : GalilVM}
    (hr : Rounds P q first delay h m c s c' s') (hI : RoundInv h raw c s) :
    RoundInv h raw c' s' := by
  obtain ⟨org, w0, hint, hs, hz, hp, he, hper, hmin, hrepl, hM⟩ := hI
  obtain ⟨org', w', hint', _, _, hchain', hz', hp', he', hper', hmin', hrepl', hM'⟩ :=
    rounds_leftmost raw P q first delay h hr w0 hp hs hz org hint he hper hmin hrepl hM
  exact ⟨org', w', hint', hchain', hz', hp', he', hper', hmin', hrepl', hM'⟩

/-- **The one genuine gap.**  `Good w` at a lag-positive background step of a
round comes from `good_of_periodOn`, whose span containment `hidx` cannot be
discharged from `RoundInv` alone: the verifier reads at index
`org.center + org.radius + 2`, which is *two past* the right end
`org.center + org.radius` of the span `rounds_leftmost` maintains.  So the
period has to be known on a strictly larger interval, and that extension is
kept here as the single named hypothesis `hidx`. -/
theorem roundInv_good (raw : List (Fin 2)) (org : ReadOrigin raw) {vm : GalilVM}
    {w : GalilScaffoldChainWatch.State}
    (hint : org.interior.length + 1 = h)
    (he : Entry raw org (toOnly vm w))
    (b : ℕ)
    (hper : PeriodOn (encoded raw) (2*h) (org.center - org.radius) b)
    (hcan : canRight w.machine.verifier)
    (hidx : org.center + org.radius + 2 ≤ b) :
    GalilScaffoldChainWatch.Good w := by
  have hsize : 2*h ≤ org.radius := by have := org.size; omega
  have hRA : org.radius ≤ org.center := org.scan.palindrome.1
  exact good_of_periodOn org h (org.center - org.radius) b hint he hper hcan ⟨by omega, hidx⟩

/-- The witnesses of `RoundInv`, for feeding `roundInv_good` at a round start. -/
theorem roundInv_entry (raw : List (Fin 2)) {c : Control} {s : GalilVM}
    (hI : RoundInv h raw c s) :
    ∃ (org : ReadOrigin raw) (w : GalilScaffoldChainWatch.State),
      org.interior.length + 1 = h ∧ s.chain = .watch w ∧ Entry raw org (toOnly s w) ∧
      PeriodOn (encoded raw) (2*h) (org.center - org.radius) (org.center + org.radius) := by
  obtain ⟨org, w, hint, hs, _, _, he, hper, _, _, _⟩ := hI
  exact ⟨org, w, hint, hs, he, hper⟩

/-! ## L7c for the concrete invariant -/

/-- **L7c.**  From the state after the first shift — where `RoundInv` holds by
`first_round_origin`/`rounds_leftmost`'s entry conditions — the controller
performs some number `m` of complete re-shift rounds and then reaches one of
the three terminals: the breaking matched comparison that `life_stepsAll`
continues from (`BreakEnd`, i.e. `hseg3`/`hmt3`/`hbroken`), the end of the
input inside a segment (`InputEnd`), or a mismatching terminal with the shift
guard false (`GuardFail`, taken by `Tick.scan_fallback`).  The round invariant
is re-established at every intermediate state, so the oracle `hround` is only
ever consulted where the periodicity and centre facts are available. -/
theorem rounds_construct_inv (raw : List (Fin 2)) (μ : Control → GalilVM → ℕ)
    (hround : ∀ c s, RoundInv h raw c s → RoundEnd P q first delay c s ∨
      ∃ (c' : Control) (s' : GalilVM),
        Rounds P q first delay h 1 c s c' s' ∧ μ c' s' < μ c s)
    (c : Control) (s : GalilVM) (hI : RoundInv h raw c s) :
    ∃ (m : ℕ) (c' : Control) (s' : GalilVM),
      Rounds P q first delay h m c s c' s' ∧ RoundInv h raw c' s' ∧
      RoundEnd P q first delay c' s' := by
  have hround' : ∀ c s, RoundInv h raw c s → RoundEnd P q first delay c s ∨
      ∃ (c' : Control) (s' : GalilVM), Rounds P q first delay h 1 c s c' s' ∧
        RoundInv h raw c' s' ∧ μ c' s' < μ c s := by
    intro c0 s0 h0
    rcases hround c0 s0 h0 with hend | ⟨c1, s1, hstep, hlt⟩
    · exact Or.inl hend
    · exact Or.inr ⟨c1, s1, hstep, roundInv_preserved P q first delay h raw hstep h0, hlt⟩
  obtain ⟨m, c', s', hr, hend⟩ :=
    rounds_construct_of_measure P q first delay h _ μ hround' c s hI
  exact ⟨m, c', s', hr, roundInv_preserved P q first delay h raw hr hI, hend⟩

#print axioms scanSeg_append
#print axioms rounds_append
#print axioms roundStep_of_shiftRun
#print axioms rounds_construct
#print axioms rounds_construct_of_measure
#print axioms roundInv_preserved
#print axioms roundInv_good
#print axioms roundInv_entry
#print axioms rounds_construct_inv

end PalPeg.GalilScaffoldChainInputSupply
