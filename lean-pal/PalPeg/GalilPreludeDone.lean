import PalPeg.GalilMismatchCaught
import PalPeg.GalilSegmentCount
import PalPeg.GalilScaffoldTopWatchRun

/-!
# `hcaught`: the chain prelude is over long before the candidate's extent runs out

`PalPeg/GalilMismatchCaught.lean` closes `WatchStop.mismatchOther` from two
halves.  Inside the found candidate's guaranteed extent (`k + 1 ≤ 2*h`) the
scan cannot mismatch at all (`no_mismatch_before_caught`).  Outside it, the
constructor's own `hno` is contradicted by `hcaught`: the chain is already a
zero-lag `.watch`.  This module proves `hcaught`, i.e. the *timing*.

**The prelude is `2h + 2` chain ticks.**  The chain starts as `.copy`
(`chainStart`), copies `h` answer bits and takes the `copyEnd` tick into
`.back` (`GalilBranchInvariants.copy_run_to_back`: `ChainSteps (n+1)` with
`n = h`), then walks back in `ls.length + 2 = h + 1` ticks
(`GalilScaffoldChainPeriod.back_exact`, lifted by `back_steps`) and enters
`.watch` with an entry lag bounded by the prelude's match count
(`GalilLedgerObligations.verifier_catchup`: `lag0 ≤ 2*h + 2`).  This is the
*only* thing assumed here, as the single named hypothesis `PreludeEnds`.

**The scan is `2048` times slower.**  `watchSegE_match_spacing` (new, proved
here by induction on the segment) says a `WatchSegE` run spends at least
`delay` ticks per matched comparison:

    es.count true * delay + c.clock ≤ es.length + delay

— `wait` keeps the clock, `count`/`countR` only decrement it, and the three
match constructors fire exactly at `clock = 1` and reload to `delay`.  This is
the segment-level form of `LocalBudget.radius_changes_slowly` /
`scanReload_le_one`, counting *all* the reloads rather than bounding a single
window.  Since `watchSegE_events` gives `value t.radius = value s.radius +
es.count true`, consuming `2h` places costs at least `2*h*2048 - 2048` ticks.

**Hence the catch-up finishes first.**  With `h ≥ 1` the tail after the
`2h + 2` prelude ticks still contains at least `2h + 2` *non-matched* ticks
(`rest.count false`), and `GalilScaffoldChainLag.catches` pays a lag of at most
`2h + 2` down to zero on exactly those ticks.  `chainTicks_from_watch` (new)
says the chain can only stay `.watch` or become `.broken`, so with the break
excluded the final chain is a zero-lag `.watch`.

**Gaps (stated, not hidden).**

* `PreludeEnds` — the chain-tick count of the copy/back prelude together with
  its exit lag bound.  One named hypothesis, as required.
* `hnb` — the chain has not `.broken`.  A break is a genuine alternative
  outcome of `ChainMatched`, and `hcaught`'s conclusion is false at a broken
  chain, so this cannot be proved away; in the caller it is discharged by the
  break's own handling (`WatchStop.break`), not here.
-/

set_option autoImplicit false

namespace PalPeg.GalilPreludeDone

open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier GalilScaffoldChainInputSupply

/-! ## 1. One matched comparison per `delay` ticks -/

theorem count_false_cons (es : List Bool) : (false :: es).count true = es.count true := by simp

theorem count_true_cons (es : List Bool) : (true :: es).count true = es.count true + 1 := by simp

/-- **Match spacing.**  Along a `WatchSegE` run the controller's clock is
reloaded to `delay` at every matched comparison and can only be decremented in
between, so the number of matched events is bounded by the number of ticks
divided by `delay`.  In additive form, with the entry clock accounted for:
`es.count true * delay + c.clock ≤ es.length + delay`. -/
theorem watchSegE_match_spacing (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    {es : List Bool} {c c' : Control} {s t : GalilVM}
    (h : WatchSegE P q first delay es c s c' t) :
    c.clock ≤ delay → es.count true * delay + c.clock ≤ es.length + delay := by
  induction h with
  | stop c s => intro hc; simpa using hc
  | wait c s s' _ _ _ _ _ ih =>
    intro hc
    have hI := ih hc
    rw [count_false_cons, List.length_cons]
    omega
  | count c s s' _ _ _ hcl _ _ ih =>
    intro hc
    have hI := ih (by dsimp only; omega)
    dsimp only at hI
    rw [count_false_cons, List.length_cons]
    omega
  | «match» c s vs vq o _ _ _ hcl _ _ _ _ _ _ ih =>
    intro hc
    have hI := ih (le_refl delay)
    dsimp only at hI
    rw [count_true_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega
  | matchIdle c s vs vq o _ _ _ hcl _ _ _ _ _ _ _ _ _ ih =>
    intro hc
    have hI := ih (le_refl delay)
    dsimp only at hI
    rw [count_true_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega
  | countR c s s' _ _ hcl _ _ _ ih =>
    intro hc
    have hI := ih (by dsimp only; omega)
    dsimp only at hI
    rw [count_false_cons, List.length_cons]
    omega
  | matchIdleR c s vs vq o _ _ hcl _ _ _ _ _ _ _ _ _ _ ih =>
    intro hc
    have hI := ih (le_refl delay)
    dsimp only at hI
    rw [count_true_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-! ## 2. A watching chain stays watching or breaks -/

/-- Chain ticks out of a `.watch` can only reach `.watch` or `.broken`:
`ChainStep` on a watch is `watchStep`, and `ChainMatched` on a watch is either
`watch` or `breaks`; `broken_stays` absorbs the rest. -/
theorem chainTicks_from_watch (es : List Bool) :
    ∀ {w : GalilScaffoldChainWatch.State} {z : ChainVM},
      ChainTicks es (.watch w) z → (∃ w', z = .watch w') ∨ (∃ w', z = .broken w') := by
  induction es with
  | nil => intro w z h; cases h; exact Or.inl ⟨w, rfl⟩
  | cons a es ih =>
    intro w z h
    cases h with
    | cons ht hr =>
      obtain ⟨m, hs, hm⟩ := ht
      cases hs with
      | watchStep _ m' hi =>
        cases a with
        | false => simp only [Bool.false_eq_true, if_false] at hm; subst hm; exact ih hr
        | true =>
          simp only [if_true] at hm
          cases hm with
          | watch _ w'' ho => exact ih hr
          | breaks _ w'' hb => exact Or.inr (broken_stays es hr)
      | watchBreak _ hb =>
        cases a with
        | false =>
          simp only [Bool.false_eq_true, if_false] at hm
          subst hm
          exact Or.inr (broken_stays es hr)
        | true =>
          simp only [if_true] at hm
          cases hm with
          | brokenMatched _ => exact Or.inr (broken_stays es hr)

/-! ## 3. The one assumed chain-tick-count fact -/

/-- **The isolated hypothesis.**  The prelude of a chain started at
`chainStart answer c walker ver radius` — `h` `copyBit` ticks, the `copyEnd`
tick, `h + 1` `backStep`/`backDone` ticks — takes exactly `2*h + 2` chain
ticks and leaves the chain watching with a canonical, nonnegative lag of at
most `2*h + 2`.

Suppliers, none of which is carried here: `GalilBranchInvariants.copy_run_to_back`
(`n + 1` copy ticks), `GalilScaffoldChainPeriod.back_exact` / `back_steps`
(`h + 1` back ticks), `prep_watch_start` (the same count against a `WatchSegE`
index `bs ++ dm :: cs`), and `GalilLedgerObligations.verifier_catchup`
(`lag0 ≤ 2*h + 2`). -/
def PreludeEnds (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    (answer : GalilScaffoldTape.Tape) (cc : Fin 3) (walker : GalilScaffoldPlace.Place)
    (ver : PlaceHead) (radius : Counter) (h : ℕ) : Prop :=
  ∀ {es : List Bool} {c0 c1 : Control} {v0 v1 : GalilVM},
    es.length = 2 * h + 2 → c0.clock ≤ delay →
    WatchSegE P q first delay es c0 v0 c1 v1 →
    v0.chain = chainStart answer cc walker ver radius →
    ∃ w : GalilScaffoldChainWatch.State,
      v1.chain = .watch w ∧ GalilScaffoldChainWatch.CanonicalState w ∧
        0 ≤ value w.lag ∧ value w.lag ≤ ((2 * h + 2 : ℕ) : ℤ)

/-! ## 4. The prelude is over before the extent is -/

/-- **`prelude_done_before_extent`.**  Take a `WatchSegE` run at the place
clock `delay = 2048` that begins at the chain start (`v0.chain = chainStart …`)
and whose scan radius has advanced by `2*h` places — i.e. the run reaches the
end of the found candidate's guaranteed extent `k + 1 ≤ 2*h`.  Then the chain
is already a zero-lag `.watch`, which is exactly `hcaught` of
`GalilMismatchCaught.mismatchOther_impossible`.

The proof is the collision of two counts.  Consuming `2*h` places costs at
least `2*h*2048 - 2048` ticks (`watchSegE_match_spacing` against
`watchSegE_events`'s `value t.radius = value s.radius + es.count true`), while
the prelude costs `2*h + 2` ticks (`PreludeEnds`) and the catch-up needs only
`2*h + 2` further non-matched ticks (`GalilScaffoldChainLag.catches` against an
entry lag `≤ 2*h + 2`).  For `h ≥ 1` the first number dwarfs the sum of the
other two. -/
theorem prelude_done_before_extent (P : Shared) (q : ℕ) (first : Fin 9)
    (answer : GalilScaffoldTape.Tape) (cc : Fin 3) (walker : GalilScaffoldPlace.Place)
    (ver : PlaceHead) (radius : Counter) (h : ℕ) (hh : 1 ≤ h)
    (hprelude : PreludeEnds P q first 2048 answer cc walker ver radius h)
    {es : List Bool} {c0 c1 : Control} {v0 v1 : GalilVM}
    (hseg : WatchSegE P q first 2048 es c0 v0 c1 v1)
    (hclock : c0.clock ≤ 2048)
    (hstart : v0.chain = chainStart answer cc walker ver radius)
    (hrad : value v0.radius + ((2 * h : ℕ) : ℤ) ≤ value v1.radius)
    (hnb : ∀ w : GalilScaffoldChainWatch.State, v1.chain ≠ .broken w) :
    ∃ w : GalilScaffoldChainWatch.State, v1.chain = .watch w ∧ zero w.lag = true := by
  -- the chain is not idle at the start
  have hne0 : v0.chain ≠ .idle := by rw [hstart]; intro h0; cases h0
  -- places consumed = matched events
  have hev := watchSegE_events P q first 2048 hseg hne0
  have hcount : 2 * h ≤ es.count true := by
    have hr := hev.2.2.2.2.1
    omega
  -- one matched comparison per 2048 ticks
  have hsp := watchSegE_match_spacing P q first 2048 hseg hclock
  -- so the run is long
  have hlen : 2 * h + 2 ≤ es.length := by omega
  -- split off the prelude
  have hcat : es.take (2 * h + 2) ++ es.drop (2 * h + 2) = es := List.take_append_drop _ _
  obtain ⟨c'', s'', seg1, seg2⟩ :=
    watchSegE_append P q first 2048 (es.take (2 * h + 2)) (by rw [hcat]; exact hseg)
  have hpre : (es.take (2 * h + 2)).length = 2 * h + 2 := by
    rw [List.length_take]; omega
  obtain ⟨w, hw, hcan, hn, hlag⟩ := hprelude hpre hclock seg1 hstart
  -- the tail
  have hclock'' : c''.clock ≤ 2048 := watchSegE_clock_le P q first 2048 seg1 hclock
  have hsp2 := watchSegE_match_spacing P q first 2048 seg2 hclock''
  have hsplit : (es.take (2 * h + 2)).length + (es.drop (2 * h + 2)).length = es.length := by
    rw [← List.length_append, hcat]
  have hbc := GalilScaffoldChainLag.bool_counts (es.drop (2 * h + 2))
  -- enough non-matched ticks remain to pay the lag down
  have hfalse : 2 * h + 2 ≤ (es.drop (2 * h + 2)).count false := by omega
  -- the chain ticks of the tail are a watch run
  have hne1 : s''.chain ≠ .idle := by rw [hw]; intro h0; cases h0
  have hev2 := watchSegE_events P q first 2048 seg2 hne1
  have hticks : ChainTicks (es.drop (2 * h + 2)) (.watch w) v1.chain := by
    rw [← hw]; exact hev2.1
  rcases chainTicks_from_watch _ hticks with ⟨w', hw'⟩ | ⟨w', hw'⟩
  · refine ⟨w', hw', ?_⟩
    rw [hw'] at hticks
    have hsupply : value w.lag ≤ (((es.drop (2 * h + 2)).count false : ℕ) : ℤ) := by
      refine le_trans hlag ?_
      exact_mod_cast hfalse
    exact GalilScaffoldChainLag.catches (chainTicks_watch_run _ hticks) hcan hn hsupply
  · exact absurd hw' (hnb w')

#print axioms count_false_cons
#print axioms count_true_cons
#print axioms watchSegE_match_spacing
#print axioms chainTicks_from_watch
#print axioms prelude_done_before_extent

end PalPeg.GalilPreludeDone
