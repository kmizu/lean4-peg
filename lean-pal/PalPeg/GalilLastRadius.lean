import PalPeg.GalilRestartStage

/-!
# The missing upper bound at the found-cycle restart

`GalilRestartStage.foundCycleStage_not_implied` shows that the facts the
scaffold exports at the period break of a found cycle (`rounds_break`,
`life_restarted`) do not yet imply the stage-entry budget
`3 * Rad ≤ 5 * value last`.  What is missing is an *upper* bound on the
restart radius in terms of the lower bound `last` installed by `restartVM`.

This file proves the chain-side half of that bound unconditionally:

* the `last` counter of a successful sweep is at most `2 * h` places behind
  its `distance` counter (`sweep_gap`), because `distance` counts consumed
  places one by one while a semiperiod boundary — which copies `boundary`
  into `last` and `distance` into `boundary` — passes every `h` places;
* the bound survives the uniform counter offset of `k` chain shifts
  (`offset_gap`) and the failing consume of the break itself
  (`break_gap`), so it holds at `w3'.machine.control`;
* together with `watch_last_lower` (`3 * h ≤ value last`) an upper bound
  `Rad ≤ value last + 2 * h` gives `StageEntry Rad last`
  (`stageEntry_of_gap`).

The one remaining gap is isolated as `RadiusConsumed`: the restart radius
does not exceed the number of places the chain has consumed since the watch
start, plus the single unconsumed place of the break.  See the comment at
`RadiusConsumed` for why this is the lockstep statement and what base case
is still missing.
-/

set_option autoImplicit false

namespace PalPeg.GalilLastRadius

open GalilScaffoldCounter GalilScaffoldChainConsume GalilScaffoldChainSweep
  GalilScaffoldChainPrediction GalilScaffoldChainInputSupply

/-! ## 1. A failing consume is permanent, and a successful one counts a place -/

theorem consume_broken_mono (s : State) (seen : Option (Fin 3)) (h : s.broken = true) :
    (consume s seen).broken = true := by
  cases ht : symbol s.period.focus with
  | none => simp [consume, ht]
  | some a =>
    by_cases ha : seen = some a
    · simp [consume, ht, ha, h]
    · simp [consume, ht, ha]

theorem run_broken_mono (s : State) (w : List (Fin 3)) (h : s.broken = true) :
    (run s w).broken = true := by
  induction w generalizing s with
  | nil => exact h
  | cons a w ih => exact ih (consume s (some a)) (consume_broken_mono s (some a) h)

/-- The only way a consume keeps `broken = false` is the matching branch,
which raises `distance` by exactly one. -/
theorem consume_distance (s : State) (seen : Option (Fin 3))
    (hs : s.broken = false) (h : (consume s seen).broken = false) :
    value (consume s seen).distance = value s.distance + 1 := by
  cases ht : symbol s.period.focus with
  | none => simp [consume, ht] at h
  | some a =>
    by_cases ha : seen = some a
    · simp [consume, ht, ha, inc_value]
    · simp [consume, ht, ha] at h

/-- `distance` of a successful sweep counts the consumed places. -/
theorem run_distance (s : State) (w : List (Fin 3)) (hs : s.broken = false)
    (h : (run s w).broken = false) :
    value (run s w).distance = value s.distance + (w.length : ℤ) := by
  induction w generalizing s with
  | nil => simp [run]
  | cons a w ih =>
    have hstep : (consume s (some a)).broken = false := by
      by_contra hb
      have : (consume s (some a)).broken = true := by
        cases hbb : (consume s (some a)).broken with
        | true => rfl
        | false => exact absurd hbb hb
      have := run_broken_mono (consume s (some a)) w this
      rw [show run s (a :: w) = run (consume s (some a)) w from rfl] at h
      rw [this] at h; cases h
    have hd := consume_distance s (some a) hs hstep
    have hrec := ih (consume s (some a)) hstep (by
      rw [show run s (a :: w) = run (consume s (some a)) w from rfl] at h; exact h)
    rw [show run s (a :: w) = run (consume s (some a)) w from rfl, hrec, hd]
    simp only [List.length_cons]
    push_cast
    ring

/-! ## 2. The aligned prefixes: a boundary every `h` places -/

theorem ready_values (center b : Fin 3) (xs : List (Fin 3)) :
    value (ready center xs b).distance = 0 ∧ value (ready center xs b).boundary = 0 ∧
      value (ready center xs b).last = 0 ∧ (ready center xs b).broken = false ∧
      (ready center xs b).forward = true := by
  refine ⟨?_, ?_, ?_, rfl, rfl⟩ <;> simp [ready, reset, value]

/-- A state at a semiperiod boundary: the period tape is back at the ready
position, the traversal is forward, nothing is broken, `boundary` has just
caught up with `distance`, and `distance` is at most one semiperiod past
`last`. -/
structure Aligned (center b : Fin 3) (xs : List (Fin 3)) (s : State) : Prop where
  period : s.period = (ready center xs b).period
  forward : s.forward = true
  unbroken : s.broken = false
  caught : value s.boundary = value s.distance
  gap : value s.distance ≤ value s.last + (xs.length + 1 : ℕ)

theorem aligned_ready (center b : Fin 3) (xs : List (Fin 3)) :
    Aligned center b xs (ready center xs b) := by
  obtain ⟨hd, hb, hl, hbr, hf⟩ := ready_values center b xs
  refine ⟨rfl, hf, hbr, by rw [hd, hb], ?_⟩
  rw [hd, hl]
  push_cast
  omega

/-- A full round trip of `2 * h` places lands on the next aligned state. -/
theorem aligned_bounce {center b : Fin 3} {xs : List (Fin 3)} {s : State}
    (ha : Aligned center b xs s) :
    Aligned center b xs (run s (bounce center b xs)) ∧
      value (run s (bounce center b xs)).distance =
        value s.distance + 2 * (xs.length + 1 : ℕ) := by
  have hr := round_trip center b xs s ha.period ha.forward
  dsimp only at hr
  obtain ⟨hp, hd, hb, hl, _, hf, hbr⟩ := hr
  refine ⟨⟨hp.trans ha.period, hf, hbr.trans ha.unbroken, by rw [hb], ?_⟩, by rw [hd]; push_cast; ring⟩
  rw [hd, hl]
  push_cast
  ring_nf
  omega

/-- `q` round trips. -/
theorem aligned_cycles (center b : Fin 3) (xs : List (Fin 3)) (q : ℕ) :
    ∀ s : State, Aligned center b xs s →
      Aligned center b xs (run s (cycles (bounce center b xs) q)) ∧
        value (run s (cycles (bounce center b xs) q)).distance =
          value s.distance + 2 * q * (xs.length + 1 : ℕ) := by
  induction q with
  | zero => intro s ha; exact ⟨by simpa [cycles, run] using ha, by simp [cycles, run]⟩
  | succ q ih =>
    intro s ha
    obtain ⟨ha1, hd1⟩ := aligned_bounce ha
    obtain ⟨ha2, hd2⟩ := ih _ ha1
    refine ⟨by simpa [cycles, run_append] using ha2, ?_⟩
    rw [show run s (cycles (bounce center b xs) (q+1)) =
          run (run s (bounce center b xs)) (cycles (bounce center b xs) q) by
        rw [cycles, run_append], hd2, hd1]
    push_cast
    ring

/-- The forward half round trip of `h` places also ends one semiperiod past
`last`, using `boundary = distance` at the aligned start. -/
theorem half_gap {center b : Fin 3} {xs : List (Fin 3)} {s : State}
    (ha : Aligned center b xs s) :
    (run s (xs ++ [b])).broken = false ∧
      value (run s (xs ++ [b])).distance ≤
        value (run s (xs ++ [b])).last + (xs.length + 1 : ℕ) ∧
      value (run s (xs ++ [b])).distance = value s.distance + (xs.length + 1 : ℕ) := by
  have hr := forward_boundary center b xs s ha.period ha.forward
  dsimp only at hr
  obtain ⟨hd, _, hl, _, _, hbr, _⟩ := hr
  refine ⟨hbr.trans ha.unbroken, ?_, by rw [hd]; push_cast; ring⟩
  rw [hd, hl, ha.caught]
  push_cast
  omega

/-- For every number `k` of semiperiods there is a successful word of exactly
`k * h` places that ends at most one semiperiod past `last`. -/
theorem aligned_word (center b : Fin 3) (xs : List (Fin 3)) (k : ℕ) :
    ∃ word : List (Fin 3), word.length = k * (xs.length + 1) ∧
      (run (ready center xs b) word).broken = false ∧
      value (run (ready center xs b) word).distance ≤
        value (run (ready center xs b) word).last + (xs.length + 1 : ℕ) := by
  have hbl : (bounce center b xs).length = 2 * (xs.length + 1) := by
    simp [bounce]; omega
  rcases Nat.even_or_odd k with ⟨q, hq⟩ | ⟨q, hq⟩
  · obtain ⟨ha, _⟩ := aligned_cycles center b xs q _ (aligned_ready center b xs)
    refine ⟨cycles (bounce center b xs) q, ?_, ha.unbroken, ha.gap⟩
    rw [cycles_length, hbl, hq]; ring
  · obtain ⟨ha, _⟩ := aligned_cycles center b xs q _ (aligned_ready center b xs)
    obtain ⟨hbr, hgap, _⟩ := half_gap ha
    refine ⟨cycles (bounce center b xs) q ++ (xs ++ [b]), ?_, ?_, ?_⟩
    · simp only [List.length_append, cycles_length, hbl, hq]
      simp
      ring
    · rw [run_append]; exact hbr
    · rw [run_append]; exact hgap

theorem ordered_ready (center b : Fin 3) (xs : List (Fin 3)) :
    GalilScaffoldChainRestart.Ordered (ready center xs b) := by
  simp [GalilScaffoldChainRestart.Ordered, ready, reset, value]

/-! ## 3. The sweep gap: `distance < last + 2 * h` -/

/-- **The chain-side bound.**  In any successful sweep from `ready`, the
number of consumed places is strictly less than `value last + 2 * h`:
the aligned prefix of `⌊L / h⌋` semiperiods has already pushed `last` to
within one semiperiod of its own `distance`, and the leftover is shorter
than a semiperiod. -/
theorem sweep_gap (center b : Fin 3) (xs actual : List (Fin 3))
    (ha : (run (ready center xs b) actual).broken = false) :
    value (run (ready center xs b) actual).distance + 1 ≤
      value (run (ready center xs b) actual).last + 2 * (xs.length + 1 : ℕ) := by
  have hpos : 0 < xs.length + 1 := Nat.succ_pos _
  obtain ⟨q, r, hr, hlen⟩ : ∃ q r : ℕ, r < xs.length + 1 ∧
      actual.length = q * (xs.length + 1) + r :=
    ⟨actual.length / (xs.length + 1), actual.length % (xs.length + 1),
      Nat.mod_lt _ hpos, (Nat.div_add_mod' actual.length (xs.length + 1)).symm⟩
  obtain ⟨word, hwl, hwb, hwg⟩ := aligned_word center b xs q
  have hle : word.length ≤ actual.length := by omega
  have htake := successful_prefix word actual (ready center xs b) hwb ha hle
  have hsplit : actual = word ++ actual.drop word.length := by
    have he := List.take_append_drop word.length actual
    rw [htake] at he
    exact he.symm
  have hmid : run (ready center xs b) actual =
      run (run (ready center xs b) word) (actual.drop word.length) := by
    conv_lhs => rw [hsplit]
    rw [run_append]
  have hordw := GalilScaffoldChainRestart.run_order (ready center xs b) word
    (ordered_ready center b xs)
  have hordd := GalilScaffoldChainRestart.run_order (run (ready center xs b) word)
    (actual.drop word.length) hordw.1
  have hlast : value (run (ready center xs b) word).last ≤
      value (run (ready center xs b) actual).last := by
    rw [hmid]; exact hordd.2
  obtain ⟨hrd, _, _, hrbr, _⟩ := ready_values center b xs
  have hdw : value (run (ready center xs b) word).distance = (word.length : ℤ) := by
    rw [run_distance _ _ hrbr hwb, hrd]; ring
  have hda : value (run (ready center xs b) actual).distance = (actual.length : ℤ) := by
    rw [run_distance _ _ hrbr ha, hrd]; ring
  have hcast : (actual.length : ℤ) + 1 ≤ (word.length : ℤ) + ((xs.length + 1 : ℕ) : ℤ) := by
    have : actual.length + 1 ≤ word.length + (xs.length + 1) := by omega
    exact_mod_cast this
  rw [hdw] at hwg
  push_cast at hwg hcast hda hlast ⊢
  omega

/-! ## 4. The bound survives the shift offset and the break -/

/-- `k` chain shifts lower all three counters uniformly, so the gap is
unchanged (`Offset`, `PalPeg/GalilScaffoldChainReadOrigin.lean`). -/
theorem offset_gap {k : ℤ} {c : State} {center b : Fin 3} {xs word : List (Fin 3)}
    (ho : Offset k c (run (ready center xs b) word))
    (hw : (run (ready center xs b) word).broken = false) :
    value c.distance + 1 ≤ value c.last + 2 * (xs.length + 1 : ℕ) := by
  have h := sweep_gap center b xs word hw
  rw [ho.distance, ho.last]
  omega

/-- The failing consume of the break changes neither `distance` nor `last`. -/
theorem break_gap (s : State) (seen : Option (Fin 3)) (hs : s.broken = false)
    (hb : (consume s seen).broken = true) :
    value (consume s seen).distance = value s.distance ∧
      value (consume s seen).last = value s.last := by
  cases ht : symbol s.period.focus with
  | none => simp [consume, ht]
  | some a =>
    by_cases ha : seen = some a
    · simp [consume, ht, ha, hs] at hb
    · simp [consume, ht, ha]

/-! ## 5. `StageEntry` from the gap and `watch_last_lower` -/

/-- **The arithmetic that closes the budget.**  With the chain's own lower
bound `3 * h ≤ value last` (`watch_last_lower`,
`PalPeg/GalilScaffoldChainInputSupply.lean`) an upper bound
`Rad ≤ value last + 2 * h` is exactly enough for `3 * Rad ≤ 5 * value last`:
`3 * (k + 2h) = 3k + 6h ≤ 3k + 2k`. -/
theorem stageEntry_of_gap (Rad h : ℕ) (last : Counter)
    (hlow : (3 * h : ℤ) ≤ value last)
    (hup : (Rad : ℤ) ≤ value last + 2 * (h : ℕ)) :
    StageEntry Rad last := by
  intro k hk
  rw [hk] at hlow hup
  have h1 : (3 * h : ℤ) ≤ (k : ℤ) := hlow
  have h2 : (Rad : ℤ) ≤ (k : ℤ) + 2 * (h : ℕ) := hup
  have : (3 * Rad : ℤ) ≤ (5 * k : ℤ) := by omega
  exact_mod_cast this

/-! ## 6. The one remaining gap -/

/-- **The isolated hypothesis.**  The restart radius does not exceed the
number of places the chain has consumed since the watch start, plus the one
place of the failing break comparison.

This is the lockstep statement of the projection: `onlyCompareNext`
(`PalPeg/GalilScaffoldTopOnly.lean`) raises `radius` by one *and* performs
the chain's `immediate` consume, i.e. raises `distance` by one; a shift round
of `CompareRounds` (`PalPeg/GalilScaffoldChainReadOrigin.lean`) starts from
`inc t.radius` and runs `h` `shiftTick`s, lowering `radius` by `h`, while the
matching `ChainShiftRun` lowers `distance` by the same `h` (`chain_shift_values`).
So `radius - distance` is invariant along the whole watch, and the claim is
that it is `≤ 1` — one unit for the break place, which raises the radius but
whose consume fails and therefore does not raise `distance`.

What is *not* available is the base case at the fresh watch start: the
`ReadOrigin` record only states `startBefore : position start ≤ center`,
whereas the invariant needs the shifted form
`position start + shifts * h ≤ center` (the centre has advanced by one
semiperiod per shift, `rounds_origin`, while the verifier start has not
moved).  With that strengthening of `startBefore`, `RadiusConsumed` follows
from `ReadOrigin.length`, `ReadOrigin.endPosition` and `Reads`. -/
def RadiusConsumed (Rad : ℕ) (c : State) : Prop :=
  (Rad : ℤ) ≤ value c.distance + 1

/-- **The found-cycle stage entry.**  `w3'.machine.control` is the break
state: the failing consume of a control that is the `k`-shift offset of a
successful sweep from `ready` (`ReadOrigin.offset`, `ReadOrigin.unbroken`,
`Offset.shift`, and `restartVM` installing `lower := ...control.last`).
Under `watch_last_lower` and the single hypothesis `RadiusConsumed` the
stage budget of `search_result_at_tick` / `restarted_next_found` holds. -/
theorem foundCycleStage (orgRadius h m n : ℕ) {k : ℤ}
    {center b : Fin 3} {xs word : List (Fin 3)} {cpre : State}
    {seen : Option (Fin 3)} {last : Counter}
    (hh : xs.length + 1 = h)
    (hoff : Offset k cpre (run (ready center xs b) word))
    (hsweep : (run (ready center xs b) word).broken = false)
    (hpre : cpre.broken = false)
    (hbreak : (consume cpre seen).broken = true)
    (hlast : last = (consume cpre seen).last)
    (hlow : (3 * h : ℤ) ≤ value last)
    (hcons : RadiusConsumed (foundRestartRadius orgRadius h m n) cpre) :
    StageEntry (foundRestartRadius orgRadius h m n) last := by
  obtain ⟨hd, hl⟩ := break_gap cpre seen hpre hbreak
  have hgap := offset_gap hoff hsweep
  rw [hh] at hgap
  refine stageEntry_of_gap _ h last hlow ?_
  rw [hlast, hl]
  have hd' := hd
  have : (foundRestartRadius orgRadius h m n : ℤ) ≤ value cpre.distance + 1 := hcons
  omega

/-- The same conclusion packaged as the `FoundCycleStage` obligation of
`PalPeg/GalilRestartStage.lean`. -/
theorem foundCycleStage' (orgRadius h m n : ℕ) {k : ℤ}
    {center b : Fin 3} {xs word : List (Fin 3)} {cpre : State}
    {seen : Option (Fin 3)} {last : Counter}
    (hh : xs.length + 1 = h)
    (hoff : Offset k cpre (run (ready center xs b) word))
    (hsweep : (run (ready center xs b) word).broken = false)
    (hpre : cpre.broken = false)
    (hbreak : (consume cpre seen).broken = true)
    (hlast : last = (consume cpre seen).last)
    (hlow : (3 * h : ℤ) ≤ value last)
    (hcons : RadiusConsumed (foundRestartRadius orgRadius h m n) cpre) :
    FoundCycleStage orgRadius h m n last :=
  foundCycleStage orgRadius h m n hh hoff hsweep hpre hbreak hlast hlow hcons

#print axioms run_broken_mono
#print axioms run_distance
#print axioms aligned_cycles
#print axioms half_gap
#print axioms aligned_word
#print axioms sweep_gap
#print axioms offset_gap
#print axioms break_gap
#print axioms stageEntry_of_gap
#print axioms foundCycleStage
#print axioms foundCycleStage'

end PalPeg.GalilLastRadius
