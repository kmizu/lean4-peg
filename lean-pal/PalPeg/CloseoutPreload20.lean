import PalPeg.CloseoutPreload19

/-!
# Where `LiveL` comes from: the match clock over an all-available tick stream

`CloseoutPreload19` §2 closes gap (b) of `CloseoutPreload18` §4 *modulo* an
explicit liveness clause `LiveL 2048 as`, and §3 shows that clause cannot be
recovered from `PacedL`/`RdPaced`.  So it has to come from the machine.  This
file supplies it.

The machine fact is the one already used for gap (a): in the real-time model a
fresh input symbol arrives on every tick, so inside a scan leg every tick is an
*available* scan tick (`GalilScaffoldTop.Tick`'s `available := replaying ∨
canRight`, fed by `GalilScaffoldChainInputSupply`), and an available tick always
decrements the controller clock `GalilScaffoldMatchClock.run`.  A clock that
starts in phase (`1 ≤ clock ≤ delay`) and is decremented every tick therefore
fires at least once in every window of `delay` consecutive ticks — which is
exactly `LiveL delay`.

To say this we need the *trace* of the clock, not just its firing count, so §1
defines `runTrace` (one boolean per tick, `true` = a comparison fired) and checks
it refines `GalilScaffoldMatchClock.run` (`runTrace_count`, `runTrace_length`).
§2 proves the window lemma and the main theorem `liveL_of_clock`.  §3 hands the
result to `CloseoutPreload19.wait_leg_length_le`.

The `.wait` mode does not interfere: `searchStep .wait` consumes the scan event
`true` to pay down the debt, so the comparisons keep firing while the search
itself is parked — the trace is the scan's firing list either way.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPreload20

open PalPeg
open PalPeg.GalilScaffoldChainInputSupply (SearchVM)
open PalPeg.GalilScaffoldSearchFinish (Mode)
open PalPeg.GalilScaffoldCounter (Canonical value zero)
open PalPeg.CloseoutPreload14 (WaitTrace)
open PalPeg.CloseoutPreload19 (LiveL wait_leg_length_le)

/-! ## 1. The firing trace of the match clock -/

/-- The per-tick trace of `GalilScaffoldMatchClock.run`: one boolean per tick,
`true` exactly on the ticks where a comparison fires.  Unavailable ticks
(`false`) carry the clock unchanged and never fire, just as in `run`. -/
def runTrace (delay : ℕ) : ℕ → List Bool → List Bool
  | _, [] => []
  | clock, false :: bs => false :: runTrace delay clock bs
  | clock, true :: bs =>
      if clock = 1 then true :: runTrace delay delay bs
      else false :: runTrace delay (clock - 1) bs

theorem runTrace_length (delay clock : ℕ) (ts : List Bool) :
    (runTrace delay clock ts).length = ts.length := by
  induction ts generalizing clock with
  | nil => simp [runTrace]
  | cons t ts ih =>
    cases t with
    | false => simp [runTrace, ih]
    | true =>
      by_cases he : clock = 1 <;> simp [runTrace, he, ih]

/-- `runTrace` refines `run`: its `true`s are exactly the firings counted by
`(run delay clock ts).2`. -/
theorem runTrace_count (delay clock : ℕ) (ts : List Bool) :
    (runTrace delay clock ts).count true
      = (PalPeg.GalilScaffoldMatchClock.run delay clock ts).2 := by
  induction ts generalizing clock with
  | nil => simp [runTrace, PalPeg.GalilScaffoldMatchClock.run]
  | cons t ts ih =>
    cases t with
    | false =>
      simp [runTrace, PalPeg.GalilScaffoldMatchClock.run, ih]
    | true =>
      by_cases he : clock = 1
      · simp [runTrace, PalPeg.GalilScaffoldMatchClock.run, he, ih]
      · simp [runTrace, PalPeg.GalilScaffoldMatchClock.run, he, ih]

#print axioms runTrace_length
#print axioms runTrace_count

/-! ## 2. Every window of `delay` available ticks holds a firing -/

/-- Counting `true`s only grows when a prefix is extended. -/
theorem count_take_mono {l : List Bool} {a b : ℕ} (hab : a ≤ b) :
    (l.take a).count true ≤ (l.take b).count true := by
  have hsplit : (l.take b).take a ++ (l.take b).drop a = l.take b :=
    List.take_append_drop a (l.take b)
  have hta : (l.take b).take a = l.take a := by
    rw [List.take_take, Nat.min_eq_left hab]
  have := congrArg (fun z : List Bool => z.count true) hsplit
  simp only [List.count_append, hta] at this
  omega

/-- **The first firing arrives within `clock` available ticks.**  If the clock is
in phase and at least `clock` available ticks follow, one of them fires. -/
theorem fire_within (delay : ℕ) :
    ∀ (clock : ℕ) (ts : List Bool), 1 ≤ clock → clock ≤ ts.length →
      (∀ b ∈ ts, b = true) →
      0 < ((runTrace delay clock ts).take clock).count true := by
  intro clock
  induction clock with
  | zero => intro _ h _; omega
  | succ k ih =>
    intro ts _ hlen hall
    cases ts with
    | nil => simp at hlen
    | cons t ts =>
      have ht : t = true := hall t (by simp)
      subst ht
      by_cases he : k + 1 = 1
      · simp [runTrace, he]
      · have hk : 1 ≤ k := by omega
        have hlen' : k ≤ ts.length := by simpa using Nat.le_of_succ_le_succ hlen
        have hall' : ∀ b ∈ ts, b = true := fun b hb => hall b (by simp [hb])
        have := ih ts hk hlen' hall'
        have hsub : (k + 1) - 1 = k := by omega
        simp only [runTrace, he, ite_false, hsub, List.take_succ_cons,
          List.count_cons_of_ne (by simp : ¬ (false = true))]
        exact this

/-- Dropping `n` ticks off an all-available trace leaves the trace of the same
clock family, still in phase. -/
theorem drop_runTrace (delay : ℕ) (hd : 0 < delay) :
    ∀ (n clock : ℕ) (ts : List Bool), 1 ≤ clock → clock ≤ delay →
      ∃ c : ℕ, 1 ≤ c ∧ c ≤ delay ∧
        (runTrace delay clock ts).drop n = runTrace delay c (ts.drop n) := by
  intro n
  induction n with
  | zero => intro clock ts h1 h2; exact ⟨clock, h1, h2, by simp⟩
  | succ n ih =>
    intro clock ts h1 h2
    cases ts with
    | nil =>
      refine ⟨clock, h1, h2, ?_⟩
      simp [runTrace]
    | cons t ts =>
      cases t with
      | false =>
        obtain ⟨c, hc1, hc2, hc3⟩ := ih clock ts h1 h2
        refine ⟨c, hc1, hc2, ?_⟩
        simpa [runTrace] using hc3
      | true =>
        by_cases he : clock = 1
        · obtain ⟨c, hc1, hc2, hc3⟩ := ih delay ts hd (le_refl delay)
          refine ⟨c, hc1, hc2, ?_⟩
          simpa [runTrace, he] using hc3
        · obtain ⟨c, hc1, hc2, hc3⟩ := ih (clock - 1) ts (by omega) (by omega)
          refine ⟨c, hc1, hc2, ?_⟩
          simpa [runTrace, he] using hc3

/-- **NAMED — the machine source of `CloseoutPreload19.LiveL`.**  If every tick
of a scan leg is available (the real-time input supply delivers one symbol per
tick) and the controller clock enters the leg in phase, then the firing trace of
`GalilScaffoldMatchClock` is live: no window of `delay` consecutive ticks is
comparison-free.  This is exactly what `CloseoutPreload19` §3 showed could not
be obtained from the pacing bound. -/
theorem liveL_of_clock (delay clock : ℕ) (hd : 0 < delay)
    (h1 : 1 ≤ clock) (h2 : clock ≤ delay) (ts : List Bool)
    (hall : ∀ b ∈ ts, b = true) :
    LiveL delay (runTrace delay clock ts) := by
  intro n hn
  rw [runTrace_length] at hn
  obtain ⟨c, hc1, hc2, hc3⟩ := drop_runTrace delay hd n clock ts h1 h2
  rw [hc3]
  have hlen : c ≤ (ts.drop n).length := by
    have : (ts.drop n).length = ts.length - n := by simp
    omega
  have hall' : ∀ b ∈ ts.drop n, b = true := fun b hb =>
    hall b (List.mem_of_mem_drop hb)
  have hfire := fire_within delay c (ts.drop n) hc1 hlen hall'
  have hmono := count_take_mono (l := runTrace delay c (ts.drop n)) hc2
  omega

#print axioms count_take_mono
#print axioms fire_within
#print axioms drop_runTrace
#print axioms liveL_of_clock

/-! ## 3. The `.wait` leg bound, now unconditional in `LiveL` -/

/-- **NAMED — gap (b) of `CloseoutPreload18` §4, closed from machine facts.**
Same statement as `CloseoutPreload19.wait_leg_length_le`, but with the liveness
clause discharged: instead of assuming `LiveL 2048 as` we assume the (purely
bookkeeping) identification of the leg's event list with the firing trace of the
match clock over an all-available tick stream. -/
theorem wait_leg_length_le_of_clock {as ts : List Bool} {v t : SearchVM}
    {debt clock : ℕ}
    (hr : WaitTrace as v t) (hmt : t.search.mode = Mode.wait)
    (hz : zero t.search.debt = true) (hc : Canonical t.search.debt)
    (hd : value v.search.debt = (debt : ℤ))
    (hc1 : 1 ≤ clock) (hc2 : clock ≤ 2048)
    (hall : ∀ b ∈ ts, b = true)
    (has : as = runTrace 2048 clock ts) :
    as.length ≤ 2048 * (debt + 1) := by
  subst has
  exact wait_leg_length_le hr hmt hz hc
    (liveL_of_clock 2048 clock (by norm_num) hc1 hc2 ts hall) hd

#print axioms wait_leg_length_le_of_clock

/-- The fresh-clock entry case (`clock = 2048`), matching
`CloseoutPreload19.prefixPhase_of_fresh_clock`. -/
theorem liveL_of_fresh_clock (ts : List Bool) (hall : ∀ b ∈ ts, b = true) :
    LiveL 2048 (runTrace 2048 2048 ts) :=
  liveL_of_clock 2048 2048 (by norm_num) (by norm_num) (le_refl 2048) ts hall

#print axioms liveL_of_fresh_clock

/-!
## 4. What is left

Gap (b) of `CloseoutPreload18` §4 is now closed down to bookkeeping: the only
remaining hypothesis of `wait_leg_length_le_of_clock` is `as = runTrace 2048
clock ts` with `ts` all-available — i.e. the identification of the `.wait` leg's
`WaitTrace` event list with the match clock's firing trace over the leg's ticks,
plus the fact that the real-time input supply makes every one of those ticks
available.  Neither is proved here; both are the same `GalilScaffoldTop.Tick` /
`GalilScaffoldChainInputSupply` bookkeeping that `CloseoutPreload19` §4 already
lists for gap (a).

**無条件 PAL ∈ PEG は未完.**
-/

end PalPeg.CloseoutPreload20
