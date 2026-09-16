import PalPeg.GalilScaffoldTopOutputCycle
import PalPeg.GalilScaffoldTopFoundLoop
import PalPeg.GalilLedgerObligations

/-!
# The two design assumptions of the restart states

`search_result_at_tick` (`PalPeg/GalilSearchResult.lean`) and
`restarted_next_found` (`PalPeg/GalilScaffoldTopReadyFound.lean`) enter a
restarted state with two hypotheses that the scaffold so far only *assumes*:

* `hcl : c0.clock = 2048` — the controller clock is the full match delay at
  the restart;
* `hstage : ∀ k, value last = k → 3 * Rad ≤ 5 * k` — the scan radius at the
  restart is within the stage budget of the lower bound installed there.

This file settles the first one for every restart form, settles the second one
for the two restart forms whose radius is `0` (the `init` tick and the fallback
cycle), and isolates exactly what is missing for the found-cycle restart.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-! ## (1) The clock at a restart -/

/-- The restart tick resets the clock to `delay`: the controller record it
produces has `clock = delay` definitionally. -/
theorem restart_clock {σ : Type} (F : GalilScaffoldTop.Frame σ) (delay : ℕ) (c : Control) (s s' : σ)
    (hm : c.mode = .scan) (hb : F.restart s s') :
    GalilScaffoldTop.Tick F delay ⟨c, s⟩ ⟨{c with clock := delay}, s'⟩ ∧
      ({c with clock := delay} : Control).clock = delay :=
  ⟨.restart c s s' hm hb, rfl⟩

/-- The control record at the end of the found cycle
(`cycle_found_stepsAll`, `life_restarted`) has `clock = delay`. -/
theorem restart_clock_found_cycle (c3 : Control) (delay : ℕ) (o3 : Bool) :
    ({c3 with clock := delay, output := o3, replaying := false} : Control).clock = delay := rfl

/-- The control record at the end of the fallback cycle
(`cycle_fallback_stepsAll`, `fallback_restarted`) has `clock = delay`. -/
theorem restart_clock_fallback_cycle (cF : Control) (delay : ℕ) (o rp od pr : Bool) :
    ({cF with mode := .scan, clock := delay, output := o, replaying := rp, odd := od, pair := pr} : Control).clock = delay := rfl

/-- Both cycles feed the next segment with `clock = 2048`, i.e. exactly the
`hcl` premise of `search_result_at_tick` at `delay = 2048`. -/
theorem restart_clock_2048 (c3 : Control) (o3 : Bool) :
    ({c3 with clock := 2048, output := o3, replaying := false} : Control).clock = 2048 := rfl

/-- **The one restart form that does not reset the clock.**  The `init` tick
produces `{c with mode := .scan, output := true}`: the clock is *inherited*,
not set to `delay`. -/
theorem init_clock_inherited {σ : Type} (F : GalilScaffoldTop.Frame σ) (delay : ℕ) (c : Control)
    (s s' : σ) (hm : c.mode = .init) (h : F.init s s') :
    GalilScaffoldTop.Tick F delay ⟨c, s⟩ ⟨{c with mode := .scan, output := true}, s'⟩ ∧
      ({c with mode := .scan, output := true} : Control).clock = c.clock :=
  ⟨.init c s s' hm h, rfl⟩

/-- …and that is enough, because the machine starts at `Control.initial delay`,
whose clock is already `delay`. -/
theorem initial_clock (delay : ℕ) : (GalilScaffoldController.initial delay).clock = delay := rfl

theorem init_clock_of_initial {σ : Type} (F : GalilScaffoldTop.Frame σ) (delay : ℕ) (c : Control)
    (s s' : σ) (hm : c.mode = .init) (hc : c.clock = delay) (h : F.init s s') :
    GalilScaffoldTop.Tick F delay ⟨c, s⟩ ⟨{c with mode := .scan, output := true}, s'⟩ ∧
      ({c with mode := .scan, output := true} : Control).clock = delay :=
  ⟨.init c s s' hm h, hc⟩

#print axioms restart_clock
#print axioms restart_clock_found_cycle
#print axioms restart_clock_fallback_cycle
#print axioms restart_clock_2048
#print axioms init_clock_inherited
#print axioms init_clock_of_initial

/-! ## (2) The stage budget at a restart -/

/-- The stage-entry side condition of `search_result_at_tick` /
`restarted_next_found`, as a predicate of the restart data. -/
def StageEntry (Rad : ℕ) (last : Counter) : Prop :=
  ∀ k : ℕ, value last = k → 3 * Rad ≤ 5 * k

/-- A restart whose radius is `0` always satisfies it. -/
theorem stageEntry_zero (last : Counter) : StageEntry 0 last := by
  intro k _; omega

/-- **The fallback restart.**  `cycle_fallback_stepsAll` / `fallback_restarted`
end in `Restarted raw t 0 reset`: radius `0`, lower bound `reset`. -/
theorem restart_stage_bound_fallback {raw : List (Fin 2)} {t : GalilVM}
    (_ : Restarted raw t 0 reset) : StageEntry 0 reset :=
  stageEntry_zero reset

/-- **The init restart.**  `init_restarted` ends in `Restarted (a :: rest) t 0 reset`. -/
theorem restart_stage_bound_init {raw : List (Fin 2)} {t : GalilVM}
    (_ : Restarted raw t 0 reset) : StageEntry 0 reset :=
  stageEntry_zero reset

/-- `value reset = 0`, so the lower bound installed by both of those restarts
is `k = 0` and the stage window is the calibrated minimum `8 * max 0 1 = 8`. -/
theorem value_reset : value reset = 0 := by
  rw [reset_eq_ofNat, ofNat_value]; simp

/-- A restart with a determined lower bound satisfies the condition as soon as
the radius does not exceed it. -/
theorem stageEntry_of_le (Rad k : ℕ) (last : Counter) (hv : value last = (k : ℤ))
    (h : Rad ≤ k) : StageEntry Rad last := by
  intro k' hk'
  have : (k' : ℤ) = (k : ℤ) := by rw [← hk', hv]
  have : k' = k := by exact_mod_cast this
  omega

#print axioms stageEntry_zero
#print axioms restart_stage_bound_fallback
#print axioms restart_stage_bound_init
#print axioms value_reset
#print axioms stageEntry_of_le

/-! ## What `StageEntry` is actually used for -/

/-- The single consumer of `3 * Rad ≤ 5 * k`: the first-stage barrier
(`GalilScaffoldAdvanceClock.first_stage_barrier`).  The stage must finish
before the scan radius reaches `2 * max k 1`. -/
theorem barrier_of_stageEntry (Rad k : ℕ) (last : Counter) (hv : value last = (k : ℤ))
    (hs : StageEntry Rad last) (es : List (Bool × Bool))
    (ht : es.length ≤ 63 * (8 * max k 1)) :
    Rad + (GalilScaffoldAdvanceClock.advances 2048 2048 es).count true ≤ 2 * max k 1 :=
  GalilScaffoldAdvanceClock.first_stage_barrier k Rad es (hs k hv) ht

/-- The weakest form the barrier really needs of the entry radius. -/
def StageBarrier (Rad : ℕ) (last : Counter) : Prop :=
  ∀ k : ℕ, value last = k → Rad ≤ 2 * max k 1

theorem stageBarrier_of_stageEntry (Rad : ℕ) (last : Counter) (h : StageEntry Rad last) :
    StageBarrier Rad last := by
  intro k hk
  have := h k hk
  rcases Nat.le_total k 1 with hle | hle
  · interval_cases k <;> omega
  · rw [max_eq_left hle]; omega

#print axioms barrier_of_stageEntry
#print axioms stageBarrier_of_stageEntry

/-! ## (2') The found-cycle restart: the open obligation -/

/-- The radius at the found-cycle restart, as `rounds_break` / `life_restarted`
produce it: `org.radius + 1 + m*h - h + n + 1` with `h` the semiperiod, `m` the
number of chained rounds and `n` the length of the final matched segment. -/
def foundRestartRadius (orgRadius h m n : ℕ) : ℕ := orgRadius + 1 + m * h - h + n + 1

/-- The obligation the found cycle leaves open: `StageEntry` for that radius
and for the lower bound `w3'.machine.control.last` installed by `restartVM`. -/
def FoundCycleStage (orgRadius h m n : ℕ) (last : Counter) : Prop :=
  StageEntry (foundRestartRadius orgRadius h m n) last

theorem foundCycleStage_of_bound (orgRadius h m n k : ℕ) (last : Counter)
    (hv : value last = (k : ℤ))
    (hb : 3 * foundRestartRadius orgRadius h m n ≤ 5 * k) :
    FoundCycleStage orgRadius h m n last := by
  intro k' hk'
  have : (k' : ℤ) = (k : ℤ) := by rw [← hk', hv]
  have : k' = k := by exact_mod_cast this
  omega

/-- **The obligation is not implied by what the scaffold currently proves at the
break.**  `rounds_break` gives only `positive w3'.machine.control.last = true`
(i.e. `1 ≤ k`) and `Canonical`; the strongest quantitative fact available about
the chain's `last` counter is `watch_last_lower`, `3 * h ≤ k`.  Even with both,
and with `0 < h`, the inequality `3 * Rad ≤ 5 * k` fails: the final matched
segment `n` (and the rounds `m`) push the radius up without moving `last`. -/
theorem foundCycleStage_not_implied :
    ∃ (orgRadius h m n k : ℕ), 0 < h ∧ 3 * h ≤ k ∧ 0 < k ∧
      5 * k < 3 * foundRestartRadius orgRadius h m n := by
  refine ⟨0, 1, 0, 10, 3, ?_, ?_, ?_, ?_⟩ <;> decide

/-- The same failure already at `m = 0, n = 0`: a long chain is not needed, an
`org.radius` larger than `(5/3) * k` suffices. -/
theorem foundCycleStage_not_implied_small :
    ∃ (orgRadius h m n k : ℕ), 0 < h ∧ 3 * h ≤ k ∧
      5 * k < 3 * foundRestartRadius orgRadius h m n := by
  refine ⟨10, 1, 1, 0, 3, ?_, ?_, ?_⟩ <;> decide

#print axioms foundCycleStage_of_bound
#print axioms foundCycleStage_not_implied
#print axioms foundCycleStage_not_implied_small

end PalPeg.GalilScaffoldChainInputSupply
