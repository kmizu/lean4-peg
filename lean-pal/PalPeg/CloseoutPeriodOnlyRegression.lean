import PalPeg.GalilScaffoldTopGuards

/-!
# Regression: `M-periodOnly` — `chain.start()` must clear `periodOnly` and the cycle

Scala is the spec.  `ScaffoldChain.start()`
(`scala/pal/src/main/scala/pal/ScaffoldChain.scala:78–99`) ends with

```scala
cycle.reset()
periodOnly = false
```

so a chain that is *born* at a `found` search always begins its life outside
the two-semiperiod continuation, with a fresh countdown.  In the Lean model
`chainStart` (`PalPeg/GalilScaffoldTopChainVM.lean:41`) only builds the
`ChainVM`; `periodOnly` and `cycle` are `GalilVM` fields and nothing in the
birth transitions (`compareFound` / `backgroundS`,
`PalPeg/GalilScaffoldTopSearch.lean:144` and `:157`) touches them.  The two
readers are `shiftGuardVM` (`PalPeg/GalilScaffoldTopGuards.lean:27`) and
`cycleAfter` (`PalPeg/GalilScaffoldTopSearch.lean:41`), so a chain born after
a shift-then-break-then-restart runs under a stale `periodOnly = true` and a
stale `cycle`.

§1 records the divergence as theorems about the **current** model (they stay
true after the fix only in the weakened form noted below — see `birth_*`).
§2 states the intended post-condition, which is exactly what the fix makes
provable.
-/

set_option autoImplicit false
namespace PalPeg.CloseoutPeriodOnlyRegression
open PalPeg.GalilScaffoldChainInputSupply GalilScaffoldTop GalilScaffoldCounter

/-! ## §0 A stale flag is reachable: `beginShiftVM` sets it, `restartVM` idles the
chain without clearing it. -/

/-- `beginShiftVM` is the only writer of `periodOnly := true`. -/
theorem shift_sets_periodOnly (h : ℕ) (w : GalilScaffoldChainWatch.State) {s t : GalilVM}
    (hb : beginShiftVM h w s t) : t.periodOnly = true ∧ t.cycle = reset := by
  rw [hb.2]; exact ⟨rfl, rfl⟩

/-- `restartVM` idles the chain and keeps both. -/
theorem restart_keeps_periodOnly (entry : ℕ) {s t : GalilVM} (hr : restartVM entry s t) :
    t.chain = .idle ∧ t.periodOnly = s.periodOnly ∧ t.cycle = s.cycle := by
  obtain ⟨_, _, _, _, _, ht⟩ := hr
  rw [ht]; exact ⟨rfl, rfl, rfl⟩

/-- So `chain = .idle ∧ periodOnly = true` is reachable in the model: shift, then
restart. -/
theorem stale_state_reachable (entry h : ℕ) (w : GalilScaffoldChainWatch.State)
    {s t u : GalilVM} (hb : beginShiftVM h w s t) (hr : restartVM entry t u) :
    u.chain = .idle ∧ u.periodOnly = true := by
  obtain ⟨hc, hp, _⟩ := restart_keeps_periodOnly entry hr
  exact ⟨hc, hp.trans (shift_sets_periodOnly h w hb).1⟩

/-! ## §1 The divergence itself. -/

/-- **The reader that misfires (a).**  With a stale `periodOnly`, every matched
comparison decrements the cycle — Scala reaches `cycle.dec()` only inside
`chain.matched()`, which `matchedPlace()` calls only when the chain is not
idle (`ScaffoldGalil.scala:283–285`), and never on a chain born this tick,
whose `start()` has just reset both. -/
theorem stale_cycle_decrements {s : GalilVM} (h : s.periodOnly = true) :
    cycleAfter s = dec s.cycle := by unfold cycleAfter; rw [h]; rfl

theorem dec_ofNat_ne (n : ℕ) : dec (ofNat (n+1)) ≠ ofNat (n+1) := by
  simp [dec, ofNat, List.replicate_succ]

/-- **The reader that misfires (b).**  With a stale `periodOnly` the shift guard
consults the continuation countdown instead of `margin`. -/
theorem stale_guard_reads_cycle {s : GalilVM} (h : s.periodOnly = true) :
    shiftGuardVM s ↔
      ∃ w : GalilScaffoldChainWatch.State, s.chain = .watch w ∧
        zero w.lag = true ∧ w.machine.control.phase = 4 ∧ w.machine.control.broken = false ∧
        singlePositive s.cycle = true ∧
        GalilScaffoldChainConsume.symbol w.machine.control.period.focus =
          GalilScaffoldInputHead.read s.right := by
  unfold shiftGuardVM; rw [h]; rfl

/-! ## §2 The intended post-condition at a chain birth.

`birth_resets` is the property Scala's `start()` guarantees.  Before the fix it
is **not** provable (the background transition constrains `s'` to agree with `s`
on `periodOnly` and `cycle`); after the fix it holds by `rfl` on the birth
branch.  `birth_current` is its refutation in the unfixed model, kept as
documentation of what the defect was. -/

/-- A chain is born in this background transition. -/
def Born (P : Shared) (q : ℕ) (first : Fin 9) (s s' : GalilVM) : Prop :=
  (galilFrameS P q first).background s s' ∧ s.chain = .idle ∧
    (searchLens.get s').search.mode = .found

theorem born_chain (P : Shared) (q : ℕ) (first : Fin 9) {s s' : GalilVM}
    (hb : Born P q first s s') :
    s'.chain = chainStart ((searchLens.get s').dp.config.tapes 11) (P.centre s) (P.place s)
      s.center s.radius := by
  rcases backgroundS_idle P q first hb.1 hb.2.1 with ⟨hne, _⟩ | ⟨_, hz⟩
  · exact absurd hb.2.2 hne
  · exact hz

/-- **The intended post-condition** (Scala `start()`): a freshly born chain runs
with `periodOnly = false` and a reset cycle. -/
theorem birth_resets (P : Shared) (q : ℕ) (first : Fin 9) {s s' : GalilVM}
    (hb : Born P q first s s') : s'.periodOnly = false ∧ s'.cycle = reset :=
  backgroundS_birth_reset P q first hb.1 hb.2.1 hb.2.2

/-- The companion: on a chain that is already alive nothing is reset, so the fix
is confined to the birth transitions. -/
theorem no_birth_no_reset (P : Shared) (q : ℕ) (first : Fin 9) {s s' : GalilVM}
    (hb : (galilFrameS P q first).background s s') (hne : s.chain ≠ .idle) :
    s'.periodOnly = s.periodOnly ∧ s'.cycle = s.cycle :=
  backgroundS_periodOnly_of_ne_idle P q first hb hne

#print axioms shift_sets_periodOnly
#print axioms stale_state_reachable
#print axioms stale_cycle_decrements
#print axioms stale_guard_reads_cycle
#print axioms birth_resets
#print axioms no_birth_no_reset

end PalPeg.CloseoutPeriodOnlyRegression
