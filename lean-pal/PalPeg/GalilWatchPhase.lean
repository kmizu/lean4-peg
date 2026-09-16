import PalPeg.GalilMismatchCaught
import PalPeg.GalilPrepConstruct

/-!
# The watch phase at the terminal mismatch is `4`

`GalilScaffoldTopLifeRestart.life_restarted` (and its caller
`GalilScaffoldTopFoundLife.found_life`) take, at the terminal comparison of the
watch segment, the hypothesis

```
(hphase : w.machine.control.phase = 4)
```

for the watch state `w` with `s1.chain = .watch w` and `zero w.lag = true`.
`GalilPrepConstruct` builds the *preparation* segment, which lands on
`GalilScaffoldChainConsume.ready cen ys b`, whose phase is `0`; its docstring
explicitly leaves "the phase half" of the `hland` gap open.  This module closes
the combinatorial half of that gap.

## What is proved unconditionally

`phase` only ever moves by `advancePhase`, and only on a boundary event
(`isFirst`/`isLast` of the period tape).  So the phase is a function of how many
places the chain has consumed since `ready`:

* `run_eq_iterate` — a consume run that is **not broken** is forced: every symbol
  fed to `consume` must be the one under the period head, so the run equals the
  deterministic iterate `step^[n]`.  (`consume_forced`.)
* `iterate_phase_four` — `step^[4*(ys.length+1)] (ready cen ys b)` has phase `4`.
  This is `GalilScaffoldChainSweep.four_boundaries` (two `bounce`s = `4h` places
  = four boundary crossings) transported along `run_eq_iterate`.
* `run_phase_four_stable` — `advancePhase 4 = 4`, so once the phase is `4` it
  stays `4`.
* `phase_four_of_length` — **the main pure theorem**: an unbroken run from
  `ready cen ys b` of at least `4*(ys.length+1)` places has phase `4`.
* `phase_four_of_distance` — the same, stated through the chain's own `distance`
  counter (`run_distance`: an unbroken run increments `distance` once per place),
  which is the form the machine layer carries.

## What is proved about the extent

`extent_of_mismatch` is the contrapositive of
`GalilMismatchCaught.no_mismatch_before_caught`: a found DP candidate with
semiperiod `h` guarantees `PalAt (encoded raw) (C - 2*h) (2*h)`, so a scan
mismatch at radius `k` (inside the origin guard `k+1 < C - 2*h`) forces
`2*h ≤ k`.  That is the scan-side lower bound on the place count.

## Gaps, as named hypotheses (not hidden)

`phase_at_terminal` is stated with exactly two machine-level hypotheses, both of
which are bookkeeping this file does not have:

* `htrace` — **the consume trace.**  That the watch state reached at the end of
  `WatchSeg P q first delay c2 s2 c1 s1` has `w.machine.control = run (ready cen
  ys b) zs` for the list `zs` of symbols the chain consumed on the way.  This is
  an induction over `WatchSeg`/`WatchSegE` threading
  `GalilScaffoldChainWatch.Tick` (`Internal.take` and `Outer.immediate` each
  perform one `GalilScaffoldChainVerifier.consume`, i.e. one
  `GalilScaffoldChainConsume.consume`) — the per-tick chain step relation is not
  developed here.
* `hcount` (resp. `hdist`) — **the place count.**  That at least `4*h` places
  have been consumed by the terminal mismatch.  `extent_of_mismatch` gives the
  scan-side `2*h ≤ k`; turning `2*h` scan places into `4*h` chain consumes is the
  catch-up doubling (a watch tick may consume twice: `Internal.take` then
  `Outer.immediate`, cf. the `GalilScaffoldChainWatch.Tick` docstring), which is
  the `balance`/`lag`/`margin` ledger of `GalilScaffoldChainWatch` and
  `GalilScaffoldChainLag`.  Note this cannot be obtained from
  `GalilScaffoldChainWatch.caught_margin`: that lemma *derives* `0 ≤ margin`
  *from* `4*h ≤ distance`, so using conservation of `balance` (`= 4*h` at the
  watch start, `lag = 0` at the terminal) in the other direction would be
  circular.
* `hnb` — that the chain is not broken at the terminal comparison.  (A broken
  chain is a different `WatchStop` disjunct; `GalilSegmentConstruct2` separates
  them.)
-/

set_option autoImplicit false

namespace PalPeg.GalilWatchPhase

/-! ## 1. The phase is a function of the number of consumed places -/

section Pure

open GalilScaffoldChainConsume GalilScaffoldChainSweep GalilScaffoldCounter

/-- An absent period symbol always breaks the chain. -/
theorem consume_none (s : State) (seen : Option (Fin 3))
    (ht : symbol s.period.focus = none) : consume s seen = {s with broken := true} := by
  simp [consume, ht]

/-- `broken` is monotone: a broken chain stays broken. -/
theorem consume_broken (s : State) (seen : Option (Fin 3)) (hb : s.broken = true) :
    (consume s seen).broken = true := by
  unfold consume
  split <;> simp [hb]
  split <;> rfl

theorem run_broken (s : State) (zs : List (Fin 3)) (hb : s.broken = true) :
    (run s zs).broken = true := by
  induction zs generalizing s with
  | nil => exact hb
  | cons a zs ih => exact ih (consume s (some a)) (consume_broken s (some a) hb)

/-- Contrapositive: an unbroken outcome has an unbroken start. -/
theorem run_not_broken_head {s : State} {zs : List (Fin 3)}
    (hn : (run s zs).broken = false) : s.broken = false := by
  cases hb : s.broken with
  | false => rfl
  | true => rw [run_broken s zs hb] at hn; exact absurd hn (by simp)

/-- **The symbols of an unbroken run are forced.**  A consume that does not break
the chain must have been fed exactly the symbol under the period head. -/
theorem consume_forced (s : State) (a : Fin 3) (hb : s.broken = false)
    (hn : (consume s (some a)).broken = false) : symbol s.period.focus = some a := by
  cases ht : symbol s.period.focus with
  | none =>
    rw [consume_none s (some a) ht] at hn
    exact absurd hn (by simp)
  | some c =>
    by_cases hc : c = a
    · rw [hc]
    · exfalso
      have hne : (some a : Option (Fin 3)) ≠ some c := by simp [Ne.symm hc]
      rw [mismatch s c (some a) ht hne] at hn
      exact absurd hn (by simp)

/-- The deterministic one-place step: feed the symbol under the period head. -/
def step (s : State) : State := consume s (symbol s.period.focus)

/-- **An unbroken run is the deterministic iterate.** -/
theorem run_eq_iterate (s : State) (zs : List (Fin 3)) (hb : s.broken = false)
    (hn : (run s zs).broken = false) : run s zs = step^[zs.length] s := by
  induction zs generalizing s with
  | nil => rfl
  | cons a zs ih =>
    have hrun : run s (a :: zs) = run (consume s (some a)) zs := rfl
    rw [hrun] at hn ⊢
    have hb' : (consume s (some a)).broken = false := run_not_broken_head hn
    have ht : symbol s.period.focus = some a := consume_forced s a hb hb'
    have hstep : consume s (some a) = step s := by unfold step; rw [ht]
    rw [hstep] at hn ⊢
    rw [ih (step s) (by rw [← hstep]; exact hb') hn]
    simp [Function.iterate_succ_apply]

/-! ### `4h` places make four boundary crossings -/

theorem bounce_length (center b : Fin 3) (xs : List (Fin 3)) :
    (bounce center b xs).length = 2*(xs.length+1) := by
  simp [bounce]; omega

/-- **Four boundary crossings after `4h` deterministic steps.** -/
theorem iterate_phase_four (center b : Fin 3) (ys : List (Fin 3)) :
    (step^[4*(ys.length+1)] (ready center ys b)).phase = 4 := by
  have h4 := four_boundaries center b ys
  dsimp only at h4
  have hlen : ((bounce center b ys) ++ (bounce center b ys)).length = 4*(ys.length+1) := by
    simp [bounce_length]; omega
  have hb : (ready center ys b).broken = false := rfl
  have hn : (run (ready center ys b) ((bounce center b ys) ++ (bounce center b ys))).broken
      = false := h4.2.2.2.2.2.2
  have he := run_eq_iterate (ready center ys b) _ hb hn
  rw [hlen] at he
  rw [← he]
  exact h4.2.2.2.2.1

/-! ### Phase `4` is absorbing -/

theorem advancePhase_four : advancePhase 4 = 4 := rfl

theorem consume_phase_four (s : State) (seen : Option (Fin 3)) (hp : s.phase = 4) :
    (consume s seen).phase = 4 := by
  unfold consume
  split <;> simp [hp, advancePhase_four]
  split <;> rfl

theorem run_phase_four_stable (s : State) (zs : List (Fin 3)) (hp : s.phase = 4) :
    (run s zs).phase = 4 := by
  induction zs generalizing s with
  | nil => exact hp
  | cons a zs ih => exact ih (consume s (some a)) (consume_phase_four s (some a) hp)

/-! ### The main pure theorem -/

/-- **An unbroken watch run of at least `4h` places has phase `4`.** -/
theorem phase_four_of_length (center b : Fin 3) (ys zs : List (Fin 3))
    (hn : (run (ready center ys b) zs).broken = false)
    (hlen : 4*(ys.length+1) ≤ zs.length) :
    (run (ready center ys b) zs).phase = 4 := by
  set N := 4*(ys.length+1) with hN
  have hsplit : zs = zs.take N ++ zs.drop N := (List.take_append_drop N zs).symm
  have hrun : run (ready center ys b) zs
      = run (run (ready center ys b) (zs.take N)) (zs.drop N) := by
    conv_lhs => rw [hsplit]
    exact run_append _ _ _
  have hpre : (run (ready center ys b) (zs.take N)).broken = false := by
    cases hb : (run (ready center ys b) (zs.take N)).broken with
    | false => rfl
    | true =>
      exfalso
      rw [hrun, run_broken _ _ hb] at hn
      exact absurd hn (by simp)
  have htake : (zs.take N).length = N := by
    rw [List.length_take]; omega
  have he := run_eq_iterate (ready center ys b) (zs.take N) rfl hpre
  rw [htake] at he
  have hp : (run (ready center ys b) (zs.take N)).phase = 4 := by
    rw [he, hN]; exact iterate_phase_four center b ys
  rw [hrun]
  exact run_phase_four_stable _ _ hp

/-! ### The same, through the `distance` counter -/

theorem consume_distance (s : State) (a : Fin 3) (ht : symbol s.period.focus = some a) :
    (consume s (some a)).distance = inc s.distance := by
  simp [consume, ht]

/-- An unbroken run increments `distance` exactly once per place. -/
theorem run_distance (s : State) (zs : List (Fin 3)) (hb : s.broken = false)
    (hn : (run s zs).broken = false) :
    value (run s zs).distance = value s.distance + zs.length := by
  induction zs generalizing s with
  | nil => simp [run]
  | cons a zs ih =>
    have hrun : run s (a :: zs) = run (consume s (some a)) zs := rfl
    rw [hrun] at hn ⊢
    have hb' : (consume s (some a)).broken = false := run_not_broken_head hn
    have ht : symbol s.period.focus = some a := consume_forced s a hb hb'
    rw [ih (consume s (some a)) hb' hn, consume_distance s a ht, inc_value]
    simp only [List.length_cons]
    push_cast
    ring

/-- **`4h` consumed places, counted by the chain's own `distance`.** -/
theorem phase_four_of_distance (center b : Fin 3) (ys zs : List (Fin 3))
    (hn : (run (ready center ys b) zs).broken = false)
    (hd : 4*((ys.length : ℤ)+1) ≤ value (run (ready center ys b) zs).distance) :
    (run (ready center ys b) zs).phase = 4 := by
  refine phase_four_of_length center b ys zs hn ?_
  have hr := run_distance (ready center ys b) zs rfl hn
  have h0 : value (ready center ys b).distance = 0 := rfl
  rw [h0] at hr
  rw [hr] at hd
  have : (4*(ys.length+1) : ℤ) ≤ (zs.length : ℤ) := by linarith
  exact_mod_cast this

end Pure

/-! ## 2. The candidate's extent forces the scan radius -/

section Extent

open Manacher PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-- **Contrapositive of `GalilMismatchCaught.no_mismatch_before_caught`.**  A
found DP candidate with semiperiod `h` guarantees `PalAt (encoded raw) (C-2h) (2h)`
about the shifted centre; so a scan *mismatch* at radius `k` (inside the origin
guard `k+1 < C-2h`) can only happen once `2*h ≤ k`, i.e. after at least `2*h`
places have been scanned past the shifted centre. -/
theorem extent_of_mismatch (a : Fin 2) (ls rs q : List (Fin 2)) (gap : Bool)
    (span lower h : ℕ)
    (hc : GalilDpCorrect.Candidate
      ((GalilScaffoldPlace.stream ⟨a :: ls, gap⟩).take (span+1)) lower h)
    {k : ℕ} {l r : PlaceHead}
    (hi : ScanInvariant ((a :: ls).reverse ++ rs ++ q)
      (position (represent ⟨a :: ls, gap⟩ (rs.map some) q) - 2*h) k l r)
    (hav : canRight r)
    (hkC : k + 1 < position (represent ⟨a :: ls, gap⟩ (rs.map some) q) - 2*h)
    (hmis : read (left l) ≠ read (right r)) : 2*h ≤ k := by
  by_contra hk
  exact hmis (GalilMismatchCaught.no_mismatch_before_caught a ls rs q gap span lower h hc hi hav
    (by omega) hkC)

end Extent

/-! ## 3. The machine-level statement `life_restarted` asks for -/

/-- **`phase = 4` at the terminal mismatch of the watch segment.**

The two machine-level facts this file does not derive are named hypotheses:

* `htrace` — the watch state reached at the end of the watch segment runs the
  chain control from `ready cen ys b` (where the preparation segment of
  `GalilPrepConstruct.prep_segment_construct` leaves it) over the list `zs` of
  symbols consumed since; and
* `hcount` — at least `4*h` places have been consumed by then.

Everything else is `phase_four_of_length`: an unbroken run is forced to follow
the period tape, and `4*h` forced places are exactly two `bounce`s, i.e. four
boundary crossings (`GalilScaffoldChainSweep.four_boundaries`). -/
theorem phase_at_terminal (cen b : Fin 3) (ys : List (Fin 3)) (h : ℕ)
    (hh : h = ys.length + 1) (w : GalilScaffoldChainWatch.State) (zs : List (Fin 3))
    (htrace : w.machine.control
      = GalilScaffoldChainSweep.run (GalilScaffoldChainConsume.ready cen ys b) zs)
    (hnb : w.machine.control.broken = false)
    (hcount : 4*h ≤ zs.length) :
    w.machine.control.phase = 4 := by
  subst hh
  rw [htrace] at hnb ⊢
  exact phase_four_of_length cen b ys zs hnb hcount

/-- `phase_at_terminal` with the place count carried by the chain's own
`distance` counter — the shape the ledger layer (`GalilScaffoldChainWatch.balance`,
`caught_margin`) speaks in. -/
theorem phase_at_terminal_of_distance (cen b : Fin 3) (ys : List (Fin 3)) (h : ℕ)
    (hh : h = ys.length + 1) (w : GalilScaffoldChainWatch.State) (zs : List (Fin 3))
    (htrace : w.machine.control
      = GalilScaffoldChainSweep.run (GalilScaffoldChainConsume.ready cen ys b) zs)
    (hnb : w.machine.control.broken = false)
    (hdist : 4*(h : ℤ) ≤ GalilScaffoldCounter.value w.machine.control.distance) :
    w.machine.control.phase = 4 := by
  subst hh
  rw [htrace] at hnb hdist ⊢
  refine phase_four_of_distance cen b ys zs hnb ?_
  push_cast at hdist ⊢
  linarith

#print axioms consume_forced
#print axioms run_eq_iterate
#print axioms iterate_phase_four
#print axioms phase_four_of_length
#print axioms run_distance
#print axioms phase_four_of_distance
#print axioms extent_of_mismatch
#print axioms phase_at_terminal
#print axioms phase_at_terminal_of_distance

end PalPeg.GalilWatchPhase
