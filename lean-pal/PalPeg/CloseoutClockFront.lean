import PalPeg.GalilFrontMono

/-!
# The clock–frontier potential: the right head cannot outrun the clock

`canRight` is the same obligation in five places on the closeout path
(`hee`, `het`, `MatchRes2.canR`/`canRNext`, and the `hcan` of
`CloseoutPackRun28.walkerInOrigin_of_run`).  It says the input has not run out.
This file gives the single counting argument that supplies all of them.

The input frontier `front s = position s.right + value s.replay`
(`GalilRunTrace:39`) never decreases and increases only on a comparison
(`GalilFrontMono.front_tick_mono`).  A comparison fires only at `clock = 1` and
puts the clock back to `delay`.  Reading the `Tick` constructors
(`GalilScaffoldTop:110-173`), exactly five of the twenty-three touch the clock:
`scan_count` takes it to `c.clock - 1`, and `scan_match`, `scan_shift`,
`scan_fallback`, `replayStart` and `restart` take it to `delay`; the other
seventeen leave it alone.  So **no tick lowers the clock by more than one**.

Hence the potential

```
Ψ (c, s) := delay * front s - c.clock
```

rises by at most one per tick: a non-comparison keeps `front` and loses at most
one clock unit, and a comparison gains one `front` unit (`delay`) while
returning `delay - 1` clock units.

From `Ψ` the bound on the right head follows: over `n` ticks from a fresh start
(`front = 0`, `clock = delay`),

```
delay * front ≤ n + clock ≤ n + delay,   so   position right ≤ front ≤ n / delay + 1.
```

The closeout run is `delay * w.length` ticks long and the input is exhausted
only at `position right = 2 * w.length`, so the head stays movable whenever
`1 < w.length`.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false

namespace PalPeg.CloseoutClockFront

open PalPeg.GalilRunTrace
open PalPeg.GalilFrontMono
open PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop
open GalilScaffoldController
open GalilScaffoldCounter

variable (onLetter leftFirst : GalilVM → Prop) (centre : GalilVM → Fin 3)
  (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9) (delay : ℕ)

/-- **No tick lowers the clock by more than one.**  Seventeen constructors keep
the clock, five raise it to `delay`, and only `scan_count` lowers it, by one. -/
theorem clock_drop_one {c c' : Control} {s t : GalilVM} (hc : c.clock ≤ delay)
    (h : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay
      ⟨c, s⟩ ⟨c', t⟩) : c.clock ≤ c'.clock + 1 := by
  cases h <;> simp_all <;> omega

/-- **The clock never exceeds `delay`.**  Every tick keeps it, lowers it, or puts
it back to `delay`. -/
theorem clock_le_delay {c c' : Control} {s t : GalilVM} (hc : c.clock ≤ delay)
    (h : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay
      ⟨c, s⟩ ⟨c', t⟩) : c'.clock ≤ delay := by
  cases h <;> simp_all <;> omega

/-- The same along a run. -/
theorem clock_le_delay_steps {n : ℕ} {x y : State GalilVM}
    (h : Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay n x y)
    (hc : x.ctl.clock ≤ delay) : y.ctl.clock ≤ delay := by
  induction h with
  | zero x => exact hc
  | @succ n x w y ht _ ih =>
      exact ih (clock_le_delay onLetter leftFirst centre place entry q first delay hc ht)

/-- **The potential.**  `delay` frontier units minus the clock. -/
def pot (delay : ℕ) (c : Control) (s : GalilVM) : ℤ :=
  (delay : ℤ) * front s - (c.clock : ℤ)

/-- **One tick raises the potential by at most one.**  A comparison gains one
frontier unit (`delay`) and gives back `delay - 1` clock units; every other tick
keeps the frontier and loses at most one clock unit. -/
theorem pot_tick {c c' : Control} {s t : GalilVM} (hP : FrontPack c s)
    (hcle : c.clock ≤ delay)
    (h : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay
      ⟨c, s⟩ ⟨c', t⟩) :
    pot delay c' t ≤ pot delay c s + 1 := by
  have hd : (0 : ℤ) ≤ (delay : ℤ) := Int.natCast_nonneg delay
  unfold pot
  rcases front_clock_tick onLetter leftFirst centre place entry q first delay hP h with
    heq | ⟨hle, hc1, hcd⟩
  · have hc := clock_drop_one onLetter leftFirst centre place entry q first delay hcle h
    have h2 : (c.clock : ℤ) ≤ (c'.clock : ℤ) + 1 := by exact_mod_cast hc
    rw [heq]; omega
  · have h1 : (delay : ℤ) * front t ≤ (delay : ℤ) * (front s + 1) :=
      mul_le_mul_of_nonneg_left hle hd
    rw [hcd, hc1]
    push_cast at h1 ⊢
    nlinarith [h1]

/-- **The potential along a run.** -/
theorem pot_steps {n : ℕ} {x y : State GalilVM}
    (h : Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay n x y)
    (hg : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay m x z →
      FrontPack z.ctl z.vm)
    (hcl : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay m x z →
      z.ctl.clock ≤ delay) :
    pot delay y.ctl y.vm ≤ pot delay x.ctl x.vm + n := by
  induction h with
  | zero x => simp
  | @succ n x w y ht _ ih =>
      have h0 := pot_tick onLetter leftFirst centre place entry q first delay
        (hg 0 x (.zero x)) (hcl 0 x (.zero x)) ht
      have h1 := ih (fun m z hz => hg (m+1) z (.succ ht hz))
        (fun m z hz => hcl (m+1) z (.succ ht hz))
      push_cast at h1 ⊢
      omega

/-- **The right head is bounded by the run length.**  From a fresh start
(`front = 0`, `clock = delay`) an `n`-tick run leaves the frontier below
`n / delay + 1`, and the right head never passes the frontier. -/
theorem front_le_of_run {n : ℕ} {x y : State GalilVM}
    (hd : 0 < delay)
    (h : Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay n x y)
    (hg : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay m x z →
      FrontPack z.ctl z.vm)
    (hx0 : front x.vm = 0) (hxc : x.ctl.clock = delay) :
    (delay : ℤ) * front y.vm ≤ (n : ℤ) := by
  have h0 := pot_steps onLetter leftFirst centre place entry q first delay h hg
    (fun m z hz =>
      clock_le_delay_steps onLetter leftFirst centre place entry q first delay hz (le_of_eq hxc))
  have hcl : y.ctl.clock ≤ delay :=
    clock_le_delay_steps onLetter leftFirst centre place entry q first delay h (le_of_eq hxc)
  have hcl' : (y.ctl.clock : ℤ) ≤ (delay : ℤ) := by exact_mod_cast hcl
  unfold pot at h0
  rw [hx0, hxc] at h0
  simp at h0
  omega

/-- **The payoff: the right head can still move.**  `position right ≤ front`
(the replay counter is non-negative), the frontier is below `n / delay`, and the
input is exhausted only at `position right = 2 * w.length`.  So any run shorter
than `delay * (2 * w.length)` ticks keeps the head movable. -/
theorem canRight_of_run {n : ℕ} {x y : State GalilVM} {w : List (Fin 2)}
    (hd : 0 < delay)
    (h : Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay n x y)
    (hg : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay m x z →
      FrontPack z.ctl z.vm)
    (hx0 : front x.vm = 0) (hxc : x.ctl.clock = delay)
    (hrep : GalilScaffoldInputTrace.Represents y.vm.right.head w)
    (hpres : y.vm.right.head.focus ≠ none)
    (hn : n < delay * (2 * w.length)) :
    GalilScaffoldChainVerifier.canRight y.vm.right := by
  by_contra hc
  have hend : position y.vm.right = 2 * w.length :=
    (PalPeg.GalilEndOfInput.not_canRight_iff _ _ hrep hpres).1 hc
  have hb := front_le_of_run onLetter leftFirst centre place entry q first delay hd h hg hx0 hxc
  have hpos : (position y.vm.right : ℤ) ≤ front y.vm := by
    have hFy := hg n y h
    unfold front
    cases hr : y.ctl.replaying with
    | true =>
      obtain ⟨m, hm⟩ := hFy.replayPos hr
      rw [hm, GalilScaffoldCounter.ofNat_value]
      omega
    | false =>
      rw [hFy.rest (Or.inl hr)]
      simp [GalilScaffoldCounter.value, GalilScaffoldCounter.reset]
  have hdz : (0 : ℤ) < (delay : ℤ) := by exact_mod_cast hd
  have hnz : (n : ℤ) < (delay : ℤ) * (2 * (w.length : ℤ)) := by exact_mod_cast hn
  rw [hend] at hpos
  push_cast at hpos
  nlinarith [hb, hpos, hnz, hdz]

/-- **`Extra7` along a run, with no `hee`/`het`.**  `Extra7` is exactly
`mode = scan → ¬replaying → canRight right`, so `canRight_of_run` supplies it at
every state of a short enough run: neither the entry obligation `hee` nor the
tick obligation `het` is needed. -/
theorem extra7_of_run {n : ℕ} {x y : State GalilVM} {w : List (Fin 2)}
    (hd : 0 < delay)
    (h : Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay n x y)
    (hg : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay m x z →
      FrontPack z.ctl z.vm)
    (hx0 : front x.vm = 0) (hxc : x.ctl.clock = delay)
    (hrep : GalilScaffoldInputTrace.Represents y.vm.right.head w)
    (hpres : y.vm.right.head.focus ≠ none)
    (hn : n < delay * (2 * w.length)) :
    y.ctl.mode = Mode.scan → y.ctl.replaying = false →
      GalilScaffoldChainVerifier.canRight y.vm.right :=
  fun _ _ => canRight_of_run onLetter leftFirst centre place entry q first delay hd h hg hx0 hxc
    hrep hpres hn

#print axioms clock_drop_one
#print axioms pot_tick
#print axioms pot_steps
#print axioms front_le_of_run
#print axioms canRight_of_run
#print axioms extra7_of_run

end PalPeg.CloseoutClockFront
