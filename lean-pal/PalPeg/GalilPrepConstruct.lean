import PalPeg.GalilCycleGlue
import PalPeg.GalilPrepLeast
import PalPeg.GalilScaffoldTopChain

/-!
# Constructing the preparation segment (the `hland` gap of `GalilCycleGlue`)

`GalilScaffoldTopLifeRestart.life_restarted` needs the segment that runs from
the found comparison to the state the watch phase starts in, *split* as

```
WatchSegE P qq first delay (bs ++ dm :: cs) … cF' sF c2 s2
```

with `bs.length = h` (the `h` copy ticks of the chain, one answer bit each),
one tick `dm` (the `copyEnd` tick, copy → back) and `cs.length = h+1` (the
back walk), landing with `s2.chain = .watch …`.  `GalilCycleGlue`'s
`watchSegE_watchSeg_construct` produces the *empty* preparation segment
instead, so the landing `Restarted` had to travel as the hypothesis `hland`
(see that module's docstring).  This file removes exactly that mismatch: it
**builds** a segment of the required shape.

## What is built

* `active_background_exists` — totality of one `backgroundS` tick on a
  *non-idle* chain: `searchEffect`'s active disjunct freezes the search
  (`vq = searchLens.get s`) and `chainAt`'s non-idle disjunct is a plain
  `ChainTick false`, i.e. a bare `ChainStep`.  So any chain step at all can
  be run as a background tick.
* `background_segE_of_chainSteps` — a `ChainSteps n` run of the chain is
  driven, tick by tick, as a `WatchSegE` over `List.replicate n false`:
  every tick is `WatchSegE.count` (right head available, clock still above
  one) or `WatchSegE.wait` (right head exhausted, clock untouched).
* `prep_chain_run` — the chain side: `copy_steps` (`h` ticks) + the
  `copyEnd` step (1 tick) + `back_steps` (`h+1` ticks) = `2h+2` steps from
  the credited `chain.start()` to `.watch ⟨⟨ver, ready cen ys b⟩, …⟩`.
* `prep_segment_construct` — the two put together, with
  `bs = List.replicate h false`, `dm = false`, `cs = List.replicate (h+1) false`.
* `prep_segment_construct_of_found` — the same, with the copy/back data
  supplied by `GalilScaffoldChainPeriod.found_start_back` from the found DP
  quantum instead of by hand.

## The clock bound `hh : 2*h+2 < delay`, and comparisons mid-copy

The construction above is the *background-only* preparation: all `2h+2`
events are `false`.  `WatchSegE.count` needs `1 < c.clock` and decrements
the clock, so starting at `clock = delay` the run needs `delay - i > 1` for
`i < 2h+2`, i.e. exactly `2*h+2 < delay`.  With `delay = 2048` that is
`h ≤ 1022`.  This is a restriction of *this construction*, **not** of the
model: `chainAt`'s non-idle disjunct is `ChainTick a` for either event, and
on `.copy` / `.back` the `true` case is `ChainMatched.copy` /
`ChainMatched.back` (`lag++`, `margin++`) — a comparison mid-copy is a
perfectly good tick, and the lower layer already accounts for it
(`GalilScaffoldTopChainCredits.copy_ticks` / `back_ticks` over arbitrary bit
lists `bs`, `cs`, and `GalilScaffoldChainCredits.prepEvents sm dm bs cs`).
Removing `hh` therefore means replaying the comparison ticks too, which needs
the comparison's own totality pack (`hsearch`, the scan effect and the refresh
output) at every one of the `2h+2` ticks; that is the next step and is *not*
done here.

## What is still missing for `hland`

`life_restarted` also wants `hphase : w.machine.control.phase = 4` for the
watch state `w` at the *terminal* comparison of the following `WatchSeg` — a
fact about the watch phase, not about the preparation segment.  The
preparation segment lands at `GalilScaffoldChainConsume.ready`, whose phase is
`0`; the four boundary crossings that bring it to `4` happen later.  So this
file closes the *shape* half of the `hland` gap and leaves the phase half
open.
-/

set_option autoImplicit false
namespace PalPeg.GalilPrepConstruct

open PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilBranchInvariants
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-! ## One background tick on an active chain -/

/-- **Totality of a background tick on a non-idle chain.**  `searchEffect`'s
active disjunct keeps the search frozen and `chainAt`'s non-idle disjunct is
`ChainTick false`, i.e. a bare `ChainStep`; so every chain step is realized by
a `backgroundS` tick that changes nothing else. -/
theorem active_background_exists (P : Shared) (q : ℕ) (first : Fin 9) (s : GalilVM)
    (hne : s.chain ≠ ChainVM.idle) {z : ChainVM} (hstep : ChainStep s.chain z) :
    ∃ s', (galilFrameS P q first).background s s' ∧ s'.chain = z ∧
      s'.left = s.left ∧ s'.right = s.right ∧ s'.center = s.center ∧
      s'.radius = s.radius ∧ s'.length = s.length ∧ s'.periodOnly = s.periodOnly ∧
      s'.replay = s.replay ∧ searchLens.get s' = searchLens.get s := by
  refine ⟨searchLens.set (scanLens.set s ⟨s.left, s.right, z⟩) (searchLens.get s),
    ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact ⟨rfl, rfl, Or.inr ⟨hne, rfl⟩, Or.inl ⟨hne, ⟨z, hstep, rfl⟩⟩, rfl⟩

/-! ## A chain run, driven as a background segment -/

/-- **A `ChainSteps` run is a `WatchSegE` over `List.replicate n false`.**
Each chain step is realized by `active_background_exists` and consumed by
`WatchSegE.count` (right head available; the clock is still above one, which
is what `n < c.clock` guarantees all the way down) or by `WatchSegE.wait`
(right head exhausted; the clock does not move).  Nothing but the chain and
the clock changes. -/
theorem background_segE_of_chainSteps (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    {n : ℕ} {x z : ChainVM} (hrun : ChainSteps n x z) :
    ∀ (c : Control) (s : GalilVM), c.mode = .scan → c.replaying = false →
      s.chain = x → x ≠ ChainVM.idle → n < c.clock →
      ∃ (c' : Control) (t : GalilVM),
        WatchSegE P q first delay (List.replicate n false) c s c' t ∧
        t.chain = z ∧ c'.mode = .scan ∧ c'.replaying = false ∧ c'.output = c.output ∧
        c.clock - n ≤ c'.clock ∧ c'.clock ≤ c.clock ∧
        t.left = s.left ∧ t.right = s.right ∧ t.center = s.center ∧
        t.radius = s.radius ∧ t.length = s.length ∧ t.periodOnly = s.periodOnly ∧
        t.replay = s.replay ∧ searchLens.get t = searchLens.get s := by
  classical
  induction hrun with
  | zero x =>
    intro c s hm hr hs _ _
    exact ⟨c, s, .stop _ _, hs, hm, hr, rfl, by omega, le_refl _, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl⟩
  | @succ n x y z hstep hrest ih =>
    intro c s hm hr hs hx hclk
    have hstep' : ChainStep s.chain y := by rw [hs]; exact hstep
    have hne : s.chain ≠ ChainVM.idle := by rw [hs]; exact hx
    have hy : y ≠ ChainVM.idle := chainTick_ne_idle' (a := false) ⟨y, hstep, rfl⟩ hx
    obtain ⟨s', hb, hch', hl', hr', hc', hrad', hlen', hpo', hrep', hget'⟩ :=
      active_background_exists P q first s hne hstep'
    by_cases hav : canRight s.right
    · -- `count`: the clock ticks down
      have hlt : 1 < c.clock := by omega
      obtain ⟨c'', t, hseg, hchz, hm'', hr'', ho'', hlo, hhi, hl2, hr2, hc2, hrad2, hlen2, hpo2,
          hrep2, hget2⟩ :=
        ih {c with clock := c.clock - 1} s' hm hr hch' hy (by simp only []; omega)
      refine ⟨c'', t, ?_, hchz, hm'', hr'', ho'', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [List.replicate_succ]
        exact .count c s s' hm hr hav hlt hb hseg
      · simp only [] at hlo; omega
      · simp only [] at hhi; omega
      · rw [hl2, hl']
      · rw [hr2, hr']
      · rw [hc2, hc']
      · rw [hrad2, hrad']
      · rw [hlen2, hlen']
      · rw [hpo2, hpo']
      · rw [hrep2, hrep']
      · rw [hget2, hget']
    · -- `wait`: the clock stands still
      obtain ⟨c'', t, hseg, hchz, hm'', hr'', ho'', hlo, hhi, hl2, hr2, hc2, hrad2, hlen2, hpo2,
          hrep2, hget2⟩ :=
        ih c s' hm hr hch' hy (by omega)
      refine ⟨c'', t, ?_, hchz, hm'', hr'', ho'', by omega, hhi, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [List.replicate_succ]
        exact .wait c s s' hm hr hav hb hseg
      · rw [hl2, hl']
      · rw [hr2, hr']
      · rw [hc2, hc']
      · rw [hrad2, hrad']
      · rw [hlen2, hlen']
      · rw [hpo2, hpo']
      · rw [hrep2, hrep']
      · rw [hget2, hget']

/-! ## The chain side of the preparation period -/

/-- **The chain run of the preparation period: `2h+2` steps.**  `copy_steps`
walks the `h` answer cells, the `copyEnd` step marks the endpoint and turns to
`.back`, and `back_steps` rewinds to the front mark and enters
`.watch (ready cen ys b)`. -/
theorem prep_chain_run (answer : GalilScaffoldTape.Tape) (cen : Fin 3)
    (p q' : GalilScaffoldPlace.Place) (ver : PlaceHead) (u : GalilScaffoldTape.Tape)
    (h : ℕ) (ys : List (Fin 3)) (b : Fin 3) (lag margin : Counter)
    (hcopy : GalilScaffoldChainPeriod.Copy answer reset p (GalilScaffoldChainPeriod.start cen) h u
      (ofNat h) q' (GalilScaffoldChainPeriod.fill (GalilScaffoldChainPeriod.start cen) (ys ++ [b])))
    (hu : u.focus = 4) (hpos : positive (ofNat h) = true)
    (hfocus : (GalilScaffoldChainPeriod.fill (GalilScaffoldChainPeriod.start cen)
      (ys ++ [b])).focus = .plain b)
    (hback : GalilScaffoldChainPeriod.Back (GalilScaffoldChainPeriod.write
      (GalilScaffoldChainPeriod.fill (GalilScaffoldChainPeriod.start cen) (ys ++ [b])) (.last b))
      (h+1) (GalilScaffoldChainPeriod.moveRight ⟨[], .first cen,
        ys.map GalilScaffoldChainPeriod.Token.plain ++ [.last b]⟩)) :
    ChainSteps (2*h+2) (.copy answer reset p (GalilScaffoldChainPeriod.start cen) lag margin ver)
      (.watch ⟨⟨ver, GalilScaffoldChainConsume.ready cen ys b⟩, lag,
        GalilScaffoldChainCredits.decFour^[h] margin⟩) := by
  have h1 := copy_steps h lag margin ver hcopy
  have h2 : ChainStep
      (ChainVM.copy u (ofNat h) q' (GalilScaffoldChainPeriod.fill
        (GalilScaffoldChainPeriod.start cen) (ys ++ [b])) lag
        (GalilScaffoldChainCredits.decFour^[h] margin) ver)
      (.back (GalilScaffoldChainPeriod.write (GalilScaffoldChainPeriod.fill
        (GalilScaffoldChainPeriod.start cen) (ys ++ [b])) (.last b)) (ofNat h) lag
        (GalilScaffoldChainCredits.decFour^[h] margin) ver) :=
    .copyEnd _ _ _ _ _ _ _ b hu hpos hfocus
  have h3 := back_steps (h+1) (ofNat h) lag (GalilScaffoldChainCredits.decFour^[h] margin) ver hback
  have h23 : ChainSteps (h+2)
      (ChainVM.copy u (ofNat h) q' (GalilScaffoldChainPeriod.fill
        (GalilScaffoldChainPeriod.start cen) (ys ++ [b])) lag
        (GalilScaffoldChainCredits.decFour^[h] margin) ver)
      (.watch ⟨⟨ver, GalilScaffoldChainConsume.ready cen ys b⟩, lag,
        GalilScaffoldChainCredits.decFour^[h] margin⟩) := by
    refine ChainSteps.succ h2 ?_
    have hready : GalilScaffoldChainConsume.ready cen ys b =
        (⟨GalilScaffoldChainPeriod.moveRight ⟨[], .first cen,
          ys.map GalilScaffoldChainPeriod.Token.plain ++ [.last b]⟩,
          reset, reset, reset, 0, true, false⟩ : GalilScaffoldChainConsume.State) := rfl
    rw [hready]
    exact h3
  have hfull := chainSteps_trans h1 h23
  have he : h + (h+2) = 2*h+2 := by omega
  rw [he] at hfull
  exact hfull

/-! ## The preparation segment -/

theorem replicate_split (h : ℕ) :
    List.replicate h false ++ false :: List.replicate (h+1) false
      = List.replicate (2*h+2) false := by
  have h1 : (false :: List.replicate (h+1) false) = List.replicate (h+2) false := by
    simp [List.replicate_succ]
  rw [h1, ← List.replicate_add]
  congr 1
  omega

/-- **The preparation segment, constructed.**  From the state right after the
found comparison — whose chain is the credited `chain.start()`, i.e.
`ChainMatched (chainStart …) ch` — the chain's own `2h+2`-step preparation run
(`prep_chain_run`) is driven as a background-only `WatchSegE`
(`background_segE_of_chainSteps`) and split as `bs ++ dm :: cs` with
`bs.length = h`, `cs.length = h+1`: exactly the shape `life_restarted` asks
for.  The clock bound `hh : 2*h+2 < delay` is what lets all `2h+2` ticks be
background ticks; see the module docstring. -/
theorem prep_segment_construct (P : Shared) (qq : ℕ) (first : Fin 9) (delay : ℕ)
    -- the period data of the found DP answer
    (answer : GalilScaffoldTape.Tape) (cen : Fin 3) (p q' : GalilScaffoldPlace.Place)
    (ver : PlaceHead) (radius : Counter) (u : GalilScaffoldTape.Tape)
    (h : ℕ) (ys : List (Fin 3)) (b : Fin 3)
    (hcopy : GalilScaffoldChainPeriod.Copy answer reset p (GalilScaffoldChainPeriod.start cen) h u
      (ofNat h) q' (GalilScaffoldChainPeriod.fill (GalilScaffoldChainPeriod.start cen) (ys ++ [b])))
    (hu : u.focus = 4) (hpos : positive (ofNat h) = true)
    (hfocus : (GalilScaffoldChainPeriod.fill (GalilScaffoldChainPeriod.start cen)
      (ys ++ [b])).focus = .plain b)
    (hback : GalilScaffoldChainPeriod.Back (GalilScaffoldChainPeriod.write
      (GalilScaffoldChainPeriod.fill (GalilScaffoldChainPeriod.start cen) (ys ++ [b])) (.last b))
      (h+1) (GalilScaffoldChainPeriod.moveRight ⟨[], .first cen,
        ys.map GalilScaffoldChainPeriod.Token.plain ++ [.last b]⟩))
    -- the chain at the found comparison: `chain.start()` plus that tick's credit
    (ch : ChainVM) (hch : ChainMatched (chainStart answer cen p ver radius) ch)
    -- the state the preparation starts from
    (cF' : Control) (sF : GalilVM)
    (hm : cF'.mode = .scan) (hr : cF'.replaying = false) (hclk : cF'.clock = delay)
    (hchain : sF.chain = ch)
    -- the copy and back phases fit inside one comparison delay
    (hh : 2*h+2 < delay) :
    ∃ (bs cs : List Bool) (dm : Bool) (c2 : Control) (s2 : GalilVM),
      WatchSegE P qq first delay (bs ++ dm :: cs) cF' sF c2 s2 ∧
      bs.length = h ∧ cs.length = h+1 ∧ dm = false ∧
      s2.chain = ChainVM.watch ⟨⟨ver, GalilScaffoldChainConsume.ready cen ys b⟩,
        inc radius, GalilScaffoldChainCredits.decFour^[h] (inc radius)⟩ ∧
      (∃ w : GalilScaffoldChainWatch.State, s2.chain = ChainVM.watch w) ∧
      c2.mode = .scan ∧ c2.replaying = false ∧ c2.output = cF'.output ∧
      delay - (2*h+2) ≤ c2.clock ∧ c2.clock ≤ delay ∧
      s2.left = sF.left ∧ s2.right = sF.right ∧ s2.center = sF.center ∧
      s2.radius = sF.radius ∧ s2.length = sF.length ∧ s2.periodOnly = sF.periodOnly ∧
      s2.replay = sF.replay ∧ searchLens.get s2 = searchLens.get sF := by
  -- the credited `chain.start()` is a copy state with `lag = margin = radius+1`
  cases hch with
  | copy _ _ _ _ _ _ _ =>
    have hrun := prep_chain_run answer cen p q' ver u h ys b (inc radius) (inc radius)
      hcopy hu hpos hfocus hback
    have hne : ChainVM.copy answer reset p (GalilScaffoldChainPeriod.start cen)
        (inc radius) (inc radius) ver ≠ ChainVM.idle := by
      intro hc; exact ChainVM.noConfusion hc
    obtain ⟨c2, s2, hseg, hchz, hm2, hr2, ho2, hlo, hhi, hl2, hr2', hc2, hrad2, hlen2, hpo2,
        hrep2, hget2⟩ :=
      background_segE_of_chainSteps P qq first delay hrun cF' sF hm hr hchain hne (by omega)
    refine ⟨List.replicate h false, List.replicate (h+1) false, false, c2, s2, ?_,
      List.length_replicate .., List.length_replicate .., rfl, hchz, ⟨_, hchz⟩, hm2, hr2, ho2,
      by omega, by omega, hl2, hr2', hc2, hrad2, hlen2, hpo2, hrep2, hget2⟩
    rw [replicate_split h]
    exact hseg

/-- `prep_segment_construct` with the copy/back data supplied by the found DP
quantum (`GalilScaffoldChainPeriod.found_start_back`) instead of by hand. -/
theorem prep_segment_construct_of_found (P : Shared) (qq : ℕ) (first : Fin 9) (delay : ℕ)
    {sq tq : GalilScaffoldSearchFinish.State} {x y : GalilScaffoldControl.Machine 12}
    {as : List Bool} {w : List (Fin 3)} {lower span : ℕ} (p : GalilScaffoldPlace.Place)
    (hw : w = (GalilScaffoldPlace.stream p).take (span+1))
    (hrq : GalilScaffoldSearchRun.SafeQuanta sq x as tq y) (hsq : sq.mode = .run)
    (htq : tq.mode = .found)
    (hv : GalilDpCorrect.Result w lower 0 (GalilScaffoldProgram.denote y.config))
    (ver : PlaceHead) (radius : Counter)
    (cF' : Control) (sF : GalilVM)
    (hm : cF'.mode = .scan) (hr : cF'.replaying = false) (hclk : cF'.clock = delay)
    -- the chain at the found comparison, for whichever centre the walker reads
    (hchv : ∀ cen : Fin 3, GalilScaffoldPlace.read p = some cen →
      ChainMatched (chainStart (y.config.tapes 11) cen p ver radius) sF.chain)
    -- every candidate semiperiod fits inside one comparison delay
    (hh : ∀ k : ℕ, GalilDpCorrect.Candidate w lower k → 2*k+2 < delay) :
    ∃ (h : ℕ) (bs cs : List Bool) (dm : Bool) (c2 : Control) (s2 : GalilVM),
      GalilDpCorrect.Candidate w lower h ∧
      WatchSegE P qq first delay (bs ++ dm :: cs) cF' sF c2 s2 ∧
      bs.length = h ∧ cs.length = h+1 ∧ dm = false ∧
      (∃ ww : GalilScaffoldChainWatch.State, s2.chain = ChainVM.watch ww) ∧
      c2.mode = .scan ∧ c2.replaying = false ∧ c2.output = cF'.output ∧
      delay - (2*h+2) ≤ c2.clock ∧ c2.clock ≤ delay ∧
      s2.left = sF.left ∧ s2.right = sF.right ∧ s2.center = sF.center ∧
      s2.radius = sF.radius ∧ s2.length = sF.length ∧ s2.periodOnly = sF.periodOnly ∧
      s2.replay = sF.replay ∧ searchLens.get s2 = searchLens.get sF := by
  obtain ⟨h, cen, u, q', ys, b, hcand, hread, hcopy, hu, hpos, hfocus, hback, _, _⟩ :=
    GalilScaffoldChainPeriod.found_start_back p hw hrq hsq htq hv
  obtain ⟨bs, cs, dm, c2, s2, hseg, hbs, hcs, hdm, _, hwatch, hm2, hr2, ho2, hlo, hhi, hl2, hr2',
      hc2, hrad2, hlen2, hpo2, hrep2, hget2⟩ :=
    prep_segment_construct P qq first delay (y.config.tapes 11) cen p q' ver radius u h ys b
      hcopy hu hpos hfocus hback sF.chain (hchv cen hread) cF' sF hm hr hclk rfl (hh h hcand)
  exact ⟨h, bs, cs, dm, c2, s2, hcand, hseg, hbs, hcs, hdm, hwatch, hm2, hr2, ho2, hlo, hhi, hl2,
    hr2', hc2, hrad2, hlen2, hpo2, hrep2, hget2⟩

#print axioms active_background_exists
#print axioms background_segE_of_chainSteps
#print axioms prep_chain_run
#print axioms replicate_split
#print axioms prep_segment_construct
#print axioms prep_segment_construct_of_found

end PalPeg.GalilPrepConstruct
