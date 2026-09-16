import PalPeg.GalilChainReadyProgress
import PalPeg.GalilScaffoldTopProgressS
import PalPeg.GalilFrontier

/-!
# (L7b) Constructing the chain-active segments of the found cycle

`cycle_found_stepsAll` (`PalPeg.GalilScaffoldTopOutputCycle`) takes the watch
phase of the found cycle as two *hypotheses*: a `WatchSegE` from the state
right after the found comparison, and a `WatchSeg` ending at the terminal
comparison.  This module **constructs** them.

The construction is a fuel recursion on `galilFrameS` ticks in scan mode with
an active chain.  At every step exactly one of four things happens:

* `¬ canRight` — the input is exhausted, the phase ends (`WatchStop.ended`);
* `1 < clock` — a counting tick (`WatchSeg.count`), from `backgroundS_exists`;
* `clock = 1` and the next move pops the *last* incoming letter — the report
  point falls inside the watch phase, so the run stops **before** that
  comparison (`WatchStop.lastLetter`);
* `clock = 1` and the outer symbols differ — the phase ends at a mismatching
  comparison (`WatchStop.mismatchWatch` / `WatchStop.mismatchOther`);
* `clock = 1` and they agree — a matched comparison (`WatchSeg.match`), unless
  the chain effect breaks the chain, which ends the phase
  (`WatchStop.broke`, the `hmt3`/`hbroken` pair of the cycle lemma).

Chain-side totality comes from `chainAt_exists` under `GalilTickFun.ChainReady`,
which `chainReady_of_blockInv` reduces to `BlockInv` plus the four branch facts
(`CopyInv` for copy, `canRight` for back, `Good` for a positive lag and the
verifier's `canRight` for watch).  Those four, the search effect's existence,
and their preservation along the run are *not* derivable here, so they travel
as one named hypothesis pack `Ctx` — a caller-supplied state predicate `Inv`
closed under the background tick and under `afterCompare`.

## Gaps (stated, not hidden)

* `Good` at a positive lag stays a hypothesis (`Ctx.ready`, via
  `chainReady_of_blockInv`'s `hgood`).  `good_of_periodOn` /
  `good_run_of_periodOn` (`PalPeg.GalilGoodLag`) would supply it, but they need
  the span-containment `hidx` for the *current* verifier index, which this
  purely local construction has no way to produce: it would have to carry the
  round's `PeriodOn` data and a head-position invariant along the recursion.
* `WatchStop.mismatchOther`.  The cycle lemma needs the terminal mismatch to sit
  at a chain `.watch w` with `zero w.lag = true` (it then calls `beginShiftVM h w`).
  Nothing local rules out a mismatch while the chain is copying, walking back,
  or watching with a positive lag, so that case is a separate disjunct rather
  than silently assumed.  Ruling it out is the "a scan mismatch happens only
  after the chain has caught up" invariant, still to be proved.
* `WatchStop.outOfFuel`.  The recursion is on fuel, not on a measure, so
  running out is a disjunct.  Turning it into a real termination proof needs
  the head-progress measure `2*|raw| - position s.right`.
-/

set_option autoImplicit false

namespace PalPeg.GalilSegmentConstruct2

open PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilBranchInvariants PalPeg.GalilTickFun
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-! ## Chain-side totality -/

/-- An active `ChainReady` chain has a tick for either event.  This is
`chainAt_exists` with the `idle` branches of `chainAt` discharged. -/
theorem chainTick_of_ready {x : ChainVM} (hx : ChainReady x) (hne : x ≠ .idle) (a : Bool)
    (answer : GalilScaffoldTape.Tape) (cc : Fin 3) (walker : GalilScaffoldPlace.Place)
    (ver : PlaceHead) (radius : Counter) : ∃ z, ChainTick a x z := by
  obtain ⟨z, hz⟩ := chainAt_exists a false answer cc walker ver radius x hx
  rcases hz with ⟨_, ht⟩ | ⟨hi, _⟩ | ⟨hi, _⟩
  · exact ⟨z, ht⟩
  · exact absurd hi hne
  · exact absurd hi hne

/-- `ChainReady` for a VM's chain from `BlockInv` plus the four branch facts,
packaged for `Ctx.ready`.  `hgood` is the `Good`-at-positive-lag gap. -/
theorem chainReady_of_vm (s : GalilVM) (hb : BlockInv s.chain)
    (hcopy : ∀ (t : GalilScaffoldTape.Tape) (hh : Counter) (p : GalilScaffoldPlace.Place)
      (v : GalilScaffoldChainPeriod.Tape) (lag margin : Counter) (ver : PlaceHead),
      s.chain = .copy t hh p v lag margin ver → ∃ n : ℕ, CopyInv t hh p v n)
    (hback : ∀ (v : GalilScaffoldChainPeriod.Tape) (hh lag margin : Counter) (ver : PlaceHead),
      s.chain = .back v hh lag margin ver → canRight ver)
    (hgood : ∀ w : GalilScaffoldChainWatch.State, s.chain = .watch w →
      positive w.lag = true → GalilScaffoldChainWatch.Good w)
    (hcan : ∀ w : GalilScaffoldChainWatch.State, s.chain = .watch w →
      ∀ m, GalilScaffoldChainWatch.Internal w m → canRight m.machine.verifier)
    (hnb : ∀ w : GalilScaffoldChainWatch.State, s.chain ≠ .broken w) :
    ChainReady s.chain :=
  PalPeg.GalilChainReadyProgress.chainReady_of_blockInv s.chain hb hcopy hback hgood hcan hnb

/-! ## The hypothesis pack -/

/-- The invariant carried along a watch phase.  `Inv` is any state predicate
that keeps the chain active and ready, keeps the search effect total, and is
preserved by a background tick and by a matched comparison. -/
structure Ctx (P : Shared) (q : ℕ) (first : Fin 9) where
  Inv : GalilVM → Prop
  ne : ∀ u : GalilVM, Inv u → u.chain ≠ .idle
  ready : ∀ u : GalilVM, Inv u → ChainReady u.chain
  hsearch : ∀ (u : GalilVM) (a : Bool), Inv u → ∃ v, searchEffect P a u v
  hpres : ∀ u u' : GalilVM, Inv u → (galilFrameS P q first).background u u' → Inv u'
  hpresC : ∀ (u : GalilVM) (vs : ScanVM) (vq : SearchVM), Inv u →
    vs.left = left u.left → vs.right = right u.right → ChainTick true u.chain vs.chain →
    Inv (afterCompare u vs vq)

/-! ## How a watch phase ends -/

/-- The four ways a watch phase ends, plus the fuel escape. -/
inductive WatchStop (P : Shared) (q : ℕ) (first : Fin 9) : Control → GalilVM → Prop
  /-- End of input. -/
  | ended (c : Control) (s : GalilVM) (hn : ¬ canRight s.right) : WatchStop P q first c s
  /-- The terminal mismatch the found cycle continues from: the chain is
  watching with zero lag. -/
  | mismatchWatch (c : Control) (s : GalilVM) (hm : c.mode = .scan) (hr : c.replaying = false)
      (hc : c.clock = 1) (ha : canRight s.right)
      (w : GalilScaffoldChainWatch.State) (hs : s.chain = .watch w) (hz : zero w.lag = true)
      (vs : ScanVM) (vq : SearchVM)
      (hcmp : (galilFrame P q first).compare s (scanLens.set s vs))
      (hmt : ¬ (galilFrame P q first).matched (scanLens.set s vs))
      (hq : searchEffect P false s vq) : WatchStop P q first c s
  /-- A mismatch while the chain is *not* a zero-lag watch — the gap. -/
  | mismatchOther (c : Control) (s : GalilVM) (hm : c.mode = .scan) (hr : c.replaying = false)
      (hc : c.clock = 1) (ha : canRight s.right)
      (hno : ¬ ∃ w : GalilScaffoldChainWatch.State, s.chain = .watch w ∧ zero w.lag = true)
      (vs : ScanVM) (vq : SearchVM)
      (hcmp : (galilFrame P q first).compare s (scanLens.set s vs))
      (hmt : ¬ (galilFrame P q first).matched (scanLens.set s vs))
      (hq : searchEffect P false s vq) : WatchStop P q first c s
  /-- The report point inside the watch phase: the comparison about to run
  would pop the last letter of the incoming FIFO, so the run stops *before*
  it and the caller takes over at the reporting tick. -/
  | lastLetter (c : Control) (s : GalilVM) (hm : c.mode = .scan) (hr : c.replaying = false)
      (hc : c.clock = 1) (ha : canRight s.right) (hpop : PopsIncoming s.right)
      (hinc : ∃ a : Fin 2, s.right.head.incoming = [a]) : WatchStop P q first c s
  /-- The period break: a matched comparison whose chain effect breaks. -/
  | broke (c : Control) (s : GalilVM) (hm : c.mode = .scan) (hr : c.replaying = false)
      (hc : c.clock = 1) (ha : canRight s.right)
      (vs : ScanVM) (vq : SearchVM)
      (hcmp : (galilFrame P q first).compare s (scanLens.set s vs))
      (hmt : (galilFrame P q first).matched (scanLens.set s vs))
      (hq : searchEffect P true s vq)
      (w' : GalilScaffoldChainWatch.State) (hbroken : (afterCompare s vs vq).chain = .broken w') :
      WatchStop P q first c s
  /-- The fuel ran out. -/
  | outOfFuel (c : Control) (s : GalilVM) : WatchStop P q first c s

/-! ## The construction -/

/-- **(L7b) The watch phase exists.**  From any scan-mode state with an active
ready chain, a `WatchSeg` run of `galilFrameS` reaches a state where the phase
ends in one of the four ways of `WatchStop` (or the fuel ran out).  No
determinism is used: each step is built from a totality lemma. -/
theorem watchSeg_construct (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    (hdelay : 1 ≤ delay) (K : Ctx P q first) :
    ∀ (_fuel : ℕ) (c : Control) (s : GalilVM), K.Inv s → c.mode = .scan →
      c.replaying = false → 1 ≤ c.clock →
      ∃ (c1 : Control) (s1 : GalilVM),
        WatchSeg P q first delay c s c1 s1 ∧ K.Inv s1 ∧
        c1.mode = .scan ∧ c1.replaying = false ∧ 1 ≤ c1.clock ∧
        WatchStop P q first c1 s1 := by
  classical
  intro fuel
  induction fuel with
  | zero =>
    intro c s hinv hm hr hclk
    exact ⟨c, s, .stop _ _, hinv, hm, hr, hclk, .outOfFuel c s⟩
  | succ fuel ih =>
    intro c s hinv hm hr hclk
    have hne : s.chain ≠ .idle := K.ne s hinv
    have hready : ChainReady s.chain := K.ready s hinv
    by_cases hav : canRight s.right
    · rcases Nat.lt_or_ge 1 c.clock with hlt | hle
      · -- a counting tick
        obtain ⟨s', hb⟩ := backgroundS_exists P q first s (K.hsearch s false hinv)
          (fun v => chainAt_exists false (decide (v.search.mode = .found))
            (v.dp.config.tapes 11) (P.centre s) (P.place s) s.center s.radius s.chain hready)
        obtain ⟨c1, s1, hseg, hinv1, hm1, hr1, hc1, hstop⟩ :=
          ih {c with clock := c.clock - 1} s' (K.hpres s s' hinv hb) hm hr
            (by show 1 ≤ c.clock - 1; omega)
        exact ⟨c1, s1, .count c s s' hm hr hav hlt hb hseg, hinv1, hm1, hr1, hc1, hstop⟩
      · -- a comparison
        have hc : c.clock = 1 := le_antisymm hle hclk
        by_cases hlast : PopsIncoming s.right ∧ ∃ a : Fin 2, s.right.head.incoming = [a]
        · -- the report point: stop before this comparison
          exact ⟨c, s, .stop _ _, hinv, hm, hr, hclk,
            .lastLetter c s hm hr hc hav hlast.1 hlast.2⟩
        by_cases hmatch : read (left s.left) = read (right s.right)
        · -- the outer symbols agree
          obtain ⟨z, hz⟩ := chainTick_of_ready hready hne true
            ((searchLens.get s).dp.config.tapes 11) (P.centre s) (P.place s) s.center s.radius
          set vs : ScanVM := ⟨left s.left, right s.right, z⟩ with hvs
          set vq : SearchVM := searchLens.get s with hvq
          have hq : searchEffect P true s vq := Or.inr ⟨hne, rfl⟩
          have hcmp : (galilFrame P q first).compare s (scanLens.set s vs) := by
            refine Lens.rel_set scanLens _ s vs ⟨rfl, rfl, ?_⟩
            show ChainTick (decide (read (left s.left) = read (right s.right))) s.chain z
            rw [decide_eq_true hmatch]
            exact hz
          have hmt : (galilFrame P q first).matched (scanLens.set s vs) := by
            show read (scanLens.get (scanLens.set s vs)).left
              = read (scanLens.get (scanLens.set s vs)).right
            rw [scanLens.get_set]
            exact hmatch
          set t : GalilVM := afterCompare s vs vq with hts
          set o : Bool := if P.onLetter t then decide (P.leftFirst t) else c.output with ho0
          have ho : refresh (galilFrame P q first) t c.output o := by
            refine ⟨fun hl => ?_, fun hl => ?_⟩
            · have hl' : P.onLetter t := hl
              show (if P.onLetter t then decide (P.leftFirst t) else c.output) = true
                ↔ P.leftFirst t
              rw [if_pos hl']
              exact decide_eq_true_iff
            · have hl' : ¬ P.onLetter t := hl
              show (if P.onLetter t then decide (P.leftFirst t) else c.output) = c.output
              rw [if_neg hl']
          by_cases hbr : ∃ w' : GalilScaffoldChainWatch.State, z = .broken w'
          · -- the chain broke: the phase ends here
            obtain ⟨w', hw'⟩ := hbr
            refine ⟨c, s, .stop _ _, hinv, hm, hr, hclk,
              .broke c s hm hr hc hav vs vq hcmp hmt hq w' ?_⟩
            rw [afterCompare_chain]
            exact hw'
          · -- the chain survived: one matched comparison, then recurse
            have hinvt : K.Inv t := K.hpresC s vs vq hinv rfl rfl (by
              show ChainTick true s.chain z
              exact hz)
            obtain ⟨c1, s1, hseg, hinv1, hm1, hr1, hc1, hstop⟩ :=
              ih {c with clock := delay, output := o, replaying := false} t hinvt hm rfl hdelay
            exact ⟨c1, s1, .match c s vs vq o hm hr hav hc hne hcmp hmt hq ho hseg,
              hinv1, hm1, hr1, hc1, hstop⟩
        · -- the outer symbols differ: the phase ends here
          obtain ⟨z, hz⟩ := chainTick_of_ready hready hne false
            ((searchLens.get s).dp.config.tapes 11) (P.centre s) (P.place s) s.center s.radius
          set vs : ScanVM := ⟨left s.left, right s.right, z⟩ with hvs
          set vq : SearchVM := searchLens.get s with hvq
          have hq : searchEffect P false s vq := Or.inr ⟨hne, rfl⟩
          have hcmp : (galilFrame P q first).compare s (scanLens.set s vs) := by
            refine Lens.rel_set scanLens _ s vs ⟨rfl, rfl, ?_⟩
            show ChainTick (decide (read (left s.left) = read (right s.right))) s.chain z
            rw [decide_eq_false hmatch]
            exact hz
          have hmt : ¬ (galilFrame P q first).matched (scanLens.set s vs) := by
            show ¬ read (scanLens.get (scanLens.set s vs)).left
              = read (scanLens.get (scanLens.set s vs)).right
            rw [scanLens.get_set]
            exact hmatch
          by_cases hw : ∃ w : GalilScaffoldChainWatch.State, s.chain = .watch w ∧ zero w.lag = true
          · obtain ⟨w, hsw, hzl⟩ := hw
            exact ⟨c, s, .stop _ _, hinv, hm, hr, hclk,
              .mismatchWatch c s hm hr hc hav w hsw hzl vs vq hcmp hmt hq⟩
          · exact ⟨c, s, .stop _ _, hinv, hm, hr, hclk,
              .mismatchOther c s hm hr hc hav hw vs vq hcmp hmt hq⟩
    · -- end of input
      exact ⟨c, s, .stop _ _, hinv, hm, hr, hclk, .ended c s hav⟩

/-- The pair of hypotheses `cycle_found_stepsAll` asks for: the preparation
segment `WatchSegE` (taken empty, so it starts and ends at the state right
after the found comparison) and the watch segment `WatchSeg` reaching the
terminal comparison. -/
theorem watchSegE_watchSeg_construct (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    (hdelay : 1 ≤ delay) (K : Ctx P q first) (fuel : ℕ) (c2 : Control) (s2 : GalilVM)
    (hinv : K.Inv s2) (hm : c2.mode = .scan) (hr : c2.replaying = false) (hclk : 1 ≤ c2.clock) :
    ∃ (c1 : Control) (s1 : GalilVM),
      WatchSegE P q first delay [] c2 s2 c2 s2 ∧
      WatchSeg P q first delay c2 s2 c1 s1 ∧ K.Inv s1 ∧
      c1.mode = .scan ∧ c1.replaying = false ∧ 1 ≤ c1.clock ∧
      WatchStop P q first c1 s1 := by
  obtain ⟨c1, s1, hseg, hinv1, hm1, hr1, hc1, hstop⟩ :=
    watchSeg_construct P q first delay hdelay K fuel c2 s2 hinv hm hr hclk
  exact ⟨c1, s1, .stop _ _, hseg, hinv1, hm1, hr1, hc1, hstop⟩


/-- **The preparation segment and the watch phase together.**  `GalilPrepConstruct`'s
`prep_segment_construct` builds the `h` copy ticks, the `copyEnd` tick and the
`h+1` back ticks as a `WatchSegE` over `bs ++ dm :: cs`, landing at `c2`/`s2`
with `delay - (2*h+2) ≤ c2.clock`; this composes that with
`watchSeg_construct`, so the result has the `hprepSeg`/`hseg` shape
`life_restarted` / `cycle_found_stepsAll` want — the non-empty preparation
segment instead of the empty one of `watchSegE_watchSeg_construct` — with the
same `WatchStop` exits.

`PalPeg.GalilPrepConstruct` cannot be imported here: it sits *downstream* of
this module (`GalilPrepConstruct` → `GalilCycleGlue` → `GalilSegmentConstruct2`),
so importing it would close an import cycle.  The preparation segment therefore
enters as `prep_segment_construct`'s conclusion, verbatim, and the caller
(in `GalilCycleGlue` or later) discharges it by applying that theorem.
`K.Inv s2` is likewise a hypothesis. -/
theorem prep_then_watch_construct (P : Shared) (qq : ℕ) (first : Fin 9) (delay : ℕ)
    (K : Ctx P qq first) (fuel : ℕ) (h : ℕ)
    -- the preparation segment, exactly as `prep_segment_construct` returns it
    {bs cs : List Bool} {dm : Bool} {cF' c2 : Control} {sF s2 : GalilVM}
    (hprepSeg : WatchSegE P qq first delay (bs ++ dm :: cs) cF' sF c2 s2)
    (hbs : bs.length = h) (hcs : cs.length = h+1) (hdm : dm = false)
    (hm2 : c2.mode = .scan) (hr2 : c2.replaying = false)
    (hlow : delay - (2*h+2) ≤ c2.clock) (hh : 2*h+2 < delay)
    -- the invariant at the landing state
    (hinv2 : K.Inv s2) :
    ∃ (c1 : Control) (s1 : GalilVM),
      WatchSegE P qq first delay (bs ++ dm :: cs) cF' sF c2 s2 ∧
      bs.length = h ∧ cs.length = h+1 ∧ dm = false ∧
      WatchSeg P qq first delay c2 s2 c1 s1 ∧ K.Inv s1 ∧
      c1.mode = .scan ∧ c1.replaying = false ∧ 1 ≤ c1.clock ∧
      WatchStop P qq first c1 s1 := by
  have hclk2 : 1 ≤ c2.clock := by omega
  obtain ⟨c1, s1, hwseg, hinv1, hm1, hr1, hc1, hstop⟩ :=
    watchSeg_construct P qq first delay (by omega) K fuel c2 s2 hinv2 hm2 hr2 hclk2
  exact ⟨c1, s1, hprepSeg, hbs, hcs, hdm, hwseg, hinv1, hm1, hr1, hc1, hstop⟩

#print axioms chainTick_of_ready
#print axioms chainReady_of_vm
#print axioms watchSeg_construct
#print axioms watchSegE_watchSeg_construct
#print axioms prep_then_watch_construct

end PalPeg.GalilSegmentConstruct2
