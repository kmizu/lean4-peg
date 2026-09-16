import PalPeg.GalilReportReplay
import PalPeg.GalilScaffoldTopFirstStagePrefix
import PalPeg.GalilScaffoldTimingCost

/-!
# Gap `hnfR` of `PalPeg.GalilReportReplay`: can the co-running search report
`found` while the replay counter is positive?

`PalPeg.GalilReportReplay` assumes

* `hnfR : ∀ s' v m, 0 < m → s'.replay = ofNat m → searchEffect P true s' v →
    v.search.mode ≠ .found`

("the search does not report `found` while the replay counter is positive").
This module settles what that hypothesis costs.

## Verdict: `hnfR` is **not** a timing fact — the model really does allow a
chain start during the replay

* **Scala** (`scala/pal/src/main/scala/pal/ScaffoldGalil.scala`).  `run()`
  calls `background()` on *every* `Scan` tick, with no `replaying` guard, and
  `background()` calls `chain.start()` as soon as `search.mode == Found`.
  `stepReplayStart` *restarts* the search (`search.start(zero)`) at the very
  moment it sets `replaying = replay.sign > 0`.  The only `replaying` guards
  in `stepScan` are on the chain **shift** (`!replaying && chain.canShift`)
  and on the fallback (`beginFallback` throws while replaying).  So the search
  runs during the replay, and a chain start during the replay is *not*
  excluded by the reference implementation.

* **Lean.**  `compareFound` carries
  `chainAt a (decide (vq.search.mode = .found)) …` and `backgroundS` carries
  `chainAt false (decide (…= .found)) …`; neither mentions `c.replaying`.
  `Tick.scan_match` admits `c.replaying = true` (`h : c.replaying = true ∨ …`)
  and sets `replaying := c.replaying && !F.replayExhausted s''`.  So a `found`
  and a replay decrement happen on the same tick, and
  `background_found_starts_chain_while_replaying` below records that the idle
  chain is started by that `found` *while replaying*.

* **The timing goes the wrong way.**  After the replay restart the search is
  `begin reset radius`, i.e. the first stage with lower bound `k = 0`.  Its
  whole cost is `max k 1 + (2k + 2m + 7) + runBudget (8·max k 1) ≤ 63·(8·max k 1)`
  (`GalilScaffoldTimingCost.first_stage_ticks`), which for `k = 0` is
  `≤ 63·8 = 504` ticks — far *less* than the `delay - 1 = 2047` background
  ticks that precede the **first** replay comparison, let alone the `r·2048`
  ticks of the whole replay (`replay_outlasts_first_stage`).  So the first
  stage always finishes inside the first countdown of the replay; there is no
  "the search cannot reach `found` in time" argument to be had.
  `stage_prefix_mode` only says that *proper* prefixes of the first stage are
  not `found`, and `504 < 2047` makes that vacuous here.

## What is true, and what the gap really is

`hnfR` is therefore **not** provable from the timing.  What *is* provable is
that a search which has already halted in a non-`found` exit mode stays away
from `found`: `searchEffect_not_found_of_halted`.  So the honest reduction is

* `not_found_during_replay` — `hnfR` follows from the invariant
  `SearchHalted`: at every replaying state the search sits in `.idle` or
  `.missed`.  `report_after_replay_of_halted` is `report_after_replay` with
  `hnfR` replaced by that invariant.

The remaining (open) obligation is thus a *search-layer* fact, not a timing
fact: after the replay restart the first stage over the window
`(stream centre).take 9` with lower bound `0` must exit `.missed` rather than
`.found`.  Note that `hbg` (the background never reports `found`) is assumed
at exactly the same level and is exposed to exactly the same risk: since the
stage ends after ~501 events, the `found`, if it happens at all, happens on a
*background* tick of the first countdown, i.e. it breaks `hbg` before it ever
gets a chance to break `hnfR`.

## If instead one accepts a chain start during the replay

Then the report/replay lemmas need a **fourth exit**: besides
"counter exhausted", "no more input" and "mismatch", a segment may end at a
state whose chain is `chainStart …` while `c.replaying = true`; `WatchSegE`
cannot even express that (`matchIdleR`/`countR` both carry
`hidle : s.chain = .idle`).  And the life lemmas would have to accept a
replaying control: `cycle_found_stepsAll` takes `hrF : cF.replaying = false`,
so as stated it does *not* apply to such a chain.  Both would have to be
generalised before that route is viable.
-/

set_option autoImplicit false

namespace PalPeg.GalilReplayFound

open PalPeg PalPeg.GalilBranchInvariants2
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier GalilScaffoldChainInputSupply GalilStructuredSkeleton

/-! ## The timing comparison -/

/-- The first stage after the replay restart (`lower = reset`, so `k = 0`)
costs at most `63·8 = 504` ticks. -/
theorem first_stage_cost_zero (m : ℕ) (hm : m ≤ 8 * max 0 1 + 1) :
    max 0 1 + 2 * 0 + 2 * m + 7 + GalilScaffoldTimingCost.runBudget (8 * max 0 1)
      ≤ 63 * (8 * max 0 1) :=
  GalilScaffoldTimingCost.first_stage_ticks 0 m hm

/-- **The timing argument fails.**  The first stage after the replay restart
finishes strictly inside the `delay - 1 = 2047` background ticks that precede
the *first* replay comparison, and a fortiori inside the `r·2048` ticks of a
replay with `r > 0`. -/
theorem replay_outlasts_first_stage (m : ℕ) (hm : m ≤ 8 * max 0 1 + 1) (r : ℕ) (hr : 0 < r) :
    max 0 1 + 2 * 0 + 2 * m + 7 + GalilScaffoldTimingCost.runBudget (8 * max 0 1) < 2048 - 1 ∧
      max 0 1 + 2 * 0 + 2 * m + 7 + GalilScaffoldTimingCost.runBudget (8 * max 0 1) < r * 2048 := by
  have h := first_stage_cost_zero m hm
  constructor <;> omega

/-! ## The model starts the chain during the replay -/

/-- **The model permits a chain start while replaying.**  The background's
chain effect never consults `c.replaying`: an idle chain whose search lands in
`found` is started exactly as during an ordinary scan.  (`_hrp` is stated only
to make the point; the proof does not use it.) -/
theorem background_found_starts_chain_while_replaying (P : Shared) (q : ℕ) (first : Fin 9)
    {c : Control} {s s' : GalilVM} (_hrp : c.replaying = true)
    (hb : (galilFrameS P q first).background s s') (hi : s.chain = ChainVM.idle)
    (hf : (searchLens.get s').search.mode = .found) :
    s'.chain = chainStart ((searchLens.get s').dp.config.tapes 11) (P.centre s) (P.place s)
      s.center s.radius := by
  rcases backgroundS_idle P q first hb hi with ⟨hne, -⟩ | ⟨-, hz⟩
  · exact absurd hf hne
  · exact hz

/-! ## What is actually provable: a halted search stays away from `found` -/

/-- The search sits in a halted, non-`found` exit mode. -/
def SearchHalted (s : GalilVM) : Prop :=
  s.search.mode = .idle ∨ s.search.mode = .missed

/-- A halted search is inert: `searchStep` cannot move it. -/
theorem searchStep_of_halted {center : GalilScaffoldPlace.Place} {a : Bool} {v v' : SearchVM}
    (hh : v.search.mode = .idle ∨ v.search.mode = .missed)
    (h : searchStep center a v v') : v' = v := by
  rcases hh with hm | hm <;> simp only [searchStep, hm] at h <;> exact h

/-- **The provable core.**  Whatever the comparison event, the search effect of
a halted search is the halted search itself, so it is not `found`. -/
theorem searchEffect_not_found_of_halted (P : Shared) {a : Bool} {s : GalilVM} {vq : SearchVM}
    (hh : SearchHalted s) (h : searchEffect P a s vq) : vq.search.mode ≠ .found := by
  have hget : (searchLens.get s).search = s.search := rfl
  have hvq : vq = searchLens.get s := by
    rcases h with ⟨-, hs⟩ | ⟨-, he⟩
    · exact searchStep_of_halted (by rw [hget]; exact hh) hs
    · exact he
  rw [hvq, hget]
  rcases hh with hm | hm <;> rw [hm] <;> exact fun h0 => by cases h0

/-- **The reduction of `hnfR`.**  The gap of `PalPeg.GalilReportReplay`
follows from the invariant that the search is halted at every replaying
state. -/
theorem not_found_during_replay (P : Shared)
    (H : ∀ (s' : GalilVM) (m : ℕ), 0 < m → s'.replay = ofNat m → SearchHalted s') :
    ∀ (s' : GalilVM) (v : SearchVM) (m : ℕ), 0 < m → s'.replay = ofNat m →
      searchEffect P true s' v → v.search.mode ≠ .found := by
  intro s' v m hm hrepl hq
  exact searchEffect_not_found_of_halted P (H s' m hm hrepl) hq

/-! ## `report_after_replay` with the gap replaced by the invariant -/

/-- `PalPeg.GalilReportReplay.report_after_replay` with `hnfR` discharged from
`SearchHalted`. -/
theorem report_after_replay_of_halted (raw : List (Fin 2)) (P : Shared)
    (hP : P.onLetter = onLetterVM raw) (hP' : P.leftFirst = leftFirstVM)
    (hex : ∀ s, P.replayExhausted s = zero s.replay)
    (q : ℕ) (first : Fin 9) (delay : ℕ) (hd : 1 ≤ delay)
    (hsearch : ∀ s' : GalilVM, SearchReady (searchLens.get s') → ∀ a : Bool,
      ∃ v, searchEffect P a s' v)
    (hpres : ∀ (s' : GalilVM) (a : Bool) (v : SearchVM),
      SearchReady (searchLens.get s') → searchEffect P a s' v → SearchReady v)
    (hbg : ∀ (s' : GalilVM) (v : SearchVM), searchEffect P false s' v → v.search.mode ≠ .found)
    (hhalt : ∀ (s' : GalilVM) (m : ℕ), 0 < m → s'.replay = ofNat m → SearchHalted s')
    {n : ℕ} {x : State GalilVM} {c : Control} {t : GalilVM} {r : ℕ}
    (hx : x.ctl = GalilScaffoldController.initial delay)
    (hrun : StepsAll (galilFrameS P q first) delay (SoundScanNR raw) n x ⟨c, t⟩)
    (hm : c.mode = Mode.scan) (hclk : 1 ≤ c.clock)
    (hR : Restarted raw t 0 reset)
    (hM : MInv raw c t) (hfr : Frontier t) (hrest : ReplayRest c t)
    (hsr : SearchReady (searchLens.get t))
    (hrepl : t.replay = ofNat r) (hrp : c.replaying = decide (0 < r)) (hr0 : 0 < r)
    (hhead : ∃ xs rs : List (Fin 2),
      t.right.head = layout xs (rs.map some) [] ∧ raw = xs.reverse ++ rs)
    (hlast : position t.right + r = 2 * raw.length - 1) :
    ∃ (es : List Bool) (c' : Control) (y : GalilVM),
      WatchSegE P q first delay es c t c' y ∧
      (∃ (k : ℕ) (x' : State GalilVM), x'.ctl = GalilScaffoldController.initial delay ∧
        StepsAll (galilFrameS P q first) delay (SoundScanNR raw) k x' ⟨c', y⟩) ∧
      ReportPoint raw ⟨c', y⟩ ∧ Refreshed P q first ⟨c', y⟩ :=
  PalPeg.GalilReportReplay.report_after_replay raw P hP hP' hex q first delay hd hsearch hpres hbg
    (not_found_during_replay P hhalt) hx hrun hm hclk hR hM hfr hrest hsr hrepl hrp hr0 hhead hlast

#print axioms first_stage_cost_zero
#print axioms replay_outlasts_first_stage
#print axioms background_found_starts_chain_while_replaying
#print axioms searchStep_of_halted
#print axioms searchEffect_not_found_of_halted
#print axioms not_found_during_replay
#print axioms report_after_replay_of_halted

end PalPeg.GalilReplayFound
