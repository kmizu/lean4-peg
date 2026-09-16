import PalPeg.GalilTickFun
import PalPeg.GalilBranchInvariants
import PalPeg.GalilChainReadyProgress
import PalPeg.GalilMismatchCaught
import PalPeg.GalilReplaySegment
import PalPeg.GalilGoodLag

/-!
# `ChainTickable`, and why it has to be weakened

`PalPeg.GalilReplayChainSeg` assumes

```
ChainTickable := ∀ a x, ChainReady x → x ≠ .idle → ∃ z, ChainTick a x z ∧ ChainReady z
```

as the chain-side enabling hypothesis of the replay construction.  This file
discharges as much of it as is true.

**It is not true as stated.**  `ChainMatched` has a fifth constructor,
`breaks`, which sends a *watching* chain to `.broken`, and `ChainReady .broken`
is `False`.  `chainMatched_watch_total` is a genuine trichotomy — queue,
consume, or break — and the break branch fires exactly when the period
predicts a symbol the verifier does not read.  Nothing in `ChainReady` rules
that out, so no proof of `ChainTickable` can exist; the honest statements are

* `chainTickable_unless_break` — the tick exists and lands in a chain that is
  ready *or* broken, and
* `no_break_during_replay` — under the extra hypothesis that the watch
  prediction agrees with every read (`Good` at every reachable watch state),
  the break branch is unreachable and the ready half survives.

**`ChainReady` is not by itself an invariant either.**  It is a *pointwise*
enabling condition: at `.back` it demands `WatchReady` only at the tape
position `isFirst` tests true, and `onBlock_moveLeft`/`onBlock_moveRight` are
the only way to keep that going, so the walk back needs the whole block
invariant `OnBlock`, not just the instance at the endpoint.  Likewise `.copy`
needs `CopyInv` and, one step before `backDone`, the verifier's right guard
`canRight ver`, which `ChainReady .copy` never mentions.  `ChainOk` is the
strengthening that *is* preserved, one clause per constructor:

| constructor | `ChainReady` | `ChainOk` |
|---|---|---|
| `.copy t h p v _ _ ver` | `∃ n, CopyInv t h p v n` | that, **and** `canRight ver` |
| `.back v _ lag _ ver` | `isFirst → zero lag → WatchReady …` | `OnBlock v` **and** `canRight ver` |
| `.watch w` | `positive lag → Good w`, `WatchBlock w`, `canRight` after `Internal` | `Ok w` |
| `.broken _` | `False` | `False` |

`Ok` is the *parameter predicate* of the watch phase: `WatchOk Ok` says `Ok`
implies the three `ChainReady` clauses, is closed under `Internal` and
`Outer`, and holds of the states `backDone` gives birth to.  The `Good`
obligation at positive lag is therefore carried by the caller, which is where
`PalPeg.GalilGoodLag.good_of_periodOn` (agreement from the `2h`-periodicity of
the current span) and `PalPeg.GalilReplaySegment.canRight_of_frontier` (the
right guard from the replay's frontier bound) are meant to be plugged in.

## Gaps

* `WatchOk Ok` is **not** instantiated here.  Producing the concrete `Ok` for
  the replay — `good_of_periodOn` for `good`/`goodAll`, `canRight_of_frontier`
  for `can`/`born`, `watchBlock_internal`/`watchBlock_outer` for `block`, and
  the `Entry`/`ReadOrigin` bookkeeping for closure under `Internal`/`Outer` —
  is the remaining work.  Without it `no_break_during_replay` is a conditional.
* The refutation of `ChainTickable` is argued, not formalised: exhibiting a
  concrete breaking `State` is left open.
* `PalPeg.GalilReplayChainSeg.ChainTickable` itself is untouched; the
  construction there still has to be re-based on `chainOk_tick`, which means
  threading `ChainOk` (not just `ChainReady`) through
  `replayChainSeg_countdown` / `_one` / `_construct`.
-/

set_option autoImplicit false

namespace PalPeg.GalilChainTickable

open PalPeg PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilBranchInvariants
open PalPeg.GalilTickFun PalPeg.GalilChainReadyProgress
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier

/-- The watch state, abbreviated. -/
abbrev WState := GalilScaffoldChainWatch.State

/-! ## The parameter predicate of the watch phase -/

/-- **What a caller must supply about the watch phase.**  `Ok` is an arbitrary
predicate on watch states; `WatchOk Ok` says it is strong enough to imply
`ChainReady (.watch ·)` and stable under everything the chain does. -/
structure WatchOk (Ok : WState → Prop) : Prop where
  /-- The lag-positive background consume agrees with the input. -/
  good : ∀ w, Ok w → positive w.lag = true → GalilScaffoldChainWatch.Good w
  /-- The period tape is a complete block. -/
  block : ∀ w, Ok w → WatchBlock w
  /-- The verifier can still move after the background phase. -/
  can : ∀ w m, Ok w → GalilScaffoldChainWatch.Internal w m → canRight m.machine.verifier
  /-- Closure under the background phase. -/
  internal : ∀ w m, Ok w → GalilScaffoldChainWatch.Internal w m → Ok m
  /-- Closure under the credit phase. -/
  outer : ∀ w b m, Ok w → GalilScaffoldChainWatch.Outer w b m → Ok m
  /-- The states `ChainStep.backDone` gives birth to. -/
  born : ∀ (ver : PlaceHead) (v : GalilScaffoldChainPeriod.Tape) (lag margin : Counter),
      canRight ver → OnBlock v → Ok ⟨⟨ver, watchControl v⟩, lag, margin⟩

/-! ## The invariant that really is preserved -/

/-- `ChainReady` strengthened into an invariant, one clause per constructor. -/
def ChainOk (Ok : WState → Prop) : ChainVM → Prop
  | .idle => True
  | .copy t h p v _ _ ver => (∃ n, CopyInv t h p v n) ∧ canRight ver
  | .back v _ _ _ ver => OnBlock v ∧ canRight ver
  | .watch w => Ok w
  | .broken _ => False

/-- **`ChainOk` implies `ChainReady`.**  The `.back` clause is
`watchReady_backDone`; the `.watch` clause is the first three fields of
`WatchOk`. -/
theorem chainReady_of_chainOk {Ok : WState → Prop} (hOk : WatchOk Ok) {x : ChainVM}
    (hx : ChainOk Ok x) : ChainReady x := by
  cases x with
  | idle => exact trivial
  | copy t h p v lag margin ver => exact hx.1
  | back v h lag margin ver =>
    intro hf _
    exact watchReady_backDone hx.1 hf ver hx.2 lag margin
  | watch w => exact ⟨hOk.good w hx, hOk.block w hx, fun m hm => hOk.can w m hx hm⟩
  | broken w => exact hx.elim

/-- A `ChainOk` chain is never broken. -/
theorem chainOk_ne_broken {Ok : WState → Prop} {x : ChainVM} (hx : ChainOk Ok x)
    (w : WState) : x ≠ .broken w := by
  intro h; rw [h] at hx; exact hx.elim

/-! ## The background phase of a watching chain -/

/-- At zero lag the verifier can still move: `Internal.idle` is available, so
`WatchOk.can` applies to `w` itself. -/
theorem canRight_of_zero {Ok : WState → Prop} (hOk : WatchOk Ok) {w : WState} (hw : Ok w)
    (hz : zero w.lag = true) : canRight w.machine.verifier :=
  hOk.can w w hw (.idle w (positive_of_zero hz))

/-- The background phase always steps, into a state that is again `Ok`. -/
theorem internal_exists {Ok : WState → Prop} (hOk : WatchOk Ok) (w : WState) (hw : Ok w) :
    ∃ m, GalilScaffoldChainWatch.Internal w m ∧ Ok m := by
  by_cases hp : positive w.lag = true
  · exact ⟨_, .take w hp (hOk.good w hw hp), hOk.internal w _ hw (.take w hp (hOk.good w hw hp))⟩
  · exact ⟨w, .idle w (Bool.eq_false_iff.mpr hp), hw⟩

/-! ## The credit phase: the trichotomy, and the break -/

/-- **`chainMatched_watch_total` with the invariant tracked.**  Queue, consume,
or break; the first two stay `ChainOk`, the third is the escape. -/
theorem watch_matched {Ok : WState → Prop} (hOk : WatchOk Ok) (w : WState) (hw : Ok w) :
    ∃ z, ChainMatched (.watch w) z ∧ (ChainOk Ok z ∨ ∃ w', z = ChainVM.broken w') := by
  by_cases hz : zero w.lag = true
  · have hcan : canRight w.machine.verifier := canRight_of_zero hOk hw hz
    rcases watch_good_or_break w ⟨hcan, hOk.block w hw⟩ with hg | ⟨a, ha, hne⟩
    · exact ⟨_, .watch _ _ (.immediate w hz hg),
        Or.inl (hOk.outer w true _ hw (.immediate w hz hg))⟩
    · exact ⟨_, .breaks _ _ ⟨hz, hcan, a, ha, hne, rfl⟩, Or.inr ⟨_, rfl⟩⟩
  · have hz' : zero w.lag = false := Bool.eq_false_iff.mpr hz
    exact ⟨_, .watch _ _ (.queued w hz'), Or.inl (hOk.outer w true _ hw (.queued w hz'))⟩

/-- **No break when the prediction always agrees.**  With `Good` at *every*
`Ok` state the zero-lag branch consumes immediately instead of breaking. -/
theorem watch_matched_good {Ok : WState → Prop} (hOk : WatchOk Ok)
    (hgood : ∀ w, Ok w → GalilScaffoldChainWatch.Good w) (w : WState) (hw : Ok w) :
    ∃ z, ChainMatched (.watch w) z ∧ ChainOk Ok z := by
  by_cases hz : zero w.lag = true
  · exact ⟨_, .watch _ _ (.immediate w hz (hgood w hw)),
      hOk.outer w true _ hw (.immediate w hz (hgood w hw))⟩
  · have hz' : zero w.lag = false := Bool.eq_false_iff.mpr hz
    exact ⟨_, .watch _ _ (.queued w hz'), hOk.outer w true _ hw (.queued w hz')⟩

/-! ## One tick, constructor by constructor -/

/-- The `.copy` clause: `copyInv_step` at `n+1`, and at `n = 0` the transition
into `.back` carrying `OnBlock` (`onBlock_write_last`). -/
theorem copy_tick {Ok : WState → Prop} (a : Bool) (t : GalilScaffoldTape.Tape) (h : Counter)
    (p : GalilScaffoldPlace.Place) (v : GalilScaffoldChainPeriod.Tape) (lag margin : Counter)
    (ver : PlaceHead) (hi : ∃ n, CopyInv t h p v n) (hc : canRight ver) :
    ∃ z, ChainTick a (ChainVM.copy t h p v lag margin ver) z ∧ ChainOk Ok z := by
  obtain ⟨n, hn⟩ := hi
  cases n with
  | zero =>
    obtain ⟨ha, hp, hv, hneg, hzr⟩ := hn
    obtain ⟨hpos, b, hb⟩ := hzr rfl
    have hstep : ChainStep (.copy t h p v lag margin ver)
        (.back (GalilScaffoldChainPeriod.write v (.last b)) h lag margin ver) :=
      .copyEnd _ _ _ _ _ _ _ b (answerAhead_zero ha) hpos hb
    have hblk : OnBlock (GalilScaffoldChainPeriod.write v (.last b)) :=
      onBlock_write_last hv b hb
    cases a with
    | false => exact ⟨_, ⟨_, hstep, rfl⟩, hblk, hc⟩
    | true => exact ⟨_, ⟨_, hstep, .back _ _ _ _ _⟩, hblk, hc⟩
  | succ n =>
    have hn' := hn
    obtain ⟨ha, hp, hv, hneg, -⟩ := hn'
    have hr := placeAhead_read hp
    cases hread : GalilScaffoldPlace.read (GalilScaffoldPlace.left p) with
    | none => exact absurd hread hr
    | some c =>
      have hstep : ChainStep (.copy t h p v lag margin ver)
          (.copy (GalilScaffoldTape.moveLeft t) (inc h) (GalilScaffoldPlace.left p)
            (GalilScaffoldChainPeriod.put v c) lag
            (GalilScaffoldChainCredits.decFour margin) ver) :=
        .copyBit _ _ _ _ _ _ _ c (answerAhead_succ_focus ha) (answerAhead_succ_left ha) hread
      have hinv := copyInv_step hn c
      cases a with
      | false => exact ⟨_, ⟨_, hstep, rfl⟩, ⟨n, hinv⟩, hc⟩
      | true => exact ⟨_, ⟨_, hstep, .copy _ _ _ _ _ _ _⟩, ⟨n, hinv⟩, hc⟩

/-- The `.back` clause: `OnBlock` survives `backStep` (`onBlock_moveLeft`), and
at `isFirst` the chain enters the watch phase at a state `WatchOk.born`
declares `Ok`.  This is the *first* place a break can happen: the newborn watch
may be asked to consume immediately. -/
theorem back_tick {Ok : WState → Prop} (hOk : WatchOk Ok) (a : Bool)
    (v : GalilScaffoldChainPeriod.Tape) (h lag margin : Counter) (ver : PlaceHead)
    (hb : OnBlock v) (hc : canRight ver) :
    ∃ z, ChainTick a (ChainVM.back v h lag margin ver) z ∧
      (ChainOk Ok z ∨ ∃ w', z = ChainVM.broken w') := by
  cases hf : GalilScaffoldChainPeriod.isFirst v.focus with
  | false =>
    have hstep : ChainStep (.back v h lag margin ver)
        (.back (GalilScaffoldChainPeriod.moveLeft v) h lag margin ver) :=
      .backStep _ _ _ _ _ hf
    cases a with
    | false => exact ⟨_, ⟨_, hstep, rfl⟩, Or.inl ⟨onBlock_moveLeft hb, hc⟩⟩
    | true => exact ⟨_, ⟨_, hstep, .back _ _ _ _ _⟩, Or.inl ⟨onBlock_moveLeft hb, hc⟩⟩
  | true =>
    have hstep : ChainStep (.back v h lag margin ver)
        (.watch ⟨⟨ver, watchControl v⟩, lag, margin⟩) := .backDone _ _ _ _ _ hf
    have hw : Ok ⟨⟨ver, watchControl v⟩, lag, margin⟩ := hOk.born ver v lag margin hc hb
    cases a with
    | false => exact ⟨_, ⟨_, hstep, rfl⟩, Or.inl hw⟩
    | true =>
      obtain ⟨z, hz, hcase⟩ := watch_matched hOk _ hw
      exact ⟨z, ⟨_, hstep, hz⟩, hcase⟩

/-- The `.watch` clause. -/
theorem watch_tick {Ok : WState → Prop} (hOk : WatchOk Ok) (a : Bool) (w : WState) (hw : Ok w) :
    ∃ z, ChainTick a (ChainVM.watch w) z ∧ (ChainOk Ok z ∨ ∃ w', z = ChainVM.broken w') := by
  obtain ⟨m, hi, hm⟩ := internal_exists hOk w hw
  cases a with
  | false => exact ⟨_, ⟨_, .watchStep _ _ hi, rfl⟩, Or.inl hm⟩
  | true =>
    obtain ⟨z, hz, hcase⟩ := watch_matched hOk m hm
    exact ⟨z, ⟨_, .watchStep _ _ hi, hz⟩, hcase⟩

/-! ## The weakened `ChainTickable` -/

/-- **One tick preserving `ChainOk`, unless the chain breaks.** -/
theorem chainOk_tick {Ok : WState → Prop} (hOk : WatchOk Ok) (a : Bool) {x : ChainVM}
    (hx : ChainOk Ok x) (hne : x ≠ ChainVM.idle) :
    ∃ z, ChainTick a x z ∧ (ChainOk Ok z ∨ ∃ w', z = ChainVM.broken w') := by
  cases x with
  | idle => exact absurd rfl hne
  | copy t h p v lag margin ver =>
    obtain ⟨z, hz, hok⟩ := copy_tick (Ok := Ok) a t h p v lag margin ver hx.1 hx.2
    exact ⟨z, hz, Or.inl hok⟩
  | back v h lag margin ver => exact back_tick hOk a v h lag margin ver hx.1 hx.2
  | watch w => exact watch_tick hOk a w hx
  | broken w => exact hx.elim

/-- **`ChainTickable`, weakened by the break case.**  This is the shape
`PalPeg.GalilReplayChainSeg.ChainTickable` should have: the tick always exists,
and the chain it lands in is ready again *unless* the comparison broke it. -/
theorem chainTickable_unless_break {Ok : WState → Prop} (hOk : WatchOk Ok) (a : Bool)
    {x : ChainVM} (hx : ChainOk Ok x) (hne : x ≠ ChainVM.idle) :
    ∃ z, ChainTick a x z ∧ (ChainReady z ∨ ∃ w', z = ChainVM.broken w') := by
  obtain ⟨z, hz, hcase⟩ := chainOk_tick hOk a hx hne
  rcases hcase with hok | hbr
  · exact ⟨z, hz, Or.inl (chainReady_of_chainOk hOk hok)⟩
  · exact ⟨z, hz, Or.inr hbr⟩

/-! ## No break during a replay -/

/-- **The replay case.**  The replayed comparisons are forced matches over a
span whose periodicity the caller has already established, so the watch
prediction agrees with every read (`hgood`, the intended instance being
`PalPeg.GalilGoodLag.good_of_periodOn`, with the right guard from
`PalPeg.GalilReplaySegment.canRight_of_frontier`).  Then `ChainMatched.breaks`
is unreachable and the full `ChainTickable` conclusion holds. -/
theorem no_break_during_replay {Ok : WState → Prop} (hOk : WatchOk Ok)
    (hgood : ∀ w, Ok w → GalilScaffoldChainWatch.Good w) (a : Bool) {x : ChainVM}
    (hx : ChainOk Ok x) (hne : x ≠ ChainVM.idle) :
    ∃ z, ChainTick a x z ∧ ChainOk Ok z ∧ ChainReady z ∧ z ≠ ChainVM.idle := by
  have main : ∃ z, ChainTick a x z ∧ ChainOk Ok z := by
    cases x with
    | idle => exact absurd rfl hne
    | copy t h p v lag margin ver => exact copy_tick (Ok := Ok) a t h p v lag margin ver hx.1 hx.2
    | back v h lag margin ver =>
      cases hf : GalilScaffoldChainPeriod.isFirst v.focus with
      | false =>
        have hstep : ChainStep (.back v h lag margin ver)
            (.back (GalilScaffoldChainPeriod.moveLeft v) h lag margin ver) :=
          .backStep _ _ _ _ _ hf
        cases a with
        | false => exact ⟨_, ⟨_, hstep, rfl⟩, onBlock_moveLeft hx.1, hx.2⟩
        | true => exact ⟨_, ⟨_, hstep, .back _ _ _ _ _⟩, onBlock_moveLeft hx.1, hx.2⟩
      | true =>
        have hstep : ChainStep (.back v h lag margin ver)
            (.watch ⟨⟨ver, watchControl v⟩, lag, margin⟩) := .backDone _ _ _ _ _ hf
        have hw : Ok ⟨⟨ver, watchControl v⟩, lag, margin⟩ :=
          hOk.born ver v lag margin hx.2 hx.1
        cases a with
        | false => exact ⟨_, ⟨_, hstep, rfl⟩, hw⟩
        | true =>
          obtain ⟨z, hz, hok⟩ := watch_matched_good hOk hgood _ hw
          exact ⟨z, ⟨_, hstep, hz⟩, hok⟩
    | watch w =>
      obtain ⟨m, hi, hm⟩ := internal_exists hOk w hx
      cases a with
      | false => exact ⟨_, ⟨_, .watchStep _ _ hi, rfl⟩, hm⟩
      | true =>
        obtain ⟨z, hz, hok⟩ := watch_matched_good hOk hgood m hm
        exact ⟨z, ⟨_, .watchStep _ _ hi, hz⟩, hok⟩
    | broken w => exact hx.elim
  obtain ⟨z, hz, hok⟩ := main
  exact ⟨z, hz, hok, chainReady_of_chainOk hOk hok, chainTick_ne_idle' hz hne⟩

/-- The `ChainTickable`-shaped corollary, relativised to `ChainOk`: on the
states the replay actually visits, a live ready chain ticks into a live ready
chain. -/
theorem chainTickable_on {Ok : WState → Prop} (hOk : WatchOk Ok)
    (hgood : ∀ w, Ok w → GalilScaffoldChainWatch.Good w) :
    ∀ (a : Bool) (x : ChainVM), ChainOk Ok x → x ≠ ChainVM.idle →
      ∃ z, ChainTick a x z ∧ ChainOk Ok z ∧ ChainReady z :=
  fun a _x hx hne =>
    let ⟨z, hz, hok, hrd, _⟩ := no_break_during_replay hOk hgood a hx hne
    ⟨z, hz, hok, hrd⟩

#print axioms chainReady_of_chainOk
#print axioms chainOk_ne_broken
#print axioms canRight_of_zero
#print axioms internal_exists
#print axioms watch_matched
#print axioms watch_matched_good
#print axioms copy_tick
#print axioms back_tick
#print axioms watch_tick
#print axioms chainOk_tick
#print axioms chainTickable_unless_break
#print axioms no_break_during_replay
#print axioms chainTickable_on

end PalPeg.GalilChainTickable
