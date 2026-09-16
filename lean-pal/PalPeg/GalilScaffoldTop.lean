import PalPeg.GalilScaffoldController

/-!
# The controller tick of the Scala online Galil scaffold

`ScaffoldGalil.transition` runs one of `stepInit … stepReplayStart` by mode.
Each step manipulates the finite controller record and the VM-side components
(heads, counters, search, chain, fpp program). This module transcribes the
controller-level control flow of those steps as an inductive `Tick`, with the
component-level effects abstracted into a `Frame`: one predicate per Scala
block that touches only VM state. The scan/shift/copy/home/fpp/markEnd/
choose/rewind/replayStart branching, the clock protocol, the `output`,
`replaying`, `odd` and `pair` flags and the mode changes are concrete.

The proofs show the mode component follows `ModeStep` and the clock stays
bounded by the match delay, so `BoundedControl delay` is preserved.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldTop
open GalilScaffoldController

/-- VM-side effects of the controller steps, one per Scala block. `σ` is the
state of the components (heads R/L/C/W/V, counters, search, chain, fpp). -/
structure Frame (σ : Type) where
  /-- `stepInit` body: R right, L/C copy R, length++, search.start(0). -/
  init : σ → σ → Prop
  /-- `available` in `stepScan` (with `replaying` short-circuit already split off). -/
  available : σ → Prop
  /-- The per-transition background work of the chain/search components that
  runs before the mode step (`transition` steps the verifier every call). -/
  background : σ → σ → Prop
  /-- The `clock == 0` block up to `chain.checkPair`: R right, L left,
  search.advanceMatch or radius++, checkPair. -/
  compare : σ → σ → Prop
  /-- `left.read() == right.read()`. -/
  matched : σ → Prop
  /-- `!replaying && chain.canShift && chain.prediction() == right.read()`. -/
  shiftGuard : σ → Prop
  /-- `matchedPlace` VM part: length += 2, chain.matched if active, replay-- if replaying. -/
  matchedPlace : Bool → σ → σ → Prop
  /-- `replay.sign == 0` after the decrement (only consulted when replaying). -/
  replayExhausted : σ → Bool
  /-- `!right.gap`: R stands on a letter, so the output is refreshed. -/
  onLetter : σ → Prop
  /-- `left.isFirst`. -/
  leftFirst : σ → Prop
  /-- `beginChainShift` VM part. -/
  beginShift : σ → σ → Prop
  /-- `beginFallback` VM part. -/
  beginFallback : σ → σ → Prop
  /-- `remaining.sign > 0`. -/
  remainingPos : σ → Prop
  /-- One unit of `stepShift`. -/
  shiftOne : σ → σ → Prop
  /-- One unit of `stepCopy`. -/
  copyOne : σ → σ → Prop
  /-- `source.write(END)` at the end of the copy. -/
  copyEnd : σ → σ → Prop
  /-- `source.read() == LEFT`. -/
  atLeft : σ → Prop
  /-- `fpp.start()`. -/
  fppStart : σ → σ → Prop
  /-- `source.move(-1)`. -/
  homeStep : σ → σ → Prop
  /-- A `stepFpp` slice that does not reach the halt. -/
  fppSlice : σ → σ → Prop
  /-- A `stepFpp` slice reaching the halt, then `marks.move(1); write(FIRST); move(1)`. -/
  fppDone : σ → σ → Prop
  /-- `marks.read() == END`. -/
  atEnd : σ → Prop
  /-- `marks.move(-1)`. -/
  markBack : σ → σ → Prop
  /-- `marks.move(1)`. -/
  markForward : σ → σ → Prop
  /-- `marks.read() == "1" || marks.read() == FIRST`. -/
  markSet : σ → Prop
  /-- `stepChoose` selection block: L/C copy R, length := 1, radius := 0. -/
  choose : σ → σ → Prop
  /-- `marks.read() == FIRST`. -/
  atFirst : σ → Prop
  /-- `fpp.reset()`. -/
  fppReset : σ → σ → Prop
  /-- `stepRewind` unit without the centre move: marks back, L left, length++. -/
  rewindOne : σ → σ → Prop
  /-- `stepRewind` unit with the centre move (`pair == 0`): also C left, radius++. -/
  rewindPair : σ → σ → Prop
  /-- `stepReplayStart` VM part: replay := radius, R/L copy C, radius/length reset,
  chain idle, search.start(0). -/
  replayStart : σ → σ → Prop
  /-- `replay.sign > 0` after `stepReplayStart`. -/
  replayPos : σ → Bool
  /-- The Broken-chain restart in the transition prelude:
  `search.start(chain.last)`, chain idle, `clock := matchDelay`. -/
  restart : σ → σ → Prop

structure State (σ : Type) where
  ctl : Control
  vm : σ

/-- The Scala `output` refresh `if (!right.gap) output = left.isFirst`. -/
def refresh {σ : Type} (F : Frame σ) (s : σ) (old : Bool) : Bool → Prop :=
  fun o => (F.onLetter s → (o = true ↔ F.leftFirst s)) ∧ (¬ F.onLetter s → o = old)

variable {σ : Type} (F : Frame σ) (delay : ℕ)

/-- One `ScaffoldGalil.transition` call, by mode. Only the controller-level
flow is concrete; VM effects go through `F`. -/
inductive Tick : State σ → State σ → Prop
  | init (c : Control) (s s' : σ) (hm : c.mode = .init) (h : F.init s s') :
      Tick ⟨c, s⟩ ⟨{c with mode := .scan, output := true}, s'⟩
  | scan_wait (c : Control) (s s' : σ) (hm : c.mode = .scan)
      (h : c.replaying = false ∧ ¬ F.available s) (hb : F.background s s') : Tick ⟨c, s⟩ ⟨c, s'⟩
  | scan_count (c : Control) (s s' : σ) (hm : c.mode = .scan)
      (h : c.replaying = true ∨ F.available s) (hc : 1 < c.clock) (hb : F.background s s') :
      Tick ⟨c, s⟩ ⟨{c with clock := c.clock - 1}, s'⟩
  | scan_match (c : Control) (s s' s'' : σ) (o : Bool) (hm : c.mode = .scan)
      (h : c.replaying = true ∨ F.available s) (hc : c.clock = 1)
      (hcmp : F.compare s s') (hmt : F.matched s')
      (hpl : F.matchedPlace c.replaying s' s'')
      (ho : refresh F s'' c.output o) :
      Tick ⟨c, s⟩ ⟨{c with clock := delay, output := o, replaying := c.replaying && !F.replayExhausted s''}, s''⟩
  | scan_shift (c : Control) (s s' s'' : σ) (hm : c.mode = .scan)
      (h : c.replaying = true ∨ F.available s) (hc : c.clock = 1)
      (hcmp : F.compare s s') (hmt : ¬ F.matched s') (hr : c.replaying = false)
      (hg : F.shiftGuard s') (hb : F.beginShift s' s'') :
      Tick ⟨c, s⟩ ⟨{c with clock := delay, mode := .shift}, s''⟩
  | scan_fallback (c : Control) (s s' s'' : σ) (hm : c.mode = .scan)
      (h : c.replaying = true ∨ F.available s) (hc : c.clock = 1)
      (hcmp : F.compare s s') (hmt : ¬ F.matched s')
      (hg : c.replaying = true ∨ ¬ F.shiftGuard s') (hr : c.replaying = false)
      (hb : F.beginFallback s' s'') :
      Tick ⟨c, s⟩ ⟨{c with clock := delay, mode := .copy}, s''⟩
  | shift_one (c : Control) (s s' : σ) (hm : c.mode = .shift) (hp : F.remainingPos s)
      (h : F.shiftOne s s') : Tick ⟨c, s⟩ ⟨c, s'⟩
  | shift_done (c : Control) (s : σ) (o : Bool) (hm : c.mode = .shift) (hp : ¬ F.remainingPos s)
      (ho : refresh F s c.output o) : Tick ⟨c, s⟩ ⟨{c with mode := .scan, output := o}, s⟩
  | copy_one (c : Control) (s s' : σ) (hm : c.mode = .copy) (hp : F.remainingPos s)
      (h : F.copyOne s s') : Tick ⟨c, s⟩ ⟨c, s'⟩
  | copy_done (c : Control) (s s' : σ) (hm : c.mode = .copy) (hp : ¬ F.remainingPos s)
      (h : F.copyEnd s s') : Tick ⟨c, s⟩ ⟨{c with mode := .home}, s'⟩
  | home_start (c : Control) (s s' : σ) (hm : c.mode = .home) (hl : F.atLeft s)
      (h : F.fppStart s s') : Tick ⟨c, s⟩ ⟨{c with mode := .fpp}, s'⟩
  | home_step (c : Control) (s s' : σ) (hm : c.mode = .home) (hl : ¬ F.atLeft s)
      (h : F.homeStep s s') : Tick ⟨c, s⟩ ⟨c, s'⟩
  | fpp_slice (c : Control) (s s' : σ) (hm : c.mode = .fpp) (h : F.fppSlice s s') :
      Tick ⟨c, s⟩ ⟨c, s'⟩
  | fpp_done (c : Control) (s s' : σ) (hm : c.mode = .fpp) (h : F.fppDone s s') :
      Tick ⟨c, s⟩ ⟨{c with mode := .markEnd}, s'⟩
  | markEnd_found (c : Control) (s s' : σ) (hm : c.mode = .markEnd) (he : F.atEnd s)
      (h : F.markBack s s') : Tick ⟨c, s⟩ ⟨{c with mode := .choose, odd := false}, s'⟩
  | markEnd_step (c : Control) (s s' : σ) (hm : c.mode = .markEnd) (he : ¬ F.atEnd s)
      (h : F.markForward s s') : Tick ⟨c, s⟩ ⟨c, s'⟩
  | choose_select (c : Control) (s s' : σ) (hm : c.mode = .choose) (ho : c.odd = true)
      (hs : F.markSet s) (h : F.choose s s') :
      Tick ⟨c, s⟩ ⟨{c with mode := .rewind, pair := false}, s'⟩
  | choose_step (c : Control) (s s' : σ) (hm : c.mode = .choose)
      (hs : c.odd = false ∨ ¬ F.markSet s) (h : F.markBack s s') :
      Tick ⟨c, s⟩ ⟨{c with odd := !c.odd}, s'⟩
  | rewind_done (c : Control) (s s' : σ) (hm : c.mode = .rewind) (hf : F.atFirst s)
      (h : F.fppReset s s') : Tick ⟨c, s⟩ ⟨{c with mode := .replayStart}, s'⟩
  | rewind_one (c : Control) (s s' : σ) (hm : c.mode = .rewind) (hf : ¬ F.atFirst s)
      (hp : c.pair = false) (h : F.rewindOne s s') : Tick ⟨c, s⟩ ⟨{c with pair := true}, s'⟩
  | rewind_pair (c : Control) (s s' : σ) (hm : c.mode = .rewind) (hf : ¬ F.atFirst s)
      (hp : c.pair = true) (h : F.rewindPair s s') : Tick ⟨c, s⟩ ⟨{c with pair := false}, s'⟩
  | replayStart (c : Control) (s s' : σ) (o : Bool) (hm : c.mode = .replayStart)
      (h : F.replayStart s s')
      (ho : F.replayPos s' = true → o = c.output)
      (ho' : F.replayPos s' = false → refresh F s' c.output o) :
      Tick ⟨c, s⟩ ⟨{c with mode := .scan, clock := delay, output := o, replaying := F.replayPos s'}, s'⟩
  | restart (c : Control) (s s' : σ) (hm : c.mode = .scan) (hb : F.restart s s') :
      Tick ⟨c, s⟩ ⟨{c with clock := delay}, s'⟩

/-- The mode component of a tick is stationary or a `ModeStep` edge. -/
theorem tick_mode {x y : State σ} (h : Tick F delay x y) :
    y.ctl.mode = x.ctl.mode ∨ ModeStep x.ctl.mode y.ctl.mode := by
  cases h <;> first
    | exact Or.inl rfl
    | (right; simp only [*]; constructor)

/-- The clock is only decremented (while positive) or reset to `delay`. -/
theorem tick_bounded {x y : State σ} (h : Tick F delay x y) (hb : Bounded delay x.ctl) :
    Bounded delay y.ctl := by
  unfold Bounded at *
  cases h <;> dsimp only at hb ⊢ <;> omega

#print axioms tick_mode
#print axioms tick_bounded

end PalPeg.GalilScaffoldTop
