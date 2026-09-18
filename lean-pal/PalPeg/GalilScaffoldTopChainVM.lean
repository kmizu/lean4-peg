import PalPeg.GalilScaffoldChainFallback

/-!
# The chain component with its modes (definitions)

`ScaffoldChain.scala`: `Idle → Copy → Back → Watch (→ Broken)`. `start()`
resets the period tape to `FRONT_MARK+centre`, copies the centre to walker
and verifier, aliases `lag`/`margin` to `radius`; `stepCopy` consumes the
unary DP answer copying C-1, C-2, … onto the period tape (`h++`,
`margin -= 4`); at LEFT it writes the tail mark and goes `Back`; `stepBack`
rewinds to the front mark and moves one cell right into `Watch`, whose
control is exactly `GalilScaffoldChainConsume.ready`. `chain.matched()` at a
matched scan comparison: `margin++`, then in Watch with `lag = 0` an
immediate consume (or the break), otherwise `lag++`. A chain tick is the
background step followed by the optional credit; on a watching chain it is
exactly `GalilScaffoldChainWatch.Tick`.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier

/-- The chain break at a matched comparison (`JointBreak`): lag zero, the
verifier can advance, the period symbol is `a` but the input under the
verifier is not `a`; the verifier still consumes and the margin grows. -/
def BreakStep (w w' : GalilScaffoldChainWatch.State) : Prop :=
  GalilScaffoldCounter.zero w.lag = true ∧ GalilScaffoldChainVerifier.canRight w.machine.verifier ∧
  ∃ a : Fin 3, GalilScaffoldChainConsume.symbol w.machine.control.period.focus = some a ∧
    GalilScaffoldInputHead.read (right w.machine.verifier) ≠ some a ∧
    w' = ⟨consume w.machine, w.lag, GalilScaffoldCounter.inc w.margin⟩

/-- The chain break during the **background** consume (`ScaffoldChain.step()`'s
`case Mode.Watch if lag.sign > 0 => if (consume()) { lag.dec() }`): the lag is
**positive**, the verifier can advance, the period symbol is `a` but the input
under the verifier is not `a`.  The verifier still consumes, but — unlike
`BreakStep`, which sits on the `matched()` path — neither the lag is decremented
(`consume()` returned `false`) nor the margin incremented (`margin.inc()` lives
in `matched()`).

Without this the model has **no successor at all** for a positive-lag watch whose
prediction fails, while the Scala source drops to `Mode.Broken`; that gap is what
forced the false `WatchOk.good` (see `PalPeg.ChainStepGap` and
`PalPeg.WatchOkRefute`). -/
def BreakStepPos (w w' : GalilScaffoldChainWatch.State) : Prop :=
  GalilScaffoldCounter.positive w.lag = true ∧
  GalilScaffoldChainVerifier.canRight w.machine.verifier ∧
  ∃ a : Fin 3, GalilScaffoldChainConsume.symbol w.machine.control.period.focus = some a ∧
    GalilScaffoldInputHead.read (right w.machine.verifier) ≠ some a ∧
    w' = ⟨consume w.machine, w.lag, w.margin⟩

inductive ChainVM
  | idle
  | copy (answer : GalilScaffoldTape.Tape) (h : Counter) (walker : GalilScaffoldPlace.Place)
      (period : GalilScaffoldChainPeriod.Tape) (lag margin : Counter) (verifier : PlaceHead)
  | back (period : GalilScaffoldChainPeriod.Tape) (h lag margin : Counter) (verifier : PlaceHead)
  | watch (w : GalilScaffoldChainWatch.State)
  | broken (w : GalilScaffoldChainWatch.State)

/-- `chain.start()` at the found search. -/
def chainStart (answer : GalilScaffoldTape.Tape) (c : Fin 3) (walker : GalilScaffoldPlace.Place)
    (verifier : PlaceHead) (radius : Counter) : ChainVM :=
  .copy answer reset walker (GalilScaffoldChainPeriod.start c) radius radius verifier

/-- The watch control at the end of `Back`: `ready`'s shape. -/
def watchControl (period : GalilScaffoldChainPeriod.Tape) : GalilScaffoldChainConsume.State :=
  ⟨GalilScaffoldChainPeriod.moveRight period, reset, reset, reset, 0, true, false⟩

/-- One background chain step (`chain.step(answer)`). -/
inductive ChainStep : ChainVM → ChainVM → Prop
  | idle : ChainStep .idle .idle
  | brokenIdle (w) : ChainStep (.broken w) (.broken w)
  | copyBit (t : GalilScaffoldTape.Tape) (h) (p) (v) (lag margin) (ver) (a : Fin 3)
      (one : t.focus = 8) (legal : t.left ≠ [])
      (present : GalilScaffoldPlace.read (GalilScaffoldPlace.left p) = some a) :
      ChainStep (.copy t h p v lag margin ver)
        (.copy (GalilScaffoldTape.moveLeft t) (inc h) (GalilScaffoldPlace.left p)
          (GalilScaffoldChainPeriod.put v a) lag (GalilScaffoldChainCredits.decFour margin) ver)
  | copyEnd (t) (h) (p) (v) (lag margin) (ver) (b : Fin 3)
      (hleft : t.focus = 4) (hp : positive h = true) (hv : v.focus = .plain b) :
      ChainStep (.copy t h p v lag margin ver) (.back (GalilScaffoldChainPeriod.write v (.last b)) h lag margin ver)
  | backStep (v) (h lag margin) (ver) (hf : GalilScaffoldChainPeriod.isFirst v.focus = false) :
      ChainStep (.back v h lag margin ver) (.back (GalilScaffoldChainPeriod.moveLeft v) h lag margin ver)
  | backDone (v) (h lag margin) (ver) (hf : GalilScaffoldChainPeriod.isFirst v.focus = true) :
      ChainStep (.back v h lag margin ver) (.watch ⟨⟨ver, watchControl v⟩, lag, margin⟩)
  | watchStep (w w') (ht : GalilScaffoldChainWatch.Internal w w') : ChainStep (.watch w) (.watch w')
  | watchBreak (w w') (hb : BreakStepPos w w') : ChainStep (.watch w) (.broken w')

/-- `chain.matched()` at a matched scan comparison. -/
inductive ChainMatched : ChainVM → ChainVM → Prop
  | idle : ChainMatched .idle .idle
  | copy (t h p v lag margin ver) :
      ChainMatched (.copy t h p v lag margin ver) (.copy t h p v (inc lag) (inc margin) ver)
  | back (v h lag margin ver) : ChainMatched (.back v h lag margin ver) (.back v h (inc lag) (inc margin) ver)
  | watch (w w') (ho : GalilScaffoldChainWatch.Outer w true w') : ChainMatched (.watch w) (.watch w')
  | breaks (w w') (hb : BreakStep w w') : ChainMatched (.watch w) (.broken w')
  | brokenMatched (w) :
      ChainMatched (.broken w)
        (.broken ⟨w.machine, GalilScaffoldCounter.inc w.lag, GalilScaffoldCounter.inc w.margin⟩)

inductive ChainSteps : ℕ → ChainVM → ChainVM → Prop
  | zero (x) : ChainSteps 0 x x
  | succ {n x y z} (h : ChainStep x y) (hr : ChainSteps n y z) : ChainSteps (n+1) x z

theorem chainSteps_trans {m n : ℕ} {x y z : ChainVM} (h1 : ChainSteps m x y) (h2 : ChainSteps n y z) :
    ChainSteps (m+n) x z := by
  induction h1 with
  | zero => simpa using h2
  | succ h _ ih => rw [Nat.add_right_comm]; exact .succ h (ih h2)

theorem watchControl_ready (c : Fin 3) (ys : List (Fin 3)) (b : Fin 3) :
    watchControl ⟨[], .first c, ys.map GalilScaffoldChainPeriod.Token.plain ++ [.last b]⟩ =
      GalilScaffoldChainConsume.ready c ys b := rfl

/-- One chain tick on the match event `a`: background step, then the credit. -/
def ChainTick (a : Bool) (x z : ChainVM) : Prop :=
  ∃ y, ChainStep x y ∧ (if a then ChainMatched y z else z = y)

/-- On a watching chain, the disabled tick is the watch's disabled tick. -/
theorem chainTick_of_watch_false {w w' : GalilScaffoldChainWatch.State}
    (h : GalilScaffoldChainWatch.Tick w false w') : ChainTick false (.watch w) (.watch w') := by
  cases h with
  | step hi ho =>
    cases ho
    exact ⟨_, .watchStep _ _ hi, rfl⟩

/-- On a watching chain, the enabled tick is the watch's enabled tick. -/
theorem chainTick_of_watch_true {w w' : GalilScaffoldChainWatch.State}
    (h : GalilScaffoldChainWatch.Tick w true w') : ChainTick true (.watch w) (.watch w') := by
  cases h with
  | step hi ho => exact ⟨_, .watchStep _ _ hi, .watch _ _ ho⟩

theorem positive_of_zero {c : Counter} (hz : zero c = true) : positive c = false := by
  unfold zero at hz
  unfold positive
  simp only [Bool.and_eq_true] at hz
  rw [hz.1]; rfl

/-- The break at a matched comparison is an enabled chain tick into `broken`. -/
theorem chainTick_of_break {w w' : GalilScaffoldChainWatch.State} (h : BreakStep w w') :
    ChainTick true (.watch w) (.broken w') :=
  ⟨_, .watchStep _ _ (.idle w (positive_of_zero h.1)), .breaks _ _ h⟩

#print axioms chainTick_of_watch_true
#print axioms chainTick_of_break

end PalPeg.GalilScaffoldChainInputSupply

namespace PalPeg.GalilScaffoldChainInputSupply

open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier

/-- **`Internal` と `BreakStepPos` は排他。** 前者は lag ゼロか一致（`Good`）を要求し、
後者は正 lag と不一致を要求する。`ChainStep` の一意性がこれで保たれる。 -/
theorem internal_breakStepPos_false {w w' w'' : GalilScaffoldChainWatch.State}
    (hi : GalilScaffoldChainWatch.Internal w w') (hb : BreakStepPos w w'') : False := by
  obtain ⟨hp, -, a, hsym, hne, -⟩ := hb
  cases hi with
  | idle hz => rw [hz] at hp; cases hp
  | take _ hg =>
    obtain ⟨-, a', hsym', heq⟩ := hg
    rw [hsym] at hsym'
    cases hsym'
    exact hne heq

/-- **`BreakStepPos` は関数的。** 行き先は `⟨consume machine, lag, margin⟩` の一点。 -/
theorem breakStepPos_unique {w w' w'' : GalilScaffoldChainWatch.State}
    (h1 : BreakStepPos w w') (h2 : BreakStepPos w w'') : w' = w'' := by
  obtain ⟨-, -, -, -, -, he1⟩ := h1
  obtain ⟨-, -, -, -, -, he2⟩ := h2
  rw [he1, he2]

/-- **`Good` を仮定しない全域性。** 正の lag では、period と入力が一致すれば
`Internal.take`、食い違えば `watchBreak` に落ちる。どちらでも後続状態が存在する。
必要なのは「verifier が右に動ける」と「period の焦点が記号を持つ」だけで、
**予測が当たること（`Good`）は要らない**。 -/
theorem chainStep_watch_total_of_symbol (s : GalilScaffoldChainWatch.State)
    (hcan : GalilScaffoldChainVerifier.canRight s.machine.verifier)
    (hsym : ∃ a : Fin 3,
      GalilScaffoldChainConsume.symbol s.machine.control.period.focus = some a) :
    ∃ y, ChainStep (ChainVM.watch s) y := by
  by_cases hp : positive s.lag = true
  · obtain ⟨a, ha⟩ := hsym
    by_cases hg : GalilScaffoldInputHead.read (right s.machine.verifier) = some a
    · exact ⟨_, .watchStep _ _ (.take s hp ⟨hcan, a, ha, hg⟩)⟩
    · exact ⟨_, .watchBreak _ _ ⟨hp, hcan, a, ha, hg, rfl⟩⟩
  · exact ⟨_, .watchStep _ _ (.idle s (Bool.eq_false_iff.mpr hp))⟩

#print axioms internal_breakStepPos_false
#print axioms breakStepPos_unique
#print axioms chainStep_watch_total_of_symbol

end PalPeg.GalilScaffoldChainInputSupply
