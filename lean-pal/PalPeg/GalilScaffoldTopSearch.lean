import PalPeg.GalilScaffoldTopOutput

/-!
# The search co-process on the unified VM

`stepScan` calls `search.advanceMatch()` at every comparison while the
search is active and the chain idle; the DP program runs its calls between
comparisons. At event granularity this is one `SafeQuanta` step on the
match event: 64 safe DP calls, then `advance a`. `galilFrameS` is
`galilFrame` with the comparison extended by that quantum on the search
projection (`searchLens`); every other tick is unchanged.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController

/-- One search quantum on the match event `a`. -/
def searchQuantum (a : Bool) (v v' : SearchVM) : Prop :=
  GalilScaffoldSearchRun.SafeQuanta v.search v.dp [a] v'.search v'.dp ∧ v'.lower = v.lower

/-- The search is not running: no quantum, state unchanged. -/
def searchIdle (v v' : SearchVM) : Prop := v.search.mode ≠ .run ∧ v' = v

/-- `chain.mode == Idle`. -/
def ChainVM.isIdle : ChainVM → Bool
  | .idle => true
  | _ => false

/-- `!search.mode.inactive` (Scala: inactive = Idle, Found, Missed). -/
def searchActive (m : GalilScaffoldSearchFinish.Mode) : Bool :=
  !(m = .idle || m = .found || m = .missed)

/-- The radius counter after a comparison: `radius.inc()`, either directly
or inside `search.advanceMatch()` (which also pays one debt credit — that
part is the `advance` of the search quantum). -/
def radiusAfter (s : GalilVM) : GalilScaffoldCounter.Counter := GalilScaffoldCounter.inc s.radius

/-- `chain.matched()`'s `if (periodOnly) cycle.dec()`: the continuation
countdown after a matched comparison. -/
def cycleAfter (s : GalilVM) : GalilScaffoldCounter.Counter :=
  if s.periodOnly then GalilScaffoldCounter.dec s.cycle else s.cycle

/-- The state after a matched comparison: heads and chain from the scan
projection, the search quantum, `radius++`, `matchedPlace`'s `length += 2`
and `chain.matched()`'s `cycle--` (in `periodOnly`). -/
def afterCompare (s : GalilVM) (vs : ScanVM) (vq : SearchVM) : GalilVM :=
  {searchLens.set (scanLens.set s vs) vq with radius := radiusAfter s, cycle := cycleAfter s, length := GalilScaffoldCounter.inc (GalilScaffoldCounter.inc s.length)}

/-- The state after a mismatched comparison: only `radius++` besides the
heads, chain and search quantum (the entries do the rest). -/
def afterMismatch (s : GalilVM) (vs : ScanVM) (vq : SearchVM) : GalilVM :=
  {searchLens.set (scanLens.set s vs) vq with radius := radiusAfter s}

/-- The comparison with the search co-process: the scan/chain part on the
scan projection, one quantum (or idleness) on the search projection, the
counters updated by the outcome, the rest of the VM untouched. The event
is whether the outer symbols agree. -/
def compareVM (P : Shared) (q : ℕ) (first : Fin 9) (s t : GalilVM) : Prop :=
  ∃ (vs : ScanVM) (vq : SearchVM) (a : Bool),
    (galilFrame P q first).compare s (scanLens.set s vs) ∧
    (a = true ↔ (galilFrame P q first).matched (scanLens.set s vs)) ∧
    (searchQuantum a (searchLens.get s) vq ∨ searchIdle (searchLens.get s) vq) ∧
    t = (if a then afterCompare s vs vq else afterMismatch s vs vq)

/-- The chain effect of a comparison: an ordinary chain tick on the match
event, or — when the chain is idle and the search quantum ends `found` —
`chain.start()` followed by the match credit. -/
def chainAt (a : Bool) (found : Bool) (answer : GalilScaffoldTape.Tape) (c : Fin 3)
    (walker : GalilScaffoldPlace.Place) (ver : GalilScaffoldInputHead.PlaceHead) (radius : GalilScaffoldCounter.Counter)
    (x z : ChainVM) : Prop :=
  (x ≠ .idle ∧ ChainTick a x z) ∨
  (x = .idle ∧ found = false ∧ z = .idle) ∨
  (x = .idle ∧ found = true ∧
    (if a then ChainMatched (chainStart answer c walker ver radius) z else z = chainStart answer c walker ver radius))

/-- The prepare-controller view of the search state. -/
def SearchVM.toPrep (v : SearchVM) : GalilScaffoldPrepareControl.State :=
  ⟨v.search.mode, v.dp, v.search.work, v.search.span, v.search.debt, v.walker, v.search.finalStage⟩

def SearchVM.ofPrep (p : GalilScaffoldPrepareControl.State) (quarter : Fin 4)
    (lower : GalilScaffoldCounter.Counter) : SearchVM :=
  ⟨GalilScaffoldStagePrepare.runState p quarter, p.program, lower, p.walker⟩

/-- One background call of the search (chain idle, search active) followed
by the comparison advance `a` (`advanceMatch`'s debt decrement), by mode:
inactive modes are inert; `grow` adds span or dispatches `prepare`; the
preparation modes are `PrepareControl.Tick`; `run` is a 64-call quantum;
`wait` and `double` are the scheduler's steps. `center` is the centre place
the window is copied from. -/
def searchStep (center : GalilScaffoldPlace.Place) (a : Bool) (v v' : SearchVM) : Prop :=
  match v.search.mode with
  | .idle | .found | .missed => v' = v
  | .grow =>
      if GalilScaffoldCounter.positive v.search.work = true then
        v' = SearchVM.ofPrep (GalilScaffoldPreparePaced.afterAdvance a
          (GalilScaffoldStagePrepare.growStep v.toPrep)) v.search.quarter v.lower
      else
        v' = SearchVM.ofPrep (GalilScaffoldPreparePaced.afterAdvance a
          (GalilScaffoldPrepareControl.prepare v.toPrep v.lower center)) v.search.quarter v.lower
  | .lower | .lowerHome | .copy | .home =>
      ∃ y, GalilScaffoldPrepareControl.Tick true v.toPrep y ∧
        v' = SearchVM.ofPrep (GalilScaffoldPreparePaced.afterAdvance a y) v.search.quarter v.lower
  | .run =>
      GalilScaffoldSearchRun.SafeQuanta v.search v.dp [a] v'.search v'.dp ∧
        v'.lower = v.lower ∧ v'.walker = v.walker
  | .wait =>
      v' = {v with search := GalilScaffoldSearchRun.advance a (GalilScaffoldDouble.waitStep true v.search)}
  | .double =>
      if GalilScaffoldCounter.positive v.search.work = true then
        v' = {v with search := GalilScaffoldSearchRun.advance a (GalilScaffoldDouble.step v.search)}
      else
        v' = SearchVM.ofPrep (GalilScaffoldPreparePaced.afterAdvance a
          (GalilScaffoldPrepareControl.prepare v.toPrep v.lower center)) v.search.quarter v.lower

/-- The search effect of a scan tick: the search steps only while the chain
is idle (Scala's `background`), with the advance `a` at a comparison. -/
def searchEffect (P : Shared) (a : Bool) (s : GalilVM) (vq : SearchVM) : Prop :=
  (s.chain = .idle ∧ searchStep (P.place s) a (searchLens.get s) vq) ∨
  (s.chain ≠ .idle ∧ vq = searchLens.get s)

theorem searchEffect_run (P : Shared) {a : Bool} {s : GalilVM} {vq : SearchVM}
    (h : searchEffect P a s vq) (hidle : s.chain = .idle) (hrun : s.search.mode = .run) :
    GalilScaffoldSearchRun.SafeQuanta s.search s.dp [a] vq.search vq.dp ∧
      vq.lower = s.lower ∧ vq.walker = s.walker := by
  rcases h with ⟨_, hs⟩ | ⟨hne, _⟩
  · have hm : (searchLens.get s).search.mode = .run := hrun
    unfold searchStep at hs
    rw [hm] at hs
    exact hs
  · exact absurd hidle hne

theorem searchEffect_active (P : Shared) {a : Bool} {s : GalilVM} {vq : SearchVM}
    (h : searchEffect P a s vq) (hne : s.chain ≠ .idle) : vq = searchLens.get s := by
  rcases h with ⟨hi, _⟩ | ⟨_, he⟩
  · exact absurd hi hne
  · exact he

/-- The comparison with the search co-process and the chain start
(`compareVM` when the chain is active). The centre symbol and place are
read from the VM by `P.centre`/`P.place` (their decoding from the heads is
the input-supply layer's). The answer tape is the one after the quantum,
as `chain.start()` runs after the search steps. -/
def compareFound (P : Shared) (q : ℕ) (first : Fin 9) (s t : GalilVM) : Prop :=
  ∃ (vs : ScanVM) (vq : SearchVM) (a : Bool),
    vs.left = GalilScaffoldInputHead.left s.left ∧ vs.right = GalilScaffoldChainVerifier.right s.right ∧
    (a = true ↔ (galilFrame P q first).matched (scanLens.set s vs)) ∧
    searchEffect P a s vq ∧
    chainAt a (decide (vq.search.mode = .found)) (vq.dp.config.tapes 11) (P.centre s) (P.place s) s.center s.radius
      s.chain vs.chain ∧
    t = (if a then afterCompare s vs vq else afterMismatch s vs vq)

/-- The background of a scan tick: heads and clock untouched, the search
stepped without advance, and the chain effect `chainAt false` — an ordinary
disabled chain tick, or `chain.start()` when the idle chain's search lands
in `found` during this background. Everything else is kept. -/
def backgroundS (P : Shared) (q : ℕ) (first : Fin 9) (s s' : GalilVM) : Prop :=
  s'.left = s.left ∧ s'.right = s.right ∧ searchEffect P false s (searchLens.get s') ∧
  chainAt false (decide ((searchLens.get s').search.mode = .found)) ((searchLens.get s').dp.config.tapes 11)
    (P.centre s) (P.place s) s.center s.radius s.chain s'.chain ∧
  s' = searchLens.set (scanLens.set s (scanLens.get s')) (searchLens.get s')

def galilFrameS (P : Shared) (q : ℕ) (first : Fin 9) : Frame GalilVM :=
  {galilFrame P q first with compare := compareFound P q first, background := backgroundS P q first}

/-- The fields of a scan background tick: heads kept, the chain by
`chainAt false`, everything else kept, the search stepped without advance. -/
theorem backgroundS_fields (P : Shared) (q : ℕ) (first : Fin 9) {s s' : GalilVM}
    (hb : (galilFrameS P q first).background s s') :
    s'.left = s.left ∧ s'.right = s.right ∧
      chainAt false (decide ((searchLens.get s').search.mode = .found)) ((searchLens.get s').dp.config.tapes 11)
        (P.centre s) (P.place s) s.center s.radius s.chain s'.chain ∧
      s'.center = s.center ∧ s'.periodOnly = s.periodOnly ∧ s'.radius = s.radius ∧
      s'.length = s.length ∧ s'.cycle = s.cycle ∧ s'.remaining = s.remaining ∧ s'.replay = s.replay ∧
      s'.fpp = s.fpp ∧ searchEffect P false s (searchLens.get s') := by
  obtain ⟨hl, hr, hse, hch, hset⟩ := hb
  refine ⟨hl, hr, hch, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hse⟩
  all_goals (rw [hset]; rfl)

/-- With an active chain the background's chain effect is a disabled tick. -/
theorem backgroundS_chainTick (P : Shared) (q : ℕ) (first : Fin 9) {s s' : GalilVM}
    (hb : (galilFrameS P q first).background s s') (hne : s.chain ≠ .idle) :
    ChainTick false s.chain s'.chain := by
  obtain ⟨_, _, hch, _⟩ := backgroundS_fields P q first hb
  rcases hch with ⟨_, ht⟩ | ⟨hi, _⟩ | ⟨hi, _⟩
  · exact ht
  · exact absurd hi hne
  · exact absurd hi hne

/-- With an idle chain the background either keeps it idle (search not
found) or starts it (search found). -/
theorem backgroundS_idle (P : Shared) (q : ℕ) (first : Fin 9) {s s' : GalilVM}
    (hb : (galilFrameS P q first).background s s') (hi : s.chain = .idle) :
    ((searchLens.get s').search.mode ≠ .found ∧ s'.chain = .idle) ∨
    ((searchLens.get s').search.mode = .found ∧
      s'.chain = chainStart ((searchLens.get s').dp.config.tapes 11) (P.centre s) (P.place s) s.center s.radius) := by
  obtain ⟨_, _, hch, _⟩ := backgroundS_fields P q first hb
  rcases hch with ⟨hne, _⟩ | ⟨_, hf, hz⟩ | ⟨_, hf, hz⟩
  · exact absurd hi hne
  · exact Or.inl ⟨by simpa using hf, hz⟩
  · exact Or.inr ⟨by simpa using hf, hz⟩

/-- A chain tick from `idle` stays `idle`. -/
theorem chainTick_idle {a : Bool} {z : ChainVM} (h : ChainTick a .idle z) : z = .idle := by
  obtain ⟨y, hs, hm⟩ := h
  cases hs
  cases a
  · simpa using hm
  · simp at hm
    cases hm
    rfl

theorem chainTick_source_ne_idle {a : Bool} {x z : ChainVM} (h : ChainTick a x z) (hz : z ≠ .idle) :
    x ≠ .idle := by
  intro hx
  subst hx
  exact hz (chainTick_idle h)

/-- Ticks of `galilFrame` that do not compare are ticks of `galilFrameS`. -/
theorem tick_S_of_tick (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) {c c' : Control} {s t : GalilVM}
    (h : Tick (galilFrame P q first) delay ⟨c, s⟩ ⟨c', t⟩) (hm : c.mode ≠ .scan) :
    Tick (galilFrameS P q first) delay ⟨c, s⟩ ⟨c', t⟩ := by
  cases h
  case init => exact .init _ _ _ ‹_› ‹_›
  case scan_wait => exact absurd ‹c.mode = .scan› hm
  case scan_count => exact absurd ‹c.mode = .scan› hm
  case scan_match => exact absurd ‹c.mode = .scan› hm
  case scan_shift => exact absurd ‹c.mode = .scan› hm
  case scan_fallback => exact absurd ‹c.mode = .scan› hm
  case shift_one => exact .shift_one _ _ _ ‹_› ‹_› ‹_›
  case shift_done => exact .shift_done _ _ _ ‹_› ‹_› ‹_›
  case copy_one => exact .copy_one _ _ _ ‹_› ‹_› ‹_›
  case copy_done => exact .copy_done _ _ _ ‹_› ‹_› ‹_›
  case home_start => exact .home_start _ _ _ ‹_› ‹_› ‹_›
  case home_step => exact .home_step _ _ _ ‹_› ‹_› ‹_›
  case fpp_slice => exact .fpp_slice _ _ _ ‹_› ‹_›
  case fpp_done => exact .fpp_done _ _ _ ‹_› ‹_›
  case markEnd_found => exact .markEnd_found _ _ _ ‹_› ‹_› ‹_›
  case markEnd_step => exact .markEnd_step _ _ _ ‹_› ‹_› ‹_›
  case choose_select => exact .choose_select _ _ _ ‹_› ‹_› ‹_› ‹_›
  case choose_step => exact .choose_step _ _ _ ‹_› ‹_› ‹_›
  case rewind_done => exact .rewind_done _ _ _ ‹_› ‹_› ‹_›
  case rewind_one => exact .rewind_one _ _ _ ‹_› ‹_› ‹_› ‹_›
  case rewind_pair => exact .rewind_pair _ _ _ ‹_› ‹_› ‹_› ‹_›
  case replayStart => exact .replayStart _ _ _ _ ‹_› ‹_› ‹_› ‹_›
  case restart => exact .restart _ _ _ ‹_› ‹_›

/-- The matched comparison of `galilFrame` extended by a search quantum. -/
theorem scan_match_S (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) (c : Control) (s : GalilVM)
    (vs : ScanVM) (vq : SearchVM) (o : Bool) (hm : c.mode = .scan) (hr : c.replaying = false)
    (hav : (galilFrame P q first).available s) (hc : c.clock = 1) (hne : s.chain ≠ .idle)
    (hcmp : (galilFrame P q first).compare s (scanLens.set s vs))
    (hmt : (galilFrame P q first).matched (scanLens.set s vs))
    (hq : searchEffect P true s vq)
    (ho : refresh (galilFrame P q first) (afterCompare s vs vq) c.output o) :
    Tick (galilFrameS P q first) delay ⟨c, s⟩
      ⟨{c with clock := delay, output := o, replaying := false},
        afterCompare s vs vq⟩ := by
  have hcmp0 := hcmp
  obtain ⟨⟨hl0, hr0, ht0⟩, _⟩ := hcmp0
  rw [scanLens.get_set] at hl0 hr0 ht0
  have hl' : vs.left = GalilScaffoldInputHead.left s.left := hl0
  have hr' : vs.right = GalilScaffoldChainVerifier.right s.right := hr0
  have hmatch : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left s.left) =
      GalilScaffoldInputHead.read (GalilScaffoldChainVerifier.right s.right) := by
    have h0 : GalilScaffoldInputHead.read (scanLens.get (scanLens.set s vs)).left =
      GalilScaffoldInputHead.read (scanLens.get (scanLens.set s vs)).right := hmt
    rw [scanLens.get_set] at h0
    have h1 : GalilScaffoldInputHead.read vs.left = GalilScaffoldInputHead.read vs.right := h0
    rw [hl', hr'] at h1
    exact h1
  have ht' : ChainTick (decide (GalilScaffoldInputHead.read (GalilScaffoldInputHead.left s.left) =
      GalilScaffoldInputHead.read (GalilScaffoldChainVerifier.right s.right))) s.chain vs.chain := ht0
  rw [decide_eq_true hmatch] at ht'
  have hcmp' : (galilFrameS P q first).compare s (afterCompare s vs vq) :=
    ⟨vs, vq, true, hl', hr', ⟨fun _ => hmt, fun _ => rfl⟩, hq, Or.inl ⟨hne, ht'⟩, rfl⟩
  have hmt' : (galilFrameS P q first).matched (afterCompare s vs vq) := by
    show (galilFrame P q first).matched (afterCompare s vs vq)
    exact hmt
  have hpl : (galilFrameS P q first).matchedPlace c.replaying (afterCompare s vs vq)
      (afterCompare s vs vq) := by
    show afterCompare s vs vq = (if c.replaying then _ else afterCompare s vs vq)
    rw [hr]; simp
  have ht := Tick.scan_match (F := galilFrameS P q first) (delay := delay) c s _ _ o hm (Or.inr hav) hc
    hcmp' hmt' hpl ho
  rw [hr] at ht
  simpa using ht

/-- The matched comparison with an idle chain whose search does not land in
`found`: the chain stays idle. -/
theorem scan_match_idle_S (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) (c : Control) (s : GalilVM)
    (vs : ScanVM) (vq : SearchVM) (o : Bool) (hm : c.mode = .scan) (hr : c.replaying = false)
    (hav : (galilFrame P q first).available s) (hc : c.clock = 1) (hidle : s.chain = .idle)
    (hl : vs.left = GalilScaffoldInputHead.left s.left)
    (hrr : vs.right = GalilScaffoldChainVerifier.right s.right) (hvs : vs.chain = .idle)
    (hmt : (galilFrame P q first).matched (scanLens.set s vs))
    (hq : searchEffect P true s vq) (hnf : vq.search.mode ≠ .found)
    (ho : refresh (galilFrame P q first) (afterCompare s vs vq) c.output o) :
    Tick (galilFrameS P q first) delay ⟨c, s⟩
      ⟨{c with clock := delay, output := o, replaying := false},
        afterCompare s vs vq⟩ := by
  have hcmp' : (galilFrameS P q first).compare s (afterCompare s vs vq) :=
    ⟨vs, vq, true, hl, hrr, ⟨fun _ => hmt, fun _ => rfl⟩, hq,
      Or.inr (Or.inl ⟨hidle, by simp [hnf], hvs⟩), rfl⟩
  have hmt' : (galilFrameS P q first).matched (afterCompare s vs vq) := by
    show (galilFrame P q first).matched (afterCompare s vs vq)
    exact hmt
  have hpl : (galilFrameS P q first).matchedPlace c.replaying (afterCompare s vs vq)
      (afterCompare s vs vq) := by
    show afterCompare s vs vq = (if c.replaying then _ else afterCompare s vs vq)
    rw [hr]; simp
  have ht := Tick.scan_match (F := galilFrameS P q first) (delay := delay) c s _ _ o hm (Or.inr hav) hc
    hcmp' hmt' hpl ho
  rw [hr] at ht
  simpa using ht

/-- `matchedPlace`'s replay countdown. -/
def replayDec (b : Bool) (s : GalilVM) : GalilVM :=
  if b then {s with replay := GalilScaffoldCounter.dec s.replay} else s

theorem replayDec_false (s : GalilVM) : replayDec false s = s := rfl
theorem replayDec_left (b : Bool) (s : GalilVM) : (replayDec b s).left = s.left := by cases b <;> rfl
theorem replayDec_right (b : Bool) (s : GalilVM) : (replayDec b s).right = s.right := by cases b <;> rfl
theorem replayDec_chain (b : Bool) (s : GalilVM) : (replayDec b s).chain = s.chain := by cases b <;> rfl
theorem replayDec_center (b : Bool) (s : GalilVM) : (replayDec b s).center = s.center := by cases b <;> rfl
theorem replayDec_radius (b : Bool) (s : GalilVM) : (replayDec b s).radius = s.radius := by cases b <;> rfl
theorem replayDec_length (b : Bool) (s : GalilVM) : (replayDec b s).length = s.length := by cases b <;> rfl
theorem replayDec_periodOnly (b : Bool) (s : GalilVM) : (replayDec b s).periodOnly = s.periodOnly := by
  cases b <;> rfl
theorem replayDec_search (b : Bool) (s : GalilVM) : searchLens.get (replayDec b s) = searchLens.get s := by
  cases b <;> rfl
theorem replayDec_cycle (b : Bool) (s : GalilVM) : (replayDec b s).cycle = s.cycle := by cases b <;> rfl
theorem replayDec_remaining (b : Bool) (s : GalilVM) : (replayDec b s).remaining = s.remaining := by
  cases b <;> rfl
theorem replayDec_fpp (b : Bool) (s : GalilVM) : (replayDec b s).fpp = s.fpp := by cases b <;> rfl

theorem matchedPlace_replayDec (P : Shared) (q : ℕ) (first : Fin 9) (b : Bool) (s : GalilVM) :
    (galilFrameS P q first).matchedPlace b s (replayDec b s) := by
  show replayDec b s = (if b then {s with replay := GalilScaffoldCounter.dec s.replay} else s)
  rfl

/-- The matched comparison with an active chain, replaying or not. -/
theorem scan_match_S' (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) (c : Control) (s : GalilVM)
    (vs : ScanVM) (vq : SearchVM) (o : Bool) (hm : c.mode = .scan)
    (hav : c.replaying = true ∨ (galilFrame P q first).available s) (hc : c.clock = 1) (hne : s.chain ≠ .idle)
    (hcmp : (galilFrame P q first).compare s (scanLens.set s vs))
    (hmt : (galilFrame P q first).matched (scanLens.set s vs))
    (hq : searchEffect P true s vq)
    (ho : refresh (galilFrame P q first) (replayDec c.replaying (afterCompare s vs vq)) c.output o) :
    Tick (galilFrameS P q first) delay ⟨c, s⟩
      ⟨{c with clock := delay, output := o, replaying := c.replaying && !P.replayExhausted (replayDec c.replaying (afterCompare s vs vq))}, replayDec c.replaying (afterCompare s vs vq)⟩ := by
  have hcmp0 := hcmp
  obtain ⟨⟨hl0, hr0, ht0⟩, _⟩ := hcmp0
  rw [scanLens.get_set] at hl0 hr0 ht0
  have hl' : vs.left = GalilScaffoldInputHead.left s.left := hl0
  have hr' : vs.right = GalilScaffoldChainVerifier.right s.right := hr0
  have hmatch : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left s.left) =
      GalilScaffoldInputHead.read (GalilScaffoldChainVerifier.right s.right) := by
    have h0 : GalilScaffoldInputHead.read (scanLens.get (scanLens.set s vs)).left =
      GalilScaffoldInputHead.read (scanLens.get (scanLens.set s vs)).right := hmt
    rw [scanLens.get_set] at h0
    have h1 : GalilScaffoldInputHead.read vs.left = GalilScaffoldInputHead.read vs.right := h0
    rw [hl', hr'] at h1
    exact h1
  have ht' : ChainTick (decide (GalilScaffoldInputHead.read (GalilScaffoldInputHead.left s.left) =
      GalilScaffoldInputHead.read (GalilScaffoldChainVerifier.right s.right))) s.chain vs.chain := ht0
  rw [decide_eq_true hmatch] at ht'
  have hcmp' : (galilFrameS P q first).compare s (afterCompare s vs vq) :=
    ⟨vs, vq, true, hl', hr', ⟨fun _ => hmt, fun _ => rfl⟩, hq, Or.inl ⟨hne, ht'⟩, rfl⟩
  have hmt' : (galilFrameS P q first).matched (afterCompare s vs vq) := by
    show (galilFrame P q first).matched (afterCompare s vs vq)
    exact hmt
  exact Tick.scan_match (F := galilFrameS P q first) (delay := delay) c s _ _ o hm hav hc
    hcmp' hmt' (matchedPlace_replayDec P q first _ _) ho

/-- The matched comparison with an idle chain not landing in `found`,
replaying or not. -/
theorem scan_match_idle_S' (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) (c : Control) (s : GalilVM)
    (vs : ScanVM) (vq : SearchVM) (o : Bool) (hm : c.mode = .scan)
    (hav : c.replaying = true ∨ (galilFrame P q first).available s) (hc : c.clock = 1) (hidle : s.chain = .idle)
    (hl : vs.left = GalilScaffoldInputHead.left s.left)
    (hrr : vs.right = GalilScaffoldChainVerifier.right s.right) (hvs : vs.chain = .idle)
    (hmt : (galilFrame P q first).matched (scanLens.set s vs))
    (hq : searchEffect P true s vq) (hnf : vq.search.mode ≠ .found)
    (ho : refresh (galilFrame P q first) (replayDec c.replaying (afterCompare s vs vq)) c.output o) :
    Tick (galilFrameS P q first) delay ⟨c, s⟩
      ⟨{c with clock := delay, output := o, replaying := c.replaying && !P.replayExhausted (replayDec c.replaying (afterCompare s vs vq))}, replayDec c.replaying (afterCompare s vs vq)⟩ := by
  have hcmp' : (galilFrameS P q first).compare s (afterCompare s vs vq) :=
    ⟨vs, vq, true, hl, hrr, ⟨fun _ => hmt, fun _ => rfl⟩, hq,
      Or.inr (Or.inl ⟨hidle, by simp [hnf], hvs⟩), rfl⟩
  have hmt' : (galilFrameS P q first).matched (afterCompare s vs vq) := by
    show (galilFrame P q first).matched (afterCompare s vs vq)
    exact hmt
  exact Tick.scan_match (F := galilFrameS P q first) (delay := delay) c s _ _ o hm hav hc
    hcmp' hmt' (matchedPlace_replayDec P q first _ _) ho

#print axioms tick_S_of_tick
#print axioms chainTick_idle
#print axioms scan_match_S

end PalPeg.GalilScaffoldChainInputSupply
