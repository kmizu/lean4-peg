import PalPeg.GalilScaffoldTopWatchSegE
import PalPeg.GalilScaffoldTopRestart
import PalPeg.GalilScaffoldTopReadyFound
import PalPeg.GalilScaffoldTopSearch
import PalPeg.GalilRunSkeleton

set_option autoImplicit false

/-!
# `ShapedRun`: runs without `restart` ticks

The oracle never emits a `restart` tick: a broken chain is left broken (`brokenIdle` /
`brokenMatched` always tick), the search stays frozen, and every later mismatch is a fallback.
The final theorem does not need the restart-first discipline of the Scala machine
(`H_realizeLIMW'` is about any sound pre-loaded trace), so the search readiness datum only has
to survive the one re-entry the oracle does use: the fallback's `replayStart`, whose landing is
a fresh restart of radius `0`.  `ShapedSteps` records exactly that about a run.
-/

namespace PalPeg.ShapedRun

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilRunSkeleton
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier

section
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-! ## Restart-free runs

The oracle never emits a `restart` tick: a broken chain is left broken (the ticks
`brokenIdle` / `brokenMatched` exist), the search stays frozen, and every later mismatch is a
fallback.  The final theorem does not need the restart-first discipline of the Scala machine
(`H_realizeLIMW'` is about any sound pre-loaded trace), so the readiness datum only has to
survive the two re-entries the oracle does use: none at `restart`, and the fallback's
`replayStart`, whose landing is a fresh restart of radius `0`. -/

/-- A `restart` leaves a broken chain idle and keeps the radius. -/
theorem restartVM_shape {s t : GalilVM} (h : restartVM entry s t) :
    (∃ w, s.chain = .broken w) ∧ t.chain = .idle ∧ t.radius = s.radius := by
  obtain ⟨w, hs, -, -, -, rfl⟩ := h
  exact ⟨⟨w, hs⟩, rfl, rfl⟩

/-- A broken chain stays broken through a chain tick. -/
theorem chainTick_broken {a : Bool} {w : GalilScaffoldChainWatch.State} {z : ChainVM}
    (h : ChainTick a (.broken w) z) : ∃ w', z = .broken w' := by
  obtain ⟨y, hs, hm⟩ := h
  cases hs
  cases a with
  | false => exact ⟨w, hm⟩
  | true => cases hm; exact ⟨_, rfl⟩

theorem chainAt_broken {a found : Bool} {answer : GalilScaffoldTape.Tape} {cc : Fin 3}
    {walker : GalilScaffoldPlace.Place} {ver : PlaceHead} {radius : Counter}
    {w : GalilScaffoldChainWatch.State} {z : ChainVM}
    (h : chainAt a found answer cc walker ver radius (.broken w) z) : ∃ w', z = .broken w' := by
  rcases h with ⟨-, ht⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · exact chainTick_broken ht
  · cases h0
  · cases h0

/-- A background step is not a `restart`: out of a broken chain it stays broken. -/
theorem not_restartVM_background {w : List (Fin 2)} {s s' : GalilVM}
    (hb : (galilFrameS (PofC centre place entry w) q first).background s s') :
    ¬ restartVM entry s s' := by
  intro hr
  obtain ⟨⟨wb, hs⟩, hidle, -⟩ := restartVM_shape entry hr
  obtain ⟨-, -, hch, -⟩ := backgroundS_fields (PofC centre place entry w) q first hb
  rw [hs] at hch
  obtain ⟨w', hw'⟩ := chainAt_broken hch
  rw [hw'] at hidle; cases hidle

/-- The chain after a comparison is the chain the comparison's chain tick produced. -/
theorem compareFound_chain {w : List (Fin 2)} {s s' : GalilVM}
    (hcmp : (galilFrameS (PofC centre place entry w) q first).compare s s') :
    ∃ (vs : ScanVM) (vq : SearchVM) (a : Bool),
      chainAt a (decide (vq.search.mode = .found)) (vq.dp.config.tapes 11)
        ((PofC centre place entry w).centre s) ((PofC centre place entry w).place s)
        s.center s.radius s.chain vs.chain ∧ s'.chain = vs.chain := by
  obtain ⟨vs, vq, a, -, -, -, -, hch, rfl⟩ := hcmp
  refine ⟨vs, vq, a, hch, ?_⟩
  rw [afterBirth_chain]
  cases a <;> rfl

/-- A comparison (and a replay decrement after it) is not a `restart`. -/
theorem not_restartVM_compare {w : List (Fin 2)} {s s' : GalilVM} (b : Bool)
    (hcmp : (galilFrameS (PofC centre place entry w) q first).compare s s') :
    ¬ restartVM entry s (replayDec b s') := by
  intro hr
  obtain ⟨⟨wb, hs⟩, hidle, -⟩ := restartVM_shape entry hr
  obtain ⟨vs, vq, a, hch, hs'⟩ := compareFound_chain centre place entry q first hcmp
  rw [hs] at hch
  obtain ⟨w', hw'⟩ := chainAt_broken hch
  rw [replayDec_chain, hs', hw'] at hidle; cases hidle

/-- **Runs whose scan-mode ticks are never `restart`s and whose `replayStart` ticks land in a
fresh radius-`0` restart.**  The oracle's own runs have this shape. -/
inductive ShapedSteps (w : List (Fin 2)) : ℕ → State GalilVM → State GalilVM → Prop
  | zero (x : State GalilVM) : ShapedSteps w 0 x x
  | succ {n : ℕ} {x y z : State GalilVM}
      (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y)
      (hnr : x.ctl.mode = .scan → ¬ restartVM entry x.vm y.vm)
      (hrs : x.ctl.mode = .replayStart →
        Restarted w y.vm 0 reset ∧ y.ctl.mode = .scan ∧ y.ctl.clock = 2048)
      (hr : ShapedSteps w n y z) : ShapedSteps w (n+1) x z

theorem shapedSteps_trans {w : List (Fin 2)} {m n : ℕ} {x y z : State GalilVM}
    (h1 : ShapedSteps centre place entry q first w m x y)
    (h2 : ShapedSteps centre place entry q first w n y z) :
    ShapedSteps centre place entry q first w (m + n) x z := by
  induction h1 with
  | zero _ => simpa using h2
  | succ h hnr hrs _ ih => rw [Nat.succ_add]; exact .succ h hnr hrs (ih h2)

theorem shapedSteps_steps {w : List (Fin 2)} {n : ℕ} {x y : State GalilVM}
    (h : ShapedSteps centre place entry q first w n x y) :
    Steps (galilFrameS (PofC centre place entry w) q first) 2048 n x y := by
  induction h with
  | zero _ => exact .zero _
  | succ h _ _ _ ih => exact .succ h ih

/-- A chain-idle-or-not `WatchSegE` segment is a shaped run: all its ticks are scan-mode
background steps and comparisons. -/
theorem watchSegE_shaped {w : List (Fin 2)} {es : List Bool} {c c' : Control} {s t : GalilVM}
    (h : WatchSegE (PofC centre place entry w) q first 2048 es c s c' t) :
    ∃ k, ShapedSteps centre place entry q first w k ⟨c, s⟩ ⟨c', t⟩ := by
  induction h with
  | stop c s => exact ⟨0, .zero _⟩
  | wait c s s' hm hr hn hb _ ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + 1, .succ (Tick.scan_wait c s s' hm ⟨hr, hn⟩ hb)
      (fun _ => not_restartVM_background centre place entry q first hb)
      (fun h0 => absurd (hm.symm.trans h0) (by decide)) hk⟩
  | count c s s' hm hr ha hc hb _ ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + 1, .succ (Tick.scan_count c s s' hm (Or.inr ha) hc hb)
      (fun _ => not_restartVM_background centre place entry q first hb)
      (fun h0 => absurd (hm.symm.trans h0) (by decide)) hk⟩
  | «match» c s vs vq o hm hr ha hc hne hcmp hmt hq ho _ ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨k + 1, .succ (scan_match_S (PofC centre place entry w) q first 2048 c s vs vq o hm hr ha
      hc hne hcmp hmt hq ho) (fun _ hrs => ?_) (fun h0 => absurd (hm.symm.trans h0) (by decide)) hk⟩
    obtain ⟨⟨wb, hs⟩, hidle, -⟩ := restartVM_shape entry hrs
    obtain ⟨⟨-, -, ht⟩, -⟩ := hcmp
    rw [scanLens.get_set] at ht
    have ht' : ChainTick _ s.chain vs.chain := ht
    rw [hs] at ht'
    obtain ⟨w', hw'⟩ := chainTick_broken ht'
    have h2 : vs.chain = ChainVM.idle := hidle
    rw [hw'] at h2; cases h2
  | matchIdle c s vs vq o hm hr ha hc hidle hl hrr hvs hmt hq hnf ho _ ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨k + 1, .succ (scan_match_idle_S (PofC centre place entry w) q first 2048 c s vs vq o hm hr
      ha hc hidle hl hrr hvs hmt hq hnf ho) (fun _ hrs => ?_)
      (fun h0 => absurd (hm.symm.trans h0) (by decide)) hk⟩
    obtain ⟨⟨wb, hs⟩, -, -⟩ := restartVM_shape entry hrs
    rw [hidle] at hs; cases hs
  | countR c s s' hm hr hc hidle hb _ ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨k + 1, .succ (Tick.scan_count c s s' hm (Or.inl hr) hc hb) (fun _ hrs => ?_)
      (fun h0 => absurd (hm.symm.trans h0) (by decide)) hk⟩
    obtain ⟨⟨wb, hs⟩, -, -⟩ := restartVM_shape entry hrs
    rw [hidle] at hs; cases hs
  | matchIdleR c s vs vq o hm hr hc ha hidle hl hrr hvs hmt hq hnf ho _ ih =>
    obtain ⟨k, hk⟩ := ih
    have ht := scan_match_idle_S' (PofC centre place entry w) q first 2048 c s vs vq o hm (Or.inl hr)
      hc hidle hl hrr hvs hmt hq hnf (by rw [hr]; exact ho)
    rw [hr] at ht
    refine ⟨k + 1, .succ (by simpa using ht) (fun _ hrs => ?_)
      (fun h0 => absurd (hm.symm.trans h0) (by decide)) hk⟩
    obtain ⟨⟨wb, hs⟩, -, -⟩ := restartVM_shape entry hrs
    rw [hidle] at hs; cases hs

#print axioms watchSegE_shaped

end

end PalPeg.ShapedRun
