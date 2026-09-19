import PalPeg.CloseoutPreload39
import PalPeg.BranchSupply
import PalPeg.GalilInvPlus3
import PalPeg.OracleRun

set_option autoImplicit false

/-!
# `OracleReady`: the search readiness leaf of the run-shaped cycle oracle

`OracleRun.cycleOracleOn_of_fourLeaves` takes `hready`: the search co-process is ready at
every chain-idle scan state of a run out of an `InvLPS` origin.  This file discharges it from
the readiness datum `CloseoutPreload39.ReadyFieldP3` (readiness now, plus readiness along every
paced future), which `readyField3_tick` transports across every tick except the two
re-entries of a fresh search.  What is left are three atomic, state-local facts:

* `hfresh` — the datum at a fresh restart (`Restarted ∧ StageEntry`, scan mode, full clock):
  the calibration of the concrete DP against the stage budget;
* `hrestart` — the datum after a `restart` tick reached from such an origin;
* `hreplayStart` — the datum after a `replayStart` tick reached from such an origin.

The `InvLPS` origin itself is reached from a fresh restart along the `WatchSegE` segment its
`ReplayStage` records, so its datum is `hfresh` transported.
-/

namespace PalPeg.OracleReady

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilRunSkeleton PalPeg.CloseoutPreload39
  PalPeg.CloseoutReadyStage PalPeg.GalilInvPlus3 PalPeg.GalilFoundStage PalPeg.GalilOracleLocal
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
  PalPeg.GalilStructuredSkeleton PalPeg.GalilTraceCost

section
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- The datum is monotone in its fuel: a larger fuel asks only about longer futures. -/
theorem readyField3_mono {n n' : ℕ} {x : State GalilVM} (hn : n ≤ n') (h : ReadyFieldP3 n x) :
    ReadyFieldP3 n' x :=
  ⟨h.ready, h.readyS, fun hm hi => readyPacedS_mono hn le_rfl (h.paced hm hi),
    fun hm => readyPacedS_mono hn le_rfl (h.paced0 hm),
    fun hm => readyPacedS_mono hn le_rfl (h.shifting hm)⟩

/-- A `WatchSegE` segment starts in `scan` mode whenever it ends there. -/
theorem watchSegE_first_mode {P : Shared} {es : List Bool} {c c' : Control} {s t : GalilVM}
    (h : WatchSegE P q first 2048 es c s c' t) (hm' : c'.mode = .scan) : c.mode = .scan := by
  cases h <;> first | exact hm' | assumption

/-- **The datum along every run out of a fresh restart.**  The two re-entry leaves are stated
for the ticks reached from that restart. -/
theorem readyField3_alongRun {w : List (Fin 2)}
    (hrestart : ∀ (c : Control) (r : GalilVM) (Rad : ℕ) (last : Counter) (k : ℕ)
      (z z' : State GalilVM),
      Restarted w r Rad last → StageEntry Rad last → c.mode = .scan → c.clock = 2048 →
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 k ⟨c, r⟩ z →
      Tick (galilFrameS (PofC centre place entry w) q first) 2048 z z' →
      z.ctl.mode = .scan → restartVM entry z.vm z'.vm → ∃ n, ReadyFieldP3 n z')
    (hreplayStart : ∀ (c : Control) (r : GalilVM) (Rad : ℕ) (last : Counter) (k : ℕ)
      (z z' : State GalilVM),
      Restarted w r Rad last → StageEntry Rad last → c.mode = .scan → c.clock = 2048 →
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 k ⟨c, r⟩ z →
      Tick (galilFrameS (PofC centre place entry w) q first) 2048 z z' →
      z.ctl.mode = .replayStart → ∃ n, ReadyFieldP3 n z')
    {c : Control} {r : GalilVM} {Rad : ℕ} {last : Counter}
    (hR : Restarted w r Rad last) (hSE : StageEntry Rad last) (hm : c.mode = .scan)
    (hclk : c.clock = 2048) :
    ∀ (k j : ℕ) (x y : State GalilVM),
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 j ⟨c, r⟩ x →
      x.ctl.mode ≠ .init → (∃ n, ReadyFieldP3 n x) →
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 k x y →
      ∃ n, ReadyFieldP3 n y := by
  classical
  intro k
  induction k with
  | zero =>
    intro j x y _ _ hx h
    cases h
    exact hx
  | succ k ih =>
    intro j x y hjx hni hx h
    obtain ⟨y₁, ht, hrest⟩ : ∃ y₁, Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y₁ ∧
        Steps (galilFrameS (PofC centre place entry w) q first) 2048 k y₁ y := by
      cases h with
      | succ ht hrest => exact ⟨_, ht, hrest⟩
    obtain ⟨n, hn⟩ := hx
    -- the fuel after the tick: enlarged at a re-entry, kept otherwise
    have key : ∃ n', n ≤ n' ∧
        (x.ctl.mode = .scan → restartVM entry x.vm y₁.vm → ReadyFieldP3 n' y₁) ∧
        (x.ctl.mode = .replayStart → ReadyFieldP3 n' y₁) := by
      by_cases h1 : x.ctl.mode = .scan ∧ restartVM entry x.vm y₁.vm
      · obtain ⟨m, hm'⟩ := hrestart c r Rad last j x y₁ hR hSE hm hclk hjx ht h1.1 h1.2
        exact ⟨max n m, le_max_left _ _, fun _ _ => readyField3_mono (le_max_right _ _) hm',
          fun h2 => absurd (h1.1.symm.trans h2) (by decide)⟩
      · by_cases h2 : x.ctl.mode = .replayStart
        · obtain ⟨m, hm'⟩ := hreplayStart c r Rad last j x y₁ hR hSE hm hclk hjx ht h2
          exact ⟨max n m, le_max_left _ _, fun h3 _ => absurd (h2.symm.trans h3) (by decide),
            fun _ => readyField3_mono (le_max_right _ _) hm'⟩
        · exact ⟨n, le_rfl, fun h3 h4 => absurd ⟨h3, h4⟩ h1, fun h3 => absurd h3 h2⟩
    obtain ⟨n', hnn', hentry, hentry'⟩ := key
    have hy₁ : ReadyFieldP3 n' y₁ :=
      readyField3_tick centre place entry q first hni hn hnn' ht hentry hentry'
    exact ih (j + 1) y₁ y (steps_trans hjx (.succ ht (.zero _)))
      (PalPeg.BranchSupply.tick_target_mode_ne_init ht) ⟨n', hy₁⟩ hrest

/-- **The datum at every state reachable from an `InvLPS` origin.**  The origin's own datum is
`hfresh` at the fresh restart its `ReplayStage` records, transported along the recorded
`WatchSegE` segment. -/
theorem readyField3_of_invLPS_steps {w : List (Fin 2)}
    (hfresh : ∀ (c : Control) (r : GalilVM) (Rad : ℕ) (last : Counter),
      Restarted w r Rad last → StageEntry Rad last → c.mode = .scan → c.clock = 2048 →
      ∃ n, ReadyFieldP3 n ⟨c, r⟩)
    (hrestart : ∀ (c : Control) (r : GalilVM) (Rad : ℕ) (last : Counter) (k : ℕ)
      (z z' : State GalilVM),
      Restarted w r Rad last → StageEntry Rad last → c.mode = .scan → c.clock = 2048 →
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 k ⟨c, r⟩ z →
      Tick (galilFrameS (PofC centre place entry w) q first) 2048 z z' →
      z.ctl.mode = .scan → restartVM entry z.vm z'.vm → ∃ n, ReadyFieldP3 n z')
    (hreplayStart : ∀ (c : Control) (r : GalilVM) (Rad : ℕ) (last : Counter) (k : ℕ)
      (z z' : State GalilVM),
      Restarted w r Rad last → StageEntry Rad last → c.mode = .scan → c.clock = 2048 →
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 k ⟨c, r⟩ z →
      Tick (galilFrameS (PofC centre place entry w) q first) 2048 z z' →
      z.ctl.mode = .replayStart → ∃ n, ReadyFieldP3 n z')
    {c₀ : Control} {r₀ : GalilVM} (hI₀ : InvLPS (PofC centre place entry w) q first w c₀ r₀)
    {k : ℕ} {y : State GalilVM}
    (hjy : Steps (galilFrameS (PofC centre place entry w) q first) 2048 k ⟨c₀, r₀⟩ y) :
    ∃ n, ReadyFieldP3 n y := by
  obtain ⟨r, Rad, last, es, c, hR, hSE, hclk, hseg⟩ := hI₀.2
  have hm₀ : c₀.mode = .scan := (invS_mode hI₀.1.1.1.1.1).1
  have hm : c.mode = .scan := watchSegE_first_mode q first hseg hm₀
  obtain ⟨j, hst⟩ := watchSegE_steps _ q first 2048 hseg
  have horig : ∃ n, ReadyFieldP3 n ⟨c₀, r₀⟩ :=
    readyField3_alongRun centre place entry q first hrestart hreplayStart hR hSE hm hclk
      j 0 ⟨c, r⟩ ⟨c₀, r₀⟩ (.zero _) (by rw [hm]; decide) (hfresh c r Rad last hR hSE hm hclk) hst
  exact readyField3_alongRun centre place entry q first hrestart hreplayStart hR hSE hm hclk
    k j ⟨c₀, r₀⟩ y hst (by rw [hm₀]; decide) horig hjy

/-- **The readiness leaf.**  At every scan state of a run out of an `InvLPS` origin the search
co-process is ready (whatever the chain does; the oracle asks only while it is idle). -/
theorem searchReady_of_invLPS_steps {w : List (Fin 2)}
    (hfresh : ∀ (c : Control) (r : GalilVM) (Rad : ℕ) (last : Counter),
      Restarted w r Rad last → StageEntry Rad last → c.mode = .scan → c.clock = 2048 →
      ∃ n, ReadyFieldP3 n ⟨c, r⟩)
    (hrestart : ∀ (c : Control) (r : GalilVM) (Rad : ℕ) (last : Counter) (k : ℕ)
      (z z' : State GalilVM),
      Restarted w r Rad last → StageEntry Rad last → c.mode = .scan → c.clock = 2048 →
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 k ⟨c, r⟩ z →
      Tick (galilFrameS (PofC centre place entry w) q first) 2048 z z' →
      z.ctl.mode = .scan → restartVM entry z.vm z'.vm → ∃ n, ReadyFieldP3 n z')
    (hreplayStart : ∀ (c : Control) (r : GalilVM) (Rad : ℕ) (last : Counter) (k : ℕ)
      (z z' : State GalilVM),
      Restarted w r Rad last → StageEntry Rad last → c.mode = .scan → c.clock = 2048 →
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 k ⟨c, r⟩ z →
      Tick (galilFrameS (PofC centre place entry w) q first) 2048 z z' →
      z.ctl.mode = .replayStart → ∃ n, ReadyFieldP3 n z')
    {c₀ : Control} {r₀ : GalilVM} (hI₀ : InvLPS (PofC centre place entry w) q first w c₀ r₀)
    {k : ℕ} {y : State GalilVM}
    (hjy : Steps (galilFrameS (PofC centre place entry w) q first) 2048 k ⟨c₀, r₀⟩ y)
    (hm : y.ctl.mode = .scan) : PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get y.vm) := by
  obtain ⟨n, hn⟩ := readyField3_of_invLPS_steps centre place entry q first hfresh hrestart
    hreplayStart hI₀ hjy
  exact readyField3_to_ready hn (Or.inl hm)

/-- **The run-shaped cycle oracle from the atomic readiness leaves**: `hready` of
`OracleRun.cycleOracleOn_of_fourLeaves` is `searchReady_of_invLPS_steps`. -/
theorem cycleOracleOn_of_readyLeaves {w : List (Fin 2)} (hP : Decodes (PofC centre place entry w))
    (h4 : first ≠ 4)
    (hfresh : ∀ (c : Control) (r : GalilVM) (Rad : ℕ) (last : Counter),
      Restarted w r Rad last → StageEntry Rad last → c.mode = .scan → c.clock = 2048 →
      ∃ n, ReadyFieldP3 n ⟨c, r⟩)
    (hrestart : ∀ (c : Control) (r : GalilVM) (Rad : ℕ) (last : Counter) (k : ℕ)
      (z z' : State GalilVM),
      Restarted w r Rad last → StageEntry Rad last → c.mode = .scan → c.clock = 2048 →
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 k ⟨c, r⟩ z →
      Tick (galilFrameS (PofC centre place entry w) q first) 2048 z z' →
      z.ctl.mode = .scan → restartVM entry z.vm z'.vm → ∃ n, ReadyFieldP3 n z')
    (hreplayStart : ∀ (c : Control) (r : GalilVM) (Rad : ℕ) (last : Counter) (k : ℕ)
      (z z' : State GalilVM),
      Restarted w r Rad last → StageEntry Rad last → c.mode = .scan → c.clock = 2048 →
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 k ⟨c, r⟩ z →
      Tick (galilFrameS (PofC centre place entry w) q first) 2048 z z' →
      z.ctl.mode = .replayStart → ∃ n, ReadyFieldP3 n z')
    (hchain : ∀ (c₀ : Control) (r₀ : GalilVM) (k : ℕ) (y : State GalilVM),
      InvLPS (PofC centre place entry w) q first w c₀ r₀ →
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 k ⟨c₀, r₀⟩ y →
      PalPeg.GalilTickFun.ChainReady y.vm.chain)
    (hminv : ∀ (c₀ : Control) (r₀ : GalilVM) (k : ℕ) (y : State GalilVM),
      InvLPS (PofC centre place entry w) q first w c₀ r₀ →
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 k ⟨c₀, r₀⟩ y →
      MInv w y.ctl y.vm)
    (hfallback : ∀ (c₀ : Control) (r₀ : GalilVM) (k : ℕ) (c : Control) (s : GalilVM) (vq : SearchVM)
      (z : ChainVM) (u : GalilVM) (m : ℕ), 1 ≤ m → m ≤ w.length →
      InvLPS (PofC centre place entry w) q first w c₀ r₀ →
      PalPeg.CloseoutCheckW.StepsIMW centre place entry q first w k ⟨c₀, r₀⟩ ⟨c, s⟩ →
      c.mode = .scan → c.replaying = false → c.clock = 1 → position s.right + 1 ≤ 2 * m - 1 →
      GalilScaffoldInputHead.read (GalilScaffoldInputHead.left s.left) ≠
        GalilScaffoldInputHead.read (GalilScaffoldChainVerifier.right s.right) →
      searchEffect (PofC centre place entry w) false s vq →
      chainAt false (decide (vq.search.mode = .found)) (vq.dp.config.tapes 11)
        ((PofC centre place entry w).centre s) ((PofC centre place entry w).place s)
        s.center s.radius s.chain z →
      ¬ (PofC centre place entry w).shiftGuard
        (afterBirth (chainBorn (decide (vq.search.mode = .found)) s.chain)
          (afterMismatch s ⟨GalilScaffoldInputHead.left s.left,
            GalilScaffoldChainVerifier.right s.right, z⟩ vq)) →
      (PofC centre place entry w).beginFallback
        (afterBirth (chainBorn (decide (vq.search.mode = .found)) s.chain)
          (afterMismatch s ⟨GalilScaffoldInputHead.left s.left,
            GalilScaffoldChainVerifier.right s.right, z⟩ vq)) u →
      Tick (galilFrameS (PofC centre place entry w) q first) 2048 ⟨c, s⟩
        ⟨{c with clock := 2048, mode := .copy}, u⟩ →
      ∃ (c' : Control) (s' : GalilVM) (kk r fb replay : ℕ),
        StepsAll (galilFrameS (PofC centre place entry w) q first) 2048 (SoundScanNR w)
          (fb + replay) ⟨{c with clock := 2048, mode := .copy}, u⟩ ⟨c', s'⟩ ∧
        c'.mode = .scan ∧ c'.replaying = false ∧
        Refreshed (PofC centre place entry w) q first ⟨c', s'⟩ ∧
        position s'.right = position s.right + 1 ∧ r ≤ kk ∧
        position s'.center = position s.center + (kk + 1 - r) ∧
        fb ≤ 12704 * (kk + 1 - r) + 4012 ∧ replay ≤ 8 * 2048 * (kk + 1 - r)) :
    PalPeg.CloseoutCheckW.CycleOracleOn centre place entry q first
      (PalPeg.CloseoutCheckW.ScanOnPackedRunFromInvLPS centre place entry q first) w :=
  PalPeg.OracleRun.cycleOracleOn_of_fourLeaves centre place entry q first hP h4
    (fun c₀ r₀ k y hI₀ hjy hm _ =>
      searchReady_of_invLPS_steps centre place entry q first hfresh hrestart hreplayStart hI₀ hjy hm)
    hchain hminv hfallback

#print axioms cycleOracleOn_of_readyLeaves

#print axioms readyField3_alongRun
#print axioms readyField3_of_invLPS_steps
#print axioms searchReady_of_invLPS_steps

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

/-- **The datum along a shaped run, from `hfresh` alone.** -/
theorem readyField3_alongShaped {w : List (Fin 2)}
    (hfresh : ∀ (c : Control) (r : GalilVM) (Rad : ℕ) (last : Counter),
      Restarted w r Rad last → StageEntry Rad last → c.mode = .scan → c.clock = 2048 →
      ∃ n, ReadyFieldP3 n ⟨c, r⟩)
    {k : ℕ} {x y : State GalilVM} (h : ShapedSteps centre place entry q first w k x y)
    (hni : x.ctl.mode ≠ .init) (hx : ∃ n, ReadyFieldP3 n x) : ∃ n, ReadyFieldP3 n y := by
  classical
  induction h with
  | zero _ => exact hx
  | @succ _ x y z ht hnr hrs _ ih =>
    obtain ⟨n, hn⟩ := hx
    have key : ∃ n', n ≤ n' ∧
        (x.ctl.mode = .scan → restartVM entry x.vm y.vm → ReadyFieldP3 n' y) ∧
        (x.ctl.mode = .replayStart → ReadyFieldP3 n' y) := by
      by_cases h2 : x.ctl.mode = .replayStart
      · obtain ⟨hR, hm, hclk⟩ := hrs h2
        obtain ⟨m, hm'⟩ := hfresh y.ctl y.vm 0 reset hR (stageEntry_zero _) hm hclk
        exact ⟨max n m, le_max_left _ _, fun h3 _ => absurd (h2.symm.trans h3) (by decide),
          fun _ => readyField3_mono (le_max_right _ _) hm'⟩
      · exact ⟨n, le_rfl, fun h3 h4 => absurd h4 (hnr h3), fun h3 => absurd h3 h2⟩
    obtain ⟨n', hnn', hentry, hentry'⟩ := key
    exact ih (PalPeg.BranchSupply.tick_target_mode_ne_init ht)
      ⟨n', readyField3_tick centre place entry q first hni hn hnn' ht hentry hentry'⟩

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
#print axioms readyField3_alongShaped

end

end PalPeg.OracleReady
