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

end

end PalPeg.OracleReady
