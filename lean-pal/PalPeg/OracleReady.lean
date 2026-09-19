import PalPeg.CloseoutPreload39
import PalPeg.BranchSupply
import PalPeg.GalilInvPlus3
import PalPeg.OracleRun
import PalPeg.ShapedRun
import PalPeg.ReadyTransport

set_option autoImplicit false

/-!
# `OracleReady`: the search readiness leaf of the run-shaped cycle oracle

`OracleRun.cycleOracleOn_of_fourLeaves` takes `hready`: the search co-process is ready at
every chain-idle scan state of a *shaped* run (`ShapedRun.ShapedSteps`: no `restart`, every
`replayStart` lands in a fresh radius-`0` restart) out of an `InvLPS` origin.  This file
discharges it from the readiness datum `CloseoutPreload39.ReadyFieldP3`, which
`ReadyTransport.readyField3_of_invLPS_shaped` carries from the fresh restart the origin's
`ReplayStage` records along the whole shaped run.  What is left is one atomic, state-local fact:

* `hfresh` — the datum at a fresh restart (`Restarted ∧ StageEntry`, scan mode, full clock):
  the calibration of the concrete DP against the stage budget.
-/

namespace PalPeg.OracleReady

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilRunSkeleton PalPeg.CloseoutPreload39
  PalPeg.CloseoutReadyStage PalPeg.GalilInvPlus3 PalPeg.GalilFoundStage PalPeg.GalilOracleLocal
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
  PalPeg.GalilStructuredSkeleton PalPeg.GalilTraceCost PalPeg.ShapedRun PalPeg.ReadyTransport

section
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **Search readiness at every scan state of a shaped run out of an `InvLPS` origin**, from
`hfresh` alone. -/
theorem searchReady_of_invLPS_shaped {w : List (Fin 2)}
    (hfresh : ∀ (c : Control) (r : GalilVM) (Rad : ℕ) (last : Counter),
      Restarted w r Rad last → StageEntry Rad last → c.mode = .scan → c.clock = 2048 →
      ∃ n, ReadyFieldP3 n ⟨c, r⟩)
    {c₀ : Control} {r₀ : GalilVM} (hI₀ : InvLPS (PofC centre place entry w) q first w c₀ r₀)
    {k : ℕ} {y : State GalilVM} (hsh : ShapedSteps centre place entry q first w k ⟨c₀, r₀⟩ y)
    (hm : y.ctl.mode = .scan) : PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get y.vm) := by
  obtain ⟨n, hn⟩ := readyField3_of_invLPS_shaped centre place entry q first hfresh hI₀ hsh
  exact readyField3_to_ready hn (Or.inl hm)

/-- **The run-shaped cycle oracle from the atomic leaves**: `hready` of
`OracleRun.cycleOracleOn_of_fourLeaves` is `searchReady_of_invLPS_shaped`. -/
theorem cycleOracleOn_of_readyLeaves {w : List (Fin 2)} (hP : Decodes (PofC centre place entry w))
    (h4 : first ≠ 4)
    (hfresh : ∀ (c : Control) (r : GalilVM) (Rad : ℕ) (last : Counter),
      Restarted w r Rad last → StageEntry Rad last → c.mode = .scan → c.clock = 2048 →
      ∃ n, ReadyFieldP3 n ⟨c, r⟩)
    (hchain : ∀ (c₀ : Control) (r₀ : GalilVM) (k : ℕ) (y : State GalilVM),
      InvLPS (PofC centre place entry w) q first w c₀ r₀ →
      ShapedSteps centre place entry q first w k ⟨c₀, r₀⟩ y →
      PalPeg.GalilTickFun.ChainReady y.vm.chain)
    (hminv : ∀ (c₀ : Control) (r₀ : GalilVM) (k : ℕ) (y : State GalilVM),
      InvLPS (PofC centre place entry w) q first w c₀ r₀ →
      ShapedSteps centre place entry q first w k ⟨c₀, r₀⟩ y →
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
        ShapedSteps centre place entry q first w (fb + replay)
          ⟨{c with clock := 2048, mode := .copy}, u⟩ ⟨c', s'⟩ ∧
        c'.mode = .scan ∧ c'.replaying = false ∧
        Refreshed (PofC centre place entry w) q first ⟨c', s'⟩ ∧
        position s'.right = position s.right + 1 ∧ r ≤ kk ∧
        position s'.center = position s.center + (kk + 1 - r) ∧
        fb ≤ 12704 * (kk + 1 - r) + 4012 ∧ replay ≤ 8 * 2048 * (kk + 1 - r)) :
    PalPeg.CloseoutCheckW.CycleOracleOn centre place entry q first
      (PalPeg.CloseoutCheckW.ScanOnPackedRunFromInvLPS centre place entry q first) w :=
  PalPeg.OracleRun.cycleOracleOn_of_fourLeaves centre place entry q first hP h4
    (fun c₀ r₀ k y hI₀ hsh hm _ =>
      searchReady_of_invLPS_shaped centre place entry q first hfresh hI₀ hsh hm)
    hchain hminv hfallback

#print axioms cycleOracleOn_of_readyLeaves
#print axioms searchReady_of_invLPS_shaped


end

end PalPeg.OracleReady
