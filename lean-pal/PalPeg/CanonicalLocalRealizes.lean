import PalPeg.GalilTickFair
import PalPeg.ShapedRun

/-!
# Canonical ticks at the partially arrived input frontier

The oracle runs on preloaded input, whereas the local machine sees a truncated
state.  Preserve the canonical scheduling predicate under that truncation before
using canonical determinism to identify a local successor with the trace.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace PalPeg.CanonicalLocalRealizes

open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
open PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilRunSkeleton
open PalPeg.GalilThrottledRun PalPeg.GalilTickFair PalPeg.ShapedRun

variable {centre : GalilVM → Fin 3} {place : GalilVM → GalilScaffoldPlace.Place}
  {entry q delay : ℕ} {first : Fin 9} {raw : List (Fin 2)}

theorem broken_of_truncChain {d : ℕ} {chain : ChainVM}
    {watch : GalilScaffoldChainWatch.State} (h : truncChain d chain = .broken watch) :
    ∃ original, chain = .broken original := by
  cases chain <;> simp_all [truncChain]

/-- Truncation preserves the chosen scheduling policy on an actual tick. -/
theorem canonical_trunc {x y : State GalilVM}
    (hTick : Tick (galilFrameS (PofC centre place entry raw) q first) delay x y)
    (hCanonical : Canonical entry delay x y) (d : ℕ) :
    Canonical entry delay (truncS d x) (truncS d y) := by
  refine ⟨?_, hCanonical.fallbackPlace, hCanonical.keepsSearchCursor⟩
  intro hScan hRestart
  obtain ⟨c, s⟩ := x
  have hScan' : c.mode = .scan := hScan
  obtain ⟨⟨watch, hBroken⟩, hIdle, hRadius⟩ := restartVM_shape entry hRestart
  obtain ⟨original, hOriginal⟩ := broken_of_truncChain hBroken
  have hBackgroundNotIdle : ∀ t,
      (galilFrameS (PofC centre place entry raw) q first).background s t →
      truncChain d t.chain ≠ .idle := by
    intro t hBackground hTargetIdle
    obtain ⟨_, _, hChain, _⟩ := backgroundS_fields (PofC centre place entry raw) q first hBackground
    rw [hOriginal] at hChain
    obtain ⟨next, hNext⟩ := chainAt_broken hChain
    rw [hNext] at hTargetIdle
    cases hTargetIdle
  rcases tick_scan_cases hScan' hTick with
    ⟨t, hReplay, hUnavailable, hBackground, hTarget⟩ |
    ⟨t, hEnabled, hClock, hBackground, hTarget⟩ |
    ⟨u, hEnabled, hClock, hCompare, hExit⟩ |
    ⟨t, hRestartOriginal, hTarget⟩
  · rw [hTarget] at hIdle
    change truncChain d t.chain = .idle at hIdle
    exact hBackgroundNotIdle t hBackground hIdle
  · rw [hTarget] at hIdle
    change truncChain d t.chain = .idle at hIdle
    exact hBackgroundNotIdle t hBackground hIdle
  · obtain ⟨vs, vq, a, hChain, hComparedChain⟩ :=
      compareFound_chain centre place entry q first hCompare
    rw [hOriginal] at hChain
    obtain ⟨next, hNext⟩ := chainAt_broken hChain
    have hComparedBroken : u.chain = .broken next := hComparedChain.trans hNext
    rcases hExit with ⟨t, output, hMatched, hPlace, hRefresh, hTarget⟩ |
      ⟨t, hMismatch, hReplay, hGuard, hShift, hTarget⟩ |
      ⟨t, hMismatch, hReplay, hGuard, hFallback, hTarget⟩
    · have hPlace' : t = replayDec c.replaying u := hPlace
      rw [hTarget] at hIdle
      change truncChain d t.chain = .idle at hIdle
      rw [hPlace', replayDec_chain, hComparedBroken] at hIdle
      cases hIdle
    · obtain ⟨shiftWatch, hWatch, _⟩ := hShift
      rw [hComparedBroken] at hWatch
      cases hWatch
    · obtain ⟨fallbackPlace, hFallbackTarget, _⟩ := hFallback
      obtain ⟨restartWatch, _, _, _, _, hRestartTarget⟩ := hRestart
      have hMode := congrArg (fun vm : GalilVM => vm.search.mode) hRestartTarget
      rw [hTarget] at hMode
      change t.search.mode = .grow at hMode
      rw [hFallbackTarget] at hMode
      cases hMode
  · exact hCanonical.noRestart hScan' (by rw [hTarget]; exact hRestartOriginal)

open PalPeg.LocalReplayParked (Mirrored1 absState'' MirInv1)
open PalPeg.LocalSysConcrete (InvC Starved PhysWF Realizes)

/-- Canonical determinism supplies the successor-identification obligation for
any local mode.  The remaining premise is the actual local step and its physical
invariants, not functionality of the unrefined nondeterministic relation. -/
theorem realizes_canonical {P : ℕ} {stOf : ℕ → State GalilVM}
    {f : Mirrored1 P → Mirrored1 P} {mode : Mode}
    (hShared : ∀ j, PalPeg.GalilTruncTick.SharedTrunc raw j (PofC centre place entry raw))
    (hTrace : ∀ k, Tick (galilFrameS (PofC centre place entry raw) q first) delay
      (stOf k) (stOf (k+1)))
    (hCanonical : ∀ k, Canonical entry delay (stOf k) (stOf (k+1)))
    (hLocal : ∀ (m : Mirrored1 P) (target : State GalilVM), InvC raw stOf m →
      m.vm.ctl.mode = mode → ¬ Starved m.vm →
      Tick (galilFrameS (PofC centre place entry raw) q first) delay (absState'' m.vm) target →
      Tick (galilFrameS (PofC centre place entry raw) q first) delay
        (absState'' m.vm) (absState'' (f m).vm) ∧
      Canonical entry delay (absState'' m.vm) (absState'' (f m).vm) ∧
      PhysWF (f m).vm ∧ MirInv1 (f m)) : Realizes raw stOf f mode := by
  apply PalPeg.LocalRealizesScan.realizes_of_refined_tick_det hShared hTrace
    (Canonical entry delay) (fun k j _ => canonical_trunc (hTrace k) (hCanonical k) _) hLocal
  intro source target₁ target₂ _ hTick₁ hCanonical₁ hTick₂ hCanonical₂
  exact tick_canonical_unique hTick₁ hCanonical₁ hTick₂ hCanonical₂

#print axioms realizes_canonical

#print axioms canonical_trunc

end PalPeg.CanonicalLocalRealizes
