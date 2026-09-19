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

/-- The restart guard reads only the chain counters, which truncation keeps. -/
theorem restartGuard_of_trunc {d : ℕ} {s : GalilVM}
    (h : PalPeg.GalilScaffoldChainInputSupply.restartGuardVM (truncVM d s)) :
    PalPeg.GalilScaffoldChainInputSupply.restartGuardVM s := by
  obtain ⟨watch, hBroken, hMargin, hLast, hLag⟩ := h
  obtain ⟨original, hOriginal⟩ := broken_of_truncChain (chain := s.chain) hBroken
  have hw : watch = truncW d original := by
    have h1 : truncChain d s.chain = .broken watch := hBroken
    rw [hOriginal] at h1
    exact (ChainVM.broken.inj h1).symm
  subst hw
  exact ⟨original, hOriginal, hMargin, hLast, hLag⟩

/-- A restart commutes with truncation. -/
theorem restartVM_trunc {d : ℕ} {s t : GalilVM} (h : restartVM entry s t) :
    restartVM entry (truncVM d s) (truncVM d t) := by
  obtain ⟨w, hs, hm, hl, hz, rfl⟩ := h
  refine ⟨truncW d w, ?_, hm, hl, hz, ?_⟩
  · show truncChain d s.chain = _
    rw [hs]; rfl
  · simp [truncVM, truncChain, truncW]

/-- Truncation preserves the chosen scheduling policy on an actual tick. -/
theorem canonical_trunc {x y : State GalilVM}
    (hCanonical : Canonical entry delay x y) (d : ℕ) :
    Canonical entry delay (truncS d x) (truncS d y) := by
  refine ⟨?_, hCanonical.fallbackPlace, hCanonical.keepsSearchCursor⟩
  intro hScan hGuard
  obtain ⟨hCtl, hRestart⟩ := hCanonical.restartFirst hScan (restartGuard_of_trunc hGuard)
  exact ⟨hCtl, restartVM_trunc hRestart⟩

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
    (Canonical entry delay) (fun k j _ => canonical_trunc (hCanonical k) _) hLocal
  intro source target₁ target₂ _ hTick₁ hCanonical₁ hTick₂ hCanonical₂
  exact tick_canonical_unique hTick₁ hCanonical₁ hTick₂ hCanonical₂

#print axioms realizes_canonical

#print axioms canonical_trunc

end PalPeg.CanonicalLocalRealizes
