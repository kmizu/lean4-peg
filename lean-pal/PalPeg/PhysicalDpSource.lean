import PalPeg.PhysicalDpRetirement
import PalPeg.PhysicalDpHistory
import PalPeg.PhysicalContract

/-!
# The retired DP bank is dense on the final consumer's run

On the tracked part the DP history is carried along the canonical trace from
boot; truncating the not-yet-arrived input does not touch the search. After
the last report the plateau invariant carries the same history. No density
premise remains in the retirement contract of a reset row.
-/
set_option autoImplicit false
namespace PalPeg.PhysicalDpSource
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilFinalAssembly2 (centreC placeC)
open PalPeg.CloseoutCheckW (PreTraceIMW CanonTrace)
open PalPeg.LocalSysConcrete (absSC)
open PalPeg.LocalReplayParked (Mirrored1)
open PalPeg.LocalShadowConcrete (OnRun)
open PalPeg.LocalBlankState (tapeCount)
open PalPeg.ShadowedLocalFinal (localGood postPhase frozenAt heldAfter)
open PalPeg.PhysicalEncoding (encTape)
open PalPeg.PhysicalProgramErase (Dense)
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract

theorem dense_onRun (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ)
    (hpre : PreTraceIMW centreC placeC 0 1 0 w st Tc) (hcanonTrace : CanonTrace 0 w st Tc)
    (m : Mirrored1 (tapeCount 0))
    (hon : OnRun (localGood (spare := 0)) (postPhase 0 1 0) w
      (heldAfter (Tc w.length) st) m) (hnotFrozen : ¬ frozenAt w m) :
    ∀ i, Dense (encTape ((absSC m).vm.dp.config.tapes i)) := by
  rcases hon with htracked | ⟨hpost, _, _, _⟩
  · obtain ⟨k, j, _, hsource⟩ := htracked.track
    have hb := PalPeg.PhysicalDpHistory.dpHistory_alongTrace centreC placeC 0 1 0
      (PalPeg.GalilFinalAssembly2.decodesC 0 w) hpre.base.pre hcanonTrace
      (min k (Tc w.length)) (Nat.min_le_right _ _)
    change ∀ i, Dense (encTape ((PalPeg.LocalReplayParked.absState'' m.vm).vm.dp.config.tapes i))
    rw [hsource]
    exact hb.2.dense
  · rcases hpost with hplateau | hfrozen
    · exact hplateau.dpDense.dense
    · exact (hnotFrozen hfrozen).elim

/-- A reset's bank flip on the run: the retired live tapes are dense without
any further premise. The reset row itself (`hy`, `hstep`, `hflip`, `hroles`)
is still to be implemented. -/
theorem forward_onRun (L : PalPeg.PhysicalShiftDispatch.RoutedStep) (w : List (Fin 2))
    (st : ℕ → State GalilVM) (Tc : ℕ → ℕ)
    (hpre : PreTraceIMW centreC placeC 0 1 0 w st Tc) (hcanonTrace : CanonTrace 0 w st Tc)
    (m : Mirrored1 (tapeCount 0))
    (hon : OnRun (localGood (spare := 0)) (postPhase 0 1 0) w
      (heldAfter (Tc w.length) st) m) (hnotFrozen : ¬ frozenAt w m)
    (y : State GalilVM) (source target : PalPeg.PhysicalShiftDispatch.RoutedCore)
    (phases : PalPeg.PhysicalDpCleanup.Phases) (a : Option (Fin 2))
    (hx : PalPeg.PhysicalDpCleanup.Enc w (absSC m)
      (((PalPeg.PhysicalShiftDispatch.liftConfig source).1,phases),source.2))
    (hy : PalPeg.PhysicalLoanInvariant.Enc w y (PalPeg.PhysicalShiftDispatch.liftConfig target))
    (hstep : L.apply PalPeg.PhysicalEncoding.blankM (PalPeg.PhysicalShiftDispatch.liftConfig source) a =
      PalPeg.PhysicalShiftDispatch.liftConfig target)
    (hflip : source.1.2.dpLive ≠ target.1.2.dpLive)
    (hroles : ∀ bank i, target.1.1 (slotIndex
        (dpSlotOf bank i)) =
      source.1.1 (slotIndex (dpSlotOf bank i))) :
    PalPeg.PhysicalDpCleanup.Enc w y
      ((PalPeg.PhysicalDpCleanup.wrap L).apply PalPeg.PhysicalEncoding.blankM
        (((PalPeg.PhysicalShiftDispatch.liftConfig source).1,phases),source.2) a) :=
  PalPeg.PhysicalDpRetirement.forward_dense L w (absSC m) y source target phases a hx hy hstep
    hflip hroles (dense_onRun w st Tc hpre hcanonTrace m hon hnotFrozen)

/-- info: 'PalPeg.PhysicalDpSource.dense_onRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dense_onRun

/-- info: 'PalPeg.PhysicalDpSource.forward_onRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forward_onRun

end PalPeg.PhysicalDpSource
