import PalPeg.PhysicalDpCleanupDispatch
import PalPeg.PhysicalDpPreload

/-! Start cleanup from the live DP representation in the shared source Enc.
This supplies the retirement side of a future reset row; that row must still
prove its ordinary transition and that the next live bank is ready. -/
set_option autoImplicit false
namespace PalPeg.PhysicalDpRetirement
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract
open PalPeg.PhysicalDpCleanup (Phases Enc wrap)
open PalPeg.PhysicalShiftDispatch (RoutedCore RoutedStep liftConfig)
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.Program PalPeg.CloseoutCoreEnc12

/-- The current live program tapes are represented even while search counters
are replaced by snapshots or the radius mirror is being rebuilt. -/
theorem live (w : List (Fin 2)) (x : State GalilVM) (p : RoutedCore)
    (he : PalPeg.PhysicalLoanInvariant.Enc w x (liftConfig p)) (i : Fin 12) :
    TEqG blankM (padLeft margin (mapTape encProg (encTape (x.vm.dp.config.tapes i))))
      (p.2 (p.1.1 (slotIndex (dpSlotOf p.1.2.dpLive i)))) := by
  by_cases hn : PalPeg.PhysicalLoanInvariant.NeedsLoan x
  · obtain ⟨_,T,hT,ht⟩ := (PalPeg.PhysicalLoanInvariant.enc_partial w x _ hn).mp he
    have hd := hT.1.1.1.1.2.dp i
    have hd' : T (slotIndex (dpSlotOf p.1.2.dpLive i)) =
        padLeft margin (mapTape encProg (encTape (x.vm.dp.config.tapes i))) := by
      cases hb : p.1.2.dpLive <;>
        simpa [PalPeg.PhysicalDebtMirror.repaired,PalPeg.PhysicalDebtMirror.repair,
          dpSlotOf,mirrorSlot,hb] using hd
    have hh := ht (slotIndex (dpSlotOf p.1.2.dpLive i))
    rw [hd'] at hh
    exact hh
  · obtain ⟨⟨y,hy,T,hT,ht⟩,_⟩ := (PalPeg.PhysicalLoanInvariant.enc_full w x _ hn).mp he
    have hs := hy.2.1
    unfold PalPeg.PhysicalRestartStorage.Same at hs
    have hd : y.vm.dp = x.vm.dp := by
      simpa only [PalPeg.PhysicalRestartStorage.replace] using congrArg GalilVM.dp hs
    have hdT : T (slotIndex (dpSlotOf p.1.2.dpLive i)) =
        padLeft margin (mapTape encProg (encTape (y.vm.dp.config.tapes i))) := hT.1.1.1.2.dp i
    have hh := ht (slotIndex (dpSlotOf p.1.2.dpLive i))
    rw [hdT,hd] at hh
    exact hh

/-- A reset's bank flip chooses the old live tapes as the new retired bank.
The source TEq is obtained here, not required as an independent hypothesis. -/
theorem forward_dense (L : RoutedStep) (w : List (Fin 2)) (x y : State GalilVM)
    (source target : RoutedCore) (phases : Phases) (a : Option (Fin 2))
    (hx : Enc w x (((liftConfig source).1,phases),source.2))
    (hy : PalPeg.PhysicalLoanInvariant.Enc w y (liftConfig target))
    (hstep : L.apply blankM (liftConfig source) a = liftConfig target)
    (hflip : source.1.2.dpLive ≠ target.1.2.dpLive)
    (hroles : ∀ bank i, target.1.1 (slotIndex (dpSlotOf bank i)) =
      source.1.1 (slotIndex (dpSlotOf bank i)))
    (hd : ∀ i, PalPeg.PhysicalProgramErase.Dense (encTape (x.vm.dp.config.tapes i))) :
    Enc w y ((wrap L).apply blankM (((liftConfig source).1,phases),source.2) a) := by
  apply PalPeg.PhysicalDpCleanup.forward_retired L w x y source target phases a
    (fun i => encTape (x.vm.dp.config.tapes i)) hx hy hstep hflip hd
  have hb : (!target.1.2.dpLive) = source.1.2.dpLive := by
    cases hs : source.1.2.dpLive <;> cases ht : target.1.2.dpLive <;> simp_all
  intro i
  rw [hroles,hb]
  exact live w x source hx.1 i

/-- Actual partial preparation supplies density when retirement interrupts
lower, lowerHome, copy, or home. Waiting ticks are allowed in that history. -/
theorem forward_preparing (L : RoutedStep) (w : List (Fin 2)) (x y : State GalilVM)
    (source target : RoutedCore) (phases : Phases) (a : Option (Fin 2))
    (hx : Enc w x (((liftConfig source).1,phases),source.2))
    (hy : PalPeg.PhysicalLoanInvariant.Enc w y (liftConfig target))
    (hstep : L.apply blankM (liftConfig source) a = liftConfig target)
    (hflip : source.1.2.dpLive ≠ target.1.2.dpLive)
    (hroles : ∀ bank i, target.1.1 (slotIndex (dpSlotOf bank i)) =
      source.1.1 (slotIndex (dpSlotOf bank i)))
    (s t : PalPeg.GalilScaffoldPrepareControl.State) (lower : PalPeg.GalilScaffoldCounter.Counter)
    (center : PalPeg.GalilScaffoldPlace.Place) (bs : List Bool)
    (hr : PalPeg.GalilScaffoldPrepareControl.Run
      (PalPeg.GalilScaffoldPrepareControl.prepare s lower center) bs t)
    (hp : x.vm.dp = t.program) :
    Enc w y ((wrap L).apply blankM (((liftConfig source).1,phases),source.2) a) := by
  apply forward_dense L w x y source target phases a hx hy hstep hflip hroles
  rw [hp]
  exact PalPeg.PhysicalDpPreload.dense_onRun s lower center hr

/-- Executing, paused and halted DP runs supply the same retirement contract. -/
theorem forward_program (L : RoutedStep) (w : List (Fin 2)) (x y : State GalilVM)
    (source target : RoutedCore) (phases : Phases) (a : Option (Fin 2))
    (hx : Enc w x (((liftConfig source).1,phases),source.2))
    (hy : PalPeg.PhysicalLoanInvariant.Enc w y (liftConfig target))
    (hstep : L.apply blankM (liftConfig source) a = liftConfig target)
    (hflip : source.1.2.dpLive ≠ target.1.2.dpLive)
    (hroles : ∀ bank i, target.1.1 (slotIndex (dpSlotOf bank i)) =
      source.1.1 (slotIndex (dpSlotOf bank i)))
    (word : List (Fin 3)) (lower : ℕ) (bs : List Bool)
    (hr : PalPeg.GalilScaffoldControl.Run PalPeg.GalilDpCode.code
      ⟨PalPeg.GalilScaffoldPreload.initial word lower,false⟩ bs x.vm.dp) :
    Enc w y ((wrap L).apply blankM (((liftConfig source).1,phases),source.2) a) :=
  forward_dense L w x y source target phases a hx hy hstep hflip hroles
    (PalPeg.PhysicalDpDensity.dense_onRun word lower hr)

/-- info: 'PalPeg.PhysicalDpRetirement.live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms live

/-- info: 'PalPeg.PhysicalDpRetirement.forward_preparing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forward_preparing

/-- info: 'PalPeg.PhysicalDpRetirement.forward_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forward_program

end PalPeg.PhysicalDpRetirement
