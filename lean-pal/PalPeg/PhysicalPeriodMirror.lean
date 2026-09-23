import PalPeg.ChainStoredPeriod
import PalPeg.PhysicalWatchEntry

/-!
# The h mirror through watch entry and count sweeps

The source h is supplied by the run invariant, not chosen to fit the period.
Counter 10 can become the boundary spare while mirror 5 retains the positive
semiperiod. Entry and background count preserve the mirror through the actual
sweep. PhysicalCacheInvariant carries these results in the common encoding;
the later shift exchange and rebuilding still require physical transitions.
-/
set_option autoImplicit false
namespace PalPeg.PhysicalPeriodMirror
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract
open PalPeg.PhysicalSpare (Rep)
open PalPeg.PhysicalScanCount PalPeg.PhysicalTickDispatch
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilScaffoldCounter (Counter ofNat)
open PalPeg.GalilScaffoldChainPeriod (Token)
open PalPeg.Local (pos readWin)
open PalPeg.CloseoutCoreEnc12
open PalPeg.LocalStepFusion (idealStep)

noncomputable def mirrorIndex : Fin tapeCountM := slotIndex (mirrorSlot 5)

theorem source (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : PalPeg.MachineStep.sweepClosure blankM (CoreEnc w) x p)
    (hs : PalPeg.ChainStoredPeriod.Stored x.vm.chain)
    (first last : Fin 3) (xs : List (Fin 3)) (h lag credit : Counter)
    (ver : PalPeg.GalilScaffoldInputHead.PlaceHead)
    (hback : x.vm.chain = .back ⟨[], .first first, xs.map Token.plain ++ [.last last]⟩ h lag credit ver) :
    Rep true (ofNat (xs.length + 1)) (p.2 mirrorIndex) := by
  have hlen : h = ofNat (xs.length + 1) := by
    simpa [PalPeg.ChainStoredPeriod.Stored, hback] using hs
  obtain ⟨T, hT, hteq⟩ := he
  have hpositive : PalPeg.GalilScaffoldCounter.positive h = true := by
    rw [hlen]
    simp [PalPeg.GalilScaffoldCounter.positive, ofNat, List.replicate_succ]
  have hp : p.1.polarity 10 = true :=
    ((counterPositive_iff_belowRead (K := macroRadius) hT.1.2 (by decide) (le_refl margin)
      10 h (by simp [counterOf, hback])).mp hpositive).1
  obtain ⟨seg, habs, htape⟩ := hT.1.2.mirrors 5 h (by simp [counterOf, mirrorSource, hback])
  refine ⟨seg, ?_, ?_⟩
  · change PalPeg.LocalCounter.absCtr seg (p.1.polarity 10) = h at habs
    simpa only [hp, hlen] using habs
  · change T mirrorIndex = padLeft margin (mapTape encSeg seg) at htape
    rw [← htape]
    exact hteq mirrorIndex

/-- The single real sweep preserves that mirror observationally, even while
resetting the old h carrier and erasing a retired program cell. -/
theorem entry (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : PalPeg.MachineStep.sweepClosure blankM (CoreEnc w) x p)
    (hs : PalPeg.ChainStoredPeriod.Stored x.vm.chain)
    (first last : Fin 3) (xs : List (Fin 3)) (h lag credit : Counter)
    (ver : PalPeg.GalilScaffoldInputHead.PlaceHead)
    (hback : x.vm.chain = .back ⟨[], .first first, xs.map Token.plain ++ [.last last]⟩ h lag credit ver)
    (input : Option (Fin 2)) :
    Rep true (ofNat (xs.length + 1))
      ((PalPeg.PhysicalWatchEntry.entryStep.apply blankM p input).2 mirrorIndex) := by
  obtain ⟨seg, habs, hrep⟩ := source w x p he hs first last xs h lag credit ver hback
  have hm : ∀ j, macroRadius ≤ pos (p.2 j) :=
    PalPeg.PhysicalContract.running_margin (q := p.1) he
  obtain ⟨_, hstep⟩ := PalPeg.CloseoutCoreEnc12.compStep_apply
    PalPeg.PhysicalWatchEntry.entryRule blankM p input hm
  have hkeep := PalPeg.PhysicalWatchEntry.entry_kept p input hm (mirrorSlot 5)
    (by intro k; cases p.1.fppLive <;> simp [progSlotOf, mirrorSlot])
  have hsame : (idealStep PalPeg.PhysicalWatchEntry.entryRule blankM p input).2 mirrorIndex =
      p.2 mirrorIndex := by
    simpa [PalPeg.PhysicalWatchEntry.nextTapes, PalPeg.PhysicalWatchEntry.resetSlot,
      mirrorSlot, periodSlot, mirrorIndex] using hkeep
  have ht := hstep mirrorIndex
  change TEqG blankM ((idealStep PalPeg.PhysicalWatchEntry.entryRule blankM p input).2 mirrorIndex)
    ((PalPeg.PhysicalWatchEntry.entryStep.apply blankM p input).2 mirrorIndex) at ht
  rw [hsame] at ht
  exact ⟨seg, habs, PalPeg.MachineStep.teqG_trans hrep ht⟩

/-- Entry and its clock update share the same physical output tapes. -/
theorem count_entry (work : PalPeg.PhysicalBootFeed.CoreStep) (w : List (Fin 2))
    (x : State GalilVM) (p : CoreState)
    (he : PalPeg.MachineStep.sweepClosure blankM (CoreEnc w) x p)
    (hs : PalPeg.ChainStoredPeriod.Stored x.vm.chain)
    (first last : Fin 3) (xs : List (Fin 3)) (h lag credit : Counter)
    (ver : PalPeg.GalilScaffoldInputHead.PlaceHead)
    (hback : x.vm.chain = .back ⟨[], .first first, xs.map Token.plain ++ [.last last]⟩ h lag credit ver)
    (hmode : x.ctl.mode = .scan) (hstarved : PalPeg.FrameFunction.starvedTest x = false)
    (hclock : 1 < x.ctl.clock) :
    Rep true (ofNat (xs.length + 1))
      (((PalPeg.PhysicalWatchEntry.withWatchEntry work).apply blankM p none).2 mirrorIndex) := by
  rw [PalPeg.PhysicalWatchEntry.selected_entry _ w x p _ h lag credit ver hback rfl
    he hmode hstarved hclock, counted_apply]
  exact entry w x p he hs first last xs h lag credit ver hback none

/-- Every background scan row keeps the h mirror, for any consume verdict. -/
theorem ideal_scan (rest : RestCommands) (p : CoreState) (hslot : p.1.slot.val = 0)
    (hmode : p.1.ctl.mode = .scan)
    (hphase : scanPhase p.1 (fun j => readWin blankM microRadius (p.2 j)) ≠ .compare) :
    (PalPeg.LocalStepFusion.idealRun (workRule rest) blankM p none 12).2 mirrorIndex = p.2 mirrorIndex := by
  rw [workRule_eq, tickPhysRule_eq, tickRule_otherSlots _ _ _ _ _ p none hslot
    mirrorIndex (by simp [mirrorIndex, mirrorSlot])]
  simp only [ruleActs, hmode]
  rw [scanActs_background _ _ hphase]
  unfold mirrorIndex
  rw [withErase_at_other _ _ _ (mirrorSlot 5)
      (by intro k; cases p.1.fppLive <;> simp [progSlotOf, mirrorSlot])]
  simp [scanConsumeActs, mirrorSlot, counterSlot, periodSlot]

/-- A symbolic rule avoids expanding the twelve concrete view transitions
while identifying a tape preserved by its fused sweep. -/
theorem fused_kept (R : ActRule (Fin 2) CoreControl Γm tapeCountM microRadius) (p : CoreState)
    (hm : ∀ j, macroRadius ≤ pos (p.2 j))
    (hkeep : (PalPeg.LocalStepFusion.idealRun R blankM p none 12).2 mirrorIndex = p.2 mirrorIndex) :
    TEqG blankM (p.2 mirrorIndex)
      (((compStep (PalPeg.LocalStepFusion.iterRule R 12)).apply blankM p none).2 mirrorIndex) := by
  have hsame : (idealStep (PalPeg.LocalStepFusion.iterRule R 12) blankM p none).2 mirrorIndex =
      p.2 mirrorIndex := by
    rw [PalPeg.LocalStepFusion.iterRule_ideal blankM R 12 p none hm,
      PalPeg.LocalStepFusion.idealIter_eq_idealRun]
    exact hkeep
  obtain ⟨_, hstep⟩ := compStep_apply (PalPeg.LocalStepFusion.iterRule R 12) blankM p none hm
  have ht := hstep mirrorIndex
  change TEqG blankM ((idealStep (PalPeg.LocalStepFusion.iterRule R 12) blankM p none).2 mirrorIndex) _ at ht
  rwa [hsame] at ht

/-- The fused twelve-slot sweep preserves the mirror observationally. -/
theorem scan_teq (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : PalPeg.MachineStep.sweepClosure blankM (CoreEnc w) x p)
    (hmode : x.ctl.mode = .scan) (hs : PalPeg.FrameFunction.starvedTest x = false)
    (hclock : 1 < x.ctl.clock) (hnoRestart : restartGuardTest x.vm = false) :
    TEqG blankM (p.2 mirrorIndex) (((workStep rest).apply blankM p none).2 mirrorIndex) := by
  have hm : ∀ j, macroRadius ≤ pos (p.2 j) :=
    PalPeg.PhysicalContract.running_margin (q := p.1) he
  obtain ⟨T, hT, hteq⟩ := he
  have hqmode : p.1.ctl.mode = .scan := by
    have hc := congrArg PalPeg.GalilScaffoldController.Control.mode hT.1.1.ctl
    change p.1.ctl.mode = x.ctl.mode at hc
    exact hc.trans hmode
  have hw : (fun j => readWin blankM microRadius (T j)) =
      (fun j => readWin blankM microRadius (p.2 j)) := by
    funext j
    exact readWin_congr_teqG (K := microRadius) (hteq j)
  have hphaseT : scanPhase p.1 (fun j => readWin blankM microRadius (T j)) ≠ .compare := by
    have hcount := countRead_eq hT.1 (by decide : 1 ≤ microRadius) micro_le_margin
      hmode hs hnoRestart hclock
    have hc := of_decide_eq_true (Bool.and_eq_true_iff.mp hcount).2
    simp only [tapesOf, Equiv.apply_symm_apply] at hc
    rw [hc]
    decide
  have hphase : scanPhase p.1 (fun j => readWin blankM microRadius (p.2 j)) ≠ .compare := by
    rw [← hw]; exact hphaseT
  have hkept := ideal_scan rest p hT.2.1 hqmode hphase
  rewrite [workStep]
  generalize hR : workRule rest = R at hkept ⊢
  exact fused_kept R p hm hkept

/-- Preparing the spare and decrementing the clock do not change mirror 5. -/
theorem count_scan (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : PalPeg.MachineStep.sweepClosure blankM (CoreEnc w) x p)
    (hmode : x.ctl.mode = .scan) (hs : PalPeg.FrameFunction.starvedTest x = false)
    (hclock : 1 < x.ctl.clock) (hnoRestart : restartGuardTest x.vm = false)
    (h : ℕ) (hr : Rep true (ofNat h) (p.2 mirrorIndex)) :
    Rep true (ofNat h) (((PalPeg.PhysicalCountSpare.countStep rest).apply blankM p none).2 mirrorIndex) := by
  rw [PalPeg.PhysicalCountSpare.countStep, PalPeg.PhysicalSpare.overlay_apply, counted_apply]
  have hn : mirrorIndex ≠ PalPeg.PhysicalSpare.spareIndex := by
    simp [mirrorIndex, PalPeg.PhysicalSpare.spareIndex, mirrorSlot, counterSlot]
  simp only [Function.update_of_ne hn]
  obtain ⟨seg, habs, hrep⟩ := hr
  exact ⟨seg, habs, PalPeg.MachineStep.teqG_trans hrep (scan_teq rest w x p he hmode hs hclock hnoRestart)⟩

/-- info: 'PalPeg.PhysicalPeriodMirror.count_scan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms count_scan

end PalPeg.PhysicalPeriodMirror
