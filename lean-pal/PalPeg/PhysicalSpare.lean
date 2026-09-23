import PalPeg.PhysicalFreeCounter
import PalPeg.PhysicalCounterCache
import PalPeg.PhysicalBootFeed

/-!
# Preparing the boundary spare in the same physical step

`overlay` replaces only logical counter slot 10 and its polarity in an existing
core step. It uses the same source windows, same radius and same sweep. The
frame theorem proves that every other represented component survives. Selection
of this overlay and maintenance of its source invariant are dispatcher work.
-/
set_option autoImplicit false
namespace PalPeg.PhysicalSpare
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract PalPeg.PhysicalFreeCounter
open PalPeg.PhysicalBootFeed (CoreStep)
open PalPeg.PhysicalCounterCache (increments increments_length increments_encode)
open PalPeg.ChainBoundaryCache (rate rate_le advanceCounter)
open PalPeg.GalilScaffoldCounter (Counter)
open PalPeg.LocalCounter (Seg absCtr)
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.Local PalPeg.Program
open PalPeg.CloseoutCoreEnc12

noncomputable def spareIndex : Fin tapeCountM := slotIndex (counterSlot 10)

/-- The spare may be a real sweep tape, with arbitrary extra trailing blanks. -/
def Rep (bit : Bool) (spare : Counter) (tape : STape Γm) : Prop :=
  ∃ seg : STape Seg, absCtr seg bit = spare ∧
    TEqG blankM (padLeft margin (mapTape encSeg seg)) tape

theorem Rep.margin {bit : Bool} {spare : Counter} {tape : STape Γm}
    (h : Rep bit spare tape) : margin ≤ pos tape := by
  obtain ⟨seg, _, he⟩ := h
  rw [← he.1, pos_padLeft]
  omega

noncomputable def compiled (q : CoreControl) (ws : Fin tapeCountM → Window Γm macroRadius) :=
  increments (rate q.chainPhase) (q.polarity 10) (ws spareIndex)

noncomputable def rule : ActRule (Fin 2) CoreControl Γm tapeCountM macroRadius where
  nq := fun q _ ws => setPolarity q 10 (compiled q ws).1
  acts := fun q _ ws j => if j = spareIndex then (compiled q ws).2 else []
  len_le := by
    intro q input ws j
    split
    · exact (by rw [compiled, increments_length]; exact Nat.le_trans (rate_le _) (by decide))
    · simp

noncomputable def step : CoreStep := compStep rule

/-- Each physical tape uses exactly one of the two local outputs, never two
sequential ticks. Control takes the base result plus the spare's new sign. -/
noncomputable def overlay (base : CoreStep) : CoreStep where
  next := fun q input ws =>
    let result := base.next q input ws
    let spare := step.next q input ws
    (setPolarity result.1 10 (spare.1.polarity 10),
      Function.update result.2 spareIndex (spare.2 spareIndex))
  disp_le := by
    intro q input ws j
    by_cases he : j = spareIndex
    · subst j
      simpa only [Function.update_self] using step.disp_le q input ws spareIndex
    · simpa only [Function.update_of_ne he] using base.disp_le q input ws j

theorem overlay_apply (base : CoreStep) (p : CoreState) (input : Option (Fin 2)) :
    (overlay base).apply blankM p input =
      (setPolarity (base.apply blankM p input).1 10 ((step.apply blankM p input).1.polarity 10),
        Function.update (base.apply blankM p input).2 spareIndex
          ((step.apply blankM p input).2 spareIndex)) := by
  apply Prod.ext
  · rfl
  · funext j
    by_cases he : j = spareIndex
    · subst j
      simp only [LocalStep.apply, overlay, Function.update_self]
    · simp only [LocalStep.apply, overlay, Function.update_of_ne he]

/-- Action lists preserve the tape equivalence used by the sweep. -/
theorem actList_teq {Γ : Type} (blank : Γ) {T U : STape Γ} (he : TEqG blank T U)
    (acts : List (Act Γ)) : TEqG blank (actList blank T acts) (actList blank U acts) := by
  have hread : rd blank T = rd blank U := funext he.2
  have hs : (rd blank T, pos T) = (rd blank U, pos U) := Prod.ext hread he.1
  have hr := congrArg (fun c => runA c acts) hs
  rw [runA_eq, runA_eq] at hr
  exact ⟨congrArg Prod.snd hr, fun j => congrFun (congrArg Prod.fst hr) j⟩

/-- The actual spare sweep represents the bounded counter update. The source
representation supplies its own margin; no other tape is read for this proof. -/
theorem step_spare (p : CoreState) (spare : Counter)
    (hrep : Rep (p.1.polarity 10) spare (p.2 spareIndex)) (input : Option (Fin 2)) :
    Rep ((step.apply blankM p input).1.polarity 10)
      (advanceCounter (rate p.1.chainPhase) spare)
      ((step.apply blankM p input).2 spareIndex) := by
  obtain ⟨seg, habs, hteq⟩ := hrep
  let ws := fun j => readWin blankM macroRadius (p.2 j)
  have hw : ws spareIndex = readWin blankM macroRadius (padLeft margin (mapTape encSeg seg)) :=
    (PalPeg.PhysicalEncoding.readWin_congr_teqG hteq).symm
  have hcompiled : compiled p.1 ws = increments (rate p.1.chainPhase) (p.1.polarity 10)
      (readWin blankM macroRadius (padLeft margin (mapTape encSeg seg))) := by
    unfold compiled
    rw [hw]
  obtain ⟨result, hresult, hacts⟩ := increments_encode (rate p.1.chainPhase)
    (Nat.le_trans (rate_le _) (by decide : 3 ≤ macroRadius)) (le_refl margin)
    (p.1.polarity 10) seg seg spare habs habs
  have hbit : (step.apply blankM p input).1.polarity 10 = (compiled p.1 ws).1 := by
    simp only [step, LocalStep.apply, compStep, rule, setPolarity, Function.update_self]
    rfl
  refine ⟨result, ?_, ?_⟩
  · rw [hbit, hcompiled]
    exact hresult
  · have hlist : actList blankM (padLeft margin (mapTape encSeg seg)) (compiled p.1 ws).2 =
        padLeft margin (mapTape encSeg result) := by rw [hcompiled]; exact hacts
    rw [← hlist]
    apply PalPeg.MachineStep.teqG_trans (actList_teq blankM hteq _)
    have hm : macroRadius ≤ pos (p.2 spareIndex) := by
      change margin ≤ _
      rw [← hteq.1, pos_padLeft]
      omega
    have hsweep := teq_sweep_actList blankM macroRadius (p.2 spareIndex)
      (compiled p.1 ws).2 (by rw [compiled, increments_length]; exact Nat.le_trans (rate_le _) (by decide)) hm
    simpa only [step, LocalStep.apply, compStep, rule, if_true] using hsweep

/-- Merge an already proved VM step with spare preparation. The target has no
logical counter in slot 10, so its encoded value is free to serve as the spare. -/
theorem overlay_preserves (base : CoreStep) (w : List (Fin 2)) (y : State GalilVM)
    (p : CoreState) (spare : Counter) (input : Option (Fin 2))
    (hbase : PalPeg.MachineStep.sweepClosure blankM (CoreEnc w) y (base.apply blankM p input))
    (hfree : counterOf y 10 = none)
    (hrep : Rep (p.1.polarity 10) spare (p.2 spareIndex)) :
    PalPeg.MachineStep.sweepClosure blankM (CoreEnc w) y ((overlay base).apply blankM p input) ∧
      Rep (((overlay base).apply blankM p input).1.polarity 10)
        (advanceCounter (rate p.1.chainPhase) spare)
        (((overlay base).apply blankM p input).2 spareIndex) := by
  have hs := step_spare p spare hrep input
  rw [overlay_apply]
  constructor
  · exact running_free_counter hbase 10 hfree _ _ hs.margin
  · simpa only [setPolarity, Function.update_self] using hs

/-- info: 'PalPeg.PhysicalSpare.overlay_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms overlay_preserves

end PalPeg.PhysicalSpare
