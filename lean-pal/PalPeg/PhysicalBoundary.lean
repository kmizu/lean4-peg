import PalPeg.PhysicalContract

/-!
# The boundary of a physical macro tick

Consumers: the boot/feed/tick preservation proofs for `PhysicalContract.CoreEnc`.
Every represented head, including the idle verifier, finishes the eleven-slot
view job with zero work owed; the twelfth micro step returns the slot to zero.
The fusion bridge below retains these facts under the real write sweep.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.PhysicalBoundary
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.LocalStepFusion
open PalPeg.CloseoutCoreEnc12 (ActRule compStep)
open PalPeg.Program (STape)

/-- `EncTapes` supplies a view even for the currently unnamed verifier. -/
theorem all_heads_represented {padding : ℕ} {x : State GalilVM}
    {polarity : Fin 16 → Bool} {gap : Fin 4 → Bool}
    {micro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl}
    {fppLive dpLive : Bool} {T : Slot → STape Γm}
    (h : EncTapes padding x polarity gap micro fppLive dpLive T) (v : Fin 4) :
    HeadSlotsRep padding gap micro T v := by
  cases hhead : headOf x v with
  | some head =>
    obtain ⟨view, viewTapes, _, hrep, hslots, hcells, hwf⟩ := h.heads v head hhead
    exact ⟨view, viewTapes, hrep, hslots, hcells, hwf⟩
  | none =>
    have hv : v = 3 := by
      fin_cases v <;> simp_all [headOf]
    subst v
    exact h.idleHead hhead

/-- All mode rows share this boundary theorem; no branch-specific readiness
assumption is needed just to finish the queue job. -/
theorem macroBoundary_of_heads
    (base commandsOf baseActs)
    (baseLen : ∀ q i ws j, (baseActs q i ws j).length ≤ microRadius)
    (p : CoreState) (input : Option (Fin 2)) (hboundary : MacroBoundary p.1)
    (hviews : ∀ v, HeadSlotsRep margin p.1.gap p.1.micro
      (fun slot => p.2 (slotIndex slot)) v) :
    MacroBoundary (idealRun
      (tickRule (by decide : 2 ≤ microRadius) base commandsOf baseActs baseLen)
      blankM p input 12).1 := by
  let R := tickRule (by decide : 2 ≤ microRadius) base commandsOf baseActs baseLen
  change MacroBoundary (idealRun R blankM p input 12).1
  generalize hrun : idealRun R blankM p input = run
  have hzero : run 0 = p := by rw [← hrun]; rfl
  have hlast : run 12 = idealStep R blankM (run 11) none := by
    rw [← hrun]
    rfl
  have hslot : (run 11).1.slot.val = 11 := by
    rw [← hrun]
    exact slot_idealRun R p input hboundary.1
      (tickRule_advance (by decide) base commandsOf baseActs baseLen) 11 (by omega)
  have hwrap : ∀ q i ws, q.slot.val = 11 → (R.nq q i ws).slot.val = 0 := by
    intro q i ws hslotLast
    change (if q.slot.val = 0 then _ else _ : CoreControl).slot.val = 0
    rw [if_neg (by omega)]
    change (slotAdvance q.slot).val = 0
    simp [slotAdvance, hslotLast]
  constructor
  · rw [hlast]
    exact hwrap (run 11).1 none _ hslot
  · intro v
    obtain ⟨view, viewTapes, hrep, hslots, hcells, hwf⟩ :=
      hviews v
    exact Fin.ext ((headTick_of_tickRule (by decide : 2 ≤ microRadius) micro_le_margin
      base commandsOf baseActs baseLen v p input hboundary.1
      (fun step => (run step).1)
      (fun step slot => (run step).2 (slotIndex slot))
      (fun step => by rw [hrun]) (fun step slot => by rw [hrun])
      view hwf hcells viewTapes (by rw [hzero]; exact hslots)
      (by rw [hzero]; exact hrep) (by rw [hzero]; exact hboundary.2 v)).2.1)

/-- The running encoding supplies every head premise of the boundary theorem. -/
theorem macroBoundary_tickRule
    (base commandsOf baseActs)
    (baseLen : ∀ q i ws j, (baseActs q i ws j).length ≤ microRadius)
    (w : List (Fin 2)) (x : State GalilVM) (p : CoreState) (input : Option (Fin 2))
    (henc : CoreEnc w x p) :
    MacroBoundary (idealRun
      (tickRule (by decide : 2 ≤ microRadius) base commandsOf baseActs baseLen)
      blankM p input 12).1 :=
  macroBoundary_of_heads base commandsOf baseActs baseLen p input henc.2
    (all_heads_represented henc.1.2)

/-- Transport a mode's full twelve-step preservation theorem through fusion and
the write sweep. The premise concerns the exact encoding, including its boundary;
the result concerns the running encoding accepted by the final consumer. -/
theorem running_fused_step
    (R : ActRule (Fin 2) CoreControl Γm tapeCountM microRadius)
    (w : List (Fin 2)) (x y : State GalilVM) (p : CoreState) (input : Option (Fin 2))
    (henc : PalPeg.MachineStep.sweepClosure blankM (CoreEnc w) x p)
    (hstep : ∀ ideal, CoreEnc w x (p.1, ideal) →
      CoreEnc w y (idealRun R blankM (p.1, ideal) input 12)) :
    PalPeg.MachineStep.sweepClosure blankM (CoreEnc w) y
      ((compStep (iterRule R 12)).apply blankM p input) := by
  obtain ⟨ideal, hexact, hteq⟩ := henc
  have hidealMargin : ∀ tape, macroRadius ≤ PalPeg.Local.pos (ideal tape) := by
    intro tape
    have h := hexact.1.2.margins (slotIndex.symm tape)
    simpa only [Equiv.apply_symm_apply, margin] using h
  have hmargin : ∀ tape, macroRadius ≤ PalPeg.Local.pos (p.2 tape) := by
    intro tape
    rw [← (hteq tape).1]
    exact hidealMargin tape
  obtain ⟨hcontrol, htapes⟩ := idealStep_congr_teqG (iterRule R 12) blankM
    p.1 ideal p.2 hteq input
  rw [iterRule_ideal blankM R 12 (p.1, ideal) input hidealMargin,
    idealIter_eq_idealRun] at hcontrol htapes
  obtain ⟨hrealControl, hrealTapes⟩ :=
    PalPeg.CloseoutCoreEnc12.compStep_apply (iterRule R 12) blankM p input hmargin
  refine ⟨(idealRun R blankM (p.1, ideal) input 12).2, ?_, fun tape =>
    PalPeg.MachineStep.teqG_trans (htapes tape) (hrealTapes tape)⟩
  rw [hrealControl]
  change CoreEnc w y ((idealStep (iterRule R 12) blankM (p.1, p.2) input).1, _)
  rw [← hcontrol]
  exact hstep ideal hexact

/-- info: 'PalPeg.PhysicalBoundary.macroBoundary_tickRule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms macroBoundary_tickRule

/-- info: 'PalPeg.PhysicalBoundary.running_fused_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms running_fused_step

end PalPeg.PhysicalBoundary
