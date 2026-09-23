import PalPeg.PhysicalSnapshotEntryDispatch

/-! # Handing the three saved last values to restart's search counters

The old chain is retired in this nonhead stage. Three finite swaps give lower,
work and lower's mirror their independent last copies; the old lower and its
mirror are reset concurrently to become span and its mirror. Debt and DP are
left for the remaining stages of the same restart tick.
-/
set_option autoImplicit false
namespace PalPeg.PhysicalRestartCopies
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract
open PalPeg.PhysicalSearchSnapshots (saved put)
open PalPeg.PhysicalCacheInvariant (CoreInv Running)
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilScaffoldCounter (Counter reset)
open PalPeg.Program PalPeg.Local PalPeg.CloseoutCoreEnc12 PalPeg.LocalStepFusion
open PalPeg.LocalCounter (Seg absCtr resetSeg)
open PalPeg.LocalRoleFusion (logicalStep)

/-- A genuine intermediate state: restart's lower/span/work are installed,
while the old debt and DP bank still need their own concrete updates. -/
def prepared (x : State GalilVM) (last : Counter) : State GalilVM :=
  ⟨{x.ctl with clock := 2048}, {x.vm with chain := .idle, lower := last, search := {x.vm.search with mode := .grow, span := reset, work := last, finalStage := false, quarter := 0}}⟩

def slots : Equiv.Perm Slot :=
  ((Equiv.swap (counterSlot 5) (counterSlot 6)).trans
    (Equiv.swap (counterSlot 7) (counterSlot 15))).trans
    (Equiv.swap (mirrorSlot 3) (mirrorSlot 4))

noncomputable def roles : PalPeg.PhysicalRoles.Roles := (slotIndex.symm.trans slots).trans slotIndex

def polarity (bits : Fin 16 → Bool) (c : Fin 16) : Bool :=
  if c = 5 then bits 6 else if c = 6 then true else if c = 7 then bits 15
  else if c = 15 then bits 7 else bits c

def nextControl (q : CoreControl) : CoreControl :=
  {q with ctl := {q.ctl with clock := 2048}, chainTag := .idle, chainPhase := 0, chainForward := false, chainBroken := false, searchMode := .grow, searchFinalStage := false, searchQuarter := 0, polarity := polarity q.polarity}

noncomputable def resets (slot : Slot) : Bool := by
  classical
  exact decide (slot = counterSlot 5 ∨ slot = mirrorSlot 3)

noncomputable def changed (T : Slot → STape Γm) (slot : Slot) : STape Γm :=
  if resets slot then (T slot).applyAction blankM (encSeg PalPeg.LocalCounter.sep, .right) else T slot

noncomputable def output (T : Slot → STape Γm) (slot : Slot) : STape Γm := changed T (slots slot)

@[simp] theorem slots_counter (c : Fin 16) :
    slots (counterSlot c) = if c = 5 then counterSlot 6 else if c = 6 then counterSlot 5
      else if c = 7 then counterSlot 15 else if c = 15 then counterSlot 7 else counterSlot c := by
  fin_cases c <;> simp [slots, Equiv.swap_apply_def, counterSlot, mirrorSlot]

@[simp] theorem slots_mirror (m : Fin 7) :
    slots (mirrorSlot m) = if m = 3 then mirrorSlot 4 else if m = 4 then mirrorSlot 3 else mirrorSlot m := by
  fin_cases m <;> simp [slots, Equiv.swap_apply_def, counterSlot, mirrorSlot]

theorem output_counter (T : Slot → STape Γm) (c : Fin 16) :
    output T (counterSlot c) = if c = 5 then T (counterSlot 6)
      else if c = 6 then (T (counterSlot 5)).applyAction blankM (encSeg PalPeg.LocalCounter.sep, .right)
      else if c = 7 then T (counterSlot 15) else if c = 15 then T (counterSlot 7) else T (counterSlot c) := by
  fin_cases c <;> simp [output, changed, resets, counterSlot, mirrorSlot]

theorem output_mirror (T : Slot → STape Γm) (m : Fin 7) :
    output T (mirrorSlot m) = if m = 3 then T (mirrorSlot 4)
      else if m = 4 then (T (mirrorSlot 3)).applyAction blankM (encSeg PalPeg.LocalCounter.sep, .right)
      else T (mirrorSlot m) := by
  fin_cases m <;> simp [output, changed, resets, counterSlot, mirrorSlot]

theorem output_other (T : Slot → STape Γm) (slot : Slot)
    (hcounter : ∀ c, slot ≠ counterSlot c) (hmirror : ∀ m, slot ≠ mirrorSlot m) :
    output T slot = T slot := by
  simp [output, changed, resets, slots, Equiv.swap_apply_def, hcounter, hmirror]

theorem control_prepared (w : List (Fin 2)) (x : State GalilVM) (q : CoreControl) (last : Counter)
    (henc : EncControl w x q) : EncControl w (prepared x last) (nextControl q) := by
  refine {henc with ctl := ?_, chainTag := rfl, chainPhase := rfl, chainForward := rfl, chainBroken := rfl, searchMode := rfl, searchFinalStage := rfl, searchQuarter := rfl, placeGap := ?_}
  · change {ctlAbs q.ctl with clock := 2048} = {x.ctl with clock := 2048}
    rw [henc.ctl]
  · intro i place hp
    fin_cases i
    · exact henc.placeGap 0 place hp
    · exact henc.placeGap 1 place hp
    · cases hp

theorem tapes_prepared (w : List (Fin 2)) (x : State GalilVM) (q : CoreControl) (T : Slot → STape Γm)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .broken wm)
    (hlast : x.vm.search.span = wm.machine.control.last)
    (henc : EncTapes margin x q.polarity q.gap q.micro q.fppLive q.dpLive T) :
    EncTapes margin (prepared x wm.machine.control.last) (polarity q.polarity)
      q.gap q.micro q.fppLive q.dpLive (output T) := by
  have hkeep (slot : Slot) (hcounter : ∀ c, slot ≠ counterSlot c) (hmirror : ∀ m, slot ≠ mirrorSlot m) :=
    output_other T slot hcounter hmirror
  refine { margins := ?_, heads := ?_, idleHead := ?_, fpp := ?_, dp := ?_, idleShape := ?_, counters := ?_, places := ?_, mirrors := ?_, period := ?_, answer := ?_ }
  · intro slot
    have hm := henc.margins (slots slot)
    unfold output changed
    split_ifs
    · rcases ht : T (slots slot) with ⟨left, focus, right⟩
      rw [ht] at hm
      cases right <;> simp_all [STape.applyAction, pos] <;> omega
    · exact hm
  · intro v head hh
    have hsource : headOf x v = some head := by
      fin_cases v <;> first | exact hh | cases hh
    obtain ⟨view, vt, ha, hv, ht, hc, hw⟩ := henc.heads v head hsource
    refine ⟨view, vt, ha, hv, ?_, hc, hw⟩
    intro i
    rw [hkeep _ (by intro c; simp [headSlot, counterSlot]) (by intro m; simp [headSlot, mirrorSlot])]
    exact ht i
  · intro _
    obtain ⟨view, vt, _, hv, ht, hc, hw⟩ := henc.heads 3 wm.machine.verifier (by simp [headOf, hchain])
    refine ⟨view, vt, hv, ?_, hc, hw⟩
    intro i
    rw [hkeep _ (by intro c; simp [headSlot, counterSlot]) (by intro m; simp [headSlot, mirrorSlot])]
    exact ht i
  · intro i
    rw [hkeep _ (by intro c; cases q.fppLive <;> simp [progSlotOf, counterSlot])
      (by intro m; cases q.fppLive <;> simp [progSlotOf, mirrorSlot])]
    exact henc.fpp i
  · intro i
    rw [hkeep _ (by intro c; cases q.dpLive <;> simp [dpSlotOf, counterSlot])
      (by intro m; cases q.dpLive <;> simp [dpSlotOf, mirrorSlot])]
    exact henc.dp i
  · intro i
    rw [hkeep _ (by intro c; cases q.fppLive <;> simp [progSlotOf, counterSlot])
      (by intro m; cases q.fppLive <;> simp [progSlotOf, mirrorSlot])]
    exact henc.idleShape i
  · intro c value hv
    fin_cases c <;> simp only [counterOf, prepared, Option.some.injEq] at hv
    all_goals first | cases hv | subst value
    all_goals rw [output_counter]
    all_goals simp only [polarity, Fin.reduceFinMk, Fin.isValue, reduceCtorEq, ↓reduceIte]
    · exact henc.counters 0 _ rfl
    · exact henc.counters 1 _ rfl
    · exact henc.counters 2 _ rfl
    · exact henc.counters 3 _ rfl
    · exact henc.counters 4 _ rfl
    · exact henc.counters 6 _ (by simp [counterOf, hlast])
    · obtain ⟨seg, _, hseg⟩ := henc.counters 5 x.vm.lower rfl
      exact ⟨resetSeg seg, PalPeg.LocalCounter.absCtr_reset seg _, by simp [hseg, padded_resetSeg]⟩
    · exact henc.counters 15 _ (by simp [counterOf, hchain])
    · exact henc.counters 8 _ rfl
    · exact henc.counters 9 _ rfl
  · intro i place hp
    have hsource : placeOf x i = some place := by fin_cases i <;> first | exact hp | cases hp
    obtain ⟨stack, junk, hj, ht, hs⟩ := henc.places i place hsource
    refine ⟨stack, junk, hj, ht, ?_⟩
    rw [hkeep _ (by intro c; simp [placeSlot, counterSlot]) (by intro m; simp [placeSlot, mirrorSlot])]
    exact hs
  · intro m value hv
    fin_cases m <;> simp only [mirrorSource, counterOf, prepared, Option.some.injEq] at hv
    all_goals first | cases hv | subst value
    all_goals rw [output_mirror]
    all_goals simp only [polarity, mirrorSource, Fin.reduceFinMk, Fin.isValue, reduceCtorEq, ↓reduceIte]
    · exact henc.mirrors 0 _ rfl
    · exact henc.mirrors 1 _ rfl
    · exact henc.mirrors 2 _ rfl
    · exact henc.mirrors 4 _ (by simp [mirrorSource, counterOf, hlast])
    · obtain ⟨seg, _, hseg⟩ := henc.mirrors 3 x.vm.lower rfl
      exact ⟨resetSeg seg, PalPeg.LocalCounter.absCtr_reset seg _, by simp [hseg, padded_resetSeg]⟩
    · exact henc.mirrors 6 _ rfl
  · intro tape ht; cases ht
  · intro tape ht; cases ht

theorem shapes_prepared {T : Slot → STape Γm}
    (hshape : PalPeg.PhysicalWatchEntry.CounterShapes T) :
    PalPeg.PhysicalWatchEntry.CounterShapes (output T) := by
  intro c
  rw [output_counter]
  split_ifs with h5 h6 h7 h15
  · exact hshape 6
  · obtain ⟨seg, ht⟩ := hshape 5
    exact ⟨resetSeg seg, by rw [ht, padded_resetSeg]⟩
  · exact hshape 15
  · exact hshape 7
  · exact hshape c

/-- The handoff establishes the entire existing encoding, including every
remaining mirror; debt and DP still have their old, explicitly specified values. -/
theorem core_prepared (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .broken wm)
    (hlast : x.vm.search.span = wm.machine.control.last) (he : CoreInv w x p) :
    CoreInv w (prepared x wm.machine.control.last)
      (nextControl p.1, fun j => output (fun slot => p.2 (slotIndex slot)) (slotIndex.symm j)) := by
  refine ⟨⟨⟨⟨control_prepared w x p.1 _ he.1.1.1.1, ?_⟩, he.1.1.2⟩, ?_⟩, trivial⟩
  · simpa only [Equiv.symm_apply_apply, nextControl] using tapes_prepared w x p.1 _ wm hchain hlast he.1.1.1.2
  · simpa only [Equiv.symm_apply_apply] using shapes_prepared he.1.2

/-- Two tapes each receive one separator. The three swaps are finite control. -/
noncomputable def rule : ActRule (Fin 2) CoreControl Γm tapeCountM 32 where
  nq := fun q _ _ => nextControl q
  acts := fun _ _ _ j => if resets (slotIndex.symm j) then
    [some (encSeg PalPeg.LocalCounter.sep, .right)] else []
  len_le := by intro q input ws j; split_ifs <;> simp

noncomputable def change : PalPeg.LocalRoleRouting.RoleChange (Fin 2) CoreControl Γm tapeCountM 32 :=
  fun _ _ _ => roles

noncomputable def plan := PalPeg.LocalRoleFusion.routeRule rule change

/-- Logical execution is exactly reset-then-rename, including the sign transfer. -/
theorem logical_prepared (p : CoreState) (input : Option (Fin 2)) :
    logicalStep rule change blankM p input =
      (nextControl p.1, fun j => output (fun slot => p.2 (slotIndex slot)) (slotIndex.symm j)) := by
  apply Prod.ext
  · rfl
  · funext j
    simp only [logicalStep, idealStep, rule, change, roles, output, changed,
      Equiv.trans_apply, Equiv.symm_apply_apply]
    split_ifs <;> rfl

/-- The action row also works on every TEqG representative of the source. -/
theorem running_ideal (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .broken wm)
    (hlast : x.vm.search.span = wm.machine.control.last) (he : Running w x p)
    (input : Option (Fin 2)) :
    Running w (prepared x wm.machine.control.last) (logicalStep rule change blankM p input) := by
  obtain ⟨T, hT, ht⟩ := he
  have hc := core_prepared w x (p.1, T) wm hchain hlast hT
  rw [← logical_prepared (p.1, T) input] at hc
  obtain ⟨_, hacts⟩ := idealStep_congr_teqG rule blankM p.1 T p.2 ht input
  exact ⟨_, hc, fun j => hacts (roles j)⟩

/-- One actual bounded sweep performs the complete last-copy handoff, for every
source role assignment. This is a stage to fuse into restart, not an extra tick. -/
theorem running (w : List (Fin 2)) (x : State GalilVM)
    (p : PalPeg.PhysicalShiftDispatch.RoutedCore)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .broken wm)
    (hlast : x.vm.search.span = wm.machine.control.last)
    (he : Running w x (PalPeg.LocalRoleRouting.decode p)) (input : Option (Fin 2)) :
    Running w (prepared x wm.machine.control.last)
      (PalPeg.LocalRoleRouting.decode ((PalPeg.LocalRoleFusion.compiled plan).apply blankM p input)) := by
  have hideal := running_ideal w x (PalPeg.LocalRoleRouting.decode p) wm hchain hlast he input
  have hmargin : ∀ j, 32 ≤ pos ((PalPeg.LocalRoleRouting.decode p).2 j) := fun j =>
    (show 32 ≤ margin by decide).trans
      (running_margin (PalPeg.PhysicalCacheInvariant.running_core he) j)
  obtain ⟨hcontrol, htapes⟩ := PalPeg.LocalRoleFusion.compiled_apply plan blankM p input hmargin
  simp only [plan, PalPeg.LocalRoleFusion.decode_routeRule] at hcontrol htapes
  exact PalPeg.MachineStep.sweepClosed_sweepClosure blankM (CoreInv w)
    _ _ _ hideal hcontrol.symm htapes

/-- The common canonical encoding supplies all three copies itself. No target
encoding or independently prepared last carrier is assumed by this stage. -/
theorem from_copies (w : List (Fin 2)) (x : State GalilVM)
    (p : PalPeg.PhysicalShiftDispatch.RoutedCore)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .broken wm)
    (he : PalPeg.PhysicalSnapshotInvariant.Enc w x (PalPeg.PhysicalShiftDispatch.liftConfig p)) :
    ∃ h age spare, PalPeg.ChainBoundaryCache.Inv h age wm.machine.control spare ∧
      Running w (prepared (saved x wm.machine.control.boundary wm.machine.control.last spare)
        wm.machine.control.last)
        (PalPeg.LocalRoleRouting.decode ((PalPeg.LocalRoleFusion.compiled plan).apply blankM p none)) := by
  obtain ⟨h, age, spare, hi, hs⟩ := he.2 wm (Or.inr hchain)
  refine ⟨h, age, spare, hi, ?_⟩
  exact running w (saved x wm.machine.control.boundary wm.machine.control.last spare) p wm
    (show (saved x _ _ spare).vm.chain = .broken wm from hchain) rfl hs none

/-- The two remaining abstract updates after the handoff. Their physical
realization, including the radius mirror and the reset DP bank, is still owed. -/
def finishDebtDp (x : State GalilVM) : State GalilVM :=
  ⟨x.ctl, {x.vm with search := {x.vm.search with debt := PalPeg.GalilScaffoldSearchFinish.initialDebt x.vm.radius}, dp := PalPeg.GalilScaffoldControl.reset 0 x.vm.dp}⟩

/-- The intermediate state is on the real restart path: only debt and DP remain,
regardless of the suspended counters originally stored in the canonical state. -/
theorem completed_is_restart (w : List (Fin 2)) (x : State GalilVM)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .broken wm)
    (hmode : x.ctl.mode = .scan) (hguard : restartGuardVM x.vm) (spare : Counter) :
    finishDebtDp (prepared (saved x wm.machine.control.boundary wm.machine.control.last spare)
      wm.machine.control.last) = PalPeg.PhysicalCacheMachine.successor w x := by
  obtain ⟨other, ho, hm, hl, hz⟩ := hguard
  have hw : other = wm := by rw [hchain] at ho; cases ho; rfl
  subst other
  have hzero : PalPeg.GalilScaffoldCounter.zero wm.machine.control.last = false := by
    cases hpos : wm.machine.control.last.pos.isEmpty <;>
      simp_all [PalPeg.GalilScaffoldCounter.positive, PalPeg.GalilScaffoldCounter.zero]
  have hr : restartVM 0 x.vm
      (finishDebtDp (prepared (saved x wm.machine.control.boundary wm.machine.control.last spare)
        wm.machine.control.last)).vm := by
    refine ⟨wm, hchain, hm, hl, hz, ?_⟩
    simp [finishDebtDp, prepared, saved, put, PalPeg.PhysicalRestartStorage.replace,
      PalPeg.GalilScaffoldSearchFinish.begin, hzero]
  unfold PalPeg.PhysicalCacheMachine.successor
  rw [PalPeg.PhysicalRestartStorage.tick_restart w x hmode ⟨wm, hchain, hm, hl, hz⟩]
  exact congrArg (fun vm => (⟨{x.ctl with clock := 2048}, vm⟩ : State GalilVM))
    (restartFun_eq 0 hr)

/-- info: 'PalPeg.PhysicalRestartCopies.running' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms running

/-- info: 'PalPeg.PhysicalRestartCopies.from_copies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms from_copies

/-- info: 'PalPeg.PhysicalRestartCopies.completed_is_restart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms completed_is_restart

end PalPeg.PhysicalRestartCopies
