import PalPeg.PhysicalRestartCopies

/-! # Lending the radius mirror to debt and tracking its reconstruction

The physical mirror is partial while search pays its initial debt. Only its
proof view is completed from the still-live radius mirror 0. Every other tape
retains the existing CoreInv. Completion is never a machine transition.
-/
set_option autoImplicit false
namespace PalPeg.PhysicalDebtMirror
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract
open PalPeg.PhysicalCacheInvariant (CoreInv)
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilScaffoldCounter (Counter value ofNat Canonical reset)
open PalPeg.Program PalPeg.Local PalPeg.CloseoutCoreEnc12 PalPeg.LocalStepFusion
open PalPeg.LocalCounter (Seg absCtr resetSeg)
open PalPeg.LocalRoleFusion (logicalStep)

/-- Credits accumulated toward a full radius copy. -/
def credit (x : State GalilVM) : Counter :=
  ofNat (value x.vm.radius + min (value x.vm.search.debt) 0).toNat

def borrowed (x : State GalilVM) : State GalilVM :=
  ⟨x.ctl, {x.vm with search := {x.vm.search with debt := PalPeg.GalilScaffoldSearchFinish.initialDebt x.vm.radius}}⟩

theorem credit_borrowed (x : State GalilVM) : credit (borrowed x) = reset := by
  have hz := PalPeg.GalilScaffoldSearchFinish.initial_balance x.vm.radius
  have hle : value x.vm.radius + min (value (PalPeg.GalilScaffoldSearchFinish.initialDebt x.vm.radius)) 0 ≤ 0 := by omega
  change ofNat (value x.vm.radius + min (value (PalPeg.GalilScaffoldSearchFinish.initialDebt x.vm.radius)) 0).toNat = reset
  rw [Int.toNat_eq_zero.mpr hle]
  rfl

theorem credit_ready (x : State GalilVM) (hc : Canonical x.vm.radius)
    (hr : 0 ≤ value x.vm.radius) (hd : 0 ≤ value x.vm.search.debt) : credit x = x.vm.radius := by
  apply PalPeg.ChainBoundaryCache.counter_eq_of_value (PalPeg.GalilScaffoldCounter.ofNat_canonical _) hc
  simp only [credit, min_eq_right hd, add_zero, PalPeg.GalilScaffoldCounter.ofNat_value]
  exact Int.toNat_of_nonneg hr

/-- Complete only mirror 2's proof view from the actual independent mirror 0. -/
noncomputable def repair (T : Slot → STape Γm) (slot : Slot) : STape Γm :=
  if slot = mirrorSlot 2 then T (mirrorSlot 0) else T slot

noncomputable def mirrorIndex : Fin tapeCountM := slotIndex (mirrorSlot 2)
noncomputable def repaired (T : Fin tapeCountM → STape Γm) (j : Fin tapeCountM) : STape Γm :=
  repair (fun slot => T (slotIndex slot)) (slotIndex.symm j)

/-- The actual partial copy retains its own exact value and tape shape. -/
def RebuildingCore (w : List (Fin 2)) (x : State GalilVM) (p : CoreState) : Prop :=
  CoreInv w x (p.1, repaired p.2) ∧ ∃ seg : STape Seg,
    absCtr seg (p.1.polarity 2) = credit x ∧ p.2 mirrorIndex = padLeft margin (mapTape encSeg seg)

def Rebuilding (w : List (Fin 2)) := PalPeg.MachineStep.sweepClosure blankM (RebuildingCore w)

noncomputable def slots : Equiv.Perm Slot := Equiv.swap (counterSlot 8) (mirrorSlot 2)
noncomputable def roles : PalPeg.PhysicalRoles.Roles := (slotIndex.symm.trans slots).trans slotIndex

def bits (b : Fin 16 → Bool) := Function.update b 8 (!(b 2))
def nextControl (q : CoreControl) : CoreControl := {q with polarity := bits q.polarity}

noncomputable def changed (T : Slot → STape Γm) (slot : Slot) : STape Γm :=
  if slot = counterSlot 8 then (T slot).applyAction blankM (encSeg PalPeg.LocalCounter.sep, .right) else T slot
noncomputable def output (T : Slot → STape Γm) (slot : Slot) : STape Γm := changed T (slots slot)
noncomputable def patched (T : Slot → STape Γm) (slot : Slot) : STape Γm :=
  if slot = counterSlot 8 then T (mirrorSlot 2) else if slot = mirrorSlot 2 then T (mirrorSlot 0) else T slot

theorem repair_output (T : Slot → STape Γm) : repair (output T) = patched T := by
  funext slot
  by_cases hc : slot = counterSlot 8
  · subst slot; simp [repair, output, changed, slots, patched, counterSlot, mirrorSlot, Equiv.swap_apply_def]
  · by_cases hm : slot = mirrorSlot 2
    · subst slot; simp [repair, output, changed, slots, patched, counterSlot, mirrorSlot, Equiv.swap_apply_def]
    · simp [repair, output, changed, slots, patched, hc, hm, Equiv.swap_apply_def]

theorem output_mirror (T : Slot → STape Γm) :
    output T (mirrorSlot 2) = (T (counterSlot 8)).applyAction blankM (encSeg PalPeg.LocalCounter.sep, .right) := by
  simp [output, changed, slots, Equiv.swap_apply_def, counterSlot, mirrorSlot]

theorem control_borrowed {w : List (Fin 2)} {x : State GalilVM} {q : CoreControl}
    (he : EncControl w x q) : EncControl w (borrowed x) (nextControl q) := by
  exact PalPeg.PhysicalFreeCounter.encControl_polarity
    (PalPeg.PhysicalRestartStorage.control_replace w x q he x.vm.lower x.vm.search.span
      x.vm.search.work (PalPeg.GalilScaffoldSearchFinish.initialDebt x.vm.radius)) _

theorem tapes_patched {x : State GalilVM} {q : CoreControl} {T : Slot → STape Γm}
    (he : EncTapes margin x q.polarity q.gap q.micro q.fppLive q.dpLive T) :
    EncTapes margin (borrowed x) (bits q.polarity) q.gap q.micro q.fppLive q.dpLive (patched T) := by
  have hkeep (slot : Slot) (hc : slot ≠ counterSlot 8) (hm : slot ≠ mirrorSlot 2) : patched T slot = T slot := by
    simp [patched, hc, hm]
  refine { margins := ?_, heads := ?_, idleHead := ?_, fpp := ?_, dp := ?_, idleShape := ?_, counters := ?_, places := ?_, mirrors := ?_, period := ?_, answer := ?_ }
  · intro slot
    unfold patched
    split_ifs <;> apply he.margins
  · intro v head hh
    obtain ⟨view, vt, ha, hv, ht, hc, hw⟩ := he.heads v head hh
    exact ⟨view, vt, ha, hv, fun i => by simpa [patched, counterSlot, mirrorSlot] using ht i, hc, hw⟩
  · intro hh
    obtain ⟨view, vt, hv, ht, hc, hw⟩ := he.idleHead hh
    exact ⟨view, vt, hv, fun i => by simpa [patched, headSlot, counterSlot, mirrorSlot] using ht i, hc, hw⟩
  · intro i
    rw [hkeep _ (by cases q.fppLive <;> simp [progSlotOf, counterSlot]) (by cases q.fppLive <;> simp [progSlotOf, mirrorSlot])]
    exact he.fpp i
  · intro i
    rw [hkeep _ (by cases q.dpLive <;> simp [dpSlotOf, counterSlot]) (by cases q.dpLive <;> simp [dpSlotOf, mirrorSlot])]
    exact he.dp i
  · intro i
    rw [hkeep _ (by cases q.fppLive <;> simp [progSlotOf, counterSlot]) (by cases q.fppLive <;> simp [progSlotOf, mirrorSlot])]
    exact he.idleShape i
  · intro c val hv
    by_cases hc : c = 8
    · subst c
      have hv' : val = PalPeg.GalilScaffoldSearchFinish.initialDebt x.vm.radius := Option.some.inj hv.symm
      subst val
      obtain ⟨seg, ha, ht⟩ := he.mirrors 2 x.vm.radius rfl
      refine ⟨seg, ?_, ?_⟩
      · change absCtr seg (!(q.polarity 2)) = _
        rw [PalPeg.LocalCounter.neg_flip]
        exact congrArg PalPeg.LocalCounter.negate ha
      · simpa [patched, counterSlot, mirrorSlot] using ht
    · have hsource : counterOf x c = some val := by
        fin_cases c <;> first | exact hv | contradiction
      obtain ⟨seg, ha, ht⟩ := he.counters c val hsource
      refine ⟨seg, by simpa [bits, hc] using ha, ?_⟩
      simpa [patched, counterSlot, mirrorSlot, hc] using ht
  · intro i place hp
    obtain ⟨stack, junk, hj, ht, hs⟩ := he.places i place hp
    exact ⟨stack, junk, hj, ht, by simpa [patched, placeSlot, counterSlot, mirrorSlot] using hs⟩
  · intro m val hv
    have h8 : mirrorSource m ≠ 8 := by fin_cases m <;> decide
    by_cases hm : m = 2
    · subst m
      obtain ⟨seg, ha, ht⟩ := he.mirrors 0 val hv
      exact ⟨seg, by simpa [bits, mirrorSource] using ha,
        by simpa [patched, mirrorSlot, counterSlot] using ht⟩
    · have hsource : counterOf x (mirrorSource m) = some val := by fin_cases m <;> exact hv
      obtain ⟨seg, ha, ht⟩ := he.mirrors m val hsource
      exact ⟨seg, by simpa [bits, h8] using ha,
        by simpa [patched, mirrorSlot, counterSlot, hm] using ht⟩
  · intro tape ht; simpa [patched, periodSlot, counterSlot, mirrorSlot] using he.period tape ht
  · intro tape ht; simpa [patched, counterSlot, mirrorSlot] using he.answer tape ht

theorem shapes_patched {x : State GalilVM} {q : CoreControl} {T : Slot → STape Γm}
    (he : EncTapes margin x q.polarity q.gap q.micro q.fppLive q.dpLive T)
    (hs : PalPeg.PhysicalWatchEntry.CounterShapes T) :
    PalPeg.PhysicalWatchEntry.CounterShapes (patched T) := by
  intro c
  by_cases hc : c = 8
  · subst c
    obtain ⟨seg, _, ht⟩ := he.mirrors 2 x.vm.radius rfl
    exact ⟨seg, by simpa [patched, counterSlot, mirrorSlot] using ht⟩
  · obtain ⟨seg, ht⟩ := hs c
    exact ⟨seg, by simpa [patched, counterSlot, mirrorSlot, hc] using ht⟩

theorem core_borrowed (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (hidle : x.vm.chain = .idle) (he : CoreInv w x p) :
    RebuildingCore w (borrowed x)
      (nextControl p.1, fun j => output (fun slot => p.2 (slotIndex slot)) (slotIndex.symm j)) := by
  have hp : CoreInv w (borrowed x)
      (nextControl p.1, fun j => patched (fun slot => p.2 (slotIndex slot)) (slotIndex.symm j)) := by
    refine ⟨⟨⟨⟨control_borrowed he.1.1.1.1, ?_⟩, he.1.1.2⟩, ?_⟩, ?_⟩
    · simpa only [Equiv.symm_apply_apply, nextControl] using tapes_patched he.1.1.1.2
    · simpa only [Equiv.symm_apply_apply] using shapes_patched he.1.1.1.2 he.1.2
    · simp [PalPeg.PhysicalCacheInvariant.Cache, borrowed, hidle]
  refine ⟨?_, ?_⟩
  · have hr : repaired (fun j => output (fun slot => p.2 (slotIndex slot)) (slotIndex.symm j)) =
        (fun j => patched (fun slot => p.2 (slotIndex slot)) (slotIndex.symm j)) := by
      funext j
      change repair (fun slot => output (fun s => p.2 (slotIndex s)) (slotIndex.symm (slotIndex slot)))
        (slotIndex.symm j) = _
      simp only [Equiv.symm_apply_apply, repair_output]
    change CoreInv w (borrowed x) (nextControl p.1, repaired _)
    rw [hr]
    exact hp
  · obtain ⟨seg, _, ht⟩ := he.1.1.1.2.counters 8 x.vm.search.debt rfl
    refine ⟨resetSeg seg, ?_, ?_⟩
    · rw [credit_borrowed]
      exact PalPeg.LocalCounter.absCtr_reset _ _
    · simp only [mirrorIndex, Equiv.symm_apply_apply, output_mirror]
      rw [ht, padded_resetSeg]

/-- Reset the old debt carrier and exchange it with the radius mirror. -/
noncomputable def rule : ActRule (Fin 2) CoreControl Γm tapeCountM 32 where
  nq := fun q _ _ => nextControl q
  acts := fun _ _ _ j => if slotIndex.symm j = counterSlot 8 then
    [some (encSeg PalPeg.LocalCounter.sep, .right)] else []
  len_le := by intro q input ws j; split_ifs <;> simp

noncomputable def change : PalPeg.LocalRoleRouting.RoleChange (Fin 2) CoreControl Γm tapeCountM 32 :=
  fun _ _ _ => roles

noncomputable def plan := PalPeg.LocalRoleFusion.routeRule rule change

theorem logical_borrowed (p : CoreState) (input : Option (Fin 2)) :
    logicalStep rule change blankM p input =
      (nextControl p.1, fun j => output (fun slot => p.2 (slotIndex slot)) (slotIndex.symm j)) := by
  apply Prod.ext
  · rfl
  · funext j
    simp only [logicalStep, idealStep, rule, change, roles, output, changed,
      Equiv.trans_apply, Equiv.symm_apply_apply]
    split_ifs <;> rfl

theorem running_ideal (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (hidle : x.vm.chain = .idle) (he : PalPeg.PhysicalCacheInvariant.Running w x p)
    (input : Option (Fin 2)) :
    Rebuilding w (borrowed x) (logicalStep rule change blankM p input) := by
  obtain ⟨T, hT, ht⟩ := he
  have hc := core_borrowed w x (p.1, T) hidle hT
  rw [← logical_borrowed (p.1, T) input] at hc
  obtain ⟨_, hacts⟩ := idealStep_congr_teqG rule blankM p.1 T p.2 ht input
  exact ⟨_, hc, fun j => hacts (roles j)⟩

/-- Lending and sign reversal take one real bounded sweep; the actual partial
mirror is reset, and every other part of the existing encoding is preserved. -/
theorem running (w : List (Fin 2)) (x : State GalilVM)
    (p : PalPeg.PhysicalShiftDispatch.RoutedCore) (hidle : x.vm.chain = .idle)
    (he : PalPeg.PhysicalCacheInvariant.Running w x (PalPeg.LocalRoleRouting.decode p))
    (input : Option (Fin 2)) :
    Rebuilding w (borrowed x)
      (PalPeg.LocalRoleRouting.decode ((PalPeg.LocalRoleFusion.compiled plan).apply blankM p input)) := by
  have hideal := running_ideal w x (PalPeg.LocalRoleRouting.decode p) hidle he input
  have hmargin : ∀ j, 32 ≤ pos ((PalPeg.LocalRoleRouting.decode p).2 j) := fun j =>
    (show 32 ≤ margin by decide).trans
      (running_margin (PalPeg.PhysicalCacheInvariant.running_core he) j)
  obtain ⟨hcontrol, htapes⟩ := PalPeg.LocalRoleFusion.compiled_apply plan blankM p input hmargin
  simp only [plan, PalPeg.LocalRoleFusion.decode_routeRule] at hcontrol htapes
  exact PalPeg.MachineStep.sweepClosed_sweepClosure blankM (RebuildingCore w)
    _ _ _ hideal hcontrol.symm htapes

/-- When the rebuilt physical mirror reaches radius, the proof completion can
be removed without copying a tape. All other encoding clauses are unchanged. -/
theorem tapes_unrepair {x : State GalilVM} {q : CoreControl} {T : Slot → STape Γm}
    (he : EncTapes margin x q.polarity q.gap q.micro q.fppLive q.dpLive (repair T))
    (hr : ∃ seg : STape Seg, absCtr seg (q.polarity 2) = x.vm.radius ∧
      T (mirrorSlot 2) = padLeft margin (mapTape encSeg seg)) :
    EncTapes margin x q.polarity q.gap q.micro q.fppLive q.dpLive T := by
  obtain ⟨raw, ha, ht⟩ := hr
  refine { margins := ?_, heads := ?_, idleHead := ?_, fpp := ?_, dp := ?_, idleShape := ?_, counters := ?_, places := ?_, mirrors := ?_, period := ?_, answer := ?_ }
  · intro slot
    by_cases hs : slot = mirrorSlot 2
    · subst slot; rw [ht, pos_padLeft]; omega
    · simpa [repair, hs] using he.margins slot
  · intro v head hh
    obtain ⟨view, vt, habs, hv, hs, hc, hw⟩ := he.heads v head hh
    exact ⟨view, vt, habs, hv, fun i => by simpa [repair, mirrorSlot] using hs i, hc, hw⟩
  · intro hh
    obtain ⟨view, vt, hv, hs, hc, hw⟩ := he.idleHead hh
    exact ⟨view, vt, hv, fun i => by simpa [repair, headSlot, mirrorSlot] using hs i, hc, hw⟩
  · intro i
    cases hq : q.fppLive <;> simpa [repair, progSlotOf, mirrorSlot, hq] using he.fpp i
  · intro i
    cases hq : q.dpLive <;> simpa [repair, dpSlotOf, mirrorSlot, hq] using he.dp i
  · intro i
    cases hq : q.fppLive <;> simpa [repair, progSlotOf, mirrorSlot, hq] using he.idleShape i
  · intro c val hv
    obtain ⟨seg, hs, heq⟩ := he.counters c val hv
    exact ⟨seg, hs, by simpa [repair, counterSlot, mirrorSlot] using heq⟩
  · intro i place hp
    obtain ⟨stack, junk, hj, hs, heq⟩ := he.places i place hp
    exact ⟨stack, junk, hj, hs, by simpa [repair, placeSlot, mirrorSlot] using heq⟩
  · intro m val hv
    by_cases hm : m = 2
    · subst m
      have hval : x.vm.radius = val := Option.some.inj hv
      exact ⟨raw, ha.trans hval, ht⟩
    · obtain ⟨seg, hs, heq⟩ := he.mirrors m val hv
      exact ⟨seg, hs, by simpa [repair, mirrorSlot, hm] using heq⟩
  · intro tape ht; simpa [repair, periodSlot, mirrorSlot] using he.period tape ht
  · intro tape ht; simpa [repair, mirrorSlot] using he.answer tape ht

theorem core_ready (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : RebuildingCore w x p) (hr : 0 ≤ value x.vm.radius)
    (hd : 0 ≤ value x.vm.search.debt) : CoreInv w x p := by
  obtain ⟨hbase, seg, ha, ht⟩ := he
  obtain ⟨radius, habs, _⟩ := hbase.1.1.1.2.counters 2 x.vm.radius rfl
  have hcanonical : Canonical x.vm.radius := habs ▸ PalPeg.LocalCounter.absCtr_canonical radius _
  have hcredit := credit_ready x hcanonical hr hd
  refine ⟨⟨⟨⟨hbase.1.1.1.1, ?_⟩, hbase.1.1.2⟩, ?_⟩, ?_⟩
  · apply tapes_unrepair
    · simpa only [repaired, Equiv.symm_apply_apply] using hbase.1.1.1.2
    · exact ⟨seg, ha.trans hcredit, ht⟩
  · intro c
    simpa [repaired, repair, counterSlot, mirrorSlot] using hbase.1.2 c
  · simpa [repaired, repair, PalPeg.PhysicalSpare.spareIndex,
      PalPeg.PhysicalPeriodMirror.mirrorIndex, counterSlot, mirrorSlot] using hbase.2

/-- Readiness converts the actual sweep representation back to the old one. -/
theorem ready (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : Rebuilding w x p) (hr : 0 ≤ value x.vm.radius)
    (hd : 0 ≤ value x.vm.search.debt) : PalPeg.PhysicalCacheInvariant.Running w x p := by
  obtain ⟨T, hT, ht⟩ := he
  exact ⟨T, core_ready w x (p.1, T) hT hr hd, ht⟩

/-- One debt increment replenishes one missing radius unit exactly when debt
was negative. The balance is nonnegative at restart and preserved by the schedule. -/
theorem credit_pay (radius debt : ℤ) (hbalance : 0 ≤ radius + debt) :
    (radius + min (debt + 1) 0).toNat =
      (radius + min debt 0).toNat + (if debt < 0 then 1 else 0) := by
  split_ifs <;> omega

/-- A matched radius increment is already paid by the simultaneous debt
decrement until debt is positive; only then does the partial mirror grow. -/
theorem credit_advance (radius debt : ℤ) (hradius : 0 ≤ radius) :
    (radius + 1 + min (debt - 1) 0).toNat =
      (radius + min debt 0).toNat + (if 0 < debt then 1 else 0) := by
  split_ifs <;> omega

/-- An exit whose outer match leaves debt=-1 is only one unit short. The run
safety guard is before that match, so readiness must not be inferred too early. -/
theorem credit_one_short (radius debt : ℤ) (hradius : 0 ≤ radius) (hdebt : -1 ≤ debt) :
    (radius + min debt 0).toNat ≤ radius.toNat ∧
      radius.toNat ≤ (radius + min debt 0).toNat + 1 := by omega

/-- Both finite-role stages use one combined source window and one real sweep. -/
noncomputable def restartPlan :
    ActRule (Fin 2) (PalPeg.LocalRoleRouting.Control CoreControl tapeCountM) Γm tapeCountM 64 :=
  seqRule PalPeg.PhysicalRestartCopies.plan plan

theorem restart_plan_ideal (p : CoreState) (hmargin : ∀ j, 64 ≤ pos (p.2 j)) :
    PalPeg.LocalRoleRouting.decode (idealStep restartPlan blankM ((Equiv.refl _, p.1), p.2) none) =
      logicalStep rule change blankM
        (logicalStep PalPeg.PhysicalRestartCopies.rule PalPeg.PhysicalRestartCopies.change blankM p none) none :=
  PalPeg.LocalRoleFusion.decode_seqRule PalPeg.PhysicalRestartCopies.rule rule
    PalPeg.PhysicalRestartCopies.change change blankM _ none hmargin

/-- The fused ideal handoff includes lower/span/work, their mirrors and debt. -/
theorem restart_ideal (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .broken wm)
    (hlast : x.vm.search.span = wm.machine.control.last)
    (he : PalPeg.PhysicalCacheInvariant.Running w x p) :
    Rebuilding w (borrowed (PalPeg.PhysicalRestartCopies.prepared x wm.machine.control.last))
      (PalPeg.LocalRoleRouting.decode (idealStep restartPlan blankM ((Equiv.refl _, p.1), p.2) none)) := by
  have hcopy := PalPeg.PhysicalRestartCopies.running_ideal w x p wm hchain hlast he none
  have hloan := running_ideal w (PalPeg.PhysicalRestartCopies.prepared x wm.machine.control.last)
    _ rfl hcopy none
  rw [restart_plan_ideal p (fun j => (show 64 ≤ margin by decide).trans
    (running_margin (PalPeg.PhysicalCacheInvariant.running_core he) j))]
  exact hloan

/-- No extra abstract or physical tick is inserted between the copy exchange
and debt's radius loan. DP is the remaining restart state update. -/
theorem restart_running (w : List (Fin 2)) (x : State GalilVM)
    (p : PalPeg.PhysicalShiftDispatch.RoutedCore)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .broken wm)
    (hlast : x.vm.search.span = wm.machine.control.last)
    (he : PalPeg.PhysicalCacheInvariant.Running w x (PalPeg.LocalRoleRouting.decode p)) :
    Rebuilding w (borrowed (PalPeg.PhysicalRestartCopies.prepared x wm.machine.control.last))
      (PalPeg.LocalRoleRouting.decode ((PalPeg.LocalRoleFusion.compiled restartPlan).apply blankM p none)) := by
  have hideal := restart_ideal w x (PalPeg.LocalRoleRouting.decode p) wm hchain hlast he
  have hmargin : ∀ j, 64 ≤ pos ((PalPeg.LocalRoleRouting.decode p).2 j) := fun j =>
    (show 64 ≤ margin by decide).trans
      (running_margin (PalPeg.PhysicalCacheInvariant.running_core he) j)
  obtain ⟨hcontrol, htapes⟩ := PalPeg.LocalRoleFusion.compiled_apply restartPlan blankM p none hmargin
  exact PalPeg.MachineStep.sweepClosed_sweepClosure blankM (RebuildingCore w)
    _ _ _ hideal hcontrol.symm htapes

/-- The already-connected canonical encoding supplies every source copy. -/
theorem restart_from_copies (w : List (Fin 2)) (x : State GalilVM)
    (p : PalPeg.PhysicalShiftDispatch.RoutedCore)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .broken wm)
    (he : PalPeg.PhysicalSnapshotInvariant.Enc w x (PalPeg.PhysicalShiftDispatch.liftConfig p)) :
    ∃ h age spare, PalPeg.ChainBoundaryCache.Inv h age wm.machine.control spare ∧
      Rebuilding w (borrowed (PalPeg.PhysicalRestartCopies.prepared
        (PalPeg.PhysicalSearchSnapshots.saved x wm.machine.control.boundary wm.machine.control.last spare)
        wm.machine.control.last))
        (PalPeg.LocalRoleRouting.decode ((PalPeg.LocalRoleFusion.compiled restartPlan).apply blankM p none)) := by
  obtain ⟨h, age, spare, hi, hs⟩ := he.2 wm (Or.inr hchain)
  refine ⟨h, age, spare, hi, ?_⟩
  exact restart_running w (PalPeg.PhysicalSearchSnapshots.saved x wm.machine.control.boundary wm.machine.control.last spare)
    p wm (show (PalPeg.PhysicalSearchSnapshots.saved x _ _ spare).vm.chain = .broken wm from hchain) rfl hs

/-- This is the remaining abstract update, not a claimed physical DP reset. -/
def finishDp (x : State GalilVM) : State GalilVM :=
  ⟨x.ctl, {x.vm with dp := PalPeg.GalilScaffoldControl.reset 0 x.vm.dp}⟩

theorem only_dp_left (w : List (Fin 2)) (x : State GalilVM)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .broken wm)
    (hmode : x.ctl.mode = .scan) (hguard : restartGuardVM x.vm) (spare : Counter) :
    finishDp (borrowed (PalPeg.PhysicalRestartCopies.prepared
      (PalPeg.PhysicalSearchSnapshots.saved x wm.machine.control.boundary wm.machine.control.last spare)
      wm.machine.control.last)) = PalPeg.PhysicalCacheMachine.successor w x :=
  PalPeg.PhysicalRestartCopies.completed_is_restart w x wm hchain hmode hguard spare

/-- info: 'PalPeg.PhysicalDebtMirror.running' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms running

/-- info: 'PalPeg.PhysicalDebtMirror.ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ready

/-- info: 'PalPeg.PhysicalDebtMirror.restart_from_copies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms restart_from_copies

/-- info: 'PalPeg.PhysicalDebtMirror.only_dp_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms only_dp_left

end PalPeg.PhysicalDebtMirror
