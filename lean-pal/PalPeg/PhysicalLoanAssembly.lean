import PalPeg.PhysicalDebtRebuild
import PalPeg.PhysicalTickAssembly

/-! # Twelve-slot head assembly while the radius mirror is being rebuilt

The actual partial tape stays in the witness. Only the proof view is repaired;
its head banks coincide with the actual banks. An unnamed verifier stays idle.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PalPeg.PhysicalLoanAssembly
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.Program PalPeg.Local PalPeg.CloseoutCoreEnc12 PalPeg.LocalStepFusion
open PalPeg.PhysicalCacheInvariant (Cache)
open PalPeg.PhysicalDebtMirror (RebuildingCore Rebuilding repair repaired credit)
open PalPeg.PhysicalTickAssembly (Base Commands tick_bits nonhead_roles macroRoles macroRoles_read)

theorem head_ne_mirror (v : Fin 4) (i : Fin 12) (m : Fin 7) : headSlot v i ≠ mirrorSlot m := by
  simp [headSlot, mirrorSlot]

theorem repaired_head (T : Fin tapeCountM → STape Γm) (v : Fin 4) (i : Fin 12) :
    repaired T (slotIndex (headSlot v i)) = T (slotIndex (headSlot v i)) := by
  simp only [repaired, repair, Equiv.symm_apply_apply, head_ne_mirror, if_false]

theorem repaired_tapesOf (T : Slot → STape Γm) (slot : Slot) :
    repaired (tapesOf T) (slotIndex slot) = repair T slot := by
  simp only [repaired, repair, Equiv.symm_apply_apply, tapesOf_apply]

theorem running_tick
    (R : ActRule (Fin 2) CoreControl Γm tapeCountM microRadius)
    (change : PalPeg.LocalRoleRouting.RoleChange (Fin 2) CoreControl Γm tapeCountM microRadius)
    (base : Base) (commands : Commands) (w : List (Fin 2)) (x z y : State GalilVM)
    (p : CoreState) (input : Option (Fin 2)) (he : RebuildingCore w x p)
    (hn : Rebuilding w z (PalPeg.LocalRoleFusion.logicalStep R change blankM p input))
    (hroles : ∀ v i, change p.1 input (fun j => readWin blankM microRadius (p.2 j))
      (slotIndex (headSlot v i)) = slotIndex (headSlot v i))
    (hbits : let ws := fun j => readWin blankM microRadius (p.2 j)
      (base p.1 input ws).polarity = (R.nq p.1 input ws).polarity ∧
      (base p.1 input ws).fppLive = (R.nq p.1 input ws).fppLive ∧
      (base p.1 input ws).dpLive = (R.nq p.1 input ws).dpLive)
    (hctl : EncControl w y (base p.1 input (fun j => readWin blankM microRadius (p.2 j))))
    (fs : Fin 4 → PalPeg.GalilScaffoldInputHead.PlaceHead → PalPeg.GalilScaffoldInputHead.PlaceHead)
    (hop : ∀ v, headOp (commands p.1 input (fun j => readWin blankM microRadius (p.2 j)) v) = some (fs v))
    (hsome : ∀ v, (headOf x v).isSome = (headOf y v).isSome)
    (hmap : ∀ v head, headOf x v = some head → headOf y v = some (fs v head))
    (hunnamed : ∀ v, headOf x v = none →
      commands p.1 input (fun j => readWin blankM microRadius (p.2 j)) v = .stay)
    (hready : ∀ v head view, headOf x v = some head → PalPeg.LocalArrival.absHead' view [] = head →
      HeadReady (commands p.1 input (fun j => readWin blankM microRadius (p.2 j)) v) view)
    (hfpp : ∀ i, y.vm.fpp.program.config.tapes i = z.vm.fpp.program.config.tapes i)
    (hdp : ∀ i, y.vm.dp.config.tapes i = z.vm.dp.config.tapes i)
    (hcounters : counterOf y = counterOf z) (hplaces : placeOf y = placeOf z)
    (hperiod : periodOf y = periodOf z) (hanswer : answerOf y = answerOf z)
    (hcache : ∀ bit T M, Cache z bit T M → Cache y bit T M)
    (hcredit : credit y = credit z) :
    let run := idealRun (tickRule (by decide) base commands R.acts R.len_le) blankM p input 12
    Rebuilding w y (run.1, fun j => run.2 (change p.1 input (fun k => readWin blankM microRadius (p.2 k)) j)) := by
  have heFull := he.1.1.1
  dsimp only
  generalize htraj : idealRun (tickRule (by decide : 2 ≤ microRadius) base commands R.acts R.len_le)
    blankM p input = trajectory
  let run := trajectory 12
  let roles := change p.1 input (fun k => readWin blankM microRadius (p.2 k))
  let qs := fun n => (trajectory n).1
  let Ts := fun n slot => (trajectory n).2 (slotIndex slot)
  let cmds := commands p.1 input (fun j => readWin blankM microRadius (p.2 j))
  have hzero : trajectory 0 = p := by rw [← htraj]; rfl
  have hcmd : ∀ v, (qs 1).commands v = cmds v := by
    intro v
    have hc := commands_afterFirstStep (by decide : 2 ≤ microRadius) base commands R.acts R.len_le p input heFull.2.1 v
    rw [htraj] at hc
    exact hc
  have hheads : ∀ v head, headOf y v = some head →
      ∃ view vt, PalPeg.LocalArrival.absHead' view [] = head ∧
        PalPeg.ConcreteLocalMachine.ViewRep margin view (run.1.gap v) (run.1.micro v) vt ∧
        (∀ i, run.2 (slotIndex (headSlot v i)) = mapTape encCell (vt i)) ∧
        PalPeg.LocalViewCells.ViewCells view ∧ PalPeg.LocalInputView.WF view := by
    intro v head hh
    have hsrc : (headOf x v).isSome = true := by rw [hsome v, hh]; rfl
    obtain ⟨old, hold⟩ : ∃ old, headOf x v = some old := by
      cases ho : headOf x v with
      | none => simp [ho] at hsrc
      | some a => exact ⟨a, rfl⟩
    have hmove : head = fs v old := Option.some.inj (hh.symm.trans (hmap v old hold))
    obtain ⟨view, vt, ha, hv, ht, hc, hw⟩ := heFull.1.2.heads v old hold
    exact heads_afterTick (by decide) micro_le_margin base commands R.acts R.len_le v p input
      heFull.2.1 qs Ts (fun step => by rw [htraj]) (fun step slot => by rw [htraj])
      view hw hc vt (by dsimp only [Ts]; rw [hzero]; intro i; simpa only [repaired_head] using ht i)
      (by dsimp only [qs]; rw [hzero]; exact hv)
      (by dsimp only [qs]; rw [hzero]; exact heFull.2.2 v)
      old head ha (fs v) (by rw [hcmd]; exact hop v) hmove
      (by rw [hcmd]; exact hready v old view hold ha)
  have hcursor : ∀ v, HeadSlotsRep margin run.1.gap run.1.micro
      (fun slot => run.2 (slotIndex slot)) v := by
    intro v
    cases hh : headOf x v with
    | some head =>
      obtain ⟨view, vt, _, hr, ht, hc, hw⟩ := hheads v (fs v head) (hmap v head hh)
      exact ⟨view, vt, hr, ht, hc, hw⟩
    | none =>
      obtain ⟨view, vt, hr, ht, hc, hw⟩ := PalPeg.PhysicalBoundary.all_heads_represented heFull.1.2 v
      have hview := headSlotsRep_afterTick (by decide : 2 ≤ microRadius) micro_le_margin
        base commands R.acts R.len_le v p input heFull.2.1 (heFull.2.2 v)
        view vt hr (fun i => by simpa only [repaired_head] using ht i) hc hw .stay (hunnamed v hh) id rfl trivial
      rw [htraj] at hview
      exact hview
  obtain ⟨U, hU, hu⟩ := hn
  let V : Slot → STape Γm := fun slot => if slot.isLeft then run.2 (slotIndex slot) else U (slotIndex slot)
  let W : Slot → STape Γm := repair V
  have hVhead : ∀ v i, V (headSlot v i) = run.2 (slotIndex (headSlot v i)) := fun _ _ => rfl
  have hVother : ∀ slot, (∀ v i, slot ≠ headSlot v i) → V slot = U (slotIndex slot) := by
    intro slot hn
    have hs := isLeft_eq_false_of_ne_headSlot hn
    rw [Equiv.symm_apply_apply] at hs
    simp only [V, hs, Bool.false_eq_true, if_false]
  have hWhead : ∀ v i, W (headSlot v i) = run.2 (slotIndex (headSlot v i)) := by
    intros; simp only [W, repair, head_ne_mirror, if_false, hVhead]
  have hWother : ∀ slot, (∀ v i, slot ≠ headSlot v i) → W slot = repaired U (slotIndex slot) := by
    intro slot hn
    simp only [W, repair, repaired, Equiv.symm_apply_apply]
    split_ifs with hm
    · exact hVother (mirrorSlot 0) (by intros; simp [mirrorSlot, headSlot])
    · exact hVother slot hn
  have hfields := tick_bits R base commands p input heFull.2.1
  dsimp only at hfields
  rw [htraj] at hfields
  have hpol : run.1.polarity = (PalPeg.LocalRoleFusion.logicalStep R change blankM p input).1.polarity :=
    hfields.1.trans hbits.1
  have hfl : run.1.fppLive = (PalPeg.LocalRoleFusion.logicalStep R change blankM p input).1.fppLive :=
    hfields.2.1.trans hbits.2.1
  have hdl : run.1.dpLive = (PalPeg.LocalRoleFusion.logicalStep R change blankM p input).1.dpLive :=
    hfields.2.2.trans hbits.2.2
  have hv : EncTapes margin y run.1.polarity run.1.gap run.1.micro run.1.fppLive run.1.dpLive W := by
    refine encTapes_replaceHeadsOfState hU.1.1.1.1.2 hfpp hdp hcounters hplaces hperiod hanswer
      hWother ?_ hpol hfl hdl ?_ ?_
    · intro v i
      rw [hWhead]
      exact margin_le_pos_headSlot (by decide : 2 ≤ microRadius) micro_le_margin (hcursor v) i
    · intro v head hh
      obtain ⟨view, vt, ha, hr, ht, hc, hw⟩ := hheads v head hh
      exact ⟨view, vt, ha, hr, ht, hc, hw⟩
    · intro _
      obtain ⟨view, vt, hr, ht, hc, hw⟩ := hcursor 3
      exact ⟨view, vt, hr, ht, hc, hw⟩
  have hfree := tickRule_headFree (by decide : 2 ≤ microRadius) base commands R.acts R.len_le p input heFull.2.1
  rw [htraj] at hfree
  have hcontrol : EncControl w y run.1 := encControl_congr hfree.symm hctl
  have hboundary := PalPeg.PhysicalBoundary.macroBoundary_of_heads base commands R.acts R.len_le
    p input heFull.2 (fun v => by
      obtain ⟨view, vt, hr, ht, hc, hw⟩ := PalPeg.PhysicalBoundary.all_heads_represented heFull.1.2 v
      exact ⟨view, vt, hr, fun i => by simpa only [repaired_head] using ht i, hc, hw⟩)
  rw [htraj] at hboundary
  have hshape : PalPeg.PhysicalWatchEntry.CounterShapes W := by
    intro c
    obtain ⟨raw, hr⟩ := hU.1.1.2 c
    exact ⟨raw, (hWother (counterSlot c) (by intros; simp [counterSlot, headSlot])).trans hr⟩
  have hcache' : Cache y (run.1.polarity 10) (W (counterSlot 10)) (W (mirrorSlot 5)) := by
    rw [hpol, hWother (counterSlot 10) (by intros; simp [counterSlot, headSlot]),
      hWother (mirrorSlot 5) (by intros; simp [mirrorSlot, headSlot])]
    exact hcache _ _ _ hU.1.2
  refine ⟨tapesOf V, ⟨⟨⟨⟨⟨hcontrol, ?_⟩, hboundary⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · simpa only [repaired_tapesOf] using hv
  · simpa only [repaired_tapesOf] using hshape
  · simpa only [PalPeg.PhysicalSpare.spareIndex, PalPeg.PhysicalPeriodMirror.mirrorIndex, repaired_tapesOf] using hcache'
  · obtain ⟨seg, hs, ht⟩ := hU.2
    refine ⟨seg, ?_, ?_⟩
    · rw [hpol, hcredit]
      exact hs
    · simp only [PalPeg.PhysicalDebtMirror.mirrorIndex, tapesOf_apply]
      exact (hVother (mirrorSlot 2) (by intros; simp [mirrorSlot, headSlot])).trans ht
  · intro j
    obtain ⟨slot, rfl⟩ := slotIndex.surjective j
    rw [tapesOf_apply]
    cases slot with
    | inl pair =>
      change TEqG blankM (V (.inl pair)) (run.2 (roles (slotIndex (.inl pair))))
      rw [show roles (slotIndex (.inl pair)) = slotIndex (.inl pair) from hroles pair.1 pair.2]
      exact ⟨rfl, fun _ => rfl⟩
    | inr rest =>
      have hn : (slotIndex.symm (slotIndex (.inr rest))).isLeft = false := by simp
      have hnr := nonhead_roles roles hroles _ hn
      have hrow := tickRule_otherSlots (by decide : 2 ≤ microRadius) base commands R.acts R.len_le
        p input heFull.2.1 (roles (slotIndex (.inr rest))) hnr
      rw [htraj] at hrow
      change TEqG blankM (U (slotIndex (.inr rest))) (run.2 (roles (slotIndex (.inr rest))))
      rw [hrow]
      exact hu (slotIndex (.inr rest))


theorem running_fused_route
    (R : ActRule (Fin 2) CoreControl Γm tapeCountM microRadius)
    (change : PalPeg.LocalRoleRouting.RoleChange (Fin 2) CoreControl Γm tapeCountM microRadius)
    (w : List (Fin 2)) (x y : State GalilVM)
    (p : PalPeg.LocalRoleRouting.Config CoreControl Γm tapeCountM) (input : Option (Fin 2))
    (he : Rebuilding w x (PalPeg.LocalRoleRouting.decode p))
    (hstep : ∀ T, RebuildingCore w x ((PalPeg.LocalRoleRouting.decode p).1, T) →
      let result := idealRun R blankM ((PalPeg.LocalRoleRouting.decode p).1, T) input 12
      Rebuilding w y (result.1, fun j => result.2
        (change (PalPeg.LocalRoleRouting.decode p).1 input (fun k => readWin blankM microRadius (T k)) j))) :
    Rebuilding w y (PalPeg.LocalRoleRouting.decode
      ((PalPeg.LocalRoleRouting.route (compStep (iterRule R 12)) (macroRoles change)).apply blankM p input)) := by
  let source := PalPeg.LocalRoleRouting.decode p
  obtain ⟨T, hT, ht⟩ := he
  have hm : ∀ j, macroRadius ≤ pos (T j) := by
    exact PalPeg.PhysicalDebtRebuild.core_margin w x (source.1, T) hT
  have hmp : ∀ j, macroRadius ≤ pos (source.2 j) := fun j => (ht j).1 ▸ hm j
  have hw : (fun j => readWin blankM microRadius (T j)) =
      (fun j => readWin blankM microRadius (source.2 j)) :=
    funext (fun j => readWin_congr_teqG (ht j))
  have hi := hstep T hT
  obtain ⟨hc, hteq⟩ := idealStep_congr_teqG (iterRule R 12) blankM source.1 T source.2 ht input
  rw [iterRule_ideal blankM R 12 (source.1, T) input hm, idealIter_eq_idealRun] at hc hteq
  obtain ⟨hr, hs⟩ := compStep_apply (iterRule R 12) blankM source input hmp
  rw [PalPeg.LocalRoleRouting.decode_route]
  change Rebuilding w y (((compStep (iterRule R 12)).apply blankM source input).1, fun j =>
    ((compStep (iterRule R 12)).apply blankM source input).2
      (macroRoles change source.1 input (fun k => readWin blankM macroRadius (source.2 k)) j))
  rw [macroRoles_read change source input hmp]
  dsimp only at hi
  rw [hw] at hi
  generalize hrun : idealRun R blankM (source.1, T) input 12 = run at hi hc hteq
  change Rebuilding w y (run.1, fun j => run.2
    (change source.1 input (fun k => readWin blankM microRadius (source.2 k)) j)) at hi
  apply PalPeg.MachineStep.sweepClosed_sweepClosure blankM (RebuildingCore w) _ _ _ hi
  · exact hc.trans hr.symm
  · intro j
    exact PalPeg.MachineStep.teqG_trans (hteq _) (hs _)

/-- info: 'PalPeg.PhysicalLoanAssembly.running_tick' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms running_tick

/-- info: 'PalPeg.PhysicalLoanAssembly.running_fused_route' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms running_fused_route

end PalPeg.PhysicalLoanAssembly
