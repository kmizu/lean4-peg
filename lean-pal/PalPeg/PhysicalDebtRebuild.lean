import PalPeg.PhysicalDebtMirror

/-! # Paying one search debt unit while rebuilding its borrowed radius mirror -/
set_option autoImplicit false
namespace PalPeg.PhysicalDebtRebuild
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract
open PalPeg.PhysicalDebtMirror (credit repair repaired mirrorIndex RebuildingCore Rebuilding)
open PalPeg.PhysicalCacheInvariant (CoreInv)
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilScaffoldCounter (Counter value Canonical inc negative)
open PalPeg.Program PalPeg.Local PalPeg.CloseoutCoreEnc12 PalPeg.LocalStepFusion
open PalPeg.LocalCounter (Seg absCtr push)

/-- One of grow's two debt increments, or double's single credit. -/
def paid (x : State GalilVM) : State GalilVM :=
  ⟨x.ctl, {x.vm with search := {x.vm.search with debt := inc x.vm.search.debt}}⟩

theorem credit_paid (x : State GalilVM) (hc : Canonical x.vm.search.debt)
    (hb : 0 ≤ value x.vm.radius + value x.vm.search.debt) :
    credit (paid x) = if negative x.vm.search.debt then inc (credit x) else credit x := by
  have h := PalPeg.PhysicalDebtMirror.credit_pay (value x.vm.radius) (value x.vm.search.debt) hb
  have hn := PalPeg.GalilScaffoldCounter.negative_iff x.vm.search.debt hc
  by_cases hd : negative x.vm.search.debt = true
  · rw [if_pos hd]
    apply PalPeg.ChainBoundaryCache.counter_eq_of_value
      (PalPeg.GalilScaffoldCounter.ofNat_canonical _)
      (PalPeg.GalilScaffoldCounter.inc_canonical _ (PalPeg.GalilScaffoldCounter.ofNat_canonical _))
    simp only [credit, paid, PalPeg.GalilScaffoldCounter.inc_value,
      PalPeg.GalilScaffoldCounter.ofNat_value]
    rw [if_pos (hn.mp hd)] at h
    exact_mod_cast h
  · rw [if_neg hd]
    apply congrArg PalPeg.GalilScaffoldCounter.ofNat
    change (value x.vm.radius + min (value (inc x.vm.search.debt)) 0).toNat = _
    rw [PalPeg.GalilScaffoldCounter.inc_value]
    simpa [if_neg (fun ht => hd (hn.mpr ht))] using h

noncomputable def output (T : Slot → STape Γm) (debt : STape Γm) (rebuild : Bool) : Slot → STape Γm :=
  Function.update (Function.update T (counterSlot 8) debt) (mirrorSlot 2)
    (if rebuild then (T (mirrorSlot 2)).applyAction blankM (encSeg PalPeg.LocalCounter.mark, .right) else T (mirrorSlot 2))

theorem repair_output (T : Slot → STape Γm) (debt : STape Γm) (rebuild : Bool) :
    repair (output T debt rebuild) = Function.update (repair T) (counterSlot 8) debt := by
  funext slot
  by_cases hc : slot = counterSlot 8
  · subst slot; simp [repair, output, counterSlot, mirrorSlot]
  · by_cases hm : slot = mirrorSlot 2
    · subst slot; simp [repair, output, counterSlot, mirrorSlot]
    · simp [repair, output, counterSlot, mirrorSlot, hc, hm]

theorem tapes_paid {x : State GalilVM} {q : CoreControl} {T : Slot → STape Γm}
    (he : EncTapes margin x q.polarity q.gap q.micro q.fppLive q.dpLive T)
    (bit : Bool) (seg : STape Seg) (ha : absCtr seg bit = inc x.vm.search.debt) :
    EncTapes margin (paid x) (Function.update q.polarity 8 bit) q.gap q.micro q.fppLive q.dpLive
      (Function.update T (counterSlot 8) (padLeft margin (mapTape encSeg seg))) := by
  apply encTapes_counterStep margin x (paid x) q.polarity (Function.update q.polarity 8 bit)
    q.gap q.micro q.fppLive q.dpLive T _ he 8 (inc x.vm.search.debt) rfl
    (fun c hc => by fin_cases c <;> first | rfl | contradiction)
    rfl rfl (fun _ => rfl) (fun _ => rfl) rfl rfl
    (fun c hc => Function.update_of_ne hc _ _) seg
  · exact ha
  · exact Function.update_self _ _ _
  · intro m hm; fin_cases m <;> cases hm
  · intro slot hs _; exact Function.update_of_ne hs _ _

/-- Only the debt sign changes. The actual missing mirror is not silently
completed: its push is checked against the credit equation. -/
theorem core_paid (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : RebuildingCore w x p) (hb : 0 ≤ value x.vm.radius + value x.vm.search.debt)
    (bit : Bool) (seg : STape Seg) (ha : absCtr seg bit = inc x.vm.search.debt) :
    RebuildingCore w (paid x)
      ({p.1 with polarity := Function.update p.1.polarity 8 bit},
        fun j => output (fun slot => p.2 (slotIndex slot)) (padLeft margin (mapTape encSeg seg))
          (negative x.vm.search.debt) (slotIndex.symm j)) := by
  obtain ⟨hbase, raw, hraw, hrawTape⟩ := he
  change p.2 (slotIndex (mirrorSlot 2)) = padLeft margin (mapTape encSeg raw) at hrawTape
  have hdebt : Canonical x.vm.search.debt := by
    obtain ⟨s, hs, _⟩ := hbase.1.1.1.2.counters 8 x.vm.search.debt rfl
    exact hs ▸ PalPeg.LocalCounter.absCtr_canonical s _
  have hcredit := credit_paid x hdebt hb
  let T := fun slot => p.2 (slotIndex slot)
  have hT : EncTapes margin x p.1.polarity p.1.gap p.1.micro p.1.fppLive p.1.dpLive (repair T) := by
    simpa only [repaired, Equiv.symm_apply_apply] using hbase.1.1.1.2
  have hshape : PalPeg.PhysicalWatchEntry.CounterShapes
      (Function.update (repair T) (counterSlot 8) (padLeft margin (mapTape encSeg seg))) := by
    intro c
    by_cases hc : c = 8
    · subst c; exact ⟨seg, Function.update_self _ _ _⟩
    · obtain ⟨s, hs⟩ := hbase.1.2 c
      refine ⟨s, ?_⟩
      rw [Function.update_of_ne (by simpa [counterSlot] using hc)]
      simpa only [repaired, T, Equiv.symm_apply_apply] using hs
  have hfull : CoreInv w (paid x)
      ({p.1 with polarity := Function.update p.1.polarity 8 bit}, fun j =>
        Function.update (repair T) (counterSlot 8) (padLeft margin (mapTape encSeg seg)) (slotIndex.symm j)) := by
    refine ⟨⟨⟨⟨?_, ?_⟩, hbase.1.1.2⟩, ?_⟩, ?_⟩
    · exact PalPeg.PhysicalFreeCounter.encControl_polarity
        (PalPeg.PhysicalRestartStorage.control_replace w x p.1 hbase.1.1.1.1
          x.vm.lower x.vm.search.span x.vm.search.work (inc x.vm.search.debt)) _
    · simpa only [Equiv.symm_apply_apply] using tapes_paid hT bit seg ha
    · simpa only [Equiv.symm_apply_apply] using hshape
    · simpa [PalPeg.PhysicalCacheInvariant.Cache, PalPeg.PhysicalCacheInvariant.mirrorMagnitude,
        paid, T, repaired, repair, PalPeg.PhysicalSpare.spareIndex,
        PalPeg.PhysicalPeriodMirror.mirrorIndex, counterSlot, mirrorSlot] using hbase.2
  refine ⟨?_, ?_⟩
  · have hrep : repaired (fun j => output T (padLeft margin (mapTape encSeg seg))
        (negative x.vm.search.debt) (slotIndex.symm j)) = (fun j =>
        Function.update (repair T) (counterSlot 8) (padLeft margin (mapTape encSeg seg)) (slotIndex.symm j)) := by
      funext j
      change repair (fun slot => output T _ _ (slotIndex.symm (slotIndex slot))) (slotIndex.symm j) = _
      simp only [Equiv.symm_apply_apply, repair_output]
    change CoreInv w (paid x) (_, repaired _)
    rw [hrep]
    exact hfull
  · by_cases hn : negative x.vm.search.debt = true
    · have hpos : p.1.polarity 2 = true := by
        have hd := (PalPeg.GalilScaffoldCounter.negative_iff _ hdebt).mp hn
        obtain ⟨r, hr, _⟩ := hbase.1.1.1.2.counters 2 x.vm.radius rfl
        have hv := congrArg value hr
        rw [PalPeg.LocalCounter.value_eq] at hv
        cases hp : p.1.polarity 2 <;> simp only [hp, Bool.false_eq_true, if_false, if_true] at hv ⊢ <;> omega
      refine ⟨push raw, ?_, ?_⟩
      · simp only [Function.update_of_ne (by decide : (2 : Fin 16) ≠ 8)]
        rw [hcredit, if_pos hn, hpos]
        rw [hpos] at hraw
        simpa [absCtr, PalPeg.LocalCounter.val_push, PalPeg.GalilScaffoldCounter.inc_ofNat] using
          congrArg inc hraw
      · simp only [mirrorIndex, Equiv.symm_apply_apply, output, Function.update_self, hn, if_true]
        rw [hrawTape]
        exact (padded_push margin raw).symm
    · refine ⟨raw, ?_, ?_⟩
      · simpa only [Function.update_of_ne (by decide : (2 : Fin 16) ≠ 8), hcredit, if_neg hn] using hraw
      · simpa only [mirrorIndex, Equiv.symm_apply_apply, output, Function.update_self, if_neg hn] using hrawTape

noncomputable def debtIndex : Fin tapeCountM := slotIndex (counterSlot 8)

noncomputable def compiled (q : CoreControl) (ws : Fin tapeCountM → Window Γm 32) :=
  PalPeg.PhysicalCounterCache.increments 1 (q.polarity 8) (ws debtIndex)

noncomputable def rule : ActRule (Fin 2) CoreControl Γm tapeCountM 32 where
  nq := fun q _ ws => {q with polarity := Function.update q.polarity 8 (compiled q ws).1}
  acts := fun q _ ws j =>
    if slotIndex.symm j = mirrorSlot 2 then
      if counterNegativeTest q ws 8 then [some (encSeg PalPeg.LocalCounter.mark, .right)] else []
    else if slotIndex.symm j = counterSlot 8 then (compiled q ws).2 else []
  len_le := by
    intro q input ws j
    split_ifs <;> simp [compiled, PalPeg.PhysicalCounterCache.increments_length]

noncomputable def step := compStep rule

theorem ideal_paid (p : CoreState) (input : Option (Fin 2)) :
    let ws := fun j => readWin blankM 32 (p.2 j)
    idealStep rule blankM p input =
      ({p.1 with polarity := Function.update p.1.polarity 8 (compiled p.1 ws).1},
        fun j => output (fun slot => p.2 (slotIndex slot))
          (actList blankM (p.2 debtIndex) (compiled p.1 ws).2)
          (counterNegativeTest p.1 ws 8) (slotIndex.symm j)) := by
  dsimp only
  apply Prod.ext
  · rfl
  · funext j
    by_cases hm : slotIndex.symm j = mirrorSlot 2
    · have hj : j = slotIndex (mirrorSlot 2) := by rw [← hm, Equiv.apply_symm_apply]
      subst j
      simp only [idealStep, rule, output, Equiv.symm_apply_apply, Function.update_self, if_true]
      split_ifs <;> rfl
    · by_cases hc : slotIndex.symm j = counterSlot 8
      · have hj : j = debtIndex := by rw [debtIndex, ← hc, Equiv.apply_symm_apply]
        subst j
        simp [idealStep, rule, output, debtIndex, counterSlot, mirrorSlot]
      · simp only [idealStep, rule, output, if_neg hm, if_neg hc,
          Function.update_of_ne hm, Function.update_of_ne hc, Equiv.apply_symm_apply]
        rfl

theorem negative_read (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : RebuildingCore w x p) :
    counterNegativeTest p.1 (fun j => readWin blankM 32 (p.2 j)) 8 = negative x.vm.search.debt := by
  have hn := counterNegativeTest_eq he.1.1.1.1.2 (K := 32) (by decide) (by decide) 8 x.vm.search.debt rfl
  simpa [counterNegativeTest, counterZeroTest, belowRead, tapesOf, repaired, repair,
    counterSlot, mirrorSlot] using hn

/-- The finite source-window rule preserves the full reconstruction invariant. -/
theorem core_ideal (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : RebuildingCore w x p) (hb : 0 ≤ value x.vm.radius + value x.vm.search.debt)
    (input : Option (Fin 2)) : RebuildingCore w (paid x) (idealStep rule blankM p input) := by
  obtain ⟨old, hold, ht⟩ := he.1.1.1.1.2.counters 8 x.vm.search.debt rfl
  have hdebt : p.2 debtIndex = padLeft margin (mapTape encSeg old) := by
    simpa [debtIndex, repaired, repair, counterSlot, mirrorSlot] using ht
  obtain ⟨seg, ha, hacts⟩ := PalPeg.PhysicalCounterCache.increments_encode (K := 32) (margin := margin)
    1 (by decide) (by decide) (p.1.polarity 8) old old x.vm.search.debt hold hold
  rw [← hdebt] at ha hacts
  have hpaid := core_paid w x p he hb
    (compiled p.1 (fun j => readWin blankM 32 (p.2 j))).1 seg ha
  rw [ideal_paid, negative_read w x p he]
  change RebuildingCore w (paid x) (_, fun j => output _
    (actList blankM (p.2 debtIndex) (PalPeg.PhysicalCounterCache.increments 1 (p.1.polarity 8)
      (readWin blankM 32 (p.2 debtIndex))).2) _ _)
  rw [hacts]
  exact hpaid

theorem core_margin (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : RebuildingCore w x p) (j : Fin tapeCountM) : margin ≤ pos (p.2 j) := by
  by_cases hj : j = mirrorIndex
  · obtain ⟨seg, _, ht⟩ := he.2
    rw [hj, ht, pos_padLeft]; omega
  · have hs : slotIndex.symm j ≠ mirrorSlot 2 := by
      intro hs
      apply hj
      rw [mirrorIndex, ← hs, Equiv.apply_symm_apply]
    simpa [repaired, repair, hs] using he.1.1.1.1.2.margins (slotIndex.symm j)

/-- Paying one unit and extending the partial mirror share the same real sweep. -/
theorem running (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : Rebuilding w x p) (hb : 0 ≤ value x.vm.radius + value x.vm.search.debt)
    (input : Option (Fin 2)) : Rebuilding w (paid x) (step.apply blankM p input) := by
  obtain ⟨T, hT, ht⟩ := he
  have hm : ∀ j, 32 ≤ pos (p.2 j) := by
    intro j
    rw [← (ht j).1]
    exact (show 32 ≤ margin by decide).trans (core_margin w x (p.1, T) hT j)
  obtain ⟨hcontrol, hacts⟩ := idealStep_congr_teqG rule blankM p.1 T p.2 ht input
  obtain ⟨hactual, hsweep⟩ := compStep_apply rule blankM p input hm
  refine ⟨(idealStep rule blankM (p.1, T) input).2, ?_,
    fun j => PalPeg.MachineStep.teqG_trans (hacts j) (hsweep j)⟩
  change RebuildingCore w (paid x) ((compStep rule).apply blankM p input |>.1, _)
  change rule.nq p.1 input (fun j => readWin blankM 32 (T j)) =
    rule.nq p.1 input (fun j => readWin blankM 32 (p.2 j)) at hcontrol
  rw [hactual, ← hcontrol]
  exact core_ideal w x (p.1, T) hT hb input

theorem borrowed_balance (x : State GalilVM) :
    0 ≤ value (PalPeg.PhysicalDebtMirror.borrowed x).vm.radius +
      value (PalPeg.PhysicalDebtMirror.borrowed x).vm.search.debt := by
  have h := PalPeg.GalilScaffoldSearchFinish.initial_balance x.vm.radius
  change 0 ≤ value x.vm.radius + value (PalPeg.GalilScaffoldSearchFinish.initialDebt x.vm.radius)
  omega

theorem paid_balance (x : State GalilVM) (hb : 0 ≤ value x.vm.radius + value x.vm.search.debt) :
    0 ≤ value (paid x).vm.radius + value (paid x).vm.search.debt := by
  change 0 ≤ value x.vm.radius + value (inc x.vm.search.debt)
  rw [PalPeg.GalilScaffoldCounter.inc_value]; omega

theorem sweep_margin (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : Rebuilding w x p) (j : Fin tapeCountM) : margin ≤ pos (p.2 j) := by
  obtain ⟨T, hT, ht⟩ := he
  rw [← (ht j).1]
  exact core_margin w x (p.1, T) hT j

theorem running_ideal (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : Rebuilding w x p) (hb : 0 ≤ value x.vm.radius + value x.vm.search.debt)
    (input : Option (Fin 2)) : Rebuilding w (paid x) (idealStep rule blankM p input) := by
  obtain ⟨T, hT, ht⟩ := he
  obtain ⟨hcontrol, hacts⟩ := idealStep_congr_teqG rule blankM p.1 T p.2 ht input
  refine ⟨(idealStep rule blankM (p.1, T) input).2, ?_, hacts⟩
  change RebuildingCore w (paid x) ((idealStep rule blankM (p.1, p.2) input).1, _)
  rw [← hcontrol]
  exact core_ideal w x (p.1, T) hT hb input

noncomputable def doubleRule := seqRule rule rule
noncomputable def doubleStep := compStep doubleRule

/-- Grow pays twice in the same micro row. The second sign test reads the
intermediate counter window, including the -1 -> 0 boundary. -/
theorem running_double (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : Rebuilding w x p) (hb : 0 ≤ value x.vm.radius + value x.vm.search.debt)
    (input : Option (Fin 2)) : Rebuilding w (paid (paid x)) (doubleStep.apply blankM p input) := by
  have hfirst := running_ideal w x p he hb input
  have hsecond := running_ideal w (paid x) _ hfirst (paid_balance x hb) none
  have hm : ∀ j, 32 + 32 ≤ pos (p.2 j) := fun j =>
    (show 32 + 32 ≤ margin by decide).trans (sweep_margin w x p he j)
  have hideal : Rebuilding w (paid (paid x)) (idealStep doubleRule blankM p input) := by
    rw [doubleRule, seqRule_ideal blankM rule rule p input hm]
    exact hsecond
  obtain ⟨hcontrol, htapes⟩ := compStep_apply doubleRule blankM p input hm
  exact PalPeg.MachineStep.sweepClosed_sweepClosure blankM (RebuildingCore w)
    _ _ _ hideal hcontrol.symm htapes

/-- info: 'PalPeg.PhysicalDebtRebuild.running' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms running

/-- info: 'PalPeg.PhysicalDebtRebuild.running_double' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms running_double

end PalPeg.PhysicalDebtRebuild
