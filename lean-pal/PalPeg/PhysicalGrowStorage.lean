import PalPeg.PhysicalLoanInvariant

/-! # Grow span/work row on the existing physical tape layout -/
set_option autoImplicit false
namespace PalPeg.PhysicalGrowStorage
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilScaffoldCounter (Counter inc dec reset)
open PalPeg.Program PalPeg.Local
open PalPeg.LocalCounter (Seg absCtr)
open PalPeg.CloseoutCoreEnc12 PalPeg.LocalStepFusion
variable {fb db : ℕ}

/-- Grow's span/work storage update. The two debt credits are fused later. -/
def prepared (x : State GalilVM) : State GalilVM :=
  ⟨x.ctl, {x.vm with search := {x.vm.search with span := PalPeg.ChainBoundaryCache.advanceCounter 8 x.vm.search.span, work := dec x.vm.search.work}}⟩

def enabled (c : Fin 16) : Bool := decide (c = 6 ∨ c = 7)
def valueAfter (c : Fin 16) (value : Counter) : Counter :=
  if c = 6 then PalPeg.ChainBoundaryCache.advanceCounter 8 value else if c = 7 then dec value else value

noncomputable def incs (q : QPhys fb db) (ws : Fin tapeCountM → Window Γm 32) :=
  PalPeg.PhysicalCounterCache.increments 8 (q.polarity 6) (ws (slotIndex (counterSlot 6)))
noncomputable def sign (q : QPhys fb db) (ws : Fin tapeCountM → Window Γm 32) (c : Fin 16) : Bool :=
  if c = 6 then (incs q ws).1 else if c = 7 then decSignAt (q.polarity c) (counterSlot c) ws else q.polarity c
noncomputable def counterActions (q : QPhys fb db) (ws : Fin tapeCountM → Window Γm 32)
    (c : Fin 16) : List (Act Γm) :=
  if c = 6 then (incs q ws).2 else if c = 7 then [decAct q c ws] else []

noncomputable def baseActions (q : QPhys fb db) (ws : Fin tapeCountM → Window Γm 32)
    (j : Fin tapeCountM) : List (Act Γm) :=
  match counterCarrier (slotIndex.symm j) with
  | some c => counterActions q ws c
  | none => []

noncomputable def next (q : QPhys fb db) (ws : Fin tapeCountM → Window Γm 32) : QPhys fb db :=
  {q with polarity := sign q ws}

noncomputable def rule : ActRule (Fin 2) (QPhys fb db) Γm tapeCountM 32 where
  nq := fun q _ ws => next q ws
  acts := fun q _ ws => withErase q.fppLive ws (baseActions q ws)
  len_le := by
    intro q input ws j
    apply withErase_length (b := 8) (by decide)
    intro k
    unfold baseActions
    split
    · unfold counterActions
      split_ifs <;> simp [incs, PalPeg.PhysicalCounterCache.increments_length]
    · simp

noncomputable def result (q : QPhys fb db) (T : Slot → STape Γm) :=
  idealStep rule blankM (q, tapesOf T) none

theorem counterOf_prepared (x : State GalilVM) (c : Fin 16) :
    counterOf (prepared x) c = (counterOf x c).map (valueAfter c) := by
  fin_cases c <;> cases hc : x.vm.chain <;> simp [prepared, counterOf, valueAfter, hc]

theorem enabled_value (x : State GalilVM) (c : Fin 16) (hc : enabled c = true) :
    ∃ value, counterOf x c = some value := by
  simp only [enabled, decide_eq_true_eq] at hc
  rcases hc with rfl | rfl <;> exact ⟨_, rfl⟩

theorem carrier_actions (q : QPhys fb db) (ws : Fin tapeCountM → Window Γm 32)
    (slot : Slot) (c : Fin 16) (hc : counterCarrier slot = some c) :
    rule.acts q none ws (slotIndex slot) = counterActions q ws c := by
  change withErase q.fppLive ws (baseActions q ws) (slotIndex slot) = _
  rw [withErase_at_other q.fppLive ws _ slot (by
    intro i hi; rw [hi, counterCarrier_prog] at hc; contradiction)]
  simp only [baseActions, Equiv.symm_apply_apply, hc]

theorem kept (q : QPhys fb db) (T : Slot → STape Γm) (slot : Slot)
    (hc : counterCarrier slot = none)
    (hr : ∀ i, slot ≠ progSlotOf (!q.fppLive) i) :
    (result q T).2 (slotIndex slot) = T slot := by
  change actList blankM (tapesOf T (slotIndex slot))
    (withErase q.fppLive _ (baseActions q _) (slotIndex slot)) = _
  rw [withErase_at_other q.fppLive _ _ slot hr]
  simp [baseActions, hc, tapesOf]

theorem counter_tape {margin : ℕ} (hpad : 32 ≤ margin)
    (q : QPhys fb db) (T : Slot → STape Γm)
    (slot : Slot) (c : Fin 16) (hc : counterCarrier slot = some c)
    (source segments : STape Seg) (value : Counter)
    (hs : absCtr source (q.polarity c) = value) (ha : absCtr segments (q.polarity c) = value)
    (hst : T (counterSlot c) = padLeft margin (mapTape encSeg source))
    (ht : T slot = padLeft margin (mapTape encSeg segments)) :
    ∃ raw : STape Seg, absCtr raw ((result q T).1.polarity c) = valueAfter c value ∧
      (result q T).2 (slotIndex slot) = padLeft margin (mapTape encSeg raw) := by
  change ∃ raw, absCtr raw (sign q _ c) = _ ∧ actList blankM (tapesOf T (slotIndex slot))
    (rule.acts q none _ (slotIndex slot)) = _
  rw [carrier_actions q _ slot c hc, tapesOf_apply]
  by_cases hc6 : c = 6
  · subst c
    simp only [sign, valueAfter, counterActions, if_true, incs, tapesOf_apply, hst, ht]
    exact PalPeg.PhysicalCounterCache.increments_encode 8 (by decide) hpad _ source segments value hs ha
  by_cases hc7 : c = 7
  · simp only [sign, valueAfter, counterActions, if_neg hc6, if_pos hc7, decAct, decActAt]
    apply counter_dec_at q.polarity c _ segments value ha _ (T slot) ht
    rw [val_eq_of_absCtr_eq (ha.trans hs.symm)]
    exact decSignAt_eq (by decide) (by omega) (q.polarity c) c T source hst
  · simp only [sign, valueAfter, counterActions, if_neg hc6, if_neg hc7]
    exact ⟨segments, ha, ht⟩

theorem carrier_tape {margin : ℕ} (hpad : 32 ≤ margin)
    (x : State GalilVM) (q : QPhys fb db) (T : Slot → STape Γm)
    (he : EncTapes margin x q.polarity q.gap q.micro q.fppLive q.dpLive T)
    (slot : Slot) (c : Fin 16) (hc : counterCarrier slot = some c)
    (value : Counter) (hv : counterOf x c = some value) :
    ∃ raw : STape Seg, absCtr raw ((result q T).1.polarity c) = valueAfter c value ∧
      (result q T).2 (slotIndex slot) = padLeft margin (mapTape encSeg raw) := by
  obtain ⟨source, hs, hst⟩ := he.counters c value hv
  obtain ⟨segments, ha, ht⟩ := counterCarrier_rep he slot c hc value hv
  exact counter_tape hpad q T slot c hc source segments value hs ha hst ht

theorem idle_tapes {margin : ℕ} (hpad : 32 ≤ margin)
    (x : State GalilVM) (q : QPhys fb db) (T : Slot → STape Γm)
    (he : EncTapes margin x q.polarity q.gap q.micro q.fppLive q.dpLive T) (i : Fin 9) :
    ∃ raw : STape (Fin 9), (result q T).2 (slotIndex (progSlotOf (!q.fppLive) i)) =
      padLeft margin (mapTape encProg raw) := by
  simpa only [result, idealStep, rule, tapesOf_apply] using
    idle_shape_withErase margin (by decide : 1 ≤ 32) (by omega) T q.fppLive (baseActions q _)
      (fun k => by simp [baseActions]) he.idleShape i

theorem kept_counter (q : QPhys fb db) (T : Slot → STape Γm)
    (slot : Slot) (c : Fin 16) (hc : counterCarrier slot = some c) (hn : enabled c = false) :
    (result q T).2 (slotIndex slot) = T slot := by
  have hn' : ¬ (c = 6 ∨ c = 7) := by simpa [enabled] using hn
  change actList blankM (tapesOf T (slotIndex slot)) (rule.acts q none _ (slotIndex slot)) = _
  rw [carrier_actions q _ slot c hc, tapesOf_apply]
  simp only [counterActions, if_neg (show c ≠ 6 from by tauto), if_neg (show c ≠ 7 from by tauto), actList]

theorem encControl_prepared (w : List (Fin 2)) (x : State GalilVM)
    (q : QPhys fb db) (T : Slot → STape Γm) (he : EncControl w x q) :
    EncControl w (prepared x) (result q T).1 := by
  exact ⟨he.ctl, he.chainTag, he.chainPhase, he.chainForward, he.chainBroken,
    he.fppMode, he.fppFinalStage, he.fppPc, he.fppDone, he.dpPc, he.dpDone,
    he.searchMode, he.searchFinalStage, he.searchQuarter, he.periodOnly,
    he.placeGap, he.onLetter, he.leftFirst⟩

/-- The span mirror receives the same eight increments, including sign changes.
Other carriers and the retired FPP background eraser retain their contracts. -/
theorem tapes_prepared {margin : ℕ} (hpad : 32 ≤ margin)
    (x : State GalilVM) (q : QPhys fb db) (T : Slot → STape Γm)
    (he : EncTapes margin x q.polarity q.gap q.micro q.fppLive q.dpLive T) :
    EncTapes margin (prepared x) (result q T).1.polarity q.gap q.micro q.fppLive q.dpLive
      (fun slot => (result q T).2 (slotIndex slot)) := by
  have hret := idle_tapes hpad x q T he
  have hheads : headOf (prepared x) = headOf x := by
    funext v; fin_cases v <;> rfl
  have hheadTape : ∀ v i, (result q T).2 (slotIndex (headSlot v i)) = T (headSlot v i) := by
    intro v i
    exact kept q T _ rfl (by intro k; cases q.fppLive <;> simp [headSlot, progSlotOf])
  have hcounter : ∀ slot c, counterCarrier slot = some c → ∀ value,
      counterOf (prepared x) c = some value →
      ∃ raw : STape Seg, absCtr raw ((result q T).1.polarity c) = value ∧
        (result q T).2 (slotIndex slot) = padLeft margin (mapTape encSeg raw) := by
    intro slot c hc value hv
    rw [counterOf_prepared] at hv
    cases hsource : counterOf x c with
    | none => simp [hsource] at hv
    | some source =>
      have hvalue : valueAfter c source = value := by simpa [hsource] using hv
      rw [← hvalue]
      exact carrier_tape hpad x q T he slot c hc source hsource
  refine ⟨?_, ?_, ?_, ?_, ?_, hret, ?_, ?_, ?_, ?_, ?_⟩
  · intro slot
    by_cases hr : ∃ i, slot = progSlotOf (!q.fppLive) i
    · obtain ⟨i, rfl⟩ := hr
      obtain ⟨raw, ht⟩ := hret i
      rw [ht, pos_padLeft]; omega
    have hnot : ∀ i, slot ≠ progSlotOf (!q.fppLive) i := fun i hi => hr ⟨i, hi⟩
    cases hc : counterCarrier slot with
    | none => rw [kept q T slot hc hnot]; exact he.margins slot
    | some c =>
      cases hen : enabled c with
      | false => rw [kept_counter q T slot c hc hen]; exact he.margins slot
      | true =>
        obtain ⟨value, hv⟩ := enabled_value x c hen
        obtain ⟨raw, _, ht⟩ := carrier_tape hpad x q T he slot c hc value hv
        rw [ht, pos_padLeft]; omega
  · intro v head hh
    rw [hheads] at hh
    obtain ⟨view, vt, ha, hv, hs, hc, hw⟩ := he.heads v head hh
    exact ⟨view, vt, ha, hv, fun i => (hheadTape v i).trans (hs i), hc, hw⟩
  · intro hh
    rw [hheads] at hh
    obtain ⟨view, vt, hv, hs, hc, hw⟩ := he.idleHead hh
    exact ⟨view, vt, hv, fun i => (hheadTape 3 i).trans (hs i), hc, hw⟩
  · intro i
    rw [kept q T _ (counterCarrier_prog _ _) (fun k => progSlotOf_ne_flip q.fppLive i k)]
    exact he.fpp i
  · intro i
    rw [kept q T _ (counterCarrier_dp _ _) (by
      intro k; cases q.dpLive <;> cases q.fppLive <;> simp [dpSlotOf, progSlotOf])]
    exact he.dp i
  · intro c value hv
    exact hcounter (counterSlot c) c rfl value hv
  · intro i place hp
    obtain ⟨raw, junk, hj, hr, ht⟩ := he.places i place hp
    refine ⟨raw, junk, hj, hr, ?_⟩
    rw [kept q T (placeSlot i) rfl (by intro k; cases q.fppLive <;> simp [placeSlot, progSlotOf])]
    exact ht
  · intro m value hv
    exact hcounter (mirrorSlot m) (mirrorSource m) rfl value hv
  · intro tape hp
    rw [kept q T periodSlot rfl (by intro k; cases q.fppLive <;> simp [periodSlot, progSlotOf])]
    exact he.period tape hp
  · intro tape ha
    rw [kept q T _ counterCarrier_answer (by intro k; cases q.fppLive <;> simp [progSlotOf])]
    exact he.answer tape ha

theorem core_prepared (w : List (Fin 2)) (x : State GalilVM)
    (p : CoreState) (he : CoreEnc w x p) :
    CoreEnc w (prepared x) (idealStep rule blankM p none) := by
  let T := fun slot => p.2 (slotIndex slot)
  have ht : tapesOf T = p.2 := by funext j; simp [T, tapesOf]
  have hh : PalPeg.PhysicalEncoding.Enc w margin (prepared x)
      ((result p.1 T).1, fun slot => (result p.1 T).2 (slotIndex slot)) :=
    ⟨encControl_prepared w x p.1 T he.1.1, tapes_prepared (by decide) x p.1 T he.1.2⟩
  dsimp only [result] at hh
  rw [ht] at hh
  exact ⟨hh, he.2⟩

/-- The common row also preserves the inactive counter shapes. -/
theorem shapes_prepared (w : List (Fin 2)) (x : State GalilVM)
    (p : CoreState) (he : PalPeg.PhysicalWatchEntry.ShapedCoreEnc w x p) :
    PalPeg.PhysicalWatchEntry.ShapedCoreEnc w (prepared x) (idealStep rule blankM p none) := by
  refine ⟨core_prepared w x p he.1, ?_⟩
  let T := fun slot => p.2 (slotIndex slot)
  have ht : tapesOf T = p.2 := by funext j; simp [T, tapesOf]
  intro c
  change ∃ raw, (idealStep rule blankM (p.1, p.2) none).2 (slotIndex (counterSlot c)) = _
  rw [← ht]
  cases hc : enabled c with
  | false =>
    change ∃ raw, (result p.1 T).2 (slotIndex (counterSlot c)) = _
    rw [kept_counter p.1 T _ c rfl hc]
    exact he.2 c
  | true =>
    obtain ⟨value, hv⟩ := enabled_value x c hc
    obtain ⟨raw, _, hr⟩ := carrier_tape (by decide : 32 ≤ margin) x p.1 T he.1.1.2 (counterSlot c) c rfl value hv
    exact ⟨raw, hr⟩

theorem invariant_prepared (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : PalPeg.PhysicalCacheInvariant.CoreInv w x p) :
    PalPeg.PhysicalCacheInvariant.CoreInv w (prepared x) (idealStep rule blankM p none) := by
  refine ⟨shapes_prepared w x p he.1, ?_⟩
  let T := fun slot => p.2 (slotIndex slot)
  have ht : tapesOf T = p.2 := by funext j; simp [T, tapesOf]
  have hs := kept_counter p.1 T (counterSlot 10) 10 rfl (by decide)
  have hm := kept_counter p.1 T (mirrorSlot 5) 10 rfl (by decide)
  dsimp only [result] at hs hm
  rw [ht] at hs hm
  change PalPeg.PhysicalCacheInvariant.Cache (prepared x) (sign p.1 (fun j => readWin blankM 32 (p.2 j)) 10)
    ((idealStep rule blankM p none).2 (slotIndex (counterSlot 10)))
    ((idealStep rule blankM p none).2 (slotIndex (mirrorSlot 5)))
  rw [hs, hm]
  simpa [PalPeg.PhysicalCacheInvariant.Cache, PalPeg.PhysicalCacheInvariant.mirrorMagnitude,
    prepared, sign, T, PalPeg.PhysicalSpare.spareIndex, PalPeg.PhysicalPeriodMirror.mirrorIndex] using he.2


open PalPeg.PhysicalDebtMirror (repaired repair mirrorIndex RebuildingCore Rebuilding credit)

theorem sign_repaired (q : CoreControl) (T : Fin tapeCountM → STape Γm) :
    sign q (fun j => readWin blankM 32 (repaired T j)) = sign q (fun j => readWin blankM 32 (T j)) := by
  funext c
  unfold sign
  split_ifs with hc6 hc7
  · simp [incs, repaired, repair, counterSlot, mirrorSlot]
  · subst c; simp [decSignAt, belowRead, repaired, repair, counterSlot, mirrorSlot] <;> rfl
  · rfl

theorem actions_repaired (q : CoreControl) (T : Fin tapeCountM → STape Γm)
    (j : Fin tapeCountM) :
    rule.acts q none (fun k => readWin blankM 32 (repaired T k)) j =
      rule.acts q none (fun k => readWin blankM 32 (T k)) j := by
  change withErase _ _ _ j = withErase _ _ _ j
  unfold withErase
  apply congrArg₂ List.append
  · unfold baseActions
    split
    · unfold counterActions
      split_ifs with hc6 hc7
      · simp [incs, repaired, repair, counterSlot, mirrorSlot]
      · subst hc7
        simp [decAct, decActAt, decSignAt, belowRead, repaired, repair, counterSlot, mirrorSlot] <;> rfl
      · rfl
    · rfl
  · unfold eraseOf
    split_ifs with he
    · obtain ⟨i, rfl⟩ := he
      cases q.fppLive <;> simp [eraseAct, repaired, repair, progSlotOf, mirrorSlot]
    · rfl

theorem radius_mirror_actions (q : CoreControl) (ws : Fin tapeCountM → Window Γm 32)
    (m : Fin 7) (hm : mirrorSource m = 2) : rule.acts q none ws (slotIndex (mirrorSlot m)) = [] := by
  rw [carrier_actions q ws (mirrorSlot m) (mirrorSource m) rfl, hm]
  simp [counterActions]

theorem step_complete (p : CoreState) :
    idealStep rule blankM (p.1, repaired p.2) none =
      ((idealStep rule blankM p none).1, repaired (idealStep rule blankM p none).2) := by
  apply Prod.ext
  · exact congrArg (fun pol => {p.1 with polarity := pol}) (sign_repaired p.1 p.2)
  · funext j
    change actList blankM (repaired p.2 j) (rule.acts _ none _ j) = _
    rw [actions_repaired]
    by_cases hj : j = mirrorIndex
    · subst j
      simp [repaired, repair, mirrorIndex, idealStep, radius_mirror_actions, mirrorSlot, mirrorSource]
    · have hn : slotIndex.symm j ≠ mirrorSlot 2 := by
        intro h
        apply hj
        rw [mirrorIndex, ← h, Equiv.apply_symm_apply]
      simp [repaired, repair, idealStep, hn]

theorem rebuilding_core (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : RebuildingCore w x p) : RebuildingCore w (prepared x) (idealStep rule blankM p none) := by
  have hf := invariant_prepared w x (p.1, repaired p.2) he.1
  rw [step_complete] at hf
  refine ⟨hf, ?_⟩
  obtain ⟨seg, ha, ht⟩ := he.2
  refine ⟨seg, ?_, ?_⟩
  · simpa [idealStep, rule, next, sign, credit, prepared] using ha
  · change actList blankM _ (rule.acts _ none _ (slotIndex (mirrorSlot 2))) = _
    rw [radius_mirror_actions _ _ 2 rfl]
    exact ht

/-- On a swept representation this remains an ideal row, for fusion with the
two debt credits in the same physical step. -/
theorem rebuilding_ideal (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : Rebuilding w x p) : Rebuilding w (prepared x) (idealStep rule blankM p none) := by
  obtain ⟨T, hT, ht⟩ := he
  obtain ⟨hc, ha⟩ := idealStep_congr_teqG rule blankM p.1 T p.2 ht none
  refine ⟨(idealStep rule blankM (p.1, T) none).2, ?_, ha⟩
  change RebuildingCore w (prepared x) ((idealStep rule blankM p none).1, _)
  rw [← hc]
  exact rebuilding_core w x (p.1, T) hT

/-- info: 'PalPeg.PhysicalGrowStorage.rebuilding_ideal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rebuilding_ideal

end PalPeg.PhysicalGrowStorage
