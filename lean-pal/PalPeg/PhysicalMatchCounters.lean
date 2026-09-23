import PalPeg.PhysicalGrowCount

/-! # Matched search counters with a rebuilding radius mirror -/
set_option autoImplicit false
namespace PalPeg.PhysicalMatchCounters
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilScaffoldCounter (Counter inc dec reset)
open PalPeg.Program PalPeg.Local
open PalPeg.LocalCounter (Seg absCtr)
open PalPeg.CloseoutCoreEnc12 PalPeg.LocalStepFusion
variable {fb db : ℕ}
variable (cyc rep : Bool)

/-- The common matched counters. Heads and finite output control are assembled separately. -/
def prepared (x : State GalilVM) : State GalilVM :=
  ⟨x.ctl, {x.vm with radius := inc x.vm.radius, length := inc (inc x.vm.length), cycle := if cyc then dec x.vm.cycle else x.vm.cycle, replay := if rep then dec x.vm.replay else x.vm.replay, search := {x.vm.search with debt := dec x.vm.search.debt}}⟩

def debit (c : Fin 16) : Bool := decide (c = 8) || (cyc && decide (c = 0)) || (rep && decide (c = 4))
def enabled (c : Fin 16) : Bool := decide (c = 2 ∨ c = 3) || (debit cyc rep) c
def valueAfter (c : Fin 16) (value : Counter) : Counter :=
  if c = 2 then inc value else if c = 3 then inc (inc value) else if (debit cyc rep) c then dec value else value

noncomputable def sign (q : QPhys fb db) (ws : Fin tapeCountM → Window Γm 32) (c : Fin 16) : Bool :=
  if c = 2 then incSign q.polarity c ws else if c = 3 then incTwiceSign q c ws
  else if (debit cyc rep) c then decSignAt (q.polarity c) (counterSlot c) ws else q.polarity c
noncomputable def counterActions (q : QPhys fb db) (ws : Fin tapeCountM → Window Γm 32)
    (c : Fin 16) : List (Act Γm) :=
  if c = 2 then [incAct q c ws] else if c = 3 then incTwiceActs q c ws
  else if (debit cyc rep) c then [decAct q c ws] else []

noncomputable def baseActions (q : QPhys fb db) (ws : Fin tapeCountM → Window Γm 32)
    (j : Fin tapeCountM) : List (Act Γm) :=
  match counterCarrier (slotIndex.symm j) with
  | some c => (counterActions cyc rep) q ws c
  | none => []

noncomputable def next (q : QPhys fb db) (ws : Fin tapeCountM → Window Γm 32) : QPhys fb db :=
  {q with polarity := (sign cyc rep) q ws}

noncomputable def rule : ActRule (Fin 2) (QPhys fb db) Γm tapeCountM 32 where
  nq := fun q _ ws => (next cyc rep) q ws
  acts := fun q _ ws => (baseActions cyc rep) q ws
  len_le := by
    intro q input ws j
    unfold baseActions
    split
    · unfold counterActions
      split_ifs <;> simp [incTwiceActs_length]
    · simp

noncomputable def result (q : QPhys fb db) (T : Slot → STape Γm) :=
  idealStep (rule cyc rep) blankM (q, tapesOf T) none

theorem counterOf_prepared (x : State GalilVM) (c : Fin 16) :
    counterOf ((prepared cyc rep) x) c = (counterOf x c).map ((valueAfter cyc rep) c) := by
  fin_cases c <;> cases hc : x.vm.chain <;> cases cyc <;> cases rep <;> simp [prepared, counterOf, valueAfter, debit, hc]

theorem enabled_value (x : State GalilVM) (c : Fin 16) (hc : (enabled cyc rep) c = true) :
    ∃ value, counterOf x c = some value := by
  fin_cases c <;> first | exact ⟨_, rfl⟩ | simp [enabled, debit] at hc

theorem carrier_actions (q : QPhys fb db) (ws : Fin tapeCountM → Window Γm 32)
    (slot : Slot) (c : Fin 16) (hc : counterCarrier slot = some c) :
    (rule cyc rep).acts q none ws (slotIndex slot) = (counterActions cyc rep) q ws c := by
  simp only [rule, baseActions, Equiv.symm_apply_apply, hc]

theorem kept (q : QPhys fb db) (T : Slot → STape Γm) (slot : Slot)
    (hc : counterCarrier slot = none) :
    ((result cyc rep) q T).2 (slotIndex slot) = T slot := by
  change actList blankM (tapesOf T (slotIndex slot)) ((baseActions cyc rep) q _ (slotIndex slot)) = _
  simp [baseActions, hc, tapesOf]

theorem counter_tape {margin : ℕ} (hpad : 32 ≤ margin)
    (q : QPhys fb db) (T : Slot → STape Γm)
    (slot : Slot) (c : Fin 16) (hc : counterCarrier slot = some c)
    (source segments : STape Seg) (value : Counter)
    (hs : absCtr source (q.polarity c) = value) (ha : absCtr segments (q.polarity c) = value)
    (hst : T (counterSlot c) = padLeft margin (mapTape encSeg source))
    (ht : T slot = padLeft margin (mapTape encSeg segments)) :
    ∃ raw : STape Seg, absCtr raw (((result cyc rep) q T).1.polarity c) = (valueAfter cyc rep) c value ∧
      ((result cyc rep) q T).2 (slotIndex slot) = padLeft margin (mapTape encSeg raw) := by
  change ∃ raw, absCtr raw ((sign cyc rep) q _ c) = _ ∧ actList blankM (tapesOf T (slotIndex slot))
    ((rule cyc rep).acts q none _ (slotIndex slot)) = _
  rw [(carrier_actions cyc rep) q _ slot c hc, tapesOf_apply]
  by_cases hr : c = 2
  · simp only [sign, valueAfter, counterActions, if_pos hr]
    apply counter_inc_at q.polarity c _ segments value ha _ (T slot) ht
    rw [val_eq_of_absCtr_eq (ha.trans hs.symm)]
    exact incSign_eq (by decide) (by omega) q.polarity c T source hst
  by_cases hl : c = 3
  · simp only [sign, valueAfter, counterActions, if_neg hr, if_pos hl]
    exact counter_incTwice_at q c T (by decide) hpad source segments value hs ha hst (T slot) ht
  by_cases hd : (debit cyc rep) c = true
  · simp only [sign, valueAfter, counterActions, if_neg hr, if_neg hl, if_pos hd, decAct, decActAt]
    apply counter_dec_at q.polarity c _ segments value ha _ (T slot) ht
    rw [val_eq_of_absCtr_eq (ha.trans hs.symm)]
    exact decSignAt_eq (by decide) (by omega) (q.polarity c) c T source hst
  · simp only [sign, valueAfter, counterActions, if_neg hr, if_neg hl, if_neg hd]
    exact ⟨segments, ha, ht⟩

theorem carrier_tape {margin : ℕ} (hpad : 32 ≤ margin)
    (x : State GalilVM) (q : QPhys fb db) (T : Slot → STape Γm)
    (he : EncTapes margin x q.polarity q.gap q.micro q.fppLive q.dpLive T)
    (slot : Slot) (c : Fin 16) (hc : counterCarrier slot = some c)
    (value : Counter) (hv : counterOf x c = some value) :
    ∃ raw : STape Seg, absCtr raw (((result cyc rep) q T).1.polarity c) = (valueAfter cyc rep) c value ∧
      ((result cyc rep) q T).2 (slotIndex slot) = padLeft margin (mapTape encSeg raw) := by
  obtain ⟨source, hs, hst⟩ := he.counters c value hv
  obtain ⟨segments, ha, ht⟩ := counterCarrier_rep he slot c hc value hv
  exact (counter_tape cyc rep) hpad q T slot c hc source segments value hs ha hst ht

theorem idle_tapes {margin : ℕ} (hpad : 32 ≤ margin)
    (x : State GalilVM) (q : QPhys fb db) (T : Slot → STape Γm)
    (he : EncTapes margin x q.polarity q.gap q.micro q.fppLive q.dpLive T) (i : Fin 9) :
    ∃ raw : STape (Fin 9), ((result cyc rep) q T).2 (slotIndex (progSlotOf (!q.fppLive) i)) =
      padLeft margin (mapTape encProg raw) := by
  obtain ⟨raw, ht⟩ := he.idleShape i
  exact ⟨raw, ((kept cyc rep) q T _ (counterCarrier_prog _ _)).trans ht⟩

theorem kept_counter (q : QPhys fb db) (T : Slot → STape Γm)
    (slot : Slot) (c : Fin 16) (hc : counterCarrier slot = some c) (hn : (enabled cyc rep) c = false) :
    ((result cyc rep) q T).2 (slotIndex slot) = T slot := by
  have hn' : c ≠ 2 ∧ c ≠ 3 ∧ (debit cyc rep) c = false := by simpa [enabled, not_or, and_assoc] using hn
  change actList blankM (tapesOf T (slotIndex slot)) ((rule cyc rep).acts q none _ (slotIndex slot)) = _
  rw [(carrier_actions cyc rep) q _ slot c hc, tapesOf_apply]
  simp only [counterActions, if_neg hn'.1, if_neg hn'.2.1, hn'.2.2, Bool.false_eq_true, if_false, actList]

theorem encControl_prepared (w : List (Fin 2)) (x : State GalilVM)
    (q : QPhys fb db) (T : Slot → STape Γm) (he : EncControl w x q) :
    EncControl w ((prepared cyc rep) x) ((result cyc rep) q T).1 := by
  exact ⟨he.ctl, he.chainTag, he.chainPhase, he.chainForward, he.chainBroken,
    he.fppMode, he.fppFinalStage, he.fppPc, he.fppDone, he.dpPc, he.dpDone,
    he.searchMode, he.searchFinalStage, he.searchQuarter, he.periodOnly,
    he.placeGap, he.onLetter, he.leftFirst⟩

/-- Full-radius reference rule; the actual partial-mirror row is proved below. -/
theorem tapes_prepared {margin : ℕ} (hpad : 32 ≤ margin)
    (x : State GalilVM) (q : QPhys fb db) (T : Slot → STape Γm)
    (he : EncTapes margin x q.polarity q.gap q.micro q.fppLive q.dpLive T) :
    EncTapes margin ((prepared cyc rep) x) ((result cyc rep) q T).1.polarity q.gap q.micro q.fppLive q.dpLive
      (fun slot => ((result cyc rep) q T).2 (slotIndex slot)) := by
  have hret := (idle_tapes cyc rep) hpad x q T he
  have hheads : headOf ((prepared cyc rep) x) = headOf x := by
    funext v; fin_cases v <;> rfl
  have hheadTape : ∀ v i, ((result cyc rep) q T).2 (slotIndex (headSlot v i)) = T (headSlot v i) := by
    intro v i
    exact (kept cyc rep) q T _ rfl
  have hcounter : ∀ slot c, counterCarrier slot = some c → ∀ value,
      counterOf ((prepared cyc rep) x) c = some value →
      ∃ raw : STape Seg, absCtr raw (((result cyc rep) q T).1.polarity c) = value ∧
        ((result cyc rep) q T).2 (slotIndex slot) = padLeft margin (mapTape encSeg raw) := by
    intro slot c hc value hv
    rw [(counterOf_prepared cyc rep)] at hv
    cases hsource : counterOf x c with
    | none => simp [hsource] at hv
    | some source =>
      have hvalue : (valueAfter cyc rep) c source = value := by simpa [hsource] using hv
      rw [← hvalue]
      exact (carrier_tape cyc rep) hpad x q T he slot c hc source hsource
  refine ⟨?_, ?_, ?_, ?_, ?_, hret, ?_, ?_, ?_, ?_, ?_⟩
  · intro slot
    by_cases hr : ∃ i, slot = progSlotOf (!q.fppLive) i
    · obtain ⟨i, rfl⟩ := hr
      obtain ⟨raw, ht⟩ := hret i
      rw [ht, pos_padLeft]; omega
    have hnot : ∀ i, slot ≠ progSlotOf (!q.fppLive) i := fun i hi => hr ⟨i, hi⟩
    cases hc : counterCarrier slot with
    | none => rw [(kept cyc rep) q T slot hc]; exact he.margins slot
    | some c =>
      cases hen : (enabled cyc rep) c with
      | false => rw [(kept_counter cyc rep) q T slot c hc hen]; exact he.margins slot
      | true =>
        obtain ⟨value, hv⟩ := (enabled_value cyc rep) x c hen
        obtain ⟨raw, _, ht⟩ := (carrier_tape cyc rep) hpad x q T he slot c hc value hv
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
    rw [(kept cyc rep) q T _ (counterCarrier_prog _ _)]
    exact he.fpp i
  · intro i
    rw [(kept cyc rep) q T _ (counterCarrier_dp _ _)]
    exact he.dp i
  · intro c value hv
    exact hcounter (counterSlot c) c rfl value hv
  · intro i place hp
    obtain ⟨raw, junk, hj, hr, ht⟩ := he.places i place hp
    refine ⟨raw, junk, hj, hr, ?_⟩
    rw [(kept cyc rep) q T (placeSlot i) rfl]
    exact ht
  · intro m value hv
    exact hcounter (mirrorSlot m) (mirrorSource m) rfl value hv
  · intro tape hp
    rw [(kept cyc rep) q T periodSlot rfl]
    exact he.period tape hp
  · intro tape ha
    rw [(kept cyc rep) q T _ counterCarrier_answer]
    exact he.answer tape ha

theorem core_prepared (w : List (Fin 2)) (x : State GalilVM)
    (p : CoreState) (he : CoreEnc w x p) :
    CoreEnc w ((prepared cyc rep) x) (idealStep (rule cyc rep) blankM p none) := by
  let T := fun slot => p.2 (slotIndex slot)
  have ht : tapesOf T = p.2 := by funext j; simp [T, tapesOf]
  have hh : PalPeg.PhysicalEncoding.Enc w margin ((prepared cyc rep) x)
      (((result cyc rep) p.1 T).1, fun slot => ((result cyc rep) p.1 T).2 (slotIndex slot)) :=
    ⟨(encControl_prepared cyc rep) w x p.1 T he.1.1, (tapes_prepared cyc rep) (by decide) x p.1 T he.1.2⟩
  dsimp only [result] at hh
  rw [ht] at hh
  exact ⟨hh, he.2⟩

/-- The common row also preserves the inactive counter shapes. -/
theorem shapes_prepared (w : List (Fin 2)) (x : State GalilVM)
    (p : CoreState) (he : PalPeg.PhysicalWatchEntry.ShapedCoreEnc w x p) :
    PalPeg.PhysicalWatchEntry.ShapedCoreEnc w ((prepared cyc rep) x) (idealStep (rule cyc rep) blankM p none) := by
  refine ⟨(core_prepared cyc rep) w x p he.1, ?_⟩
  let T := fun slot => p.2 (slotIndex slot)
  have ht : tapesOf T = p.2 := by funext j; simp [T, tapesOf]
  intro c
  change ∃ raw, (idealStep (rule cyc rep) blankM (p.1, p.2) none).2 (slotIndex (counterSlot c)) = _
  rw [← ht]
  cases hc : (enabled cyc rep) c with
  | false =>
    change ∃ raw, ((result cyc rep) p.1 T).2 (slotIndex (counterSlot c)) = _
    rw [(kept_counter cyc rep) p.1 T _ c rfl hc]
    exact he.2 c
  | true =>
    obtain ⟨value, hv⟩ := (enabled_value cyc rep) x c hc
    obtain ⟨raw, _, hr⟩ := (carrier_tape cyc rep) (by decide : 32 ≤ margin) x p.1 T he.1.1.2 (counterSlot c) c rfl value hv
    exact ⟨raw, hr⟩

theorem invariant_prepared (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : PalPeg.PhysicalCacheInvariant.CoreInv w x p) :
    PalPeg.PhysicalCacheInvariant.CoreInv w ((prepared cyc rep) x) (idealStep (rule cyc rep) blankM p none) := by
  refine ⟨(shapes_prepared cyc rep) w x p he.1, ?_⟩
  let T := fun slot => p.2 (slotIndex slot)
  have ht : tapesOf T = p.2 := by funext j; simp [T, tapesOf]
  have hs := (kept_counter cyc rep) p.1 T (counterSlot 10) 10 rfl (by simp [enabled, debit])
  have hm := (kept_counter cyc rep) p.1 T (mirrorSlot 5) 10 rfl (by simp [enabled, debit])
  dsimp only [result] at hs hm
  rw [ht] at hs hm
  change PalPeg.PhysicalCacheInvariant.Cache ((prepared cyc rep) x) ((sign cyc rep) p.1 (fun j => readWin blankM 32 (p.2 j)) 10)
    ((idealStep (rule cyc rep) blankM p none).2 (slotIndex (counterSlot 10)))
    ((idealStep (rule cyc rep) blankM p none).2 (slotIndex (mirrorSlot 5)))
  rw [hs, hm]
  simpa [PalPeg.PhysicalCacheInvariant.Cache, PalPeg.PhysicalCacheInvariant.mirrorMagnitude,
    prepared, sign, debit, T, PalPeg.PhysicalSpare.spareIndex, PalPeg.PhysicalPeriodMirror.mirrorIndex] using he.2


open PalPeg.PhysicalDebtMirror (credit repaired repair mirrorIndex RebuildingCore Rebuilding)
open PalPeg.GalilScaffoldCounter (value Canonical positive)

/-- The radius/debt pair preserves the nonnegative credit balance. -/
theorem balanced (x : State GalilVM) (hb : PalPeg.PhysicalLoanInvariant.Balanced x) :
    PalPeg.PhysicalLoanInvariant.Balanced (prepared cyc rep x) := by
  obtain ⟨hr, hd⟩ := hb
  unfold PalPeg.PhysicalLoanInvariant.Balanced prepared
  simp only [PalPeg.GalilScaffoldCounter.inc_value, PalPeg.GalilScaffoldCounter.dec_value]
  constructor <;> omega

theorem credit_prepared (x : State GalilVM) (hr : 0 ≤ value x.vm.radius)
    (hd : Canonical x.vm.search.debt) :
    credit (prepared cyc rep x) = if positive x.vm.search.debt then inc (credit x) else credit x := by
  have h := PalPeg.PhysicalDebtMirror.credit_advance (value x.vm.radius) (value x.vm.search.debt) hr
  have hp := PalPeg.GalilScaffoldCounter.positive_iff x.vm.search.debt hd
  by_cases ht : positive x.vm.search.debt = true
  · rw [if_pos ht]
    apply PalPeg.ChainBoundaryCache.counter_eq_of_value
      (PalPeg.GalilScaffoldCounter.ofNat_canonical _)
      (PalPeg.GalilScaffoldCounter.inc_canonical _ (PalPeg.GalilScaffoldCounter.ofNat_canonical _))
    simp only [credit, prepared, PalPeg.GalilScaffoldCounter.inc_value,
      PalPeg.GalilScaffoldCounter.dec_value, PalPeg.GalilScaffoldCounter.ofNat_value]
    rw [if_pos (hp.mp ht)] at h
    exact_mod_cast h
  · rw [if_neg ht]
    apply congrArg PalPeg.GalilScaffoldCounter.ofNat
    change (value (inc x.vm.radius) + min (value (dec x.vm.search.debt)) 0).toNat = _
    rw [PalPeg.GalilScaffoldCounter.inc_value, PalPeg.GalilScaffoldCounter.dec_value]
    simpa [if_neg (fun hv => ht (hp.mpr hv))] using h

/-- Only the rebuilding mirror uses the credit test. All full carriers use the
reference row, and its decisions never read this mirror. -/
noncomputable def actual : ActRule (Fin 2) CoreControl Γm tapeCountM 32 where
  nq := (rule cyc rep).nq
  acts := fun q input ws j => if j = mirrorIndex then
    if counterPositiveTest q ws 8 then [some (encSeg PalPeg.LocalCounter.mark, .right)] else []
    else (rule cyc rep).acts q input ws j
  len_le := by
    intro q input ws j
    split_ifs <;> first | simp | exact (rule cyc rep).len_le q input ws j

theorem window_counter_repaired {K : ℕ} (T : Fin tapeCountM → STape Γm) (c : Fin 16) :
    readWin blankM K (repaired T (slotIndex (counterSlot c))) =
      readWin blankM K (T (slotIndex (counterSlot c))) := by
  simp [repaired, repair, counterSlot, mirrorSlot]

theorem sign_repaired (q : CoreControl) (T : Fin tapeCountM → STape Γm) :
    sign cyc rep q (fun j => readWin blankM 32 (repaired T j)) =
      sign cyc rep q (fun j => readWin blankM 32 (T j)) := by
  funext c
  simp only [sign, incSign, incSignAt, incTwiceSign, incAct, incActAt,
    decSignAt, belowRead, window_counter_repaired]
  rfl

theorem actions_repaired (q : CoreControl) (T : Fin tapeCountM → STape Γm) (j : Fin tapeCountM) :
    (rule cyc rep).acts q none (fun k => readWin blankM 32 (repaired T k)) j =
      (rule cyc rep).acts q none (fun k => readWin blankM 32 (T k)) j := by
  simp only [rule, baseActions, counterActions, incTwiceActs, incTwiceSign,
    incAct, incActAt, incSign, incSignAt, decAct, decActAt, decSignAt,
    belowRead, window_counter_repaired]
  rfl

theorem step_complete (p : CoreState) :
    idealStep (rule cyc rep) blankM (p.1, repaired p.2) none =
      ((idealStep (actual cyc rep) blankM p none).1,
        repaired (idealStep (actual cyc rep) blankM p none).2) := by
  apply Prod.ext
  · exact congrArg (fun pol => {p.1 with polarity := pol}) (sign_repaired cyc rep p.1 p.2)
  · funext j
    change actList blankM (repaired p.2 j) ((rule cyc rep).acts _ none _ j) = _
    rw [actions_repaired]
    by_cases hj : j = mirrorIndex
    · subst j
      simp [repaired, repair, mirrorIndex, idealStep, actual, rule, baseActions,
        counterCarrier, mirrorSource, mirrorSlot]
    · have hn : slotIndex.symm j ≠ mirrorSlot 2 := by
        intro h
        apply hj
        rw [mirrorIndex, ← h, Equiv.apply_symm_apply]
      simp only [repaired, repair, if_neg hn, Equiv.apply_symm_apply, idealStep, actual, if_neg hj]

theorem positive_read (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : RebuildingCore w x p) :
    counterPositiveTest p.1 (fun j => readWin blankM 32 (p.2 j)) 8 = positive x.vm.search.debt := by
  have h := counterPositiveTest_eq he.1.1.1.1.2 (K := 32) (by decide) (by decide) 8 x.vm.search.debt rfl
  simpa [counterPositiveTest, counterZeroTest, belowRead, tapesOf, repaired, repair, counterSlot, mirrorSlot] using h

theorem radius_sign (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : RebuildingCore w x p) (hr : 0 ≤ value x.vm.radius) :
    incSign p.1.polarity 2 (fun j => readWin blankM 32 (p.2 j)) = true := by
  obtain ⟨seg, ha, ht⟩ := he.1.1.1.1.2.counters 2 x.vm.radius rfl
  have hsign := incSign_eq (K := 32) (by decide) (by decide : 32 ≤ margin + 1) p.1.polarity 2
    (fun slot => repaired p.2 (slotIndex slot)) seg ht
  have hs : incSign p.1.polarity 2 (fun j => readWin blankM 32 (p.2 j)) =
      (p.1.polarity 2 || decide (PalPeg.LocalCounter.val seg = 0)) := by
    simp only [incSign, incSignAt, belowRead, tapesOf, Equiv.apply_symm_apply, window_counter_repaired] at hsign
    exact hsign
  rw [hs]
  have hv := congrArg value ha
  rw [PalPeg.LocalCounter.value_eq] at hv
  cases hb : p.1.polarity 2 <;> simp only [hb, Bool.false_eq_true, if_false, if_true] at hv ⊢
  · have hz : PalPeg.LocalCounter.val seg = 0 := by omega
    simp [hz]
  · rfl

/-- A nonnegative represented counter can use the positive sign even at zero. -/
theorem credit_positive_sign (x : State GalilVM) (seg : STape Seg) (bit : Bool)
    (he : absCtr seg bit = credit x) : absCtr seg true = credit x := by
  cases bit with
  | true => exact he
  | false =>
    have hv := congrArg value he
    simp only [PalPeg.LocalCounter.value_eq, Bool.false_eq_true, if_false, credit,
      PalPeg.GalilScaffoldCounter.ofNat_value] at hv
    have hz : PalPeg.LocalCounter.val seg = 0 := by omega
    simpa [absCtr, hz, PalPeg.LocalCounter.negOfNat, PalPeg.GalilScaffoldCounter.ofNat] using he

theorem rebuilding_core (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : RebuildingCore w x p) (hr : 0 ≤ value x.vm.radius) :
    RebuildingCore w (prepared cyc rep x) (idealStep (actual cyc rep) blankM p none) := by
  have hf := invariant_prepared cyc rep w x (p.1, repaired p.2) he.1
  rw [step_complete] at hf
  refine ⟨hf, ?_⟩
  obtain ⟨raw, ha, ht⟩ := he.2
  have ha' := credit_positive_sign x raw (p.1.polarity 2) ha
  have hdebt : Canonical x.vm.search.debt := by
    obtain ⟨seg, hs, _⟩ := he.1.1.1.1.2.counters 8 x.vm.search.debt rfl
    exact hs ▸ PalPeg.LocalCounter.absCtr_canonical seg _
  have hc := credit_prepared cyc rep x hr hdebt
  have hp := radius_sign w x p he hr
  have hd := positive_read w x p he
  by_cases hb : positive x.vm.search.debt = true
  · refine ⟨PalPeg.LocalCounter.push raw, ?_, ?_⟩
    · change absCtr _ (sign cyc rep p.1 _ 2) = _
      simp only [sign, if_true, hp]
      rw [hc, if_pos hb]
      simpa [absCtr, PalPeg.LocalCounter.val_push, PalPeg.GalilScaffoldCounter.inc_ofNat] using congrArg inc ha'
    · change actList blankM (p.2 mirrorIndex) ((actual cyc rep).acts _ none _ mirrorIndex) = _
      simp only [actual, if_true, hd, hb]
      rw [ht]
      exact (padded_push margin raw).symm
  · refine ⟨raw, ?_, ?_⟩
    · change absCtr _ (sign cyc rep p.1 _ 2) = _
      simp only [sign, if_true, hp]
      rw [hc, if_neg hb]
      exact ha'
    · change actList blankM (p.2 mirrorIndex) ((actual cyc rep).acts _ none _ mirrorIndex) = _
      simp only [actual, if_true, hd, if_neg hb]
      exact ht


theorem running_ideal (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : Rebuilding w x p) (hr : 0 ≤ value x.vm.radius) :
    Rebuilding w (prepared cyc rep x) (idealStep (actual cyc rep) blankM p none) := by
  obtain ⟨T, hT, ht⟩ := he
  obtain ⟨hc, ha⟩ := idealStep_congr_teqG (actual cyc rep) blankM p.1 T p.2 ht none
  refine ⟨(idealStep (actual cyc rep) blankM (p.1, T) none).2, ?_, ha⟩
  change RebuildingCore w (prepared cyc rep x) ((idealStep (actual cyc rep) blankM p none).1, _)
  rw [← hc]
  exact rebuilding_core cyc rep w x (p.1, T) hT hr

/-- The real action row grows mirror2 only when the source debt is positive. -/
theorem running (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : Rebuilding w x p) (hr : 0 ≤ value x.vm.radius) :
    Rebuilding w (prepared cyc rep x) ((compStep (actual cyc rep)).apply blankM p none) := by
  have hi := running_ideal cyc rep w x p he hr
  have hm : ∀ j, 32 ≤ pos (p.2 j) := fun j =>
    (show 32 ≤ margin by decide).trans (PalPeg.PhysicalDebtRebuild.sweep_margin w x p he j)
  obtain ⟨hc, ht⟩ := compStep_apply (actual cyc rep) blankM p none hm
  exact PalPeg.MachineStep.sweepClosed_sweepClosure blankM (RebuildingCore w) _ _ _ hi hc.symm ht


/-- The two conditional decrements are selected by the same finite control
that is already present in the source encoding. -/
noncomputable def currentRule : ActRule (Fin 2) CoreControl Γm tapeCountM 32 where
  nq := fun q input ws => (actual q.periodOnly q.ctl.replaying).nq q input ws
  acts := fun q input ws => (actual q.periodOnly q.ctl.replaying).acts q input ws
  len_le := fun q input ws j => (actual q.periodOnly q.ctl.replaying).len_le q input ws j

theorem current_ideal (p : CoreState) : idealStep currentRule blankM p none =
    idealStep (actual p.1.periodOnly p.1.ctl.replaying) blankM p none := rfl

theorem running_current (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : Rebuilding w x p) (hr : 0 ≤ value x.vm.radius) :
    Rebuilding w (prepared x.vm.periodOnly x.ctl.replaying x) (idealStep currentRule blankM p none) := by
  obtain ⟨hc, hp⟩ : p.1.periodOnly = x.vm.periodOnly ∧ p.1.ctl.replaying = x.ctl.replaying := by
    obtain ⟨T, hT, _⟩ := he
    exact ⟨hT.1.1.1.1.1.periodOnly, congrArg PalPeg.GalilScaffoldController.Control.replaying hT.1.1.1.1.1.ctl⟩
  rw [current_ideal, hc, hp]
  exact running_ideal _ _ w x p he hr

/-- info: 'PalPeg.PhysicalMatchCounters.running' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms running

/-- info: 'PalPeg.PhysicalMatchCounters.running_current' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms running_current

end PalPeg.PhysicalMatchCounters
