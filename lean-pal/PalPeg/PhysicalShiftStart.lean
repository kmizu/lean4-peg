import PalPeg.PhysicalShiftEntry
import PalPeg.PhysicalWatchStep
import PalPeg.WindowPack

/-!
# The common nonhead work of entering shift

The entry resets cycle and remaining, increments radius, and increments length
and its mirrors twice. Background erasure shares this row. The saved h is then
lent to remaining by the existing role exchange, without copying a tape.
-/
set_option autoImplicit false
namespace PalPeg.PhysicalShiftStart
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilScaffoldCounter (Counter inc reset)
open PalPeg.Program PalPeg.Local
open PalPeg.LocalCounter (Seg absCtr)
open PalPeg.CloseoutCoreEnc12 PalPeg.LocalStepFusion
variable {fb db : ℕ}

/-- The heads and chain have their own parts of the same entry tick. -/
def prepared (x : State GalilVM) : State GalilVM :=
  ⟨{x.ctl with mode := .shift, clock := 2048}, {x.vm with cycle := reset, remaining := reset, radius := inc x.vm.radius, length := inc (inc x.vm.length), periodOnly := true}⟩

def enabled (c : Fin 16) : Bool := decide (c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3)

def valueAfter (c : Fin 16) (value : Counter) : Counter :=
  if c = 0 ∨ c = 1 then reset
  else if c = 2 then inc value
  else if c = 3 then inc (inc value) else value

noncomputable def sign (q : QPhys fb db) (ws : Fin tapeCountM → Window Γm 64)
    (c : Fin 16) : Bool :=
  if c = 0 ∨ c = 1 then true
  else if c = 2 then incSign q.polarity c ws
  else if c = 3 then incTwiceSign q c ws else q.polarity c

noncomputable def counterActions (q : QPhys fb db) (ws : Fin tapeCountM → Window Γm 64)
    (c : Fin 16) : List (Act Γm) :=
  if c = 0 ∨ c = 1 then [some (encSeg PalPeg.LocalCounter.sep, .right)]
  else if c = 2 then [incAct q c ws]
  else if c = 3 then incTwiceActs q c ws else []

noncomputable def baseActions (q : QPhys fb db) (ws : Fin tapeCountM → Window Γm 64)
    (j : Fin tapeCountM) : List (Act Γm) :=
  match counterCarrier (slotIndex.symm j) with
  | some c => counterActions q ws c
  | none => []

noncomputable def next (q : QPhys fb db) (ws : Fin tapeCountM → Window Γm 64) : QPhys fb db :=
  {q with ctl := {q.ctl with mode := .shift, clock := 2048}, periodOnly := true, polarity := sign q ws}

noncomputable def rule : ActRule (Fin 2) (QPhys fb db) Γm tapeCountM 64 where
  nq := fun q _ ws => next q ws
  acts := fun q _ ws => withErase q.fppLive ws (baseActions q ws)
  len_le := by
    intro q input ws j
    apply withErase_length (b := 2) (by decide)
    intro k
    unfold baseActions
    split
    · unfold counterActions
      split_ifs <;> simp [incTwiceActs_length]
    · simp

noncomputable def result (q : QPhys fb db) (T : Slot → STape Γm) :=
  idealStep rule blankM (q, tapesOf T) none

theorem counterOf_prepared (x : State GalilVM) (c : Fin 16) :
    counterOf (prepared x) c = (counterOf x c).map (valueAfter c) := by
  fin_cases c <;> cases hc : x.vm.chain <;> simp [prepared, counterOf, valueAfter, hc]

theorem enabled_value (x : State GalilVM) (c : Fin 16) (hc : enabled c = true) :
    ∃ value, counterOf x c = some value := by
  simp only [enabled, decide_eq_true_eq] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩

theorem carrier_actions (q : QPhys fb db) (ws : Fin tapeCountM → Window Γm 64)
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

theorem counter_tape {margin : ℕ} (hpad : 64 ≤ margin)
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
  by_cases hz : c = 0 ∨ c = 1
  · simp only [sign, valueAfter, counterActions, if_pos hz]
    exact ⟨PalPeg.LocalCounter.resetSeg segments, PalPeg.LocalCounter.absCtr_reset _ _,
      by rw [ht]; exact (padded_resetSeg margin segments).symm⟩
  by_cases hrad : c = 2
  · simp only [sign, valueAfter, counterActions, if_neg hz, if_pos hrad]
    apply counter_inc_at q.polarity c _ segments value ha _ (T slot) ht
    rw [val_eq_of_absCtr_eq (ha.trans hs.symm)]
    exact incSign_eq (by decide) (by omega) q.polarity c T source hst
  by_cases hlen : c = 3
  · simp only [sign, valueAfter, counterActions, if_neg hz, if_neg hrad, if_pos hlen]
    exact counter_incTwice_at q c T (by decide) hpad source segments value hs ha hst (T slot) ht
  · simp only [sign, valueAfter, counterActions, if_neg hz, if_neg hrad, if_neg hlen]
    exact ⟨segments, ha, ht⟩

theorem carrier_tape {margin : ℕ} (hpad : 64 ≤ margin)
    (x : State GalilVM) (q : QPhys fb db) (T : Slot → STape Γm)
    (he : EncTapes margin x q.polarity q.gap q.micro q.fppLive q.dpLive T)
    (slot : Slot) (c : Fin 16) (hc : counterCarrier slot = some c)
    (value : Counter) (hv : counterOf x c = some value) :
    ∃ raw : STape Seg, absCtr raw ((result q T).1.polarity c) = valueAfter c value ∧
      (result q T).2 (slotIndex slot) = padLeft margin (mapTape encSeg raw) := by
  obtain ⟨source, hs, hst⟩ := he.counters c value hv
  obtain ⟨segments, ha, ht⟩ := counterCarrier_rep he slot c hc value hv
  exact counter_tape hpad q T slot c hc source segments value hs ha hst ht

theorem idle_tapes {margin : ℕ} (hpad : 64 ≤ margin)
    (x : State GalilVM) (q : QPhys fb db) (T : Slot → STape Γm)
    (he : EncTapes margin x q.polarity q.gap q.micro q.fppLive q.dpLive T) (i : Fin 9) :
    ∃ raw : STape (Fin 9), (result q T).2 (slotIndex (progSlotOf (!q.fppLive) i)) =
      padLeft margin (mapTape encProg raw) := by
  simpa only [result, idealStep, rule, tapesOf_apply] using
    idle_shape_withErase margin (by decide : 1 ≤ 64) (by omega) T q.fppLive (baseActions q _)
      (fun k => by simp [baseActions]) he.idleShape i

theorem kept_counter (q : QPhys fb db) (T : Slot → STape Γm)
    (slot : Slot) (c : Fin 16) (hc : counterCarrier slot = some c) (hn : enabled c = false) :
    (result q T).2 (slotIndex slot) = T slot := by
  have hn' : ¬ (c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) := by simpa [enabled] using hn
  change actList blankM (tapesOf T (slotIndex slot)) (rule.acts q none _ (slotIndex slot)) = _
  rw [carrier_actions q _ slot c hc, tapesOf_apply]
  simp only [counterActions, if_neg (show ¬ (c = 0 ∨ c = 1) from by tauto),
    if_neg (show c ≠ 2 from by tauto), if_neg (show c ≠ 3 from by tauto), actList]

theorem encControl_prepared (w : List (Fin 2)) (x : State GalilVM)
    (q : QPhys fb db) (T : Slot → STape Γm) (he : EncControl w x q) :
    EncControl w (prepared x) (result q T).1 := by
  refine ⟨?_, he.chainTag, he.chainPhase, he.chainForward, he.chainBroken,
    he.fppMode, he.fppFinalStage, he.fppPc, he.fppDone, he.dpPc, he.dpDone,
    he.searchMode, he.searchFinalStage, he.searchQuarter, rfl, he.placeGap, he.onLetter, he.leftFirst⟩
  change ctlAbs {q.ctl with mode := .shift, clock := 2048} = _
  change {ctlAbs q.ctl with mode := .shift, clock := 2048} = _
  rw [he.ctl]
  rfl

/-- All 118 tapes, including the three radius mirrors, length mirror and
retired preparation tapes, survive the entry's common action row. -/
theorem tapes_prepared {margin : ℕ} (hpad : 64 ≤ margin)
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
    obtain ⟨raw, _, hr⟩ := carrier_tape (by decide : 64 ≤ margin) x p.1 T he.1.1.2 (counterSlot c) c rfl value hv
    exact ⟨raw, hr⟩

theorem invariant_prepared (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : PalPeg.PhysicalCacheInvariant.CoreInv w x p)
    (hmode : x.ctl.mode ≠ .shift) :
    PalPeg.PhysicalCacheInvariant.CoreInv w (prepared x) (idealStep rule blankM p none) := by
  refine ⟨shapes_prepared w x p he.1, ?_⟩
  let T := fun slot => p.2 (slotIndex slot)
  have ht : tapesOf T = p.2 := by funext j; simp [T, tapesOf]
  have hs := kept_counter p.1 T (counterSlot 10) 10 rfl (by decide)
  have hm := kept_counter p.1 T (mirrorSlot 5) 10 rfl (by decide)
  dsimp only [result] at hs hm
  rw [ht] at hs hm
  change PalPeg.PhysicalCacheInvariant.Cache (prepared x) (sign p.1 (fun j => readWin blankM 64 (p.2 j)) 10)
    ((idealStep rule blankM p none).2 (slotIndex (counterSlot 10)))
    ((idealStep rule blankM p none).2 (slotIndex (mirrorSlot 5)))
  rw [hs, hm]
  have hcache := he.2
  cases hc : x.vm.chain <;>
    simpa [PalPeg.PhysicalCacheInvariant.Cache, PalPeg.PhysicalCacheInvariant.mirrorMagnitude,
      prepared, sign, hmode, hc, PalPeg.GalilScaffoldCounter.value, reset, T,
      PalPeg.PhysicalSpare.spareIndex, PalPeg.PhysicalPeriodMirror.mirrorIndex] using hcache

/-- This is preservation on the real swept source, not just a canonical tape.
Its result is still the ideal action row, so it can be fused with the watch
quanta and the existing view executor without adding a machine tick. -/
theorem running_prepared (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : PalPeg.PhysicalCacheInvariant.Running w x p) (hmode : x.ctl.mode ≠ .shift) :
    PalPeg.PhysicalCacheInvariant.Running w (prepared x) (idealStep rule blankM p none) := by
  obtain ⟨T, he, ht⟩ := he
  have hi := invariant_prepared w x (p.1, T) he hmode
  obtain ⟨hq, hteq⟩ := idealStep_congr_teqG rule blankM p.1 T p.2 ht none
  generalize hresult : idealStep rule blankM (p.1, T) none = resultIdeal at hi hq hteq
  generalize hactual : idealStep rule blankM p none = actual at hq hteq ⊢
  refine ⟨resultIdeal.2, ?_, hteq⟩
  rw [← hq]
  exact hi

/-- Both finite control updates are in this row; the permutation lends h
only after the old remaining carrier has been reset. -/
noncomputable def entryRule : ActRule (Fin 2) CoreControl Γm tapeCountM 64 where
  nq := fun q input ws => PalPeg.PhysicalShiftEntry.lendControl (rule.nq q input ws)
  acts := rule.acts
  len_le := rule.len_le

noncomputable def entryChange : PalPeg.LocalRoleRouting.RoleChange (Fin 2) CoreControl Γm tapeCountM 64 :=
  fun _ _ _ => PalPeg.PhysicalShiftEntry.entryRoles

theorem running_entry (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : PalPeg.PhysicalCacheInvariant.Running w x p) (hmode : x.ctl.mode ≠ .shift)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm) :
    PalPeg.PhysicalCacheInvariant.Running w
      (PalPeg.PhysicalShiftEntry.lent (prepared x) (periodLength wm))
      (PalPeg.LocalRoleFusion.logicalStep entryRule entryChange blankM p none) := by
  have hr := running_prepared w x p he hmode
  exact PalPeg.PhysicalShiftEntry.running_lend w (prepared x) (idealStep rule blankM p none)
    wm hr hchain rfl rfl

/-- The watch quanta use 32 + 32 cells of lookaround; the common entry row
uses the other 64. The unchanged micro radius is therefore exactly 128. -/
noncomputable def plan (consume : Bool) :
    ActRule (Fin 2) (PalPeg.LocalRoleRouting.Control CoreControl tapeCountM) Γm tapeCountM microRadius :=
  seqRule (PalPeg.PhysicalWatchActions.plan consume)
    (PalPeg.LocalRoleFusion.routeRule entryRule entryChange)

def pairedState (consume : Bool) (x : State GalilVM) (wm : PalPeg.GalilScaffoldChainWatch.State) :
    State GalilVM :=
  stepState ⟨x.ctl, {x.vm with chain := .watch (PalPeg.GalilScaffoldChainWatch.immediate
    (PalPeg.PhysicalWatchStep.afterInternal consume wm))}⟩ wm.machine.verifier

/-- The verifier is held here only while the existing twelve-slot view stage
is being assembled; the period and counter effects are already complete. -/
def entryState (consume : Bool) (x : State GalilVM) (wm : PalPeg.GalilScaffoldChainWatch.State) :
    State GalilVM :=
  PalPeg.PhysicalShiftEntry.lent (prepared (pairedState consume x wm))
    (periodLength (PalPeg.GalilScaffoldChainWatch.immediate (PalPeg.PhysicalWatchStep.afterInternal consume wm)))

theorem plan_ideal (consume : Bool) (p : CoreState)
    (hm : ∀ j, microRadius ≤ pos (p.2 j)) :
    PalPeg.LocalRoleRouting.decode
      (idealStep (plan consume) blankM ((Equiv.refl _, p.1), p.2) none) =
    PalPeg.LocalRoleFusion.logicalStep entryRule entryChange blankM
      (PalPeg.LocalRoleFusion.logicalStep (PalPeg.PhysicalWatchActions.fusedRule consume)
        (PalPeg.PhysicalWatchActions.fusedRoles consume) blankM p none) none := by
  have hs := seqRule_ideal blankM (PalPeg.PhysicalWatchActions.plan consume)
    (PalPeg.LocalRoleFusion.routeRule entryRule entryChange) ((Equiv.refl _, p.1), p.2) none hm
  exact (congrArg PalPeg.LocalRoleRouting.decode hs).trans
    (PalPeg.LocalRoleFusion.decode_routeRule entryRule entryChange blankM _ none)

/-- Both watch quanta, all entry counters and the lending permutation preserve
the common invariant as one bounded nonhead row. -/
theorem running_nonhead_ideal (consume : Bool) (w : List (Fin 2)) (x : State GalilVM)
    (p : CoreState) (he : PalPeg.PhysicalCacheInvariant.Running w x p)
    (hmode : x.ctl.mode = .scan) (wm : PalPeg.GalilScaffoldChainWatch.State)
    (hchain : x.vm.chain = .watch wm)
    (hfirst : consume = true → PalPeg.GalilScaffoldChainWatch.Good wm)
    (hsecond : PalPeg.GalilScaffoldChainWatch.Good (PalPeg.PhysicalWatchStep.afterInternal consume wm)) :
    PalPeg.PhysicalCacheInvariant.Running w (entryState consume x wm)
      (PalPeg.LocalRoleFusion.logicalStep (PalPeg.LocalRoleFusion.flatten (plan consume))
        (PalPeg.LocalRoleFusion.finalRoles (plan consume)) blankM p none) := by
  have hw := PalPeg.PhysicalWatchStep.running_pair_good_ideal consume w x p he wm hchain hfirst hsecond
  let before := PalPeg.LocalRoleFusion.logicalStep (PalPeg.PhysicalWatchActions.fusedRule consume)
    (PalPeg.PhysicalWatchActions.fusedRoles consume) blankM p none
  let watched := PalPeg.GalilScaffoldChainWatch.immediate (PalPeg.PhysicalWatchStep.afterInternal consume wm)
  let held := {watched with machine := {watched.machine with verifier := wm.machine.verifier}}
  have hh : (pairedState consume x wm).vm.chain = .watch held := by
    simp [pairedState, stepState, chainVerifierBack, held, watched]
  have hr := running_entry w (pairedState consume x wm) before hw
    (by change x.ctl.mode ≠ .shift; rw [hmode]; decide) held hh
  have hm : ∀ j, microRadius ≤ pos (p.2 j) := fun j => micro_le_margin.trans
    (PalPeg.PhysicalContract.running_margin (PalPeg.PhysicalCacheInvariant.running_core he) j)
  change PalPeg.PhysicalCacheInvariant.Running w _
    (PalPeg.LocalRoleRouting.decode (idealStep (plan consume) blankM ((Equiv.refl _, p.1), p.2) none))
  rw [plan_ideal consume p hm]
  exact hr

/-- The actual single sweep implements the complete nonhead entry plan,
including intermediate boundary rotation and the final remaining/mirror swap. -/
theorem running_nonhead (consume : Bool) (w : List (Fin 2)) (x : State GalilVM)
    (p : PalPeg.LocalRoleRouting.Config CoreControl Γm tapeCountM)
    (he : PalPeg.PhysicalCacheInvariant.Running w x (PalPeg.LocalRoleRouting.decode p))
    (hmode : x.ctl.mode = .scan) (wm : PalPeg.GalilScaffoldChainWatch.State)
    (hchain : x.vm.chain = .watch wm)
    (hfirst : consume = true → PalPeg.GalilScaffoldChainWatch.Good wm)
    (hsecond : PalPeg.GalilScaffoldChainWatch.Good (PalPeg.PhysicalWatchStep.afterInternal consume wm)) :
    PalPeg.PhysicalCacheInvariant.Running w (entryState consume x wm)
      (PalPeg.LocalRoleRouting.decode ((PalPeg.LocalRoleFusion.compiled (plan consume)).apply blankM p none)) := by
  have hi := running_nonhead_ideal consume w x (PalPeg.LocalRoleRouting.decode p) he hmode wm hchain hfirst hsecond
  have hm : ∀ j, microRadius ≤ pos ((PalPeg.LocalRoleRouting.decode p).2 j) := fun j => micro_le_margin.trans
    (PalPeg.PhysicalContract.running_margin (PalPeg.PhysicalCacheInvariant.running_core he) j)
  obtain ⟨hq, ht⟩ := PalPeg.LocalRoleFusion.compiled_apply (plan consume) blankM p none hm
  change PalPeg.PhysicalCacheInvariant.Running w _
    (PalPeg.LocalRoleRouting.decode
      (idealStep (plan consume) blankM ((Equiv.refl _, (PalPeg.LocalRoleRouting.decode p).1),
        (PalPeg.LocalRoleRouting.decode p).2) none)) at hi
  generalize hresult : PalPeg.LocalRoleRouting.decode
    (idealStep (plan consume) blankM ((Equiv.refl _, (PalPeg.LocalRoleRouting.decode p).1),
      (PalPeg.LocalRoleRouting.decode p).2) none) = ideal at hi hq ht
  generalize hactual : PalPeg.LocalRoleRouting.decode
    ((PalPeg.LocalRoleFusion.compiled (plan consume)).apply blankM p none) = actual at hq ht ⊢
  exact PalPeg.MachineStep.sweepClosed_sweepClosure blankM (PalPeg.PhysicalCacheInvariant.CoreInv w)
    _ ideal actual hi hq.symm ht

/-- A real guarded comparison supplies the watch source and its first Good
premise. The existing source-watch theorem also excludes a newly born phase-0
watch; no extra reachability assumption is needed for this classification. -/
theorem source_of_guard {P : Shared} {q : ℕ} {first : Fin 9} {s t : GalilVM}
    (hcmp : compareFound P q first s t)
    (hmis : ¬ (galilFrameS P q first).matched t) (hg : shiftGuardVM t) :
    ∃ wm : PalPeg.GalilScaffoldChainWatch.State, s.chain = .watch wm ∧
      (PalPeg.GalilScaffoldCounter.positive wm.lag = true → PalPeg.GalilScaffoldChainWatch.Good wm) ∧
      t.chain = .watch (PalPeg.PhysicalWatchStep.afterInternal
        (PalPeg.GalilScaffoldCounter.positive wm.lag) wm) := by
  obtain ⟨wm, hw, hi⟩ := PalPeg.WindowPack.source_watch_of_guard hcmp hmis hg
  obtain ⟨mid, hm, _⟩ := hg
  have hstep := hi mid hm
  refine ⟨wm, hw, ?_⟩
  cases hstep with
  | idle hp =>
    refine ⟨fun h => ?_, ?_⟩
    · rw [hp] at h; cases h
    · simpa [PalPeg.PhysicalWatchStep.afterInternal, hp] using hm
  | take hp hgood =>
    exact ⟨fun _ => hgood, by simpa [PalPeg.PhysicalWatchStep.afterInternal, hp] using hm⟩

/-- The guard's prediction is checked against the moved outer cursor. The
existing window invariant aligns that cursor with the verifier, supplying
Good for the immediate quantum, including its right-move availability. -/
theorem immediate_good_of_window {P : Shared} {q : ℕ} {first : Fin 9}
    {x : State GalilVM} {t : GalilVM} (arrived : List (Fin 2))
    (hx : PalPeg.WindowRun.ChainWindowRun arrived x.ctl x.vm)
    (hr : PalPeg.GalilScaffoldInputTrace.Represents x.vm.right.head arrived)
    (hp : x.vm.right.head.focus ≠ none) (hcan : PalPeg.GalilScaffoldChainVerifier.canRight x.vm.right)
    (hcmp : compareFound P q first x.vm t)
    (hmis : ¬ (galilFrameS P q first).matched t) (hg : shiftGuardVM t)
    (mid : PalPeg.GalilScaffoldChainWatch.State) (hmid : t.chain = .watch mid) :
    PalPeg.GalilScaffoldChainWatch.Good mid := by
  obtain ⟨wm, hw, hi⟩ := PalPeg.WindowPack.source_watch_of_guard hcmp hmis hg
  obtain ⟨cen, cc, _, hinv, _⟩ := hx
  have hstep : ChainStep x.vm.chain (.watch mid) := by
    rw [hw]
    exact .watchStep wm mid (hi mid hmid)
  have hwin := PalPeg.WindowInv.windowInv_step hinv hstep
  obtain ⟨guardWatch, hgwatch, hz, _, _, _, hsym⟩ := hg
  have heq : guardWatch = mid := ChainVM.watch.inj (hgwatch.symm.trans hmid)
  subst guardWatch
  obtain ⟨vs, vq, agree, _, hright, _, _, _, htarget⟩ := hcmp
  have hheads := PalPeg.WindowTick.compare_target_heads htarget
  have hrightEq : t.right = PalPeg.GalilScaffoldChainVerifier.right x.vm.right :=
    hheads.2.1.trans hright
  have hrep : PalPeg.GalilScaffoldInputTrace.Represents t.right.head arrived := by
    rw [hrightEq]
    exact right_word _ arrived hr hcan
  have hpres : t.right.head.focus ≠ none := by
    rw [hrightEq]
    exact right_present _ arrived hr hp hcan
  have hpos : position t.right = position x.vm.right + 1 := by
    rw [hrightEq]
    exact right_position _ hcan (represented_position _ arrived hr hp).1
  exact PalPeg.WindowTick.good_of_guard hwin hz hrep hpres hpos hsym

/-- The nonhead physical entry consumes the original comparison relation and
shift guard. Only the immediate prediction/read alignment remains external;
the source-watch classification and Internal success are supplied above. -/
theorem running_from_guard (w : List (Fin 2)) (x : State GalilVM)
    (p : PalPeg.LocalRoleRouting.Config CoreControl Γm tapeCountM)
    (he : PalPeg.PhysicalCacheInvariant.Running w x (PalPeg.LocalRoleRouting.decode p))
    (hmode : x.ctl.mode = .scan) (P : Shared) (q : ℕ) (first : Fin 9) (t : GalilVM)
    (hcmp : compareFound P q first x.vm t)
    (hmis : ¬ (galilFrameS P q first).matched t) (hg : shiftGuardVM t)
    (hgood : ∀ mid, t.chain = .watch mid → PalPeg.GalilScaffoldChainWatch.Good mid) :
    ∃ wm : PalPeg.GalilScaffoldChainWatch.State, x.vm.chain = .watch wm ∧
      PalPeg.PhysicalCacheInvariant.Running w
        (entryState (PalPeg.GalilScaffoldCounter.positive wm.lag) x wm)
        (PalPeg.LocalRoleRouting.decode ((PalPeg.LocalRoleFusion.compiled
          (plan (PalPeg.GalilScaffoldCounter.positive wm.lag))).apply blankM p none)) := by
  obtain ⟨wm, hw, hfirst, hmid⟩ := source_of_guard hcmp hmis hg
  exact ⟨wm, hw, running_nonhead _ w x p he hmode wm hw hfirst (hgood _ hmid)⟩

/-- The complete nonhead entry now consumes source window/word facts instead
of either of the two Good assumptions. Transport of those source facts from
OnRun, and the head executor, remain the final entry integration work. -/
theorem running_from_window (w arrived : List (Fin 2)) (x : State GalilVM)
    (p : PalPeg.LocalRoleRouting.Config CoreControl Γm tapeCountM)
    (he : PalPeg.PhysicalCacheInvariant.Running w x (PalPeg.LocalRoleRouting.decode p))
    (hmode : x.ctl.mode = .scan) (P : Shared) (q : ℕ) (first : Fin 9) (t : GalilVM)
    (hcmp : compareFound P q first x.vm t)
    (hmis : ¬ (galilFrameS P q first).matched t) (hg : shiftGuardVM t)
    (hx : PalPeg.WindowRun.ChainWindowRun arrived x.ctl x.vm)
    (hr : PalPeg.GalilScaffoldInputTrace.Represents x.vm.right.head arrived)
    (hp : x.vm.right.head.focus ≠ none) (hcan : PalPeg.GalilScaffoldChainVerifier.canRight x.vm.right) :
    ∃ wm : PalPeg.GalilScaffoldChainWatch.State, x.vm.chain = .watch wm ∧
      PalPeg.PhysicalCacheInvariant.Running w
        (entryState (PalPeg.GalilScaffoldCounter.positive wm.lag) x wm)
        (PalPeg.LocalRoleRouting.decode ((PalPeg.LocalRoleFusion.compiled
          (plan (PalPeg.GalilScaffoldCounter.positive wm.lag))).apply blankM p none)) :=
  running_from_guard w x p he hmode P q first t hcmp hmis hg
    (immediate_good_of_window arrived hx hr hp hcan hcmp hmis hg)

/-- info: 'PalPeg.PhysicalShiftStart.running_nonhead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms running_nonhead

/-- info: 'PalPeg.PhysicalShiftStart.running_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms running_entry

/-- info: 'PalPeg.PhysicalShiftStart.running_from_guard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms running_from_guard

/-- info: 'PalPeg.PhysicalShiftStart.running_from_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms running_from_window

end PalPeg.PhysicalShiftStart
