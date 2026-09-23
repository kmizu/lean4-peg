import PalPeg.PhysicalRestartStorage
import PalPeg.PhysicalCacheMachine

/-! # Reclaiming the dormant search tapes on the existing physical layout

Counters 5--8 and the lower/span mirrors are six independent segmented tapes.
One bounded action on each makes them available for paired boundary snapshots.
The actual VM is unchanged; only its dormant storage representative changes.
This is an internal operation for the watch-entry row, not an extra VM tick.
-/
set_option autoImplicit false
namespace PalPeg.PhysicalSearchRecycle
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract
open PalPeg.PhysicalRestartStorage
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilScaffoldCounter (Counter reset)
open PalPeg.Program (STape)
open PalPeg.Local (pos)
open PalPeg.LocalCounter (Seg absCtr)
open PalPeg.CloseoutCoreEnc12
open PalPeg.LocalStepFusion
open PalPeg.PhysicalCacheInvariant (CoreInv Running)
open PalPeg.PhysicalWatchEntry (CounterShapes)
open PalPeg.PhysicalCacheMachine (successor)
open PalPeg.GalilFinalAssembly2 (centreC placeC)

/-- The existing four search counters and their two independent mirrors. -/
def resetSlot : Slot → Bool
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl c)))))) => decide (c = 5 ∨ c = 6 ∨ c = 7 ∨ c = 8)
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl m))))))) => decide (m = 3 ∨ m = 4)
  | _ => false

def nextTapes (T : Slot → STape Γm) (slot : Slot) : STape Γm :=
  if resetSlot slot then (T slot).applyAction blankM (encSeg PalPeg.LocalCounter.sep, .right)
  else T slot

def clearedState (x : State GalilVM) : State GalilVM :=
  ⟨x.ctl, replace x.vm reset reset reset reset⟩

theorem next_counter (T : Slot → STape Γm) (c : Fin 16) :
    nextTapes T (counterSlot c) =
      if c = 5 ∨ c = 6 ∨ c = 7 ∨ c = 8 then
        (T (counterSlot c)).applyAction blankM (encSeg PalPeg.LocalCounter.sep, .right)
      else T (counterSlot c) := by simp [nextTapes, resetSlot, counterSlot, mirrorSlot]

theorem next_mirror (T : Slot → STape Γm) (m : Fin 7) :
    nextTapes T (mirrorSlot m) =
      if m = 3 ∨ m = 4 then
        (T (mirrorSlot m)).applyAction blankM (encSeg PalPeg.LocalCounter.sep, .right)
      else T (mirrorSlot m) := by simp [nextTapes, resetSlot, counterSlot, mirrorSlot]

theorem next_shapes {T : Slot → STape Γm} (hs : CounterShapes T) :
    CounterShapes (nextTapes T) := by
  intro c
  obtain ⟨seg, ht⟩ := hs c
  rw [next_counter]
  split_ifs
  · exact ⟨PalPeg.LocalCounter.resetSeg seg, by rw [ht, padded_resetSeg]⟩
  · exact ⟨seg, ht⟩

/-- All non-search state is preserved by the six resets, including the complete
head views, live program banks, retired FPP bank, period and answer tapes. -/
theorem tapes_clear {x : State GalilVM} {q : CoreControl} {T : Slot → STape Γm}
    (he : EncTapes margin x q.polarity q.gap q.micro q.fppLive q.dpLive T) :
    EncTapes margin (clearedState x) q.polarity q.gap q.micro q.fppLive q.dpLive (nextTapes T) := by
  refine { margins := ?_, heads := ?_, idleHead := ?_, fpp := ?_, dp := ?_, idleShape := ?_, counters := ?_, places := ?_, mirrors := ?_, period := ?_, answer := ?_ }
  · intro slot
    by_cases hr : resetSlot slot = true
    · have hm := he.margins slot
      simp only [nextTapes, hr, if_true]
      rcases ht : T slot with ⟨left, focus, right⟩
      rw [ht] at hm
      cases right <;> simp_all [STape.applyAction, pos] <;> omega
    · simpa only [nextTapes, if_neg hr] using he.margins slot
  · intro v head hh
    obtain ⟨view, vt, ha, hv, ht, hc, hw⟩ := he.heads v head hh
    exact ⟨view, vt, ha, hv, fun i => by simpa [nextTapes, resetSlot] using ht i, hc, hw⟩
  · intro hh
    obtain ⟨view, vt, hv, ht, hc, hw⟩ := he.idleHead hh
    exact ⟨view, vt, hv, fun i => by simpa [nextTapes, resetSlot, headSlot] using ht i, hc, hw⟩
  · intro i
    cases hl : q.fppLive <;> simpa [nextTapes, resetSlot, progSlotOf, hl, clearedState, replace] using he.fpp i
  · intro i
    cases hl : q.dpLive <;> simpa [nextTapes, resetSlot, dpSlotOf, hl, clearedState, replace] using he.dp i
  · intro i
    obtain ⟨raw, ht⟩ := he.idleShape i
    refine ⟨raw, ?_⟩
    cases hl : q.fppLive <;> simpa [nextTapes, resetSlot, progSlotOf, hl] using ht
  · intro c value hv
    by_cases hc : c = 5 ∨ c = 6 ∨ c = 7 ∨ c = 8
    · have hvreset : value = reset := by
        rcases hc with rfl | rfl | rfl | rfl <;>
          simpa [counterOf, clearedState, replace] using hv.symm
      subst value
      have hex : ∃ old, counterOf x c = some old := by
        rcases hc with rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩
      obtain ⟨old, ho⟩ := hex
      obtain ⟨seg, _, ht⟩ := he.counters c old ho
      exact ⟨PalPeg.LocalCounter.resetSeg seg, PalPeg.LocalCounter.absCtr_reset seg _,
        by rw [next_counter, if_pos hc, ht, padded_resetSeg]⟩
    · have ho : counterOf x c = some value := by
        simpa only [clearedState, counterOf_replace, if_neg (fun h => hc (Or.inl h)),
          if_neg (fun h => hc (Or.inr (Or.inl h))),
          if_neg (fun h => hc (Or.inr (Or.inr (Or.inl h)))),
          if_neg (fun h => hc (Or.inr (Or.inr (Or.inr h))))] using hv
      obtain ⟨seg, ha, ht⟩ := he.counters c value ho
      exact ⟨seg, ha, by rw [next_counter, if_neg hc]; exact ht⟩
  · intro i place hp
    obtain ⟨stack, junk, hj, ht, hs⟩ := he.places i place hp
    exact ⟨stack, junk, hj, ht, by simpa [nextTapes, resetSlot] using hs⟩
  · intro m value hv
    by_cases hm : m = 3 ∨ m = 4
    · have hvreset : value = reset := by
        rcases hm with rfl | rfl <;>
          simpa [counterOf, mirrorSource, clearedState, replace] using hv.symm
      subst value
      have hex : ∃ old, counterOf x (mirrorSource m) = some old := by
        rcases hm with rfl | rfl <;> exact ⟨_, rfl⟩
      obtain ⟨old, ho⟩ := hex
      obtain ⟨seg, _, ht⟩ := he.mirrors m old ho
      exact ⟨PalPeg.LocalCounter.resetSeg seg, PalPeg.LocalCounter.absCtr_reset seg _,
        by rw [next_mirror, if_pos hm, ht, padded_resetSeg]⟩
    · have ho : counterOf x (mirrorSource m) = some value := by
        fin_cases m <;> simp_all [mirrorSource, counterOf, clearedState, replace]
      obtain ⟨seg, ha, ht⟩ := he.mirrors m value ho
      exact ⟨seg, ha, by rw [next_mirror, if_neg hm]; exact ht⟩
  · intro t ht
    simpa [nextTapes, resetSlot, periodSlot] using he.period t ht
  · intro t ht
    simpa [nextTapes, resetSlot] using he.answer t ht

/-- Resetting dormant storage preserves the exact existing boundary cache. -/
theorem core_clear {w : List (Fin 2)} {x : State GalilVM} {p : CoreState}
    (he : CoreInv w x p) :
    CoreInv w (clearedState x)
      (p.1, fun j => nextTapes (fun slot => p.2 (slotIndex slot)) (slotIndex.symm j)) := by
  refine ⟨⟨⟨⟨control_replace w x p.1 he.1.1.1.1 _ _ _ _, ?_⟩, he.1.1.2⟩, ?_⟩, ?_⟩
  · simpa only [Equiv.symm_apply_apply] using tapes_clear he.1.1.1.2
  · simpa only [Equiv.symm_apply_apply] using next_shapes he.1.2
  · simpa [PalPeg.PhysicalCacheInvariant.Cache, PalPeg.PhysicalCacheInvariant.mirrorMagnitude,
      clearedState, replace, nextTapes, resetSlot, PalPeg.PhysicalSpare.spareIndex,
      PalPeg.PhysicalPeriodMirror.mirrorIndex, counterSlot, mirrorSlot] using he.2

/-- Only six existing tapes are written, one action on each. -/
noncomputable def rule : ActRule (Fin 2) CoreControl Γm tapeCountM macroRadius where
  nq := fun q _ _ => q
  acts := fun _ _ _ j =>
    if resetSlot (slotIndex.symm j) then [some (encSeg PalPeg.LocalCounter.sep, .right)] else []
  len_le := by intro q input ws j; split_ifs <;> simp <;> decide

noncomputable def step : PalPeg.PhysicalBootFeed.CoreStep := compStep rule

theorem ideal_clear (p : CoreState) (input : Option (Fin 2)) :
    idealStep rule blankM p input =
      (p.1, fun j => nextTapes (fun slot => p.2 (slotIndex slot)) (slotIndex.symm j)) := by
  apply Prod.ext
  · rfl
  · funext j
    simp only [idealStep, rule, nextTapes, Equiv.apply_symm_apply]
    split_ifs <;> rfl

/-- The concrete fused sweep realizes all six resets. TEqG carries the result
from ideal segmented tapes to the actual physical tape representation. -/
theorem running_clear (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : Running w x p) (input : Option (Fin 2)) :
    Running w (clearedState x) (step.apply blankM p input) := by
  obtain ⟨T, hT, ht⟩ := he
  have hm : ∀ j, macroRadius ≤ pos (T j) := by
    intro j
    simpa only [Equiv.apply_symm_apply, margin] using hT.1.1.1.2.margins (slotIndex.symm j)
  have hmp : ∀ j, macroRadius ≤ pos (p.2 j) := fun j => (ht j).1 ▸ hm j
  obtain ⟨hc, heq⟩ := idealStep_congr_teqG rule blankM p.1 T p.2 ht input
  obtain ⟨hactual, hsweep⟩ := compStep_apply rule blankM p input hmp
  refine ⟨(idealStep rule blankM (p.1, T) input).2, ?_,
    fun j => PalPeg.MachineStep.teqG_trans (heq j) (hsweep j)⟩
  rw [show (step.apply blankM p input).1 = p.1 from hactual, ideal_clear]
  exact core_clear hT

/-- Overlay uses the same source windows and the same physical sweep as its
base step. Selected tapes receive the reset output; every other tape and the
finite control receive the base output. -/
noncomputable def overlay (base : PalPeg.PhysicalBootFeed.CoreStep) :
    PalPeg.PhysicalBootFeed.CoreStep where
  next := fun q input ws =>
    let result := base.next q input ws
    let cleared := step.next q input ws
    (result.1, fun j => if resetSlot (slotIndex.symm j) then cleared.2 j else result.2 j)
  disp_le := by
    intro q input ws j
    dsimp only
    split
    · exact step.disp_le q input ws j
    · exact base.disp_le q input ws j

theorem overlay_apply (base : PalPeg.PhysicalBootFeed.CoreStep) (p : CoreState)
    (input : Option (Fin 2)) :
    (overlay base).apply blankM p input =
      ((base.apply blankM p input).1, fun j => if resetSlot (slotIndex.symm j) then
        (step.apply blankM p input).2 j else (base.apply blankM p input).2 j) := by
  apply Prod.ext
  · rfl
  · funext j
    simp only [PalPeg.Local.LocalStep.apply, overlay]
    split_ifs <;> rfl

/-- Combine a real VM operation with recycling, without adding a controller
tick. The base only has to leave these six tapes unchanged up to TEqG. -/
theorem overlay_running (base : PalPeg.PhysicalBootFeed.CoreStep)
    (w : List (Fin 2)) (y : State GalilVM) (p : CoreState) (input : Option (Fin 2))
    (he : Running w y (base.apply blankM p input))
    (hstay : ∀ j, resetSlot (slotIndex.symm j) = true →
      TEqG blankM (p.2 j) ((base.apply blankM p input).2 j)) :
    Running w (clearedState y) ((overlay base).apply blankM p input) := by
  obtain ⟨T, hT, ht⟩ := he
  rw [overlay_apply]
  refine ⟨(fun j => nextTapes (fun slot => T (slotIndex slot)) (slotIndex.symm j)),
    core_clear hT, ?_⟩
  intro j
  by_cases hr : resetSlot (slotIndex.symm j) = true
  · have heq : TEqG blankM (T j) (p.2 j) := PalPeg.MachineStep.teqG_trans (ht j)
      ⟨(hstay j hr).1.symm, fun k => ((hstay j hr).2 k).symm⟩
    have hm : macroRadius ≤ pos (p.2 j) := by
      rw [← heq.1]
      simpa only [margin, Equiv.apply_symm_apply] using hT.1.1.1.2.margins (slotIndex.symm j)
    simp only [nextTapes, hr, if_true, Equiv.apply_symm_apply]
    apply PalPeg.MachineStep.teqG_trans
      (PalPeg.PhysicalSpare.actList_teq blankM heq [some (encSeg PalPeg.LocalCounter.sep, .right)])
    simpa only [step, PalPeg.Local.LocalStep.apply, compStep, rule, hr, if_true] using
      teq_sweep_actList blankM macroRadius (p.2 j)
        [some (encSeg PalPeg.LocalCounter.sep, .right)] (by simp; decide) hm
  · simpa only [nextTapes, if_neg hr, Equiv.apply_symm_apply] using ht j

/-- The watch-entry row already leaves precisely these six carriers untouched. -/
theorem entry_preserves_storage (p : CoreState) (input : Option (Fin 2))
    (hm : ∀ j, macroRadius ≤ pos (p.2 j)) (j : Fin tapeCountM)
    (hr : resetSlot (slotIndex.symm j) = true) :
    TEqG blankM (p.2 j) ((PalPeg.PhysicalWatchEntry.entryStep.apply blankM p input).2 j) := by
  have hacts : PalPeg.PhysicalWatchEntry.entryRule.acts p.1 input
      (fun k => PalPeg.Local.readWin blankM macroRadius (p.2 k)) j = [] := by
    generalize hs : slotIndex.symm j = slot at hr ⊢
    unfold resetSlot at hr
    split at hr <;> try cases hr
    all_goals
      simp only [decide_eq_true_eq] at hr
      rcases hr with rfl | rfl | rfl | rfl
      all_goals simp [PalPeg.PhysicalWatchEntry.entryRule, withErase,
        PalPeg.PhysicalWatchEntry.entryActs, PalPeg.PhysicalWatchEntry.resetSlot,
        PalPeg.PhysicalWatchEntry.resets, periodSlot, hs]
      all_goals
        have ho : ¬ ∃ i : Fin 9, j = slotIndex (progSlotOf (!p.1.fppLive) i) := by
          rintro ⟨i, hi⟩
          have heq := congrArg slotIndex.symm hi
          simp only [Equiv.symm_apply_apply, hs] at heq
          cases hf : p.1.fppLive <;> simp [progSlotOf, hf] at heq
        exact if_neg ho
  have ht := (compStep_apply PalPeg.PhysicalWatchEntry.entryRule blankM p input hm).2 j
  simpa only [PalPeg.PhysicalWatchEntry.entryStep, idealStep, hacts, actList] using ht

/-- Reclaiming these tapes changes no canonical abstract state. Dormancy is a
source condition, checked before the operation; it is never asserted of live search. -/
theorem stored_clear (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : Stored w x p) (hd : Dormant x.vm) (input : Option (Fin 2)) :
    Stored w x (step.apply blankM p input) := by
  obtain ⟨y, hr, hy⟩ := he
  have hdy : Dormant y.vm := by
    have hs := hr.2.1
    unfold Same at hs
    rw [hs]
    exact hd
  refine ⟨clearedState y, ⟨hr.1, related_trans hr.2 (related_replace y.vm _ _ _ _ hdy)⟩,
    running_clear w y p hy input⟩

/-- The actual six physical tapes are ready to start two independent boundary
snapshot groups. Lower/span still use their existing mirror polarity. -/
structure Ready (p : CoreState) : Prop where
  counters : ∀ c : Fin 16, c = 5 ∨ c = 6 ∨ c = 7 ∨ c = 8 →
    PalPeg.PhysicalSpare.Rep (p.1.polarity c) reset (p.2 (slotIndex (counterSlot c)))
  mirrors : ∀ m : Fin 7, m = 3 ∨ m = 4 →
    PalPeg.PhysicalSpare.Rep (p.1.polarity (mirrorSource m)) reset (p.2 (slotIndex (mirrorSlot m)))

theorem ready_of_cleared {w : List (Fin 2)} {x : State GalilVM} {p : CoreState}
    (he : Running w (clearedState x) p) : Ready p := by
  obtain ⟨T, hT, ht⟩ := he
  constructor
  · intro c hc
    have hv : counterOf (clearedState x) c = some reset := by
      rcases hc with rfl | rfl | rfl | rfl <;> rfl
    obtain ⟨seg, ha, hseg⟩ := hT.1.1.1.2.counters c reset hv
    exact ⟨seg, ha, hseg ▸ ht (slotIndex (counterSlot c))⟩
  · intro m hm
    have hv : counterOf (clearedState x) (mirrorSource m) = some reset := by
      rcases hm with rfl | rfl <;> rfl
    obtain ⟨seg, ha, hseg⟩ := hT.1.1.1.2.mirrors m reset hv
    exact ⟨seg, ha, hseg ▸ ht (slotIndex (mirrorSlot m))⟩

/-- The entry row performs the ordinary watch entry, clock decrement and
retired-bank erasure alongside the six search-storage resets. -/
noncomputable def entryStep : PalPeg.PhysicalBootFeed.CoreStep :=
  overlay (PalPeg.PhysicalScanCount.countedStep PalPeg.PhysicalWatchEntry.entryStep)

theorem entry_dormant (w : List (Fin 2)) (x : State GalilVM)
    (v : PalPeg.GalilScaffoldChainPeriod.Tape) (h lag credit : Counter)
    (ver : PalPeg.GalilScaffoldInputHead.PlaceHead)
    (hb : x.vm.chain = .back v h lag credit ver)
    (hf : PalPeg.GalilScaffoldChainPeriod.isFirst v.focus = true)
    (hm : x.ctl.mode = .scan) (hs : PalPeg.FrameFunction.starvedTest x = false)
    (hc : 1 < x.ctl.clock) : Dormant (successor w x).vm := by
  have hr : restartGuardTest x.vm = false := by simp [restartGuardTest, hb]
  rw [successor, PalPeg.PhysicalGuardProbe.tickFun_nonstarved_count _ _ 0 1 0 w _ 2048 x hm hs hr hc]
  exact dormant_background _ x.vm (Or.inl (by simp [hb]))

/-- The watch-entry operation is a complete abstract count tick and storage
preparation in one bounded physical step. Its source cache facts are the same
ones already supplied to the ordinary entry; no target encoding is assumed. -/
theorem running_watch_entry (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (first last : Fin 3) (xs : List (Fin 3)) (h lag credit : Counter)
    (ver : PalPeg.GalilScaffoldInputHead.PlaceHead)
    (hb : x.vm.chain = .back ⟨[], .first first,
      xs.map PalPeg.GalilScaffoldChainPeriod.Token.plain ++ [.last last]⟩ h lag credit ver)
    (he : Running w x p) (hm : x.ctl.mode = .scan)
    (hs : PalPeg.FrameFunction.starvedTest x = false) (hc : 1 < x.ctl.clock)
    (hp : PalPeg.ChainStoredPeriod.Stored x.vm.chain) :
    Running w (clearedState (successor w x)) (entryStep.apply blankM p none) := by
  have hout := PalPeg.PhysicalCacheInvariant.running_entry PalPeg.PhysicalBootFeed.feedStep
    w x p first last xs h lag credit ver hb he hm hs hc hp
  rw [PalPeg.PhysicalWatchEntry.selected_entry PalPeg.PhysicalBootFeed.feedStep
    w x p _ h lag credit ver hb rfl (PalPeg.PhysicalCacheInvariant.running_core he) hm hs hc] at hout
  apply overlay_running _ w (successor w x) p none hout
  intro j hr
  rw [PalPeg.PhysicalScanCount.counted_apply]
  apply entry_preserves_storage p none _ j hr
  intro k
  obtain ⟨T, hT, ht⟩ := he
  rw [← (ht k).1]
  simpa only [margin, Equiv.apply_symm_apply] using hT.1.1.1.2.margins (slotIndex.symm k)

/-- Canonical states can already use the recycled representation on entry.
The old lower/span/work/debt need not match the storage representative. -/
theorem stored_watch_entry (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (first last : Fin 3) (xs : List (Fin 3)) (h lag credit : Counter)
    (ver : PalPeg.GalilScaffoldInputHead.PlaceHead)
    (hb : x.vm.chain = .back ⟨[], .first first,
      xs.map PalPeg.GalilScaffoldChainPeriod.Token.plain ++ [.last last]⟩ h lag credit ver)
    (he : Stored w x p) (hm : x.ctl.mode = .scan)
    (hs : PalPeg.FrameFunction.starvedTest x = false) (hc : 1 < x.ctl.clock)
    (hp : PalPeg.ChainStoredPeriod.Stored x.vm.chain) :
    Stored w (successor w x) (entryStep.apply blankM p none) := by
  obtain ⟨y, hr, hy⟩ := he
  have hchain : y.vm.chain = x.vm.chain := by
    have heq := hr.2.1
    unfold Same at heq
    simpa only [replace] using congrArg GalilVM.chain heq
  have hby := hchain.trans hb
  have hmy : y.ctl.mode = .scan := (congrArg (fun c => c.mode) hr.1).symm.trans hm
  have hsy : PalPeg.FrameFunction.starvedTest y = false := (related_starved hr).trans hs
  have hcy : 1 < y.ctl.clock := by rw [← hr.1]; exact hc
  have hpy : PalPeg.ChainStoredPeriod.Stored y.vm.chain := by rw [hchain]; exact hp
  have ht := related_tick w hr
  have hd := entry_dormant w y _ h lag credit ver hby rfl hmy hsy hcy
  refine ⟨clearedState (successor w y), ⟨ht.1,
    related_trans ht.2 (related_replace (successor w y).vm _ _ _ _ hd)⟩, ?_⟩
  exact running_watch_entry w y p first last xs h lag credit ver hby hy hmy hsy hcy hpy

/-- Entry supplies both the preserved canonical state and the ready physical
storage required by the next snapshot-maintenance operation. -/
theorem ready_watch_entry (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (first last : Fin 3) (xs : List (Fin 3)) (h lag credit : Counter)
    (ver : PalPeg.GalilScaffoldInputHead.PlaceHead)
    (hb : x.vm.chain = .back ⟨[], .first first,
      xs.map PalPeg.GalilScaffoldChainPeriod.Token.plain ++ [.last last]⟩ h lag credit ver)
    (he : Stored w x p) (hm : x.ctl.mode = .scan)
    (hs : PalPeg.FrameFunction.starvedTest x = false) (hc : 1 < x.ctl.clock)
    (hp : PalPeg.ChainStoredPeriod.Stored x.vm.chain) :
    Stored w (successor w x) (entryStep.apply blankM p none) ∧ Ready (entryStep.apply blankM p none) := by
  refine ⟨stored_watch_entry w x p first last xs h lag credit ver hb he hm hs hc hp, ?_⟩
  obtain ⟨y, hr, hy⟩ := he
  have hchain : y.vm.chain = x.vm.chain := by
    have heq := hr.2.1
    unfold Same at heq
    simpa only [replace] using congrArg GalilVM.chain heq
  apply ready_of_cleared (running_watch_entry w y p first last xs h lag credit ver
    (hchain.trans hb) hy _ ((related_starved hr).trans hs) _ _)
  · rw [← hr.1]; exact hm
  · rw [← hr.1]; exact hc
  · rw [hchain]; exact hp

/-- info: 'PalPeg.PhysicalSearchRecycle.ready_watch_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ready_watch_entry

/-- info: 'PalPeg.PhysicalSearchRecycle.stored_watch_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stored_watch_entry

/-- info: 'PalPeg.PhysicalSearchRecycle.stored_clear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stored_clear

end PalPeg.PhysicalSearchRecycle
