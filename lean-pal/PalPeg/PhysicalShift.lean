import PalPeg.PhysicalCacheInvariant
import PalPeg.PhysicalCountReady
import PalPeg.PhysicalChainShape

/-!
# The shift row on the existing physical machine

The shared rule moves the left cursor twice and the center once. Its counter
row includes the boundary spare and rebuilding h mirror, with at most two
counter actions per tape. The lemmas below connect that row to the abstract
shift and preserve the whole cache-bearing encoding through the real fused
sweep. Head availability, the remaining-budget bound and copy idleness come
from the legal source tick and OnRun. PhysicalBoundaryCount connects this row
to the final TickCases; shift entry and exit still require their own connections.
-/
set_option autoImplicit false
namespace PalPeg.PhysicalShift
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract PalPeg.PhysicalScanCount
open PalPeg.PhysicalSpare (Rep)
open PalPeg.Program (STape)
open PalPeg.Local (readWin pos)
open PalPeg.LocalCounter (Seg absCtr)
open PalPeg.CloseoutCoreEnc12 PalPeg.LocalStepFusion
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilScaffoldCounter (Counter inc dec)
open PalPeg.GalilScaffoldChainVerifier (right)
open PalPeg.GalilFinalAssembly2 (centreC placeC)

/-- The shift's actual simultaneous update, with no counter aliases. -/
def shifted (x : State GalilVM) (wm : PalPeg.GalilScaffoldChainWatch.State) : State GalilVM :=
  ⟨x.ctl, {x.vm with left := right (right x.vm.left), center := right x.vm.center, remaining := dec x.vm.remaining, radius := dec x.vm.radius, length := dec (dec x.vm.length), cycle := inc (inc x.vm.cycle), chain := .watch (chainShiftOne wm)}⟩

theorem counterOf_shifted (x : State GalilVM) (wm : PalPeg.GalilScaffoldChainWatch.State)
    (hchain : x.vm.chain = .watch wm) (c : Fin 16) :
    counterOf (shifted x wm) c = (counterOf x c).map (shiftCounterValue c) := by
  fin_cases c <;> simp [counterOf, shifted, hchain, chainShiftOne, shiftCounterValue, shiftCounterDec]

theorem tickFun_shift (w : List (Fin 2)) (x : State GalilVM)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm)
    (hmode : x.ctl.mode = .shift) (hrem : PalPeg.GalilScaffoldCounter.positive x.vm.remaining = true) :
    tickFun (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w)
      (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x = shifted x wm := by
  simp only [tickFun, hmode]
  have htest : (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w).remainingPos x.vm = true := by
    simp [PalPeg.FrameFunction.galilFrameFun, PalPeg.FrameFunction.shiftRemainingTest, shiftLens, hrem]
  rw [if_pos htest]
  change (⟨x.ctl, shiftLens.set x.vm (PalPeg.FrameFunction.shiftOneFun (shiftLens.get x.vm))⟩ : State GalilVM) = _
  simp only [PalPeg.FrameFunction.shiftOneFun, shiftLens, hchain]
  rfl

theorem rule_counter (q : CoreControl) (ws : Fin tapeCountM → PalPeg.Local.Window Γm microRadius)
    (hmode : q.ctl.mode = .shift) (hrem : remainsTest q.polarity ws = true)
    (slot : Slot) (c : Fin 16) (hcarrier : counterCarrier slot = some c)
    (hmirror : slot ≠ mirrorSlot 5) :
    ruleActs 1 0 q ws (slotIndex slot) = shiftCounterActions q ws c := by
  have hidle : ∀ k : Fin 9, slot ≠ progSlotOf (!q.fppLive) k := by
    intro k hk
    rw [hk, counterCarrier_prog] at hcarrier
    contradiction
  simp only [ruleActs, hmode, hrem, if_true]
  rw [withErase_at_other q.fppLive ws _ slot hidle]
  simp only [shiftActs, Equiv.apply_eq_iff_eq, if_neg hmirror, Equiv.symm_apply_apply, hcarrier]

theorem next_counter (q : CoreControl) (ws : Fin tapeCountM → PalPeg.Local.Window Γm microRadius)
    (hmode : q.ctl.mode = .shift) (hrem : remainsTest q.polarity ws = true) (c : Fin 16) :
    (ruleNext 1 0 fppBound_gt_start q ws).polarity c = shiftCounterSign q ws c := by
  simp only [ruleNext, hmode, hrem, if_true, shiftNext]

/-- This action theorem also applies to the unnamed spare: it needs its
represented value, not an entry in counterOf. -/
theorem ideal_carrier (rest : RestCommands) (p : CoreState)
    (hslot : p.1.slot.val = 0) (hmode : p.1.ctl.mode = .shift)
    (hrem : remainsTest p.1.polarity (fun j => readWin blankM microRadius (p.2 j)) = true)
    (slot : Slot) (c : Fin 16) (hcarrier : counterCarrier slot = some c)
    (hmirror : slot ≠ mirrorSlot 5)
    (source segments : STape Seg) (value : Counter)
    (hsource : absCtr source (p.1.polarity c) = value)
    (habs : absCtr segments (p.1.polarity c) = value)
    (hsourceTape : p.2 (slotIndex (counterSlot c)) = padLeft margin (mapTape encSeg source))
    (htape : p.2 (slotIndex slot) = padLeft margin (mapTape encSeg segments)) :
    ∃ result : STape Seg,
      absCtr result ((idealRun (workRule rest) blankM p none 12).1.polarity c) = shiftCounterValue c value ∧
      (idealRun (workRule rest) blankM p none 12).2 (slotIndex slot) =
        padLeft margin (mapTape encSeg result) := by
  let T := fun slot => p.2 (slotIndex slot)
  have hT : tapesOf T = p.2 := by funext j; simp [T, tapesOf]
  let ws := fun j => readWin blankM microRadius (tapesOf T j)
  have hqmode := hmode
  have hqrem : remainsTest p.1.polarity ws = true := by
    dsimp only [ws]; rw [hT]; exact hrem
  obtain ⟨result, hresult, hresultTape⟩ := shiftCounter_tape p.1 T (by decide : 2 ≤ microRadius)
    micro_le_margin c source segments value hsource habs hsourceTape (T slot) htape
  refine ⟨result, ?_, ?_⟩
  · have hb := (tickPhysRule_bits 1 0 fppBound_gt_start (by decide : 1+3 ≤ microRadius)
      (by decide : 2 ≤ microRadius) rest p.1 T none hslot).1
    rw [hT] at hb
    rw [workRule_eq, hb]
    rw [← hT, next_counter p.1 ws hqmode hqrem c]
    exact hresult
  · have hnonhead : (slotIndex.symm (slotIndex slot)).isLeft = false := by
      rw [Equiv.symm_apply_apply]
      cases slot with
      | inl head => cases hcarrier
      | inr other => rfl
    rw [workRule_eq, tickPhysRule_eq,
      tickRule_otherSlots (by decide : 2 ≤ microRadius)
        (fun q _ ws => ruleNext 1 0 fppBound_gt_start q ws) (modeCommands 0 rest)
        (fun q _ ws => ruleActs 1 0 q ws)
        (fun q _ ws j => ruleActs_length 1 0 (by decide : 1+3 ≤ microRadius) q ws j)
        p none hslot (slotIndex slot) hnonhead]
    change actList blankM (T slot) (ruleActs 1 0 p.1 (fun j => readWin blankM microRadius (p.2 j))
      (slotIndex slot)) = _
    rw [← hT, rule_counter p.1 ws hqmode hqrem slot c hcarrier hmirror]
    exact hresultTape

/-- Source and mirror counters are both updated by the same real twelve-slot row. -/
theorem ideal_counter (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : CoreState) (he : CoreEnc w x p)
    (hmode : x.ctl.mode = .shift) (hrem : PalPeg.GalilScaffoldCounter.positive x.vm.remaining = true)
    (slot : Slot) (c : Fin 16) (hcarrier : counterCarrier slot = some c)
    (hmirror : slot ≠ mirrorSlot 5)
    (value : Counter) (hvalue : counterOf x c = some value) :
    ∃ segments : STape Seg,
      absCtr segments ((idealRun (workRule rest) blankM p none 12).1.polarity c) = shiftCounterValue c value ∧
      (idealRun (workRule rest) blankM p none 12).2 (slotIndex slot) =
        padLeft margin (mapTape encSeg segments) := by
  let T := fun slot => p.2 (slotIndex slot)
  have hT : tapesOf T = p.2 := by funext j; simp [T, tapesOf]
  let ws := fun j => readWin blankM microRadius (tapesOf T j)
  have hqmode : p.1.ctl.mode = .shift := by
    have hc := congrArg PalPeg.GalilScaffoldController.Control.mode he.1.1.ctl
    change p.1.ctl.mode = x.ctl.mode at hc
    exact hc.trans hmode
  have hqrem : remainsTest p.1.polarity ws = true := by
    rw [remainsTest_eq he.1.2 (by decide : 1 ≤ microRadius) micro_le_margin centreC placeC 0 1 0 w]
    simp [PalPeg.FrameFunction.galilFrameFun, PalPeg.FrameFunction.shiftRemainingTest, shiftLens, hrem]
  obtain ⟨source, hsource, hsourceTape⟩ := he.1.2.counters c value hvalue
  obtain ⟨segments, habs, htape⟩ := counterCarrier_rep he.1.2 slot c hcarrier value hvalue
  have hactual : remainsTest p.1.polarity (fun j => readWin blankM microRadius (p.2 j)) = true := by
    rw [← hT]; exact hqrem
  exact ideal_carrier rest p he.2.1 hqmode hactual slot c hcarrier hmirror source segments value
    hsource habs hsourceTape htape

/-- A symbolic rule transports a represented counter through both ideal-tape
replacement and the final write sweep without expanding the concrete view rule. -/
theorem fused_rep (R : ActRule (Fin 2) CoreControl Γm tapeCountM microRadius)
    (p : CoreState) (T : Fin tapeCountM → STape Γm)
    (hteq : ∀ j, TEqG blankM (T j) (p.2 j)) (hm : ∀ j, macroRadius ≤ pos (T j))
    (bit : CoreControl → Bool) (value : Counter) (j : Fin tapeCountM)
    (hr : Rep (bit (idealRun R blankM (p.1, T) none 12).1) value
      ((idealRun R blankM (p.1, T) none 12).2 j)) :
    Rep (bit ((compStep (iterRule R 12)).apply blankM p none).1) value
      (((compStep (iterRule R 12)).apply blankM p none).2 j) := by
  have hmp : ∀ i, macroRadius ≤ pos (p.2 i) := fun i => (hteq i).1 ▸ hm i
  obtain ⟨hc, ht⟩ := idealStep_congr_teqG (iterRule R 12) blankM p.1 T p.2 hteq none
  rw [iterRule_ideal blankM R 12 (p.1, T) none hm, idealIter_eq_idealRun] at hc ht
  obtain ⟨hcontrol, hactual⟩ := compStep_apply (iterRule R 12) blankM p none hmp
  obtain ⟨seg, habs, hrep⟩ := hr
  refine ⟨seg, ?_, PalPeg.MachineStep.teqG_trans hrep (PalPeg.MachineStep.teqG_trans (ht j) (hactual j))⟩
  change ((compStep (iterRule R 12)).apply blankM p none).1 =
    (idealStep (iterRule R 12) blankM (p.1, p.2) none).1 at hcontrol
  rw [hcontrol, ← hc]
  exact habs

/-- The actual fused step encodes every logical counter of the abstract shift.
Source facts all come from the existing encoding and branch guard. -/
theorem running_counter (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : CoreState) (he : PalPeg.MachineStep.sweepClosure blankM (CoreEnc w) x p)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm)
    (hmode : x.ctl.mode = .shift) (hrem : PalPeg.GalilScaffoldCounter.positive x.vm.remaining = true)
    (slot : Slot) (c : Fin 16) (hcarrier : counterCarrier slot = some c)
    (value : Counter) (hvalue : counterOf (shifted x wm) c = some value) :
    Rep (((workStep rest).apply blankM p none).1.polarity c) value
      (((workStep rest).apply blankM p none).2 (slotIndex slot)) := by
  rw [counterOf_shifted x wm hchain c] at hvalue
  obtain ⟨old, hold, hnext⟩ : ∃ old, counterOf x c = some old ∧ shiftCounterValue c old = value := by
    cases hv : counterOf x c with
    | none => simp [hv] at hvalue
    | some old => exact ⟨old, rfl, Option.some.inj (by simpa only [hv, Option.map_some] using hvalue)⟩
  have hmirror : slot ≠ mirrorSlot 5 := by
    intro hs
    rw [hs, counterCarrier_mirror] at hcarrier
    have hc : c = 10 := by simpa [mirrorSource] using hcarrier.symm
    subst c
    simp [counterOf, hchain] at hold
  obtain ⟨T, hT, ht⟩ := he
  obtain ⟨seg, ha, hseg⟩ := ideal_counter rest w x (p.1, T) hT hmode hrem slot c hcarrier hmirror old hold
  have hr : Rep ((idealRun (workRule rest) blankM (p.1, T) none 12).1.polarity c) value
      ((idealRun (workRule rest) blankM (p.1, T) none 12).2 (slotIndex slot)) := by
    generalize hrun : idealRun (workRule rest) blankM (p.1, T) none 12 = result at ha hseg ⊢
    refine ⟨seg, ha.trans hnext, ?_⟩
    rw [hseg]
    exact ⟨rfl, fun _ => rfl⟩
  have hm : ∀ j, macroRadius ≤ pos (T j) := by
    intro j
    simpa only [Equiv.apply_symm_apply, margin] using hT.1.2.margins (slotIndex.symm j)
  rewrite [workStep]
  generalize hR : workRule rest = R at hr ⊢
  exact fused_rep R p T ht hm (fun q => q.polarity c) value (slotIndex slot) hr

/-- info: 'PalPeg.PhysicalShift.running_counter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms running_counter

/-- A legal shift tick supplies all three right-move guards and its watching
chain. These are inputs already carried by the final physical consumer. -/
theorem ready_of_tick (w : List (Fin 2)) {x y : State GalilVM}
    (htick : Tick (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x y)
    (hmode : x.ctl.mode = .shift) (hrem : PalPeg.GalilScaffoldCounter.positive x.vm.remaining = true) :
    ∃ wm : PalPeg.GalilScaffoldChainWatch.State, x.vm.chain = .watch wm ∧
      PalPeg.GalilScaffoldChainVerifier.canRight x.vm.center ∧
      PalPeg.GalilScaffoldChainVerifier.canRight x.vm.left ∧
      PalPeg.GalilScaffoldChainVerifier.canRight (right x.vm.left) := by
  cases htick <;> simp_all
  case shift_one c s t hm hp hone =>
    obtain ⟨⟨hc, hl, hl', wm, hchain, _⟩, _⟩ := hone
    exact ⟨⟨wm, hchain⟩, hc, hl, hl'⟩
  case shift_done c s out hm hnot hout =>
    apply False.elim
    apply hnot
    change PalPeg.GalilScaffoldCounter.positive s.remaining = true ∨ _
    exact Or.inl hrem

def headStep (v : Fin 4) (head : PalPeg.GalilScaffoldInputHead.PlaceHead) :
    PalPeg.GalilScaffoldInputHead.PlaceHead :=
  if v = 0 then right (right head) else if v = 1 then right head else head

theorem headOf_shifted (x : State GalilVM) (wm : PalPeg.GalilScaffoldChainWatch.State)
    (hchain : x.vm.chain = .watch wm) (v : Fin 4) :
    headOf (shifted x wm) v = (headOf x v).map (headStep v) := by
  fin_cases v <;> simp [shifted, headOf, headStep, hchain, chainShiftOne]

/-- Each cursor, including the whole-cell move on the left, is realized by the
same twelve physical slots. Availability comes from the legal source tick. -/
theorem ideal_head (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (q : CoreControl) (T : Slot → STape Γm)
    (he : PalPeg.PhysicalEncoding.Enc w margin x (q, T))
    (hslot : q.slot.val = 0) (howed : ∀ v, (q.micro v).2.2.2 = 0)
    (hmode : x.ctl.mode = .shift) (hrem : PalPeg.GalilScaffoldCounter.positive x.vm.remaining = true)
    {y : State GalilVM}
    (htick : Tick (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x y)
    (v : Fin 4) (head : PalPeg.GalilScaffoldInputHead.PlaceHead) (hhead : headOf x v = some head) :
    ∃ (view : PalPeg.LocalInputView.InputView) (viewTapes : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc),
      PalPeg.LocalArrival.absHead' view [] = headStep v head ∧
      PalPeg.ConcreteLocalMachine.ViewRep margin view
        ((idealRun (tickPhysRule 1 0 fppBound_gt_start (by decide : 1+3 ≤ microRadius)
          (by decide : 2 ≤ microRadius) rest) blankM (q, tapesOf T) none 12).1.gap v)
        ((idealRun (tickPhysRule 1 0 fppBound_gt_start (by decide : 1+3 ≤ microRadius)
          (by decide : 2 ≤ microRadius) rest) blankM (q, tapesOf T) none 12).1.micro v) viewTapes ∧
      (∀ i, (idealRun (tickPhysRule 1 0 fppBound_gt_start (by decide : 1+3 ≤ microRadius)
          (by decide : 2 ≤ microRadius) rest) blankM (q, tapesOf T) none 12).2
            (slotIndex (headSlot v i)) = mapTape encCell (viewTapes i)) ∧
      PalPeg.LocalViewCells.ViewCells view ∧ PalPeg.LocalInputView.WF view := by
  obtain ⟨_, _, hcenter, hleft, hleftNext⟩ := ready_of_tick w htick hmode hrem
  have hqmode : q.ctl.mode = .shift := by
    have hc := congrArg PalPeg.GalilScaffoldController.Control.mode he.1.ctl
    change q.ctl.mode = x.ctl.mode at hc
    exact hc.trans hmode
  let ws := fun j => readWin blankM microRadius (tapesOf T j)
  have hqrem : remainsTest q.polarity ws = true := by
    rw [remainsTest_eq he.2 (by decide : 1 ≤ microRadius) micro_le_margin centreC placeC 0 1 0 w]
    simp [PalPeg.FrameFunction.galilFrameFun, PalPeg.FrameFunction.shiftRemainingTest, shiftLens, hrem]
  have hrow : modeCommands 0 rest q none ws v = shiftCommands v := by
    simp only [modeCommands, hqmode, hqrem, if_true]
  have hf : headOp (shiftCommands v) = some (headStep v) := by
    fin_cases v <;> rfl
  obtain ⟨view, viewTapes, habs, hrep, hslots, hcells, hwf⟩ := he.2.heads v head hhead
  have hready : HeadReady (shiftCommands v) view := by
    by_cases hv : v = 0
    · subst v
      have hh : head = x.vm.left := Option.some.inj hhead.symm
      apply headReady_stepRight_of_canRight
      · rw [habs, hh]; exact hleft
      · rw [habs, hh]; exact hleftNext
    · by_cases hvcenter : v = 1
      · subst v
        have hh : head = x.vm.center := Option.some.inj hhead.symm
        have hav : PalPeg.GalilScaffoldChainVerifier.canRight (PalPeg.LocalArrival.absHead' view []) := by
          rw [habs, hh]; exact hcenter
        intro hgap hnear
        simpa [PalPeg.GalilScaffoldChainVerifier.canRight, PalPeg.LocalArrival.absHead', hgap, hnear] using hav
      · simp only [shiftCommands, if_neg hv, if_neg hvcenter, HeadReady]
  exact tickPhysRule_heads 1 0 fppBound_gt_start (by decide) (by decide) micro_le_margin rest v
    (q, tapesOf T) none hslot (shiftCommands v) hrow view hwf hcells viewTapes
    (fun i => by
      change tapesOf T (slotIndex (headSlot v i)) = _
      rw [tapesOf_apply]; exact hslots i) hrep (howed v) head _ habs
    (headStep v) hf rfl hready

/-- info: 'PalPeg.PhysicalShift.ideal_head' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ideal_head

/-- The exact same source window selects the shift row on a swept encoding. -/
theorem running_guards (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : PalPeg.MachineStep.sweepClosure blankM (CoreEnc w) x p)
    (hmode : x.ctl.mode = .shift) (hrem : PalPeg.GalilScaffoldCounter.positive x.vm.remaining = true) :
    p.1.ctl.mode = .shift ∧ p.1.slot.val = 0 ∧
      remainsTest p.1.polarity (fun j => readWin blankM microRadius (p.2 j)) = true := by
  refine ⟨?_, (running_boundary (q := p.1) he).1, ?_⟩
  · obtain ⟨T, hT, _⟩ := he
    have hc := congrArg PalPeg.GalilScaffoldController.Control.mode hT.1.1.ctl
    change p.1.ctl.mode = x.ctl.mode at hc
    exact hc.trans hmode
  · apply PalPeg.PhysicalTickDispatch.read_from_running (fun q ws => remainsTest q.polarity ws)
      (fun _ => true) w x p he
    intro T hT
    have ht := remainsTest_eq hT.1.2 (by decide : 1 ≤ microRadius) micro_le_margin centreC placeC 0 1 0 w
    simp only [tapesOf, Equiv.apply_symm_apply] at ht
    rw [ht]
    simp [PalPeg.FrameFunction.galilFrameFun, PalPeg.FrameFunction.shiftRemainingTest, shiftLens, hrem]

/-- The spare has no counterOf entry in watch. Its independent Rep supplies
an observationally equal ideal source, so its real decrement is still proved. -/
theorem running_spare (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : PalPeg.MachineStep.sweepClosure blankM (CoreEnc w) x p)
    (hmode : x.ctl.mode = .shift) (hrem : PalPeg.GalilScaffoldCounter.positive x.vm.remaining = true)
    (spare : Counter) (hr : Rep (p.1.polarity 10) spare (p.2 PalPeg.PhysicalSpare.spareIndex)) :
    Rep (((workStep rest).apply blankM p none).1.polarity 10) (dec spare)
      (((workStep rest).apply blankM p none).2 PalPeg.PhysicalSpare.spareIndex) := by
  obtain ⟨hqmode, hslot, hqrem⟩ := running_guards w x p he hmode hrem
  obtain ⟨seg, habs, hrep⟩ := hr
  let T := Function.update p.2 PalPeg.PhysicalSpare.spareIndex (padLeft margin (mapTape encSeg seg))
  have ht : ∀ j, TEqG blankM (T j) (p.2 j) := by
    intro j
    by_cases hj : j = PalPeg.PhysicalSpare.spareIndex
    · subst j
      simpa only [T, Function.update_self] using hrep
    · simp only [T, Function.update_of_ne hj]
      exact ⟨rfl, fun _ => rfl⟩
  have hw : (fun j => readWin blankM microRadius (T j)) =
      (fun j => readWin blankM microRadius (p.2 j)) := by
    funext j
    exact readWin_congr_teqG (ht j)
  have hm : ∀ j, macroRadius ≤ pos (T j) := fun j =>
    (ht j).1.symm ▸ running_margin (q := p.1) he j
  obtain ⟨result, ha, hresult⟩ := ideal_carrier rest (p.1, T) hslot hqmode
    (by rw [hw]; exact hqrem) (counterSlot 10) 10 rfl
    (by simp [counterSlot, mirrorSlot]) seg seg spare habs habs
    (Function.update_self _ _ _) (Function.update_self _ _ _)
  have hout : Rep ((idealRun (workRule rest) blankM (p.1, T) none 12).1.polarity 10)
      (dec spare) ((idealRun (workRule rest) blankM (p.1, T) none 12).2 PalPeg.PhysicalSpare.spareIndex) := by
    generalize hrule : idealRun (workRule rest) blankM (p.1, T) none 12 = step at ha hresult ⊢
    refine ⟨result, ?_, ?_⟩
    · simpa [shiftCounterValue, shiftCounterDec] using ha
    · rw [show step.2 PalPeg.PhysicalSpare.spareIndex = padLeft margin (mapTape encSeg result) from hresult]
      exact ⟨rfl, fun _ => rfl⟩
  rewrite [workStep]
  generalize hR : workRule rest = R at hout ⊢
  exact fused_rep R p T ht hm (fun q => q.polarity 10) (dec spare) PalPeg.PhysicalSpare.spareIndex hout

/-- Rebuilding the h mirror uses a positive push independent of spare polarity. -/
theorem ideal_mirror (rest : RestCommands) (p : CoreState)
    (hslot : p.1.slot.val = 0) (hmode : p.1.ctl.mode = .shift)
    (hrem : remainsTest p.1.polarity (fun j => readWin blankM microRadius (p.2 j)) = true) :
    (idealRun (workRule rest) blankM p none 12).2 PalPeg.PhysicalPeriodMirror.mirrorIndex =
      actList blankM (p.2 PalPeg.PhysicalPeriodMirror.mirrorIndex)
        [some (encSeg PalPeg.LocalCounter.mark, .right)] := by
  rw [workRule_eq, tickPhysRule_eq,
    tickRule_otherSlots (by decide : 2 ≤ microRadius)
      (fun q _ ws => ruleNext 1 0 fppBound_gt_start q ws) (modeCommands 0 rest)
      (fun q _ ws => ruleActs 1 0 q ws)
      (fun q _ ws j => ruleActs_length 1 0 (by decide : 1+3 ≤ microRadius) q ws j)
      p none hslot PalPeg.PhysicalPeriodMirror.mirrorIndex
      (by simp [PalPeg.PhysicalPeriodMirror.mirrorIndex, mirrorSlot])]
  simp only [ruleActs, hmode, hrem, if_true]
  unfold PalPeg.PhysicalPeriodMirror.mirrorIndex
  rw [withErase_at_other _ _ _ (mirrorSlot 5)
    (by intro k; cases p.1.fppLive <;> simp [progSlotOf, mirrorSlot])]
  simp [shiftActs]

/-- The h mirror grows by one in the actual fused shift, even when its tape
contains sweep padding or garbage beyond the represented segment. -/
theorem running_mirror (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : PalPeg.MachineStep.sweepClosure blankM (CoreEnc w) x p)
    (hmode : x.ctl.mode = .shift) (hrem : PalPeg.GalilScaffoldCounter.positive x.vm.remaining = true)
    (n : ℕ) (hr : Rep true (PalPeg.GalilScaffoldCounter.ofNat n) (p.2 PalPeg.PhysicalPeriodMirror.mirrorIndex)) :
    Rep true (PalPeg.GalilScaffoldCounter.ofNat (n+1))
      (((workStep rest).apply blankM p none).2 PalPeg.PhysicalPeriodMirror.mirrorIndex) := by
  obtain ⟨hqmode, hslot, hqrem⟩ := running_guards w x p he hmode hrem
  obtain ⟨seg, habs, hrep⟩ := hr
  obtain ⟨result, ha, hresult⟩ := counter_inc_at (fun _ => true) 0 true seg
    (PalPeg.GalilScaffoldCounter.ofNat n) habs (by simp)
    (padLeft margin (mapTape encSeg seg)) rfl
  have hout : Rep true (PalPeg.GalilScaffoldCounter.ofNat (n+1))
      ((idealRun (workRule rest) blankM p none 12).2 PalPeg.PhysicalPeriodMirror.mirrorIndex) := by
    rw [ideal_mirror rest p hslot hqmode hqrem]
    refine ⟨result, ?_, ?_⟩
    · simpa only [PalPeg.GalilScaffoldCounter.inc_ofNat] using ha
    · have ht := PalPeg.PhysicalSpare.actList_teq blankM hrep
        [some (encSeg PalPeg.LocalCounter.mark, .right)]
      have hacts : actList blankM (padLeft margin (mapTape encSeg seg))
          [some (encSeg PalPeg.LocalCounter.mark, .right)] = padLeft margin (mapTape encSeg result) := hresult
      rw [hacts] at ht
      exact ht
  rewrite [workStep]
  generalize hR : workRule rest = R at hout ⊢
  exact fused_rep R p p.2 (fun _ => ⟨rfl, fun _ => rfl⟩) (running_margin (q := p.1) he)
    (fun _ => true) (PalPeg.GalilScaffoldCounter.ofNat (n+1)) PalPeg.PhysicalPeriodMirror.mirrorIndex hout

/-- info: 'PalPeg.PhysicalShift.running_spare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms running_spare

/-- info: 'PalPeg.PhysicalShift.running_mirror' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms running_mirror

/-- The first-letter bit after a whole-cell right move is observable even
at the sentinel; no run-only lower bound on the source position is needed. -/
theorem rightTwice_first_iff (head : PalPeg.GalilScaffoldInputHead.PlaceHead)
    (hfirst : PalPeg.GalilScaffoldChainVerifier.canRight head)
    (hsecond : PalPeg.GalilScaffoldChainVerifier.canRight (right head)) :
    position (right (right head)) = 1 ↔ head.gap = false ∧ head.head.left = [] := by
  rcases head with ⟨⟨focus, back, near, incoming⟩, gap⟩
  cases gap <;> cases back <;> cases near <;> cases incoming <;>
    simp_all [PalPeg.GalilScaffoldChainVerifier.canRight, right,
      PalPeg.GalilScaffoldChainVerifier.headRight, PalPeg.GalilScaffoldInputTrace.moveRight, position]

theorem leftFirst_eq (w : List (Fin 2)) (x : State GalilVM) (q : CoreControl) (T : Slot → STape Γm)
    (he : PalPeg.PhysicalEncoding.Enc w margin x (q, T))
    (hleft : PalPeg.GalilScaffoldChainVerifier.canRight x.vm.left)
    (hleftNext : PalPeg.GalilScaffoldChainVerifier.canRight (right x.vm.left)) :
    shiftLeftFirst q (fun j => readWin blankM microRadius (tapesOf T j)) =
      leftFirstTest {x.vm with left := right (right x.vm.left)} := by
  obtain ⟨view, viewTapes, habs, hrep, hslots, hcells, hwf⟩ := he.2.heads 0 x.vm.left rfl
  obtain ⟨bottom, hheight, hstack⟩ := hrep.back
  have hmargin : microRadius ≤ (PalPeg.ConcreteLocalMachine.backStack view ++ bottom).length := by
    simp only [PalPeg.ConcreteLocalMachine.backStack, List.length_append, List.length_cons]
    have hm := micro_le_margin
    omega
  have hcentre : centreRead (fun j => readWin blankM microRadius (tapesOf T j))
      (headSlot 0 PalPeg.ConcreteLocalMachine.backTape) =
      encCell (PalPeg.CloseoutCoreEnc.cellSym view.focus) := by
    rw [centreRead_backSlot 0 viewTapes (PalPeg.ConcreteLocalMachine.backStack view ++ bottom)
      (hslots PalPeg.ConcreteLocalMachine.backTape) hstack hmargin]
    rfl
  have hsentinel : (encCell (PalPeg.CloseoutCoreEnc.cellSym view.focus) =
      encCell (PalPeg.CloseoutCoreEnc.cellSym none)) ↔ view.focus = none := by
    cases hf : view.focus with
    | none => simp
    | some b =>
      simp only [iff_false, reduceCtorEq, iff_false]
      show ¬ (encCell (PalPeg.CloseoutCoreEnc.cellSym (some b)) = blankM)
      have hn : PalPeg.CloseoutCoreEnc.cellSym (some b) ≠ PalPeg.CloseoutCoreStep.blankc := by
        simp [PalPeg.CloseoutCoreEnc.cellSym, PalPeg.CloseoutCoreStep.blankc,
          PalPeg.GalilVMEncode.blank, PalPeg.GalilVMEncode.sOpt]
      simp [encCell, hn, blankM]
  rw [Bool.eq_iff_iff]
  simp only [shiftLeftFirst, leftFirstTest, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]
  rw [rightTwice_first_iff x.vm.left hleft hleftNext, ← habs]
  change (q.gap 0 = false ∧ _) ↔ view.gap = false ∧ view.back = []
  rw [hrep.gap, hcentre, hsentinel, PalPeg.LocalViewCells.back_nil_iff_focus_none hcells]

theorem encControl_shifted (w : List (Fin 2)) (x : State GalilVM) (q : CoreControl) (T : Slot → STape Γm)
    (he : PalPeg.PhysicalEncoding.Enc w margin x (q, T))
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm)
    (hleft : PalPeg.GalilScaffoldChainVerifier.canRight x.vm.left)
    (hleftNext : PalPeg.GalilScaffoldChainVerifier.canRight (right x.vm.left)) :
    EncControl w (shifted x wm) (shiftNext q (fun j => readWin blankM microRadius (tapesOf T j))) where
  ctl := he.1.ctl
  chainTag := by simpa only [shiftNext, shifted, hchain, chainTagOf] using he.1.chainTag
  chainPhase := by simpa only [shiftNext, shifted, hchain, chainConsumeOf, chainShiftOne] using he.1.chainPhase
  chainForward := by simpa only [shiftNext, shifted, hchain, chainConsumeOf, chainShiftOne] using he.1.chainForward
  chainBroken := by simpa only [shiftNext, shifted, hchain, chainConsumeOf, chainShiftOne] using he.1.chainBroken
  fppMode := he.1.fppMode
  fppFinalStage := he.1.fppFinalStage
  fppPc := he.1.fppPc
  fppDone := he.1.fppDone
  dpPc := he.1.dpPc
  dpDone := he.1.dpDone
  searchMode := he.1.searchMode
  searchFinalStage := he.1.searchFinalStage
  searchQuarter := he.1.searchQuarter
  periodOnly := he.1.periodOnly
  placeGap := by
    intro i pl hpl
    apply he.1.placeGap i pl
    fin_cases i <;> simpa only [placeOf, shifted, hchain, chainShiftOne] using hpl
  onLetter := he.1.onLetter
  leftFirst := leftFirst_eq w x q T he hleft hleftNext

/-- info: 'PalPeg.PhysicalShift.encControl_shifted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms encControl_shifted

/-- All finite control fields agree with the real abstract shift after the
whole twelve-slot row, using only encoding, guards and the legal source tick. -/
theorem ideal_control (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : CoreState) (he : CoreEnc w x p)
    (hmode : x.ctl.mode = .shift) (hrem : PalPeg.GalilScaffoldCounter.positive x.vm.remaining = true)
    {y : State GalilVM}
    (htick : Tick (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x y) :
    EncControl w
      (tickFun (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w)
        (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x)
      (idealRun (workRule rest) blankM p none 12).1 := by
  obtain ⟨wm, hchain, _, hleft, hleftNext⟩ := ready_of_tick w htick hmode hrem
  rw [tickFun_shift w x wm hchain hmode hrem]
  let T := fun slot => p.2 (slotIndex slot)
  have hT : tapesOf T = p.2 := by funext j; simp [T, tapesOf]
  let ws := fun j => readWin blankM microRadius (tapesOf T j)
  have hqmode : p.1.ctl.mode = .shift := by
    have hc := congrArg PalPeg.GalilScaffoldController.Control.mode he.1.1.ctl
    change p.1.ctl.mode = x.ctl.mode at hc
    exact hc.trans hmode
  have hqrem : remainsTest p.1.polarity ws = true := by
    rw [remainsTest_eq he.1.2 (by decide : 1 ≤ microRadius) micro_le_margin centreC placeC 0 1 0 w]
    simp [PalPeg.FrameFunction.galilFrameFun, PalPeg.FrameFunction.shiftRemainingTest, shiftLens, hrem]
  have hc : EncControl w (shifted x wm) (ruleNext 1 0 fppBound_gt_start p.1 ws) := by
    simp only [ruleNext, hqmode, hqrem, if_true]
    exact encControl_shifted w x p.1 T he.1 wm hchain hleft hleftNext
  have hout := encControl_afterTick 1 0 fppBound_gt_start (by decide : 1+3 ≤ microRadius)
    (by decide : 2 ≤ microRadius) rest w (shifted x wm) p.1 T none he.2.1 hc
  rw [workRule_eq]
  simpa only [hT] using hout

/-- info: 'PalPeg.PhysicalShift.ideal_control' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ideal_control

/-- Outside counters and their mirrors the shift has no branch action. -/
theorem actions_off (q : CoreControl) (ws : Fin tapeCountM → PalPeg.Local.Window Γm microRadius)
    (slot : Slot) (hc : counterCarrier slot = none) :
    shiftActs q ws (slotIndex slot) = [] := by
  have hm : slot ≠ mirrorSlot 5 := by
    intro h
    rw [h, counterCarrier_mirror] at hc
    contradiction
  simp only [shiftActs, Equiv.apply_eq_iff_eq, if_neg hm, Equiv.symm_apply_apply, hc]

/-- Non-head tapes perform precisely their step-zero actions. -/
theorem ideal_other (rest : RestCommands) (p : CoreState) (hslot : p.1.slot.val = 0)
    (slot : Slot) (hhead : ∀ v i, slot ≠ headSlot v i) :
    (idealRun (workRule rest) blankM p none 12).2 (slotIndex slot) =
      actList blankM (p.2 (slotIndex slot))
        (ruleActs 1 0 p.1 (fun j => readWin blankM microRadius (p.2 j)) (slotIndex slot)) := by
  rw [workRule_eq, tickPhysRule_eq]
  exact tickRule_otherSlots (by decide) _ _ _ _ p none hslot _
    (isLeft_eq_false_of_ne_headSlot hhead)

theorem ideal_kept (rest : RestCommands) (p : CoreState) (hslot : p.1.slot.val = 0)
    (hmode : p.1.ctl.mode = .shift)
    (hrem : remainsTest p.1.polarity (fun j => readWin blankM microRadius (p.2 j)) = true)
    (slot : Slot) (hhead : ∀ v i, slot ≠ headSlot v i)
    (hc : counterCarrier slot = none) (hi : ∀ i, slot ≠ progSlotOf (!p.1.fppLive) i) :
    (idealRun (workRule rest) blankM p none 12).2 (slotIndex slot) = p.2 (slotIndex slot) := by
  rw [ideal_other rest p hslot slot hhead]
  simp only [ruleActs, hmode, hrem, if_true]
  rw [withErase_at_other p.1.fppLive _ _ slot hi, actions_off p.1 _ slot hc]
  rfl

/-- All sixteen carriers keep their padded shape, even when unnamed by the VM. -/
theorem ideal_shapes (rest : RestCommands) (p : CoreState) (hslot : p.1.slot.val = 0)
    (hmode : p.1.ctl.mode = .shift)
    (hrem : remainsTest p.1.polarity (fun j => readWin blankM microRadius (p.2 j)) = true)
    (hs : PalPeg.PhysicalWatchEntry.CounterShapes (fun slot => p.2 (slotIndex slot))) :
    PalPeg.PhysicalWatchEntry.CounterShapes
      (fun slot => (idealRun (workRule rest) blankM p none 12).2 (slotIndex slot)) := by
  intro c
  obtain ⟨seg, ht⟩ := hs c
  obtain ⟨result, _, hr⟩ := ideal_carrier rest p hslot hmode hrem (counterSlot c) c rfl
    (by simp [counterSlot, mirrorSlot]) seg seg (absCtr seg (p.1.polarity c)) rfl rfl ht ht
  generalize hrun : idealRun (workRule rest) blankM p none 12 = output at hr ⊢
  exact ⟨result, hr⟩

/-- The program roles do not change during shift. -/
theorem ideal_live (rest : RestCommands) (p : CoreState) (hslot : p.1.slot.val = 0)
    (hmode : p.1.ctl.mode = .shift)
    (hrem : remainsTest p.1.polarity (fun j => readWin blankM microRadius (p.2 j)) = true) :
    (idealRun (workRule rest) blankM p none 12).1.fppLive = p.1.fppLive ∧
    (idealRun (workRule rest) blankM p none 12).1.dpLive = p.1.dpLive := by
  let T := fun slot => p.2 (slotIndex slot)
  have hT : tapesOf T = p.2 := by funext j; simp [T, tapesOf]
  have hb := (tickPhysRule_bits 1 0 fppBound_gt_start (by decide : 1+3 ≤ microRadius)
    (by decide : 2 ≤ microRadius) rest p.1 T none hslot).2
  simp only [hT, Prod.eta] at hb
  rewrite [workRule_eq]
  generalize hrun : idealRun (tickPhysRule 1 0 fppBound_gt_start
    (by decide : 1+3 ≤ microRadius) (by decide : 2 ≤ microRadius) rest) blankM p none 12 = result at hb ⊢
  simpa only [ruleNext, hmode, hrem, if_true, shiftNext] using hb

/-- Background erasure preserves the whole retired program bundle. -/
theorem ideal_idleShape (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : CoreState) (he : CoreEnc w x p)
    (hmode : p.1.ctl.mode = .shift)
    (hrem : remainsTest p.1.polarity (fun j => readWin blankM microRadius (p.2 j)) = true)
    (i : Fin 9) :
    ∃ raw : STape (Fin 9), (idealRun (workRule rest) blankM p none 12).2
      (slotIndex (progSlotOf (!p.1.fppLive) i)) = padLeft margin (mapTape encProg raw) := by
  let T := fun slot => p.2 (slotIndex slot)
  have hT : tapesOf T = p.2 := by funext j; simp [T, tapesOf]
  have hi := idle_shape_withErase margin (by decide : 1 ≤ microRadius)
    (by decide : microRadius ≤ margin + 1) T p.1.fppLive
    (shiftActs p.1 (fun j => readWin blankM microRadius (p.2 j)))
    (fun k => actions_off p.1 _ _ (counterCarrier_prog _ k)) he.1.2.idleShape i
  rw [hT] at hi
  rw [ideal_other rest p he.2.1 _ (by intro v j; cases p.1.fppLive <;> simp [progSlotOf, headSlot])]
  simp only [ruleActs, hmode, hrem, if_true]
  exact hi

/-- The shift preserves every tape field, including margins and inactive
carriers. Its moving-head premises are supplied by the legal source tick. -/
theorem ideal_tapes (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : CoreState) (he : PalPeg.PhysicalWatchEntry.ShapedCoreEnc w x p)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm)
    (hmode : x.ctl.mode = .shift) (hrem : PalPeg.GalilScaffoldCounter.positive x.vm.remaining = true)
    {y : State GalilVM}
    (htick : Tick (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x y) :
    EncTapes margin (shifted x wm)
      (idealRun (workRule rest) blankM p none 12).1.polarity
      (idealRun (workRule rest) blankM p none 12).1.gap
      (idealRun (workRule rest) blankM p none 12).1.micro
      (idealRun (workRule rest) blankM p none 12).1.fppLive
      (idealRun (workRule rest) blankM p none 12).1.dpLive
      (fun slot => (idealRun (workRule rest) blankM p none 12).2 (slotIndex slot)) := by
  have hexact : PalPeg.MachineStep.sweepClosure blankM (CoreEnc w) x p :=
    ⟨p.2, he.1, fun _ => ⟨rfl, fun _ => rfl⟩⟩
  obtain ⟨hqmode, hslot, hqrem⟩ := running_guards w x p hexact hmode hrem
  have hshapes := ideal_shapes rest p hslot hqmode hqrem he.2
  have hlive := ideal_live rest p hslot hqmode hqrem
  have hidle := ideal_idleShape rest w x p he.1 hqmode hqrem
  have hkeep := ideal_kept rest p hslot hqmode hqrem
  have hmirrorPush := ideal_mirror rest p hslot hqmode hqrem
  have hcarrier : ∀ slot c, counterCarrier slot = some c → ∀ value,
      counterOf (shifted x wm) c = some value →
      ∃ seg : STape Seg,
        absCtr seg ((idealRun (workRule rest) blankM p none 12).1.polarity c) = value ∧
        (idealRun (workRule rest) blankM p none 12).2 (slotIndex slot) = padLeft margin (mapTape encSeg seg) := by
    intro slot c hc value hv
    rw [counterOf_shifted x wm hchain c] at hv
    obtain ⟨old, ho, hn⟩ : ∃ old, counterOf x c = some old ∧ shiftCounterValue c old = value := by
      cases hh : counterOf x c with
      | none => simp [hh] at hv
      | some old => exact ⟨old, rfl, Option.some.inj (by simpa only [hh, Option.map_some] using hv)⟩
    have hm : slot ≠ mirrorSlot 5 := by
      intro hs
      rw [hs, counterCarrier_mirror] at hc
      have hc10 : c = 10 := by simpa [mirrorSource] using hc.symm
      subst c
      simp [counterOf, hchain] at ho
    obtain ⟨seg, ha, ht⟩ := ideal_counter rest w x p he.1 hmode hrem slot c hc hm old ho
    generalize hrun : idealRun (workRule rest) blankM p none 12 = output at ha ht ⊢
    exact ⟨seg, ha.trans hn, ht⟩
  let T := fun slot => p.2 (slotIndex slot)
  have hT : tapesOf T = p.2 := by funext j; simp [T, tapesOf]
  have hheads : ∀ v head, headOf (shifted x wm) v = some head →
      ∃ (view : PalPeg.LocalInputView.InputView) (viewTapes : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc),
        PalPeg.LocalArrival.absHead' view [] = head ∧
        PalPeg.ConcreteLocalMachine.ViewRep margin view
          ((idealRun (workRule rest) blankM p none 12).1.gap v)
          ((idealRun (workRule rest) blankM p none 12).1.micro v) viewTapes ∧
        (∀ i, (idealRun (workRule rest) blankM p none 12).2 (slotIndex (headSlot v i)) = mapTape encCell (viewTapes i)) ∧
        PalPeg.LocalViewCells.ViewCells view ∧ PalPeg.LocalInputView.WF view := by
    intro v head hh
    rw [headOf_shifted x wm hchain v] at hh
    obtain ⟨old, ho, hn⟩ : ∃ old, headOf x v = some old ∧ headStep v old = head := by
      cases hv : headOf x v with
      | none => simp [hv] at hh
      | some old => exact ⟨old, rfl, Option.some.inj (by simpa only [hv, Option.map_some] using hh)⟩
    have hout := ideal_head rest w x p.1 T he.1.1 hslot he.1.2.2 hmode hrem htick v old ho
    simpa only [workRule_eq, hT, Prod.eta, hn] using hout
  generalize hrun : idealRun (workRule rest) blankM p none 12 = result at hshapes hlive hidle hkeep hmirrorPush hcarrier hheads ⊢
  have hplaces : placeOf (shifted x wm) = placeOf x := by
    funext i; fin_cases i <;> simp [placeOf, shifted, hchain, chainShiftOne]
  have hperiod : periodOf (shifted x wm) = periodOf x := by
    simp [periodOf, shifted, hchain, chainShiftOne]
  refine ⟨?_, hheads, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro slot
    by_cases hh : ∃ v i, slot = headSlot v i
    · obtain ⟨v, i, rfl⟩ := hh
      obtain ⟨head, hh⟩ : ∃ head, headOf (shifted x wm) v = some head := by
        fin_cases v <;> simp [headOf, shifted]
      obtain ⟨view, vt, _, hr, hs, hc, hw⟩ := hheads v head hh
      exact margin_le_pos_headSlot (by decide : 2 ≤ microRadius) micro_le_margin
        (gap := result.1.gap) (micro := result.1.micro)
        (tapes := fun slot => result.2 (slotIndex slot)) (v := v)
        ⟨view, vt, hr, hs, hc, hw⟩ i
    by_cases hc : ∃ c, slot = counterSlot c
    · obtain ⟨c, rfl⟩ := hc
      obtain ⟨seg, hs⟩ := hshapes c
      dsimp only at hs
      rw [hs, pos_padLeft]; omega
    by_cases hm : ∃ m, slot = mirrorSlot m
    · obtain ⟨m, rfl⟩ := hm
      by_cases hm5 : m = 5
      · subst m
        simp only [PalPeg.PhysicalPeriodMirror.mirrorIndex] at hmirrorPush
        rw [hmirrorPush]
        have hp := he.1.1.2.margins (mirrorSlot 5)
        simpa only [actList, actOnG, PalPeg.Local.pos_applyAction_right] using Nat.le_succ_of_le hp
      · obtain ⟨value, hv⟩ : ∃ value, counterOf (shifted x wm) (mirrorSource m) = some value := by
          fin_cases m <;> first | contradiction | simp [counterOf, shifted, mirrorSource]
        obtain ⟨seg, _, hs⟩ := hcarrier (mirrorSlot m) (mirrorSource m) rfl value hv
        rw [hs, pos_padLeft]; omega
    by_cases hi : ∃ i, slot = progSlotOf (!p.1.fppLive) i
    · obtain ⟨i, rfl⟩ := hi
      obtain ⟨raw, hr⟩ := hidle i
      rw [hr, pos_padLeft]; omega
    have hnone : counterCarrier slot = none := by
      rcases slot with head | prog | dp | answer | period | place | c | m | retired | retiredDP
      all_goals first
        | rfl
        | exact False.elim (hc ⟨c, rfl⟩)
        | exact False.elim (hm ⟨m, rfl⟩)
    rw [hkeep slot (fun v i h => hh ⟨v, i, h⟩) hnone (fun i h => hi ⟨i, h⟩)]
    exact he.1.1.2.margins slot
  · simp [headOf, shifted]
  · intro i
    rw [hlive.1, hkeep (progSlotOf p.1.fppLive i)
      (by intro v j; cases p.1.fppLive <;> simp [progSlotOf, headSlot])
      (counterCarrier_prog _ i) (progSlotOf_ne_flip p.1.fppLive i)]
    exact he.1.1.2.fpp i
  · intro i
    rw [hlive.2, hkeep (dpSlotOf p.1.dpLive i)
      (by intro v j; cases p.1.dpLive <;> simp [dpSlotOf, headSlot])
      (counterCarrier_dp _ i)
      (by intro k; cases p.1.dpLive <;> cases p.1.fppLive <;> simp [dpSlotOf, progSlotOf])]
    exact he.1.1.2.dp i
  · rw [hlive.1]; exact hidle
  · intro c value hv
    exact hcarrier (counterSlot c) c rfl value hv
  · intro i place hp
    rw [hplaces] at hp
    obtain ⟨st, junk, hj, hs, ht⟩ := he.1.1.2.places i place hp
    refine ⟨st, junk, hj, hs, ?_⟩
    rw [hkeep (placeSlot i) (by intros; simp [placeSlot, headSlot])
      (counterCarrier_place i) (by intro k; cases p.1.fppLive <;> simp [placeSlot, progSlotOf])]
    exact ht
  · intro m value hv
    exact hcarrier (mirrorSlot m) (mirrorSource m) rfl value hv
  · intro tape ht
    rw [hperiod] at ht
    rw [hkeep periodSlot (by intros; simp [periodSlot, headSlot]) counterCarrier_period
      (by intro k; cases p.1.fppLive <;> simp [periodSlot, progSlotOf])]
    exact he.1.1.2.period tape ht
  · intro tape ht
    simp [answerOf, shifted] at ht

/-- The complete abstract shift is realized by the existing twelve-slot row,
with all counter shapes and the next macro boundary retained. -/
theorem ideal_shaped (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : CoreState) (he : PalPeg.PhysicalWatchEntry.ShapedCoreEnc w x p)
    (hmode : x.ctl.mode = .shift) (hrem : PalPeg.GalilScaffoldCounter.positive x.vm.remaining = true)
    {y : State GalilVM}
    (htick : Tick (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x y) :
    PalPeg.PhysicalWatchEntry.ShapedCoreEnc w
      (tickFun (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w)
        (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x)
      (idealRun (workRule rest) blankM p none 12) := by
  obtain ⟨wm, hchain, _, _, _⟩ := ready_of_tick w htick hmode hrem
  have hc := ideal_control rest w x p he.1 hmode hrem htick
  have ht := ideal_tapes rest w x p he wm hchain hmode hrem htick
  have hexact : PalPeg.MachineStep.sweepClosure blankM (CoreEnc w) x p :=
    ⟨p.2, he.1, fun _ => ⟨rfl, fun _ => rfl⟩⟩
  obtain ⟨hm, hslot, hr⟩ := running_guards w x p hexact hmode hrem
  have hs := ideal_shapes rest p hslot hm hr he.2
  have hb := PalPeg.PhysicalBoundary.macroBoundary_tickRule
    (fun q _ ws => ruleNext 1 0 fppBound_gt_start q ws) (modeCommands 0 rest)
    (fun q _ ws => ruleActs 1 0 q ws)
    (fun q _ ws j => ruleActs_length 1 0 (by decide : 1+3 ≤ microRadius) q ws j)
    w x p none he.1
  simp only [← tickPhysRule_eq 1 0 fppBound_gt_start (by decide) (by decide) rest,
    ← workRule_eq] at hb
  rw [tickFun_shift w x wm hchain hmode hrem] at hc ⊢
  generalize hrun : idealRun (workRule rest) blankM p none 12 = result at hc ht hs hb ⊢
  exact ⟨⟨⟨hc, ht⟩, hb⟩, hs⟩

/-- The real fused sweep preserves the whole encoding and all sixteen counter
shapes. No post-state encoding or arbitrary-view readiness is assumed. -/
theorem running_shaped (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : CoreState)
    (he : PalPeg.MachineStep.sweepClosure blankM (PalPeg.PhysicalWatchEntry.ShapedCoreEnc w) x p)
    (hmode : x.ctl.mode = .shift) (hrem : PalPeg.GalilScaffoldCounter.positive x.vm.remaining = true)
    {y : State GalilVM}
    (htick : Tick (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x y) :
    PalPeg.MachineStep.sweepClosure blankM (PalPeg.PhysicalWatchEntry.ShapedCoreEnc w)
      (tickFun (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w)
        (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x)
      ((workStep rest).apply blankM p none) := by
  obtain ⟨T, hT, ht⟩ := he
  have hout := ideal_shaped rest w x (p.1, T) hT hmode hrem htick
  rewrite [workStep]
  generalize hR : workRule rest = R at hout ⊢
  change PalPeg.MachineStep.sweepClosure blankM (PalPeg.PhysicalWatchEntry.ShapedCoreEnc w)
    (tickFun (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w)
      (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x)
    ((compStep (iterRule R 12)).apply blankM p none)
  have hm : ∀ j, macroRadius ≤ pos (T j) := by
    intro j
    simpa only [Equiv.apply_symm_apply, margin] using hT.1.1.2.margins (slotIndex.symm j)
  have hmp : ∀ j, macroRadius ≤ pos (p.2 j) := fun j => (ht j).1 ▸ hm j
  obtain ⟨hc, hteq⟩ := idealStep_congr_teqG (iterRule R 12) blankM p.1 T p.2 ht none
  rw [iterRule_ideal blankM R 12 (p.1, T) none hm, idealIter_eq_idealRun] at hc hteq
  obtain ⟨hr, hs⟩ := compStep_apply (iterRule R 12) blankM p none hmp
  refine ⟨(idealRun R blankM (p.1, T) none 12).2, ?_,
    fun j => PalPeg.MachineStep.teqG_trans (hteq j) (hs j)⟩
  rw [hr]
  change PalPeg.PhysicalWatchEntry.ShapedCoreEnc w _
    ((idealStep (iterRule R 12) blankM p none).1, _)
  rw [← hc]
  exact hout

/-- info: 'PalPeg.PhysicalShift.ideal_shaped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ideal_shaped

/-- info: 'PalPeg.PhysicalShift.running_shaped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms running_shaped

/-- Each shift starts with h units and only decrements its remaining counter.
This fact belongs to the existing abstract run, not to extra physical state. -/
def RemainingBound (x : State GalilVM) : Prop :=
  x.ctl.mode = .shift → ∀ wm : PalPeg.GalilScaffoldChainWatch.State,
    x.vm.chain = .watch wm →
      (PalPeg.GalilScaffoldCounter.value x.vm.remaining).toNat ≤ periodLength wm

theorem remainingBound_tick (w : List (Fin 2)) {x y : State GalilVM}
    (ht : Tick (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x y)
    (hcpl : PalPeg.GalilChainCoupling.Coupled x.ctl x.vm)
    (hi : RemainingBound x) : RemainingBound y := by
  cases ht <;> simp_all [RemainingBound]
  case scan_shift c s s' s'' hm ha hc hcmp hmt hr hg hb =>
    obtain ⟨wm, hchain, hlanding⟩ : beginShiftVM' s' s'' := hb
    rw [hlanding]
    intro wm' hwm
    have heq : PalPeg.GalilScaffoldChainWatch.immediate wm = wm' := ChainVM.watch.inj hwm
    subst wm'
    have hblock := (PalPeg.GalilChainCoupling.compare_inv (onLetterVM w) leftFirstVM
      centreC placeC 0 1 0 hcpl hm hcmp).1
    rw [hchain] at hblock
    have hlen := PalPeg.GalilChainCoupling.periodLength_consume wm.machine wm.lag wm.margin
      wm.lag (inc wm.margin) hblock
    change PalPeg.GalilScaffoldCounter.value (PalPeg.GalilScaffoldCounter.ofNat (periodLength wm)) ≤
      (periodLength (PalPeg.GalilScaffoldChainWatch.immediate wm) : ℤ)
    rw [PalPeg.GalilScaffoldCounter.ofNat_value]
    exact le_of_eq (congrArg Int.ofNat hlen.symm)
  case shift_one c s s' hm hp hone =>
    obtain ⟨⟨_, _, _, wm, hchain, hstep⟩, hframe⟩ := hone
    rw [hstep] at hframe
    subst s'
    intro wm' hwm
    have heq : chainShiftOne wm = wm' := ChainVM.watch.inj hwm
    subst wm'
    have hb := hi wm hchain
    change PalPeg.GalilScaffoldCounter.value (dec s.remaining) ≤ (periodLength wm : ℤ)
    rw [PalPeg.GalilScaffoldCounter.dec_value]
    omega

/-- Input truncation changes heads, leaving the shift budget and period intact. -/
theorem remainingBound_trunc (d : ℕ) (x : State GalilVM) (hi : RemainingBound x) :
    RemainingBound (PalPeg.GalilThrottledRun.truncS d x) := by
  intro hm wm hc
  have hm' : x.ctl.mode = .shift := hm
  cases hchain : x.vm.chain <;>
    simp [PalPeg.GalilThrottledRun.truncS, PalPeg.GalilThrottledRun.truncVM,
      PalPeg.GalilThrottledRun.truncChain, hchain] at hc
  case watch v =>
    subst wm
    exact hi hm' v hchain

/-- The actual final-consumer run supplies the mirror's remaining-budget bound,
including input truncation and the packed post-report phase. -/
theorem remainingBound_onRun (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ)
    (hpre : PalPeg.CloseoutCheckW.PreTraceIMW centreC placeC 0 1 0 w st Tc)
    (m : PalPeg.LocalReplayParked.Mirrored1 (PalPeg.LocalBlankState.tapeCount 0))
    (hon : PalPeg.LocalShadowConcrete.OnRun (PalPeg.ShadowedLocalFinal.localGood (spare := 0))
      (PalPeg.ShadowedLocalFinal.postPhase 0 1 0) w
      (PalPeg.ShadowedLocalFinal.heldAfter (Tc w.length) st) m)
    (hnotFrozen : ¬ PalPeg.ShadowedLocalFinal.frozenAt w m) :
    RemainingBound (PalPeg.LocalSysConcrete.absSC m) := by
  have hidleBound : ∀ x : State GalilVM, x.vm.chain = .idle → RemainingBound x := by
    intro x hc hm wm hw
    rw [hc] at hw
    cases hw
  let Inv := fun x : State GalilVM => PalPeg.GalilChainCoupling.Coupled x.ctl x.vm ∧ RemainingBound x
  have hstep : ∀ x y, Tick (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x y → Inv x → Inv y := by
    intro x y ht hi
    exact ⟨PalPeg.GalilChainCoupling.coupled_tick (onLetterVM w) leftFirstVM centreC placeC 0 1 0 2048 hi.1 ht,
      remainingBound_tick w ht hi.1 hi.2⟩
  rcases hon with htracked | ⟨hpost, _, _, _⟩
  · obtain ⟨k, j, _, hsource⟩ := htracked.track
    have hstart : Inv (st 0) := by
      rw [hpre.base.pre.start]
      exact ⟨PalPeg.GalilChainCoupling.coupled_of_idle rfl, hidleBound _ rfl⟩
    have hb := hpre.base.pre.trace.carried (Pk := Inv) hstart (fun _ _ ht hi => hstep _ _ ht hi)
      (min k (Tc w.length)) (Nat.min_le_right _ _)
    change RemainingBound (PalPeg.LocalReplayParked.absState'' m.vm)
    rw [hsource]
    exact remainingBound_trunc (w.length - j) _ hb.2
  · rcases hpost with hplateau | hfrozen
    · obtain ⟨c, s, k, kS, horigin, hrun, _⟩ := hplateau.onRun
      obtain ⟨g, hzero, hlast, htrace, _, _⟩ := hrun
      have hidle : s.chain = .idle := by
        rcases horigin.1.1.1.1.1 with hI | ⟨n, hI⟩
        · obtain ⟨radius, last, hrest⟩ := hI.rest
          exact hrest.1
        · exact hI.chainIdle
      have hstart : Inv (g 0) := by
        rw [hzero]
        exact ⟨PalPeg.GalilChainCoupling.coupled_of_idle hidle, hidleBound _ hidle⟩
      have hend := htrace.carried (Pk := Inv) hstart (fun _ _ ht hi => hstep _ _ ht hi) k le_rfl
      rw [hlast] at hend
      exact hend.2
    · exact (hnotFrozen hfrozen).elim

/-- One positive remaining unit is exactly one new unit in the saved h mirror. -/
theorem mirrorMagnitude_shift (x : State GalilVM) (wm : PalPeg.GalilScaffoldChainWatch.State)
    (hmode : x.ctl.mode = .shift) (hrem : PalPeg.GalilScaffoldCounter.positive x.vm.remaining = true)
    (hcanonical : PalPeg.GalilScaffoldCounter.Canonical x.vm.remaining) (h : ℕ)
    (hbound : (PalPeg.GalilScaffoldCounter.value x.vm.remaining).toNat ≤ h) :
    PalPeg.PhysicalCacheInvariant.mirrorMagnitude (shifted x wm) h =
      PalPeg.PhysicalCacheInvariant.mirrorMagnitude x h + 1 := by
  have hp := (PalPeg.GalilScaffoldCounter.positive_iff _ hcanonical).mp hrem
  simp only [PalPeg.PhysicalCacheInvariant.mirrorMagnitude, shifted, hmode, if_true,
    PalPeg.GalilScaffoldCounter.dec_value]
  omega

/-- Shift preserves the same cache-bearing encoding already used by feed and
all watching count cases. The run supplies the sole numerical budget premise. -/
theorem running (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : CoreState) (he : PalPeg.PhysicalCacheInvariant.Running w x p)
    (hmode : x.ctl.mode = .shift) (hrem : PalPeg.GalilScaffoldCounter.positive x.vm.remaining = true)
    (hbound : RemainingBound x) {y : State GalilVM}
    (htick : Tick (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x y) :
    PalPeg.PhysicalCacheInvariant.Running w
      (tickFun (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w)
        (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x)
      ((workStep rest).apply blankM p none) := by
  obtain ⟨wm, hchain, _, _, _⟩ := ready_of_tick w htick hmode hrem
  have hcore := PalPeg.PhysicalCacheInvariant.running_core he
  have hcache := PalPeg.PhysicalCacheInvariant.running_cache he
  rw [PalPeg.PhysicalCacheInvariant.Cache, hchain] at hcache
  obtain ⟨h, age, spare, hi, hr, hm⟩ := hcache
  have hlimit : (PalPeg.GalilScaffoldCounter.value x.vm.remaining).toNat ≤ h := by
    have hh : periodLength wm = h := PalPeg.ChainBoundaryCache.cursor_length hi.cursor
    rw [← hh]
    exact hbound hmode wm hchain
  have hcanonical : PalPeg.GalilScaffoldCounter.Canonical x.vm.remaining := by
    obtain ⟨T, hT, _⟩ := hcore
    obtain ⟨seg, ha, _⟩ := hT.1.2.counters 1 x.vm.remaining rfl
    rw [← ha]
    exact PalPeg.LocalCounter.absCtr_canonical _ _
  have hmirror := running_mirror rest w x p hcore hmode hrem
    (PalPeg.PhysicalCacheInvariant.mirrorMagnitude x h) hm
  have hspare := running_spare rest w x p hcore hmode hrem spare hr
  have hshape := running_shaped rest w x p (PalPeg.PhysicalCacheInvariant.running_shape he)
    hmode hrem htick
  rw [tickFun_shift w x wm hchain hmode hrem] at hshape ⊢
  rw [← mirrorMagnitude_shift x wm hmode hrem hcanonical h hlimit] at hmirror
  generalize hstep : (workStep rest).apply blankM p none = result at hshape hspare hmirror ⊢
  apply PalPeg.PhysicalCacheInvariant.of_watching_cache (chainShiftOne wm) (Or.inl rfl)
  · obtain ⟨T, hT, ht⟩ := hshape
    exact ⟨T, hT.1, ht⟩
  · exact ⟨h, age, dec spare, PalPeg.ChainBoundaryCache.inv_shift hi, hspare, hmirror⟩

/-- info: 'PalPeg.PhysicalShift.remainingBound_onRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms remainingBound_onRun

/-- info: 'PalPeg.PhysicalShift.running' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms running

/-- On a legal shift run the fallback copy walker is idle. The plateau is
already in scan mode, so only the tracked pre-trace needs this field. -/
theorem copyIdle_onRun (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ)
    (hpre : PalPeg.CloseoutCheckW.PreTraceIMW centreC placeC 0 1 0 w st Tc)
    (m : PalPeg.LocalReplayParked.Mirrored1 (PalPeg.LocalBlankState.tapeCount 0))
    (hon : PalPeg.LocalShadowConcrete.OnRun (PalPeg.ShadowedLocalFinal.localGood (spare := 0))
      (PalPeg.ShadowedLocalFinal.postPhase 0 1 0) w
      (PalPeg.ShadowedLocalFinal.heldAfter (Tc w.length) st) m)
    (hnotFrozen : ¬ PalPeg.ShadowedLocalFinal.frozenAt w m)
    (hmode : (PalPeg.LocalSysConcrete.absSC m).ctl.mode = .shift) :
    CopyIdle (PalPeg.LocalSysConcrete.absSC m).vm := by
  rcases hon with htracked | ⟨hpost, _, _, _⟩
  · obtain ⟨k, j, _, hsource⟩ := htracked.track
    have hm : (st (min k (Tc w.length))).ctl.mode = .shift := by
      have hctl := congrArg (fun z : State GalilVM => z.ctl.mode) hsource
      exact hctl.symm.trans hmode
    have hc := PalPeg.CloseoutRadPack3.copyIdle_trace centreC placeC 0 1 0
      hpre.base.pre (min k (Tc w.length)) (Nat.min_le_right _ _) hm
    change CopyIdle (PalPeg.LocalReplayParked.absState'' m.vm).vm
    rw [hsource]
    exact hc
  · rcases hpost with hplateau | hfrozen
    · have hbad := hplateau.scan.symm.trans hmode
      cases hbad
    · exact (hnotFrozen hfrozen).elim

/-- info: 'PalPeg.PhysicalShift.copyIdle_onRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms copyIdle_onRun

/-- Shift exhaustion changes only mode and the refreshed output. -/
noncomputable def exited (w : List (Fin 2)) (x : State GalilVM) : State GalilVM :=
  ⟨{x.ctl with mode := .scan, output := refreshFun (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w) x.vm x.ctl.output}, x.vm⟩

theorem tickFun_exit (w : List (Fin 2)) (x : State GalilVM) (hmode : x.ctl.mode = .shift)
    (hdone : (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w).remainingPos x.vm = false) :
    tickFun (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w)
      (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x = exited w x := by
  simp only [tickFun, hmode, hdone, Bool.false_eq_true, if_false, exited]

/-- An exhausted represented countdown has zero natural magnitude, so the
rebuilt h mirror already holds exactly the value needed in scan mode. -/
theorem exhausted_magnitude (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : CoreEnc w x p)
    (hdone : (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w).remainingPos x.vm = false) :
    (PalPeg.GalilScaffoldCounter.value x.vm.remaining).toNat = 0 := by
  obtain ⟨seg, ha, _⟩ := he.1.2.counters 1 x.vm.remaining rfl
  have hcanonical : PalPeg.GalilScaffoldCounter.Canonical x.vm.remaining := by
    rw [← ha]; exact PalPeg.LocalCounter.absCtr_canonical _ _
  have hz : PalPeg.GalilScaffoldCounter.positive x.vm.remaining = false := by
    change (_ || _) = false at hdone
    exact (Bool.or_eq_false_iff.mp hdone).1
  have hp := PalPeg.GalilScaffoldCounter.positive_iff _ hcanonical
  have hn : ¬ 0 < PalPeg.GalilScaffoldCounter.value x.vm.remaining :=
    fun h => Bool.false_ne_true (hz.symm.trans (hp.mpr h))
  omega

theorem cache_exited (w : List (Fin 2)) (x : State GalilVM)
    (hz : (PalPeg.GalilScaffoldCounter.value x.vm.remaining).toNat = 0)
    (bit : Bool) (tape mirror : STape Γm) :
    PalPeg.PhysicalCacheInvariant.Cache (exited w x) bit tape mirror ↔
      PalPeg.PhysicalCacheInvariant.Cache x bit tape mirror := by
  cases hc : x.vm.chain <;>
    simp [PalPeg.PhysicalCacheInvariant.Cache, exited, hc,
      PalPeg.PhysicalCacheInvariant.mirrorMagnitude, hz]

/-- Exhaustion leaves every non-head, non-retired-program tape in place. -/
theorem ideal_exit_kept (rest : RestCommands) (p : CoreState) (hslot : p.1.slot.val = 0)
    (hmode : p.1.ctl.mode = .shift)
    (hdone : remainsTest p.1.polarity (fun j => readWin blankM microRadius (p.2 j)) = false)
    (slot : Slot) (hhead : ∀ v i, slot ≠ headSlot v i)
    (hidle : ∀ i, slot ≠ progSlotOf (!p.1.fppLive) i) :
    (idealRun (workRule rest) blankM p none 12).2 (slotIndex slot) = p.2 (slotIndex slot) := by
  rw [ideal_other rest p hslot slot hhead]
  simp only [ruleActs, hmode, hdone, Bool.false_eq_true, if_false]
  rw [withErase_at_other p.1.fppLive _ _ slot hidle]
  rfl

/-- The old exit row preserves the full common invariant, including free
counter shapes and the completed h mirror. -/
theorem ideal_exit (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : CoreState) (he : PalPeg.PhysicalCacheInvariant.CoreInv w x p)
    (hmode : x.ctl.mode = .shift)
    (hdone : (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w).remainingPos x.vm = false) :
    PalPeg.PhysicalCacheInvariant.CoreInv w
      (tickFun (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w)
        (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x)
      (idealRun (workRule rest) blankM p none 12) := by
  let T := fun slot => p.2 (slotIndex slot)
  have hT : tapesOf T = p.2 := by funext j; simp [T, tapesOf]
  have hcore : CoreEnc w x p := he.1.1
  have hm : p.1.ctl.mode = .shift := by
    have hc := congrArg PalPeg.GalilScaffoldController.Control.mode hcore.1.1.ctl
    exact hc.trans hmode
  have hd : remainsTest p.1.polarity (fun j => readWin blankM microRadius (tapesOf T j)) = false := by
    rw [remainsTest_eq hcore.1.2 (by decide : 1 ≤ microRadius) micro_le_margin centreC placeC 0 1 0 w]
    exact hdone
  have hencoded := shift_exit_of_tick margin centreC placeC 0 1 0 w
    (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x p.1 T rest none
    fppBound_gt_start (by decide : 1+3 ≤ microRadius) (by decide : 2 ≤ microRadius)
    (by decide : 1 ≤ microRadius) micro_le_margin (by decide : microRadius ≤ margin+1)
    hcore.2.1 hcore.2.2 hm hmode hd hdone hcore.1
  have hbits := (tickPhysRule_bits 1 0 fppBound_gt_start (by decide : 1+3 ≤ microRadius)
    (by decide : 2 ≤ microRadius) rest p.1 T none hcore.2.1).1
  have hb := PalPeg.PhysicalBoundary.macroBoundary_tickRule
    (fun q _ ws => ruleNext 1 0 fppBound_gt_start q ws) (modeCommands 0 rest)
    (fun q _ ws => ruleActs 1 0 q ws)
    (fun q _ ws j => ruleActs_length 1 0 (by decide : 1+3 ≤ microRadius) q ws j)
    w x p none hcore
  simp only [← tickPhysRule_eq 1 0 fppBound_gt_start (by decide) (by decide) rest,
    ← workRule_eq] at hb
  simp only [← workRule_eq, hT, Prod.eta] at hencoded hbits
  rw [hT] at hd
  have hk := ideal_exit_kept rest p hcore.2.1 hm hd
  generalize hrun : idealRun (workRule rest) blankM p none 12 = result at hencoded hbits hb hk ⊢
  simp only [ruleNext, hm, hd, Bool.false_eq_true, if_false, shiftExitNext] at hbits
  refine ⟨⟨⟨hencoded, hb⟩, ?_⟩, ?_⟩
  · intro c
    obtain ⟨seg, hs⟩ := he.1.2 c
    refine ⟨seg, ?_⟩
    change result.2 (slotIndex (counterSlot c)) = _
    rw [hk (counterSlot c) (by intros; simp [counterSlot, headSlot])
      (by intro i; cases p.1.fppLive <;> simp [counterSlot, progSlotOf])]
    exact hs
  · rw [tickFun_exit w x hmode hdone, hbits]
    rw [show result.2 PalPeg.PhysicalSpare.spareIndex = p.2 PalPeg.PhysicalSpare.spareIndex from
      hk (counterSlot 10) (by intros; simp [counterSlot, headSlot])
        (by intro i; cases p.1.fppLive <;> simp [counterSlot, progSlotOf])]
    rw [show result.2 PalPeg.PhysicalPeriodMirror.mirrorIndex = p.2 PalPeg.PhysicalPeriodMirror.mirrorIndex from
      hk (mirrorSlot 5) (by intros; simp [mirrorSlot, headSlot])
        (by intro i; cases p.1.fppLive <;> simp [mirrorSlot, progSlotOf])]
    exact (cache_exited w x (exhausted_magnitude w x p hcore hdone) _ _ _).mpr he.2

/-- The real shift exit restores scan mode and h without another physical tick. -/
theorem running_exit (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : CoreState) (he : PalPeg.PhysicalCacheInvariant.Running w x p)
    (hmode : x.ctl.mode = .shift)
    (hdone : (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w).remainingPos x.vm = false) :
    PalPeg.PhysicalCacheInvariant.Running w
      (tickFun (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w)
        (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x)
      ((workStep rest).apply blankM p none) := by
  have hi := fun T hT => ideal_exit rest w x (p.1, T) hT hmode hdone
  exact PalPeg.PhysicalCacheInvariant.running_fused (workRule rest) w x _ p none he hi

/-- info: 'PalPeg.PhysicalShift.running_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms running_exit

/-- Both branches of shift use the same common encoding and physical step.
The original OR guard is resolved using the run's copy-idleness fact. -/
theorem running_mode (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : CoreState) (he : PalPeg.PhysicalCacheInvariant.Running w x p)
    (hmode : x.ctl.mode = .shift) (hcopy : CopyIdle x.vm) (hbound : RemainingBound x)
    {y : State GalilVM}
    (htick : Tick (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x y) :
    PalPeg.PhysicalCacheInvariant.Running w
      (tickFun (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w)
        (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 x)
      ((workStep rest).apply blankM p none) := by
  by_cases hrem : PalPeg.GalilScaffoldCounter.positive x.vm.remaining = true
  · exact running rest w x p he hmode hrem hbound htick
  · have hc : PalPeg.FrameFunction.copyRemainingTest x.vm.fpp = false := by
      rcases (copyIdle_iff _).mp hcopy with hc | hc <;>
        simp [PalPeg.FrameFunction.copyRemainingTest, hc]
    apply running_exit rest w x p he hmode
    change (_ || _) = false
    apply Bool.or_eq_false_iff.mpr
    exact ⟨Bool.eq_false_iff.mpr hrem, hc⟩

/-- info: 'PalPeg.PhysicalShift.running_mode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms running_mode

end PalPeg.PhysicalShift
