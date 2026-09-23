import PalPeg.PhysicalWatchEntry
import PalPeg.PhysicalPeriodMirror

/-!
# Carrying the boundary cache through the actual machine

The invariant strengthens the existing encoding with the shape of inactive
counter tapes, the boundary spare and the saved semiperiod in both watch and
broken states. Boot/feed use their existing steps, and every connected count
branch preserves this same invariant. The shift-dependent mirror value is
specified here; its exchange and rebuilding transitions remain to be connected.
-/
set_option autoImplicit false
namespace PalPeg.PhysicalCacheInvariant
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract PalPeg.PhysicalSpare
open PalPeg.PhysicalWatchEntry (CounterShapes ShapedCoreEnc)
open PalPeg.PhysicalBootFeed PalPeg.PhysicalFeed PalPeg.PhysicalScanCount
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.Program (STape)
open PalPeg.Local (pos readWin)
open PalPeg.CloseoutCoreEnc12 PalPeg.LocalStepFusion
open PalPeg.GalilScaffoldCounter (Counter)
open PalPeg.PhysicalPeriodMirror (mirrorIndex)

/-- In scan the mirror stores h. The shift contract reserves the old remaining
carrier for rebuilding one unit per decrement, after lending h to remaining.
This value specifies the intended exchange; the physical shift proof is pending. -/
def mirrorMagnitude (x : State GalilVM) (h : ℕ) : ℕ :=
  if x.ctl.mode = .shift then h - (PalPeg.GalilScaffoldCounter.value x.vm.remaining).toNat else h

/-- Broken chains keep their saved counters until restart uses them. -/
def Cache (x : State GalilVM) (bit : Bool) (tape mirror : STape Γm) : Prop :=
  match x.vm.chain with
  | .watch wm | .broken wm => ∃ h age spare,
      PalPeg.ChainBoundaryCache.Inv h age wm.machine.control spare ∧ Rep bit spare tape ∧
      Rep true (PalPeg.GalilScaffoldCounter.ofNat (mirrorMagnitude x h)) mirror
  | _ => True

def CoreInv (w : List (Fin 2)) (x : State GalilVM) (p : CoreState) : Prop :=
  ShapedCoreEnc w x p ∧ Cache x (p.1.polarity 10) (p.2 spareIndex) (p.2 mirrorIndex)

def Running (w : List (Fin 2)) := PalPeg.MachineStep.sweepClosure blankM (CoreInv w)

def Enc (w : List (Fin 2)) (x : State GalilVM) (p : PhysicalState) : Prop :=
  match p.1 with
  | .inl _ => PalPeg.PhysicalContract.Enc w x p
  | .inr q => Running w x (q, p.2)

theorem enc_initial (w : List (Fin 2)) :
    Enc w initialState (initialControl, fun _ => STape.blankTape blankM) :=
  PalPeg.PhysicalContract.enc_initial w

theorem running_core {w : List (Fin 2)} {x : State GalilVM} {p : CoreState}
    (he : Running w x p) : PalPeg.MachineStep.sweepClosure blankM (CoreEnc w) x p := by
  obtain ⟨T, hT, ht⟩ := he
  exact ⟨T, hT.1.1, ht⟩

theorem running_shape {w : List (Fin 2)} {x : State GalilVM} {p : CoreState}
    (he : Running w x p) : PalPeg.MachineStep.sweepClosure blankM (ShapedCoreEnc w) x p := by
  obtain ⟨T, hT, ht⟩ := he
  exact ⟨T, hT.1, ht⟩

theorem cache_teq {x : State GalilVM} {bit : Bool} {T U M N : STape Γm}
    (hc : Cache x bit T M) (ht : TEqG blankM T U) (hm : TEqG blankM M N) : Cache x bit U N := by
  cases hchain : x.vm.chain <;> simp only [Cache, hchain] at hc ⊢
  all_goals
    obtain ⟨h, age, spare, hi, ⟨seg, ha, he⟩, ⟨raw, hr, hrep⟩⟩ := hc
    exact ⟨h, age, spare, hi, ⟨seg, ha, PalPeg.MachineStep.teqG_trans he ht⟩,
      ⟨raw, hr, PalPeg.MachineStep.teqG_trans hrep hm⟩⟩

theorem running_cache {w : List (Fin 2)} {x : State GalilVM} {p : CoreState}
    (he : Running w x p) : Cache x (p.1.polarity 10) (p.2 spareIndex) (p.2 mirrorIndex) := by
  obtain ⟨T, hT, ht⟩ := he
  exact cache_teq hT.2 (ht spareIndex) (ht mirrorIndex)

/-- The mirror now exposes the exact length consumed by beginShiftVM', not
an unrelated existential size. During shift it stores the rebuilding progress. -/
theorem running_mirror {w : List (Fin 2)} {x : State GalilVM} {p : CoreState}
    (he : Running w x p) (wm : PalPeg.GalilScaffoldChainWatch.State)
    (hchain : x.vm.chain = .watch wm ∨ x.vm.chain = .broken wm) :
    Rep true (PalPeg.GalilScaffoldCounter.ofNat (mirrorMagnitude x (periodLength wm)))
      (p.2 mirrorIndex) := by
  have hc := running_cache he
  have hcache : ∃ h age spare, PalPeg.ChainBoundaryCache.Inv h age wm.machine.control spare ∧
      Rep (p.1.polarity 10) spare (p.2 spareIndex) ∧
      Rep true (PalPeg.GalilScaffoldCounter.ofNat (mirrorMagnitude x h)) (p.2 mirrorIndex) := by
    rcases hchain with hchain | hchain <;> simpa only [Cache, hchain] using hc
  obtain ⟨h, age, spare, hi, _, hm⟩ := hcache
  have hlength : periodLength wm = h := PalPeg.ChainBoundaryCache.cursor_length hi.cursor
  rwa [hlength]

theorem cache_feed (input : Option (Fin 2)) (x : State GalilVM) (bit : Bool) (T M : STape Γm) :
    Cache (feedState input x) bit T M ↔ Cache x bit T M := by
  cases input with
  | none => rfl
  | some a =>
    cases hc : x.vm.chain <;> simp [Cache, mirrorMagnitude, feedState, PalPeg.GalilArriveChain.arriveState',
      PalPeg.GalilArriveChain.arriveVM', PalPeg.GalilArriveChain.arriveChain,
      PalPeg.GalilArriveChain.arriveW, PalPeg.LocalTracking.arriveVM, hc]

/-- The actual twelve-slot arrival leaves every non-head counter at its
step-zero result, including inactive counters omitted by counterOf. -/
theorem arrival_counter (baseActs : InputActs)
    (baseLen : ∀ q i ws j, (baseActs q i ws j).length ≤ microRadius)
    (p : CoreState) (input : Option (Fin 2)) (hslot : p.1.slot.val = 0) (c : Fin 16) :
    (idealRun (arrivalRule baseActs baseLen) blankM p input 12).2 (slotIndex (counterSlot c)) =
      actList blankM (p.2 (slotIndex (counterSlot c)))
        (baseActs p.1 input (fun j => readWin blankM microRadius (p.2 j)) (slotIndex (counterSlot c))) :=
  tickRule_otherSlots (by decide) (fun q _ _ => q) commands baseActs baseLen p input hslot
    (slotIndex (counterSlot c)) (by simp [counterSlot])

/-- Arrival updates only the head slots; its non-head mirror follows the
same bounded action list as an ordinary counter. -/
theorem arrival_mirror (baseActs : InputActs)
    (baseLen : ∀ q i ws j, (baseActs q i ws j).length ≤ microRadius)
    (p : CoreState) (input : Option (Fin 2)) (hslot : p.1.slot.val = 0) :
    (idealRun (arrivalRule baseActs baseLen) blankM p input 12).2 mirrorIndex =
      actList blankM (p.2 mirrorIndex)
        (baseActs p.1 input (fun j => readWin blankM microRadius (p.2 j)) mirrorIndex) :=
  tickRule_otherSlots (by decide) (fun q _ _ => q) commands baseActs baseLen p input hslot
    mirrorIndex (by simp [mirrorIndex, mirrorSlot])

theorem arrival_polarity (baseActs : InputActs)
    (baseLen : ∀ q i ws j, (baseActs q i ws j).length ≤ microRadius)
    (p : CoreState) (input : Option (Fin 2)) (hslot : p.1.slot.val = 0) :
    (idealRun (arrivalRule baseActs baseLen) blankM p input 12).1.polarity = p.1.polarity := by
  generalize hr : idealRun (arrivalRule baseActs baseLen) blankM p input 12 = result
  have hf : headFreeFields result.1 = headFreeFields p.1 := by
    rw [← hr]
    exact tickRule_headFree (by decide) (fun q _ _ => q) commands baseActs baseLen p input hslot
  simp only [headFreeFields, Prod.mk.injEq] at hf
  exact hf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem core_feed (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (input : Option (Fin 2)) (he : CoreInv w x p) :
    CoreInv w (feedState input x) (idealRun feedRule blankM p input 12) := by
  have hc : ∀ c : Fin 16, (idealRun feedRule blankM p input 12).2 (slotIndex (counterSlot c)) =
      p.2 (slotIndex (counterSlot c)) := fun c =>
    arrival_counter (fun _ _ _ _ => []) (by intros; simp) p input he.1.1.2.1 c
  refine ⟨⟨PalPeg.PhysicalFeed.core_feed w x p input he.1.1, ?_⟩, ?_⟩
  · intro c
    change ∃ seg, (idealRun feedRule blankM p input 12).2 (slotIndex (counterSlot c)) = _
    rw [hc c]
    exact he.1.2 c
  · have hp : (idealRun feedRule blankM p input 12).1.polarity = p.1.polarity :=
      arrival_polarity (fun _ _ _ _ => []) (by intros; simp) p input he.1.1.2.1
    rw [hp]
    have hm : (idealRun feedRule blankM p input 12).2 mirrorIndex = p.2 mirrorIndex :=
      arrival_mirror (fun _ _ _ _ => []) (by intros; simp) p input he.1.1.2.1
    change Cache (feedState input x) (p.1.polarity 10)
      ((idealRun feedRule blankM p input 12).2 (slotIndex (counterSlot 10)))
      ((idealRun feedRule blankM p input 12).2 mirrorIndex)
    rw [hc, hm, cache_feed]
    exact he.2

theorem boot_core (w : List (Fin 2)) (input : Option (Fin 2)) :
    CoreInv w (feedState input initialState)
      (idealRun bootRule blankM (bootControl, fun _ => shiftedBlank) input 12) := by
  generalize hr : idealRun bootRule blankM (bootControl, fun _ => shiftedBlank) input 12 = result
  have hb : CoreEnc w (feedState input initialState) result := by
    rw [← hr]
    exact PalPeg.PhysicalBootFeed.boot_core w input
  refine ⟨⟨hb, ?_⟩, ?_⟩
  · intro c
    have hc : result.2 (slotIndex (counterSlot c)) = preparedTapes (counterSlot c) := by
      have ht := arrival_counter bootActs bootActs_bound (bootControl, fun _ => shiftedBlank)
        input boot_boundary.1 c
      have hrule : bootRule = arrivalRule bootActs bootActs_bound := rfl
      rw [← hrule, hr] at ht
      simpa only [bootActs, Equiv.symm_apply_apply, bootActs_prepared] using ht
    change ∃ seg, result.2 (slotIndex (counterSlot c)) = _
    rw [hc]
    exact PalPeg.PhysicalWatchEntry.prepared_shapes c
  · rw [cache_feed]
    simp [Cache, initialState_eq, PalPeg.GalilBootVM.initVM0]

/-- Fuse and sweep while retaining the strengthened invariant in the witness. -/
theorem running_fused (R : ActRule (Fin 2) CoreControl Γm tapeCountM microRadius)
    (w : List (Fin 2)) (x y : State GalilVM) (p : CoreState) (input : Option (Fin 2))
    (he : Running w x p)
    (hstep : ∀ T, CoreInv w x (p.1, T) → CoreInv w y (idealRun R blankM (p.1, T) input 12)) :
    Running w y ((compStep (iterRule R 12)).apply blankM p input) := by
  obtain ⟨T, hT, ht⟩ := he
  have hm : ∀ j, macroRadius ≤ pos (T j) := by
    intro j
    simpa only [Equiv.apply_symm_apply, margin] using hT.1.1.1.2.margins (slotIndex.symm j)
  have hmp : ∀ j, macroRadius ≤ pos (p.2 j) := fun j => (ht j).1 ▸ hm j
  obtain ⟨hc, hteq⟩ := idealStep_congr_teqG (iterRule R 12) blankM p.1 T p.2 ht input
  rw [iterRule_ideal blankM R 12 (p.1, T) input hm, idealIter_eq_idealRun] at hc hteq
  obtain ⟨hr, hs⟩ := compStep_apply (iterRule R 12) blankM p input hmp
  refine ⟨(idealRun R blankM (p.1, T) input 12).2, ?_,
    fun j => PalPeg.MachineStep.teqG_trans (hteq j) (hs j)⟩
  rw [hr]
  change CoreInv w y ((idealStep (iterRule R 12) blankM p input).1, _)
  rw [← hc]
  exact hstep T hT

theorem running_feed (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (input : Option (Fin 2)) (he : Running w x p) :
    Running w (feedState input x) (feedStep.apply blankM p input) :=
  running_fused feedRule w x (feedState input x) p input he
    (fun T hT => core_feed w x (p.1, T) input hT)

theorem boot_sweep (w : List (Fin 2)) (input : Option (Fin 2))
    (T : Fin tapeCountM → STape Γm)
    (hT : ∀ j, TEqG blankM (STape.blankTape blankM) (T j)) :
    Running w (feedState input initialState) (bootStep.apply blankM (bootControl, T) input) := by
  apply sweep_from_blank (iterRule bootRule 12) (CoreInv w) (feedState input initialState)
    bootControl input T (fun _ => shiftedBlank) hT
    (fun _ => shiftedBlank_pos) (fun _ => shiftedBlank_blank)
  rw [iterRule_ideal blankM bootRule 12 (bootControl, fun _ => shiftedBlank) input
    (fun _ => shiftedBlank_pos.ge), idealIter_eq_idealRun]
  exact boot_core w input

theorem enc_running (w : List (Fin 2)) (x : State GalilVM) (p : CoreState) :
    Enc w x (Sum.inr p.1, p.2) ↔ Running w x p := Iff.rfl

/-- All input arrivals, including the first, preserve the same invariant. -/
theorem forward_feed (noneStep : CoreStep) (w : List (Fin 2)) (x : State GalilVM)
    (p : PhysicalState) (a : Fin 2) (he : Enc w x p) :
    Enc w (PalPeg.GalilArriveChain.arriveState' a x)
      ((machineStep noneStep).apply blankM p (some a)) := by
  rcases p with ⟨q, T⟩
  cases q with
  | inl tag =>
    cases tag
    obtain ⟨rfl, hblank⟩ := he
    rw [machine_apply_boot, enc_running]
    exact boot_sweep w (some a) T hblank
  | inr control =>
    rw [machine_apply_feed noneStep a (control, T), enc_running]
    exact running_feed w x (control, T) (some a) he

/-- Starvation retains the cache, using the existing no-input feed step. -/
theorem forward_starved (active : CoreStep) (w : List (Fin 2)) (x : State GalilVM)
    (p : PhysicalState) (he : Enc w x p) (hs : PalPeg.FrameFunction.starvedTest x = true) :
    Enc w x ((PalPeg.PhysicalTickDispatch.machine active).apply blankM p none) := by
  rcases p with ⟨q, T⟩
  cases q with
  | inl tag =>
    cases tag
    obtain ⟨rfl, hblank⟩ := he
    rw [PalPeg.PhysicalTickDispatch.machine, machine_apply_boot, enc_running]
    exact boot_sweep w none T hblank
  | inr control =>
    rw [PalPeg.PhysicalTickDispatch.machine,
      machine_apply_none (PalPeg.PhysicalTickDispatch.guardedStep active) (control, T), enc_running,
      PalPeg.PhysicalTickDispatch.guarded_apply,
      PalPeg.PhysicalTickDispatch.starvedRead_running (running_core he), if_pos hs]
    exact running_feed w x (control, T) none he

/-- info: 'PalPeg.PhysicalCacheInvariant.forward_feed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forward_feed

/-- info: 'PalPeg.PhysicalCacheInvariant.forward_starved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forward_starved

/-- A cache represented on the real tape also holds on the ideal witness. -/
theorem of_shaped_cache {w : List (Fin 2)} {x : State GalilVM} {p : CoreState}
    (he : PalPeg.MachineStep.sweepClosure blankM (ShapedCoreEnc w) x p)
    (hc : Cache x (p.1.polarity 10) (p.2 spareIndex) (p.2 mirrorIndex)) : Running w x p := by
  obtain ⟨T, hT, ht⟩ := he
  exact ⟨T, ⟨hT, cache_teq hc
    ⟨(ht spareIndex).1.symm, fun j => ((ht spareIndex).2 j).symm⟩
    ⟨(ht mirrorIndex).1.symm, fun j => ((ht mirrorIndex).2 j).symm⟩⟩, ht⟩

/-- In watch/broken, the fifteen named counters plus the spare determine
all counter shapes. The unused slot is replaced only in the ideal witness. -/
theorem of_watching_cache {w : List (Fin 2)} {x : State GalilVM} {p : CoreState}
    (wm : PalPeg.GalilScaffoldChainWatch.State)
    (hchain : x.vm.chain = .watch wm ∨ x.vm.chain = .broken wm)
    (he : PalPeg.MachineStep.sweepClosure blankM (CoreEnc w) x p)
    (hc : Cache x (p.1.polarity 10) (p.2 spareIndex) (p.2 mirrorIndex)) : Running w x p := by
  have hhas : ∃ h age spare, PalPeg.ChainBoundaryCache.Inv h age wm.machine.control spare ∧
      Rep (p.1.polarity 10) spare (p.2 spareIndex) ∧
        Rep true (PalPeg.GalilScaffoldCounter.ofNat (mirrorMagnitude x h)) (p.2 mirrorIndex) := by
    rcases hchain with hchain | hchain <;> simpa only [Cache, hchain] using hc
  obtain ⟨h, age, spare, hi, ⟨seg, ha, hseg⟩, _⟩ := hhas
  have hfree : counterOf x 10 = none := by
    rcases hchain with hchain | hchain <;> simp [counterOf, hchain]
  have hused : ∀ c : Fin 16, c ≠ 10 → ∃ value, counterOf x c = some value := by
    intro c hn
    rcases hchain with hchain | hchain <;> fin_cases c <;> simp_all [counterOf]
  obtain ⟨T, hT, ht⟩ := he
  let U := Function.update T spareIndex (padLeft margin (mapTape encSeg seg))
  have hcore : CoreEnc w x (p.1, U) := by
    have hm : margin ≤ pos (padLeft margin (mapTape encSeg seg)) := by rw [pos_padLeft]; omega
    have hp : PalPeg.PhysicalFreeCounter.setPolarity p.1 10 (p.1.polarity 10) = p.1 := by
      unfold PalPeg.PhysicalFreeCounter.setPolarity
      rw [Function.update_eq_self]
    simpa only [hp, U, spareIndex] using
      PalPeg.PhysicalFreeCounter.core_free_counter hT 10 hfree (p.1.polarity 10) _ hm
  have hshape : CounterShapes (fun slot => U (slotIndex slot)) := by
    intro c
    by_cases hn : c = 10
    · subst c
      exact ⟨seg, Function.update_self _ _ _⟩
    · obtain ⟨value, hv⟩ := hused c hn
      obtain ⟨raw, _, hr⟩ := hT.1.2.counters c value hv
      have hj : slotIndex (counterSlot c) ≠ spareIndex := by
        intro hj
        apply hn
        simpa only [spareIndex, counterSlot, Equiv.apply_eq_iff_eq, Sum.inr.injEq, Sum.inl.injEq] using hj
      exact ⟨raw, by simpa only [U, Function.update_of_ne hj] using hr⟩
  apply of_shaped_cache (p := p) _ hc
  refine ⟨U, ⟨hcore, hshape⟩, ?_⟩
  intro j
  by_cases hj : j = spareIndex
  · subst j
    simpa only [U, Function.update_self] using hseg
  · simpa only [U, Function.update_of_ne hj] using ht j

/-- The source cache is supplied by Running; the consume theorem's Inv/Rep
are no longer independent hypotheses of this branch. -/
theorem running_plain (rest : RestCommands) (w : List (Fin 2))
    (x : State GalilVM) (p : CoreState) (he : Running w x p)
    (hmode : x.ctl.mode = .scan) (hstarved : PalPeg.FrameFunction.starvedTest x = false)
    (hclock : 1 < x.ctl.clock) {y : State GalilVM}
    (htick : Tick (galilFrameS (PalPeg.GalilRunSkeleton.PofC
      PalPeg.GalilFinalAssembly2.centreC PalPeg.GalilFinalAssembly2.placeC 0 w) 1 0) 2048 x y)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm) (a : Fin 3)
    (htok : wm.machine.control.period.focus = .plain a)
    (hseen : PalPeg.GalilScaffoldInputHead.read
      (PalPeg.GalilScaffoldChainVerifier.right wm.machine.verifier) = some a)
    (hforward : wm.machine.control.forward = true)
    (hlag : PalPeg.GalilScaffoldCounter.positive wm.lag = true) :
    Running w (countState (PalPeg.PhysicalCountConsume.caughtState x wm))
      ((PalPeg.PhysicalCountSpare.countStep rest).apply blankM p none) := by
  have hc := running_cache he
  rw [Cache, hchain] at hc
  obtain ⟨h, age, spare, hi, hr, hmirror⟩ := hc
  obtain ⟨hnext, nextSpare, hrep, hinv⟩ := PalPeg.PhysicalCountSpare.forward_plain rest w x p
    (running_core he) hmode hstarved hclock htick wm hchain a htok hseen hforward hlag spare h age hi hr
  apply of_watching_cache (PalPeg.GalilScaffoldChainWatch.caught wm) (Or.inl rfl) hnext
  exact ⟨h, age+1, nextSpare, hinv, hrep,
    by simpa only [mirrorMagnitude, countState, PalPeg.PhysicalCountConsume.caughtState,
        hmode, reduceCtorEq, if_false] using
      PalPeg.PhysicalPeriodMirror.count_scan rest w x p (running_core he) hmode hstarved hclock
        (by simp [restartGuardTest, hchain]) h
        (by simpa only [mirrorMagnitude, hmode, reduceCtorEq, if_false] using hmirror)⟩

/-- Entry creates the cache inside the same invariant used by feed and consume.
The source period shape and stored length are supplied from OnRun by the dispatcher. -/
theorem running_entry (work : CoreStep) (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (first last : Fin 3) (xs : List (Fin 3)) (h lag credit : Counter)
    (ver : PalPeg.GalilScaffoldInputHead.PlaceHead)
    (hback : x.vm.chain = .back ⟨[], .first first, xs.map PalPeg.GalilScaffoldChainPeriod.Token.plain ++ [.last last]⟩ h lag credit ver)
    (he : Running w x p) (hmode : x.ctl.mode = .scan)
    (hstarved : PalPeg.FrameFunction.starvedTest x = false) (hclock : 1 < x.ctl.clock)
    (hperiod : PalPeg.ChainStoredPeriod.Stored x.vm.chain) :
    Running w
      (tickFun (PalPeg.FrameFunction.galilFrameFun PalPeg.GalilFinalAssembly2.centreC
        PalPeg.GalilFinalAssembly2.placeC 0 1 0 w)
        (galilFrameS (PalPeg.GalilRunSkeleton.PofC PalPeg.GalilFinalAssembly2.centreC
          PalPeg.GalilFinalAssembly2.placeC 0 w) 1 0) 2048 x)
      ((PalPeg.PhysicalWatchEntry.withWatchEntry work).apply blankM p none) := by
  obtain ⟨hnext, hr⟩ := PalPeg.PhysicalWatchEntry.forward_count work w x p _ h lag credit ver
    hback rfl (running_shape he) hmode hstarved hclock
  apply of_shaped_cache hnext
  have hrestart : restartGuardTest x.vm = false := by simp [restartGuardTest, hback]
  have hactive : x.vm.chain ≠ .idle := by simp [hback]
  rw [PalPeg.PhysicalGuardProbe.tickFun_nonstarved_count _ _ 0 1 0 w _ 2048 x
    hmode hstarved hrestart hclock]
  change Cache (⟨_, backgroundFun _ x.vm⟩ : State GalilVM) _ _ _
  rw [backgroundFun_of_active _ x.vm hactive, hback]
  simp only [chainStepFun, PalPeg.GalilScaffoldChainPeriod.isFirst, if_true, Cache]
  exact ⟨xs.length+1, 0, PalPeg.GalilScaffoldCounter.reset,
    PalPeg.ChainBoundaryCache.inv_ready first last xs, hr,
    by simpa only [mirrorMagnitude, hmode, reduceCtorEq, if_false] using
      PalPeg.PhysicalPeriodMirror.count_entry work w x p (running_core he) hperiod
        first last xs h lag credit ver hback hmode hstarved hclock⟩

/-- info: 'PalPeg.PhysicalCacheInvariant.running_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms running_plain

/-- info: 'PalPeg.PhysicalCacheInvariant.running_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms running_entry

end PalPeg.PhysicalCacheInvariant
