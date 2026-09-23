import PalPeg.PhysicalCountSpare

/-!
# Physical initialization of the watch boundary cache

Back-to-watch resets four segmented tapes in one action per tape and advances
only the period cursor. Counter 10 becomes the spare; its old h mirror is kept.
The shape of inactive counter tapes is explicit: it must be maintained from boot
by the complete dispatcher. This module does not assume a target encoding.
-/
set_option autoImplicit false
namespace PalPeg.PhysicalWatchEntry
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract PalPeg.PhysicalSpare
open PalPeg.PhysicalScanCount PalPeg.PhysicalBootFeed
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilScaffoldCounter (Counter reset)
open PalPeg.GalilScaffoldChainPeriod (Token Tape)
open PalPeg.GalilScaffoldInputHead (PlaceHead)
open PalPeg.Program (STape)
open PalPeg.Local (pos readWin)
open PalPeg.LocalCounter (Seg absCtr)
open PalPeg.CloseoutCoreEnc12
open PalPeg.LocalStepFusion

/-- Physical shape, also required while a logical counter is inactive. -/
def CounterShapes (T : Slot → STape Γm) : Prop :=
  ∀ c : Fin 16, ∃ seg : STape Seg, T (counterSlot c) = padLeft margin (mapTape encSeg seg)

theorem prepared_shapes : CounterShapes preparedTapes := by
  intro c
  exact ⟨PalPeg.LocalBlankState.zeroTape, by simp [preparedTapes, counterCarrier, zeroCounter, counterSlot]⟩

def resets (c : Fin 16) : Bool := decide (c = 10 ∨ c = 13 ∨ c = 14 ∨ c = 15)

def resetSlot : Slot → Bool
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl c)))))) => resets c
  | _ => false

def nextControl (q : CoreControl) : CoreControl :=
  {q with chainTag := .watchers, chainPhase := 0, chainForward := true, chainBroken := false}

def watchState (x : State GalilVM) (v : Tape) (lag credit : Counter) (ver : PlaceHead) : State GalilVM :=
  ⟨x.ctl, {x.vm with chain := .watch ⟨⟨ver, watchControl v⟩, lag, credit⟩}⟩

def nextTapes (T : Slot → STape Γm) (slot : Slot) : STape Γm :=
  if resetSlot slot then (T slot).applyAction blankM (encSeg PalPeg.LocalCounter.sep, .right)
  else if slot = periodSlot then (T slot).applyAction blankM ((T slot).focus, .right)
  else T slot

theorem next_counter (T : Slot → STape Γm) (c : Fin 16) :
    nextTapes T (counterSlot c) = if resets c then
      (T (counterSlot c)).applyAction blankM (encSeg PalPeg.LocalCounter.sep, .right)
      else T (counterSlot c) := by simp [nextTapes, resetSlot, counterSlot, periodSlot]

theorem next_counter_rep {T : Slot → STape Γm} (hs : CounterShapes T) (c : Fin 16)
    (hc : resets c = true) (bit : Bool) :
    ∃ seg : STape Seg, absCtr seg bit = reset ∧
      nextTapes T (counterSlot c) = padLeft margin (mapTape encSeg seg) := by
  obtain ⟨seg, ht⟩ := hs c
  refine ⟨PalPeg.LocalCounter.resetSeg seg, PalPeg.LocalCounter.absCtr_reset seg bit, ?_⟩
  simp only [next_counter, hc, if_true, ht, padded_resetSeg]

theorem next_shapes {T : Slot → STape Γm} (hs : CounterShapes T) : CounterShapes (nextTapes T) := by
  intro c
  cases hc : resets c with
  | false => simpa only [next_counter, hc, Bool.false_eq_true, if_false] using hs c
  | true => obtain ⟨seg, _, ht⟩ := next_counter_rep hs c hc true; exact ⟨seg, ht⟩

theorem next_period {T : Slot → STape Γm} {v : Tape}
    (ht : T periodSlot = padLeft margin (mapTape encToken (encPeriod v))) :
    nextTapes T periodSlot = padLeft margin (mapTape encToken
      (encPeriod (PalPeg.GalilScaffoldChainPeriod.moveRight v))) := by
  simp only [nextTapes, periodSlot, resetSlot, Bool.false_eq_true, if_false, if_true]
  rw [ht, encPeriod_moveRight, padded_token_right]
  rfl

section Entry
variable {w : List (Fin 2)} {x : State GalilVM} {q : CoreControl}
variable {v : Tape} {h lag credit : Counter} {ver : PlaceHead}
variable (hback : x.vm.chain = .back v h lag credit ver)
include hback

theorem heads_unchanged : headOf (watchState x v lag credit ver) = headOf x := by
  funext i
  fin_cases i <;> simp [watchState, headOf, hback]

theorem places_unchanged : placeOf (watchState x v lag credit ver) = placeOf x := by
  funext i
  fin_cases i <;> simp [watchState, placeOf, hback]

theorem control_entry (henc : EncControl w x q) :
    EncControl w (watchState x v lag credit ver) (nextControl q) := by
  refine {henc with chainTag := rfl, chainPhase := rfl, chainForward := rfl, chainBroken := rfl, placeGap := ?_}
  intro i place hp
  exact henc.placeGap i place (by rw [← congrFun (places_unchanged hback) i]; exact hp)

theorem tapes_entry {T : Slot → STape Γm}
    (henc : EncTapes margin x q.polarity q.gap q.micro q.fppLive q.dpLive T)
    (hs : CounterShapes T) :
    EncTapes margin (watchState x v lag credit ver) q.polarity q.gap q.micro
      q.fppLive q.dpLive (nextTapes T) := by
  have hp : T periodSlot = padLeft margin (mapTape encToken (encPeriod v)) :=
    henc.period v (by simp [periodOf, hback])
  refine { margins := ?_, heads := ?_, idleHead := ?_, fpp := ?_, dp := ?_, idleShape := ?_, counters := ?_, places := ?_, mirrors := ?_, period := ?_, answer := ?_ }
  · intro slot
    by_cases hr : resetSlot slot = true
    · have hm := henc.margins slot
      simp only [nextTapes, hr, if_true]
      rcases ht : T slot with ⟨left, focus, right⟩
      rw [ht] at hm
      cases right <;> simp_all [STape.applyAction, pos] <;> omega
    · by_cases he : slot = periodSlot
      · subst slot
        rw [next_period hp, pos_padLeft]
        omega
      · simpa only [nextTapes, if_neg hr, if_neg he] using henc.margins slot
  · intro i head hh
    obtain ⟨view, vt, ha, hv, ht, hc, hw⟩ := henc.heads i head
      (by rw [← congrFun (heads_unchanged hback) i]; exact hh)
    exact ⟨view, vt, ha, hv, fun j => by simpa [nextTapes, resetSlot, periodSlot] using ht j, hc, hw⟩
  · intro hh
    have hn : headOf (watchState x v lag credit ver) 3 = some ver := rfl
    rw [hn] at hh
    cases hh
  · intro i
    cases hl : q.fppLive <;> simpa [nextTapes, resetSlot, progSlotOf, periodSlot, hl, watchState] using henc.fpp i
  · intro i
    cases hl : q.dpLive <;> simpa [nextTapes, resetSlot, dpSlotOf, periodSlot, hl, watchState] using henc.dp i
  · intro i
    obtain ⟨raw, ht⟩ := henc.idleShape i
    refine ⟨raw, ?_⟩
    cases hl : q.fppLive <;> simpa [nextTapes, resetSlot, progSlotOf, periodSlot, hl] using ht
  · intro c value hc
    by_cases hr : resets c = true
    · have hv : value = reset := by
        fin_cases c <;> simp_all [watchState, counterOf, watchControl, resets]
      subst value
      exact next_counter_rep hs c hr (q.polarity c)
    · have hcOld : counterOf x c = some value := by
        fin_cases c <;> simp_all [watchState, counterOf, watchControl, resets]
      obtain ⟨seg, ha, ht⟩ := henc.counters c value hcOld
      exact ⟨seg, ha, by simpa only [next_counter, if_neg hr] using ht⟩
  · intro i place hp
    obtain ⟨stack, junk, hj, ht, hs⟩ := henc.places i place
      (by rw [← congrFun (places_unchanged hback) i]; exact hp)
    exact ⟨stack, junk, hj, ht, by simpa [nextTapes, resetSlot, periodSlot] using hs⟩
  · intro m value hv
    have hvOld : counterOf x (mirrorSource m) = some value := by
      fin_cases m <;> simp_all [mirrorSource, counterOf, watchState]
    obtain ⟨seg, ha, ht⟩ := henc.mirrors m value hvOld
    exact ⟨seg, ha, by simpa [nextTapes, resetSlot, periodSlot] using ht⟩
  · intro tape ht
    have he : tape = PalPeg.GalilScaffoldChainPeriod.moveRight v := by
      simpa [watchState, periodOf, watchControl] using ht.symm
    subst tape
    exact next_period hp
  · intro tape ht
    simp [answerOf, watchState] at ht

theorem core_entry {T : Fin tapeCountM → STape Γm}
    (henc : CoreEnc w x (q, T)) (hs : CounterShapes (fun slot => T (slotIndex slot))) :
    CoreEnc w (watchState x v lag credit ver)
      (nextControl q, fun j => nextTapes (fun slot => T (slotIndex slot)) (slotIndex.symm j)) := by
  refine ⟨⟨control_entry hback henc.1.1, ?_⟩, henc.2⟩
  simpa only [Equiv.symm_apply_apply, nextControl] using tapes_entry hback henc.1.2 hs

end Entry

/-- The stronger physical shape belongs inside the sweep closure, where it is
independent of trailing blanks introduced by a real sweep. -/
def ShapedCoreEnc (w : List (Fin 2)) (x : State GalilVM) (p : CoreState) : Prop :=
  CoreEnc w x p ∧ CounterShapes (fun slot => p.2 (slotIndex slot))

theorem shaped_clockDown {w : List (Fin 2)} {x : State GalilVM} {p : CoreState}
    (henc : PalPeg.MachineStep.sweepClosure blankM (ShapedCoreEnc w) x p) :
    PalPeg.MachineStep.sweepClosure blankM (ShapedCoreEnc w) (countState x) (clockDown p.1, p.2) := by
  obtain ⟨T, hT, he⟩ := henc
  exact ⟨T, ⟨core_clockDown hT.1, hT.2⟩, he⟩

noncomputable def entryActs (ws : Fin tapeCountM → PalPeg.Local.Window Γm macroRadius)
    (j : Fin tapeCountM) : List (Act Γm) :=
  if resetSlot (slotIndex.symm j) then [some (encSeg PalPeg.LocalCounter.sep, .right)]
  else if slotIndex.symm j = periodSlot then
    [some (ws j ⟨macroRadius, by omega⟩, .right)]
  else []

noncomputable def baseRule : ActRule (Fin 2) CoreControl Γm tapeCountM macroRadius where
  nq := fun q _ _ => nextControl q
  acts := fun _ _ ws j => entryActs ws j
  len_le := by intro q input ws j; unfold entryActs; split_ifs <;> simp only [List.length_singleton, List.length_nil] <;> decide

theorem ideal_entry (p : CoreState) (input : Option (Fin 2))
    (hm : ∀ j, macroRadius ≤ pos (p.2 j)) :
    idealStep baseRule blankM p input =
      (nextControl p.1, fun j => nextTapes (fun slot => p.2 (slotIndex slot)) (slotIndex.symm j)) := by
  apply Prod.ext
  · rfl
  · funext j
    simp only [idealStep, baseRule, entryActs, nextTapes, Equiv.apply_symm_apply]
    split_ifs
    · rfl
    · rw [window_centre macroRadius (p.2 j) (hm j)]
      rfl
    · rfl

/-- The usual retired-program erasure also runs on the entry tick. -/
noncomputable def entryRule : ActRule (Fin 2) CoreControl Γm tapeCountM macroRadius where
  nq := fun q _ _ => nextControl q
  acts := fun q _ ws => withErase q.fppLive ws (entryActs ws)
  len_le := by
    intro q input ws j
    exact withErase_length (b := 1) (by decide) q.fppLive ws (entryActs ws)
      (fun k => by unfold entryActs; split_ifs <;> simp) j

noncomputable def entryStep : CoreStep := compStep entryRule

theorem entry_kept (p : CoreState) (input : Option (Fin 2))
    (hm : ∀ j, macroRadius ≤ pos (p.2 j)) (slot : Slot)
    (hoff : ∀ k : Fin 9, slot ≠ progSlotOf (!p.1.fppLive) k) :
    (idealStep entryRule blankM p input).2 (slotIndex slot) =
      nextTapes (fun slot => p.2 (slotIndex slot)) slot := by
  change actList blankM _ (withErase _ _ _ (slotIndex slot)) = _
  rw [withErase_at_other _ _ _ slot hoff]
  have he := congrFun (congrArg Prod.snd (ideal_entry p input hm)) (slotIndex slot)
  simpa only [idealStep, baseRule, Equiv.symm_apply_apply] using he

theorem core_rule {w : List (Fin 2)} {x : State GalilVM} {p : CoreState}
    {v : Tape} {h lag credit : Counter} {ver : PlaceHead}
    (hback : x.vm.chain = .back v h lag credit ver)
    (henc : ShapedCoreEnc w x p) (input : Option (Fin 2)) :
    ShapedCoreEnc w (watchState x v lag credit ver) (idealStep entryRule blankM p input) := by
  let T : Slot → STape Γm := fun slot => p.2 (slotIndex slot)
  let U : Slot → STape Γm := fun slot => (idealStep entryRule blankM p input).2 (slotIndex slot)
  have hm : ∀ j, macroRadius ≤ pos (p.2 j) := by
    intro j
    simpa only [Equiv.apply_symm_apply, margin] using henc.1.1.2.margins (slotIndex.symm j)
  have hk : ∀ slot, (∀ k : Fin 9, slot ≠ progSlotOf (!p.1.fppLive) k) →
      U slot = nextTapes T slot := entry_kept p input hm
  have hi : ∀ k : Fin 9, ∃ raw : STape (Fin 9),
      U (progSlotOf (!p.1.fppLive) k) = padLeft margin (mapTape encProg raw) := by
    intro k
    have hb : ∀ k : Fin 9, entryActs (fun j => readWin blankM macroRadius (tapesOf T j))
        (slotIndex (progSlotOf (!p.1.fppLive) k)) = [] := by
      intro i
      cases p.1.fppLive <;> simp [entryActs, progSlotOf, resetSlot, periodSlot]
    simpa only [U, idealStep, entryRule, T, tapesOf, Equiv.apply_symm_apply] using
      idle_shape_withErase margin (by decide : 1 ≤ macroRadius) (by change macroRadius ≤ macroRadius+1; omega)
        T p.1.fppLive _ hb henc.1.1.2.idleShape k
  refine ⟨⟨⟨control_entry hback henc.1.1.1, ?_⟩, henc.1.2⟩, ?_⟩
  · exact encTapes_idleOnly margin (watchState x v lag credit ver) p.1.polarity p.1.gap p.1.micro
      p.1.fppLive p.1.dpLive (nextTapes T) U (tapes_entry hback henc.1.1.2 henc.2) hk hi
  · intro c
    obtain ⟨seg, hs⟩ := next_shapes henc.2 c
    refine ⟨seg, ?_⟩
    change U (counterSlot c) = _
    rw [hk (counterSlot c) (by intro k; cases p.1.fppLive <;> simp [progSlotOf, counterSlot])]
    exact hs

/-- The real sweep initializes all three new logical counters and its spare,
while retaining the carrier shapes needed by the next lifecycle. -/
theorem running_entry (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (v : Tape) (h lag credit : Counter) (ver : PlaceHead)
    (hback : x.vm.chain = .back v h lag credit ver)
    (henc : PalPeg.MachineStep.sweepClosure blankM (ShapedCoreEnc w) x p)
    (input : Option (Fin 2)) :
    PalPeg.MachineStep.sweepClosure blankM (ShapedCoreEnc w) (watchState x v lag credit ver)
      (entryStep.apply blankM p input) ∧
    Rep ((entryStep.apply blankM p input).1.polarity 10) reset
      ((entryStep.apply blankM p input).2 spareIndex) := by
  obtain ⟨T, hT, he⟩ := henc
  have hm : ∀ j, macroRadius ≤ pos (T j) := by
    intro j
    simpa only [Equiv.apply_symm_apply, margin] using hT.1.1.2.margins (slotIndex.symm j)
  have hmp : ∀ j, macroRadius ≤ pos (p.2 j) := fun j => (he j).1 ▸ hm j
  let U : Fin tapeCountM → STape Γm := (idealStep entryRule blankM (p.1, T) input).2
  have hU : ShapedCoreEnc w (watchState x v lag credit ver) (nextControl p.1, U) :=
    core_rule hback hT input
  obtain ⟨hc, ht⟩ := idealStep_congr_teqG entryRule blankM p.1 T p.2 he input
  obtain ⟨hactual, hsweep⟩ := compStep_apply entryRule blankM p input hmp
  have hcontrol : (entryStep.apply blankM p input).1 = nextControl p.1 := hactual
  have hteq : ∀ j, TEqG blankM (U j) ((entryStep.apply blankM p input).2 j) :=
    fun j => PalPeg.MachineStep.teqG_trans (ht j) (hsweep j)
  constructor
  · refine ⟨U, ?_, hteq⟩
    rw [hcontrol]
    exact hU
  · obtain ⟨seg, ha, hseg⟩ := next_counter_rep hT.2 10 (by decide) (p.1.polarity 10)
    refine ⟨seg, ?_, ?_⟩
    · rw [hcontrol]
      exact ha
    · have hs : U spareIndex = padLeft margin (mapTape encSeg seg) := by
        change (idealStep entryRule blankM (p.1, T) input).2 (slotIndex (counterSlot 10)) = _
        rw [entry_kept (p.1, T) input hm (counterSlot 10)
          (by intro k; cases p.1.fppLive <;> simp [progSlotOf, counterSlot])]
        exact hseg
      rw [← hs]
      exact hteq spareIndex

/-- This result supplies precisely the Inv/Rep consumed by
`PhysicalCountSpare.forward_plain`; neither is assumed at the source. -/
theorem cache_at_entry (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (first last : Fin 3) (xs : List (Fin 3)) (h lag credit : Counter) (ver : PlaceHead)
    (hback : x.vm.chain = .back ⟨[], .first first, xs.map Token.plain ++ [.last last]⟩ h lag credit ver)
    (henc : PalPeg.MachineStep.sweepClosure blankM (ShapedCoreEnc w) x p)
    (input : Option (Fin 2)) :
    let v : Tape := ⟨[], .first first, xs.map Token.plain ++ [.last last]⟩
    PalPeg.MachineStep.sweepClosure blankM (ShapedCoreEnc w) (watchState x v lag credit ver)
      (entryStep.apply blankM p input) ∧
    Rep ((entryStep.apply blankM p input).1.polarity 10) reset
      ((entryStep.apply blankM p input).2 spareIndex) ∧
    PalPeg.ChainBoundaryCache.Inv (xs.length + 1) 0 (watchControl v) reset := by
  obtain ⟨he, hr⟩ := running_entry w x p _ h lag credit ver hback henc input
  exact ⟨he, hr, PalPeg.ChainBoundaryCache.inv_ready first last xs⟩

/-- info: 'PalPeg.PhysicalWatchEntry.cache_at_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cache_at_entry

/-- Entry is selected from finite control and the period's current window. -/
noncomputable def entryRead (q : CoreControl)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm macroRadius) : Bool :=
  countRead q ws && (decide (q.chainTag = .back) &&
    PalPeg.GalilScaffoldChainPeriod.isFirst (decToken (centreRead ws periodSlot)))

noncomputable def withWatchEntry (work : CoreStep) : CoreStep :=
  PalPeg.PhysicalTickDispatch.branchStep entryRead (countedStep entryStep) work

theorem entryRead_running (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (v : Tape) (h lag credit : Counter) (ver : PlaceHead)
    (hback : x.vm.chain = .back v h lag credit ver)
    (hfirst : PalPeg.GalilScaffoldChainPeriod.isFirst v.focus = true)
    (henc : PalPeg.MachineStep.sweepClosure blankM (CoreEnc w) x p)
    (hmode : x.ctl.mode = .scan) (hstarved : PalPeg.FrameFunction.starvedTest x = false)
    (hclock : 1 < x.ctl.clock) :
    entryRead p.1 (fun j => readWin blankM macroRadius (p.2 j)) = true := by
  have hrestart : restartGuardTest x.vm = false := by simp [restartGuardTest, hback]
  unfold entryRead
  rw [countRead_running henc hmode hstarved hrestart hclock, Bool.true_and]
  apply PalPeg.PhysicalTickDispatch.read_from_running
    (fun q ws => decide (q.chainTag = .back) &&
      PalPeg.GalilScaffoldChainPeriod.isFirst (decToken (centreRead ws periodSlot)))
    (fun _ => true) w x p henc
  intro T hT
  have htag : p.1.chainTag = .back := by rw [hT.1.1.chainTag, hback]; rfl
  have hp : centreRead (fun j => readWin blankM macroRadius (T j)) periodSlot = encToken v.focus := by
    simpa only [tapesOf, Equiv.apply_symm_apply, encPeriod, margin] using
      centreRead_periodSlot hT.1.2 (le_refl margin) v (by simp [periodOf, hback])
  simp only [htag, decide_true, Bool.true_and, hp, decToken_encToken, hfirst]

theorem selected_entry (work : CoreStep) (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (v : Tape) (h lag credit : Counter) (ver : PlaceHead)
    (hback : x.vm.chain = .back v h lag credit ver)
    (hfirst : PalPeg.GalilScaffoldChainPeriod.isFirst v.focus = true)
    (henc : PalPeg.MachineStep.sweepClosure blankM (CoreEnc w) x p)
    (hmode : x.ctl.mode = .scan) (hstarved : PalPeg.FrameFunction.starvedTest x = false)
    (hclock : 1 < x.ctl.clock) :
    (withWatchEntry work).apply blankM p none = (countedStep entryStep).apply blankM p none := by
  rw [withWatchEntry, PalPeg.PhysicalTickDispatch.branch_apply,
    entryRead_running w x p v h lag credit ver hback hfirst henc hmode hstarved hclock]
  rfl

/-- info: 'PalPeg.PhysicalWatchEntry.selected_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms selected_entry

/-- The actual nonstarved count successor, including its clock decrement. -/
theorem forward_count (work : CoreStep) (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (v : Tape) (h lag credit : Counter) (ver : PlaceHead)
    (hback : x.vm.chain = .back v h lag credit ver)
    (hfirst : PalPeg.GalilScaffoldChainPeriod.isFirst v.focus = true)
    (henc : PalPeg.MachineStep.sweepClosure blankM (ShapedCoreEnc w) x p)
    (hmode : x.ctl.mode = .scan) (hstarved : PalPeg.FrameFunction.starvedTest x = false)
    (hclock : 1 < x.ctl.clock) :
    PalPeg.MachineStep.sweepClosure blankM (ShapedCoreEnc w)
      (tickFun (PalPeg.FrameFunction.galilFrameFun PalPeg.GalilFinalAssembly2.centreC
        PalPeg.GalilFinalAssembly2.placeC 0 1 0 w)
        (galilFrameS (PalPeg.GalilRunSkeleton.PofC PalPeg.GalilFinalAssembly2.centreC
          PalPeg.GalilFinalAssembly2.placeC 0 w) 1 0) 2048 x)
      ((withWatchEntry work).apply blankM p none) ∧
    Rep (((withWatchEntry work).apply blankM p none).1.polarity 10) reset
      (((withWatchEntry work).apply blankM p none).2 spareIndex) := by
  have hcore : PalPeg.MachineStep.sweepClosure blankM (CoreEnc w) x p := by
    obtain ⟨T, hT, he⟩ := henc
    exact ⟨T, hT.1, he⟩
  rw [selected_entry work w x p v h lag credit ver hback hfirst hcore hmode hstarved hclock]
  have hrestart : restartGuardTest x.vm = false := by simp [restartGuardTest, hback]
  have hactive : x.vm.chain ≠ .idle := by simp [hback]
  obtain ⟨he, hr⟩ := running_entry w x p v h lag credit ver hback henc none
  rw [PalPeg.PhysicalGuardProbe.tickFun_nonstarved_count _ _ 0 1 0 w _ 2048 x
    hmode hstarved hrestart hclock]
  change PalPeg.MachineStep.sweepClosure blankM (ShapedCoreEnc w) (⟨_, backgroundFun _ x.vm⟩ : State GalilVM) _ ∧ _
  rw [backgroundFun_of_active _ x.vm hactive, hback]
  simp only [chainStepFun, hfirst, if_true]
  rw [counted_apply, countRead_running hcore hmode hstarved hrestart hclock]
  simp only [if_true]
  constructor
  · exact shaped_clockDown (x := watchState x v lag credit ver) he
  · exact hr

/-- info: 'PalPeg.PhysicalWatchEntry.forward_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forward_count

end PalPeg.PhysicalWatchEntry
