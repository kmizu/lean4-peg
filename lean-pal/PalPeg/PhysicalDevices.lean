import PalPeg.PhysicalEncoding

/-!
# The tape encoding as a product of virtual devices

`EncTapes` speaks about seven kinds of virtual device, each on its own slots: the four input
views (a real-time queue with two stacks), the preparation and search programs (with their
idle halves), the sixteen counters together with their mirrors, the three place stacks, and
the chain's period and answer tapes.

This module states each device's representation on its own, proves that `EncTapes` is exactly
their conjunction (plus the margins), and gives every device a *keep* lemma: a device whose
abstract value, control bits and slots did not change is still represented. A step of the
machine is then proved device by device — the devices it drives by their own operation lemmas,
all others by `keep` — and `encTapes_of_devices` composes them. No step has to reopen the
representation of a device it does not touch.
-/
set_option autoImplicit false
namespace PalPeg.PhysicalDevices
open PalPeg.PhysicalEncoding
open PalPeg.Program (STape)
open PalPeg.LocalCounter (Seg)
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply

section Devices
variable (margin : ℕ) (x : State GalilVM)

/-- An input view: its twelve slots hold a represented view of the abstract head. -/
def ViewDev (gap : Fin 4 → Bool) (micro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl)
    (tapes : Slot → STape Γm) (v : Fin 4) : Prop :=
  ∀ head, headOf x v = some head →
    ∃ (view : PalPeg.LocalInputView.InputView) (viewTapes : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc),
      PalPeg.LocalArrival.absHead' view [] = head ∧
        PalPeg.ConcreteLocalMachine.ViewRep margin view (gap v) (micro v) viewTapes ∧
        (∀ i, tapes (.inl (v, i)) = mapTape encCell (viewTapes i)) ∧
          PalPeg.LocalViewCells.ViewCells view ∧ PalPeg.LocalInputView.WF view

/-- The verifier's view while the chain is idle. -/
def IdleViewDev (gap : Fin 4 → Bool) (micro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl)
    (tapes : Slot → STape Γm) : Prop :=
  headOf x 3 = none → HeadSlotsRep margin gap micro tapes 3

/-- The preparation program: live half represented, idle half padded. -/
def FppDev (fppLive : Bool) (tapes : Slot → STape Γm) : Prop :=
  (∀ i : Fin 9, tapes (progSlotOf fppLive i) =
      padLeft margin (mapTape encProg (encTape (x.vm.fpp.program.config.tapes i)))) ∧
    ∀ i : Fin 9, ∃ raw : STape (Fin 9),
      tapes (progSlotOf (!fppLive) i) = padLeft margin (mapTape encProg raw)

/-- The search program's live half. -/
def DpDev (dpLive : Bool) (tapes : Slot → STape Γm) : Prop :=
  ∀ i : Fin 12, tapes (dpSlotOf dpLive i) =
    padLeft margin (mapTape encProg (encTape (x.vm.dp.config.tapes i)))

/-- A counter together with the mirrors that copy it. -/
def CounterDev (polarity : Fin 16 → Bool) (tapes : Slot → STape Γm) (c : Fin 16) : Prop :=
  (∀ value, counterOf x c = some value →
    ∃ segments : STape Seg, PalPeg.LocalCounter.absCtr segments (polarity c) = value ∧
      tapes (counterSlot c) = padLeft margin (mapTape encSeg segments)) ∧
  ∀ m : Fin 7, mirrorSource m = c → ∀ value, counterOf x c = some value →
    ∃ segments : STape Seg, PalPeg.LocalCounter.absCtr segments (polarity c) = value ∧
      tapes (mirrorSlot m) = padLeft margin (mapTape encSeg segments)

/-- A place stack. -/
def PlaceDev (tapes : Slot → STape Γm) (i : Fin 3) : Prop :=
  ∀ place, placeOf x i = some place →
    ∃ (stackTape : STape PalPeg.CloseoutCoreStep.Γc) (junk : List (Option (Fin 2))),
      PalPeg.ConcreteLocalMachine.Sealed junk ∧
        PalPeg.ConcreteLocalMachine.StackTape stackTape
          (place.letters.map (fun letter => some letter) ++ junk) ∧
        tapes (placeSlot i) = padLeft margin (mapTape encCell stackTape)

/-- The chain's period tape. -/
def PeriodDev (tapes : Slot → STape Γm) : Prop :=
  ∀ tape, periodOf x = some tape →
    tapes (.inr (.inr (.inr (.inr (.inl ()))))) = padLeft margin (mapTape encToken (encPeriod tape))

/-- The chain's answer tape. -/
def AnswerDev (tapes : Slot → STape Γm) : Prop :=
  ∀ tape, answerOf x = some tape →
    tapes (.inr (.inr (.inr (.inl ())))) = padLeft margin (mapTape encProg (encTape tape))

end Devices

/-- **The encoding is the product of its devices**, plus the margins. -/
theorem encTapes_iff_devices (margin : ℕ) (x : State GalilVM) (polarity : Fin 16 → Bool)
    (gap : Fin 4 → Bool) (micro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl)
    (fppLive dpLive : Bool) (tapes : Slot → STape Γm) :
    EncTapes margin x polarity gap micro fppLive dpLive tapes ↔
      (∀ slot, margin ≤ PalPeg.Local.pos (tapes slot)) ∧
        (∀ v, ViewDev margin x gap micro tapes v) ∧ IdleViewDev margin x gap micro tapes ∧
        FppDev margin x fppLive tapes ∧ DpDev margin x dpLive tapes ∧
        (∀ c, CounterDev margin x polarity tapes c) ∧ (∀ i, PlaceDev margin x tapes i) ∧
        PeriodDev margin x tapes ∧ AnswerDev margin x tapes := by
  constructor
  · intro h
    refine ⟨h.margins, h.heads, h.idleHead, ⟨h.fpp, h.idleShape⟩, h.dp,
      fun c => ⟨h.counters c, fun m hm value hvalue => ?_⟩, h.places, h.period, h.answer⟩
    subst hm
    exact h.mirrors m value hvalue
  · rintro ⟨hmargins, hviews, hidle, ⟨hfpp, hidleShape⟩, hdp, hcounters, hplaces, hperiod,
      hanswer⟩
    exact
      { margins := hmargins
        heads := hviews
        idleHead := hidle
        fpp := hfpp
        dp := hdp
        idleShape := hidleShape
        counters := fun c => (hcounters c).1
        places := hplaces
        mirrors := fun m value hvalue => (hcounters (mirrorSource m)).2 m rfl value hvalue
        period := hperiod
        answer := hanswer }

/-- Assemble the encoding from its devices. -/
theorem encTapes_of_devices {margin : ℕ} {x : State GalilVM} {polarity : Fin 16 → Bool}
    {gap : Fin 4 → Bool} {micro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl}
    {fppLive dpLive : Bool} {tapes : Slot → STape Γm}
    (hmargins : ∀ slot, margin ≤ PalPeg.Local.pos (tapes slot))
    (hviews : ∀ v, ViewDev margin x gap micro tapes v) (hidle : IdleViewDev margin x gap micro tapes)
    (hfpp : FppDev margin x fppLive tapes) (hdp : DpDev margin x dpLive tapes)
    (hcounters : ∀ c, CounterDev margin x polarity tapes c)
    (hplaces : ∀ i, PlaceDev margin x tapes i)
    (hperiod : PeriodDev margin x tapes) (hanswer : AnswerDev margin x tapes) :
    EncTapes margin x polarity gap micro fppLive dpLive tapes :=
  (encTapes_iff_devices margin x polarity gap micro fppLive dpLive tapes).mpr
    ⟨hmargins, hviews, hidle, hfpp, hdp, hcounters, hplaces, hperiod, hanswer⟩

section Keep
/-! ## Devices the step does not drive -/
variable {margin : ℕ} {x y : State GalilVM} {tapes newTapes : Slot → STape Γm}

theorem viewDev_keep {gap newGap : Fin 4 → Bool}
    {micro newMicro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl} {v : Fin 4}
    (h : ViewDev margin x gap micro tapes v) (hhead : headOf y v = headOf x v)
    (hgap : newGap v = gap v) (hmicro : newMicro v = micro v)
    (hslots : ∀ i, newTapes (.inl (v, i)) = tapes (.inl (v, i))) :
    ViewDev margin y newGap newMicro newTapes v := by
  intro head hy
  obtain ⟨view, viewTapes, habs, hrep, hs, hcells, hwf⟩ := h head (hhead ▸ hy)
  exact ⟨view, viewTapes, habs, hgap ▸ hmicro ▸ hrep, fun i => (hslots i).trans (hs i), hcells, hwf⟩

theorem idleViewDev_keep {gap newGap : Fin 4 → Bool}
    {micro newMicro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl}
    (h : IdleViewDev margin x gap micro tapes) (hhead : headOf y 3 = headOf x 3)
    (hgap : newGap 3 = gap 3) (hmicro : newMicro 3 = micro 3)
    (hslots : ∀ i, newTapes (.inl (3, i)) = tapes (.inl (3, i))) :
    IdleViewDev margin y newGap newMicro newTapes := by
  intro hnone
  obtain ⟨view, viewTapes, hrep, hs, hcells, hwf⟩ := h (hhead ▸ hnone)
  exact ⟨view, viewTapes, hgap ▸ hmicro ▸ hrep, fun i => (hslots i).trans (hs i), hcells, hwf⟩

theorem fppDev_keep {fppLive : Bool} (h : FppDev margin x fppLive tapes)
    (hprog : ∀ i, y.vm.fpp.program.config.tapes i = x.vm.fpp.program.config.tapes i)
    (hslots : ∀ i b, newTapes (progSlotOf b i) = tapes (progSlotOf b i)) :
    FppDev margin y fppLive newTapes :=
  ⟨fun i => by rw [hslots, hprog]; exact h.1 i,
    fun i => by obtain ⟨raw, hraw⟩ := h.2 i; exact ⟨raw, (hslots i _).trans hraw⟩⟩

theorem dpDev_keep {dpLive : Bool} (h : DpDev margin x dpLive tapes)
    (hprog : ∀ i, y.vm.dp.config.tapes i = x.vm.dp.config.tapes i)
    (hslots : ∀ i, newTapes (dpSlotOf dpLive i) = tapes (dpSlotOf dpLive i)) :
    DpDev margin y dpLive newTapes :=
  fun i => by rw [hslots, hprog]; exact h i

theorem counterDev_keep {polarity newPolarity : Fin 16 → Bool} {c : Fin 16}
    (h : CounterDev margin x polarity tapes c) (hvalue : counterOf y c = counterOf x c)
    (hpolarity : newPolarity c = polarity c)
    (hslot : newTapes (counterSlot c) = tapes (counterSlot c))
    (hmirrors : ∀ m, mirrorSource m = c → newTapes (mirrorSlot m) = tapes (mirrorSlot m)) :
    CounterDev margin y newPolarity newTapes c := by
  refine ⟨fun value hv => ?_, fun m hm value hv => ?_⟩
  · obtain ⟨seg, habs, hs⟩ := h.1 value (hvalue ▸ hv)
    exact ⟨seg, hpolarity ▸ habs, hslot.trans hs⟩
  · obtain ⟨seg, habs, hs⟩ := h.2 m hm value (hvalue ▸ hv)
    exact ⟨seg, hpolarity ▸ habs, (hmirrors m hm).trans hs⟩

theorem placeDev_keep {i : Fin 3} (h : PlaceDev margin x tapes i)
    (hplace : placeOf y i = placeOf x i) (hslot : newTapes (placeSlot i) = tapes (placeSlot i)) :
    PlaceDev margin y newTapes i := by
  intro place hp
  obtain ⟨stackTape, junk, hsealed, hstack, hs⟩ := h place (hplace ▸ hp)
  exact ⟨stackTape, junk, hsealed, hstack, hslot.trans hs⟩

theorem periodDev_keep (h : PeriodDev margin x tapes) (hperiod : periodOf y = periodOf x)
    (hslot : newTapes (.inr (.inr (.inr (.inr (.inl ()))))) =
      tapes (.inr (.inr (.inr (.inr (.inl ())))))) :
    PeriodDev margin y newTapes :=
  fun tape ht => hslot.trans (h tape (hperiod ▸ ht))

theorem answerDev_keep (h : AnswerDev margin x tapes) (hanswer : answerOf y = answerOf x)
    (hslot : newTapes (.inr (.inr (.inr (.inl ())))) = tapes (.inr (.inr (.inr (.inl ()))))) :
    AnswerDev margin y newTapes :=
  fun tape ht => hslot.trans (h tape (hanswer ▸ ht))

end Keep

/-- `encTapes_headStep`, device by device: one view moves, every other device is kept. -/
theorem encTapes_headStep_dev (margin : ℕ) (x y : State GalilVM) (polarity : Fin 16 → Bool)
    (gap newGap : Fin 4 → Bool) (micro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl)
    (fppLive dpLive : Bool) (tapes newTapes : Slot → STape Γm)
    (henc : EncTapes margin x polarity gap micro fppLive dpLive tapes)
    (v : Fin 4) (head : PalPeg.GalilScaffoldInputHead.PlaceHead)
    (hhead : headOf y v = some head)
    (hother : ∀ v' : Fin 4, v' ≠ v → headOf y v' = headOf x v')
    (hcounters : counterOf y = counterOf x) (hplaces : placeOf y = placeOf x)
    (hfpp : ∀ i, y.vm.fpp.program.config.tapes i = x.vm.fpp.program.config.tapes i)
    (hdp : ∀ i, y.vm.dp.config.tapes i = x.vm.dp.config.tapes i)
    (hperiod : periodOf y = periodOf x) (hanswer : answerOf y = answerOf x)
    (hgapOther : ∀ v' : Fin 4, v' ≠ v → newGap v' = gap v')
    (view : PalPeg.LocalInputView.InputView)
    (viewTapes : Fin 12 → STape PalPeg.CloseoutCoreStep.Γc)
    (habsView : PalPeg.LocalArrival.absHead' view [] = head)
    (hrep : PalPeg.ConcreteLocalMachine.ViewRep margin view (newGap v) (micro v) viewTapes)
    (hcells : PalPeg.LocalViewCells.ViewCells view) (hwf : PalPeg.LocalInputView.WF view)
    (hslots : ∀ i, newTapes (headSlot v i) = mapTape encCell (viewTapes i))
    (hkept : ∀ slot, (∀ i : Fin 12, slot ≠ headSlot v i) → newTapes slot = tapes slot)
    (hmargin : ∀ i : Fin 12, margin ≤ PalPeg.Local.pos (newTapes (headSlot v i))) :
    EncTapes margin y polarity newGap micro fppLive dpLive newTapes := by
  obtain ⟨hmargins, hviews, hidle, hfppDev, hdpDev, hcounterDevs, hplaceDevs, hperiodDev,
    hanswerDev⟩ := (encTapes_iff_devices margin x polarity gap micro fppLive dpLive tapes).mp henc
  have hkeep : ∀ slot, (∀ i : Fin 12, slot ≠ headSlot v i) → newTapes slot = tapes slot := hkept
  have hviewKeep : ∀ v', v' ≠ v → ∀ i, newTapes (.inl (v', i)) = tapes (.inl (v', i)) :=
    fun v' hv i => hkeep _ fun k h => hv (show v' = v ∧ i = k by simpa [headSlot] using h).1
  have hnew : ViewDev margin y newGap micro newTapes v := fun head' h' =>
    ⟨view, viewTapes, (Option.some.inj (hhead.symm.trans h')) ▸ habsView, hrep, hslots, hcells, hwf⟩
  refine encTapes_of_devices ?_ (fun v' => ?_) ?_
    (fppDev_keep hfppDev hfpp fun i b => hkeep _ fun k => by cases b <;> simp [progSlotOf])
    (dpDev_keep hdpDev hdp fun i => hkeep _ fun k => by cases dpLive <;> simp [dpSlotOf])
    (fun c => counterDev_keep (hcounterDevs c) (congrFun hcounters c) rfl
      (hkeep _ fun k => by simp) fun m _ => hkeep _ fun k => by simp)
    (fun i => placeDev_keep (hplaceDevs i) (congrFun hplaces i) (hkeep _ fun k => by simp))
    (periodDev_keep hperiodDev hperiod (hkeep _ fun k => by simp))
    (answerDev_keep hanswerDev hanswer (hkeep _ fun k => by simp))
  · intro slot
    by_cases hh : ∃ i : Fin 12, slot = headSlot v i
    · obtain ⟨i, rfl⟩ := hh
      exact hmargin i
    · rw [hkeep slot fun i hi => hh ⟨i, hi⟩]
      exact hmargins slot
  · by_cases hv : v' = v
    · exact hv ▸ hnew
    · exact viewDev_keep (hviews v') (hother v' hv) (hgapOther v' hv) rfl (hviewKeep v' hv)
  · by_cases hv3 : v = 3
    · intro h3
      rw [← hv3, hhead] at h3
      cases h3
    · exact idleViewDev_keep hidle (hother 3 fun h => hv3 h.symm) (hgapOther 3 fun h => hv3 h.symm)
        rfl (hviewKeep 3 fun h => hv3 h.symm)

/-- info: 'PalPeg.PhysicalDevices.encTapes_iff_devices' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms encTapes_iff_devices

end PalPeg.PhysicalDevices
