import PalPeg.PhysicalWatchActions

/-!
# Whole-state encoding of the successful nonhead watch row

Both internal and immediate consumption use the action plan already proved in
PhysicalWatchActions. The verifier remains where it was in this intermediate
state; the existing view executor moves it after the two nonhead stages.
-/
set_option autoImplicit false
namespace PalPeg.PhysicalWatchStep
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract PalPeg.PhysicalWatchActions
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilScaffoldCounter (Counter inc dec)
open PalPeg.GalilScaffoldChainWatch (State)
open PalPeg.Program PalPeg.Local PalPeg.CloseoutCoreEnc12 PalPeg.LocalStepFusion
open PalPeg.LocalCounter (Seg absCtr)
open PalPeg.LocalRoleFusion (logicalStep)
open PalPeg.PhysicalSpare (Rep)
variable {fb db K : ℕ}

def watchAfter (internal : Bool) (wm : PalPeg.GalilScaffoldChainWatch.State) (a : Fin 3) :
    PalPeg.GalilScaffoldChainWatch.State :=
  {wm with machine := {wm.machine with control := PalPeg.GalilScaffoldChainConsume.consume wm.machine.control (some a)}, lag := if internal then dec wm.lag else wm.lag, margin := if internal then wm.margin else inc wm.margin}

def stateAfter (internal : Bool) (x : PalPeg.GalilScaffoldTop.State GalilVM)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (a : Fin 3) : PalPeg.GalilScaffoldTop.State GalilVM :=
  ⟨x.ctl, {x.vm with chain := .watch (watchAfter internal wm a)}⟩

noncomputable def result (hK : 3 ≤ K) (internal : Bool) (q : QPhys fb db) (T : Slot → STape Γm) :=
  logicalStep (rule internal hK) change blankM (q,tapesOf T) none

theorem result_control (hK : 3 ≤ K) (internal : Bool) (q : QPhys fb db) (T : Slot → STape Γm) :
    (result hK internal q T).1 = next internal q (fun j => readWin blankM K (tapesOf T j)) := rfl

theorem result_kept (hK : 3 ≤ K) (internal : Bool) (q : QPhys fb db) (T : Slot → STape Γm)
    (slot : Slot) (h10 : slot ≠ counterSlot 10) (h13 : slot ≠ counterSlot 13)
    (hb : slot ≠ counterSlot (balanceIndex internal)) (h14 : slot ≠ counterSlot 14)
    (h15 : slot ≠ counterSlot 15) (hp : slot ≠ periodSlot) :
    (result hK internal q T).2 (slotIndex slot) = T slot := by
  dsimp only [result, logicalStep, idealStep, rule]
  rw [change_other _ _ _ _ (fun h => h10 (slotIndex.injective h))
    (fun h => h14 (slotIndex.injective h)) (fun h => h15 (slotIndex.injective h))]
  simp only [actions, Equiv.apply_eq_iff_eq, h10, h13, hb, hp, if_false]
  exact tapesOf_apply T slot

theorem result_sign (hK : 3 ≤ K) (internal : Bool) (q : QPhys fb db) (T : Slot → STape Γm)
    (c : Fin 16) (h10 : c ≠ 10) (h13 : c ≠ 13) (hb : c ≠ balanceIndex internal)
    (h14 : c ≠ 14) (h15 : c ≠ 15) :
    (result hK internal q T).1.polarity c = q.polarity c := by
  rw [result_control]
  cases he : event (fun j => readWin blankM K (tapesOf T j)) <;>
    simp [next, he, PalPeg.PhysicalBoundaryRotate.rotatePol, signs, h10, h13, hb, h14, h15]

theorem result_nonchain (hK : 3 ≤ K) (internal : Bool) (q : QPhys fb db) (T : Slot → STape Γm)
    (slot : Slot) (hc : ∀ c, slot ≠ counterSlot c) (hp : slot ≠ periodSlot) :
    (result hK internal q T).2 (slotIndex slot) = T slot :=
  result_kept hK internal q T slot (hc 10) (hc 13) (hc _) (hc 14) (hc 15) hp

theorem event_read (hpad : K ≤ margin) (x : PalPeg.GalilScaffoldTop.State GalilVM)
    (q : QPhys fb db) (T : Slot → STape Γm)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm)
    (he : EncTapes margin x q.polarity q.gap q.micro q.fppLive q.dpLive T) :
    event (fun j => readWin blankM K (tapesOf T j)) = PalPeg.ChainBoundaryCache.boundaryEvent wm.machine.control := by
  unfold event
  rw [centreRead_periodSlot he hpad wm.machine.control.period (by simp [periodOf, hchain]),
    decToken_encToken]
  rfl

theorem encControl_after (hK : 3 ≤ K) (hpad : K ≤ margin) (internal : Bool)
    (w : List (Fin 2)) (x : PalPeg.GalilScaffoldTop.State GalilVM) (q : QPhys fb db) (T : Slot → STape Γm)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm) (a : Fin 3)
    (htok : PalPeg.GalilScaffoldChainConsume.symbol wm.machine.control.period.focus = some a)
    (he : PalPeg.PhysicalEncoding.Enc w margin x (q,T)) :
    EncControl w (stateAfter internal x wm a) (result hK internal q T).1 := by
  have hm := control_matches internal q (fun j => readWin blankM K (tapesOf T j)) wm.machine.control a htok
    (by rw [centreRead_periodSlot he.2 hpad wm.machine.control.period (by simp [periodOf, hchain]), decToken_encToken]; rfl)
    (by simpa [chainConsumeOf, hchain] using he.1.chainPhase)
    (by simpa [chainConsumeOf, hchain] using he.1.chainForward)
    (by simpa [chainConsumeOf, hchain] using he.1.chainBroken)
  rw [Prod.mk.injEq, Prod.mk.injEq] at hm
  refine ⟨he.1.ctl, ?_, hm.1, hm.2.1, hm.2.2, he.1.fppMode, he.1.fppFinalStage,
    he.1.fppPc, he.1.fppDone, he.1.dpPc, he.1.dpDone, he.1.searchMode,
    he.1.searchFinalStage, he.1.searchQuarter, he.1.periodOnly, ?_, he.1.onLetter, he.1.leftFirst⟩
  · simpa [result, logicalStep, idealStep, rule, next, stateAfter, hchain, chainTagOf] using he.1.chainTag
  · intro i place hp
    apply he.1.placeGap i place
    fin_cases i <;> simpa [placeOf, stateAfter, hchain] using hp

/-- Every named counter after the routed row has a canonical padded witness. -/
theorem result_counters (hK : 3 ≤ K) (hpad : K ≤ margin) (internal : Bool)
    (x : PalPeg.GalilScaffoldTop.State GalilVM) (q : QPhys fb db) (T : Slot → STape Γm)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm) (a : Fin 3)
    (htok : PalPeg.GalilScaffoldChainConsume.symbol wm.machine.control.period.focus = some a)
    (he : EncTapes margin x q.polarity q.gap q.micro q.fppLive q.dpLive T)
    (hphase : q.chainPhase = wm.machine.control.phase)
    (h age : ℕ) (value : Counter) (hi : PalPeg.ChainBoundaryCache.Inv h age wm.machine.control value)
    (spareSeg : STape Seg) (hspare : absCtr spareSeg (q.polarity 10) = value)
    (hspareTape : T (counterSlot 10) = padLeft margin (mapTape encSeg spareSeg)) :
    ∀ c value', counterOf (stateAfter internal x wm a) c = some value' →
      ∃ seg : STape Seg, absCtr seg ((result hK internal q T).1.polarity c) = value' ∧
        (result hK internal q T).2 (slotIndex (counterSlot c)) = padLeft margin (mapTape encSeg seg) := by
  let ws := fun j => readWin blankM K (tapesOf T j)
  have hev : event ws = PalPeg.ChainBoundaryCache.boundaryEvent wm.machine.control :=
    event_read hpad x q T wm hchain he
  have hwsp : ws (slotIndex (counterSlot 10)) = readWin blankM K (padLeft margin (mapTape encSeg spareSeg)) := by
    simp only [ws, tapesOf_apply, hspareTape]
  obtain ⟨spareNext, hsval, hstape⟩ := PalPeg.PhysicalCounterCache.increments_encode
    (PalPeg.ChainBoundaryCache.rate q.chainPhase)
    ((PalPeg.ChainBoundaryCache.rate_le _).trans hK) hpad (q.polarity 10) spareSeg spareSeg value hspare hspare
  have hsbit : PalPeg.PhysicalWatchActions.spare q ws =
      PalPeg.PhysicalCounterCache.increments (PalPeg.ChainBoundaryCache.rate q.chainPhase) (q.polarity 10)
        (readWin blankM K (padLeft margin (mapTape encSeg spareSeg))) := by
    unfold PalPeg.PhysicalWatchActions.spare
    rw [hwsp]
  rw [← hsbit] at hsval hstape
  rw [← hspareTape] at hstape
  dsimp only [ws] at hev hsval hstape
  have hcEvent : (PalPeg.GalilScaffoldChainPeriod.isFirst wm.machine.control.period.focus ||
      PalPeg.GalilScaffoldChainConsume.isLast wm.machine.control.period.focus) =
      PalPeg.ChainBoundaryCache.boundaryEvent wm.machine.control := rfl
  obtain ⟨bdSeg, hbval, hbtape⟩ := he.counters 14 wm.machine.control.boundary (by simp [counterOf, hchain])
  obtain ⟨lastSeg, hlval, hltape⟩ := he.counters 15 wm.machine.control.last (by simp [counterOf, hchain])
  obtain ⟨distSeg, hdval, hdtape⟩ := he.counters 13 wm.machine.control.distance (by simp [counterOf, hchain])
  have hd : PalPeg.GalilScaffoldCounter.Canonical wm.machine.control.distance := hdval ▸ PalPeg.LocalCounter.absCtr_canonical _ _
  have hs : PalPeg.GalilScaffoldCounter.Canonical value := hspare ▸ PalPeg.LocalCounter.absCtr_canonical _ _
  intro c value' hc
  by_cases hbalance : c = balanceIndex internal
  · subst c
    have hvalue : counterOf x (balanceIndex internal) = some (if internal then wm.lag else wm.margin) := by
      cases internal <;> simp [counterOf, balanceIndex, hchain]
    obtain ⟨raw, hv, ht⟩ := he.counters _ _ hvalue
    obtain ⟨out, ho, hot⟩ := balance_tape (by omega : 1 ≤ K) (by omega : K ≤ margin+1)
      internal q T raw _ hv ht
    refine ⟨out, ?_, ?_⟩
    · rw [result_control]
      cases internal <;> simpa [stateAfter, watchAfter, counterOf, balanceIndex, Option.some.injEq] using ho.trans (Option.some.inj hc)
    · dsimp only [result, logicalStep, idealStep, rule]
      rw [change_other _ _ _ _ (by cases internal <;> simp [balanceIndex, counterSlot])
        (by cases internal <;> simp [balanceIndex, counterSlot]) (by cases internal <;> simp [balanceIndex, counterSlot]), tapesOf_apply]
      exact hot
  by_cases hdist : c = 13
  · subst c
    obtain ⟨out, ho, hot⟩ := distance_tape (by omega : 1 ≤ K) (by omega : K ≤ margin+1)
      internal q T distSeg wm.machine.control.distance hdval hdtape
    have hv : inc wm.machine.control.distance = value' := by
      simpa [counterOf, stateAfter, watchAfter, PalPeg.GalilScaffoldChainConsume.consume, htok] using hc
    refine ⟨out, ho.trans hv, ?_⟩
    dsimp only [result, logicalStep, idealStep, rule]
    rw [change_other _ _ _ _ (by simp [counterSlot]) (by simp [counterSlot]) (by simp [counterSlot]), tapesOf_apply]
    exact hot
  by_cases hboundary : c = 14
  · subst c
    cases hb : PalPeg.ChainBoundaryCache.boundaryEvent wm.machine.control with
    | false =>
      have hv : wm.machine.control.boundary = value' := by
        simpa [counterOf, stateAfter, watchAfter, PalPeg.GalilScaffoldChainConsume.consume, htok,
          hcEvent, hb] using hc
      refine ⟨bdSeg, ?_, ?_⟩
      · cases internal <;> simpa [result, logicalStep, idealStep, rule, next, hev, hb, signs, balanceIndex] using hbval.trans hv
      · cases internal <;> simpa [result, logicalStep, idealStep, rule, change, hev, hb, actions,
          balanceIndex, counterSlot, tapesOf_apply] using hbtape
    | true =>
      have hv : inc wm.machine.control.distance = value' := by
        simpa [counterOf, stateAfter, watchAfter, PalPeg.GalilScaffoldChainConsume.consume, htok,
          hcEvent, hb] using hc
      rw [hphase, PalPeg.ChainBoundaryCache.spare_eq_at_boundary hi hb hs hd] at hsval
      refine ⟨spareNext, ?_, ?_⟩
      · simpa [result, logicalStep, idealStep, rule, next, hev, hb,
          PalPeg.PhysicalBoundaryRotate.rotatePol, signs] using hsval.trans hv
      · simpa [result, logicalStep, idealStep, rule, change, hev, hb,
          PalPeg.PhysicalRoles.boundaryRoles_boundary, actions, tapesOf_apply] using hstape
  by_cases hlast : c = 15
  · subst c
    cases hb : PalPeg.ChainBoundaryCache.boundaryEvent wm.machine.control with
    | false =>
      have hv : wm.machine.control.last = value' := by
        simpa [counterOf, stateAfter, watchAfter, PalPeg.GalilScaffoldChainConsume.consume, htok,
          hcEvent, hb] using hc
      refine ⟨lastSeg, ?_, ?_⟩
      · cases internal <;> simpa [result, logicalStep, idealStep, rule, next, hev, hb, signs, balanceIndex] using hlval.trans hv
      · cases internal <;> simpa [result, logicalStep, idealStep, rule, change, hev, hb, actions,
          balanceIndex, counterSlot, tapesOf_apply] using hltape
    | true =>
      have hv : wm.machine.control.boundary = value' := by
        simpa [counterOf, stateAfter, watchAfter, PalPeg.GalilScaffoldChainConsume.consume, htok,
          hcEvent, hb] using hc
      refine ⟨bdSeg, ?_, ?_⟩
      · cases internal <;> simpa [result, logicalStep, idealStep, rule, next, hev, hb,
          PalPeg.PhysicalBoundaryRotate.rotatePol, signs, balanceIndex] using hbval.trans hv
      · cases internal <;> simpa [result, logicalStep, idealStep, rule, change, hev, hb,
          PalPeg.PhysicalRoles.boundaryRoles_last, actions, balanceIndex, counterSlot, tapesOf_apply] using hbtape
  have h10 : c ≠ 10 := by intro hh; subst c; cases hc
  have hsame : counterOf (stateAfter internal x wm a) c = counterOf x c := by
    cases internal <;> fin_cases c <;> simp_all [counterOf, stateAfter, watchAfter, balanceIndex]
  obtain ⟨raw, ha, ht⟩ := he.counters c value' (hsame.symm.trans hc)
  refine ⟨raw, ?_, ?_⟩
  · rw [result_sign hK internal q T c h10 hdist hbalance hboundary hlast]
    exact ha
  · rw [result_kept hK internal q T _ (by simpa [counterSlot] using h10)
      (by simpa [counterSlot] using hdist) (by simpa [counterSlot] using hbalance)
      (by simpa [counterSlot] using hboundary) (by simpa [counterSlot] using hlast) (by simp [counterSlot, periodSlot])]
    exact ht

theorem result_period (hK : 3 ≤ K) (hpad : K ≤ margin) (internal : Bool)
    (x : PalPeg.GalilScaffoldTop.State GalilVM) (q : QPhys fb db) (T : Slot → STape Γm)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm) (a : Fin 3)
    (htok : PalPeg.GalilScaffoldChainConsume.symbol wm.machine.control.period.focus = some a)
    (he : EncTapes margin x q.polarity q.gap q.micro q.fppLive q.dpLive T)
    (hforward : q.chainForward = wm.machine.control.forward)
    (hleft : (PalPeg.GalilScaffoldChainConsume.consume wm.machine.control (some a)).forward = false →
      wm.machine.control.period.left ≠ []) :
    (result hK internal q T).2 (slotIndex periodSlot) = padLeft margin (mapTape encToken
      (encPeriod (PalPeg.GalilScaffoldChainConsume.consume wm.machine.control (some a)).period)) := by
  have ht : decToken (centreRead (fun j => readWin blankM K (tapesOf T j)) periodSlot) = wm.machine.control.period.focus := by
    rw [centreRead_periodSlot he hpad wm.machine.control.period (by simp [periodOf, hchain]), decToken_encToken]
    rfl
  have hf : forward q (fun j => readWin blankM K (tapesOf T j)) =
      (PalPeg.GalilScaffoldChainConsume.consume wm.machine.control (some a)).forward := by
    simp [forward, event, ht, hforward, PalPeg.GalilScaffoldChainConsume.consume, htok]
  have hp := period_tape hpad internal x q T he wm.machine.control.period
    (by simp [periodOf, hchain]) (fun hb => hleft (hf.symm.trans hb))
  dsimp only at hp
  rw [hf] at hp
  have hc : (PalPeg.GalilScaffoldChainConsume.consume wm.machine.control (some a)).period =
      if (PalPeg.GalilScaffoldChainConsume.consume wm.machine.control (some a)).forward then
        PalPeg.GalilScaffoldChainPeriod.moveRight wm.machine.control.period
      else PalPeg.GalilScaffoldChainPeriod.moveLeft wm.machine.control.period := by
    simp [PalPeg.GalilScaffoldChainConsume.consume, htok]
  rw [← hc] at hp
  dsimp only [result, logicalStep, idealStep, rule]
  rw [change_other _ _ _ _ (by simp [periodSlot, counterSlot])
    (by simp [periodSlot, counterSlot]) (by simp [periodSlot, counterSlot]), tapesOf_apply]
  exact hp

/-- Full EncTapes, using the same source layout and retaining all four heads. -/
theorem result_tapes (hK : 3 ≤ K) (hpad : K ≤ margin) (internal : Bool)
    (w : List (Fin 2)) (x : PalPeg.GalilScaffoldTop.State GalilVM) (q : QPhys fb db) (T : Slot → STape Γm)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm) (a : Fin 3)
    (htok : PalPeg.GalilScaffoldChainConsume.symbol wm.machine.control.period.focus = some a)
    (he : PalPeg.PhysicalEncoding.Enc w margin x (q,T))
    (h age : ℕ) (value : Counter) (hi : PalPeg.ChainBoundaryCache.Inv h age wm.machine.control value)
    (spareSeg : STape Seg) (hspare : absCtr spareSeg (q.polarity 10) = value)
    (hspareTape : T (counterSlot 10) = padLeft margin (mapTape encSeg spareSeg))
    (hleft : (PalPeg.GalilScaffoldChainConsume.consume wm.machine.control (some a)).forward = false →
      wm.machine.control.period.left ≠ []) :
    EncTapes margin (stateAfter internal x wm a)
      (result hK internal q T).1.polarity q.gap q.micro q.fppLive q.dpLive
      (fun slot => (result hK internal q T).2 (slotIndex slot)) := by
  have hphase : q.chainPhase = wm.machine.control.phase := by simpa [chainConsumeOf, hchain] using he.1.chainPhase
  have hforward : q.chainForward = wm.machine.control.forward := by simpa [chainConsumeOf, hchain] using he.1.chainForward
  have hc := result_counters hK hpad internal x q T wm hchain a htok he.2 hphase h age value hi spareSeg hspare hspareTape
  have hp := result_period hK hpad internal x q T wm hchain a htok he.2 hforward hleft
  have hkeep := result_nonchain hK internal q T
  have hheads : headOf (stateAfter internal x wm a) = headOf x := by
    funext v; fin_cases v <;> simp [headOf, stateAfter, watchAfter, hchain]
  have hplaces : placeOf (stateAfter internal x wm a) = placeOf x := by
    funext i; fin_cases i <;> simp [placeOf, stateAfter, hchain]
  have hsp : Rep (q.polarity 10) value ((tapesOf T) (slotIndex (counterSlot 10))) := by
    refine ⟨spareSeg, hspare, ?_⟩
    rw [tapesOf_apply, hspareTape]
    exact ⟨rfl, fun _ => rfl⟩
  have hl : Rep (q.polarity 15) wm.machine.control.last ((tapesOf T) (slotIndex (counterSlot 15))) := by
    obtain ⟨seg, ha, ht⟩ := he.2.counters 15 wm.machine.control.last (by simp [counterOf, hchain])
    refine ⟨seg, ha, ?_⟩
    change T (counterSlot 15) = padLeft margin (mapTape encSeg seg) at ht
    rw [tapesOf_apply, ht]
    exact ⟨rfl, fun _ => rfl⟩
  have hs := (logical_cache hK hpad internal q (tapesOf T) wm.machine.control a htok hphase
    (event_read hpad x q T wm hchain he.2) h age value hi hsp hl).2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hc, ?_, ?_, ?_, ?_⟩
  · intro slot
    by_cases hcounter : ∃ c, slot = counterSlot c
    · obtain ⟨c, rfl⟩ := hcounter
      by_cases h10 : c = 10
      · subst c
        exact hs.margin
      · obtain ⟨value', hv⟩ : ∃ value', counterOf (stateAfter internal x wm a) c = some value' := by
          fin_cases c <;> first | exact (h10 rfl).elim | exact ⟨_, rfl⟩
        obtain ⟨seg, _, ht⟩ := hc c value' hv
        rw [ht, pos_padLeft]; omega
    by_cases hperiod : slot = periodSlot
    · subst slot; rw [hp, pos_padLeft]; omega
    rw [hkeep slot (fun c h => hcounter ⟨c,h⟩) hperiod]
    exact he.2.margins slot
  · intro v head hh
    obtain ⟨view, vt, ha, hv, ht, hcells, hwf⟩ := he.2.heads v head (by rw [← hheads]; exact hh)
    refine ⟨view, vt, ha, hv, ?_, hcells, hwf⟩
    intro i
    rw [hkeep (headSlot v i) (by intro c; simp [headSlot, counterSlot]) (by simp [headSlot, periodSlot])]
    exact ht i
  · intro hh
    simp [headOf, stateAfter, watchAfter] at hh
  · intro i
    rw [hkeep _ (by intro c; cases q.fppLive <;> simp [progSlotOf, counterSlot])
      (by cases q.fppLive <;> simp [progSlotOf, periodSlot])]
    exact he.2.fpp i
  · intro i
    rw [hkeep _ (by intro c; cases q.dpLive <;> simp [dpSlotOf, counterSlot])
      (by cases q.dpLive <;> simp [dpSlotOf, periodSlot])]
    exact he.2.dp i
  · intro i
    rw [hkeep _ (by intro c; cases q.fppLive <;> simp [progSlotOf, counterSlot])
      (by cases q.fppLive <;> simp [progSlotOf, periodSlot])]
    exact he.2.idleShape i
  · intro i place hh
    obtain ⟨stack, junk, hj, hs, ht⟩ := he.2.places i place (by rw [← hplaces]; exact hh)
    refine ⟨stack, junk, hj, hs, ?_⟩
    rw [hkeep (placeSlot i) (by intro c; simp [placeSlot, counterSlot]) (by simp [placeSlot, periodSlot])]
    exact ht
  · intro m value' hv
    have hm5 : m ≠ 5 := by intro hm; subst m; simp [counterOf, stateAfter, mirrorSource] at hv
    have hsame : counterOf (stateAfter internal x wm a) (mirrorSource m) = counterOf x (mirrorSource m) := by
      fin_cases m <;> simp [counterOf, mirrorSource, stateAfter, hchain]
    obtain ⟨seg, ha, ht⟩ := he.2.mirrors m value' (hsame.symm.trans hv)
    refine ⟨seg, ?_, ?_⟩
    · rw [result_sign hK internal q T (mirrorSource m)
        (by fin_cases m <;> first | decide | exact (hm5 rfl).elim) (by fin_cases m <;> decide)
        (by cases internal <;> fin_cases m <;> decide)
        (by fin_cases m <;> decide) (by fin_cases m <;> decide)]
      exact ha
    · rw [hkeep (mirrorSlot m) (by intro c; simp [mirrorSlot, counterSlot]) (by simp [mirrorSlot, periodSlot])]
      exact ht
  · intro tape ht
    have hh : (PalPeg.GalilScaffoldChainConsume.consume wm.machine.control (some a)).period = tape := by
      simpa [periodOf, stateAfter, watchAfter] using ht
    rw [← hh]
    exact hp
  · intro tape ht
    simp [answerOf, stateAfter] at ht

/-- All finite control and tape components, at the unchanged macro boundary. -/
theorem core_after (hK : 3 ≤ K) (hpad : K ≤ margin) (internal : Bool)
    (w : List (Fin 2)) (x : PalPeg.GalilScaffoldTop.State GalilVM) (p : CoreState)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm) (a : Fin 3)
    (htok : PalPeg.GalilScaffoldChainConsume.symbol wm.machine.control.period.focus = some a)
    (he : CoreEnc w x p)
    (h age : ℕ) (value : Counter) (hi : PalPeg.ChainBoundaryCache.Inv h age wm.machine.control value)
    (spareSeg : STape Seg) (hspare : absCtr spareSeg (p.1.polarity 10) = value)
    (hspareTape : p.2 (slotIndex (counterSlot 10)) = padLeft margin (mapTape encSeg spareSeg))
    (hleft : (PalPeg.GalilScaffoldChainConsume.consume wm.machine.control (some a)).forward = false →
      wm.machine.control.period.left ≠ []) :
    CoreEnc w (stateAfter internal x wm a)
      (logicalStep (rule internal hK) change blankM p none) := by
  let T := fun slot => p.2 (slotIndex slot)
  have hT : tapesOf T = p.2 := by funext j; simp [T, tapesOf]
  have hc := encControl_after hK hpad internal w x p.1 T wm hchain a htok he.1
  have ht := result_tapes hK hpad internal w x p.1 T wm hchain a htok he.1
    h age value hi spareSeg hspare hspareTape hleft
  simp only [result, hT, Prod.eta] at hc ht
  exact ⟨⟨hc, ht⟩, he.2⟩

/-- The period cursor supplies the left-move condition without referring to
which verifier quantum will later supply the successful letter. -/
theorem cursor_left {h age : ℕ} {s : PalPeg.GalilScaffoldChainConsume.State}
    (hc : PalPeg.ChainBoundaryCache.Cursor h age s.period s.forward)
    (a : Fin 3) (htok : PalPeg.GalilScaffoldChainConsume.symbol s.period.focus = some a)
    (hback : (PalPeg.GalilScaffoldChainConsume.consume s (some a)).forward = false) :
    s.period.left ≠ [] := by
  obtain ⟨passed, future, first, last, hp, hlen, hc⟩ := hc
  cases hf : s.forward <;> simp only [hf, Bool.false_eq_true, if_false, if_true] at hc
  · cases future with
    | nil =>
      have hfocus := (List.cons.inj (by simpa using hc.2)).1
      simp only [PalPeg.GalilScaffoldChainConsume.consume, htok, decide_true, if_true] at hback
      simp [hfocus, PalPeg.GalilScaffoldChainPeriod.isFirst] at hback
    | cons b rest =>
      have hleft := (List.cons.inj (by simpa using hc.2)).2
      rw [hleft]
      simp
  · rw [hc.1]
    simp

/-- CoreEnc, all counter shapes, the boundary cache and the saved h mirror
are assembled into the exact same Running predicate used by the dispatcher. -/
theorem running_exact (hK : 3 ≤ K) (hpad : K ≤ margin) (internal : Bool)
    (w : List (Fin 2)) (x : PalPeg.GalilScaffoldTop.State GalilVM) (p : CoreState)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm) (a : Fin 3)
    (htok : PalPeg.GalilScaffoldChainConsume.symbol wm.machine.control.period.focus = some a)
    (he : CoreEnc w x p)
    (h age : ℕ) (value : Counter) (hi : PalPeg.ChainBoundaryCache.Inv h age wm.machine.control value)
    (spareSeg : STape Seg) (hspare : absCtr spareSeg (p.1.polarity 10) = value)
    (hspareTape : p.2 (slotIndex (counterSlot 10)) = padLeft margin (mapTape encSeg spareSeg))
    (hmirror : Rep true (PalPeg.GalilScaffoldCounter.ofNat (PalPeg.PhysicalCacheInvariant.mirrorMagnitude x h))
      (p.2 PalPeg.PhysicalPeriodMirror.mirrorIndex)) :
    PalPeg.PhysicalCacheInvariant.Running w (stateAfter internal x wm a)
      (logicalStep (rule internal hK) change blankM p none) := by
  have hcore := core_after hK hpad internal w x p wm hchain a htok he h age value hi
    spareSeg hspare hspareTape (cursor_left hi.cursor a htok)
  have hphase : p.1.chainPhase = wm.machine.control.phase := by
    simpa [chainConsumeOf, hchain] using he.1.1.chainPhase
  have hsp : Rep (p.1.polarity 10) value (p.2 (slotIndex (counterSlot 10))) := by
    refine ⟨spareSeg, hspare, ?_⟩
    rw [hspareTape]
    exact ⟨rfl, fun _ => rfl⟩
  have hl : Rep (p.1.polarity 15) wm.machine.control.last (p.2 (slotIndex (counterSlot 15))) := by
    obtain ⟨seg, ha, ht⟩ := he.1.2.counters 15 wm.machine.control.last (by simp [counterOf, hchain])
    change p.2 (slotIndex (counterSlot 15)) = padLeft margin (mapTape encSeg seg) at ht
    refine ⟨seg, ha, ?_⟩
    rw [ht]
    exact ⟨rfl, fun _ => rfl⟩
  have hev : event (fun j => readWin blankM K (p.2 j)) = PalPeg.ChainBoundaryCache.boundaryEvent wm.machine.control := by
    have hr := event_read hpad x p.1 (fun slot => p.2 (slotIndex slot)) wm hchain he.1.2
    simpa only [tapesOf, Equiv.apply_symm_apply] using hr
  have hcache := logical_cache hK hpad internal p.1 p.2 wm.machine.control a htok hphase hev
    h age value hi hsp hl
  have hm := logical_other hK internal p none PalPeg.PhysicalPeriodMirror.mirrorIndex
    (by simp [PalPeg.PhysicalPeriodMirror.mirrorIndex, mirrorSlot, counterSlot])
    (by simp [PalPeg.PhysicalPeriodMirror.mirrorIndex, mirrorSlot, counterSlot])
    (by simp [PalPeg.PhysicalPeriodMirror.mirrorIndex, mirrorSlot, counterSlot])
    (by simp [PalPeg.PhysicalPeriodMirror.mirrorIndex, mirrorSlot, counterSlot])
    (by simp [PalPeg.PhysicalPeriodMirror.mirrorIndex, mirrorSlot, counterSlot])
    (by simp [PalPeg.PhysicalPeriodMirror.mirrorIndex, mirrorSlot, counterSlot])
    (by simp [PalPeg.PhysicalPeriodMirror.mirrorIndex, mirrorSlot, periodSlot])
  apply PalPeg.PhysicalCacheInvariant.of_watching_cache
    (p := logicalStep (rule internal hK) change blankM p none) (watchAfter internal wm a) (Or.inl rfl)
    ⟨_, hcore, fun _ => ⟨rfl, fun _ => rfl⟩⟩
  refine ⟨h, PalPeg.ChainBoundaryCache.nextAge wm.machine.control age,
    PalPeg.ChainBoundaryCache.nextSpare wm.machine.control value, hcache.1, hcache.2, ?_⟩
  rw [hm]
  exact hmirror

/-- The nonhead row cannot distinguish a real swept source from its ideal
witness, including the boundary permutation selected by its windows. -/
theorem logical_congr (hK : 3 ≤ K) (internal : Bool) (q : QPhys fb db)
    (T U : Fin tapeCountM → STape Γm) (ht : ∀ j, TEqG blankM (T j) (U j)) :
    (logicalStep (rule internal hK) change blankM (q,T) none).1 =
      (logicalStep (rule internal hK) change blankM (q,U) none).1 ∧
    ∀ j, TEqG blankM ((logicalStep (rule internal hK) change blankM (q,T) none).2 j)
      ((logicalStep (rule internal hK) change blankM (q,U) none).2 j) := by
  have hw : (fun j => readWin blankM K (T j)) = fun j => readWin blankM K (U j) :=
    funext (fun j => readWin_congr_teqG (ht j))
  obtain ⟨hc, hacts⟩ := idealStep_congr_teqG (rule internal hK) blankM q T U ht none
  refine ⟨hc, ?_⟩
  intro j
  dsimp only [logicalStep]
  rw [hw]
  exact hacts _

/-- A complete successful nonhead quantum on the common swept encoding.
The source invariant supplies the spare, snapshots, cursor and saved h; no
post-state encoding or new trace assumption is requested. -/
theorem running (hK : 3 ≤ K) (hpad : K ≤ margin) (internal : Bool)
    (w : List (Fin 2)) (x : PalPeg.GalilScaffoldTop.State GalilVM) (p : CoreState)
    (he : PalPeg.PhysicalCacheInvariant.Running w x p)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm) (a : Fin 3)
    (htok : PalPeg.GalilScaffoldChainConsume.symbol wm.machine.control.period.focus = some a) :
    PalPeg.PhysicalCacheInvariant.Running w (stateAfter internal x wm a)
      (logicalStep (rule internal hK) change blankM p none) := by
  have hcache := PalPeg.PhysicalCacheInvariant.running_cache he
  rw [PalPeg.PhysicalCacheInvariant.Cache, hchain] at hcache
  obtain ⟨h, age, value, hi, ⟨seg, hseg, hsp⟩, hmirror⟩ := hcache
  obtain ⟨T, hT, ht⟩ := PalPeg.PhysicalCacheInvariant.running_core he
  let U := Function.update T PalPeg.PhysicalSpare.spareIndex (padLeft margin (mapTape encSeg seg))
  have hU : CoreEnc w x (p.1,U) := by
    have hp : PalPeg.PhysicalFreeCounter.setPolarity p.1 10 (p.1.polarity 10) = p.1 := by
      unfold PalPeg.PhysicalFreeCounter.setPolarity
      rw [Function.update_eq_self]
    simpa only [hp, U, PalPeg.PhysicalSpare.spareIndex] using
      PalPeg.PhysicalFreeCounter.core_free_counter hT 10 (by simp [counterOf, hchain])
        (p.1.polarity 10) (padLeft margin (mapTape encSeg seg)) (by rw [pos_padLeft]; omega)
  have hu : ∀ j, TEqG blankM (U j) (p.2 j) := by
    intro j
    by_cases hj : j = PalPeg.PhysicalSpare.spareIndex
    · subst j; simpa only [U, Function.update_self] using hsp
    · simpa only [U, Function.update_of_ne hj] using ht j
  have hM : Rep true (PalPeg.GalilScaffoldCounter.ofNat (PalPeg.PhysicalCacheInvariant.mirrorMagnitude x h))
      (U PalPeg.PhysicalPeriodMirror.mirrorIndex) := by
    obtain ⟨raw, ha, hr⟩ := hmirror
    exact ⟨raw, ha, PalPeg.MachineStep.teqG_trans hr
      ⟨(hu _).1.symm, fun j => ((hu _).2 j).symm⟩⟩
  have hout := running_exact hK hpad internal w x (p.1,U) wm hchain a htok hU
    h age value hi seg hseg (Function.update_self _ _ _) hM
  obtain ⟨hq, hteq⟩ := logical_congr hK internal p.1 U p.2 hu
  exact PalPeg.MachineStep.sweepClosed_sweepClosure blankM (PalPeg.PhysicalCacheInvariant.CoreInv w)
    _ _ _ hout hq hteq

def beforeImmediate (consume : Bool) (x : PalPeg.GalilScaffoldTop.State GalilVM)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (a : Fin 3) : PalPeg.GalilScaffoldTop.State GalilVM :=
  if consume then stateAfter true x wm a else x

def beforeImmediateWatch (consume : Bool) (wm : PalPeg.GalilScaffoldChainWatch.State) (a : Fin 3) :
    PalPeg.GalilScaffoldChainWatch.State := if consume then watchAfter true wm a else wm

def afterInternal (consume : Bool) (wm : PalPeg.GalilScaffoldChainWatch.State) :
    PalPeg.GalilScaffoldChainWatch.State := if consume then PalPeg.GalilScaffoldChainWatch.caught wm else wm

/-- Identify the intermediate nonhead state with the actual watch semantics;
only the verifier is put back for the existing twelve-slot view executor. -/
theorem pair_state (consume : Bool) (x : PalPeg.GalilScaffoldTop.State GalilVM)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (a b : Fin 3)
    (hfirst : consume = true → PalPeg.GalilScaffoldInputHead.read
      (PalPeg.GalilScaffoldChainVerifier.right wm.machine.verifier) = some a)
    (hsecond : PalPeg.GalilScaffoldInputHead.read
      (PalPeg.GalilScaffoldChainVerifier.right (afterInternal consume wm).machine.verifier) = some b) :
    stateAfter false (beforeImmediate consume x wm a) (beforeImmediateWatch consume wm a) b =
      stepState ⟨x.ctl, {x.vm with chain := .watch (PalPeg.GalilScaffoldChainWatch.immediate (afterInternal consume wm))}⟩ wm.machine.verifier := by
  cases consume with
  | false =>
    simp [stateAfter, beforeImmediate, beforeImmediateWatch, watchAfter, stepState, chainVerifierBack,
      PalPeg.GalilScaffoldChainWatch.immediate, PalPeg.GalilScaffoldChainVerifier.consume,
      afterInternal] at hsecond ⊢
    rw [hsecond]
  | true =>
    have ha := hfirst rfl
    have hb : PalPeg.GalilScaffoldInputHead.read (PalPeg.GalilScaffoldChainVerifier.right
        (PalPeg.GalilScaffoldChainVerifier.right wm.machine.verifier)) = some b := hsecond
    simp [stateAfter, beforeImmediate, beforeImmediateWatch, watchAfter, stepState, chainVerifierBack,
      PalPeg.GalilScaffoldChainWatch.immediate, PalPeg.GalilScaffoldChainWatch.caught,
      PalPeg.GalilScaffoldChainVerifier.consume, afterInternal, ha, hb]

/-- The two logical watch stages preserve the common invariant before the
single sweep. The final role permutation is still part of the action plan. -/
theorem running_pair_ideal (consume : Bool) (w : List (Fin 2))
    (x : PalPeg.GalilScaffoldTop.State GalilVM) (p : CoreState)
    (he : PalPeg.PhysicalCacheInvariant.Running w x p)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm) (a b : Fin 3)
    (htok : PalPeg.GalilScaffoldChainConsume.symbol wm.machine.control.period.focus = some a)
    (hnext : PalPeg.GalilScaffoldChainConsume.symbol
      (beforeImmediateWatch consume wm a).machine.control.period.focus = some b) :
    PalPeg.PhysicalCacheInvariant.Running w
      (stateAfter false (beforeImmediate consume x wm a) (beforeImmediateWatch consume wm a) b)
      (logicalStep (fusedRule consume) (fusedRoles consume) blankM p none) := by
  have hfirst : PalPeg.PhysicalCacheInvariant.Running w (beforeImmediate consume x wm a)
      (logicalStep (firstRule consume) (firstChange consume) blankM p none) := by
    cases consume with
    | false =>
      simpa only [beforeImmediate, Bool.false_eq_true, if_false, logicalStep, idealStep,
        firstRule, firstChange, Equiv.refl_apply, actList, Prod.eta] using he
    | true =>
      exact running (K := 32) (by decide) (by decide) true w x p he wm hchain a htok
  have hwatch : (beforeImmediate consume x wm a).vm.chain =
      .watch (beforeImmediateWatch consume wm a) := by
    cases consume <;> simp [beforeImmediate, beforeImmediateWatch, stateAfter, hchain]
  have hsecond := running (K := 32) (by decide) (by decide) false w (beforeImmediate consume x wm a)
    (logicalStep (firstRule consume) (firstChange consume) blankM p none)
    hfirst (beforeImmediateWatch consume wm a) hwatch b hnext
  have hm : ∀ j, 64 ≤ pos (p.2 j) := fun j =>
    (show 64 ≤ margin by decide).trans
      (PalPeg.PhysicalContract.running_margin (PalPeg.PhysicalCacheInvariant.running_core he) j)
  change PalPeg.PhysicalCacheInvariant.Running w _
    (PalPeg.LocalRoleRouting.decode (idealStep (plan consume) blankM ((Equiv.refl _, p.1), p.2) none))
  rw [plan_ideal consume p none hm]
  exact hsecond

/-- The optional internal quantum and the immediate quantum preserve the whole
common invariant through the compiled single sweep, including two boundaries. -/
theorem running_pair (consume : Bool) (w : List (Fin 2))
    (x : PalPeg.GalilScaffoldTop.State GalilVM)
    (p : PalPeg.LocalRoleRouting.Config CoreControl Γm tapeCountM)
    (he : PalPeg.PhysicalCacheInvariant.Running w x (PalPeg.LocalRoleRouting.decode p))
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm) (a b : Fin 3)
    (htok : PalPeg.GalilScaffoldChainConsume.symbol wm.machine.control.period.focus = some a)
    (hnext : PalPeg.GalilScaffoldChainConsume.symbol
      (beforeImmediateWatch consume wm a).machine.control.period.focus = some b) :
    PalPeg.PhysicalCacheInvariant.Running w
      (stateAfter false (beforeImmediate consume x wm a) (beforeImmediateWatch consume wm a) b)
      (PalPeg.LocalRoleRouting.decode
        ((PalPeg.LocalRoleFusion.compiled (plan consume)).apply blankM p none)) := by
  have hfirst : PalPeg.PhysicalCacheInvariant.Running w (beforeImmediate consume x wm a)
      (logicalStep (firstRule consume) (firstChange consume) blankM (PalPeg.LocalRoleRouting.decode p) none) := by
    cases consume with
    | false =>
      simpa only [beforeImmediate, Bool.false_eq_true, if_false, logicalStep, idealStep,
        firstRule, firstChange, Equiv.refl_apply, actList, Prod.eta] using he
    | true =>
      exact running (K := 32) (by decide) (by decide) true w x (PalPeg.LocalRoleRouting.decode p) he wm hchain a htok
  have hwatch : (beforeImmediate consume x wm a).vm.chain =
      .watch (beforeImmediateWatch consume wm a) := by
    cases consume <;> simp [beforeImmediate, beforeImmediateWatch, stateAfter, hchain]
  have hsecond := running (K := 32) (by decide) (by decide) false w (beforeImmediate consume x wm a)
    (logicalStep (firstRule consume) (firstChange consume) blankM (PalPeg.LocalRoleRouting.decode p) none)
    hfirst (beforeImmediateWatch consume wm a) hwatch b hnext
  have hm : ∀ j, 64 ≤ pos ((PalPeg.LocalRoleRouting.decode p).2 j) := by
    intro j
    exact (show 64 ≤ margin by decide).trans
      (PalPeg.PhysicalContract.running_margin (PalPeg.PhysicalCacheInvariant.running_core he) j)
  obtain ⟨hq, ht⟩ := fused_apply consume p none hm
  generalize hfirstResult : logicalStep (firstRule consume) (firstChange consume) blankM
    (PalPeg.LocalRoleRouting.decode p) none = firstResult at hsecond hq ht
  generalize hfinalResult : logicalStep (rule (K := 32) false (by decide)) change blankM
    firstResult none = finalResult at hsecond hq ht
  generalize hactual : PalPeg.LocalRoleRouting.decode
    ((PalPeg.LocalRoleFusion.compiled (plan consume)).apply blankM p none) = actual at hq ht ⊢
  exact PalPeg.MachineStep.sweepClosed_sweepClosure blankM (PalPeg.PhysicalCacheInvariant.CoreInv w)
    _ finalResult actual hsecond hq.symm ht

/-- The actual caught/immediate VM update, with the verifier held for the
view stage, on the ideal fused nonhead row. -/
theorem running_pair_good_ideal (consume : Bool) (w : List (Fin 2))
    (x : PalPeg.GalilScaffoldTop.State GalilVM) (p : CoreState)
    (he : PalPeg.PhysicalCacheInvariant.Running w x p)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm)
    (hfirst : consume = true → PalPeg.GalilScaffoldChainWatch.Good wm)
    (hsecond : PalPeg.GalilScaffoldChainWatch.Good (afterInternal consume wm)) :
    PalPeg.PhysicalCacheInvariant.Running w
      (stepState ⟨x.ctl, {x.vm with chain := .watch (PalPeg.GalilScaffoldChainWatch.immediate (afterInternal consume wm))}⟩ wm.machine.verifier)
      (logicalStep (fusedRule consume) (fusedRoles consume) blankM p none) := by
  obtain ⟨_, b, htokb, hreadb⟩ := hsecond
  cases consume with
  | false =>
    rw [← pair_state false x wm b b (by simp) hreadb]
    exact running_pair_ideal false w x p he wm hchain b b htokb htokb
  | true =>
    obtain ⟨_, a, htoka, hreada⟩ := hfirst rfl
    have hnext : PalPeg.GalilScaffoldChainConsume.symbol
        (beforeImmediateWatch true wm a).machine.control.period.focus = some b := by
      simpa [beforeImmediateWatch, watchAfter, afterInternal, PalPeg.GalilScaffoldChainWatch.caught,
        PalPeg.GalilScaffoldChainVerifier.consume, hreada] using htokb
    rw [← pair_state true x wm a b (fun _ => hreada) hreadb]
    exact running_pair_ideal true w x p he wm hchain a b htoka hnext

/-- Successful source quanta give the original caught/immediate VM state,
with its verifier held for the view stage. This is the same CoreInv as the
final dispatcher, after one real sweep of the fused nonhead action plan. -/
theorem running_pair_good (consume : Bool) (w : List (Fin 2))
    (x : PalPeg.GalilScaffoldTop.State GalilVM)
    (p : PalPeg.LocalRoleRouting.Config CoreControl Γm tapeCountM)
    (he : PalPeg.PhysicalCacheInvariant.Running w x (PalPeg.LocalRoleRouting.decode p))
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm)
    (hfirst : consume = true → PalPeg.GalilScaffoldChainWatch.Good wm)
    (hsecond : PalPeg.GalilScaffoldChainWatch.Good (afterInternal consume wm)) :
    PalPeg.PhysicalCacheInvariant.Running w
      (stepState ⟨x.ctl, {x.vm with chain := .watch (PalPeg.GalilScaffoldChainWatch.immediate (afterInternal consume wm))}⟩ wm.machine.verifier)
      (PalPeg.LocalRoleRouting.decode
        ((PalPeg.LocalRoleFusion.compiled (plan consume)).apply blankM p none)) := by
  obtain ⟨_, b, htokb, hreadb⟩ := hsecond
  cases consume with
  | false =>
    rw [← pair_state false x wm b b (by simp) hreadb]
    exact running_pair false w x p he wm hchain b b htokb htokb
  | true =>
    obtain ⟨_, a, htoka, hreada⟩ := hfirst rfl
    have hnext : PalPeg.GalilScaffoldChainConsume.symbol
        (beforeImmediateWatch true wm a).machine.control.period.focus = some b := by
      simpa [beforeImmediateWatch, watchAfter, afterInternal, PalPeg.GalilScaffoldChainWatch.caught,
        PalPeg.GalilScaffoldChainVerifier.consume, hreada] using htokb
    rw [← pair_state true x wm a b (fun _ => hreada) hreadb]
    exact running_pair true w x p he wm hchain a b htoka hnext

/-- info: 'PalPeg.PhysicalWatchStep.running_pair_good' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms running_pair_good

/-- info: 'PalPeg.PhysicalWatchStep.running_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms running_pair

/-- info: 'PalPeg.PhysicalWatchStep.running' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms running

end PalPeg.PhysicalWatchStep
