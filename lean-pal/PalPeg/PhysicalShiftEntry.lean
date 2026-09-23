import PalPeg.PhysicalCacheInvariant

/-!
# Lending the saved semiperiod to the shift remainder

This is the role exchange inside the entry tick, after its ordinary operations
have reset remaining and selected shift. It swaps the existing remaining and
mirror carriers. The zero carrier becomes the rebuilding mirror, so the common
cache is preserved. Producing this intermediate state from the comparison and
selecting the exchange in the dispatcher are separate entry obligations.
-/
set_option autoImplicit false
namespace PalPeg.PhysicalShiftEntry
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract
open PalPeg.PhysicalSpare (Rep spareIndex)
open PalPeg.PhysicalPeriodMirror (mirrorIndex)
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilScaffoldCounter (Counter ofNat reset)
open PalPeg.Program (STape)
open PalPeg.Local (pos)
open PalPeg.LocalCounter (Seg absCtr)
open PalPeg.CloseoutCoreEnc12

noncomputable def remainingIndex : Fin tapeCountM := slotIndex (counterSlot 1)

noncomputable def entryRoles : Equiv.Perm (Fin tapeCountM) :=
  Equiv.swap remainingIndex mirrorIndex

def lendControl (q : CoreControl) : CoreControl :=
  {q with polarity := Function.update q.polarity 1 true}

noncomputable def lendCore (p : CoreState) : CoreState :=
  (lendControl p.1, fun j => p.2 (entryRoles j))

def lent (x : State GalilVM) (h : ℕ) : State GalilVM :=
  ⟨x.ctl, {x.vm with remaining := ofNat h}⟩

theorem roles_remaining : entryRoles remainingIndex = mirrorIndex :=
  Equiv.swap_apply_left _ _

theorem roles_mirror : entryRoles mirrorIndex = remainingIndex :=
  Equiv.swap_apply_right _ _

theorem roles_other (j : Fin tapeCountM) (hr : j ≠ remainingIndex)
    (hm : j ≠ mirrorIndex) : entryRoles j = j :=
  Equiv.swap_apply_of_ne_of_ne hr hm

theorem roles_spare : entryRoles spareIndex = spareIndex := by
  apply roles_other
  · intro h
    have hs := slotIndex.injective h
    simp only [counterSlot, Sum.inr.injEq, Sum.inl.injEq] at hs
    exact (by decide : (10 : Fin 16) ≠ 1) hs
  · intro h
    have hs := slotIndex.injective h
    simp only [counterSlot, mirrorSlot, Sum.inr.injEq, Sum.inl_ne_inr] at hs

/-- Zero has the same abstract value under either physical sign bit. -/
theorem absCtr_zero_positive (seg : STape Seg) (bit : Bool)
    (hz : absCtr seg bit = reset) : absCtr seg true = ofNat 0 := by
  have hv := PalPeg.LocalCounter.value_eq seg bit
  rw [hz] at hv
  have hval : PalPeg.LocalCounter.val seg = 0 := by
    cases bit <;> simp [PalPeg.GalilScaffoldCounter.value, reset] at hv <;> omega
  simp [absCtr, hval]

/-- A canonical witness is needed only for the ideal tape, not for the real
swept mirror, whose representation is observational. -/
noncomputable def lentTapes (T : Slot → STape Γm) (seg : STape Seg) : Slot → STape Γm :=
  fun slot => if slot = counterSlot 1 then padLeft margin (mapTape encSeg seg)
    else if slot = mirrorSlot 5 then T (counterSlot 1) else T slot

theorem counterOf_lent (x : State GalilVM) (h : ℕ) (c : Fin 16) (hc : c ≠ 1) :
    counterOf (lent x h) c = counterOf x c := by
  fin_cases c <;> first | exact (hc rfl).elim | rfl

theorem encControl_lent {w : List (Fin 2)} {x : State GalilVM} {q : CoreControl}
    (he : EncControl w x q) (h : ℕ) : EncControl w (lent x h) (lendControl q) :=
  ⟨he.ctl, he.chainTag, he.chainPhase, he.chainForward, he.chainBroken,
    he.fppMode, he.fppFinalStage, he.fppPc, he.fppDone, he.dpPc, he.dpDone,
    he.searchMode, he.searchFinalStage, he.searchQuarter, he.periodOnly,
    he.placeGap, he.onLetter, he.leftFirst⟩

/-- The exchange preserves every field of the existing tape encoding. -/
theorem tapes_lent (x : State GalilVM) (q : CoreControl) (T : Slot → STape Γm)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (hchain : x.vm.chain = .watch wm)
    (he : EncTapes margin x q.polarity q.gap q.micro q.fppLive q.dpLive T)
    (h : ℕ) (seg : STape Seg) (hseg : absCtr seg true = ofNat h) :
    EncTapes margin (lent x h) (lendControl q).polarity q.gap q.micro q.fppLive q.dpLive
      (lentTapes T seg) where
  margins := by
    intro slot
    simp only [lentTapes]
    split_ifs
    · rw [pos_padLeft]; omega
    · exact he.margins _
    · exact he.margins _
  heads := by
    intro v head hh
    obtain ⟨view, vt, ha, hv, hs, hc, hw⟩ := he.heads v head hh
    exact ⟨view, vt, ha, hv, fun i => by simpa [lentTapes, counterSlot, mirrorSlot] using hs i, hc, hw⟩
  idleHead := by
    intro hh
    obtain ⟨view, vt, hv, hs, hc, hw⟩ := he.idleHead hh
    exact ⟨view, vt, hv, fun i => by simpa [lentTapes, counterSlot, mirrorSlot, headSlot] using hs i, hc, hw⟩
  fpp := by
    intro i
    cases hb : q.fppLive <;> simpa [lentTapes, progSlotOf, counterSlot, mirrorSlot, hb, lent] using he.fpp i
  dp := by
    intro i
    cases hb : q.dpLive <;> simpa [lentTapes, dpSlotOf, counterSlot, mirrorSlot, hb, lent] using he.dp i
  idleShape := by
    intro i
    cases hb : q.fppLive <;> simpa [lentTapes, progSlotOf, counterSlot, mirrorSlot, hb] using he.idleShape i
  counters := by
    intro c value hv
    by_cases hc : c = 1
    · subst c
      have hvalue : ofNat h = value := by simpa [counterOf, lent] using hv
      exact ⟨seg, by simpa [lendControl, hvalue] using hseg, by simp [lentTapes]⟩
    obtain ⟨raw, ha, ht⟩ := he.counters c value ((counterOf_lent x h c hc).symm.trans hv)
    exact ⟨raw, by simpa [lendControl, hc] using ha,
      by simpa [lentTapes, counterSlot, mirrorSlot, hc] using ht⟩
  places := by
    intro i place hp
    obtain ⟨stack, junk, hj, hs, ht⟩ := he.places i place hp
    exact ⟨stack, junk, hj, hs, by simpa [lentTapes, counterSlot, mirrorSlot] using ht⟩
  mirrors := by
    intro m value hv
    have hn : mirrorSource m ≠ 1 := by fin_cases m <;> decide
    have hm : m ≠ 5 := by
      intro hm
      subst m
      simp [counterOf, lent, mirrorSource, hchain] at hv
    obtain ⟨raw, ha, ht⟩ := he.mirrors m value ((counterOf_lent x h _ hn).symm.trans hv)
    exact ⟨raw, by simpa [lendControl, hn] using ha,
      by simpa [lentTapes, counterSlot, mirrorSlot, hm] using ht⟩
  period := by
    intro tape ht
    simpa [lentTapes, counterSlot, mirrorSlot] using he.period tape ht
  answer := by
    intro tape ht
    simpa [lentTapes, counterSlot, mirrorSlot] using he.answer tape ht

/-- Actual sweep tapes may contain trailing blanks. Only the ideal witness
is canonicalized; the real output is precisely the finite role permutation. -/
theorem running_lend (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (he : PalPeg.PhysicalCacheInvariant.Running w x p)
    (hchain : x.vm.chain = .watch wm) (hmode : x.ctl.mode = .shift)
    (hreset : x.vm.remaining = reset) :
    PalPeg.PhysicalCacheInvariant.Running w (lent x (periodLength wm)) (lendCore p) := by
  have hm := PalPeg.PhysicalCacheInvariant.running_mirror he wm (Or.inl hchain)
  have hmag : PalPeg.PhysicalCacheInvariant.mirrorMagnitude x (periodLength wm) = periodLength wm := by
    simp [PalPeg.PhysicalCacheInvariant.mirrorMagnitude, hmode, hreset, PalPeg.GalilScaffoldCounter.value, reset]
  rw [hmag] at hm
  obtain ⟨seg, hseg, hm⟩ := hm
  obtain ⟨T, hT, ht⟩ := he
  have hcore : CoreEnc w (lent x (periodLength wm))
      (lendControl p.1, tapesOf (lentTapes (fun slot => T (slotIndex slot)) seg)) := by
    refine ⟨⟨encControl_lent hT.1.1.1.1 _, ?_⟩, hT.1.1.2⟩
    simpa only [tapesOf, Equiv.symm_apply_apply, lendControl] using
      tapes_lent x p.1 (fun slot => T (slotIndex slot)) wm hchain hT.1.1.1.2 _ seg hseg
  have hteq : ∀ j, TEqG blankM
      (tapesOf (lentTapes (fun slot => T (slotIndex slot)) seg) j) ((lendCore p).2 j) := by
    intro j
    obtain ⟨slot, rfl⟩ := slotIndex.surjective j
    simp only [tapesOf, Equiv.symm_apply_apply, lentTapes]
    by_cases hr : slot = counterSlot 1
    · subst slot
      simp only [ite_true]
      change TEqG blankM (padLeft margin (mapTape encSeg seg)) (p.2 (entryRoles remainingIndex))
      rw [roles_remaining]
      exact hm
    by_cases hmirror : slot = mirrorSlot 5
    · subst slot
      simp only [if_neg hr, ite_true]
      change TEqG blankM (T remainingIndex) (p.2 (entryRoles mirrorIndex))
      rw [roles_mirror]
      exact ht remainingIndex
    rw [if_neg hr, if_neg hmirror]
    change TEqG blankM (T (slotIndex slot)) (p.2 (entryRoles (slotIndex slot)))
    rw [roles_other _ (fun h => hr (slotIndex.injective h))
      (fun h => hmirror (slotIndex.injective h))]
    exact ht _
  have hc := PalPeg.PhysicalCacheInvariant.running_cache (⟨T, hT, ht⟩ : PalPeg.PhysicalCacheInvariant.Running w x p)
  obtain ⟨h, age, spare, hi, hs, _⟩ := (show ∃ h age spare,
      PalPeg.ChainBoundaryCache.Inv h age wm.machine.control spare ∧
      Rep (p.1.polarity 10) spare (p.2 spareIndex) ∧
      Rep true (ofNat (PalPeg.PhysicalCacheInvariant.mirrorMagnitude x h)) (p.2 mirrorIndex) from
    by simpa only [PalPeg.PhysicalCacheInvariant.Cache, hchain] using hc)
  have hlength : periodLength wm = h := PalPeg.ChainBoundaryCache.cursor_length hi.cursor
  obtain ⟨zeroSeg, hzero, hz⟩ := hT.1.1.1.2.counters 1 reset (by simp [counterOf, hreset])
  have hzeroRep : Rep true (ofNat 0) (p.2 remainingIndex) :=
    ⟨zeroSeg, absCtr_zero_positive zeroSeg _ hzero, by rw [← hz]; exact ht remainingIndex⟩
  apply PalPeg.PhysicalCacheInvariant.of_watching_cache (wm := wm)
    (Or.inl (show (lent x (periodLength wm)).vm.chain = .watch wm from hchain))
    ⟨_, hcore, hteq⟩
  change PalPeg.PhysicalCacheInvariant.Cache (lent x (periodLength wm)) (Function.update p.1.polarity 1 true 10)
    (p.2 (entryRoles spareIndex)) (p.2 (entryRoles mirrorIndex))
  rw [roles_spare, roles_mirror]
  simp only [PalPeg.PhysicalCacheInvariant.Cache, lent, hchain, Function.update_of_ne (by decide : (10 : Fin 16) ≠ 1)]
  refine ⟨h, age, spare, hi, hs, ?_⟩
  simpa [PalPeg.PhysicalCacheInvariant.mirrorMagnitude, lent, hmode, PalPeg.GalilScaffoldCounter.value, ofNat, hlength]
    using hzeroRep

/-- info: 'PalPeg.PhysicalShiftEntry.running_lend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms running_lend

end PalPeg.PhysicalShiftEntry
