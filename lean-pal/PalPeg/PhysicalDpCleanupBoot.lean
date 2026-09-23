import PalPeg.PhysicalDpCleanup

/-! Blank boot establishes the cleanup invariant for both existing DP banks;
the same first sweep still delivers its input to all views. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace PalPeg.PhysicalDpCleanupBoot
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract PalPeg.PhysicalDpCleanup
open PalPeg.PhysicalShiftDispatch (RoutedCore RoutedState liftConfig)
open PalPeg.PhysicalBootFeed PalPeg.PhysicalFeed
open PalPeg.Program PalPeg.Local PalPeg.CloseoutCoreEnc12 PalPeg.LocalStepFusion

attribute [local irreducible] bootStep PalPeg.PhysicalLoanDispatch.machine

theorem boot_nonhead (p : CoreState) (a : Option (Fin 2)) (hs : p.1.slot.val = 0)
    (j : Fin tapeCountM) (hj : (slotIndex.symm j).isLeft = false) :
    (idealRun bootRule blankM p a 12).2 j =
      actList blankM (p.2 j) (bootActs p.1 a (fun k => readWin blankM microRadius (p.2 k)) j) :=
  tickRule_otherSlots (by decide : 2 ≤ microRadius) (fun q _ _ => q)
    commands bootActs bootActs_bound p a hs j hj

/-- Both banks, including the unnamed one, receive the boot floor marker. -/
theorem boot_banks (T : Fin tapeCountM → STape Γm) (a : Option (Fin 2))
    (hT : ∀ j, TEqG blankM (STape.blankTape blankM) (T j)) :
    ∀ bank i, TEqG blankM (padLeft margin (mapTape encProg (STape.blankTape 6)))
      ((bootStep.apply blankM (bootControl,T) a).2 (slotIndex (dpSlotOf bank i))) := by
  unfold bootStep
  let E : PalPeg.GalilScaffoldTop.State PalPeg.GalilScaffoldChainInputSupply.GalilVM → CoreState → Prop :=
    fun _ p => ∀ bank i, p.2 (slotIndex (dpSlotOf bank i)) = padLeft margin (mapTape encProg (STape.blankTape 6))
  have hi : E initialState (idealStep (iterRule bootRule 12) blankM (bootControl,fun _ => shiftedBlank) a) := by
    rw [iterRule_ideal blankM bootRule 12 (bootControl,fun _ => shiftedBlank) a (fun _ => shiftedBlank_pos.ge),idealIter_eq_idealRun]
    intro bank i
    have hj : (slotIndex.symm (slotIndex (dpSlotOf bank i))).isLeft = false := by
      rw [Equiv.symm_apply_apply]; cases bank <;> rfl
    have hh := boot_nonhead (bootControl,fun _ => shiftedBlank) a boot_boundary.1
      (slotIndex (dpSlotOf bank i)) hj
    exact hh.trans (by
      simp only [bootActs,Equiv.symm_apply_apply,bootActs_prepared]
      cases bank <;> rfl)
  generalize hR : iterRule bootRule 12 = R at hi ⊢
  obtain ⟨U,hU,hu⟩ := sweep_from_blank R E initialState bootControl a T
    (fun _ => shiftedBlank) hT (fun _ => shiftedBlank_pos) (fun _ => shiftedBlank_blank) hi
  intro bank i
  have h := hu (slotIndex (dpSlotOf bank i))
  have hi : U (slotIndex (dpSlotOf bank i)) = _ := hU bank i
  rw [hi] at h
  exact h

theorem old_boot (rest : PalPeg.PhysicalScanCount.RestCommands)
    (roles : Equiv.Perm (Fin tapeCountM)) (T : Fin tapeCountM → STape Γm) (a : Option (Fin 2)) :
    (PalPeg.PhysicalLoanDispatch.machine rest).apply blankM ((roles,.inl ()),T) a =
      liftConfig ((PalPeg.LocalRoleRouting.hold bootStep).apply blankM ((roles,bootControl),T) a) := by
  rw [PalPeg.PhysicalLoanDispatch.apply_previous rest _ a rfl rfl rfl,
    PalPeg.PhysicalSnapshotEntryDispatch.apply_previous rest _ a rfl,
    PalPeg.PhysicalSnapshotShiftDispatch.apply_previous rest _ a rfl,
    PalPeg.PhysicalSnapshotMachine.apply_previous rest _ a rfl rfl,
    PalPeg.PhysicalShiftDispatch.apply_previous rest _ a rfl]
  rfl

theorem wrap_boot (L : PalPeg.PhysicalShiftDispatch.RoutedStep)
    (roles : Equiv.Perm (Fin tapeCountM)) (phases : Phases)
    (T : Fin tapeCountM → STape Γm) (a : Option (Fin 2)) :
    (wrap L).apply blankM (((roles,.inl ()),phases),T) a =
      (((L.apply blankM ((roles,.inl ()),T) a).1,fun _ => .done),
        (L.apply blankM ((roles,.inl ()),T) a).2) := rfl

/-- The first sweep establishes both the raw blank bank and its certified done
phase, without asking the source blank tapes to carry a floor already. -/
theorem boot_progress (rest : PalPeg.PhysicalScanCount.RestCommands)
    (roles : Equiv.Perm (Fin tapeCountM)) (phases : Phases)
    (T : Fin tapeCountM → STape Γm) (a : Option (Fin 2))
    (hT : ∀ j, TEqG blankM (STape.blankTape blankM) (T j)) :
    Progress ((PalPeg.PhysicalDpCleanup.machine rest).apply blankM (((roles,.inl ()),phases),T) a) := by
  change Progress ((wrap (PalPeg.PhysicalLoanDispatch.machine rest)).apply blankM _ a)
  rw [wrap_boot,old_boot]
  refine ⟨fun _ => (.done,STape.blankTape 6),fun _ => PalPeg.PhysicalEraseBatch.good_blank,?_⟩
  have hb := boot_banks (fun j => T (roles j)) a (fun j => hT (roles j))
  have hd := PalPeg.LocalRoleRouting.decode_hold bootStep blankM ((roles,bootControl),T) a
  intro i
  refine ⟨rfl,?_⟩
  have hh := congrArg Prod.snd hd
  have ht := congrFun hh (slotIndex (dpSlotOf
    (!((PalPeg.LocalRoleRouting.hold bootStep).apply blankM ((roles,bootControl),T) a).1.2.dpLive) i))
  change TEqG blankM (padLeft margin (mapTape encProg (STape.blankTape 6)))
    ((PalPeg.LocalRoleRouting.decode ((PalPeg.LocalRoleRouting.hold bootStep).apply blankM ((roles,bootControl),T) a)).2 _)
  rw [ht]
  exact hb _ i

/-- At boot the source's old encoding supplies actual blank tapes. -/
theorem boot_source (w : List (Fin 2))
    (x : PalPeg.GalilScaffoldTop.State PalPeg.GalilScaffoldChainInputSupply.GalilVM)
    (roles : Equiv.Perm (Fin tapeCountM)) (T : Fin tapeCountM → STape Γm)
    (he : PalPeg.PhysicalLoanInvariant.Enc w x ((roles,.inl ()),T)) :
    ∀ j, TEqG blankM (STape.blankTape blankM) (T j) := by
  have hn : ¬ PalPeg.PhysicalLoanInvariant.NeedsLoan x := by
    intro h
    exact ((PalPeg.PhysicalLoanInvariant.enc_partial w x _ h).mp he).2
  obtain ⟨⟨_,_,_,hT⟩,_⟩ := (PalPeg.PhysicalLoanInvariant.enc_full w x _ hn).mp he
  intro j
  simpa only [PalPeg.LocalRoleRouting.decode,Equiv.apply_symm_apply] using hT (roles.symm j)

/-- The shared cleanup machine preserves input arrival, including the first
letter on the actual all-blank initial state. -/
theorem forward_feed (rest : PalPeg.PhysicalScanCount.RestCommands)
    (w : List (Fin 2)) (x : PalPeg.GalilScaffoldTop.State PalPeg.GalilScaffoldChainInputSupply.GalilVM)
    (p : Config) (a : Fin 2) (he : PalPeg.PhysicalDpCleanup.Enc w x p) :
    PalPeg.PhysicalDpCleanup.Enc w (PalPeg.GalilArriveChain.arriveState' a x)
      ((PalPeg.PhysicalDpCleanup.machine rest).apply blankM p (some a)) := by
  rcases p with ⟨⟨⟨roles,q⟩,phases⟩,T⟩
  cases q with
  | inr c => exact forward_feed_running rest w x ((roles,c),T) phases a he
  | inl tag =>
    cases tag
    refine ⟨?_,boot_progress rest roles phases T (some a) (boot_source w x roles T he.1)⟩
    have hh := PalPeg.PhysicalLoanDispatch.forward_feed rest w x ((roles,.inl ()),T) a he.1
    change PalPeg.PhysicalLoanInvariant.Enc w _ (forget ((wrap _).apply blankM _ (some a)))
    rw [wrap_boot]
    exact hh

theorem forward_starved (rest : PalPeg.PhysicalScanCount.RestCommands)
    (w : List (Fin 2)) (x : PalPeg.GalilScaffoldTop.State PalPeg.GalilScaffoldChainInputSupply.GalilVM)
    (p : Config) (he : PalPeg.PhysicalDpCleanup.Enc w x p) (hs : PalPeg.FrameFunction.starvedTest x = true) :
    PalPeg.PhysicalDpCleanup.Enc w x ((PalPeg.PhysicalDpCleanup.machine rest).apply blankM p none) := by
  rcases p with ⟨⟨⟨roles,q⟩,phases⟩,T⟩
  cases q with
  | inr c => exact forward_starved_running rest w x ((roles,c),T) phases he hs
  | inl tag =>
    cases tag
    refine ⟨?_,boot_progress rest roles phases T none (boot_source w x roles T he.1)⟩
    have hh := PalPeg.PhysicalLoanDispatch.forward_starved rest w x ((roles,.inl ()),T) he.1 hs
    change PalPeg.PhysicalLoanInvariant.Enc w x (forget ((wrap _).apply blankM _ none))
    rw [wrap_boot]
    exact hh

/-- info: 'PalPeg.PhysicalDpCleanupBoot.boot_banks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boot_banks

/-- info: 'PalPeg.PhysicalDpCleanupBoot.forward_feed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forward_feed

/-- info: 'PalPeg.PhysicalDpCleanupBoot.forward_starved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forward_starved

end PalPeg.PhysicalDpCleanupBoot
