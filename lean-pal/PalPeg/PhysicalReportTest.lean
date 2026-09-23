import PalPeg.PhysicalReport

/-!
# The report test of the common machine, read from its control and windows

`reportCaught` asks for scan, not replaying, the right head on a letter, and nothing arrived
beyond the right head. The first three are bits of the control. The last is read from the
right view's windows: the top of `near` and the front of the queue, the same two symbols the
availability test reads.
-/
set_option autoImplicit false
namespace PalPeg.PhysicalReportTest
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply

/-- Something has arrived beyond a view's head: the top of `near` or the front of the queue. -/
noncomputable def pendingTest {fppBound dpBound K : ℕ} (q : QPhys fppBound dpBound)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) (v : Fin 4) : Bool :=
  let tops := PalPeg.ConcreteLocalMachine.viewTopsOfWindows (q.micro v).2.1 (viewWindows v ws)
  tops.near.isSome || tops.front.isSome

theorem pendingTest_of_view {fppBound dpBound K : ℕ} (q : QPhys fppBound dpBound)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm K) (v : Fin 4)
    (view : PalPeg.LocalInputView.InputView)
    (htops : PalPeg.ConcreteLocalMachine.viewTopsOfWindows (q.micro v).2.1 (viewWindows v ws)
      = PalPeg.ConcreteLocalMachine.viewTops view)
    (hcells : PalPeg.LocalViewCells.ViewCells view) (hwf : PalPeg.LocalInputView.WF view) :
    pendingTest q ws v = decide ¬ ((PalPeg.LocalArrival.absHead' view []).head.incoming = [] ∧
      (PalPeg.LocalArrival.absHead' view []).head.right = []) := by
  unfold pendingTest
  rw [htops]
  obtain ⟨letters, hnear⟩ := PalPeg.LocalViewCells.near_letters hcells
  simp only [PalPeg.ConcreteLocalMachine.viewTops, PalPeg.RTQueue.head?_eq hwf,
    PalPeg.LocalArrival.absHead', List.append_nil, hnear]
  cases letters <;> cases PalPeg.RTQueue.toList view.far <;> simp

/-- On an encoded head, the pending test reads the abstract head. -/
theorem pendingTest_eq {fppBound dpBound K margin : ℕ} {x : State GalilVM}
    {q : QPhys fppBound dpBound} {T : Slot → PalPeg.Program.STape Γm}
    (henc : EncTapes margin x q.polarity q.gap q.micro q.fppLive q.dpLive T)
    (hmargin : K ≤ margin) (v : Fin 4) (head : PalPeg.GalilScaffoldInputHead.PlaceHead)
    (hhead : headOf x v = some head) :
    pendingTest q (fun tape => PalPeg.Local.readWin blankM K (tapesOf T tape)) v
      = decide ¬ (head.head.incoming = [] ∧ head.head.right = []) := by
  obtain ⟨view, viewTapes, habs, hrep, hslots, hcells, hwf⟩ := henc.heads v head hhead
  rw [← habs]
  apply pendingTest_of_view q _ v view _ hcells hwf
  rw [viewWindows_of_encoded v T viewTapes hslots]
  exact PalPeg.ConcreteLocalMachine.viewTopsOfWindows_eq hmargin hcells hrep

theorem pendingTest_congr {fppBound dpBound K : ℕ} (q : QPhys fppBound dpBound)
    (ws ws' : Fin tapeCountM → PalPeg.Local.Window Γm K) (v : Fin 4)
    (h : ∀ i, ws (slotIndex (headSlot v i)) = ws' (slotIndex (headSlot v i))) :
    pendingTest q ws v = pendingTest q ws' v := by
  unfold pendingTest viewWindows
  simp only [h]

/-- **The report test of the common machine.** Read from the control and the right view's
windows, through the machine's current roles. -/
noncomputable def repW (c : PalPeg.PhysicalDpCleanup.Control)
    (ws : Fin tapeCountM → PalPeg.Local.Window Γm macroRadius) : Bool :=
  match c.1.2 with
  | .inl _ => false
  | .inr q => decide ((ctlAbs q.ctl).mode = PalPeg.GalilScaffoldController.Mode.scan) &&
      decide ((ctlAbs q.ctl).replaying = false) && q.onLetterBit &&
      !pendingTest q (fun j => ws (c.1.1 j)) 2

/-- The running layers of the common encoding expose the control and the head slots of a
state with the same controller and the same right head. -/
theorem headEnc_of_loan (w : List (Fin 2)) (x : State GalilVM)
    (p : PalPeg.PhysicalShiftDispatch.RoutedCore)
    (he : PalPeg.PhysicalLoanInvariant.Enc w x (PalPeg.PhysicalShiftDispatch.liftConfig p)) :
    ∃ (y : State GalilVM) (T : Fin tapeCountM → PalPeg.Program.STape Γm),
      y.ctl = x.ctl ∧ y.vm.right = x.vm.right ∧
      PalPeg.PhysicalEncoding.Enc w margin y (p.1.2, fun slot => T (slotIndex slot)) ∧
      ∀ v i, PalPeg.CloseoutCoreEnc12.TEqG blankM (T (slotIndex (headSlot v i)))
        (p.2 (p.1.1 (slotIndex (headSlot v i)))) := by
  by_cases hn : PalPeg.PhysicalLoanInvariant.NeedsLoan x
  · obtain ⟨_,T,hT,ht⟩ := (PalPeg.PhysicalLoanInvariant.enc_partial w x _ hn).mp he
    refine ⟨x, PalPeg.PhysicalDebtMirror.repaired T, rfl, rfl, hT.1.1.1.1, fun v i => ?_⟩
    have hslot : PalPeg.PhysicalDebtMirror.repaired T (slotIndex (headSlot v i)) =
        T (slotIndex (headSlot v i)) := by
      simp [PalPeg.PhysicalDebtMirror.repaired, PalPeg.PhysicalDebtMirror.repair, headSlot,
        mirrorSlot]
    rw [hslot]
    exact ht _
  · obtain ⟨⟨y,hy,T,hT,ht⟩,_⟩ := (PalPeg.PhysicalLoanInvariant.enc_full w x _ hn).mp he
    have hright : y.vm.right = x.vm.right := by
      have hs := hy.2.1
      unfold PalPeg.PhysicalRestartStorage.Same at hs
      rw [hs]
      rfl
    exact ⟨y, T, hy.1.symm, hright, hT.1.1.1, fun v i => ht _⟩

/-- A boot control stands for the initial state, whose right head is at place `0`. -/
theorem boot_right (w : List (Fin 2)) (x : State GalilVM) (p : PalPeg.PhysicalDpCleanup.Config)
    (he : PalPeg.PhysicalDpCleanup.Enc w x p) (u : Unit) (hc : p.1.1.2 = .inl u) :
    position x.vm.right = 0 := by
  obtain ⟨⟨⟨roles, c⟩, phases⟩, T⟩ := p
  simp only at hc
  subst hc
  have h := he.1
  by_cases hn : PalPeg.PhysicalLoanInvariant.NeedsLoan x
  · have hp := ((PalPeg.PhysicalLoanInvariant.enc_partial w x _ hn).mp h).2
    simp [PalPeg.PhysicalDpCleanup.forget] at hp
  · obtain ⟨⟨y, hy, hold⟩, _⟩ := (PalPeg.PhysicalLoanInvariant.enc_full w x _ hn).mp h
    have hinit : y = initialState := by
      simpa [PalPeg.PhysicalSnapshotInvariant.OldEnc, PalPeg.PhysicalShiftDispatch.Enc,
        PalPeg.PhysicalBoundaryCount.Enc, PalPeg.PhysicalCacheMachine.routedEnc,
        PalPeg.PhysicalCacheMachine.Enc, PalPeg.PhysicalCacheInvariant.Enc,
        PalPeg.LocalRoleRouting.decode, PalPeg.PhysicalDpCleanup.forget,
        PalPeg.PhysicalContract.Enc] using hold.1
    have hright : y.vm.right = x.vm.right := by
      have hs := hy.2.1
      unfold PalPeg.PhysicalRestartStorage.Same at hs
      rw [hs]
      rfl
    rw [← hright, hinit]
    rfl

/-- **The report contract of the final consumer**, for every source on the run. -/
theorem encRep (w : List (Fin 2)) (x : State GalilVM) (p : PalPeg.PhysicalDpCleanup.Config)
    (he : PalPeg.PhysicalDpCleanup.Enc w x p) :
    PalPeg.ShadowedLocalFinal.reportCaught w x =
      repW p.1 (fun j => PalPeg.Local.readWin blankM macroRadius (p.2 j)) := by
  obtain ⟨⟨⟨roles, c⟩, phases⟩, T⟩ := p
  cases c with
  | inl u =>
    have hpos := boot_right w x _ he u rfl
    simp only [repW]
    cases hcaught : PalPeg.ShadowedLocalFinal.reportCaught w x
    · rfl
    · exfalso
      obtain ⟨-, -, hon, -, -⟩ := (PalPeg.ShadowedLocalFinal.reportCaught_iff w x).mp hcaught
      unfold onLetterTest at hon
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hon
      omega
  | inr q =>
    obtain ⟨y, T', hctl, hright, henc, hteq⟩ := headEnc_of_loan w x ((roles, q), T) he.1
    have hctlq : ctlAbs q.ctl = x.ctl := henc.1.ctl.trans hctl
    have hon : q.onLetterBit = onLetterTest w x.vm := by
      rw [henc.1.onLetter]
      unfold onLetterTest
      rw [hright]
    have hpend : pendingTest q (fun j => PalPeg.Local.readWin blankM macroRadius (T (roles j))) 2 =
        decide ¬ (x.vm.right.head.incoming = [] ∧ x.vm.right.head.right = []) := by
      rw [pendingTest_congr q _ (fun tape => PalPeg.Local.readWin blankM macroRadius
          (tapesOf (fun slot => T' (slotIndex slot)) tape)) 2 (fun i => ?_)]
      · have h := pendingTest_eq (K := macroRadius) (q := q) henc.2 (le_of_eq rfl) 2 y.vm.right rfl
        rw [hright] at h
        exact h
      · simp only [tapesOf, Equiv.apply_symm_apply]
        exact (PalPeg.ConcreteLocalMachine.readWin_teqG (hteq 2 i)).symm
    show PalPeg.ShadowedLocalFinal.reportCaught w x =
      (decide ((ctlAbs q.ctl).mode = PalPeg.GalilScaffoldController.Mode.scan) &&
        decide ((ctlAbs q.ctl).replaying = false) && q.onLetterBit &&
        !pendingTest q (fun j => PalPeg.Local.readWin blankM macroRadius (T (roles j))) 2)
    rw [hctlq, hon, hpend, Bool.eq_iff_iff, PalPeg.ShadowedLocalFinal.reportCaught_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not,
      not_not, and_assoc]

/-- **`PAL ∈ PEG` from the common machine**: the report and output contracts are proved; what
remains are the unimplemented tick cases and the freeze after the last report. -/
theorem given_remainingCases_and_frozen (rest : PalPeg.PhysicalScanCount.RestCommands)
    (hcases : PalPeg.PhysicalContract.TickCases (PalPeg.PhysicalDpCleanup.machine rest) blankM
      PalPeg.PhysicalDpCleanup.Enc)
    (PhysFrozen : List (Fin 2) → PalPeg.PhysicalDpCleanup.Config → Prop)
    (hfrozenEnter : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PalPeg.CloseoutCheckW.PreTraceIMW PalPeg.GalilFinalAssembly2.centreC
        PalPeg.GalilFinalAssembly2.placeC 0 1 0 w st Tc → PalPeg.CloseoutCheckW.CanonTrace 0 w st Tc →
      ∀ m p, PalPeg.LocalShadowConcrete.OnRun (PalPeg.ShadowedLocalFinal.localGood (spare := 0))
          (PalPeg.ShadowedLocalFinal.postPhase 0 1 0) w
          (PalPeg.ShadowedLocalFinal.heldAfter (Tc w.length) st) m →
        PalPeg.ShadowedLocalFinal.frozenAt w m →
        PalPeg.PhysicalDpCleanup.Enc w (PalPeg.LocalSysConcrete.absSC m) p → PhysFrozen w p)
    (hfrozenKeep : ∀ (w : List (Fin 2)) p, PhysFrozen w p →
      PhysFrozen w ((PalPeg.PhysicalDpCleanup.machine rest).apply blankM p none))
    (hfrozenQuiet : ∀ (w : List (Fin 2)) p, PhysFrozen w p →
      repW p.1 (fun j => PalPeg.Local.readWin blankM macroRadius (p.2 j)) = false) :
    PegSeparation.RecognizedByTotalPEG PalPeg.PAL :=
  PalPeg.PhysicalFinal.given_tickCases_and_reports rest hcases repW PalPeg.PhysicalReport.outQ
    PhysFrozen
    { frozenEnter := hfrozenEnter
      frozenKeep := hfrozenKeep
      frozenQuiet := hfrozenQuiet
      encRep := fun w _ _ _ _ m p _ he => encRep w _ p he
      encOut := fun w _ _ _ _ m p _ he hc => PalPeg.PhysicalReport.encOut w m p he hc }

/-- info: 'PalPeg.PhysicalReportTest.given_remainingCases_and_frozen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms given_remainingCases_and_frozen

/-- info: 'PalPeg.PhysicalReportTest.pendingTest_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pendingTest_eq

end PalPeg.PhysicalReportTest
