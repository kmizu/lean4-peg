import PalPeg.PhysicalFinal

/-! # Reading the report and output bits from the common machine's control

The control carries the abstract controller (`EncControl.ctl`) in every layer of the common
encoding: loaned, snapshot and cleanup. Output and report tests read it without the tapes. -/
set_option autoImplicit false
namespace PalPeg.PhysicalReport
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract
open PalPeg.PhysicalShiftDispatch (RoutedCore liftConfig)
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply

theorem ctl_loan (w : List (Fin 2)) (x : State GalilVM) (p : RoutedCore)
    (he : PalPeg.PhysicalLoanInvariant.Enc w x (liftConfig p)) :
    ctlAbs p.1.2.ctl = x.ctl := by
  by_cases hn : PalPeg.PhysicalLoanInvariant.NeedsLoan x
  · obtain ⟨_,T,hT,_⟩ := (PalPeg.PhysicalLoanInvariant.enc_partial w x _ hn).mp he
    exact hT.1.1.1.1.1.ctl
  · obtain ⟨⟨y,hy,T,hT,_⟩,_⟩ := (PalPeg.PhysicalLoanInvariant.enc_full w x _ hn).mp he
    exact hT.1.1.1.1.ctl.trans hy.1.symm

/-- The output bit of the common machine: the controller's output flag. -/
def outQ (c : PalPeg.PhysicalDpCleanup.Control) : Bool :=
  match c.1.2 with
  | .inl _ => false
  | .inr q => (ctlAbs q.ctl).output

theorem output_of_enc (w : List (Fin 2)) (x : State GalilVM) (p : PalPeg.PhysicalDpCleanup.Config)
    (he : PalPeg.PhysicalDpCleanup.Enc w x p) (hpos : position x.vm.right ≠ 0) :
    x.ctl.output = outQ p.1 := by
  obtain ⟨⟨⟨roles, c⟩, phases⟩, T⟩ := p
  cases c with
  | inr q =>
    have h := ctl_loan w x ((roles, q), T) he.1
    simp only [outQ]
    rw [h]
  | inl u =>
    exfalso
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
      apply hpos
      rw [← hright, hinit]
      rfl

/-- **The output contract of the final consumer**, for every source on the run. -/
theorem encOut (w : List (Fin 2))
    (m : PalPeg.LocalReplayParked.Mirrored1 (PalPeg.LocalBlankState.tapeCount 0))
    (p : PalPeg.PhysicalDpCleanup.Config)
    (henc : PalPeg.PhysicalDpCleanup.Enc w (PalPeg.LocalSysConcrete.absSC m) p)
    (hcaught : PalPeg.ShadowedLocalFinal.reportCaught w (PalPeg.LocalSysConcrete.absSC m) = true) :
    m.vm.ctl.output = outQ p.1 := by
  obtain ⟨-, -, hon, -, -⟩ := (PalPeg.ShadowedLocalFinal.reportCaught_iff w _).mp hcaught
  unfold PalPeg.GalilScaffoldChainInputSupply.onLetterTest at hon
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hon
  exact output_of_enc w _ p henc (by omega)

/-- info: 'PalPeg.PhysicalReport.encOut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms encOut

end PalPeg.PhysicalReport
