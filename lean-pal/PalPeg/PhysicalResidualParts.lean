import PalPeg.PhysicalFinalResidual

/-!
# The residual ticks, split by mode

`UnhandledTicks` is one obligation over every tick the common machine does not handle yet. Here
it is split into one obligation per remaining kind of tick, all of the same shape `TicksWhere`:
the scan ticks outside the seven dispatcher cases, `fpp` of a halted program, the select half of `choose`, the reset
of `rewind`, `init` and `replayStart`. The final theorem then takes these six and the freeze.
-/
set_option autoImplicit false
namespace PalPeg.PhysicalResidualParts
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract
open PalPeg.PhysicalScanCount (RestCommands)
open PalPeg.GalilFinalAssembly2 (centreC placeC)
open PalPeg.CloseoutCheckW (PreTraceIMW CanonTrace)
open PalPeg.LocalSysConcrete (absSC)
open PalPeg.LocalReplayParked (Mirrored1)
open PalPeg.LocalBlankState (tapeCount)
open PalPeg.ShadowedLocalFinal (localGood postPhase frozenAt heldAfter)

/-- **The common machine realizes the ticks whose source satisfies `P`**, with every source fact
the consumer supplies. -/
def TicksWhere (rest : RestCommands) (P : List (Fin 2) → State GalilVM → Prop) : Prop :=
  ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
    PreTraceIMW centreC placeC 0 1 0 w st Tc → CanonTrace 0 w st Tc →
    ∀ (m : Mirrored1 (tapeCount 0)) (p : PalPeg.PhysicalDpCleanup.Config),
      PalPeg.LocalShadowConcrete.ArrivedOnRun (localGood (spare := 0)) (postPhase 0 1 0) w
        (heldAfter (Tc w.length) st) m →
      ¬ frozenAt w m → PalPeg.PhysicalDpCleanup.Enc w (absSC m) p →
      PalPeg.FrameFunction.starvedTest (absSC m) = false →
      Tick (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 (absSC m)
        (PalPeg.PhysicalCacheMachine.successor w (absSC m)) →
      P w (absSC m) →
      PalPeg.PhysicalDpCleanup.Enc w (PalPeg.PhysicalCacheMachine.successor w (absSC m))
        ((PalPeg.PhysicalDpCleanup.machine rest).apply blankM p none)

/-- Scan ticks outside the seven dispatcher cases: matched, fallback, restart, the search. -/
def ScanRest (w : List (Fin 2)) (x : State GalilVM) : Prop :=
  x.ctl.mode = .scan ∧ ¬ PalPeg.PhysicalScanCount.CountAtRest x ∧
    ¬ PalPeg.PhysicalBoundaryCount.CountWatch x ∧ ¬ PalPeg.PhysicalBoundaryCount.CountBackReady x ∧
    ¬ PalPeg.PhysicalShiftDispatch.Entry w x ∧ ¬ PalPeg.PhysicalGrowCount.CountGrow x ∧
    ¬ PalPeg.PhysicalGrowMatchCase.MatchGrow x

/-- The fpp tick of a program that has already halted (a live program's tick is handled). -/
def FppDone (_ : List (Fin 2)) (x : State GalilVM) : Prop :=
  x.ctl.mode = .fpp ∧ x.vm.fpp.program.done = true

/-- The choose tick that selects and leaves for `rewind`. -/
def ChooseSelect (_ : List (Fin 2)) (x : State GalilVM) : Prop :=
  x.ctl.mode = .choose ∧ ¬ PalPeg.PhysicalPhaseLayers.ChooseBack x

/-- The rewind tick at the first mark: resets the program and leaves for `replayStart`. -/
def RewindReset (w : List (Fin 2)) (x : State GalilVM) : Prop :=
  x.ctl.mode = .rewind ∧
    (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w).atFirst x.vm = true

def InitMode (_ : List (Fin 2)) (x : State GalilVM) : Prop := x.ctl.mode = .init

def ReplayStartMode (_ : List (Fin 2)) (x : State GalilVM) : Prop := x.ctl.mode = .replayStart

/-- **The six parts cover the residual.** -/
theorem unhandled_of_parts (rest : RestCommands)
    (hscan : TicksWhere rest ScanRest) (hfpp : TicksWhere rest FppDone)
    (hselect : TicksWhere rest ChooseSelect) (hreset : TicksWhere rest RewindReset)
    (hinit : TicksWhere rest InitMode) (hreplay : TicksWhere rest ReplayStartMode) :
    PalPeg.PhysicalPhaseLayers.UnhandledTicks rest := by
  intro w st Tc hpre hcanon m p hon hf he hs htick hrest hwatch hback hshift hentry hgrow hmatch
    hhome hmark hchooseBack hcopy hrewind hfppLive
  have go := fun (P : List (Fin 2) → State GalilVM → Prop) (h : TicksWhere rest P)
    (hp : P w (absSC m)) => h w st Tc hpre hcanon m p hon hf he hs htick hp
  cases hmode : (absSC m).ctl.mode with
  | init => exact go _ hinit hmode
  | scan => exact go _ hscan ⟨hmode, hrest, hwatch, hback, hentry, hgrow, hmatch⟩
  | shift => exact absurd hmode hshift
  | copy => exact absurd hmode hcopy
  | home => exact absurd hmode hhome
  | fpp =>
    refine go _ hfpp ⟨hmode, ?_⟩
    cases hd : (absSC m).vm.fpp.program.done
    · exact absurd ⟨hmode, hd⟩ hfppLive
    · rfl
  | markEnd => exact absurd hmode hmark
  | choose => exact go _ hselect ⟨hmode, hchooseBack⟩
  | rewind => exact go _ hreset ⟨hmode, hrewind hmode⟩
  | replayStart => exact go _ hreplay hmode

/-- **The final theorem from the six residual parts and the freeze.** -/
theorem given_parts_and_frozen (rest : RestCommands)
    (hscan : TicksWhere rest ScanRest) (hfpp : TicksWhere rest FppDone)
    (hselect : TicksWhere rest ChooseSelect) (hreset : TicksWhere rest RewindReset)
    (hinit : TicksWhere rest InitMode) (hreplay : TicksWhere rest ReplayStartMode)
    (PhysFrozen : List (Fin 2) → PalPeg.PhysicalDpCleanup.Config → Prop)
    (hfrozenEnter : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC 0 1 0 w st Tc → CanonTrace 0 w st Tc →
      ∀ m p, PalPeg.LocalShadowConcrete.OnRun (localGood (spare := 0)) (postPhase 0 1 0) w
          (heldAfter (Tc w.length) st) m →
        frozenAt w m → PalPeg.PhysicalDpCleanup.Enc w (absSC m) p → PhysFrozen w p)
    (hfrozenKeep : ∀ (w : List (Fin 2)) p, PhysFrozen w p →
      PhysFrozen w ((PalPeg.PhysicalDpCleanup.machine rest).apply blankM p none))
    (hfrozenQuiet : ∀ (w : List (Fin 2)) p, PhysFrozen w p →
      PalPeg.PhysicalReportTest.repW p.1
        (fun j => PalPeg.Local.readWin blankM macroRadius (p.2 j)) = false) :
    PegSeparation.RecognizedByTotalPEG PalPeg.PAL :=
  PalPeg.PhysicalFinalResidual.given_unhandledTicks_and_frozen rest
    (unhandled_of_parts rest hscan hfpp hselect hreset hinit hreplay)
    PhysFrozen hfrozenEnter hfrozenKeep hfrozenQuiet

/-- info: 'PalPeg.PhysicalResidualParts.given_parts_and_frozen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms given_parts_and_frozen

end PalPeg.PhysicalResidualParts
