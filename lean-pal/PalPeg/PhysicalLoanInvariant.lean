import PalPeg.PhysicalDebtFeed

/-! # The shared encoding with a rebuilding radius mirror during active search -/
set_option autoImplicit false
namespace PalPeg.PhysicalLoanInvariant
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract
open PalPeg.PhysicalDebtMirror (Rebuilding)
open PalPeg.PhysicalFeed (feedState)
open PalPeg.PhysicalBootFeed (feedStep)
open PalPeg.PhysicalShiftDispatch (RoutedState RoutedCore liftConfig)
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilScaffoldCounter (value)
open PalPeg.LocalRoleRouting (decode hold)

/-- Only the active, idle-chain search uses the borrowed radius carrier. -/
def NeedsLoan (x : State GalilVM) : Prop :=
  x.ctl.mode = .scan ∧ x.vm.chain = .idle ∧ searchActive x.vm.search.mode = true

/-- The credit counter is nonnegative throughout a borrowed search phase. -/
def Balanced (x : State GalilVM) : Prop :=
  0 ≤ value x.vm.radius ∧ 0 ≤ value x.vm.radius + value x.vm.search.debt

def Partial (w : List (Fin 2)) (x : State GalilVM) (p : RoutedState) : Prop :=
  Balanced x ∧ match p.1.2 with
    | .inl _ => False
    | .inr q => Rebuilding w x (q, fun j => p.2 (p.1.1 j))

noncomputable def Enc (w : List (Fin 2)) (x : State GalilVM) (p : RoutedState) : Prop := by
  classical
  exact if NeedsLoan x then Partial w x p else PalPeg.PhysicalSnapshotInvariant.Enc w x p

theorem enc_partial (w : List (Fin 2)) (x : State GalilVM) (p : RoutedState) (h : NeedsLoan x) :
    Enc w x p ↔ Partial w x p := by simp [Enc, h]

theorem enc_full (w : List (Fin 2)) (x : State GalilVM) (p : RoutedState) (h : ¬ NeedsLoan x) :
    Enc w x p ↔ PalPeg.PhysicalSnapshotInvariant.Enc w x p := by simp [Enc, h]

theorem needs_feed (input : Option (Fin 2)) (x : State GalilVM) :
    NeedsLoan (feedState input x) ↔ NeedsLoan x := by
  cases input with
  | none => rfl
  | some a =>
    cases hchain : x.vm.chain <;>
      simp [NeedsLoan, feedState, PalPeg.GalilArriveChain.arriveState',
        PalPeg.GalilArriveChain.arriveVM', PalPeg.GalilArriveChain.arriveChain,
        PalPeg.GalilArriveChain.arriveW, PalPeg.LocalTracking.arriveVM, hchain]

theorem balanced_feed (input : Option (Fin 2)) (x : State GalilVM) :
    Balanced (feedState input x) ↔ Balanced x := by cases input <;> rfl

theorem initial_not_loan : ¬ NeedsLoan initialState := by
  intro h
  cases h.1

theorem enc_initial (w : List (Fin 2)) :
    Enc w initialState (PalPeg.PhysicalRoles.initialControl, fun _ => PalPeg.Program.STape.blankTape blankM) :=
  (enc_full _ _ _ initial_not_loan).mpr (PalPeg.PhysicalSnapshotInvariant.enc_initial w)

/-- The old snapshot encoding is also preserved by the explicit routed feed row. -/
theorem snapshot_feed (w : List (Fin 2)) (x : State GalilVM) (p : RoutedCore)
    (input : Option (Fin 2))
    (he : PalPeg.PhysicalSnapshotInvariant.Enc w x (liftConfig p)) :
    PalPeg.PhysicalSnapshotInvariant.Enc w (feedState input x)
      (liftConfig ((hold feedStep).apply blankM p input)) := by
  have hstep (y : State GalilVM) (hy : PalPeg.PhysicalSnapshotInvariant.OldEnc w y (liftConfig p)) :
      PalPeg.PhysicalSnapshotInvariant.OldEnc w (feedState input y)
        (liftConfig ((hold feedStep).apply blankM p input)) := by
    change PalPeg.PhysicalCacheInvariant.Running w _ (decode _)
    rw [PalPeg.LocalRoleRouting.decode_hold]
    exact PalPeg.PhysicalCacheInvariant.running_feed w y (decode p) input hy
  cases input with
  | none => exact PalPeg.PhysicalSnapshotInvariant.preserve w x _ _ he (fun y _ hy => hstep y hy)
  | some a => exact PalPeg.PhysicalSnapshotInvariant.feed w x _ _ a he hstep

/-- Arrival and the starvation feed share this proof, including the finite role
register. The live partial mirror and its balance are preserved. -/
theorem running_feed (w : List (Fin 2)) (x : State GalilVM) (p : RoutedCore)
    (input : Option (Fin 2)) (he : Enc w x (liftConfig p)) :
    Enc w (feedState input x) (liftConfig ((hold feedStep).apply blankM p input)) := by
  by_cases hn : NeedsLoan x
  · obtain ⟨hb, hp⟩ := (enc_partial w x _ hn).mp he
    apply (enc_partial w _ _ ((needs_feed input x).mpr hn)).mpr
    refine ⟨(balanced_feed input x).mpr hb, ?_⟩
    change Rebuilding w _ (decode _)
    rw [PalPeg.LocalRoleRouting.decode_hold]
    exact PalPeg.PhysicalDebtFeed.running_feed w x (decode p) input hp
  · apply (enc_full w _ _ (fun h => hn ((needs_feed input x).mp h))).mpr
    exact snapshot_feed w x p input ((enc_full w x _ hn).mp he)

theorem starved_running (w : List (Fin 2)) (x : State GalilVM) (p : RoutedCore)
    (he : Enc w x (liftConfig p)) :
    PalPeg.PhysicalTickDispatch.starvedRead (decode p).1
      (fun j => PalPeg.Local.readWin blankM macroRadius ((decode p).2 j)) =
      PalPeg.FrameFunction.starvedTest x := by
  by_cases hn : NeedsLoan x
  · exact PalPeg.PhysicalDebtFeed.starved_running w x (decode p) ((enc_partial w x _ hn).mp he).2
  · obtain ⟨y, hr, hy⟩ := ((enc_full w x _ hn).mp he).1
    exact (PalPeg.PhysicalTickDispatch.starvedRead_running
      (PalPeg.PhysicalCacheInvariant.running_core hy)).trans (PalPeg.PhysicalRestartStorage.related_starved hr)

/-- info: 'PalPeg.PhysicalLoanInvariant.enc_initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms enc_initial

end PalPeg.PhysicalLoanInvariant
