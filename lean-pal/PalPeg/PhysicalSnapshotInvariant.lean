import PalPeg.PhysicalSearchSnapshots
import PalPeg.PhysicalShiftDispatch

/-! # The canonical encoding with restart snapshots

The boot tag and finite role register are unchanged. A storage representative
carries the old physical invariant; watch and broken chains additionally carry
the two independent copies established by the actual snapshot rows.
-/
set_option autoImplicit false
namespace PalPeg.PhysicalSnapshotInvariant
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract
open PalPeg.PhysicalRestartStorage
open PalPeg.PhysicalSearchSnapshots (saved)
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilScaffoldCounter (Counter)
open PalPeg.PhysicalShiftDispatch (RoutedState)
open PalPeg.GalilArriveChain (arriveState' arriveVM' arriveChain arriveW)

abbrev OldEnc := PalPeg.PhysicalShiftDispatch.Enc

/-- Watching and broken states retain the prepared spare and both extra copies.
The input indices h/age are proof witnesses, never fields of finite control. -/
def Copies (w : List (Fin 2)) (x : State GalilVM) (p : RoutedState) : Prop :=
  ∀ wm : PalPeg.GalilScaffoldChainWatch.State,
    x.vm.chain = .watch wm ∨ x.vm.chain = .broken wm →
    ∃ h age spare, PalPeg.ChainBoundaryCache.Inv h age wm.machine.control spare ∧
      OldEnc w (saved x wm.machine.control.boundary wm.machine.control.last spare) p

def Enc (w : List (Fin 2)) (x : State GalilVM) (p : RoutedState) : Prop :=
  (∃ y, StateRelated x y ∧ OldEnc w y p) ∧ Copies w x p

theorem chain_related {x y : State GalilVM} (hr : StateRelated x y) : y.vm.chain = x.vm.chain := by
  have hh := hr.2.1
  unfold Same at hh
  simpa only [replace] using congrArg GalilVM.chain hh

theorem saved_related {x y : State GalilVM} (hr : StateRelated x y)
    (boundary last spare : Counter) : saved y boundary last spare = saved x boundary last spare := by
  rcases x with ⟨cx, sx⟩
  rcases y with ⟨cy, sy⟩
  obtain ⟨hc, hs, _⟩ := hr
  change sy = replace sx sy.lower sy.search.span sy.search.work sy.search.debt at hs
  change cx = cy at hc
  cases hc
  rw [hs]
  rfl

theorem related_saved (x : State GalilVM) (boundary last spare : Counter) (hd : Dormant x.vm) :
    StateRelated x (saved x boundary last spare) := ⟨rfl, related_replace x.vm _ _ _ _ hd⟩

theorem dormant_of_chain {x : State GalilVM} {wm : PalPeg.GalilScaffoldChainWatch.State}
    (hc : x.vm.chain = .watch wm ∨ x.vm.chain = .broken wm) : Dormant x.vm := by
  left
  rcases hc with hc | hc <;> simp [hc]

theorem watching_unique {x : State GalilVM} {wm next : PalPeg.GalilScaffoldChainWatch.State}
    (hc : x.vm.chain = .watch wm ∨ x.vm.chain = .broken wm)
    (hn : x.vm.chain = .watch next ∨ x.vm.chain = .broken next) : next = wm := by
  rcases hc with hc | hc <;> rcases hn with hn | hn <;> rw [hc] at hn <;>
    first | cases hn; rfl | cases hn

/-- A concrete saved result supplies the entire canonical encoding. -/
theorem of_watching (w : List (Fin 2)) (x : State GalilVM) (p : RoutedState)
    (wm : PalPeg.GalilScaffoldChainWatch.State)
    (hc : x.vm.chain = .watch wm ∨ x.vm.chain = .broken wm)
    (h age : ℕ) (spare : Counter) (hi : PalPeg.ChainBoundaryCache.Inv h age wm.machine.control spare)
    (he : OldEnc w (saved x wm.machine.control.boundary wm.machine.control.last spare) p) :
    Enc w x p := by
  refine ⟨⟨_, related_saved x _ _ _ (dormant_of_chain hc), he⟩, ?_⟩
  intro next hn
  have hn' := watching_unique hc hn
  subst next
  exact ⟨h, age, spare, hi, he⟩

theorem enc_initial (w : List (Fin 2)) :
    Enc w initialState (PalPeg.PhysicalRoles.initialControl, fun _ => PalPeg.Program.STape.blankTape blankM) := by
  refine ⟨⟨initialState, stateRelated_refl _, PalPeg.PhysicalBoundaryCount.enc_initial w⟩, ?_⟩
  intro wm hc
  rcases hc with hc | hc <;> cases hc

/-- The relation remains canonical when no physical operation changes it. -/
theorem preserve (w : List (Fin 2)) (x : State GalilVM) (p p' : RoutedState) (he : Enc w x p)
    (hstep : ∀ y, StateRelated x y → OldEnc w y p → OldEnc w y p') : Enc w x p' := by
  obtain ⟨⟨y, hr, hy⟩, hc⟩ := he
  refine ⟨⟨y, hr, hstep y hr hy⟩, ?_⟩
  intro wm hw
  obtain ⟨h, age, spare, hi, hh⟩ := hc wm hw
  exact ⟨h, age, spare, hi, hstep _ (related_saved x _ _ _ (dormant_of_chain hw)) hh⟩

/-- Arrival changes verifier queues but no snapshot value or traversal index. -/
theorem feed (w : List (Fin 2)) (x : State GalilVM) (p p' : RoutedState) (a : Fin 2)
    (he : Enc w x p)
    (hstep : ∀ y, OldEnc w y p → OldEnc w (arriveState' a y) p') :
    Enc w (arriveState' a x) p' := by
  obtain ⟨⟨y, hr, hy⟩, hc⟩ := he
  refine ⟨⟨arriveState' a y, related_arrive a hr, hstep y hy⟩, ?_⟩
  intro wm hw
  cases hchain : x.vm.chain with
  | idle | copy | back =>
    rcases hw with hw | hw <;> simp [arriveState', arriveVM', arriveChain, hchain] at hw
  | watch old =>
    have heq : wm = arriveW a old := by
      rcases hw with hw | hw
      · simpa [arriveState', arriveVM', arriveChain, hchain] using hw.symm
      · simp [arriveState', arriveVM', arriveChain, hchain] at hw
    subst wm
    obtain ⟨h, age, spare, hi, hh⟩ := hc old (Or.inl hchain)
    exact ⟨h, age, spare, hi, hstep _ hh⟩
  | broken old =>
    have heq : wm = arriveW a old := by
      rcases hw with hw | hw
      · simp [arriveState', arriveVM', arriveChain, hchain] at hw
      · simpa [arriveState', arriveVM', arriveChain, hchain] using hw.symm
    subst wm
    obtain ⟨h, age, spare, hi, hh⟩ := hc old (Or.inr hchain)
    exact ⟨h, age, spare, hi, hstep _ hh⟩

/-- info: 'PalPeg.PhysicalSnapshotInvariant.feed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms feed

end PalPeg.PhysicalSnapshotInvariant
