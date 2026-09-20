import PalPeg.LocalSysConcrete
import PalPeg.GalilFinalAssembly

/-!
# The blank local state

The local state every run starts in: five empty cursors (with the gap bit of `initialHead`),
nothing pending, every counter at zero on its own tape, both programs halted, the chain idle.
Its abstraction is the boot state of any word with all of its letters truncated away, so it does
not depend on the word.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace PalPeg.LocalBlankState

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
open PalPeg.GalilScaffoldChainInputSupply
open PalPeg.LocalState (GalilVML Ctr)
open PalPeg.LocalInputView (InputView emptyView WF_emptyView)
open PalPeg.LocalReplayParked (absState'')
open PalPeg.LocalSysConcrete (x0C)
open PalPeg.GalilThrottledRun (truncS)
open PalPeg.GalilFinalAssembly (boot)
open PalPeg.Program (STape)

/-- The empty cursor, with the gap bit the initial head carries. -/
def blankView : InputView := { emptyView with gap := true }

/-- The counter tape holding zero: an empty mark-run above a separator. -/
def zeroTape : STape LocalCounter.Seg := ⟨[LocalCounter.sep], LocalCounter.sep, []⟩

/-- The number of physical counter tapes: one per logical counter, and `spare` tapes without a
role.  The commits of the local layer (`LocalTick2.RestartStaged` and its relatives) stage the
next value of a counter on a tape without a role and swap roles, so the bank needs spares; how
many is decided by the local steps, not here. -/
abbrev tapeCount (spare : ℕ) : ℕ := Fintype.card Ctr + spare

/-- **The blank local state.** -/
noncomputable def blankVML (spare : ℕ) : GalilVML (tapeCount spare) where
  left := blankView
  center := blankView
  right := blankView
  pending := []
  walkerView := emptyView
  fppWalker := emptyView
  phys := fun _ => zeroTape
  roles := fun counter => Fin.castAdd spare (Fintype.equivFin Ctr counter)
  pol := fun _ => true
  radiusMir := ⟨zeroTape, fun _ => zeroTape⟩
  lowerMir := ⟨zeroTape, fun _ => zeroTape⟩
  lengthMir := ⟨zeroTape, fun _ => zeroTape⟩
  dpBuf := ⟨fun _ => GalilScaffoldTape.reset, fun _ => GalilScaffoldTape.reset, true, none⟩
  dpPc := 0
  dpDone := true
  fppBuf := ⟨fun _ => GalilScaffoldTape.reset, fun _ => GalilScaffoldTape.reset, true, none⟩
  fppPc := 0
  fppDone := true
  chain := .idle
  ctl := GalilScaffoldController.initial 2048
  searchMode := .idle
  searchFinalStage := false
  searchQuarter := 0
  fppMode := .run
  fppFinalStage := false
  periodOnly := false

/-- Truncating every letter of a word away from its boot VM leaves the boot VM of the empty
word. -/
theorem truncVM_initVM0 (w : List (Fin 2)) :
    GalilThrottledRun.truncVM w.length (GalilBootVM.initVM0 w) = GalilBootVM.initVM0 [] := by
  have hdrop : GalilThrottledRun.dropN w.length w = [] := by
    simp [GalilThrottledRun.dropN]
  unfold GalilThrottledRun.truncVM GalilBootVM.initVM0
  simp only [GalilThrottledRun.truncPH, initialHead, hdrop, GalilThrottledRun.truncChain]

/-- The abstraction of the blank state is the boot VM of the empty word. -/
theorem abs''_blank (spare : ℕ) :
    LocalReplayParked.abs'' (x0C (blankVML spare) 2048).core.vm = GalilBootVM.initVM0 [] := by
  rfl

/-- **The abstraction of the blank state is the truncated boot state of every word.** -/
theorem absState''_blank (spare : ℕ) (w : List (Fin 2)) :
    absState'' (x0C (blankVML spare) 2048).core.vm = truncS w.length (boot w) := by
  show (⟨_, _⟩ : State GalilVM) = ⟨_, _⟩
  congr 1
  show LocalReplayParked.abs'' _ = GalilThrottledRun.truncVM w.length (GalilBootVM.initVM0 w)
  rw [truncVM_initVM0, abs''_blank spare]

#print axioms absState''_blank

theorem segCtr_zeroTape : LocalCounter.SegCtr zeroTape 0 := ⟨[], rfl⟩

theorem wf_blankView : PalPeg.LocalInputView.WF blankView := WF_emptyView

/-- **The blank state satisfies the invariant of the local layer.** -/
theorem inv_blank (spare : ℕ) : PalPeg.LocalTick1.Inv (blankVML spare) where
  roles := fun _ _ h => (Fintype.equivFin Ctr).injective (Fin.castAdd_injective _ _ h)
  attached := ⟨rfl, rfl, rfl⟩
  views := ⟨wf_blankView, wf_blankView, wf_blankView, WF_emptyView, WF_emptyView⟩
  radiusShaped := ⟨0, segCtr_zeroTape, fun _ => segCtr_zeroTape⟩
  lowerShaped := ⟨0, segCtr_zeroTape, fun _ => segCtr_zeroTape⟩
  lengthShaped := ⟨0, segCtr_zeroTape, fun _ => segCtr_zeroTape⟩
  shaped := fun _ => ⟨0, segCtr_zeroTape⟩

theorem twin_blank (spare : ℕ) :
    PalPeg.LocalReplaySwap.Twin (blankVML spare).left (blankVML spare).center :=
  PalPeg.LocalReplaySwap.Twin.refl _

#print axioms inv_blank

end PalPeg.LocalBlankState
