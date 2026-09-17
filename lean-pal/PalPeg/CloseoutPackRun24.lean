import PalPeg.CloseoutPackRun21

/-!
# `CloseoutPackRun24`: `rShiftNext` modulo one non-idle-chain fact

The last `BigResid6` contract (`CloseoutPackRun11.BigResid6.rShiftNext`) asks
for `ShiftLocal` at the target `y` of a tick out of a `BigPack2M` state.  When
`y.vm.chain = .idle` this is `CloseoutPackRun6.shiftLocal_of_chainIdle`.  When
the chain is *not* idle the five fields of `ShiftLocal` speak about the
watching chain of the comparison target `s''`, and nothing in `BigPack2M`
(`Coupled.watch` is `WatchOK`, a *round* bound, not the guard's `4h ≤ distance`
nor `distance ≤ 2·rad`) carries them.  That fact is isolated as `WatchShift`
(§1), the theorem `rShiftNext_of_pack` (§2) is the contract modulo it.

**Caveat found while reading the definitions.**  `compareFound` has no mode
guard and `beginShiftVM'` only needs `s''.chain = .watch _`; so at a `shift`
mode state (whose chain *is* a watch, by `beginShiftVM`) the field
`ShiftLocal.mode` demands `y.ctl.mode = Mode.scan`, which is false whenever a
`GalilScaffoldChainWatch.Internal` step is enabled there.  `WatchShift` is
therefore stated with the premise `s.chain ≠ .idle`, and the field carrying it
must live *under* `c.mode = Mode.scan ∧ c.replaying = false` — or `ShiftLocal`
must be re-cut with that guard — before it can be a pack invariant.
-/

namespace PalPeg.CloseoutPackRun24

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton PalPeg.GalilFrontMono PalPeg.GalilChainCoupling
open PalPeg.CloseoutLPack PalPeg.CloseoutLPack3 PalPeg.CloseoutLPack4
open PalPeg.CloseoutLPack5 PalPeg.CloseoutPackRun6
open PalPeg.CloseoutPackRun10 PalPeg.CloseoutPackRun11

section
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-! ## 1. The one missing fact -/

/-- **(NAMED) the shift-entry data of a non-idle chain.**  Exactly the payload of
`ShiftLocal`'s five fields at a comparison target `s''` whose chain watches
`wch`, together with `canRight` of the right head — stated only when the
source chain is not idle (the idle case is a theorem, §2). -/
def WatchShift (w : List (Fin 2)) (x : State GalilVM) : Prop :=
  x.vm.chain ≠ ChainVM.idle →
  ∀ s'' : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).compare x.vm s'' →
    ∀ wch : GalilScaffoldChainWatch.State, s''.chain = .watch wch →
      (x.ctl.mode = Mode.scan ∧ x.ctl.replaying = false) ∧
      GalilScaffoldChainVerifier.canRight x.vm.right ∧
      4 * (periodLength wch : ℤ) ≤ value wch.machine.control.distance ∧
      (∀ rad : ℕ, ScanInvariant w (position x.vm.center) rad x.vm.left x.vm.right →
        value wch.machine.control.distance ≤ 2 * (rad : ℤ)) ∧
      GalilScaffoldChainVerifier.canRight wch.machine.verifier ∧
        GalilFrontMono.Sane wch.machine.verifier

/-- `ShiftLocal` from `WatchShift` at a non-idle chain. -/
theorem shiftLocal_of_watchShift {w : List (Fin 2)} {x : State GalilVM}
    (hni : x.vm.chain ≠ ChainVM.idle) (hw : WatchShift centre place entry q first w x) :
    ShiftLocal centre place entry q first w x := by
  have key : ∀ s'' t'' : GalilVM,
      (galilFrameS (PofC centre place entry w) q first).compare x.vm s'' →
      beginShiftVM' s'' t'' →
      ∃ wch : GalilScaffoldChainWatch.State, s''.chain = .watch wch := by
    intro s'' t'' _ hb
    obtain ⟨wch, hwch, -⟩ := hb
    exact ⟨wch, hwch⟩
  exact
    { mode := fun s'' t'' h1 h2 => by
        obtain ⟨wch, hwch⟩ := key s'' t'' h1 h2
        exact (hw hni s'' h1 wch hwch).1
      move := fun s'' t'' h1 h2 => by
        obtain ⟨wch, hwch⟩ := key s'' t'' h1 h2
        exact (hw hni s'' h1 wch hwch).2.1
      guard := fun s'' _ h1 _ wch hwch => (hw hni s'' h1 wch hwch).2.2.1
      coupled := fun s'' _ h1 _ wch hwch => (hw hni s'' h1 wch hwch).2.2.2.1
      ver := fun s'' _ h1 _ wch hwch => (hw hni s'' h1 wch hwch).2.2.2.2 }

/-! ## 2. The contract modulo `WatchShift` -/

/-- **`BigResid6.rShiftNext` modulo `WatchShift` at the target.**  The idle
chain case is `shiftLocal_of_chainIdle`; the pack at `x`, the tick and
`SoundScanNR` are not consumed — nothing in them reaches the watching chain of
the comparison target. -/
theorem rShiftNext_of_pack {w : List (Fin 2)}
    (hws : ∀ y : State GalilVM, WatchShift centre place entry q first w y)
    (x y : State GalilVM) (_hx : BigPack2M centre place entry q first w x)
    (_h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y)
    (_hg : SoundScanNR w y) :
    ShiftLocal centre place entry q first w y := by
  by_cases hi : y.vm.chain = ChainVM.idle
  · exact shiftLocal_of_chainIdle centre place entry q first hi
  · exact shiftLocal_of_watchShift centre place entry q first hi (hws y)

end

#print axioms shiftLocal_of_watchShift
#print axioms rShiftNext_of_pack

end PalPeg.CloseoutPackRun24
