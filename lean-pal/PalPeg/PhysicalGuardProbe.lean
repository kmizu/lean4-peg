import PalPeg.FrameFunction

/-!
# Guards at the physical-machine boundary

The raw quiet scan arm lies on the starved side of the final consumer. These
facts constrain the physical tick dispatcher that remains to be assembled.
-/
set_option autoImplicit false

namespace PalPeg.PhysicalGuardProbe
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply

theorem quiet_scan_starves (x : State GalilVM)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.scan)
    (hquiet : (!x.ctl.replaying && !canRightTest x.vm.right) = true) :
    PalPeg.FrameFunction.starvedTest x = true := by
  have hav : canRightTest x.vm.right = false := by
    cases h : canRightTest x.vm.right <;> simp_all
  simp [PalPeg.FrameFunction.starvedTest, PalPeg.FrameFunction.starvedOf, hmode, hav]

theorem frame_quiet_scan_starves (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (x : State GalilVM)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.scan)
    (hquiet : (!x.ctl.replaying &&
      !(PalPeg.FrameFunction.galilFrameFun centre place entry q first w).available x.vm) = true) :
    PalPeg.FrameFunction.starvedTest x = true :=
  quiet_scan_starves x hmode hquiet

theorem nonstarved_scan_not_quiet (x : State GalilVM)
    (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.scan)
    (hstarved : PalPeg.FrameFunction.starvedTest x = false) :
    (!x.ctl.replaying && !canRightTest x.vm.right) = false := by
  cases h : (!x.ctl.replaying && !canRightTest x.vm.right) with
  | false => rfl
  | true => have := quiet_scan_starves x hmode h; simp_all

/-- The nonstarved count arm, including its clock decrement. Its VM effect is
the same background function used by the existing quiet-arm components. -/
theorem tickFun_nonstarved_count (centre : GalilVM → Fin 3)
    (place : GalilVM → PalPeg.GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (F : PalPeg.GalilScaffoldTop.Frame GalilVM) (delay : ℕ)
    (x : State GalilVM) (hmode : x.ctl.mode = PalPeg.GalilScaffoldController.Mode.scan)
    (hstarved : PalPeg.FrameFunction.starvedTest x = false)
    (hrestart : (PalPeg.FrameFunction.galilFrameFun centre place entry q first w).restartGuard x.vm = false)
    (hclock : 1 < x.ctl.clock) :
    tickFun (PalPeg.FrameFunction.galilFrameFun centre place entry q first w) F delay x
      = ⟨{x.ctl with clock := x.ctl.clock - 1},
          (PalPeg.FrameFunction.galilFrameFun centre place entry q first w).background x.vm⟩ := by
  have hquiet := nonstarved_scan_not_quiet x hmode hstarved
  unfold tickFun
  rw [hmode]
  dsimp only
  rw [if_neg (by rw [hrestart]; decide)]
  change (if (!x.ctl.replaying && !canRightTest x.vm.right) then _ else _) = _
  rw [if_neg (by rw [hquiet]; decide), if_pos hclock]

/-- info: 'PalPeg.PhysicalGuardProbe.quiet_scan_starves' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms quiet_scan_starves

/-- info: 'PalPeg.PhysicalGuardProbe.tickFun_nonstarved_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tickFun_nonstarved_count

end PalPeg.PhysicalGuardProbe
