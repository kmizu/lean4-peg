import PalPeg.PhysicalResidualParts
import PalPeg.PhysicalDpSource

/-!
# The fpp mode never holds a halted program

The machine enters `fpp` only through `fppStart`, which restarts the program, and stays there only
through `fppSlice`, whose run has not halted; a halting run leaves for `markEnd`. So along the
trace an `fpp` state's program is live, and the plateau after the last report is in `scan`. This
discharges the `fpp` residual (`FppDone`).
-/
set_option autoImplicit false
namespace PalPeg.PhysicalFppAlive
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton (PofC)
open PalPeg.GalilFinalAssembly2 (centreC placeC)
open PalPeg.CloseoutCheckW (PreTraceIMW CanonTrace)
open PalPeg.LocalSysConcrete (absSC)
open PalPeg.LocalBlankState (tapeCount)
open PalPeg.ShadowedLocalFinal (localGood postPhase frozenAt heldAfter)
open PalPeg.PhysicalResidualParts

/-- An `fpp` state's program has not halted. -/
def FppAlive (x : State GalilVM) : Prop := x.ctl.mode = .fpp → x.vm.fpp.program.done = false

section
variable (centre : GalilVM → Fin 3) (place : GalilVM → PalPeg.GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

theorem fppAlive_tick {raw : List (Fin 2)} {x y : State GalilVM} (hx : FppAlive x)
    (ht : Tick (galilFrameS (PofC centre place entry raw) q first) 2048 x y) : FppAlive y := by
  intro hy
  cases ht
  all_goals first | (exfalso; simp_all; done) | skip
  · rename_i s' _ _ h
    have he := h.1
    change s'.fpp.program.done = false
    rw [show s'.fpp = _ from he]
    rfl
  · rename_i h
    exact h.1.2.2.1

theorem fppAlive_boot (w : List (Fin 2)) : FppAlive (PalPeg.GalilFinalAssembly.boot w) := by
  intro h
  simp [PalPeg.GalilFinalAssembly.boot, PalPeg.GalilScaffoldController.initial] at h

/-- Along a pre-loaded trace, every `fpp` state's program is live. -/
theorem fppAlive_alongTrace {w : List (Fin 2)} {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hpre : PalPeg.GalilFinalAssembly.PreTrace centre place entry q first w st Tc) :
    ∀ i, i ≤ Tc w.length → FppAlive (st i) := by
  have h0 : FppAlive (st 0) := by rw [hpre.start]; exact fppAlive_boot w
  exact hpre.trace.carried (Pk := FppAlive) h0 fun _ _ ht hx =>
    fppAlive_tick centre place entry q first hx ht

end

/-- **The `fpp` residual is empty**: the simulated state is on the trace (whose `fpp` states are
live) or on the plateau after the last report (which is in `scan`). -/
theorem ticks_fppDone (rest : PalPeg.PhysicalScanCount.RestCommands) : TicksWhere rest FppDone := by
  intro w st Tc hpre _ m _ hon hnotFrozen _ _ _ hdone
  exfalso
  have halive : FppAlive (absSC m) := by
    rcases hon.onRun with htracked | ⟨hpost, _, _, _⟩
    · obtain ⟨k, _, _, hsource⟩ := htracked.track
      have hb := fppAlive_alongTrace centreC placeC 0 1 0 hpre.base.pre (min k (Tc w.length))
        (Nat.min_le_right _ _)
      change FppAlive (PalPeg.LocalReplayParked.absState'' m.vm)
      rw [hsource]
      exact hb
    · rcases hpost with hplateau | hfrozen
      · intro hm
        rw [hplateau.scan] at hm
        cases hm
      · exact (hnotFrozen hfrozen).elim
  obtain ⟨hmode, hhalted⟩ := hdone
  rw [halive hmode] at hhalted
  cases hhalted

/-- info: 'PalPeg.PhysicalFppAlive.ticks_fppDone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ticks_fppDone

end PalPeg.PhysicalFppAlive
