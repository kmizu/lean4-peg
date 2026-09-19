import PalPeg.StageWaitPhase

/-!
# The `.run` phase frame, step-locally

`DpBudgetState.DpBudgetAt` carries the DP's *budget* through the `.run` phase;
this file carries its *frame* — the stage window, the lower bound and the
canonicity of the debt — so that the `.wait` leg can be entered with the data
`StageWaitPhase.WaitPhase` asks for.

* `RunPhase k mw v` — the frame during the leg.
* `runPhase_step` — a tick that stays in `.run` keeps it
  (`CloseoutPreload13.runTrace_frame` at a one-tick trace; `stageSpan` is the
  span in both `.run` and `.wait`, which is what makes the window survive the
  exit).
* `waitPhase_of_runExit` — a tick that lands in `.wait` gives `WaitPhase k mw`.
  This is `CloseoutPreload13.run_exit_frame` read at the empty trace.

**The open exit.**  `GalilScaffoldSearchRun.ExitMode` also allows a `.run` tick
to land directly in `.double` (`run_exit_frame` supplies `work = ofNat mw`,
`span = reset`, `quarter = 0` there).  `StageDoubleLeg.DoubleLeg` additionally
asks for `value debt = 0`, which the `.wait` leg is what establishes
(`CloseoutPreload24.wait_exit_debt_zero`), so a direct `.run` → `.double` exit
is not covered by the phase chain as it stands.  Whether the machine can take
that exit at all is not settled here; the assembly has to either rule it out or
carry the debt separately.

**Not done here.**  All four phases now have step-local frames, but they are not
yet one predicate, and `CloseoutReadyStage.ReadyIface P Φ` has no instance, so
no hypothesis is removed.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace PalPeg.StageRunPhase

open PalPeg PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop
open PalPeg.GalilScaffoldSearchFinish (Mode)
open PalPeg.GalilScaffoldCounter (Canonical value ofNat)
open PalPeg.GalilScaffoldSearchRun (stageSpan)
open PalPeg.CloseoutPreload13 (RunTrace runTrace_frame runTrace_lower run_exit_frame)
open PalPeg.CloseoutPreload32 (canonical_run_step)
open PalPeg.StageWaitPhase (WaitPhase)

/-- **The frame carried through the `.run` leg.** -/
def RunPhase (k mw : ℕ) (v : SearchVM) : Prop :=
  v.search.mode = Mode.run ∧ v.search.span = ofNat mw ∧ v.lower = ofNat k ∧
    Canonical v.search.debt

/-- **A tick that stays in `.run` keeps the frame.** -/
theorem runPhase_step {k mw : ℕ} {c : GalilScaffoldPlace.Place} {a : Bool} {v v' : SearchVM}
    (h : RunPhase k mw v) (hs : searchStep c a v v')
    (hstay : v'.search.mode = Mode.run) : RunPhase k mw v' := by
  obtain ⟨hm, hsp, hlow, hcan⟩ := h
  have hr : RunTrace [a] v v' := .cons c a [] v v' v' hm hs (.nil v')
  obtain ⟨-, hfr⟩ := runTrace_frame hr
  obtain ⟨hl, -⟩ := runTrace_lower hr
  refine ⟨hstay, ?_, hl.trans hlow, canonical_run_step hm hs hcan⟩
  have h1 : stageSpan v'.search = v'.search.span := by simp [stageSpan, hstay]
  have h2 : stageSpan v.search = v.search.span := by simp [stageSpan, hm]
  rw [← h1, hfr, h2, hsp]

/-- **A tick that leaves `.run` for `.wait` hands over the `.wait` frame.** -/
theorem waitPhase_of_runExit {k mw : ℕ} {c : GalilScaffoldPlace.Place} {a : Bool}
    {v v' : SearchVM} (h : RunPhase k mw v) (hs : searchStep c a v v')
    (hwait : v'.search.mode = Mode.wait) : WaitPhase k mw v' := by
  obtain ⟨hm, hsp, hlow, hcan⟩ := h
  have hne : v'.search.mode ≠ Mode.run := by rw [hwait]; decide
  obtain ⟨hl, -, -, -, -, hspw, -⟩ := run_exit_frame hm hsp hlow (.nil v) hm hs hne
  exact ⟨hwait, hspw hwait, hl, canonical_run_step hm hs hcan⟩

#print axioms runPhase_step
#print axioms waitPhase_of_runExit

end PalPeg.StageRunPhase
