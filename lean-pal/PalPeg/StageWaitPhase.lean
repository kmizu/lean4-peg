import PalPeg.StageDoubleLeg

/-!
# The `.wait` phase, step-locally

The stage cycle is `.run` → `.wait` → `.double` → preparation.  `StageDoubleLeg`
turned the `.double` leg into a step-local invariant; this file does the same for
the `.wait` leg, which is the simpler one: while the phase lasts, nothing of the
frame moves at all — the window, the lower bound and the canonicity of the debt
are carried unchanged, and only the debt itself falls, one unit per comparison.

* `WaitPhase k mw v` — the frame during the leg.
* `waitPhase_step` — a tick that stays in `.wait` keeps it.
* `doubleLeg_head_of_waitExit` — a tick that leaves `.wait` on a background
  event lands on exactly the head data `StageDoubleLeg.DoubleLeg` asks for:
  `work = ofNat mw`, `span = reset`, `quarter = 0`, zero debt, `lower = ofNat k`.

**Why the exit event is a background one.**  `CloseoutPreload34.exitNotFire_of_wait`
proves it at the machine level, and its argument is: if the `.wait` leg is empty
then the `.run` → `.wait` exit was itself a comparison
(`CloseoutPreload34.run_exit_wait_match`), which resets the clock to `2048`, so
the very next tick cannot be a comparison.  In the `ReadyIface` accounting that
is literally the `comparison` field's conclusion `Φ v n 0`: after a comparison
the slack is `0`, and a comparison needs `2048 ≤ k + 1`.  This file does not
carry that argument — the exit here takes `a = false` as a hypothesis, and
supplying it is left to the assembly.

**Not done here.**  Three of the four phases now have step-local invariants
(`StagePrepS`-style preparation, this, `StageDoubleLeg`); assembling them into a
single `Φ` with `CloseoutReadyStage.ReadyIface P Φ` is not done, so no
hypothesis is removed.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace PalPeg.StageWaitPhase

open PalPeg PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop
open PalPeg.GalilScaffoldSearchFinish (Mode)
open PalPeg.GalilScaffoldCounter (Canonical value ofNat reset zero)
open PalPeg.CloseoutPreload14 (wait_step_cases)
open PalPeg.CloseoutPreload24 (wait_exit_debt_zero)
open PalPeg.CloseoutPreload32 (canonical_wait_step)

/-- **The frame carried through the `.wait` leg.** -/
def WaitPhase (k mw : ℕ) (v : SearchVM) : Prop :=
  v.search.mode = Mode.wait ∧ v.search.span = ofNat mw ∧ v.lower = ofNat k ∧
    Canonical v.search.debt

/-- **A tick that stays in `.wait` keeps the frame.** -/
theorem waitPhase_step {k mw : ℕ} {c : GalilScaffoldPlace.Place} {a : Bool} {v v' : SearchVM}
    (h : WaitPhase k mw v) (hs : searchStep c a v v')
    (hstay : v'.search.mode = Mode.wait) : WaitPhase k mw v' := by
  obtain ⟨hm, hsp, hlow, hcan⟩ := h
  obtain ⟨hl, -, -, hc | hc⟩ := wait_step_cases hm hs
  · exact ⟨hstay, hc.2.2.1.trans hsp, hl.trans hlow, canonical_wait_step hm hs hcan⟩
  · exact absurd (hc.2.1 ▸ hstay) (by decide)

/-- **The exit hands the `.double` leg its head data.**  This is exactly the
tuple `StageDoubleLeg.DoubleLeg` opens with. -/
theorem doubleLeg_head_of_waitExit {k mw : ℕ} {c : GalilScaffoldPlace.Place} {v v' : SearchVM}
    (h : WaitPhase k mw v) (hs : searchStep c false v v')
    (hne : v'.search.mode ≠ Mode.wait) :
    v'.search.mode = Mode.double ∧ v'.search.work = ofNat mw ∧
      v'.search.span = reset ∧ v'.search.quarter = 0 ∧
      value v'.search.debt = 0 ∧ Canonical v'.search.debt ∧ v'.lower = ofNat k := by
  obtain ⟨hm, hsp, hlow, hcan⟩ := h
  obtain ⟨hl, -, -, hc | hc⟩ := wait_step_cases hm hs
  · exact absurd hc.2.1 hne
  · exact ⟨hc.2.1, hc.2.2.1.trans hsp, hc.2.2.2.1, hc.2.2.2.2,
      wait_exit_debt_zero hm hc.1 hcan hs, canonical_wait_step hm hs hcan, hl.trans hlow⟩

#print axioms waitPhase_step
#print axioms doubleLeg_head_of_waitExit

end PalPeg.StageWaitPhase
