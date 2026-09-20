import PalPeg.CloseoutCoreAgree
import PalPeg.GalilLexMeasure

/-!
# Closeout: `RightInBounds` from the trace's right-head bound

`CloseoutCoreAgree.agree_shift` — and with it the seventh `AgreeOn` obligation
of `CloseoutCoreStep.realizes_seven_of_agree` — is stated modulo the NAMED
residual

```
RightInBounds P Good raw stOf :=
  ∀ m, InvC Good raw stOf m → m.vm.ctl.mode = .shift → ¬ RemPosL m.vm →
    (abs' m.vm).right.head.left.length ≤ raw.length
```

This file discharges it from two facts that are *about the abstract trace and
its control flow*, not about the local machine:

* `PhaseNoReplay` (`LocalRealizesPhase`) — a phase mode never replays.  This is
  already the shared hypothesis of all five phase obligations, so it costs
  nothing new.
* `TraceRightLe` — the trace's R head never stands past the end of the input,
  `position (stOf k).vm.right ≤ 2 * raw.length`.  For a trace carrying the
  scan/lex invariant this is `GalilLexMeasure.invL_right_le`, packaged here as
  `traceRightLe_of_invL`.

The chain is purely computational: `InvC`'s tracking datum pins
`absState'' m.vm` to `truncS (raw.length - j) (stOf k)`; `truncPH` rewrites only
`incoming`, so the *left stack* of the R head is the trace's verbatim
(`truncPH_head_left`); with `replaying = false` the parked abstraction `absR`
collapses onto `abs'`'s R head (`absR_of_not_replaying`); and `position`, being
`2·|left|` or `2·|left| - 1`, turns the `2 * raw.length` bound into
`|left| ≤ raw.length` (`left_length_le_of_position`).

No new dynamics, no `LocalStep`, no `Tick` is built here, so

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace PalPeg.CloseoutRightBounds

open PalPeg PalPeg.Program
open PalPeg.GalilScaffoldTop
open PalPeg.GalilScaffoldChainInputSupply (position GalilVM)
open PalPeg.LocalState (GalilVML)
open PalPeg.LocalArrival (abs')
open PalPeg.LocalReplayParked (Mirrored1 absR physHead absR_of_not_replaying absState'')
open PalPeg.LocalSysConcrete (InvC Needy Tracked)
open PalPeg.GalilThrottledRun (truncPH truncVM truncS)
open PalPeg.LocalRealizesPhase (PhaseNoReplay RemPosL)
open PalPeg.CloseoutCoreAgree (RightInBounds)

variable {P : ℕ}

variable {Good : Mirrored1 P → Prop}

/-! ## 1. `position` bounds the left stack -/

/-- `position p = 2·|left|` or `2·|left| - 1`, so a `2 n` bound on the position is
an `n` bound on the left stack. -/
theorem left_length_le_of_position {n : ℕ} {p : GalilScaffoldInputHead.PlaceHead}
    (h : position p ≤ 2 * n) : p.head.left.length ≤ n := by
  unfold position at h
  cases hg : p.gap with
  | true => rw [hg, if_pos rfl] at h; omega
  | false =>
    rw [hg] at h
    simp only [Bool.false_eq_true, if_false] at h
    omega

/-! ## 2. Truncation does not touch the left stack -/

/-- `truncPH` rewrites only `incoming`. -/
theorem truncPH_head_left (d : ℕ) (p : GalilScaffoldInputHead.PlaceHead) :
    (truncPH d p).head.left = p.head.left := rfl

theorem truncS_right_head_left (d : ℕ) (st : State GalilVM) :
    (truncS d st).vm.right.head.left = st.vm.right.head.left := rfl

/-! ## 3. The trace-side hypothesis -/

/-- **The trace's R head stays inside the input.** -/
def TraceRightLe (raw : List (Fin 2)) (stOf : ℕ → State GalilVM) : Prop :=
  ∀ k, position (stOf k).vm.right ≤ 2 * raw.length

/-- For a trace carrying the scan/lex invariant, `TraceRightLe` is
`GalilLexMeasure.invL_right_le`. -/
theorem traceRightLe_of_invL {raw : List (Fin 2)} {stOf : ℕ → State GalilVM}
    (h : ∀ k, ∃ c, PalPeg.GalilOracleLocal.InvL raw c (stOf k).vm) :
    TraceRightLe raw stOf := by
  intro k
  obtain ⟨c, hc⟩ := h k
  exact PalPeg.GalilLexMeasure.invL_right_le hc

/-! ## 4. The residual -/

/-- The R head of `abs'` is the trace's R head, verbatim, on a non-replaying
tracked state. -/
theorem abs'_right_head_left {raw : List (Fin 2)} {stOf : ℕ → State GalilVM}
    {x : GalilVML P} (hnr : x.ctl.replaying = false) {k j : ℕ}
    (hn : Needy raw stOf k j x) :
    (abs' x).right.head.left = (stOf k).vm.right.head.left := by
  have h : absR x = (truncVM (raw.length - j) (stOf k).vm).right :=
    congrArg (fun s => s.vm.right) hn.2
  have h2 : (abs' x).right = absR x := (absR_of_not_replaying hnr).symm
  rw [h2, h]
  rfl

/-- **`RightInBounds` is discharged.** -/
theorem rightInBounds {raw : List (Fin 2)} {stOf : ℕ → State GalilVM}
    (H_nr : PhaseNoReplay (P := P) Good raw stOf) (H_pos : TraceRightLe raw stOf) :
    RightInBounds P Good raw stOf := by
  intro m hinv hmd _
  obtain ⟨k, j, hn⟩ := hinv.track
  have hnr : m.vm.ctl.replaying = false := H_nr m hinv (Or.inl hmd)
  rw [abs'_right_head_left hnr hn]
  exact left_length_le_of_position (H_pos k)

end PalPeg.CloseoutRightBounds

#print axioms PalPeg.CloseoutRightBounds.left_length_le_of_position
#print axioms PalPeg.CloseoutRightBounds.traceRightLe_of_invL
#print axioms PalPeg.CloseoutRightBounds.abs'_right_head_left
#print axioms PalPeg.CloseoutRightBounds.rightInBounds
