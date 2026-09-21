import PalPeg.FrameFunction
import PalPeg.LocalStepRealize
import PalPeg.CloseoutCoreEnc12
import PalPeg.LocalStepFusion

/-!
# The two branches of the physical obligation, as properties of one rule

`ShadowedLocalFinal.forwardTick_of_stepping` asks a machine for two things: to stand still where
the abstraction starves, and to step by `GalilScaffoldTop.tickFun` otherwise.  A machine built
from an `ActRule` runs its actions through a read-write sweep, which returns the tapes only up
to `TEqG`.  An encoding that speaks of its tapes only up to `TEqG` — `SweepClosed` — absorbs
that, and then both branches are properties of the rule alone: that it names no action where the
starvation test stands, and that its ideal step encodes the successor.
-/

set_option autoImplicit false
namespace PalPeg.MachineStep

open PalPeg.CloseoutCoreEnc12 (Act ActRule compStep compStep_apply TEqG)
open PalPeg.GalilScaffoldChainInputSupply (GalilVM)
open PalPeg.Local (Window readWin pos)
open PalPeg.Program (STape)
open PalPeg.GalilScaffoldTop (State)

variable {Q Γ : Type} {t K : ℕ}

/-- an encoding a sweep can keep: it only ever speaks of the tapes up to `TEqG`. -/
def SweepClosed (blank : Γ) (Enc : State GalilVM → Q × (Fin t → STape Γ) → Prop) : Prop :=
  ∀ x p p', Enc x p → p.1 = p'.1 → (∀ tape, TEqG blank (p.2 tape) (p'.2 tape)) → Enc x p'

/-- **where the abstraction starves, a machine whose rule names no action keeps its
encoding.**  This is the standing-still branch of the physical obligation, with nothing left of
it but a property of the rule. -/
theorem enc_of_starved {blank : Γ} {Enc : State GalilVM → Q × (Fin t → STape Γ) → Prop}
    (hclosed : SweepClosed blank Enc) (R : ActRule (Fin 2) Q Γ t K)
    (hmargin : ∀ x p, Enc x p → ∀ tape, K ≤ pos (p.2 tape))
    (hidle : ∀ x p, Enc x p → PalPeg.FrameFunction.starvedTest x = true →
      R.nq p.1 none (fun tape => readWin blank K (p.2 tape)) = p.1 ∧
        ∀ tape, R.acts p.1 none (fun tape => readWin blank K (p.2 tape)) tape = [])
    (x : State GalilVM) (p : Q × (Fin t → STape Γ)) (henc : Enc x p)
    (hstarved : PalPeg.FrameFunction.starvedTest x = true) :
    Enc x ((compStep R).apply blank p none) := by
  obtain ⟨hcontrol, hacts⟩ := hidle x p henc hstarved
  obtain ⟨hnext, htapes⟩ := compStep_apply R blank p none (hmargin x p henc)
  refine hclosed x p _ henc (hnext.trans hcontrol).symm (fun tape => ?_)
  have hkept := htapes tape
  rw [hacts tape] at hkept
  exact hkept

/-- **where the abstraction moves, a machine whose ideal step encodes the successor
keeps its encoding.**  The sweep only ever returns the ideal tapes up to `TEqG`, which a
`SweepClosed` encoding absorbs; so the stepping branch of the physical obligation is a property
of the rule alone. -/
theorem enc_of_stepping {blank : Γ} {Enc : State GalilVM → Q × (Fin t → STape Γ) → Prop}
    (hclosed : SweepClosed blank Enc) (R : ActRule (Fin 2) Q Γ t K)
    (hmargin : ∀ x p, Enc x p → ∀ tape, K ≤ pos (p.2 tape))
    {successor : State GalilVM → State GalilVM}
    (hideal : ∀ x p, Enc x p → PalPeg.FrameFunction.starvedTest x = false →
      Enc (successor x) (PalPeg.LocalStepFusion.idealStep R blank p none))
    (x : State GalilVM) (p : Q × (Fin t → STape Γ)) (henc : Enc x p)
    (hmoves : PalPeg.FrameFunction.starvedTest x = false) :
    Enc (successor x) ((compStep R).apply blank p none) := by
  obtain ⟨hnext, htapes⟩ := compStep_apply R blank p none (hmargin x p henc)
  refine hclosed (successor x) (PalPeg.LocalStepFusion.idealStep R blank p none) _
    (hideal x p henc hmoves) ?_ (fun tape => htapes tape)
  show R.nq p.1 none (fun tape => readWin blank K (p.2 tape)) = _
  rw [hnext]

#print axioms enc_of_starved
#print axioms enc_of_stepping

end PalPeg.MachineStep
