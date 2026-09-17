import PalPeg.GalilReplaySpan
import PalPeg.GalilRunSkeleton
import PalPeg.GalilFoundStageInv
import PalPeg.GalilFinalAssembly2

/-!
# `RestartShape` is a theorem at the concrete shared record

`RestartShape` (`GalilReplaySpan:771`) asks that a broken, restartable chain can
actually restart.  At `PofC` the restart relation is `restartVM entry`
(`GalilScaffoldTopRestart:19`), which asks for exactly the first three fields of
`Restartable` (`GalilReplaySpan:500`) — `zero lag`, `¬ negative margin`,
`positive last` — and then *names* the successor state.  So the witness is the
named state and the proof is the destructuring.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false

namespace PalPeg.CloseoutRestartShape

open PalPeg.GalilReplaySpan
open PalPeg.GalilRunSkeleton
open PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilFinalAssembly2

/-- **`RestartShape` holds at `PofC`.**  No hypothesis: `restartVM` demands the
three `Restartable` fields and installs the state the shape asks for. -/
theorem restartShape_PofC (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry : ℕ) (w : List (Fin 2)) :
    RestartShape (PofC centre place entry w) := by
  intro s wch hbroken hr
  exact ⟨_, ⟨wch, hbroken, hr.margin, hr.last, hr.lag, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **`ReplayBudgetR` holds at `PofC`.**  `replayBudgetR_of_decodes'`
(`GalilFoundStageInv:232`) needs only `Decodes P`, and `decodesC`
(`GalilFinalAssembly2:327`) gives that for the concrete shared record. -/
theorem replayBudgetR_PofC (entry : ℕ) (q : ℕ) (first : Fin 9) (w : List (Fin 2)) :
    PalPeg.GalilFoundStage.ReplayBudgetR w (PofC centreC placeC entry w) q first 2048 :=
  PalPeg.GalilFoundStageInv.replayBudgetR_of_decodes'
    (PalPeg.GalilFinalAssembly2.decodesC entry w)

#print axioms restartShape_PofC
#print axioms replayBudgetR_PofC

end PalPeg.CloseoutRestartShape
