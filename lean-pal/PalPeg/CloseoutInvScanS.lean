import PalPeg.CloseoutStageScan1
import PalPeg.CloseoutOracleI2

/-!
# The `hsc` re-cut: `InvS` with the stage field restored

`H_stageScan` (`CloseoutOracleI2:173`) is false: it asks for `ReplayStage` at
**every** state satisfying `InvScan`, and `InvScan`'s eleven fields never
mention `s.radius`, while `ReplayStage`'s `Restarted` demands
`Canonical s.radius`.  Replacing only `radius := ⟨[()],[()]⟩` in any inhabitant
keeps all eleven fields and breaks the conclusion.

The repair is the standard re-cut.  `hsc` is consumed in exactly one place,
`hstage_of_scanBranch` (`CloseoutOracleI2:179`), which takes the replay branch
of `InvS = Inv ∨ ∃ k, InvScan` and applies `hsc` to it.  Carrying `ReplayStage`
in that branch makes the step disappear:

```
InvSS raw P q first c s := Inv raw c s ∨ ∃ k, InvScan 2048 raw c s k ∧ ReplayStage raw P q first c s
```

and the producer already has the data — `CloseoutStageScan1` picks up the stage
field that `replay_after_fallback` drops.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false

namespace PalPeg.CloseoutInvScanS

open PalPeg.CloseoutOracleI2
open PalPeg.CloseoutStageScan1
open PalPeg.GalilOracleDischarge
open PalPeg.GalilReplaySegment
open PalPeg.GalilInvPlus3
open PalPeg.GalilFoundStage
open PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilScaffoldController
open PalPeg.GalilRunSkeleton
open GalilScaffoldTop

variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **`InvS` with the replay branch carrying its stage.** -/
def InvSS (raw : List (Fin 2)) (c : Control) (s : GalilVM) : Prop :=
  Inv raw c s ∨
    ∃ k : ℕ, InvScan 2048 raw c s k ∧
      ReplayStage raw (PofC centre place entry raw) q first c s

/-- `InvSS` forgets to `InvS`. -/
theorem invS_of_invSS {raw : List (Fin 2)} {c : Control} {s : GalilVM}
    (h : InvSS centre place entry q first raw c s) : InvS raw c s := by
  rcases h with hInv | ⟨k, hScan, -⟩
  · exact Or.inl hInv
  · exact Or.inr ⟨k, hScan⟩

/-- **`ReplayStage` from `InvSS`, with no `H_stageScan`.**  This is the whole
content of `hsc`: the restart branch gives it outright
(`GalilInvPlus3.replayStage_of_inv`) and the replay branch now carries it. -/
theorem replayStage_of_invSS {raw : List (Fin 2)} {c : Control} {s : GalilVM}
    (h : InvSS centre place entry q first raw c s) :
    ReplayStage raw (PofC centre place entry raw) q first c s := by
  rcases h with hInv | ⟨-, -, hStage⟩
  · exact replayStage_of_inv hInv
  · exact hStage

#print axioms invS_of_invSS
#print axioms replayStage_of_invSS

end PalPeg.CloseoutInvScanS
