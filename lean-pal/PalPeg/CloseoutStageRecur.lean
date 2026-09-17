import PalPeg.CloseoutPackRun36
import PalPeg.CloseoutStageSupply

/-!
# `H_stageScan` is not needed: the cycle hands back its own stage

`cycleOracleIMG2_of_cycleOracleMC3R` (`CloseoutPackRun36:673`) turns the `InvLPC`
it is handed into the `InvLPS` that `CycleOracleMC3` demands by calling
`CloseoutOracleI2.hstage_of_scanBranch`, and that is the only place `hsc` enters
the main path.  Look at what that theorem actually does:

```
rcases hIC.1.1.1.1 with h | ⟨k, h⟩
· exact replayStage_of_inv h      -- restart branch: free
· exact hsc c r k h               -- scan branch: the hypothesis
```

So `hsc` is needed **only** for states whose `InvS` disjunct is `InvScan`, and
`InvScan` is exactly what a replay landing produces — where the stage is in hand
(`CloseoutStageLanding.invLPCS_of_replayLanding`).  Better still, the oracle's own
progress branch already exits at `InvLPS` (`CycleOutMC3`, `GalilInvPlus3:206`),
and `InvLPS = InvLPC ∧ ReplayStage` (`:86`).

This file runs the `reachIMG2_fuel` recursion on `InvLPS` instead of `InvLPC`, so
the stage is consumed and reproduced by the cycle itself.  `H_stageScan` does not
appear.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutStageRecur

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
open PalPeg.GalilScaffoldChainInputSupply PegSeparation
open PalPeg.CloseoutPackRun36 PalPeg.CloseoutStageSupply
open PalPeg.GalilInvPlus2 PalPeg.GalilInvPlus3 PalPeg.GalilOracleMC2
open PalPeg.GalilLexMeasure PalPeg.GalilTraceCost PalPeg.GalilRunSkeleton
open PalPeg.CloseoutPackRun26 PalPeg.CloseoutOracleI2

variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **`reachIMG2_fuel` with the stage carried by the recursion.**  Identical to
`CloseoutPackRun36.reachIMG2_fuel` (:260) except that the entry invariant is
`InvLPS`, which the oracle's own progress exit supplies — so no `H_stageScan`. -/
theorem reachIMG2_fuel_stageFree {w : List (Fin 2)}
    (hpr : PackRunRMG2 centre place entry q first w)
    (hsl : H_shiftLocalG centre place entry q first w)
    (hor : CycleOracleMC3 (PofC centre place entry w) q first w)
    (m : ℕ) (hm1 : 1 ≤ m) (hmle : m ≤ w.length) :
    ∀ (n : ℕ) (c : Control) (r : GalilVM), mu w r ≤ n →
      InvLPS (PofC centre place entry w) q first w c r →
      position r.right ≤ 2 * m - 1 →
      ReachAtIMG2 centre place entry q first w m c r := by
  intro n
  induction n with
  | zero =>
    intro c r hn hI hp
    rcases hor m c r hm1 hmle hI hp with hdone | ⟨cT, sT, k, L, _, _, _, hlt, _⟩
    · exact reachAtIMG2_of_reachAtC3R centre place entry q first hpr hI.1
        (ipackMG2_of_invLPC centre place entry q first hsl hI.1) hdone
    · omega
  | succ n ih =>
    intro c r hn hI hp
    rcases hor m c r hm1 hmle hI hp with hdone | ⟨cT, sT, k, L, hst, hcr, hIT, hlt, hpT⟩
    · exact reachAtIMG2_of_reachAtC3R centre place entry q first hpr hI.1
        (ipackMG2_of_invLPC centre place entry q first hsl hI.1) hdone
    · obtain ⟨y, k', L', hst', hcr', hrp, hfr, hcont⟩ := ih cT sT (by omega) hIT hpT
      refine ⟨y, k + k', L ++ L', ?_, costedRun_trans hcr hcr', hrp, hfr, hcont⟩
      exact stepsIMG2_trans centre place entry q first
        (hpr c r hI.1 0 ⟨c, r⟩ (.zero _) k ⟨cT, sT⟩
          (ipackMG2_of_invLPC centre place entry q first hsl hI.1) hst) hst'

/-- **`ReachAtIMG2` from an `InvLPS` entry, no `H_stageScan`.** -/
theorem reachIMG2_from_invLPS {w : List (Fin 2)}
    (hpr : PackRunRMG2 centre place entry q first w)
    (hsl : H_shiftLocalG centre place entry q first w)
    (hor : CycleOracleMC3 (PofC centre place entry w) q first w)
    {m : ℕ} (hm1 : 1 ≤ m) (hmle : m ≤ w.length) {c : Control} {r : GalilVM}
    (hI : InvLPS (PofC centre place entry w) q first w c r)
    (hp : position r.right ≤ 2 * m - 1) :
    ReachAtIMG2 centre place entry q first w m c r :=
  reachIMG2_fuel_stageFree centre place entry q first hpr hsl hor m hm1 hmle _ c r le_rfl hI hp

/-- **`CycleOracleIMG2` from an `InvLPCS` supply.**  `hup` replaces `hsc`: instead
of a stage at *every* `InvScan` state, it asks only for the disjunction
`Inv ∨ ReplayStage`, whose first branch `hstage_of_scanBranch` already proves for
free and whose second branch a replay landing supplies. -/
theorem cycleOracleIMG2_stageFree {w : List (Fin 2)}
    (hpr : PackRunRMG2 centre place entry q first w)
    (hsl : H_shiftLocalG centre place entry q first w)
    (hor : CycleOracleMC3 (PofC centre place entry w) q first w)
    (hup : ∀ (c : Control) (r : GalilVM), InvLPC w c r →
      InvLPCS w (PofC centre place entry w) q first c r) :
    CycleOracleIMG2 centre place entry q first w := by
  intro m c r hm1 hmle hIC hp
  exact cycleOutIMG2_of_cycleOutMC3R centre place entry q first hpr hIC
    (ipackMG2_of_invLPC centre place entry q first hsl hIC)
    (hor m c r hm1 hmle (invLPS_of_invLPCS (hup c r hIC)) hp)

#print axioms reachIMG2_fuel_stageFree
#print axioms reachIMG2_from_invLPS
#print axioms cycleOracleIMG2_stageFree

end PalPeg.CloseoutStageRecur
