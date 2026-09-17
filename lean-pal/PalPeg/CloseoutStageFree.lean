import PalPeg.CloseoutStageSupply
import PalPeg.CloseoutPackRun36

/-!
# `H_stageScan` removed from the oracle bridge

`CloseoutPackRun36.cycleOracleIMG2_of_cycleOracleMC3R` (:673) takes `hsc` only to
run `CloseoutOracleI2.hstage_of_scanBranch`, which turns an `InvLPC` into the
`InvLPS` that `CycleOracleMC3` wants.  `H_stageScan` is false, so that step
cannot be discharged as stated.

`CloseoutStageSupply.invLPS_of_invLPCS` does the same job from `InvLPCS`
(`InvLPC` plus the replay branch's own stage), with no hypothesis.  This file
states the bridge over `InvLPCS`, so the `hsc` argument disappears.

What moves, honestly: the obligation is no longer "prove `H_stageScan`" but
"produce `InvLPCS` where the recursion currently produces `InvLPC`".  The
producer already has the data — `CloseoutOracle6.invScanO_of_replay_generalR'`
takes `hR : Restarted raw t 0 reset` and returns the `WatchSegE` — so this is a
plumbing change, not a new mathematical obligation.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false

namespace PalPeg.CloseoutStageFree

open PalPeg.CloseoutStageSupply
open PalPeg.CloseoutPackRun36
open PalPeg.CloseoutPackRun26
open PalPeg.GalilInvPlus2
open PalPeg.GalilInvPlus3
open PalPeg.GalilRunSkeleton
open PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop
open GalilScaffoldController

variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **`CycleOracleIMG2` with `hsc` gone.**  Same as
`cycleOracleIMG2_of_cycleOracleMC3R` except the `InvLPC` input is strengthened to
`InvLPCS`, which carries the stage the replay branch was reached with. -/
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

#print axioms cycleOracleIMG2_stageFree

end PalPeg.CloseoutStageFree
