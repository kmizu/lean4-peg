import PalPeg.CloseoutStageSupply

/-!
# `InvLPCS` at the replay landing

`CloseoutStageFree.cycleOracleIMG2_stageFree` drops `hsc` in exchange for
`hup : ∀ c r, InvLPC w c r → InvLPCS w P q first c r`.  That trade is only worth
making if `hup` is actually available where `InvLPC` is produced.

It is.  `GalilInvPlus2.invLPC_after_replayLanding` (:239) runs
`GalilReplaySegment.replay_after_fallback` on a `ReplayLanding`
(`GalilOracleDischarge:186`), whose fields include

* `rest : Restarted raw s 0 reset`,
* `clock : c.clock = 2048`,

and the call returns `hseg : WatchSegE P q first 2048 es c s c' t'`.  Those are
exactly the three inputs of `CloseoutStageSupply.invLPCS_of_seg`.

This file states the landing-level supply.  Threading it through
`invLPC_after_replayLanding`'s own conclusion is the remaining edit.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false

namespace PalPeg.CloseoutStageLanding

open PalPeg.CloseoutStageSupply
open PalPeg.GalilOracleDischarge
open PalPeg.GalilInvPlus2
open PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilReplaySegment
open GalilScaffoldTop
open GalilScaffoldController
open GalilScaffoldCounter

/-- **`InvLPCS` from a `ReplayLanding` and the segment it produced.**  The
landing supplies `Restarted` and the full clock; the segment supplies the run. -/
theorem invLPCS_of_replayLanding {raw : List (Fin 2)} {P : Shared} {q : ℕ} {first : Fin 9}
    {es : List Bool} {cT c' : Control} {sT t' : GalilVM} {R : ℕ}
    (hL : ReplayLanding raw cT sT R)
    (hseg : WatchSegE P q first 2048 es cT sT c' t')
    (hIC : InvLPC raw c' t') :
    InvLPCS raw P q first c' t' :=
  invLPCS_of_seg hIC hL.rest hL.clock hseg

#print axioms invLPCS_of_replayLanding

end PalPeg.CloseoutStageLanding
