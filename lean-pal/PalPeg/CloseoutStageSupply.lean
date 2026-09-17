import PalPeg.CloseoutOracle6
import PalPeg.CloseoutStageScan1
import PalPeg.CloseoutOracleI2

/-!
# Supplying `ReplayStage` where the replay branch is produced

`H_stageScan` (`CloseoutOracleI2:173`) is false — `InvScan`'s eleven fields never
mention `s.radius`, while `ReplayStage`'s `Restarted` demands `Canonical radius`.
Its only consumer is `hstage_of_scanBranch` (`CloseoutOracleI2:179`), which takes
the replay branch of `InvS` and applies `hsc` to it.

The producer already holds the data.  `invScanO_of_replay_generalR'`
(`CloseoutOracle6:88`) takes `hR : Restarted raw t 0 reset` and `hc : c.clock = delay`
as hypotheses and returns the segment `hseg : WatchSegE …` alongside the
`InvScanO`.  `CloseoutStageScan1.replayStage_of_seg` turns exactly those three
into `ReplayStage`.  This file states the strengthened producer.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false

namespace PalPeg.CloseoutStageSupply

open PalPeg.CloseoutOracle6
open PalPeg.CloseoutStageScan1
open PalPeg.GalilReplaySegment
open PalPeg.GalilFoundStage
open PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilTickFun2
open PalPeg.GalilBranchInvariants2
open GalilScaffoldTop
open GalilScaffoldController
open GalilScaffoldCounter

/-- **The replay landing carries its stage.**  Same hypotheses as
`invScanO_of_replay_generalR'` at `delay = 2048`; the first branch gains the
`ReplayStage` field that `H_stageScan` was named to supply. -/
theorem replayStage_at_landing (raw : List (Fin 2)) (P : Shared)
    {q : ℕ} {first : Fin 9} {es : List Bool} {c c' : Control} {t t' : GalilVM}
    (hR : Restarted raw t 0 reset) (hc : c.clock = 2048)
    (hseg : WatchSegE P q first 2048 es c t c' t') :
    ReplayStage raw P q first c' t' :=
  replayStage_of_seg hR hc hseg

/-- **`InvScan` together with its stage**: the re-cut of the replay branch of
`InvS`.  `ReplayStage` does *not* ask the landing state to be `Restarted` — it
asks for a `Restarted` ancestor reached by a `WatchSegE`, which is exactly what
the fallback replay has. -/
def InvScanS (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9)
    (c : Control) (s : GalilVM) (k : ℕ) : Prop :=
  InvScan 2048 raw c s k ∧ ReplayStage raw P q first c s

/-- **The producer fills both halves.**  Same three inputs as
`replayStage_of_seg`, plus the `InvScan` the segment already returns. -/
theorem invScanS_of_seg {raw : List (Fin 2)} {P : Shared} {q : ℕ} {first : Fin 9}
    {es : List Bool} {c c' : Control} {t t' : GalilVM} {r : ℕ}
    (hR : Restarted raw t 0 reset) (hc : c.clock = 2048)
    (hseg : WatchSegE P q first 2048 es c t c' t')
    (hIS : InvScan 2048 raw c' t' r) :
    InvScanS raw P q first c' t' r :=
  ⟨hIS, replayStage_of_seg hR hc hseg⟩

/-- **`ReplayStage` out of the re-cut branch, with no `H_stageScan`.**  This is
the whole content of `hsc`: the `Inv` branch gives it outright
(`GalilInvPlus3.replayStage_of_inv`) and the replay branch now carries it. -/
theorem replayStage_of_invScanS {raw : List (Fin 2)} {P : Shared} {q : ℕ} {first : Fin 9}
    {c : Control} {s : GalilVM} {k : ℕ}
    (h : InvScanS raw P q first c s k) : ReplayStage raw P q first c s := h.2

/-- **`InvLPC` with the replay branch's stage attached.**  The re-cut that makes
`H_stageScan` unnecessary: `InvLPC` says nothing about a `Restarted` ancestor,
so the replay branch has to carry the stage it was reached with. -/
def InvLPCS (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9)
    (c : Control) (s : GalilVM) : Prop :=
  PalPeg.GalilInvPlus2.InvLPC raw c s ∧
    (Inv raw c s ∨ ReplayStage raw P q first c s)

/-- **`InvLPS` from `InvLPCS`, with no `H_stageScan`.**  This is exactly what
`CloseoutOracleI2.hstage_of_scanBranch` does, minus the `hsc` argument: the
restart branch gives `ReplayStage` outright
(`GalilInvPlus3.replayStage_of_inv`) and the replay branch now carries it. -/
theorem invLPS_of_invLPCS {raw : List (Fin 2)} {P : Shared} {q : ℕ} {first : Fin 9}
    {c : Control} {s : GalilVM} (h : InvLPCS raw P q first c s) :
    PalPeg.GalilInvPlus3.InvLPS P q first raw c s := by
  refine ⟨h.1, ?_⟩
  rcases h.2 with hInv | hStage
  · exact PalPeg.GalilInvPlus3.replayStage_of_inv hInv
  · exact hStage

/-- `InvLPCS` at a restart landing: the `Inv` branch needs nothing extra. -/
theorem invLPCS_of_inv {raw : List (Fin 2)} {P : Shared} {q : ℕ} {first : Fin 9}
    {c : Control} {s : GalilVM} (hIC : PalPeg.GalilInvPlus2.InvLPC raw c s)
    (h : Inv raw c s) : InvLPCS raw P q first c s :=
  ⟨hIC, Or.inl h⟩

/-- `InvLPCS` at a replay landing, from the segment that produced it. -/
theorem invLPCS_of_seg {raw : List (Fin 2)} {P : Shared} {q : ℕ} {first : Fin 9}
    {es : List Bool} {c c' : Control} {t t' : GalilVM}
    (hIC : PalPeg.GalilInvPlus2.InvLPC raw c' t')
    (hR : Restarted raw t 0 reset) (hc : c.clock = 2048)
    (hseg : WatchSegE P q first 2048 es c t c' t') :
    InvLPCS raw P q first c' t' :=
  ⟨hIC, Or.inr (replayStage_of_seg hR hc hseg)⟩

#print axioms replayStage_at_landing
#print axioms invScanS_of_seg
#print axioms replayStage_of_invScanS
#print axioms invLPS_of_invLPCS
#print axioms invLPCS_of_inv
#print axioms invLPCS_of_seg

end PalPeg.CloseoutStageSupply
