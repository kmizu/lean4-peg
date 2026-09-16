import PalPeg.CloseoutContracts

/-!
# The in-replay found leaf: `hfoundReplay` ⟶ `CloseoutContracts.FoundExit`

`GalilOracleMC3.h_oracle_of_leaves''` asks for

```
hfoundReplay : ∀ w m c r cT sT R k, 1 ≤ m → m ≤ w.length → InvLPC w c r →
  StepsAll (galilFrameS (PofC …) q first) 2048 (SoundScanNR w) k ⟨c, r⟩ ⟨cT, sT⟩ →
  ReplayLanding w cT sT R → SpanRep sT →
  position r.center < position sT.center → position sT.right ≤ 2 * m - 1 →
  (GalilReplaySpan.ChainEnd w … (position sT.right + R) cT sT 0 R ∨
   GalilReplaySpan.BrokeAndRestarted w … cT sT) →
  FoundInReplayRouteMC2 …
```

and the closeout wants its `InvLPS`-strengthened value
`CloseoutContracts.FoundExit`, entered through `CloseoutContracts.StageEntryC`.

## What this file settles

1. **The `broke` constructor is unavailable at this leaf** (`not_broke_here`):
   `FoundExit.broke` fixes `position sT.center = position r.center`, while the
   leaf hands us `position r.center < position sT.center`.  So *both* branches
   (ii) `ChainEnd` and (iii) `BrokeAndRestarted` must land in `FoundExit.landed`,
   i.e. must be continued to a **restarted** state.  This is the structural fact
   that fixes the shape of the two continuation contracts below.

2. **The composition is proved.**  Given the prefix cost of the leaf's own
   `StepsAll` (`PrefixCost`) and a continuation from the landing to a restarted
   state (`ChainContinuation` / `RestartContinuation`), the run, its cost, the
   centre progress and the position bound compose to `FoundExit.landed`
   (`foundExit_of_chainEnd`, `foundExit_of_broke`, `foundExit_of_leaf`).

## What stays open (NAMED, with the exact types below)

* `PrefixCost` — the leaf publishes a `StepsAll` with no `CostedRun`; the
  producer (`GalilInvPlus3.cycleOutMC3_of_fallback'`, `replaying` branch) has
  `GalilCostedFallback.costedRun_fallback_replay` only for the *quiet* landing.
* `ChainContinuation` — branch (ii): the chain survives to the landing in
  `ChainW`, so the continuation is the **watch phase of the found route's
  preparation-and-back part** (`GalilFoundLandingL.foundRouteMC_shift`'s
  `hseg…`/`Rounds`, or `GalilNoShiftDischarge.foundRouteMC_noshift_d`'s `hcont`).
* `RestartContinuation` — branch (iii): the landing is idle with
  `InvScan ∧ OutputRel` and, being immediately after a restart, its
  `ReplayStage` is `replayStage_entry`; the continuation is the ordinary
  found route from a restarted state.

Both continuation contracts charge their cost exactly as
`GalilInvPlus3.FoundInReplayRouteMC3.landed` does, i.e. as a `CostedRun` over
the *same* run as the `StepsAll`.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutFoundReplay

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton PalPeg.GalilTraceCost
open PalPeg.GalilOracleDischarge
open PalPeg.GalilInvPlus3 PalPeg.CloseoutContracts

/-! ## 1. Why the break constructor cannot be used here -/

/-- **The leaf's centre progress forbids `FoundExit.broke`.**  The `broke`
constructor keeps the centre (`position sT.center = position r.center`); the
leaf's own hypothesis says the centre already moved.  Hence every value this
leaf returns is a `landed`, and both continuations must reach a restarted
state. -/
theorem not_broke_here {r sT : GalilVM}
    (hprog : position r.center < position sT.center)
    (hc : position sT.center = position r.center) : False := by omega

/-! ## 2. The three named obligations -/

/-- **NAMED (open).**  The cost of the leaf's own prefix run.  `hfoundReplay`
receives a `StepsAll` of length `k` from `⟨c, r⟩` to `⟨cT, sT⟩` and no cost for
it; `FoundExit.landed` charges the whole run.  The producer has
`GalilCostedFallback.costedRun_fallback_replay` for the quiet landing only. -/
def PrefixCost (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) : Prop :=
  ∀ (c : Control) (r : GalilVM) (cT : Control) (sT : GalilVM) (k : ℕ),
    StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩ →
    ∃ L : List Piece, CostedRun r sT k L

/-- The common shape of a continuation: from the landing `⟨cT, sT⟩` of the
replay, the machine runs on to a **restarted** state, with a cost for that
stretch, without moving the centre backwards and without passing the checkpoint
position. -/
def ContinuesToRestart (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ)
    (cT : Control) (sT : GalilVM) : Prop :=
  ∃ (cU : Control) (sU : GalilVM) (k' : ℕ) (L' : List Piece),
    StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k' ⟨cT, sT⟩ ⟨cU, sU⟩ ∧
    CostedRun sT sU k' L' ∧
    MInv raw cU sU ∧ (∃ (Rad : ℕ) (last : Counter), Restarted raw sU Rad last) ∧
    FoundResidual raw cU sU ∧ SpanRep sU ∧
    position sT.center ≤ position sU.center ∧
    position sU.right ≤ 2 * m - 1

/-- **NAMED (open).**  Branch (ii) of
`GalilReplaySpan.replay_after_fallback_general''_fuel'_of_decodes`: the chain
started in the replay survives to the landing, which sits in `ChainW` with
window `position sT.right + R` and right head exactly that window.  The
continuation is the watch phase of the found route's preparation-and-back part
(`GalilFoundLandingL.foundRouteMC_shift` `hseg…`/`Rounds`, or
`GalilNoShiftDischarge.foundRouteMC_noshift_d` `hcont`). -/
def ChainContinuation (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ) : Prop :=
  ∀ (cT : Control) (sT : GalilVM) (R : ℕ),
    ReplayLanding raw cT sT R → SpanRep sT →
    position sT.right ≤ 2 * m - 1 →
    PalPeg.GalilReplaySpan.ChainEnd raw P q first 2048 (position sT.right + R) cT sT 0 R →
    ContinuesToRestart P q first raw m cT sT

/-- **NAMED (open).**  Branch (iii): a chain broke inside the replay and the
search restarted, so the landing is idle with `InvScan ∧ OutputRel`
(`GalilLeafOutReplay`), and — being immediately after a restart — its stage
datum is `replayStage_entry`.  The continuation is the ordinary found route
from a restarted state. -/
def RestartContinuation (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ) :
    Prop :=
  ∀ (cT : Control) (sT : GalilVM) (R : ℕ),
    ReplayLanding raw cT sT R → SpanRep sT →
    position sT.right ≤ 2 * m - 1 →
    PalPeg.GalilReplaySpan.BrokeAndRestarted raw P q first 2048 cT sT →
    ContinuesToRestart P q first raw m cT sT

/-! ## 3. The composition -/

/-- The composition step, shared by the two branches: prefix run + prefix cost +
continuation ⟹ `FoundExit.landed`. -/
theorem foundExit_of_continues {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    {m k : ℕ} {c cT : Control} {r sT : GalilVM}
    (hpc : PrefixCost P q first raw)
    (hst : StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩)
    (hprog : position r.center < position sT.center)
    (hcont : ContinuesToRestart P q first raw m cT sT) :
    FoundExit P q first raw m c r := by
  obtain ⟨L, hcr⟩ := hpc c r cT sT k hst
  obtain ⟨cU, sU, k', L', hst', hcr', hM, hR, hres, hSpan, hmono, hpos⟩ := hcont
  refine FoundExit.landed cU sU (k + k') (L ++ L') (stepsAll_trans hst hst')
    (costedRun_trans hcr hcr') hM hR hres hSpan ?_ hpos
  omega

/-- **Branch (ii).**  The surviving-chain landing, continued. -/
theorem foundExit_of_chainEnd {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    {m k R : ℕ} {c cT : Control} {r sT : GalilVM}
    (hpc : PrefixCost P q first raw) (hch : ChainContinuation P q first raw m)
    (hst : StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩)
    (hL : ReplayLanding raw cT sT R) (hSpan : SpanRep sT)
    (hprog : position r.center < position sT.center)
    (hpos : position sT.right ≤ 2 * m - 1)
    (hE : PalPeg.GalilReplaySpan.ChainEnd raw P q first 2048 (position sT.right + R) cT sT 0 R) :
    FoundExit P q first raw m c r :=
  foundExit_of_continues hpc hst hprog (hch cT sT R hL hSpan hpos hE)

/-- **Branch (iii).**  The break-and-restart landing, continued. -/
theorem foundExit_of_broke {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    {m k R : ℕ} {c cT : Control} {r sT : GalilVM}
    (hpc : PrefixCost P q first raw) (hrc : RestartContinuation P q first raw m)
    (hst : StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩)
    (hL : ReplayLanding raw cT sT R) (hSpan : SpanRep sT)
    (hprog : position r.center < position sT.center)
    (hpos : position sT.right ≤ 2 * m - 1)
    (hB : PalPeg.GalilReplaySpan.BrokeAndRestarted raw P q first 2048 cT sT) :
    FoundExit P q first raw m c r :=
  foundExit_of_continues hpc hst hprog (hrc cT sT R hL hSpan hpos hB)

/-- **The leaf.**  Exactly the hypothesis list of `hfoundReplay` in
`GalilOracleMC3.h_oracle_of_leaves''` (with the entry taken at
`CloseoutContracts.StageEntryC`, whose `InvLPC` projection is the `InvLPC` the
leaf states), concluding at `CloseoutContracts.FoundExit`. -/
theorem foundExit_of_leaf {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    {m k R : ℕ} {c cT : Control} {r sT : GalilVM}
    (hpc : PrefixCost P q first raw) (hch : ChainContinuation P q first raw m)
    (hrc : RestartContinuation P q first raw m)
    (hm1 : 1 ≤ m) (hmle : m ≤ raw.length)
    (hE : StageEntryC P q first raw c r)
    (hst : StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩)
    (hL : ReplayLanding raw cT sT R) (hSpan : SpanRep sT)
    (hprog : position r.center < position sT.center)
    (hpos : position sT.right ≤ 2 * m - 1)
    (hor : PalPeg.GalilReplaySpan.ChainEnd raw P q first 2048 (position sT.right + R) cT sT 0 R ∨
      PalPeg.GalilReplaySpan.BrokeAndRestarted raw P q first 2048 cT sT) :
    FoundExit P q first raw m c r := by
  rcases hor with h | h
  · exact foundExit_of_chainEnd hpc hch hst hL hSpan hprog hpos h
  · exact foundExit_of_broke hpc hrc hst hL hSpan hprog hpos h

/-- **Connected, consumer side.**  The leaf value feeds the route the oracle
asks for. -/
theorem foundInReplayRouteMC3_of_leaf {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    {m k R : ℕ} {c cT : Control} {r sT : GalilVM}
    (hpc : PrefixCost P q first raw) (hch : ChainContinuation P q first raw m)
    (hrc : RestartContinuation P q first raw m)
    (hm1 : 1 ≤ m) (hmle : m ≤ raw.length)
    (hE : StageEntryC P q first raw c r)
    (hst : StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩)
    (hL : ReplayLanding raw cT sT R) (hSpan : SpanRep sT)
    (hprog : position r.center < position sT.center)
    (hpos : position sT.right ≤ 2 * m - 1)
    (hor : PalPeg.GalilReplaySpan.ChainEnd raw P q first 2048 (position sT.right + R) cT sT 0 R ∨
      PalPeg.GalilReplaySpan.BrokeAndRestarted raw P q first 2048 cT sT) :
    FoundInReplayRouteMC3 P q first raw m c r :=
  foundInReplayRouteMC3_of_foundExit
    (foundExit_of_leaf hpc hch hrc hm1 hmle hE hst hL hSpan hprog hpos hor)

/-! ## 4. The producers this leaf is meant to meet -/

#check @PalPeg.GalilReplaySpan.replay_after_fallback_general''_fuel'_of_decodes
#check @PalPeg.GalilReplaySpan.ChainEnd
#check @PalPeg.GalilReplaySpan.ChainW
#check @PalPeg.GalilReplaySpan.BrokeAndRestarted
#check @PalPeg.GalilFoundLandingL.foundRouteMC_shift
#check @PalPeg.GalilNoShiftDischarge.foundRouteMC_noshift_d
#check @PalPeg.GalilInvPlus3.FoundInReplayRouteMC3
#check @PalPeg.CloseoutContracts.FoundExit

end PalPeg.CloseoutFoundReplay

#print axioms PalPeg.CloseoutFoundReplay.not_broke_here
#print axioms PalPeg.CloseoutFoundReplay.foundExit_of_continues
#print axioms PalPeg.CloseoutFoundReplay.foundExit_of_chainEnd
#print axioms PalPeg.CloseoutFoundReplay.foundExit_of_broke
#print axioms PalPeg.CloseoutFoundReplay.foundExit_of_leaf
#print axioms PalPeg.CloseoutFoundReplay.foundInReplayRouteMC3_of_leaf
