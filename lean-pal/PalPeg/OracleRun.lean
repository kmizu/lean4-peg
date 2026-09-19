import PalPeg.GalilTickFun3
import PalPeg.GalilBranchInvariants2
import PalPeg.GalilRunSkeleton

set_option autoImplicit false

/-!
# `OracleRun`: tick existence in the `PofC` frame

`CycleOracleMC3` (the remaining oracle obligation) speaks about runs of
`galilFrameS (PofC centre place entry w) q first`, whose fallback entry is the relational
`beginFallbackVM'`.  `GalilTickFun.tick_exists` is stated for the functional frame
`sharedFun`, so it does not apply; the generic `scan_tick_gen` / `phase_tick_gen` do.
This file instantiates them at `PofC` with the entries' own existence lemmas
(`beginShift_exists`, `beginFallback_exists`), the search co-process's totality
(`searchEffect_exists`, from `SearchReady`) and the chain's totality (`chainAt_exists`,
from `ChainReady` — with `M-watchBreak` fixed, a positive-lag watch always ticks).
-/

namespace PalPeg.OracleRun

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilRunSkeleton PalPeg.GalilTickFun
  PalPeg.GalilTickFun3
open GalilScaffoldCounter

section
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **A non-replaying scan state with a positive clock ticks in the `PofC` frame**, given a
ready search co-process and a ready chain. -/
theorem scan_tick_exists_PofC {w : List (Fin 2)} (c : Control) (s : GalilVM)
    (hm : c.mode = .scan) (hclk : 1 ≤ c.clock) (hr : c.replaying = false)
    (hsearch : PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get s))
    (hready : ChainReady s.chain) :
    ∃ st', Tick (galilFrameS (PofC centre place entry w) q first) 2048 ⟨c, s⟩ st' :=
  scan_tick_gen (PofC centre place entry w) q first 2048 c s hm hclk hr
    (fun t hg => beginShift_exists t hg) (fun t => beginFallback_exists t)
    (fun a => PalPeg.GalilBranchInvariants2.searchEffect_exists _ a s hsearch)
    (fun a v => chainAt_exists a _ _ _ _ _ _ s.chain hready)

/-- **Every phase mode ticks in the `PofC` frame** (the generic `phase_tick_gen`). -/
theorem phase_tick_exists_PofC {w : List (Fin 2)} (x : State GalilVM)
    (hx : PhaseEnabled q first x) :
    ∃ y, Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y :=
  phase_tick_gen (PofC centre place entry w) q first 2048 x hx

#print axioms scan_tick_exists_PofC
#print axioms phase_tick_exists_PofC

end

end PalPeg.OracleRun
