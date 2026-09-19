import PalPeg.GalilTickFun3
import PalPeg.GalilBranchInvariants2
import PalPeg.GalilRunSkeleton
import PalPeg.WindowInv
import PalPeg.GalilWatchPhase

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
  PalPeg.GalilTickFun3 PalPeg.ShiftPalAlongTrace PalPeg.GalilReplayGeneral2
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier

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


/-- A place head sits at most two cells per letter to its left. -/
theorem position_le_two_left (p : PlaceHead) : position p ≤ 2 * p.head.left.length := by
  unfold position; split <;> omega

/-- **`ChainReady` at a watch that carries the birth-anchored window**, given that the right
head (which the verifier trails, `LagAt`) can still move.  The watch clause is the one
`M-watchBreak` left: the verifier can move and the period tape reads a symbol; the read
itself may or may not match. -/
theorem chainReady_watch_of_watchWindow {raw : List (Fin 2)} {cen₀ : ℕ} {cc b : Fin 3}
    {xs : List (Fin 3)} {w : GalilScaffoldChainWatch.State} {r : PlaceHead}
    (hW : WatchWindow raw cen₀ (position r) cc b xs (ChainVM.watch w))
    (hrep : GalilScaffoldInputTrace.Represents r.head raw) (hpres : r.head.focus ≠ none)
    (hcan : canRight r) : ChainReady (ChainVM.watch w) := by
  obtain ⟨hlag, -, hcore⟩ := hW
  obtain ⟨hon, hvrep, hvpres, -, -⟩ := id hcore
  have hlength : (encoded raw).length = 2 * raw.length + 1 := by simp [encoded, pairs_length]
  -- the right head is strictly inside the encoded word
  have hrb : position r + 1 < (encoded raw).length := by
    have h1 := right_position r hcan (represented_position _ raw hrep hpres).1
    have h2 := (represented_position _ raw (right_word r raw hrep hcan)
      (right_present r raw hrep hpres hcan)).2
    have h3 := position_le_two_left (right r)
    omega
  have hvpos := hlag.2
  have hcanV : canRight w.machine.verifier :=
    canRight_of_bound _ raw hvrep hvpres (by omega)
  refine ⟨fun hp => ⟨hcanV, ?_⟩, hon, fun m hm => ?_⟩
  · have hi : (position w.machine.verifier + 1 - (cen₀ + 1)) % (2 * (xs.length + 1)) <
        (GalilScaffoldChainSweep.bounce cc b xs).length := by
      rw [PalPeg.GalilWatchPhase.bounce_length]; exact Nat.mod_lt _ (by omega)
    exact ⟨_, (symbol_of_coreP hcore).trans (List.getElem?_eq_getElem hi)⟩
  · cases hm with
    | idle _ => exact hcanV
    | take hp _ =>
      have hne : w.lag.pos ≠ [] := by
        intro h0; simp [positive, h0] at hp
      have hlen : 0 < w.lag.pos.length := List.length_pos_of_ne_nil hne
      have h1 := right_position w.machine.verifier hcanV (represented_position _ raw hvrep hvpres).1
      show canRight (right w.machine.verifier)
      exact canRight_of_bound _ raw (right_word _ raw hvrep hcanV)
        (right_present _ raw hvrep hvpres hcanV) (by omega)

#print axioms chainReady_watch_of_watchWindow

#print axioms scan_tick_exists_PofC
#print axioms phase_tick_exists_PofC

end

end PalPeg.OracleRun
