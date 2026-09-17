import PalPeg.CloseoutWatchRound16

/-!
# Round 17: the watch-chain fallback contract `FallbackRouteW`

Round 16 settled negatively the last item of Round 15's three-way exit split:
at a `BreakEndC` landing the chain is a `.watch`, so the `PrepChain s1.chain`
premise of `CloseoutWatchPhase2.FallbackRouteLP` is **false** there, and the
prep-time fallback route is inapplicable, not merely unproved.

This round supplies the contract Round 16 named as missing — the same landing
record with `PrepChain` replaced by `CloseoutWatchRun.LiveScanWatch` — and
proves everything that follows from it downstream.

## What is proved here (unconditionally, no `sorry`)

1. `FallbackRouteW` — the watch-chain sibling of
   `CloseoutWatchPhase2.FallbackRouteLP`: same conclusion (a `StepsAll` run
   from `⟨c, r⟩` with its `CostedRun`, `InvLP` landing and the two head
   positions), premise `LiveScanWatch c1 s1` in place of `PrepChain s1.chain`.
2. `not_prepChain_of_liveScanWatch` — Round 16's vacuity argument isolated:
   a live scan watch landing never satisfies `PrepChain`.  Hence
   `FallbackRouteW` is **not** derivable from `FallbackRouteLP` (the premises
   are disjoint), and conversely: the two contracts are independent.
3. `foundExitW_of_route` — **the third exit branch, modulo the segment form.**
   `FallbackRouteW` plus `CloseoutWatchPhase2.LandingRestartReach` turns a
   watch-chain mismatch landing reached by `WatchSegE` from the preparation
   landing into a `CloseoutContracts.FoundExit` (`.landed`), by the same
   composition `CloseoutWatchPhase2.fallbackRouteG_of_raw` uses on the
   prep-time side (`CloseoutWatchPhase.inv_of_invLP` + `spanRep_of_invLP` +
   `CloseoutFoundExits.landed_pack`).
4. `foundExitW_of_breakEndE` — 3 packaged for a `BreakEndC`-shaped landing
   presented in `WatchSegE` form: mismatch, clock `1`, `canRight`, watching
   chain.

## Attempted and NOT closed, with the exact missing facts

* **`FallbackRouteW` is a NAMED contract, not a derivation.**  The task asked
  to re-prove it from the证明元 of `FallbackRouteLP`; there is none:
  `FallbackRouteLP` has no producer anywhere in the tree — it is itself a
  `def` consumed only by `fallbackRouteG_of_raw` / `mismatchExitG_of_raw`,
  exactly as `CloseoutPrepInputs3.FallbackRouteG` is a named residue.  So the
  watch variant cannot be *derived*; it can only be stated (1) and consumed
  (3, 4), which is what this round does.  The `GalilPrepMatch` route
  (`prep_guard_false_afterMismatch`, `fallback_from_prep`) consumes `PrepChain`
  at that very state and therefore supplies nothing here either.
* **`ExitSplit3C` / `foundExit_compare_final9` are NOT constructed.**
  Beyond `FallbackRouteW` itself, the branch still needs the landing in
  `WatchSegE es cP sP` form, whereas `CloseoutWatchRound.BreakEndC` presents it
  as a `WatchSeg` from the *rounds* state.  **Missing fact (one sentence):**
  that a `WatchSeg P q first 2048 c s c1 s1` carries an event list, i.e.
  `∃ es, WatchSegE P q first 2048 es c s c1 s1`, which no lemma in the tree
  states (`watchSeg_append` and `watchSegE_append` are proved separately,
  never related).

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutWatchRound17

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton PalPeg.GalilTraceCost PalPeg.GalilInvPlus
open PalPeg.CloseoutContracts
open PalPeg.CloseoutWatchRun (LiveScanWatch)
open PalPeg.CloseoutWatchPhase2 (LandingRestartReach)

/-! ## 1. The contract -/

/-- **NAMED (open).**  `CloseoutWatchPhase2.FallbackRouteLP` with its
`GalilPrepMatch.PrepChain` premise replaced by `LiveScanWatch`: the machine's
continuation from a clock-one outer mismatch discovered while the chain is
*watching* (the post-rounds `BreakEndC` shape), as opposed to while it is still
preparing. -/
def FallbackRouteW (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ)
    (c : Control) (r : GalilVM) (cP : Control) (sP : GalilVM) : Prop :=
  ∀ (es : List Bool) (c1 : Control) (s1 : GalilVM),
    WatchSegE P q first 2048 es cP sP c1 s1 → LiveScanWatch c1 s1 →
    c1.clock = 1 → canRight s1.right →
    read (left s1.left) ≠ read (right s1.right) →
    ∃ (cT : Control) (sT : GalilVM) (k : ℕ) (L : List Piece),
      StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩ ∧
      CostedRun r sT k L ∧ InvLP raw cT sT ∧
      position r.center < position sT.center ∧ position sT.right ≤ 2 * m - 1

/-! ## 2. Independence from the prep-time contract -/

/-- **Derived (Round 16's vacuity, isolated).**  A live scan watch landing never
satisfies `PrepChain`, so `FallbackRouteLP` says nothing at the landings
`FallbackRouteW` speaks about, and `FallbackRouteW` says nothing at the
prep-time landings `FallbackRouteLP` speaks about. -/
theorem not_prepChain_of_liveScanWatch {c1 : Control} {s1 : GalilVM}
    (h : LiveScanWatch c1 s1) : ¬ GalilPrepMatch.PrepChain s1.chain := by
  obtain ⟨-, -, -, w, hw⟩ := h
  intro hpc
  rcases hpc with ⟨_, _, _, _, _, _, _, hx, -⟩ | ⟨_, _, _, _, _, hx, -⟩ <;>
    · rw [hw] at hx; exact ChainVM.noConfusion hx

/-! ## 3. The consumer side -/

/-- **Derived.**  `FallbackRouteW` plus the landing sharpening turns a watching
mismatch landing into a `FoundExit`, by the composition
`CloseoutWatchPhase2.fallbackRouteG_of_raw` performs on the prep-time side. -/
theorem foundExitW_of_route {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    {m : ℕ} {c cP : Control} {r sP : GalilVM}
    (h : FallbackRouteW P q first raw m c r cP sP)
    (hLR : LandingRestartReach P q first raw c r)
    (es : List Bool) (c1 : Control) (s1 : GalilVM)
    (hseg : WatchSegE P q first 2048 es cP sP c1 s1) (hlive : LiveScanWatch c1 s1)
    (hclk : c1.clock = 1) (hav : canRight s1.right)
    (hne : read (left s1.left) ≠ read (right s1.right)) :
    FoundExit P q first raw m c r := by
  obtain ⟨cT, sT, k, L, hst, hcr, hLP, hprog, hpos⟩ := h es c1 s1 hseg hlive hclk hav hne
  have hL := hLR k cT sT hst hLP
  have hI := PalPeg.CloseoutWatchPhase.inv_of_invLP hLP hL
  have hS := PalPeg.CloseoutWatchPhase.spanRep_of_invLP hLP
  obtain ⟨hM, hR, hres, hSpan⟩ := PalPeg.CloseoutFoundExits.landed_pack hI hS
  exact .landed cT sT k L hst hcr hM hR hres hSpan hprog hpos

/-- **Derived.**  The same, packaged for a `BreakEndC`-shaped landing presented
in `WatchSegE` form: this is the third branch of the three-way exit split, up
to the `WatchSeg` → `WatchSegE` bridge named in the header. -/
theorem foundExitW_of_breakEndE {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    {m : ℕ} {c cP : Control} {r sP : GalilVM}
    (h : FallbackRouteW P q first raw m c r cP sP)
    (hLR : LandingRestartReach P q first raw c r)
    (hbe : ∃ (es : List Bool) (c1 : Control) (s1 : GalilVM),
      WatchSegE P q first 2048 es cP sP c1 s1 ∧ c1.clock = 1 ∧ LiveScanWatch c1 s1 ∧
        canRight s1.right ∧ read (left s1.left) ≠ read (right s1.right)) :
    FoundExit P q first raw m c r := by
  obtain ⟨es, c1, s1, hseg, hclk, hlive, hav, hne⟩ := hbe
  exact foundExitW_of_route h hLR es c1 s1 hseg hlive hclk hav hne

end PalPeg.CloseoutWatchRound17

#print axioms PalPeg.CloseoutWatchRound17.not_prepChain_of_liveScanWatch
#print axioms PalPeg.CloseoutWatchRound17.foundExitW_of_route
#print axioms PalPeg.CloseoutWatchRound17.foundExitW_of_breakEndE
