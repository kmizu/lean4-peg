import PalPeg.CloseoutWatchRound49
import PalPeg.CloseoutWatchRound45

/-!
# Closeout watch round 51 — the found-to-landing segment, and why `WatchFreshC` is false

Round 49 reduced the three remaining watch leaves to one object: a `WatchSegE`
from the found tick to the landing, fresh at its start.  This round locates
that segment in the consumer's context and finds that it is **not** the found
tick's segment at all.

* `foundCtx_landing_clock` — in `FoundCompareCtxC` the found tick carries
  `cF.clock = 1`, and the landing `cP = {cF with clock := 2048}`.  So the
  fresh end is the **landing**, not the found tick.

* `not_watchFreshC` — consequently `WatchFreshC` (Round 49:87) is **false**.

* `WatchFreshAtC` / `watchFreshAtC_of_ctx` — the corrected leaf, at the landing.

* `prepPaceC_of_seg` — `PrepPaceC h m` from a landing segment of length `2h+3`.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

namespace PalPeg.CloseoutWatchRound51

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.CloseoutContracts
open PalPeg.GalilRunSkeleton
open PalPeg.GalilBranchInvariants (BlockInv blockInv_chainStart blockInv_matched)
open PalPeg.CloseoutWatchRound2 (FoundCompareCtxC)
open PalPeg.CloseoutWatchRound49 (WatchFreshC PrepPaceC fresh_advances_pace)

/-! ## 1. Where the fresh clock actually sits -/

/-- **NAMED — the found tick is at clock `1`, the landing at `2048`.** -/
theorem foundCtx_landing_clock (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) {c0 cP : Control} {r sP : GalilVM}
    (hctx : FoundCompareCtxC centre place entry qq first raw c0 r cP sP) :
    cP.clock = 2048 := by
  obtain ⟨es0, cF, sF, vq, ch, oF, a, ls, rs, qw, gap, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hcP, -⟩ := hctx
  rw [hcP]

/-- The landing chain of the context satisfies the block invariant. -/
theorem foundCtx_landing_chain (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) {c0 cP : Control} {r sP : GalilVM}
    (hctx : FoundCompareCtxC centre place entry qq first raw c0 r cP sP) :
    BlockInv sP.chain := by
  obtain ⟨es0, cF, sF, vq, ch, oF, a, ls, rs, qw, gap, -, -, -, -, -, -, -, -, -, -, -, hch, -, -,
    -, hsP⟩ := hctx
  rw [hsP, afterBirth_chain, afterCompare_chain]
  exact blockInv_matched hch (blockInv_chainStart _ _ _ _ _)

/-! ## 2. `WatchFreshC` is false -/

/-- **REFUTED (schema).**  `WatchFreshC` asserts that *every* watch segment
starts at clock `2048`; `WatchSegE.stop` refutes that at any other clock. -/
theorem not_watchFreshC (P : Shared) (q : ℕ) (first : Fin 9)
    (c : Control) (s : GalilVM) (w0 : GalilScaffoldChainWatch.State)
    (hs : s.chain = ChainVM.watch w0) (hc : c.clock ≠ 2048) :
    ¬ WatchFreshC P q first := by
  intro hf
  exact hc (hf [] c c s s w0 w0 (WatchSegE.stop c s) hs hs).2

/-! ## 3. The corrected leaf, at the landing -/

/-- **NAMED — the landing-restricted freshness leaf.** -/
def WatchFreshAtC (P : Shared) (q : ℕ) (first : Fin 9) (cP : Control) (sP : GalilVM) : Prop :=
  ∀ (es2 : List Bool) (c1 : Control) (s1 : GalilVM)
    (w0 w : GalilScaffoldChainWatch.State),
    WatchSegE P q first 2048 es2 cP sP c1 s1 → sP.chain = ChainVM.watch w0 →
    s1.chain = ChainVM.watch w →
    BlockInv (ChainVM.watch w0) ∧ cP.clock = 2048

/-- **(1) CLOSED at the landing.** -/
theorem watchFreshAtC_of_ctx (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) {c0 cP : Control} {r sP : GalilVM}
    (hctx : FoundCompareCtxC centre place entry qq first raw c0 r cP sP) :
    WatchFreshAtC (PofC centre place entry raw) qq first cP sP := by
  intro es2 c1 s1 w0 w hseg hsP hw
  refine ⟨?_, foundCtx_landing_clock centre place entry qq first raw hctx⟩
  have hb := foundCtx_landing_chain centre place entry qq first raw hctx
  rwa [hsP] at hb

/-! ## 4. The preparation pace, from a landing segment -/

/-- **NAMED — the one hypothesis left.** -/
def PrepSegLenC (P : Shared) (q : ℕ) (first : Fin 9) (cP : Control) (sP : GalilVM)
    (h m : ℕ) : Prop :=
  ∃ (es : List Bool) (c1 : Control) (s1 : GalilVM),
    WatchSegE P q first 2048 es cP sP c1 s1 ∧ es.length = 2 * h + 3 ∧ es.count true = m

/-- **(2) CLOSED modulo `PrepSegLenC`.** -/
theorem prepPaceC_of_seg (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) {c0 cP : Control} {r sP : GalilVM} (h m : ℕ)
    (hctx : FoundCompareCtxC centre place entry qq first raw c0 r cP sP)
    (hseg : PrepSegLenC (PofC centre place entry raw) qq first cP sP h m) :
    PrepPaceC h m := by
  obtain ⟨es, c1, s1, hs, hlen, hcnt⟩ := hseg
  have hclk := foundCtx_landing_clock centre place entry qq first raw hctx
  obtain ⟨av, hav, he, -, -⟩ := watchSegE_clock (PofC centre place entry raw) qq first 2048 hs
  rw [hclk] at he
  have hp := fresh_advances_pace av
  rw [← he] at hp
  unfold PrepPaceC
  omega

end PalPeg.CloseoutWatchRound51

#print axioms PalPeg.CloseoutWatchRound51.foundCtx_landing_clock
#print axioms PalPeg.CloseoutWatchRound51.foundCtx_landing_chain
#print axioms PalPeg.CloseoutWatchRound51.not_watchFreshC
#print axioms PalPeg.CloseoutWatchRound51.watchFreshAtC_of_ctx
#print axioms PalPeg.CloseoutWatchRound51.prepPaceC_of_seg
